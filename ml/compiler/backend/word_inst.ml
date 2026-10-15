(* ======================================================== *)
(*  word_inst: ported from HOL4's
    compiler/backend/word_instScript.sml  *)
(* ======================================================== *)

(*
  This compiler phase implements instruction selection. It uses the
  Maximal Munch strategy.
*)

needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sorting.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

(*Scheme:
1) Pull all nested ops and consts as far up as possible and convert
  Sub [ x ; Const w ] to Add [x ; Const -w]
2) Flatten to binary branching expressions
3) inst select, assuming binary branches
4) 3->2 regs if necessary
*)

(*Pull all nested arguments with the same op up*)
let pull_ops_def = cake_define_list
  [`pull_ops op [] acc = acc`;
   `pull_ops op (x :: xs) acc =
        (match x with (wordLang_Op op' ls) -> (if op = op' then
          pull_ops op xs (ls ++ acc) else pull_ops op xs (x :: acc))
          | _2 -> pull_ops op xs (x :: acc))`];;

let is_const_def = cake_define
  `word_inst_is_const x1 =
        match x1 with
          wordLang_Const w -> T
        | _3 -> F`;;
hol4_overload "is_const" "word_inst_is_const";;

let rm_const_def = cake_define
  `rm_const x1 =
        match x1 with
          wordLang_Const w -> w
        | _4 -> (n2w 0)`;;

let convert_sub_def = cake_define
  `convert_sub ls =
        match ls with
          [wordLang_Const w1; Const w2] -> Const (w1 - w2)
        | [x; Const w] -> wordLang_Op Add [Const (--w); x]
        | ls -> wordLang_Op Sub ls`;;

let op_consts_def = cake_define
  `op_consts x1 =
        match x1 with
          And -> Const (--(n2w 0))
        | _5 -> Const (n2w 0)`;;

(* Returns a definite value *)
let reduce_const_def = cake_define
  `reduce_const op w rest =
   (if w = (n2w 0) then
     if op = Add \/ op = Or \/ op = Xor then
       match rest with
         [] -> Const w | [x] -> x | _6 -> wordLang_Op op rest else if
           op = And then
       Const (n2w 0) else wordLang_Op op (Const w :: rest) else
         wordLang_Op op (Const w :: rest))`;;

let optimize_consts_def = cake_define
  `optimize_consts op ls =
   (let (const_ls,nconst_ls) = PARTITION word_inst_is_const ls in
     match const_ls with
       [] -> wordLang_Op op nconst_ls | _7 ->
       (let w = THE (wordLang_word_op op (MAP rm_const const_ls)) in
       reduce_const op w nconst_ls))`;;

(* If this expression contains a constant it should
    be head of the output operation list *)
let _ = size_thms "exp";;
(* HOL4 termination: \\ rw[] \\ gvs[] \\ drule MEM_list_size \\
   disch_then(qspec_then `exp_size ARB` mp_tac) \\ rw[] *)
let pull_exp_def = cake_define_wf
  `MEASURE (exp_size ARB)`
  `pull_exp exp =
        match exp with
          wordLang_Op Sub ls ->
       (let new_ls = MAP pull_exp ls in
       convert_sub new_ls)
        | (wordLang_Op op []) -> op_consts op
        | (wordLang_Op op [x]) -> pull_exp x
        | (wordLang_Op op ls) ->
       (let new_ls = MAP pull_exp ls in
       let pull_ls = pull_ops op new_ls [] in
         optimize_consts op pull_ls)
        | (Load exp) -> Load (pull_exp exp)
        | (Shift backend_common_word_shift exp nexp) -> Shift
          backend_common_word_shift (pull_exp exp) (pull_exp nexp)
        | exp -> exp`;;

(*Flatten list expressions to trees -- of the form:
      +
     /\
    + a
   /\
  + b
 /\
c d
*)
let _ = size_thms "exp";;
(* HOL4 termination: \\ REPEAT STRIP_TAC \\ IMP_RES_TAC
   MEM_IMP_exp_size \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC
   `ARB`)) \\ fs[exp_size_def] \\ TRY (DECIDE_TAC) *)
let flatten_exp_def = cake_define_wf
  `MEASURE (exp_size ARB)`
  `flatten_exp exp =
        match exp with
          wordLang_Op Sub exps -> wordLang_Op Sub (MAP flatten_exp
            exps)
        | (wordLang_Op op []) -> op_consts op
        | (wordLang_Op op [x]) -> flatten_exp x
        | (wordLang_Op op (x :: xs)) -> wordLang_Op op [flatten_exp
          (wordLang_Op op xs); flatten_exp x]
        | (Load exp) -> Load (flatten_exp exp)
        | (Shift backend_common_word_shift exp nexp) -> Shift
          backend_common_word_shift (flatten_exp exp) (flatten_exp nexp)
        | exp -> exp`;;


  (*
Theorem flatten_exp_pmatch:
  !exp.
  flatten_exp exp =
  pmatch exp of
    (Op Sub exps) => Op Sub (MAP flatten_exp exps)
  | (Op op []) => op_consts op
  | (Op op [x]) => flatten_exp x
  | (Op op (x::xs)) => Op op [flatten_exp (Op op xs);flatten_exp x]
  | (Load exp) => Load (flatten_exp exp)
  | (Shift shift exp nexp) => Shift shift (flatten_exp exp) nexp
  | exp => exp
Proof
  rpt strip_tac
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> every_case_tac
  >> fs[flatten_exp_def, ETA_THM]
QED*)
(*
val test = EVAL ``flatten_exp (pull_exp (Op Add [Const 1w;Const 2w;
  Const 3w; Op Add [Const 4w; Const 5w; Op Add[Const 6w; Const 7w];Op
  Xor[Const 1w;Var y;Var x]] ; Const (8w:8 word)]))``

val test = EVAL ``flatten_exp (pull_exp (Op Sub [Const 1w; Op Sub[Const
  2w;Const (3w:64 word)]]))``

 Op Add [Const 4w; Const 5w; Op Add[Const 6w; Const 7w];Op Xor[Const
   1w;Var y;Var x]] ; Const (8w:8 word)]))``
*)

let is_Lookup_CurrHeap_def = cake_define
  `is_Lookup_CurrHeap x1 =
      match x1 with
        wordLang_Lookup CurrHeap -> T
      | _8 -> F`;;

(*
  Maximal Munch instruction selection on (binary) expressions
  c is an asm_config to check validity of imms (TODO: assume 0w is
    accepted?)
  Optimized munches (assumes Consts are on the RIGHT):
  --Load [Op Add [exp;Const w]]
  Op op [exp;Const w]
  --Store exp var

  Next, perform instruction selection assuming input is binary branching
  Each step takes tar and temp where we are allowed to store temporaries
  in temp and the value of the whole expression must be saved in tar
*)

let _ = size_thms "exp";;
(* HOL4 termination: \\ REPEAT STRIP_TAC \\ IMP_RES_TAC
   MEM_IMP_exp_size \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC
   `ARB`)) \\ fs[exp_size_def] \\ TRY (DECIDE_TAC) *)
let inst_select_exp_def = cake_define_wf
  `MEASURE (exp_size ARB o SND o SND o SND)`
  `inst_select_exp c tar temp x4 =
        match (c,tar,temp,x4) with
          ((c:'a asm_config),(tar:num),(temp:num),wordLang_Load exp)
            ->
       (match exp with wordLang_Op Add [exp'; Const w] ->
         (if (\c. asm_offset_ok 0 (asm_config_addr_offset c)) c w
           then
           let prog = inst_select_exp c temp temp exp' in
             Seq prog (Inst (asm_Mem Load tar (Addr temp w))) else
           let prog = inst_select_exp c temp temp exp in
             Seq prog (Inst (asm_Mem Load tar (Addr temp ((n2w
               0)))))) | _9 ->
         (let prog = inst_select_exp c temp temp exp in
         Seq prog (Inst (asm_Mem Load tar (Addr temp ((n2w 0)))))))
        | (c,(tar:num),(temp:num),(Const w)) -> (Inst (Const tar w))
        | (c,(tar:num),(temp:num),(Var v)) ->
       wordLang_Move 0 [tar,v]
        | (c,tar,temp,(wordLang_Lookup store_name)) ->
       Get tar store_name
        | (c,tar,temp,(wordLang_Op op [e1; e2])) ->
       (if is_Lookup_CurrHeap e2 then
         (let p1 = inst_select_exp c temp temp e1 in
           Seq p1 (OpCurrHeap op tar temp)) else if
             is_Lookup_CurrHeap e1 /\ ~(op = Sub) then
         (let p2 = inst_select_exp c temp temp e2 in
           Seq p2 (OpCurrHeap op tar temp)) else
       let p1 = inst_select_exp c temp temp e1 in
       match e2 with Const w ->
         (if asm_config_valid_imm c (INL op) w then
           Seq p1 (Inst (Arith (asm_Binop op tar temp (Imm w)))) else
             if op = Add /\ asm_config_valid_imm c (INL Sub) (--w) then
           Seq p1 (Inst (Arith (asm_Binop Sub tar temp (Imm (--w)))))
             else
           let p2 = Inst (Const (temp + 1) w) in
           Seq p1 (Seq p2 (Inst (Arith (asm_Binop op tar temp (Reg
             (temp + 1))))))) | _10 ->
         (let p2 = inst_select_exp c (temp + 1) (temp + 1) e2 in
         Seq p1 (Seq p2 (Inst (Arith (asm_Binop op tar temp (Reg
           (temp + 1))))))))
        | (c,tar,temp,(Shift sh exp e1)) ->
       (match e1 with Const shift_len ->
           (let n = w2n shift_len in
             if (n < dimindex (:'a)) then
               (let prog = inst_select_exp c temp temp exp in
                 if n = 0 then
                   Seq prog (wordLang_Move 0 [tar,temp]) else
                    Seq prog (Inst (Arith (Shift sh tar temp (Imm
                      (n2w n)))))) else
               Inst (Const tar (n2w 0))) | _11 ->
         (let p = inst_select_exp c temp temp exp in
         let p1 = inst_select_exp c (temp + 1) (temp + 1) e1 in
         Seq p (Seq p1 (Inst (Arith (Shift sh tar temp (Reg (temp +
           1))))))))
        | (_12,_13,_14,_15) -> Skip`;;

(*

First munch
EVAL ``inst_select_exp``
 x64_config 5 5 (Load (Op Add [Const 400w; Var 6]))``
EVAL ``inst_select_exp x64_config 5 5 (Load (Op Add [Const 99999999999w;
  Var 6]))``

Second munch
EVAL ``inst_select_exp x64_config 0 99
EVAL ``(pull_exp (Op And [Const (99w:64 word); Op Add [Op Add [];Op Or
  []]]))``
*)

(*Flattens all expressions in program, temp must a fresh var*)
let inst_select_def = cake_define
  `inst_select c temp prog =
        match prog with
          wordLang_Assign v exp ->
       (inst_select_exp c v temp o flatten_exp o pull_exp) exp
        | (Set store exp) ->
       (let prog = (inst_select_exp c temp temp o flatten_exp o
         pull_exp) exp in
       Seq prog (Set store (Var temp)))
        | (Store exp var) ->
       (let exp = (flatten_exp o pull_exp) exp in
       match exp with wordLang_Op Add [exp'; Const w] ->
         (if (\c. asm_offset_ok 0 (asm_config_addr_offset c)) c w
           then
           let prog = inst_select_exp c temp temp exp' in
             Seq prog (Inst (asm_Mem Store var (Addr temp w))) else
           let prog = inst_select_exp c temp temp exp in
             Seq prog (Inst (asm_Mem Store var (Addr temp ((n2w
               0)))))) | _16 ->
         (let prog = inst_select_exp c temp temp exp in
         Seq prog (Inst (asm_Mem Store var (Addr temp ((n2w 0)))))))
        | (Seq p1 p2) ->
       Seq (inst_select c temp p1) (inst_select c temp p2)
        | (wordLang_MustTerminate p1) ->
       wordLang_MustTerminate (inst_select c temp p1)
        | (wordLang_ShareInst op v exp) ->
       (let exp = (flatten_exp o pull_exp) exp in
       match exp with wordLang_Op Add [exp'; Const w] ->
         (if ((op = Load \/ op = Store) /\ (\c. asm_offset_ok 0
           (asm_config_addr_offset c)) c w) \/
             ((op = asm_Load32 \/ op = asm_Store32) /\ (\c.
               asm_offset_ok 0 (asm_config_addr_offset c)) c w) \/
             ((op = asm_Load16 \/ op = asm_Store16) /\ (\c.
               asm_offset_ok 0 (asm_config_hw_offset c)) c w) \/
             ((op = asm_Load8 \/ op = asm_Store8) /\ (\c.
               asm_offset_ok 0 (asm_config_byte_offset c)) c w) then
           let prog = inst_select_exp c temp temp exp' in
             Seq prog (wordLang_ShareInst op v (wordLang_Op Add [Var
               temp; Const w])) else
           let prog = inst_select_exp c temp temp exp in
             Seq prog (wordLang_ShareInst op v (Var temp))) | _17 ->
         (let prog = inst_select_exp c temp temp exp in
         Seq prog (wordLang_ShareInst op v (Var temp))))
        | (If cmp r1 ri c1 c2) ->
       If cmp r1 ri (inst_select c temp c1) (inst_select c temp c2)
        | (Call ret dest args handler) ->
       (let retsel =
         match ret with
           NONE -> NONE | SOME (n,names,ret_handler,l1,l2) ->
           SOME (n,names,inst_select c temp ret_handler,l1,l2) in
       let handlersel =
         match handler with
           NONE -> NONE | SOME (n,h,l1,l2) -> SOME (n,inst_select c
             temp h,l1,l2) in
       Call retsel dest args handlersel)
        | (Loop names body exit_names) ->
       Loop names (inst_select c temp body) exit_names
        | prog -> prog`;;

(*
  Convert all 3 register instructions to 2 register instructions
*)
let three_to_two_reg_def = cake_define
  `three_to_two_reg prog =
        match prog with
          wordLang_Inst (Arith (asm_Binop bop r1 r2 ri)) ->
       Seq (wordLang_Move 0 [r1,r2]) (Inst (Arith (asm_Binop bop r1
         r1 ri)))
        | (Inst (Arith (Shift l r1 r2 n))) ->
       Seq (wordLang_Move 0 [r1,r2]) (Inst (Arith (Shift l r1 r1 n)))
        | (Inst (Arith (asm_AddCarry r1 r2 r3 r4))) ->
       Seq (wordLang_Move 0 [r1,r2]) (Inst (Arith (asm_AddCarry r1 r1
         r3 r4)))
        | (Inst (Arith (asm_AddOverflow r1 r2 r3 r4))) ->
       Seq (wordLang_Move 0 [r1,r2]) (Inst (Arith (asm_AddOverflow r1
         r1 r3 r4)))
        | (Inst (Arith (asm_SubOverflow r1 r2 r3 r4))) ->
       Seq (wordLang_Move 0 [r1,r2]) (Inst (Arith (asm_SubOverflow r1
         r1 r3 r4)))
        | (OpCurrHeap bop r1 r2) ->
       Seq (wordLang_Move 0 [r1,r2]) (OpCurrHeap bop r1 r1)
        | (Seq p1 p2) ->
       Seq (three_to_two_reg p1) (three_to_two_reg p2)
        | (wordLang_MustTerminate p1) ->
       wordLang_MustTerminate (three_to_two_reg p1)
        | (If cmp r1 ri c1 c2) ->
       If cmp r1 ri (three_to_two_reg c1) (three_to_two_reg c2)
        | (Call ret dest args handler) ->
       (let retsel =
         match ret with
           NONE -> NONE | SOME (n,names,ret_handler,l1,l2) ->
           SOME (n,names,three_to_two_reg ret_handler,l1,l2) in
       let handlersel =
         match handler with
           NONE -> NONE | SOME (n,h,l1,l2) -> SOME
             (n,three_to_two_reg h,l1,l2) in
       Call retsel dest args handlersel)
        | (Loop names body exit_names) ->
       Loop names (three_to_two_reg body) exit_names
        | prog -> prog`;;

let three_to_two_reg_prog_def = cake_define
  `three_to_two_reg_prog b prog =
     (if b then three_to_two_reg prog else prog)`;;
