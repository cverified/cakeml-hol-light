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
let pull_ops_def = cake_define
  `(pull_ops ast_op [] acc = acc) /\
   (pull_ops ast_op (x :: xs) acc =
     (match x with (wordLang_Op op' ls) -> (if ast_op = op' then
       pull_ops ast_op xs (ls ++ acc) else pull_ops ast_op xs (x ::
       acc)) | _1 -> pull_ops ast_op xs (x :: acc)))`;;

let is_const_def = cake_define
  `word_inst_is_const x1 =
        match x1 with
          (wordLang_Const w) -> T
        | _2 -> F`;;

let rm_const_def = cake_define
  `rm_const x1 =
        match x1 with
          (wordLang_Const w) -> w
        | _3 -> (n2w 0)`;;

let convert_sub_def = cake_define
  `convert_sub ls =
        match ls with
          [wordLang_Const w1; wordLang_Const w2] -> wordLang_Const
            (w1 - w2)
        | [x; wordLang_Const w] -> wordLang_Op asm_Add
          [wordLang_Const (--w); x]
        | ls -> wordLang_Op asm_Sub ls`;;

let op_consts_def = cake_define
  `op_consts x1 =
        match x1 with
          asm_And -> wordLang_Const (--(n2w 0))
        | _4 -> wordLang_Const (n2w 0)`;;

(* Returns a definite value *)
let reduce_const_def = cake_define
  `reduce_const ast_op w rest =
   (if w = (n2w 0) then
     if ast_op = asm_Add \/ ast_op = asm_Or \/ ast_op = asm_Xor then
       match rest with
         [] -> wordLang_Const w | [x] -> x | _5 -> wordLang_Op ast_op
           rest else if ast_op = asm_And then
       wordLang_Const (n2w 0) else wordLang_Op ast_op
         (wordLang_Const w :: rest) else wordLang_Op ast_op
         (wordLang_Const w :: rest))`;;

let optimize_consts_def = cake_define
  `optimize_consts ast_op ls =
   (let (const_ls,nconst_ls) = PARTITION word_inst_is_const ls in
     match const_ls with
       [] -> wordLang_Op ast_op nconst_ls | _6 ->
       (let w = THE (wordLang_word_op ast_op (MAP rm_const const_ls))
         in
       reduce_const ast_op w nconst_ls))`;;

(* If this expression contains a constant it should
    be head of the output operation list *)
(* HOL4 termination: \\ rw[] \\ gvs[] \\ drule MEM_list_size \\
   disch_then(qspec_then `exp_size ARB` mp_tac) \\ rw[] *)
let pull_exp_def = cake_define_wf
  `MEASURE (exp_size ARB)`
  `pull_exp exp =
        match exp with
          (wordLang_Op asm_Sub ls) ->
       let new_ls = MAP pull_exp ls in
       convert_sub new_ls
        | (wordLang_Op ast_op []) -> op_consts ast_op
        | (wordLang_Op ast_op [x]) -> pull_exp x
        | (wordLang_Op ast_op ls) ->
       let new_ls = MAP pull_exp ls in
       let pull_ls = pull_ops ast_op new_ls [] in
         optimize_consts ast_op pull_ls
        | (wordLang_Load wordLang_exp) -> wordLang_Load (pull_exp
          wordLang_exp)
        | (wordLang_Shift (backend_common_word_shift) wordLang_exp
          nexp) -> wordLang_Shift (backend_common_word_shift) (pull_exp
          wordLang_exp) (pull_exp nexp)
        | wordLang_exp -> wordLang_exp`;;

(*Flatten list expressions to trees -- of the form:
      +
     /\
    + a
   /\
  + b
 /\
c d
*)
(* HOL4 termination: \\ REPEAT STRIP_TAC \\ IMP_RES_TAC
   MEM_IMP_exp_size \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC
   `ARB`)) \\ fs[exp_size_def] \\ TRY (DECIDE_TAC) *)
let flatten_exp_def = cake_define_wf
  `MEASURE (exp_size ARB)`
  `flatten_exp exp =
        match exp with
          (wordLang_Op asm_Sub exps) -> wordLang_Op asm_Sub (MAP
            flatten_exp exps)
        | (wordLang_Op ast_op []) -> op_consts ast_op
        | (wordLang_Op ast_op [x]) -> flatten_exp x
        | (wordLang_Op ast_op (x :: xs)) -> wordLang_Op ast_op
          [flatten_exp (wordLang_Op ast_op xs); flatten_exp x]
        | (wordLang_Load wordLang_exp) -> wordLang_Load (flatten_exp
          wordLang_exp)
        | (wordLang_Shift (backend_common_word_shift) wordLang_exp
          nexp) -> wordLang_Shift (backend_common_word_shift)
          (flatten_exp wordLang_exp) (flatten_exp nexp)
        | wordLang_exp -> wordLang_exp`;;


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
        (wordLang_Lookup CurrHeap) -> T
      | _7 -> F`;;

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

(* HOL4 termination: \\ REPEAT STRIP_TAC \\ IMP_RES_TAC
   MEM_IMP_exp_size \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC
   `ARB`)) \\ fs[exp_size_def] \\ TRY (DECIDE_TAC) *)
let inst_select_exp_def = cake_define_wf
  `MEASURE (exp_size ARB o SND o SND o SND)`
  `inst_select_exp c tar temp x4 =
        match (c,tar,temp,x4) with
          ((c:'a asm_config),(tar:num),(temp:num),(wordLang_Load
            wordLang_exp)) ->
       match wordLang_exp with wordLang_Op asm_Add [exp';
         wordLang_Const w] ->
         (if (\c. offset_ok 0 (asm_config_addr_offset c)) c w then
           let wordLang_prog = inst_select_exp c temp temp exp' in
             wordLang_Seq wordLang_prog (wordLang_Inst (asm_Mem
               wordLang_Load tar (Addr temp w))) else
           let wordLang_prog = inst_select_exp c temp temp
             wordLang_exp in
             wordLang_Seq wordLang_prog (wordLang_Inst (asm_Mem
               wordLang_Load tar (Addr temp ((n2w 0)))))) | _8 ->
         (let wordLang_prog = inst_select_exp c temp temp
           wordLang_exp in
         wordLang_Seq wordLang_prog (wordLang_Inst (asm_Mem
           wordLang_Load tar (Addr temp ((n2w 0))))))
        | (c,(tar:num),(temp:num),(wordLang_Const w)) ->
          (wordLang_Inst (wordLang_Const tar w))
        | (c,(tar:num),(temp:num),(wordLang_Var v)) ->
       wordLang_Move 0 [tar,v]
        | (c,tar,temp,(wordLang_Lookup store_name)) ->
       wordLang_Get tar store_name
        | (c,tar,temp,(wordLang_Op ast_op [e1; e2])) ->
       if is_Lookup_CurrHeap e2 then
         (let p1 = inst_select_exp c temp temp e1 in
           wordLang_Seq p1 (wordLang_OpCurrHeap ast_op tar temp))
             else if is_Lookup_CurrHeap e1 /\ ~(ast_op = asm_Sub) then
         (let p2 = inst_select_exp c temp temp e2 in
           wordLang_Seq p2 (wordLang_OpCurrHeap ast_op tar temp))
             else
       let p1 = inst_select_exp c temp temp e1 in
       match e2 with wordLang_Const w ->
         (if asm_config_valid_imm c (INL ast_op) w then
           wordLang_Seq p1 (wordLang_Inst (asm_Arith (asm_Binop
             ast_op tar temp (Imm w)))) else if ast_op = asm_Add /\
             asm_config_valid_imm c (INL asm_Sub) (--w) then
           wordLang_Seq p1 (wordLang_Inst (asm_Arith (asm_Binop
             asm_Sub tar temp (Imm (--w))))) else
           let p2 = wordLang_Inst (wordLang_Const (temp + 1) w) in
           wordLang_Seq p1 (wordLang_Seq p2 (wordLang_Inst (asm_Arith
             (asm_Binop ast_op tar temp (Reg (temp + 1))))))) | _9 ->
         (let p2 = inst_select_exp c (temp + 1) (temp + 1) e2 in
         wordLang_Seq p1 (wordLang_Seq p2 (wordLang_Inst (asm_Arith
           (asm_Binop ast_op tar temp (Reg (temp + 1)))))))
        | (c,tar,temp,(wordLang_Shift sh wordLang_exp e1)) ->
       match e1 with wordLang_Const shift_len ->
           (let n = w2n shift_len in
             if (n < dimindex (:'a)) then
               (let wordLang_prog = inst_select_exp c temp temp
                 wordLang_exp in
                 if n = 0 then
                   wordLang_Seq wordLang_prog (wordLang_Move 0
                     [tar,temp]) else
                    wordLang_Seq wordLang_prog (wordLang_Inst
                      (asm_Arith (wordLang_Shift sh tar temp (Imm (n2w
                      n)))))) else
               wordLang_Inst (wordLang_Const tar (n2w 0))) | _10 ->
         (let p = inst_select_exp c temp temp wordLang_exp in
         let p1 = inst_select_exp c (temp + 1) (temp + 1) e1 in
         wordLang_Seq p (wordLang_Seq p1 (wordLang_Inst (asm_Arith
           (wordLang_Shift sh tar temp (Reg (temp + 1)))))))
        | (_11,_12,_13,_14) -> wordLang_Skip`;;

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
          (wordLang_Assign v wordLang_exp) ->
       (inst_select_exp c v temp o flatten_exp o pull_exp)
         wordLang_exp
        | (wordLang_Set store wordLang_exp) ->
       let wordLang_prog = (inst_select_exp c temp temp o flatten_exp
         o pull_exp) wordLang_exp in
       wordLang_Seq wordLang_prog (wordLang_Set store (wordLang_Var
         temp))
        | (wordLang_Store wordLang_exp var) ->
       let wordLang_exp = (flatten_exp o pull_exp) wordLang_exp in
       match wordLang_exp with wordLang_Op asm_Add [exp';
         wordLang_Const w] ->
         (if (\c. offset_ok 0 (asm_config_addr_offset c)) c w then
           let wordLang_prog = inst_select_exp c temp temp exp' in
             wordLang_Seq wordLang_prog (wordLang_Inst (asm_Mem
               wordLang_Store var (Addr temp w))) else
           let wordLang_prog = inst_select_exp c temp temp
             wordLang_exp in
             wordLang_Seq wordLang_prog (wordLang_Inst (asm_Mem
               wordLang_Store var (Addr temp ((n2w 0)))))) | _15 ->
         (let wordLang_prog = inst_select_exp c temp temp
           wordLang_exp in
         wordLang_Seq wordLang_prog (wordLang_Inst (asm_Mem
           wordLang_Store var (Addr temp ((n2w 0))))))
        | (wordLang_Seq p1 p2) ->
       wordLang_Seq (inst_select c temp p1) (inst_select c temp p2)
        | (wordLang_MustTerminate p1) ->
       wordLang_MustTerminate (inst_select c temp p1)
        | (wordLang_ShareInst ast_op v wordLang_exp) ->
       let wordLang_exp = (flatten_exp o pull_exp) wordLang_exp in
       match wordLang_exp with wordLang_Op asm_Add [exp';
         wordLang_Const w] ->
         (if ((ast_op = wordLang_Load \/ ast_op = wordLang_Store) /\
           (\c. offset_ok 0 (asm_config_addr_offset c)) c w) \/
             ((ast_op = asm_Load32 \/ ast_op = asm_Store32) /\ (\c.
               offset_ok 0 (asm_config_addr_offset c)) c w) \/
             ((ast_op = asm_Load16 \/ ast_op = asm_Store16) /\ (\c.
               offset_ok 0 (asm_config_hw_offset c)) c w) \/
             ((ast_op = asm_Load8 \/ ast_op = asm_Store8) /\ (\c.
               offset_ok 0 (asm_config_byte_offset c)) c w) then
           let wordLang_prog = inst_select_exp c temp temp exp' in
             wordLang_Seq wordLang_prog (wordLang_ShareInst ast_op v
               (wordLang_Op asm_Add [wordLang_Var temp; wordLang_Const
               w])) else
           let wordLang_prog = inst_select_exp c temp temp
             wordLang_exp in
             wordLang_Seq wordLang_prog (wordLang_ShareInst ast_op v
               (wordLang_Var temp))) | _16 ->
         (let wordLang_prog = inst_select_exp c temp temp
           wordLang_exp in
         wordLang_Seq wordLang_prog (wordLang_ShareInst ast_op v
           (wordLang_Var temp)))
        | (wordLang_If cmp r1 ri c1 c2) ->
       wordLang_If cmp r1 ri (inst_select c temp c1) (inst_select c
         temp c2)
        | (wordLang_Call ret dest args handler) ->
       let retsel =
         match ret with
           NONE -> NONE | SOME (n,names,ret_handler,l1,l2) ->
           SOME (n,names,inst_select c temp ret_handler,l1,l2) in
       let handlersel =
         match handler with
           NONE -> NONE | SOME (n,h,l1,l2) -> SOME (n,inst_select c
             temp h,l1,l2) in
       wordLang_Call retsel dest args handlersel
        | (wordLang_Loop names body exit_names) ->
       wordLang_Loop names (inst_select c temp body) exit_names
        | wordLang_prog -> wordLang_prog`;;

(*
  Convert all 3 register instructions to 2 register instructions
*)
let three_to_two_reg_def = cake_define
  `three_to_two_reg prog =
        match prog with
          (wordLang_Inst (asm_Arith (asm_Binop bop r1 r2 ri))) ->
       wordLang_Seq (wordLang_Move 0 [r1,r2]) (wordLang_Inst
         (asm_Arith (asm_Binop bop r1 r1 ri)))
        | (wordLang_Inst (asm_Arith (wordLang_Shift l r1 r2 n))) ->
       wordLang_Seq (wordLang_Move 0 [r1,r2]) (wordLang_Inst
         (asm_Arith (wordLang_Shift l r1 r1 n)))
        | (wordLang_Inst (asm_Arith (asm_AddCarry r1 r2 r3 r4))) ->
       wordLang_Seq (wordLang_Move 0 [r1,r2]) (wordLang_Inst
         (asm_Arith (asm_AddCarry r1 r1 r3 r4)))
        | (wordLang_Inst (asm_Arith (asm_AddOverflow r1 r2 r3 r4)))
          ->
       wordLang_Seq (wordLang_Move 0 [r1,r2]) (wordLang_Inst
         (asm_Arith (asm_AddOverflow r1 r1 r3 r4)))
        | (wordLang_Inst (asm_Arith (asm_SubOverflow r1 r2 r3 r4)))
          ->
       wordLang_Seq (wordLang_Move 0 [r1,r2]) (wordLang_Inst
         (asm_Arith (asm_SubOverflow r1 r1 r3 r4)))
        | (wordLang_OpCurrHeap bop r1 r2) ->
       wordLang_Seq (wordLang_Move 0 [r1,r2]) (wordLang_OpCurrHeap
         bop r1 r1)
        | (wordLang_Seq p1 p2) ->
       wordLang_Seq (three_to_two_reg p1) (three_to_two_reg p2)
        | (wordLang_MustTerminate p1) ->
       wordLang_MustTerminate (three_to_two_reg p1)
        | (wordLang_If cmp r1 ri c1 c2) ->
       wordLang_If cmp r1 ri (three_to_two_reg c1) (three_to_two_reg
         c2)
        | (wordLang_Call ret dest args handler) ->
       let retsel =
         match ret with
           NONE -> NONE | SOME (n,names,ret_handler,l1,l2) ->
           SOME (n,names,three_to_two_reg ret_handler,l1,l2) in
       let handlersel =
         match handler with
           NONE -> NONE | SOME (n,h,l1,l2) -> SOME
             (n,three_to_two_reg h,l1,l2) in
       wordLang_Call retsel dest args handlersel
        | (wordLang_Loop names body exit_names) ->
       wordLang_Loop names (three_to_two_reg body) exit_names
        | wordLang_prog -> wordLang_prog`;;

let three_to_two_reg_prog_def = cake_define
  `three_to_two_reg_prog b wordLang_prog =
     (if b then three_to_two_reg wordLang_prog else wordLang_prog)`;;
