(* ======================================================== *)
(*  word_inst: ported from HOL4's
    compiler/backend/word_instScript.sml
    A definition theory, with 14 definitions and 7 theorems.  Needed
    by 7 files of the port.  *)
(* ======================================================== *)

(*
  This compiler phase implements instruction selection. It uses the
  Maximal Munch strategy.
*)

needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sorting.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "word_inst"
  ["stackLang"; "wordLang"];;

let _ = do_list hide_constant ["pmatch"];;

(* HOL4 word_instScript.sml:11-12: an overload that the source brings
   to the front: Shift, written out as wordLang_Shift *)

(*Scheme:
1) Pull all nested ops and consts as far up as possible and convert
  Sub [ x ; Const w ] to Add [x ; Const -w]
2) Flatten to binary branching expressions
3) inst select, assuming binary branches
4) 3->2 regs if necessary
*)

(*Pull all nested arguments with the same op up*)
let pull_ops_def,pull_ops_ind = define_rec
  [`pull_ops op [] acc = acc`;
   `pull_ops op (CONS x xs) acc =
        (match x with (wordLang_Op op' ls) -> (if op = op' then
            pull_ops op xs (APPEND ls acc) else pull_ops op xs
            (CONS x acc)) | _2 -> pull_ops op xs (CONS x acc))`];;

let word_inst_is_const_def = new_definition
  `word_inst_is_const x1 =
        match x1 with
          wordLang_Const w -> T
        | _3 -> F`;;

let rm_const_def = new_definition
  `rm_const x1 =
        match x1 with
          wordLang_Const w -> w
        // Make it total
        | _4 -> (n2w 0)`;;

let convert_sub_def = new_definition
  `convert_sub ls =
        match ls with
          [wordLang_Const w1; wordLang_Const w2] -> wordLang_Const
            (w1 - w2)
        | [x; wordLang_Const w] -> wordLang_Op asm_Add
          [wordLang_Const (--w); x]
        | ls -> wordLang_Op asm_Sub ls`;;

let convert_sub_pmatch = prove
 (`!l.
   convert_sub l =
   (match l with
     [wordLang_Const w1; wordLang_Const w2] -> wordLang_Const (w1 -
       w2) | [x; wordLang_Const w] -> wordLang_Op asm_Add
       [wordLang_Const (--w); x] | ls -> wordLang_Op asm_Sub ls)`,
  CHEAT_TAC);;

let op_consts_def = new_definition
  `op_consts x1 =
        match x1 with
          (asm_And:binop) -> wordLang_Const (word_not (n2w 0))
        | _5 -> wordLang_Const (n2w 0)`;;

let op_consts_pmatch = prove
 (`!op.
   op_consts op =
   (match op with
     asm_And -> wordLang_Const (word_not (n2w 0)) | _6 ->
       wordLang_Const (n2w 0))`,
  CHEAT_TAC);;

(* Returns a definite value *)
let reduce_const_def = new_definition
  `reduce_const op w rest =
   (if w = (n2w 0) then
     if op = asm_Add \/ op = asm_Or \/ op = asm_Xor then
       match rest with
         [] -> wordLang_Const w | [x] -> x | _7 -> wordLang_Op op
           rest else if op = asm_And then
       wordLang_Const (n2w 0) else wordLang_Op op (CONS
         (wordLang_Const w) rest) else wordLang_Op op (CONS
         (wordLang_Const w) rest))`;;

let optimize_consts_def = new_definition
  `optimize_consts op ls =
   (let (const_ls,nconst_ls) = PARTITION word_inst_is_const ls in
     match const_ls with
       [] -> wordLang_Op op nconst_ls | _8 ->
       (let w = THE (wordLang_word_op op (MAP rm_const const_ls)) in
       reduce_const op w nconst_ls))`;;

(* If this expression contains a constant it should
    be head of the output operation list *)
(* the termination relation that HOL4 gives is
     MEASURE (wordLang_exp_size ARB)
   which is not one that HOL Light takes here; the one
   below is what the port found for it *)
(* HOL4 word_instScript.sml:122-129: the tactic that proves the
   termination *)
let pull_exp_def,pull_exp_ind = define_wf
  `MEASURE (\x0. wordLang_exp_size (\x. 0) x0)`
  [`pull_exp exp =
        match exp with
          wordLang_Op asm_Sub ls ->
       (let new_ls = MAP pull_exp ls in
       convert_sub new_ls)
        | (wordLang_Op op []) -> op_consts op
        | (wordLang_Op op [x]) -> pull_exp x
        | (wordLang_Op op ls) ->
       // First, pull all the inner expressions
       (let new_ls = MAP pull_exp ls in
       // Then pull at the topmost
       let pull_ls = pull_ops op new_ls [] in
         optimize_consts op pull_ls)
        | (wordLang_Load exp) -> wordLang_Load (pull_exp exp)
        | (wordLang_Shift shift' exp nexp) -> wordLang_Shift shift'
          (pull_exp exp) (pull_exp nexp)
        | exp -> exp`];;

let pull_exp_pmatch = prove
 (`!(exp:'a wordLang_exp).
   pull_exp exp =
   (match exp with
    wordLang_Op asm_Sub ls -> (
     let new_ls = MAP pull_exp ls in
     convert_sub new_ls) | wordLang_Op op [] -> op_consts op |
       wordLang_Op op [x] -> pull_exp x | wordLang_Op op ls -> (
     let new_ls = MAP pull_exp ls in
     let pull_ls = pull_ops op new_ls [] in
       optimize_consts op pull_ls) | wordLang_Load exp ->
         wordLang_Load (pull_exp exp) | wordLang_Shift sh exp nexp ->
         wordLang_Shift sh (pull_exp exp) (pull_exp nexp) | exp ->
         exp)`,
  CHEAT_TAC);;

(*Flatten list expressions to trees -- of the form:
      +
     /\
    + a
   /\
  + b
 /\
c d
*)
(* the termination relation that HOL4 gives is
     MEASURE (wordLang_exp_size ARB)
   which is not one that HOL Light takes here; the one
   below is what the port found for it *)
(* HOL4 word_instScript.sml:171-177: the tactic that proves the
   termination *)
let flatten_exp_def,flatten_exp_ind = define_wf
  `MEASURE (\x0. wordLang_exp_size (\x. 0) x0)`
  [`flatten_exp exp =
        match exp with
          wordLang_Op asm_Sub exps -> wordLang_Op asm_Sub (MAP
            flatten_exp exps)
        | (wordLang_Op op []) -> op_consts op
        | (wordLang_Op op [x]) -> flatten_exp x
        | (wordLang_Op op (CONS x xs)) -> wordLang_Op op
          [flatten_exp (wordLang_Op op xs); flatten_exp x]
        | (wordLang_Load exp) -> wordLang_Load (flatten_exp exp)
        | (wordLang_Shift shift' exp nexp) -> wordLang_Shift shift'
          (flatten_exp exp) (flatten_exp nexp)
        | exp -> exp`];;


(* HOL4 word_instScript.sml:180-197: code that the source has in a
   comment *)
(* HOL4 word_instScript.sml:198-204: code that the source has in a
   comment *)

let is_Lookup_CurrHeap_def = new_definition
  `is_Lookup_CurrHeap x1 =
      match x1 with
        wordLang_Lookup CurrHeap -> T
      | _9 -> F`;;

let is_Lookup_CurrHeap_pmatch = prove
 (`is_Lookup_CurrHeap e =
     (match e with wordLang_Lookup CurrHeap -> T | _10 -> F)`,
  CHEAT_TAC);;

(*
  Maximal Munch instruction selection on (binary) expressions
  c is an asm_config to check validity of imms (TODO: assume 0w is accepted?)
  Optimized munches (assumes Consts are on the RIGHT):
  --Load [Op Add [exp;Const w]]
  Op op [exp;Const w]
  --Store exp var

  Next, perform instruction selection assuming input is binary branching
  Each step takes tar and temp where we are allowed to store temporaries
  in temp and the value of the whole expression must be saved in tar
*)

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 word_instScript.sml:294-300: the tactic that proves the
   termination *)
let inst_select_exp_def,inst_select_exp_ind = define_wf
  `MEASURE (wordLang_exp_size ARB o SND o SND o SND)`
  [`inst_select_exp c tar temp x4 =
        match (c,tar,temp,x4) with
          ((c:'a asm_config),(tar:num),(temp:num),wordLang_Load exp)
            ->
       (match exp with wordLang_Op asm_Add [exp'; wordLang_Const w]
         ->
         (if (\c. asm_offset_ok 0 (asm_config_addr_offset c)) c w
           then
           let prog = inst_select_exp c temp temp exp' in
             wordLang_Seq prog (wordLang_Inst (asm_Mem asm_Load tar
               (Addr temp w))) else
           let prog = inst_select_exp c temp temp exp in
             wordLang_Seq prog (wordLang_Inst (asm_Mem asm_Load tar
               (Addr temp ((n2w 0)))))) | _11 ->
         (let prog = inst_select_exp c temp temp exp in
         wordLang_Seq prog (wordLang_Inst (asm_Mem asm_Load tar
           (Addr temp ((n2w 0)))))))
        | (c,(tar:num),(temp:num),(wordLang_Const w)) ->
          (wordLang_Inst (asm_Const tar w))
        | (c,(tar:num),(temp:num),(wordLang_Var v)) ->
       wordLang_Move 0 [tar,v]
        | (c,tar,temp,(wordLang_Lookup store_name)) ->
       wordLang_Get tar store_name
        // All ops are binary branching
        | (c,tar,temp,(wordLang_Op op [e1; e2])) ->
       (if is_Lookup_CurrHeap e2 then
         (let p1 = inst_select_exp c temp temp e1 in
           wordLang_Seq p1 (wordLang_OpCurrHeap op tar temp)) else
             if is_Lookup_CurrHeap e1 /\ ~(op = asm_Sub) then
         (let p2 = inst_select_exp c temp temp e2 in
           wordLang_Seq p2 (wordLang_OpCurrHeap op tar temp)) else
       let p1 = inst_select_exp c temp temp e1 in
       match e2 with wordLang_Const w ->
         // t = r op const
         (if asm_config_valid_imm c (INL op) w then
           wordLang_Seq p1 (wordLang_Inst (asm_Arith (asm_Binop op
             tar temp (Imm w)))) else
          // t = r + const --> t = r - const
          if op = asm_Add /\ asm_config_valid_imm c (INL asm_Sub)
            (--w) then
           wordLang_Seq p1 (wordLang_Inst (asm_Arith (asm_Binop
             asm_Sub tar temp (Imm (--w))))) else
           // no immediates
           let p2 = wordLang_Inst (asm_Const (temp + 1) w) in
           wordLang_Seq p1 (wordLang_Seq p2 (wordLang_Inst
             (asm_Arith (asm_Binop op tar temp (Reg (temp + 1))))))) |
             _12 ->
         (let p2 = inst_select_exp c (temp + 1) (temp + 1) e2 in
         wordLang_Seq p1 (wordLang_Seq p2 (wordLang_Inst (asm_Arith
           (asm_Binop op tar temp (Reg (temp + 1))))))))
        | (c,tar,temp,(wordLang_Shift sh exp e1)) ->
       (match e1 with wordLang_Const shift_len ->
           (let n = w2n shift_len in
             if (n < dimindex (:'a)) then
               (let prog = inst_select_exp c temp temp exp in
                 if n = 0 then
                   wordLang_Seq prog (wordLang_Move 0 [tar,temp])
                     else
                    wordLang_Seq prog (wordLang_Inst (asm_Arith
                      (asm_Shift sh tar temp (Imm (n2w n)))))) else
               wordLang_Inst (asm_Const tar (n2w 0))) | _13 ->
         (let p = inst_select_exp c temp temp exp in
         let p1 = inst_select_exp c (temp + 1) (temp + 1) e1 in
         wordLang_Seq p (wordLang_Seq p1 (wordLang_Inst (asm_Arith
           (asm_Shift sh tar temp (Reg (temp + 1))))))))
        // Make it total
        | (_14,_15,_16,_17) -> wordLang_Skip`];;

let inst_select_exp_pmatch = prove
 (`!c tar temp exp.
   inst_select_exp (c:'a asm_config) tar temp exp =
   (match exp with
     wordLang_Load (wordLang_Op asm_Add [exp'; wordLang_Const w]) ->
       (if asm_offset_ok 0 (asm_config_addr_offset c) w then
         let prog = inst_select_exp c temp temp exp' in
           wordLang_Seq prog (wordLang_Inst (asm_Mem asm_Load tar
             (Addr temp w))) else
         (let prog = inst_select_exp c temp temp (wordLang_Op asm_Add
           [exp'; wordLang_Const w]) in
           wordLang_Seq prog (wordLang_Inst (asm_Mem asm_Load tar
             (Addr temp ((n2w 0))))))) | wordLang_Load exp ->
       (let prog = inst_select_exp c temp temp exp in
       wordLang_Seq prog (wordLang_Inst (asm_Mem asm_Load tar (Addr
         temp ((n2w 0)))))) | wordLang_Const w -> wordLang_Inst
         (asm_Const tar w) | wordLang_Var v ->
     wordLang_Move 0 [tar,v] | wordLang_Lookup store_name ->
     wordLang_Get tar store_name |
     // All ops are binary branching
     wordLang_Op op [e1; e2] ->
     (if is_Lookup_CurrHeap e2 then
       (let p1 = inst_select_exp c temp temp e1 in
         wordLang_Seq p1 (wordLang_OpCurrHeap op tar temp)) else if
           is_Lookup_CurrHeap e1 /\ ~(op = asm_Sub) then
       (let p2 = inst_select_exp c temp temp e2 in
         wordLang_Seq p2 (wordLang_OpCurrHeap op tar temp)) else
      match e2 with
       wordLang_Const w ->
       // t = r op const
       (if asm_config_valid_imm c (INL op) w then
         wordLang_Seq (inst_select_exp c temp temp e1) (wordLang_Inst
           (asm_Arith (asm_Binop op tar temp (Imm w)))) else
        // t = r + const --> t = r - const
        if op = asm_Add /\ asm_config_valid_imm c (INL asm_Sub) (--w)
          then
         wordLang_Seq (inst_select_exp c temp temp e1) (wordLang_Inst
           (asm_Arith (asm_Binop asm_Sub tar temp (Imm (--w))))) else
         // no immediates
         let p2 = wordLang_Inst (asm_Const (temp + 1) w) in
         wordLang_Seq (inst_select_exp c temp temp e1) (wordLang_Seq
           p2 (wordLang_Inst (asm_Arith (asm_Binop op tar temp (Reg
           (temp + 1))))))) | _18 ->
       (let p2 = inst_select_exp c (temp + 1) (temp + 1) e2 in
       wordLang_Seq (inst_select_exp c temp temp e1) (wordLang_Seq p2
         (wordLang_Inst (asm_Arith (asm_Binop op tar temp (Reg (temp +
         1)))))))) | wordLang_Shift sh exp e1 ->
    (match e1 with wordLang_Const shift_len ->
         (let n = w2n shift_len in
           if (n < dimindex (:'a)) then
             (let prog = inst_select_exp c temp temp exp in
               if n = 0 then
                 wordLang_Seq prog (wordLang_Move 0 [tar,temp]) else
                  wordLang_Seq prog (wordLang_Inst (asm_Arith
                    (asm_Shift sh tar temp (Imm (n2w n)))))) else
             wordLang_Inst (asm_Const tar (n2w 0))) | _19 ->
       (let p = inst_select_exp c temp temp exp in
       let p1 = inst_select_exp c (temp + 1) (temp + 1) e1 in
       wordLang_Seq p (wordLang_Seq p1 (wordLang_Inst (asm_Arith
         (asm_Shift sh tar temp (Reg (temp + 1)))))))) |
     // Make it total
     _20 -> wordLang_Skip)`,
  CHEAT_TAC);;

(*

First munch
EVAL ``inst_select_exp``
 x64_config 5 5 (Load (Op Add [Const 400w; Var 6]))``
EVAL ``inst_select_exp x64_config 5 5 (Load (Op Add [Const 99999999999w; Var 6]))``

Second munch
EVAL ``inst_select_exp x64_config 0 99
EVAL ``(pull_exp (Op And [Const (99w:64 word); Op Add [Op Add [];Op Or []]]))``
*)

(*Flattens all expressions in program, temp must a fresh var*)
let _ = size_thms "wordLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let inst_select_def,inst_select_ind = define_wf
  `MEASURE (\(x0,x1,x2). wordLang_prog_size (\x. 0) x2)`
  [`inst_select c temp prog =
        match prog with
          wordLang_Assign v exp ->
       (inst_select_exp c v temp o flatten_exp o pull_exp) exp
        | (wordLang_Set store exp) ->
       (let prog = (inst_select_exp c temp temp o flatten_exp o
         pull_exp) exp in
       wordLang_Seq prog (wordLang_Set store (wordLang_Var temp)))
        | (wordLang_Store exp var) ->
       (let exp = (flatten_exp o pull_exp) exp in
       match exp with wordLang_Op asm_Add [exp'; wordLang_Const w]
         ->
         (if (\c. asm_offset_ok 0 (asm_config_addr_offset c)) c w
           then
           let prog = inst_select_exp c temp temp exp' in
             wordLang_Seq prog (wordLang_Inst (asm_Mem asm_Store var
               (Addr temp w))) else
           let prog = inst_select_exp c temp temp exp in
             wordLang_Seq prog (wordLang_Inst (asm_Mem asm_Store var
               (Addr temp ((n2w 0)))))) | _21 ->
         (let prog = inst_select_exp c temp temp exp in
         wordLang_Seq prog (wordLang_Inst (asm_Mem asm_Store var
           (Addr temp ((n2w 0)))))))
        | (wordLang_Seq p1 p2) ->
       wordLang_Seq (inst_select c temp p1) (inst_select c temp p2)
        | (wordLang_MustTerminate p1) ->
       wordLang_MustTerminate (inst_select c temp p1)
        | (wordLang_ShareInst op v exp) ->
       (let exp = (flatten_exp o pull_exp) exp in
       match exp with wordLang_Op asm_Add [exp'; wordLang_Const w]
         ->
         (if ((op = wordLang_Load \/ op = wordLang_Store) /\ (\c.
           asm_offset_ok 0 (asm_config_addr_offset c)) c w) \/
             ((op = asm_Load32 \/ op = asm_Store32) /\ (\c.
               asm_offset_ok 0 (asm_config_addr_offset c)) c w) \/
             ((op = asm_Load16 \/ op = asm_Store16) /\ (\c.
               asm_offset_ok 0 (asm_config_hw_offset c)) c w) \/
             ((op = asm_Load8 \/ op = asm_Store8) /\ (\c.
               asm_offset_ok 0 (asm_config_byte_offset c)) c w) then
           let prog = inst_select_exp c temp temp exp' in
             wordLang_Seq prog (wordLang_ShareInst op v (wordLang_Op
               asm_Add [wordLang_Var temp; wordLang_Const w])) else
           let prog = inst_select_exp c temp temp exp in
             wordLang_Seq prog (wordLang_ShareInst op v
               (wordLang_Var temp))) | _22 ->
         (let prog = inst_select_exp c temp temp exp in
         wordLang_Seq prog (wordLang_ShareInst op v (wordLang_Var
           temp))))
        | (wordLang_If cmp r1 ri c1 c2) ->
       wordLang_If cmp r1 ri (inst_select c temp c1) (inst_select c
         temp c2)
        | (wordLang_Call ret dest args handler) ->
       (let retsel =
         (match ret with
           NONE -> NONE | SOME (n,names,ret_handler,l1,l2) ->
           SOME (n,names,inst_select c temp ret_handler,l1,l2)) in
       let handlersel =
         (match handler with
           NONE -> NONE | SOME (n,h,l1,l2) -> SOME (n,inst_select c
             temp h,l1,l2)) in
       wordLang_Call retsel dest args handlersel)
        | (wordLang_Loop names body exit_names) ->
       wordLang_Loop names (inst_select c temp body) exit_names
        | prog -> prog`];;

let inst_select_pmatch = prove
 (`!c temp prog.
   inst_select c temp prog =
   (match prog with wordLang_Assign v exp ->
     (inst_select_exp c v temp o flatten_exp o pull_exp) exp |
       wordLang_Set store exp ->
     (let prog = (inst_select_exp c temp temp o flatten_exp o
       pull_exp) exp in
     wordLang_Seq prog (wordLang_Set store (wordLang_Var temp))) |
       wordLang_Store exp var ->
     (let exp = (flatten_exp o pull_exp) exp in
     match exp with wordLang_Op asm_Add [exp'; wordLang_Const w] ->
       (if asm_offset_ok 0 (asm_config_addr_offset c) w then
         let prog = inst_select_exp c temp temp exp' in
           wordLang_Seq prog (wordLang_Inst (asm_Mem asm_Store var
             (Addr temp w))) else
         let prog = inst_select_exp c temp temp exp in
           wordLang_Seq prog (wordLang_Inst (asm_Mem asm_Store var
             (Addr temp ((n2w 0)))))) | _23 ->
       (let prog = inst_select_exp c temp temp exp in
       wordLang_Seq prog (wordLang_Inst (asm_Mem asm_Store var (Addr
         temp ((n2w 0))))))) | wordLang_Seq p1 p2 ->
     wordLang_Seq (inst_select c temp p1) (inst_select c temp p2) |
       wordLang_MustTerminate p1 ->
     wordLang_MustTerminate (inst_select c temp p1) | (wordLang_If
       cmp r1 ri c1 c2) ->
       wordLang_If cmp r1 ri (inst_select c temp c1) (inst_select c
         temp c2) | wordLang_ShareInst op var exp ->
     (let exp = (flatten_exp o pull_exp) exp in
     match exp with wordLang_Op asm_Add [exp'; wordLang_Const w] ->
       (if ((op = wordLang_Load \/ op = wordLang_Store) /\
         asm_offset_ok 0 (asm_config_addr_offset c) w) \/
           ((op = asm_Load32 \/ op = asm_Store32) /\ asm_offset_ok 0
             (asm_config_addr_offset c) w) \/
           ((op = asm_Load16 \/ op = asm_Store16) /\ asm_offset_ok 0
             (asm_config_hw_offset c) w) \/
           ((op = asm_Load8 \/ op = asm_Store8) /\ asm_offset_ok 0
             (asm_config_byte_offset c) w) then
         let prog = inst_select_exp c temp temp exp' in
           wordLang_Seq prog (wordLang_ShareInst op var (wordLang_Op
             asm_Add [wordLang_Var temp; wordLang_Const w])) else
         let prog = inst_select_exp c temp temp exp in
           wordLang_Seq prog (wordLang_ShareInst op var (wordLang_Var
             temp))) | _24 ->
       (let prog = inst_select_exp c temp temp exp in
       wordLang_Seq prog (wordLang_ShareInst op var (wordLang_Var
         temp)))) | (wordLang_Call ret dest args handler) ->
     (let retsel =
       (match ret with
         NONE -> NONE | SOME (n,names,ret_handler,l1,l2) ->
         SOME (n,names,inst_select c temp ret_handler,l1,l2)) in
     let handlersel =
       (match handler with
         NONE -> NONE | SOME (n,h,l1,l2) -> SOME (n,inst_select c
           temp h,l1,l2)) in
     wordLang_Call retsel dest args handlersel) | (wordLang_Loop
       names body exit_names) ->
     wordLang_Loop names (inst_select c temp body) exit_names |
       prog -> prog)`,
  CHEAT_TAC);;

(*
  Convert all 3 register instructions to 2 register instructions
*)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let three_to_two_reg_def,three_to_two_reg_ind = define_wf
  `MEASURE (\x0. wordLang_prog_size (\x. 0) x0)`
  [`three_to_two_reg prog =
        match prog with
          wordLang_Inst (asm_Arith (asm_Binop bop r1 r2 ri)) ->
       wordLang_Seq (wordLang_Move 0 [r1,r2]) (wordLang_Inst
         (asm_Arith (asm_Binop bop r1 r1 ri)))
        | (wordLang_Inst (asm_Arith (asm_Shift l r1 r2 n))) ->
       wordLang_Seq (wordLang_Move 0 [r1,r2]) (wordLang_Inst
         (asm_Arith (asm_Shift l r1 r1 n)))
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
       (let retsel =
         (match ret with
           NONE -> NONE | SOME (n,names,ret_handler,l1,l2) ->
           SOME (n,names,three_to_two_reg ret_handler,l1,l2)) in
       let handlersel =
         (match handler with
           NONE -> NONE | SOME (n,h,l1,l2) -> SOME
             (n,three_to_two_reg h,l1,l2)) in
       wordLang_Call retsel dest args handlersel)
        | (wordLang_Loop names body exit_names) ->
       wordLang_Loop names (three_to_two_reg body) exit_names
        | prog -> prog`];;

let three_to_two_reg_pmatch = prove
 (`!prog.
   three_to_two_reg prog =
   (match prog with (wordLang_Inst (asm_Arith (asm_Binop bop r1 r2
     ri))) ->
     wordLang_Seq (wordLang_Move 0 [r1,r2]) (wordLang_Inst (asm_Arith
       (asm_Binop bop r1 r1 ri))) | (wordLang_Inst (asm_Arith (asm_Shift
       l r1 r2 n))) ->
     wordLang_Seq (wordLang_Move 0 [r1,r2]) (wordLang_Inst (asm_Arith
       (asm_Shift l r1 r1 n))) | (wordLang_Inst (asm_Arith (asm_AddCarry
       r1 r2 r3 r4))) ->
     wordLang_Seq (wordLang_Move 0 [r1,r2]) (wordLang_Inst (asm_Arith
       (asm_AddCarry r1 r1 r3 r4))) | (wordLang_Inst (asm_Arith
       (asm_AddOverflow r1 r2 r3 r4))) ->
     wordLang_Seq (wordLang_Move 0 [r1,r2]) (wordLang_Inst (asm_Arith
       (asm_AddOverflow r1 r1 r3 r4))) | (wordLang_Inst (asm_Arith
       (asm_SubOverflow r1 r2 r3 r4))) ->
     wordLang_Seq (wordLang_Move 0 [r1,r2]) (wordLang_Inst (asm_Arith
       (asm_SubOverflow r1 r1 r3 r4))) | (wordLang_OpCurrHeap bop r1 r2)
       ->
     wordLang_Seq (wordLang_Move 0 [r1,r2]) (wordLang_OpCurrHeap bop
       r1 r1) | (wordLang_Seq p1 p2) ->
     wordLang_Seq (three_to_two_reg p1) (three_to_two_reg p2) |
       (wordLang_MustTerminate p1) ->
     wordLang_MustTerminate (three_to_two_reg p1) | (wordLang_If cmp
       r1 ri c1 c2) ->
     wordLang_If cmp r1 ri (three_to_two_reg c1) (three_to_two_reg
       c2) | (wordLang_Call ret dest args handler) ->
     (let retsel =
       (match ret with
         NONE -> NONE | SOME (n,names,ret_handler,l1,l2) ->
         SOME (n,names,three_to_two_reg ret_handler,l1,l2)) in
     let handlersel =
       (match handler with
         NONE -> NONE | SOME (n,h,l1,l2) -> SOME (n,three_to_two_reg
           h,l1,l2)) in
     wordLang_Call retsel dest args handlersel) | (wordLang_Loop
       names body exit_names) ->
     wordLang_Loop names (three_to_two_reg body) exit_names | prog
       -> prog)`,
  CHEAT_TAC);;

let three_to_two_reg_prog_def = new_definition
  `three_to_two_reg_prog b prog =
     (if b then three_to_two_reg prog else prog)`;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["pmatch"];;
