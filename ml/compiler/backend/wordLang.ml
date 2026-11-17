(* ======================================================== *)
(*  wordLang: ported from HOL4's
    compiler/backend/wordLangScript.sml
    A definition theory, with 15 definitions, 3 datatypes and 3
    theorems.  Needed by 45 files of the port.  *)
(* ======================================================== *)

(*
  The wordLang intermediate language consists of structured programs
  that operate over machine words, a list-like stack and a flat memory.
  This is the language where register allocation is performed.
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "wordLang"
  ["stackLang"];;

new_type_abbrev("word_shift",`:ast_shift`);;

let word_exp_INDUCT,word_exp_RECURSION = define_datatype
  "word_exp =
     word_Const ('a word)
   | word_Var num
   | word_Lookup store_name
   | word_Load word_exp
   | word_Op asm_binop (word_exp list)
   | word_Shift word_shift word_exp word_exp";;

(* HOL4 wordLangScript.sml:23: the overload ShiftN, which the port expands *)

make_size "word_exp";;
(* MEM_IMP_exp_size *)
let word_MEM_IMP_exp_size = prove
 (`!xs a. MEM a xs ==> (word_exp_size l a < (list_size o word_exp_size) l xs)`,
  CHEAT_TAC);;

new_type_abbrev("cutsets",`:misc_num_set#misc_num_set`);;
(* non-GCed cutset, GCed cutset *)

let word_prog_INDUCT,word_prog_RECURSION = define_datatype
  "word_prog =
     word_Skip
   | word_Move num ((num#num) list)
   | word_Inst ('a asm_inst)
   | word_Assign num ('a word_exp)
   | word_Get num store_name
   | word_Set store_name ('a word_exp)
   | word_Store ('a word_exp) num
   | word_MustTerminate word_prog
   | word_Call ((num list#cutsets#word_prog#num#num) option) (num option) (num
       list) ((num#word_prog#num#num) option)
     // target of call
     // arguments
     // return vars, cut-set, return-handler code, labels l1,l2
     // handler: varname, exception-handler code, labels l1,l2
   | word_Seq word_prog word_prog
   | word_If cmp num ('a asm_reg_imm) word_prog word_prog
   | word_Loop misc_num_set word_prog misc_num_set
   | word_Alloc num cutsets
   | word_StoreConsts num num num num ((bool#'a word) list)
   | word_Raise num
   | word_Return num (num list)
     // return lab, return values
   | word_Break num
   | word_Continue num
   | word_Tick
   | word_OpCurrHeap asm_binop num num
     // special case compiled well in stackLang
   | word_LocValue num num
     // assign v1 := Loc v2 0
   | word_Install num num num num cutsets
     // code buffer start, length of new code,
     // data buffer start, length of new data, cut-set
   | word_CodeBufferWrite num num
     // code buffer address, byte to write
   | word_DataBufferWrite num num
     // data buffer address, word to write
   | word_FFI mlstring num num num num cutsets
     // FFI name, conf_ptr, conf_len, array_ptr, array_len, cut-set
   | word_ShareInst memop num ('a word_exp)
     // memory operation, varname, expression for memory address
  ";;

let raise_stub_location_def = new_definition
  `raise_stub_location = word_num_stubs - 2`;;
let word_store_consts_stub_location_def = new_definition
  `word_store_consts_stub_location = word_num_stubs - 1`;;

let raise_stub_location_eq =
  CAKE_EVAL [raise_stub_location_def; word_num_stubs_def;
  stack_num_stubs_def] `raise_stub_location`;;
let word_store_consts_stub_location_eq =
  CAKE_EVAL [word_store_consts_stub_location_def; word_num_stubs_def;
  stack_num_stubs_def] `word_store_consts_stub_location`;;

(* HOL4 wordLangScript.sml:80-82: code that the source has in a comment *)

(* Recursors for variables *)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let every_var_exp_def,every_var_exp_ind = define_wf
  `MEASURE (\(x0,x1). word_exp_size (\x. 0) x1)`
  `every_var_exp P expr =
     match expr with
       word_Var num' -> P num'
     | word_Load exp -> every_var_exp P exp
     | word_Op wop ls -> ALL (every_var_exp P) ls
     | word_Shift sh e1 e2 -> (every_var_exp P e1 /\ every_var_exp P e2)
     | expr -> T`;;

let every_var_imm_def = new_definition
  `every_var_imm P x2 =
     match x2 with
       asm_Reg r -> P r
     | _ -> T`;;

let every_var_inst_def = new_definition
  `every_var_inst P inst =
     match inst with
       asm_Const reg w -> P reg
     | asm_Arith (asm_Binop bop r1 r2 ri) ->
       (P r1 /\ P r2 /\ every_var_imm P ri)
     | asm_Arith (asm_Shift shift' r1 r2 ri) -> (P r1 /\ P r2
       /\ every_var_imm P ri)
     | asm_Arith (asm_Div r1 r2 r3) -> (P r1 /\ P r2 /\ P r3)
     | asm_Arith (asm_AddCarry r1 r2 r3 r4) -> (P r1 /\ P r2 /\ P r3 /\ P
       r4)
     | asm_Arith (asm_AddOverflow r1 r2 r3 r4) -> (P r1 /\ P r2 /\ P r3 /\ P
       r4)
     | asm_Arith (asm_SubOverflow r1 r2 r3 r4) -> (P r1 /\ P r2 /\ P r3 /\ P
       r4)
     | asm_Arith (asm_LongMul r1 r2 r3 r4) -> (P r1 /\ P r2 /\ P r3 /\ P r4)
     | asm_Arith (asm_LongDiv r1 r2 r3 r4 r5) -> (P r1 /\ P r2 /\ P r3 /\ P
       r4 /\ P r5)
     | asm_Mem asm_Load r (Addr a w) -> (P r /\ P a)
     | asm_Mem asm_Store r (Addr a w) -> (P r /\ P a)
     | asm_Mem asm_Load32 r (Addr a w) -> (P r /\ P a)
     | asm_Mem asm_Store32 r (Addr a w) -> (P r /\ P a)
     | asm_Mem asm_Load8 r (Addr a w) -> (P r /\ P a)
     | asm_Mem asm_Store8 r (Addr a w) -> (P r /\ P a)
     | asm_FP (FPLess r d1 d2) -> P r
     | asm_FP (FPLessEqual r d1 d2) -> P r
     | asm_FP (FPEqual r d1 d2) -> P r
     | (asm_FP (FPMovToReg r1 r2 d):'a asm_inst) ->
       if dimindex (:'a) = 64 then P r1
       else (P r1 /\ P r2)
     | asm_FP (FPMovFromReg d r1 r2) ->
       if dimindex (:'a) = 64 then P r1
       else (P r1 /\ P r2)
     | inst -> T`;;
(*catchall*)

(* HOL4 wordLangScript.sml:127-131: the definition *)

make_size "word_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let every_var_def,every_var_ind = define_wf
  `MEASURE (\(x0,x1). word_prog_size (\x. 0) x1)`
  `word_every_var P p =
     match p with
       (word_Skip:'a word_prog) -> T
     | word_Move pri ls -> (ALL P (MAP FST ls) /\ ALL P (MAP SND ls))
     | word_Inst i -> every_var_inst P i
     | word_Assign num' exp -> (P num' /\ every_var_exp P exp)
     | word_Get num' store -> P num'
     | word_Store exp num' -> (P num' /\ every_var_exp P exp)
     | word_LocValue r _ -> P r
     | word_Install r1 r2 r3 r4 names -> (P r1 /\ P r2 /\ P r3 /\ P r4
       /\ every_name P names)
     | word_CodeBufferWrite r1 r2 -> (P r1 /\ P r2)
     | word_DataBufferWrite r1 r2 -> (P r1 /\ P r2)
     | word_FFI ffi_index cptr clen ptr len names ->
       (P cptr /\ P clen /\ P ptr /\ P len /\ every_name P names)
     | word_MustTerminate s1 -> word_every_var P s1
     | word_Call ret dest args h ->
       ((ALL P args) /\
       (match ret with
         NONE -> T
       | SOME (v,cutset,ret_handler,l1,l2) ->
         (ALL P v /\ every_name P cutset /\
         word_every_var P ret_handler /\
         (match h with
           NONE -> T
         | SOME (v,prog,l1,l2) ->
           (P v /\
           word_every_var P prog)))))
     | word_Seq s1 s2 -> (word_every_var P s1 /\ word_every_var P s2)
     | word_If cmp r1 ri e2 e3 ->
       (P r1 /\ every_var_imm P ri /\ word_every_var P e2 /\ word_every_var
         P e3)
     | word_Alloc num' numset ->
       (P num' /\ every_name P numset)
     | word_StoreConsts a b c d ws ->
       (P a /\ P b /\ P c /\ P d)
     | word_Raise num' -> P num'
     | word_Return num1 ns -> (P num1 /\ ALL P ns)
     | word_OpCurrHeap _ num1 num2 -> (P num1 /\ P num2)
     | word_Tick -> T
     | word_Set n exp -> every_var_exp P exp
     | word_ShareInst op num' exp -> (P num' /\ every_var_exp P exp)
     | word_Loop names body exit_names ->
       (ALL P (MAP FST (toAList names)) /\ word_every_var P body /\
        ALL P (MAP FST (toAList exit_names)))
     | p -> T`;;

(*Recursor for stack variables*)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let every_stack_var_def,every_stack_var_ind = define_wf
  `MEASURE (\(x0,x1). word_prog_size (\x. 0) x1)`
  `every_stack_var P p =
     match p with
       word_FFI ffi_index cptr clen ptr len names ->
       every_name P names
     | word_Install _ _ _ _ names ->
       every_name P names
     | word_Call ret dest args h ->
       (match ret with
         NONE -> T
       | SOME (v,cutset,ret_handler,l1,l2) ->
         every_name P cutset /\
         every_stack_var P ret_handler /\
       (match h with
         // Does not check the case where Calls are ill-formed
         NONE -> T
       | SOME (v,prog,l1,l2) ->
         every_stack_var P prog))
     | word_Alloc num' numset ->
       every_name P numset
     | word_MustTerminate s1 ->
       every_stack_var P s1
     | word_Seq s1 s2 ->
       (every_stack_var P s1 /\ every_stack_var P s2)
     | word_If cmp r1 ri e2 e3 ->
       (every_stack_var P e2 /\ every_stack_var P e3)
     | word_Loop names body exit_names ->
       every_stack_var P body
     | p -> T`;;

(*Find the maximum variable*)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let max_var_exp_def,max_var_exp_ind = define_wf
  `MEASURE (\x0. word_exp_size (\x. 0) x0)`
  `max_var_exp exp =
     match exp with
       word_Var num' -> num'
     | word_Load exp -> max_var_exp exp
     | word_Op wop ls -> MAX_LIST (MAP (max_var_exp) ls)
     | word_Shift sh exp1 exp2 -> MAX (max_var_exp exp1) (max_var_exp exp2)
     | exp -> (0:num)`;;

let max_var_inst_def = new_definition
  `max_var_inst x1 =
     match x1 with
       asm_Skip -> 0
     | asm_Const reg w -> reg
     | asm_Arith (asm_Binop bop r1 r2 ri) ->
       (match ri with asm_Reg r -> max3 r1 r2 r | _ -> MAX r1 r2)
     | asm_Arith (asm_Shift shift' r1 r2 n) ->
       (match n with asm_Reg r -> max3 r1 r2 r | _ -> MAX r1 r2)
     | asm_Arith (asm_Div r1 r2 r3) -> max3 r1 r2 r3
     | asm_Arith (asm_AddCarry r1 r2 r3 r4) -> MAX (MAX r1 r2) (MAX r3 r4)
     | asm_Arith (asm_AddOverflow r1 r2 r3 r4) -> MAX (MAX r1 r2) (MAX r3
       r4)
     | asm_Arith (asm_SubOverflow r1 r2 r3 r4) -> MAX (MAX r1 r2) (MAX r3
       r4)
     | asm_Arith (asm_LongMul r1 r2 r3 r4) -> MAX (MAX r1 r2) (MAX r3 r4)
     | asm_Arith (asm_LongDiv r1 r2 r3 r4 r5) -> MAX (MAX (MAX r1 r2) (MAX
       r3 r4)) r5
     | asm_Mem asm_Load r (Addr a w) -> MAX a r
     | asm_Mem asm_Store r (Addr a w) -> MAX a r
     | asm_Mem asm_Load32 r (Addr a w) -> MAX a r
     | asm_Mem asm_Store32 r (Addr a w) -> MAX a r
     | asm_Mem asm_Load8 r (Addr a w) -> MAX a r
     | asm_Mem asm_Store8 r (Addr a w) -> MAX a r
     | asm_FP (FPLess r f1 f2) -> r
     | asm_FP (FPLessEqual r f1 f2) -> r
     | asm_FP (FPEqual r f1 f2) -> r
     | (asm_FP (FPMovToReg r1 r2 d):'a asm_inst) ->
       if dimindex (:'a) = 64 then r1
       else MAX r1 r2
     | asm_FP (FPMovFromReg d r1 r2) ->
       if dimindex (:'a) = 64 then r1
       else MAX r1 r2
     | _ -> 0`;;

let cutsets_max_def = new_definition
  `cutsets_max (c:1 spt#1 spt) =
     MAX (MAX_LIST (MAP FST (toAList (FST c)))) (MAX_LIST (MAP FST
       (toAList (SND c))))`;;
add_simp cutsets_max_def;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let max_var_def,max_var_ind = define_wf
  `MEASURE (\x0. word_prog_size (\x. 0) x0)`
  `max_var p =
     match p with
       word_Skip -> 0
     | word_Move pri ls ->
       MAX_LIST (APPEND (MAP FST ls) (MAP SND ls))
     | word_Inst i -> max_var_inst i
     | word_Assign num' exp -> MAX num' (max_var_exp exp)
     | word_Get num' store -> num'
     | word_Store exp num' -> MAX num' (max_var_exp exp)
     | word_Call ret dest args h ->
       (let n = MAX_LIST args in
       match ret with
         NONE -> n
       | SOME (v,cutset,ret_handler,l1,l2) ->
         (let cutset_max = MAX n (cutsets_max cutset) in
         let ret_max = max3 (MAX_LIST v) cutset_max (max_var ret_handler) in
         (match h with
           NONE -> ret_max
         | SOME (v,prog,l1,l2) ->
           max3 v ret_max (max_var prog))))
     | word_Seq s1 s2 -> MAX (max_var s1) (max_var s2)
     | word_MustTerminate s1 -> max_var s1
     | word_If cmp r1 ri e2 e3 ->
       let r = (match ri with asm_Reg r -> MAX r r1 | _ -> r1) in
         max3 r (max_var e2) (max_var e3)
     | word_Alloc num' numset ->
       MAX num' (cutsets_max numset)
     | word_StoreConsts a b c d ws ->
       MAX_LIST [a; b; c; d]
     | word_Install r1 r2 r3 r4 numset ->
       (MAX_LIST [r1; r2; r3; r4; cutsets_max numset])
     | word_CodeBufferWrite r1 r2 ->
       MAX r1 r2
     | word_DataBufferWrite r1 r2 ->
       MAX r1 r2
     | word_FFI ffi_index ptr1 len1 ptr2 len2 numset ->
       MAX_LIST [ptr1; len1; ptr2; len2; cutsets_max numset]
     | word_Raise num' -> num'
     | word_OpCurrHeap _ num1 num2 -> MAX num1 num2
     | word_Return num1 ns -> MAX_LIST (CONS num1 ns)
     | word_Tick -> 0
     | word_LocValue r l1 -> r
     | word_Set n exp -> max_var_exp exp
     | word_ShareInst op num' exp -> MAX num' (max_var_exp exp)
     | word_Loop names body exit_names ->
       max3 (MAX_LIST (MAP FST (toAList names)))
            (max_var body)
            (MAX_LIST (MAP FST (toAList exit_names)))
     | p -> 0`;;

let word_op_def = new_definition
  `word_word_op op (ws:('a word) list) =
     match (op,ws) with (asm_And,ws) -> SOME (ITLIST word_and ws (word_not
       (n2w 0)))
     | (asm_Add,ws) -> SOME (ITLIST word_add ws (n2w 0))
     | (asm_Or,ws) -> SOME (ITLIST word_or ws (n2w 0))
     | (asm_Xor,ws) -> SOME (ITLIST word_xor ws (n2w 0))
     | (asm_Sub,[w1; w2]) -> SOME (w1 - w2)
     | _ -> NONE`;;

let word_sh_def = new_definition
  `word_sh sh (w:'a word) n =
     if ~(n = 0) /\ n >= dimindex (:'a) then NONE else match sh with Lsl ->
       SOME (w << n)
       | Lsr -> SOME (w >>> n)
       | Asr -> SOME (w >> n)
       | Ror -> SOME (word_ror w n)`;;

let exp_to_addr_def = new_definition
  `exp_to_addr x1' =
     match x1' with
       word_Var ad -> SOME (Addr ad (n2w 0))
     | word_Op asm_Add [word_Var ad; word_Const offset] -> SOME (Addr ad
       offset)
     | _ -> NONE`;;

(* HOL4 wordLangScript.sml:329: the overload shift, which the port expands *)

let word_loc_INDUCT,word_loc_RECURSION = define_datatype
  "word_loc =
     word_Word ('a word)
   | word_Loc num num";;

(* and the interface *)
let _ = unhide_overloads ();;
