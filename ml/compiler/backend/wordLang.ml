(* ======================================================== *)
(*  wordLang: ported from HOL4's
    compiler/backend/wordLangScript.sml
    A definition theory, with 15 definitions, 3 datatypes and 3
    theorems.  Needed by 41 files of the port.  *)
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

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "wordLang"
  ["stackLang"];;

new_type_abbrev("wordLang_shift",`: ast_shift`);;

let wordLang_exp_INDUCT,wordLang_exp_RECURSION = define_datatype
  "wordLang_exp = wordLang_Const ('a word) | wordLang_Var (num) | \
   wordLang_Lookup (store_name) | wordLang_Load (wordLang_exp) | \
   wordLang_Op (binop) (wordLang_exp list) | wordLang_Shift \
   (ast_shift) (wordLang_exp) (wordLang_exp)";;

(* HOL4 wordLangScript.sml:23: the overload ShiftN, which the port
   expands *)

(* HOL4 wordLangScript.sml:25-31: a theorem whose statement the port
   cannot state yet: MEM_IMP_exp_size *)

new_type_abbrev("cutsets",`: 1 spt#1 spt`);;
(* non-GCed cutset, GCed cutset *)

let wordLang_prog_INDUCT,wordLang_prog_RECURSION = define_datatype
  "wordLang_prog = wordLang_Skip | wordLang_Move (num) ((num#num) \
   list) | wordLang_Inst ('a asm_inst) | wordLang_Assign (num) ('a \
   wordLang_exp) | wordLang_Get (num) (store_name) | wordLang_Set \
   (store_name) ('a wordLang_exp) | wordLang_Store ('a wordLang_exp) \
   (num) | wordLang_MustTerminate (wordLang_prog) | wordLang_Call \
   ((num list#(1 spt#1 spt)#wordLang_prog#num#num) option) (num \
   option) (num list) ((num#wordLang_prog#num#num) option) \
   // target of call\n\
   // arguments\n\
   | \
   // return vars, cut-set, return-handler code, labels l1,l2\n\
   // handler: varname, exception-handler code, labels l1,l2\n\
   wordLang_Seq (wordLang_prog) (wordLang_prog) | wordLang_If (cmp) \
   (num) ('a asm_reg_imm) (wordLang_prog) (wordLang_prog) | \
   wordLang_Loop (1 spt) (wordLang_prog) (1 spt) | wordLang_Alloc \
   (num) (1 spt#1 spt) | wordLang_StoreConsts (num) (num) (num) (num) \
   ((bool#'a word) list) | wordLang_Raise (num) | wordLang_Return \
   (num) (num list) \
   // return lab, return values\n\
   | wordLang_Break (num) | wordLang_Continue (num) | wordLang_Tick | \
   wordLang_OpCurrHeap (binop) (num) (num) \
   // special case compiled well in stackLang\n\
   | wordLang_LocValue (num) (num) \
   // assign v1 := Loc v2 0\n\
   | wordLang_Install (num) (num) (num) (num) (1 spt#1 spt) \
   // code buffer start, length of new code,\n\
   // data buffer start, length of new data, cut-set\n\
   | wordLang_CodeBufferWrite (num) (num) \
   // code buffer address, byte to write\n\
   | wordLang_DataBufferWrite (num) (num) \
   // data buffer address, word to write\n\
   | wordLang_FFI (mlstring) (num) (num) (num) (num) (1 spt#1 spt) \
   // FFI name, conf_ptr, conf_len, array_ptr, array_len, cut-set\n\
   | wordLang_ShareInst (memop) (num) ('a wordLang_exp) \
   // memory operation, varname, expression for memory address";;

let raise_stub_location_def = new_definition
  `raise_stub_location = word_num_stubs - 2`;;
let wordLang_store_consts_stub_location_def = new_definition
  `wordLang_store_consts_stub_location = word_num_stubs - 1`;;

(* HOL4 wordLangScript.sml:77: a theorem that HOL4 states as the
   value of an ML expression: raise_stub_location_eq *)
(* HOL4 wordLangScript.sml:78: a theorem that HOL4 states as the
   value of an ML expression: store_consts_stub_location_eq *)

(* HOL4 wordLangScript.sml:80-82: code that the source has in a
   comment *)

(* Recursors for variables *)
let _ = size_thms "wordLang_exp";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let every_var_exp_def,every_var_exp_ind = define_wf
  `MEASURE (\(x0,x1). wordLang_exp_size (\x. 0) x1)`
  [`every_var_exp P expr =
        match expr with
          wordLang_Var num' -> P num'
        | (wordLang_Load exp) -> every_var_exp P exp
        | (wordLang_Op wop ls) -> ALL (every_var_exp P) ls
        | (wordLang_Shift sh e1 e2) -> (every_var_exp P e1 /\
          every_var_exp P e2)
        | expr -> T`];;

let every_var_imm_def = new_definition
  `every_var_imm P x2 =
        match x2 with
          Reg r -> P r
        | _1 -> T`;;

let every_var_inst_def = new_definition
  `every_var_inst P inst' =
        match inst' with
          asm_Const reg w -> P reg
        | (asm_Arith (asm_Binop bop r1 r2 ri)) ->
       (P r1 /\ P r2 /\ every_var_imm P ri)
        | (asm_Arith (asm_Shift shift' r1 r2 ri)) -> (P r1 /\ P r2 /\
          every_var_imm P ri)
        | (asm_Arith (asm_Div r1 r2 r3)) -> (P r1 /\ P r2 /\ P r3)
        | (asm_Arith (asm_AddCarry r1 r2 r3 r4)) -> (P r1 /\ P r2 /\
          P r3 /\ P r4)
        | (asm_Arith (asm_AddOverflow r1 r2 r3 r4)) -> (P r1 /\ P r2
          /\ P r3 /\ P r4)
        | (asm_Arith (asm_SubOverflow r1 r2 r3 r4)) -> (P r1 /\ P r2
          /\ P r3 /\ P r4)
        | (asm_Arith (asm_LongMul r1 r2 r3 r4)) -> (P r1 /\ P r2 /\ P
          r3 /\ P r4)
        | (asm_Arith (asm_LongDiv r1 r2 r3 r4 r5)) -> (P r1 /\ P r2
          /\ P r3 /\ P r4 /\ P r5)
        | (asm_Mem asm_Load r (Addr a w)) -> (P r /\ P a)
        | (asm_Mem asm_Store r (Addr a w)) -> (P r /\ P a)
        | (asm_Mem asm_Load32 r (Addr a w)) -> (P r /\ P a)
        | (asm_Mem asm_Store32 r (Addr a w)) -> (P r /\ P a)
        | (asm_Mem asm_Load8 r (Addr a w)) -> (P r /\ P a)
        | (asm_Mem asm_Store8 r (Addr a w)) -> (P r /\ P a)
        | (asm_FP (FPLess r d1 d2)) -> P r
        | (asm_FP (FPLessEqual r d1 d2)) -> P r
        | (asm_FP (FPEqual r d1 d2)) -> P r
        | (asm_FP (FPMovToReg r1 r2 d):'a asm_inst) ->
       (if dimindex (:'a) = 64 then P r1 else (P r1 /\ P r2))
        | (asm_FP (FPMovFromReg d r1 r2)) ->
       (if dimindex (:'a) = 64 then P r1 else (P r1 /\ P r2))
        | inst' -> T`;;
(*catchall*)

let every_name_def = new_definition
  `every_name P (t:1 spt#1 spt) <=>
   ALL P (MAP FST (toAList (FST t))) /\
   ALL P (MAP FST (toAList (SND t)))`;;

let _ = size_thms "wordLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let every_var_def,every_var_ind = define_wf
  `MEASURE (\(x0,x1). wordLang_prog_size (\x. 0) x1)`
  [`wordLang_every_var P p =
        match p with
          (wordLang_Skip:'a wordLang_prog) -> T
        | (wordLang_Move pri ls) -> (ALL P (MAP FST ls) /\ ALL P
          (MAP SND ls))
        | (wordLang_Inst i) -> every_var_inst P i
        | (wordLang_Assign num' exp) -> (P num' /\ every_var_exp P
          exp)
        | (wordLang_Get num' store) -> P num'
        | (wordLang_Store exp num') -> (P num' /\ every_var_exp P
          exp)
        | (wordLang_LocValue r _2) -> P r
        | (wordLang_Install r1 r2 r3 r4 names) -> (P r1 /\ P r2 /\ P
          r3 /\ P r4 /\ every_name P names)
        | (wordLang_CodeBufferWrite r1 r2) -> (P r1 /\ P r2)
        | (wordLang_DataBufferWrite r1 r2) -> (P r1 /\ P r2)
        | (wordLang_FFI ffi_index cptr clen ptr len names) ->
       (P cptr /\ P clen /\ P ptr /\ P len /\ every_name P names)
        | (wordLang_MustTerminate s1) -> wordLang_every_var P s1
        | (wordLang_Call ret dest args h) ->
       ((ALL P args) /\
       (match ret with
         NONE -> T | SOME (v,cutset,ret_handler,l1,l2) ->
         (ALL P v /\ every_name P cutset /\
         wordLang_every_var P ret_handler /\
         (match h with
           NONE -> T | SOME (v,prog,l1,l2) ->
           (P v /\
           wordLang_every_var P prog)))))
        | (wordLang_Seq s1 s2) -> (wordLang_every_var P s1 /\
          wordLang_every_var P s2)
        | (wordLang_If cmp r1 ri e2 e3) ->
       (P r1 /\ every_var_imm P ri /\ wordLang_every_var P e2 /\
         wordLang_every_var P e3)
        | (wordLang_Alloc num' numset) ->
       (P num' /\ every_name P numset)
        | (wordLang_StoreConsts a b c d ws) ->
       (P a /\ P b /\ P c /\ P d)
        | (wordLang_Raise num') -> P num'
        | (wordLang_Return num1 ns) -> (P num1 /\ ALL P ns)
        | (wordLang_OpCurrHeap _3 num1 num2) -> (P num1 /\ P num2)
        | wordLang_Tick -> T
        | (wordLang_Set n exp) -> every_var_exp P exp
        | (wordLang_ShareInst op num' exp) -> (P num' /\
          every_var_exp P exp)
        | (wordLang_Loop names body exit_names) ->
       (ALL P (MAP FST (toAList names)) /\ wordLang_every_var P body
         /\
        ALL P (MAP FST (toAList exit_names)))
        | p -> T`];;

(*Recursor for stack variables*)
let _ = size_thms "wordLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let every_stack_var_def,every_stack_var_ind = define_wf
  `MEASURE (\(x0,x1). wordLang_prog_size (\x. 0) x1)`
  [`every_stack_var P p =
        match p with
          wordLang_FFI ffi_index cptr clen ptr len names ->
       every_name P names
        | (wordLang_Install _4 _5 _6 _7 names) ->
       every_name P names
        | (wordLang_Call ret dest args h) ->
       (match ret with
         NONE -> T | SOME (v,cutset,ret_handler,l1,l2) ->
         every_name P cutset /\
         every_stack_var P ret_handler /\
       (match h with
         // Does not check the case where Calls are ill-formed
         NONE -> T | SOME (v,prog,l1,l2) ->
         every_stack_var P prog))
        | (wordLang_Alloc num' numset) ->
       every_name P numset
        | (wordLang_MustTerminate s1) ->
       every_stack_var P s1
        | (wordLang_Seq s1 s2) ->
       (every_stack_var P s1 /\ every_stack_var P s2)
        | (wordLang_If cmp r1 ri e2 e3) ->
       (every_stack_var P e2 /\ every_stack_var P e3)
        | (wordLang_Loop names body exit_names) ->
       every_stack_var P body
        | p -> T`];;

(*Find the maximum variable*)
let _ = size_thms "wordLang_exp";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let max_var_exp_def,max_var_exp_ind = define_wf
  `MEASURE (\x0. wordLang_exp_size (\x. 0) x0)`
  [`max_var_exp exp =
        match exp with
          wordLang_Var num' -> num'
        | (wordLang_Load exp) -> max_var_exp exp
        | (wordLang_Op wop ls) -> MAX_LIST (MAP (max_var_exp) ls)
        | (wordLang_Shift sh exp1 exp2) -> MAX (max_var_exp exp1)
          (max_var_exp exp2)
        | exp -> (0:num)`];;

let max_var_inst_def = new_definition
  `max_var_inst x1 =
        match x1 with
          asm_Skip -> 0
        | (wordLang_Const reg w) -> reg
        | (asm_Arith (asm_Binop bop r1 r2 ri)) ->
       (match ri with Reg r -> max3 r1 r2 r | _8 -> MAX r1 r2)
        | (asm_Arith (asm_Shift shift' r1 r2 n)) ->
       (match n with Reg r -> max3 r1 r2 r | _9 -> MAX r1 r2)
        | (asm_Arith (asm_Div r1 r2 r3)) -> max3 r1 r2 r3
        | (asm_Arith (asm_AddCarry r1 r2 r3 r4)) -> MAX (MAX r1 r2)
          (MAX r3 r4)
        | (asm_Arith (asm_AddOverflow r1 r2 r3 r4)) -> MAX (MAX r1
          r2) (MAX r3 r4)
        | (asm_Arith (asm_SubOverflow r1 r2 r3 r4)) -> MAX (MAX r1
          r2) (MAX r3 r4)
        | (asm_Arith (asm_LongMul r1 r2 r3 r4)) -> MAX (MAX r1 r2)
          (MAX r3 r4)
        | (asm_Arith (asm_LongDiv r1 r2 r3 r4 r5)) -> MAX (MAX (MAX
          r1 r2) (MAX r3 r4)) r5
        | (asm_Mem asm_Load r (Addr a w)) -> MAX a r
        | (asm_Mem asm_Store r (Addr a w)) -> MAX a r
        | (asm_Mem asm_Load32 r (Addr a w)) -> MAX a r
        | (asm_Mem asm_Store32 r (Addr a w)) -> MAX a r
        | (asm_Mem asm_Load8 r (Addr a w)) -> MAX a r
        | (asm_Mem asm_Store8 r (Addr a w)) -> MAX a r
        | (asm_FP (FPLess r f1 f2)) -> r
        | (asm_FP (FPLessEqual r f1 f2)) -> r
        | (asm_FP (FPEqual r f1 f2)) -> r
        | (asm_FP (FPMovToReg r1 r2 d):'a asm_inst) ->
       (if dimindex (:'a) = 64 then r1 else MAX r1 r2)
        | (asm_FP (FPMovFromReg d r1 r2)) ->
       (if dimindex (:'a) = 64 then r1 else MAX r1 r2)
        | _10 -> 0`;;

let cutsets_max_def = new_definition
  `cutsets_max (c:1 spt#1 spt) =
     MAX (MAX_LIST (MAP FST (toAList (FST c)))) (MAX_LIST (MAP FST
       (toAList (SND c))))`;;

let _ = size_thms "wordLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let max_var_def,max_var_ind = define_wf
  `MEASURE (\x0. wordLang_prog_size (\x. 0) x0)`
  [`max_var p =
        match p with
          wordLang_Skip -> 0
        | (wordLang_Move pri ls) ->
       MAX_LIST (APPEND (MAP FST ls) (MAP SND ls))
        | (wordLang_Inst i) -> max_var_inst i
        | (wordLang_Assign num' exp) -> MAX num' (max_var_exp exp)
        | (wordLang_Get num' store) -> num'
        | (wordLang_Store exp num') -> MAX num' (max_var_exp exp)
        | (wordLang_Call ret dest args h) ->
       (let n = MAX_LIST args in
       match ret with
         NONE -> n | SOME (v,cutset,ret_handler,l1,l2) ->
         (let cutset_max = MAX n (cutsets_max cutset) in
         let ret_max = max3 (MAX_LIST v) cutset_max (max_var
           ret_handler) in
         (match h with
           NONE -> ret_max | SOME (v,prog,l1,l2) ->
           max3 v ret_max (max_var prog))))
        | (wordLang_Seq s1 s2) -> MAX (max_var s1) (max_var s2)
        | (wordLang_MustTerminate s1) -> max_var s1
        | (wordLang_If cmp r1 ri e2 e3) ->
       (let r = (match ri with Reg r -> MAX r r1 | _11 -> r1) in
         max3 r (max_var e2) (max_var e3))
        | (wordLang_Alloc num' numset) ->
       MAX num' (cutsets_max numset)
        | (wordLang_StoreConsts a b c d ws) ->
       MAX_LIST [a; b; c; d]
        | (wordLang_Install r1 r2 r3 r4 numset) ->
       (MAX_LIST [r1; r2; r3; r4; cutsets_max numset])
        | (wordLang_CodeBufferWrite r1 r2) ->
       MAX r1 r2
        | (wordLang_DataBufferWrite r1 r2) ->
       MAX r1 r2
        | (wordLang_FFI ffi_index ptr1 len1 ptr2 len2 numset) ->
       MAX_LIST [ptr1; len1; ptr2; len2; cutsets_max numset]
        | (wordLang_Raise num') -> num'
        | (wordLang_OpCurrHeap _12 num1 num2) -> MAX num1 num2
        | (wordLang_Return num1 ns) -> MAX_LIST (CONS num1 ns)
        | wordLang_Tick -> 0
        | (wordLang_LocValue r l1) -> r
        | (wordLang_Set n exp) -> max_var_exp exp
        | (wordLang_ShareInst op num' exp) -> MAX num' (max_var_exp
          exp)
        | (wordLang_Loop names body exit_names) ->
       max3 (MAX_LIST (MAP FST (toAList names)))
            (max_var body)
            (MAX_LIST (MAP FST (toAList exit_names)))
        | p -> 0`];;

let word_op_def = new_definition
  `wordLang_word_op op (ws:('a word) list) =
     (match (op,ws) with (asm_And,ws) -> SOME (ITLIST word_and ws
       (word_not (n2w 0))) | (asm_Add,ws) -> SOME (ITLIST word_add ws
       (n2w 0)) | (asm_Or,ws) -> SOME (ITLIST word_or ws (n2w 0)) |
       (asm_Xor,ws) -> SOME (ITLIST word_xor ws (n2w 0)) |
       (asm_Sub,[w1; w2]) -> SOME (w1 - w2) | _13 -> NONE)`;;

let word_sh_def = new_definition
  `word_sh sh (w:'a word) n =
     (if ~(n = 0) /\ n >= dimindex (:'a) then NONE else
       match sh with Lsl -> SOME (w << n) | Lsr -> SOME (w >>> n)
         | Asr -> SOME (w >> n) | Ror -> SOME (word_ror w n))`;;

let exp_to_addr_def = new_definition
  `exp_to_addr x1 =
        match x1 with
          wordLang_Var ad -> SOME (Addr ad (n2w 0))
        | (wordLang_Op asm_Add [wordLang_Var ad; wordLang_Const
          offset]) -> SOME (Addr ad offset)
        | _14 -> NONE`;;

(* HOL4 wordLangScript.sml:329: the overload shift, which the port
   expands *)

let word_loc_INDUCT,word_loc_RECURSION = define_datatype
  "word_loc = wordLang_Word ('a word) | wordLang_Loc (num) (num)";;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
