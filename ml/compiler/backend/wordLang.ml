(* ======================================================== *)
(*  wordLang: ported from HOL4's
    compiler/backend/wordLangScript.sml  *)
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

new_type_abbrev("wordLang_shift",`: ast_shift`);;

let wordLang_exp_INDUCT,wordLang_exp_RECURSION = define_datatype
  "wordLang_exp = wordLang_Const ('a word) | wordLang_Var (num) | \
   wordLang_Lookup (store_name) | wordLang_Load (wordLang_exp) | \
   wordLang_Op (binop) (wordLang_exp list) | wordLang_Shift \
   (ast_shift) (wordLang_exp) (wordLang_exp)";;
hol4_overload "Const" "wordLang_Const";;
hol4_overload "Var" "wordLang_Var";;
hol4_overload "Lookup" "wordLang_Lookup";;
hol4_overload "Load" "wordLang_Load";;
hol4_overload "Op" "wordLang_Op";;
hol4_overload "Shift" "wordLang_Shift";;

(* HOL4 overload (expanded in the port):
     ShiftN = λsh e n. Shift sh e (Const (n2w n)) *)

new_type_abbrev("cutsets",`: 1 spt#1 spt`);;

let wordLang_prog_INDUCT,wordLang_prog_RECURSION = define_datatype
  "wordLang_prog = wordLang_Skip | wordLang_Move (num) ((num#num) \
   list) | wordLang_Inst ('a asm_inst) | wordLang_Assign (num) ('a \
   wordLang_exp) | wordLang_Get (num) (store_name) | wordLang_Set \
   (store_name) ('a wordLang_exp) | wordLang_Store ('a wordLang_exp) \
   (num) | wordLang_MustTerminate (wordLang_prog) | wordLang_Call \
   ((num list#(1 spt#1 spt)#wordLang_prog#num#num) option) (num \
   option) (num list) ((num#wordLang_prog#num#num) option) | \
   wordLang_Seq (wordLang_prog) (wordLang_prog) | wordLang_If (cmp) \
   (num) ('a asm_reg_imm) (wordLang_prog) (wordLang_prog) | \
   wordLang_Loop (1 spt) (wordLang_prog) (1 spt) | wordLang_Alloc \
   (num) (1 spt#1 spt) | wordLang_StoreConsts (num) (num) (num) (num) \
   ((bool#'a word) list) | wordLang_Raise (num) | wordLang_Return \
   (num) (num list) | wordLang_Break (num) | wordLang_Continue (num) \
   | wordLang_Tick | wordLang_OpCurrHeap (binop) (num) (num) | \
   wordLang_LocValue (num) (num) | wordLang_Install (num) (num) (num) \
   (num) (1 spt#1 spt) | wordLang_CodeBufferWrite (num) (num) | \
   wordLang_DataBufferWrite (num) (num) | wordLang_FFI (mlstring) \
   (num) (num) (num) (num) (1 spt#1 spt) | wordLang_ShareInst (memop) \
   (num) ('a wordLang_exp)";;
hol4_overload "Skip" "wordLang_Skip";;
hol4_overload "Move" "wordLang_Move";;
hol4_overload "Inst" "wordLang_Inst";;
hol4_overload "Assign" "wordLang_Assign";;
hol4_overload "Get" "wordLang_Get";;
hol4_overload "Set" "wordLang_Set";;
hol4_overload "Store" "wordLang_Store";;
hol4_overload "MustTerminate" "wordLang_MustTerminate";;
hol4_overload "Call" "wordLang_Call";;
hol4_overload "Seq" "wordLang_Seq";;
hol4_overload "If" "wordLang_If";;
hol4_overload "Loop" "wordLang_Loop";;
hol4_overload "Alloc" "wordLang_Alloc";;
hol4_overload "StoreConsts" "wordLang_StoreConsts";;
hol4_overload "Raise" "wordLang_Raise";;
hol4_overload "Return" "wordLang_Return";;
hol4_overload "Break" "wordLang_Break";;
hol4_overload "Continue" "wordLang_Continue";;
hol4_overload "Tick" "wordLang_Tick";;
hol4_overload "OpCurrHeap" "wordLang_OpCurrHeap";;
hol4_overload "LocValue" "wordLang_LocValue";;
hol4_overload "Install" "wordLang_Install";;
hol4_overload "CodeBufferWrite" "wordLang_CodeBufferWrite";;
hol4_overload "DataBufferWrite" "wordLang_DataBufferWrite";;
hol4_overload "FFI" "wordLang_FFI";;
hol4_overload "ShareInst" "wordLang_ShareInst";;

let raise_stub_location_def = cake_define
  `raise_stub_location = word_num_stubs - 2`;;
let store_consts_stub_location_def = cake_define
  `wordLang_store_consts_stub_location = word_num_stubs - 1`;;
hol4_overload "store_consts_stub_location"
  "wordLang_store_consts_stub_location";;

(* wordLang uses syntactic invariants compared to stackLang that uses
   semantic flags
   Some of these are also used to EVAL (e.g. for the oracle)
*)

(* Recursors for variables *)
let every_var_exp_def = cake_define
  `every_var_exp P expr =
        match expr with
          wordLang_Var num' -> P num'
        | (Load exp) -> every_var_exp P exp
        | (wordLang_Op wop ls) -> EVERY (every_var_exp P) ls
        | (Shift sh e1 e2) -> (every_var_exp P e1 /\ every_var_exp P
          e2)
        | expr -> T`;;

let every_var_imm_def = cake_define
  `every_var_imm P x2 =
        match x2 with
          Reg r -> P r
        | _1 -> T`;;

let every_var_inst_def = cake_define
  `every_var_inst P inst =
        match inst with
          asm_Const reg w -> P reg
        | (Arith (asm_Binop bop r1 r2 ri)) ->
       (P r1 /\ P r2 /\ every_var_imm P ri)
        | (Arith (Shift shift' r1 r2 ri)) -> (P r1 /\ P r2 /\
          every_var_imm P ri)
        | (Arith (Div r1 r2 r3)) -> (P r1 /\ P r2 /\ P r3)
        | (Arith (asm_AddCarry r1 r2 r3 r4)) -> (P r1 /\ P r2 /\ P r3
          /\ P r4)
        | (Arith (asm_AddOverflow r1 r2 r3 r4)) -> (P r1 /\ P r2 /\ P
          r3 /\ P r4)
        | (Arith (asm_SubOverflow r1 r2 r3 r4)) -> (P r1 /\ P r2 /\ P
          r3 /\ P r4)
        | (Arith (asm_LongMul r1 r2 r3 r4)) -> (P r1 /\ P r2 /\ P r3
          /\ P r4)
        | (Arith (asm_LongDiv r1 r2 r3 r4 r5)) -> (P r1 /\ P r2 /\ P
          r3 /\ P r4 /\ P r5)
        | (asm_Mem Load r (Addr a w)) -> (P r /\ P a)
        | (asm_Mem Store r (Addr a w)) -> (P r /\ P a)
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

let every_name_def = cake_define
  `every_name P (t:1 spt#1 spt) <=>
   EVERY P (MAP FST (toAList (FST t))) /\
   EVERY P (MAP FST (toAList (SND t)))`;;

let every_var_def = cake_define
  `every_var P p =
        match p with
          (Skip:'a wordLang_prog) -> T
        | (wordLang_Move pri ls) -> (EVERY P (MAP FST ls) /\ EVERY P
          (MAP SND ls))
        | (Inst i) -> every_var_inst P i
        | (wordLang_Assign num' exp) -> (P num' /\ every_var_exp P
          exp)
        | (Get num' store) -> P num'
        | (Store exp num') -> (P num' /\ every_var_exp P exp)
        | (LocValue r _2) -> P r
        | (Install r1 r2 r3 r4 names) -> (P r1 /\ P r2 /\ P r3 /\ P
          r4 /\ every_name P names)
        | (CodeBufferWrite r1 r2) -> (P r1 /\ P r2)
        | (DataBufferWrite r1 r2) -> (P r1 /\ P r2)
        | (FFI ffi_index cptr clen ptr len names) ->
       (P cptr /\ P clen /\ P ptr /\ P len /\ every_name P names)
        | (wordLang_MustTerminate s1) -> every_var P s1
        | (Call ret dest args h) ->
       ((EVERY P args) /\
       (match ret with
         NONE -> T | SOME (v,cutset,ret_handler,l1,l2) ->
         (EVERY P v /\ every_name P cutset /\
         every_var P ret_handler /\
         (match h with
           NONE -> T | SOME (v,prog,l1,l2) ->
           (P v /\
           every_var P prog)))))
        | (Seq s1 s2) -> (every_var P s1 /\ every_var P s2)
        | (If cmp r1 ri e2 e3) ->
       (P r1 /\ every_var_imm P ri /\ every_var P e2 /\ every_var P
         e3)
        | (Alloc num' numset) ->
       (P num' /\ every_name P numset)
        | (StoreConsts a b c d ws) ->
       (P a /\ P b /\ P c /\ P d)
        | (Raise num') -> P num'
        | (Return num1 ns) -> (P num1 /\ EVERY P ns)
        | (OpCurrHeap _3 num1 num2) -> (P num1 /\ P num2)
        | Tick -> T
        | (Set n exp) -> every_var_exp P exp
        | (wordLang_ShareInst op num' exp) -> (P num' /\
          every_var_exp P exp)
        | (wordLang_Loop names body exit_names) ->
       (EVERY P (MAP FST (toAList names)) /\ every_var P body /\
        EVERY P (MAP FST (toAList exit_names)))
        | p -> T`;;

(*Recursor for stack variables*)
let every_stack_var_def = cake_define
  `every_stack_var P p =
        match p with
          wordLang_FFI ffi_index cptr clen ptr len names ->
       every_name P names
        | (Install _4 _5 _6 _7 names) ->
       every_name P names
        | (Call ret dest args h) ->
       (match ret with
         NONE -> T | SOME (v,cutset,ret_handler,l1,l2) ->
         every_name P cutset /\
         every_stack_var P ret_handler /\
       (match h with
         NONE -> T | SOME (v,prog,l1,l2) ->
         every_stack_var P prog))
        | (Alloc num' numset) ->
       every_name P numset
        | (wordLang_MustTerminate s1) ->
       every_stack_var P s1
        | (Seq s1 s2) ->
       (every_stack_var P s1 /\ every_stack_var P s2)
        | (If cmp r1 ri e2 e3) ->
       (every_stack_var P e2 /\ every_stack_var P e3)
        | (wordLang_Loop names body exit_names) ->
       every_stack_var P body
        | p -> T`;;

(*Find the maximum variable*)
let max_var_exp_def = cake_define
  `max_var_exp exp =
        match exp with
          wordLang_Var num' -> num'
        | (Load exp) -> max_var_exp exp
        | (wordLang_Op wop ls) -> MAX_LIST (MAP (max_var_exp) ls)
        | (Shift sh exp1 exp2) -> MAX (max_var_exp exp1) (max_var_exp
          exp2)
        | exp -> (0:num)`;;

let max_var_inst_def = cake_define
  `max_var_inst x1 =
        match x1 with
          asm_Skip -> 0
        | (Const reg w) -> reg
        | (Arith (asm_Binop bop r1 r2 ri)) ->
       (match ri with Reg r -> max3 r1 r2 r | _8 -> MAX r1 r2)
        | (Arith (Shift shift' r1 r2 n)) ->
       (match n with Reg r -> max3 r1 r2 r | _9 -> MAX r1 r2)
        | (Arith (Div r1 r2 r3)) -> max3 r1 r2 r3
        | (Arith (asm_AddCarry r1 r2 r3 r4)) -> MAX (MAX r1 r2) (MAX
          r3 r4)
        | (Arith (asm_AddOverflow r1 r2 r3 r4)) -> MAX (MAX r1 r2)
          (MAX r3 r4)
        | (Arith (asm_SubOverflow r1 r2 r3 r4)) -> MAX (MAX r1 r2)
          (MAX r3 r4)
        | (Arith (asm_LongMul r1 r2 r3 r4)) -> MAX (MAX r1 r2) (MAX
          r3 r4)
        | (Arith (asm_LongDiv r1 r2 r3 r4 r5)) -> MAX (MAX (MAX r1
          r2) (MAX r3 r4)) r5
        | (asm_Mem Load r (Addr a w)) -> MAX a r
        | (asm_Mem Store r (Addr a w)) -> MAX a r
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

let cutsets_max_def = cake_define
  `cutsets_max (c:1 spt#1 spt) =
     MAX (MAX_LIST (MAP FST (toAList (FST c)))) (MAX_LIST (MAP FST
       (toAList (SND c))))`;;

let max_var_def = cake_define
  `max_var p =
        match p with
          wordLang_Skip -> 0
        | (wordLang_Move pri ls) ->
       MAX_LIST (MAP FST ls ++ MAP SND ls)
        | (Inst i) -> max_var_inst i
        | (wordLang_Assign num' exp) -> MAX num' (max_var_exp exp)
        | (Get num' store) -> num'
        | (Store exp num') -> MAX num' (max_var_exp exp)
        | (Call ret dest args h) ->
       (let n = MAX_LIST args in
       match ret with
         NONE -> n | SOME (v,cutset,ret_handler,l1,l2) ->
         (let cutset_max = MAX n (cutsets_max cutset) in
         let ret_max = max3 (MAX_LIST v) cutset_max (max_var
           ret_handler) in
         (match h with
           NONE -> ret_max | SOME (v,prog,l1,l2) ->
           max3 v ret_max (max_var prog))))
        | (Seq s1 s2) -> MAX (max_var s1) (max_var s2)
        | (wordLang_MustTerminate s1) -> max_var s1
        | (If cmp r1 ri e2 e3) ->
       (let r = (match ri with Reg r -> MAX r r1 | _11 -> r1) in
         max3 r (max_var e2) (max_var e3))
        | (Alloc num' numset) ->
       MAX num' (cutsets_max numset)
        | (StoreConsts a b c d ws) ->
       MAX_LIST [a; b; c; d]
        | (Install r1 r2 r3 r4 numset) ->
       (MAX_LIST [r1; r2; r3; r4; cutsets_max numset])
        | (CodeBufferWrite r1 r2) ->
       MAX r1 r2
        | (DataBufferWrite r1 r2) ->
       MAX r1 r2
        | (FFI ffi_index ptr1 len1 ptr2 len2 numset) ->
       MAX_LIST [ptr1; len1; ptr2; len2; cutsets_max numset]
        | (Raise num') -> num'
        | (OpCurrHeap _12 num1 num2) -> MAX num1 num2
        | (Return num1 ns) -> MAX_LIST (num1 :: ns)
        | Tick -> 0
        | (LocValue r l1) -> r
        | (Set n exp) -> max_var_exp exp
        | (wordLang_ShareInst op num' exp) -> MAX num' (max_var_exp
          exp)
        | (Loop names body exit_names) ->
       max3 (MAX_LIST (MAP FST (toAList names)))
            (max_var body)
            (MAX_LIST (MAP FST (toAList exit_names)))
        | p -> 0`;;

let word_op_def = cake_define
  `wordLang_word_op op (ws:('a word) list) =
     (match (op,ws) with (And,ws) -> SOME (ITLIST word_and ws
       (word_not (n2w 0))) | (Add,ws) -> SOME (ITLIST word_add ws
       (n2w 0)) | (Or,ws) -> SOME (ITLIST word_or ws (n2w 0)) |
       (Xor,ws) -> SOME (ITLIST word_xor ws (n2w 0)) | (Sub,[w1; w2])
       -> SOME (w1 - w2) | _13 -> NONE)`;;
hol4_overload "word_op" "wordLang_word_op";;

let word_sh_def = cake_define
  `word_sh sh (w:'a word) n =
     (if ~(n = 0) /\ n >= dimindex (:'a) then NONE else
       match sh with Lsl -> SOME (w << n) | Lsr -> SOME (w >>> n)
         | Asr -> SOME (w >> n) | Ror -> SOME (word_ror w n))`;;

let exp_to_addr_def = cake_define
  `exp_to_addr x1 =
        match x1 with
          wordLang_Var ad -> SOME (Addr ad (n2w 0))
        | (wordLang_Op Add [Var ad; Const offset]) -> SOME (Addr ad
          offset)
        | _14 -> NONE`;;

(* HOL4 overload (expanded in the port):
     shift = backend_common$word_shift *)

let word_loc_INDUCT,word_loc_RECURSION = define_datatype
  "word_loc = wordLang_Word ('a word) | wordLang_Loc (num) (num)";;
hol4_overload "Word" "wordLang_Word";;
hol4_overload "Loc" "wordLang_Loc";;
