(* ======================================================== *)
(*  wordConvs: ported from HOL4's
    compiler/backend/semantics/wordConvsScript.sml
    A definition theory, with 22 definitions and 23 theorems.
    Needed by 14 files of the port.  *)
(* ======================================================== *)

(*
  Syntactic properties used by wordLang across passes.
*)

needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sorting.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "wordConvs"
  ["asm"; "reg_alloc"; "wordLang"];;

let _ = do_list hide_constant ["inst"];;
(*** Mono and conj lemmas for every_var/every_stack_var ***)
let every_var_inst_mono = prove
 (`!P inst' Q.
   (!x. P x ==> Q x) /\
   every_var_inst P inst' ==>
   every_var_inst Q inst'`,
  CHEAT_TAC);;

let every_var_exp_mono = prove
 (`!P exp Q.
   (!x. P x ==> Q x) /\
   every_var_exp P exp ==>
   every_var_exp Q exp`,
  CHEAT_TAC);;

let every_name_mono = prove
 (`!P names Q.
   (!x. P x ==> Q x) /\
   every_name P names ==> every_name Q names`,
  CHEAT_TAC);;

let every_var_mono = prove
 (`!P prog Q.
   (!x. P x ==> Q x) /\
   wordLang_every_var P prog ==>
   wordLang_every_var Q prog`,
  CHEAT_TAC);;

(*Conjunct*)
let every_var_inst_conj = prove
 (`!P inst' Q.
   every_var_inst P inst' /\ every_var_inst Q inst' <=>
   every_var_inst (\x. P x /\ Q x) inst'`,
  CHEAT_TAC);;

let every_var_exp_conj = prove
 (`!P exp Q.
   every_var_exp P exp /\ every_var_exp Q exp <=>
   every_var_exp (\x. P x /\ Q x) exp`,
  CHEAT_TAC);;

let every_name_conj = prove
 (`!P names Q.
   every_name P names /\ every_name Q names <=>
   every_name (\x. P x /\ Q x) names`,
  (REWRITE_TAC[every_name_def; GSYM AND_ALL] THEN CONV_TAC TAUT));;

let every_var_conj = prove
 (`!P prog Q.
   wordLang_every_var P prog /\ wordLang_every_var Q prog <=>
   wordLang_every_var (\x. P x /\ Q x) prog`,
  CHEAT_TAC);;

(*Similar lemmas about every_stack_var*)
let every_var_imp_every_stack_var = prove
 (`!P prog.
   wordLang_every_var P prog ==> every_stack_var P prog`,
  CHEAT_TAC);;

let every_stack_var_mono = prove
 (`!P prog Q.
   (!x. P x ==> Q x) /\
   every_stack_var P prog ==>
   every_stack_var Q prog`,
  CHEAT_TAC);;

let every_stack_var_conj = prove
 (`!P prog Q.
   every_stack_var P prog /\ every_stack_var Q prog <=>
   every_stack_var (\x. P x /\ Q x) prog`,
  CHEAT_TAC);;

(*** labels_rel ***)
let labels_rel_def = new_definition
  `labels_rel old_labs new_labs <=>
     (ALL_DISTINCT old_labs ==> ALL_DISTINCT new_labs) /\
     set_of_list new_labs SUBSET set_of_list old_labs`;;

let labels_rel_refl = prove
 (`!xs. labels_rel xs xs`,
  CHEAT_TAC);;
add_simp labels_rel_refl;;

let labels_rel_APPEND = prove
 (`labels_rel xs xs1 /\ labels_rel ys ys1 ==>
   labels_rel (APPEND xs ys) (APPEND xs1 ys1)`,
  CHEAT_TAC);;

(* HOL4 wordConvsScript.sml:158-160: a theorem that HOL4 states as
   the value of an ML expression: labels_rel_CONS *)

let PERM_IMP_labels_rel = prove
 (`PERM xs ys ==> labels_rel ys xs`,
  CHEAT_TAC);;

let labels_rel_TRANS = prove
 (`labels_rel xs ys /\ labels_rel ys zs ==> labels_rel xs zs`,
  (REWRITE_TAC[labels_rel_def] THEN MESON_TAC[SUBSET_TRANS]));;

(***
  Expressions in ShareInst must be Var or Op Add;
  No other expressions occur except in Set,
  where it must be a Var expr ***)
let _ = size_thms "wordLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let flat_exp_conventions_def,flat_exp_conventions_ind = define_wf
  `MEASURE (\x0. wordLang_prog_size (\x. 0) x0)`
  [`flat_exp_conventions x1 =
        match x1 with
          // These should be converted to Insts
        wordLang_Assign v exp -> F
        | (wordLang_Store exp num') -> F
        // The only place where top level (expression) vars are allowed
        | (reg_alloc_Set store_name (wordLang_Var r)) -> T
        | (reg_alloc_Set store_name _1) -> F
        | (wordLang_ShareInst op v (wordLang_Var r)) -> T
        | (wordLang_ShareInst op v (wordLang_Op asm_Add
          [wordLang_Var r; wordLang_Const c])) -> T
        | (wordLang_ShareInst op v _2) -> F
        | (reg_alloc_Seq p1 p2) ->
       flat_exp_conventions p1 /\ flat_exp_conventions p2
        | (wordLang_Loop names c exit_names) ->
       flat_exp_conventions c
        | (wordLang_If cmp r1 ri e2 e3) ->
       flat_exp_conventions e2 /\ flat_exp_conventions e3
        | (wordLang_MustTerminate p) -> flat_exp_conventions p
        | (wordLang_Call ret dest args h) ->
       ((match ret with
         NONE -> T | SOME (v,cutset,ret_handler,l1,l2) ->
           flat_exp_conventions ret_handler) /\
       (match h with
         NONE -> T | SOME (v,prog,l1,l2) -> flat_exp_conventions
           prog))
        | _3 -> T`];;

(*** Well-formed instructions. This also includes the FP conditions since we do not allocate them ***)
let inst_ok_less_def = new_definition
  `inst_ok_less c x2 =
        match (c,x2) with
          ((c:'a asm_config),asm_Arith (asm_Binop b r1 r2 (Imm w)))
            -> asm_config_valid_imm
       c (INL b) w
        | (c,(asm_Arith (asm_Shift l r1 r2 (Imm i)))) ->
       (((i = (n2w 0)) ==> (l = Lsl)) /\ w2n i < dimindex (:'a))
        | (c,(asm_Arith (asm_Div r1 r2 r3))) ->
       (asm_config_ISA c IN {ARMv8,MIPS,RISC_V})
        | (c,(asm_Arith (asm_LongMul r1 r2 r3 r4))) ->
       ((asm_config_ISA c = ARMv7 ==> ~(r1 = r2)) /\
       (asm_config_ISA c = ARMv8 \/ asm_config_ISA c = RISC_V \/
         asm_config_ISA c = Ag32 ==> ~(r1 = r3) /\ ~(r1 = r4)))
        | (c,(asm_Arith (asm_LongDiv r1 r2 r3 r4 r5))) ->
       (asm_config_ISA c = x86_64)
        | (c,(asm_Arith (asm_AddCarry r1 r2 r3 r4))) ->
       (((asm_config_ISA c = MIPS) \/ (asm_config_ISA c = RISC_V))
         ==> ~(r1 = r3) /\ ~(r1 = r4))
        | (c,(asm_Arith (asm_AddOverflow r1 r2 r3 r4))) ->
       (((asm_config_ISA c = MIPS) \/ (asm_config_ISA c = RISC_V))
         ==> ~(r1 = r3))
        | (c,(asm_Arith (asm_SubOverflow r1 r2 r3 r4))) ->
       (((asm_config_ISA c = MIPS) \/ (asm_config_ISA c = RISC_V))
         ==> ~(r1 = r3))
        | (c,(asm_Mem m r (Addr r' w))) ->
        (if m IN
          {asm_Load,asm_Store,asm_Load16,asm_Store16,asm_Load32
          ,asm_Store32} then (\c. asm_offset_ok 0
          (asm_config_addr_offset c)) c w else if m IN
          {asm_Load16,asm_Store16} then (\c. asm_offset_ok 0
          (asm_config_hw_offset c)) c w else (\c. asm_offset_ok 0
          (asm_config_byte_offset c)) c w)
        | (c,(asm_FP (FPLess r d1 d2))) -> fp_reg_ok d1 c /\
          fp_reg_ok d2 c
        | (c,(asm_FP (FPLessEqual r d1 d2))) -> fp_reg_ok d1 c /\
          fp_reg_ok d2 c
        | (c,(asm_FP (FPEqual r d1 d2))) -> fp_reg_ok d1 c /\
          fp_reg_ok d2 c
        | (c,(asm_FP (FPAbs d1 d2))) ->
       (asm_config_two_reg_arith c ==> (~(d1 = d2))) /\ fp_reg_ok d1
         c /\ fp_reg_ok d2 c
        | (c,(asm_FP (FPNeg d1 d2))) ->
       (asm_config_two_reg_arith c ==> (~(d1 = d2))) /\ fp_reg_ok d1
         c /\ fp_reg_ok d2 c
        | (c,(asm_FP (FPSqrt d1 d2))) -> fp_reg_ok d1 c /\ fp_reg_ok
          d2 c
        | (c,(asm_FP (FPAdd d1 d2 d3))) ->
       (asm_config_two_reg_arith c ==> (d1 = d2)) /\
       fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c
        | (c,(asm_FP (FPSub d1 d2 d3))) ->
       (asm_config_two_reg_arith c ==> (d1 = d2)) /\
       fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c
        | (c,(asm_FP (FPMul d1 d2 d3))) ->
       (asm_config_two_reg_arith c ==> (d1 = d2)) /\
       fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c
        | (c,(asm_FP (FPDiv d1 d2 d3))) ->
       (asm_config_two_reg_arith c ==> (d1 = d2)) /\
       fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c
        | (c,(asm_FP (FPFma d1 d2 d3))) ->
       (asm_config_ISA c = ARMv7) /\
       2 < asm_config_fp_reg_count c /\
       fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c
        | (c,(asm_FP (FPMov d1 d2))) -> fp_reg_ok d1 c /\ fp_reg_ok
          d2 c
        | (c,(asm_FP (FPMovToReg r1 r2 d))) ->
         ((dimindex (:'a) = 32) ==> ~(r1 = r2)) /\ fp_reg_ok d c
        | (c,(asm_FP (FPMovFromReg d r1 r2))) ->
         ((dimindex (:'a) = 32) ==> ~(r1 = r2)) /\ fp_reg_ok d c
        | (c,(asm_FP (FPToInt d1 d2))) -> fp_reg_ok d1 c /\ fp_reg_ok
          d2 c
        | (c,(asm_FP (FPFromInt d1 d2))) -> fp_reg_ok d1 c /\
          fp_reg_ok d2 c
        | (_4,_5) -> T`;;

(*** Instructions have distinct targets and read vars -- set by SSA form ***)
let distinct_tar_reg_def = new_definition
  `distinct_tar_reg x1 =
        match x1 with
          asm_Arith (asm_Binop bop r1 r2 ri) -> ~(ri = Reg r1)
        | (asm_Arith (asm_Shift l r1 r2 ri)) -> ~(ri = Reg r1)
        | (asm_Arith (asm_AddCarry r1 r2 r3 r4)) -> ~(r1 = r3) /\
          ~(r1 = r4)
        | (asm_Arith (asm_AddOverflow r1 r2 r3 r4)) -> ~(r1 = r3)
        | (asm_Arith (asm_SubOverflow r1 r2 r3 r4)) -> ~(r1 = r3)
        | _6 -> T`;;

(***
  Instructions are 2 register code for arith ok
  Currently no two_reg for Mul and Div ***)
let two_reg_inst_def = new_definition
  `two_reg_inst x1 =
        match x1 with
          asm_Arith (asm_Binop bop r1 r2 ri) -> (r1 = r2)
        | (asm_Arith (asm_Shift l r1 r2 ri)) -> (r1 = r2)
        | (asm_Arith (asm_AddCarry r1 r2 r3 r4)) -> (r1 = r2)
        | (asm_Arith (asm_AddOverflow r1 r2 r3 r4)) -> (r1 = r2)
        | (asm_Arith (asm_SubOverflow r1 r2 r3 r4)) -> (r1 = r2)
        | _7 -> T`;;

(*** Recursor over instructions ***)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let every_inst_def,every_inst_ind = define_wf
  `MEASURE (\(x0,x1). wordLang_prog_size (\x. 0) x1)`
  [`every_inst P prog =
        match prog with
          wordLang_Inst i -> P i
        | (wordLang_Seq p1 p2) -> (every_inst P p1 /\ every_inst P
          p2)
        | (wordLang_Loop names c exit_names) ->
       every_inst P c
        | (wordLang_If cmp r1 ri c1 c2) -> every_inst P c1 /\
          every_inst P c2
        | (wordLang_OpCurrHeap bop r1 r2) -> P (asm_Arith (asm_Binop
          bop r1 r2 (Reg r2)))
        | (wordLang_MustTerminate p) -> every_inst P p
        | (wordLang_Call ret dest args handler) -> (match ret with
           NONE -> T | SOME (n,names,ret_handler,l1,l2) ->
             every_inst P ret_handler /\
         (match handler with
           NONE -> T | SOME (n,h,l1,l2) -> every_inst P h))
        | prog -> T`];;

(*** Every instruction is well-formed ***)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let full_inst_ok_less_def,full_inst_ok_less_ind = define_wf
  `MEASURE (\(x0,x1). wordLang_prog_size (\x. 0) x1)`
  [`full_inst_ok_less c prog =
        match prog with
          wordLang_Inst i -> inst_ok_less c i
        | (wordLang_Seq p1 p2) ->
       (full_inst_ok_less c p1 /\ full_inst_ok_less c p2)
        | (wordLang_Loop names p exit_names) ->
       (full_inst_ok_less c p)
        | (wordLang_If cmp r1 ri c1 c2) ->
       (full_inst_ok_less c c1 /\ full_inst_ok_less c c2)
        | (wordLang_MustTerminate p) -> full_inst_ok_less c p
        | (wordLang_Call ret dest args handler) -> (match ret with
           NONE -> T | SOME (n,names,ret_handler,l1,l2) ->
             full_inst_ok_less c ret_handler /\
         (match handler with
           NONE -> T | SOME (n,h,l1,l2) -> full_inst_ok_less c h))
        | (wordLang_ShareInst op r ad) ->
       (match exp_to_addr ad with SOME (Addr _8 w) ->
         (if op IN
           {wordLang_Load,wordLang_Store,asm_Load32,asm_Store32} then
           (\c. asm_offset_ok 0 (asm_config_addr_offset c)) c w else if
           op IN {asm_Load16,asm_Store16} then (\c. asm_offset_ok 0
           (asm_config_hw_offset c)) c w else (\c. asm_offset_ok 0
           (asm_config_byte_offset c)) c w) | NONE -> F)
        | prog -> T`];;

(*** All cutsets are well-formed ***)
let wf_names_def = new_definition
  `wf_names t =
     (sptree_wf (FST t) /\ sptree_wf (SND t))`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let wf_cutsets_def,wf_cutsets_ind = define_wf
  `MEASURE (\x0. wordLang_prog_size (\x. 0) x0)`
  [`wf_cutsets x1 =
        match x1 with
          wordLang_Alloc n s -> wf_names s
        | (wordLang_Install _9 _10 _11 _12 s) -> wf_names s
        | (wordLang_Call ret dest args h) ->
       (match ret with
         NONE -> T | SOME (v,cutset,ret_handler,l1,l2) ->
         wf_names cutset /\
         wf_cutsets ret_handler /\
         (match h with
           NONE -> T | SOME (v,prog,l1,l2) ->
           wf_cutsets prog))
        | (wordLang_FFI x1 y1 x2 y2 z args) -> wf_names args
        | (wordLang_MustTerminate s) -> wf_cutsets s
        | (wordLang_Seq s1 s2) ->
       (wf_cutsets s1 /\ wf_cutsets s2)
        | (wordLang_Loop names p exit_names) ->
       sptree_wf names /\ sptree_wf exit_names /\ wf_cutsets p
        | (wordLang_If cmp r1 ri e2 e3) ->
       (wf_cutsets e2 /\
        wf_cutsets e3)
        | _13 -> T`];;

(*** Conventions for args to instructions ***)
let inst_arg_convention_def = new_definition
  `inst_arg_convention x1 =
        match x1 with
          asm_Arith (asm_AddCarry r1 r2 r3 r4) -> r4 = 0
        | (asm_Arith (asm_Shift _14 _15 _16 (Reg r))) -> r = 8
        // Note: these are not necessary
        | (asm_Arith (asm_AddOverflow r1 r2 r3 r4)) -> r4 = 0
        | (asm_Arith (asm_SubOverflow r1 r2 r3 r4)) -> r4 = 0
        | (asm_Arith (asm_LongMul r1 r2 r3 r4)) -> r1 = 6 /\ r2 = 0
          /\ r3 = 0 /\ r4 = 4
        // LongDiv follows conventions for x86 as it is the only possibility
        | (asm_Arith (asm_LongDiv r1 r2 r3 r4 r5)) -> r1 = 0 /\ r2 =
          6 /\ r3 = 6 /\ r4 = 0
        | _17 -> T`;;

(*** Calling conventions ***)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let call_arg_convention_def,call_arg_convention_ind = define_wf
  `MEASURE (\x0. wordLang_prog_size (\x. 0) x0)`
  [`call_arg_convention p =
        match p with
          wordLang_Inst i ->
       inst_arg_convention i
        | (wordLang_Return x ys) -> (ys = list_of_seq (\x. 2 * (x +
          1)) (LENGTH ys))
        | (wordLang_Raise y) -> (y = 2)
        | (wordLang_Install ptr len _18 _19 _20) -> (ptr = 2 /\ len
          = 4)
        | (wordLang_FFI x ptr len ptr2 len2 args) -> (ptr = 2 /\ len
          = 4 /\
                              ptr2 = 6 /\ len2 = 8)
        | (wordLang_Alloc n s) -> (n = 2)
        | (wordLang_StoreConsts a b c d ws) ->
       ((a = 0) /\ (b = 2) /\ (c = 4) /\ (d = 6))
        | (wordLang_Call ret dest args h) ->
       (match ret with
         NONE -> args = list_of_seq (\x. 2 * x) (LENGTH args) | SOME
           (vs,cutset,ret_handler,l1,l2) ->
         args = list_of_seq (\x. 2 * (x + 1)) (LENGTH args) /\
         (vs = list_of_seq (\x. 2 * (x + 1)) (LENGTH vs)) /\
           call_arg_convention ret_handler /\
       (match h with
         // Does not check the case where Calls are ill-formed
         NONE -> T | SOME (v,prog,l1,l2) ->
         (v = 2) /\ call_arg_convention prog))
        | (wordLang_MustTerminate s1) ->
       call_arg_convention s1
        | (wordLang_Seq s1 s2) ->
       (call_arg_convention s1 /\ call_arg_convention s2)
        | (wordLang_Loop names p exit_names) ->
       call_arg_convention p
        | (wordLang_If cmp r1 ri e2 e3) ->
       (call_arg_convention e2 /\
        call_arg_convention e3)
        | p -> T`];;

(*** Before allocation, generated by SSA CC ***)
let pre_alloc_conventions_def = new_definition
  `pre_alloc_conventions p =
     (every_stack_var is_stack_var p /\
     call_arg_convention p)`;;

(*** After allocation, generated by allocator and/or the oracles ***)
let post_alloc_conventions_def = new_definition
  `post_alloc_conventions k prog =
     (wordLang_every_var is_phy_var prog /\
     every_stack_var (\x. x >= 2 * k) prog /\
     call_arg_convention prog)`;;

(*** This is for label preservation -- wordLang shouldn't need to inspect the labels explicitly. ***)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let extract_labels_def,extract_labels_ind = define_wf
  `MEASURE (\x0. wordLang_prog_size (\x. 0) x0)`
  [`wordConvs_extract_labels x1 =
        match x1 with
          wordLang_Call ret dest args h ->
       (match ret with
         NONE -> [] | SOME (v,cutset,ret_handler,l1,l2) ->
         (let ret_rest = wordConvs_extract_labels ret_handler in
       (match h with
         NONE -> APPEND [(l1,l2)] ret_rest | SOME (v,prog,l1',l2')
           ->
         (let h_rest = wordConvs_extract_labels prog in APPEND
           (APPEND [(l1,l2); (l1',l2')] ret_rest) h_rest))))
        | (wordLang_MustTerminate s1) -> wordConvs_extract_labels s1
        | (wordLang_Seq s1 s2) -> APPEND (wordConvs_extract_labels
          s1) (wordConvs_extract_labels s2)
        | (wordLang_Loop names p exit_names) ->
       wordConvs_extract_labels p
        | (wordLang_If cmp r1 ri e2 e3) ->
       (APPEND (wordConvs_extract_labels e2)
         (wordConvs_extract_labels e3))
        | _21 -> []`];;

(*** Property on max_var ***)
(* [local] *)
let max_var_exp_IMP = prove
 (`!exp.
   P 0 /\ every_var_exp P exp ==>
   P (max_var_exp exp)`,
  CHEAT_TAC);;

let max_var_intro = prove
 (`!prog.
   P 0 /\ wordLang_every_var P prog ==>
   P (max_var prog)`,
  CHEAT_TAC);;

(*** code_labels ***)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let get_code_labels_def,get_code_labels_ind = define_wf
  `MEASURE (\x0. wordLang_prog_size (\x. 0) x0)`
  [`wordConvs_get_code_labels x1 =
        match x1 with
          wordLang_Call r d a h ->
       (match d with SOME x -> {x} | _22 -> {}) UNION
       (match r with SOME (_23,_24,x,_25,_26) ->
         wordConvs_get_code_labels x | _27 -> {}) UNION
       (match h with SOME (_28,x,l1,l2) -> wordConvs_get_code_labels
         x | _29 -> {})
        | (wordLang_Seq p1 p2) -> wordConvs_get_code_labels p1 UNION
          wordConvs_get_code_labels p2
        | (wordLang_Loop names p exit_names) ->
          wordConvs_get_code_labels p
        | (wordLang_If _30 _31 _32 p1 p2) ->
          wordConvs_get_code_labels p1 UNION wordConvs_get_code_labels
          p2
        | (wordLang_MustTerminate p) -> wordConvs_get_code_labels p
        | (wordLang_LocValue _33 l1) -> {l1}
        | _34 -> {}`];;
add_simp get_code_labels_def;;

(*** TODO: This seems like it must have been established before
  handler labels point only within the current table entry
***)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let good_handlers_def,good_handlers_ind = define_wf
  `MEASURE (\(x0,x1). wordLang_prog_size (\x. 0) x1)`
  [`good_handlers n x2 =
        match x2 with
          wordLang_Call r d a h ->
       (match r with
         NONE -> T | SOME (_35,_36,x,_37,_38) -> good_handlers n x
           /\
       (match h with SOME (_39,x,l1,_40) -> l1 = n /\ good_handlers
         n x | _41 -> T))
        | (wordLang_Seq p1 p2) -> good_handlers n p1 /\
          good_handlers n p2
        | (wordLang_Loop names p exit_names) -> good_handlers n p
        | (wordLang_If _42 _43 _44 p1 p2) -> good_handlers n p1 /\
          good_handlers n p2
        | (wordLang_MustTerminate p) -> good_handlers n p
        | _45 -> T`];;
add_simp good_handlers_def;;

let good_code_labels_def = new_definition
  `wordConvs_good_code_labels p elabs <=>
   ALL (\(n,m,pp). good_handlers n pp) p /\
   (UNIONS (set_of_list (MAP (\(n,m,pp). (wordConvs_get_code_labels
     pp)) p))) SUBSET
   (set_of_list (MAP FST p) UNION elabs)`;;

(*** not_created_subprogs ***)

(* Examines various syntactic elements within programs that some phases are
   expected to possibly remove but not create. *)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let not_created_subprogs_def,not_created_subprogs_ind = define_wf
  `MEASURE (\(x0,x1). wordLang_prog_size (\x. 0) x1)`
  [`not_created_subprogs P x2 =
      match x2 with
        (wordLang_MustTerminate p:'a wordLang_prog) ->
     (P (wordLang_MustTerminate (wordLang_Skip:'a wordLang_prog)) /\
       not_created_subprogs P p)
      | (wordLang_Seq p1 p2) -> (not_created_subprogs P p1 /\
     not_created_subprogs P p2)
      | (wordLang_Loop names c exit_names) ->
     (not_created_subprogs P c)
      | (wordLang_If _46 _47 _48 p1 p2) -> (not_created_subprogs P
        p1 /\
     not_created_subprogs P p2)
      | (wordLang_Call r dest args h) ->
     (P (wordLang_Call NONE dest [] NONE) /\
     (match r with NONE -> T | SOME (_49,_50,p,_51) ->
       not_created_subprogs P p) /\
     (match h with NONE -> T | SOME (_52,p,h1,_53) ->
         P (wordLang_Call NONE NONE [] (SOME
           (0,wordLang_Skip,h1,0))) /\
         not_created_subprogs P p))
      | (wordLang_Alloc _54 _55) -> P (wordLang_Alloc 0 (LN,LN))
      | (wordLang_LocValue _56 l) -> P (wordLang_LocValue 0 l)
      | (wordLang_ShareInst _57 _58 _59) -> P (wordLang_ShareInst
        ARB 0 (wordLang_Var 0))
      | (wordLang_Install _60 _61 _62 _63 _64) -> P
        (wordLang_Install 0 0 0 0 (LN,LN))
      | _65 -> T`];;

(* HOL4 wordConvsScript.sml:558-562: a theorem that HOL4 states as
   the value of an ML expression: not_created_subprogs_P_def *)

(* no_alloc specialisation *)

(* HOL4 wordConvsScript.sml:566: the ML values that the definitions
   below antiquote *)

let no_alloc_subprogs_def = new_definition
  `no_alloc p = not_created_subprogs (((\x y. ~(x = y))
  (wordLang_Alloc 0 (LN,LN)))) p`;;

(* HOL4 wordConvsScript.sml:572-574: a theorem that HOL4 states as
   the value of an ML expression: no_alloc_def *)

(* HOL4 wordConvsScript.sml:576: the ML values that the definitions
   below antiquote *)

let no_install_subprogs_def = new_definition
  `wordConvs_no_install p = not_created_subprogs (((\x y. ~(x = y))
  (wordLang_Install 0 0 0 0 (LN,LN)))) p`;;

(* HOL4 wordConvsScript.sml:582-584: a theorem that HOL4 states as
   the value of an ML expression: no_install_def *)

(****** no_mt : no MustTerminate ******)

(* HOL4 wordConvsScript.sml:588: the ML values that the definitions
   below antiquote *)

let no_mt_subprogs_def = new_definition
  `no_mt p = not_created_subprogs (((\x y. ~(x = y))
  (wordLang_MustTerminate wordLang_Skip))) p`;;

(* HOL4 wordConvsScript.sml:594-596: a theorem that HOL4 states as
   the value of an ML expression: no_mt_def *)

(* no_share_inst: no ShareInst *)

(* HOL4 wordConvsScript.sml:600: the ML values that the definitions
   below antiquote *)

let no_share_inst_subprogs_def = new_definition
  `no_share_inst p = not_created_subprogs (((\x y. ~(x = y))
  (wordLang_ShareInst ARB 0 (wordLang_Var 0)))) p`;;

(* HOL4 wordConvsScript.sml:606-608: a theorem that HOL4 states as
   the value of an ML expression: no_share_inst_def *)

(* HOL4 wordConvsScript.sml:610: the overload word_get_code_labels,
   which the port expands *)
(* HOL4 wordConvsScript.sml:611: the overload word_good_handlers,
   which the port expands *)
(* HOL4 wordConvsScript.sml:612: the overload word_good_code_labels,
   which the port expands *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["inst"];;
