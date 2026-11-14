(* ======================================================== *)
(*  stack_rawcallProof: ported from HOL4's
    compiler/backend/proofs/stack_rawcallProofScript.sml
    A proof theory about stack_rawcall.ml, with 2 definitions and 21
    theorems.  Needed by stack_to_labProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for stack_rawcall
*)

needs "compiler/backend/semantics/labProps.ml";;
needs "compiler/backend/semantics/stackProps.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_rawcall.ml";;
needs "lib/sptree.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "stack_rawcallProof"
  ["labProps"; "stackLang"; "stackProps"; "stackSem"; "stack_rawcall";
   "wordSem"];;


(* HOL4 stack_rawcallProofScript.sml:12: ML code, not ported *)

(* HOL4 stack_rawcallProofScript.sml:14-16: ML code, not ported *)

(* HOL4 stack_rawcallProofScript.sml:18: the overload good_dimindex,
   which the port expands *)
(* HOL4 stack_rawcallProofScript.sml:19: the overload comp, which the
   port expands *)
(* HOL4 stack_rawcallProofScript.sml:20: the overload compile, which
   the port expands *)
(* HOL4 stack_rawcallProofScript.sml:21: the type abbreviation prog,
   which the port expands *)

let stack_rawcallProof_state_ok_def = new_definition
  `stack_rawcallProof_state_ok i code <=>
     (!n v.
       sptree_lookup n i = SOME v ==>
       (?p. sptree_lookup n code = SOME (stackLang_Seq
         (stackLang_StackAlloc v) p)))`;;

let stack_rawcallProof_state_rel_def = new_definition
  `stack_rawcallProof_state_rel i s t <=>
     (?c.
       // co cc
       domain c = domain (state_code s) /\
       t = state_code_fupd (K c) s /\
       // ;
       // compile := cc ;
       // compile_oracle := co
       // s.compile = pure_cc compile t.compile /\
       // t.compile_oracle = (I ## compile ## I) o s.compile_oracle /\
       stack_rawcallProof_state_ok i (state_code s) /\
       (!n b.
         sptree_lookup n (state_code s) = SOME b ==>
         (?i. stack_rawcallProof_state_ok i (state_code s) /\
             sptree_lookup n c = SOME (comp_top i b))))`;;

(* HOL4 stack_rawcallProofScript.sml:46-47: a theorem that HOL4
   states as the value of an ML expression: state_rel_thm *)

(* [local] *)
let with_stack_space = prove
 (`stackSem_state_stack_space_fupd (K (stackSem_state_stack_space t1))
     t1 = t1`,
  CHEAT_TAC);;

let comp_LN = prove
 (`!(i:num spt) b. comp_top LN b = b /\ stack_rawcall_comp LN b = b`,
  CHEAT_TAC);;

let comp_seq_neq_IMP = prove
 (`~(comp_seq p1 p2 i default = default) ==>
     (?k dest. p1 = stackLang_StackFree k /\ p2 = stackLang_Call
       NONE (INL dest) NONE)`,
  CHEAT_TAC);;

(* get_labels_comp *)
let stack_rawcallProof_get_labels_comp = prove
 (`!i e.
     labProps_get_labels (stack_rawcall_comp i e) =
       labProps_get_labels e /\
     labProps_get_labels (comp_top i e) = labProps_get_labels e`,
  CHEAT_TAC);;

(* HOL4 stack_rawcallProofScript.sml:107-119: a proof *)

let evaluate_comp_Inst = prove
 (`stackSem_evaluate (stackLang_Inst i,s) = (r,s1) /\ ~(r = SOME
  stackSem_Error) /\ stack_rawcallProof_state_rel i' s t ==>
   (?ck t1 k1.
     stack_rawcallProof_state_rel i' s1 t1 /\
     stackSem_evaluate (stack_rawcall_comp i' (stackLang_Inst
       i),state_clock_fupd (K (ck + state_clock t)) t) =
     (r,stackSem_state_stack_space_fupd (K k1) t1) /\
     (~(r = SOME stackSem_TimeOut) /\ ~(r = SOME (stackLang_Halt
       (wordLang_Word (n2w 2)))) ==>
      k1 = stackSem_state_stack_space t1))`,
  CHEAT_TAC);;

(* comp_correct *)
let stack_rawcallProof_comp_correct = prove
 (`!p (s:('a,'c,'b)stackSem_state) t i r s1.
     stackSem_evaluate (p,s) = (r,s1) /\ ~(r = SOME stackSem_Error)
       /\ stack_rawcallProof_state_rel i s t ==>
     (?ck t1 k1.
        stack_rawcallProof_state_rel i s1 t1 /\
        stackSem_evaluate (comp_top i p,state_clock_fupd (K
          (state_clock t + ck)) t) =
          (r,stackSem_state_stack_space_fupd (K k1) t1) /\
        (~(r = SOME stackSem_TimeOut) /\ ~(r = SOME (stackLang_Halt
          (wordLang_Word (n2w 2)))) ==> k1 = stackSem_state_stack_space
          t1)) /\
     (?ck t1 k1.
        stack_rawcallProof_state_rel i s1 t1 /\
        stackSem_evaluate (stack_rawcall_comp i p,state_clock_fupd (K
          (state_clock t + ck)) t) =
          (r,stackSem_state_stack_space_fupd (K k1) t1) /\
        (~(r = SOME stackSem_TimeOut) /\ ~(r = SOME (stackLang_Halt
          (wordLang_Word (n2w 2)))) ==> k1 =
          stackSem_state_stack_space t1))`,
  CHEAT_TAC);;

let domain_fromAList_compile = prove
 (`domain (fromAList (stack_rawcall_compile code)) = domain (fromAList
  code)`,
  CHEAT_TAC);;

let lookup_collect_info = prove
 (`!xs n rest.
     ALL_DISTINCT (MAP FST xs) ==>
     sptree_lookup n (collect_info xs rest) =
       (match ALOOKUP xs n with NONE -> sptree_lookup n rest | SOME
         body -> sptree_lookup n (collect_info [(n,body)] rest))`,
  CHEAT_TAC);;

let state_ok_collect_info = prove
 (`ALL_DISTINCT (MAP FST code) ==>
   stack_rawcallProof_state_ok (collect_info code LN) (fromAList
     code)`,
  CHEAT_TAC);;

(* compile_semantics *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let stack_rawcallProof_compile_semantics = prove
 (cake_as_vars (fun () ->
    `ALL_DISTINCT (MAP FST code) /\ stackSem_state_use_stack s /\
  state_code
     s = fromAList code /\ ~(stackSem_semantics start s = ffi_Fail)
       ==>
     stackSem_semantics start (state_code_fupd (K (fromAList
       (stack_rawcall_compile code))) s) =
     stackSem_semantics start s`),
  CHEAT_TAC);;

let extract_labels_comp = prove
 (`!i p.
     stackProps_extract_labels (stack_rawcall_comp i p) =
       stackProps_extract_labels p /\
     stackProps_extract_labels (comp_top i p) =
       stackProps_extract_labels p`,
  CHEAT_TAC);;

let stack_asm_name_comp = prove
 (`!i p.
     (stack_asm_name c (stack_rawcall_comp i p) = stack_asm_name c p
       /\
      stack_asm_name c (comp_top i p) = stack_asm_name c p) /\
     (stack_asm_remove c (stack_rawcall_comp i p) = stack_asm_remove
       c p /\
      stack_asm_remove c (comp_top i p) = stack_asm_remove c p)`,
  CHEAT_TAC);;

(* stack_alloc_stack_asm_convs *)
let stack_rawcallProof_stack_alloc_stack_asm_convs = prove
 (`ALL (\(n,p). stack_asm_name c p) (stack_rawcall_compile prog) =
   ALL (\(n,p). stack_asm_name c p) prog /\
   ALL (\(n,p). stack_asm_remove c p) (stack_rawcall_compile prog) =
   ALL (\(n,p). stack_asm_remove c p) prog`,
  CHEAT_TAC);;

let reg_bound_comp = prove
 (`!i p.
     reg_bound (stack_rawcall_comp i p) s = reg_bound p s /\
     reg_bound (comp_top i p) s = reg_bound p s`,
  CHEAT_TAC);;

let stack_rawcall_reg_bound = prove
 (`ALL (\p. reg_bound p sp) (MAP SND (stack_rawcall_compile prog1)) =
   ALL (\p. reg_bound p sp) (MAP SND prog1)`,
  CHEAT_TAC);;

let call_args_comp = prove
 (`!i p.
     call_args (stack_rawcall_comp i p) r1 r2 r3 r4 r5 = call_args p
       r1 r2 r3 r4 r5 /\
     call_args (comp_top i p) r1 r2 r3 r4 r5 = call_args p r1 r2 r3
       r4 r5`,
  CHEAT_TAC);;

(* stack_alloc_call_args *)
let stack_rawcallProof_stack_alloc_call_args = prove
 (`ALL (\p. call_args p 1 2 3 4 0) (MAP SND (stack_rawcall_compile
  prog1)) =
   ALL (\p. call_args p 1 2 3 4 0) (MAP SND prog1)`,
  CHEAT_TAC);;

(* MAP_FST_compile *)
let stack_rawcallProof_MAP_FST_compile = prove
 (`MAP FST (stack_rawcall_compile code) = MAP FST code`,
  CHEAT_TAC);;

let call_arg_comp = prove
 (`!i p.
     alloc_arg (stack_rawcall_comp i p) = alloc_arg p /\
     alloc_arg (comp_top i p) = alloc_arg p`,
  CHEAT_TAC);;

let stack_get_handler_labels_comp = prove
 (`!i p k.
     stack_get_handler_labels k (stack_rawcall_comp i p) =
     stack_get_handler_labels k p /\
     stack_get_handler_labels k (comp_top i p) =
     stack_get_handler_labels k p`,
  CHEAT_TAC);;
