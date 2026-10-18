(* ======================================================== *)
(*  stack_rawcallProof: ported from HOL4's
    compiler/backend/proofs/stack_rawcallProofScript.sml
    A proof theory about stack_rawcall.ml, with 2 definitions and 21
    theorems.  Needed by stack_to_labProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for stack_rawcall
*)

needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/semantics/labProps.ml";;
needs "compiler/backend/semantics/stackProps.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_rawcall.ml";;
needs "lib/sptree.ml";;


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

let state_ok_def = cake_define
  `stack_rawcallProof_state_ok i code <=>
     (!n v.
       sptree_lookup n i = SOME v ==>
       (?p. sptree_lookup n code = SOME (Seq (stackLang_StackAlloc
         v) p)))`;;
hol4_overload "state_ok" "stack_rawcallProof_state_ok";;

let state_rel_def = cake_define
  `stack_rawcallProof_state_rel i s t <=>
     (?c.
       domain c = domain (state_code s) /\
       t = state_code_fupd (K c) s /\
       stack_rawcallProof_state_ok i (state_code s) /\
       (!n b.
         sptree_lookup n (state_code s) = SOME b ==>
         (?i. stack_rawcallProof_state_ok i (state_code s) /\
             lookup n c = SOME (comp_top i b))))`;;
hol4_overload "state_rel" "stack_rawcallProof_state_rel";;

(* HOL4 stack_rawcallProofScript.sml:107-119: a proof *)
