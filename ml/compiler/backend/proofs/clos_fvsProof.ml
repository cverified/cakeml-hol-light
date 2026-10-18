(* ======================================================== *)
(*  clos_fvsProof: ported from HOL4's
    compiler/backend/proofs/clos_fvsProofScript.sml
    A proof theory about clos_fvs.ml, with 5 definitions and 37
    theorems.  Needed by clos_knownProof.ml and clos_to_bvlProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for clos_fvs
*)

needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_fvs.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

let code_rel_def = cake_define
  `clos_fvsProof_code_rel fvs e1 e2 <=>
     e2 = remove_fvs fvs e1`;;
hol4_overload "code_rel" "clos_fvsProof_code_rel";;

(* value relation *)

let f_rel_def = cake_define
  `clos_fvsProof_f_rel fvs (a1,e1) (a2,e2) <=>
      a1 = a2 /\ clos_fvsProof_code_rel (a1 + fvs) [e1] [e2]`;;
hol4_overload "f_rel" "clos_fvsProof_f_rel";;

let v_rel = cake_inductive
  `(!i. clos_fvsProof_v_rel (closSem_Number i) (closSem_Number i)) /\
   (!w. clos_fvsProof_v_rel (Word64 w) (Word64 w)) /\
   (!w. clos_fvsProof_v_rel (closSem_ByteVector w)
     (closSem_ByteVector w)) /\
   (!n b. clos_fvsProof_v_rel (closSem_RefPtr b n) (closSem_RefPtr b
     n)) /\
   (!tag xs ys.
      LIST_REL clos_fvsProof_v_rel xs ys ==>
        clos_fvsProof_v_rel (closSem_Block tag xs) (closSem_Block tag
          ys)) /\
   (!loc args1 args2 env1 env2 num_args e1 e2.
      LIST_REL clos_fvsProof_v_rel env1 env2 /\
      LIST_REL clos_fvsProof_v_rel args1 args2 /\
      clos_fvsProof_code_rel (LENGTH env1 + num_args) [e1] [e2] ==>
        clos_fvsProof_v_rel (Closure loc args1 env1 num_args e1)
          (Closure loc args2 env2 num_args e2)) /\
   (!loc args1 args2 env1 env2 k.
      LIST_REL clos_fvsProof_v_rel env1 env2 /\
      LIST_REL clos_fvsProof_v_rel args1 args2 /\
      LIST_REL (clos_fvsProof_f_rel (LENGTH env1 + LENGTH funs1))
        funs1 funs2 ==>
        clos_fvsProof_v_rel (Recclosure loc args1 env1 funs1 k)
          (Recclosure loc args2 env2 funs2 k))`;;
hol4_overload "v_rel" "clos_fvsProof_v_rel";;

(* state relation *)

let ref_rel = cake_inductive
  `(!bs. clos_fvsProof_ref_rel (closSem_ByteArray bs) (closSem_ByteArray
  bs)) /\
   (!xs ys.
     LIST_REL clos_fvsProof_v_rel xs ys ==>
     clos_fvsProof_ref_rel (closSem_ValueArray xs)
       (closSem_ValueArray ys)) /\
   (!m v w.
     clos_fvsProof_v_rel v w ==>
     clos_fvsProof_ref_rel (Thunk m v) (Thunk m w))`;;
hol4_overload "ref_rel" "clos_fvsProof_ref_rel";;

let state_rel_def = cake_define
  `clos_fvsProof_state_rel (s:('c,'ffi)closSem_state)
  (t:('c,'ffi)closSem_state) <=>
     (!n. SND (SND (closSem_state_compile_oracle s n)) = []) /\
       closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY /\
       closSem_state_max_app
     t = closSem_state_max_app s /\ 1 <= closSem_state_max_app s /\
       state_clock
     t = state_clock s /\ state_ffi
     t = state_ffi s /\
     LIST_REL (OPTREL clos_fvsProof_v_rel) (closSem_state_globals s)
       (closSem_state_globals t) /\
     fmap_rel ref_rel (state_refs s) (state_refs t) /\
       closSem_state_compile
     s = pure_cc clos_fvs_compile_inc (closSem_state_compile t) /\
       closSem_state_compile_oracle
     t = pure_co clos_fvs_compile_inc o
       closSem_state_compile_oracle s`;;
hol4_overload "state_rel" "clos_fvsProof_state_rel";;

(* *)


(* *)

(* evaluate level correctness *)

(* preservation of observational semantics *)

(* syntactic properties *)
