(* ======================================================== *)
(*  clos_letopProof: ported from HOL4's
    compiler/backend/proofs/clos_letopProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for clos_letop
*)

needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_letop.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;


(* HOL4 clos_letopProofScript.sml:11: ML code, not ported *)

(* HOL4 clos_letopProofScript.sml:15: the overload let_op, which the
   port expands *)
(* HOL4 clos_letopProofScript.sml:16: the overload var_list, which
   the port expands *)

let code_rel_def = cake_define
  `clos_letopProof_code_rel e1 e2 <=>
     e2 = clos_letop_let_op e1`;;
hol4_overload "code_rel" "clos_letopProof_code_rel";;

(* value relation *)

let f_rel_def = cake_define
  `clos_letopProof_f_rel (a1,e1) (a2,e2) <=>
      a1 = a2 /\ clos_letopProof_code_rel [e1] [e2]`;;
hol4_overload "f_rel" "clos_letopProof_f_rel";;

let v_rel = cake_inductive
  `(!i. clos_letopProof_v_rel (closSem_Number i) (closSem_Number i)) /\
   (!w. clos_letopProof_v_rel (Word64 w) (Word64 w)) /\
   (!w. clos_letopProof_v_rel (closSem_ByteVector w)
     (closSem_ByteVector w)) /\
   (!n b. clos_letopProof_v_rel (closSem_RefPtr b n) (closSem_RefPtr
     b n)) /\
   (!tag xs ys.
      LIST_REL clos_letopProof_v_rel xs ys ==>
        clos_letopProof_v_rel (closSem_Block tag xs) (closSem_Block
          tag ys)) /\
   (!loc args1 args2 env1 env2 num_args e1 e2.
      LIST_REL clos_letopProof_v_rel env1 env2 /\
      LIST_REL clos_letopProof_v_rel args1 args2 /\
      clos_letopProof_code_rel [e1] [e2] ==>
        clos_letopProof_v_rel (Closure loc args1 env1 num_args e1)
          (Closure loc args2 env2 num_args e2)) /\
   (!loc args1 args2 env1 env2 k.
      LIST_REL clos_letopProof_v_rel env1 env2 /\
      LIST_REL clos_letopProof_v_rel args1 args2 /\
      LIST_REL clos_letopProof_f_rel funs1 funs2 ==>
        clos_letopProof_v_rel (Recclosure loc args1 env1 funs1 k)
          (Recclosure loc args2 env2 funs2 k))`;;
hol4_overload "v_rel" "clos_letopProof_v_rel";;

(* state relation *)

let ref_rel = cake_inductive
  `(!bs. clos_letopProof_ref_rel (closSem_ByteArray bs)
  (closSem_ByteArray bs)) /\
   (!xs ys.
     LIST_REL clos_letopProof_v_rel xs ys ==>
     clos_letopProof_ref_rel (closSem_ValueArray xs)
       (closSem_ValueArray ys)) /\
   (!m v w.
     clos_letopProof_v_rel v w ==>
     clos_letopProof_ref_rel (Thunk m v) (Thunk m w))`;;
hol4_overload "ref_rel" "clos_letopProof_ref_rel";;

let FMAP_REL_def = cake_define
  `clos_letopProof_FMAP_REL r f1 f2 <=>
     FDOM f1 = FDOM f2 /\
     (!k v. FLOOKUP f1 k = SOME v ==>
           (?v2. FLOOKUP f2 k = SOME v2 /\ r v v2))`;;
hol4_overload "FMAP_REL" "clos_letopProof_FMAP_REL";;

let state_rel_def = cake_define
  `clos_letopProof_state_rel (s:('c,'ffi)closSem_state)
  (t:('c,'ffi)closSem_state) <=>
     (!n. SND (SND (closSem_state_compile_oracle s n)) = []) /\
       closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY /\
       closSem_state_max_app
     t = closSem_state_max_app s /\ 1 <= closSem_state_max_app s /\
       state_clock
     t = state_clock s /\ state_ffi
     t = state_ffi s /\
     LIST_REL (OPTREL clos_letopProof_v_rel) (closSem_state_globals
       s) (closSem_state_globals t) /\
     clos_letopProof_FMAP_REL ref_rel (state_refs s) (state_refs t)
       /\ closSem_state_compile
     s = pure_cc clos_letop_compile_inc (closSem_state_compile t) /\
       closSem_state_compile_oracle
     t = pure_co clos_letop_compile_inc o
       closSem_state_compile_oracle s`;;
hol4_overload "state_rel" "clos_letopProof_state_rel";;

(* *)


(* *)

(* evaluate_let_op *)

(* preservation of observational semantics *)

(* syntactic properties *)
