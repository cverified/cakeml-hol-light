(* ======================================================== *)
(*  clos_numberProof: ported from HOL4's
    compiler/backend/proofs/clos_numberProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for clos_number
*)

needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_number.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

(* properties of renumber_code_locs *)

(* HOL4 clos_numberProofScript.sml:20-36: a proof *)

(* value relation *)

let v_rel = cake_inductive
  `(clos_numberProof_v_rel max_app (closSem_Number j) (closSem_Number
  j)) /\
   (clos_numberProof_v_rel max_app (Word64 w) (Word64 w)) /\
   (EVERY2 (clos_numberProof_v_rel max_app) (xs:closSem_v list)
     (ys:closSem_v list) ==>
    clos_numberProof_v_rel max_app (closSem_Block t xs)
      (closSem_Block t ys)) /\
   (clos_numberProof_v_rel max_app (closSem_ByteVector ws)
     (closSem_ByteVector ws)) /\
   (clos_numberProof_v_rel max_app (closSem_RefPtr b r1)
     (closSem_RefPtr b r1)) /\
   (LIST_REL (clos_numberProof_v_rel max_app) env env' /\
    LIST_REL (clos_numberProof_v_rel max_app) argenv argenv' /\
    ~contains_App_SOME max_app [c] /\
    c' = SND (renumber_code_locs n c) ==>
    clos_numberProof_v_rel max_app (Closure p argenv env num_args c)
      (Closure p' argenv' env' num_args c')) /\
   (
    LIST_REL (clos_numberProof_v_rel max_app) env env' /\
    LIST_REL (clos_numberProof_v_rel max_app) argenv argenv' /\
    ~contains_App_SOME max_app (MAP SND es) /\
    es' = ZIP (MAP FST es) (SND (renumber_code_locs_list n (MAP SND
      es))) ==>
    clos_numberProof_v_rel max_app (Recclosure p argenv env es k)
      (Recclosure p' argenv' env' es' k))`;;
hol4_overload "v_rel" "clos_numberProof_v_rel";;

let state_rel_def = cake_define
  `clos_numberProof_state_rel (s:(num#'c,'ffi)closSem_state)
  (t:('c,'ffi)closSem_state) <=>
     (state_clock s = state_clock t) /\ (state_ffi s = state_ffi t)
       /\ (closSem_state_max_app t = closSem_state_max_app s) /\
       closSem_state_compile
     s = state_cc (ignore_table clos_number_compile_inc)
       (closSem_state_compile t) /\ closSem_state_compile_oracle
     t = state_co (ignore_table clos_number_compile_inc)
       (closSem_state_compile_oracle s) /\
     fmap_rel (closProps_ref_rel (clos_numberProof_v_rel
       (closSem_state_max_app s))) (state_refs s) (state_refs t) /\
     EVERY2 (OPTREL (clos_numberProof_v_rel (closSem_state_max_app
       s))) (closSem_state_globals s) (closSem_state_globals t) /\
     (!n. SND (SND (closSem_state_compile_oracle s n)) = [] /\
          ~contains_App_SOME (closSem_state_max_app s) (FST (SND
            (closSem_state_compile_oracle s n)))) /\ closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY`;;
hol4_overload "state_rel" "clos_numberProof_state_rel";;

(* semantic functions respect relation *)

(* HOL4 clos_numberProofScript.sml:467-472: ML code, not ported *)

(* HOL4 clos_numberProofScript.sml:531-538: ML code, not ported *)

(* compiler correctness *)

(* HOL4 clos_numberProofScript.sml:637-645: code that the source has
   in a comment *)

(* preservation of observable semantics *)
