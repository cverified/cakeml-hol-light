(* ======================================================== *)
(*  primSemEnv: ported from HOL4's
    semantics/proofs/primSemEnvScript.sml
    A proof theory, with no definitions and 2 theorems.  Needed by
    backendProof.ml and typeSound.ml.  *)
(* ======================================================== *)

(*
  Proof about the primitive semantic environment
*)

needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/namespace.ml";;
needs "semantics/primTypes.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/semantics.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "primSemEnv"
  ["ast"; "evaluate"; "namespace"; "namespaceProps"; "primTypes";
   "semanticPrimitives"; "semanticPrimitivesProps"; "semantics";
   "typeSoundInvariants"; "typeSysProps"; "typeSystem"];;

let prim_sem_env_eq =
  CAKE_EVAL [prim_sem_env_def; add_to_sem_env_def; nsEmpty_def;
  prim_types_program_def; unknown_loc_def; extend_dec_env_def; nsAppend_def]
  `prim_sem_env (ffi:'ffi ffi_state)`;;

let prim_type_sound_invariants = prove
 (`!type_ids sem_st prim_env.
     (sem_st,prim_env) = THE (prim_sem_env ffi) /\
     DISJOINT type_ids {Tlist_num,Tbool_num,Texn_num} ==>
     (?ctMap.
       type_sound_invariant sem_st prim_env ctMap FEMPTY type_ids prim_tenv
         /\
       FRANGE ((SND o SND) o_f ctMap) SUBSET prim_type_ids)`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
