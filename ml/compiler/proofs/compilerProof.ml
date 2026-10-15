(* ======================================================== *)
(*  compilerProof: ported from HOL4's
    compiler/proofs/compilerProofScript.sml  *)
(* ======================================================== *)

(*
  Prove top-level correctness theorem for complete compiler, i.e. the
  combination of parsing, type inference, compiler backend.
*)

needs "compiler/backend/proofs/backendProof.ml";;
needs "compiler/backend/proofs/bvi_letProof.ml";;
needs "compiler/backend/proofs/lab_to_targetProof.ml";;
needs "compiler/backend/semantics/targetSem.ml";;
needs "compiler/compiler.ml";;
needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/proofs/envRel.ml";;
needs "compiler/inference/proofs/inferComplete.ml";;
needs "compiler/inference/proofs/inferSound.ml";;
needs "compiler/inference/proofs/type_dCanon.ml";;
needs "compiler/parsing/proofs/pegComplete.ml";;
needs "compiler/parsing/proofs/pegSound.ml";;
needs "semantics/primTypes.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/typeSound.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/semantics.ml";;

let config_ok_def = cake_define
  `config_ok (cc:'a compiler_config) mc <=>
     env_rel prim_tenv (compiler_config_inferencer_config cc) /\
     inf_set_tids_ienv prim_type_ids
       (compiler_config_inferencer_config cc) /\
     ~compiler_config_input_is_sexp cc /\
     ~compiler_config_exclude_prelude cc /\
     ~compiler_config_skip_type_inference cc /\
     ~compiler_config_only_print_types cc /\
     ~compiler_config_only_print_sexp cc /\
     backend_config_ok (compiler_config_asm_config cc)
       (compiler_config_backend_config cc) /\
     mc_conf_ok mc /\ mc_init_ok (compiler_config_asm_config cc)
       (compiler_config_backend_config cc) mc`;;

let initial_condition_def = cake_define
  `initial_condition (st:'ffi semantics_state) (cc:'a compiler_config)
  mc <=>
     (semantics_state_sem_st st,semantics_state_sem_env st) = THE
       (prim_sem_env (state_ffi (semantics_state_sem_st st))) /\
     (?ctMap.
       type_sound_invariant (semantics_state_sem_st st)
         (semantics_state_sem_env st) ctMap FEMPTY {}
         (semantics_state_tenv st) /\
       FRANGE ((SND o SND) o_f ctMap) SUBSET semantics_state_type_ids
         st) /\
     env_rel (semantics_state_tenv st)
       (compiler_config_inferencer_config cc) /\
       semantics_state_type_ids
     st = count start_type_id /\
     set_tids_tenv (count start_type_id) (semantics_state_tenv st) /\
     inf_set_tids_ienv (count start_type_id)
       (compiler_config_inferencer_config cc) /\
     ~compiler_config_input_is_sexp cc /\
     ~compiler_config_exclude_prelude cc /\
     ~compiler_config_skip_type_inference cc /\
     ~compiler_config_only_print_types cc /\
     ~compiler_config_only_print_sexp cc /\
     backend_config_ok (compiler_config_asm_config cc)
       (compiler_config_backend_config cc) /\
     mc_conf_ok mc /\ mc_init_ok (compiler_config_asm_config cc)
       (compiler_config_backend_config cc) mc`;;

let read_limits_def = cake_define
  `compilerProof_read_limits cc mc ms = backendProof_read_limits
  (compiler_config_asm_config cc) (compiler_config_backend_config cc)
  mc ms`;;
hol4_overload "read_limits" "compilerProof_read_limits";;

let is_safe_for_space_def = cake_define
  `compilerProof_is_safe_for_space ffi cc =
  backendProof_is_safe_for_space ffi (compiler_config_asm_config cc)
  (compiler_config_backend_config cc)`;;
hol4_overload "is_safe_for_space" "compilerProof_is_safe_for_space";;
(* HOL4 ML code, not ported:
          (* see the compile_correct_safe_for_space version above
             for the one without the ⊆ and extend_with_resource_limit
               *)`,
*)
(* HOL4 ML code, not ported:
  rw [] \\ mp_tac (SPEC_ALL compile_correct_lemma)
  \\ fs [] \\ TOP_CASE_TAC \\ fs []
  \\ rename [‘(M_success a,_)’]
  \\ PairCases_on `a` \\ fs [] \\ strip_tac \\ fs []
  \\ rw [] \\ first_x_assum drule \\ rw []
  \\ match_mp_tac SUBSET_TRANS
  \\ asm_exists_tac \\ fs
    [semanticsPropsTheory.extend_with_resource_limit'_SUBSET])
  |> check_thm;
*)
