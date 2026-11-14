(* ======================================================== *)
(*  compilerProof: ported from HOL4's
    compiler/proofs/compilerProofScript.sml
    A proof theory about compiler.ml, with 4 definitions and 8
    theorems.  No file of the port needs it.  *)
(* ======================================================== *)

(*
  Prove top-level correctness theorem for complete compiler, i.e. the
  combination of parsing, type inference, compiler backend.
*)

needs "compiler/backend/backend_passes.ml";;
needs "compiler/backend/proofs/backendProof.ml";;
needs "compiler/backend/proofs/lab_to_targetProof.ml";;
needs "compiler/backend/semantics/targetSem.ml";;
needs "compiler/compiler.ml";;
needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/proofs/envRel.ml";;
needs "compiler/inference/proofs/inferComplete.ml";;
needs "compiler/inference/proofs/inferSound.ml";;
needs "compiler/inference/proofs/type_dCanon.ml";;
needs "compiler/parsing/cmlParse.ml";;
needs "compiler/parsing/proofs/pegComplete.ml";;
needs "compiler/parsing/proofs/pegSound.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/lexer_fun.ml";;
needs "semantics/primTypes.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/proofs/typeSound.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/semantics.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "compilerProof"
  ["backendProof"; "compiler"; "envRel"; "evaluateProps"; "infer";
   "inferComplete"; "inferProps"; "inferSound"; "lab_to_targetProof";
   "pegComplete"; "pegSound"; "semantics"; "targetSem"; "typeSound";
   "typeSoundInvariants"];;

let config_ok_def = new_definition
  `config_ok (cc:'a compiler_config) mc <=>
     envRel_env_rel prim_tenv (compiler_config_inferencer_config cc)
       /\
     inf_set_tids_ienv prim_type_ids
       (compiler_config_inferencer_config cc) /\
     // TODO: ok?
     ~(compiler_config_input_is_sexp cc) /\
     ~(compiler_config_exclude_prelude cc) /\
     ~(compiler_config_skip_type_inference cc) /\
     ~(compiler_config_only_print_types cc) /\
     ~(compiler_config_only_print_sexp cc) /\
     backend_config_ok (compiler_config_asm_config cc)
       (compiler_config_backend_config cc) /\
     mc_conf_ok mc /\ mc_init_ok (compiler_config_asm_config cc)
       (compiler_config_backend_config cc) mc`;;

let initial_condition_def = new_definition
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
     // TODO: is this OK?
     envRel_env_rel (semantics_state_tenv st)
       (compiler_config_inferencer_config cc) /\
       semantics_state_type_ids
     // TODO: are these consistent (with the rest)? necessary?
     st = count start_type_id /\
     set_tids_tenv (count start_type_id) (semantics_state_tenv st) /\
     inf_set_tids_ienv (count start_type_id)
       (compiler_config_inferencer_config cc) /\
     // --
     ~(compiler_config_input_is_sexp cc) /\
     ~(compiler_config_exclude_prelude cc) /\
     ~(compiler_config_skip_type_inference cc) /\
     ~(compiler_config_only_print_types cc) /\
     ~(compiler_config_only_print_sexp cc) /\
     backend_config_ok (compiler_config_asm_config cc)
       (compiler_config_backend_config cc) /\
     mc_conf_ok mc /\ mc_init_ok (compiler_config_asm_config cc)
       (compiler_config_backend_config cc) mc`;;

let parse_prog_correct = prove
 (`(parse_prog s = peg_Failure y1 y2 ==> semantics_parse s = NONE) /\
   (parse_prog s = peg_Success x1 a x2 ==> semantics_parse s = SOME
     a)`,
  CHEAT_TAC);;

let infertype_prog_correct = prove
 (`envRel_env_rel (semantics_state_tenv st) ienv /\
  semantics_state_type_ids
   st = count start_type_id /\
   inf_set_tids_ienv (count start_type_id) ienv /\
   set_tids_tenv (count start_type_id) (semantics_state_tenv st) ==>
   (?c' x. infertype_prog ienv p = (if can_type_prog st p then
     M_success c' else M_failure x))`,
  CHEAT_TAC);;

let compile_tap_compile = prove
 (`!asm_conf conf p res td.
     compile_tap asm_conf conf p = (res,td) ==>
     backend_compile asm_conf conf p = res`,
  CHEAT_TAC);;

let compilerProof_read_limits_def = new_definition
  `compilerProof_read_limits cc mc ms = backendProof_read_limits
  (compiler_config_asm_config cc) (compiler_config_backend_config cc)
  mc ms`;;

let compilerProof_is_safe_for_space_def = new_definition
  `compilerProof_is_safe_for_space ffi cc =
  backendProof_is_safe_for_space ffi (compiler_config_asm_config cc)
  (compiler_config_backend_config cc)`;;

let compile_correct_gen = prove
 (`!(st:'ffi semantics_state) (cc:'a compiler_config) prelude input mc
  data_sp cbspace.
    initial_condition st cc mc ==>
    (match FST (compiler_compile cc prelude input) with M_failure
      (ParseError e) -> semantics_semantics st prelude input =
      CannotParse | M_failure (TypeError e) -> semantics_semantics st
      prelude input = IllTyped | M_failure AssembleError -> T |
      // see theorem about to_lab to avoid AssembleError
      M_failure (ConfigError e) -> T |
      // configuration string is malformed
      M_success (code,data,c) ->
      (?behaviours source_decs.
        (semantics_semantics st prelude input = Execute behaviours)
          /\
        semantics_parse (lexer_fun input) = SOME source_decs /\
        (!ms.
          installed code cbspace data data_sp (ffi_names
            (backend_config_lab_conf c))
            (heap_regs (stack_to_lab_config_reg_names
              (backend_config_stack_conf (compiler_config_backend_config
              cc)))) mc (lab_to_target_config_shmem_extra
              (backend_config_lab_conf c)) ms ==>
            machine_sem mc (state_ffi (semantics_state_sem_st st)) ms
              SUBSET
              extend_with_resource_limit'
                (compilerProof_is_safe_for_space (state_ffi
                  (semantics_state_sem_st st)) cc
                   (APPEND prelude source_decs)
                     (compilerProof_read_limits cc mc ms))
                behaviours)))`,
  CHEAT_TAC);;

(* compile_correct_lemma *)
let compilerProof_compile_correct_lemma = prove
 (`!(ffi:'ffi ffi_state) prelude input (cc:'a compiler_config) mc
  data_sp cbspace.
     config_ok cc mc ==>
     (match FST (compiler_compile cc prelude input) with M_failure
       (ParseError e) -> semantics_init ffi prelude input = CannotParse
       | M_failure (TypeError e) -> semantics_init ffi prelude input =
       IllTyped | M_failure AssembleError -> T |
       // see theorem about to_lab to avoid AssembleError
       M_failure (ConfigError e) -> T |
       // configuration string is malformed
       M_success (code,data,c) ->
       (?behaviours source_decs.
         (semantics_init ffi prelude input = Execute behaviours) /\
         semantics_parse (lexer_fun input) = SOME source_decs /\
         (!ms.
           installed code cbspace data data_sp (ffi_names
             (backend_config_lab_conf c)) (heap_regs
             (stack_to_lab_config_reg_names (backend_config_stack_conf
             (compiler_config_backend_config cc)))) mc
             (lab_to_target_config_shmem_extra (backend_config_lab_conf
             c)) ms ==>
             machine_sem mc ffi ms SUBSET
               extend_with_resource_limit'
                 (compilerProof_is_safe_for_space ffi cc
                    (APPEND prelude source_decs)
                      (compilerProof_read_limits cc mc ms))
                 behaviours)))`,
  CHEAT_TAC);;

let compile_correct_safe_for_space = prove
 (`!(ffi:'ffi ffi_state) prelude input (cc:'a compiler_config) mc
  data_sp cbspace code data c c'.
     config_ok cc mc ==>
     compiler_compile cc prelude input = (M_success (code,data,c),c')
       ==>
       (?behaviours source_decs.
         (semantics_init ffi prelude input = Execute behaviours) /\
         semantics_parse (lexer_fun input) = SOME source_decs /\
         (!ms.
           compilerProof_is_safe_for_space ffi cc (APPEND prelude
             source_decs)
             (
              // cost semantics
              compilerProof_read_limits cc mc ms) /\
           installed code cbspace data data_sp (ffi_names
             (backend_config_lab_conf c))
             (heap_regs (stack_to_lab_config_reg_names
               (backend_config_stack_conf
               (compiler_config_backend_config cc)))) mc
               (lab_to_target_config_shmem_extra
               (backend_config_lab_conf c)) ms ==>
           machine_sem mc ffi ms = behaviours))
   // <-- equality`,
  CHEAT_TAC);;

(* compile_correct *)
let compilerProof_compile_correct = prove
 (`!(ffi:'ffi ffi_state) prelude input (cc:'a compiler_config) mc
  data_sp cbspace.
       config_ok cc mc ==>
       (match FST (compiler_compile cc prelude input) with M_failure
         (ParseError e) -> semantics_init ffi prelude input =
         CannotParse | M_failure (TypeError e) -> semantics_init ffi
         prelude input = IllTyped | M_failure AssembleError -> T |
         M_failure (ConfigError e) -> T | M_success (code,data,c) ->
         (?behaviours.
           (semantics_init ffi prelude input = Execute behaviours) /\
           (!ms.
             installed code cbspace data data_sp (ffi_names
               (backend_config_lab_conf c))
               (heap_regs (stack_to_lab_config_reg_names
                 (backend_config_stack_conf
                 (compiler_config_backend_config cc)))) mc
                 (lab_to_target_config_shmem_extra
                 (backend_config_lab_conf c)) ms ==>
             machine_sem mc ffi ms SUBSET
               extend_with_resource_limit behaviours)))`,
  CHEAT_TAC);;
(* see the compile_correct_safe_for_space version above
   for the one without the ⊆ and extend_with_resource_limit *)

let type_config_ok = prove
 (`envRel_env_rel prim_tenv infer_init_config /\
   inf_set_tids_ienv prim_type_ids infer_init_config`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
