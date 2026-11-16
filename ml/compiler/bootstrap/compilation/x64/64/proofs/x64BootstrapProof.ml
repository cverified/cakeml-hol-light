(* ======================================================== *)
(*  x64BootstrapProof: ported from HOL4's
    compiler/bootstrap/compilation/x64/64/proofs/
      x64BootstrapProofScript.sml
    A proof theory about x64Bootstrap.ml, with 4 definitions and 25
    theorems.  No file of the port needs it.  *)
(* ======================================================== *)

(*
  Proves an end-to-end correctness theorem for the bootstrapped compiler.
*)

needs "basis/CommandLineProof.ml";;
needs "basis/TextIOProof.ml";;
needs "basis/basis_ffi.ml";;
needs "basis/fsFFIProps.ml";;
needs "basis/pure/mlstring.ml";;
needs "candle/prover/ast_extras.ml";;
needs "candle/prover/candle_kernel_vals.ml";;
needs "candle/prover/candle_prover_inv.ml";;
needs "candle/prover/candle_prover_semantics.ml";;
needs "candle/set-theory/setModel.ml";;
needs "candle/set-theory/setSpec.ml";;
needs "candle/standard/monadic/holKernelProof.ml";;
needs "candle/standard/semantics/holConsistency.ml";;
needs "candle/standard/semantics/holLightConsistency.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/proofs/backendProof.ml";;
needs "compiler/backend/proofs/lab_to_targetProof.ml";;
needs "compiler/backend/proofs/source_evalProof.ml";;
needs "compiler/backend/semantics/targetSem.ml";;
needs "compiler/backend/x64/proofs/x64_configProof.ml";;
needs "compiler/backend/x64/x64_config.ml";;
needs "compiler/bootstrap/compilation/x64/64/proofs/replProof.ml";;
needs "compiler/bootstrap/compilation/x64/64/x64Bootstrap.ml";;
needs "compiler/bootstrap/translation/compiler64Prog.ml";;
needs "compiler/repl/repl_decs_allowed.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/semantics.ml";;
needs "translator/ml_prog.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "x64BootstrapProof"
  ["backendProof"; "candle_prover_semantics"; "compiler64Prog";
   "holLightConsistency"; "mlstring"; "replProof"; "semanticsProps";
   "x64Bootstrap"; "x64_configProof"];;

(* with_clos_conf_simp[local] *)
let x64BootstrapProof_with_clos_conf_simp = prove
 (`(mc_init_ok x64_config (backend_config_bvl_conf_fupd
                   (\c. bvl_to_bvi_config_exp_cut_fupd (K t2)
                     (bvl_to_bvi_config_inline_size_limit_fupd (K t1) c))
                     (backend_config_clos_conf_fupd (K z) x64_backend_config))
                     =
    mc_init_ok x64_config x64_backend_config) /\
   (~(closSem_state_max_app x = 0) /\ (match clos_to_bvl_config_known_conf x
     with NONE -> T | SOME k -> clos_known_config_val_approx_spt k = LN) ==>
    (backend_config_ok x64_config (backend_config_clos_conf_fupd (K x)
      x64_backend_config) =
     backend_config_ok x64_config x64_backend_config))`,
  CHEAT_TAC);;

let x64BootstrapProof_compiler_instance_def = new_definition
  `x64BootstrapProof_compiler_instance =
     mk_source_evalProof_compiler_instance (compile_inc_progs_for_eval
       x64_config) BACKEND_CONFIG_v UNIV (LIST_v AST_DEC_v) decs_allowed
       info`;;

(* compiler_instance_lemma[local] *)
let x64BootstrapProof_compiler_instance_lemma = prove
 (`INJ (source_evalProof_compiler_instance_config_v
  x64BootstrapProof_compiler_instance) (UNIV:backend_config->bool)
  (UNIV:semanticPrimitives_v->bool)
  /\ source_evalProof_compiler_instance_init_state
   x64BootstrapProof_compiler_instance = info
     /\ source_evalProof_compiler_instance_compiler_fun
   x64BootstrapProof_compiler_instance = compile_inc_progs_for_eval
     x64_config`,
  CHEAT_TAC);;

let backend_config_ok_init_conf = prove
 (`backend_config_ok x64_config init_conf`,
  CHEAT_TAC);;

let mc_init_ok_init_conf = prove
 (`mc_init_ok x64_config init_conf mc = mc_init_ok x64_config
  x64_backend_config mc`,
  CHEAT_TAC);;

(* HOL4 x64BootstrapProofScript.sml:56-64: a proof *)

(* HOL4 x64BootstrapProofScript.sml:66-67: ML code, not ported *)

(* HOL4 x64BootstrapProofScript.sml:69-82: ML code, not ported *)

(* HOL4 x64BootstrapProofScript.sml:84-86: a theorem that HOL4 states as the
   value of an ML expression: cake_compiled_thm *)

(* --- *)

(* [local] *)
let mk_compiler_fun_from_ci_tuple = prove
 (`mk_compiler_fun_from_ci c = (\(x,y,z). mk_compiler_fun_from_ci c (x,y,z))`,
  CHEAT_TAC);;

let mk_init_eval_state_lemma =
  SIMP_RULE [mk_compiler_fun_from_ci_def; GSYM compiler_inst_def]
  (ONCE_REWRITE_RULE [mk_compiler_fun_from_ci_tuple] (SIMP_CONV
  [x64BootstrapProof_compiler_instance_def; mk_init_eval_state_def]
  `mk_init_eval_state x64BootstrapProof_compiler_instance`));;

(* HOL4 x64BootstrapProofScript.sml:104-106: the overload
   init_eval_state_for, which the port expands *)

let candle_soundness = prove
 (`res IN semantics_prog ((semanticPrimitives_state_eval_state_fupd (K (SOME
  (mk_init_eval_state x64BootstrapProof_compiler_instance)))
  (ml_prog_init_state (basis_ffi ext cl fs)))) init_env (APPEND candle_code
  prog) /\
   ALL safe_dec prog /\ prog_syntax_ok candle_code /\ ~(res = ffi_Fail) ==>
   (!e. e IN events_of res ==> ok_event e)`,
  CHEAT_TAC);;

(* HOL4 x64BootstrapProofScript.sml:125-131: a theorem that HOL4 states as
   the value of an ML expression: repl_not_fail *)

(* HOL4 x64BootstrapProofScript.sml:133-135: the overload basis_init_ok,
   which the port expands *)

let repl_not_fail_thm = prove
 (`has_repl_flag (TL cl) /\ (\cl fs. STD_streams fs /\ wfFS fs /\ wfcl cl
  /\ (\fs. CARD (set_of_list (MAP FST (IO_fs_infds fs))) < MIN (IO_fs_maxFD fs)
  (256 EXP 8)) fs /\
            file_content fs (implode "config_enc_str.txt") = SOME conf) cl
              fs ==> ~(ffi_Fail IN semantics_prog
              ((semanticPrimitives_state_eval_state_fupd (K (SOME
              (mk_init_eval_state x64BootstrapProof_compiler_instance)))
              (ml_prog_init_state (basis_ffi ext cl fs)))) init_env
              compiler64_prog)`,
  CHEAT_TAC);;

(* HOL4 x64BootstrapProofScript.sml:145-152: ML code, not ported *)

let repl_ready_to_run_def = new_definition
  `repl_ready_to_run cl fs (mc,ms) <=>
     (?cbspace data_sp.
       has_repl_flag (TL cl) /\ wfcl cl /\ wfFS fs /\ STD_streams fs /\
       (\fs. CARD (set_of_list (MAP FST (IO_fs_infds fs))) < MIN
         (IO_fs_maxFD fs) (256 EXP 8)) fs /\
       file_content fs (implode "config_enc_str.txt") = SOME conf /\
       mc_conf_ok mc /\ mc_init_ok x64_config x64_backend_config mc /\
       installed code cbspace data data_sp (lab_to_target_config_ffi_names
         (backend_config_lab_conf
         info))
         (heap_regs (stack_to_lab_config_reg_names
           (backend_config_stack_conf x64_backend_config)))
         mc (lab_to_target_config_shmem_extra (backend_config_lab_conf
           info)) ms)`;;

(* HOL4 x64BootstrapProofScript.sml:167: the overload machine_sem, which the
   port expands *)

let compile_correct_applied = prove
 (`~(ffi_Fail IN semantics_prog ((semanticPrimitives_state_eval_state_fupd (K
  (SOME (mk_init_eval_state x64BootstrapProof_compiler_instance)))
  (ml_prog_init_state (basis_ffi ext cl fs)))) init_env compiler64_prog) /\
     repl_ready_to_run cl fs ms ==>
     (\ffi (mc,ms). targetSem_machine_sem mc ffi ms) (basis_ffi ext cl fs)
       ms SUBSET
       extend_with_resource_limit
         (semantics_prog ((semanticPrimitives_state_eval_state_fupd (K
           (SOME (mk_init_eval_state x64BootstrapProof_compiler_instance)))
           (ml_prog_init_state (basis_ffi ext cl fs)))) init_env
           compiler64_prog)`,
  CHEAT_TAC);;

(* [local] *)
let isPREFIX_MEM = prove
 (`!xs ys. isPREFIX xs ys ==> (!x. ag32_MEM x xs ==> ag32_MEM x ys)`,
  CHEAT_TAC);;

(* [local] *)
let LPREFIX_MEM = prove
 (`!xs ys. LPREFIX (fromList xs) ys ==> (!x. ag32_MEM x xs ==> x IN LSET ys)`,
  CHEAT_TAC);;

let repl_ready_to_run_imp = prove
 (`repl_ready_to_run cl fs ms ==>
   has_repl_flag (TL cl) /\ (\cl fs. STD_streams fs /\ wfFS fs /\ wfcl cl
     /\ (\fs. CARD (set_of_list (MAP FST (IO_fs_infds fs))) < MIN (IO_fs_maxFD
     fs) (256 EXP 8)) fs /\
            file_content fs (implode "config_enc_str.txt") = SOME conf) cl
              fs`,
  CHEAT_TAC);;

(* HOL4 x64BootstrapProofScript.sml:204: ML code, not ported *)

let safe_dec'_def = new_definition
  `safe_dec' x1 =
   match x1 with
     Dlet locs pat x -> safe_exp x
   | Dletrec locs' funs -> ALL safe_exp (MAP (SND o SND) funs)
   | _ -> T`;;

let safe_dec_thm = prove
 (`safe_dec = every_dec safe_dec'`,
  CHEAT_TAC);;

let safe_exp'_def = new_definition
  `safe_exp' x1' =
     match x1' with
       clos_Con (SOME i) _ -> (~(id_to_n i IN kernel_ctors))
     | ast_App (clos_FFI n) _ -> (~(n = kernel_ffi))
     | _ -> T`;;

let safe_exp_thm = prove
 (`safe_exp = ast_extras_every_exp safe_exp'`,
  CHEAT_TAC);;

(* [local] *)
let MAP_SND = prove
 (`MAP SND [] = [] /\
   MAP SND (CONS (x1,x2) xs) = CONS x2 (MAP SND xs)`,
  CHEAT_TAC);;

(* [local] *)
let MAP_SND_SND = prove
 (`MAP (SND o SND) [] = [] /\
   MAP (SND o SND) (CONS (x1,x2,x3) xs) = CONS x3 (MAP (SND o SND) xs)`,
  CHEAT_TAC);;

(* HOL4 x64BootstrapProofScript.sml:253-259: ML code, not ported *)

(* HOL4 x64BootstrapProofScript.sml:261-270: a proof *)

let compiler64_prog_eq_candle_code_append = prove
 (`// this is very slow
   ?prog. compiler64_prog = APPEND candle_code prog /\ ALL safe_dec prog`,
  CHEAT_TAC);;

(* [local] *)
let prog_syntax_ok_candle_code = prove
 (`prog_syntax_ok candle_code`,
  CHEAT_TAC);;

let events_of_extend_with_resource_limit = prove
 (`e IN events_of res1 /\ res1 IN sem1 /\
   sem1 SUBSET extend_with_resource_limit sem2 ==>
   (?res2. e IN events_of res2 /\ res2 IN sem2)`,
  CHEAT_TAC);;

let candle_top_level_soundness = prove
 (`repl_ready_to_run cl fs ms /\ res IN (\ffi (mc,ms). targetSem_machine_sem mc
  ffi ms) (basis_ffi ext cl fs) ms ==> ~(res = ffi_Fail) /\
   (!e. e IN events_of res ==> ok_event e)`,
  CHEAT_TAC);;

(* Every byte string the kernel writes on its own channel decodes back to the
   theorem and the context it was proved in, and that context extends the
   initial one. So a reader of the channel can decide the shape of the context
   and, when it is one of the shapes a HOL Light session builds, conclude that
   the theory the theorem lives in is consistent. *)

let candle_top_level_consistency_axiom_free = prove
 (`repl_ready_to_run cl fs ms /\ res IN (\ffi (mc,ms). targetSem_machine_sem mc
  ffi ms) (basis_ffi ext cl fs) ms ==> ~(res = ffi_Fail) /\
   (!out y. IO_event (ffi_ExtCall kernel_ffi) out y IN events_of res ==>
     (?ctxt th.
       THM ctxt th /\ thm2bytes ctxt th = out /\
       string_to_thm (bytes2str out) = (ctxt,th) /\ extends ctxt init_ctxt
         /\
       ((\l. ALL (\u. !p. ~(u = NewAxiom p)) l) ctxt ==> consistent_theory
         ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list).
         ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
         ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
         ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
         APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt))
         ctxt)) ctxt))))`,
  CHEAT_TAC);;

let candle_top_level_consistency_fhol_light = prove
 (`repl_ready_to_run cl fs ms /\ res IN (\ffi (mc,ms). targetSem_machine_sem mc
  ffi ms) (basis_ffi ext cl fs) ms ==> ~(res = ffi_Fail) /\
   (!out y. IO_event (ffi_ExtCall kernel_ffi) out y IN events_of res ==>
     (?ctxt th.
       THM ctxt th /\ thm2bytes ctxt th = out /\
       string_to_thm (bytes2str out) = (ctxt,th) /\ extends ctxt init_ctxt
         /\
       (fhol_light_ctxt ctxt ==> consistent_theory
         ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list).
         ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
         ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
         ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
         APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt))
         ctxt)) ctxt))))`,
  CHEAT_TAC);;

let candle_top_level_consistency_hol_light = prove
 (`repl_ready_to_run cl fs ms /\ res IN (\ffi (mc,ms). targetSem_machine_sem mc
  ffi ms) (basis_ffi ext cl fs) ms ==> ~(res = ffi_Fail) /\
   (!out y. IO_event (ffi_ExtCall kernel_ffi) out y IN events_of res ==>
     (?ctxt th.
       THM ctxt th /\ thm2bytes ctxt th = out /\
       string_to_thm (bytes2str out) = (ctxt,th) /\ extends ctxt init_ctxt
         /\
       (hol_light_ctxt ctxt /\ (?inf'. is_infinite V_mem inf') ==>
          consistent_theory ((\(ctxt:holSyntax_update list).
            ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt.
            FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap
            ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt))
            ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
            (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
            ctxt))))`,
  CHEAT_TAC);;

(* HOL4 x64BootstrapProofScript.sml:411-416: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
