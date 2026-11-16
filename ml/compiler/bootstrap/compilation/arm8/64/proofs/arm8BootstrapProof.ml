(* ======================================================== *)
(*  arm8BootstrapProof: ported from HOL4's
    compiler/bootstrap/compilation/arm8/64/proofs/
      arm8BootstrapProofScript.sml
    A proof theory about arm8Bootstrap.ml, with 1 definition and 3
    theorems.  No file of the port needs it.  *)
(* ======================================================== *)

(*
  Proves an end-to-end correctness theorem for the bootstrapped compiler.
*)

needs "compiler/backend/arm8/arm8_config.ml";;
needs "compiler/backend/arm8/proofs/arm8_configProof.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/proofs/backendProof.ml";;
needs "compiler/bootstrap/compilation/arm8/64/arm8Bootstrap.ml";;
needs "compiler/bootstrap/translation/compiler64Prog.ml";;
needs "compiler/repl/repl_decs_allowed.ml";;
needs "lib/sptree.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "arm8BootstrapProof"
  ["arm8Bootstrap"; "arm8_configProof"; "backendProof"; "compiler64Prog";
   "repl_decs_allowed"; "semanticsProps"];;

(* with_clos_conf_simp[local] *)
let arm8BootstrapProof_with_clos_conf_simp = prove
 (`(mc_init_ok arm8_config (backend_config_bvl_conf_fupd
                   (\c. bvl_to_bvi_config_exp_cut_fupd (K t2)
                     (bvl_to_bvi_config_inline_size_limit_fupd (K t1) c))
                     (backend_config_clos_conf_fupd (K z) arm8_backend_config))
                     =
    mc_init_ok arm8_config arm8_backend_config) /\
   (~(closSem_state_max_app x = 0) /\ (match clos_to_bvl_config_known_conf x
     with NONE -> T | SOME k -> clos_known_config_val_approx_spt k = LN) ==>
    (backend_config_ok arm8_config (backend_config_clos_conf_fupd (K x)
      arm8_backend_config) =
     backend_config_ok arm8_config arm8_backend_config))`,
  CHEAT_TAC);;

let arm8BootstrapProof_compiler_instance_def = new_definition
  `arm8BootstrapProof_compiler_instance =
     mk_source_evalProof_compiler_instance (compile_inc_progs_for_eval
       arm8_config) BACKEND_CONFIG_v UNIV (LIST_v AST_DEC_v) decs_allowed
       info`;;

(* compiler_instance_lemma[local] *)
let arm8BootstrapProof_compiler_instance_lemma = prove
 (`INJ (source_evalProof_compiler_instance_config_v
  arm8BootstrapProof_compiler_instance) (UNIV:backend_config->bool)
  (UNIV:semanticPrimitives_v->bool)
  /\ source_evalProof_compiler_instance_init_state
   arm8BootstrapProof_compiler_instance = info
     /\ source_evalProof_compiler_instance_compiler_fun
   arm8BootstrapProof_compiler_instance = compile_inc_progs_for_eval
     arm8_config`,
  CHEAT_TAC);;

(* HOL4 arm8BootstrapProofScript.sml:41-49: a proof *)

(* HOL4 arm8BootstrapProofScript.sml:51-52: ML code, not ported *)

(* HOL4 arm8BootstrapProofScript.sml:54-67: ML code, not ported *)

(* HOL4 arm8BootstrapProofScript.sml:69-72: a theorem that HOL4 states as
   the value of an ML expression: cake_compiled_thm *)

(* and the interface *)
let _ = unhide_overloads ();;
