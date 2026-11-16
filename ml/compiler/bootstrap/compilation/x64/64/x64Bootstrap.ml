(* ======================================================== *)
(*  x64Bootstrap: ported from HOL4's
    compiler/bootstrap/compilation/x64/64/x64BootstrapScript.sml
    A definition theory, with 1 definition and 1 theorem.  Needed by
    x64BootstrapProof.ml.  *)
(* ======================================================== *)

(*
  Evaluate the 64-bit version of the compiler into x64 machine code.
*)

needs "compiler/backend/backend.ml";;
needs "compiler/backend/x64/x64_config.ml";;
needs "compiler/bootstrap/translation/compiler64Prog.ml";;
needs "lib/sptree.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "x64Bootstrap"
  ["compiler64Prog"];;

let init_conf_def = new_definition
  `init_conf = backend_config_word_to_word_conf_fupd (K
         (word_to_word_config_reg_alg_fupd (K 4)
           (backend_config_word_to_word_conf x64_backend_config)))
           (backend_config_bvl_conf_fupd (K (bvl_to_bvi_config_exp_cut_fupd (K
           200) (bvl_to_bvi_config_inline_size_limit_fupd (K 3)
           bvl_to_bvi_default_config))) (backend_config_clos_conf_fupd (K
                         (clos_to_bvl_config_known_conf_fupd (K (SOME
                          (mk_clos_known_config 8 0 0 LN)))
                            clos_to_bvl_default_config))
                            (backend_config_source_conf_fupd (K
                            prim_src_config)
     x64_backend_config)))`;;

(* HOL4 x64BootstrapScript.sml:25-27: ML code, not ported *)

(* HOL4 x64BootstrapScript.sml:29-37: a theorem that HOL4 states as the
   value of an ML expression: compiler64_compiled *)

(* and the interface *)
let _ = unhide_overloads ();;
