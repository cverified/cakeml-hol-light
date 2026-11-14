(* ======================================================== *)
(*  ag32_config: ported from HOL4's
    compiler/backend/ag32/ag32_configScript.sml
    A definition theory, with 2 definitions and 1 theorem.  Needed
    by compiler.ml.  *)
(* ======================================================== *)

(*
  Define the compiler configuration for ag32
*)

needs "compiler/backend/backend.ml";;
needs "compiler/backend/presLang.ml";;
needs "lib/sptree.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ag32_config"
  ["asmProps"; "asmSem"; "backend"];;
(* HOL4 ancestors outside the port: ag32_target *)

let ag32_names_def = new_definition
  `ag32_names = (LN:num spt)`;;

(* HOL4 ag32_configScript.sml:14-15: a theorem that HOL4 states as
   the value of an ML expression: ag32_names_def *)

(* HOL4 ag32_configScript.sml:17-23: the ML values that the
   definitions below antiquote *)

let ag32_backend_config_def = new_definition
  `ag32_backend_config =
              mk_backend_config prim_src_config
                (clos_to_bvl_default_config)
                (bvl_to_bvi_default_config) (mk_data_to_word_config 0
                0 1 20 F F F F F F data_to_word_Simple)
                (mk_word_to_word_config 2 [])
                (mk_word_to_stack_config 0 LN)
                (mk_stack_to_lab_config ag32_names T F)
                (mk_lab_to_target_config LN [] 0 5 NONE [] 104729) []
                default_tap_config []`;;
