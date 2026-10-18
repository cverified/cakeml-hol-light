(* ======================================================== *)
(*  ag32_config: ported from HOL4's
    compiler/backend/ag32/ag32_configScript.sml  *)
(* ======================================================== *)

(*
  Define the compiler configuration for ag32
*)

needs "compiler/backend/backend.ml";;
needs "compiler/backend/presLang.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
(* HOL4 ancestors outside the port: ag32_target *)

let ag32_names_def = cake_define
  `ag32_names = (LN:num spt)`;;

(* HOL4 ag32_configScript.sml:17-23: the ML values that the
   definitions below antiquote *)

let ag32_backend_config_def = cake_define
  `ag32_backend_config =
              mk_backend_config prim_src_config
                (clos_to_bvl_default_config)
                (bvl_to_bvi_default_config) (mk_data_to_word_config 0
                0 1 20 F F F F F F Simple) (mk_word_to_word_config 2
                []) (mk_word_to_stack_config 0 LN)
                (mk_stack_to_lab_config ag32_names T F)
                (mk_lab_to_target_config LN [] 0 5 NONE [] 104729) []
                default_tap_config []`;;
