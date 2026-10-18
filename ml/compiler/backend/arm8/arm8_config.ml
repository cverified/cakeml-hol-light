(* ======================================================== *)
(*  arm8_config: ported from HOL4's
    compiler/backend/arm8/arm8_configScript.sml
    A definition theory, with 2 definitions and 1 theorem.  Needed
    by compiler.ml.  *)
(* ======================================================== *)

(*
  Define the compiler configuration for ARMv8
*)

needs "compiler/backend/backend.ml";;
needs "compiler/backend/presLang.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
(* HOL4 ancestors outside the port: arm8_target *)

let arm8_names_def = cake_define
  `arm8_names =
     ((insert 0 30 o
      insert 1 0 o
      insert 2 1 o
      insert 3 2 o
      insert 4 3 o
      insert 18 4 o
      insert 25 29 o
      insert 26 25 o
      insert 29 18 o
      insert 30 26) LN:num spt)`;;

(* HOL4 arm8_configScript.sml:32-33: a theorem that HOL4 states as
   the value of an ML expression *)

(* HOL4 arm8_configScript.sml:35-37: the ML values that the
   definitions below antiquote *)
(* TODO: this config may need to change *)
(* HOL4 arm8_configScript.sml:39-42: the ML values that the
   definitions below antiquote *)

let arm8_backend_config_def = cake_define
  `arm8_backend_config =
              mk_backend_config prim_src_config
                (clos_to_bvl_default_config)
                (bvl_to_bvi_default_config) (mk_data_to_word_config 4
                4 2 32 T F F F F F Simple) (mk_word_to_word_config 2
                []) (mk_word_to_stack_config 0 LN)
                (mk_stack_to_lab_config arm8_names F F)
                (mk_lab_to_target_config LN [] 0 5 NONE [] 104729) []
                default_tap_config []`;;
