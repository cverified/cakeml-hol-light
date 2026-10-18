(* ======================================================== *)
(*  arm7_config: ported from HOL4's
    compiler/backend/arm7/arm7_configScript.sml
    A definition theory, with 2 definitions and 1 theorem.  Needed
    by compiler.ml.  *)
(* ======================================================== *)

(*
  Define the compiler configuration for ARMv7
*)

needs "compiler/backend/backend.ml";;
needs "compiler/backend/presLang.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
(* HOL4 ancestors outside the port: arm7_target *)

let arm7_names_def = cake_define
  `arm7_names =
     ((insert 0 14 o
      insert 1 0 o
      insert 2 1 o
      insert 3 2 o
      insert 4 3 o
      insert 12 8 o
      insert 13 10 o
      insert 8 4 o
      insert 10 12 o
      insert 14 13) LN:num spt)`;;

(* HOL4 arm7_configScript.sml:32-33: a theorem that HOL4 states as
   the value of an ML expression *)

(* HOL4 arm7_configScript.sml:35-41: the ML values that the
   definitions below antiquote *)

let arm7_backend_config_def = cake_define
  `arm7_backend_config =
              mk_backend_config prim_src_config
                (clos_to_bvl_default_config)
                (bvl_to_bvi_default_config) (mk_data_to_word_config 0
                0 1 20 F F T T F F Simple) (mk_word_to_word_config 2
                []) (mk_word_to_stack_config 0 LN)
                (mk_stack_to_lab_config arm7_names T F)
                (mk_lab_to_target_config LN [] 0 5 NONE [] 104729) []
                default_tap_config []`;;
