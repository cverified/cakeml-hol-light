(* ======================================================== *)
(*  mips_config: ported from HOL4's
    compiler/backend/mips/mips_configScript.sml  *)
(* ======================================================== *)

(*
  Define the compiler configuration for MIPS
*)

needs "compiler/backend/backend.ml";;
needs "compiler/backend/presLang.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
(* HOL4 ancestors outside the port: mips_target *)

let mips_names_def = cake_define
  `mips_names =
     ((insert 0 31 o
      insert 1 4 o
      insert 2 5 o
      insert 3 6 o
      insert 4 7 o
      insert 7 2 o
      insert 5 24 o
      insert 6 3 o
      insert 24 0 o
      insert 31 1) LN:num spt)`;;

(* HOL4 mips_configScript.sml:38-44: the ML values that the
   definitions below antiquote *)

let mips_backend_config_def = cake_define
  `mips_backend_config =
              mk_backend_config prim_src_config
                (clos_to_bvl_default_config)
                (bvl_to_bvi_default_config) (mk_data_to_word_config 4
                4 2 32 T F F F T F Simple) (mk_word_to_word_config 2
                []) (mk_word_to_stack_config 0 LN)
                (mk_stack_to_lab_config mips_names F F)
                (mk_lab_to_target_config LN [] 0 5 NONE [] 104729) []
                default_tap_config []`;;
