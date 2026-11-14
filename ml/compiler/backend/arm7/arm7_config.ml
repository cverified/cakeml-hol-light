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

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "arm7_config"
  ["asmProps"; "asmSem"; "backend"];;
(* HOL4 ancestors outside the port: arm7_target *)

let arm7_names_def = new_definition
  `arm7_names =
     ((
      // source can use 14 regs,
      // target's r15 must be avoided (pc),
      // target's r13 must be avoided (stack pointer),
      // source 0 must represent r14 (link register),
      // source 1-4 must be r0-r3 (1st 4 arguments)
      // the top three (source 11-13) must be callee-saved
      // (callee-saved include: r4-r8, r10-11)
      balanced_map_insert 0 14 o
      balanced_map_insert 1 0 o
      balanced_map_insert 2 1 o
      balanced_map_insert 3 2 o
      balanced_map_insert 4 3 o
      balanced_map_insert 12 8 o
      balanced_map_insert 13 10 o
      // the rest just ensures that the mapping is well-formed
      balanced_map_insert 8 4 o
      balanced_map_insert 10 12 o
      balanced_map_insert 14 13) LN:num spt)`;;

(* HOL4 arm7_configScript.sml:32-33: a theorem that HOL4 states as
   the value of an ML expression: arm7_names_def *)

(* HOL4 arm7_configScript.sml:35-41: the ML values that the
   definitions below antiquote *)

let arm7_backend_config_def = new_definition
  `arm7_backend_config =
              mk_backend_config prim_src_config
                (clos_to_bvl_default_config)
                (bvl_to_bvi_default_config) (mk_data_to_word_config 0
                0 1 20 F F T T F F data_to_word_Simple)
                (mk_word_to_word_config 2 [])
                (mk_word_to_stack_config 0 LN)
                (mk_stack_to_lab_config arm7_names T F)
                (mk_lab_to_target_config LN [] 0 5 NONE [] 104729) []
                default_tap_config []`;;
