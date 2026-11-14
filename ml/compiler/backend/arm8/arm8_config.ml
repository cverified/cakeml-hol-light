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

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "arm8_config"
  ["asmProps"; "asmSem"; "backend"];;
(* HOL4 ancestors outside the port: arm8_target *)

let arm8_names_def = new_definition
  `arm8_names =
     ((
      // source can use 29 regs (0-28),
      // target's r18 should be avoided (platform reserved),
      // target's r26 must be avoided (extra encoding register),
      // target's r31 must be avoided (stack pointer),
      // source 0 must represent r30 (link register),
      // source 1-4 must be r0-r3 (1st 4 args),
      // top three (26-28) must be callee-saved (in r19-r28)
      sptree_insert 0 30 o
      sptree_insert 1 0 o
      sptree_insert 2 1 o
      sptree_insert 3 2 o
      sptree_insert 4 3 o
      sptree_insert 18 4 o
      sptree_insert 25 29 o
      sptree_insert 26 25 o
      // Next ones are for well-formedness only
      sptree_insert 29 18 o
      sptree_insert 30 26) LN:num spt)`;;

(* HOL4 arm8_configScript.sml:32-33: a theorem that HOL4 states as
   the value of an ML expression: arm8_names_def *)

(* HOL4 arm8_configScript.sml:35-37: the ML values that the
   definitions below antiquote *)
(* TODO: this config may need to change *)
(* HOL4 arm8_configScript.sml:39-42: the ML values that the
   definitions below antiquote *)

let arm8_backend_config_def = new_definition
  `arm8_backend_config =
              mk_backend_config prim_src_config
                (clos_to_bvl_default_config)
                (bvl_to_bvi_default_config) (mk_data_to_word_config 4
                4 2 32 T F F F F F data_to_word_Simple)
                (mk_word_to_word_config 2 [])
                (mk_word_to_stack_config 0 LN)
                (mk_stack_to_lab_config arm8_names F F)
                (mk_lab_to_target_config LN [] 0 5 NONE [] 104729) []
                default_tap_config []`;;
