(* ======================================================== *)
(*  mips_config: ported from HOL4's
    compiler/backend/mips/mips_configScript.sml
    A definition theory, with 2 definitions and 1 theorem.  Needed
    by compiler.ml.  *)
(* ======================================================== *)

(*
  Define the compiler configuration for MIPS
*)

needs "compiler/backend/backend.ml";;
needs "compiler/backend/presLang.ml";;
needs "lib/sptree.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "mips_config"
  ["asmProps"; "asmSem"; "backend"];;
(* HOL4 ancestors outside the port: mips_target *)

let mips_names_def = new_definition
  `mips_names =
     ((
      // source can use 24 regs (r2-r24,r31),
      // target's r0 must be avoided (hardcoded to 0),
      // target's r1 must be avoided (used by encoder in asm),
      // target's r25 and r28 are used to set up PIC
      // target's r29 must be avoided (stack pointer),
      // target's r26-r27 avoided (reserved for OS kernel),
      // target's r30 must be avoided (used by encoder in asm),
      // source 0 must represent r31 (link register),
      // source 1-4 must be r4-r7 (1st 4 args),
      // top 3 (21-23) must be callee-saved (in 16-23, 28, 30)
      balanced_map_insert 0 31 o
      balanced_map_insert 1 4 o
      balanced_map_insert 2 5 o
      balanced_map_insert 3 6 o
      balanced_map_insert 4 7 o
      // the rest just ensures that the mapping is well-formed
      balanced_map_insert 7 2 o
      balanced_map_insert 5 24 o
      balanced_map_insert 6 3 o
      balanced_map_insert 24 0 o
      balanced_map_insert 31 1) LN:num spt)`;;

(* HOL4 mips_configScript.sml:35-36: a theorem that HOL4 states as
   the value of an ML expression: mips_names_def *)

(* HOL4 mips_configScript.sml:38-44: the ML values that the
   definitions below antiquote *)

let mips_backend_config_def = new_definition
  `mips_backend_config =
              mk_backend_config prim_src_config
                (clos_to_bvl_default_config)
                (bvl_to_bvi_default_config) (mk_data_to_word_config 4
                4 2 32 T F F F T F data_to_word_Simple)
                (mk_word_to_word_config 2 [])
                (mk_word_to_stack_config 0 LN)
                (mk_stack_to_lab_config mips_names F F)
                (mk_lab_to_target_config LN [] 0 5 NONE [] 104729) []
                default_tap_config []`;;
