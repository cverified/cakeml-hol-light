(* ======================================================== *)
(*  riscv_config: ported from HOL4's
    compiler/backend/riscv/riscv_configScript.sml
    A definition theory, with 2 definitions and 1 theorem.  Needed
    by compiler.ml.  *)
(* ======================================================== *)

(*
  Define the compiler configuration for RISC-V
*)

needs "compiler/backend/backend.ml";;
needs "compiler/backend/presLang.ml";;
needs "lib/sptree.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "riscv_config"
  ["asmProps"; "asmSem"; "backend"];;
(* HOL4 ancestors outside the port: riscv_target *)

let riscv_names_def = new_definition
  `riscv_names =
   ((
    // arguments: 10-17
    // including return values: 10-11
    // temporaries: 5-7, 28-31
    // return address: 1
    // saved regs: 8-9, 18-27
    // 3 = global pointer, 4 = thread pointer
    // 0 avoided (hardwired zero)
    // 2 avoided (stack pointer)
    // 3 avoided (global pointer)
    // 4 avoided (thread pointer)
    // 31 avoided (used by encoder)
    // 5 avoid regs means 27 regs available for CakeML
    // constraints:
    // the last 3 of these (24, 25, 26) must be mapped to callee saved regs
    // 0 must be mapped to link reg (1)
    // 1-4 must be mapped to 1st-4st args (10-13)
    balanced_map_insert 0 1 o
    balanced_map_insert 1 10 o
    balanced_map_insert 2 11 o
    balanced_map_insert 3 12 o
    balanced_map_insert 4 13 o
    // the rest to make the mapping well-formed
    balanced_map_insert 10 27 o
    balanced_map_insert 11 28 o
    balanced_map_insert 12 29 o
    balanced_map_insert 13 30 o
    balanced_map_insert 27 0 o
    balanced_map_insert 28 2 o
    balanced_map_insert 29 3 o
    balanced_map_insert 30 4) LN:num spt)`;;

(* HOL4 riscv_configScript.sml:45-46: a theorem that HOL4 states as
   the value of an ML expression: riscv_names_def *)

(* HOL4 riscv_configScript.sml:48-54: the ML values that the
   definitions below antiquote *)

let riscv_backend_config_def = new_definition
  `riscv_backend_config =
              mk_backend_config prim_src_config
                (clos_to_bvl_default_config)
                (bvl_to_bvi_default_config) (mk_data_to_word_config 4
                4 2 32 T F F F F F data_to_word_Simple)
                (mk_word_to_word_config 3 [])
                (mk_word_to_stack_config 0 LN)
                (mk_stack_to_lab_config riscv_names F F)
                (mk_lab_to_target_config LN [] 0 5 NONE [] 104729) []
                default_tap_config []`;;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
