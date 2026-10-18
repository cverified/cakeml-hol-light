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
needs "semantics/ast.ml";;
(* HOL4 ancestors outside the port: riscv_target *)

let riscv_names_def = cake_define
  `riscv_names =
   ((insert 0 1 o
    insert 1 10 o
    insert 2 11 o
    insert 3 12 o
    insert 4 13 o
    insert 10 27 o
    insert 11 28 o
    insert 12 29 o
    insert 13 30 o
    insert 27 0 o
    insert 28 2 o
    insert 29 3 o
    insert 30 4) LN:num spt)`;;

(* HOL4 riscv_configScript.sml:45-46: a theorem that HOL4 states as
   the value of an ML expression: riscv_names_def *)

(* HOL4 riscv_configScript.sml:48-54: the ML values that the
   definitions below antiquote *)

let riscv_backend_config_def = cake_define
  `riscv_backend_config =
              mk_backend_config prim_src_config
                (clos_to_bvl_default_config)
                (bvl_to_bvi_default_config) (mk_data_to_word_config 4
                4 2 32 T F F F F F Simple) (mk_word_to_word_config 3
                []) (mk_word_to_stack_config 0 LN)
                (mk_stack_to_lab_config riscv_names F F)
                (mk_lab_to_target_config LN [] 0 5 NONE [] 104729) []
                default_tap_config []`;;
