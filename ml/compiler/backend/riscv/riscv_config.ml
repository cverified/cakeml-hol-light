(* ======================================================== *)
(*  riscv_config: ported from HOL4's
    compiler/backend/riscv/riscv_configScript.sml  *)
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

(* HOL4 ML code, not ported:
val clos_conf = rconc (EVAL ``clos_to_bvl$default_config``)
val bvl_conf = rconc (EVAL``bvl_to_bvi$default_config``)
val word_to_word_conf = ``<| reg_alg:=3; col_oracle := [] |>``
val riscv_data_conf = ``<| tag_bits:=4; len_bits:=4; pad_bits:=2;
  len_size:=32; has_div:=T; has_longdiv:=F; has_fp_ops:=F;
  has_fp_tern:=F; be:=F; call_empty_ffi:=F; gc_kind:=Simple|>``
val riscv_word_conf = ``<| bitmaps_length := 0; stack_frame_size := LN
  |>``
val riscv_stack_conf =
  ``<|jump:=F;reg_names:=riscv_names;perf_calls:=F|>``
val riscv_lab_conf =
  ``<|pos:=0;ffi_names:=NONE;labels:=LN;sec_pos_len:=
  [];init_clock:=5;hash_size:=104729n;shmem_extra:=[]|>``
*)

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
