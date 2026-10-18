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

(* HOL4 ML code, not ported:
val clos_conf = rconc (EVAL ``clos_to_bvl$default_config``)
val bvl_conf = rconc (EVAL``bvl_to_bvi$default_config``)
val word_to_word_conf = ``<| reg_alg:=2; col_oracle := [] |>``
val mips_data_conf = ``<| tag_bits:=4; len_bits:=4; pad_bits:=2;
  len_size:=32; has_div:=T; has_longdiv:=F; has_fp_ops:=F; has_fp_tern
  := F; be:=T; call_empty_ffi:=F; gc_kind:=Simple|>``
val mips_word_conf = ``<| bitmaps_length := 0; stack_frame_size := LN
  |>``
val mips_stack_conf =
  ``<|jump:=F;reg_names:=mips_names;perf_calls:=F|>``
val mips_lab_conf =
  ``<|pos:=0;ffi_names:=NONE;labels:=LN;sec_pos_len:=
  [];init_clock:=5;hash_size:=104729n;shmem_extra:=[]|>``
*)

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
