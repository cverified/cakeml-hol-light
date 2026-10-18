(* ======================================================== *)
(*  arm8_config: ported from HOL4's
    compiler/backend/arm8/arm8_configScript.sml  *)
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

(* HOL4 ML code, not ported:
val clos_conf = rconc (EVAL ``clos_to_bvl$default_config``)
val bvl_conf = rconc (EVAL``bvl_to_bvi$default_config``)
val word_to_word_conf = ``<| reg_alg:=2; col_oracle := [] |>``
*)
(* TODO: this config may need to change *)
(* HOL4 ML code, not ported:
val arm8_data_conf = ``<| tag_bits:=4; len_bits:=4; pad_bits:=2;
  len_size:=32; has_div:=T; has_longdiv:=F; has_fp_ops:=F;
  has_fp_tern:=F; be:=F; call_empty_ffi:=F; gc_kind:=Simple|>``
val arm8_word_conf = ``<| bitmaps_length := 0; stack_frame_size := LN
  |>``
val arm8_stack_conf =
  ``<|jump:=F;reg_names:=arm8_names;perf_calls:=F|>``
val arm8_lab_conf =
  ``<|pos:=0;ffi_names:=NONE;labels:=LN;sec_pos_len:=
  [];init_clock:=5;hash_size:=104729n;shmem_extra:=[]|>``
*)

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
