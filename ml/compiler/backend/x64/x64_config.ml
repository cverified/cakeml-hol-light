(* ======================================================== *)
(*  x64_config: ported from HOL4's
    compiler/backend/x64/x64_configScript.sml  *)
(* ======================================================== *)

(*
  Define the compiler configuration for x64
*)

needs "compiler/backend/backend.ml";;
needs "compiler/backend/presLang.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
(* HOL4 ancestors outside the port: x64_target *)

let x64_names_def = cake_define
  `x64_names =
     ((insert 1 7 o
      insert 2 6 o
      insert 3 2 o
      insert 4 1 o
      insert 5 8 o
      insert 6 9 o
      insert 11 14 o
      insert 12 13 o
      insert 13 12 o
      insert 7 3 o
      insert 8 15 o
      insert 9 11 o
      insert 14 4 o
      insert 15 5) LN:num spt)`;;

(* HOL4 ML code, not ported:
val clos_conf = rconc (EVAL ``clos_to_bvl$default_config``)
val bvl_conf = rconc (EVAL``bvl_to_bvi$default_config``)
val word_to_word_conf = ``<| reg_alg:=2; col_oracle := [] |>``
*)

(* HOL4 ML code, not ported:
val x64_data_conf = ``<| tag_bits:=4; len_bits:=4; pad_bits:=2;
  len_size:=32; has_div:=F; has_longdiv:=T; has_fp_ops:=T;
  has_fp_tern:=F; be:=F; call_empty_ffi:=F; gc_kind:=Simple|>``
val x64_word_conf = ``<| bitmaps_length := 0; stack_frame_size := LN
  |>``
*)
(* perf_calls=T yields an unverified binary suitable for
   `perf record --call-graph fp` profiling (x64 only). *)
(* HOL4 ML code, not ported:
val x64_stack_conf = ``<|jump:=T;reg_names:=x64_names;perf_calls:=F|>``
val x64_lab_conf =
  ``<|pos:=0;ffi_names:=NONE;labels:=LN;sec_pos_len:=
  [];init_clock:=5;hash_size:=104729n;shmem_extra:=[]|>``
*)

let x64_backend_config_def = cake_define
  `x64_backend_config =
              mk_backend_config prim_src_config
                (clos_to_bvl_default_config)
                (bvl_to_bvi_default_config) (mk_data_to_word_config 4
                4 2 32 F T T F F F Simple) (mk_word_to_word_config 2
                []) (mk_word_to_stack_config 0 LN)
                (mk_stack_to_lab_config x64_names T F)
                (mk_lab_to_target_config LN [] 0 5 NONE [] 104729) []
                default_tap_config []`;;
