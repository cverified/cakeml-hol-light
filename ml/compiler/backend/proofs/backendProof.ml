(* ======================================================== *)
(*  backendProof: ported from HOL4's
    compiler/backend/proofs/backendProofScript.sml  *)
(* ======================================================== *)

(*
  Composes the correctness theorems for all of the compiler phases.
*)

needs "compiler/backend/backend.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/backend_passes.ml";;
needs "compiler/backend/bvi_to_data.ml";;
needs "compiler/backend/bvl_to_bvi.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/flat_to_clos.ml";;
needs "compiler/backend/proofs/bvi_inlineProof.ml";;
needs "compiler/backend/proofs/bvi_to_dataProof.ml";;
needs "compiler/backend/proofs/bvl_to_bviProof.ml";;
needs "compiler/backend/proofs/clos_to_bvlProof.ml";;
needs "compiler/backend/proofs/data_to_wordProof.ml";;
needs "compiler/backend/proofs/flat_to_closProof.ml";;
needs "compiler/backend/proofs/lab_to_targetProof.ml";;
needs "compiler/backend/proofs/source_evalProof.ml";;
needs "compiler/backend/proofs/source_to_flatProof.ml";;
needs "compiler/backend/proofs/source_to_sourceProof.ml";;
needs "compiler/backend/proofs/stack_removeProof.ml";;
needs "compiler/backend/proofs/stack_to_labProof.ml";;
needs "compiler/backend/proofs/word_to_stackProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/stackProps.ml";;
needs "compiler/backend/stack_alloc.ml";;
needs "compiler/backend/stack_remove.ml";;
needs "compiler/backend/stack_to_lab.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_to_stack.ml";;
needs "compiler/backend/word_to_word.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/multiword.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/proofs/primSemEnv.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* TODO: move/rephrase *)

(* -- *)

(* HOL4 backendProofScript.sml:51: ML code, not ported *)

let backend_config_ok_def = cake_define
  `backend_config_ok (asm_conf:'a asm_config) (c:backend_config) <=>
  backend_config_source_conf
     c = prim_src_config /\
     0 < clos_to_bvl_config_max_app (backend_config_clos_conf c) /\
       bvl_to_bvi_config_next_name2 (backend_config_bvl_conf
     c) = bvl_num_stubs + 2 /\
     LENGTH (asm_config_avoid_regs asm_conf) + 13 <=
       asm_config_reg_count asm_conf /\ lab_to_target_config_pos
       (backend_config_lab_conf
     c) = 0 /\ lab_to_target_config_labels (backend_config_lab_conf
     c) = LN /\
     conf_ok (:'a) (backend_config_data_conf c) /\
     (data_to_word_config_has_longdiv (backend_config_data_conf c)
       ==> asm_config_ISA asm_conf = x86_64) /\
     (data_to_word_config_has_div (backend_config_data_conf c) ==>
       asm_config_ISA
       asm_conf = ARMv8 \/ asm_config_ISA asm_conf = MIPS \/
         asm_config_ISA
       asm_conf = RISC_V) /\
     (data_to_word_config_has_fp_tern (backend_config_data_conf c)
       <=> asm_config_ISA
         asm_conf = ARMv7 /\ 2 < asm_config_fp_reg_count asm_conf) /\
     (data_to_word_config_has_fp_ops (backend_config_data_conf c) <=>
       1 < asm_config_fp_reg_count asm_conf) /\
     max_stack_alloc <= 2 * max_heap_limit (:'a)
       (backend_config_data_conf c) - 1 /\
       stack_to_lab_config_perf_calls (backend_config_stack_conf
     c) = F /\
     (\c. asm_offset_ok 0 (asm_config_addr_offset c)) asm_conf (n2w
       0) /\
     (\c. asm_offset_ok 0 (asm_config_hw_offset c)) asm_conf (n2w 0)
       /\
     (!w. --(n2w 8) <= w /\ w <= (n2w 8) ==> (\c. asm_offset_ok 0
       (asm_config_byte_offset c)) asm_conf w) /\ asm_config_valid_imm
     asm_conf (INL Add) (n2w 8) /\ asm_config_valid_imm
     asm_conf (INL Add) (n2w 4) /\ asm_config_valid_imm
     asm_conf (INL Add) (n2w 1) /\ asm_config_valid_imm
     asm_conf (INL Sub) (n2w 1) /\
     OPTION_ALL (EVERY (\x. ?s. x = ffi_ExtCall s)) (ffi_names
       (backend_config_lab_conf c)) /\
     tlookup (stack_to_lab_config_reg_names
       (backend_config_stack_conf c)) PERMUTES UNIV /\
     stack_names_names_ok (stack_to_lab_config_reg_names
       (backend_config_stack_conf c)) (asm_config_reg_count asm_conf)
       (asm_config_avoid_regs asm_conf) /\
     fixed_names (stack_to_lab_config_reg_names
       (backend_config_stack_conf c)) asm_conf /\
     (!s. (\c. asm_offset_ok 0 (asm_config_addr_offset c)) asm_conf
       (store_offset s)) /\
     (!s. (\c. asm_offset_ok 0 (asm_config_hw_offset c)) asm_conf
       (store_offset s)) /\
     (!n.
          n <= max_stack_alloc ==> asm_config_valid_imm
          asm_conf (INL Sub) (n2w (n * (dimindex (:'a) DIV 8))) /\
            asm_config_valid_imm
          asm_conf (INL Add) (n2w (n * (dimindex (:'a) DIV 8))))`;;

let mc_init_ok_def = cake_define
  `mc_init_ok asm_conf c mc <=>
   EVERY (\r. MEM (tlookup (stack_to_lab_config_reg_names
     (backend_config_stack_conf c)) ((r + asm_config_reg_count
     (target_config (machine_config_target mc))) - (LENGTH
     (asm_config_avoid_regs (target_config (machine_config_target mc)))
     + 5))) (machine_config_callee_saved_regs mc)) [2; 3; 4] /\
   tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf
     c)) 4 = len2_reg mc /\
   tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf
     c)) 3 = ptr2_reg mc /\
   tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf
     c)) 2 = len_reg mc /\
   tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf
     c)) 1 = ptr_reg mc /\
   tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf
     c)) 0 =
     (match link_reg (target_config (machine_config_target mc)) with
       NONE -> 0 | SOME n -> n) /\ be (backend_config_data_conf
   c) = asm_config_big_endian (target_config (machine_config_target
     mc)) /\ ~(
   (match link_reg (target_config (machine_config_target mc)) with
     NONE -> 0 | SOME n -> n) = len_reg mc) /\ ~(
   (match link_reg (target_config (machine_config_target mc)) with
     NONE -> 0 | SOME n -> n) = ptr_reg mc) /\ ~(
   (match link_reg (target_config (machine_config_target mc)) with
     NONE -> 0 | SOME n -> n) = len2_reg mc) /\ ~(
   (match link_reg (target_config (machine_config_target mc)) with
     NONE -> 0 | SOME n -> n) = ptr2_reg mc) /\
   ~MEM (match link_reg (target_config (machine_config_target mc))
     with NONE -> 0 | SOME n -> n) (machine_config_callee_saved_regs mc)
     /\
    asm_conf = target_config (machine_config_target mc)`;;

let heap_regs_def = cake_define
  `heap_regs reg_names =
     (tlookup reg_names 2,tlookup reg_names 4)`;;

(* HOL4 backendProofScript.sml:175: the overload
   bvl_inline_compile_prog, which the port expands *)
(* HOL4 backendProofScript.sml:176: the overload
   bvi_tailrec_compile_prog, which the port expands *)
(* HOL4 backendProofScript.sml:177: the overload
   bvi_tmc_compile_prog, which the port expands *)
(* HOL4 backendProofScript.sml:178: the overload
   bvi_inline_compile_inc, which the port expands *)
(* HOL4 backendProofScript.sml:179: the overload
   bvi_to_data_compile_prog, which the port expands *)
(* HOL4 backendProofScript.sml:180: the overload
   bvl_to_bvi_compile_prog, which the port expands *)
(* HOL4 backendProofScript.sml:181: the overload
   bvl_to_bvi_compile_inc, which the port expands *)
(* HOL4 backendProofScript.sml:182: the overload bvl_to_bvi_compile,
   which the port expands *)
(* HOL4 backendProofScript.sml:183: the overload bvi_to_data_compile,
   which the port expands *)
(* HOL4 backendProofScript.sml:184: the overload bvi_let_compile,
   which the port expands *)
(* HOL4 backendProofScript.sml:185: the overload bvl_const_compile,
   which the port expands *)
(* HOL4 backendProofScript.sml:186: the overload bvl_handle_compile,
   which the port expands *)
(* HOL4 backendProofScript.sml:187: the overload
   bvl_inline_compile_inc, which the port expands *)
(* HOL4 backendProofScript.sml:188: the overload
   bvl_to_bvi_compile_exps, which the port expands *)
(* HOL4 backendProofScript.sml:189: the overload
   flat_to_clos_inc_compile, which the port expands *)
(* HOL4 backendProofScript.sml:190: the overload
   stack_remove_prog_comp, which the port expands *)
(* HOL4 backendProofScript.sml:191: the overload
   stack_alloc_prog_comp, which the port expands *)
(* HOL4 backendProofScript.sml:192: the overload
   stack_names_prog_comp, which the port expands *)

(* TODO: remove when theorems are moved *)
(* HOL4 backendProofScript.sml:195: the overload obeys_max_app, which
   the port expands *)
(* HOL4 backendProofScript.sml:196: the overload no_Labels, which the
   port expands *)
(* HOL4 backendProofScript.sml:197: the overload every_Fn_SOME, which
   the port expands *)
(* HOL4 backendProofScript.sml:198: the overload code_locs, which the
   port expands *)
(* HOL4 backendProofScript.sml:199: the overload no_mti, which the
   port expands *)

(* TODO: move these *)

(* HOL4 backendProofScript.sml:308-315: ML code, not ported *)

let cake_configs_def = cake_define
  `cake_configs asm_conf c source =
   state_orac_states (compile_inc_progs T asm_conf) c source`;;

let cake_orac_def = cake_define
  `cake_orac asm_conf c source f g i =
     (let c = cake_configs asm_conf c source i in
     let (_1,progs) = compile_inc_progs T asm_conf c (source i) in
     (f c,g progs))`;;

let config_tuple2_def = cake_define
  `config_tuple2 c = (bvl_to_bvi_config_inlines (backend_config_bvl_conf
  c),bvl_to_bvi_config_next_name1 (backend_config_bvl_conf
  c),bvl_to_bvi_config_next_name2 (backend_config_bvl_conf
     c),bvl_to_bvi_config_next_name3 (backend_config_bvl_conf
       c),bvl_to_bvi_config_bvi_inlines (backend_config_bvl_conf
       c),word_to_stack_config_bitmaps_length (backend_config_word_conf
     c),backend_config_lab_conf c)`;;

let config_tuple1_def = cake_define
  `config_tuple1 c = (backend_config_source_conf
  c,clos_to_bvl_config_next_loc (backend_config_clos_conf c),
     option_val_approx_spt (clos_to_bvl_config_known_conf
       (backend_config_clos_conf c)),
     FST (clos_to_bvl_config_call_state (backend_config_clos_conf
       c)),config_tuple2 c)`;;

(* HOL4 backendProofScript.sml:404-409: the ML values that the
   definitions below antiquote *)

(* HOL4 backendProofScript.sml:411-412: ML code, not ported *)

(* HOL4 backendProofScript.sml:414-417: the ML values that the
   definitions below antiquote *)

(* HOL4 backendProofScript.sml:583-586: ML code, not ported *)

(* HOL4 backendProofScript.sml:588-589: ML code, not ported *)

(* HOL4 backendProofScript.sml:694-701: ML code, not ported *)

(* HOL4 backendProofScript.sml:703-712: code that the source has in a
   comment *)

(* HOL4 backendProofScript.sml:753: ML code, not ported *)

(* HOL4 backendProofScript.sml:755-758: ML code, not ported *)

let state_co_fun_def = cake_define
  `state_co_fun f_inc x =
     (let ((cfg1,cfg2),p) = x in
     let (_2,p') = f_inc cfg1 p in
     (cfg2,p'))`;;

(* bvi_inline is name preserving, so the namespace-sliced projection
   used
   by monotonic_labels_bvl_to_bvi cannot see it either. *)

(*
max_print_depth := 20
*)

let compute_stack_frame_sizes_def = cake_define
  `compute_stack_frame_sizes c word_prog =
     (let reg_count = asm_config_reg_count c - LENGTH
       (asm_config_avoid_regs c) - 5 in
       mapi (\n (arg_count,prog).
               let stack_arg_count' = arg_count - reg_count in let
                   stack_var_count = MAX ((max_var prog DIV 2 + 1) -
                     reg_count) stack_arg_count' in if stack_var_count =
                     0 then 0 else stack_var_count + 1)
         (fromAList (word_prog)))`;;

let is_64_bits_def = cake_define
  `is_64_bits (:'a) <=> (dimindex (:'a) = 64)`;;

let is_safe_for_space_def = cake_define
  `backendProof_is_safe_for_space ffi asm_conf c prog stack_heap_limit =
     (let data_prog = FST (SND (to_data c prog)) in
     let word_prog = FST (SND (to_word (asm_conf:'a asm_config) c
       prog)) in
       data_lang_safe_for_space ffi (fromAList data_prog)
         (compute_limits (data_to_word_config_len_size
           (backend_config_data_conf c)) (is_64_bits (:'a))
           (data_to_word_config_has_fp_ops (backend_config_data_conf c))
           (data_to_word_config_has_fp_tern (backend_config_data_conf
           c)) stack_heap_limit)
         (compute_stack_frame_sizes asm_conf word_prog)
           InitGlobals_location /\ ~(data_to_word_config_gc_kind
           (backend_config_data_conf
       c) = None))`;;
hol4_overload "is_safe_for_space" "backendProof_is_safe_for_space";;

(* TODO: MOVE *)

let read_limits_def = cake_define
  `backendProof_read_limits (asm_conf:'a asm_config) (c:backend_config)
  mc ms =
     get_stack_heap_limit
       (2 * max_heap_limit (:'a) (backend_config_data_conf c) - 1)
       ((target_get_reg (machine_config_target mc) ms (tlookup
         (stack_to_lab_config_reg_names (backend_config_stack_conf c))
         2):'a word),(target_get_reg (machine_config_target
        mc) ms (tlookup (stack_to_lab_config_reg_names
          (backend_config_stack_conf c)) 3):'a word),(target_get_reg
          (machine_config_target
        mc) ms (tlookup (stack_to_lab_config_reg_names
          (backend_config_stack_conf c)) 4):'a word))`;;
hol4_overload "read_limits" "backendProof_read_limits";;

let add_eval_state_def = cake_define_list
  [`add_eval_state NONE s0 = s0`;
   `add_eval_state (SOME ci) s0 =
  semanticPrimitives_state_eval_state_fupd (K (SOME (mk_init_eval_state
  ci)))
      s0`];;


let opt_eval_config_wf_def = cake_define_list
  [`opt_eval_config_wf asm_conf c' (SOME ci) =
  (compiler_instance_compiler_fun
      ci = compile_inc_progs_for_eval asm_conf /\
      INJ (compiler_instance_config_v ci) UNIV UNIV /\
        compiler_instance_init_state ci = c')`;
   `opt_eval_config_wf asm_conf c' NONE = T`];;

let backend_from_data_tuple_cc_def = cake_define
  `backend_from_data_tuple_cc asm_conf (c:backend_config) cfg =
     OPTION_MAP (I ## MAP upper_w2w ## I) o
       (\progs.
         (\(bm0,cfg) progs.
           (\(progs,fs,bm).
             OPTION_MAP
               (\(bytes,cfg).
                 (bytes,append (FST bm),(SND bm,cfg)))
               (compile asm_conf cfg
                 (MAP prog_to_section
                   (MAP
                     (prog_comp (stack_to_lab_config_reg_names
                       (backend_config_stack_conf c)))
                     (MAP
                       (prog_comp (stack_to_lab_config_jump
                         (backend_config_stack_conf c))
                         (asm_config_addr_offset
                         asm_conf)
                         (asm_config_reg_count asm_conf - (LENGTH
                           (asm_config_avoid_regs asm_conf) + 3)))
                       (MAP prog_comp progs))))))
            (compile_word_to_stack asm_conf F
             ((asm_config_reg_count asm_conf - (LENGTH
               (asm_config_avoid_regs asm_conf) + 3)) - 2) progs
               (misc_Nil,bm0)))
               cfg (MAP (\p. full_compile_single
                 (asm_config_two_reg_arith asm_conf)
                 (asm_config_reg_count asm_conf - (LENGTH
                 (asm_config_avoid_regs asm_conf) + 5))
                 (word_to_word_config_reg_alg
                 (backend_config_word_to_word_conf
               c))
               asm_conf (p,NONE)) progs)) o
               MAP (compile_part (ensure_fp_conf_ok asm_conf
                 (backend_config_data_conf c)))`;;

let backend_from_flat_tuple_cc_def = cake_define
  `backend_from_flat_tuple_cc asm_conf (c:backend_config) =
     pure_cc inc_compile_decs
       (compile_common_inc (backend_config_clos_conf c)
          (pure_cc (clos_to_bvl_compile_inc'
            (clos_to_bvl_config_max_app (backend_config_clos_conf c)))
            (full_cc (backend_config_bvl_conf c) (pure_cc
              bvi_to_data_compile_prog
              (backend_from_data_tuple_cc asm_conf c)))))`;;

(* HOL4 backendProofScript.sml:3046: the overload
   mk_flat_install_conf, which the port expands *)

(* HOL4 backendProofScript.sml:3048: ML code, not ported *)

let the_EvalDecs_def = cake_define
  `the_EvalDecs (EvalDecs x) = x`;;
