(* ======================================================== *)
(*  backendProof: ported from HOL4's
    compiler/backend/proofs/backendProofScript.sml
    A proof theory about backend.ml, with 17 definitions and 152
    theorems.  Needed by compilerProof.ml.  *)
(* ======================================================== *)

(*
  Composes the correctness theorems for all of the compiler phases.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/backend_passes.ml";;
needs "compiler/backend/bvl_to_bvi.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_call.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/clos_mti.ml";;
needs "compiler/backend/clos_number.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/flat_pattern.ml";;
needs "compiler/backend/flat_to_clos.ml";;
needs "compiler/backend/labLang.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/backend/proofs/bvi_inlineProof.ml";;
needs "compiler/backend/proofs/bvi_to_dataProof.ml";;
needs "compiler/backend/proofs/bvl_to_bviProof.ml";;
needs "compiler/backend/proofs/clos_knownProof.ml";;
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
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/flatProps.ml";;
needs "compiler/backend/semantics/labProps.ml";;
needs "compiler/backend/semantics/stackProps.ml";;
needs "compiler/backend/semantics/targetSem.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/source_to_flat.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_remove.ml";;
needs "compiler/backend/stack_to_lab.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_to_stack.ml";;
needs "compiler/backend/word_to_word.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/alignment.ml";;
needs "lib/byte.ml";;
needs "lib/set_sep.ml";;
needs "lib/sorting.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/namespace.ml";;
needs "semantics/primTypes.ml";;
needs "semantics/proofs/primSemEnv.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/semantics.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "backendProof"
  ["backend"; "backendProps"; "backend_common"; "backend_passes";
   "bvi_inlineProof"; "bvi_to_dataProof"; "bvl_jumpProof";
   "bvl_to_bviProof"; "clos_annotateProof"; "clos_callProof";
   "clos_constantProof"; "clos_fvsProof"; "clos_knownProof";
   "clos_knownProps"; "clos_letopProof"; "clos_mtiProof";
   "clos_numberProof"; "clos_opProof"; "clos_ticksProof";
   "clos_to_bvlProof"; "dataProps"; "data_to_wordProof";
   "flat_to_closProof"; "lab_to_targetProof"; "primSemEnv";
   "semanticsProps"; "source_to_flatProof"; "source_to_sourceProof";
   "stack_to_labProof"; "word_to_stack"; "word_to_stackProof"];;

let _ = do_list hide_constant ["done"];;

(* TODO: move/rephrase *)

let byte_aligned_mult = prove
 (`good_dimindex (:'a) ==>
    byte_aligned (a + bytes_in_word * n2w i) = byte_aligned (a:'a
      word)`,
  CHEAT_TAC);;

let byte_aligned_MOD = prove
 (`good_dimindex (:'a) ==>
   (!(x:'a word). x IN byte_aligned ==>
   w2n x MOD (dimindex (:'a) DIV 8) = 0)`,
  CHEAT_TAC);;

(* -- *)

(* HOL4 backendProofScript.sml:51: ML code, not ported *)

let backend_config_ok_def = new_definition
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
     asm_conf (INL asm_Add) (n2w 8) /\ asm_config_valid_imm
     asm_conf (INL asm_Add) (n2w 4) /\ asm_config_valid_imm
     asm_conf (INL asm_Add) (n2w 1) /\ asm_config_valid_imm
     asm_conf (INL asm_Sub) (n2w 1) /\
     OPTION_ALL (ALL (\x. ?s. x = ffi_ExtCall s)) (ffi_names
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
          asm_conf (INL asm_Sub) (n2w (n * (dimindex (:'a) DIV 8)))
            /\ asm_config_valid_imm
          asm_conf (INL asm_Add) (n2w (n * (dimindex (:'a) DIV
            8))))`;;

let backend_config_ok_with_bvl_conf_updated = prove
 (`bvl_to_bvi_config_next_name2
      (f (backend_config_bvl_conf cc)) = bvl_to_bvi_config_next_name2
        (backend_config_bvl_conf cc) ==>
      (backend_config_ok asm_conf (backend_config_bvl_conf_fupd f
        cc) <=> backend_config_ok asm_conf cc)`,
  CHEAT_TAC);;
add_simp backend_config_ok_with_bvl_conf_updated;;

let backend_config_ok_with_word_to_word_conf_updated = prove
 (`backend_config_ok asm_conf (backend_config_word_to_word_conf_fupd f
  cc) <=> backend_config_ok asm_conf cc`,
  CHEAT_TAC);;
add_simp backend_config_ok_with_word_to_word_conf_updated;;

let backend_config_ok_call_empty_ffi = prove
 (`backend_config_ok asm_conf (backend_config_data_conf_fupd (\c.
  data_to_word_config_call_empty_ffi_fupd x c) cc) =
    backend_config_ok asm_conf cc`,
  CHEAT_TAC);;
add_simp backend_config_ok_call_empty_ffi;;

let mc_init_ok_def = new_definition
  `mc_init_ok asm_conf c mc <=>
   ALL (\r. MEM (tlookup (stack_to_lab_config_reg_names
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
     mc)) /\ ~((
    // the next four are implied by injectivity of find_name
    match link_reg (target_config (machine_config_target mc)) with
      NONE -> 0 | SOME n -> n) = len_reg mc) /\ ~((match link_reg
      (target_config (machine_config_target mc)) with NONE -> 0 | SOME n
      -> n) = ptr_reg mc) /\ ~((match link_reg (target_config
      (machine_config_target mc)) with NONE -> 0 | SOME n -> n) =
      len2_reg mc) /\ ~((match link_reg (target_config
      (machine_config_target mc)) with NONE -> 0 | SOME n -> n) =
      ptr2_reg mc) /\
   ~(MEM (match link_reg (target_config (machine_config_target mc))
     with NONE -> 0 | SOME n -> n) (machine_config_callee_saved_regs
     mc)) /\
    asm_conf = target_config (machine_config_target mc)`;;

let mc_init_ok_with_bvl_conf_updated = prove
 (`mc_init_ok asm_conf (backend_config_bvl_conf_fupd f cc) mc <=>
   mc_init_ok asm_conf cc mc`,
  CHEAT_TAC);;
add_simp mc_init_ok_with_bvl_conf_updated;;

let mc_init_ok_with_word_to_word_conf_updated = prove
 (`mc_init_ok asm_conf (backend_config_word_to_word_conf_fupd f cc) mc
  <=>
   mc_init_ok asm_conf cc mc`,
  CHEAT_TAC);;
add_simp mc_init_ok_with_word_to_word_conf_updated;;

let mc_init_ok_with_clos_conf_updated = prove
 (`mc_init_ok asm_conf (backend_config_clos_conf_fupd f cc) mc <=>
   mc_init_ok asm_conf cc mc`,
  CHEAT_TAC);;
add_simp mc_init_ok_with_clos_conf_updated;;

let set_oracle_simp = prove
 (`backend_config_ok asm_conf (set_oracle c x) = backend_config_ok
  asm_conf c /\
   mc_init_ok asm_conf (set_oracle c x) = mc_init_ok asm_conf c /\
     backend_config_stack_conf
   (set_oracle c x) = backend_config_stack_conf c`,
  CHEAT_TAC);;
add_simp set_oracle_simp;;

let mc_init_ok_call_empty_ffi = prove
 (`mc_init_ok asm_conf (backend_config_data_conf_fupd (\c.
  data_to_word_config_call_empty_ffi_fupd x c) cc) =
    mc_init_ok asm_conf cc`,
  CHEAT_TAC);;
add_simp mc_init_ok_call_empty_ffi;;

let heap_regs_def = new_definition
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

let no_mti_IMP_obeys_max_app = prove
 (`!m exp. 0 < m /\ no_mti exp ==> obeys_max_app m exp`,
  CHEAT_TAC);;

let EVERY_no_mti_IMP_obeys_max_app = prove
 (`!e3. 0 < m /\ ALL no_mti exps ==> ALL (obeys_max_app m) exps`,
  CHEAT_TAC);;

(* TODO: move these *)
let compile_common_syntax = prove
 (`!cf e3 cf1 e4.
      compile_common cf e3 = (cf1,e4) ==>
      (ALL no_Labels e3 ==>
       ALL no_Labels (MAP (SND o SND) e4)) /\
      (0 < clos_to_bvl_config_max_app cf /\ ALL no_mti e3 ==>
       ALL (obeys_max_app (clos_to_bvl_config_max_app cf)) (MAP (SND
         o SND) e4)) /\
      every_Fn_SOME (MAP (SND o SND) e4)`,
  CHEAT_TAC);;

let word_list_exists_imp = prove
 (`dm = addresses a n /\
    dimindex (:'a) DIV 8 * n < dimword (:'a) /\ good_dimindex (:'a)
      ==>
    word_list_exists a n (fun2set (m1,(dm:'a word->bool)))`,
  CHEAT_TAC);;

(* HOL4 backendProofScript.sml:308-315: ML code, not ported *)

let cake_configs_def = new_definition
  `cake_configs asm_conf c source =
   state_orac_states (compile_inc_progs T asm_conf) c source`;;

let cake_orac_def = new_definition
  `cake_orac asm_conf c source f g i =
     (let c = cake_configs asm_conf c source i in
     let (_1,progs) = compile_inc_progs T asm_conf c (source i) in
     (f c,g progs))`;;

let config_tuple2_def = new_definition
  `config_tuple2 c = (bvl_to_bvi_config_inlines (backend_config_bvl_conf
  c),bvl_to_bvi_config_next_name1 (backend_config_bvl_conf
  c),bvl_to_bvi_config_next_name2 (backend_config_bvl_conf
     c),bvl_to_bvi_config_next_name3 (backend_config_bvl_conf
       c),bvl_to_bvi_config_bvi_inlines (backend_config_bvl_conf
       c),word_to_stack_config_bitmaps_length (backend_config_word_conf
     c),backend_config_lab_conf c)`;;

let config_tuple1_def = new_definition
  `config_tuple1 c = (backend_config_source_conf
  c,clos_to_bvl_config_next_loc (backend_config_clos_conf c),
     option_val_approx_spt (clos_to_bvl_config_known_conf
       (backend_config_clos_conf c)),
     FST (clos_to_bvl_config_call_state (backend_config_clos_conf
       c)),config_tuple2 c)`;;

let cake_configs_eq = prove
 (`!f. backend_compile asm_conf c prog = SOME (b,bm,c') /\
     f c' = f c /\ (!c p. f (FST (compile_inc_progs T asm_conf c p))
       = f c) ==>
   f c' = f c /\ (!i. f (cake_configs asm_conf c' src x) = f c)`,
  CHEAT_TAC);;

let PAIR_MAP_EQ_EQ = prove
 (`(f ## g) x = y <=> (?x0 x1. x = (x0,x1) /\ (f x0,g x1) = y)`,
  CHEAT_TAC);;

(* known_compile_IS_SOME *)
let backendProof_known_compile_IS_SOME = prove
 (`backend_compile kc es = (kc',es') ==> (IS_SOME kc' <=> IS_SOME kc)`,
  CHEAT_TAC);;

let attach_bitmaps_SOME = prove
 (`attach_bitmaps names c bm v = SOME r ==>
   (?bytes c'. v = SOME (bytes,c') /\
   r = (bytes,bm,backend_config_symbols_fupd (K (MAP (\(n,p,l).
     (lookup_any n names (implode "NOTFOUND"),p,l))
     (lab_to_target_config_sec_pos_len c')))
     (backend_config_lab_conf_fupd (K c') c)))`,
  CHEAT_TAC);;

let known_compile_static_conf = prove
 (`backend_compile kc es = (kc',es') ==> known_static_conf kc' =
  known_static_conf kc`,
  CHEAT_TAC);;

let known_option_upd_val_spt_eq = prove
 (`IS_SOME (option_upd_val_spt spt kc) = IS_SOME kc /\
   known_static_conf (option_upd_val_spt spt kc) =
     known_static_conf kc`,
  CHEAT_TAC);;

let source_compile_pattern_cfg = prove
 (`(backend_compile c p = (c',p') ==> source_to_flat_config_pattern_cfg
  c' = source_to_flat_config_pattern_cfg c) /\
   (inc_compile env_id c p = (c',p') ==>
     source_to_flat_config_pattern_cfg c' =
     source_to_flat_config_pattern_cfg c)`,
  CHEAT_TAC);;

(* HOL4 backendProofScript.sml:404-409: the ML values that the
   definitions below antiquote *)

(* HOL4 backendProofScript.sml:411-412: ML code, not ported *)

(* HOL4 backendProofScript.sml:414-417: the ML values that the
   definitions below antiquote *)

(* HOL4 backendProofScript.sml:419-442: a theorem whose statement the
   port cannot state yet: cake_orac_config_eqs *)

let decide_inline_reset_spt = prove
 (`decide_inline (clos_known_config_val_approx_spt_fupd f kc) =
  decide_inline kc`,
  CHEAT_TAC);;

let known_reset_spt = prove
 (`!kc. known (clos_known_config_val_approx_spt_fupd f kc) = known
  (kc)`,
  CHEAT_TAC);;

let known_reset_to_static_conf = prove
 (`known (reset_inline_factor kc) = known (THE (known_static_conf
  (SOME kc)))`,
  CHEAT_TAC);;

let known_co_eq_state_co_inc = prove
 (`known_co kc co =
   state_co (known_compile_inc (known_static_conf kc)) co`,
  CHEAT_TAC);;

(* [local] *)
let keep_progs_T = prove
 (`keep_progs T = I`,
  CHEAT_TAC);;

(* HOL4 backendProofScript.sml:493-494: a theorem that HOL4 states as
   the value of an ML expression: compile_inc_progs_defs *)

let cake_orac_eqs = prove
 (`state_co (\c (env_id,decs). inc_compile env_id c
     (source_to_source_compile decs)) (cake_orac asm_conf c' src
       config_tuple1 (\ps. (backend_progs_env_id
       ps,backend_progs_source_prog ps))) =
   cake_orac asm_conf c' src (SND o config_tuple1) (\ps.
     backend_progs_flat_prog ps) /\
   pure_co (inc_compile_decs) o cake_orac asm_conf c' src f1 (\ps.
     backend_progs_flat_prog ps) =
   cake_orac asm_conf c' src f1 (\ps. backend_progs_clos_prog ps) /\
   (
   backend_compile asm_conf c prog = SOME (b,bm,c') /\ clos_c =
     backend_config_clos_conf c ==>
   pure_co (clos_to_bvl_compile_inc (clos_to_bvl_config_max_app
     clos_c)) o
   pure_co clos_annotate_compile_inc o
   state_co (cond_call_compile_inc (clos_to_bvl_config_do_call
     clos_c))
     (known_co (clos_to_bvl_config_known_conf clos_c)
       (state_co (ignore_table clos_number_compile_inc)
         (pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti
           clos_c) (clos_to_bvl_config_max_app
                     clos_c)) o
           cake_orac asm_conf c' src (SND o config_tuple1) (\ps.
             backend_progs_clos_prog ps)))) =
   cake_orac asm_conf c' src config_tuple2 (\ps.
     backend_progs_bvl_prog ps)) /\
   (
   backend_compile asm_conf c prog = SOME (b,bm,c') /\ bvl_c =
     backend_config_bvl_conf c ==>
   full_co bvl_c
     (cake_orac asm_conf c' src config_tuple2 (\ps.
       backend_progs_bvl_prog ps)) =
   cake_orac asm_conf c' src (SND o SND o SND o SND o SND o
     config_tuple2) (\ps. backend_progs_bvi_prog ps)) /\
   pure_co bvi_to_data_compile_prog o
     cake_orac asm_conf c' src f3 (\ps. backend_progs_bvi_prog ps) =
   cake_orac asm_conf c' src f3 (\ps. backend_progs_data_prog ps) /\
   (
   backend_compile asm_conf c prog = SOME (b,bm,c') /\
     dc = ensure_fp_conf_ok asm_conf (backend_config_data_conf c) /\
     tr_c = asm_config_two_reg_arith asm_conf /\
     reg_c = asm_config_reg_count asm_conf -
         (LENGTH (asm_config_avoid_regs asm_conf) + 5) /\
     reg_alg = word_to_word_config_reg_alg
       (backend_config_word_to_word_conf c) ==>
   pure_co (MAP (\p. full_compile_single tr_c reg_c reg_alg asm_conf
     (p,NONE))) o
     pure_co (MAP (data_to_word_compile_part dc)) o cake_orac
       asm_conf c' src f4 (\ps. backend_progs_data_prog ps) =
   cake_orac asm_conf c' src f4 (\ps. backend_progs_word_prog ps)) /\
   (
   backend_compile asm_conf c prog = SOME (b,bm,c') /\
     stack_to_lab_config_perf_calls (backend_config_stack_conf c) = F
     ==>
   (\((bm0,cfg),prg). (\(prg2,fs,bm). (cfg,prg2,append (FST bm)))
     (compile_word_to_stack asm_conf F (asm_config_reg_count asm_conf
       -
       (LENGTH (asm_config_avoid_regs asm_conf) + 5)) prg
         (misc_Nil,bm0))) o
   cake_orac asm_conf c' src (SND o SND o SND o SND o SND o
     config_tuple2) (\ps. backend_progs_word_prog ps) =
   cake_orac asm_conf c' src (SND o SND o SND o SND o SND o SND o
     config_tuple2)
     (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps))) /\
   (
   backend_compile asm_conf c prog = SOME (b,bm,c') /\ reg_nm =
     stack_to_lab_config_reg_names (backend_config_stack_conf c) /\
     jump = stack_to_lab_config_jump (backend_config_stack_conf c) /\
       sp = asm_config_reg_count asm_conf -
       (LENGTH (asm_config_avoid_regs asm_conf) + 3) /\
     offs = asm_config_addr_offset asm_conf ==>
   pure_co (compile_no_stubs reg_nm jump offs sp o FST) o
   cake_orac asm_conf c' src f5 (\ps. (backend_progs_stack_prog
     ps,backend_progs_cur_bm ps)) =
   cake_orac asm_conf c' src f5 (\ps. backend_progs_lab_prog ps))`,
  CHEAT_TAC);;

(* HOL4 backendProofScript.sml:583-586: ML code, not ported *)

(* HOL4 backendProofScript.sml:588-589: ML code, not ported *)

let cake_orac_0 = prove
 (`cake_orac asm_conf c' src f g 0 = (f c',g (SND (compile_inc_progs T
  asm_conf c' (src 0))))`,
  CHEAT_TAC);;

let cake_orac_SUC = prove
 (`cake_orac asm_conf c' src f g (SUC i) = (let (c'',ps) = cake_orac
  asm_conf c' src I I i in
     let c''' = FST (compile_inc_progs T asm_conf c'' (src i)) in
     (f c''',g (SND (compile_inc_progs T asm_conf c''' (src (SUC
       i))))))`,
  CHEAT_TAC);;

(* [local] *)
let compile_inc_progs_src_env_tup = prove
 (`compile_inc_progs T asm_conf cfg p = (cfg',progs) ==>
  backend_progs_env_id
   progs = FST p /\ backend_progs_source_prog progs = SND p`,
  CHEAT_TAC);;

let cake_orac_SUC2 = prove
 (`cake_orac asm_conf c' src f g (SUC i) = (
     let (c'',ps) = cake_orac asm_conf c' src I I i in
     let c''' = FST (compile_inc_progs T asm_conf c''
       (backend_progs_env_id ps,backend_progs_source_prog ps)) in
     (f c''',g (SND (compile_inc_progs T asm_conf c''' (src (SUC
       i))))))`,
  CHEAT_TAC);;

let from_clos_conf_EX = prove
 (`from_clos asm_conf c p = v ==>
   (?cc names p. from_bvl asm_conf (backend_config_clos_conf_fupd
     (K cc) c) names p = v)`,
  CHEAT_TAC);;

let from_bvl_conf_EX = prove
 (`from_bvl asm_conf c names p = v ==>
   (?st bvlcu (names:mlstring spt) p.
     from_bvi asm_conf (backend_config_clos_conf_fupd (\c.
       clos_to_bvl_config_start_fupd (K st) c)
       (backend_config_bvl_conf_fupd bvlcu c)) names p = v)`,
  CHEAT_TAC);;

let from_bvi_conf_EX = prove
 (`from_bvi asm_conf c names p = v ==>
   (?p. from_data asm_conf c names p = v)`,
  CHEAT_TAC);;

let from_data_conf_EX = prove
 (`from_data asm_conf c names p = v ==>
   (?wcu p. from_word asm_conf
     (backend_config_word_to_word_conf_fupd wcu c) names p = v)`,
  CHEAT_TAC);;

let from_word_conf_EX = prove
 (`from_word asm_conf c names p = v ==>
   (?wc p bm. from_stack asm_conf (backend_config_word_conf_fupd (K
     wc) c) names p bm = v)`,
  CHEAT_TAC);;

let from_stack_conf_EX = prove
 (`from_stack asm_conf c names p bm = v ==>
   (?p. from_lab asm_conf c names p bm = v)`,
  CHEAT_TAC);;

let from_lab_conf_EX = prove
 (`from_lab asm_conf c names p bm = SOME (bytes,bitmap,c') ==>
   (?lc. c' = backend_config_symbols_fupd (K (MAP (\(n,p,l).
     (lookup_any n names (implode "NOTFOUND"),p,l))
     (lab_to_target_config_sec_pos_len lc)))
     (backend_config_lab_conf_fupd (K lc) c))`,
  CHEAT_TAC);;

(* HOL4 backendProofScript.sml:694-701: ML code, not ported *)

(* HOL4 backendProofScript.sml:703-712: code that the source has in a
   comment *)

let oracle_monotonic_globals_flat_to_clos = prove
 (`no_Mat_decs p /\
   (!n. no_Mat_decs (SND (orac n))) /\
   oracle_monotonic (IMAGE SUC o SET_OF_BAG o
         flatProps_elist_globals o SND) (<)
     (0 INSERT IMAGE SUC (SET_OF_BAG (flatProps_elist_globals p)))
     orac ==>
   oracle_monotonic (SET_OF_BAG o closProps_elist_globals o FST o
     SND) (<)
     (SET_OF_BAG (closProps_elist_globals (word_to_stack_compile_prog
       p)))
     (pure_co inc_compile_decs o orac)`,
  CHEAT_TAC);;

let cake_orac_eq_I = prove
 (`!f g. cake_orac asm_conf c syntax f g = (f ## g) o cake_orac
  asm_conf c syntax I I`,
  CHEAT_TAC);;

let cake_orac_invariant = prove
 (`P (f c) /\
   (!c prog. P (f c) ==> P (f (FST (compile_inc_progs T asm_conf c
     prog)))) ==>
   (!i. P (FST (cake_orac asm_conf c syntax f g i)))`,
  CHEAT_TAC);;

(* HOL4 backendProofScript.sml:753: ML code, not ported *)

(* HOL4 backendProofScript.sml:755-758: ML code, not ported *)

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let bvl_to_bvi_compile_semantics2 = prove
 (cake_as_vars (fun () ->
    `bvl_to_bvi_compile start c names prog =
       (start',prog',inlines,bvi_inlines,n1,n2,n3,names1) /\
     (?v. FST (co 0) = (inlines,n1,n2,n3,bvi_inlines,v)) /\
     (!n. ALL_DISTINCT (MAP FST (SND (co n)))) /\
     ALL_DISTINCT (MAP FST prog) /\
     is_state_oracle (bvi_tailrec_compile_prog
       (bvl_to_bvi_config_do_tailrec c))
       (state_co bvl_to_bvi_compile_inc
         (state_co (bvl_inline_compile_inc
           (bvl_to_bvi_config_inline_size_limit c)
           (bvl_to_bvi_config_split_main_at_seq
             c) (bvl_to_bvi_config_exp_cut c)) co)) /\
     is_state_oracle (bvi_tmc_compile_prog
       (bvl_to_bvi_config_do_tmc c))
       (state_co (bvi_tailrec_compile_prog
         (bvl_to_bvi_config_do_tailrec c))
         (state_co bvl_to_bvi_compile_inc
           (state_co (bvl_inline_compile_inc
             (bvl_to_bvi_config_inline_size_limit c)
             (bvl_to_bvi_config_split_main_at_seq
               c) (bvl_to_bvi_config_exp_cut c)) co))) ==>
                 ~(bvlSem_semantics ffi0 (fromAList prog) co (full_cc c
                 cc)
       start = ffi_Fail) ==>
     bviSem_semantics ffi0 (fromAList prog') (full_co c co)
       cc start' =
     bvlSem_semantics (ffi0:'ffi ffi_state) (fromAList prog)
       co (full_cc c cc) start`),
  CHEAT_TAC);;

let compile_no_stubs_wrap_pure_co = prove
 (`(\n. (let (c,p,b) = coracle n in
     (c,compile_no_stubs rn j offs sp p))) =
   (pure_co (compile_no_stubs rn j offs sp o FST) o coracle)`,
  CHEAT_TAC);;

(* HOL4 backendProofScript.sml:832-833: a theorem that HOL4 states as
   the value of an ML expression: full_make_init_semantics2 *)

let data_num_stubs_LE_tailrec_compile = prove
 (`data_num_stubs <= nn2 /\ ALL ((<=) data_num_stubs) (MAP FST (orac n))
  ==>
   ALL ((<=) data_num_stubs)
     (MAP FST (state_co_progs (bvi_tailrec_compile_prog do_it) nn2
       orac n))`,
  CHEAT_TAC);;

let data_num_stubs_LE_bvl_bvi_compile = prove
 (`ALL ((<=) data_num_stubs)
     (MAP FST (state_co_progs bvl_to_bvi_compile_inc nn1 orac n))`,
  CHEAT_TAC);;

let configs_nn2_MULT_namespaces = prove
 (`?k.
     bvl_to_bvi_config_next_name2 (backend_config_bvl_conf
       (cake_configs asm_conf c' syntax n)) =
       bvl_to_bvi_config_next_name2 (backend_config_bvl_conf c') + (k
       * bvl_to_bvi_namespaces)`,
  CHEAT_TAC);;

let configs_nn2_MOD_namespaces = prove
 (`bvl_to_bvi_config_next_name2 (backend_config_bvl_conf
   (cake_configs asm_conf c' syntax n)) MOD bvl_to_bvi_namespaces =
     bvl_to_bvi_config_next_name2 (backend_config_bvl_conf c') MOD
     bvl_to_bvi_namespaces`,
  CHEAT_TAC);;

let configs_nn3_MULT_namespaces = prove
 (`?k.
     bvl_to_bvi_config_next_name3 (backend_config_bvl_conf
       (cake_configs asm_conf c' syntax n)) =
       bvl_to_bvi_config_next_name3 (backend_config_bvl_conf c') + (k
       * bvl_to_bvi_namespaces)`,
  CHEAT_TAC);;

let configs_nn3_MOD_namespaces = prove
 (`bvl_to_bvi_config_next_name3 (backend_config_bvl_conf
   (cake_configs asm_conf c' syntax n)) MOD bvl_to_bvi_namespaces =
     bvl_to_bvi_config_next_name3 (backend_config_bvl_conf c') MOD
     bvl_to_bvi_namespaces`,
  CHEAT_TAC);;

let configs_nn2_MOD_namespaces_ok = prove
 (`backend_compile asm_conf c prog = SOME (b,bm,c') /\ backend_config_ok
  asm_conf c ==> bvl_to_bvi_config_next_name2 (backend_config_bvl_conf
   c') MOD bvl_to_bvi_namespaces = 2`,
  CHEAT_TAC);;

let configs_nn3_MOD_namespaces_ok = prove
 (`backend_compile asm_conf c prog = SOME (b,bm,c') /\ backend_config_ok
  asm_conf c ==> bvl_to_bvi_config_next_name3 (backend_config_bvl_conf
   c') MOD bvl_to_bvi_namespaces = 3`,
  CHEAT_TAC);;

let bvl_to_bvi_compile_inc_all_num_stubs_LE = prove
 (`bvl_to_bvi_compile_inc_all c bvl = (c',bvi) ==>
   bvl_num_stubs <= bvl_to_bvi_config_next_name2 c /\ bvl_num_stubs
     <= bvl_to_bvi_config_next_name3 c ==>
   ALL ((<=) bvl_num_stubs) (MAP FST bvi)`,
  CHEAT_TAC);;

let bvl_num_stubs_LE_bvi_prog = prove
 (`backend_compile asm_conf c prog = SOME (b,bm,c') ==>
   ALL ((<=) bvl_num_stubs)
     (MAP FST (SND (cake_orac asm_conf c' syntax f (\ps.
       backend_progs_bvi_prog ps) n)))`,
  CHEAT_TAC);;

(* HOL4 backendProofScript.sml:1003-1005: a theorem that HOL4 states
   as the value of an ML expression: stack_to_lab_orac_eq_std_sym *)

let state_co_fun_def = new_definition
  `state_co_fun f_inc x =
     (let ((cfg1,cfg2),p) = x in
     let (_2,p') = f_inc cfg1 p in
     (cfg2,p'))`;;

let state_co_eq_comp = prove
 (`state_co f_inc orac = state_co_fun f_inc o orac`,
  CHEAT_TAC);;

let is_state_oracle_cake_orac_comp = prove
 (`(!i ps'.
     let (c'',ps) = compile_inc_progs T asm_conf (cake_configs
       asm_conf c' syntax i) (syntax i) in
     let ((f_c,_3),f_p) = f (g (cake_configs asm_conf c' syntax i),h
       ps) in
     let ((f_c',_4),_5) = f (g c'',ps') in
     f_c' = FST (f_inc f_c f_p)) ==>
   is_state_oracle f_inc (f o cake_orac asm_conf c' syntax g h)`,
  CHEAT_TAC);;

(* HOL4 backendProofScript.sml:1039-1041: a theorem that HOL4 states
   as the value of an ML expression: is_state_oracle_cake_orac *)

let cake_orac_clos_is_state = prove
 (`is_state_oracle clos_to_bvl_clos_to_bvl_compile_inc
     (cake_orac asm_conf c' syntax (\c. (backend_config_clos_conf
       c,one)) (\ps. backend_progs_clos_prog ps))`,
  CHEAT_TAC);;

let cake_orac_source_is_state = prove
 (`is_state_oracle
     (\c (env_id,decs). inc_compile env_id c
       (source_to_source_compile decs))
     (cake_orac asm_conf c' syntax config_tuple1 (\ps.
       (backend_progs_env_id ps,backend_progs_source_prog ps)))`,
  CHEAT_TAC);;

(* HOL4 backendProofScript.sml:1066-1068: a theorem that HOL4 states
   as the value of an ML expression: SND_flat_to_clos_inc_compile *)

let is_state_oracle_cake_orac_to_comp = prove
 (`is_state_oracle f_inc (cake_orac asm_conf c' syntax st_f ps_f) ==>
   backend_compile asm_conf c prog = SOME (b,bm,c') ==>
   (!c'' ps c''' g_p'.
     (
     (\(sc,cc,bc,mc). (source_to_flat_config_pattern_cfg
       sc,clos_to_bvl_config_max_app cc,clos_to_bvl_config_do_call
       cc,IS_SOME (clos_to_bvl_config_known_conf cc),
         known_static_conf (clos_to_bvl_config_known_conf
           cc),clos_to_bvl_config_do_mti
           cc,bvl_to_bvi_config_inline_size_limit
           bc,bvl_to_bvi_config_split_main_at_seq
         bc,bvl_to_bvi_config_exp_cut bc,bvl_to_bvi_config_do_tailrec
           bc,bvl_to_bvi_config_do_tmc bc,
                     // f step
                     mc)) o (\c. (backend_config_source_conf
                       c,backend_config_clos_conf
                       c,backend_config_bvl_conf
                       c,backend_config_data_conf
                       c,word_to_word_config_reg_alg
                       (backend_config_word_to_word_conf
             // g step
             c),backend_config_stack_conf c,(asm_conf:'a
               asm_config)))) c'' = ((\(sc,cc,bc,mc).
               (source_to_flat_config_pattern_cfg
               sc,clos_to_bvl_config_max_app
               cc,clos_to_bvl_config_do_call cc,IS_SOME
               (clos_to_bvl_config_known_conf cc),known_static_conf
               (clos_to_bvl_config_known_conf
               cc),clos_to_bvl_config_do_mti
               cc,bvl_to_bvi_config_inline_size_limit
               bc,bvl_to_bvi_config_split_main_at_seq
               bc,bvl_to_bvi_config_exp_cut
               bc,bvl_to_bvi_config_do_tailrec
               bc,bvl_to_bvi_config_do_tmc bc,mc)) o (\c.
               (backend_config_source_conf c,backend_config_clos_conf
               c,backend_config_bvl_conf c,backend_config_data_conf
               c,word_to_word_config_reg_alg
               (backend_config_word_to_word_conf
               c),backend_config_stack_conf c,(asm_conf:'a
               asm_config)))) c ==>
     (let (f_c',_6) = f_inc (FST (st_f c'')) (ps_f ps) in
     let ((g_c,_7),g_p) = adj (g c'',h ps) in
     let (g_c',_8) = g_inc g_c g_p in
     // for some c''', if f step agrees, g step should agree
     f_c' = FST (st_f c''') ==> g_c' = FST (FST (adj (g
       c''',g_p'))))) ==>
   is_state_oracle g_inc (adj o cake_orac asm_conf c' syntax g h)`,
  CHEAT_TAC);;

(* [local] *)
let BAG_ALL_DISTINCT_BAG_IMAGE_SUC = prove
 (`BAG_ALL_DISTINCT s ==> BAG_ALL_DISTINCT (BAG_IMAGE SUC s)`,
  CHEAT_TAC);;
add_simp BAG_ALL_DISTINCT_BAG_IMAGE_SUC;;

(* [local] *)
let BAG_ALL_DISTINCT_BAG_IMAGE_SUC' = prove
 (`BAG_ALL_DISTINCT s ==> BAG_ALL_DISTINCT ((BAG_UNION) (BAG_INSERT 0
  (EMPTY_BAG)) (BAG_IMAGE SUC s))`,
  CHEAT_TAC);;
add_simp BAG_ALL_DISTINCT_BAG_IMAGE_SUC';;

let cake_orac_clos_syntax_oracle_ok = prove
 (`backend_compile asm_conf (c:backend_config) prog = SOME (b,bm,c') /\
   backend_compile c2 clos_prog = (clos_c',clos_prog') /\
   (?st. backend_config_clos_conf c' = start_fupd (K st) clos_c') /\
   c2 = backend_config_clos_conf c /\ clos_prog = SND (to_clos c
     prog) /\
   1 <= clos_to_bvl_config_max_app (backend_config_clos_conf c) /\
     backend_config_source_conf
   c = prim_src_config ==>
   clos_to_bvlProof_syntax_oracle_ok (backend_config_clos_conf c)
     clos_c' clos_prog
      (cake_orac asm_conf c' syntax (SND o config_tuple1) (\ps.
        backend_progs_clos_prog ps))`,
  CHEAT_TAC);;

let cake_orac_bvl_ALL_DISTINCT = prove
 (`backend_compile asm_conf c prog = SOME (b,bm,c') ==>
   ALL_DISTINCT (MAP FST (SND (cake_orac asm_conf c' syntax f (\ps.
     backend_progs_bvl_prog ps) n)))`,
  CHEAT_TAC);;

let compile_lab_LENGTH = prove
 (`compile_lab asm_conf c secs = SOME (bytes,c') ==>
  lab_to_target_config_pos
   c' = LENGTH bytes + lab_to_target_config_pos c`,
  CHEAT_TAC);;

let bvl_to_bvi_compile_inc_all_DISTINCT = prove
 (`bvl_to_bvi_compile_inc_all c p = (c',p') /\
   ALL_DISTINCT (MAP FST p) /\ bvl_to_bvi_config_next_name2 c MOD
     bvl_to_bvi_namespaces = 2 /\ bvl_to_bvi_config_next_name3
   c MOD bvl_to_bvi_namespaces = 3 ==>
   ALL_DISTINCT (MAP FST p')`,
  CHEAT_TAC);;

let cake_orac_stack_ALL_DISTINCT = prove
 (`backend_compile asm_conf c prog = SOME (b,bm,c') ==>
   ALL_DISTINCT (MAP FST (FST (SND (cake_orac asm_conf c' syntax
     (SND o SND o SND o SND o SND o SND o config_tuple2)
     (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps))
       n))))`,
  CHEAT_TAC);;

let MAP_full_compile_single_to_compile = prove
 (`Abbrev (pp = MAP (\p. full_compile_single (asm_config_two_reg_arith
  asm_c) reg_count
       reg_alg asm_c (p,NONE)) pp0) /\
   reg_count = (asm_config_reg_count asm_c - (LENGTH
     (asm_config_avoid_regs asm_c) + 5)) ==>
   (?wc ign. word_to_word_compile wc asm_c pp0 = (ign,pp))`,
  CHEAT_TAC);;

let compile_to_word_conventions2 = prove
 (`backend_compile wc ac p = (_9,ps) /\
   ALL (\(_10,_11,prg). no_share_inst prg \/ ~(asm_config_ISA ac =
     Ag32)) p ==>
   MAP FST ps = MAP FST p /\
   ALL2 labels_rel
     (MAP (wordConvs_extract_labels o SND o SND) p)
     (MAP (wordConvs_extract_labels o SND o SND) ps) /\
   ALL (\(n,m,prog).
     flat_exp_conventions prog /\
     post_alloc_conventions
       (asm_config_reg_count ac - (5 + LENGTH (asm_config_avoid_regs
         ac))) prog /\
     (ALL (\(n,m,prog).
               every_inst (inst_ok_less ac) prog)
            p /\ asm_offset_ok 0 (asm_config_addr_offset ac) (n2w 0)
              /\ asm_offset_ok 0 (asm_config_hw_offset ac) (n2w 0) /\
      asm_offset_ok 0 (asm_config_byte_offset ac) (n2w 0) ==>
                full_inst_ok_less ac prog) /\
               (asm_config_two_reg_arith ac ==>
                every_inst two_reg_inst prog) /\
               (no_share_inst prog \/ ~(asm_config_ISA ac = Ag32)))
                 ps`,
  CHEAT_TAC);;

let sec_labels_ok_FST_code_labels_Section_num = prove
 (`ALL sec_labels_ok code ==>
   IMAGE FST (labProps_get_code_labels code) = set_of_list (MAP
     Section_num code)`,
  CHEAT_TAC);;

let stack_labels_ok_FST_code_labels_Section_num = prove
 (`labels_ok code ==>
   IMAGE FST (labProps_get_code_labels code) = set_of_list (MAP
     Section_num code)`,
  CHEAT_TAC);;

let lab_labels_ok_oracle = prove
 (`backend_compile asm_conf c prog = SOME (b,bm,c') /\
   cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND o SND o
     config_tuple2)
     (\ps. backend_progs_lab_prog ps) i = (cfg,code) ==>
   labels_ok code`,
  CHEAT_TAC);;

let compile_lab_domain_labels = prove
 (`compile_lab asm_conf c prog = SOME (b,c') ==>
   domain (lab_to_target_config_labels c') = IMAGE FST
     (labProps_get_code_labels prog) UNION domain
     (lab_to_target_config_labels c)`,
  CHEAT_TAC);;

let accum_lab_conf_labels = prove
 (`backend_compile asm_conf c prog = SOME (b,bm,c') ==>
   domain (lab_to_target_config_labels (backend_config_lab_conf
     (cake_configs asm_conf c' syntax i))) SUBSET
   domain (lab_to_target_config_labels (backend_config_lab_conf c'))
     UNION UNIONS (set_of_list (MAP (set_of_list o MAP Section_num o
     SND o cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND
       o SND o config_tuple2)
     (\ps. backend_progs_lab_prog ps)) (COUNT_LIST i)))`,
  CHEAT_TAC);;

let MAP_Section_num_stack_to_lab_SUBSET = prove
 (`set_of_list (MAP FST prog) SUBSET labs /\ count (SUC
  gc_stub_location) SUBSET labs ==>
   set_of_list (MAP Section_num (backend_compile scc dc max_heap sp
     offset prog)) SUBSET labs`,
  CHEAT_TAC);;

let to_data_labels_ok = prove
 (`backend_compile asm_conf c prog = SOME (b,bm,c') /\ backend_config_ok
  asm_conf c ==>
   (let (_12,p,_13) = to_data c prog in
   ALL (\n. data_num_stubs <= n) (MAP FST p) /\ ALL_DISTINCT (MAP
     FST p))`,
  CHEAT_TAC);;

let data_to_word_stubs_above_store_consts_stub = prove
 (`ALL (\n. n > wordLang_store_consts_stub_location) (MAP FST
  (data_to_word_stubs (:'a) dc))`,
  CHEAT_TAC);;

let to_word_labels_ok = prove
 (`backend_compile asm_conf c prog = SOME (b,bm,c') /\ backend_config_ok
  asm_conf c ==>
   (let (_14,p,_15) = to_word asm_conf c prog in
   ALL_DISTINCT (MAP FST p) /\
   ALL (\n. n > wordLang_store_consts_stub_location) (MAP FST p) /\
   ALL (\(n,m,p).
     let labs = wordConvs_extract_labels p in
     ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) labs /\
       ALL_DISTINCT labs) p)`,
  CHEAT_TAC);;

let to_bvi_perf_calls = prove
 (`!c c' prog p n.
     (to_bvi c prog = (c',p,n)) ==> stack_to_lab_config_perf_calls
       (backend_config_stack_conf c) = stack_to_lab_config_perf_calls
       (backend_config_stack_conf c')`,
  CHEAT_TAC);;

let to_data_perf_calls = prove
 (`!c c' prog p n.
     (to_data c prog = (c',p,n)) ==> stack_to_lab_config_perf_calls
       (backend_config_stack_conf c) = stack_to_lab_config_perf_calls
       (backend_config_stack_conf c')`,
  CHEAT_TAC);;

let to_word_perf_calls = prove
 (`!c c' prog p n.
     (to_word asm_conf c prog = (c',p,n)) ==>
       stack_to_lab_config_perf_calls (backend_config_stack_conf c) =
       stack_to_lab_config_perf_calls (backend_config_stack_conf c')`,
  CHEAT_TAC);;

let to_lab_labels_ok = prove
 (`backend_compile asm_conf c prog = SOME (b,bm,c') /\ backend_config_ok
  asm_conf c ==>
   labels_ok (FST (SND (SND (to_lab asm_conf c prog))))`,
  CHEAT_TAC);;

let oracle_monotonic_slice = prove
 (`!g.
   (!z. oracle_monotonic (\x. f x INTER PREIMAGE g {z}) (\x y. ~(x =
     y))
     (init_s INTER PREIMAGE g {z}) orac) ==>
   oracle_monotonic f (\x y. ~(x = y)) init_s orac`,
  CHEAT_TAC);;

let oracle_monotonic_rel_mono = prove
 (`!R R'. (!x y. R x y ==> R' x y) /\ oracle_monotonic f R init_s orac
  ==>
   oracle_monotonic f R' init_s orac`,
  CHEAT_TAC);;

(* oracle_monotonic_state_with_inv *)
let backendProof_oracle_monotonic_state_with_inv = prove
 (`!P n_f. P (FST (FST (orac 0))) /\
   (!x. x IN St ==> x < n_f (FST (FST (orac 0)))) /\
   (!i st prog st' prog' st_ex. f_inc st prog = (st',prog') /\ P st
     /\
         orac i = ((st,st_ex),prog) ==>
     P st' /\ n_f st <= n_f st' /\
     (!cfg x. x IN f (cfg,prog') ==> n_f st <= x /\ x < n_f st')) /\
   is_state_oracle f_inc orac ==>
   oracle_monotonic f (<) (St:num->bool) (state_co f_inc orac)`,
  CHEAT_TAC);;

let oracle_monotonic_bounded_state = prove
 (`!n_f.
   (!x. x IN St ==> x < n_f (orac 0)) /\
   (!i. n_f (orac i) <= n_f (orac (SUC i)) /\
         (!x. x IN f (orac i) ==> n_f (orac i) <= x /\ x < n_f (orac
           (SUC i)))) ==>
   oracle_monotonic f (<) (St:num->bool) orac`,
  CHEAT_TAC);;

(* compile_prog_avoids_nss_2 *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let backendProof_compile_prog_avoids_nss_2 = prove
 (cake_as_vars (fun () ->
    `word_to_stack_compile_prog start f prog = (loc,code,new_state) /\
     MEM k (MAP FST code) /\ k MOD bvl_to_bvi_namespaces = 2 ==>
     k < bvl_num_stubs`),
  CHEAT_TAC);;

let tailrec_compile_prog_MEM_not_nss_2 = prove
 (`!ys xs n1 n e do_it.
   bvi_tailrec_compile_prog do_it n xs = (n1,ys) /\ MEM e (MAP FST
     ys) /\
   n MOD bvl_to_bvi_namespaces = 2 /\ ~(e MOD bvl_to_bvi_namespaces =
     2) ==>
   MEM e (MAP FST xs)`,
  CHEAT_TAC);;

let tmc_compile_prog_MEM_not_nss_3 = prove
 (`!ys xs n1 n e do_it.
   bvi_tmc_compile_prog do_it n xs = (n1,ys) /\ MEM e (MAP FST ys) /\
   n MOD bvl_to_bvi_namespaces = 3 /\ ~(e MOD bvl_to_bvi_namespaces =
     3) ==>
   MEM e (MAP FST xs)`,
  CHEAT_TAC);;

let is_state_oracle_tailrec_cake_orac = prove
 (`backend_compile asm_conf c prog = SOME (b,bm,c') ==>
   is_state_oracle (bvi_tailrec_compile_prog
     (bvl_to_bvi_config_do_tailrec (backend_config_bvl_conf c)))
     (state_co bvl_to_bvi_compile_inc (state_co
       (bvl_inline_compile_inc (bvl_to_bvi_config_inline_size_limit
         (backend_config_bvl_conf c))
         (bvl_to_bvi_config_split_main_at_seq (backend_config_bvl_conf
         c)) (bvl_to_bvi_config_exp_cut (backend_config_bvl_conf c)))
       (cake_orac asm_conf c' syntax config_tuple2 (\ps.
         backend_progs_bvl_prog ps))))`,
  CHEAT_TAC);;

let is_state_oracle_tmc_cake_orac = prove
 (`backend_compile asm_conf c prog = SOME (b,bm,c') ==>
   is_state_oracle (bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc
     (backend_config_bvl_conf c)))
     (state_co (bvi_tailrec_compile_prog
       (bvl_to_bvi_config_do_tailrec (backend_config_bvl_conf c)))
       (state_co bvl_to_bvi_compile_inc (state_co
       (bvl_inline_compile_inc (bvl_to_bvi_config_inline_size_limit
         (backend_config_bvl_conf c))
         (bvl_to_bvi_config_split_main_at_seq (backend_config_bvl_conf
         c)) (bvl_to_bvi_config_exp_cut (backend_config_bvl_conf c)))
       (cake_orac asm_conf c' syntax config_tuple2 (\ps.
         backend_progs_bvl_prog ps)))))`,
  CHEAT_TAC);;

let inline_compile_inc_names = prove
 (`bvl_inline_compile_inc l b i spt prog = (inlines,prog3) ==>
   MAP FST prog3 = MAP FST prog`,
  CHEAT_TAC);;

let bvi_inline_state_co_MAP_FST = prove
 (`MAP FST (SND (state_co bvi_inline_compile_inc co n)) =
   MAP FST (SND (co n))`,
  CHEAT_TAC);;
add_simp bvi_inline_state_co_MAP_FST;;

let oracle_monotonic_bvi_inline = prove
 (`oracle_monotonic (set_of_list o MAP FST o SND) R init (state_co
  bvi_inline_compile_inc co) =
   oracle_monotonic (set_of_list o MAP FST o SND) R init co`,
  CHEAT_TAC);;
add_simp oracle_monotonic_bvi_inline;;

(* bvi_inline is name preserving, so the namespace-sliced projection used
   by monotonic_labels_bvl_to_bvi cannot see it either. *)
let oracle_monotonic_bvi_inline_inter = prove
 (`oracle_monotonic (\x. set_of_list (MAP FST (SND x)) INTER s) R init
  (state_co bvi_inline_compile_inc co) =
   oracle_monotonic (\x. set_of_list (MAP FST (SND x)) INTER s) R
     init co`,
  CHEAT_TAC);;
add_simp oracle_monotonic_bvi_inline_inter;;

let oracle_monotonic_subset_inject = prove
 (`!g. (!x y. R (g x) (g y) ==> R' x y) /\
   IMAGE g init_set' SUBSET init_set /\ (!n. IMAGE g (f' (co' n))
     SUBSET f (co n)) ==>
   oracle_monotonic f R init_set co ==>
   oracle_monotonic f' R' init_set' co'`,
  CHEAT_TAC);;

let oracle_monotonic_handle_init_component = prove
 (`!D. (!i x y. x IN D /\ y IN f (co i) ==> R x y) /\
   oracle_monotonic f R (init_set DIFF D) co ==>
   oracle_monotonic f R init_set co`,
  CHEAT_TAC);;

let oracle_monotonic_cake_orac_to_I = prove
 (`oracle_monotonic (\(cfg,p). f (cfg_f cfg,p_f p)) R init_st
     (cake_orac asm_conf c' syntax I I) ==>
   oracle_monotonic f R init_st (cake_orac asm_conf c' syntax cfg_f
     p_f)`,
  CHEAT_TAC);;

let cake_orac_monotonic_bounded_state = prove
 (`!n_f.
   (!x. x IN St ==> x < n_f c') /\
   (!i c2 ps. let c1 = cake_configs asm_conf c' syntax i in
     compile_inc_progs T asm_conf c1 (syntax i) = (c2,ps) ==>
     n_f c1 <= n_f c2 /\
     (!x. x IN f (cfg_f c1,p_f ps) ==> n_f c1 <= x /\ x < n_f c2))
       ==>
   oracle_monotonic f (<) (St:num->bool) (cake_orac asm_conf c'
     syntax cfg_f p_f)`,
  CHEAT_TAC);;

let monotonic_DISJOINT_labels_lab = prove
 (`backend_compile asm_conf c prog = SOME (b,bm,c') /\
   oracle_monotonic (set_of_list o MAP Section_num o SND) (\x y. ~(x
     = y))
     (domain (lab_to_target_config_labels (backend_config_lab_conf
       c')))
     (cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND o SND
       o config_tuple2)
                 (\ps. backend_progs_lab_prog ps)) ==>
   DISJOINT (domain (lab_to_target_config_labels
     (backend_config_lab_conf (cake_configs asm_conf c' syntax i))))
     (set_of_list (MAP Section_num (SND (cake_orac asm_conf c' syntax
       (SND o SND o SND o SND o SND o SND o config_tuple2) (\ps.
         backend_progs_lab_prog ps) i))))`,
  CHEAT_TAC);;

let monotonic_labels_stack_to_lab = prove
 (`backend_compile asm_conf c prog = SOME (b,bm,c') /\ backend_config_ok
  asm_conf c ==>
   oracle_monotonic (set_of_list o MAP FST o FST o SND) (\x y. ~(x =
     y))
     (set_of_list (MAP FST (FST (SND (SND (to_stack asm_conf c
       prog))))) UNION count (SUC gc_stub_location))
     (cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND o SND
       o config_tuple2)
         (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm
           ps))) ==>
   oracle_monotonic (set_of_list o MAP Section_num o SND) (\x y. ~(x
     = y))
     (domain (lab_to_target_config_labels (backend_config_lab_conf
       c')))
     (cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND o SND
       o config_tuple2)
         (\ps. backend_progs_lab_prog ps))`,
  CHEAT_TAC);;

let monotonic_labels_bvi_down_to_stack = prove
 (`backend_compile asm_conf c prog = SOME (b,bm,c') /\ backend_config_ok
  asm_conf c ==>
   oracle_monotonic (set_of_list o MAP FST o SND) (\x y. ~(x = y))
     (set_of_list (MAP FST (FST (SND (to_bvi c prog)))) UNION count
       (SUC data_num_stubs))
     (cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND o
       config_tuple2) (\ps. backend_progs_bvi_prog ps)) ==>
   oracle_monotonic (set_of_list o MAP FST o FST o SND) (\x y. ~(x =
     y))
     (set_of_list (MAP FST (FST (SND (SND (to_stack asm_conf c
       prog))))) UNION count (SUC gc_stub_location))
     (cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND o SND
       o config_tuple2)
         (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm
           ps)))`,
  CHEAT_TAC);;

let monotonic_labels_bvl_to_bvi = prove
 (`backend_compile asm_conf c prog = SOME (b,bm,c') /\ backend_config_ok
  asm_conf c ==>
   oracle_monotonic (set_of_list o MAP FST o SND) (\x y. ~(x = y))
     (set_of_list (MAP FST (FST (SND (to_bvl c prog)))))
     (cake_orac asm_conf c' syntax config_tuple2 (\ps.
       backend_progs_bvl_prog ps)) ==>
   oracle_monotonic (set_of_list o MAP FST o SND) (\x y. ~(x = y))
     (set_of_list (MAP FST (FST (SND (to_bvi c prog)))) UNION count
       (SUC data_num_stubs))
     (cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND o
       config_tuple2) (\ps. backend_progs_bvi_prog ps))`,
  CHEAT_TAC);;


(* syntax_oracle_ok_start *)
let backendProof_syntax_oracle_ok_start = prove
 (`clos_to_bvlProof_syntax_oracle_ok c (start_fupd f c') es co =
   clos_to_bvlProof_syntax_oracle_ok c c' es co`,
  CHEAT_TAC);;

let monotonic_labels_bvl = prove
 (`backend_compile asm_conf c prog = SOME (b,bm,c') /\ backend_config_ok
  asm_conf c ==>
   oracle_monotonic (set_of_list o MAP FST o SND) (\x y. ~(x = y))
     (set_of_list (MAP FST (FST (SND (to_bvl c prog)))))
     (cake_orac asm_conf c' syntax config_tuple2 (\ps.
       backend_progs_bvl_prog ps))`,
  CHEAT_TAC);;

let good_code_lab_oracle = prove
 (`backend_compile asm_conf c prog = SOME (b,bm,c') /\
   // validity of the code produced in the oracle at step i
   // - the tricky bit is cfg.labels, which gathers past and current labels
   // - older labels must always be there
   // - newer labels should never overlap older ones
   cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND o SND o
     config_tuple2)
     (\ps. backend_progs_lab_prog ps) i = (cfg,code) /\
   backend_config_ok asm_conf c /\
   asm_conf = target_config (machine_config_target mc) /\
   mc_conf_ok mc ==>
   lab_to_targetProof_good_code asm_conf
     (lab_to_target_config_labels cfg) code`,
  CHEAT_TAC);;

let oracle_stack_good_code = prove
 (`backend_compile asm_conf c prog = SOME (b,bm,c') /\
   reg_count_sub = (
     asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs
       asm_conf) + 3)) /\
   backend_config_ok asm_conf c /\ mc_conf_ok mc /\
   asm_conf = target_config (machine_config_target mc) ==>
   stack_to_labProof_good_code reg_count_sub
     (FST (SND (cake_orac asm_conf c' syntax f (\ps.
       (backend_progs_stack_prog ps,backend_progs_cur_bm ps)) n)))`,
  CHEAT_TAC);;

let to_lab_good_code_lemma = prove
 (`backend_compile (backend_config_stack_conf c)
  (backend_config_data_conf c) lim1 lim2 offs stack_prog = code /\
   backend_compile asm_conf3 F word_prog = (bm,wc,fs,stack_prog) /\
   backend_compile data_conf word_conf asm_conf2 data_prog =
     (col,word_prog) /\
   labels_ok code /\
   (\c ls. ALL (sec_ok_pre c) ls) conf code ==>
   lab_to_targetProof_good_code conf LN code`,
  CHEAT_TAC);;

(* HOL4 backendProofScript.sml:2670-2671: a theorem that HOL4 states
   as the value of an ML expression: data_to_word_orac_eq_std *)

(* HOL4 backendProofScript.sml:2673-2675: a theorem that HOL4 states
   as the value of an ML expression: data_to_word_orac_eq_sym_std *)

(*
max_print_depth := 20
*)

let compute_stack_frame_sizes_def = new_definition
  `compute_stack_frame_sizes c word_prog =
     (let reg_count = asm_config_reg_count c - LENGTH
       (asm_config_avoid_regs c) - 5 in
       mllist_mapi (\n (arg_count,prog).
               let stack_arg_count' = arg_count - reg_count in let
                   stack_var_count = MAX ((max_var prog DIV 2 + 1) -
                     reg_count) stack_arg_count' in if stack_var_count =
                     0 then 0 else stack_var_count + 1)
         (fromAList (word_prog)))`;;

let compute_stack_frame_sizes_thm = prove
 (`compute_stack_frame_sizes c word_prog =
     (let k = asm_config_reg_count c - LENGTH (asm_config_avoid_regs
       c) - 5 in
       mllist_mapi (\n (arg_count,prog).
         FST (SND (word_to_stack_compile_prog c F prog arg_count k
           (misc_Nil,0)))) (fromAList word_prog))`,
  CHEAT_TAC);;

let is_64_bits_def = new_definition
  `is_64_bits (:'a) <=> (dimindex (:'a) = 64)`;;

let is_safe_for_space_def = new_definition
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
       c) = backend_common_None))`;;

let compile_word_conf_eq = prove
 (`!c prog code data conf w_conf stack_prog stack_names.
     (backend_compile asm_conf c prog = SOME (code,data,conf)) /\
     (to_stack asm_conf c prog =
       (bm,w_conf,stack_prog,stack_names)) ==>
       word_to_stack_config_stack_frame_size (backend_config_word_conf
       conf) = word_to_stack_config_stack_frame_size
       (backend_config_word_conf w_conf)`,
  CHEAT_TAC);;

let to_word_lab_conf = prove
 (`!c c' prog p n.
     (to_word asm_conf c prog = (c',p,n)) ==>
       backend_config_lab_conf c = backend_config_lab_conf c'`,
  CHEAT_TAC);;

(* TODO: MOVE *)
let PERM_toAList_fromAList = prove
 (`!p. ALL_DISTINCT (MAP FST p) ==> PERM (toAList (fromAList p)) p`,
  CHEAT_TAC);;

let compile_word_to_stack_sfs_aux = prove
 (`!ac perf k p bm progs' fs' bitmaps.
     compile_word_to_stack ac perf k p bm = (progs',fs',bitmaps) /\
       perf = F ==>
      fromAList
        (MAP
           (\kv.
                (FST kv,
                 (\(arg_count,prog).
                      FST (SND (word_to_stack_compile_prog ac perf
                        prog arg_count k (misc_Nil,0)))) (SND kv))) p)
                        = fromAList (MAP (\((i,_16),n). (i,n)) (ZIP
                        progs' fs'))`,
  CHEAT_TAC);;

let IMP_is_safe_for_space = prove
 (`backend_config_ok (asm_conf:'a asm_config) c ==>
   backend_compile asm_conf c prog = SOME (code,data,conf) ==>
   to_data c prog = (bvi_conf,data_prog,names) ==>
     ~(data_to_word_config_gc_kind (backend_config_data_conf
   c) = backend_common_None) ==>
   data_lang_safe_for_space ffi (fromAList data_prog)
     (compute_limits (data_to_word_config_len_size
       (backend_config_data_conf c)) (is_64_bits (:'a))
       (data_to_word_config_has_fp_ops (backend_config_data_conf c))
       (data_to_word_config_has_fp_tern (backend_config_data_conf c))
       stack_heap_limit) (word_to_stack_config_stack_frame_size
       (backend_config_word_conf
     conf)) InitGlobals_location ==> backendProof_is_safe_for_space
       ffi asm_conf c prog stack_heap_limit`,
  CHEAT_TAC);;

let read_limits_def = new_definition
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

(* [local] *)
let FST_SND_EQ = prove
 (`(FST x = y /\ SND x = z <=> x = (y,z)) /\
   (SND x = z /\ FST x = y <=> x = (y,z))`,
  CHEAT_TAC);;

(* [local] *)
let PERMUTE_IMP_LINV = prove
 (`f PERMUTES UNIV ==> (!x y. (y = LINV f UNIV x <=> x = f y))`,
  CHEAT_TAC);;

let state_co_inc_compile_has_flat_comp = prove
 (`backend_compile asm_conf c prog = SOME (b,bm,c') ==>
   state_co (\c (env_id,(decs:dec list)). inc_compile env_id c (f
     decs)) (cake_orac asm_conf c' src config_tuple1 g) =
   pure_co (MAP (compile_dec (source_to_flat_config_pattern_cfg
     (backend_config_source_conf c)))) o
   state_co (\c (env_id,decs). inc_compile_prog env_id c (f decs))
     (cake_orac asm_conf c' src config_tuple1 g)`,
  CHEAT_TAC);;

let add_eval_state_def = define_cases
  [`add_eval_state NONE s0 = s0`;
   `add_eval_state (SOME ci) s0 =
    semanticPrimitives_state_eval_state_fupd (K (SOME
    (mk_init_eval_state ci)))
      s0`];;

let add_eval_state_ffi = prove
 (`state_ffi
     (add_eval_state opt_ev s0) = state_ffi s0`,
  CHEAT_TAC);;


let opt_eval_config_wf_def = define_cases
  [`opt_eval_config_wf asm_conf c' (SOME ci) =
    (compiler_instance_compiler_fun
      ci = compile_inc_progs_for_eval asm_conf /\
      INJ (compiler_instance_config_v ci) UNIV UNIV /\
          compiler_instance_init_state ci = c')`;
   `opt_eval_config_wf asm_conf c' NONE = T`];;

let backend_from_data_tuple_cc_def = new_definition
  `backend_from_data_tuple_cc asm_conf (c:backend_config) cfg =
     OPTION_MAP (I ## MAP upper_w2w ## I) o
       (\progs.
         (\(bm0,cfg) progs.
           (\(progs,fs,bm).
             OPTION_MAP
               (\(bytes,cfg).
                 (bytes,append (FST bm),(SND bm,cfg)))
               (backend_compile asm_conf cfg
                 (MAP prog_to_section
                   (MAP
                     (stack_alloc_prog_comp
                       (stack_to_lab_config_reg_names
                       (backend_config_stack_conf c)))
                     (MAP
                       (stack_alloc_prog_comp
                         (stack_to_lab_config_jump
                         (backend_config_stack_conf c))
                         (asm_config_addr_offset
                         asm_conf)
                         (asm_config_reg_count asm_conf - (LENGTH
                           (asm_config_avoid_regs asm_conf) + 3)))
                       (MAP stack_alloc_prog_comp progs))))))
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
               MAP (data_to_word_compile_part (ensure_fp_conf_ok
                 asm_conf (backend_config_data_conf c)))`;;

let backend_from_flat_tuple_cc_def = new_definition
  `backend_from_flat_tuple_cc asm_conf (c:backend_config) =
     pure_cc inc_compile_decs
       (compile_common_inc (backend_config_clos_conf c)
          (pure_cc (clos_to_bvl_compile_inc
            (clos_to_bvl_config_max_app (backend_config_clos_conf c)))
            (full_cc (backend_config_bvl_conf c) (pure_cc
              bvi_to_data_compile_prog
              (backend_from_data_tuple_cc asm_conf c)))))`;;

let known_cc_eq_state_cc_inc = prove
 (`known_cc kc cc =
   state_cc (known_compile_inc (known_static_conf kc)) cc`,
  CHEAT_TAC);;

let known_compile_inc_retreive_spt = prove
 (`known_compile_inc (known_static_conf kcfg1)
     (option_val_approx_spt kcfg2) p = (spt,p') /\
   IS_SOME kcfg2 = IS_SOME kcfg1 ==>
   option_val_approx_spt (option_upd_val_spt spt kcfg2) = spt`,
  CHEAT_TAC);;

let backend_from_flat_tuple_cc_eq_compile_inc_progs = prove
 (`(((
     (\(sc,cc,bc,mc). (source_to_flat_config_pattern_cfg
       sc,clos_to_bvl_config_max_app cc,clos_to_bvl_config_do_call
       cc,IS_SOME (clos_to_bvl_config_known_conf cc),
         known_static_conf (clos_to_bvl_config_known_conf
           cc),clos_to_bvl_config_do_mti
           cc,bvl_to_bvi_config_inline_size_limit
           bc,bvl_to_bvi_config_split_main_at_seq
         bc,bvl_to_bvi_config_exp_cut bc,bvl_to_bvi_config_do_tailrec
           bc,bvl_to_bvi_config_do_tmc bc,mc)) o (\c.
           (backend_config_source_conf c,backend_config_clos_conf
           c,backend_config_bvl_conf c,backend_config_data_conf
           c,word_to_word_config_reg_alg
           (backend_config_word_to_word_conf
             c),backend_config_stack_conf c,(asm_conf:'a
               asm_config))))) c') = ((((\(sc,cc,bc,mc).
               (source_to_flat_config_pattern_cfg
               sc,clos_to_bvl_config_max_app
               cc,clos_to_bvl_config_do_call cc,IS_SOME
               (clos_to_bvl_config_known_conf cc),known_static_conf
               (clos_to_bvl_config_known_conf
               cc),clos_to_bvl_config_do_mti
               cc,bvl_to_bvi_config_inline_size_limit
               bc,bvl_to_bvi_config_split_main_at_seq
               bc,bvl_to_bvi_config_exp_cut
               bc,bvl_to_bvi_config_do_tailrec
               bc,bvl_to_bvi_config_do_tmc bc,mc)) o (\c.
               (backend_config_source_conf c,backend_config_clos_conf
               c,backend_config_bvl_conf c,backend_config_data_conf
               c,word_to_word_config_reg_alg
               (backend_config_word_to_word_conf
               c),backend_config_stack_conf c,(asm_conf:'a
               asm_config))))) c) /\
   src_cfg = backend_config_source_conf c' /\
     stack_to_lab_config_perf_calls (backend_config_stack_conf
   c) = F /\ source_to_flat_config_pattern_cfg
     (backend_config_source_conf
   c) = source_to_flat_config_pattern_cfg prim_src_config ==>
   backend_from_flat_tuple_cc asm_conf c (SND (config_tuple1 c'))
     (MAP (compile_dec (source_to_flat_config_pattern_cfg
       prim_src_config)) (SND (inc_compile_prog env_id src_cfg
       (source_to_source_compile decs)))) =
   (let (c'',ps) = compile_inc_progs T asm_conf c' (env_id,decs) in
     OPTION_MAP (\(bs,ws). (bs,
         MAP upper_w2w ws,
         SND (config_tuple1 c''))) (backend_progs_target_prog ps))`,
  CHEAT_TAC);;

(* [local] *)
let compile_inc_progs_src_env = prove
 (`backend_progs_env_id
     (SND (compile_inc_progs T asm_conf c env_decs)) = FST env_decs
       /\ backend_progs_source_prog
     (SND (compile_inc_progs T asm_conf c env_decs)) = SND env_decs`,
  CHEAT_TAC);;

let cake_orac_cfg_f_eq_I = prove
 (`!f g. cake_orac asm_conf c syntax f g = (f ## I) o cake_orac
  asm_conf c syntax I g`,
  CHEAT_TAC);;

(* HOL4 backendProofScript.sml:3046: the overload
   mk_flat_install_conf, which the port expands *)

(* HOL4 backendProofScript.sml:3048: ML code, not ported *)

let config_wf_abs_conc = prove
 (`opt_eval_config_wf asm_conf c' (SOME ci) ==>
   v_fun_abs dom (compiler_instance_config_v ci)
     (compiler_instance_config_v ci cfg) = (if cfg IN dom then SOME
     cfg else NONE)`,
  CHEAT_TAC);;

(* [local] *)
let cake_orac_extended_wf = prove
 (`backend_compile asm_conf (c:backend_config) prog = SOME (b,bm,c') /\
   opt_eval_config_wf asm_conf c' (SOME ci) ==>
   orac_extended_wf (mk_compiler_fun_from_ci ci)
     ((\(cfg,id',ds). (id',compiler_instance_config_v ci cfg,ds)) o
     cake_orac asm_conf c' syntax I (\ps. (backend_progs_env_id
       ps,backend_progs_source_prog ps)))`,
  CHEAT_TAC);;

(* [local] *)
let cake_orac_eq_get_oracle = prove
 (`~(semantics_prog s env prog ffi_Fail) /\
   opt_eval_config_wf (asm_conf:'a asm_config) (c':backend_config)
     (SOME ci) /\
   nsAll (K concrete_v) (sem_env_v env) /\
     semanticPrimitives_state_refs s = [] /\
     semanticPrimitives_state_eval_state
   s = SOME (mk_init_eval_state ci) /\
   (!i r. get_oracle ci s env prog i = SOME r ==> syntax i = (I ##
     SND) r) /\
   s' = s ==>
   (!i r x. get_oracle ci s' env prog i = SOME r /\
   cake_orac asm_conf c' syntax I (\ps. (backend_progs_env_id
     ps,backend_progs_source_prog ps)) i = x ==>
   (match r with (id',cfg_v,ds) -> (?cfg. cfg_v =
     compiler_instance_config_v ci cfg /\
     x = (cfg,id',ds))))`,
  CHEAT_TAC);;

(* [local] *)
let step_invs_cake_orac = prove
 (`oracle
     st = f o cake_orac asm_conf c' syn I I ==>
     (!x k env_id st decs. x = cake_orac asm_conf c' syn I I k ==>
       f x = (env_id,st,decs) ==>
       decs = backend_progs_source_prog (SND x) /\
       env_id = backend_progs_env_id (SND x) /\
       (?d_st. decf st = SOME d_st /\ FST d_st =
         backend_config_source_conf (FST x))) ==>
     src_orac_step_invs (SOME decf)
       (source_to_source_compile) (SOME (EvalOracle st))`,
  CHEAT_TAC);;

(* [local] *)
let source_to_source_semantics_prog_equiv = prove
 (`~(semantics_prog s0 env prog ffi_Fail) ==>
   semantics_prog s0 env (source_to_source_compile prog) res =
   semantics_prog s0 env prog res`,
  CHEAT_TAC);;

(* [local] *)
let source_to_source_semantics_prog_intro = prove
 (`~(semantics_prog s0 env prog ffi_Fail) ==>
   (~(semantics_prog s0 env (source_to_source_compile prog) ffi_Fail)
     ==>
     semantics_prog s0 env (source_to_source_compile prog) res) ==>
   semantics_prog s0 env prog res`,
  CHEAT_TAC);;

(* [local] *)
let eval_oracle_semantics_prog_intro = prove
 (`!ci. ~(semantics_prog s1 env decs ffi_Fail) /\
   precond_eval_state orac ci s1 env decs /\
     semanticPrimitives_state_refs s1 = [] /\
   nsAll (K concrete_v) (sem_env_v env) /\
   (~(semantics_prog (semanticPrimitives_state_eval_state_fupd (K
     (put_oracle ci orac)) s1) env decs ffi_Fail) ==>
     semantics_prog (semanticPrimitives_state_eval_state_fupd (K
       (put_oracle ci orac)) s1) env decs res) ==>
   semantics_prog s1 env decs res`,
  CHEAT_TAC);;

(* [local] *)
let source_to_source_semantics_prog_oracle_intro = prove
 (`~(semantics_prog (semanticPrimitives_state_eval_state_fupd (K
  (insert_gen_oracle ev I sf orac es)) s0) env prog ffi_Fail) ==>
   (~(semantics_prog (semanticPrimitives_state_eval_state_fupd (K
     (insert_gen_oracle ev source_to_source_compile sf orac es)) s0) env
     prog ffi_Fail) ==>
       semantics_prog (semanticPrimitives_state_eval_state_fupd (K
         (insert_gen_oracle ev source_to_source_compile sf orac es)) s0)
         env prog res) ==>
   semantics_prog (semanticPrimitives_state_eval_state_fupd (K
     (insert_gen_oracle ev I sf orac es)) s0) env prog res`,
  CHEAT_TAC);;

let source_eval_to_flat_semantics = prove
 (`~(semantics_prog (add_eval_state ev s0) env prog ffi_Fail) /\
   backend_compile asm_conf (c:backend_config) prog = SOME (b,bm,c')
     /\
   source_to_flat_compile prim_src_config (source_to_source_compile
     prog) = (src_c',p') /\
   THE (prim_sem_env (ffi:'ffi ffi_state)) = (s0,env) /\
   opt_eval_config_wf asm_conf c' ev /\
     stack_to_lab_config_perf_calls (backend_config_stack_conf
   c) = F /\ backend_config_source_conf
   c = prim_src_config ==>
   (?syntax_oracle.
   semantics_prog (add_eval_state ev s0) env prog (flatSem_semantics
     (flatProps_mk_flat_install_conf
         (backend_from_flat_tuple_cc asm_conf c)
         (cake_orac asm_conf c' syntax_oracle (SND o config_tuple1)
           (\ps. backend_progs_flat_prog ps))) (state_ffi
     s0) p'))`,
  CHEAT_TAC);;

let flat_semantics = prove
 (`let co = cake_orac asm_conf c' syn (SND o config_tuple1) (\ps.
  backend_progs_flat_prog ps) in
   let f_inst = flatProps_mk_flat_install_conf
         (pure_cc inc_compile_decs cc)
         co in ~(flatSem_semantics f_inst ffi ds = ffi_Fail) /\
   0 < clos_to_bvl_config_max_app cconf /\ no_Mat_decs ds ==>
   closSem_semantics ffi (clos_to_bvl_config_max_app cconf) FEMPTY
     (pure_co inc_compile_decs o co) cc (word_to_stack_compile_prog
       ds) =
   flatSem_semantics f_inst ffi ds`,
  CHEAT_TAC);;

let pad_code_no_share_mem_inst = prove
 (`no_share_mem_inst sec_list ==>
   no_share_mem_inst (pad_code nop sec_list)`,
  CHEAT_TAC);;

let enc_sec_list_no_share_mem_inst = prove
 (`no_share_mem_inst code ==>
   no_share_mem_inst (enc_sec_list enc code)`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let enc_secs_again_no_share_mem_inst = prove
 (cake_as_vars (fun () ->
    `!done'.
     enc_secs_again pos labs ffi_names enc sec_list = (code,done')
       /\
     no_share_mem_inst sec_list ==>
     no_share_mem_inst code`),
  CHEAT_TAC);;

let upd_lab_len_no_share_mem_inst = prove
 (`!pos.
   no_share_mem_inst sec_list ==>
   no_share_mem_inst (upd_lab_len pos sec_list)`,
  CHEAT_TAC);;

let remove_labels_loop_no_share_mem_inst = prove
 (`!cl conf pos init_labs ffi_names' sec_list code labs.
   remove_labels_loop cl conf pos init_labs ffi_names' sec_list =
     SOME (code,labs) /\
   no_share_mem_inst sec_list ==>
   no_share_mem_inst code`,
  CHEAT_TAC);;

let compile_lab_IMP_mmio_pcs_min_index = prove
 (`compile_lab asm_conf c sec_list = SOME (bytes,c') /\
   OPTION_ALL (ALL (\x. ?s. x = ffi_ExtCall s)) (ffi_names c) ==>
   (?ffi_names'. ffi_names c' = SOME ffi_names' /\
     (?x. mmio_pcs_min_index ffi_names' = SOME x))`,
  CHEAT_TAC);;

let compile_lab_no_share_mem_IMP_mmio_pcs_min_index = prove
 (`compile_lab asm_conf c sec_list = SOME (bytes,c') /\
   no_share_mem_inst sec_list /\
   OPTION_ALL (ALL (\x. ?s. x = ffi_ExtCall s)) (ffi_names c) ==>
   (?ffi_names'. ffi_names c' = SOME ffi_names' /\
   mmio_pcs_min_index ffi_names' = SOME (LENGTH ffi_names'))`,
  CHEAT_TAC);;

let compile_correct' = prove
 (`backend_compile (asm_conf:'a asm_config) (c:backend_config) prog =
  SOME (bytes,bitmaps,c') ==>
    (let (s0,env) = THE (prim_sem_env (ffi:'ffi ffi_state)) in
    let s = add_eval_state ev s0 in
    ~(semantics_prog s env prog ffi_Fail) /\
    backend_config_ok asm_conf c /\ mc_conf_ok mc /\ mc_init_ok
      asm_conf c mc /\
    opt_eval_config_wf asm_conf c' ev /\
    installed bytes cbspace bitmaps data_sp (ffi_names
      (backend_config_lab_conf c')) (heap_regs
      (stack_to_lab_config_reg_names (backend_config_stack_conf c))) mc
      (lab_to_target_config_shmem_extra (backend_config_lab_conf
       c')) ms ==>
      machine_sem (mc:('a,'b,'c)machine_config) ffi ms SUBSET
        extend_with_resource_limit'
          (backendProof_is_safe_for_space ffi asm_conf c prog
            (backendProof_read_limits asm_conf c mc ms))
          (semantics_prog s env prog))`,
  CHEAT_TAC);;


(* HOL4 backendProofScript.sml:4429-4431: a theorem that HOL4 states
   as the value of an ML expression: compile_correct_no_eval *)

(* compile_correct *)
let backendProof_compile_correct = prove
 (`backend_compile (asm_conf:'a asm_config) (c:backend_config) prog =
  SOME (bytes,bitmaps,c') ==>
    (let (s,env) = THE (prim_sem_env (ffi:'ffi ffi_state)) in
    ~(semantics_prog s env prog ffi_Fail) /\
    backend_config_ok asm_conf c /\ mc_conf_ok mc /\ mc_init_ok
      asm_conf c mc /\
    installed bytes cbspace bitmaps data_sp (ffi_names
      (backend_config_lab_conf c'))
         (heap_regs (stack_to_lab_config_reg_names
           (backend_config_stack_conf c))) mc
           (lab_to_target_config_shmem_extra (backend_config_lab_conf
         c')) ms ==>
      machine_sem (mc:('a,'b,'c)machine_config) ffi ms SUBSET
        extend_with_resource_limit (semantics_prog s env prog))`,
  CHEAT_TAC);;

let semantics_prog_sing = prove
 (`?x. semantics_prog s env prog = {x}`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let compile_correct_is_safe_for_space = prove
 (cake_as_vars (fun () ->
    `backend_compile (asm_conf:'a asm_config) (c:backend_config) prog =
  SOME (bytes,bitmaps,c') ==>
     backendProof_is_safe_for_space ffi asm_conf c prog
       (stack_limit,heap_limit) ==>
     (backendProof_read_limits asm_conf c mc ms) =
       (stack_limit,heap_limit) ==>
     (let (s,env) = THE (prim_sem_env (ffi:'ffi ffi_state)) in
     ~(semantics_prog s env prog ffi_Fail) /\
     backend_config_ok asm_conf c /\ mc_conf_ok mc /\ mc_init_ok
       asm_conf c mc /\
     installed bytes cbspace bitmaps data_sp
       (lab_to_target_config_ffi_names (backend_config_lab_conf c'))
          (heap_regs (stack_to_lab_config_reg_names
            (backend_config_stack_conf c))) mc
            (lab_to_target_config_shmem_extra (backend_config_lab_conf
          c')) ms ==>
     machine_sem (mc:('a,'b,'c)machine_config) ffi ms =
     semantics_prog s env prog)`),
  CHEAT_TAC);;

let the_EvalDecs_def = define_general
  [`the_EvalDecs (EvalDecs x) = x`];;

let compile_correct_eval = prove
 (`backend_compile asm_conf c prog = SOME (bytes,bitmaps,c') ==>
    (let (s0,env) = THE (prim_sem_env (ffi:'ffi ffi_state)) in
    ~(semantics_prog (add_eval_state ev s0) env prog ffi_Fail) /\
      backend_config_ok asm_conf c /\
    mc_conf_ok mc /\ mc_init_ok asm_conf c mc /\ opt_eval_config_wf
      asm_conf c' ev /\
    installed bytes cbspace bitmaps data_sp (ffi_names
      (backend_config_lab_conf c'))
      (heap_regs (stack_to_lab_config_reg_names
        (backend_config_stack_conf c))) mc
        (lab_to_target_config_shmem_extra (backend_config_lab_conf
      c')) ms ==>
    machine_sem mc ffi ms SUBSET
      extend_with_resource_limit
        (semantics_prog (add_eval_state ev s0) env prog))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["done"];;

(* and the interface *)
let _ = unhide_overloads ();;
