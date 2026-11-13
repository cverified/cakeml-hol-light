"""how each definition of the port was made

A definition of a source goes through cake_define, which tries one
strategy after another, because no single primitive of HOL Light
takes what HOL4 writes.  Searching for the way again on every load
is both slow and silent about what came out, so a run harvests
what worked and the files say it themselves.

WAY holds it, as (theory, constant) -> (strategy, assumed,
relation): the strategy that made the definition, whether its
termination condition was assumed rather than proved, and the
relation it was made with ('' where there was none).

PRIMITIVE is the constants where the strategy is HOL Light's own
new_definition, which is the common case.

tools/bin/strategies harvests both from a run (cake_strategies).
"""

WAY = {
  ('ASCIInumbers', 'HEX'):
    ('new_definition', False, ''),
  ('ASCIInumbers', 'UNHEX'):
    ('new_definition', False, ''),
  ('ASCIInumbers', 'n2s'):
    ('new_definition', False, ''),
  ('ASCIInumbers', 'num_from_dec_string'):
    ('new_definition', False, ''),
  ('ASCIInumbers', 'num_from_hex_string'):
    ('new_definition', False, ''),
  ('ASCIInumbers', 'num_to_dec_string'):
    ('new_definition', False, ''),
  ('ASCIInumbers', 'num_to_hex_string'):
    ('new_definition', False, ''),
  ('ASCIInumbers', 's2n'):
    ('new_definition', False, ''),
  ('NTproperties', 'firstSet'):
    ('new_definition', False, ''),
  ('NTproperties', 'firstSetML'):
    ('measure', True, ''),
  ('NTproperties', 'nullable'):
    ('new_definition', False, ''),
  ('NTproperties', 'nullableML'):
    ('measure', True, ''),
  ('ag32_config', 'ag32_backend_config'):
    ('new_definition', False, ''),
  ('ag32_config', 'ag32_names'):
    ('new_definition', False, ''),
  ('alignment', 'align'):
    ('new_definition', False, ''),
  ('alignment', 'alignment_aligned'):
    ('new_definition', False, ''),
  ('alignment', 'byte_align'):
    ('new_definition', False, ''),
  ('alignment', 'byte_aligned'):
    ('new_definition', False, ''),
  ('arm7_config', 'arm7_backend_config'):
    ('new_definition', False, ''),
  ('arm7_config', 'arm7_names'):
    ('new_definition', False, ''),
  ('arm8_config', 'arm8_backend_config'):
    ('new_definition', False, ''),
  ('arm8_config', 'arm8_names'):
    ('new_definition', False, ''),
  ('asm', 'arith_ok'):
    ('new_recursive_definition', False, ''),
  ('asm', 'asm_offset_ok'):
    ('new_definition', False, ''),
  ('asm', 'asm_ok'):
    ('new_recursive_definition', False, ''),
  ('asm', 'asm_word_cmp'):
    ('new_recursive_definition', False, ''),
  ('asm', 'cmp_ok'):
    ('new_definition', False, ''),
  ('asm', 'fp_ok'):
    ('new_recursive_definition', False, ''),
  ('asm', 'fp_reg_ok'):
    ('new_definition', False, ''),
  ('asm', 'inst_ok'):
    ('new_definition', False, ''),
  ('asm', 'is_load'):
    ('new_definition', False, ''),
  ('asm', 'reg_imm_ok'):
    ('new_recursive_definition', False, ''),
  ('asm', 'reg_ok'):
    ('new_definition', False, ''),
  ('asmProps', 'all_pcs'):
    ('measure', True, ''),
  ('asmProps', 'asserts'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4). (\\n. n) x0)'),
  ('asmProps', 'asserts2'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4). (\\n. n) x0)'),
  ('asmProps', 'enc_ok'):
    ('new_definition', False, ''),
  ('asmProps', 'encoder_correct'):
    ('new_definition', False, ''),
  ('asmProps', 'interference_ok'):
    ('new_definition', False, ''),
  ('asmProps', 'offset_monotonic'):
    ('new_definition', False, ''),
  ('asmProps', 'target_ok'):
    ('new_definition', False, ''),
  ('asmProps', 'target_state_rel'):
    ('new_definition', False, ''),
  ('asmSem', 'asmSem_addr'):
    ('define_single', False, ''),
  ('asmSem', 'asmSem_arith_upd'):
    ('new_recursive_definition', False, ''),
  ('asmSem', 'asmSem_asm'):
    ('new_recursive_definition', False, ''),
  ('asmSem', 'asmSem_assert'):
    ('new_definition', False, ''),
  ('asmSem', 'asmSem_binop_upd'):
    ('define_single', False, ''),
  ('asmSem', 'asmSem_fp_upd'):
    ('new_recursive_definition', False, ''),
  ('asmSem', 'asmSem_inst'):
    ('new_recursive_definition', False, ''),
  ('asmSem', 'asmSem_mem_load'):
    ('new_definition', False, ''),
  ('asmSem', 'asmSem_mem_op'):
    ('define_single', False, ''),
  ('asmSem', 'asmSem_mem_store'):
    ('new_definition', False, ''),
  ('asmSem', 'asmSem_read_fp_reg'):
    ('new_definition', False, ''),
  ('asmSem', 'asmSem_read_mem'):
    ('new_definition', False, ''),
  ('asmSem', 'asmSem_read_reg'):
    ('new_definition', False, ''),
  ('asmSem', 'asmSem_reg_imm'):
    ('new_recursive_definition', False, ''),
  ('asmSem', 'asmSem_upd_fp_reg'):
    ('new_definition', False, ''),
  ('asmSem', 'asmSem_upd_mem'):
    ('new_definition', False, ''),
  ('asmSem', 'asmSem_upd_pc'):
    ('new_definition', False, ''),
  ('asmSem', 'asmSem_upd_reg'):
    ('new_definition', False, ''),
  ('asmSem', 'asmSem_word_shift'):
    ('new_recursive_definition', False, ''),
  ('asmSem', 'asm_step'):
    ('new_definition', False, ''),
  ('asmSem', 'is_test'):
    ('new_definition', False, ''),
  ('asmSem', 'jump_to_offset'):
    ('new_definition', False, ''),
  ('asmSem', 'read_mem_word'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x1)'),
  ('asmSem', 'write_mem_word'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). (\\n. n) x1)'),
  ('ast', 'Apps'):
    ('prim_rec', False, ''),
  ('ast', 'Funs'):
    ('prim_rec', False, ''),
  ('ast', 'ast_Seqs'):
    ('prim_rec', False, ''),
  ('ast', 'ast_pat_bindings'):
    ('prim_rec', False, ''),
  ('ast', 'every_exp'):
    ('nested', False, ''),
  ('ast', 'getOpClass'):
    ('new_definition', False, ''),
  ('backend', 'attach_bitmaps'):
    ('new_recursive_definition', False, ''),
  ('backend', 'backend_compile'):
    ('new_definition', False, ''),
  ('backend', 'compile_inc_progs'):
    ('new_definition', False, ''),
  ('backend', 'compile_inc_progs_for_eval'):
    ('new_definition', False, ''),
  ('backend', 'empty_progs'):
    ('new_definition', False, ''),
  ('backend', 'ensure_fp_conf_ok'):
    ('new_definition', False, ''),
  ('backend', 'ffinames_to_string_list'):
    ('measure', False, 'MEASURE (\\x0. list_size ffiname_size x0)'),
  ('backend', 'from_bvi'):
    ('new_definition', False, ''),
  ('backend', 'from_bvl'):
    ('new_definition', False, ''),
  ('backend', 'from_clos'):
    ('new_definition', False, ''),
  ('backend', 'from_data'):
    ('new_definition', False, ''),
  ('backend', 'from_flat'):
    ('new_definition', False, ''),
  ('backend', 'from_lab'):
    ('new_definition', False, ''),
  ('backend', 'from_livesets'):
    ('new_definition', False, ''),
  ('backend', 'from_source'):
    ('new_definition', False, ''),
  ('backend', 'from_stack'):
    ('new_definition', False, ''),
  ('backend', 'from_word'):
    ('new_definition', False, ''),
  ('backend', 'from_word_0'):
    ('new_definition', False, ''),
  ('backend', 'keep_progs'):
    ('new_definition', False, ''),
  ('backend', 'prim_config'):
    ('new_definition', False, ''),
  ('backend', 'prim_src_config'):
    ('new_definition', False, ''),
  ('backend', 'set_oracle'):
    ('new_definition', False, ''),
  ('backend', 'to_bvi'):
    ('new_definition', False, ''),
  ('backend', 'to_bvl'):
    ('new_definition', False, ''),
  ('backend', 'to_clos'):
    ('new_definition', False, ''),
  ('backend', 'to_data'):
    ('new_definition', False, ''),
  ('backend', 'to_flat'):
    ('new_definition', False, ''),
  ('backend', 'to_lab'):
    ('new_definition', False, ''),
  ('backend', 'to_livesets'):
    ('new_definition', False, ''),
  ('backend', 'to_livesets_0'):
    ('new_definition', False, ''),
  ('backend', 'to_stack'):
    ('new_definition', False, ''),
  ('backend', 'to_target'):
    ('new_definition', False, ''),
  ('backend', 'to_word'):
    ('new_definition', False, ''),
  ('backend', 'to_word_0'):
    ('new_definition', False, ''),
  ('backendProof', 'add_eval_state'):
    ('new_recursive_definition', False, ''),
  ('backendProof', 'backendProof_is_safe_for_space'):
    ('new_definition', False, ''),
  ('backendProof', 'backendProof_read_limits'):
    ('new_definition', False, ''),
  ('backendProof', 'backend_config_ok'):
    ('new_definition', False, ''),
  ('backendProof', 'backend_from_data_tuple_cc'):
    ('new_definition', False, ''),
  ('backendProof', 'backend_from_flat_tuple_cc'):
    ('new_definition', False, ''),
  ('backendProof', 'cake_configs'):
    ('new_definition', False, ''),
  ('backendProof', 'cake_orac'):
    ('new_definition', False, ''),
  ('backendProof', 'compute_stack_frame_sizes'):
    ('new_definition', False, ''),
  ('backendProof', 'config_tuple1'):
    ('new_definition', False, ''),
  ('backendProof', 'config_tuple2'):
    ('new_definition', False, ''),
  ('backendProof', 'heap_regs'):
    ('new_definition', False, ''),
  ('backendProof', 'is_64_bits'):
    ('new_definition', False, ''),
  ('backendProof', 'mc_init_ok'):
    ('new_definition', False, ''),
  ('backendProof', 'opt_eval_config_wf'):
    ('new_recursive_definition', False, ''),
  ('backendProof', 'state_co_fun'):
    ('new_definition', False, ''),
  ('backendProof', 'the_EvalDecs'):
    ('define_single', False, ''),
  ('backendProps', 'add_state_co'):
    ('new_definition', False, ''),
  ('backendProps', 'is_state_oracle'):
    ('new_definition', False, ''),
  ('backendProps', 'option_le'):
    ('new_definition', False, ''),
  ('backendProps', 'oracle_monotonic'):
    ('new_definition', False, ''),
  ('backendProps', 'pure_cc'):
    ('new_definition', False, ''),
  ('backendProps', 'pure_co'):
    ('new_definition', False, ''),
  ('backendProps', 'pure_co_progs'):
    ('new_definition', False, ''),
  ('backendProps', 'restrict_nonzero'):
    ('new_definition', False, ''),
  ('backendProps', 'restrict_zero'):
    ('new_definition', False, ''),
  ('backendProps', 'state_cc'):
    ('new_definition', False, ''),
  ('backendProps', 'state_co'):
    ('new_definition', False, ''),
  ('backendProps', 'state_co_progs'):
    ('new_definition', False, ''),
  ('backendProps', 'state_orac_states'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). (\\n. n) x3)'),
  ('backendProps', 'syntax_to_full_oracle'):
    ('new_definition', False, ''),
  ('backend_common', 'backend_common_word_shift'):
    ('new_definition', False, ''),
  ('backend_common', 'bind_tag'):
    ('new_definition', False, ''),
  ('backend_common', 'bool_to_tag'):
    ('new_definition', False, ''),
  ('backend_common', 'bvl_num_stubs'):
    ('new_definition', False, ''),
  ('backend_common', 'bvl_to_bvi_namespaces'):
    ('new_definition', False, ''),
  ('backend_common', 'chr_tag'):
    ('new_definition', False, ''),
  ('backend_common', 'clos_tag_shift'):
    ('new_definition', False, ''),
  ('backend_common', 'closure_tag'):
    ('new_definition', False, ''),
  ('backend_common', 'cons_tag'):
    ('new_definition', False, ''),
  ('backend_common', 'data_num_stubs'):
    ('new_definition', False, ''),
  ('backend_common', 'div_tag'):
    ('new_definition', False, ''),
  ('backend_common', 'false_tag'):
    ('new_definition', False, ''),
  ('backend_common', 'list_delete'):
    ('prim_rec', False, ''),
  ('backend_common', 'mk_cons'):
    ('new_definition', False, ''),
  ('backend_common', 'mk_union'):
    ('new_definition', False, ''),
  ('backend_common', 'nil_tag'):
    ('new_definition', False, ''),
  ('backend_common', 'none_tag'):
    ('new_definition', False, ''),
  ('backend_common', 'orphan_trace'):
    ('new_definition', False, ''),
  ('backend_common', 'partial_app_tag'):
    ('new_definition', False, ''),
  ('backend_common', 'small_enough_int'):
    ('new_definition', False, ''),
  ('backend_common', 'some_tag'):
    ('new_definition', False, ''),
  ('backend_common', 'stack_num_stubs'):
    ('new_definition', False, ''),
  ('backend_common', 'subscript_tag'):
    ('new_definition', False, ''),
  ('backend_common', 'true_tag'):
    ('new_definition', False, ''),
  ('backend_common', 'tuple_tag'):
    ('new_definition', False, ''),
  ('backend_common', 'upper_w2w'):
    ('new_definition', False, ''),
  ('backend_common', 'word_add_carry'):
    ('new_definition', False, ''),
  ('backend_common', 'word_num_stubs'):
    ('new_definition', False, ''),
  ('backend_passes', 'any_prog_pp'):
    ('new_definition', False, ''),
  ('backend_passes', 'compile_tap'):
    ('new_definition', False, ''),
  ('backend_passes', 'from_data_all'):
    ('new_definition', False, ''),
  ('backend_passes', 'from_lab_all'):
    ('new_definition', False, ''),
  ('backend_passes', 'from_stack_all'):
    ('new_definition', False, ''),
  ('backend_passes', 'from_word_0_all'):
    ('new_definition', False, ''),
  ('backend_passes', 'from_word_all'):
    ('new_definition', False, ''),
  ('backend_passes', 'pp_with_title'):
    ('new_definition', False, ''),
  ('backend_passes', 'to_bvi_all'):
    ('new_definition', False, ''),
  ('backend_passes', 'to_bvl_all'):
    ('new_definition', False, ''),
  ('backend_passes', 'to_clos_all'):
    ('new_definition', False, ''),
  ('backend_passes', 'to_data_all'):
    ('new_definition', False, ''),
  ('backend_passes', 'to_flat_all'):
    ('new_definition', False, ''),
  ('backend_passes', 'to_lab_all'):
    ('new_definition', False, ''),
  ('backend_passes', 'to_stack_all'):
    ('new_definition', False, ''),
  ('backend_passes', 'to_target_all'):
    ('new_definition', False, ''),
  ('backend_passes', 'to_word_all'):
    ('new_definition', False, ''),
  ('backend_passes', 'word_internal_all'):
    ('new_definition', False, ''),
  ('balanced_map', 'balanceL'):
    ('new_definition', False, ''),
  ('balanced_map', 'balanceR'):
    ('new_definition', False, ''),
  ('balanced_map', 'balanced'):
    ('new_definition', False, ''),
  ('balanced_map', 'balanced_map_compare'):
    ('new_definition', False, ''),
  ('balanced_map', 'balanced_map_delete'):
    ('prim_rec', False, ''),
  ('balanced_map', 'balanced_map_empty'):
    ('new_definition', False, ''),
  ('balanced_map', 'balanced_map_exists'):
    ('prim_rec', False, ''),
  ('balanced_map', 'balanced_map_insert'):
    ('prim_rec', False, ''),
  ('balanced_map', 'balanced_map_invariant'):
    ('prim_rec', False, ''),
  ('balanced_map', 'balanced_map_lookup'):
    ('prim_rec', False, ''),
  ('balanced_map', 'balanced_map_map'):
    ('new_definition', False, ''),
  ('balanced_map', 'balanced_map_size'):
    ('new_recursive_definition', False, ''),
  ('balanced_map', 'balanced_map_union'):
    ('new_definition', False, ''),
  ('balanced_map', 'bin'):
    ('new_definition', False, ''),
  ('balanced_map', 'deleteFindMax'):
    ('measure', False, 'MEASURE (\\x0. balanced_map_size1 (\\x. 0) (\\x. 0) x0)'),
  ('balanced_map', 'deleteFindMin'):
    ('measure', False, 'MEASURE (\\x0. balanced_map_size1 (\\x. 0) (\\x. 0) x0)'),
  ('balanced_map', 'delta'):
    ('new_definition', False, ''),
  ('balanced_map', 'filterGt'):
    ('new_recursive_definition', False, ''),
  ('balanced_map', 'filterGt_help'):
    ('prim_rec', False, ''),
  ('balanced_map', 'filterLt'):
    ('new_recursive_definition', False, ''),
  ('balanced_map', 'filterLt_help'):
    ('prim_rec', False, ''),
  ('balanced_map', 'foldrWithKey'):
    ('prim_rec', False, ''),
  ('balanced_map', 'glue'):
    ('new_definition', False, ''),
  ('balanced_map', 'hedgeUnion'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4). balanced_map_size1 (\\x. 0) (\\x. 0) x3)'),
  ('balanced_map', 'insertMax'):
    ('prim_rec', False, ''),
  ('balanced_map', 'insertMin'):
    ('prim_rec', False, ''),
  ('balanced_map', 'insertR'):
    ('prim_rec', False, ''),
  ('balanced_map', 'key_ordered'):
    ('prim_rec', False, ''),
  ('balanced_map', 'key_set'):
    ('new_definition', False, ''),
  ('balanced_map', 'link'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3).      balanced_map_size1 (\\x. 0) (\\x. 0) x2 +      balanced_map_size1 (\\x. 0) (\\x. 0) x3)'),
  ('balanced_map', 'mapWithKey'):
    ('prim_rec', False, ''),
  ('balanced_map', 'ratio'):
    ('new_definition', False, ''),
  ('balanced_map', 'singleton'):
    ('new_definition', False, ''),
  ('balanced_map', 'structure_size'):
    ('prim_rec', False, ''),
  ('balanced_map', 'toAscList'):
    ('new_definition', False, ''),
  ('balanced_map', 'to_fmap'):
    ('prim_rec', False, ''),
  ('balanced_map', 'trim'):
    ('new_definition', False, ''),
  ('balanced_map', 'trim_help_greater'):
    ('prim_rec', False, ''),
  ('balanced_map', 'trim_help_lesser'):
    ('prim_rec', False, ''),
  ('balanced_map', 'trim_help_middle'):
    ('prim_rec', False, ''),
  ('binary_ieee', 'check_for_signalling'):
    ('new_definition', False, ''),
  ('binary_ieee', 'clear_flags'):
    ('new_definition', False, ''),
  ('binary_ieee', 'closest'):
    ('new_definition', False, ''),
  ('binary_ieee', 'closest_such'):
    ('new_definition', False, ''),
  ('binary_ieee', 'dividezero_flags'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_abs'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_add'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_bottom'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_compare'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_div'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_equal'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_greater_equal'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_greater_than'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_is_finite'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_is_infinite'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_is_nan'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_is_signalling'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_is_zero'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_less_equal'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_less_than'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_minus_infinity'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_minus_zero'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_mul'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_mul_add'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_negate'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_plus_infinity'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_plus_zero'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_round'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_round_with_flags'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_some_qnan'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_sqrt'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_sub'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_to_int'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_to_real'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_top'):
    ('new_definition', False, ''),
  ('binary_ieee', 'float_value'):
    ('new_definition', False, ''),
  ('binary_ieee', 'invalidop_flags'):
    ('new_definition', False, ''),
  ('binary_ieee', 'is_closest'):
    ('new_definition', False, ''),
  ('binary_ieee', 'largest'):
    ('new_definition', False, ''),
  ('binary_ieee', 'real_to_float'):
    ('new_definition', False, ''),
  ('binary_ieee', 'round'):
    ('new_definition', False, ''),
  ('binary_ieee', 'threshold'):
    ('new_definition', False, ''),
  ('bitstring', 'add'):
    ('new_definition', False, ''),
  ('bitstring', 'bitify'):
    ('guess', False, ''),
  ('bitstring', 'boolify'):
    ('prim_rec', False, ''),
  ('bitstring', 'field'):
    ('new_definition', False, ''),
  ('bitstring', 'fixwidth'):
    ('new_definition', False, ''),
  ('bitstring', 'n2v'):
    ('new_definition', False, ''),
  ('bitstring', 'shiftr'):
    ('new_definition', False, ''),
  ('bitstring', 'testbit'):
    ('new_definition', False, ''),
  ('bitstring', 'v2n'):
    ('new_definition', False, ''),
  ('bitstring', 'zero_extend'):
    ('new_definition', False, ''),
  ('bviProps', 'adj_orac'):
    ('new_definition', False, ''),
  ('bviProps', 'adj_orac_ok'):
    ('new_definition', False, ''),
  ('bviProps', 'bviProps_adj_orac_rel'):
    ('new_definition', False, ''),
  ('bviProps', 'bviProps_get_code_labels'):
    ('measure', False, ''),
  ('bviProps', 'bviProps_good_code_labels'):
    ('new_definition', False, ''),
  ('bviProps', 'bviProps_inc_clock'):
    ('new_definition', False, ''),
  ('bviSem', 'bviSem_dec_clock'):
    ('new_definition', False, ''),
  ('bviSem', 'bviSem_dest_thunk'):
    ('new_definition', False, ''),
  ('bviSem', 'bviSem_do_app'):
    ('new_definition', False, ''),
  ('bviSem', 'bviSem_do_app_aux'):
    ('new_definition', False, ''),
  ('bviSem', 'bviSem_do_install'):
    ('new_definition', False, ''),
  ('bviSem', 'bviSem_evaluate'):
    ('measure', False, ''),
  ('bviSem', 'bviSem_finalise_cons'):
    ('measure', True, ''),
  ('bviSem', 'bviSem_fix_clock'):
    ('new_definition', False, ''),
  ('bviSem', 'bviSem_initial_state'):
    ('new_definition', False, ''),
  ('bviSem', 'bviSem_semantics'):
    ('new_definition', False, ''),
  ('bviSem', 'bvi_to_bvl'):
    ('new_definition', False, ''),
  ('bviSem', 'bvl_to_bvi'):
    ('new_definition', False, ''),
  ('bvi_inline', 'bvi_inline_compile_inc'):
    ('new_definition', False, ''),
  ('bvi_inline', 'bvi_inline_compile_prog'):
    ('new_definition', False, ''),
  ('bvi_inline', 'bvi_mk_tick'):
    ('new_definition', False, ''),
  ('bvi_inline', 'canonical_wrapper'):
    ('new_definition', False, ''),
  ('bvi_inline', 'inline_all'):
    ('prim_rec', False, ''),
  ('bvi_inline', 'inline_exp'):
    ('measure', False, ''),
  ('bvi_inline', 'remove_ticks_exp'):
    ('measure', False, 'MEASURE (\\x0. bvi_exp_size x0)'),
  ('bvi_inline', 'wrapper_ok'):
    ('new_definition', False, ''),
  ('bvi_inlineProof', 'bvi_inlineProof_in_cc'):
    ('new_definition', False, ''),
  ('bvi_inlineProof', 'bvi_inlineProof_in_co'):
    ('new_definition', False, ''),
  ('bvi_inlineProof', 'bvi_inlineProof_in_state_rel'):
    ('new_definition', False, ''),
  ('bvi_inlineProof', 'bvi_inlineProof_remove_ticks_cc'):
    ('new_definition', False, ''),
  ('bvi_inlineProof', 'bvi_inlineProof_remove_ticks_co'):
    ('new_definition', False, ''),
  ('bvi_inlineProof', 'cache_code_labels'):
    ('new_definition', False, ''),
  ('bvi_inlineProof', 'clean_prog'):
    ('new_definition', False, ''),
  ('bvi_inlineProof', 'remove_state_rel'):
    ('new_definition', False, ''),
  ('bvi_let', 'bvi_let_compile_exp'):
    ('new_definition', False, ''),
  ('bvi_let', 'bvi_let_compile_sing'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). bvi_exp_size x2)'),
  ('bvi_let', 'bvi_let_delete_var'):
    ('new_definition', False, ''),
  ('bvi_let', 'bvi_let_extract'):
    ('new_definition', False, ''),
  ('bvi_let', 'bvi_let_extract_list'):
    ('prim_rec', False, ''),
  ('bvi_letProof', 'bvi_letProof_env_rel'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). list_size (\\n. n) x0)'),
  ('bvi_letProof', 'bvi_letProof_v_rel'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'LAST1'):
    ('guess', False, ''),
  ('bvi_tailrec', 'apply_op'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'arg_ty'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'args_from'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'bvi_tailrec_compile_each'):
    ('prim_rec', False, ''),
  ('bvi_tailrec', 'bvi_tailrec_compile_exp'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'bvi_tailrec_compile_prog'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'bvi_tailrec_is_const'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'bvi_tailrec_is_rec'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'check_exp'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'check_op'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'decide_ty'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'dummy'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'from_op'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'get_bin_args'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'has_rec'):
    ('measure', True, ''),
  ('bvi_tailrec', 'has_rec1'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'has_rec_sing'):
    ('prim_rec', False, ''),
  ('bvi_tailrec', 'id_from_op'):
    ('new_recursive_definition', False, ''),
  ('bvi_tailrec', 'index_of'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'is_arith'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'is_rel'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'let_wrap'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'mk_aux_call'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'op_eq'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'op_ty'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'op_type'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'opbinargs'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'push_call'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'rewrite'):
    ('match', False, ''),
  ('bvi_tailrec', 'scan_expr'):
    ('measure', False, ''),
  ('bvi_tailrec', 'scan_expr_sing'):
    ('prim_rec', False, ''),
  ('bvi_tailrec', 'term_ok'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'term_ok_any'):
    ('measure', False, 'MEASURE (bvi_exp_size o SND o SND)'),
  ('bvi_tailrec', 'term_ok_int'):
    ('measure', False, 'MEASURE (bvi_exp_size o SND)'),
  ('bvi_tailrec', 'to_op'):
    ('new_recursive_definition', False, ''),
  ('bvi_tailrec', 'try_swap'):
    ('new_definition', False, ''),
  ('bvi_tailrec', 'try_update'):
    ('new_recursive_definition', False, ''),
  ('bvi_tailrec', 'update_context'):
    ('new_definition', False, ''),
  ('bvi_tailrecProof', 'bvi_tailrecProof_code_rel'):
    ('new_definition', False, ''),
  ('bvi_tailrecProof', 'bvi_tailrecProof_env_rel'):
    ('new_definition', False, ''),
  ('bvi_tailrecProof', 'bvi_tailrecProof_free_names'):
    ('new_definition', False, ''),
  ('bvi_tailrecProof', 'bvi_tailrecProof_input_condition'):
    ('new_definition', False, ''),
  ('bvi_tailrecProof', 'bvi_tailrecProof_namespace_rel'):
    ('new_definition', False, ''),
  ('bvi_tailrecProof', 'bvi_tailrecProof_state_rel'):
    ('new_definition', False, ''),
  ('bvi_tailrecProof', 'op_id_val'):
    ('new_recursive_definition', False, ''),
  ('bvi_tailrecProof', 'optimized_code'):
    ('new_definition', False, ''),
  ('bvi_tailrecProof', 'ty_rel'):
    ('new_definition', False, ''),
  ('bvi_tmc', 'bvi_tmc_bind'):
    ('prim_rec', False, ''),
  ('bvi_tmc', 'bvi_tmc_compile_each'):
    ('prim_rec', False, ''),
  ('bvi_tmc', 'bvi_tmc_compile_exp'):
    ('new_definition', False, ''),
  ('bvi_tmc', 'bvi_tmc_compile_prog'):
    ('new_definition', False, ''),
  ('bvi_tmc', 'bvi_tmc_dest_Cons'):
    ('new_definition', False, ''),
  ('bvi_tmc', 'bvi_tmc_finalise_cons'):
    ('new_definition', False, ''),
  ('bvi_tmc', 'bvi_tmc_pure_op'):
    ('new_definition', False, ''),
  ('bvi_tmc', 'bvi_to_cb'):
    ('new_definition', False, ''),
  ('bvi_tmc', 'bvi_to_cb_aux_sing'):
    ('measure', False, ''),
  ('bvi_tmc', 'call_to_cb'):
    ('new_definition', False, ''),
  ('bvi_tmc', 'cb_size'):
    ('match', False, ''),
  ('bvi_tmc', 'cb_to_bvi'):
    ('prim_rec', False, ''),
  ('bvi_tmc', 'cb_to_bvi_worker'):
    ('new_recursive_definition', False, ''),
  ('bvi_tmc', 'cb_to_bvi_worker_aux'):
    ('measure', True, ''),
  ('bvi_tmc', 'cb_to_bvi_worker_aux_alt'):
    ('prim_rec', False, ''),
  ('bvi_tmc', 'cb_to_bvi_wrapper'):
    ('new_definition', False, ''),
  ('bvi_tmc', 'fill_hole'):
    ('new_definition', False, ''),
  ('bvi_tmc', 'mut_cons'):
    ('new_definition', False, ''),
  ('bvi_tmc', 'optimise_call'):
    ('new_definition', False, ''),
  ('bvi_tmc', 'pure_exp'):
    ('prim_rec', False, ''),
  ('bvi_tmc', 'rewrite_worker'):
    ('match', False, ''),
  ('bvi_tmc', 'rewrite_wrapper'):
    ('match', False, ''),
  ('bvi_tmc', 'shift_cb'):
    ('prim_rec', False, ''),
  ('bvi_tmc', 'shift_vars'):
    ('prim_rec', False, ''),
  ('bvi_tmc', 'update_cons'):
    ('new_definition', False, ''),
  ('bvi_tmc', 'wf_cb'):
    ('prim_rec', False, ''),
  ('bvi_tmc', 'wf_vars'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'alloc_hole_has_val'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'bvi_tmcProof_code_rel'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'bvi_tmcProof_env_rel'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'bvi_tmcProof_free_names'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'bvi_tmcProof_input_condition'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'bvi_tmcProof_namespace_rel'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'bvi_tmcProof_state_rel'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'dest_thunk_ret_rel'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'eor_rel'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'fmap_inj'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'hole_has_val'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'hole_not_finalised'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'holes_still_not_finalised'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'holes_unchanged_except'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'hypothesis'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'is_block_op_cons'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'mb_rel'):
    ('measure', True, ''),
  ('bvi_tmcProof', 'no_mutcons'):
    ('measure', False, 'MEASURE bvi_exp_size'),
  ('bvi_tmcProof', 'no_mutcons_op'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'only_fresh'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'opt_res_rel'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'optimised_code'):
    ('new_definition', False, ''),
  ('bvi_tmcProof', 'state_ref_rel'):
    ('new_definition', False, ''),
  ('bvi_to_data', 'bvi_to_data_compile'):
    ('measure', False, ''),
  ('bvi_to_data', 'bvi_to_data_compile_exp'):
    ('new_definition', False, ''),
  ('bvi_to_data', 'bvi_to_data_compile_part'):
    ('new_definition', False, ''),
  ('bvi_to_data', 'bvi_to_data_compile_prog'):
    ('new_definition', False, ''),
  ('bvi_to_data', 'bvi_to_data_compile_sing'):
    ('measure', False, ''),
  ('bvi_to_data', 'bvi_to_data_optimise'):
    ('new_definition', False, ''),
  ('bvi_to_data', 'iAssign'):
    ('new_definition', False, ''),
  ('bvi_to_dataProof', 'bvi_to_dataProof_code_rel'):
    ('new_definition', False, ''),
  ('bvi_to_dataProof', 'bvi_to_dataProof_state_rel'):
    ('new_definition', False, ''),
  ('bvi_to_dataProof', 'data_to_bvi_ref'):
    ('new_recursive_definition', False, ''),
  ('bvi_to_dataProof', 'data_to_bvi_result'):
    ('new_definition', False, ''),
  ('bvi_to_dataProof', 'data_to_bvi_v'):
    ('nested', False, ''),
  ('bvl', 'bvl_Bool'):
    ('new_definition', False, ''),
  ('bvl', 'mk_tick'):
    ('new_definition', False, ''),
  ('bvlProps', 'bEvery'):
    ('measure', False, 'MEASURE (list_size bvl_exp_size o SND)'),
  ('bvlProps', 'bVarBound'):
    ('measure', False, 'MEASURE (list_size bvl_exp_size o SND)'),
  ('bvlProps', 'bvlProps_get_code_labels'):
    ('measure', False, 'MEASURE (\\x0. bvl_exp_size x0)'),
  ('bvlProps', 'bvlProps_get_vars'):
    ('prim_rec', False, ''),
  ('bvlProps', 'bvlProps_inc_clock'):
    ('new_definition', False, ''),
  ('bvlProps', 'destVar'):
    ('define_single', False, ''),
  ('bvlProps', 'isVar'):
    ('new_definition', False, ''),
  ('bvlSem', 'bvlSem_Boolv'):
    ('new_definition', False, ''),
  ('bvlSem', 'bvlSem_Unit'):
    ('new_definition', False, ''),
  ('bvlSem', 'bvlSem_bad_thunk_update'):
    ('new_definition', False, ''),
  ('bvlSem', 'bvlSem_dec_clock'):
    ('new_definition', False, ''),
  ('bvlSem', 'bvlSem_dest_thunk'):
    ('new_definition', False, ''),
  ('bvlSem', 'bvlSem_do_app'):
    ('new_definition', False, ''),
  ('bvlSem', 'bvlSem_do_build'):
    ('prim_rec', False, ''),
  ('bvlSem', 'bvlSem_do_build_const'):
    ('new_definition', False, ''),
  ('bvlSem', 'bvlSem_do_eq'):
    ('measure', False, 'MEASURE (sum_measure (\\(x0,x1,x2). (\\x. 0) x0 + bvlSem_v_size x1 + bvlSem_v_size x2) (\\(x0,x1,x2). (\\x. 0) x0 + bvlSem_v_size1 x1 + bvlSem_v_size1 x2))'),
  ('bvlSem', 'bvlSem_do_install'):
    ('new_definition', False, ''),
  ('bvlSem', 'bvlSem_do_int_app'):
    ('new_definition', False, ''),
  ('bvlSem', 'bvlSem_do_part'):
    ('new_recursive_definition', False, ''),
  ('bvlSem', 'bvlSem_do_word_app'):
    ('new_definition', False, ''),
  ('bvlSem', 'bvlSem_evaluate'):
    ('measure', False, ''),
  ('bvlSem', 'bvlSem_find_code'):
    ('new_recursive_definition', False, ''),
  ('bvlSem', 'bvlSem_fix_clock'):
    ('new_definition', False, ''),
  ('bvlSem', 'bvlSem_initial_state'):
    ('new_definition', False, ''),
  ('bvlSem', 'bvlSem_isClos'):
    ('new_definition', False, ''),
  ('bvlSem', 'bvlSem_list_to_v'):
    ('prim_rec', False, ''),
  ('bvlSem', 'bvlSem_semantics'):
    ('new_definition', False, ''),
  ('bvlSem', 'bvlSem_v_to_bytes'):
    ('new_definition', False, ''),
  ('bvlSem', 'bvlSem_v_to_list'):
    ('measure', False, 'MEASURE (\\x0. bvlSem_v_size x0)'),
  ('bvlSem', 'bvlSem_v_to_words'):
    ('new_definition', False, ''),
  ('bvl_const', 'SmartOp1'):
    ('new_definition', False, ''),
  ('bvl_const', 'SmartOp2'):
    ('new_definition', False, ''),
  ('bvl_const', 'SmartOp_flip'):
    ('new_definition', False, ''),
  ('bvl_const', 'bvl_const_SmartOp'):
    ('new_definition', False, ''),
  ('bvl_const', 'bvl_const_compile_exp'):
    ('new_definition', False, ''),
  ('bvl_const', 'bvl_const_compile_sing'):
    ('prim_rec', False, ''),
  ('bvl_const', 'bvl_const_delete_var'):
    ('new_definition', False, ''),
  ('bvl_const', 'bvl_const_extract'):
    ('new_definition', False, ''),
  ('bvl_const', 'bvl_const_extract_list'):
    ('prim_rec', False, ''),
  ('bvl_const', 'case_op_const'):
    ('new_definition', False, ''),
  ('bvl_const', 'dest_EqualInt'):
    ('new_definition', False, ''),
  ('bvl_const', 'dest_simple'):
    ('new_definition', False, ''),
  ('bvl_constProof', 'bvl_constProof_env_rel'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4).      (\\x. 0) x0 +      (\\x. 0) x1 +      list_size (option_size bvl_exp_size) x2 +      bvlSem_v_size1 x3 +      bvlSem_v_size1 x4)'),
  ('bvl_constProof', 'bvl_constProof_v_rel'):
    ('new_definition', False, ''),
  ('bvl_handle', 'LetLet'):
    ('new_definition', False, ''),
  ('bvl_handle', 'OptionalLetLet'):
    ('new_definition', False, ''),
  ('bvl_handle', 'OptionalLetLet_sing'):
    ('new_definition', False, ''),
  ('bvl_handle', 'SmartLet'):
    ('new_definition', False, ''),
  ('bvl_handle', 'bvl_handle_compile'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). bvl_exp_size1 x2)'),
  ('bvl_handle', 'bvl_handle_compile_exp'):
    ('new_definition', False, ''),
  ('bvl_handle', 'bvl_handle_compile_sing'):
    ('prim_rec', False, ''),
  ('bvl_handle', 'bvl_handle_dest_Seq'):
    ('new_definition', False, ''),
  ('bvl_handle', 'can_raise'):
    ('prim_rec', False, ''),
  ('bvl_handle', 'compile_any'):
    ('new_definition', False, ''),
  ('bvl_handle', 'compile_seqs'):
    ('measure', False, 'MEASURE (\\(c,e,a). bvl_exp_size e)'),
  ('bvl_handle', 'dest_handle_If'):
    ('new_definition', False, ''),
  ('bvl_handle', 'dest_handle_Let'):
    ('new_definition', False, ''),
  ('bvl_handle', 'dest_handle_Raise'):
    ('new_definition', False, ''),
  ('bvl_handle', 'handle_adj_vars'):
    ('prim_rec', False, ''),
  ('bvl_handle', 'handle_simp'):
    ('measure', False, ''),
  ('bvl_handle', 'handle_size'):
    ('prim_rec', False, ''),
  ('bvl_handleProof', 'bvl_handleProof_env_rel'):
    ('new_definition', False, ''),
  ('bvl_handleProof', 'handle_ok'):
    ('measure', True, ''),
  ('bvl_handleProof', 'let_ok'):
    ('new_definition', False, ''),
  ('bvl_inline', 'bvl_inline_compile_inc'):
    ('new_definition', False, ''),
  ('bvl_inline', 'bvl_inline_compile_prog'):
    ('new_definition', False, ''),
  ('bvl_inline', 'bvl_inline_dest_op'):
    ('new_definition', False, ''),
  ('bvl_inline', 'bvl_inline_is_rec'):
    ('measure', False, 'MEASURE (\\(x0,x1). bvl_exp_size1 x1)'),
  ('bvl_inline', 'bvl_inline_let_op'):
    ('nested', False, ''),
  ('bvl_inline', 'bvl_inline_let_op_sing'):
    ('new_definition', False, ''),
  ('bvl_inline', 'bvl_inline_optimise'):
    ('new_definition', False, ''),
  ('bvl_inline', 'bvl_inline_remove_ticks'):
    ('nested', False, ''),
  ('bvl_inline', 'bvl_inline_remove_ticks_sing'):
    ('prim_rec', False, ''),
  ('bvl_inline', 'bvl_inline_var_list'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). bvl_exp_size1 x1)'),
  ('bvl_inline', 'is_rec_sing'):
    ('prim_rec', False, ''),
  ('bvl_inline', 'is_small'):
    ('new_definition', False, ''),
  ('bvl_inline', 'is_small_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1). bvl_exp_size1 x1)'),
  ('bvl_inline', 'is_small_sing'):
    ('prim_rec', False, ''),
  ('bvl_inline', 'let_op_one'):
    ('prim_rec', False, ''),
  ('bvl_inline', 'must_inline'):
    ('new_definition', False, ''),
  ('bvl_inline', 'tick_compile_prog'):
    ('new_definition', False, ''),
  ('bvl_inline', 'tick_inline'):
    ('nested', False, ''),
  ('bvl_inline', 'tick_inline_all'):
    ('prim_rec', False, ''),
  ('bvl_inline', 'tick_inline_sing'):
    ('prim_rec', False, ''),
  ('bvl_inlineProof', 'bvl_inlineProof_in_cc'):
    ('new_definition', False, ''),
  ('bvl_inlineProof', 'bvl_inlineProof_in_co'):
    ('new_definition', False, ''),
  ('bvl_inlineProof', 'bvl_inlineProof_in_state_rel'):
    ('new_definition', False, ''),
  ('bvl_inlineProof', 'bvl_inlineProof_remove_ticks_cc'):
    ('new_definition', False, ''),
  ('bvl_inlineProof', 'bvl_inlineProof_remove_ticks_co'):
    ('new_definition', False, ''),
  ('bvl_inlineProof', 'bvl_inlineProof_state_rel'):
    ('new_definition', False, ''),
  ('bvl_inlineProof', 'bvl_inline_cc'):
    ('new_definition', False, ''),
  ('bvl_inlineProof', 'bvl_inline_co'):
    ('new_definition', False, ''),
  ('bvl_inlineProof', 'let_op_cc'):
    ('new_definition', False, ''),
  ('bvl_inlineProof', 'let_opt'):
    ('new_definition', False, ''),
  ('bvl_inlineProof', 'let_opt_remove'):
    ('new_definition', False, ''),
  ('bvl_inlineProof', 'let_state_rel'):
    ('new_definition', False, ''),
  ('bvl_jump', 'JumpList'):
    ('measure', True, ''),
  ('bvl_jump', 'bvl_jump_Jump'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'AllocGlobal_code'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'AllocGlobal_location'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'ConcatByte_code'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'ConcatByte_location'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'CopyGlobals_code'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'CopyGlobals_location'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'FromListByte_code'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'FromListByte_location'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'InitGlobals_code'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'InitGlobals_location'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'InitGlobals_max'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'ListLength_code'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'ListLength_location'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'SumListLength_code'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'SumListLength_location'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'ToListByte_code'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'ToListByte_location'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'alloc_glob_count'):
    ('measure', False, 'MEASURE (\\x0. bvl_exp_size1 x0)'),
  ('bvl_to_bvi', 'bvl_to_bvi_compile'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'bvl_to_bvi_compile_exps'):
    ('measure', False, ''),
  ('bvl_to_bvi', 'bvl_to_bvi_compile_inc'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'bvl_to_bvi_compile_inc_all'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'bvl_to_bvi_compile_list'):
    ('prim_rec', False, ''),
  ('bvl_to_bvi', 'bvl_to_bvi_compile_op'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'bvl_to_bvi_compile_prog'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'bvl_to_bvi_compile_single'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'bvl_to_bvi_default_config'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'bvl_to_bvi_get_names'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'bvl_to_bvi_stubs'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'compile_aux'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'compile_exps_sing'):
    ('measure', False, ''),
  ('bvl_to_bvi', 'compile_int'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'destLet'):
    ('new_definition', False, ''),
  ('bvl_to_bvi', 'global_count_sing'):
    ('prim_rec', False, ''),
  ('bvl_to_bviProof', 'adjust_bv'):
    ('nested', False, ''),
  ('bvl_to_bviProof', 'aux_code_installed'):
    ('prim_rec', False, ''),
  ('bvl_to_bviProof', 'bv_ok'):
    ('measure', False, 'MEASURE (bvlSem_v_size o SND)'),
  ('bvl_to_bviProof', 'bvl_to_bviProof_names_ok'):
    ('new_definition', False, ''),
  ('bvl_to_bviProof', 'bvl_to_bviProof_state_ok'):
    ('new_definition', False, ''),
  ('bvl_to_bviProof', 'bvl_to_bviProof_state_rel'):
    ('new_definition', False, ''),
  ('bvl_to_bviProof', 'full_cc'):
    ('new_definition', False, ''),
  ('bvl_to_bviProof', 'full_co'):
    ('new_definition', False, ''),
  ('bvl_to_bviProof', 'in_ns'):
    ('new_definition', False, ''),
  ('byte', 'byte_index'):
    ('new_definition', False, ''),
  ('byte', 'bytes_in_word'):
    ('new_definition', False, ''),
  ('byte', 'bytes_to_word'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4). (\\n. n) x0)'),
  ('byte', 'get_byte'):
    ('new_definition', False, ''),
  ('byte', 'set_byte'):
    ('new_definition', False, ''),
  ('byte', 'word_of_bytes'):
    ('prim_rec', False, ''),
  ('byte', 'word_to_bytes'):
    ('new_definition', False, ''),
  ('byte', 'word_to_bytes_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x0)'),
  ('closLang', 'assign_get_code_label'):
    ('new_definition', False, ''),
  ('closLang', 'closLang_pure_op'):
    ('new_definition', False, ''),
  ('closLang', 'has_install'):
    ('nested', False, ''),
  ('closLang', 'pure'):
    ('nested', False, ''),
  ('closProps', 'SUBMAP_rel'):
    ('new_definition', False, ''),
  ('closProps', 'app_call_dests'):
    ('measure', False, ''),
  ('closProps', 'check_closures'):
    ('new_definition', False, ''),
  ('closProps', 'clo_add_partial_args'):
    ('new_recursive_definition', False, ''),
  ('closProps', 'clo_can_apply'):
    ('new_definition', False, ''),
  ('closProps', 'clo_to_env'):
    ('new_recursive_definition', False, ''),
  ('closProps', 'clo_to_loc'):
    ('new_recursive_definition', False, ''),
  ('closProps', 'clo_to_num_params'):
    ('new_recursive_definition', False, ''),
  ('closProps', 'clo_to_partial_args'):
    ('new_recursive_definition', False, ''),
  ('closProps', 'closProps_adj_orac_rel'):
    ('new_definition', False, ''),
  ('closProps', 'closProps_esgc_free'):
    ('nested', False, ''),
  ('closProps', 'closProps_eval_sim'):
    ('new_definition', False, ''),
  ('closProps', 'closProps_get_code_labels'):
    ('measure', False, ''),
  ('closProps', 'closProps_isClos'):
    ('new_definition', False, ''),
  ('closProps', 'closProps_op_gbag'):
    ('new_definition', False, ''),
  ('closProps', 'closProps_ref_rel'):
    ('new_definition', False, ''),
  ('closProps', 'closProps_set_globals'):
    ('measure', False, ''),
  ('closProps', 'closProps_simple_state_rel'):
    ('new_definition', False, ''),
  ('closProps', 'closProps_simple_val_rel'):
    ('new_definition', False, ''),
  ('closProps', 'code_locs'):
    ('measure', False, ''),
  ('closProps', 'contains_App_SOME'):
    ('measure', True, ''),
  ('closProps', 'every_Fn_SOME'):
    ('measure', False, ''),
  ('closProps', 'every_Fn_vs_NONE'):
    ('measure', False, ''),
  ('closProps', 'every_Fn_vs_SOME'):
    ('measure', False, ''),
  ('closProps', 'fv'):
    ('measure', False, ''),
  ('closProps', 'fv1'):
    ('new_definition', False, ''),
  ('closProps', 'is_closure'):
    ('new_definition', False, ''),
  ('closProps', 'no_Labels'):
    ('measure', False, ''),
  ('closProps', 'no_mti'):
    ('nested', False, ''),
  ('closProps', 'obeys_max_app'):
    ('measure', False, ''),
  ('closProps', 'rec_clo_ok'):
    ('new_recursive_definition', False, ''),
  ('closProps', 'rsgc_free'):
    ('new_definition', False, ''),
  ('closProps', 'simple_compile_state_rel'):
    ('new_definition', False, ''),
  ('closProps', 'ssgc_free'):
    ('new_definition', False, ''),
  ('closProps', 'vsgc_free'):
    ('measure', False, 'MEASURE closSem_v_size'),
  ('closSem', 'build_recc'):
    ('new_definition', False, ''),
  ('closSem', 'check_loc'):
    ('new_recursive_definition', False, ''),
  ('closSem', 'closSem_AppUnit'):
    ('new_definition', False, ''),
  ('closSem', 'closSem_Boolv'):
    ('new_definition', False, ''),
  ('closSem', 'closSem_Unit'):
    ('new_definition', False, ''),
  ('closSem', 'closSem_bad_thunk_update'):
    ('new_definition', False, ''),
  ('closSem', 'closSem_dec_clock'):
    ('new_definition', False, ''),
  ('closSem', 'closSem_dest_thunk'):
    ('new_definition', False, ''),
  ('closSem', 'closSem_do_app'):
    ('new_definition', False, ''),
  ('closSem', 'closSem_do_eq'):
    ('measure', False, 'MEASURE (sum_measure (\\(x0,x1). closSem_v_size x0 + closSem_v_size x1) (\\(x0,x1). closSem_v_size1 x0 + closSem_v_size1 x1))'),
  ('closSem', 'closSem_do_install'):
    ('new_definition', False, ''),
  ('closSem', 'closSem_do_int_app'):
    ('new_definition', False, ''),
  ('closSem', 'closSem_do_word_app'):
    ('new_definition', False, ''),
  ('closSem', 'closSem_evaluate'):
    ('measure', False, ''),
  ('closSem', 'closSem_exp_alt_size'):
    ('prim_rec', False, ''),
  ('closSem', 'closSem_find_code'):
    ('new_definition', False, ''),
  ('closSem', 'closSem_fix_clock'):
    ('new_definition', False, ''),
  ('closSem', 'closSem_initial_state'):
    ('new_definition', False, ''),
  ('closSem', 'closSem_list_to_v'):
    ('prim_rec', False, ''),
  ('closSem', 'closSem_semantics'):
    ('new_definition', False, ''),
  ('closSem', 'closSem_update_thunk'):
    ('new_definition', False, ''),
  ('closSem', 'closSem_v_to_bytes'):
    ('new_definition', False, ''),
  ('closSem', 'closSem_v_to_list'):
    ('measure', False, 'MEASURE (\\x0. closSem_v_size x0)'),
  ('closSem', 'closSem_v_to_words'):
    ('new_definition', False, ''),
  ('closSem', 'clos_env'):
    ('new_definition', False, ''),
  ('closSem', 'dest_closure'):
    ('new_definition', False, ''),
  ('closSem', 'get_global'):
    ('new_definition', False, ''),
  ('closSem', 'make_const'):
    ('nested', False, ''),
  ('closSem', 'opw_lookup'):
    ('define_single', False, ''),
  ('closSem', 'store_thunk'):
    ('new_definition', False, ''),
  ('clos_annotate', 'alt_free'):
    ('measure', False, ''),
  ('clos_annotate', 'alt_free_sing'):
    ('measure', False, ''),
  ('clos_annotate', 'annotate_list'):
    ('new_definition', False, ''),
  ('clos_annotate', 'annotate_sing'):
    ('new_definition', False, ''),
  ('clos_annotate', 'clos_annotate_annotate'):
    ('new_definition', False, ''),
  ('clos_annotate', 'clos_annotate_compile'):
    ('new_definition', False, ''),
  ('clos_annotate', 'clos_annotate_compile_inc'):
    ('new_definition', False, ''),
  ('clos_annotate', 'clos_annotate_get_var'):
    ('new_definition', False, ''),
  ('clos_annotate', 'clos_annotate_shift'):
    ('measure', False, ''),
  ('clos_annotate', 'const_0'):
    ('new_definition', False, ''),
  ('clos_annotate', 'no_overlap'):
    ('measure', False, 'MEASURE (\\(x0,x1). (\\n. n) x0)'),
  ('clos_annotate', 'shift_sing'):
    ('measure', False, ''),
  ('clos_annotate', 'shifted_env'):
    ('prim_rec', False, ''),
  ('clos_annotateProof', 'alt_fv'):
    ('new_definition', False, ''),
  ('clos_annotateProof', 'alt_fv1'):
    ('new_definition', False, ''),
  ('clos_annotateProof', 'clos_annotateProof_state_rel'):
    ('new_definition', False, ''),
  ('clos_call', 'GENLIST_Var'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x2)'),
  ('clos_call', 'calls'):
    ('measure', False, ''),
  ('clos_call', 'calls_list'):
    ('prim_rec', False, ''),
  ('clos_call', 'calls_sing'):
    ('measure', False, ''),
  ('clos_call', 'clos_call_closed'):
    ('new_definition', False, ''),
  ('clos_call', 'clos_call_compile'):
    ('define_single', False, ''),
  ('clos_call', 'clos_call_compile_inc'):
    ('new_definition', False, ''),
  ('clos_call', 'clos_call_free'):
    ('measure', False, ''),
  ('clos_call', 'code_list'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). list_size (pair_size (\\x. 0) (\\x. 0)) x1)'),
  ('clos_call', 'cond_call_compile_inc'):
    ('new_definition', False, ''),
  ('clos_call', 'free_sing'):
    ('nested', False, ''),
  ('clos_call', 'insert_each'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x1)'),
  ('clos_callProof', 'clos_callProof_env_rel'):
    ('new_definition', False, ''),
  ('clos_callProof', 'clos_callProof_nth_code'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x2)'),
  ('clos_callProof', 'clos_callProof_state_rel'):
    ('new_definition', False, ''),
  ('clos_callProof', 'clos_callProof_syntax_ok'):
    ('new_definition', False, ''),
  ('clos_callProof', 'clos_callProof_v_rel'):
    ('measure', False, ''),
  ('clos_callProof', 'co_ok'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). (\\n. n) x3)'),
  ('clos_callProof', 'code_includes'):
    ('new_definition', False, ''),
  ('clos_callProof', 'code_inv'):
    ('new_definition', False, ''),
  ('clos_callProof', 'every_refv'):
    ('new_definition', False, ''),
  ('clos_callProof', 'includes_state'):
    ('new_definition', False, ''),
  ('clos_callProof', "insert_each'"):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). list_size (pair_size (\\n. n) (\\x. 0)) x0)'),
  ('clos_callProof', 'is_Recclosure'):
    ('new_definition', False, ''),
  ('clos_callProof', 'make_g'):
    ('new_definition', False, ''),
  ('clos_callProof', 'mk_code_g'):
    ('new_definition', False, ''),
  ('clos_callProof', 'recclosure_rel'):
    ('new_definition', False, ''),
  ('clos_callProof', 'recclosure_wf'):
    ('new_definition', False, ''),
  ('clos_callProof', 'state_syntax'):
    ('new_definition', False, ''),
  ('clos_callProof', 'subg'):
    ('new_definition', False, ''),
  ('clos_callProof', 'wfg'):
    ('new_definition', False, ''),
  ('clos_callProof', "wfg'"):
    ('new_definition', False, ''),
  ('clos_callProof', 'wfv'):
    ('measure', False, 'MEASURE (closSem_v_size o SND o SND o SND)'),
  ('clos_callProof', 'wfv_state'):
    ('new_definition', False, ''),
  ('clos_constantProof', 'build'):
    ('prim_rec', False, ''),
  ('clos_constantProof', "build'"):
    ('prim_rec', False, ''),
  ('clos_constantProof', 'build_const'):
    ('new_definition', False, ''),
  ('clos_constantProof', "build_const'"):
    ('new_definition', False, ''),
  ('clos_constantProof', 'build_map'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). list_size const_part_size x2)'),
  ('clos_constantProof', 'build_part'):
    ('new_recursive_definition', False, ''),
  ('clos_constantProof', "build_part'"):
    ('new_recursive_definition', False, ''),
  ('clos_constantProof', 'conses_ok'):
    ('new_definition', False, ''),
  ('clos_constantProof', 'good_hash_table'):
    ('new_definition', False, ''),
  ('clos_constantProof', 'make_part'):
    ('new_definition', False, ''),
  ('clos_constantProof', 'parts'):
    ('prim_rec', False, ''),
  ('clos_constantProof', 'to_parts'):
    ('new_recursive_definition', False, ''),
  ('clos_constantProof', 'update_tag'):
    ('new_definition', False, ''),
  ('clos_fvs', 'clos_fvs_compile'):
    ('new_definition', False, ''),
  ('clos_fvs', 'clos_fvs_compile_inc'):
    ('new_definition', False, ''),
  ('clos_fvs', 'remove_fvs'):
    ('nested', False, ''),
  ('clos_fvs', 'remove_fvs_sing'):
    ('nested', False, ''),
  ('clos_fvsProof', 'clos_fvsProof_code_rel'):
    ('new_definition', False, ''),
  ('clos_fvsProof', 'clos_fvsProof_f_rel'):
    ('new_definition', False, ''),
  ('clos_fvsProof', 'clos_fvsProof_state_rel'):
    ('new_definition', False, ''),
  ('clos_interp', 'attach_interpreter'):
    ('new_definition', False, ''),
  ('clos_interp', 'can_interpret'):
    ('prim_rec', False, ''),
  ('clos_interp', 'can_interpret_op'):
    ('new_definition', False, ''),
  ('clos_interp', 'check_size'):
    ('prim_rec', False, ''),
  ('clos_interp', 'check_size_op'):
    ('new_definition', False, ''),
  ('clos_interp', 'clos_interp_el'):
    ('new_definition', False, ''),
  ('clos_interp', 'clos_interp_rev'):
    ('new_definition', False, ''),
  ('clos_interp', 'clos_interpreter'):
    ('new_definition', False, ''),
  ('clos_interp', 'clos_interpreter_body'):
    ('new_definition', False, ''),
  ('clos_interp', 'compile_init'):
    ('new_definition', False, ''),
  ('clos_interp', 'insert_interp'):
    ('new_definition', False, ''),
  ('clos_interp', 'insert_interp1'):
    ('new_definition', False, ''),
  ('clos_interp', 'nontrivial_size'):
    ('new_definition', False, ''),
  ('clos_interp', 'opt_interp'):
    ('new_definition', False, ''),
  ('clos_interp', 'opt_interp1'):
    ('new_definition', False, ''),
  ('clos_interp', 'to_constant'):
    ('measure', False, ''),
  ('clos_interp', 'to_constant_op'):
    ('new_definition', False, ''),
  ('clos_interpProof', 'clos_interpProof_state_rel'):
    ('new_definition', False, ''),
  ('clos_interpProof', 'interp_assum'):
    ('new_definition', False, ''),
  ('clos_interpProof', 'res_ok'):
    ('new_definition', False, ''),
  ('clos_interpProof', "state_rel'"):
    ('new_definition', False, ''),
  ('clos_interpProof', 'state_rel_1'):
    ('new_definition', False, ''),
  ('clos_interpProof', 'v_ok'):
    ('nested', False, ''),
  ('clos_known', 'clos_approx'):
    ('new_definition', False, ''),
  ('clos_known', 'clos_gen_noinline'):
    ('prim_rec', False, ''),
  ('clos_known', 'clos_known_closed'):
    ('new_definition', False, ''),
  ('clos_known', 'clos_known_compile'):
    ('new_recursive_definition', False, ''),
  ('clos_known', 'clos_known_compile_inc'):
    ('new_definition', False, ''),
  ('clos_known', 'clos_known_default_config'):
    ('new_definition', False, ''),
  ('clos_known', 'clos_known_free'):
    ('measure', False, ''),
  ('clos_known', 'clos_known_get_size'):
    ('new_definition', False, ''),
  ('clos_known', 'clos_known_merge'):
    ('measure', False, 'MEASURE (\\(x0,x1). val_approx_size x0 + val_approx_size x1)'),
  ('clos_known', 'clos_known_mk_Ticks'):
    ('measure', False, 'MEASURE (FST o SND o SND)'),
  ('clos_known', 'contains_closures'):
    ('measure', False, 'MEASURE (\\x0. closLang_exp_size1 x0)'),
  ('clos_known', 'dec_inline_factor'):
    ('new_definition', False, ''),
  ('clos_known', 'decide_inline'):
    ('new_definition', False, ''),
  ('clos_known', 'default_inline_factor'):
    ('new_definition', False, ''),
  ('clos_known', 'default_max_body_size'):
    ('new_definition', False, ''),
  ('clos_known', 'gO_destApx'):
    ('new_definition', False, ''),
  ('clos_known', 'get_size_aux'):
    ('measure', False, 'MEASURE (list_size closLang_exp_size)'),
  ('clos_known', 'get_size_sc'):
    ('new_definition', False, ''),
  ('clos_known', 'get_size_sc_aux'):
    ('measure', False, ''),
  ('clos_known', 'isGlobal'):
    ('new_definition', False, ''),
  ('clos_known', 'known'):
    ('measure', False, ''),
  ('clos_known', 'known_compile_inc'):
    ('new_recursive_definition', False, ''),
  ('clos_known', 'known_op'):
    ('new_definition', False, ''),
  ('clos_known', 'known_static_conf'):
    ('new_definition', False, ''),
  ('clos_known', 'merge_tup'):
    ('measure', False, 'MEASURE (val_approx_size o FST)'),
  ('clos_known', 'mk_config'):
    ('new_definition', False, ''),
  ('clos_known', 'option_upd_val_spt'):
    ('new_recursive_definition', False, ''),
  ('clos_known', 'option_val_approx_spt'):
    ('new_definition', False, ''),
  ('clos_known', 'reset_inline_factor'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'clos_knownProof_every_var'):
    ('prim_rec', False, ''),
  ('clos_knownProof', 'clos_knownProof_exp_rel'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'clos_knownProof_f_rel'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'clos_knownProof_state_rel'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'clos_knownProof_syntax_ok'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'clos_knownProof_syntax_oracle_ok'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'clos_knownProof_v_rel'):
    ('measure', False, ''),
  ('clos_knownProof', 'co_every_Fn_vs_NONE'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'first_n_exps'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'fv_max'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'gapprox_disjoint'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'gapprox_extend'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'globals_approx_every_Fn_SOME'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'globals_approx_every_Fn_vs_NONE'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'globals_approx_no_Labels'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'globals_approx_obeys_max_app'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'globals_approx_sgc_free'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'known_cc'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'known_co'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'known_co_progs'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'known_mk_co'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'loptrel'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'mapped_globals'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'mglobals_disjoint'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'mglobals_extend'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'next_g'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'oracle_gapprox_disjoint'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'oracle_gapprox_subspt'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'oracle_state_sgc_free'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'state_globals_approx'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'state_oracle_mglobals_disjoint'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'unique_set_globals'):
    ('new_definition', False, ''),
  ('clos_knownProof', 'v_rel_app'):
    ('new_recursive_definition', False, ''),
  ('clos_knownProof', 'val_approx_every_Fn_SOME'):
    ('measure', False, 'MEASURE val_approx_size'),
  ('clos_knownProof', 'val_approx_every_Fn_vs_NONE'):
    ('measure', False, 'MEASURE val_approx_size'),
  ('clos_knownProof', 'val_approx_no_Labels'):
    ('measure', False, 'MEASURE val_approx_size'),
  ('clos_knownProof', 'val_approx_obeys_max_app'):
    ('measure', False, 'MEASURE (val_approx_size o SND)'),
  ('clos_knownProof', 'val_approx_sgc_free'):
    ('measure', False, 'MEASURE val_approx_size'),
  ('clos_knownProps', 'better_definedg'):
    ('new_definition', False, ''),
  ('clos_knownProps', 'subapprox'):
    ('new_definition', False, ''),
  ('clos_letop', 'clos_letop_compile_inc'):
    ('new_definition', False, ''),
  ('clos_letop', 'clos_letop_dest_op'):
    ('new_definition', False, ''),
  ('clos_letop', 'clos_letop_let_op'):
    ('nested', False, ''),
  ('clos_letop', 'clos_letop_let_op_sing'):
    ('nested', False, ''),
  ('clos_letop', 'clos_letop_var_list'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). closLang_exp_size1 x1)'),
  ('clos_letopProof', 'clos_letopProof_FMAP_REL'):
    ('new_definition', False, ''),
  ('clos_letopProof', 'clos_letopProof_code_rel'):
    ('new_definition', False, ''),
  ('clos_letopProof', 'clos_letopProof_f_rel'):
    ('new_definition', False, ''),
  ('clos_letopProof', 'clos_letopProof_state_rel'):
    ('new_definition', False, ''),
  ('clos_mti', 'clos_mti_compile'):
    ('define_single', False, ''),
  ('clos_mti', 'clos_mti_compile_inc'):
    ('new_definition', False, ''),
  ('clos_mti', 'collect_apps'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). closLang_exp_size x2)'),
  ('clos_mti', 'collect_args'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). closLang_exp_size x2)'),
  ('clos_mti', 'cond_mti_compile_inc'):
    ('new_definition', False, ''),
  ('clos_mti', 'intro_multi'):
    ('measure', True, ''),
  ('clos_mtiProof', 'clos_mtiProof_FMAP_REL'):
    ('new_definition', False, ''),
  ('clos_mtiProof', 'clos_mtiProof_code_rel'):
    ('new_definition', False, ''),
  ('clos_mtiProof', 'clos_mtiProof_f_rel'):
    ('new_definition', False, ''),
  ('clos_mtiProof', 'clos_mtiProof_state_rel'):
    ('new_definition', False, ''),
  ('clos_mtiProof', 'evaluate_apps'):
    ('prim_rec', False, ''),
  ('clos_mtiProof', 'mk_Apps'):
    ('prim_rec', False, ''),
  ('clos_mtiProof', 'mk_Fns'):
    ('prim_rec', False, ''),
  ('clos_mtiProof', 'v_rel_opt'):
    ('new_definition', False, ''),
  ('clos_number', 'clos_number_compile_inc'):
    ('new_definition', False, ''),
  ('clos_number', 'ignore_table'):
    ('new_definition', False, ''),
  ('clos_number', 'renumber_code_locs_list'):
    ('measure', False, ''),
  ('clos_numberProof', 'clos_numberProof_state_rel'):
    ('new_definition', False, ''),
  ('clos_op', 'ConjList'):
    ('measure', False, 'MEASURE (\\x0. closLang_exp_size1 x0)'),
  ('clos_op', 'MakeBool'):
    ('new_definition', False, ''),
  ('clos_op', 'MakeInt'):
    ('new_definition', False, ''),
  ('clos_op', "SmartOp'"):
    ('new_definition', False, ''),
  ('clos_op', 'clos_op_SmartOp'):
    ('new_definition', False, ''),
  ('clos_op', 'clos_op_dest_Cons'):
    ('new_definition', False, ''),
  ('clos_op', 'clos_op_dest_Constant'):
    ('new_definition', False, ''),
  ('clos_op', 'clos_op_int_op'):
    ('new_definition', False, ''),
  ('clos_op', 'cons_measure'):
    ('measure', False, 'MEASURE closLang_exp_size'),
  ('clos_op', 'cons_op'):
    ('new_definition', False, ''),
  ('clos_op', 'dest_Const'):
    ('new_definition', False, ''),
  ('clos_op', 'dest_ElemAt'):
    ('new_definition', False, ''),
  ('clos_op', 'dest_LenEq'):
    ('new_definition', False, ''),
  ('clos_op', 'dest_Op'):
    ('new_definition', False, ''),
  ('clos_op', 'dest_Op_Consts'):
    ('new_definition', False, ''),
  ('clos_op', 'dest_Op_Nil'):
    ('new_definition', False, ''),
  ('clos_op', 'dest_TagEq'):
    ('new_definition', False, ''),
  ('clos_op', 'dest_TagLenEq'):
    ('new_definition', False, ''),
  ('clos_op', 'dont_lift'):
    ('new_definition', False, ''),
  ('clos_op', 'eq_any'):
    ('new_definition', False, ''),
  ('clos_op', 'eq_direct'):
    ('new_definition', False, ''),
  ('clos_op', 'eq_direct_const'):
    ('new_definition', False, ''),
  ('clos_op', 'eq_direct_constant'):
    ('new_definition', False, ''),
  ('clos_op', 'eq_direct_nil'):
    ('new_definition', False, ''),
  ('clos_op', 'eq_op'):
    ('new_definition', False, ''),
  ('clos_op', 'eq_pure'):
    ('new_definition', False, ''),
  ('clos_op', 'eq_pure_list'):
    ('measure', True, ''),
  ('clos_op', 'is_Var'):
    ('new_definition', False, ''),
  ('clos_op', 'lift_exps'):
    ('measure', False, 'MEASURE (\\(xs,n,binds). list_size closLang_exp_size xs)'),
  ('clos_ticks', 'clos_ticks_compile_inc'):
    ('new_definition', False, ''),
  ('clos_ticks', 'clos_ticks_remove_ticks'):
    ('nested', False, ''),
  ('clos_ticks', 'clos_ticks_remove_ticks_sing'):
    ('nested', False, ''),
  ('clos_ticksProof', 'clos_ticksProof_FMAP_REL'):
    ('new_definition', False, ''),
  ('clos_ticksProof', 'clos_ticksProof_code_rel'):
    ('new_definition', False, ''),
  ('clos_ticksProof', 'clos_ticksProof_f_rel'):
    ('new_definition', False, ''),
  ('clos_ticksProof', 'clos_ticksProof_mk_Ticks'):
    ('prim_rec', False, ''),
  ('clos_ticksProof', 'clos_ticksProof_state_rel'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'add_part'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'add_parts'):
    ('prim_rec', False, ''),
  ('clos_to_bvl', 'add_src_names'):
    ('prim_rec', False, ''),
  ('clos_to_bvl', 'build_aux'):
    ('prim_rec', False, ''),
  ('clos_to_bvl', 'build_recc_lets'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'chain_exps'):
    ('measure', False, 'MEASURE (\\(x0,x1). closLang_exp_size1 x1)'),
  ('clos_to_bvl', 'check_closure'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'clos_to_bvl_compile'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'clos_to_bvl_compile_exps'):
    ('measure', False, ''),
  ('clos_to_bvl', 'clos_to_bvl_compile_inc'):
    ('new_definition', False, ''),
  ('clos_to_bvl', "clos_to_bvl_compile_inc'"):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'clos_to_bvl_compile_op'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'clos_to_bvl_compile_prog'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'clos_to_bvl_default_config'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'clos_to_bvl_init_code'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'code_for_recc_case'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'code_merge'):
    ('measure', False, 'MEASURE (\\(x0,x1).      list_size (pair_size (\\n. n) (\\x. 0)) x0 +      list_size (pair_size (\\n. n) (\\x. 0)) x1)'),
  ('clos_to_bvl', 'code_sort'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'code_split'):
    ('prim_rec', False, ''),
  ('clos_to_bvl', 'compile_common'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'compile_const'):
    ('new_recursive_definition', False, ''),
  ('clos_to_bvl', 'compile_exp_sing'):
    ('measure', False, ''),
  ('clos_to_bvl', 'extract_name'):
    ('new_recursive_definition', False, ''),
  ('clos_to_bvl', 'force_thunk_code'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'free_let'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'generate_generic_app'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'generate_partial_app_closure_fn'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'generic_app_fn_location'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'get_src_names'):
    ('measure', False, ''),
  ('clos_to_bvl', 'get_src_names_sing'):
    ('measure', False, ''),
  ('clos_to_bvl', 'init_globals'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'make_name_alist'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'mk_cl_call'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'mk_const'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'mk_el'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'mk_label'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'num_added_globals'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'num_stubs'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'part_hash'):
    ('new_recursive_definition', False, ''),
  ('clos_to_bvl', 'partial_app_fn_location'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'partial_app_fn_location_code'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'partial_app_label_table_loc'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'recc_Let'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'recc_Let0'):
    ('new_definition', False, ''),
  ('clos_to_bvl', 'recc_Lets'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). (\\n. n) x2)'),
  ('clos_to_bvlProof', 'add_args'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'can_extract'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'chain_installed'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', "check_loc'"):
    ('new_recursive_definition', False, ''),
  ('clos_to_bvlProof', 'clos_init'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'clos_state_cc'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'clos_to_bvlProof_code_installed'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'clos_to_bvlProof_env_rel'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4,x5). closSem_v_size1 x4 + bvlSem_v_size1 x5)'),
  ('clos_to_bvlProof', 'clos_to_bvlProof_eval_sim'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'clos_to_bvlProof_init_code'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'clos_to_bvlProof_nth_code'):
    ('measure', False, 'MEASURE (\\(x0,x1). (\\n. n) x1)'),
  ('clos_to_bvlProof', 'clos_to_bvlProof_ref_rel'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'clos_to_bvlProof_state_rel'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'clos_to_bvlProof_syntax_oracle_ok'):
    ('', False, ''),
  ('clos_to_bvlProof', 'closure_code_installed'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'compile_common_inc'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'compile_inc_post_kcompile'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'compile_oracle_inv'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', "dest_closure'"):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'eq_res'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'extracted_addrs'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'get_cl_env'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'get_loc'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'get_num_args'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'get_old_args'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'global_table'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'num_remaining_args'):
    ('new_definition', False, ''),
  ('clos_to_bvlProof', 'req_compile_inc_addrs'):
    ('new_definition', False, ''),
  ('cmlPEG', 'bindNT'):
    ('new_definition', False, ''),
  ('cmlPEG', 'bindNT0'):
    ('new_definition', False, ''),
  ('cmlPEG', 'cmlPEG'):
    ('new_definition', False, ''),
  ('cmlPEG', 'cmlPEG_choicel'):
    ('prim_rec', False, ''),
  ('cmlPEG', 'cmlPEG_pegf'):
    ('new_definition', False, ''),
  ('cmlPEG', 'cmlPEG_pnt'):
    ('new_definition', False, ''),
  ('cmlPEG', 'cmlPEG_sumID'):
    ('new_recursive_definition', False, ''),
  ('cmlPEG', 'cmlPEG_tokeq'):
    ('new_definition', False, ''),
  ('cmlPEG', 'cmlPEG_try'):
    ('new_definition', False, ''),
  ('cmlPEG', 'mkNd'):
    ('new_definition', False, ''),
  ('cmlPEG', 'mk_linfix'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). parsetree_size1 locs_size (\\x. 0) (\\x. 0) x2)'),
  ('cmlPEG', 'mk_rinfix'):
    ('measure', False, 'MEASURE (\\(x0,x1). parsetree_size1 locs_size (\\x. 0) (\\x. 0) x1)'),
  ('cmlPEG', 'mktokLf'):
    ('new_definition', False, ''),
  ('cmlPEG', 'peg_EbaseParen'):
    ('new_definition', False, ''),
  ('cmlPEG', 'peg_EbaseParenFn'):
    ('new_definition', False, ''),
  ('cmlPEG', 'peg_StructName'):
    ('new_definition', False, ''),
  ('cmlPEG', 'peg_TypeDec'):
    ('new_definition', False, ''),
  ('cmlPEG', 'peg_UQConstructorName'):
    ('new_definition', False, ''),
  ('cmlPEG', 'peg_V'):
    ('new_definition', False, ''),
  ('cmlPEG', 'peg_linfix'):
    ('new_definition', False, ''),
  ('cmlPEG', 'peg_longV'):
    ('new_definition', False, ''),
  ('cmlPEG', 'ptPapply'):
    ('new_definition', False, ''),
  ('cmlPEG', 'ptPapply0'):
    ('measure', False, 'MEASURE (\\(x0,x1). parsetree_size1 locs_size MMLnonT_size (\\x. 0) x1)'),
  ('cmlPEG', 'seql'):
    ('new_definition', False, ''),
  ('cmlPEG', 'tokSymP'):
    ('new_definition', False, ''),
  ('cmlParse', 'cmlParseExpr'):
    ('new_definition', False, ''),
  ('cmlParse', 'cmlParse_destResult'):
    ('new_definition', False, ''),
  ('cmlParse', 'optlift'):
    ('define_single', False, ''),
  ('cmlParse', 'parse_prog'):
    ('new_definition', False, ''),
  ('cmlParse', 'pegresult_bind'):
    ('new_definition', False, ''),
  ('cmlParse', 'pegresult_choice'):
    ('new_definition', False, ''),
  ('cmlParse', 'pegresult_guard'):
    ('new_definition', False, ''),
  ('cmlParse', 'toks_to_loc'):
    ('new_recursive_definition', False, ''),
  ('cmlPtreeConversion', 'Eseq_encode'):
    ('measure', False, 'MEASURE (\\x0. ast_exp_size3 x0)'),
  ('cmlPtreeConversion', 'EtoPat'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'Long_Short'):
    ('prim_rec', False, ''),
  ('cmlPtreeConversion', 'Papply'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'bind_loc'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'dePat'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'destFFIop'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'dest_Conk'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'detuplify'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'empty_PCstate0'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'fixity_lookup'):
    ('match', False, ''),
  ('cmlPtreeConversion', 'ifM'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'isConstructor'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'isSymbolicConstructor'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'letFromPat'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'mFUPD_HD'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'maybe_handleRef'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'merge_locsopt'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'mfixity_lookup'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'mkAst_App'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'mkFun'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'mk_binop'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'mpop_namedscope'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'mpopscope'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'mpushPC_scope'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'msetfix'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'optLannot'):
    ('new_recursive_definition', False, ''),
  ('cmlPtreeConversion', 'ptree_ConstructorName'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'ptree_Dconstructor'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'ptree_Decl'):
    ('measure', False, 'MEASURE (sum_measure  (\\x0. parsetree_size locs_size MMLnonT_size tokens_token_size x0) (sum_measure  (\\x0. parsetree_size locs_size MMLnonT_size tokens_token_size x0) (\\x0. parsetree_size locs_size MMLnonT_size tokens_token_size x0)))'),
  ('cmlPtreeConversion', 'ptree_DtypeDecl'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'ptree_Eliteral'):
    ('new_recursive_definition', False, ''),
  ('cmlPtreeConversion', 'ptree_Expr'):
    ('measure', False, ''),
  ('cmlPtreeConversion', 'ptree_FQV'):
    ('new_recursive_definition', False, ''),
  ('cmlPtreeConversion', 'ptree_Op'):
    ('define_single', False, ''),
  ('cmlPtreeConversion', 'ptree_OpID'):
    ('new_recursive_definition', False, ''),
  ('cmlPtreeConversion', 'ptree_OptTypEqn'):
    ('new_recursive_definition', False, ''),
  ('cmlPtreeConversion', 'ptree_PTbase'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'ptree_Pattern'):
    ('measure', False, 'MEASURE (sum_measure  (\\(x0,x1). parsetree_size (\\x. 0) MMLnonT_size tokens_token_size x1) (\\x0. parsetree_size (\\x. 0) MMLnonT_size tokens_token_size x0))'),
  ('cmlPtreeConversion', 'ptree_PbaseList1'):
    ('measure', False, 'MEASURE (\\x0. parsetree_size (\\x. 0) MMLnonT_size tokens_token_size x0)'),
  ('cmlPtreeConversion', 'ptree_SignatureValue'):
    ('new_recursive_definition', False, ''),
  ('cmlPtreeConversion', 'ptree_SpecLine'):
    ('new_recursive_definition', False, ''),
  ('cmlPtreeConversion', 'ptree_SpeclineList'):
    ('measure', False, 'MEASURE (\\x0. parsetree_size locs_size MMLnonT_size tokens_token_size x0)'),
  ('cmlPtreeConversion', 'ptree_StructName'):
    ('new_recursive_definition', False, ''),
  ('cmlPtreeConversion', 'ptree_TbaseList'):
    ('measure', False, 'MEASURE (\\x0. parsetree_size (\\x. 0) MMLnonT_size tokens_token_size x0)'),
  ('cmlPtreeConversion', 'ptree_TopLevelDecs'):
    ('measure', False, 'MEASURE (sum_measure  (\\x0. parsetree_size locs_size MMLnonT_size tokens_token_size x0) (\\x0. parsetree_size locs_size MMLnonT_size tokens_token_size x0))'),
  ('cmlPtreeConversion', 'ptree_Tyop'):
    ('new_recursive_definition', False, ''),
  ('cmlPtreeConversion', 'ptree_Type'):
    ('measure', False, 'MEASURE (sum_measure  (\\(x0,x1). parsetree_size (\\x. 0) MMLnonT_size tokens_token_size x1) (sum_measure (\\x0. parsetree_size (\\x. 0) MMLnonT_size tokens_token_size x0) (sum_measure (\\x0. parsetree_size (\\x. 0) MMLnonT_size tokens_token_size x0) (\\x0. parsetree_size (\\x. 0) MMLnonT_size tokens_token_size x0))))'),
  ('cmlPtreeConversion', 'ptree_TypeAbbrevDec'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'ptree_TypeDec'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'ptree_TypeName'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'ptree_TyvarN'):
    ('new_recursive_definition', False, ''),
  ('cmlPtreeConversion', 'ptree_UQConstructorName'):
    ('new_recursive_definition', False, ''),
  ('cmlPtreeConversion', 'ptree_UQTyop'):
    ('new_recursive_definition', False, ''),
  ('cmlPtreeConversion', 'ptree_V'):
    ('new_recursive_definition', False, ''),
  ('cmlPtreeConversion', 'ptree_linfix'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). parsetree_size locs_size MMLnonT_size tokens_token_size x3)'),
  ('cmlPtreeConversion', 'singleSymP'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'strip_loc_expr'):
    ('match', False, ''),
  ('cmlPtreeConversion', 'tokcheck'):
    ('new_definition', False, ''),
  ('cmlPtreeConversion', 'tokcheckl'):
    ('measure', False, 'MEASURE (\\(x0,x1). parsetree_size1 (\\x. 0) (\\x. 0) (\\x. 0) x0)'),
  ('cmlPtreeConversion', 'tuplify'):
    ('new_definition', False, ''),
  ('collapse', 'collapse'):
    ('new_definition', False, ''),
  ('comparison', 'good_cmp'):
    ('new_definition', False, ''),
  ('compiler', 'add_tap_output'):
    ('new_definition', False, ''),
  ('compiler', 'comma_tokens'):
    ('prim_rec', False, ''),
  ('compiler', 'compile_32'):
    ('new_definition', False, ''),
  ('compiler', 'compile_64'):
    ('new_definition', False, ''),
  ('compiler', 'compile_pancake'):
    ('new_definition', False, ''),
  ('compiler', 'compile_pancake_32'):
    ('new_definition', False, ''),
  ('compiler', 'compile_pancake_64'):
    ('new_definition', False, ''),
  ('compiler', 'compiler_compile'):
    ('new_definition', False, ''),
  ('compiler', 'conf_ok_check'):
    ('new_definition', False, ''),
  ('compiler', 'error_to_str'):
    ('new_recursive_definition', False, ''),
  ('compiler', 'extend_conf'):
    ('new_definition', False, ''),
  ('compiler', 'find_bool'):
    ('new_definition', False, ''),
  ('compiler', 'find_next_newline'):
    ('measure', False, 'MEASURE (\\(n,s). strlen s - n)'),
  ('compiler', 'find_num'):
    ('new_definition', False, ''),
  ('compiler', 'find_str'):
    ('prim_rec', False, ''),
  ('compiler', 'find_strs'):
    ('prim_rec', False, ''),
  ('compiler', 'format_compiler_result'):
    ('new_recursive_definition', False, ''),
  ('compiler', 'get_err_str'):
    ('new_recursive_definition', False, ''),
  ('compiler', 'get_nth_line'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x0)'),
  ('compiler', 'has_help_flag'):
    ('new_definition', False, ''),
  ('compiler', 'has_pancake_flag'):
    ('new_definition', False, ''),
  ('compiler', 'has_version_flag'):
    ('new_definition', False, ''),
  ('compiler', 'is_error_msg'):
    ('new_definition', False, ''),
  ('compiler', 'locs_to_string'):
    ('new_definition', False, ''),
  ('compiler', 'pancake_backend_conf'):
    ('new_definition', False, ''),
  ('compiler', 'parse_bool'):
    ('new_definition', False, ''),
  ('compiler', 'parse_bvl_conf'):
    ('new_definition', False, ''),
  ('compiler', 'parse_clos_conf'):
    ('new_definition', False, ''),
  ('compiler', 'parse_cml_input'):
    ('new_definition', False, ''),
  ('compiler', 'parse_data_conf'):
    ('new_definition', False, ''),
  ('compiler', 'parse_gc'):
    ('new_definition', False, ''),
  ('compiler', 'parse_lab_conf'):
    ('new_definition', False, ''),
  ('compiler', 'parse_num'):
    ('new_definition', False, ''),
  ('compiler', 'parse_num_list'):
    ('prim_rec', False, ''),
  ('compiler', 'parse_nums'):
    ('new_definition', False, ''),
  ('compiler', 'parse_sexp_input'):
    ('new_definition', False, ''),
  ('compiler', 'parse_stack_conf'):
    ('new_definition', False, ''),
  ('compiler', 'parse_tap_conf'):
    ('new_definition', False, ''),
  ('compiler', 'parse_target_32'):
    ('new_definition', False, ''),
  ('compiler', 'parse_target_64'):
    ('new_definition', False, ''),
  ('compiler', 'parse_top_config'):
    ('new_definition', False, ''),
  ('compiler', 'parse_wtw_conf'):
    ('new_definition', False, ''),
  ('compiler', 'print_option'):
    ('new_definition', False, ''),
  ('compiler', 'safe_substring'):
    ('new_definition', False, ''),
  ('compilerProof', 'compilerProof_is_safe_for_space'):
    ('new_definition', False, ''),
  ('compilerProof', 'compilerProof_read_limits'):
    ('new_definition', False, ''),
  ('compilerProof', 'config_ok'):
    ('new_definition', False, ''),
  ('compilerProof', 'initial_condition'):
    ('new_definition', False, ''),
  ('copying_gc', 'copying_gc_gc_inv'):
    ('new_definition', False, ''),
  ('copying_gc', 'copying_gc_gc_move'):
    ('define_single', False, ''),
  ('copying_gc', 'copying_gc_gc_move_list'):
    ('measure', True, ''),
  ('copying_gc', 'copying_gc_gc_move_loop'):
    ('measure', True, ''),
  ('copying_gc', 'full_gc'):
    ('new_definition', False, ''),
  ('dataLang', 'mk_ticks'):
    ('new_definition', False, ''),
  ('dataLang', 'op_requires_names'):
    ('new_definition', False, ''),
  ('dataLang', 'op_space_reset'):
    ('new_definition', False, ''),
  ('dataProps', 'approx_of'):
    ('measure', True, ''),
  ('dataProps', 'cc_co_only_diff'):
    ('new_definition', False, ''),
  ('dataProps', 'dataProps_get_code_labels'):
    ('measure', False, 'MEASURE (\\x0. dataLang_prog_size x0)'),
  ('dataProps', 'dataProps_good_code_labels'):
    ('new_definition', False, ''),
  ('dataProps', 'locals_ok'):
    ('new_definition', False, ''),
  ('dataProps', 'same_stack_size'):
    ('new_definition', False, ''),
  ('dataProps', 'stack_frame_size_rel'):
    ('new_definition', False, ''),
  ('dataProps', 'var_corr'):
    ('new_definition', False, ''),
  ('dataProps', 'zero_limits'):
    ('new_definition', False, ''),
  ('dataSem', 'add_space'):
    ('new_definition', False, ''),
  ('dataSem', 'allowed_op'):
    ('new_definition', False, ''),
  ('dataSem', 'arch_size'):
    ('new_definition', False, ''),
  ('dataSem', 'bignum_digits'):
    ('measure', False, 'MEASURE (\\(x0,x1). (\\n. n) x1)'),
  ('dataSem', 'bignum_size'):
    ('new_definition', False, ''),
  ('dataSem', 'check_lim'):
    ('new_definition', False, ''),
  ('dataSem', 'check_res'):
    ('new_definition', False, ''),
  ('dataSem', 'compute_limits'):
    ('new_definition', False, ''),
  ('dataSem', 'consume_space'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_Boolv'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_Unit'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_bad_thunk_update'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_call_env'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_cut_env'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_cut_state'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_cut_state_opt'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_dec_clock'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_dest_thunk'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_do_app'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_do_app_aux'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_do_build'):
    ('prim_rec', False, ''),
  ('dataSem', 'dataSem_do_build_const'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_do_eq'):
    ('measure', False, 'MEASURE (sum_measure  (\\(x0,x1,x2).       spt_size (bvlSem_ref_size (\\x. 0)) x0 +       dataSem_v_size x1 +       dataSem_v_size x2) (\\(x0,x1,x2).      spt_size (bvlSem_ref_size (\\x. 0)) x0 +      dataSem_v_size1 x1 +      dataSem_v_size1 x2))'),
  ('dataSem', 'dataSem_do_install'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_do_int_app'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_do_part'):
    ('new_recursive_definition', False, ''),
  ('dataSem', 'dataSem_do_word_app'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_evaluate'):
    ('measure', False, ''),
  ('dataSem', 'dataSem_finalise_cons'):
    ('measure', True, ''),
  ('dataSem', 'dataSem_find_code'):
    ('new_recursive_definition', False, ''),
  ('dataSem', 'dataSem_fix_clock'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_flush_state'):
    ('define_single', False, ''),
  ('dataSem', 'dataSem_get_var'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_get_vars'):
    ('prim_rec', False, ''),
  ('dataSem', 'dataSem_initial_state'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_isClos'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_jump_exc'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_list_to_v'):
    ('prim_rec', False, ''),
  ('dataSem', 'dataSem_pop_env'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_push_env'):
    ('define_single', False, ''),
  ('dataSem', 'dataSem_semantics'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_set_var'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_set_vars'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_v_to_bytes'):
    ('new_definition', False, ''),
  ('dataSem', 'dataSem_v_to_list'):
    ('measure', False, 'MEASURE (\\x0. dataSem_v_size x0)'),
  ('dataSem', 'dataSem_v_to_words'):
    ('new_definition', False, ''),
  ('dataSem', 'data_lang_safe_for_space'):
    ('new_definition', False, ''),
  ('dataSem', 'dest_Boolv'):
    ('new_definition', False, ''),
  ('dataSem', 'do_lim_safe'):
    ('new_definition', False, ''),
  ('dataSem', 'do_space'):
    ('new_definition', False, ''),
  ('dataSem', 'do_stack'):
    ('new_definition', False, ''),
  ('dataSem', 'eq_code_stack_max'):
    ('new_definition', False, ''),
  ('dataSem', 'evaluate_peak'):
    ('new_definition', False, ''),
  ('dataSem', 'evaluate_safe'):
    ('new_definition', False, ''),
  ('dataSem', 'extract_stack'):
    ('new_recursive_definition', False, ''),
  ('dataSem', 'global_to_vs'):
    ('new_recursive_definition', False, ''),
  ('dataSem', 'install_sfs'):
    ('new_definition', False, ''),
  ('dataSem', 'isBool'):
    ('new_definition', False, ''),
  ('dataSem', 'lim_safe'):
    ('new_definition', False, ''),
  ('dataSem', 'lim_safe_part'):
    ('new_recursive_definition', False, ''),
  ('dataSem', 'no_thunks_in_refs'):
    ('new_definition', False, ''),
  ('dataSem', 'size_of'):
    ('measure', False, ''),
  ('dataSem', 'size_of_heap'):
    ('new_definition', False, ''),
  ('dataSem', 'size_of_heap_args'):
    ('new_definition', False, ''),
  ('dataSem', 'size_of_stack'):
    ('new_definition', False, ''),
  ('dataSem', 'size_of_stack_frame'):
    ('new_recursive_definition', False, ''),
  ('dataSem', 'small_num'):
    ('new_definition', False, ''),
  ('dataSem', 'space_consumed'):
    ('new_definition', False, ''),
  ('dataSem', 'stack_consumed'):
    ('new_definition', False, ''),
  ('dataSem', 'stack_to_vs'):
    ('new_definition', False, ''),
  ('dataSem', 'vb_size'):
    ('measure', False, 'MEASURE (\\x0. dataSem_v_size x0)'),
  ('dataSem', 'vs_depth'):
    ('measure', False, 'MEASURE (sum_measure (\\x0. dataSem_v_size x0) (\\x0. dataSem_v_size1 x0))'),
  ('dataSem', 'with_fresh_ts'):
    ('new_definition', False, ''),
  ('data_live', 'data_live_compile'):
    ('cases', False, ''),
  ('data_live', 'data_live_is_pure'):
    ('new_definition', False, ''),
  ('data_liveProof', 'data_liveProof_state_rel'):
    ('new_definition', False, ''),
  ('data_simp', 'pSeq'):
    ('new_definition', False, ''),
  ('data_simp', 'simp'):
    ('match', False, ''),
  ('data_space', 'data_space_compile'):
    ('new_definition', False, ''),
  ('data_space', 'data_space_num_size'):
    ('measure', False, 'MEASURE (\\x0. (\\n. n) x0)'),
  ('data_space', 'op_space_req'):
    ('new_definition', False, ''),
  ('data_space', 'pMakeSpace'):
    ('new_recursive_definition', False, ''),
  ('data_space', 'part_space_req'):
    ('new_recursive_definition', False, ''),
  ('data_space', 'space'):
    ('match', False, ''),
  ('data_to_word', 'AddNumSize'):
    ('new_definition', False, ''),
  ('data_to_word', 'Add_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'Add_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'AllocVar'):
    ('new_definition', False, ''),
  ('data_to_word', 'AnyArith_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'AnyArith_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'AnyHeader'):
    ('new_definition', False, ''),
  ('data_to_word', 'AppendLenLoop_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'AppendLenLoop_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'AppendMainLoop_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'AppendMainLoop_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'Append_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'Append_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'AssignCmp'):
    ('new_recursive_definition', False, ''),
  ('data_to_word', 'BignumHalt'):
    ('new_definition', False, ''),
  ('data_to_word', 'Bignum_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'ByteCopyAdd_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'ByteCopyAdd_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'ByteCopyNew_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'ByteCopyNew_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'ByteCopySub_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'ByteCopySub_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'ByteCopy_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'ByteCopy_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'Compare1_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'Compare1_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'Compare_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'Compare_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'Div_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'Div_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'Dummy_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'Equal1_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'Equal1_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'Equal_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'Equal_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'FromList1_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'FromList1_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'FromList_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'FromList_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'GiveUp'):
    ('new_definition', False, ''),
  ('data_to_word', 'InstallCode_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'InstallCode_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'InstallData_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'InstallData_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'Install_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'Install_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'LoadBignum'):
    ('new_definition', False, ''),
  ('data_to_word', 'LoadWord64'):
    ('new_definition', False, ''),
  ('data_to_word', 'LongDiv1_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'LongDiv1_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'LongDiv_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'LongDiv_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'MakeBytes'):
    ('new_definition', False, ''),
  ('data_to_word', 'Make_ptr_bits_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'Maxout_bits_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'MemCopy_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'MemCopy_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'MemEqList'):
    ('prim_rec', False, ''),
  ('data_to_word', 'Mod_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'Mod_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'Mul_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'Mul_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'RefArray_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'RefArray_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'RefByte_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'RefByte_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'Replicate_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'Replicate_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'SetBool'):
    ('new_definition', False, ''),
  ('data_to_word', 'ShiftVar'):
    ('new_definition', False, ''),
  ('data_to_word', 'SilentFFI'):
    ('new_definition', False, ''),
  ('data_to_word', 'SmallLsr'):
    ('new_definition', False, ''),
  ('data_to_word', 'Smallnum'):
    ('new_definition', False, ''),
  ('data_to_word', 'StoreAnyConsts'):
    ('measure', True, ''),
  ('data_to_word', 'StoreEach'):
    ('prim_rec', False, ''),
  ('data_to_word', 'StringCmpLoop_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'StringCmpLoop_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'Sub_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'Sub_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'Unused_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'WordOp64_on_32'):
    ('new_definition', False, ''),
  ('data_to_word', 'WordShift64_on_32'):
    ('new_definition', False, ''),
  ('data_to_word', 'WriteLastByte_aux'):
    ('new_definition', False, ''),
  ('data_to_word', 'WriteLastBytes'):
    ('new_definition', False, ''),
  ('data_to_word', 'WriteWord32_on_32'):
    ('new_definition', False, ''),
  ('data_to_word', 'WriteWord64'):
    ('new_definition', False, ''),
  ('data_to_word', 'WriteWord64_on_32'):
    ('new_definition', False, ''),
  ('data_to_word', 'XorLoop_code'):
    ('new_definition', False, ''),
  ('data_to_word', 'XorLoop_location'):
    ('new_definition', False, ''),
  ('data_to_word', 'adjust_set'):
    ('new_definition', False, ''),
  ('data_to_word', 'adjust_sets'):
    ('new_definition', False, ''),
  ('data_to_word', 'adjust_var'):
    ('new_definition', False, ''),
  ('data_to_word', 'all_ones'):
    ('new_definition', False, ''),
  ('data_to_word', 'arg3'):
    ('new_definition', False, ''),
  ('data_to_word', 'arg4'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_Add'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_AllocThunk'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_BoolNot'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_BoolTest'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_BoundsCheckArray'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_BoundsCheckBlock'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_BoundsCheckByte'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_Build'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_ConfigGC'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_Cons'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_ConsExtend'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_Const'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_CopyByte'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_DerefByte'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_Div'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_El'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_ElemAt'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_Equal'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_EqualConst'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_FFI'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_FP_bop'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_FP_cmp'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_FP_top'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_FP_uop'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_FinaliseCons'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_FromList'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_Global'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_Install'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_LenEq'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_Length'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_LengthBlock'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_LengthByte'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_Less'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_LessConstSmall'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_LessEq'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_ListAppend'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_Mod'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_Mult'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_MutCons'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_Ref'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_RefArray'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_RefByte'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_SetGlobal'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_SetGlobalsPtr'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_StringCmp'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_Sub'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_TagEq'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_TagLenEq'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_Update'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_UpdateByte'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_UpdateThunk'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_WordFromInt'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_WordFromWord'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_WordOpW64'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_WordOpW8'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_WordShiftW64'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_WordShiftW8'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_WordTest'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_WordToInt'):
    ('new_definition', False, ''),
  ('data_to_word', 'assign_XorByte'):
    ('new_definition', False, ''),
  ('data_to_word', 'byte_len'):
    ('new_definition', False, ''),
  ('data_to_word', 'compile_0'):
    ('new_definition', False, ''),
  ('data_to_word', 'conf_ok'):
    ('new_definition', False, ''),
  ('data_to_word', 'const_parts_to_words'):
    ('new_definition', False, ''),
  ('data_to_word', 'data_to_word_Unit'):
    ('new_definition', False, ''),
  ('data_to_word', 'data_to_word_arg1'):
    ('new_definition', False, ''),
  ('data_to_word', 'data_to_word_arg2'):
    ('new_definition', False, ''),
  ('data_to_word', 'data_to_word_assign'):
    ('new_definition', False, ''),
  ('data_to_word', 'data_to_word_comp'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). dataLang_prog_size x3)'),
  ('data_to_word', 'data_to_word_compile'):
    ('new_definition', False, ''),
  ('data_to_word', 'data_to_word_compile_part'):
    ('new_definition', False, ''),
  ('data_to_word', 'data_to_word_get_names'):
    ('new_recursive_definition', False, ''),
  ('data_to_word', 'data_to_word_list_Seq'):
    ('measure', False, 'MEASURE (\\x0. list_size (wordLang_prog_size (\\x. 0)) x0)'),
  ('data_to_word', 'data_to_word_stub_names'):
    ('new_definition', False, ''),
  ('data_to_word', 'data_to_word_stubs'):
    ('new_definition', False, ''),
  ('data_to_word', 'encode_header'):
    ('new_definition', False, ''),
  ('data_to_word', 'force_thunk'):
    ('new_definition', False, ''),
  ('data_to_word', 'fp_bop_inst'):
    ('new_definition', False, ''),
  ('data_to_word', 'fp_cmp_inst'):
    ('new_recursive_definition', False, ''),
  ('data_to_word', 'fp_top_inst'):
    ('new_definition', False, ''),
  ('data_to_word', 'fp_uop_inst'):
    ('new_definition', False, ''),
  ('data_to_word', 'getWords'):
    ('prim_rec', False, ''),
  ('data_to_word', 'get_Word'):
    ('new_definition', False, ''),
  ('data_to_word', 'get_gen_size'):
    ('new_recursive_definition', False, ''),
  ('data_to_word', 'get_lowerbits'):
    ('new_definition', False, ''),
  ('data_to_word', 'lookup_mem'):
    ('new_definition', False, ''),
  ('data_to_word', 'lookup_word_op'):
    ('new_recursive_definition', False, ''),
  ('data_to_word', 'make_byte_header'):
    ('new_definition', False, ''),
  ('data_to_word', 'make_cons_ptr'):
    ('new_definition', False, ''),
  ('data_to_word', 'make_header'):
    ('new_definition', False, ''),
  ('data_to_word', 'make_ptr'):
    ('new_definition', False, ''),
  ('data_to_word', 'max_heap_limit'):
    ('new_definition', False, ''),
  ('data_to_word', 'maxout_bits'):
    ('new_definition', False, ''),
  ('data_to_word', 'part_to_words'):
    ('new_recursive_definition', False, ''),
  ('data_to_word', 'parts_to_words'):
    ('prim_rec', False, ''),
  ('data_to_word', 'ptr_bits'):
    ('new_definition', False, ''),
  ('data_to_word', 'real_addr'):
    ('new_definition', False, ''),
  ('data_to_word', 'real_byte_offset'):
    ('new_definition', False, ''),
  ('data_to_word', 'real_offset'):
    ('new_definition', False, ''),
  ('data_to_word', 'shift_length'):
    ('new_definition', False, ''),
  ('data_to_word', 'small_int'):
    ('new_definition', False, ''),
  ('data_to_word', 'small_shift_length'):
    ('new_definition', False, ''),
  ('data_to_word', 'structure_le'):
    ('measure', False, 'MEASURE (\\(x0,x1). call_tree_size x0 + call_tree_size x1)'),
  ('data_to_word', 'tag_mask'):
    ('new_definition', False, ''),
  ('data_to_word', 'write_bytes'):
    ('prim_rec', False, ''),
  ('data_to_wordProof', 'get_limits'):
    ('new_definition', False, ''),
  ('data_to_wordProof', 'state_rel_ext'):
    ('new_definition', False, ''),
  ('data_to_word_assignProof', 'data_to_word_assignProof_STOP'):
    ('new_definition', False, ''),
  ('data_to_word_assignProof', 'is_env'):
    ('new_definition', False, ''),
  ('data_to_word_assignProof', 'memcopy'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4). (\\n. n) x0)'),
  ('data_to_word_assignProof', 'sane_locals_size'):
    ('new_definition', False, ''),
  ('data_to_word_assignProof', 'w2w_upper'):
    ('new_definition', False, ''),
  ('data_to_word_bignumProof', 'Arith_code'):
    ('new_definition', False, ''),
  ('data_to_word_bignumProof', 'Arith_location'):
    ('new_definition', False, ''),
  ('data_to_word_bignumProof', 'data_to_word_bignumProof_int_op'):
    ('new_definition', False, ''),
  ('data_to_word_bignumProof', 'get_iop'):
    ('new_definition', False, ''),
  ('data_to_word_gcProof', 'alloc_size'):
    ('new_definition', False, ''),
  ('data_to_word_gcProof', 'can_select'):
    ('new_definition', False, ''),
  ('data_to_word_gcProof', 'code_oracle_rel'):
    ('new_definition', False, ''),
  ('data_to_word_gcProof', 'contains_loc'):
    ('define_single', False, ''),
  ('data_to_word_gcProof', 'cut_locals'):
    ('new_definition', False, ''),
  ('data_to_word_gcProof', 'data_to_word_gcProof_code_rel'):
    ('new_definition', False, ''),
  ('data_to_word_gcProof', 'data_to_word_gcProof_inc_clock'):
    ('new_definition', False, ''),
  ('data_to_word_gcProof', 'data_to_word_gcProof_stack_rel'):
    ('guess', False, ''),
  ('data_to_word_gcProof', 'data_to_word_gcProof_state_rel'):
    ('', False, ''),
  ('data_to_word_gcProof', 'do_partial'):
    ('new_definition', False, ''),
  ('data_to_word_gcProof', 'ends_with_refs'):
    ('new_definition', False, ''),
  ('data_to_word_gcProof', 'flat'):
    ('measure', False, 'MEASURE (\\(x0,x1).      list_size dataSem_stack_size x0 +      list_size (stack_frame_size (\\x. 0)) x1)'),
  ('data_to_word_gcProof', 'init_store_ok'):
    ('new_definition', False, ''),
  ('data_to_word_gcProof', 'is_Ref'):
    ('new_definition', False, ''),
  ('data_to_word_gcProof', 'join_env'):
    ('new_definition', False, ''),
  ('data_to_word_gcProof', 'join_env_locals'):
    ('new_definition', False, ''),
  ('data_to_word_gcProof', 'len_inv'):
    ('new_definition', False, ''),
  ('data_to_word_gcProof', 'limits_inv'):
    ('new_definition', False, ''),
  ('data_to_word_gcProof', 'loc_merge'):
    ('measure', False, 'MEASURE (\\(x0,x1).      list_size (word_loc_size (\\x. 0)) x0 +      list_size (word_loc_size (\\x. 0)) x1)'),
  ('data_to_word_gcProof', 'loc_ok'):
    ('new_definition', False, ''),
  ('data_to_word_gcProof', 'mk_loc'):
    ('define_single', False, ''),
  ('data_to_word_gcProof', 'muttag_header'):
    ('', False, ''),
  ('data_to_word_gcProof', 'partial_len_inv'):
    ('new_definition', False, ''),
  ('data_to_word_gcProof', 'the_global'):
    ('new_definition', False, ''),
  ('data_to_word_gcProof', 'word_heap_parts'):
    ('', False, ''),
  ('data_to_word_memoryProof', 'Bignum'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'BlockNil'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'BlockRep'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'Bytes'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'RefBlock'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'ThunkBlock'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'Word64Rep'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'abs_ml_inv'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'all_reachable_from_roots'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'all_ts'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'all_vs'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'bc_ref_inv'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'bc_stack_ref_inv'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'be_ok'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'blocks_unique'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'data_to_word_memoryProof_isRef'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'data_up_to'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'evaluated_thunk_ptr'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'find_ref'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'gc_inline'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'gc_inline_related'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'gc_kind_inv'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'gc_related_roots_heap'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'gen_start_ok'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'gen_state_ok'):
    ('define_single', False, ''),
  ('data_to_word_memoryProof', 'get_refs'):
    ('nested', False, ''),
  ('data_to_word_memoryProof', 'has_gen'):
    ('define_single', False, ''),
  ('data_to_word_memoryProof', 'isMutTag'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'make_gc_conf'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'reachable_refs'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'ref_edge'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'ref_ptr_annot'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'reset_gens'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'unused_space_inv'):
    ('new_definition', False, ''),
  ('data_to_word_memoryProof', 'v_all_ts'):
    ('measure', False, 'MEASURE dataSem_v_size'),
  ('data_to_word_memoryProof', 'v_all_vs'):
    ('measure', False, 'MEASURE (\\x0. dataSem_v_size1 x0)'),
  ('data_to_word_memoryProof', 'v_inv'):
    ('new_definition', False, ''),
  ('db_vars', 'db_to_set'):
    ('new_definition', False, ''),
  ('db_vars', 'db_to_set_acc'):
    ('prim_rec', False, ''),
  ('db_vars', 'has_var'):
    ('prim_rec', False, ''),
  ('db_vars', 'list_mk_Union'):
    ('prim_rec', False, ''),
  ('db_vars', 'mk_Union'):
    ('new_definition', False, ''),
  ('db_vars', 'vars_flatten'):
    ('new_definition', False, ''),
  ('db_vars', 'vars_from_list'):
    ('new_definition', False, ''),
  ('db_vars', 'vars_to_list'):
    ('new_definition', False, ''),
  ('displayLang', 'display_to_json'):
    ('nested', False, ''),
  ('displayLang', 'display_to_str_tree'):
    ('prim_rec', False, ''),
  ('displayLang', 'trace_to_json'):
    ('prim_rec', False, ''),
  ('envRel', 'convert_env'):
    ('new_definition', False, ''),
  ('envRel', 'convert_t'):
    ('nested', False, ''),
  ('envRel', 'envRel_env_rel'):
    ('new_definition', False, ''),
  ('envRel', 'env_rel_complete'):
    ('new_definition', False, ''),
  ('envRel', 'env_rel_sound'):
    ('new_definition', False, ''),
  ('envRel', 'ienv_to_tenv'):
    ('new_definition', False, ''),
  ('envRel', 'tenv_to_ienv'):
    ('new_definition', False, ''),
  ('envRel', 'tscheme_approx'):
    ('new_definition', False, ''),
  ('evaluate', 'do_eval_res'):
    ('new_definition', False, ''),
  ('evaluate', 'evaluate'):
    ('measure', False, ''),
  ('evaluate', 'evaluate_dec_clock'):
    ('new_definition', False, ''),
  ('evaluate', 'evaluate_fix_clock'):
    ('new_definition', False, ''),
  ('evaluate', 'list_result'):
    ('new_recursive_definition', False, ''),
  ('evaluate', 'sing_env'):
    ('new_definition', False, ''),
  ('evaluateProps', 'adj_clock'):
    ('new_definition', False, ''),
  ('evaluateProps', 'call_FFI_rel'):
    ('new_definition', False, ''),
  ('evaluateProps', 'dest_IO_event'):
    ('define_single', False, ''),
  ('evaluateProps', 'io_events_mono'):
    ('new_definition', False, ''),
  ('evaluateProps', 'is_clock_io_mono'):
    ('new_definition', False, ''),
  ('export', 'all_bytes'):
    ('new_definition', False, ''),
  ('export', 'byte_to_string'):
    ('new_definition', False, ''),
  ('export', 'code_buffer'):
    ('new_definition', False, ''),
  ('export', 'comm_strlit'):
    ('new_definition', False, ''),
  ('export', 'comma_cat'):
    ('guess', False, ''),
  ('export', 'data_buffer'):
    ('new_definition', False, ''),
  ('export', 'data_section'):
    ('new_definition', False, ''),
  ('export', 'emit_symbol'):
    ('new_definition', False, ''),
  ('export', 'emit_symbols'):
    ('new_definition', False, ''),
  ('export', 'escape_sym_char'):
    ('new_definition', False, ''),
  ('export', 'get_sym_label'):
    ('new_definition', False, ''),
  ('export', 'get_sym_labels'):
    ('new_definition', False, ''),
  ('export', 'newl_strlit'):
    ('new_definition', False, ''),
  ('export', 'preamble'):
    ('new_definition', False, ''),
  ('export', 'split16'):
    ('measure', True, ''),
  ('export', 'word_to_string'):
    ('new_definition', False, ''),
  ('export', 'words_line'):
    ('new_definition', False, ''),
  ('export_ag32', 'ag32_export'):
    ('new_definition', False, ''),
  ('export_arm7', 'arm7_export'):
    ('new_definition', False, ''),
  ('export_arm7', 'export_arm7_export_func'):
    ('new_definition', False, ''),
  ('export_arm7', 'export_arm7_export_funcs'):
    ('new_definition', False, ''),
  ('export_arm7', 'export_arm7_ffi_asm'):
    ('prim_rec', False, ''),
  ('export_arm7', 'export_arm7_startup'):
    ('new_definition', False, ''),
  ('export_arm8', 'arm8_export'):
    ('new_definition', False, ''),
  ('export_arm8', 'export_arm8_export_func'):
    ('new_definition', False, ''),
  ('export_arm8', 'export_arm8_export_funcs'):
    ('new_definition', False, ''),
  ('export_arm8', 'export_arm8_ffi_asm'):
    ('prim_rec', False, ''),
  ('export_arm8', 'export_arm8_startup'):
    ('new_definition', False, ''),
  ('export_mips', 'export_mips_export_func'):
    ('new_definition', False, ''),
  ('export_mips', 'export_mips_export_funcs'):
    ('new_definition', False, ''),
  ('export_mips', 'export_mips_ffi_asm'):
    ('prim_rec', False, ''),
  ('export_mips', 'export_mips_startup'):
    ('new_definition', False, ''),
  ('export_mips', 'mips_export'):
    ('new_definition', False, ''),
  ('export_riscv', 'export_riscv_export_func'):
    ('new_definition', False, ''),
  ('export_riscv', 'export_riscv_export_funcs'):
    ('new_definition', False, ''),
  ('export_riscv', 'export_riscv_ffi_asm'):
    ('prim_rec', False, ''),
  ('export_riscv', 'export_riscv_startup'):
    ('new_definition', False, ''),
  ('export_riscv', 'riscv_export'):
    ('new_definition', False, ''),
  ('export_x64', 'export_x64_export_func'):
    ('new_definition', False, ''),
  ('export_x64', 'export_x64_export_funcs'):
    ('new_definition', False, ''),
  ('export_x64', 'export_x64_ffi_asm'):
    ('prim_rec', False, ''),
  ('export_x64', 'export_x64_startup'):
    ('new_definition', False, ''),
  ('export_x64', 'windows_ffi_asm'):
    ('prim_rec', False, ''),
  ('export_x64', 'x64_export'):
    ('new_definition', False, ''),
  ('ffi', 'call_FFI'):
    ('new_definition', False, ''),
  ('ffi', 'initial_ffi_state'):
    ('new_definition', False, ''),
  ('ffi', 'trace_oracle'):
    ('new_definition', False, ''),
  ('flatLang', 'SmartIf'):
    ('new_definition', False, ''),
  ('flatLang', 'bool_id'):
    ('new_definition', False, ''),
  ('flatLang', 'flatLang_Bool'):
    ('new_definition', False, ''),
  ('flatLang', 'flatLang_pat_bindings'):
    ('prim_rec', False, ''),
  ('flatProps', 'bind_locals_list'):
    ('new_definition', False, ''),
  ('flatProps', 'flatProps_esgc_free'):
    ('measure', False, 'MEASURE flatLang_exp_size'),
  ('flatProps', 'flatProps_eval_sim'):
    ('new_definition', False, ''),
  ('flatProps', 'flatProps_evaluate_match'):
    ('new_definition', False, ''),
  ('flatProps', 'flatProps_mk_flat_install_conf'):
    ('new_definition', False, ''),
  ('flatProps', 'flatProps_op_gbag'):
    ('new_definition', False, ''),
  ('flatProps', 'flatProps_set_globals'):
    ('measure', True, ''),
  ('flatProps', 'flatProps_simple_state_rel'):
    ('new_definition', False, ''),
  ('flatProps', 'flatProps_simple_val_rel'):
    ('new_definition', False, ''),
  ('flatProps', 'flatProps_store_v_vs'):
    ('new_recursive_definition', False, ''),
  ('flatProps', 'isClosure'):
    ('new_definition', False, ''),
  ('flatProps', 'no_Mat'):
    ('measure', False, ''),
  ('flatProps', 'no_Mat_decs'):
    ('prim_rec', False, ''),
  ('flatProps', 'result_vs'):
    ('new_definition', False, ''),
  ('flatProps', 'simple_basic_val_rel'):
    ('new_recursive_definition', False, ''),
  ('flatProps', 'v_container_xs'):
    ('new_recursive_definition', False, ''),
  ('flatSem', 'Unitv'):
    ('new_definition', False, ''),
  ('flatSem', 'dec_alt_size'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_AppUnit'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_Boolv'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_bad_thunk_update'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_bind_exn_v'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_build_rec_env'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_check_type'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_chr_exn_v'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_ctor_same_type'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_dec_clock'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_dest_Litv'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_dest_thunk'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_div_exn_v'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_do_app'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_do_eq'):
    ('measure', False, ''),
  ('flatSem', 'flatSem_do_eval'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_do_if'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_do_opapp'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_do_test'):
    ('new_recursive_definition', False, ''),
  ('flatSem', 'flatSem_evaluate'):
    ('measure', False, ''),
  ('flatSem', 'flatSem_exp_alt_size'):
    ('prim_rec', False, ''),
  ('flatSem', 'flatSem_fix_clock'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_initial_state'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_list_to_v'):
    ('prim_rec', False, ''),
  ('flatSem', 'flatSem_pmatch'):
    ('measure', False, ''),
  ('flatSem', 'flatSem_semantics'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_the_Litv_Float64'):
    ('define_single', False, ''),
  ('flatSem', 'flatSem_update_thunk'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_v_to_bytes'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_v_to_char_list'):
    ('measure', False, 'MEASURE (\\x0. flatSem_v_size x0)'),
  ('flatSem', 'flatSem_v_to_list'):
    ('measure', False, 'MEASURE (\\x0. flatSem_v_size x0)'),
  ('flatSem', 'flatSem_v_to_words'):
    ('new_definition', False, ''),
  ('flatSem', 'flatSem_vs_to_string'):
    ('measure', False, 'MEASURE (\\x0. flatSem_v_size2 x0)'),
  ('flatSem', 'flat_to_v'):
    ('new_definition', False, ''),
  ('flatSem', 'list_id'):
    ('new_definition', False, ''),
  ('flatSem', 'pmatch_rows'):
    ('prim_rec', False, ''),
  ('flatSem', 'subscript_exn_v'):
    ('new_definition', False, ''),
  ('flatSem', 'v_to_flat'):
    ('new_definition', False, ''),
  ('flat_elim', 'analyse_code'):
    ('prim_rec', False, ''),
  ('flat_elim', 'analyse_exp'):
    ('new_definition', False, ''),
  ('flat_elim', 'code_analysis_union'):
    ('new_definition', False, ''),
  ('flat_elim', 'dest_GlobalVarInit'):
    ('new_definition', False, ''),
  ('flat_elim', 'dest_GlobalVarLookup'):
    ('new_definition', False, ''),
  ('flat_elim', 'find_loc'):
    ('measure', False, ''),
  ('flat_elim', 'find_lookups'):
    ('measure', False, ''),
  ('flat_elim', 'flat_elim_is_pure'):
    ('measure', False, 'MEASURE (\\e. flatLang_exp_size e)'),
  ('flat_elim', 'has_Eval'):
    ('nested', False, ''),
  ('flat_elim', 'has_Eval_dec'):
    ('new_definition', False, ''),
  ('flat_elim', 'is_hidden'):
    ('measure', False, 'MEASURE (\\x0. flatLang_exp_size x0)'),
  ('flat_elim', 'keep'):
    ('new_definition', False, ''),
  ('flat_elim', 'remove_flat_prog'):
    ('new_definition', False, ''),
  ('flat_elim', 'remove_unreachable'):
    ('new_definition', False, ''),
  ('flat_elim', 'total_pat'):
    ('measure', True, ''),
  ('flat_elimProof', 'decs_closed'):
    ('new_definition', False, ''),
  ('flat_elimProof', 'find_env_globals'):
    ('new_definition', False, ''),
  ('flat_elimProof', 'find_refs_globals'):
    ('measure', False, 'MEASURE (\\x0. list_size (store_v_size flatSem_v_size) x0)'),
  ('flat_elimProof', 'find_result_globals'):
    ('new_definition', False, ''),
  ('flat_elimProof', 'find_sem_prim_res_globals'):
    ('new_recursive_definition', False, ''),
  ('flat_elimProof', 'find_v_globals'):
    ('measure', True, ''),
  ('flat_elimProof', 'flat_state_rel'):
    ('new_definition', False, ''),
  ('flat_elimProof', 'globals_rel'):
    ('new_definition', False, ''),
  ('flat_elimProof', 'v_has_Eval'):
    ('measure', True, ''),
  ('flat_pattern', 'compile_dec'):
    ('new_definition', False, ''),
  ('flat_pattern', 'compile_pat_bindings'):
    ('measure', False, ''),
  ('flat_pattern', 'compile_pat_rhs'):
    ('new_definition', False, ''),
  ('flat_pattern', 'compile_pats'):
    ('new_definition', False, ''),
  ('flat_pattern', 'dec_name_to_num'):
    ('new_definition', False, ''),
  ('flat_pattern', 'decode_dtree'):
    ('match', False, ''),
  ('flat_pattern', 'decode_guard'):
    ('prim_rec', False, ''),
  ('flat_pattern', 'decode_pos'):
    ('prim_rec', False, ''),
  ('flat_pattern', 'enc_num_to_name'):
    ('new_definition', False, ''),
  ('flat_pattern', 'enc_num_to_name_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1). (\\n. n) x0)'),
  ('flat_pattern', 'encode_pat'):
    ('measure', False, 'MEASURE (\\x0. flatLang_pat_size x0)'),
  ('flat_pattern', 'flat_pattern_compile_exp'):
    ('measure', False, ''),
  ('flat_pattern', 'flat_pattern_decode_test'):
    ('new_recursive_definition', False, ''),
  ('flat_pattern', 'flat_pattern_init_config'):
    ('new_definition', False, ''),
  ('flat_pattern', 'max_dec_name'):
    ('prim_rec', False, ''),
  ('flat_pattern', 'naive_pattern_match'):
    ('measure', True, ''),
  ('flat_pattern', 'naive_pattern_matches'):
    ('prim_rec', False, ''),
  ('flat_pattern', 'op_sets_globals'):
    ('new_definition', False, ''),
  ('flat_pattern', 'simp_guard'):
    ('match', False, ''),
  ('flat_pattern', 'sum_string_ords'):
    ('measure', False, 'MEASURE (\\(i,str). strlen str - i)'),
  ('flat_patternProof', 'ALOOKUP_rel'):
    ('new_definition', False, ''),
  ('flat_patternProof', 'encode_refs'):
    ('new_definition', False, ''),
  ('flat_patternProof', 'encode_val'):
    ('measure', False, 'MEASURE flatSem_v_size'),
  ('flat_patternProof', 'flat_patternProof_state_rel'):
    ('new_definition', False, ''),
  ('flat_patternProof', 'install_conf_rel'):
    ('new_definition', False, ''),
  ('flat_patternProof', 'match_rel'):
    ('new_definition', False, ''),
  ('flat_patternProof', 'pure_eval_to'):
    ('new_definition', False, ''),
  ('flat_to_clos', 'SmartCons'):
    ('new_definition', False, ''),
  ('flat_to_clos', 'compile_arith'):
    ('new_definition', False, ''),
  ('flat_to_clos', 'compile_lit'):
    ('new_definition', False, ''),
  ('flat_to_clos', 'dest_Constants'):
    ('prim_rec', False, ''),
  ('flat_to_clos', 'dest_nop'):
    ('new_definition', False, ''),
  ('flat_to_clos', 'dest_pat'):
    ('new_definition', False, ''),
  ('flat_to_clos', 'flat_to_clos_arg1'):
    ('new_definition', False, ''),
  ('flat_to_clos', 'flat_to_clos_arg2'):
    ('new_definition', False, ''),
  ('flat_to_clos', 'flat_to_clos_compile'):
    ('measure', False, ''),
  ('flat_to_clos', 'flat_to_clos_compile_decs'):
    ('prim_rec', False, ''),
  ('flat_to_clos', 'flat_to_clos_compile_op'):
    ('new_definition', False, ''),
  ('flat_to_clos', 'flat_to_clos_compile_prog'):
    ('new_definition', False, ''),
  ('flat_to_clos', 'flat_to_clos_dest_Constant'):
    ('new_definition', False, ''),
  ('flat_to_clos', 'inc_compile_decs'):
    ('new_definition', False, ''),
  ('flat_to_clos', 'join_strings'):
    ('new_definition', False, ''),
  ('flat_to_closProof', 'flat_to_closProof_state_rel'):
    ('new_definition', False, ''),
  ('flat_to_closProof', "inc_compile_decs'"):
    ('new_definition', False, ''),
  ('flat_to_closProof', "initial_state'"):
    ('new_definition', False, ''),
  ('flat_to_closProof', 'install_config_rel'):
    ('new_definition', False, ''),
  ('flat_to_closProof', "install_config_rel'"):
    ('new_definition', False, ''),
  ('flat_to_closProof', 'store_rel'):
    ('new_definition', False, ''),
  ('fmsp', 'fm2sp'):
    ('new_definition', False, ''),
  ('fmsp', 'sp2fm'):
    ('new_definition', False, ''),
  ('fpSem', 'fp_bop_comp'):
    ('new_definition', False, ''),
  ('fpSem', 'fp_cmp'):
    ('new_definition', False, ''),
  ('fpSem', 'fp_cmp_comp'):
    ('new_definition', False, ''),
  ('fpSem', 'fp_top_comp'):
    ('new_definition', False, ''),
  ('fpSem', 'fp_uop_comp'):
    ('new_definition', False, ''),
  ('fpSem', 'fpfma'):
    ('new_definition', False, ''),
  ('fromSexp', 'SEXSTR'):
    ('new_definition', False, ''),
  ('fromSexp', 'arithsexp'):
    ('new_recursive_definition', False, ''),
  ('fromSexp', 'decode_control'):
    ('measure', False, 'MEASURE (\\x0. list_size char_size x0)'),
  ('fromSexp', 'decode_prim_type'):
    ('new_definition', False, ''),
  ('fromSexp', 'decode_thunk_mode'):
    ('new_definition', False, ''),
  ('fromSexp', 'decsexp'):
    ('nested', False, ''),
  ('fromSexp', 'encode_control'):
    ('prim_rec', False, ''),
  ('fromSexp', 'encode_thunk_mode'):
    ('new_recursive_definition', False, ''),
  ('fromSexp', 'expsexp'):
    ('nested', False, ''),
  ('fromSexp', 'fromSexp_decode_test'):
    ('new_definition', False, ''),
  ('fromSexp', 'idsexp'):
    ('prim_rec', False, ''),
  ('fromSexp', 'listsexp'):
    ('new_definition', False, ''),
  ('fromSexp', 'litsexp'):
    ('new_recursive_definition', False, ''),
  ('fromSexp', 'locnsexp'):
    ('new_recursive_definition', False, ''),
  ('fromSexp', 'locssexp'):
    ('define_single', False, ''),
  ('fromSexp', 'logsexp'):
    ('new_recursive_definition', False, ''),
  ('fromSexp', 'odestSEXSTR'):
    ('new_definition', False, ''),
  ('fromSexp', 'odestSXNUM'):
    ('new_definition', False, ''),
  ('fromSexp', 'odestSXSTR'):
    ('new_definition', False, ''),
  ('fromSexp', 'odestSXSYM'):
    ('new_definition', False, ''),
  ('fromSexp', 'opsexp'):
    ('new_definition', False, ''),
  ('fromSexp', 'optsexp'):
    ('new_recursive_definition', False, ''),
  ('fromSexp', 'patsexp'):
    ('nested', False, ''),
  ('fromSexp', 'prim_typesexp'):
    ('new_definition', False, ''),
  ('fromSexp', 'sexparith'):
    ('new_definition', False, ''),
  ('fromSexp', 'sexpdec'):
    ('measure', True, ''),
  ('fromSexp', 'sexpdec_alt'):
    ('measure', True, ''),
  ('fromSexp', 'sexpexp'):
    ('measure', True, ''),
  ('fromSexp', 'sexpexp_alt'):
    ('measure', True, ''),
  ('fromSexp', 'sexpid'):
    ('measure', True, ''),
  ('fromSexp', 'sexplist'):
    ('match', False, ''),
  ('fromSexp', 'sexplit'):
    ('new_definition', False, ''),
  ('fromSexp', 'sexplocn'):
    ('new_definition', False, ''),
  ('fromSexp', 'sexplocpt'):
    ('new_definition', False, ''),
  ('fromSexp', 'sexplog'):
    ('new_definition', False, ''),
  ('fromSexp', 'sexpop'):
    ('new_definition', False, ''),
  ('fromSexp', 'sexpopt'):
    ('new_definition', False, ''),
  ('fromSexp', 'sexppair'):
    ('new_definition', False, ''),
  ('fromSexp', 'sexppat'):
    ('measure', True, ''),
  ('fromSexp', 'sexppat_alt'):
    ('measure', True, ''),
  ('fromSexp', 'sexptype'):
    ('measure', True, ''),
  ('fromSexp', 'sexptype_alt'):
    ('measure', True, ''),
  ('fromSexp', 'sexptype_def'):
    ('new_definition', False, ''),
  ('fromSexp', 'testsexp'):
    ('new_definition', False, ''),
  ('fromSexp', 'type_defsexp'):
    ('new_definition', False, ''),
  ('fromSexp', 'typesexp'):
    ('nested', False, ''),
  ('gc_combined', 'gc_combined'):
    ('new_definition', False, ''),
  ('gc_combined', 'make_partial_conf'):
    ('define_single', False, ''),
  ('gc_shared', 'ADDR_APPLY'):
    ('new_recursive_definition', False, ''),
  ('gc_shared', 'ADDR_MAP'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (heap_address_size (\\x. 0)) x1)'),
  ('gc_shared', 'el_length'):
    ('new_recursive_definition', False, ''),
  ('gc_shared', 'empty_state'):
    ('new_definition', False, ''),
  ('gc_shared', 'gc_edge'):
    ('new_definition', False, ''),
  ('gc_shared', 'gc_forward_ptr'):
    ('prim_rec', False, ''),
  ('gc_shared', 'gc_related'):
    ('new_definition', False, ''),
  ('gc_shared', 'heap_addresses'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (heap_element_size (\\x. 0) (\\x. 0)) x1)'),
  ('gc_shared', 'heap_drop'):
    ('new_definition', False, ''),
  ('gc_shared', 'heap_expand'):
    ('new_definition', False, ''),
  ('gc_shared', 'heap_filter'):
    ('new_definition', False, ''),
  ('gc_shared', 'heap_filter_aux'):
    ('prim_rec', False, ''),
  ('gc_shared', 'heap_length'):
    ('new_definition', False, ''),
  ('gc_shared', 'heap_lookup'):
    ('prim_rec', False, ''),
  ('gc_shared', 'heap_map'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (heap_element_size (\\x. 0) (\\x. 0)) x1)'),
  ('gc_shared', 'heap_map1'):
    ('new_definition', False, ''),
  ('gc_shared', 'heap_ok'):
    ('new_definition', False, ''),
  ('gc_shared', 'heap_restrict'):
    ('new_definition', False, ''),
  ('gc_shared', 'heap_segment'):
    ('new_definition', False, ''),
  ('gc_shared', 'heap_split'):
    ('prim_rec', False, ''),
  ('gc_shared', 'heap_take'):
    ('new_definition', False, ''),
  ('gc_shared', 'heaps_similar'):
    ('new_definition', False, ''),
  ('gc_shared', 'isDataElement'):
    ('new_definition', False, ''),
  ('gc_shared', 'isForwardPointer'):
    ('new_definition', False, ''),
  ('gc_shared', 'isSomeDataElement'):
    ('new_definition', False, ''),
  ('gc_shared', 'isSomeDataOrForward'):
    ('new_definition', False, ''),
  ('gc_shared', 'isSomeForwardPointer'):
    ('new_definition', False, ''),
  ('gc_shared', 'reachable_addresses'):
    ('new_definition', False, ''),
  ('gc_shared', 'roots_ok'):
    ('new_definition', False, ''),
  ('gen_gc', 'gc_move_refs'):
    ('measure', True, ''),
  ('gen_gc', 'gen_gc'):
    ('new_definition', False, ''),
  ('gen_gc', 'gen_gc_gc_inv'):
    ('new_definition', False, ''),
  ('gen_gc', 'gen_gc_gc_move'):
    ('new_recursive_definition', False, ''),
  ('gen_gc', 'gen_gc_gc_move_data'):
    ('measure', True, ''),
  ('gen_gc', 'gen_gc_gc_move_list'):
    ('prim_rec', False, ''),
  ('gen_gc', 'gen_gc_gc_move_loop'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x2)'),
  ('gen_gc', 'is_final'):
    ('new_definition', False, ''),
  ('gen_gc_partial', 'all_old_ptrs'):
    ('new_definition', False, ''),
  ('gen_gc_partial', 'balanced_state'):
    ('new_definition', False, ''),
  ('gen_gc_partial', 'f_old_ptrs'):
    ('new_definition', False, ''),
  ('gen_gc_partial', 'gc_move_ref_list'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). list_size (heap_element_size (\\x. 0) (\\x. 0)) x2)'),
  ('gen_gc_partial', 'gen_gc_partial_gc_move'):
    ('new_recursive_definition', False, ''),
  ('gen_gc_partial', 'gen_gc_partial_gc_move_data'):
    ('measure', True, ''),
  ('gen_gc_partial', 'gen_gc_partial_gc_move_list'):
    ('prim_rec', False, ''),
  ('gen_gc_partial', 'gen_inv'):
    ('new_definition', False, ''),
  ('gen_gc_partial', 'has_bad_ref'):
    ('new_definition', False, ''),
  ('gen_gc_partial', 'has_old_ptr'):
    ('new_definition', False, ''),
  ('gen_gc_partial', 'heap_element_is_ref'):
    ('new_definition', False, ''),
  ('gen_gc_partial', 'heap_gen_ok'):
    ('new_definition', False, ''),
  ('gen_gc_partial', 'new_f'):
    ('new_definition', False, ''),
  ('gen_gc_partial', 'partial_gc'):
    ('new_definition', False, ''),
  ('gen_gc_partial', 'refs_to_roots'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (heap_element_size (\\x. 0) (\\x. 0)) x1)'),
  ('gen_gc_partial', 'sim_inv'):
    ('new_definition', False, ''),
  ('gen_gc_partial', 'similar_data'):
    ('new_definition', False, ''),
  ('gen_gc_partial', 'similar_ptr'):
    ('new_definition', False, ''),
  ('gen_gc_partial', 'simple_rel'):
    ('new_definition', False, ''),
  ('gen_gc_partial', 'to_gen_conf'):
    ('new_definition', False, ''),
  ('gen_gc_partial', 'to_gen_heap'):
    ('new_definition', False, ''),
  ('gen_gc_partial', 'to_gen_heap_address'):
    ('new_recursive_definition', False, ''),
  ('gen_gc_partial', 'to_gen_heap_element'):
    ('new_recursive_definition', False, ''),
  ('gen_gc_partial', 'to_gen_heap_list'):
    ('new_definition', False, ''),
  ('gen_gc_partial', 'to_gen_roots'):
    ('new_definition', False, ''),
  ('gen_gc_partial', 'to_gen_state'):
    ('new_definition', False, ''),
  ('gram', 'Lfl'):
    ('new_definition', False, ''),
  ('gram', 'Ndl'):
    ('new_definition', False, ''),
  ('gram', 'validAddSym'):
    ('new_definition', False, ''),
  ('gram', 'validListSym'):
    ('new_definition', False, ''),
  ('gram', 'validMultSym'):
    ('new_definition', False, ''),
  ('gram', 'validPrefixSym'):
    ('new_definition', False, ''),
  ('gram', 'validRelSym'):
    ('new_definition', False, ''),
  ('gramProps', 'NT_rank'):
    ('new_definition', False, ''),
  ('gramProps', 'fringe_lengths'):
    ('new_definition', False, ''),
  ('grammar', 'derive'):
    ('new_definition', False, ''),
  ('grammar', 'grammar_destTOK'):
    ('new_definition', False, ''),
  ('grammar', 'ptree_fringe'):
    ('nested', False, ''),
  ('grammar', 'ptree_head'):
    ('new_recursive_definition', False, ''),
  ('grammar', 'ptree_list_loc'):
    ('new_definition', False, ''),
  ('grammar', 'ptree_loc'):
    ('new_recursive_definition', False, ''),
  ('grammar', 'real_fringe'):
    ('nested', False, ''),
  ('grammar', 'valid_locs'):
    ('nested', False, ''),
  ('grammar', 'valid_lptree'):
    ('new_definition', False, ''),
  ('grammar', 'valid_ptree'):
    ('nested', False, ''),
  ('indexedLists', 'FOLDRi'):
    ('prim_rec', False, ''),
  ('indexedLists', 'indexedLists_findi'):
    ('prim_rec', False, ''),
  ('infer', 'add_constraint'):
    ('new_definition', False, ''),
  ('infer', 'add_constraints'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). infer_t_size1 x1 + infer_t_size1 x2)'),
  ('infer', 'alist_nub'):
    ('measure', True, ''),
  ('infer', 'apply_subst'):
    ('new_definition', False, ''),
  ('infer', 'apply_subst_list'):
    ('new_definition', False, ''),
  ('infer', 'check_ctor_types'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). list_size (pair_size mlstring_size ast_t_size1) x3)'),
  ('infer', 'check_ctors'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2).      list_size      (pair_size (list_size mlstring_size)      (pair_size mlstring_size      (list_size (pair_size mlstring_size ast_t_size1))))      x2)'),
  ('infer', 'check_dups'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). loc_err_info_size x0)'),
  ('infer', 'check_s'):
    ('new_definition', False, ''),
  ('infer', 'check_t'):
    ('nested', False, ''),
  ('infer', 'check_type_definition'):
    ('new_definition', False, ''),
  ('infer', 'constrain_op'):
    ('new_definition', False, ''),
  ('infer', 'extend_dec_ienv'):
    ('new_definition', False, ''),
  ('infer', 'find_dup'):
    ('prim_rec', False, ''),
  ('infer', 'fresh_uvar'):
    ('new_definition', False, ''),
  ('infer', 'generalise'):
    ('prim_rec', False, ''),
  ('infer', 'get_next_uvar'):
    ('new_definition', False, ''),
  ('infer', 'ienv_val_ok'):
    ('new_definition', False, ''),
  ('infer', 'inf_env_to_types_string'):
    ('new_definition', False, ''),
  ('infer', 'infer_d'):
    ('measure', False, ''),
  ('infer', 'infer_deBruijn_inc'):
    ('nested', False, ''),
  ('infer', 'infer_deBruijn_subst'):
    ('prim_rec', False, ''),
  ('infer', 'infer_e'):
    ('measure', False, ''),
  ('infer', 'infer_failwith'):
    ('new_definition', False, ''),
  ('infer', 'infer_guard'):
    ('new_definition', False, ''),
  ('infer', 'infer_init_config'):
    ('new_definition', False, ''),
  ('infer', 'infer_p'):
    ('measure', False, ''),
  ('infer', 'infer_subst'):
    ('nested', False, ''),
  ('infer', 'infer_type_subst'):
    ('prim_rec', False, ''),
  ('infer', 'infertype_prog'):
    ('new_definition', False, ''),
  ('infer', 'infertype_prog_inc'):
    ('new_definition', False, ''),
  ('infer', 'init_infer_state'):
    ('new_definition', False, ''),
  ('infer', 'init_state'):
    ('new_definition', False, ''),
  ('infer', 'lift_ienv'):
    ('new_definition', False, ''),
  ('infer', 'lookup_st_ex'):
    ('new_definition', False, ''),
  ('infer', 'n_fresh_id'):
    ('new_definition', False, ''),
  ('infer', 'n_fresh_uvar'):
    ('measure', False, 'MEASURE (\\x0. (\\n. n) x0)'),
  ('infer', 'ns_nub'):
    ('nested', False, ''),
  ('infer', 'ns_to_alist'):
    ('measure', True, ''),
  ('infer', 'op_n_args_msg'):
    ('new_definition', False, ''),
  ('infer', 'op_simple_constraints'):
    ('new_definition', False, ''),
  ('infer', 'op_to_string'):
    ('new_definition', False, ''),
  ('infer', 'pure_add_constraints'):
    ('prim_rec', False, ''),
  ('infer', 'read'):
    ('new_definition', False, ''),
  ('infer', 'sub_completion'):
    ('new_definition', False, ''),
  ('infer', 't_num_of'):
    ('new_definition', False, ''),
  ('infer', 'type_name_check_sub'):
    ('measure', False, 'MEASURE (sum_measure (\\(x0,x1,x2,x3). ast_t_size x3) (\\(x0,x1,x2,x3). ast_t_size1 x3))'),
  ('infer', 'type_name_check_subst'):
    ('measure', False, 'MEASURE (sum_measure (\\(x0,x1,x2,x3,x4). ast_t_size x4) (\\(x0,x1,x2,x3,x4). ast_t_size1 x4))'),
  ('infer', 'word_tc'):
    ('new_recursive_definition', False, ''),
  ('infer', 'write'):
    ('new_definition', False, ''),
  ('inferProps', 'ienv_ok'):
    ('new_definition', False, ''),
  ('inferProps', 'inf_set_tids'):
    ('measure', False, 'MEASURE infer_t_size'),
  ('inferProps', 'inf_set_tids_ienv'):
    ('new_definition', False, ''),
  ('inferProps', 'inf_set_tids_subset'):
    ('new_definition', False, ''),
  ('inferProps', 'inf_set_tids_subst'):
    ('new_definition', False, ''),
  ('inferProps', 'inferProps_hide'):
    ('new_definition', False, ''),
  ('inferProps', 'infer_subst_var'):
    ('new_definition', False, ''),
  ('inferProps', 'prim_tids'):
    ('new_definition', False, ''),
  ('inferProps', 'remap_tenv'):
    ('new_definition', False, ''),
  ('inferProps', 'set_tids'):
    ('measure', False, 'MEASURE t_size'),
  ('inferProps', 'set_tids_subset'):
    ('new_definition', False, ''),
  ('inferProps', 'ts_tid_rename'):
    ('measure', False, 'MEASURE (\\(_2,y). t_size y)'),
  ('inferProps', 'unconvert_t'):
    ('nested', False, ''),
  ('inferSound', 'set_ids'):
    ('new_definition', False, ''),
  ('infer_eComplete', 'simp_tenv_invC'):
    ('new_definition', False, ''),
  ('infer_t', 'add_parens'):
    ('new_definition', False, ''),
  ('infer_t', 'get_tyname'):
    ('measure', False, 'MEASURE (\\(x0,x1).      namespace_size (pair_size (\\x. 0) t_size) mlstring_size mlstring_size x1)'),
  ('infer_t', 'id_to_string'):
    ('prim_rec', False, ''),
  ('infer_t', 'inf_type_to_string'):
    ('new_definition', False, ''),
  ('infer_t', 'inf_type_to_string_rec'):
    ('measure', False, 'MEASURE (\\(x0,x1). infer_t_size x1)'),
  ('infer_t', 'infer_t_commas'):
    ('guess', False, ''),
  ('infer_t', 'ty_var_name'):
    ('new_definition', False, ''),
  ('infer_t', 'type_ident_to_string'):
    ('new_definition', False, ''),
  ('jsonLang', 'concat_with'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (app_list_size (\\x. 0)) x0)'),
  ('jsonLang', 'encode_str'):
    ('new_definition', False, ''),
  ('jsonLang', 'json_to_mlstring'):
    ('measure', False, 'MEASURE (sum_measure (\\x0. obj_size x0) (\\x0. obj_size3 x0))'),
  ('jsonLang', 'n_rev_hex_digs'):
    ('measure', False, 'MEASURE (\\(x0,x1). (\\n. n) x0)'),
  ('jsonLang', 'num_to_hex_digit'):
    ('new_definition', False, ''),
  ('jsonLang', 'printable'):
    ('new_definition', False, ''),
  ('labLang', 'Section_lines'):
    ('define_single', False, ''),
  ('labLang', 'Section_num'):
    ('define_single', False, ''),
  ('labProps', 'align_dm'):
    ('new_definition', False, ''),
  ('labProps', 'align_sdm'):
    ('new_definition', False, ''),
  ('labProps', 'labProps_extract_labels'):
    ('measure', False, 'MEASURE (\\x0. list_size (line_size (\\x. 0)) x0)'),
  ('labProps', 'labProps_get_code_labels'):
    ('new_definition', False, ''),
  ('labProps', 'labProps_get_labels'):
    ('new_definition', False, ''),
  ('labProps', 'labProps_no_install'):
    ('new_definition', False, ''),
  ('labProps', 'labs_of'):
    ('new_definition', False, ''),
  ('labProps', 'line_get_code_labels'):
    ('new_definition', False, ''),
  ('labProps', 'line_get_labels'):
    ('new_definition', False, ''),
  ('labProps', 'line_length'):
    ('new_recursive_definition', False, ''),
  ('labProps', 'line_ok_pre'):
    ('new_definition', False, ''),
  ('labProps', 'no_share_mem_inst'):
    ('new_definition', False, ''),
  ('labProps', 'sec_ends_with_label'):
    ('define_single', False, ''),
  ('labProps', 'sec_get_code_labels'):
    ('define_single', False, ''),
  ('labProps', 'sec_get_labels'):
    ('define_single', False, ''),
  ('labProps', 'sec_label_ok'):
    ('new_definition', False, ''),
  ('labProps', 'sec_labels_ok'):
    ('define_single', False, ''),
  ('labProps', 'sec_ok_pre'):
    ('define_single', False, ''),
  ('labSem', 'asm_code_length'):
    ('measure', True, ''),
  ('labSem', 'asm_fetch'):
    ('new_definition', False, ''),
  ('labSem', 'asm_fetch_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (sec_size (\\x. 0)) x1)'),
  ('labSem', 'asm_inst'):
    ('new_recursive_definition', False, ''),
  ('labSem', 'get_lab_after'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (sec_size (\\x. 0)) x1)'),
  ('labSem', 'get_pc_value'):
    ('new_definition', False, ''),
  ('labSem', 'get_ret_Loc'):
    ('new_definition', False, ''),
  ('labSem', 'inc_pc'):
    ('new_definition', False, ''),
  ('labSem', 'is_Label'):
    ('new_definition', False, ''),
  ('labSem', 'is_Loc'):
    ('new_definition', False, ''),
  ('labSem', 'labSem_addr'):
    ('define_single', False, ''),
  ('labSem', 'labSem_arith_upd'):
    ('new_recursive_definition', False, ''),
  ('labSem', 'labSem_assert'):
    ('new_definition', False, ''),
  ('labSem', 'labSem_binop_upd'):
    ('define_single', False, ''),
  ('labSem', 'labSem_dec_clock'):
    ('new_definition', False, ''),
  ('labSem', 'labSem_evaluate'):
    ('measure', False, ''),
  ('labSem', 'labSem_fp_upd'):
    ('new_recursive_definition', False, ''),
  ('labSem', 'labSem_mem_load'):
    ('new_definition', False, ''),
  ('labSem', 'labSem_mem_op'):
    ('define_single', False, ''),
  ('labSem', 'labSem_mem_store'):
    ('new_definition', False, ''),
  ('labSem', 'labSem_read_fp_reg'):
    ('new_definition', False, ''),
  ('labSem', 'labSem_reg_imm'):
    ('new_recursive_definition', False, ''),
  ('labSem', 'labSem_semantics'):
    ('new_definition', False, ''),
  ('labSem', 'labSem_upd_fp_reg'):
    ('new_definition', False, ''),
  ('labSem', 'labSem_upd_mem'):
    ('new_definition', False, ''),
  ('labSem', 'labSem_upd_pc'):
    ('new_definition', False, ''),
  ('labSem', 'labSem_upd_reg'):
    ('new_definition', False, ''),
  ('labSem', 'lab_to_loc'):
    ('define_single', False, ''),
  ('labSem', 'loc_to_pc'):
    ('measure', True, ''),
  ('labSem', 'mem_load32'):
    ('new_definition', False, ''),
  ('labSem', 'mem_load_byte'):
    ('new_definition', False, ''),
  ('labSem', 'mem_store32'):
    ('new_definition', False, ''),
  ('labSem', 'mem_store_byte'):
    ('new_definition', False, ''),
  ('labSem', 'next_label'):
    ('measure', False, 'MEASURE (\\x0. list_size (sec_size (\\x. 0)) x0)'),
  ('labSem', 'share_mem_load'):
    ('new_definition', False, ''),
  ('labSem', 'share_mem_op'):
    ('new_recursive_definition', False, ''),
  ('labSem', 'share_mem_store'):
    ('new_definition', False, ''),
  ('lab_filter', 'filter_skip'):
    ('measure', False, 'MEASURE (\\x0. list_size (sec_size (\\x. 0)) x0)'),
  ('lab_filter', 'not_skip'):
    ('new_definition', False, ''),
  ('lab_filterProof', 'adjust_pc'):
    ('measure', True, ''),
  ('lab_filterProof', 'all_skips'):
    ('new_definition', False, ''),
  ('lab_filterProof', 'lab_filterProof_state_rel'):
    ('new_definition', False, ''),
  ('lab_to_target', 'add_nop'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (line_size (\\x. 0)) x1)'),
  ('lab_to_target', 'cbw_to_asm'):
    ('new_definition', False, ''),
  ('lab_to_target', 'compile_lab'):
    ('new_definition', False, ''),
  ('lab_to_target', 'compute_labels_alt'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). list_size (sec_size (\\x. 0)) x1)'),
  ('lab_to_target', 'enc_line'):
    ('new_recursive_definition', False, ''),
  ('lab_to_target', 'enc_lines_again'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4,x5).      list_size (line_size (\\x. 0)) x4 +      pair_size (list_size (line_size (\\x. 0))) (\\x. 0) x5)'),
  ('lab_to_target', 'enc_sec'):
    ('define_single', False, ''),
  ('lab_to_target', 'enc_sec_list'):
    ('new_definition', False, ''),
  ('lab_to_target', 'enc_secs_again'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4). list_size (sec_size (\\x. 0)) x4)'),
  ('lab_to_target', 'ffi_offset'):
    ('new_definition', False, ''),
  ('lab_to_target', 'find_ffi_names'):
    ('measure', True, ''),
  ('lab_to_target', 'find_pos'):
    ('define_single', False, ''),
  ('lab_to_target', 'get_ffi_index'):
    ('new_definition', False, ''),
  ('lab_to_target', 'get_jump_offset'):
    ('new_definition', False, ''),
  ('lab_to_target', 'get_label'):
    ('new_definition', False, ''),
  ('lab_to_target', 'get_memop_info'):
    ('new_recursive_definition', False, ''),
  ('lab_to_target', 'get_shmem_info'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). list_size (sec_size (\\x. 0)) x0)'),
  ('lab_to_target', 'get_symbols'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (sec_size (\\x. 0)) x1)'),
  ('lab_to_target', 'get_zero_labs_acc'):
    ('new_definition', False, ''),
  ('lab_to_target', 'lab_inst'):
    ('new_recursive_definition', False, ''),
  ('lab_to_target', 'lab_to_target_compile'):
    ('new_definition', False, ''),
  ('lab_to_target', 'line_bytes'):
    ('new_recursive_definition', False, ''),
  ('lab_to_target', 'line_get_zero_labs_acc'):
    ('new_definition', False, ''),
  ('lab_to_target', 'line_ok_light'):
    ('new_definition', False, ''),
  ('lab_to_target', 'lines_upd_lab_len'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). list_size (line_size (\\x. 0)) x1)'),
  ('lab_to_target', 'list_add_if_fresh'):
    ('prim_rec', False, ''),
  ('lab_to_target', 'pad_bytes'):
    ('new_definition', False, ''),
  ('lab_to_target', 'pad_code'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (sec_size (\\x. 0)) x1)'),
  ('lab_to_target', 'pad_section'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). list_size (line_size (\\x. 0)) x1)'),
  ('lab_to_target', 'prog_to_bytes'):
    ('measure', True, ''),
  ('lab_to_target', 'remove_labels'):
    ('new_definition', False, ''),
  ('lab_to_target', 'remove_labels_loop'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4,x5). (\\n. n) x0)'),
  ('lab_to_target', 'sec_get_zero_labs_acc'):
    ('define_single', False, ''),
  ('lab_to_target', 'sec_length'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (line_size (\\x. 0)) x0)'),
  ('lab_to_target', 'sec_ok_light'):
    ('define_single', False, ''),
  ('lab_to_target', 'section_labels'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). list_size (line_size (\\x. 0)) x1)'),
  ('lab_to_target', 'upd_lab_len'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (sec_size (\\x. 0)) x1)'),
  ('lab_to_target', 'zero_labs_acc_exist'):
    ('new_definition', False, ''),
  ('lab_to_target', 'zero_labs_acc_of'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'all_enc_ok'):
    ('measure', True, ''),
  ('lab_to_targetProof', 'all_enc_with_nop'):
    ('measure', True, ''),
  ('lab_to_targetProof', 'all_encd'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4). list_size (sec_size (\\x. 0)) x4)'),
  ('lab_to_targetProof', 'all_lab_len_pos_ok'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (sec_size (\\x. 0)) x1)'),
  ('lab_to_targetProof', 'asm_step_nop'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'code_similar'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (sec_size (\\x. 0)) x0 + list_size (sec_size (\\x. 0)) x1)'),
  ('lab_to_targetProof', 'compiler_oracle_ok'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'enc_lines_again_simp'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4). list_size (line_size (\\x. 0)) x4)'),
  ('lab_to_targetProof', 'enc_with_nop'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'even_labels'):
    ('measure', True, ''),
  ('lab_to_targetProof', 'even_labels_strong'):
    ('measure', True, ''),
  ('lab_to_targetProof', 'has_io_name'):
    ('measure', True, ''),
  ('lab_to_targetProof', 'has_odd_inst'):
    ('measure', True, ''),
  ('lab_to_targetProof', 'init_ok'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'lab_len_pos_ok'):
    ('prim_rec', False, ''),
  ('lab_to_targetProof', 'lab_lookup'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'lab_to_targetProof_good_code'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'lab_to_targetProof_make_init'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'lab_to_targetProof_offset_ok'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). list_size (sec_size (\\x. 0)) x3)'),
  ('lab_to_targetProof', 'lab_to_targetProof_state_rel'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'label_one'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'label_prefix_zero'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'label_zero'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'labs_domain'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'line_aligned'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'line_enc_with_nop'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'line_encd'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'line_encd0'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'line_lab_len_pos_ok'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'line_labs_exist'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'line_len'):
    ('new_recursive_definition', False, ''),
  ('lab_to_targetProof', 'line_length_leq'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'line_length_ok'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'line_offset_ok'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'line_ok'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'line_similar'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'line_to_info'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'lines_enc_with_nop'):
    ('prim_rec', False, ''),
  ('lab_to_targetProof', 'lines_encd'):
    ('prim_rec', False, ''),
  ('lab_to_targetProof', 'lines_even_labels'):
    ('prim_rec', False, ''),
  ('lab_to_targetProof', 'lines_offset_ok'):
    ('prim_rec', False, ''),
  ('lab_to_targetProof', 'lines_ok'):
    ('prim_rec', False, ''),
  ('lab_to_targetProof', 'make_word'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'mc_conf_ok'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'no_install_or_no_share_mem'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'num_pcs'):
    ('measure', True, ''),
  ('lab_to_targetProof', 'oracle_tie'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'pos_val'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). list_size (sec_size (\\x. 0)) x2)'),
  ('lab_to_targetProof', 'sec_aligned'):
    ('define_single', False, ''),
  ('lab_to_targetProof', 'sec_encd0'):
    ('define_single', False, ''),
  ('lab_to_targetProof', 'sec_label_one'):
    ('define_single', False, ''),
  ('lab_to_targetProof', 'sec_label_prefix_zero'):
    ('define_single', False, ''),
  ('lab_to_targetProof', 'sec_label_zero'):
    ('define_single', False, ''),
  ('lab_to_targetProof', 'sec_labs_exist'):
    ('define_single', False, ''),
  ('lab_to_targetProof', 'sec_length_leq'):
    ('define_single', False, ''),
  ('lab_to_targetProof', 'sec_length_ok'):
    ('define_single', False, ''),
  ('lab_to_targetProof', 'sec_loc_to_pc'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (line_size (\\x. 0)) x1)'),
  ('lab_to_targetProof', 'sec_pos_val'):
    ('prim_rec', False, ''),
  ('lab_to_targetProof', 'set_bytes'):
    ('prim_rec', False, ''),
  ('lab_to_targetProof', 'share_mem_domain_code_rel'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'share_mem_state_rel'):
    ('new_definition', False, ''),
  ('lab_to_targetProof', 'word_loc_val'):
    ('new_recursive_definition', False, ''),
  ('lab_to_targetProof', 'word_loc_val_byte'):
    ('new_definition', False, ''),
  ('lexer_fun', 'get_token'):
    ('new_definition', False, ''),
  ('lexer_fun', 'init_loc'):
    ('new_definition', False, ''),
  ('lexer_fun', 'isAlphaNumPrime'):
    ('new_definition', False, ''),
  ('lexer_fun', 'isSymbol'):
    ('new_definition', False, ''),
  ('lexer_fun', 'is_single_char_symbol'):
    ('new_definition', False, ''),
  ('lexer_fun', 'lexer_fun'):
    ('new_definition', False, ''),
  ('lexer_fun', 'lexer_fun_aux'):
    ('measure', True, ''),
  ('lexer_fun', 'lexer_fun_read_string'):
    ('measure', True, ''),
  ('lexer_fun', 'mkCharS'):
    ('new_definition', False, ''),
  ('lexer_fun', 'next_line'):
    ('new_definition', False, ''),
  ('lexer_fun', 'next_loc'):
    ('new_definition', False, ''),
  ('lexer_fun', 'next_sym'):
    ('guess', False, ''),
  ('lexer_fun', 'next_token'):
    ('new_definition', False, ''),
  ('lexer_fun', 'processIdent'):
    ('new_definition', False, ''),
  ('lexer_fun', 'read_FFIcall'):
    ('prim_rec', False, ''),
  ('lexer_fun', 'read_Ident'):
    ('measure', True, ''),
  ('lexer_fun', 'read_Ident_ret'):
    ('new_definition', False, ''),
  ('lexer_fun', 'read_REPLcommand'):
    ('prim_rec', False, ''),
  ('lexer_fun', 'read_char_as_3digits'):
    ('new_definition', False, ''),
  ('lexer_fun', 'read_while'):
    ('match', False, ''),
  ('lexer_fun', 'skip_comment'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). list_size char_size x0)'),
  ('lexer_fun', 'split_top_level_semi'):
    ('measure', True, ''),
  ('lexer_fun', 'to_path'):
    ('prim_rec', False, ''),
  ('lexer_fun', 'token_of_sym'):
    ('new_definition', False, ''),
  ('lexer_fun', 'toplevel_semi_dex'):
    ('prim_rec', False, ''),
  ('lexer_impl', 'lex_aux_alt'):
    ('measure', True, ''),
  ('lexer_impl', 'lex_aux_tokens'):
    ('match', False, ''),
  ('lexer_impl', 'lex_impl_all'):
    ('measure', True, ''),
  ('lexer_impl', 'lex_impl_all_tokens'):
    ('measure', True, ''),
  ('lexer_impl', 'lex_until_top_semicolon_alt'):
    ('new_definition', False, ''),
  ('lexer_impl', 'lex_until_toplevel_semicolon'):
    ('new_definition', False, ''),
  ('lexer_impl', 'lex_until_toplevel_semicolon_tokens'):
    ('new_definition', False, ''),
  ('lexer_impl', 'lexer_impl_lex_aux'):
    ('measure', True, ''),
  ('lexer_impl', 'next_sym_alt'):
    ('guess', False, ''),
  ('lexer_impl', 'num_from_dec_string_alt'):
    ('new_definition', False, ''),
  ('lexer_impl', 'num_from_hex_string_alt'):
    ('new_definition', False, ''),
  ('lexer_impl', 'token_of_sym_loc'):
    ('new_definition', False, ''),
  ('lexer_impl', 'unhex_alt'):
    ('new_definition', False, ''),
  ('linear_scan', 'MAP_colors'):
    ('measure', False, 'MEASURE (\\(x0,x1). (\\n. n) x1)'),
  ('linear_scan', 'add_active_interval'):
    ('prim_rec', False, ''),
  ('linear_scan', 'apply_bij_on_clash_tree'):
    ('prim_rec', False, ''),
  ('linear_scan', 'apply_bijection'):
    ('new_definition', False, ''),
  ('linear_scan', 'apply_reg_exchange'):
    ('new_definition', False, ''),
  ('linear_scan', 'check_intervals'):
    ('new_definition', False, ''),
  ('linear_scan', 'check_live_tree'):
    ('prim_rec', False, ''),
  ('linear_scan', 'check_number_property'):
    ('prim_rec', False, ''),
  ('linear_scan', 'check_number_property_strong'):
    ('prim_rec', False, ''),
  ('linear_scan', 'check_startlive_prop'):
    ('prim_rec', False, ''),
  ('linear_scan', 'color_register'):
    ('new_definition', False, ''),
  ('linear_scan', 'colors_length'):
    ('new_definition', False, ''),
  ('linear_scan', 'colors_sub'):
    ('new_definition', False, ''),
  ('linear_scan', 'edges_to_adjlist'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (pair_size (\\n. n) (\\n. n)) x0)'),
  ('linear_scan', 'extract_coloration'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). list_size (\\n. n) x1)'),
  ('linear_scan', 'find_bijection_clash_tree'):
    ('prim_rec', False, ''),
  ('linear_scan', 'find_bijection_init'):
    ('new_definition', False, ''),
  ('linear_scan', 'find_bijection_step'):
    ('new_definition', False, ''),
  ('linear_scan', 'find_color'):
    ('new_definition', False, ''),
  ('linear_scan', 'find_color_in_colornum'):
    ('new_definition', False, ''),
  ('linear_scan', 'find_color_in_list'):
    ('prim_rec', False, ''),
  ('linear_scan', 'find_last_stealable'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (pair_size (\\x. 0) (\\n. n)) x0)'),
  ('linear_scan', 'find_reg_exchange'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). list_size (\\n. n) x0)'),
  ('linear_scan', 'find_spill'):
    ('new_definition', False, ''),
  ('linear_scan', 'fix_domination'):
    ('new_definition', False, ''),
  ('linear_scan', 'get_colors'):
    ('new_definition', False, ''),
  ('linear_scan', 'get_int_beg'):
    ('new_definition', False, ''),
  ('linear_scan', 'get_int_end'):
    ('new_definition', False, ''),
  ('linear_scan', 'get_intervals'):
    ('prim_rec', False, ''),
  ('linear_scan', 'get_intervals_ct'):
    ('new_definition', False, ''),
  ('linear_scan', 'get_intervals_ct_aux'):
    ('prim_rec', False, ''),
  ('linear_scan', 'get_intervals_ct_monad'):
    ('new_definition', False, ''),
  ('linear_scan', 'get_intervals_ct_monad_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). clash_tree_size x0)'),
  ('linear_scan', 'get_intervals_withlive'):
    ('prim_rec', False, ''),
  ('linear_scan', 'get_live_backward'):
    ('prim_rec', False, ''),
  ('linear_scan', 'get_live_tree'):
    ('prim_rec', False, ''),
  ('linear_scan', 'get_sorted_moves'):
    ('new_definition', False, ''),
  ('linear_scan', 'get_sorted_regs'):
    ('new_definition', False, ''),
  ('linear_scan', 'int_beg_length'):
    ('new_definition', False, ''),
  ('linear_scan', 'int_beg_sub'):
    ('new_definition', False, ''),
  ('linear_scan', 'int_end_length'):
    ('new_definition', False, ''),
  ('linear_scan', 'int_end_sub'):
    ('new_definition', False, ''),
  ('linear_scan', 'interval_intersect'):
    ('new_definition', False, ''),
  ('linear_scan', 'linear_reg_alloc_and_extract_coloration'):
    ('new_definition', False, ''),
  ('linear_scan', 'linear_reg_alloc_intervals'):
    ('new_definition', False, ''),
  ('linear_scan', 'linear_reg_alloc_pass1_initial_state'):
    ('new_definition', False, ''),
  ('linear_scan', 'linear_reg_alloc_pass2_initial_state'):
    ('new_definition', False, ''),
  ('linear_scan', 'linear_reg_alloc_step_aux'):
    ('new_definition', False, ''),
  ('linear_scan', 'linear_reg_alloc_step_pass1'):
    ('new_definition', False, ''),
  ('linear_scan', 'linear_reg_alloc_step_pass2'):
    ('new_definition', False, ''),
  ('linear_scan', 'linear_scan_numset_list_insert'):
    ('prim_rec', False, ''),
  ('linear_scan', 'linear_scan_reg_alloc'):
    ('new_definition', False, ''),
  ('linear_scan', 'linear_scan_sort_moves'):
    ('measure', True, ''),
  ('linear_scan', 'list_to_sorted_moves'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (pair_size (\\n. n) (pair_size (\\n. n) (\\n. n))) x0)'),
  ('linear_scan', 'list_to_sorted_regs'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (\\n. n) x0)'),
  ('linear_scan', 'live_tree_registers'):
    ('measure', False, 'MEASURE (\\x0. live_tree_size x0)'),
  ('linear_scan', 'numset_list_add_if'):
    ('prim_rec', False, ''),
  ('linear_scan', 'numset_list_add_if_gt'):
    ('new_definition', False, ''),
  ('linear_scan', 'numset_list_add_if_gt_monad'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (\\n. n) x0)'),
  ('linear_scan', 'numset_list_add_if_lt'):
    ('new_definition', False, ''),
  ('linear_scan', 'numset_list_add_if_lt_monad'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (\\n. n) x0)'),
  ('linear_scan', 'numset_list_insert_nottailrec'):
    ('prim_rec', False, ''),
  ('linear_scan', 'partition_moves'):
    ('measure', False, 'MEASURE (\\(l,piv,r). r - l)'),
  ('linear_scan', 'partition_regs'):
    ('measure', False, 'MEASURE (\\(l,rpiv,begrpiv,r). r - l)'),
  ('linear_scan', 'point_inside_interval'):
    ('new_definition', False, ''),
  ('linear_scan', 'remove_inactive_intervals'):
    ('measure', True, ''),
  ('linear_scan', 'run_i_linear_scan_hidden_state'):
    ('new_definition', False, ''),
  ('linear_scan', 'set_colors'):
    ('new_definition', False, ''),
  ('linear_scan', 'set_int_beg'):
    ('new_definition', False, ''),
  ('linear_scan', 'set_int_end'):
    ('new_definition', False, ''),
  ('linear_scan', 'set_sorted_moves'):
    ('new_definition', False, ''),
  ('linear_scan', 'set_sorted_regs'):
    ('new_definition', False, ''),
  ('linear_scan', 'size_of_clash_tree'):
    ('prim_rec', False, ''),
  ('linear_scan', 'size_of_live_tree'):
    ('prim_rec', False, ''),
  ('linear_scan', 'sort_moves_rev'):
    ('new_definition', False, ''),
  ('linear_scan', 'sort_regs'):
    ('measure', True, ''),
  ('linear_scan', 'sorted_moves_length'):
    ('new_definition', False, ''),
  ('linear_scan', 'sorted_moves_sub'):
    ('new_definition', False, ''),
  ('linear_scan', 'sorted_moves_to_list'):
    ('measure', False, 'MEASURE (\\(n,len). len - n)'),
  ('linear_scan', 'sorted_regs_length'):
    ('new_definition', False, ''),
  ('linear_scan', 'sorted_regs_sub'):
    ('new_definition', False, ''),
  ('linear_scan', 'sorted_regs_to_list'):
    ('measure', False, 'MEASURE (\\(n,last). last - n)'),
  ('linear_scan', 'spill_register'):
    ('new_definition', False, ''),
  ('linear_scan', 'st_ex_FILTER_good'):
    ('measure', True, ''),
  ('linear_scan', 'st_ex_FOLDL'):
    ('measure', True, ''),
  ('linear_scan', 'swap_moves'):
    ('new_definition', False, ''),
  ('linear_scan', 'swap_regs'):
    ('new_definition', False, ''),
  ('linear_scan', 'update_colors'):
    ('new_definition', False, ''),
  ('linear_scan', 'update_int_beg'):
    ('new_definition', False, ''),
  ('linear_scan', 'update_int_end'):
    ('new_definition', False, ''),
  ('linear_scan', 'update_sorted_moves'):
    ('new_definition', False, ''),
  ('linear_scan', 'update_sorted_regs'):
    ('new_definition', False, ''),
  ('linear_scanProof', 'IS_SPARSE_SUBLIST'):
    ('guess', False, ''),
  ('linear_scanProof', 'edges_to_adjlist_step'):
    ('new_definition', False, ''),
  ('linear_scanProof', 'find_reg_exchange_step'):
    ('new_definition', False, ''),
  ('linear_scanProof', 'forbidden_is_from_forced'):
    ('new_definition', False, ''),
  ('linear_scanProof', 'forbidden_is_from_forced_list'):
    ('new_definition', False, ''),
  ('linear_scanProof', 'forbidden_is_from_forced_sublist'):
    ('new_definition', False, ''),
  ('linear_scanProof', 'forbidden_is_from_map_color_forced'):
    ('new_definition', False, ''),
  ('linear_scanProof', 'good_bijection_state'):
    ('new_definition', False, ''),
  ('linear_scanProof', 'good_linear_scan_state'):
    ('new_definition', False, ''),
  ('linear_scanProof', 'intbeg_less'):
    ('new_definition', False, ''),
  ('linear_scanProof', 'less_FST'):
    ('new_definition', False, ''),
  ('linear_scanProof', 'linear_scanProof_id'):
    ('new_definition', False, ''),
  ('linear_scanProof', 'lookup_default_id'):
    ('new_definition', False, ''),
  ('linear_scanProof', 'phystack_on_stack'):
    ('new_definition', False, ''),
  ('linear_scanProof', 'sptree_eq_list'):
    ('new_definition', False, ''),
  ('location', 'locn_colupdate'):
    ('define_single', False, ''),
  ('location', 'locn_rowupdate'):
    ('define_single', False, ''),
  ('location', 'locncol'):
    ('define_single', False, ''),
  ('location', 'locnle'):
    ('new_definition', False, ''),
  ('location', 'locnrow'):
    ('define_single', False, ''),
  ('location', 'locsle'):
    ('define_single', False, ''),
  ('location', 'merge_list_locs'):
    ('measure', False, 'MEASURE (\\x0. list_size locs_size x0)'),
  ('location', 'merge_locs'):
    ('define_single', False, ''),
  ('location', 'unknown_loc'):
    ('new_definition', False, ''),
  ('lprefix_lub', 'build_lprefix_lub'):
    ('new_definition', False, ''),
  ('lprefix_lub', 'build_lprefix_lub_f'):
    ('new_definition', False, ''),
  ('lprefix_lub', 'lprefix_chain'):
    ('new_definition', False, ''),
  ('lprefix_lub', 'lprefix_chain_nth'):
    ('new_definition', False, ''),
  ('lprefix_lub', 'lprefix_lub'):
    ('new_definition', False, ''),
  ('mc_multiword', 'mc_fac'):
    ('measure', False, 'MEASURE FST'),
  ('mc_multiword', 'mc_fac_pre'):
    ('measure', False, 'MEASURE FST'),
  ('mc_multiword', 'mc_header'):
    ('new_definition', False, ''),
  ('mc_multiword', 'single_add_word'):
    ('new_definition', False, ''),
  ('mc_multiword', 'single_div_pre'):
    ('new_definition', False, ''),
  ('mc_multiword', 'single_sub_word'):
    ('new_definition', False, ''),
  ('mergesort', 'merge_tail'):
    ('guess', False, ''),
  ('mergesort', 'mergesort'):
    ('new_definition', False, ''),
  ('mergesort', 'mergesort_merge'):
    ('guess', False, ''),
  ('mergesort', 'mergesort_tail'):
    ('new_definition', False, ''),
  ('mergesort', 'sort2'):
    ('new_definition', False, ''),
  ('mergesort', 'sort2_tail'):
    ('new_definition', False, ''),
  ('mergesort', 'sort3'):
    ('new_definition', False, ''),
  ('mergesort', 'sort3_tail'):
    ('new_definition', False, ''),
  ('mips_config', 'mips_backend_config'):
    ('new_definition', False, ''),
  ('mips_config', 'mips_names'):
    ('new_definition', False, ''),
  ('misc', 'Lnext_pos'):
    ('new_definition', False, ''),
  ('misc', 'SmartAppend'):
    ('new_definition', False, ''),
  ('misc', 'UPDATE_LIST'):
    ('new_definition', False, ''),
  ('misc', 'all_words'):
    ('measure', False, 'MEASURE (\\(x0,x1). (\\n. n) x1)'),
  ('misc', 'anub'):
    ('prim_rec', False, ''),
  ('misc', 'any_el'):
    ('prim_rec', False, ''),
  ('misc', 'any_word64_ror'):
    ('measure', False, 'MEASURE (\\(x0,x1). (\\n. n) x1)'),
  ('misc', 'append'):
    ('new_definition', False, ''),
  ('misc', 'append_aux'):
    ('prim_rec', False, ''),
  ('misc', 'arith_shift_right'):
    ('measure', False, 'MEASURE (\\(x0,x1). (\\n. n) x1)'),
  ('misc', 'asm_write_bytearray'):
    ('guess', False, ''),
  ('misc', 'between'):
    ('new_definition', False, ''),
  ('misc', 'bytes_in_mem'):
    ('prim_rec', False, ''),
  ('misc', 'bytes_in_memory'):
    ('prim_rec', False, ''),
  ('misc', 'copy_shape'):
    ('measure', False, 'MEASURE (\\(x0,x1). spt_size (\\x. 0) x0 + spt_size (\\x. 0) x1)'),
  ('misc', 'enumerate'):
    ('prim_rec', False, ''),
  ('misc', 'eq_shape'):
    ('measure', False, 'MEASURE (\\(x0,x1). spt_size (\\x. 0) x0 + spt_size (\\x. 0) x1)'),
  ('misc', 'find_index'):
    ('prim_rec', False, ''),
  ('misc', 'fmap_linv'):
    ('new_definition', False, ''),
  ('misc', 'fmap_update'):
    ('new_definition', False, ''),
  ('misc', 'fromList2'):
    ('new_definition', False, ''),
  ('misc', 'good_dimindex'):
    ('new_definition', False, ''),
  ('misc', 'insert_atI'):
    ('new_definition', False, ''),
  ('misc', 'is_subseq'):
    ('guess', False, ''),
  ('misc', 'least_from'):
    ('new_definition', False, ''),
  ('misc', 'list_inter'):
    ('new_definition', False, ''),
  ('misc', 'list_set_eq'):
    ('new_definition', False, ''),
  ('misc', 'list_subset'):
    ('new_definition', False, ''),
  ('misc', 'lookup_any'):
    ('new_definition', False, ''),
  ('misc', 'lookup_vars'):
    ('prim_rec', False, ''),
  ('misc', 'make_even'):
    ('new_definition', False, ''),
  ('misc', 'max3'):
    ('new_definition', False, ''),
  ('misc', 'misc_shift_seq'):
    ('new_definition', False, ''),
  ('misc', 'misc_word_list'):
    ('guess', False, ''),
  ('misc', 'opt_bind'):
    ('new_definition', False, ''),
  ('misc', 'option_fold'):
    ('new_recursive_definition', False, ''),
  ('misc', 'range'):
    ('new_definition', False, ''),
  ('misc', 'read_bytearray'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x1)'),
  ('misc', 'shift_left'):
    ('measure', False, 'MEASURE (\\(x0,x1). (\\n. n) x1)'),
  ('misc', 'shift_right'):
    ('measure', False, 'MEASURE (\\(x0,x1). (\\n. n) x1)'),
  ('misc', 'splitlines'):
    ('new_definition', False, ''),
  ('misc', 'steps'):
    ('prim_rec', False, ''),
  ('misc', 'steps_rel'):
    ('prim_rec', False, ''),
  ('misc', 'sum_cmp'):
    ('new_definition', False, ''),
  ('misc', 'the'):
    ('new_recursive_definition', False, ''),
  ('misc', 'tlookup'):
    ('new_definition', False, ''),
  ('misc', 'update_resize'):
    ('new_definition', False, ''),
  ('misc', 'word_list_exists'):
    ('new_definition', False, ''),
  ('misc', 'zlookup'):
    ('new_definition', False, ''),
  ('ml_monadBase', 'Marray_alloc'):
    ('new_definition', False, ''),
  ('ml_monadBase', 'Marray_length'):
    ('new_definition', False, ''),
  ('ml_monadBase', 'Marray_resize'):
    ('new_definition', False, ''),
  ('ml_monadBase', 'Marray_sub'):
    ('new_definition', False, ''),
  ('ml_monadBase', 'Marray_update'):
    ('new_definition', False, ''),
  ('ml_monadBase', 'Mdref'):
    ('define_single', False, ''),
  ('ml_monadBase', 'Mdref_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1). (\\n. n) x1)'),
  ('ml_monadBase', 'Mget_ref'):
    ('new_definition', False, ''),
  ('ml_monadBase', 'Mpop_ref'):
    ('new_definition', False, ''),
  ('ml_monadBase', 'Mref'):
    ('new_definition', False, ''),
  ('ml_monadBase', 'Mref_assign'):
    ('define_single', False, ''),
  ('ml_monadBase', 'Mref_assign_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x1)'),
  ('ml_monadBase', 'Mset_ref'):
    ('new_definition', False, ''),
  ('ml_monadBase', 'Msub'):
    ('match', False, ''),
  ('ml_monadBase', 'Mupdate'):
    ('match', False, ''),
  ('ml_monadBase', 'array_resize'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x0)'),
  ('ml_monadBase', 'can'):
    ('new_definition', False, ''),
  ('ml_monadBase', 'dref'):
    ('new_definition', False, ''),
  ('ml_monadBase', 'liftM'):
    ('new_definition', False, ''),
  ('ml_monadBase', 'ref_assign'):
    ('new_definition', False, ''),
  ('ml_monadBase', 'ref_bind'):
    ('new_definition', False, ''),
  ('ml_monadBase', 'run'):
    ('new_definition', False, ''),
  ('ml_monadBase', 'st_ex_bind'):
    ('new_definition', False, ''),
  ('ml_monadBase', 'st_ex_ignore_bind'):
    ('new_definition', False, ''),
  ('ml_monadBase', 'st_ex_return'):
    ('new_definition', False, ''),
  ('mlint', 'exp_for_dec_enc'):
    ('new_definition', False, ''),
  ('mlint', 'fromChar'):
    ('new_definition', False, ''),
  ('mlint', 'fromChar_unsafe'):
    ('new_definition', False, ''),
  ('mlint', 'fromChars'):
    ('measure', False, 'MEASURE FST'),
  ('mlint', 'fromChars_range'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x1)'),
  ('mlint', 'fromChars_range_unsafe'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x1)'),
  ('mlint', 'fromChars_unsafe'):
    ('measure', False, 'MEASURE FST'),
  ('mlint', 'fromNatString'):
    ('new_definition', False, ''),
  ('mlint', 'fromString_unsafe'):
    ('new_definition', False, ''),
  ('mlint', 'int_to_string'):
    ('new_definition', False, ''),
  ('mlint', 'maxSmall_DEC'):
    ('new_definition', False, ''),
  ('mlint', 'mlint_fromString'):
    ('new_definition', False, ''),
  ('mlint', 'mlint_int_cmp'):
    ('new_definition', False, ''),
  ('mlint', 'mlint_int_gcd'):
    ('new_definition', False, ''),
  ('mlint', 'mlint_num_gcd'):
    ('measure', False, 'MEASURE (\\(x0,x1). (\\n. n) x0)'),
  ('mlint', 'mlint_toString'):
    ('new_definition', False, ''),
  ('mlint', 'num_to_chars'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). (\\n. n) x0)'),
  ('mlint', 'num_to_str'):
    ('new_definition', False, ''),
  ('mlint', 'padLen_DEC'):
    ('new_definition', False, ''),
  ('mlint', 'toChar'):
    ('new_definition', False, ''),
  ('mllist', 'LENGTH_AUX'):
    ('prim_rec', False, ''),
  ('mllist', 'cpn_to_reln'):
    ('new_definition', False, ''),
  ('mllist', 'drop'):
    ('new_definition', False, ''),
  ('mllist', 'dropUntil'):
    ('prim_rec', False, ''),
  ('mllist', 'filter_rev'):
    ('new_definition', False, ''),
  ('mllist', "filter_rev'"):
    ('prim_rec', False, ''),
  ('mllist', 'flat_rev'):
    ('new_definition', False, ''),
  ('mllist', "flat_rev'"):
    ('prim_rec', False, ''),
  ('mllist', 'getItem'):
    ('new_recursive_definition', False, ''),
  ('mllist', 'intersperse'):
    ('guess', False, ''),
  ('mllist', 'map_rev'):
    ('new_definition', False, ''),
  ('mllist', "map_rev'"):
    ('prim_rec', False, ''),
  ('mllist', 'mllist_collate'):
    ('guess', False, ''),
  ('mllist', 'mllist_foldl'):
    ('prim_rec', False, ''),
  ('mllist', 'mllist_foldli'):
    ('new_definition', False, ''),
  ('mllist', 'mllist_foldli_aux'):
    ('prim_rec', False, ''),
  ('mllist', 'mllist_mapPartial'):
    ('prim_rec', False, ''),
  ('mllist', 'mllist_mapi'):
    ('prim_rec', False, ''),
  ('mllist', 'mllist_tabulate'):
    ('new_definition', False, ''),
  ('mllist', 'nth'):
    ('new_definition', False, ''),
  ('mllist', 'partition'):
    ('new_definition', False, ''),
  ('mllist', 'partition_aux'):
    ('prim_rec', False, ''),
  ('mllist', 'sort'):
    ('new_definition', False, ''),
  ('mllist', 'tabulate_aux'):
    ('measure', False, 'MEASURE (\\(n,m,_1,_2). m - n)'),
  ('mllist', 'take'):
    ('new_definition', False, ''),
  ('mllist', 'takeUntil'):
    ('prim_rec', False, ''),
  ('mloption', 'compose'):
    ('new_definition', False, ''),
  ('mloption', 'composePartial'):
    ('new_definition', False, ''),
  ('mloption', 'getOpt'):
    ('', False, ''),
  ('mloption', 'mloption_compare'):
    ('new_definition', False, ''),
  ('mloption', 'mloption_filter'):
    ('new_definition', False, ''),
  ('mloption', 'mloption_mapPartial'):
    ('new_definition', False, ''),
  ('mlsexp', 'get_next_size'):
    ('match', False, ''),
  ('mlsexp', 'is_safe_char'):
    ('new_definition', False, ''),
  ('mlsexp', 'lex'):
    ('new_definition', False, ''),
  ('mlsexp', 'make_str_safe'):
    ('new_definition', False, ''),
  ('mlsexp', 'mlsexp_annotate'):
    ('prim_rec', False, ''),
  ('mlsexp', 'mlsexp_flatten'):
    ('prim_rec', False, ''),
  ('mlsexp', 'mlsexp_fromString'):
    ('new_definition', False, ''),
  ('mlsexp', 'mlsexp_get_size'):
    ('match', False, ''),
  ('mlsexp', 'mlsexp_lex_aux'):
    ('measure', True, ''),
  ('mlsexp', 'mlsexp_parse'):
    ('new_definition', False, ''),
  ('mlsexp', 'mlsexp_read_string'):
    ('new_definition', False, ''),
  ('mlsexp', 'newlines'):
    ('measure', False, 'MEASURE (\\x0. list_size pretty_size x0)'),
  ('mlsexp', 'parse_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). list_size mlsexp_token_size x0)'),
  ('mlsexp', 'read_string_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size char_size x0)'),
  ('mlsexp', 'read_symbol'):
    ('prim_rec', False, ''),
  ('mlsexp', 'remove_all'):
    ('prim_rec', False, ''),
  ('mlsexp', 'sexp2tree'):
    ('prim_rec', False, ''),
  ('mlsexp', 'sexp_to_app_list'):
    ('prim_rec', False, ''),
  ('mlsexp', 'sexp_to_pretty_string'):
    ('new_definition', False, ''),
  ('mlsexp', 'sexp_to_string'):
    ('new_definition', False, ''),
  ('mlsexp', 'smart_remove'):
    ('prim_rec', False, ''),
  ('mlsexp', 'str_every'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x1)'),
  ('mlsexp', 'str_tree_to_strs'):
    ('new_definition', False, ''),
  ('mlsexp', 'to_tokens'):
    ('nested', False, ''),
  ('mlsexp', 'v2pretty'):
    ('measure', False, 'MEASURE (sum_measure (\\x0. str_tree_size x0) (\\x0. str_tree_size1 x0))'),
  ('mlstring', 'char_escape_seq'):
    ('new_definition', False, ''),
  ('mlstring', 'char_escaped'):
    ('new_definition', False, ''),
  ('mlstring', 'char_to_word8'):
    ('new_definition', False, ''),
  ('mlstring', 'chr_to_str'):
    ('new_definition', False, ''),
  ('mlstring', 'compare_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4). mlstring_size x0)'),
  ('mlstring', 'concatWith'):
    ('new_definition', False, ''),
  ('mlstring', 'empty_ffi'):
    ('new_definition', False, ''),
  ('mlstring', 'escape_char'):
    ('new_definition', False, ''),
  ('mlstring', 'escape_str'):
    ('new_definition', False, ''),
  ('mlstring', 'explode'):
    ('new_definition', False, ''),
  ('mlstring', 'explode_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x2)'),
  ('mlstring', 'fast_ge'):
    ('new_definition', False, ''),
  ('mlstring', 'fast_gt'):
    ('new_definition', False, ''),
  ('mlstring', 'fast_le'):
    ('new_definition', False, ''),
  ('mlstring', 'fast_lt'):
    ('new_definition', False, ''),
  ('mlstring', 'fields'):
    ('new_definition', False, ''),
  ('mlstring', 'fields_alt_aux'):
    ('measure', False, 'MEASURE (\\(f,s,i,j,n). n - j)'),
  ('mlstring', 'fields_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4). (\\n. n) x4)'),
  ('mlstring', 'isPrefix'):
    ('new_definition', False, ''),
  ('mlstring', 'isStringThere_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4). (\\n. n) x4)'),
  ('mlstring', 'isSubstring'):
    ('new_definition', False, ''),
  ('mlstring', 'isSubstring_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4). (\\n. n) x4)'),
  ('mlstring', 'isSuffix'):
    ('new_definition', False, ''),
  ('mlstring', 'make_app_list_ann'):
    ('measure', False, 'MEASURE (\\x0. app_list_size mlstring_size x0)'),
  ('mlstring', 'mlstring_collate'):
    ('new_definition', False, ''),
  ('mlstring', 'mlstring_collate_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4,x5). (\\n. n) x5)'),
  ('mlstring', 'mlstring_compare'):
    ('new_definition', False, ''),
  ('mlstring', 'mlstring_concat'):
    ('new_definition', False, ''),
  ('mlstring', 'mlstring_extract'):
    ('new_definition', False, ''),
  ('mlstring', 'mlstring_ge'):
    ('new_definition', False, ''),
  ('mlstring', 'mlstring_gt'):
    ('new_definition', False, ''),
  ('mlstring', 'mlstring_le'):
    ('new_definition', False, ''),
  ('mlstring', 'mlstring_lt'):
    ('new_definition', False, ''),
  ('mlstring', 'shrink'):
    ('prim_rec', False, ''),
  ('mlstring', 'splitl'):
    ('new_definition', False, ''),
  ('mlstring', 'splitl_aux'):
    ('measure', False, 'inv_image (<) (\\(x,s,i). strlen s - i)'),
  ('mlstring', 'str_app_list_opt'):
    ('new_definition', False, ''),
  ('mlstring', 'str_findi'):
    ('measure', False, 'MEASURE (\\(P,i,s). strlen s - i)'),
  ('mlstring', 'strcat'):
    ('new_definition', False, ''),
  ('mlstring', 'strlen'):
    ('define_single', False, ''),
  ('mlstring', 'strsub'):
    ('define_single', False, ''),
  ('mlstring', 'substring'):
    ('define_single', False, ''),
  ('mlstring', 'sum_sizes'):
    ('prim_rec', False, ''),
  ('mlstring', 'tokens'):
    ('new_definition', False, ''),
  ('mlstring', 'tokens_alt_aux'):
    ('measure', False, 'MEASURE (\\(f,s,i,j,n). n - j)'),
  ('mlstring', 'tokens_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4). (\\n. n) x4)'),
  ('mlstring', 'translate'):
    ('new_definition', False, ''),
  ('mlstring', 'translate_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). (\\n. n) x3)'),
  ('mlstring', 'word8_to_char'):
    ('new_definition', False, ''),
  ('mlvector', 'all'):
    ('new_definition', False, ''),
  ('mlvector', 'all_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). (\\n. n) x3)'),
  ('mlvector', 'exists_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). (\\n. n) x3)'),
  ('mlvector', 'find'):
    ('new_definition', False, ''),
  ('mlvector', 'find_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). (\\n. n) x3)'),
  ('mlvector', 'findi_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). (\\n. n) x3)'),
  ('mlvector', 'foldl_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4). (\\n. n) x4)'),
  ('mlvector', 'foldr'):
    ('new_definition', False, ''),
  ('mlvector', 'foldr_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). (\\n. n) x3)'),
  ('mlvector', 'foldri'):
    ('new_definition', False, ''),
  ('mlvector', 'foldri_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). (\\n. n) x3)'),
  ('mlvector', 'mlvector_collate'):
    ('new_definition', False, ''),
  ('mlvector', 'mlvector_collate_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4,x5). (\\n. n) x5)'),
  ('mlvector', 'mlvector_concat'):
    ('new_definition', False, ''),
  ('mlvector', 'mlvector_exists'):
    ('new_definition', False, ''),
  ('mlvector', 'mlvector_findi'):
    ('new_definition', False, ''),
  ('mlvector', 'mlvector_foldl'):
    ('new_definition', False, ''),
  ('mlvector', 'mlvector_foldli'):
    ('new_definition', False, ''),
  ('mlvector', 'mlvector_foldli_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4). (\\n. n) x4)'),
  ('mlvector', 'mlvector_map'):
    ('new_definition', False, ''),
  ('mlvector', 'mlvector_mapi'):
    ('new_definition', False, ''),
  ('mlvector', 'mlvector_tabulate'):
    ('new_definition', False, ''),
  ('mlvector', 'mlvector_toList'):
    ('new_definition', False, ''),
  ('mlvector', 'sub_unsafe'):
    ('define_single', False, ''),
  ('mlvector', 'toList_aux'):
    ('measure', False, 'MEASURE (\\(vec,n). length vec - n)'),
  ('mlvector', 'update'):
    ('new_definition', False, ''),
  ('multiword', 'b2n'):
    ('define_single', False, ''),
  ('multiword', 'b2w'):
    ('new_definition', False, ''),
  ('multiword', 'i2mw'):
    ('new_definition', False, ''),
  ('multiword', 'multiword_int_op'):
    ('new_recursive_definition', False, ''),
  ('multiword', 'mw2n'):
    ('prim_rec', False, ''),
  ('multiword', 'mw_cmp'):
    ('guess', False, ''),
  ('multiword', 'mw_ok'):
    ('new_definition', False, ''),
  ('multiword', 'mw_shift'):
    ('new_definition', False, ''),
  ('multiword', 'mw_sub'):
    ('guess', False, ''),
  ('multiword', 'n2mw'):
    ('measure', False, 'MEASURE I'),
  ('multiword', 'single_add'):
    ('new_definition', False, ''),
  ('multiword', 'single_div'):
    ('new_definition', False, ''),
  ('multiword', 'single_div_full'):
    ('new_definition', False, ''),
  ('multiword', 'single_div_loop'):
    ('guess', False, ''),
  ('multiword', 'single_mul'):
    ('new_definition', False, ''),
  ('namespace', 'alist_to_ns'):
    ('new_definition', False, ''),
  ('namespace', 'id_to_mods'):
    ('prim_rec', False, ''),
  ('namespace', 'id_to_n'):
    ('prim_rec', False, ''),
  ('namespace', 'mk_id'):
    ('prim_rec', False, ''),
  ('namespace', 'nsAll'):
    ('new_definition', False, ''),
  ('namespace', 'nsAll2'):
    ('new_definition', False, ''),
  ('namespace', 'nsAppend'):
    ('define_single', False, ''),
  ('namespace', 'nsBind'):
    ('define_single', False, ''),
  ('namespace', 'nsBindList'):
    ('new_definition', False, ''),
  ('namespace', 'nsDom'):
    ('new_definition', False, ''),
  ('namespace', 'nsDomMod'):
    ('new_definition', False, ''),
  ('namespace', 'nsEmpty'):
    ('new_definition', False, ''),
  ('namespace', 'nsLift'):
    ('new_definition', False, ''),
  ('namespace', 'nsLookup'):
    ('measure', False, 'MEASURE (\\(x0,x1). namespace_id_size (\\x. 0) (\\x. 0) x1)'),
  ('namespace', 'nsLookupMod'):
    ('guess', False, ''),
  ('namespace', 'nsMap'):
    ('nested', False, ''),
  ('namespace', 'nsOptBind'):
    ('new_definition', False, ''),
  ('namespace', 'nsSing'):
    ('new_definition', False, ''),
  ('namespace', 'nsSub'):
    ('new_definition', False, ''),
  ('namespaceProps', 'alistSub'):
    ('new_definition', False, ''),
  ('namespaceProps', 'alist_rel_restr'):
    ('prim_rec', False, ''),
  ('namespaceProps', 'nsSub_compute'):
    ('measure', True, ''),
  ('numposrep', 'l2n'):
    ('prim_rec', False, ''),
  ('numposrep', 'n2l'):
    ('measure', False, 'MEASURE (\\(x0,x1). (\\n. n) x1)'),
  ('numposrep', 'num_from_bin_list'):
    ('new_definition', False, ''),
  ('panLang', 'exceptions'):
    ('measure', False, 'MEASURE (\\x0. list_size (decl_size (\\x. 0)) x0)'),
  ('panLang', 'exp_ids'):
    ('match', False, ''),
  ('panLang', 'free_var_ids'):
    ('match', False, ''),
  ('panLang', 'fun_ids'):
    ('match', False, ''),
  ('panLang', 'functions'):
    ('measure', False, 'MEASURE (\\x0. list_size (decl_size (\\x. 0)) x0)'),
  ('panLang', 'global_var_exp'):
    ('measure', False, ''),
  ('panLang', 'inlinable'):
    ('new_definition', False, ''),
  ('panLang', 'is_decl'):
    ('new_definition', False, ''),
  ('panLang', 'is_exn_decl'):
    ('new_definition', False, ''),
  ('panLang', 'is_function'):
    ('new_definition', False, ''),
  ('panLang', 'is_name'):
    ('new_definition', False, ''),
  ('panLang', 'is_wf_ctxt'):
    ('prim_rec', False, ''),
  ('panLang', 'is_wf_flds'):
    ('prim_rec', False, ''),
  ('panLang', 'is_wf_shape'):
    ('nested', False, ''),
  ('panLang', 'load_op'):
    ('new_recursive_definition', False, ''),
  ('panLang', 'nested_seq'):
    ('prim_rec', False, ''),
  ('panLang', 'shape_to_str'):
    ('measure', False, 'MEASURE (\\x0. shape_size x0)'),
  ('panLang', 'shape_val'):
    ('prim_rec', False, ''),
  ('panLang', 'size_of_eids'):
    ('new_definition', False, ''),
  ('panLang', 'size_of_sh_with_ctxt'):
    ('nested', False, ''),
  ('panLang', 'size_of_shape'):
    ('nested', False, ''),
  ('panLang', 'store_op'):
    ('new_recursive_definition', False, ''),
  ('panLang', 'var_exp'):
    ('measure', False, ''),
  ('panLang', 'with_shape'):
    ('prim_rec', False, ''),
  ('parmove', 'eqenv'):
    ('new_definition', False, ''),
  ('parmove', 'fstep'):
    ('new_definition', False, ''),
  ('parmove', 'inj_on_state'):
    ('new_definition', False, ''),
  ('parmove', 'map_state'):
    ('new_definition', False, ''),
  ('parmove', 'not_use_temp_before_assign'):
    ('measure', False, 'MEASURE (\\x0. list_size (pair_size (option_size (\\x. 0)) (option_size (\\x. 0))) x0)'),
  ('parmove', 'parmove'):
    ('new_definition', False, ''),
  ('parmove', 'parmove_path'):
    ('measure', False, 'MEASURE (\\x0. list_size (pair_size (\\x. 0) (\\x. 0)) x0)'),
  ('parmove', 'parmove_wf'):
    ('new_definition', False, ''),
  ('parmove', 'parsem'):
    ('new_definition', False, ''),
  ('parmove', 'pmov'):
    ('guess', False, ''),
  ('parmove', 'sem'):
    ('new_definition', False, ''),
  ('parmove', 'seqsem'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (pair_size (\\x. 0) (\\x. 0)) x0)'),
  ('parmove', 'state_to_list'):
    ('new_definition', False, ''),
  ('parmove', 'windmill'):
    ('new_definition', False, ''),
  ('pattern_comp', 'get_pos'):
    ('prim_rec', False, ''),
  ('pattern_comp', 'insert_Any'):
    ('measure', False, 'MEASURE (\\x0. list_size (pair_size pattern_semantics_pat_size (\\x. 0)) x0)'),
  ('pattern_comp', 'is_Any'):
    ('match', False, ''),
  ('pattern_comp', 'is_Or_row'):
    ('new_definition', False, ''),
  ('pattern_comp', 'is_True'):
    ('new_definition', False, ''),
  ('pattern_comp', 'is_const_row'):
    ('new_definition', False, ''),
  ('pattern_comp', 'mk_Conj'):
    ('new_definition', False, ''),
  ('pattern_comp', 'mk_Disj'):
    ('new_definition', False, ''),
  ('pattern_comp', 'mk_If'):
    ('new_definition', False, ''),
  ('pattern_comp', 'move_const_up'):
    ('new_definition', False, ''),
  ('pattern_comp', 'pat_to_guard'):
    ('measure', True, ''),
  ('pattern_comp', 'pats_to_code'):
    ('prim_rec', False, ''),
  ('pattern_comp', 'pattern_comp_comp'):
    ('new_definition', False, ''),
  ('pattern_comp', 'pattern_comp_walk'):
    ('prim_rec', False, ''),
  ('pattern_comp', 'take_until_Any'):
    ('prim_rec', False, ''),
  ('pattern_comp', 'walk_list'):
    ('new_definition', False, ''),
  ('pattern_exh', 'add_head'):
    ('prim_rec', False, ''),
  ('pattern_exh', 'anys'):
    ('measure', False, 'MEASURE (\\x0. (\\n. n) x0)'),
  ('pattern_exh', 'col_ctors'):
    ('measure', False, 'MEASURE (\\x0. list_size pattern_semantics_pat_size1 x0)'),
  ('pattern_exh', 'ctor_arity'):
    ('new_recursive_definition', False, ''),
  ('pattern_exh', 'ctor_inter'):
    ('new_definition', False, ''),
  ('pattern_exh', 'ctor_keep'):
    ('prim_rec', False, ''),
  ('pattern_exh', 'ctor_nub'):
    ('prim_rec', False, ''),
  ('pattern_exh', 'ctors_of'):
    ('new_definition', False, ''),
  ('pattern_exh', 'default_mat'):
    ('prim_rec', False, ''),
  ('pattern_exh', 'default_row'):
    ('new_definition', False, ''),
  ('pattern_exh', 'dest_val'):
    ('new_definition', False, ''),
  ('pattern_exh', 'exh_all'):
    ('measure', True, ''),
  ('pattern_exh', 'exh_matrix'):
    ('measure', True, ''),
  ('pattern_exh', 'exh_rows'):
    ('new_definition', False, ''),
  ('pattern_exh', 'exh_steps'):
    ('measure', True, ''),
  ('pattern_exh', 'expand'):
    ('prim_rec', False, ''),
  ('pattern_exh', 'mat_len'):
    ('prim_rec', False, ''),
  ('pattern_exh', 'mat_weight'):
    ('prim_rec', False, ''),
  ('pattern_exh', 'mats_len'):
    ('prim_rec', False, ''),
  ('pattern_exh', 'mats_weight'):
    ('prim_rec', False, ''),
  ('pattern_exh', 'mk_conses'):
    ('prim_rec', False, ''),
  ('pattern_exh', 'mk_prods'):
    ('prim_rec', False, ''),
  ('pattern_exh', 'mk_refs'):
    ('prim_rec', False, ''),
  ('pattern_exh', 'mk_rows'):
    ('prim_rec', False, ''),
  ('pattern_exh', 'or_rows'):
    ('prim_rec', False, ''),
  ('pattern_exh', 'pand'):
    ('new_recursive_definition', False, ''),
  ('pattern_exh', 'pat_weight'):
    ('prim_rec', False, ''),
  ('pattern_exh', 'spec_mat'):
    ('prim_rec', False, ''),
  ('pattern_exh', 'spec_mats'):
    ('prim_rec', False, ''),
  ('pattern_exh', 'spec_row'):
    ('new_definition', False, ''),
  ('pattern_exh', 'tag_ctors'):
    ('prim_rec', False, ''),
  ('pattern_semantics', 'app_pos'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). position_size x1)'),
  ('pattern_semantics', 'dt_eval'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). dTree_size x2)'),
  ('pattern_semantics', 'dt_eval_guard'):
    ('prim_rec', False, ''),
  ('pattern_semantics', 'dt_test'):
    ('new_definition', False, ''),
  ('pattern_semantics', 'is_sibling'):
    ('new_recursive_definition', False, ''),
  ('pattern_semantics', 'pattern_semantics_match'):
    ('prim_rec', False, ''),
  ('pattern_semantics', 'pattern_semantics_pmatch'):
    ('measure', False, ''),
  ('peg', 'Gexprs'):
    ('new_definition', False, ''),
  ('peg', 'MAXerr'):
    ('new_definition', False, ''),
  ('peg', 'ignoreL'):
    ('new_definition', False, ''),
  ('peg', 'ignoreR'):
    ('new_definition', False, ''),
  ('peg', 'isFailure'):
    ('new_recursive_definition', False, ''),
  ('peg', 'isSuccess'):
    ('new_recursive_definition', False, ''),
  ('peg', 'optmax'):
    ('new_definition', False, ''),
  ('peg', 'peg_choicel'):
    ('prim_rec', False, ''),
  ('peg', 'peg_pegf'):
    ('new_definition', False, ''),
  ('peg', 'resultmap'):
    ('new_recursive_definition', False, ''),
  ('peg', 'sloc'):
    ('new_recursive_definition', False, ''),
  ('peg', 'subexprs'):
    ('measure', False, 'MEASURE (\\x0. pegsym_size (\\x. 0) (\\x. 0) (\\x. 0) (\\x. 0) x0)'),
  ('peg', 'wfG'):
    ('new_definition', False, ''),
  ('pegComplete', 'leftLoc'):
    ('define_single', False, ''),
  ('pegComplete', 'left_insert'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). parsetree_size locs_size (\\x. 0) (\\x. 0) x0)'),
  ('pegComplete', 'left_insert1'):
    ('measure', False, 'MEASURE (\\(x0,x1). parsetree_size locs_size (\\x. 0) (\\x. 0) x1)'),
  ('pegComplete', 'left_insert2'):
    ('measure', False, 'MEASURE (\\(x0,x1). parsetree_size locs_size (\\x. 0) (\\x. 0) x1)'),
  ('pegComplete', 'leftmost'):
    ('measure', False, 'MEASURE (\\x0. parsetree_size (\\x. 0) MMLnonT_size (\\x. 0) x0)'),
  ('pegComplete', 'nestoppers'):
    ('new_definition', False, ''),
  ('pegComplete', 'pegComplete_stoppers'):
    ('new_definition', False, ''),
  ('pegComplete', 'rightLoc'):
    ('define_single', False, ''),
  ('pegComplete', 'sym2peg'):
    ('new_recursive_definition', False, ''),
  ('pegSound', 'pegsym_to_sym'):
    ('new_definition', False, ''),
  ('pegexec', 'coreloop'):
    ('new_definition', False, ''),
  ('pegexec', 'peg_exec'):
    ('new_definition', False, ''),
  ('pegexec', 'pegexec_destResult'):
    ('define_single', False, ''),
  ('pegexec', 'pegparse'):
    ('new_definition', False, ''),
  ('pegexec', 'poplist_aux'):
    ('cases', False, ''),
  ('pegexec', 'poplistval'):
    ('new_definition', False, ''),
  ('presLang', 'add_name_hint'):
    ('new_definition', False, ''),
  ('presLang', 'arith_to_display'):
    ('new_recursive_definition', False, ''),
  ('presLang', 'asm_addr_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'asm_arith_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'asm_asm_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'asm_binop_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'asm_cmp_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'asm_fp_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'asm_inst_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'asm_memop_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'asm_reg_imm_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'ast_t_to_display'):
    ('measure', False, 'MEASURE (\\x0. ast_t_size x0)'),
  ('presLang', 'attach_name'):
    ('new_recursive_definition', False, ''),
  ('presLang', 'bool_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'bvi_fun_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'bvi_to_display'):
    ('measure', False, ''),
  ('presLang', 'bvi_to_strs'):
    ('new_definition', False, ''),
  ('presLang', 'bvl_fun_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'bvl_to_display'):
    ('measure', False, 'MEASURE (sum_measure (\\(x0,x1,x2). bvl_exp_size x2) (\\(x0,x1,x2,x3). bvl_exp_size1 x3))'),
  ('presLang', 'bvl_to_strs'):
    ('new_definition', False, ''),
  ('presLang', 'clos_dec_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'clos_fun_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'clos_op_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'clos_to_display'):
    ('measure', False, ''),
  ('presLang', 'clos_to_strs'):
    ('new_definition', False, ''),
  ('presLang', 'const_part_to_display'):
    ('new_recursive_definition', False, ''),
  ('presLang', 'const_to_display'):
    ('prim_rec', False, ''),
  ('presLang', 'data_fun_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'data_prog_to_display'):
    ('measure', False, 'MEASURE (\\x. match x with INL (k,_20,_21) -> k | INR (k,_22,_23) -> k)'),
  ('presLang', 'data_seqs'):
    ('measure', False, 'MEASURE (\\x0. dataLang_prog_size x0)'),
  ('presLang', 'data_to_strs'):
    ('new_definition', False, ''),
  ('presLang', 'default_tap_config'):
    ('new_definition', False, ''),
  ('presLang', 'display_num_as_varn'):
    ('new_definition', False, ''),
  ('presLang', 'empty_item'):
    ('new_definition', False, ''),
  ('presLang', 'exp_to_display'):
    ('measure', True, ''),
  ('presLang', 'flat_op_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'flat_pat_to_display'):
    ('measure', False, 'MEASURE (\\x0. flatLang_pat_size x0)'),
  ('presLang', 'flat_to_display'):
    ('nested', False, ''),
  ('presLang', 'flat_to_strs'):
    ('new_definition', False, ''),
  ('presLang', 'fp_bop_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'fp_cmp_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'fp_top_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'fp_uop_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'id_to_display'):
    ('prim_rec', False, ''),
  ('presLang', 'int_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'item_with_num'):
    ('new_definition', False, ''),
  ('presLang', 'item_with_nums'):
    ('new_definition', False, ''),
  ('presLang', 'item_with_word'):
    ('new_definition', False, ''),
  ('presLang', 'lab_asm_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'lab_fun_to_display'):
    ('define_single', False, ''),
  ('presLang', 'lab_line_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'lab_to_strs'):
    ('new_definition', False, ''),
  ('presLang', 'lit_to_display'):
    ('new_recursive_definition', False, ''),
  ('presLang', 'lop_to_display'):
    ('new_recursive_definition', False, ''),
  ('presLang', 'map_to_append'):
    ('prim_rec', False, ''),
  ('presLang', 'num_set_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'num_sets_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'num_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'num_to_hex'):
    ('measure', False, 'MEASURE (\\x0. (\\n. n) x0)'),
  ('presLang', 'num_to_hex_mlstring'):
    ('new_definition', False, ''),
  ('presLang', 'num_to_varn'):
    ('new_definition', False, ''),
  ('presLang', 'num_to_varn_aux'):
    ('measure', False, 'MEASURE I'),
  ('presLang', 'num_to_varn_list'):
    ('measure', False, 'MEASURE (\\(x0,x1). (\\n. n) x1)'),
  ('presLang', 'op_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'opb_to_display'):
    ('new_recursive_definition', False, ''),
  ('presLang', 'opt_con_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'opw_to_display'):
    ('new_recursive_definition', False, ''),
  ('presLang', 'pat_to_display'):
    ('measure', False, 'MEASURE (\\x0. ast_pat_size x0)'),
  ('presLang', 'presLang_commas'):
    ('measure', False, 'MEASURE (\\x0. list_size mlstring_size x0)'),
  ('presLang', 'prim_type_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'separate_lines'):
    ('new_definition', False, ''),
  ('presLang', 'shift_to_display'):
    ('new_recursive_definition', False, ''),
  ('presLang', 'source_to_display_dec'):
    ('measure', False, 'MEASURE (\\x0. dec_size x0)'),
  ('presLang', 'source_to_strs'):
    ('new_definition', False, ''),
  ('presLang', 'stack_fun_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'stack_prog_to_display'):
    ('measure', False, ''),
  ('presLang', 'stack_seqs'):
    ('measure', False, 'MEASURE (\\x0. stackLang_prog_size (\\x. 0) x0)'),
  ('presLang', 'stack_to_strs'):
    ('new_definition', False, ''),
  ('presLang', 'store_name_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'string_imp'):
    ('new_definition', False, ''),
  ('presLang', 'test_to_display'):
    ('new_recursive_definition', False, ''),
  ('presLang', 'thunk_mode_to_display'):
    ('new_recursive_definition', False, ''),
  ('presLang', 'thunk_op_to_display'):
    ('new_recursive_definition', False, ''),
  ('presLang', 'word_exp_to_display'):
    ('prim_rec', False, ''),
  ('presLang', 'word_fun_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'word_prog_to_display'):
    ('measure', False, ''),
  ('presLang', 'word_seqs'):
    ('measure', False, 'MEASURE (\\x0. wordLang_prog_size (\\x. 0) x0)'),
  ('presLang', 'word_size_to_display'):
    ('new_recursive_definition', False, ''),
  ('presLang', 'word_to_display'):
    ('new_definition', False, ''),
  ('presLang', 'word_to_strs'):
    ('new_definition', False, ''),
  ('presLang', 'ws_to_display'):
    ('prim_rec', False, ''),
  ('primTypes', 'add_to_sem_env'):
    ('new_definition', False, ''),
  ('primTypes', 'prim_sem_env'):
    ('new_definition', False, ''),
  ('primTypes', 'prim_tenv'):
    ('new_definition', False, ''),
  ('primTypes', 'prim_type_ids'):
    ('new_definition', False, ''),
  ('primTypes', 'prim_types_program'):
    ('new_definition', False, ''),
  ('reg_alloc', 'add_freeze_wl'):
    ('new_definition', False, ''),
  ('reg_alloc', 'add_simp_wl'):
    ('new_definition', False, ''),
  ('reg_alloc', 'add_spill_wl'):
    ('new_definition', False, ''),
  ('reg_alloc', 'add_unavail_moves_wl'):
    ('new_definition', False, ''),
  ('reg_alloc', 'adj_ls_length'):
    ('new_definition', False, ''),
  ('reg_alloc', 'adj_ls_sub'):
    ('new_definition', False, ''),
  ('reg_alloc', 'assign_Atemp_tag'):
    ('new_definition', False, ''),
  ('reg_alloc', 'assign_Atemps'):
    ('new_definition', False, ''),
  ('reg_alloc', 'assign_Stemp_tag'):
    ('new_definition', False, ''),
  ('reg_alloc', 'assign_Stemps'):
    ('new_definition', False, ''),
  ('reg_alloc', 'bg_ok'):
    ('new_definition', False, ''),
  ('reg_alloc', 'biased_pref'):
    ('new_definition', False, ''),
  ('reg_alloc', 'canonize_move'):
    ('new_definition', False, ''),
  ('reg_alloc', 'check_clash_tree'):
    ('prim_rec', False, ''),
  ('reg_alloc', 'check_col'):
    ('new_definition', False, ''),
  ('reg_alloc', 'check_partial_col'):
    ('prim_rec', False, ''),
  ('reg_alloc', 'clique_insert_edge'):
    ('measure', False, 'MEASURE (\\x0. list_size (\\n. n) x0)'),
  ('reg_alloc', 'coalesce_parent'):
    ('measure', False, 'MEASURE (\\x0. (\\n. n) x0)'),
  ('reg_alloc', 'coalesce_root'):
    ('measure', False, 'MEASURE (\\x0. (\\n. n) x0)'),
  ('reg_alloc', 'coalesced_length'):
    ('new_definition', False, ''),
  ('reg_alloc', 'coalesced_sub'):
    ('new_definition', False, ''),
  ('reg_alloc', 'considered_var'):
    ('new_definition', False, ''),
  ('reg_alloc', 'consistency_ok'):
    ('new_definition', False, ''),
  ('reg_alloc', 'dec_deg'):
    ('new_definition', False, ''),
  ('reg_alloc', 'dec_degree'):
    ('new_definition', False, ''),
  ('reg_alloc', 'deg_or_inf'):
    ('new_definition', False, ''),
  ('reg_alloc', 'degrees_length'):
    ('new_definition', False, ''),
  ('reg_alloc', 'degrees_sub'):
    ('new_definition', False, ''),
  ('reg_alloc', 'do_alloc1'):
    ('new_definition', False, ''),
  ('reg_alloc', 'do_coalesce'):
    ('new_definition', False, ''),
  ('reg_alloc', 'do_coalesce_real'):
    ('new_definition', False, ''),
  ('reg_alloc', 'do_freeze'):
    ('new_definition', False, ''),
  ('reg_alloc', 'do_prefreeze'):
    ('new_definition', False, ''),
  ('reg_alloc', 'do_reg_alloc'):
    ('new_definition', False, ''),
  ('reg_alloc', 'do_simplify'):
    ('new_definition', False, ''),
  ('reg_alloc', 'do_spill'):
    ('new_definition', False, ''),
  ('reg_alloc', 'do_step'):
    ('new_definition', False, ''),
  ('reg_alloc', 'do_upd_coalesce'):
    ('new_definition', False, ''),
  ('reg_alloc', 'extend_clique'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (\\n. n) x0)'),
  ('reg_alloc', 'extend_graph'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (pair_size (\\x. 0) (\\x. 0)) x1)'),
  ('reg_alloc', 'extract_color'):
    ('new_definition', False, ''),
  ('reg_alloc', 'extract_tag'):
    ('new_definition', False, ''),
  ('reg_alloc', 'first_match_col'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (\\n. n) x1)'),
  ('reg_alloc', 'full_consistency_ok'):
    ('new_definition', False, ''),
  ('reg_alloc', 'get_adj_ls'):
    ('new_definition', False, ''),
  ('reg_alloc', 'get_avail_moves_wl'):
    ('new_definition', False, ''),
  ('reg_alloc', 'get_coalesced'):
    ('new_definition', False, ''),
  ('reg_alloc', 'get_degrees'):
    ('new_definition', False, ''),
  ('reg_alloc', 'get_dim'):
    ('new_definition', False, ''),
  ('reg_alloc', 'get_freeze_wl'):
    ('new_definition', False, ''),
  ('reg_alloc', 'get_move_related'):
    ('new_definition', False, ''),
  ('reg_alloc', 'get_node_tag'):
    ('new_definition', False, ''),
  ('reg_alloc', 'get_simp_wl'):
    ('new_definition', False, ''),
  ('reg_alloc', 'get_spill_wl'):
    ('new_definition', False, ''),
  ('reg_alloc', 'get_unavail_moves_wl'):
    ('new_definition', False, ''),
  ('reg_alloc', 'handle_Fail'):
    ('new_definition', False, ''),
  ('reg_alloc', 'handle_Subscript'):
    ('new_definition', False, ''),
  ('reg_alloc', 'inc_deg'):
    ('new_definition', False, ''),
  ('reg_alloc', 'init_alloc1_heu'):
    ('new_definition', False, ''),
  ('reg_alloc', 'init_ra_state'):
    ('new_definition', False, ''),
  ('reg_alloc', 'insert_edge'):
    ('new_definition', False, ''),
  ('reg_alloc', 'is_Atemp'):
    ('new_definition', False, ''),
  ('reg_alloc', 'is_Fixed'):
    ('new_definition', False, ''),
  ('reg_alloc', 'is_Fixed_k'):
    ('new_definition', False, ''),
  ('reg_alloc', 'is_alloc_var'):
    ('new_definition', False, ''),
  ('reg_alloc', 'is_not_coalesced'):
    ('new_definition', False, ''),
  ('reg_alloc', 'is_phy_var'):
    ('new_definition', False, ''),
  ('reg_alloc', 'is_stack_var'):
    ('new_definition', False, ''),
  ('reg_alloc', 'list_insert_edge'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (\\n. n) x1)'),
  ('reg_alloc', 'list_remap'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (\\n. n) x0)'),
  ('reg_alloc', 'mk_bij'):
    ('new_definition', False, ''),
  ('reg_alloc', 'mk_bij_aux'):
    ('prim_rec', False, ''),
  ('reg_alloc', 'mk_graph'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). clash_tree_size x1)'),
  ('reg_alloc', 'mk_tags'):
    ('new_definition', False, ''),
  ('reg_alloc', 'move_related_length'):
    ('new_definition', False, ''),
  ('reg_alloc', 'move_related_sub'):
    ('new_definition', False, ''),
  ('reg_alloc', 'moves_to_sp'):
    ('prim_rec', False, ''),
  ('reg_alloc', 'neg_biased_pref'):
    ('new_definition', False, ''),
  ('reg_alloc', 'neg_first_match_col'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). list_size (\\n. n) x2)'),
  ('reg_alloc', 'node_tag_length'):
    ('new_definition', False, ''),
  ('reg_alloc', 'node_tag_sub'):
    ('new_definition', False, ''),
  ('reg_alloc', 'numset_list_delete'):
    ('prim_rec', False, ''),
  ('reg_alloc', 'pri_move_insert'):
    ('new_definition', False, ''),
  ('reg_alloc', 'push_stack'):
    ('new_definition', False, ''),
  ('reg_alloc', 'raise_Fail'):
    ('new_definition', False, ''),
  ('reg_alloc', 'raise_Subscript'):
    ('new_definition', False, ''),
  ('reg_alloc', 'reg_alloc'):
    ('new_definition', False, ''),
  ('reg_alloc', 'reg_alloc_aux'):
    ('new_definition', False, ''),
  ('reg_alloc', 'reg_alloc_get_stack'):
    ('new_definition', False, ''),
  ('reg_alloc', 'reg_alloc_sort_moves'):
    ('new_definition', False, ''),
  ('reg_alloc', 'remove_colours'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (\\n. n) x0)'),
  ('reg_alloc', 'reset_move_related'):
    ('new_definition', False, ''),
  ('reg_alloc', 'resort_moves'):
    ('new_definition', False, ''),
  ('reg_alloc', 'respill'):
    ('new_definition', False, ''),
  ('reg_alloc', 'revive_moves'):
    ('new_definition', False, ''),
  ('reg_alloc', 'rpt_do_step'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x2)'),
  ('reg_alloc', 'run_ira_state'):
    ('new_definition', False, ''),
  ('reg_alloc', 'safe_div'):
    ('new_definition', False, ''),
  ('reg_alloc', 'set_adj_ls'):
    ('new_definition', False, ''),
  ('reg_alloc', 'set_avail_moves_wl'):
    ('new_definition', False, ''),
  ('reg_alloc', 'set_coalesced'):
    ('new_definition', False, ''),
  ('reg_alloc', 'set_degrees'):
    ('new_definition', False, ''),
  ('reg_alloc', 'set_dim'):
    ('new_definition', False, ''),
  ('reg_alloc', 'set_freeze_wl'):
    ('new_definition', False, ''),
  ('reg_alloc', 'set_move_related'):
    ('new_definition', False, ''),
  ('reg_alloc', 'set_node_tag'):
    ('new_definition', False, ''),
  ('reg_alloc', 'set_simp_wl'):
    ('new_definition', False, ''),
  ('reg_alloc', 'set_spill_wl'):
    ('new_definition', False, ''),
  ('reg_alloc', 'set_stack'):
    ('new_definition', False, ''),
  ('reg_alloc', 'set_unavail_moves_wl'):
    ('new_definition', False, ''),
  ('reg_alloc', 'smerge'):
    ('measure', False, 'MEASURE (\\(x0,x1).      list_size (pair_size (\\n. n) (\\x. 0)) x0 +      list_size (pair_size (\\n. n) (\\x. 0)) x1)'),
  ('reg_alloc', 'sorted_insert'):
    ('prim_rec', False, ''),
  ('reg_alloc', 'sorted_mem'):
    ('prim_rec', False, ''),
  ('reg_alloc', 'sp_default'):
    ('new_definition', False, ''),
  ('reg_alloc', 'split_degree'):
    ('new_definition', False, ''),
  ('reg_alloc', 'st_ex_FILTER'):
    ('measure', True, ''),
  ('reg_alloc', 'st_ex_FIRST'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3).      list_size (pair_size (\\x. 0) (pair_size (\\n. n) (\\n. n))) x2)'),
  ('reg_alloc', 'st_ex_FOREACH'):
    ('guess', False, ''),
  ('reg_alloc', 'st_ex_MAP'):
    ('measure', True, ''),
  ('reg_alloc', 'st_ex_PARTITION'):
    ('measure', True, ''),
  ('reg_alloc', 'st_ex_list_MAX_deg'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4). list_size (\\n. n) x0)'),
  ('reg_alloc', 'st_ex_list_MIN_cost'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4,x5). list_size (\\n. n) x1)'),
  ('reg_alloc', 'tag_col'):
    ('new_definition', False, ''),
  ('reg_alloc', 'unbound_colour'):
    ('prim_rec', False, ''),
  ('reg_alloc', 'undir_move_insert'):
    ('new_definition', False, ''),
  ('reg_alloc', 'unspill'):
    ('new_definition', False, ''),
  ('reg_alloc', 'update_adj_ls'):
    ('new_definition', False, ''),
  ('reg_alloc', 'update_coalesced'):
    ('new_definition', False, ''),
  ('reg_alloc', 'update_degrees'):
    ('new_definition', False, ''),
  ('reg_alloc', 'update_move'):
    ('new_definition', False, ''),
  ('reg_alloc', 'update_move_related'):
    ('new_definition', False, ''),
  ('reg_alloc', 'update_node_tag'):
    ('new_definition', False, ''),
  ('reg_allocProof', 'colouring_satisfactory'):
    ('new_definition', False, ''),
  ('reg_allocProof', 'good_neg_pref'):
    ('new_definition', False, ''),
  ('reg_allocProof', 'good_pref'):
    ('new_definition', False, ''),
  ('reg_allocProof', 'good_ra_state'):
    ('new_definition', False, ''),
  ('reg_allocProof', 'has_edge'):
    ('new_definition', False, ''),
  ('reg_allocProof', 'in_clash_tree'):
    ('prim_rec', False, ''),
  ('reg_allocProof', 'is_clique'):
    ('new_definition', False, ''),
  ('reg_allocProof', 'is_subgraph'):
    ('new_definition', False, ''),
  ('reg_allocProof', 'no_clash'):
    ('new_definition', False, ''),
  ('reg_allocProof', 'reg_allocProof_hide'):
    ('new_definition', False, ''),
  ('reg_allocProof', 'sp_inverts'):
    ('new_definition', False, ''),
  ('reg_allocProof', 'undirected'):
    ('new_definition', False, ''),
  ('regexp_compiler', 'length'):
    ('define_single', False, ''),
  ('regexp_compiler', 'sub'):
    ('define_single', False, ''),
  ('riscv_config', 'riscv_backend_config'):
    ('new_definition', False, ''),
  ('riscv_config', 'riscv_names'):
    ('new_definition', False, ''),
  ('rmfmap', 'soc'):
    ('new_definition', False, ''),
  ('rmfmap', 'sunify'):
    ('new_definition', False, ''),
  ('rmfmap', 'svwalk'):
    ('new_definition', False, ''),
  ('rmfmap', 'swalk'):
    ('new_definition', False, ''),
  ('rmfmap', 'swfs'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'add_decs_generation'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'add_env_generation'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'ast_t_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'bind_stamp'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'bool_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'build_constrs'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'build_conv'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'build_tdefs'):
    ('prim_rec', False, ''),
  ('semanticPrimitives', 'can_pmatch_all'):
    ('prim_rec', False, ''),
  ('semanticPrimitives', 'chars_to_ws'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'check_dup_ctors'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'chr_stamp'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'combine_dec_result'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'compiler_agrees'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'concrete_v'):
    ('measure', False, 'MEASURE (\\x0. semanticPrimitives_v_size x0)'),
  ('semanticPrimitives', 'copy_array'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'dec_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'declare_env'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'div_stamp'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'do_arith'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'do_con_check'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'do_conversion'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'do_log'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'empty_store'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'exp_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'extend_dec_env'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'find_recfun'):
    ('match', False, ''),
  ('semanticPrimitives', 'fp_bop_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'fp_cmp_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'fp_top_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'fp_uop_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'id_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'list_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'lit_same_type'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'lit_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'locn_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'locs_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'lookup_env'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'lop_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'maybe_all_list'):
    ('match', False, ''),
  ('semanticPrimitives', 'maybe_to_v'):
    ('new_recursive_definition', False, ''),
  ('semanticPrimitives', 'nat_to_v'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'one_con_check'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'op_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'opb_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'opn_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'option_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'opw_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'pat_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'reset_env_generation'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'same_ctor'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'same_type'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_Boolv'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_bad_thunk_update'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_bind_exn_v'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_build_rec_env'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_check_type'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_chr_exn_v'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_ctor_same_type'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_dest_Litv'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_dest_thunk'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_div_exn_v'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_do_app'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_do_eq'):
    ('measure', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_do_eval'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_do_if'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_do_opapp'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_do_test'):
    ('new_recursive_definition', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_int_cmp'):
    ('new_recursive_definition', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_list_to_v'):
    ('prim_rec', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_num_cmp'):
    ('new_recursive_definition', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_pmatch'):
    ('measure', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_the_Litv_Float64'):
    ('define_single', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_thunk_op'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_update_thunk'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'semanticPrimitives_v_to_char_list'):
    ('measure', False, 'MEASURE (\\x0. semanticPrimitives_v_size x0)'),
  ('semanticPrimitives', 'semanticPrimitives_v_to_list'):
    ('measure', False, 'MEASURE (\\x0. semanticPrimitives_v_size x0)'),
  ('semanticPrimitives', 'semanticPrimitives_vs_to_string'):
    ('measure', False, 'MEASURE (\\x0. semanticPrimitives_v_size3 x0)'),
  ('semanticPrimitives', 'shift64_lookup'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'shift8_lookup'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'shift_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'store_alloc'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'store_assign'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'store_lookup'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'store_v_same_type'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'str_cmp'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'sub_exn_v'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'subscript_stamp'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'the_Boolv'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'the_Litv_Char'):
    ('define_single', False, ''),
  ('semanticPrimitives', 'the_Litv_IntLit'):
    ('define_single', False, ''),
  ('semanticPrimitives', 'the_Litv_Word64'):
    ('define_single', False, ''),
  ('semanticPrimitives', 'the_Litv_Word8'):
    ('define_single', False, ''),
  ('semanticPrimitives', 'v_to_id'):
    ('measure', False, 'MEASURE (\\x0. semanticPrimitives_v_size x0)'),
  ('semanticPrimitives', 'v_to_word64'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'v_to_word64_list'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'v_to_word8'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'v_to_word8_list'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'word_size_type_num'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'ws_to_chars'):
    ('new_definition', False, ''),
  ('semanticPrimitives', 'xor_bytes'):
    ('guess', False, ''),
  ('semanticPrimitivesProps', 'FV'):
    ('measure', False, ''),
  ('semanticPrimitivesProps', 'FV_dec'):
    ('define_single', False, ''),
  ('semanticPrimitivesProps', 'ctors_of_dec'):
    ('new_definition', False, ''),
  ('semanticPrimitivesProps', 'ctors_of_tdef'):
    ('new_definition', False, ''),
  ('semanticPrimitivesProps', 'dest_Refv'):
    ('define_single', False, ''),
  ('semanticPrimitivesProps', 'do_shift'):
    ('new_definition', False, ''),
  ('semanticPrimitivesProps', 'every_error_result'):
    ('new_recursive_definition', False, ''),
  ('semanticPrimitivesProps', 'every_result'):
    ('new_recursive_definition', False, ''),
  ('semanticPrimitivesProps', 'exc_rel'):
    ('new_definition', False, ''),
  ('semanticPrimitivesProps', 'is_Refv'):
    ('new_definition', False, ''),
  ('semanticPrimitivesProps', 'map_error_result'):
    ('new_recursive_definition', False, ''),
  ('semanticPrimitivesProps', 'map_match'):
    ('new_definition', False, ''),
  ('semanticPrimitivesProps', 'map_result'):
    ('new_recursive_definition', False, ''),
  ('semanticPrimitivesProps', 'map_sv'):
    ('new_recursive_definition', False, ''),
  ('semanticPrimitivesProps', 'semanticPrimitivesProps_result_rel'):
    ('new_definition', False, ''),
  ('semanticPrimitivesProps', 'semanticPrimitivesProps_store_v_vs'):
    ('new_recursive_definition', False, ''),
  ('semanticPrimitivesProps', 'semanticPrimitivesProps_sv_rel'):
    ('new_definition', False, ''),
  ('semanticPrimitivesProps', 'shift_lookup'):
    ('define_single', False, ''),
  ('semanticPrimitivesProps', 'store_vs'):
    ('new_definition', False, ''),
  ('semanticPrimitivesProps', 'sv_every'):
    ('new_definition', False, ''),
  ('semantics', 'can_type_prog'):
    ('new_definition', False, ''),
  ('semantics', 'evaluate_prog_with_clock'):
    ('new_definition', False, ''),
  ('semantics', 'semantics_init'):
    ('new_definition', False, ''),
  ('semantics', 'semantics_parse'):
    ('new_definition', False, ''),
  ('semantics', 'semantics_prog'):
    ('new_recursive_definition', False, ''),
  ('semantics', 'semantics_semantics'):
    ('new_definition', False, ''),
  ('semanticsProps', 'extend_with_resource_limit'):
    ('new_definition', False, ''),
  ('semanticsProps', "extend_with_resource_limit'"):
    ('new_definition', False, ''),
  ('semanticsProps', 'implements'):
    ('new_definition', False, ''),
  ('semanticsProps', "implements'"):
    ('new_definition', False, ''),
  ('semanticsProps', 'state_invariant'):
    ('new_definition', False, ''),
  ('set_sep', 'SEP_EXISTS'):
    ('new_definition', False, ''),
  ('set_sep', 'SEP_T'):
    ('new_definition', False, ''),
  ('set_sep', 'SPLIT'):
    ('new_definition', False, ''),
  ('set_sep', 'cond'):
    ('new_definition', False, ''),
  ('set_sep', 'emp'):
    ('new_definition', False, ''),
  ('set_sep', 'fun2set'):
    ('new_definition', False, ''),
  ('set_sep', 'set_sep_one'):
    ('new_definition', False, ''),
  ('simpleSexp', 'arb_sexp'):
    ('new_definition', False, ''),
  ('simpleSexp', 'destSXCONS'):
    ('new_definition', False, ''),
  ('simpleSexp', 'destSXNUM'):
    ('new_definition', False, ''),
  ('simpleSexp', 'destSXSYM'):
    ('new_definition', False, ''),
  ('simpleSexp', 'dstrip_sexp'):
    ('new_definition', False, ''),
  ('simpleSexp', 'strip_sxcons'):
    ('match', False, ''),
  ('simpleSexp', 'sxMEM'):
    ('new_definition', False, ''),
  ('simpleSexp', 'valid_first_symchar'):
    ('new_definition', False, ''),
  ('simpleSexp', 'valid_sexp'):
    ('match', False, ''),
  ('simpleSexp', 'valid_symbol'):
    ('new_recursive_definition', False, ''),
  ('simpleSexp', 'valid_symchar'):
    ('new_definition', False, ''),
  ('simpleSexpPEG', 'grabWS'):
    ('new_definition', False, ''),
  ('simpleSexpPEG', 'replace_nil'):
    ('match', False, ''),
  ('simpleSexpPEG', 'sexpPEG'):
    ('new_definition', False, ''),
  ('simpleSexpPEG', 'simpleSexpPEG_choicel'):
    ('prim_rec', False, ''),
  ('simpleSexpPEG', 'simpleSexpPEG_pegf'):
    ('new_definition', False, ''),
  ('simpleSexpPEG', 'simpleSexpPEG_pnt'):
    ('new_definition', False, ''),
  ('simpleSexpPEG', 'simpleSexpPEG_sumID'):
    ('new_recursive_definition', False, ''),
  ('simpleSexpPEG', 'simpleSexpPEG_tokeq'):
    ('new_definition', False, ''),
  ('simpleSexpParse', 'escape_string'):
    ('measure', False, 'MEASURE (\\x0. list_size char_size x0)'),
  ('simpleSexpParse', 'parse_sexp'):
    ('new_definition', False, ''),
  ('simpleSexpParse', 'print_sexp'):
    ('measure', True, ''),
  ('simpleSexpParse', 'print_space_separated'):
    ('measure', False, 'MEASURE (\\x0. list_size (list_size char_size) x0)'),
  ('simpleSexpParse', 'strip_dot'):
    ('prim_rec', False, ''),
  ('sorting', 'PART'):
    ('prim_rec', False, ''),
  ('sorting', 'PARTITION'):
    ('new_definition', False, ''),
  ('sorting', 'PERM'):
    ('new_definition', False, ''),
  ('sorting', 'SORTED'):
    ('guess', False, ''),
  ('sorting', 'SORTS'):
    ('new_definition', False, ''),
  ('source_evalProof', 'adjust_oracle'):
    ('new_definition', False, ''),
  ('source_evalProof', 'do_eval_oracle'):
    ('new_definition', False, ''),
  ('source_evalProof', 'do_eval_record'):
    ('new_definition', False, ''),
  ('source_evalProof', 'es_forward'):
    ('new_definition', False, ''),
  ('source_evalProof', 'es_stack_forward'):
    ('new_definition', False, ''),
  ('source_evalProof', 'extract_oracle'):
    ('new_definition', False, ''),
  ('source_evalProof', 'get_oracle'):
    ('new_definition', False, ''),
  ('source_evalProof', 'insert_gen_oracle'):
    ('new_definition', False, ''),
  ('source_evalProof', 'is_insert_oracle'):
    ('new_definition', False, ''),
  ('source_evalProof', 'is_record'):
    ('new_definition', False, ''),
  ('source_evalProof', 'mk_compiler_fun_from_ci'):
    ('new_definition', False, ''),
  ('source_evalProof', 'mk_init_eval_state'):
    ('new_definition', False, ''),
  ('source_evalProof', 'orac_agrees'):
    ('new_definition', False, ''),
  ('source_evalProof', 'orac_extended_wf'):
    ('new_definition', False, ''),
  ('source_evalProof', 'orac_s'):
    ('new_definition', False, ''),
  ('source_evalProof', 'precond_eval_state'):
    ('new_definition', False, ''),
  ('source_evalProof', 'put_oracle'):
    ('new_definition', False, ''),
  ('source_evalProof', 'record_forward'):
    ('new_definition', False, ''),
  ('source_evalProof', 'recorded_orac_wf'):
    ('new_definition', False, ''),
  ('source_evalProof', 'source_evalProof_abort'):
    ('new_definition', False, ''),
  ('source_evalProof', 'source_evalProof_env_rel'):
    ('new_definition', False, ''),
  ('source_evalProof', 'source_evalProof_match_result_rel'):
    ('new_definition', False, ''),
  ('source_evalProof', 'source_evalProof_s_rel'):
    ('new_definition', False, ''),
  ('source_evalProof', 'v_fun_abs'):
    ('new_definition', False, ''),
  ('source_evalProof', 'v_to_env_id'):
    ('new_definition', False, ''),
  ('source_evalProof', 'v_to_nat'):
    ('new_definition', False, ''),
  ('source_let', 'dest_Let'):
    ('new_definition', False, ''),
  ('source_let', 'dest_Letrec'):
    ('new_definition', False, ''),
  ('source_let', 'lift_let'):
    ('new_definition', False, ''),
  ('source_let', 'lift_lets'):
    ('guess', False, ''),
  ('source_let', 'source_let_compile_decs'):
    ('measure', False, 'MEASURE (list_size dec_size)'),
  ('source_to_flat', 'alloc_defs'):
    ('prim_rec', False, ''),
  ('source_to_flat', 'alloc_env_ref'):
    ('new_definition', False, ''),
  ('source_to_flat', 'alloc_tags'):
    ('new_definition', False, ''),
  ('source_to_flat', 'alloc_tags1'):
    ('prim_rec', False, ''),
  ('source_to_flat', 'astOp_to_flatOp'):
    ('new_definition', False, ''),
  ('source_to_flat', 'compile_flat'):
    ('new_definition', False, ''),
  ('source_to_flat', 'compile_pat'):
    ('nested', False, ''),
  ('source_to_flat', 'compile_var'):
    ('new_recursive_definition', False, ''),
  ('source_to_flat', 'empty_config'):
    ('new_definition', False, ''),
  ('source_to_flat', 'env_id_tuple'):
    ('new_definition', False, ''),
  ('source_to_flat', 'extend_env'):
    ('new_definition', False, ''),
  ('source_to_flat', 'glob_alloc'):
    ('new_definition', False, ''),
  ('source_to_flat', 'inc_compile'):
    ('new_definition', False, ''),
  ('source_to_flat', 'inc_compile_prog'):
    ('new_definition', False, ''),
  ('source_to_flat', 'join_all_names'):
    ('new_definition', False, ''),
  ('source_to_flat', 'join_all_names_aux'):
    ('prim_rec', False, ''),
  ('source_to_flat', 'lift_env'):
    ('new_definition', False, ''),
  ('source_to_flat', 'lookup_env_id'):
    ('new_definition', False, ''),
  ('source_to_flat', 'lookup_inc'):
    ('new_definition', False, ''),
  ('source_to_flat', 'make_varls'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). tra_size x1 + list_size mlstring_size x3)'),
  ('source_to_flat', 'om_tra'):
    ('new_definition', False, ''),
  ('source_to_flat', 'pat_tups'):
    ('prim_rec', False, ''),
  ('source_to_flat', 'simple_dlet'):
    ('new_definition', False, ''),
  ('source_to_flat', 'source_to_flat_compile'):
    ('new_definition', False, ''),
  ('source_to_flat', 'source_to_flat_compile_decs'):
    ('measure', False, ''),
  ('source_to_flat', 'source_to_flat_compile_exp'):
    ('measure', False, ''),
  ('source_to_flat', 'source_to_flat_compile_prog'):
    ('new_definition', False, ''),
  ('source_to_flat', 'source_to_flat_empty_env'):
    ('new_definition', False, ''),
  ('source_to_flat', 'store_env_id'):
    ('new_definition', False, ''),
  ('source_to_flat', 'str_sep'):
    ('new_definition', False, ''),
  ('source_to_flat', 'type_group_id_type'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'ALL_DISJOINT'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'bind_locals'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'env_domain_eq'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'env_gen_future_rel'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'env_gen_inv'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'env_gen_rel'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'env_store_inv'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'eval_ref_inv'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'eval_state_call_rel'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'fin_idx_match'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'genv_allocated_idxs'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'genv_c_ok'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'genv_c_tys_ok'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'has_bools'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'has_exns'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'has_lists'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'idx_block'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'idx_final_block'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'idx_prev'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'idx_range_rel'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'init_eval_state_ok'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'init_genv'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'init_genv_els'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'init_genv_next'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'init_genv_ty_els'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'init_global_env_inv'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'num_bindings'):
    ('measure', False, 'MEASURE dec_size'),
  ('source_to_flatProof', 'orac_config_envs_subspt'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'orac_forward_rel'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'orac_rel'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'precondition'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'precondition1'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'source_to_flatProof_abort'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'source_to_flatProof_invariant'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'source_to_flatProof_match_result_rel'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'src_orac_env_invs'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'src_orac_gen_inv'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'src_orac_invs'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'src_orac_next_cfg'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'src_orac_next_cfg_inner'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'src_orac_step_invs'):
    ('new_definition', False, ''),
  ('source_to_flatProof', 'subglobals'):
    ('new_definition', False, ''),
  ('source_to_source', 'source_to_source_compile'):
    ('new_definition', False, ''),
  ('spt_closure', 'closure_spt'):
    ('measure', False, 'MEASURE (\\(x0,x1). spt_size (spt_size (\\x. 0)) x1)'),
  ('spt_closure', 'is_adjacent'):
    ('new_definition', False, ''),
  ('spt_closure', 'is_reachable'):
    ('new_definition', False, ''),
  ('spt_closure', 'num_set_tree_union'):
    ('prim_rec', False, ''),
  ('sptree', 'alist_insert'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). list_size (\\n. n) x0)'),
  ('sptree', 'difference'):
    ('prim_rec', False, ''),
  ('sptree', 'domain'):
    ('measure', False, 'MEASURE (\\x0. spt_size (\\x. 0) x0)'),
  ('sptree', 'filter_v'):
    ('prim_rec', False, ''),
  ('sptree', 'foldi'):
    ('prim_rec', False, ''),
  ('sptree', 'fromAList'):
    ('prim_rec', False, ''),
  ('sptree', 'inter'):
    ('prim_rec', False, ''),
  ('sptree', 'inter_eq'):
    ('prim_rec', False, ''),
  ('sptree', 'list_insert'):
    ('prim_rec', False, ''),
  ('sptree', 'list_to_num_set'):
    ('prim_rec', False, ''),
  ('sptree', 'lrnext'):
    ('measure', False, 'MEASURE I'),
  ('sptree', 'mapi0'):
    ('prim_rec', False, ''),
  ('sptree', 'mk_BN'):
    ('new_definition', False, ''),
  ('sptree', 'mk_BS'):
    ('new_definition', False, ''),
  ('sptree', 'mk_wf'):
    ('prim_rec', False, ''),
  ('sptree', 'spt_center'):
    ('new_definition', False, ''),
  ('sptree', 'spt_fold'):
    ('prim_rec', False, ''),
  ('sptree', 'spt_left'):
    ('new_recursive_definition', False, ''),
  ('sptree', 'spt_right'):
    ('new_recursive_definition', False, ''),
  ('sptree', 'sptree_delete'):
    ('prim_rec', False, ''),
  ('sptree', 'sptree_fromList'):
    ('new_definition', False, ''),
  ('sptree', 'sptree_insert'):
    ('measure', False, 'MEASURE FST'),
  ('sptree', 'sptree_lookup'):
    ('measure', False, 'MEASURE FST'),
  ('sptree', 'sptree_map'):
    ('prim_rec', False, ''),
  ('sptree', 'sptree_mapi'):
    ('new_definition', False, ''),
  ('sptree', 'sptree_size'):
    ('prim_rec', False, ''),
  ('sptree', 'sptree_toList'):
    ('new_definition', False, ''),
  ('sptree', 'sptree_union'):
    ('prim_rec', False, ''),
  ('sptree', 'sptree_wf'):
    ('prim_rec', False, ''),
  ('sptree', 'spts_to_alist'):
    ('guess', False, ''),
  ('sptree', 'spts_to_alist_add_pause'):
    ('new_definition', False, ''),
  ('sptree', 'spts_to_alist_aux'):
    ('match', False, ''),
  ('sptree', 'subspt'):
    ('prim_rec', False, ''),
  ('sptree', 'toAList'):
    ('new_definition', False, ''),
  ('sptree', 'toListA'):
    ('prim_rec', False, ''),
  ('sptree', 'toSortedAList'):
    ('new_definition', False, ''),
  ('stackLang', 'gc_stub_location'):
    ('new_definition', False, ''),
  ('stackLang', 'stackLang_list_Seq'):
    ('measure', False, 'MEASURE (\\x0. list_size (stackLang_prog_size (\\x. 0)) x0)'),
  ('stackLang', 'stackLang_store_consts_stub_location'):
    ('new_definition', False, ''),
  ('stackProps', 'addr_name'):
    ('define_single', False, ''),
  ('stackProps', 'addr_ok'):
    ('define_single', False, ''),
  ('stackProps', 'alloc_arg'):
    ('measure', False, 'MEASURE (\\x0. stackLang_prog_size (\\x. 0) x0)'),
  ('stackProps', 'arith_name'):
    ('new_definition', False, ''),
  ('stackProps', 'call_args'):
    ('measure', False, ''),
  ('stackProps', 'clock_neutral'):
    ('match', False, ''),
  ('stackProps', 'fixed_names'):
    ('new_definition', False, ''),
  ('stackProps', 'fp_name'):
    ('new_recursive_definition', False, ''),
  ('stackProps', 'inst_name'):
    ('new_definition', False, ''),
  ('stackProps', 'no_shmemop'):
    ('measure', False, 'MEASURE (\\x0. stackLang_prog_size (\\x. 0) x0)'),
  ('stackProps', 'reg_bound'):
    ('measure', False, 'MEASURE (\\(x0,x1). stackLang_prog_size (\\x. 0) x0)'),
  ('stackProps', 'reg_bound_exp'):
    ('measure', False, 'MEASURE (\\(x0,x1). wordLang_exp_size (\\x. 0) x0)'),
  ('stackProps', 'reg_bound_inst'):
    ('new_definition', False, ''),
  ('stackProps', 'reg_imm_name'):
    ('new_recursive_definition', False, ''),
  ('stackProps', 'reg_name'):
    ('new_definition', False, ''),
  ('stackProps', 'stackProps_extract_labels'):
    ('measure', False, 'MEASURE (\\x0. stackLang_prog_size (\\x. 0) x0)'),
  ('stackProps', 'stackProps_get_code_labels'):
    ('measure', False, 'MEASURE (\\x0. stackLang_prog_size (\\x. 0) x0)'),
  ('stackProps', 'stackProps_no_install'):
    ('measure', False, 'MEASURE (\\x0. stackLang_prog_size (\\x. 0) x0)'),
  ('stackProps', 'stack_asm_name'):
    ('measure', False, 'MEASURE (\\(x0,x1). stackLang_prog_size (\\x. 0) x1)'),
  ('stackProps', 'stack_asm_ok'):
    ('measure', False, 'MEASURE (\\(x0,x1). stackLang_prog_size (\\x. 0) x1)'),
  ('stackProps', 'stack_asm_remove'):
    ('measure', False, 'MEASURE (\\(x0,x1). stackLang_prog_size (\\x. 0) x1)'),
  ('stackProps', 'stack_get_handler_labels'):
    ('measure', False, 'MEASURE (\\(x0,x1). stackLang_prog_size (\\x. 0) x1)'),
  ('stackProps', 'stack_good_code_labels'):
    ('new_definition', False, ''),
  ('stackProps', 'stack_good_handler_labels'):
    ('new_definition', False, ''),
  ('stackSem', 'bit_length'):
    ('measure', True, ''),
  ('stackSem', 'check_store_consts_opt'):
    ('new_recursive_definition', False, ''),
  ('stackSem', 'copy_words'):
    ('measure', True, ''),
  ('stackSem', 'copy_words_for_pattern'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4,x5,x6). list_size (\\x. 0) x4)'),
  ('stackSem', 'filter_bitmap'):
    ('guess', False, ''),
  ('stackSem', 'full_read_bitmap'):
    ('new_definition', False, ''),
  ('stackSem', 'loc_check'):
    ('new_definition', False, ''),
  ('stackSem', 'map_bitmap'):
    ('guess', False, ''),
  ('stackSem', 'read_bitmap'):
    ('prim_rec', False, ''),
  ('stackSem', 'read_stack'):
    ('new_definition', False, ''),
  ('stackSem', 'read_stack_space'):
    ('new_definition', False, ''),
  ('stackSem', 'sh_mem_op'):
    ('new_recursive_definition', False, ''),
  ('stackSem', 'stackSem_STOP'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_alloc'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_assign'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_bad_fun_return'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_cont_loop'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_dec_clock'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_dec_stack'):
    ('measure', True, ''),
  ('stackSem', 'stackSem_dest_Seq'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_empty_env'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_enc_stack'):
    ('measure', True, ''),
  ('stackSem', 'stackSem_evaluate'):
    ('measure', False, ''),
  ('stackSem', 'stackSem_exit_loop'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_find_code'):
    ('new_recursive_definition', False, ''),
  ('stackSem', 'stackSem_fix_clock'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_gc'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_get_fp_var'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_get_labels'):
    ('measure', False, 'MEASURE (\\x0. stackLang_prog_size (\\x. 0) x0)'),
  ('stackSem', 'stackSem_get_var'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_get_var_imm'):
    ('new_recursive_definition', False, ''),
  ('stackSem', 'stackSem_get_vars'):
    ('prim_rec', False, ''),
  ('stackSem', 'stackSem_has_space'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_inst'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_mem_load'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_mem_store'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_semantics'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_set_fp_var'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_set_store'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_set_var'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_sh_mem_load'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_sh_mem_load16'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_sh_mem_load32'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_sh_mem_load_byte'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_sh_mem_store'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_sh_mem_store16'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_sh_mem_store32'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_sh_mem_store_byte'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_unset_var'):
    ('new_definition', False, ''),
  ('stackSem', 'stackSem_word_exp'):
    ('nested', False, ''),
  ('stackSem', 'store_const_sem'):
    ('new_definition', False, ''),
  ('stack_alloc', 'SetNewTrigger'):
    ('new_definition', False, ''),
  ('stack_alloc', 'clear_top_inst'):
    ('new_definition', False, ''),
  ('stack_alloc', 'memcpy_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'next_lab'):
    ('measure', False, 'MEASURE (\\(x0,x1). stackLang_prog_size (\\x. 0) x0)'),
  ('stack_alloc', 'stack_alloc_comp'):
    ('measure', True, ''),
  ('stack_alloc', 'stack_alloc_compile'):
    ('new_definition', False, ''),
  ('stack_alloc', 'stack_alloc_prog_comp'):
    ('new_definition', False, ''),
  ('stack_alloc', 'stack_alloc_stub_names'):
    ('new_definition', False, ''),
  ('stack_alloc', 'stack_alloc_stubs'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gc_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gc_move_bitmap_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gc_move_bitmaps_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gc_move_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gc_move_list_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gc_move_loop_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gc_move_roots_bitmaps_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gc_partial_or_full'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gen_gc_move_bitmap_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gen_gc_move_bitmaps_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gen_gc_move_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gen_gc_move_data_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gen_gc_move_list_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gen_gc_move_loop_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gen_gc_move_refs_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gen_gc_move_roots_bitmaps_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gen_gc_partial_move_bitmap_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gen_gc_partial_move_bitmaps_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gen_gc_partial_move_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gen_gc_partial_move_data_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gen_gc_partial_move_list_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gen_gc_partial_move_ref_list_code'):
    ('new_definition', False, ''),
  ('stack_alloc', 'word_gen_gc_partial_move_roots_bitmaps_code'):
    ('new_definition', False, ''),
  ('stack_allocProof', 'get_bits'):
    ('new_definition', False, ''),
  ('stack_allocProof', 'stack_allocProof_make_init'):
    ('new_definition', False, ''),
  ('stack_allocProof', 'word_gc_move_bitmap'):
    ('new_definition', False, ''),
  ('stack_allocProof', 'word_gc_move_bitmaps'):
    ('new_definition', False, ''),
  ('stack_allocProof', 'word_gc_move_roots_bitmaps'):
    ('new_definition', False, ''),
  ('stack_allocProof', 'word_gen_gc_move_bitmap'):
    ('new_definition', False, ''),
  ('stack_allocProof', 'word_gen_gc_move_bitmaps'):
    ('new_definition', False, ''),
  ('stack_allocProof', 'word_gen_gc_move_roots_bitmaps'):
    ('new_definition', False, ''),
  ('stack_allocProof', 'word_gen_gc_partial_move_bitmap'):
    ('new_definition', False, ''),
  ('stack_allocProof', 'word_gen_gc_partial_move_bitmaps'):
    ('new_definition', False, ''),
  ('stack_allocProof', 'word_gen_gc_partial_move_roots_bitmaps'):
    ('new_definition', False, ''),
  ('stack_names', 'dest_find_name'):
    ('new_definition', False, ''),
  ('stack_names', 'inst_find_name'):
    ('new_definition', False, ''),
  ('stack_names', 'ri_find_name'):
    ('new_recursive_definition', False, ''),
  ('stack_names', 'stack_names_comp'):
    ('measure', False, 'MEASURE (\\(x0,x1). stackLang_prog_size (\\x. 0) x1)'),
  ('stack_names', 'stack_names_compile'):
    ('new_definition', False, ''),
  ('stack_names', 'stack_names_names_ok'):
    ('new_definition', False, ''),
  ('stack_names', 'stack_names_prog_comp'):
    ('new_definition', False, ''),
  ('stack_namesProof', 'rename_state'):
    ('new_definition', False, ''),
  ('stack_namesProof', 'stack_namesProof_make_init'):
    ('new_definition', False, ''),
  ('stack_rawcall', 'collect_info'):
    ('prim_rec', False, ''),
  ('stack_rawcall', 'comp_seq'):
    ('new_definition', False, ''),
  ('stack_rawcall', 'comp_top'):
    ('new_definition', False, ''),
  ('stack_rawcall', 'dest_case'):
    ('new_definition', False, ''),
  ('stack_rawcall', 'seq_stack_alloc'):
    ('new_definition', False, ''),
  ('stack_rawcall', 'stack_rawcall_comp'):
    ('measure', False, 'MEASURE (\\(x0,x1). stackLang_prog_size (\\x. 0) x1)'),
  ('stack_rawcall', 'stack_rawcall_compile'):
    ('new_definition', False, ''),
  ('stack_rawcallProof', 'stack_rawcallProof_state_ok'):
    ('new_definition', False, ''),
  ('stack_rawcallProof', 'stack_rawcallProof_state_rel'):
    ('new_definition', False, ''),
  ('stack_remove', 'copy_each'):
    ('new_definition', False, ''),
  ('stack_remove', 'copy_loop'):
    ('new_definition', False, ''),
  ('stack_remove', 'downshift'):
    ('measure', False, 'MEASURE SND'),
  ('stack_remove', 'halt_inst'):
    ('new_definition', False, ''),
  ('stack_remove', 'init_memory'):
    ('new_definition', False, ''),
  ('stack_remove', 'init_stubs'):
    ('new_definition', False, ''),
  ('stack_remove', 'max_stack_alloc'):
    ('new_definition', False, ''),
  ('stack_remove', 'single_stack_alloc'):
    ('new_definition', False, ''),
  ('stack_remove', 'single_stack_free'):
    ('new_definition', False, ''),
  ('stack_remove', 'stack_alloc'):
    ('measure', False, 'MEASURE (SND o SND)'),
  ('stack_remove', 'stack_err_lab'):
    ('new_definition', False, ''),
  ('stack_remove', 'stack_load'):
    ('new_definition', False, ''),
  ('stack_remove', 'stack_remove_comp'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). stackLang_prog_size (\\x. 0) x3)'),
  ('stack_remove', 'stack_remove_compile'):
    ('new_definition', False, ''),
  ('stack_remove', 'stack_remove_init_code'):
    ('new_definition', False, ''),
  ('stack_remove', 'stack_remove_prog_comp'):
    ('new_definition', False, ''),
  ('stack_remove', 'stack_remove_stack_free'):
    ('measure', False, 'MEASURE SND'),
  ('stack_remove', 'stack_remove_store_list'):
    ('new_definition', False, ''),
  ('stack_remove', 'stack_remove_stub_names'):
    ('new_definition', False, ''),
  ('stack_remove', 'stack_store'):
    ('new_definition', False, ''),
  ('stack_remove', 'store_init'):
    ('new_definition', False, ''),
  ('stack_remove', 'store_length'):
    ('new_definition', False, ''),
  ('stack_remove', 'store_list_code'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). list_size (sum_size (\\n. n) (\\x. 0)) x2)'),
  ('stack_remove', 'store_offset'):
    ('new_definition', False, ''),
  ('stack_remove', 'store_pos'):
    ('new_definition', False, ''),
  ('stack_remove', 'upshift'):
    ('measure', False, 'MEASURE SND'),
  ('stack_remove', 'word_offset'):
    ('new_definition', False, ''),
  ('stack_removeProof', 'addresses'):
    ('measure', False, 'MEASURE (\\(x0,x1). (\\n. n) x1)'),
  ('stack_removeProof', 'discharge_these'):
    ('new_definition', False, ''),
  ('stack_removeProof', 'get_stack_heap_limit'):
    ('new_definition', False, ''),
  ('stack_removeProof', "get_stack_heap_limit'"):
    ('new_definition', False, ''),
  ('stack_removeProof', "get_stack_heap_limit''"):
    ('new_definition', False, ''),
  ('stack_removeProof', 'init_code_pre'):
    ('new_definition', False, ''),
  ('stack_removeProof', 'init_pre'):
    ('new_definition', False, ''),
  ('stack_removeProof', 'init_prop'):
    ('new_definition', False, ''),
  ('stack_removeProof', 'init_reduce'):
    ('new_definition', False, ''),
  ('stack_removeProof', 'is_SOME_Word'):
    ('new_definition', False, ''),
  ('stack_removeProof', 'make_init_any'):
    ('new_definition', False, ''),
  ('stack_removeProof', 'make_init_opt'):
    ('new_definition', False, ''),
  ('stack_removeProof', 'mem_val'):
    ('new_recursive_definition', False, ''),
  ('stack_removeProof', 'memory'):
    ('new_definition', False, ''),
  ('stack_removeProof', 'propagate_these'):
    ('new_definition', False, ''),
  ('stack_removeProof', 'read_pointers'):
    ('new_definition', False, ''),
  ('stack_removeProof', 'stack_heap_limit_ok'):
    ('new_definition', False, ''),
  ('stack_removeProof', 'stack_removeProof_code_rel'):
    ('new_definition', False, ''),
  ('stack_removeProof', 'stack_removeProof_read_mem'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x2)'),
  ('stack_removeProof', 'stack_removeProof_state_rel'):
    ('new_definition', False, ''),
  ('stack_removeProof', 'the_SOME_Word'):
    ('define_single', False, ''),
  ('stack_removeProof', 'word_list_rev'):
    ('guess', False, ''),
  ('stack_removeProof', 'word_store'):
    ('new_definition', False, ''),
  ('stack_to_lab', 'compile_jump'):
    ('new_recursive_definition', False, ''),
  ('stack_to_lab', 'compile_no_stubs'):
    ('new_definition', False, ''),
  ('stack_to_lab', 'find_lab'):
    ('new_definition', False, ''),
  ('stack_to_lab', 'is_Seq'):
    ('new_definition', False, ''),
  ('stack_to_lab', 'is_gen_gc'):
    ('new_definition', False, ''),
  ('stack_to_lab', 'negate'):
    ('new_recursive_definition', False, ''),
  ('stack_to_lab', 'prog_to_section'):
    ('new_definition', False, ''),
  ('stack_to_lab', 'stack_to_lab_compile'):
    ('new_definition', False, ''),
  ('stack_to_lab', 'stack_to_lab_flatten'):
    ('measure', True, ''),
  ('stack_to_labProof', "code_installed'"):
    ('prim_rec', False, ''),
  ('stack_to_labProof', 'complex_get_code_labels'):
    ('measure', False, 'MEASURE (\\x0. stackLang_prog_size (\\x. 0) x0)'),
  ('stack_to_labProof', 'contain'):
    ('new_definition', False, ''),
  ('stack_to_labProof', 'dest_to_loc'):
    ('new_definition', False, ''),
  ('stack_to_labProof', "dest_to_loc'"):
    ('new_definition', False, ''),
  ('stack_to_labProof', 'full_make_init'):
    ('new_definition', False, ''),
  ('stack_to_labProof', 'halt_assum'):
    ('new_definition', False, ''),
  ('stack_to_labProof', 'halt_view'):
    ('new_definition', False, ''),
  ('stack_to_labProof', 'halt_word_view'):
    ('new_definition', False, ''),
  ('stack_to_labProof', 'labels_ok'):
    ('new_definition', False, ''),
  ('stack_to_labProof', 'labs_correct'):
    ('prim_rec', False, ''),
  ('stack_to_labProof', 'memory_assumption'):
    ('new_definition', False, ''),
  ('stack_to_labProof', 'result_view'):
    ('new_definition', False, ''),
  ('stack_to_labProof', 'stack_to_labProof_code_installed'):
    ('prim_rec', False, ''),
  ('stack_to_labProof', 'stack_to_labProof_good_code'):
    ('new_definition', False, ''),
  ('stack_to_labProof', 'stack_to_labProof_make_init'):
    ('new_definition', False, ''),
  ('stack_to_labProof', 'stack_to_labProof_state_rel'):
    ('new_definition', False, ''),
  ('subst', 'rangevars'):
    ('new_definition', False, ''),
  ('subst', 'subst_APPLY'):
    ('prim_rec', False, ''),
  ('subst', 'substvars'):
    ('new_definition', False, ''),
  ('subst', 'vR'):
    ('new_definition', False, ''),
  ('subst', 'wfs'):
    ('new_definition', False, ''),
  ('tailrec', 'SHORT_TAILREC'):
    ('new_definition', False, ''),
  ('tailrec', 'SHORT_TAILREC_PRE'):
    ('new_definition', False, ''),
  ('tailrec', 'TAILREC_PRE'):
    ('new_definition', False, ''),
  ('tailrec', 'tailrec_TAILREC'):
    ('new_definition', False, ''),
  ('targetProps', 'app_post'):
    ('new_recursive_definition', False, ''),
  ('targetProps', 'ffi_entry_pcs_disjoint'):
    ('new_definition', False, ''),
  ('targetProps', 'find_next_interference'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). (\\n. n) x2)'),
  ('targetProps', 'interference_app_seq'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). (\\n. n) x3)'),
  ('targetProps', 'interference_count'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4). (\\n. n) x4)'),
  ('targetProps', 'interference_pos'):
    ('new_definition', False, ''),
  ('targetProps', 'is_ffi_app'):
    ('new_recursive_definition', False, ''),
  ('targetProps', 'next_interference'):
    ('new_definition', False, ''),
  ('targetProps', 'shift_interfer'):
    ('new_definition', False, ''),
  ('targetProps', 'target_cc_fp_regs'):
    ('new_definition', False, ''),
  ('targetProps', 'target_cc_regs'):
    ('new_definition', False, ''),
  ('targetProps', 'target_io_fp_regs'):
    ('new_definition', False, ''),
  ('targetProps', 'target_io_regs'):
    ('new_definition', False, ''),
  ('targetSem', 'apply_oracle'):
    ('new_definition', False, ''),
  ('targetSem', 'ccache_interfer_ok'):
    ('new_definition', False, ''),
  ('targetSem', 'code_loaded'):
    ('new_definition', False, ''),
  ('targetSem', 'encoded_bytes_in_mem'):
    ('new_definition', False, ''),
  ('targetSem', 'ffi_interfer_ok'):
    ('new_definition', False, ''),
  ('targetSem', 'get_reg_value'):
    ('new_recursive_definition', False, ''),
  ('targetSem', 'good_init_state'):
    ('new_definition', False, ''),
  ('targetSem', 'installed'):
    ('new_definition', False, ''),
  ('targetSem', 'is_valid_mapped_read'):
    ('new_definition', False, ''),
  ('targetSem', 'is_valid_mapped_write'):
    ('new_definition', False, ''),
  ('targetSem', 'machine_sem'):
    ('new_recursive_definition', False, ''),
  ('targetSem', 'mmio_pcs_min_index'):
    ('new_definition', False, ''),
  ('targetSem', 'post_ccache_asm'):
    ('new_definition', False, ''),
  ('targetSem', 'post_ffi_asm'):
    ('new_definition', False, ''),
  ('targetSem', 'read_ffi_bytearray'):
    ('new_definition', False, ''),
  ('targetSem', 'read_ffi_bytearrays'):
    ('new_definition', False, ''),
  ('targetSem', 'start_pc_ok'):
    ('new_definition', False, ''),
  ('targetSem', 'targetSem_evaluate'):
    ('measure', False, ''),
  ('targetSem', 'target_configured'):
    ('new_definition', False, ''),
  ('term', 'pair_count'):
    ('prim_rec', False, ''),
  ('term', 'varb'):
    ('measure', False, 'MEASURE (\\x0. term_size (\\x. 0) x0)'),
  ('term', 'vars'):
    ('measure', False, 'MEASURE (\\x0. term_size (\\x. 0) x0)'),
  ('ternaryComparisons', 'invert_comparison'):
    ('new_recursive_definition', False, ''),
  ('ternaryComparisons', 'list_compare'):
    ('guess', False, ''),
  ('ternaryComparisons', 'num_compare'):
    ('new_definition', False, ''),
  ('ternaryComparisons', 'pair_compare'):
    ('new_definition', False, ''),
  ('tokenUtils', 'destAlphaT'):
    ('new_definition', False, ''),
  ('tokenUtils', 'destCharT'):
    ('new_definition', False, ''),
  ('tokenUtils', 'destFFIT'):
    ('new_definition', False, ''),
  ('tokenUtils', 'destIntT'):
    ('new_definition', False, ''),
  ('tokenUtils', 'destLf'):
    ('new_definition', False, ''),
  ('tokenUtils', 'destLongidT'):
    ('new_definition', False, ''),
  ('tokenUtils', 'destREPLIDT'):
    ('new_definition', False, ''),
  ('tokenUtils', 'destStringT'):
    ('new_definition', False, ''),
  ('tokenUtils', 'destSymbolT'):
    ('new_definition', False, ''),
  ('tokenUtils', 'destTyvarPT'):
    ('new_definition', False, ''),
  ('tokenUtils', 'destWordT'):
    ('new_definition', False, ''),
  ('tokenUtils', 'isAlphaSym'):
    ('new_definition', False, ''),
  ('tokenUtils', 'isAlphaT'):
    ('new_definition', False, ''),
  ('tokenUtils', 'isCharT'):
    ('new_definition', False, ''),
  ('tokenUtils', 'isInt'):
    ('new_definition', False, ''),
  ('tokenUtils', 'isLongidT'):
    ('new_definition', False, ''),
  ('tokenUtils', 'isString'):
    ('new_definition', False, ''),
  ('tokenUtils', 'isSymbolT'):
    ('new_definition', False, ''),
  ('tokenUtils', 'isTyvarT'):
    ('new_definition', False, ''),
  ('tokenUtils', 'isWhitespaceT'):
    ('new_definition', False, ''),
  ('tokenUtils', 'isWordT'):
    ('new_definition', False, ''),
  ('tokenUtils', 'tokenUtils_destTOK'):
    ('new_definition', False, ''),
  ('toto', 'TotOrd'):
    ('new_definition', False, ''),
  ('typeSound', 'store_type_extension'):
    ('new_definition', False, ''),
  ('typeSoundInvariants', 'add_tenvE'):
    ('prim_rec', False, ''),
  ('typeSoundInvariants', 'consistent_ctMap'):
    ('new_definition', False, ''),
  ('typeSoundInvariants', 'ctMap_has_bools'):
    ('new_definition', False, ''),
  ('typeSoundInvariants', 'ctMap_has_exns'):
    ('new_definition', False, ''),
  ('typeSoundInvariants', 'ctMap_has_lists'):
    ('new_definition', False, ''),
  ('typeSoundInvariants', 'ctMap_ok'):
    ('new_definition', False, ''),
  ('typeSoundInvariants', 'good_ctMap'):
    ('new_definition', False, ''),
  ('typeSoundInvariants', 'tenv_abbrev_ok'):
    ('new_definition', False, ''),
  ('typeSoundInvariants', 'tenv_ctor_ok'):
    ('new_definition', False, ''),
  ('typeSoundInvariants', 'tenv_ok'):
    ('new_definition', False, ''),
  ('typeSoundInvariants', 'tenv_val_exp_ok'):
    ('prim_rec', False, ''),
  ('typeSoundInvariants', 'tenv_val_ok'):
    ('new_definition', False, ''),
  ('typeSoundInvariants', 'type_all_env'):
    ('new_definition', False, ''),
  ('typeSoundInvariants', 'type_ctor'):
    ('new_definition', False, ''),
  ('typeSoundInvariants', 'type_s'):
    ('new_definition', False, ''),
  ('typeSoundInvariants', 'type_sound_invariant'):
    ('new_definition', False, ''),
  ('typeSoundInvariants', 'type_sv'):
    ('new_definition', False, ''),
  ('typeSysProps', 'db_merge'):
    ('prim_rec', False, ''),
  ('typeSysProps', 'deBruijn_subst_tenvE'):
    ('prim_rec', False, ''),
  ('typeSysProps', 'type_def_to_ctMap'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3).      list_size      (pair_size (\\x. 0)      (pair_size (\\x. 0) (list_size (pair_size mlstring_size ast_t_size1))))      x2)'),
  ('typeSysProps', 'type_pes'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tarray'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tarray_num'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tbool'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tbool_num'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tchar'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tchar_num'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tdouble'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tdouble_num'):
    ('new_definition', False, ''),
  ('typeSystem', 'Texn'):
    ('new_definition', False, ''),
  ('typeSystem', 'Texn_num'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tfn'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tfn_num'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tint'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tint_num'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tlist'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tlist_num'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tref'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tref_num'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tstring'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tstring_num'):
    ('new_definition', False, ''),
  ('typeSystem', 'Ttup'):
    ('new_definition', False, ''),
  ('typeSystem', 'Ttup_num'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tvector'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tvector_num'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tword64'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tword64_num'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tword8'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tword8_num'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tword8array'):
    ('new_definition', False, ''),
  ('typeSystem', 'Tword8array_num'):
    ('new_definition', False, ''),
  ('typeSystem', 'bind_tvar'):
    ('new_definition', False, ''),
  ('typeSystem', 'bind_var_list'):
    ('prim_rec', False, ''),
  ('typeSystem', 'build_ctor_tenv'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2).      list_size      (pair_size (\\x. 0)      (pair_size (\\x. 0) (list_size (pair_size (\\x. 0) ast_t_size1))))      x1)'),
  ('typeSystem', 'check_ctor_tenv'):
    ('prim_rec', False, ''),
  ('typeSystem', 'check_freevars'):
    ('nested', False, ''),
  ('typeSystem', 'check_freevars_ast'):
    ('nested', False, ''),
  ('typeSystem', 'check_type_names'):
    ('nested', False, ''),
  ('typeSystem', 'deBruijn_inc'):
    ('nested', False, ''),
  ('typeSystem', 'deBruijn_subst'):
    ('nested', False, ''),
  ('typeSystem', 'extend_dec_tenv'):
    ('new_definition', False, ''),
  ('typeSystem', 'is_value'):
    ('measure', False, 'MEASURE (\\x0. ast_exp_size x0)'),
  ('typeSystem', 'lookup_var'):
    ('new_definition', False, ''),
  ('typeSystem', 'lookup_varE'):
    ('new_definition', False, ''),
  ('typeSystem', 'num_tvs'):
    ('prim_rec', False, ''),
  ('typeSystem', 'opt_bind_name'):
    ('new_definition', False, ''),
  ('typeSystem', 'prim_type_nums'):
    ('new_definition', False, ''),
  ('typeSystem', 'supported_arith'):
    ('new_definition', False, ''),
  ('typeSystem', 'supported_conversion'):
    ('new_definition', False, ''),
  ('typeSystem', 'supported_test'):
    ('new_definition', False, ''),
  ('typeSystem', 't_of'):
    ('new_definition', False, ''),
  ('typeSystem', 'tenvLift'):
    ('new_definition', False, ''),
  ('typeSystem', 'tenv_add_tvs'):
    ('new_definition', False, ''),
  ('typeSystem', 'tscheme_inst'):
    ('new_definition', False, ''),
  ('typeSystem', 'tscheme_inst2'):
    ('new_definition', False, ''),
  ('typeSystem', 'tveLookup'):
    ('prim_rec', False, ''),
  ('typeSystem', 'type_name_subst'):
    ('nested', False, ''),
  ('typeSystem', 'type_op'):
    ('new_definition', False, ''),
  ('typeSystem', 'type_pe_determ'):
    ('new_definition', False, ''),
  ('typeSystem', 'type_subst'):
    ('nested', False, ''),
  ('typeSystem', 'weak_tenv'):
    ('new_definition', False, ''),
  ('type_dCanon', 'LINVI'):
    ('new_definition', False, ''),
  ('type_dCanon', 'extend_bij'):
    ('new_definition', False, ''),
  ('type_dCanon', 'good_remap'):
    ('new_definition', False, ''),
  ('type_dCanon', 'remap_tenvE'):
    ('prim_rec', False, ''),
  ('type_dCanon', 'set_tids_tenv'):
    ('new_definition', False, ''),
  ('type_dCanon', 'sing_renum'):
    ('new_definition', False, ''),
  ('type_dCanon', 'tenv_equiv'):
    ('new_definition', False, ''),
  ('type_dCanon', 'type_pe_determ_canon'):
    ('new_definition', False, ''),
  ('unifDef', 'ext_s_check'):
    ('new_definition', False, ''),
  ('unify', 'PFLAT'):
    ('measure', False, 'MEASURE (\\x0. list_size (pair_size infer_t_size1 infer_t_size1) x0)'),
  ('unify', 'RKC'):
    ('new_definition', False, ''),
  ('unify', 'apply_cunifk'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (pair_size infer_t_size1 infer_t_size1) x0)'),
  ('unify', 'apply_kclkont'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). list_size kclkont_size x1)'),
  ('unify', 'apply_kcockont'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). list_size infer_t_size1 x2)'),
  ('unify', 'apply_subst_t'):
    ('new_definition', False, ''),
  ('unify', 'capply_subst'):
    ('nested', False, ''),
  ('unify', 'coc'):
    ('new_definition', False, ''),
  ('unify', 'cocl'):
    ('prim_rec', False, ''),
  ('unify', 'cplist_vars'):
    ('measure', False, 'MEASURE (\\x0. list_size (pair_size infer_t_size1 infer_t_size1) x0)'),
  ('unify', 'cunify'):
    ('new_definition', False, ''),
  ('unify', 'cunifyl'):
    ('new_definition', False, ''),
  ('unify', 'cvwalk'):
    ('new_definition', False, ''),
  ('unify', 'cvwalkR'):
    ('new_definition', False, ''),
  ('unify', 'cwalk'):
    ('new_definition', False, ''),
  ('unify', 'cwalkstar'):
    ('new_definition', False, ''),
  ('unify', 'cwalkstarl'):
    ('prim_rec', False, ''),
  ('unify', 'cwfs'):
    ('new_definition', False, ''),
  ('unify', 'decode_infer_t'):
    ('measure', True, ''),
  ('unify', 'dfkcoc'):
    ('new_definition', False, ''),
  ('unify', 'dfkcocl'):
    ('new_definition', False, ''),
  ('unify', 'dfkcunifyl'):
    ('new_definition', False, ''),
  ('unify', 'dfkcwalkstarl'):
    ('new_definition', False, ''),
  ('unify', 'encode_infer_t'):
    ('prim_rec', False, ''),
  ('unify', 'isCONSk'):
    ('new_definition', False, ''),
  ('unify', 'isvars'):
    ('measure', False, 'MEASURE (\\x0. infer_t_size1 x0)'),
  ('unify', 'kcoc'):
    ('new_definition', False, ''),
  ('unify', 'kcocl'):
    ('new_definition', False, ''),
  ('unify', 'kcocwl'):
    ('new_definition', False, ''),
  ('unify', 'kcocwlR'):
    ('new_definition', False, ''),
  ('unify', 'kcunifyl'):
    ('new_definition', False, ''),
  ('unify', 'kcunifywl'):
    ('new_definition', False, ''),
  ('unify', 'kcunifywlR'):
    ('new_definition', False, ''),
  ('unify', 'kcwalkstar'):
    ('new_definition', False, ''),
  ('unify', 'kcwalkstarl'):
    ('new_definition', False, ''),
  ('unify', 'kcwalkstarwl'):
    ('define_single', False, ''),
  ('unify', 'kcwalkstarwlR'):
    ('new_definition', False, ''),
  ('unify', 'star_kwork'):
    ('measure', False, 'MEASURE (\\x0. list_size kclkont_size x0)'),
  ('unify', 'star_workbag'):
    ('new_definition', False, ''),
  ('unify', 'substR'):
    ('new_definition', False, ''),
  ('unify', 'subterm'):
    ('new_definition', False, ''),
  ('unify', 't_collapse'):
    ('new_definition', False, ''),
  ('unify', 't_compat'):
    ('new_definition', False, ''),
  ('unify', 't_ext_s_check'):
    ('new_definition', False, ''),
  ('unify', 't_oc'):
    ('new_definition', False, ''),
  ('unify', 't_rangevars'):
    ('new_definition', False, ''),
  ('unify', 't_unify'):
    ('new_definition', False, ''),
  ('unify', 't_vR'):
    ('new_definition', False, ''),
  ('unify', 't_vars'):
    ('new_definition', False, ''),
  ('unify', 't_vwalk'):
    ('new_definition', False, ''),
  ('unify', 't_walk'):
    ('new_definition', False, ''),
  ('unify', 't_walkstar'):
    ('new_definition', False, ''),
  ('unify', 't_wfs'):
    ('new_definition', False, ''),
  ('unify', 'tcocwl'):
    ('new_definition', False, ''),
  ('unify', 'tcunify'):
    ('new_definition', False, ''),
  ('unify', 'tcvwalk'):
    ('new_definition', False, ''),
  ('unify', 'tcwalk'):
    ('new_definition', False, ''),
  ('unify', 'tcwalkstar_p1'):
    ('new_definition', False, ''),
  ('unify', 'tcwalkstar_p2'):
    ('new_definition', False, ''),
  ('unify', 'tcwalkstarwl'):
    ('new_definition', False, ''),
  ('unify', 'ts_unify'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). infer_t_size1 x1 + infer_t_size1 x2)'),
  ('walk', 'walk'):
    ('new_definition', False, ''),
  ('walkstar', 'walkstarR'):
    ('new_definition', False, ''),
  ('weakening', 'weak'):
    ('new_definition', False, ''),
  ('weakening', 'weakCT'):
    ('new_definition', False, ''),
  ('weakening', 'weakS'):
    ('new_definition', False, ''),
  ('weakening', 'weak_tenvE'):
    ('new_definition', False, ''),
  ('wordConvs', 'call_arg_convention'):
    ('measure', False, 'MEASURE (\\x0. wordLang_prog_size (\\x. 0) x0)'),
  ('wordConvs', 'distinct_tar_reg'):
    ('new_definition', False, ''),
  ('wordConvs', 'every_inst'):
    ('measure', False, 'MEASURE (\\(x0,x1). wordLang_prog_size (\\x. 0) x1)'),
  ('wordConvs', 'flat_exp_conventions'):
    ('measure', False, 'MEASURE (\\x0. wordLang_prog_size (\\x. 0) x0)'),
  ('wordConvs', 'full_inst_ok_less'):
    ('measure', False, 'MEASURE (\\(x0,x1). wordLang_prog_size (\\x. 0) x1)'),
  ('wordConvs', 'good_handlers'):
    ('measure', False, 'MEASURE (\\(x0,x1). wordLang_prog_size (\\x. 0) x1)'),
  ('wordConvs', 'inst_arg_convention'):
    ('new_definition', False, ''),
  ('wordConvs', 'inst_ok_less'):
    ('new_definition', False, ''),
  ('wordConvs', 'labels_rel'):
    ('new_definition', False, ''),
  ('wordConvs', 'no_alloc'):
    ('new_definition', False, ''),
  ('wordConvs', 'no_mt'):
    ('new_definition', False, ''),
  ('wordConvs', 'no_share_inst'):
    ('new_definition', False, ''),
  ('wordConvs', 'not_created_subprogs'):
    ('measure', False, 'MEASURE (\\(x0,x1). wordLang_prog_size (\\x. 0) x1)'),
  ('wordConvs', 'post_alloc_conventions'):
    ('new_definition', False, ''),
  ('wordConvs', 'pre_alloc_conventions'):
    ('new_definition', False, ''),
  ('wordConvs', 'two_reg_inst'):
    ('new_definition', False, ''),
  ('wordConvs', 'wf_cutsets'):
    ('measure', False, 'MEASURE (\\x0. wordLang_prog_size (\\x. 0) x0)'),
  ('wordConvs', 'wf_names'):
    ('new_definition', False, ''),
  ('wordConvs', 'wordConvs_extract_labels'):
    ('measure', False, 'MEASURE (\\x0. wordLang_prog_size (\\x. 0) x0)'),
  ('wordConvs', 'wordConvs_get_code_labels'):
    ('measure', False, 'MEASURE (\\x0. wordLang_prog_size (\\x. 0) x0)'),
  ('wordConvs', 'wordConvs_good_code_labels'):
    ('new_definition', False, ''),
  ('wordConvs', 'wordConvs_no_install'):
    ('new_definition', False, ''),
  ('wordLang', 'cutsets_max'):
    ('new_definition', False, ''),
  ('wordLang', 'every_name'):
    ('new_definition', False, ''),
  ('wordLang', 'every_stack_var'):
    ('measure', False, 'MEASURE (\\(x0,x1). wordLang_prog_size (\\x. 0) x1)'),
  ('wordLang', 'every_var_exp'):
    ('measure', False, 'MEASURE (\\(x0,x1). wordLang_exp_size (\\x. 0) x1)'),
  ('wordLang', 'every_var_imm'):
    ('new_definition', False, ''),
  ('wordLang', 'every_var_inst'):
    ('new_definition', False, ''),
  ('wordLang', 'exp_to_addr'):
    ('new_definition', False, ''),
  ('wordLang', 'max_var'):
    ('measure', False, 'MEASURE (\\x0. wordLang_prog_size (\\x. 0) x0)'),
  ('wordLang', 'max_var_exp'):
    ('measure', False, 'MEASURE (\\x0. wordLang_exp_size (\\x. 0) x0)'),
  ('wordLang', 'max_var_inst'):
    ('new_definition', False, ''),
  ('wordLang', 'raise_stub_location'):
    ('new_definition', False, ''),
  ('wordLang', 'wordLang_every_var'):
    ('measure', False, 'MEASURE (\\(x0,x1). wordLang_prog_size (\\x. 0) x1)'),
  ('wordLang', 'wordLang_store_consts_stub_location'):
    ('new_definition', False, ''),
  ('wordLang', 'wordLang_word_op'):
    ('new_definition', False, ''),
  ('wordLang', 'word_sh'):
    ('new_definition', False, ''),
  ('wordProps', 'gc_fun_ok'):
    ('new_definition', False, ''),
  ('wordProps', 'locals_rel'):
    ('new_definition', False, ''),
  ('wordProps', 'no_alloc_code'):
    ('new_definition', False, ''),
  ('wordProps', 'no_install_code'):
    ('new_definition', False, ''),
  ('wordProps', 'no_mt_code'):
    ('new_definition', False, ''),
  ('wordProps', 's_frame_key_eq'):
    ('new_definition', False, ''),
  ('wordProps', 's_frame_val_eq'):
    ('new_definition', False, ''),
  ('wordProps', 's_key_eq'):
    ('measure', False, 'MEASURE (\\(x0,x1).      list_size (stack_frame_size (\\x. 0)) x0 +      list_size (stack_frame_size (\\x. 0)) x1)'),
  ('wordProps', 's_val_eq'):
    ('measure', False, 'MEASURE (\\(x0,x1).      list_size (stack_frame_size (\\x. 0)) x0 +      list_size (stack_frame_size (\\x. 0)) x1)'),
  ('wordProps', 'wordProps_inc_clock'):
    ('new_definition', False, ''),
  ('wordSem', 'MustTerminate_limit'):
    ('new_definition', False, ''),
  ('wordSem', 'add_ret_loc'):
    ('new_recursive_definition', False, ''),
  ('wordSem', 'bad_dest_args'):
    ('new_definition', False, ''),
  ('wordSem', 'buffer_flush'):
    ('new_definition', False, ''),
  ('wordSem', 'buffer_write'):
    ('new_definition', False, ''),
  ('wordSem', 'const_addresses'):
    ('prim_rec', False, ''),
  ('wordSem', 'const_writes'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). list_size (pair_size (\\x. 0) (\\x. 0)) x2)'),
  ('wordSem', 'cut_envs'):
    ('new_definition', False, ''),
  ('wordSem', 'cut_names'):
    ('new_definition', False, ''),
  ('wordSem', 'env_to_list'):
    ('new_definition', False, ''),
  ('wordSem', 'gc_bij_ok'):
    ('new_definition', False, ''),
  ('wordSem', 'get_word'):
    ('define_single', False, ''),
  ('wordSem', 'isWord'):
    ('new_definition', False, ''),
  ('wordSem', 'is_fwd_ptr'):
    ('new_definition', False, ''),
  ('wordSem', 'is_word'):
    ('new_definition', False, ''),
  ('wordSem', 'key_val_compare'):
    ('new_definition', False, ''),
  ('wordSem', 'list_rearrange'):
    ('new_definition', False, ''),
  ('wordSem', 'mem_load_32'):
    ('new_definition', False, ''),
  ('wordSem', 'mem_load_byte_aux'):
    ('new_definition', False, ''),
  ('wordSem', 'mem_store_32'):
    ('new_definition', False, ''),
  ('wordSem', 'mem_store_byte_aux'):
    ('new_definition', False, ''),
  ('wordSem', 'sh_mem_set_var'):
    ('new_definition', False, ''),
  ('wordSem', 'share_inst'):
    ('new_recursive_definition', False, ''),
  ('wordSem', 'stack_size'):
    ('new_definition', False, ''),
  ('wordSem', 'stack_size_frame'):
    ('new_definition', False, ''),
  ('wordSem', 'theWord'):
    ('define_single', False, ''),
  ('wordSem', 'the_words'):
    ('prim_rec', False, ''),
  ('wordSem', 'wordSem_STOP'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_alloc'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_assign'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_bad_fun_return'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_call_env'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_cont_loop'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_cut_env'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_cut_state'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_cut_state_opt'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_dec_clock'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_dec_stack'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (stack_frame_size (\\x. 0)) x1)'),
  ('wordSem', 'wordSem_enc_stack'):
    ('measure', False, 'MEASURE (\\x0. list_size (stack_frame_size (\\x. 0)) x0)'),
  ('wordSem', 'wordSem_evaluate'):
    ('measure', False, ''),
  ('wordSem', 'wordSem_exit_loop'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_find_code'):
    ('new_recursive_definition', False, ''),
  ('wordSem', 'wordSem_fix_clock'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_flush_state'):
    ('define_single', False, ''),
  ('wordSem', 'wordSem_gc'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_get_fp_var'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_get_store'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_get_var'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_get_var_imm'):
    ('new_recursive_definition', False, ''),
  ('wordSem', 'wordSem_get_vars'):
    ('prim_rec', False, ''),
  ('wordSem', 'wordSem_has_space'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_inst'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_isException'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_isResult'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_jump_exc'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_mem_load'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_mem_store'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_pop_env'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_push_env'):
    ('new_recursive_definition', False, ''),
  ('wordSem', 'wordSem_semantics'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_set_fp_var'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_set_store'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_set_var'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_set_vars'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_sh_mem_load'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_sh_mem_load16'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_sh_mem_load32'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_sh_mem_load_byte'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_sh_mem_store'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_sh_mem_store16'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_sh_mem_store32'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_sh_mem_store_byte'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_unset_var'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_word_cmp'):
    ('new_definition', False, ''),
  ('wordSem', 'wordSem_word_exp'):
    ('nested', False, ''),
  ('wordSem', 'word_lang_safe_for_space'):
    ('new_definition', False, ''),
  ('wordSem', 'write_bytearray'):
    ('guess', False, ''),
  ('word_alloc', 'add1_lhs_const'):
    ('new_definition', False, ''),
  ('word_alloc', 'add1_lhs_mem'):
    ('new_definition', False, ''),
  ('word_alloc', 'add1_lhs_reg'):
    ('new_definition', False, ''),
  ('word_alloc', 'add1_rhs_mem'):
    ('new_definition', False, ''),
  ('word_alloc', 'add1_rhs_reg'):
    ('new_definition', False, ''),
  ('word_alloc', 'add_call'):
    ('new_definition', False, ''),
  ('word_alloc', 'apply_colour'):
    ('measure', False, 'MEASURE (\\(x0,x1). wordLang_prog_size (\\x. 0) x1)'),
  ('word_alloc', 'apply_colour_exp'):
    ('measure', False, 'MEASURE (\\(x0,x1). wordLang_exp_size (\\x. 0) x1)'),
  ('word_alloc', 'apply_colour_imm'):
    ('new_definition', False, ''),
  ('word_alloc', 'apply_colour_inst'):
    ('new_definition', False, ''),
  ('word_alloc', 'apply_nummap_key'):
    ('new_definition', False, ''),
  ('word_alloc', 'apply_nummaps_key'):
    ('new_definition', False, ''),
  ('word_alloc', 'big_union'):
    ('new_definition', False, ''),
  ('word_alloc', 'canonize_moves'):
    ('new_definition', False, ''),
  ('word_alloc', 'canonize_moves_aux'):
    ('prim_rec', False, ''),
  ('word_alloc', 'check_colouring_ok_alt'):
    ('prim_rec', False, ''),
  ('word_alloc', 'even_list'):
    ('new_definition', False, ''),
  ('word_alloc', 'every_even_colour'):
    ('new_definition', False, ''),
  ('word_alloc', 'fake_move'):
    ('new_definition', False, ''),
  ('word_alloc', 'fake_moves'):
    ('prim_rec', False, ''),
  ('word_alloc', 'fix_inconsistencies'):
    ('new_definition', False, ''),
  ('word_alloc', 'force_rename'):
    ('prim_rec', False, ''),
  ('word_alloc', 'full_ssa_cc_trans'):
    ('new_definition', False, ''),
  ('word_alloc', 'get_clash_tree'):
    ('measure', False, ''),
  ('word_alloc', 'get_coalescecost'):
    ('new_definition', False, ''),
  ('word_alloc', 'get_delta_inst'):
    ('new_definition', False, ''),
  ('word_alloc', 'get_forced'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). asm_config_size (\\x. 0) x0 + wordLang_prog_size (\\x. 0) x1)'),
  ('word_alloc', 'get_heu'):
    ('measure', False, ''),
  ('word_alloc', 'get_heu_inst'):
    ('new_definition', False, ''),
  ('word_alloc', 'get_heuristics'):
    ('new_definition', False, ''),
  ('word_alloc', 'get_live'):
    ('match', False, ''),
  ('word_alloc', 'get_live_exp'):
    ('measure', False, 'MEASURE (\\x0. wordLang_exp_size (\\x. 0) x0)'),
  ('word_alloc', 'get_live_inst'):
    ('new_definition', False, ''),
  ('word_alloc', 'get_prefs'):
    ('measure', False, 'MEASURE (\\(x0,x1). wordLang_prog_size (\\x. 0) x0)'),
  ('word_alloc', 'get_reads_exp'):
    ('measure', False, 'MEASURE (\\x0. wordLang_exp_size (\\x. 0) x0)'),
  ('word_alloc', 'get_spillcost'):
    ('new_definition', False, ''),
  ('word_alloc', 'get_stack_only'):
    ('new_definition', False, ''),
  ('word_alloc', 'get_stack_only_aux'):
    ('measure', True, ''),
  ('word_alloc', 'get_writes'):
    ('new_definition', False, ''),
  ('word_alloc', 'get_writes_inst'):
    ('new_definition', False, ''),
  ('word_alloc', 'heu_max'):
    ('new_definition', False, ''),
  ('word_alloc', 'heu_max_all'):
    ('new_definition', False, ''),
  ('word_alloc', 'heu_merge_call'):
    ('new_definition', False, ''),
  ('word_alloc', 'limit_var'):
    ('new_definition', False, ''),
  ('word_alloc', 'list_next_var_rename'):
    ('prim_rec', False, ''),
  ('word_alloc', 'list_next_var_rename_move'):
    ('new_definition', False, ''),
  ('word_alloc', 'loop_setup'):
    ('new_definition', False, ''),
  ('word_alloc', 'merge_stack_only'):
    ('new_definition', False, ''),
  ('word_alloc', 'merge_stack_sets'):
    ('new_definition', False, ''),
  ('word_alloc', 'mk_prio'):
    ('new_definition', False, ''),
  ('word_alloc', 'next_var_rename'):
    ('new_definition', False, ''),
  ('word_alloc', 'option_lookup'):
    ('new_definition', False, ''),
  ('word_alloc', 'oracle_colour_ok'):
    ('new_definition', False, ''),
  ('word_alloc', 'priority'):
    ('new_definition', False, ''),
  ('word_alloc', 'remove_dead'):
    ('measure', False, ''),
  ('word_alloc', 'remove_dead_inst'):
    ('new_definition', False, ''),
  ('word_alloc', 'remove_dead_prog'):
    ('new_definition', False, ''),
  ('word_alloc', 'remove_temp_stack'):
    ('new_definition', False, ''),
  ('word_alloc', 'select_reg_alloc'):
    ('new_definition', False, ''),
  ('word_alloc', 'setup_ssa'):
    ('new_definition', False, ''),
  ('word_alloc', 'ssa_cc_trans'):
    ('measure', False, ''),
  ('word_alloc', 'ssa_cc_trans_exp'):
    ('measure', False, 'MEASURE (\\(x0,x1). wordLang_exp_size (\\x. 0) x1)'),
  ('word_alloc', 'ssa_cc_trans_inst'):
    ('new_definition', False, ''),
  ('word_alloc', 'ssa_reconcile'):
    ('new_definition', False, ''),
  ('word_alloc', 'total_colour'):
    ('new_definition', False, ''),
  ('word_alloc', 'word_alloc'):
    ('new_definition', False, ''),
  ('word_alloc', 'word_alloc_merge_moves'):
    ('prim_rec', False, ''),
  ('word_alloc', 'word_alloc_numset_list_insert'):
    ('prim_rec', False, ''),
  ('word_allocProof', 'colouring_ok'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3). wordLang_prog_size (\\x. 0) x1)'),
  ('word_allocProof', 'even_starting_locals'):
    ('new_definition', False, ''),
  ('word_allocProof', 'live_store_rel'):
    ('new_definition', False, ''),
  ('word_allocProof', 'lt_ok'):
    ('new_definition', False, ''),
  ('word_allocProof', 'nlive_store'):
    ('measure', False, 'MEASURE (\\(x0,x1). wordLang_exp_size (\\x. 0) x1)'),
  ('word_allocProof', 'ssa_locals_rel'):
    ('new_definition', False, ''),
  ('word_allocProof', 'ssa_map_ok'):
    ('new_definition', False, ''),
  ('word_allocProof', 'strong_locals_rel'):
    ('new_definition', False, ''),
  ('word_allocProof', 'word_allocProof_hide'):
    ('new_definition', False, ''),
  ('word_allocProof', 'word_state_eq_rel'):
    ('new_definition', False, ''),
  ('word_bignum', 'DivCode'):
    ('new_definition', False, ''),
  ('word_bignum', 'LoadRegs'):
    ('prim_rec', False, ''),
  ('word_bignum', 'SaveRegs'):
    ('prim_rec', False, ''),
  ('word_bignum', 'SeqIndex'):
    ('new_definition', False, ''),
  ('word_bignum', 'SeqTemp'):
    ('new_definition', False, ''),
  ('word_bignum', 'SeqTempImm'):
    ('new_recursive_definition', False, ''),
  ('word_bignum', 'SeqTempImmNot'):
    ('new_recursive_definition', False, ''),
  ('word_bignum', 'TempIn1'):
    ('new_definition', False, ''),
  ('word_bignum', 'TempIn2'):
    ('new_definition', False, ''),
  ('word_bignum', 'TempOut'):
    ('new_definition', False, ''),
  ('word_bignum', 'code_acc_next'):
    ('new_definition', False, ''),
  ('word_bignum', 'div_location'):
    ('new_definition', False, ''),
  ('word_bignum', 'generated_bignum_stubs'):
    ('new_definition', False, ''),
  ('word_bignum', 'has_compiled'):
    ('new_definition', False, ''),
  ('word_bignum', 'install'):
    ('new_definition', False, ''),
  ('word_bignum', 'word_bignum_compile'):
    ('match', False, ''),
  ('word_bignum', 'word_bignum_compile_exp'):
    ('measure', False, 'MEASURE (\\x0. wordLang_exp_size (\\x. 0) x0)'),
  ('word_bignumProof', 'Corr'):
    ('new_definition', False, ''),
  ('word_bignumProof', 'array_rel'):
    ('new_definition', False, ''),
  ('word_bignumProof', 'array_write'):
    ('new_definition', False, ''),
  ('word_bignumProof', 'clock_write'):
    ('new_definition', False, ''),
  ('word_bignumProof', 'code_subset'):
    ('new_definition', False, ''),
  ('word_bignumProof', 'delete_vars'):
    ('prim_rec', False, ''),
  ('word_bignumProof', 'div_code_assum'):
    ('new_definition', False, ''),
  ('word_bignumProof', 'eval_exp'):
    ('measure', False, 'MEASURE (\\(x0,x1). wordLang_exp_size (\\x. 0) x1)'),
  ('word_bignumProof', 'eval_exp_pre'):
    ('measure', False, 'MEASURE (\\(x0,x1). wordLang_exp_size (\\x. 0) x1)'),
  ('word_bignumProof', 'eval_ri_pre'):
    ('new_recursive_definition', False, ''),
  ('word_bignumProof', 'exp_ok'):
    ('measure', False, 'MEASURE (\\x0. wordLang_exp_size (\\x. 0) x0)'),
  ('word_bignumProof', 'list_store'):
    ('prim_rec', False, ''),
  ('word_bignumProof', 'list_update'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). list_size (\\n. n) x0)'),
  ('word_bignumProof', 'loop_app'):
    ('new_definition', False, ''),
  ('word_bignumProof', 'reg_write'):
    ('new_recursive_definition', False, ''),
  ('word_bignumProof', 'syntax_ok_aux'):
    ('match', False, ''),
  ('word_bignumProof', 'tick_before'):
    ('new_definition', False, ''),
  ('word_bignumProof', 'word_bignumProof_code_rel'):
    ('new_definition', False, ''),
  ('word_bignumProof', 'word_bignumProof_copy_vars'):
    ('prim_rec', False, ''),
  ('word_bignumProof', 'word_bignumProof_dec_clock'):
    ('new_definition', False, ''),
  ('word_bignumProof', 'word_bignumProof_good_code'):
    ('new_definition', False, ''),
  ('word_bignumProof', 'word_bignumProof_state_rel'):
    ('new_definition', False, ''),
  ('word_bignumProof', 'word_bignumProof_syntax_ok'):
    ('new_definition', False, ''),
  ('word_copy', 'copy_prop'):
    ('new_definition', False, ''),
  ('word_copy', 'copy_prop_inst'):
    ('new_definition', False, ''),
  ('word_copy', 'copy_prop_move'):
    ('prim_rec', False, ''),
  ('word_copy', 'copy_prop_prog'):
    ('match', False, ''),
  ('word_copy', 'copy_prop_share'):
    ('new_definition', False, ''),
  ('word_copy', 'empty_eq'):
    ('new_definition', False, ''),
  ('word_copy', 'lookup_eq'):
    ('new_definition', False, ''),
  ('word_copy', 'lookup_eq_imm'):
    ('new_definition', False, ''),
  ('word_copy', 'lookup_store_eq'):
    ('new_definition', False, ''),
  ('word_copy', 'merge_eqs'):
    ('new_definition', False, ''),
  ('word_copy', 'remove_eq'):
    ('new_definition', False, ''),
  ('word_copy', 'remove_eqs'):
    ('prim_rec', False, ''),
  ('word_copy', 'set_eq'):
    ('new_definition', False, ''),
  ('word_copy', 'set_store_eq'):
    ('new_definition', False, ''),
  ('word_copyProof', 'CPstate_inv'):
    ('new_definition', False, ''),
  ('word_copyProof', 'CPstate_models'):
    ('new_definition', False, ''),
  ('word_copyProof', 'both_alloc_vars'):
    ('new_definition', False, ''),
  ('word_cse', 'OpCurrHeapToNumList'):
    ('new_definition', False, ''),
  ('word_cse', 'add_to_data'):
    ('new_definition', False, ''),
  ('word_cse', 'add_to_data_aux'):
    ('new_definition', False, ''),
  ('word_cse', 'add_to_data_const'):
    ('new_definition', False, ''),
  ('word_cse', 'add_to_load_aux'):
    ('new_definition', False, ''),
  ('word_cse', 'arithOpToNum'):
    ('new_recursive_definition', False, ''),
  ('word_cse', 'arithReads'):
    ('new_definition', False, ''),
  ('word_cse', 'arithToNumList'):
    ('new_recursive_definition', False, ''),
  ('word_cse', 'arithWrites'):
    ('new_recursive_definition', False, ''),
  ('word_cse', 'bm_inter_eq'):
    ('new_definition', False, ''),
  ('word_cse', 'bm_inter_eq_acc'):
    ('prim_rec', False, ''),
  ('word_cse', 'can_mem_arith'):
    ('new_definition', False, ''),
  ('word_cse', 'canonicalArith'):
    ('new_recursive_definition', False, ''),
  ('word_cse', 'canonicalFp'):
    ('new_recursive_definition', False, ''),
  ('word_cse', 'canonicalImmReg'):
    ('new_recursive_definition', False, ''),
  ('word_cse', "canonicalImmReg'"):
    ('new_recursive_definition', False, ''),
  ('word_cse', 'canonicalMoveRegs'):
    ('new_definition', False, ''),
  ('word_cse', 'canonicalMultRegs'):
    ('new_definition', False, ''),
  ('word_cse', 'canonicalRegs'):
    ('new_definition', False, ''),
  ('word_cse', "canonicalRegs'"):
    ('new_definition', False, ''),
  ('word_cse', 'dest_Var'):
    ('new_definition', False, ''),
  ('word_cse', 'empty_data'):
    ('new_definition', False, ''),
  ('word_cse', 'firstRegOfArith'):
    ('new_recursive_definition', False, ''),
  ('word_cse', 'fpToNumList'):
    ('new_recursive_definition', False, ''),
  ('word_cse', 'fpWrites'):
    ('new_definition', False, ''),
  ('word_cse', 'instToNumList'):
    ('new_definition', False, ''),
  ('word_cse', 'invalidate_data'):
    ('new_definition', False, ''),
  ('word_cse', 'invalidate_regs'):
    ('prim_rec', False, ''),
  ('word_cse', 'is_store'):
    ('new_recursive_definition', False, ''),
  ('word_cse', 'keep_data'):
    ('new_definition', False, ''),
  ('word_cse', 'listCmp'):
    ('measure', False, 'MEASURE (\\(x0,x1). list_size (\\n. n) x0 + list_size (\\n. n) x1)'),
  ('word_cse', 'loadToNumList'):
    ('new_definition', False, ''),
  ('word_cse', 'map_insert'):
    ('prim_rec', False, ''),
  ('word_cse', 'memOpToNum'):
    ('new_recursive_definition', False, ''),
  ('word_cse', 'merge_data'):
    ('new_definition', False, ''),
  ('word_cse', 'regImmToNumList'):
    ('new_recursive_definition', False, ''),
  ('word_cse', 'register_read'):
    ('new_definition', False, ''),
  ('word_cse', 'register_reads'):
    ('prim_rec', False, ''),
  ('word_cse', 'shiftToNum'):
    ('new_recursive_definition', False, ''),
  ('word_cse', 'wordToNum'):
    ('new_definition', False, ''),
  ('word_cse', 'word_common_subexp_elim'):
    ('new_definition', False, ''),
  ('word_cse', 'word_cse'):
    ('prim_rec', False, ''),
  ('word_cse', 'word_cseInst'):
    ('new_definition', False, ''),
  ('word_cse', 'word_cse_Seqs'):
    ('measure', False, 'MEASURE (\\x0. list_size (wordLang_prog_size (\\x. 0)) x0)'),
  ('word_cseProof', 'data_inv'):
    ('new_definition', False, ''),
  ('word_cseProof', 'in_names_set'):
    ('new_definition', False, ''),
  ('word_cseProof', 'sem_inv'):
    ('new_definition', False, ''),
  ('word_cseProof', 'wf_data'):
    ('new_definition', False, ''),
  ('word_depth', 'call_graph'):
    ('measure', False, ''),
  ('word_depth', 'full_call_graph'):
    ('new_definition', False, ''),
  ('word_depth', 'max_depth'):
    ('prim_rec', False, ''),
  ('word_depth', 'max_depth_graphs'):
    ('prim_rec', False, ''),
  ('word_depth', 'mk_Branch'):
    ('new_definition', False, ''),
  ('word_elim', 'analyse_word_code'):
    ('prim_rec', False, ''),
  ('word_elim', 'find_word_loc'):
    ('new_definition', False, ''),
  ('word_elim', 'find_word_ref'):
    ('measure', False, 'MEASURE (\\x0. wordLang_prog_size (\\x. 0) x0)'),
  ('word_elim', 'remove_word_code'):
    ('new_definition', False, ''),
  ('word_elim', 'remove_word_prog'):
    ('new_definition', False, ''),
  ('word_elimProof', 'code_closed'):
    ('new_definition', False, ''),
  ('word_elimProof', 'dest_result_loc'):
    ('new_definition', False, ''),
  ('word_elimProof', 'dest_word_loc'):
    ('new_definition', False, ''),
  ('word_elimProof', 'find_loc_state'):
    ('new_definition', False, ''),
  ('word_elimProof', 'gc_no_new_locs'):
    ('new_definition', False, ''),
  ('word_elimProof', 'get_locals'):
    ('prim_rec', False, ''),
  ('word_elimProof', 'get_memory'):
    ('new_definition', False, ''),
  ('word_elimProof', 'get_num_wordloc_alist'):
    ('new_definition', False, ''),
  ('word_elimProof', 'word_elimProof_code_rel'):
    ('new_definition', False, ''),
  ('word_elimProof', 'word_elimProof_get_stack'):
    ('measure', False, 'MEASURE (\\x0. list_size (stack_frame_size (\\x. 0)) x0)'),
  ('word_elimProof', 'word_elimProof_get_store'):
    ('new_definition', False, ''),
  ('word_elimProof', 'word_state_rel'):
    ('new_definition', False, ''),
  ('word_gcFunctions', 'decode_length'):
    ('new_definition', False, ''),
  ('word_gcFunctions', 'glob_real'):
    ('new_definition', False, ''),
  ('word_gcFunctions', 'is_ref_header'):
    ('new_definition', False, ''),
  ('word_gcFunctions', 'memcpy'):
    ('measure', True, ''),
  ('word_gcFunctions', 'new_trig'):
    ('new_definition', False, ''),
  ('word_gcFunctions', 'ptr_to_addr'):
    ('new_definition', False, ''),
  ('word_gcFunctions', 'refs_to_addresses'):
    ('measure', False, 'MEASURE (\\x0. list_size (heap_element_size (\\x. 0) (\\x. 0)) x0)'),
  ('word_gcFunctions', 'update_addr'):
    ('new_definition', False, ''),
  ('word_gcFunctions', 'word_full_gc'):
    ('new_definition', False, ''),
  ('word_gcFunctions', 'word_gc_fun'):
    ('new_definition', False, ''),
  ('word_gcFunctions', 'word_gc_fun_assum'):
    ('new_definition', False, ''),
  ('word_gcFunctions', 'word_gc_move'):
    ('define_single', False, ''),
  ('word_gcFunctions', 'word_gc_move_list'):
    ('measure', True, ''),
  ('word_gcFunctions', 'word_gc_move_loop'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x0)'),
  ('word_gcFunctions', 'word_gc_move_roots'):
    ('measure', False, 'MEASURE (\\(x0,x1).      pair_size (list_size (word_loc_size (\\x. 0)))      (pair_size (\\x. 0)      (pair_size (\\x. 0) (pair_size (\\x. 0) (pair_size (\\x. 0) (\\x. 0)))))      x1)'),
  ('word_gcFunctions', 'word_gen_gc'):
    ('new_definition', False, ''),
  ('word_gcFunctions', 'word_gen_gc_can_do_partial'):
    ('new_definition', False, ''),
  ('word_gcFunctions', 'word_gen_gc_move'):
    ('define_single', False, ''),
  ('word_gcFunctions', 'word_gen_gc_move_data'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x1)'),
  ('word_gcFunctions', 'word_gen_gc_move_list'):
    ('measure', True, ''),
  ('word_gcFunctions', 'word_gen_gc_move_loop'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x1)'),
  ('word_gcFunctions', 'word_gen_gc_move_refs'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x1)'),
  ('word_gcFunctions', 'word_gen_gc_move_roots'):
    ('measure', False, 'MEASURE (\\(x0,x1).      pair_size (list_size (word_loc_size (\\x. 0)))      (pair_size (\\x. 0)      (pair_size (\\x. 0)      (pair_size (\\x. 0)      (pair_size (\\x. 0) (pair_size (\\x. 0) (pair_size (\\x. 0) (\\x. 0)))))))      x1)'),
  ('word_gcFunctions', 'word_gen_gc_partial'):
    ('new_definition', False, ''),
  ('word_gcFunctions', 'word_gen_gc_partial_full'):
    ('new_definition', False, ''),
  ('word_gcFunctions', 'word_gen_gc_partial_move'):
    ('define_single', False, ''),
  ('word_gcFunctions', 'word_gen_gc_partial_move_data'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x1)'),
  ('word_gcFunctions', 'word_gen_gc_partial_move_list'):
    ('measure', True, ''),
  ('word_gcFunctions', 'word_gen_gc_partial_move_ref_list'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x0)'),
  ('word_gcFunctions', 'word_gen_gc_partial_move_roots'):
    ('measure', False, 'MEASURE (\\(x0,x1).      pair_size (list_size (word_loc_size (\\x. 0)))      (pair_size (\\x. 0)      (pair_size (\\x. 0)      (pair_size (\\x. 0)      (pair_size (\\x. 0) (pair_size (\\x. 0) (pair_size (\\x. 0) (\\x. 0)))))))      x1)'),
  ('word_inst', 'convert_sub'):
    ('new_definition', False, ''),
  ('word_inst', 'flatten_exp'):
    ('measure', False, 'MEASURE (\\x0. wordLang_exp_size (\\x. 0) x0)'),
  ('word_inst', 'inst_select'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). wordLang_prog_size (\\x. 0) x2)'),
  ('word_inst', 'inst_select_exp'):
    ('measure', False, 'MEASURE (wordLang_exp_size ARB o SND o SND o SND)'),
  ('word_inst', 'is_Lookup_CurrHeap'):
    ('new_definition', False, ''),
  ('word_inst', 'op_consts'):
    ('new_definition', False, ''),
  ('word_inst', 'optimize_consts'):
    ('new_definition', False, ''),
  ('word_inst', 'pull_exp'):
    ('measure', False, 'MEASURE (\\x0. wordLang_exp_size (\\x. 0) x0)'),
  ('word_inst', 'pull_ops'):
    ('prim_rec', False, ''),
  ('word_inst', 'reduce_const'):
    ('new_definition', False, ''),
  ('word_inst', 'rm_const'):
    ('new_definition', False, ''),
  ('word_inst', 'three_to_two_reg'):
    ('measure', False, 'MEASURE (\\x0. wordLang_prog_size (\\x. 0) x0)'),
  ('word_inst', 'three_to_two_reg_prog'):
    ('new_definition', False, ''),
  ('word_inst', 'word_inst_is_const'):
    ('new_definition', False, ''),
  ('word_instProof', 'binary_branch_exp'):
    ('measure', False, 'MEASURE (\\x0. wordLang_exp_size (\\x. 0) x0)'),
  ('word_instProof', 'pull_ops_simp'):
    ('prim_rec', False, ''),
  ('word_remove', 'remove_must_terminate'):
    ('measure', False, 'MEASURE (\\x0. wordLang_prog_size (\\x. 0) x0)'),
  ('word_removeProof', 'compile_state'):
    ('new_definition', False, ''),
  ('word_simp', 'Seq_assoc'):
    ('measure', False, 'MEASURE (\\(x0,x1). wordLang_prog_size (\\x. 0) x1)'),
  ('word_simp', 'SmartSeq'):
    ('new_definition', False, ''),
  ('word_simp', 'all_names'):
    ('new_definition', False, ''),
  ('word_simp', 'const_fp'):
    ('new_definition', False, ''),
  ('word_simp', 'const_fp_exp'):
    ('measure', False, 'MEASURE (\\(x0,x1). wordLang_exp_size (\\x. 0) x0)'),
  ('word_simp', 'const_fp_inst_cs'):
    ('new_definition', False, ''),
  ('word_simp', 'const_fp_loop'):
    ('measure', False, 'MEASURE (\\(x0,x1). wordLang_prog_size (\\x. 0) x0)'),
  ('word_simp', 'const_fp_move_cs'):
    ('prim_rec', False, ''),
  ('word_simp', 'dest_If'):
    ('new_definition', False, ''),
  ('word_simp', 'dest_If_Eq_Imm'):
    ('new_definition', False, ''),
  ('word_simp', 'dest_Raise_num'):
    ('new_definition', False, ''),
  ('word_simp', 'dest_Seq_Assign_Const'):
    ('new_definition', False, ''),
  ('word_simp', 'drop_consts'):
    ('prim_rec', False, ''),
  ('word_simp', 'get_var_imm_cs'):
    ('new_recursive_definition', False, ''),
  ('word_simp', 'is_gc_const'):
    ('new_definition', False, ''),
  ('word_simp', 'is_simple'):
    ('new_definition', False, ''),
  ('word_simp', 'push_out_if'):
    ('new_definition', False, ''),
  ('word_simp', 'push_out_if_aux'):
    ('measure', False, 'MEASURE (\\x0. wordLang_prog_size (\\x. 0) x0)'),
  ('word_simp', 'rewrite_duplicate_if_max_reassoc'):
    ('new_definition', False, ''),
  ('word_simp', 'simp_duplicate_if'):
    ('measure', False, 'MEASURE (\\x0. wordLang_prog_size (\\x. 0) x0)'),
  ('word_simp', 'strip_const'):
    ('measure', False, 'MEASURE (\\x0. wordLang_exp_size1 (\\x. 0) x0)'),
  ('word_simp', 'try_if_hoist1'):
    ('new_definition', False, ''),
  ('word_simp', 'try_if_hoist2'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4). (\\n. n) x0)'),
  ('word_simp', 'word_simp_compile_exp'):
    ('new_definition', False, ''),
  ('word_simp', 'word_simp_dest_Seq'):
    ('new_definition', False, ''),
  ('word_simpProof', 'gc_fun_const_ok'):
    ('new_definition', False, ''),
  ('word_simpProof', 'get_above_handler'):
    ('new_definition', False, ''),
  ('word_simpProof', 'is_gc_word_const'):
    ('new_recursive_definition', False, ''),
  ('word_simpProof', 'sf_gc_consts'):
    ('define_single', False, ''),
  ('word_to_stack', 'PopHandler'):
    ('new_definition', False, ''),
  ('word_to_stack', 'PushHandler'):
    ('new_definition', False, ''),
  ('word_to_stack', 'SeqStackFree'):
    ('new_definition', False, ''),
  ('word_to_stack', 'StackArgs'):
    ('new_definition', False, ''),
  ('word_to_stack', 'StackHandlerArgs'):
    ('new_definition', False, ''),
  ('word_to_stack', 'bits_to_word'):
    ('guess', False, ''),
  ('word_to_stack', 'call_dest'):
    ('new_recursive_definition', False, ''),
  ('word_to_stack', 'chunk_to_bitmap'):
    ('new_definition', False, ''),
  ('word_to_stack', 'chunk_to_bits'):
    ('prim_rec', False, ''),
  ('word_to_stack', 'compile_word_to_stack'):
    ('prim_rec', False, ''),
  ('word_to_stack', 'const_words_to_bitmap'):
    ('measure', False, 'MEASURE (\\(x0,x1). (\\n. n) x1)'),
  ('word_to_stack', 'copy_ret'):
    ('new_definition', False, ''),
  ('word_to_stack', 'copy_ret_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2). (\\n. n) x2)'),
  ('word_to_stack', 'format_var'):
    ('new_recursive_definition', False, ''),
  ('word_to_stack', 'handler_slots'):
    ('new_definition', False, ''),
  ('word_to_stack', 'insert_bitmap'):
    ('new_definition', False, ''),
  ('word_to_stack', 'num_stack_ret'):
    ('new_definition', False, ''),
  ('word_to_stack', 'perf_call_prefix'):
    ('new_definition', False, ''),
  ('word_to_stack', 'perf_call_suffix'):
    ('new_definition', False, ''),
  ('word_to_stack', 'perf_rbp'):
    ('new_definition', False, ''),
  ('word_to_stack', 'perf_rsp'):
    ('new_definition', False, ''),
  ('word_to_stack', 'raise_stub'):
    ('new_definition', False, ''),
  ('word_to_stack', 'skip_free'):
    ('new_definition', False, ''),
  ('word_to_stack', 'stack_arg_count'):
    ('new_definition', False, ''),
  ('word_to_stack', 'stack_move'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3,x4). (\\n. n) x0)'),
  ('word_to_stack', 'store_consts_stub'):
    ('new_definition', False, ''),
  ('word_to_stack', 'wInst'):
    ('new_definition', False, ''),
  ('word_to_stack', 'wLive'):
    ('new_definition', False, ''),
  ('word_to_stack', 'wMove'):
    ('new_definition', False, ''),
  ('word_to_stack', 'wMoveAux'):
    ('measure', False, 'MEASURE (\\(x0,x1).      list_size      (pair_size (sum_size (\\n. n) (\\n. n)) (sum_size (\\n. n) (\\n. n)))      x0)'),
  ('word_to_stack', 'wMoveSingle'):
    ('new_definition', False, ''),
  ('word_to_stack', 'wReg1'):
    ('new_definition', False, ''),
  ('word_to_stack', 'wReg2'):
    ('new_definition', False, ''),
  ('word_to_stack', 'wRegWrite1'):
    ('new_definition', False, ''),
  ('word_to_stack', 'wRegWrite2'):
    ('new_definition', False, ''),
  ('word_to_stack', 'wShareInst'):
    ('new_definition', False, ''),
  ('word_to_stack', 'wStackLoad'):
    ('prim_rec', False, ''),
  ('word_to_stack', 'wStackStore'):
    ('prim_rec', False, ''),
  ('word_to_stack', 'word_to_stack_comp'):
    ('measure', False, ''),
  ('word_to_stack', 'word_to_stack_compile'):
    ('new_definition', False, ''),
  ('word_to_stack', 'word_to_stack_compile_prog'):
    ('new_definition', False, ''),
  ('word_to_stack', 'word_to_stack_stack_free'):
    ('new_definition', False, ''),
  ('word_to_stack', 'word_to_stack_stub_names'):
    ('new_definition', False, ''),
  ('word_to_stack', 'word_to_stack_word_list'):
    ('measure', False, 'MEASURE (LENGTH o FST)'),
  ('word_to_stack', 'write_bitmap'):
    ('new_definition', False, ''),
  ('word_to_stackProof', 'MAP_FST'):
    ('new_definition', False, ''),
  ('word_to_stackProof', 'abs_frame_eq'):
    ('new_definition', False, ''),
  ('word_to_stackProof', 'abs_stack'):
    ('measure', False, ''),
  ('word_to_stackProof', 'adjust_names'):
    ('new_definition', False, ''),
  ('word_to_stackProof', 'compile_result'):
    ('new_recursive_definition', False, ''),
  ('word_to_stackProof', 'handler_val'):
    ('cases', False, ''),
  ('word_to_stackProof', 'index_list'):
    ('prim_rec', False, ''),
  ('word_to_stackProof', 'init_state_ok'):
    ('new_definition', False, ''),
  ('word_to_stackProof', 'is_handler_frame'):
    ('new_definition', False, ''),
  ('word_to_stackProof', 'list_LUPDATE'):
    ('prim_rec', False, ''),
  ('word_to_stackProof', 'map_var'):
    ('nested', False, ''),
  ('word_to_stackProof', 'push_locals'):
    ('new_definition', False, ''),
  ('word_to_stackProof', 'sorted_env'):
    ('define_single', False, ''),
  ('word_to_stackProof', 'stack_rel_aux'):
    ('measure', False, 'MEASURE (\\(x0,x1,x2,x3).      list_size (stack_frame_size (\\x. 0)) x2 +      list_size      (pair_size       (option_size       (pair_size (word_loc_size (\\x. 0)) (word_loc_size (\\x. 0))))      (pair_size (list_size (\\x. 0)) (list_size (word_loc_size (\\x. 0)))))      x3)'),
  ('word_to_stackProof', 'stack_size_rel'):
    ('new_definition', False, ''),
  ('word_to_stackProof', 'word_to_stackProof_make_init'):
    ('new_definition', False, ''),
  ('word_to_stackProof', 'word_to_stackProof_stack_rel'):
    ('new_definition', False, ''),
  ('word_to_stackProof', 'word_to_stackProof_state_rel'):
    ('new_definition', False, ''),
  ('word_to_word', 'full_compile_single'):
    ('new_definition', False, ''),
  ('word_to_word', 'full_compile_single_for_eval'):
    ('new_definition', False, ''),
  ('word_to_word', 'next_n_oracle'):
    ('new_definition', False, ''),
  ('word_to_word', 'word_to_word_compile'):
    ('new_definition', False, ''),
  ('word_to_word', 'word_to_word_compile_single'):
    ('new_definition', False, ''),
  ('word_to_wordProof', 'code_rel_ext'):
    ('new_definition', False, ''),
  ('word_to_wordProof', 'word_to_wordProof_code_rel'):
    ('new_definition', False, ''),
  ('word_unreach', 'Seq_assoc_right'):
    ('measure', False, 'MEASURE (\\(x0,x1). wordLang_prog_size (\\x. 0) x0)'),
  ('word_unreach', 'SimpSeq'):
    ('new_definition', False, ''),
  ('word_unreach', 'dest_Seq_Move'):
    ('new_definition', False, ''),
  ('word_unreach', 'remove_unreach'):
    ('new_definition', False, ''),
  ('word_unreach', 'word_unreach_merge_moves'):
    ('new_definition', False, ''),
  ('word_unreachProof', 'word_unreachProof_copy_vars'):
    ('prim_rec', False, ''),
  ('x64_config', 'x64_backend_config'):
    ('new_definition', False, ''),
  ('x64_config', 'x64_names'):
    ('new_definition', False, ''),
}

PRIMITIVE = {k for k, v in WAY.items() if v[0] == 'new_definition'}
