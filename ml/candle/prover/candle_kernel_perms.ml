(* ======================================================== *)
(*  candle_kernel_perms: ported from HOL4's
    candle/prover/candle_kernel_permsScript.sml
    A definition theory, with no definitions and 222 theorems.
    Needed by candle_kernel_funs.ml.  *)
(* ======================================================== *)

(*
  Prove perms theorems for kernel functions
 *)

needs "candle/prover/ast_extras.ml";;
needs "candle/prover/candle_kernelProg.ml";;
needs "candle/prover/candle_kernel_vals.ml";;
needs "candle/prover/candle_prover_inv.ml";;
needs "candle/prover/perms.ml";;
needs "candle/standard/ml_kernel/ml_hol_kernel_funsProg.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "candle_kernel_perms"
  ["ast_extras"; "candle_kernelProg"; "candle_kernel_vals";
   "candle_prover_inv"; "evaluate"; "evaluateProps"; "misc";
   "ml_hol_kernel_funsProg"; "ml_prog"; "namespaceProps"; "perms";
   "semanticPrimitives"; "semanticPrimitivesProps"];;


(* HOL4 candle_kernel_permsScript.sml:14-16: a proof *)

(* Functions translated with 'translate' should be proved for any ps *)

let perms_ok_word8_fromint_v = prove
 (`perms_ok ps word8_fromint_v`,
  CHEAT_TAC);;
add_simp perms_ok_word8_fromint_v;;

let perms_ok_fst_v = prove
 (`perms_ok ps fst_v`,
  CHEAT_TAC);;
add_simp perms_ok_fst_v;;

let perms_ok_snd_v = prove
 (`perms_ok ps snd_v`,
  CHEAT_TAC);;
add_simp perms_ok_snd_v;;

let perms_ok_exists_v = prove
 (`perms_ok ps exists_v`,
  CHEAT_TAC);;
add_simp perms_ok_exists_v;;

let perms_ok_length_aux_v = prove
 (`perms_ok ps length_aux_v`,
  CHEAT_TAC);;
add_simp perms_ok_length_aux_v;;

let perms_ok_length_v = prove
 (`perms_ok ps length_v`,
  CHEAT_TAC);;
add_simp perms_ok_length_v;;

let perms_ok_map_1_v = prove
 (`perms_ok ps map_1_v`,
  CHEAT_TAC);;
add_simp perms_ok_map_1_v;;

let perms_ok_member_v = prove
 (`perms_ok ps member_v`,
  CHEAT_TAC);;
add_simp perms_ok_member_v;;

let perms_ok_filter_v = prove
 (`perms_ok ps filter_v`,
  CHEAT_TAC);;
add_simp perms_ok_filter_v;;

let perms_ok_every_v = prove
 (`perms_ok ps every_v`,
  CHEAT_TAC);;
add_simp perms_ok_every_v;;

let perms_ok_sort2_tail_v = prove
 (`perms_ok ps sort2_tail_v`,
  CHEAT_TAC);;
add_simp perms_ok_sort2_tail_v;;

let perms_ok_sort3_tail_v = prove
 (`perms_ok ps sort3_tail_v`,
  CHEAT_TAC);;
add_simp perms_ok_sort3_tail_v;;

let perms_ok_div2_v = prove
 (`perms_ok ps div2_v`,
  CHEAT_TAC);;
add_simp perms_ok_div2_v;;

let perms_ok_rev_1_v = prove
 (`perms_ok ps rev_1_v`,
  CHEAT_TAC);;
add_simp perms_ok_rev_1_v;;

let perms_ok_drop_1_v = prove
 (`perms_ok ps drop_1_v`,
  CHEAT_TAC);;
add_simp perms_ok_drop_1_v;;

let perms_ok_merge_tail = prove
 (`perms_ok ps merge_tail_v`,
  CHEAT_TAC);;
add_simp perms_ok_merge_tail;;

let perms_ok_mergesortn_tail_v = prove
 (`perms_ok ps mergesortn_tail_v`,
  CHEAT_TAC);;
add_simp perms_ok_mergesortn_tail_v;;

let perms_ok_mergesort_tail_v = prove
 (`perms_ok ps mergesort_tail_v`,
  CHEAT_TAC);;
add_simp perms_ok_mergesort_tail_v;;

let perms_ok_sort_v = prove
 (`perms_ok ps sort_v`,
  CHEAT_TAC);;
add_simp perms_ok_sort_v;;

let perms_ok_strcat_v = prove
 (`perms_ok ps strcat_v`,
  CHEAT_TAC);;
add_simp perms_ok_strcat_v;;

let perms_ok_string_lt_v = prove
 (`perms_ok ps string_lt_v`,
  CHEAT_TAC);;
add_simp perms_ok_string_lt_v;;

let perms_ok_string_le_v = prove
 (`perms_ok ps string_le_v`,
  CHEAT_TAC);;
add_simp perms_ok_string_le_v;;

let perms_ok_mmap_1_v = prove
 (`perms_ok ps map_1_v`,
  CHEAT_TAC);;
add_simp perms_ok_mmap_1_v;;

let perms_ok_check_tm_v = prove
 (`perms_ok ps check_tm_v`,
  CHEAT_TAC);;
add_simp perms_ok_check_tm_v;;

let perms_ok_check_thm_v = prove
 (`perms_ok ps check_thm_v`,
  CHEAT_TAC);;
add_simp perms_ok_check_thm_v;;

let perms_ok_check_tm_tm_v = prove
 (`perms_ok ps check_tm_tm_v`,
  CHEAT_TAC);;
add_simp perms_ok_check_tm_tm_v;;

let perms_ok_check_ty_ty_v = prove
 (`perms_ok ps check_ty_ty_v`,
  CHEAT_TAC);;
add_simp perms_ok_check_ty_ty_v;;

let perms_ok_vfree_in_v = prove
 (`perms_ok ps vfree_in_v`,
  CHEAT_TAC);;
add_simp perms_ok_vfree_in_v;;

let perms_ok_call_vfree_in_v = prove
 (`perms_ok ps call_vfree_in_v`,
  CHEAT_TAC);;
add_simp perms_ok_call_vfree_in_v;;

let perms_ok_variant_v = prove
 (`perms_ok ps variant_v`,
  CHEAT_TAC);;
add_simp perms_ok_variant_v;;

let perms_ok_call_variant_v = prove
 (`!ps. perms_ok ps call_variant_v`,
  CHEAT_TAC);;
add_simp perms_ok_call_variant_v;;

let perms_ok_concl_v = prove
 (`!ps. perms_ok ps concl_v`,
  CHEAT_TAC);;
add_simp perms_ok_concl_v;;

let perms_ok_assoc_v = prove
 (`perms_ok ps assoc_v`,
  CHEAT_TAC);;
add_simp perms_ok_assoc_v;;

let perms_ok_alphavars_v = prove
 (`perms_ok ps alphavars_v`,
  CHEAT_TAC);;
add_simp perms_ok_alphavars_v;;

let perms_ok_raconv_v = prove
 (`perms_ok ps raconv_v`,
  CHEAT_TAC);;
add_simp perms_ok_raconv_v;;

let perms_ok_aconv_v = prove
 (`perms_ok ps aconv_v`,
  CHEAT_TAC);;
add_simp perms_ok_aconv_v;;

let perms_ok_try_v = prove
 (`perms_ok ps try_v`,
  CHEAT_TAC);;
add_simp perms_ok_try_v;;

let perms_ok_o_1_v = prove
 (`perms_ok ps o_1_v`,
  CHEAT_TAC);;
add_simp perms_ok_o_1_v;;

let perms_ok_dest_vartype_v = prove
 (`perms_ok ps dest_vartype_v`,
  CHEAT_TAC);;
add_simp perms_ok_dest_vartype_v;;

let perms_ok_dest_type_v = prove
 (`perms_ok ps dest_type_v`,
  CHEAT_TAC);;
add_simp perms_ok_dest_type_v;;

let perms_ok_is_type_v = prove
 (`perms_ok ps is_type_v`,
  CHEAT_TAC);;
add_simp perms_ok_is_type_v;;

let perms_ok_is_vartype_v = prove
 (`perms_ok ps is_vartype_v`,
  CHEAT_TAC);;
add_simp perms_ok_is_vartype_v;;

let perms_ok_check_ty_v = prove
 (`perms_ok ps check_ty_v`,
  CHEAT_TAC);;
add_simp perms_ok_check_ty_v;;

let perms_ok_rev_assocd_v = prove
 (`perms_ok ps rev_assocd_v`,
  CHEAT_TAC);;
add_simp perms_ok_rev_assocd_v;;

let perms_ok_type_subst_v = prove
 (`perms_ok ps type_subst_v`,
  CHEAT_TAC);;
add_simp perms_ok_type_subst_v;;

let perms_ok_call_type_subst_v = prove
 (`perms_ok ps call_type_subst_v`,
  CHEAT_TAC);;
add_simp perms_ok_call_type_subst_v;;

let perms_ok_itlist_v = prove
 (`perms_ok ps itlist_v`,
  CHEAT_TAC);;
add_simp perms_ok_itlist_v;;

let perms_ok_insert_1_v = prove
 (`perms_ok ps insert_1_v`,
  CHEAT_TAC);;
add_simp perms_ok_insert_1_v;;

let perms_ok_union_1_v = prove
 (`perms_ok ps union_1_v`,
  CHEAT_TAC);;
add_simp perms_ok_union_1_v;;

let perms_ok_subtract_v = prove
 (`perms_ok ps subtract_v`,
  CHEAT_TAC);;
add_simp perms_ok_subtract_v;;

let perms_ok_forall_v = prove
 (`perms_ok ps forall_v`,
  CHEAT_TAC);;
add_simp perms_ok_forall_v;;

let perms_ok_tyvars_v = prove
 (`!ps. perms_ok ps tyvars_v`,
  CHEAT_TAC);;
add_simp perms_ok_tyvars_v;;

let perms_ok_call_tyvars_v = prove
 (`!ps. perms_ok ps call_tyvars_v`,
  CHEAT_TAC);;
add_simp perms_ok_call_tyvars_v;;

let perms_ok_frees_v = prove
 (`perms_ok ps frees_v`,
  CHEAT_TAC);;
add_simp perms_ok_frees_v;;

let perms_ok_call_frees_v = prove
 (`perms_ok ps call_frees_v`,
  CHEAT_TAC);;
add_simp perms_ok_call_frees_v;;

let perms_ok_freesl_v = prove
 (`perms_ok ps freesl_v`,
  CHEAT_TAC);;
add_simp perms_ok_freesl_v;;

let perms_ok_freesin_v = prove
 (`perms_ok ps freesin_v`,
  CHEAT_TAC);;
add_simp perms_ok_freesin_v;;

let perms_ok_call_freesin_v = prove
 (`perms_ok ps call_freesin_v`,
  CHEAT_TAC);;
add_simp perms_ok_call_freesin_v;;

let perms_ok_type_vars_in_term_v = prove
 (`perms_ok ps type_vars_in_term_v`,
  CHEAT_TAC);;
add_simp perms_ok_type_vars_in_term_v;;

let perms_ok_call_type_vars_in_term_v = prove
 (`perms_ok ps call_type_vars_in_term_v`,
  CHEAT_TAC);;
add_simp perms_ok_call_type_vars_in_term_v;;

let perms_ok_dest_var_v = prove
 (`perms_ok ps dest_var_v`,
  CHEAT_TAC);;
add_simp perms_ok_dest_var_v;;

let perms_ok_dest_const_v = prove
 (`perms_ok ps dest_const_v`,
  CHEAT_TAC);;
add_simp perms_ok_dest_const_v;;

let perms_ok_dest_comb_v = prove
 (`perms_ok ps dest_comb_v`,
  CHEAT_TAC);;
add_simp perms_ok_dest_comb_v;;

let perms_ok_dest_abs_v = prove
 (`perms_ok ps dest_abs_v`,
  CHEAT_TAC);;
add_simp perms_ok_dest_abs_v;;

let perms_ok_dest_thm_v = prove
 (`perms_ok ps dest_thm_v`,
  CHEAT_TAC);;
add_simp perms_ok_dest_thm_v;;

let perms_ok_hyp_v = prove
 (`perms_ok ps hyp_v`,
  CHEAT_TAC);;
add_simp perms_ok_hyp_v;;

let perms_ok_rand_v = prove
 (`perms_ok ps rand_v`,
  CHEAT_TAC);;
add_simp perms_ok_rand_v;;

let perms_ok_rator_v = prove
 (`perms_ok ps rator_v`,
  CHEAT_TAC);;
add_simp perms_ok_rator_v;;

let perms_ok_dest_eq_v = prove
 (`perms_ok ps dest_eq_v`,
  CHEAT_TAC);;
add_simp perms_ok_dest_eq_v;;

let perms_ok_is_var_v = prove
 (`perms_ok ps is_var_v`,
  CHEAT_TAC);;
add_simp perms_ok_is_var_v;;

let perms_ok_is_const_v = prove
 (`perms_ok ps is_const_v`,
  CHEAT_TAC);;
add_simp perms_ok_is_const_v;;

let perms_ok_is_comb_v = prove
 (`perms_ok ps is_comb_v`,
  CHEAT_TAC);;
add_simp perms_ok_is_comb_v;;

let perms_ok_is_abs_v = prove
 (`perms_ok ps is_abs_v`,
  CHEAT_TAC);;
add_simp perms_ok_is_abs_v;;

let perms_ok_vsubst_aux_v = prove
 (`perms_ok ps vsubst_aux_v`,
  CHEAT_TAC);;
add_simp perms_ok_vsubst_aux_v;;

let perms_ok_inst_aux_v = prove
 (`perms_ok ps inst_aux_v`,
  CHEAT_TAC);;
add_simp perms_ok_inst_aux_v;;

let perms_ok_inst_v = prove
 (`perms_ok ps inst_v`,
  CHEAT_TAC);;
add_simp perms_ok_inst_v;;

let perms_ok_mk_vartype_v = prove
 (`perms_ok ps mk_vartype_v`,
  CHEAT_TAC);;
add_simp perms_ok_mk_vartype_v;;

let perms_ok_mk_var_v = prove
 (`perms_ok ps mk_var_v`,
  CHEAT_TAC);;
add_simp perms_ok_mk_var_v;;

let perms_ok_mk_abs_v = prove
 (`perms_ok ps mk_abs_v`,
  CHEAT_TAC);;
add_simp perms_ok_mk_abs_v;;

let perms_ok_compare_1_v = prove
 (`perms_ok ps compare_1_v`,
  CHEAT_TAC);;
add_simp perms_ok_compare_1_v;;

let perms_ok_type_cmp_v = prove
 (`perms_ok ps type_cmp_v`,
  CHEAT_TAC);;
add_simp perms_ok_type_cmp_v;;

let perms_ok_term_cmp_v = prove
 (`perms_ok ps term_cmp_v`,
  CHEAT_TAC);;
add_simp perms_ok_term_cmp_v;;

let perms_ok_ordav_v = prove
 (`perms_ok ps ordav_v`,
  CHEAT_TAC);;
add_simp perms_ok_ordav_v;;

let perms_ok_codomain_v = prove
 (`perms_ok ps codomain_v`,
  CHEAT_TAC);;
add_simp perms_ok_codomain_v;;

let perms_ok_typeof_v = prove
 (`perms_ok ps typeof_v`,
  CHEAT_TAC);;
add_simp perms_ok_typeof_v;;

let perms_ok_orda_v = prove
 (`perms_ok ps orda_v`,
  CHEAT_TAC);;
add_simp perms_ok_orda_v;;

let perms_ok_term_union_v = prove
 (`perms_ok ps term_union_v`,
  CHEAT_TAC);;
add_simp perms_ok_term_union_v;;

let perms_ok_image_v = prove
 (`perms_ok ps image_v`,
  CHEAT_TAC);;
add_simp perms_ok_image_v;;

let perms_ok_eq_mp_v = prove
 (`perms_ok ps eq_mp_v`,
  CHEAT_TAC);;
add_simp perms_ok_eq_mp_v;;

let perms_ok_inst_type_v = prove
 (`perms_ok ps inst_type_v`,
  CHEAT_TAC);;
add_simp perms_ok_inst_type_v;;

let perms_ok_term_remove_v = prove
 (`perms_ok ps term_remove_v`,
  CHEAT_TAC);;
add_simp perms_ok_term_remove_v;;

let perms_ok_can_v = prove
 (`perms_ok ps can_v`,
  CHEAT_TAC);;
add_simp perms_ok_can_v;;

let perms_ok_subset_v = prove
 (`perms_ok ps subset_v`,
  CHEAT_TAC);;
add_simp perms_ok_subset_v;;

let perms_ok_flatten_v = prove
 (`perms_ok ps flatten_v`,
  CHEAT_TAC);;
add_simp perms_ok_flatten_v;;

let perms_ok_get_size_v = prove
 (`perms_ok ps get_size_v`,
  CHEAT_TAC);;
add_simp perms_ok_get_size_v;;

let perms_ok_get_next_size_v = prove
 (`perms_ok ps get_next_size_v`,
  CHEAT_TAC);;
add_simp perms_ok_get_next_size_v;;

let perms_ok_remove_all_v = prove
 (`perms_ok ps remove_all_v`,
  CHEAT_TAC);;
add_simp perms_ok_remove_all_v;;

let perms_ok_smart_remove_v = prove
 (`perms_ok ps smart_remove_v`,
  CHEAT_TAC);;
add_simp perms_ok_smart_remove_v;;

let perms_ok_annotate_v = prove
 (`perms_ok ps annotate_v`,
  CHEAT_TAC);;
add_simp perms_ok_annotate_v;;

let perms_ok_exp_1_v = prove
 (`perms_ok ps exp_1_v`,
  CHEAT_TAC);;
add_simp perms_ok_exp_1_v;;

let perms_ok_newlines_v = prove
 (`perms_ok ps newlines_v`,
  CHEAT_TAC);;
add_simp perms_ok_newlines_v;;

let perms_ok_v2pretty_v = prove
 (`perms_ok ps v2pretty_v`,
  CHEAT_TAC);;
add_simp perms_ok_v2pretty_v;;

let perms_ok_str_tree_to_strs_v = prove
 (`perms_ok ps str_tree_to_strs_v`,
  CHEAT_TAC);;
add_simp perms_ok_str_tree_to_strs_v;;

let perms_ok_null_v = prove
 (`perms_ok ps null_v`,
  CHEAT_TAC);;
add_simp perms_ok_null_v;;

let perms_ok_flat_v = prove
 (`perms_ok ps flat_v`,
  CHEAT_TAC);;
add_simp perms_ok_flat_v;;

let perms_ok_exp_for_dec_enc_v = prove
 (`perms_ok ps exp_for_dec_enc_v`,
  CHEAT_TAC);;
add_simp perms_ok_exp_for_dec_enc_v;;

let perms_ok_tochar_v = prove
 (`perms_ok ps tochar_v`,
  CHEAT_TAC);;
add_simp perms_ok_tochar_v;;

let perms_ok_num_to_chars_v = prove
 (`perms_ok ps num_to_chars_v`,
  CHEAT_TAC);;
add_simp perms_ok_num_to_chars_v;;

let perms_ok_int_to_string_v = prove
 (`perms_ok ps int_to_string_v`,
  CHEAT_TAC);;
add_simp perms_ok_int_to_string_v;;

let perms_ok_tostring_v = prove
 (`perms_ok ps tostring_v`,
  CHEAT_TAC);;
add_simp perms_ok_tostring_v;;

let perms_ok_ty_to_v_v = prove
 (`perms_ok ps ty_to_v_v`,
  CHEAT_TAC);;
add_simp perms_ok_ty_to_v_v;;

let perms_ok_term_to_v_v = prove
 (`perms_ok ps term_to_v_v`,
  CHEAT_TAC);;
add_simp perms_ok_term_to_v_v;;

let perms_ok_thm_to_v_v = prove
 (`perms_ok ps thm_to_v_v`,
  CHEAT_TAC);;
add_simp perms_ok_thm_to_v_v;;

let perms_ok_update_to_v_v = prove
 (`perms_ok ps update_to_v_v`,
  CHEAT_TAC);;
add_simp perms_ok_update_to_v_v;;

let perms_ok_str_every_v = prove
 (`perms_ok ps str_every_v`,
  CHEAT_TAC);;
add_simp perms_ok_str_every_v;;

let perms_ok_isspace_v = prove
 (`perms_ok ps isspace_v`,
  CHEAT_TAC);;
add_simp perms_ok_isspace_v;;

let perms_ok_is_safe_char_v = prove
 (`perms_ok ps is_safe_char_v`,
  CHEAT_TAC);;
add_simp perms_ok_is_safe_char_v;;

let perms_ok_char_escape_seq_v = prove
 (`perms_ok ps char_escape_seq_v`,
  CHEAT_TAC);;
add_simp perms_ok_char_escape_seq_v;;

let perms_ok_char_escaped_v = prove
 (`perms_ok ps char_escaped_v`,
  CHEAT_TAC);;
add_simp perms_ok_char_escaped_v;;

let perms_ok_escape_str_v = prove
 (`perms_ok ps escape_str_v`,
  CHEAT_TAC);;
add_simp perms_ok_escape_str_v;;

let perms_ok_make_str_safe_v = prove
 (`perms_ok ps make_str_safe_v`,
  CHEAT_TAC);;
add_simp perms_ok_make_str_safe_v;;

let perms_ok_sexp2tree_v = prove
 (`perms_ok ps sexp2tree_v`,
  CHEAT_TAC);;
add_simp perms_ok_sexp2tree_v;;

let perms_ok_sexp_to_pretty_string_v = prove
 (`perms_ok ps sexp_to_pretty_string_v`,
  CHEAT_TAC);;
add_simp perms_ok_sexp_to_pretty_string_v;;

let perms_ok_thm_to_string_v = prove
 (`perms_ok ps thm_to_string_v`,
  CHEAT_TAC);;
add_simp perms_ok_thm_to_string_v;;

let perms_ok_funpow_v = prove
 (`perms_ok ps funpow_v`,
  CHEAT_TAC);;
add_simp perms_ok_funpow_v;;

let perms_ok_app_type_v = prove
 (`perms_ok ps app_type_v`,
  CHEAT_TAC);;
add_simp perms_ok_app_type_v;;

let perms_ok_num2bit_v = prove
 (`perms_ok ps num2bit_v`,
  CHEAT_TAC);;
add_simp perms_ok_num2bit_v;;

let perms_ok_cv2term_v = prove
 (`perms_ok ps cv2term_v`,
  CHEAT_TAC);;
add_simp perms_ok_cv2term_v;;

let perms_ok_safemod_v = prove
 (`perms_ok ps safemod_v`,
  CHEAT_TAC);;
add_simp perms_ok_safemod_v;;

let perms_ok_safediv_v = prove
 (`perms_ok ps safediv_v`,
  CHEAT_TAC);;
add_simp perms_ok_safediv_v;;
let perms_ok_alookup_v = prove
 (`perms_ok ps alookup_v`,
  CHEAT_TAC);;
add_simp perms_ok_alookup_v;;

let perms_ok_zip_v = prove
 (`perms_ok ps zip_v`,
  CHEAT_TAC);;
add_simp perms_ok_zip_v;;

let perms_ok_option_v = prove
 (`perms_ok ps option_v`,
  CHEAT_TAC);;
add_simp perms_ok_option_v;;

let perms_ok_check_v = prove
 (`perms_ok ps check_v`,
  CHEAT_TAC);;
add_simp perms_ok_check_v;;

let perms_ok_get_code_v = prove
 (`perms_ok ps get_code_v`,
  CHEAT_TAC);;
add_simp perms_ok_get_code_v;;

let perms_ok_env_lookup_v = prove
 (`perms_ok ps env_lookup_v`,
  CHEAT_TAC);;
add_simp perms_ok_env_lookup_v;;

let perms_ok_exec_v = prove
 (`perms_ok ps exec_v`,
  CHEAT_TAC);;
add_simp perms_ok_exec_v;;

let perms_ok_cv_t_v = prove
 (`perms_ok ps cv_t_v`,
  CHEAT_TAC);;
add_simp perms_ok_cv_t_v;;

let perms_ok_cv_f_v = prove
 (`perms_ok ps cv_f_v`,
  CHEAT_TAC);;
add_simp perms_ok_cv_f_v;;

let perms_ok_to_num_v = prove
 (`perms_ok ps to_num_v`,
  CHEAT_TAC);;
add_simp perms_ok_to_num_v;;

let perms_ok_monop_fst_v = prove
 (`perms_ok ps monop_fst_v`,
  CHEAT_TAC);;
add_simp perms_ok_monop_fst_v;;

let perms_ok_monop_snd_v = prove
 (`perms_ok ps monop_snd_v`,
  CHEAT_TAC);;
add_simp perms_ok_monop_snd_v;;

let perms_ok_monop_ispair_v = prove
 (`perms_ok ps monop_ispair_v`,
  CHEAT_TAC);;
add_simp perms_ok_monop_ispair_v;;

let perms_ok_monop_v = prove
 (`perms_ok ps monop_v`,
  CHEAT_TAC);;
add_simp perms_ok_monop_v;;

let perms_ok_binop_add_v = prove
 (`perms_ok ps binop_add_v`,
  CHEAT_TAC);;
add_simp perms_ok_binop_add_v;;

let perms_ok_binop_sub_v = prove
 (`perms_ok ps binop_sub_v`,
  CHEAT_TAC);;
add_simp perms_ok_binop_sub_v;;

let perms_ok_binop_mul_v = prove
 (`perms_ok ps binop_mul_v`,
  CHEAT_TAC);;
add_simp perms_ok_binop_mul_v;;

let perms_ok_binop_div_v = prove
 (`perms_ok ps binop_div_v`,
  CHEAT_TAC);;
add_simp perms_ok_binop_div_v;;

let perms_ok_binop_mod_v = prove
 (`perms_ok ps binop_mod_v`,
  CHEAT_TAC);;
add_simp perms_ok_binop_mod_v;;

let perms_ok_binop_eq_v = prove
 (`perms_ok ps binop_eq_v`,
  CHEAT_TAC);;
add_simp perms_ok_binop_eq_v;;

let perms_ok_binop_less_v = prove
 (`perms_ok ps binop_less_v`,
  CHEAT_TAC);;
add_simp perms_ok_binop_less_v;;

let perms_ok_binop_v = prove
 (`perms_ok ps binop_v`,
  CHEAT_TAC);;
add_simp perms_ok_binop_v;;

let perms_ok_findi_1_v = prove
 (`perms_ok ps findi_1_v`,
  CHEAT_TAC);;
add_simp perms_ok_findi_1_v;;

let perms_ok_to_ce_v = prove
 (`perms_ok ps to_ce_v`,
  CHEAT_TAC);;
add_simp perms_ok_to_ce_v;;

let perms_ok_rev_v = prove
 (`perms_ok ps rev_v`,
  CHEAT_TAC);;
add_simp perms_ok_rev_v;;

let perms_ok_reverse_v = prove
 (`perms_ok ps reverse_v`,
  CHEAT_TAC);;
add_simp perms_ok_reverse_v;;

let perms_ok_compile_to_ce_v = prove
 (`perms_ok ps compile_to_ce_v`,
  CHEAT_TAC);;
add_simp perms_ok_compile_to_ce_v;;

let perms_ok_build_funs_v = prove
 (`perms_ok ps build_funs_v`,
  CHEAT_TAC);;
add_simp perms_ok_build_funs_v;;

let perms_ok_compute_thms_v = prove
 (`perms_ok ps compute_thms_v`,
  CHEAT_TAC);;
add_simp perms_ok_compute_thms_v;;

let perms_ok_compute_init_v = prove
 (`perms_ok ps compute_init_v`,
  CHEAT_TAC);;
add_simp perms_ok_compute_init_v;;

let perms_ok_list_dest_comb_v = prove
 (`perms_ok ps list_dest_comb_v`,
  CHEAT_TAC);;
add_simp perms_ok_list_dest_comb_v;;

let perms_ok_mapoption_v = prove
 (`perms_ok ps mapoption_v`,
  CHEAT_TAC);;
add_simp perms_ok_mapoption_v;;

let perms_ok_i_v = prove
 (`perms_ok ps i_v`,
  CHEAT_TAC);;
add_simp perms_ok_i_v;;

let perms_ok_dest_num_v = prove
 (`perms_ok ps dest_num_v`,
  CHEAT_TAC);;
add_simp perms_ok_dest_num_v;;

let perms_ok_dest_numeral_v = prove
 (`perms_ok ps dest_numeral_v`,
  CHEAT_TAC);;
add_simp perms_ok_dest_numeral_v;;

let perms_ok_dest_binary_v = prove
 (`perms_ok ps dest_binary_v`,
  CHEAT_TAC);;
add_simp perms_ok_dest_binary_v;;

let perms_ok_dest_numeral_opt_v = prove
 (`perms_ok ps dest_numeral_opt_v`,
  CHEAT_TAC);;
add_simp perms_ok_dest_numeral_opt_v;;

let perms_ok_hd_v = prove
 (`perms_ok ps hd_v`,
  CHEAT_TAC);;
add_simp perms_ok_hd_v;;

let perms_ok_dest_cexp_v = prove
 (`perms_ok ps dest_cexp_v`,
  CHEAT_TAC);;
add_simp perms_ok_dest_cexp_v;;

let perms_ok_check_cexp_closed_v = prove
 (`perms_ok ps check_cexp_closed_v`,
  CHEAT_TAC);;
add_simp perms_ok_check_cexp_closed_v;;

let perms_ok_map_2_v = prove
 (`perms_ok ps map_2_v`,
  CHEAT_TAC);;
add_simp perms_ok_map_2_v;;

let perms_ok_all_distinct_v = prove
 (`perms_ok ps all_distinct_v`,
  CHEAT_TAC);;
add_simp perms_ok_all_distinct_v;;

let perms_ok_check_var_v = prove
 (`perms_ok ps check_var_v`,
  CHEAT_TAC);;
add_simp perms_ok_check_var_v;;

let perms_ok_var_list_v = prove
 (`perms_ok ps var_list_v`,
  CHEAT_TAC);;
add_simp perms_ok_var_list_v;;

let perms_ok_check_eqn_v = prove
 (`perms_ok ps check_eqn_v`,
  CHEAT_TAC);;
add_simp perms_ok_check_eqn_v;;

let perms_ok_const_list_v = prove
 (`perms_ok ps const_list_v`,
  CHEAT_TAC);;
add_simp perms_ok_const_list_v;;

let perms_ok_check_consts_v = prove
 (`perms_ok ps check_consts_v`,
  CHEAT_TAC);;
add_simp perms_ok_check_consts_v;;

let perms_ok_compute_default_clock_v = prove
 (`perms_ok ps compute_default_clock_v`,
  CHEAT_TAC);;
add_simp perms_ok_compute_default_clock_v;;

let perms_ok_bool_ty_v = prove
 (`perms_ok kernel_perms bool_ty_v`,
  CHEAT_TAC);;
add_simp perms_ok_bool_ty_v;;

let perms_ok_aty_v = prove
 (`perms_ok kernel_perms aty_v`,
  CHEAT_TAC);;
add_simp perms_ok_aty_v;;

(* Functions translated with 'm_translate' should be proved for kernel_perms *)

let perms_ok_the_type_constants = prove
 (`perms_ok kernel_perms the_type_constants`,
  CHEAT_TAC);;
add_simp perms_ok_the_type_constants;;

let perms_ok_the_term_constants = prove
 (`perms_ok kernel_perms the_term_constants`,
  CHEAT_TAC);;
add_simp perms_ok_the_term_constants;;

let perms_ok_the_axioms = prove
 (`perms_ok kernel_perms the_axioms`,
  CHEAT_TAC);;
add_simp perms_ok_the_axioms;;

let perms_ok_constants_v = prove
 (`perms_ok kernel_perms constants_v`,
  CHEAT_TAC);;
add_simp perms_ok_constants_v;;

let perms_ok_types_v = prove
 (`perms_ok kernel_perms types_v`,
  CHEAT_TAC);;
add_simp perms_ok_types_v;;

let perms_ok_axioms_v = prove
 (`perms_ok kernel_perms axioms_v`,
  CHEAT_TAC);;
add_simp perms_ok_axioms_v;;

let perms_ok_get_type_arity_v = prove
 (`perms_ok kernel_perms get_type_arity_v`,
  CHEAT_TAC);;
add_simp perms_ok_get_type_arity_v;;

let perms_ok_mk_type_v = prove
 (`perms_ok kernel_perms mk_type_v`,
  CHEAT_TAC);;
add_simp perms_ok_mk_type_v;;

let perms_ok_mk_fun_ty_v = prove
 (`perms_ok kernel_perms mk_fun_ty_v`,
  CHEAT_TAC);;
add_simp perms_ok_mk_fun_ty_v;;

let perms_ok_type_of_v = prove
 (`perms_ok kernel_perms type_of_v`,
  CHEAT_TAC);;
add_simp perms_ok_type_of_v;;

let perms_ok_call_type_of_v = prove
 (`perms_ok kernel_perms call_type_of_v`,
  CHEAT_TAC);;
add_simp perms_ok_call_type_of_v;;

let perms_ok_get_const_type_v = prove
 (`perms_ok kernel_perms get_const_type_v`,
  CHEAT_TAC);;
add_simp perms_ok_get_const_type_v;;

let perms_ok_mk_const_v = prove
 (`perms_ok kernel_perms mk_const_v`,
  CHEAT_TAC);;
add_simp perms_ok_mk_const_v;;

let perms_ok_mk_comb_v = prove
 (`perms_ok kernel_perms mk_comb_v`,
  CHEAT_TAC);;
add_simp perms_ok_mk_comb_v;;

let perms_ok_mk_eq_v = prove
 (`perms_ok kernel_perms mk_eq_v`,
  CHEAT_TAC);;
add_simp perms_ok_mk_eq_v;;

let perms_ok_safe_mk_eq_v = prove
 (`perms_ok kernel_perms safe_mk_eq_v`,
  CHEAT_TAC);;
add_simp perms_ok_safe_mk_eq_v;;

let perms_ok_mk_comb_1_v = prove
 (`perms_ok kernel_perms mk_comb_1_v`,
  CHEAT_TAC);;
add_simp perms_ok_mk_comb_1_v;;

let perms_ok_refl_v = prove
 (`perms_ok kernel_perms refl_v`,
  CHEAT_TAC);;
add_simp perms_ok_refl_v;;

let perms_ok_assume_v = prove
 (`perms_ok kernel_perms assume_v`,
  CHEAT_TAC);;
add_simp perms_ok_assume_v;;

let perms_ok_deduct_antisym_rule_v = prove
 (`perms_ok kernel_perms deduct_antisym_rule_v`,
  CHEAT_TAC);;
add_simp perms_ok_deduct_antisym_rule_v;;

let perms_ok_vsubst_v = prove
 (`perms_ok kernel_perms vsubst_v`,
  CHEAT_TAC);;
add_simp perms_ok_vsubst_v;;

let perms_ok_inst_1_v = prove
 (`perms_ok kernel_perms inst_1_v`,
  CHEAT_TAC);;
add_simp perms_ok_inst_1_v;;

let perms_ok_beta_v = prove
 (`perms_ok kernel_perms beta_v`,
  CHEAT_TAC);;
add_simp perms_ok_beta_v;;

let perms_ok_trans_v = prove
 (`perms_ok kernel_perms trans_v`,
  CHEAT_TAC);;
add_simp perms_ok_trans_v;;

let perms_ok_abs_v = prove
 (`perms_ok kernel_perms abs_1_v`,
  CHEAT_TAC);;
add_simp perms_ok_abs_v;;

let perms_ok_check_for_dups_v = prove
 (`perms_ok ps check_for_dups_v`,
  CHEAT_TAC);;
add_simp perms_ok_check_for_dups_v;;

let perms_ok_add_constants_v = prove
 (`perms_ok kernel_perms add_constants_v`,
  CHEAT_TAC);;
add_simp perms_ok_add_constants_v;;

let perms_ok_the_context = prove
 (`perms_ok kernel_perms the_context`,
  CHEAT_TAC);;
add_simp perms_ok_the_context;;

let perms_ok_add_def_v = prove
 (`perms_ok kernel_perms add_def_v`,
  CHEAT_TAC);;
add_simp perms_ok_add_def_v;;

let perms_ok_new_constant_v = prove
 (`perms_ok kernel_perms new_constant_v`,
  CHEAT_TAC);;
add_simp perms_ok_new_constant_v;;

let perms_ok_add_type_v = prove
 (`perms_ok kernel_perms add_type_v`,
  CHEAT_TAC);;
add_simp perms_ok_add_type_v;;

let perms_ok_new_type_v = prove
 (`perms_ok kernel_perms new_type_v`,
  CHEAT_TAC);;
add_simp perms_ok_new_type_v;;

let perms_ok_call_new_type_v = prove
 (`perms_ok kernel_perms call_new_type_v`,
  CHEAT_TAC);;
add_simp perms_ok_call_new_type_v;;

let perms_ok_new_axiom_v = prove
 (`perms_ok kernel_perms new_axiom_v`,
  CHEAT_TAC);;
add_simp perms_ok_new_axiom_v;;

let perms_ok_new_specification_v = prove
 (`perms_ok kernel_perms new_specification_v`,
  CHEAT_TAC);;
add_simp perms_ok_new_specification_v;;

let perms_ok_new_basic_definition_v = prove
 (`perms_ok kernel_perms new_basic_definition_v`,
  CHEAT_TAC);;
add_simp perms_ok_new_basic_definition_v;;

let perms_ok_new_basic_type_definition_v = prove
 (`perms_ok kernel_perms new_basic_type_definition_v`,
  CHEAT_TAC);;
add_simp perms_ok_new_basic_type_definition_v;;

let perms_ok_compute_add_v = prove
 (`perms_ok kernel_perms compute_add_v`,
  CHEAT_TAC);;
add_simp perms_ok_compute_add_v;;

let perms_ok_compute_v = prove
 (`perms_ok kernel_perms compute_v`,
  CHEAT_TAC);;
add_simp perms_ok_compute_v;;

(* HOL4 candle_kernel_permsScript.sml:1627-1680: code that the source has in
   a comment *)

(* [local] *)
let evaluate_kernel_perms_lemma = prove
 (`!ps.
     evaluate s env [exp] = (s',res) /\
     perms_ok_exp ps exp /\ perms_ok_env ps (freevars exp) env
       /\ perms_ok_state ps s /\ ~(DoFFI IN ps) /\ ~(RefAlloc IN ps)
       /\ ~(W8Alloc IN ps) ==>
     LENGTH (semanticPrimitives_state_refs s') = LENGTH
       (semanticPrimitives_state_refs s) /\ semanticPrimitives_state_ffi
     s' = semanticPrimitives_state_ffi s
       /\ semanticPrimitives_state_eval_state
     s' = semanticPrimitives_state_eval_state s`,
  CHEAT_TAC);;

let evaluate_kernel_perms =
  REWRITE_RULE [GSYM kernel_perms_def] (SIMP_RULE [kernel_perms_def]
  (CAKE_SPEC `kernel_perms` evaluate_kernel_perms_lemma));;

let evaluate_empty_perms =
  SIMP_RULE [] (CAKE_SPEC `{}` evaluate_kernel_perms_lemma);;

(* and the interface *)
let _ = unhide_overloads ();;
