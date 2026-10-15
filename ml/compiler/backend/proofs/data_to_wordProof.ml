(* ======================================================== *)
(*  data_to_wordProof: ported from HOL4's
    compiler/backend/proofs/data_to_wordProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for data_to_word
*)

needs "compiler/backend/backend.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/gc/copying_gc.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "compiler/backend/gc/gen_gc_partial.ml";;
needs "compiler/backend/proofs/data_to_word_assignProof.ml";;
needs "compiler/backend/proofs/data_to_word_bignumProof.ml";;
needs "compiler/backend/proofs/data_to_word_gcProof.ml";;
needs "compiler/backend/proofs/data_to_word_memoryProof.ml";;
needs "compiler/backend/proofs/wordConvsProof.ml";;
needs "compiler/backend/proofs/word_bignumProof.ml";;
needs "compiler/backend/proofs/word_to_wordProof.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/backend/word_to_word.ml";;
needs "lib/alignment.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "semantics/proofs/semanticsProps.ml";;
(* HOL4 ancestors outside the port: int_bitwise finite_map While *)

(* HOL4 ML code, not ported:
val clean_tac = rpt var_eq_tac \\ rpt (qpat_x_assum `T` kall_tac)
fun rpt_drule th = old_drule (th |> GEN_ALL) \\ rpt (disch_then
  old_drule \\ fs [])
*)

(* HOL4 ML code, not ported:
val state_rel_def = data_to_word_gcProofTheory.state_rel_def
val code_rel_def = data_to_word_gcProofTheory.code_rel_def
*)

(* HOL4 ML code, not ported:
val assign_def =
  data_to_wordTheory.assign_def
  |> REWRITE_RULE [data_to_wordTheory.arg1_def,
                   data_to_wordTheory.arg2_def,
                   data_to_wordTheory.arg3_def,
                   data_to_wordTheory.arg4_def,
                   data_to_wordTheory.all_assign_defs];
*)

(* shared conjunct tail for the two popped-frame cases (Env / Exc) of
   state_rel_pop_env_set_vars_IMP below. *)
(* HOL4 ML code, not ported:
val psv_tail =
  conj_asm1_tac
  >- (`ALOOKUP fvs 0 = NONE`
        by (simp[ALOOKUP_NONE] \\ fs[EVERY_MEM,MEM_MAP,FORALL_PROD] \\
          metis_tac[])
      \\ `lookup 0 (alist_insert (MAP adjust_var ns) ws
              (union (fromAList fvs) (fromAList fws)))
            = lookup 0 (union (fromAList fvs) (fromAList fws))`
            by (rw[lookup_alist_insert]
                \\ `ALOOKUP (ZIP (MAP adjust_var ns,ws)) 0 = NONE`
                     by simp[ALOOKUP_NONE,MAP_ZIP]
                \\ simp[])
      \\ fs[lookup_union,lookup_fromAList])
  \\ qpat_assum ‘_ t1.mdomain limit’ $ irule_at Any \\ simp[]
  \\ drule option_le_tl \\ strip_tac \\ simp[]
  \\ conj_tac
  >- (rw[] \\ rename [‘lookup vv (union (fromAList (ZIP (ns,as))) s)’]
      \\ simp[lookup_alist_insert]
      \\ Cases_on ‘MEM vv ns’
      >- (`MEM (adjust_var vv) (MAP adjust_var ns)` by (simp[MEM_MAP] \\
        metis_tac[])
          \\ `IS_SOME (ALOOKUP (ZIP (MAP adjust_var ns,ws)) (adjust_var
            vv))` by
               (Cases_on `ALOOKUP (ZIP (MAP adjust_var ns,ws))
                 (adjust_var vv)`
                \\ gvs[ALOOKUP_NONE,MAP_ZIP])
          \\ CASE_TAC \\ fs[])
      \\ `lookup vv (fromAList (ZIP (ns,as))) = NONE`
           by simp[lookup_fromAList,ALOOKUP_NONE,MAP_ZIP]
      \\ `IS_SOME (lookup vv s)` by fs[lookup_union]
      \\ `IS_SOME (lookup (adjust_var vv) (fromAList fvs))` by
        metis_tac[]
      \\ CASE_TAC \\ fs[lookup_union] \\ every_case_tac \\ fs[])
  \\ fs[flat_def]
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac
    word_ml_inv_rearrange)
  \\ rw[] \\ fs[]
  \\ fs[join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD,MEM_toAList,
        lookup_inter_alt,AllCaseEqs()]
  \\ reverse (Cases_on `MEM p_1 (MAP adjust_var ns)`)
  >- (* p_1 is from the popped frame, not freshly set *)
     (`lookup p_1 (union (fromAList fvs) (fromAList fws)) = SOME p_2` by
         (qpat_x_assum `lookup p_1 (alist_insert _ _ _) = _` mp_tac
          \\ rw[lookup_alist_insert]
          \\ `ALOOKUP (ZIP (MAP adjust_var ns,ws)) p_1 = NONE`
               by simp[ALOOKUP_NONE,MAP_ZIP,LENGTH_MAP]
          \\ fs[])
      \\ `ALOOKUP fws p_1 = NONE` by
           (Cases_on `ALOOKUP fws p_1` \\ fs[] \\ imp_res_tac
             ALOOKUP_MEM
            \\ fs[EVERY_MEM,FORALL_PROD] \\ res_tac \\ fs[])
      \\ `ALOOKUP fvs p_1 = SOME p_2` by
           (fs[lookup_union,lookup_fromAList] \\ Cases_on `ALOOKUP fvs
             p_1` \\ fs[])
      \\ `adjust_var ((p_1 - 2) DIV 2) = p_1` by (irule IMP_adjust_var
        \\ fs[])
      \\ `~MEM ((p_1 - 2) DIV 2) ns` by (CCONTR_TAC \\ fs[MEM_MAP] \\
        metis_tac[])
      \\ `lookup ((p_1 - 2) DIV 2) (union (fromAList (ZIP (ns,as))) s)
            = lookup ((p_1 - 2) DIV 2) s` by
           (simp[lookup_union]
            \\ `ALOOKUP (ZIP (ns,as)) ((p_1 - 2) DIV 2) = NONE` by
              simp[ALOOKUP_NONE,MAP_ZIP]
            \\ simp[lookup_fromAList])
      \\ disj1_tac \\ disj2_tac
      \\ qexists_tac `p_1` \\ imp_res_tac ALOOKUP_MEM \\ fs[])
  \\ (* p_1 is a freshly set return variable *)
     (fs[MEM_MAP]
      \\ `adjust_var ((p_1 - 2) DIV 2) = p_1` by (irule IMP_adjust_var
        \\ fs[])
      \\ `(p_1 - 2) DIV 2 = y` by metis_tac[adjust_var_11]
      \\ gvs[MEM_EL] \\ rename1 ‘EL ix ns’
      \\ `ALOOKUP (ZIP (MAP adjust_var ns,ws)) (adjust_var (EL ix ns)) =
        SOME (EL ix ws)` by
           (irule ALOOKUP_ALL_DISTINCT_MEM \\ simp[MAP_ZIP,LENGTH_MAP]
            \\ simp[MEM_ZIP,LENGTH_MAP] \\ qexists_tac `ix` \\
              simp[EL_MAP])
      \\ `p_2 = EL ix ws` by
           (qpat_x_assum `lookup _ (alist_insert _ _ _) = SOME p_2`
             mp_tac
            \\ simp[lookup_alist_insert])
      \\ `lookup (EL ix ns) (union (fromAList (ZIP (ns,as))) s) = SOME
        (EL ix as)` by
           (simp[lookup_union]
            \\ `ALOOKUP (ZIP (ns,as)) (EL ix ns) = SOME (EL ix as)` by
                 (irule ALOOKUP_ALL_DISTINCT_MEM \\ simp[MAP_ZIP]
                  \\ simp[MEM_ZIP] \\ qexists_tac `ix` \\ simp[])
            \\ simp[lookup_fromAList])
      \\ disj1_tac \\ disj1_tac \\ disj1_tac \\ disj1_tac
      \\ simp[MEM_ZIP] \\ qexists_tac `ix` \\ simp[EL_ZIP]);
*)

(* multi-value generalisation of state_rel_pop_env_set_var_IMP
   (gcProof): the
   returning-Call reconstruction places the whole result list via
     set_vars. *)

(* HOL4 ML code, not ported:
Resume state_rel_pop_env_set_vars_IMP[psv_env]:
  psv_tail
QED
*)

(* HOL4 ML code, not ported:
Resume state_rel_pop_env_set_vars_IMP[psv_exc]:
  psv_tail
QED
*)

(* HOL4 ML code, not ported:
Finalise state_rel_pop_env_set_vars_IMP;
*)

(* HOL4 ML code, not ported:
Resume data_compile_correct[Skip]:
  (fs [comp_def,dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ srw_tac[][] \\ fs [state_rel_def])
QED
*)

(* HOL4 ML code, not ported:
Resume data_compile_correct[Move]:
  (fs [comp_def,dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var src s.locals` \\ fs [] \\ srw_tac[][]
    \\ fs [] \\ imp_res_tac state_rel_get_var_IMP \\ fs []
    \\ fs
      [wordSemTheory.get_vars_def,wordSemTheory.set_vars_def
      ,alist_insert_def]
    \\ fs [state_rel_def,set_var_def,lookup_insert]
    \\ rpt strip_tac \\ fs []
    THEN1 (srw_tac[][] \\ Cases_on `n = dest` \\ fs [])
    \\ asm_exists_tac
    \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
    \\ imp_res_tac word_ml_inv_get_var_IMP
    \\ match_mp_tac word_ml_inv_insert \\ fs [])
QED
*)

(* HOL4 ML code, not ported:
Resume data_compile_correct[Assign]:
  (fs [comp_def,dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ gvs [CaseEq"bool"]
    \\ gvs [CaseEq"option"]
    \\ reverse (Cases_on `do_app op xs v`) \\ fs []
    THEN1 (imp_res_tac do_app_Rerr \\ rveq \\ fs []
           \\ drule_all assign_FFI_final
           \\ disch_then $ qspecl_then [`n`,`l`,`dest`] strip_assume_tac
           \\ asm_exists_tac >> fs[] >> rpt strip_tac \\
             fs[flush_state_def]
           \\ imp_res_tac cut_state_opt_ffi \\ fs []
           \\ imp_res_tac cut_state_opt_const \\
             fs[state_rel_def,flush_state_def]
           \\ fs [cut_state_opt_def,CaseEq"option",cut_state_def] \\
             rveq \\ fs [])
    \\ Cases_on `a` \\ gvs [CaseEq"option"]
    \\ drule_all assign_thm \\ fs []
    \\ disch_then (qspecl_then [`n`,`l`,`dest`] strip_assume_tac)
    \\ `option_le r'.stack_max r.stack_max` by
        (Cases_on `q' = SOME NotEnoughSpace` \\ fs
          [state_rel_def,set_var_def])
    \\ fs [set_var_def]
    \\ imp_res_tac do_app_io_events_mono \\ rfs []
    \\ `s.ffi = t.ffi` by fs [state_rel_def]
    \\ strip_tac \\ gvs []
    \\ imp_res_tac cut_state_opt_ffi \\ fs [])
QED
*)

(* HOL4 ML code, not ported:
Resume data_compile_correct[Force]:
  (simp [comp_def, force_thunk_def]
    \\ TOP_CASE_TAC \\ gvs []
    >- gvs [encode_header_def, encode_header_def, state_rel_def,
            good_dimindex_def, limits_inv_def, dimword_def,
              memory_rel_def,
            heap_in_memory_store_def, consume_space_def, arch_size_def,
            NOT_LESS]
    \\ simp [wordSemTheory.evaluate_def]
    \\ gvs [evaluate_def]
    \\ Cases_on ‘get_var src s.locals’ \\ gvs []
    \\ Cases_on ‘dest_thunk x' s.refs’ \\ gvs []
    \\ gvs [oneline dest_thunk_def]
    \\ Cases_on ‘x'’ \\ gvs []
    \\ Cases_on ‘lookup n' s.refs’ \\ gvs []
    \\ Cases_on ‘x'’ \\ gvs []
    \\ Cases_on ‘b’ \\ gvs []
    >- (Cases_on ‘t''’ \\ gvs [])
    \\ ‘IsThunk t' v = IsThunk t'' a’ by (Cases_on ‘t''’ \\ gvs []) \\
      gvs []
    \\ qpat_x_assum ‘_ = IsThunk t' a’ kall_tac
    \\ drule_all state_rel_get_var_IMP \\ strip_tac \\ gvs []
    \\ simp [wordSemTheory.get_var_imm_def]
    \\ TOP_CASE_TAC \\ gvs []
    >- (Cases_on ‘w’
        \\ gvs [wordSemTheory.word_cmp_def]
        \\ drule_all state_rel_get_var_RefPtr_Loc \\ gvs [])
    \\ qpat_assum ‘state_rel _ _ _ _ _ _ _’ mp_tac
    \\ pure_rewrite_tac [Once state_rel_thm] \\ strip_tac \\ gvs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ drule memory_rel_lookup
    \\ gvs [get_var_def, wordSemTheory.get_var_def]
    \\ disch_then drule \\ gvs []
    \\ strip_tac \\ gvs []
    \\ TOP_CASE_TAC \\ gvs []
    >- (
      drule memory_rel_Thunk_inlined \\ gvs []
      \\ impl_tac \\ gvs []
      >- (
        Cases_on ‘w’ \\ gvs [asmTheory.word_cmp_def]
        \\ full_simp_tac std_ss [WORD_AND_COMM]
        \\ gvs [word_and_one_eq_0_iff])
      \\ rw []
      \\ TOP_CASE_TAC \\ gvs []
      >- (
        simp [wordSemTheory.evaluate_def, wordSemTheory.get_var_def,
              wordSemTheory.get_vars_def, wordSemTheory.flush_state_def,
              flush_state_def]
        \\ gvs [state_rel_thm]
        \\ conj_tac
        >- (
          irule backendPropsTheory.option_le_trans
          \\ first_x_assum $ irule_at Any
          \\ Cases_on ‘s.locals_size’ \\ fs []
          \\ Cases_on ‘stack_size t.stack’ \\ fs [])
        \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
        \\ match_mp_tac memory_rel_rearrange
        \\ simp [SF DNF_ss, join_env_def])
      \\ TOP_CASE_TAC \\ gvs []
      \\ simp [wordSemTheory.evaluate_def, wordSemTheory.word_exp_def,
               wordSemTheory.get_var_def]
      \\ gvs [AllCaseEqs()]
      \\ simp [set_var_def, wordSemTheory.set_var_def]
      \\ gvs [state_rel_thm, lookup_insert, adjust_var_11]
      \\ conj_tac >- (rw [] \\ gvs [cut_env_def,lookup_inter_alt]
                      \\ pop_assum mp_tac \\ rw [] \\ fs [])
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert
      \\ fs[inter_insert_ODD_adjust_set_alt]
      \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
      \\ match_mp_tac memory_rel_rearrange
      \\ simp [SF DNF_ss]
      \\ rpt strip_tac
      \\ drule_all MEM_join_env_cut_env \\ fs [])
    \\ Cases_on ‘w’ \\ gvs [asmTheory.word_cmp_def,
      wordSemTheory.word_cmp_def]
    \\ full_simp_tac std_ss [WORD_AND_COMM]
    \\ gvs [word_and_one_eq_0_iff]
    \\ simp [Once list_Seq_def, wordSemTheory.evaluate_def]
    \\ ‘∃x' w. get_real_addr c t.store c' = SOME x' ∧
               x' ∈ t.mdomain ∧
               t.memory x' = Word w’ by (
      drule_all memory_rel_Thunk_IMP \\ rw [] \\ metis_tac []) \\ gvs []
    \\ ‘word_exp t (real_addr c (adjust_var src)) = SOME (Word x')’
      by metis_tac [get_real_addr_lemma, wordSemTheory.get_var_def] \\
        gvs []
    \\ simp [Once list_Seq_def, wordSemTheory.evaluate_def]
    \\ simp [wordSemTheory.set_var_def, wordSemTheory.word_exp_def,
             wordSemTheory.get_var_def, wordSemTheory.the_words_def,
             wordSemTheory.mem_load_def, word_op_def]
    \\ simp [list_Seq_def, wordSemTheory.evaluate_def]
    \\ simp [wordSemTheory.get_var_def, wordSemTheory.get_var_imm_def]
    \\ simp [asmTheory.word_cmp_def]
    \\ rename [‘_ = SOME (Thunk has_been_eval a)’]
    \\ drule_all memory_rel_Thunk_IMP \\ gvs []
    \\ drule_all memory_rel_Thunk_bits \\ gvs []
    \\ strip_tac \\ gvs []
    >- ((* inlined pointer case *)
      reverse $ strip_tac \\ gvs []
      >- (
        drule word_test_lemma1 \\ gvs []
        \\ disch_then $ qspec_then ‘w’ assume_tac \\ gvs [])
      \\ TOP_CASE_TAC \\ gvs []
      >- (
        simp [wordSemTheory.evaluate_def, wordSemTheory.get_var_def,
              lookup_insert, wordSemTheory.get_vars_def]
        \\ simp [flush_state_def, wordSemTheory.flush_state_def]
        \\ gvs [state_rel_thm]
        \\ conj_tac
        >-
         (irule backendPropsTheory.option_le_trans
          \\ first_x_assum $ irule_at Any
          \\ Cases_on ‘s.locals_size’ \\ fs []
          \\ Cases_on ‘stack_size t.stack’ \\ fs [])
        \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
        \\ match_mp_tac memory_rel_rearrange
        \\ simp [SF DNF_ss, join_env_def])
      \\ TOP_CASE_TAC \\ gvs []
      \\ simp [wordSemTheory.evaluate_def, wordSemTheory.word_exp_def,
               wordSemTheory.get_var_def, lookup_insert,
               wordSemTheory.the_words_def, word_op_def,
               wordSemTheory.mem_load_def]
      \\ gvs [wordSemTheory.get_var_def, wordSemTheory.set_var_def]
      \\ Cases_on ‘cut_env r s.locals’ \\ gvs []
      \\ conj_tac >- (simp [set_var_def])
      \\ simp [wordSemTheory.set_var_def, set_var_def]
      \\ fs [state_rel_thm,lookup_insert,adjust_var_11]
      \\ conj_tac >- (rw [] \\ gvs [cut_env_def,lookup_inter_alt]
                      \\ pop_assum mp_tac \\ rw [] \\ fs [])
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert
      \\ fs[inter_insert_ODD_adjust_set_alt]
      \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
      \\ match_mp_tac memory_rel_rearrange
      \\ simp [SF DNF_ss]
      \\ rpt strip_tac
      \\ drule_all MEM_join_env_cut_env \\ fs [])
    \\ strip_tac \\ gvs []
    \\ Cases_on ‘has_been_eval’ \\ gvs []
    >- (
      TOP_CASE_TAC \\ gvs []
      >- (
        simp [wordSemTheory.evaluate_def, wordSemTheory.word_exp_def,
              wordSemTheory.get_var_def, lookup_insert,
              wordSemTheory.the_words_def, word_op_def,
              wordSemTheory.mem_load_def, wordSemTheory.set_var_def,
              wordSemTheory.get_vars_def]
        \\ simp [flush_state_def, wordSemTheory.flush_state_def]
        \\ gvs [state_rel_thm]
        \\ conj_tac
        >-
         (irule backendPropsTheory.option_le_trans
          \\ first_x_assum $ irule_at Any
          \\ Cases_on ‘s.locals_size’ \\ fs []
          \\ Cases_on ‘stack_size t.stack’ \\ fs [])
        \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
        \\ match_mp_tac memory_rel_rearrange
        \\ simp [SF DNF_ss, join_env_def])
      \\ TOP_CASE_TAC \\ gvs []
      \\ simp [wordSemTheory.evaluate_def, wordSemTheory.word_exp_def,
               wordSemTheory.get_var_def, lookup_insert,
               wordSemTheory.the_words_def, word_op_def,
               wordSemTheory.mem_load_def]
      \\ gvs [wordSemTheory.get_var_def, wordSemTheory.set_var_def]
      \\ Cases_on ‘cut_env r s.locals’ \\ gvs []
      \\ conj_tac >- (simp [set_var_def])
      \\ simp [wordSemTheory.set_var_def, set_var_def]
      \\ fs [state_rel_thm,lookup_insert,adjust_var_11]
      \\ conj_tac >- (rw [] \\ gvs [cut_env_def,lookup_inter_alt]
                      \\ pop_assum mp_tac \\ rw [] \\ fs [])
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert
      \\ fs[inter_insert_ODD_adjust_set_alt]
      \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
      \\ match_mp_tac memory_rel_rearrange
      \\ simp [SF DNF_ss]
      \\ rpt strip_tac
      \\ drule_all MEM_join_env_cut_env \\ fs [])
    \\ rpt strip_tac \\ gvs []
    \\ IF_CASES_TAC \\ gvs []
    >- gvs [asmTheory.word_cmp_def, dimword_def, good_dimindex_def]
    \\ simp [wordSemTheory.word_exp_def, wordSemTheory.get_var_def,
             lookup_insert, wordSemTheory.the_words_def, word_op_def,
             wordSemTheory.mem_load_def, wordSemTheory.set_var_def]
    \\ Cases_on ‘find_code (SOME loc) [RefPtr F n'; a] s.code
                           s.stack_frame_sizes’ \\ gvs []
    \\ Cases_on ‘x''’ \\ gvs []
    \\ Cases_on ‘r’ \\ gvs []
    \\ Cases_on ‘ret’ \\ gvs []
    >- (
      simp [wordSemTheory.evaluate_def, wordSemTheory.get_vars_def,
            wordSemTheory.get_var_def, lookup_insert]
      \\ once_rewrite_tac [GSYM wordSemTheory.get_var_def] \\ gvs []
      \\ simp [wordSemTheory.bad_dest_args_def]
      \\ gvs [find_code_def]
      \\ Cases_on ‘lookup loc s.code’ \\ gvs []
      \\ Cases_on ‘x''’ \\ gvs []
      \\ simp [wordSemTheory.find_code_def]
      \\ qpat_x_assum ‘code_rel _ _ _’ assume_tac
      \\ gvs [code_rel_def]
      \\ first_x_assum drule \\ strip_tac \\ gvs []
      \\ simp [wordSemTheory.add_ret_loc_def]
      \\ IF_CASES_TAC \\ gvs []
      >- simp [wordSemTheory.flush_state_def]
      \\ gvs [CaseEq"prod",CaseEq"option",PULL_EXISTS]
      \\ qmatch_goalsub_abbrev_tac ‘(FST _, t8)’
      \\ last_x_assum $ qspecl_then
        [‘c’,‘loc’,‘2’,‘l1’,‘l2’,‘t8’,‘locs’] mp_tac
      \\ impl_tac >-
       (fs [state_rel_thm,dataSemTheory.call_env_def,
            dataSemTheory.dec_clock_def,wordSemTheory.dec_clock_def,
            wordSemTheory.call_env_def,dec_clock_def,Abbr‘t8’]
        \\ conj_tac >- EVAL_TAC
        \\ conj_tac >-
         (simp [fromList_def,fromList2_def]
          \\ simp [lookup_insert]
          \\ rw [] \\ gvs [])
        \\ conj_tac >-
         (Cases_on ‘t.stack_max’ \\ gvs []
          \\ Cases_on ‘stack_size t.stack’ \\ gvs []
          \\ Cases_on ‘lookup loc s.stack_frame_sizes’ \\ gvs [] )
        \\ conj_tac >-
         (imp_res_tac stack_rel_IMP_size_of_stack
          \\ Cases_on ‘size_of_stack s.stack’ \\ gvs []
          \\ Cases_on ‘lookup loc s.stack_frame_sizes’ \\ gvs []
          \\ Cases_on ‘s.stack_max’ \\ gvs []
          \\ Cases_on ‘t.stack_max’ \\ gvs [])
        \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
        \\ match_mp_tac memory_rel_rearrange
        \\ simp [SF DNF_ss]
        \\ EVAL_TAC
        \\ simp [SF DNF_ss])
      \\ strip_tac \\ fs []
      \\ Cases_on ‘res1’ \\ gvs []
      \\ IF_CASES_TAC
      >- (rename [‘bad_fun_return (SOME tt)’] \\ Cases_on ‘tt’ \\ fs [])
      \\ simp []
      \\ strip_tac \\ gvs []
      \\ CASE_TAC \\ gvs []
      \\ CASE_TAC \\ gvs []
      \\ ‘(jump_exc t8 = NONE ⇔ jump_exc t = NONE) ∧
          mk_loc (jump_exc t8) = mk_loc (jump_exc t) : 'a word_loc’ by
       (gvs
         [wordSemTheory.jump_exc_def,Abbr‘t8’,wordSemTheory.call_env_def
         ,
             wordSemTheory.dec_clock_def,mk_loc_def]
        \\ IF_CASES_TAC \\ simp []
        \\ rpt (CASE_TAC \\ gvs [mk_loc_def]))
      \\ gvs []
      \\ Cases_on ‘jump_exc t’ \\ gvs [wordSemTheory.set_var_def])
    \\ TOP_CASE_TAC \\ gvs []
    \\ simp [wordSemTheory.evaluate_def, wordSemTheory.get_vars_def,
             wordSemTheory.get_var_def, lookup_insert]
    \\ once_rewrite_tac [GSYM wordSemTheory.get_var_def] \\ gvs []
    \\ simp [wordSemTheory.bad_dest_args_def]
    \\ gvs [find_code_def]
    \\ Cases_on ‘lookup loc s.code’ \\ gvs []
    \\ Cases_on ‘x''’ \\ gvs []
    \\ simp [wordSemTheory.find_code_def]
    \\ qpat_x_assum ‘code_rel _ _ _’ assume_tac
    \\ gvs [code_rel_def]
    \\ first_x_assum drule \\ strip_tac \\ gvs []
    \\ simp [wordSemTheory.add_ret_loc_def, domain_adjust_sets]
    \\ Cases_on ‘cut_env r s.locals’ \\ gvs []
    \\ simp [cut_envs_adjust_sets_insert_ODD]
    \\ pop_assum mp_tac
    \\ simp [cut_env_def, SUBSET_DEF, domain_lookup] \\ strip_tac \\ gvs
      []
    \\ simp [adjust_sets_def, adjust_set_def,
      wordSemTheory.cut_envs_def,
             wordSemTheory.cut_names_def, domain_lookup,
               domain_fromAList]
    \\ simp [SUBSET_DEF, MEM_MAP, PULL_EXISTS]
    \\ reverse $ IF_CASES_TAC \\ gvs []
    >- (
      spose_not_then kall_tac
      \\ pairarg_tac \\ gvs [MEM_toAList, domain_lookup]
      \\ first_x_assum $ drule_then assume_tac \\ gvs []
      \\ first_x_assum $ qspec_then ‘n’ assume_tac \\ gvs []
      \\ Cases_on ‘lookup (adjust_var n) t.locals’ \\ gvs [])
    \\ IF_CASES_TAC \\ gvs []
    >-
     (fs [dataSemTheory.call_env_def,wordSemTheory.call_env_def]
      \\ imp_res_tac stack_rel_IMP_size_of_stack
      \\ fs [dataSemTheory.push_env_def,wordSemTheory.push_env_def,
             wordSemTheory.env_to_list_def,dataSemTheory.dec_clock_def,
             wordSemTheory.stack_size_def,
             wordSemTheory.stack_size_frame_def,
             dataSemTheory.size_of_stack_def,
             dataSemTheory.size_of_stack_frame_def]
      \\ fs [GSYM wordSemTheory.stack_size_def,
             GSYM wordSemTheory.stack_size_frame_def,
             GSYM dataSemTheory.size_of_stack_def,
             GSYM dataSemTheory.size_of_stack_frame_def]
      \\ Cases_on ‘s.stack_max’ \\ fs []
      \\ Cases_on ‘t.stack_max’ \\ fs []
      \\ Cases_on ‘s.locals_size’ \\ fs []
      \\ Cases_on ‘lookup loc s.stack_frame_sizes’ \\ fs []
      \\ Cases_on ‘size_of_stack s.stack’ \\ fs [])
    \\ gvs [CaseEq"prod",CaseEq"option",PULL_EXISTS]
    \\ qmatch_goalsub_abbrev_tac ‘(FST _, t8)’
    \\ last_x_assum
         $ qspecl_then [‘c’,‘loc’,‘2’,‘n’,‘l’,‘t8’,‘(l1,l2)::locs’]
           mp_tac
    \\ impl_tac >-
     (conj_tac >- (CCONTR_TAC \\ gvs [])
      \\ reverse conj_tac >- gvs [Abbr‘t8’]
      \\ simp [Abbr‘t8’]
      \\ irule state_rel_call_env_push \\ simp []
      \\ conj_tac >-
      (fs [cut_envs_adjust_sets_ODD]
       \\ qexists_tac ‘r’
       \\ ‘cut_env r s.locals = SOME (inter s.locals r)’ by
         simp [dataSemTheory.cut_env_def,SUBSET_DEF,domain_lookup]
       \\ drule_all state_rel_cut_env_IMP_cut_env
       \\ strip_tac \\ simp []
       \\ drule cut_env_IMP_cut_envs \\ strip_tac
       \\ gvs [wordSemTheory.cut_envs_def,CaseEq"option"]
       \\ gvs [wordSemTheory.cut_names_def,CaseEq"option"]
       \\ simp [adjust_sets_def,adjust_set_def])
      \\ fs [state_rel_thm,lookup_insert]
      \\ fs[inter_insert_ODD_adjust_set_alt]
      \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
      \\ match_mp_tac memory_rel_rearrange
      \\ simp [SF DNF_ss])
    \\ strip_tac \\ fs []
    >- (Cases_on ‘res1’
    >- (gvs [] \\ gvs [AllCaseEqs()])
    \\ gvs []
    \\ rename [‘word_res = NotEnoughSpace ⇒ _’]
    \\ Cases_on ‘word_res = NotEnoughSpace’ \\ gvs []
    >- (gvs
      [AllCaseEqs(),dataSemTheory.set_var_def
      ,dataSemTheory.pop_env_def])
    \\ rename [‘dataSem$evaluate _ = (SOME data_res,s2)’]
    \\ reverse $ Cases_on ‘data_res’
    >- (reverse (Cases_on `e`) \\ full_simp_tac(srw_ss())[] \\
      srw_tac[][]
      \\ full_simp_tac(srw_ss())[jump_exc_call_env,jump_exc_dec_clock,
                                 jump_exc_push_env_NONE,Abbr‘t8’
                                   ,jump_exc_locals]
      THEN1 (every_case_tac \\ fs[])
      \\ Cases_on ‘jump_exc t = NONE’ \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[jump_exc_push_env_NONE_simp
        ,jump_exc_locals]
      \\ ‘LENGTH locs = LENGTH s.stack’ by
         (fs[state_rel_def] \\ imp_res_tac LIST_REL_LENGTH \\ fs[]) \\
           full_simp_tac(srw_ss())[]
      \\ ‘LENGTH s1.stack < LENGTH locs’ by(imp_res_tac
        eval_exc_stack_shorter \\ fs[])
      \\ imp_res_tac LASTN_TL \\ full_simp_tac(srw_ss())[]
      \\ fs [jump_exc_push_env_NONE]
      \\ fs [wordSemTheory.set_var_def])
    >- (gvs [AllCaseEqs()]
    \\ gvs [LENGTH_EQ_NUM_compute]
    \\ Cases_on ‘pop_env s2’ \\ gvs []
    \\ qrefinel [‘_’,‘NONE’] \\ simp [AllCaseEqs(),PULL_EXISTS]
    \\ rename [‘set_var ret_var _ _’]
    \\ drule_all state_rel_pop_env_set_var_IMP
    \\ disch_then $ qspec_then ‘ret_var’ strip_assume_tac
    \\ gvs
      [wordSemTheory.set_vars_def,alist_insert_def
      ,wordSemTheory.set_var_def,
            dataSemTheory.set_var_def]
    \\ reverse $ rpt strip_tac
    >- (imp_res_tac dataPropsTheory.pop_env_const
        \\ imp_res_tac wordPropsTheory.pop_env_const
        \\ gvs [])
    \\ simp [Abbr‘t8’]
    \\ drule evaluate_IMP_domain_EQ \\ fs [])))
QED
*)

(* HOL4 ML code, not ported:
Resume data_compile_correct[Tick]:
  (fs [comp_def,dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ `t.clock = s.clock` by fs [state_rel_def] \\ fs [] \\ srw_tac[][]
    \\ fs [] \\ srw_tac[][] \\ rpt (pop_assum mp_tac)
    \\ fs [wordSemTheory.jump_exc_def,wordSemTheory.dec_clock_def] \\
      srw_tac[][]
    \\ fs
      [state_rel_def,dataSemTheory.dec_clock_def
      ,wordSemTheory.dec_clock_def]
    \\ fs
      [call_env_def,wordSemTheory.call_env_def
      ,wordSemTheory.flush_state_def,flush_state_def]
    \\ asm_exists_tac \\ fs [])
QED
*)

(* HOL4 ML code, not ported:
Resume data_compile_correct[MakeSpace]:
  (fs [comp_def,dataSemTheory.evaluate_def,
        wordSemTheory.evaluate_def,
        GSYM alloc_size_def,LET_DEF,wordSemTheory.word_exp_def,
        wordLangTheory.word_op_def,wordSemTheory.get_var_imm_def]
    \\ `?end next hlen curr.
          FLOOKUP t.store CurrHeap = SOME (Word curr) /\
          FLOOKUP t.store HeapLength = SOME (Word hlen) /\
          FLOOKUP t.store TriggerGC = SOME (Word end) /\
          FLOOKUP t.store NextFree = SOME (Word next)` by
            fs [state_rel_def,heap_in_memory_store_def]
    \\ fs [wordSemTheory.the_words_def,wordSemTheory.get_store_def]
    \\ reverse CASE_TAC THEN1
     (every_case_tac \\ fs [] \\ srw_tac[][]
      \\ fs [wordSemTheory.set_var_def,state_rel_insert_1,add_space_def]
      THEN1 fs [state_rel_def]
      \\ match_mp_tac state_rel_cut_env \\ reverse (srw_tac[][])
      \\ fs [] \\ match_mp_tac has_space_state_rel
      \\ fs [wordSemTheory.has_space_def,WORD_LO,NOT_LESS,
             asmTheory.word_cmp_def,wordSemTheory.get_store_def])
    \\ reverse (Cases_on `c.call_empty_ffi`)
    THEN1
     (fs
       [SilentFFI_def,wordSemTheory.evaluate_def,list_Seq_def
       ,CaseEq"option"]
      \\ srw_tac[][]
      \\ fs
        [add_space_def,wordSemTheory.word_exp_def,alloc_locals_insert_1,
           wordSemTheory.get_var_def,wordSemTheory.set_var_def]
      \\ pairarg_tac \\ gvs []
      \\ drule alloc_lemma
      \\ rpt (disch_then drule)
      \\ rw [] \\ fs [] \\ rfs [GSYM NOT_LESS,cut_locals_def]
      \\ qpat_x_assum `state_rel c l1 l2 _ _ _ _` mp_tac \\ simp
        [state_rel_def]
      \\ Cases_on ‘no_thunks_in_refs s.refs’ \\ gvs [])
    \\ fs
      [SilentFFI_def,wordSemTheory.evaluate_def,list_Seq_def,eq_eval]
    \\ fs
      [wordSemTheory.evaluate_def,SilentFFI_def
      ,wordSemTheory.word_exp_def,
           wordSemTheory.set_var_def,EVAL ``read_bytearray a 0 m``,
           wordSemTheory.get_store_def,
           ffiTheory.call_FFI_def,EVAL ``write_bytearray a [] m dm b``,
           wordSemTheory.get_var_def,lookup_insert
             ,cut_names_adjust_set_insert_ODD]
    \\ Cases_on `dataSem$cut_env names s.locals` \\ gvs []
    \\ drule_all cut_env_IMP_cut_env \\ strip_tac \\ fs []
    \\ gvs [cut_env_adjust_sets_insert_ODD]
    \\ pairarg_tac \\ fs []
    \\ drule_all state_rel_cut_env_cut_env \\ strip_tac
    \\ rename [‘_ = (res1,s1)’]
    \\ ‘state_rel c l1 l2 (s with locals := x)
          (t with <|locals := y; fp_regs := FEMPTY|>) NONE locs’ by
         (drule state_rel_with_fp_regs \\ simp [])
    \\ ‘alloc (alloc_size k) (adjust_sets names)
          (t with <|locals := y; fp_regs := FEMPTY|>) = (res1,s1)’ by
      (‘t with
           <|locals := insert 1 (Word (alloc_size k)) y; fp_regs :=
             FEMPTY;
             memory := t.memory; ffi := t.ffi|> =
        (t with <|locals := y; fp_regs := FEMPTY|>) with
          locals := insert 1 (Word (alloc_size k))
                      (t with <|locals := y; fp_regs :=
                        FEMPTY|>).locals’ by
          gvs [wordSemTheory.state_component_equality]
       \\ full_simp_tac std_ss [alloc_locals_insert_1])
    \\ `dataSem$cut_env names x = SOME x` by
      (fs [dataSemTheory.cut_env_def] \\ rveq \\ fs
        [lookup_inter_alt,domain_inter])
    \\ drule_then (drule_at $ Pos last) alloc_lemma
    \\ simp []
    \\ strip_tac \\ Cases_on `res1 = SOME NotEnoughSpace`
    >- (fs [] \\ rveq \\ rfs [add_space_def,cut_locals_def] \\ fs [GSYM
      NOT_LESS] \\ gvs []
        \\ Cases_on ‘no_thunks_in_refs s.refs’ \\ fs [])
    \\ `?end next hlen curr.
          FLOOKUP s1.store CurrHeap = SOME (Word curr) /\
          FLOOKUP s1.store HeapLength = SOME (Word hlen) /\
          FLOOKUP s1.store TriggerGC = SOME (Word end) /\
          FLOOKUP s1.store NextFree = SOME (Word next)` by
            fs [state_rel_def,heap_in_memory_store_def]
    \\ rfs [lookup_insert,EVAL ``read_bytearray a 0 m``,
            cut_env_adjust_sets_insert_ODD]
    \\ rveq \\ rfs [add_space_def,cut_locals_def] \\ fs [GSYM NOT_LESS]
    \\ drule cut_env_IMP_cut_env \\ simp []
    \\ disch_then drule \\ strip_tac \\ gvs []
    \\ gvs [EVAL ``write_bytearray a [] m dm b``]
    \\ drule state_rel_cut_env_cut_env \\ simp []
    \\ disch_then drule \\ strip_tac \\ gvs []
    \\ gvs [state_rel_thm])
QED
*)

(* HOL4 ML code, not ported:
Resume data_compile_correct[Raise]:
  (fs [comp_def,dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var n s.locals` \\ fs [] \\ srw_tac[][]
    \\ fs [] \\ imp_res_tac state_rel_get_var_IMP \\ fs []
    \\ Cases_on `jump_exc s` \\ fs [] \\ srw_tac[][]
    \\ imp_res_tac state_rel_jump_exc \\ fs []
    \\ srw_tac[][] \\ fs [] \\ srw_tac[][mk_loc_def]
    \\ first_x_assum (qspec_then `0` mp_tac) \\ fs [state_rel_def]
    \\ fs [set_var_def])
QED
*)

(* HOL4 ML code, not ported:
Resume data_compile_correct[Return]:
  (fs [comp_def,dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_vars ns s.locals` \\ fs [] \\ srw_tac[][]
    \\ `get_var 0 t = SOME (Loc l1 l2)` by
          fs [state_rel_def,wordSemTheory.get_var_def]
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs [wordSemTheory.get_vars_def]
    \\ fs [state_rel_def,wordSemTheory.call_env_def,lookup_def,LET_THM,
           dataSemTheory.call_env_def,fromList_def,EVAL ``join_env LN
             []``,
           EVAL ``toAList (inter (fromList2 []) (insert 0 () LN))``,
           wordSemTheory.flush_state_def,flush_state_def]
    \\ conj_tac THEN1
     (qpat_x_assum `option_le _ t.stack_max` mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ Cases_on `stack_size t.stack`
      \\ Cases_on `t.locals_size`
      \\ Cases_on `t.stack_max`
      \\ fs [] \\ rveq \\ fs [])
    \\ asm_exists_tac \\ fs []
    \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule word_ml_inv_get_vars_IMP
    \\ match_mp_tac word_ml_inv_rearrange
    \\ fs [] \\ srw_tac[][] \\ fs[EVAL ``join_env LN []``])
QED
*)

(* HOL4 ML code, not ported:
Resume data_compile_correct[Seq]:
  (once_rewrite_tac [data_to_wordTheory.comp_def] \\ fs []
    \\ Cases_on `comp c n l c1` \\ fs [LET_DEF]
    \\ Cases_on `comp c n r c2` \\ fs [LET_DEF]
    \\ fs [dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `evaluate (c1,s)` \\ fs [LET_DEF]
    \\ `q'' <> SOME (Rerr (Rabort Rtype_error))` by
         (Cases_on `q'' = NONE` \\ fs []) \\ fs []
    \\ fs[GSYM AND_IMP_INTRO]
    \\ first_x_assum (drule_all_then assume_tac)
    \\ fs[]
    \\ pop_assum (mp_tac o Q.SPECL [`n`,`l`])
    \\ rpt strip_tac \\ rfs []
    \\ reverse (Cases_on `q'' = NONE`) \\ fs []
    THEN1 (fs [] \\ rpt strip_tac \\ fs []
           \\ srw_tac[][] \\ Cases_on `q''` \\ fs []
           \\ Cases_on `x` \\ fs [] \\ Cases_on `e`
           \\ fs [] \\ PURE_TOP_CASE_TAC >> fs[])
    \\ Cases_on `res1 = SOME NotEnoughSpace` \\ fs []
    THEN1 (fs []
      \\ imp_res_tac dataPropsTheory.evaluate_io_events_mono \\ fs []
      \\ imp_res_tac IS_PREFIX_TRANS \\ fs []
      \\ rw [] \\ fs []
      \\ rpt strip_tac \\ imp_res_tac evaluate_safe_for_space_mono
      \\ imp_res_tac evaluate_option_le_stack_max
      \\ match_mp_tac backendPropsTheory.option_le_trans
      \\ asm_exists_tac \\ fs [])
    \\ srw_tac[][]
    \\ qpat_x_assum `state_rel c l1 l2 _ _ NONE locs` (fn th =>
             first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
    \\ imp_res_tac wordSemTheory.evaluate_clock \\ fs[]
    \\ strip_tac \\ pop_assum (mp_tac o Q.SPECL [`n`,`r`])
    \\ rpt strip_tac \\ rfs [] \\ rpt strip_tac \\ fs []
    \\ BasicProvers.EVERY_CASE_TAC \\ fs [mk_loc_def] \\ fs []
    \\ imp_res_tac evaluate_mk_loc_EQ \\ fs []
    \\ imp_res_tac eval_NONE_IMP_jump_exc_NONE_EQ
    \\ fs [jump_exc_inc_clock_EQ_NONE] \\ metis_tac [])
QED
*)

(* HOL4 ML code, not ported:
Resume data_compile_correct[If]:
  (once_rewrite_tac [data_to_wordTheory.comp_def] \\ fs []
    \\ fs [LET_DEF]
    \\ pairarg_tac \\ fs [] \\ rename1 `comp c n4 l c1 = (q4,l4)`
    \\ pairarg_tac \\ fs [] \\ rename1 `comp c _ _ _ = (q5,l5)`
    \\ fs [dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var n s.locals` \\ fs []
    \\ fs [] \\ imp_res_tac state_rel_get_var_IMP
    \\ fs [wordSemTheory.get_var_imm_def]
    \\ imp_res_tac get_var_isT_OR_isF
    \\ fs[GSYM AND_IMP_INTRO]
    \\ Cases_on `isBool T x` \\ fs [] THEN1
     (simp [asmTheory.word_cmp_def]
      \\ qpat_x_assum `state_rel c l1 l2 s t NONE locs` (fn th =>
                 first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
      \\ strip_tac \\ pop_assum (qspecl_then [`n4`,`l`] mp_tac)
      \\ rpt strip_tac \\ rfs [])
    \\ Cases_on `isBool F x` \\ fs [] THEN1
     (simp [asmTheory.word_cmp_def]
      \\ qpat_x_assum `state_rel c l1 l2 s t NONE locs` (fn th =>
                 first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
      \\ strip_tac \\ pop_assum (qspecl_then [`n4`,`l4`] mp_tac)
      \\ rpt strip_tac \\ rfs []))
QED
*)

(* HOL4 ML code, not ported:
Resume data_compile_correct[Call]:
  (rename [‘evaluate (Call ret dest args handler,s)’]
  \\ `t.clock = s.clock` by fs [state_rel_def]
  \\ once_rewrite_tac [data_to_wordTheory.comp_def] \\ fs []
  \\ Cases_on `ret`
  \\ fs [dataSemTheory.evaluate_def,wordSemTheory.evaluate_def,
         wordSemTheory.add_ret_loc_def,get_vars_inc_clock
           ,flush_state_def,
         wordSemTheory.flush_state_def]
  >- (fs [wordSemTheory.bad_dest_args_def]
    \\ Cases_on `get_vars args s.locals` \\ fs []
    \\ imp_res_tac state_rel_0_get_vars_IMP \\ fs []
    \\ Cases_on `find_code dest x s.code s.stack_frame_sizes` \\ fs []
    \\ rename1 `_ = SOME z` \\ PairCases_on `z` \\ fs []
    \\ Cases_on `handler` \\ fs []
    \\ `t.clock = s.clock /\
        t.stack_size = s.stack_frame_sizes` by fs [state_rel_def]
    \\ fs []
    \\ drule find_code_thm \\ rpt (disch_then drule)
    \\ srw_tac[][] \\ fs []
    \\ Cases_on `s.clock = 0` \\ fs[] \\ srw_tac[][] \\ fs[]
    THEN1
      (fs[flush_state_def,wordSemTheory.flush_state_def,state_rel_def])
    THEN1
      (fs[flush_state_def,wordSemTheory.flush_state_def,state_rel_def])
    \\ fs [CaseEq"option",pair_case_eq] \\ rveq
    \\ fs [] \\ res_tac
    \\ pop_assum kall_tac
    \\ pop_assum mp_tac \\ impl_tac
    >- fs[wordSemTheory.call_env_def,wordSemTheory.dec_clock_def]
    \\ disch_then (qspecl_then [`n1`,`n2`] strip_assume_tac) \\ fs[]
    \\ `t.clock <> 0` by fs [state_rel_def]
    \\ Cases_on `res1` \\ fs [] \\ srw_tac[][] \\ fs[]
    >- (rename [‘bad_fun_return (SOME tt)’] \\ Cases_on ‘tt’ \\ fs [])
    \\ every_case_tac \\ fs [mk_loc_def]
    \\ fs [wordSemTheory.jump_exc_def,wordSemTheory.call_env_def,
           wordSemTheory.dec_clock_def]
    \\ BasicProvers.EVERY_CASE_TAC \\ fs [mk_loc_def])
  \\ Cases_on `x` \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ `domain (FST (adjust_sets r)) <> {}` by
    fs[adjust_sets_def,domain_fromAList]
*)
  (* dataSem now has the up-front `ALL_DISTINCT q` guard (matching
     wordSem), so
     `res <> Rtype_error` forces `ALL_DISTINCT q`. *)
(* HOL4 ML code, not ported:
  \\ `ALL_DISTINCT q` by (Cases_on `ALL_DISTINCT q` \\ fs[] \\
    gvs[AllCaseEqs()])
  \\ `ALL_DISTINCT (MAP adjust_var q)` by (irule ALL_DISTINCT_MAP_INJ \\
    simp[adjust_var_11])
  \\ Cases_on `handler` \\
    full_simp_tac(srw_ss())[wordSemTheory.evaluate_def]
  \\ Cases_on `get_vars args s.locals` \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac state_rel_get_vars_IMP \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[wordSemTheory.add_ret_loc_def]
  >- (Cases_on `find_code dest x s.code s.stack_frame_sizes` \\ fs[]
    \\ rename1 `_ = SOME x9` \\ PairCases_on `x9` \\
      full_simp_tac(srw_ss())[]
    \\ rename1 `_ = SOME (actual_args,called_prog,ss)`
    \\ imp_res_tac data_find_code
    \\ `¬bad_dest_args dest (MAP adjust_var args)` by
      (full_simp_tac(srw_ss())[wordSemTheory.bad_dest_args_def]>>
      imp_res_tac get_vars_IMP_LENGTH>>
      metis_tac[LENGTH_NIL])
    \\ Q.MATCH_ASSUM_RENAME_TAC
         `find_code dest xs s.code s.stack_frame_sizes =SOME
           (ys,prog,ss)`
    \\ Cases_on `dataSem$cut_env r s.locals` \\
      full_simp_tac(srw_ss())[]
    \\ imp_res_tac cut_env_IMP_cut_env \\ full_simp_tac(srw_ss())[] \\
      srw_tac[][]
    \\ drule cut_env_IMP_cut_envs \\ strip_tac \\ gvs []
    \\ `t.clock = s.clock /\
        t.stack_size = s.stack_frame_sizes` by
          full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[]
    \\ rpt_drule find_code_thm_ret
    \\ disch_then (qspecl_then [`n`,`l`] strip_assume_tac) \\ fs []
    \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\
      srw_tac[][]
    THEN1
     (fs [state_rel_def] \\ qpat_x_assum `option_le _ _` mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ fs [wordSemTheory.flush_state_def,wordSemTheory.call_env_def,
             wordPropsTheory.push_env_dec_clock_stack])
    THEN1 (fs[call_env_def,wordSemTheory.call_env_def,state_rel_def])
    >- (Cases_on `evaluate (prog,call_env ys ss (push_env x F (dec_clock
      s)))`
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `q'` \\
      full_simp_tac(srw_ss())[]
    \\ Cases_on `x' = Rerr (Rabort Rtype_error)` \\
      full_simp_tac(srw_ss())[]
    \\ res_tac (* inst ind hyp *)
    \\ pop_assum kall_tac
    \\ pop_assum mp_tac \\ impl_tac >-
      fs[wordSemTheory.call_env_def,wordSemTheory.push_env_def,
         wordSemTheory.env_to_list_def,wordSemTheory.dec_clock_def]
    \\ disch_then (qspecl_then [`n1`,`n2`] strip_assume_tac)
    \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `res1 = SOME NotEnoughSpace` \\
      full_simp_tac(srw_ss())[]
    >- (sg `s1.ffi = r'.ffi` \\ full_simp_tac(srw_ss())[]
      \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ full_simp_tac(srw_ss())[set_var_def,dataSemTheory.set_vars_def]
      \\ imp_res_tac dataPropsTheory.pop_env_const \\
        full_simp_tac(srw_ss())[]
      \\ imp_res_tac wordPropsTheory.pop_env_const \\
        full_simp_tac(srw_ss())[]
      \\ imp_res_tac evaluate_safe_for_space_mono
      \\ fs
        [pop_env_def,CaseEq"list",CaseEq"stack"
        ,dataSemTheory.set_vars_def]
      \\ rveq \\ fs [])
    \\ reverse (Cases_on `x'` \\ full_simp_tac(srw_ss())[])
    >- (reverse (Cases_on `e`) \\ full_simp_tac(srw_ss())[] \\
      srw_tac[][]
      \\ full_simp_tac(srw_ss())[jump_exc_call_env,jump_exc_dec_clock
        ,jump_exc_push_env_NONE]
      THEN1 (every_case_tac \\ fs[])
      \\ Cases_on `jump_exc t = NONE` \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[jump_exc_push_env_NONE_simp]
      \\ `LENGTH locs = LENGTH s.stack` by
         (fs[state_rel_def] \\ imp_res_tac LIST_REL_LENGTH \\ fs[]) \\
           full_simp_tac(srw_ss())[]
      \\ `LENGTH r'.stack < LENGTH locs` by(imp_res_tac
        eval_exc_stack_shorter \\ fs[])
      \\ imp_res_tac LASTN_TL \\ full_simp_tac(srw_ss())[]
      \\ fs [jump_exc_push_env_NONE])
    >- (Cases_on `LENGTH a = LENGTH q /\ ALL_DISTINCT q` \\ gvs []
    \\ Cases_on `pop_env r'` \\ gvs []
    \\ `LENGTH a = LENGTH ws' /\ LENGTH q = LENGTH a` by simp[]
    \\ drule_all state_rel_pop_env_set_vars_IMP \\ strip_tac
    \\ rename1 `pop_env t1 = SOME t2`
    \\ imp_res_tac evaluate_IMP_domain_EQ
    \\ imp_res_tac dataPropsTheory.pop_env_const
    \\ imp_res_tac wordPropsTheory.pop_env_const
    \\ qexists_tac `set_vars (MAP adjust_var q) ws' t2` \\ qexists_tac
      `NONE`
    \\ fs [wordSemTheory.set_vars_def, dataSemTheory.set_vars_def])))
  >- ((* with handler *)
  PairCases_on `x` \\ full_simp_tac(srw_ss())[]
  \\ `?prog1 h1. comp c n (l + 2) x1 = (prog1,h1)` by METIS_TAC [PAIR]
  \\ fs[wordSemTheory.evaluate_def,wordSemTheory.add_ret_loc_def]
  \\ Cases_on `find_code dest x' s.code s.stack_frame_sizes` \\ fs[] \\
    PairCases_on `x` \\ fs[]
  \\ imp_res_tac data_find_code
  \\ `¬bad_dest_args dest (MAP adjust_var args)` by
      (full_simp_tac(srw_ss())[wordSemTheory.bad_dest_args_def]>>
      imp_res_tac get_vars_IMP_LENGTH>>
      metis_tac[LENGTH_NIL])
  \\ Q.MATCH_ASSUM_RENAME_TAC
       `find_code dest xs s.code s.stack_frame_sizes = SOME
         (ys,prog,ss)`
  \\ Cases_on `dataSem$cut_env r s.locals` \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac cut_env_IMP_cut_env \\ full_simp_tac(srw_ss())[] \\
    srw_tac[][]
  \\ drule cut_env_IMP_cut_envs \\ strip_tac \\ gvs []
  \\ rpt_drule find_code_thm_handler \\ fs []
  \\ disch_then (qspecl_then [`x0`,`n`,`prog1`,`n`,`l`]
    strip_assume_tac) \\ fs []
  \\ `t.stack_size = s.stack_frame_sizes` by fs [state_rel_def]
  \\ full_simp_tac std_ss []
  \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  THEN1
   (fs [state_rel_def] \\ qpat_x_assum `option_le _ _` mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ fs [wordSemTheory.flush_state_def,wordSemTheory.call_env_def,
           wordPropsTheory.push_env_dec_clock_stack])
  THEN1 (fs[call_env_def,wordSemTheory.call_env_def,state_rel_def])
  \\ Cases_on `evaluate (prog,call_env ys ss (push_env x T (dec_clock
    s)))`
  \\ full_simp_tac(srw_ss())[] \\ Cases_on `q'` \\
    full_simp_tac(srw_ss())[]
  \\ Cases_on `x' = Rerr (Rabort Rtype_error)` \\
    full_simp_tac(srw_ss())[]
  \\ `t.clock = s.clock /\
      t.stack_size = s.stack_frame_sizes` by
        full_simp_tac(srw_ss())[state_rel_def]
  \\ res_tac (* inst ind hyp *)
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac \\ impl_tac >-
      fs[wordSemTheory.call_env_def,wordSemTheory.push_env_def,
         wordSemTheory.env_to_list_def,wordSemTheory.dec_clock_def]
  \\ disch_then (qspecl_then [`n1`,`n2`] strip_assume_tac) \\ fs[]
  \\ Cases_on `res1 = SOME NotEnoughSpace` \\ full_simp_tac(srw_ss())[]
  >- (full_simp_tac(srw_ss())[]
    \\ qsuff_tac `r'.ffi.io_events ≼ s1.ffi.io_events /\ option_le
      r'.stack_max s1.stack_max`
    THEN1
     (strip_tac \\ imp_res_tac IS_PREFIX_TRANS
      \\ imp_res_tac backendPropsTheory.option_le_trans
      \\ full_simp_tac(srw_ss())[] \\ rpt strip_tac \\ fs []
      \\ fs [CaseEq"option",pair_case_eq,pop_env_def,
             CaseEq"semanticPrimitives$result",
             CaseEq"semanticPrimitives$error_result",
             CaseEq"list",CaseEq"stack"] \\ rveq
      \\ fs [set_var_def,dataSemTheory.set_vars_def]
      \\ imp_res_tac evaluate_safe_for_space_mono \\ fs []
      \\ every_case_tac \\ gvs [dataSemTheory.set_vars_def]
      \\ imp_res_tac dataPropsTheory.pop_env_const \\ gvs [])
    \\ every_case_tac \\ fs []
    \\ imp_res_tac dataPropsTheory.evaluate_io_events_mono
    \\ imp_res_tac dataPropsTheory.evaluate_option_le_stack_max
    \\ imp_res_tac dataPropsTheory.pop_env_const
    \\ gvs [dataSemTheory.set_var_def,dataSemTheory.set_vars_def,
            pop_env_def,CaseEq"list",CaseEq"stack"]
    \\ rfs [] \\ fs []
    \\ imp_res_tac IS_PREFIX_TRANS
    \\ imp_res_tac backendPropsTheory.option_le_trans \\ fs [])
  \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[]
  >- (Cases_on `LENGTH a = LENGTH q /\ ALL_DISTINCT q` \\ gvs []
    \\ Cases_on `pop_env r'` \\ gvs []
    \\ `LENGTH a = LENGTH ws' /\ LENGTH q = LENGTH a` by simp[]
    \\ drule_all state_rel_pop_env_set_vars_IMP \\ strip_tac
    \\ rename1 `pop_env t1 = SOME t2`
    \\ imp_res_tac evaluate_IMP_domain_EQ
    \\ imp_res_tac dataPropsTheory.pop_env_const
    \\ imp_res_tac wordPropsTheory.pop_env_const
    \\ qexists_tac `set_vars (MAP adjust_var q) ws' t2` \\ qexists_tac
      `NONE`
    \\ fs [wordSemTheory.set_vars_def, dataSemTheory.set_vars_def])
  \\ reverse (Cases_on `e`) \\ full_simp_tac(srw_ss())[]
  THEN1 (full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ every_case_tac \\
    fs[])
  \\ full_simp_tac(srw_ss())[mk_loc_jump_exc]
  \\ imp_res_tac evaluate_IMP_domain_EQ_Exc \\ full_simp_tac(srw_ss())[]
  \\ qpat_x_assum `!x y z.bbb` kall_tac
  \\ full_simp_tac(srw_ss())[jump_exc_push_env_NONE_simp
    ,jump_exc_push_env_SOME]
  \\ imp_res_tac eval_push_env_T_Raise_IMP_stack_length
  \\ `LENGTH s.stack = LENGTH locs` by
       (full_simp_tac(srw_ss())[state_rel_def]
        \\ imp_res_tac LIST_REL_LENGTH \\ fs[]) \\ fs []
  \\ full_simp_tac(srw_ss())[LASTN_ADD1] \\ srw_tac[][]
  \\ qpat_x_assum `_ ==> _` mp_tac
  \\ impl_tac THEN1
   (simp [wordSemTheory.jump_exc_def,wordSemTheory.call_env_def,
          wordSemTheory.push_env_def,wordSemTheory.dec_clock_def]
    \\ pairarg_tac \\ fs [LASTN_ADD1])
  \\ strip_tac \\ rveq
  \\ first_x_assum (qspec_then `x0` assume_tac)
  \\ res_tac (* inst ind hyp *)
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac \\ impl_tac >-
    (imp_res_tac wordSemTheory.evaluate_clock>>
    fs[wordSemTheory.set_var_def,wordSemTheory.call_env_def
      ,wordSemTheory.push_env_def,
       wordSemTheory.env_to_list_def,wordSemTheory.dec_clock_def])
  \\ disch_then (qspecl_then [`n`,`l+2`] strip_assume_tac) \\ rfs []
  \\ `jump_exc (set_var (adjust_var x0) w t1) = jump_exc t1` by
        fs[wordSemTheory.set_var_def,wordSemTheory.jump_exc_def]
  \\ full_simp_tac(srw_ss())[] \\ rpt strip_tac \\
    full_simp_tac(srw_ss())[]
  \\ imp_res_tac evaluate_IMP_domain_EQ_Exc \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `res` \\ full_simp_tac(srw_ss())[]
  \\ rpt (CASE_TAC \\ full_simp_tac(srw_ss())[])
  \\ imp_res_tac mk_loc_eq_push_env_exc_Exception \\
    full_simp_tac(srw_ss())[]
  \\ imp_res_tac eval_push_env_SOME_exc_IMP_s_key_eq
  \\ imp_res_tac s_key_eq_handler_eq_IMP
  \\ full_simp_tac(srw_ss())[jump_exc_inc_clock_EQ_NONE] \\ metis_tac
    []))
QED
*)

(* HOL4 ML code, not ported:
Finalise data_compile_correct;
*)

let state_rel_ext_def = cake_define
  `state_rel_ext c l1 l2 s u <=>
     (?t l.
       word_bignumProof_state_rel c l1 l2 s t NONE [] /\
       domain (?_code t) = domain l /\ wordSem_state_termdep
       t > 1 /\
       (?tt kk aa co. ?_compile_oracle
          u =
            (I ## MAP (\p. full_compile_single tt kk aa co (p,NONE)))
              o ?_compile_oracle
              t /\ ?_compile
          t = (\conf progs. ?_compile u conf
            (MAP (\p. full_compile_single tt kk aa co (p,NONE))
              progs))) /\
       (!n v. lookup n (?_code t) = SOME v ==>
              (?t' k' a' c' col.
              lookup n l = SOME (SND (full_compile_single t' k' a' c'
                ((n,v),col))))) /\
       u = ?_compile_oracle_fupd (K (?_compile_oracle u))
         (?_compile_fupd (K (?_compile u))
         (wordSem_state_termdep_fupd (K 0) (?_code_fupd (K l) t))))`;;

(* observational semantics preservation *)

let get_limits_def = cake_define
  `get_limits c (t:('a,'c,'ffi)wordSem_state) =
     mk_? (?_stack_limit t) (w2n (theWord (FAPPLY
       (wordSem_state_store t) HeapLength)) DIV (dimindex (:'a) DIV
       8)) (data_to_word_config_len_size c) (dimindex (:'a) = 64)
       (?_has_fp_ops c) (data_to_word_config_has_fp_tern c)`;;

(* HOL4 ML code, not ported:
val _ = (max_print_depth := 15);
*)

(* HOL4 ML code, not ported:
val extract_labels_def = wordConvsTheory.extract_labels_def;
*)

(* TODO: goes away on inlineenc branch *)

(* HOL4 ML code, not ported:
fun cases_on_op q = Cases_on q >|
  map (MAP_EVERY Cases_on)
      [[`n`], [`m`], [`i`], [`w`], [`b`], [`g`], [`m`], [], [`t`]];
*)

(* no ShareInst in the compiled program *)

(***)

(* HOL4 ML code, not ported:
fun cases_on_op q = Cases_on q >|
  map (MAP_EVERY Cases_on)
      [[`n`], [`m`], [`i`], [`w`], [`b`], [`g`], [`m`], [], [`t`]];
*)

(*
inst_ok_less_def
*)

(* HOL4 overload (expanded in the port):
     data_get_code_labels = dataProps$get_code_labels *)
(* HOL4 overload (expanded in the port):
     data_good_code_labels = dataProps$good_code_labels *)

(* semi-slow... *)

(* slow... *)

(* HOL4 ML code, not ported:
val th = EVAL``MAP FST (stubs (:'a) c)``;
*)

(* TODO: move somewhere better *)
let stubs_fst_def = cake_define
  `stubs_fst = (rconc th)`;;

(* The incremental version ONLY does data_to_word
  TODO: MAP FST stubs is independent of the data conf,
  not sure if generality is needed
*)
