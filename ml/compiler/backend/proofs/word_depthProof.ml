(* ======================================================== *)
(*  word_depthProof: ported from HOL4's
    compiler/backend/proofs/word_depthProofScript.sml  *)
(* ======================================================== *)

(*
  Proves correctness of the max_depth applied to the call graph of a
  wordLang program as produced by the word_depth$call_graph function.
*)

needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_depth.ml";;

(* HOL4 ML code, not ported:
Resume max_depth_call_graph_lemma[Call]:
  rpt gen_tac
  \\ Cases_on `call_graph funs n ns (size funs2)
                  (Call ret dest args handler) = Unknown`
  THEN1 (simp [max_depth_def] \\ simp [OPTION_MAP2_DEF])
  \\ pop_assum mp_tac
  \\ rewrite_tac [call_graph_def]
  \\ TOP_CASE_TAC \\ simp []
  \\ IF_CASES_TAC THEN1
     (fs [] \\ rename [`MEM name ns`] \\ rveq
      \\ simp
        [evaluate_def,CaseEq"option",CaseEq"bool",pair_case_eq
        ,find_code_def]
      \\ Cases_on `res = SOME Error` \\ asm_rewrite_tac []
      \\ simp_tac std_ss [PULL_EXISTS]
      \\ rpt gen_tac \\ strip_tac \\ rveq \\ fs []
      \\ fs [flush_state_def,find_code_def]
      \\ first_x_assum (qspecl_then [`funs`,`name`,`ns`,`funs2`] mp_tac)
      \\ impl_tac THEN1 fs [call_env_def]
      \\ rveq \\ fs []
      \\ fs [subspt_lookup] \\ res_tac \\ fs []
      \\ fs [call_env_def,max_depth_def] \\ rveq \\ fs []
      \\ fs [backendPropsTheory.option_map2_max_add]
      \\ fs [subspt_lookup] \\ res_tac \\ fs [] \\ rveq \\ fs []
      \\ `option_le (lookup n s.stack_size)
           (max_depth_graphs s.stack_size ns ns funs funs2)` by
       (match_mp_tac backendPropsTheory.option_le_trans
        \\ qexists_tac `max_depth_graphs s.stack_size [n] ns funs funs2`
        \\ `?y. lookup n funs2 = SOME y` by
               fs [subspt_lookup,SUBSET_DEF,domain_lookup]
        \\ PairCases_on `y` \\ fs []
        \\ reverse conj_tac THEN1 (match_mp_tac MEM_max_depth_graphs \\
          fs [])
        \\ fs [max_depth_graphs_def,option_le_X_MAX_X])
      \\ `?a body. lookup name funs2 = SOME (a, body)` by
       (fs [SUBSET_DEF,domain_lookup] \\ rw [] \\ res_tac \\ fs []
        \\ rename [`_ = SOME vv`] \\ PairCases_on `vv` \\ fs [])
      \\ fs [subspt_lookup] \\ res_tac \\ fs [] \\ rveq \\ fs []
      \\ `option_le
           (OPTION_MAP2 MAX (lookup name s.stack_size)
              (max_depth s.stack_size (call_graph funs name ns (size
                funs2) body)))
           (max_depth_graphs s.stack_size ns ns funs funs2)` by
       (match_mp_tac backendPropsTheory.option_le_trans
        \\ qexists_tac `max_depth_graphs s.stack_size [name] ns funs
          funs2`
        \\ reverse conj_tac THEN1 (match_mp_tac MEM_max_depth_graphs \\
          fs [])
        \\ fs [max_depth_graphs_def])
      \\ qmatch_assum_abbrev_tac `option_le (_ _ x1) x2`
      \\ Cases_on `x2` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\
        fs [])
      \\ Cases_on `x1` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\
        fs [])
      \\ Cases_on `lookup name s.stack_size` THEN1 (fs [OPTION_MAP2_DEF]
        \\ rpt strip_tac \\ fs [])
      \\ Cases_on `lookup n s.stack_size` THEN1 (fs [OPTION_MAP2_DEF] \\
        rpt strip_tac \\ fs [])
      \\ Cases_on `s.stack_max` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
        strip_tac \\ fs [])
      \\ Cases_on `stack_size s.stack` THEN1 (fs [OPTION_MAP2_DEF] \\
        rpt strip_tac \\ fs [])
      \\ Cases_on `s'.stack_max` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
        strip_tac \\ fs [])
      \\ fs [] \\ rpt strip_tac \\ fs [])
  \\ TOP_CASE_TAC \\ simp []
  \\ TOP_CASE_TAC \\ simp []
  \\ rename [`lookup name funs = SOME (a,body)`]
  \\ qpat_x_assum `~_:bool` mp_tac
  \\ TOP_CASE_TAC \\ simp []
  THEN1 ((* TailCall *)
    strip_tac
    \\ Cases_on `set ns ⊆ domain funs2` \\ fs []
    \\ Cases_on `ALL_DISTINCT ns` \\ fs []
    \\ Cases_on `subspt funs funs2` \\ fs []
    \\ `LENGTH ns < size funs2` by
          (match_mp_tac LENGTH_LESS_size \\ asm_exists_tac \\ fs []
           \\ fs [subspt_lookup] \\ pop_assum drule \\ simp [])
    \\ asm_rewrite_tac []
    \\ simp_tac (srw_ss())
      [evaluate_def,CaseEq"option",CaseEq"bool",pair_case_eq
      ,find_code_def,PULL_EXISTS]
    \\ strip_tac \\ rpt gen_tac \\ strip_tac \\ gvs
      [flush_state_def,option_le_X_MAX_X,find_code_def]
    \\ first_x_assum (qspecl_then [`funs`,`name`,`name::ns`,`funs2`]
      mp_tac)
    \\ impl_tac THEN1
      (gvs [call_env_def,SUBSET_DEF,domain_lookup,subspt_lookup] \\
        metis_tac [])
    \\ strip_tac
    \\ imp_res_tac subspt_lookup
    \\ gvs
      [lookup_delete,max_depth_mk_Branch,max_depth_def,call_env_def,
            backendPropsTheory.option_map2_max_add
              ,OPTION_MAP2_MAX_ASSOC]
    \\ simp [AC OPTION_MAP2_MAX_ASSOC OPTION_MAP2_MAX_COMM]
    \\ fs [max_depth_graphs_def,lookup_delete]
    \\ imp_res_tac subspt_lookup \\ gvs []
    \\ Cases_on `(max_depth s.stack_size
         (call_graph funs name (name::ns) (size funs2) body))`
    THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs []) \\ simp []
    \\ `option_le
         (max_depth_graphs s.stack_size ns (name::ns) funs funs2)
         (max_depth_graphs s.stack_size ns ns funs funs2)` by
      (match_mp_tac option_le_max_depth_graphs \\ fs [] \\ rw [])
    \\ qmatch_assum_abbrev_tac `option_le x1 x2`
    \\ Cases_on `x2` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs
      [])
    \\ Cases_on `x1` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs
      [])
    \\ Cases_on `lookup name s.stack_size` THEN1 (fs [OPTION_MAP2_DEF]
      \\ rpt strip_tac \\ fs [])
    \\ Cases_on `s.stack_max` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
      strip_tac \\ fs [])
    \\ Cases_on `stack_size s.stack` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
      strip_tac \\ fs [])
    \\ Cases_on `s'.stack_max` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
      strip_tac \\ fs [])
    \\ fs [OPTION_MAP2_DEF,MAX_DEF] \\ rpt strip_tac \\ fs [])
*)
  (* non-tail-call case *)
(* HOL4 ML code, not ported:
  \\ PairCases_on `x` \\ simp []
  \\ TOP_CASE_TAC \\ simp []
  THEN1 ((* NoHandler *)
    simp [Once
      evaluate_def,CaseEq"option",CaseEq"bool",pair_case_eq
      ,find_code_def]
    \\ Cases_on `res = SOME Error` \\ simp [PULL_EXISTS]
    \\ rpt gen_tac \\ strip_tac \\ rveq
    THEN1
     (rpt(first_x_assum(qspec_then`ARB`kall_tac))
      \\ fs [flush_state_def,option_le_X_MAX_X] >>
      fs [call_env_def,push_env_def] \\ pairarg_tac \\ fs []
      \\ fs [stack_size_def,stack_size_frame_def]
      \\ fs [GSYM stack_size_def,max_depth_def,
             max_depth_mk_Branch]
      \\ Cases_on `lookup name s.stack_size` THEN1 (fs [OPTION_MAP2_DEF]
        \\ rpt strip_tac \\ fs [])
      \\ Cases_on `s.stack_max` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
        strip_tac \\ fs [])
      \\ Cases_on `lookup n s.stack_size` THEN1 (fs [OPTION_MAP2_DEF] \\
        rpt strip_tac \\ fs [])
      \\ Cases_on `stack_size s.stack` THEN1 (fs [OPTION_MAP2_DEF] \\
        rpt strip_tac \\ fs [])
      \\ Cases_on `max_depth s.stack_size
                    (call_graph (delete name funs) name [name] (size
                      funs2) body)`
      THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs [])
      \\ Cases_on `max_depth_graphs s.stack_size ns ns funs funs2`
      THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs [])
      \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size
        funs2) x3)`
      THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs [])
      \\ fs [] \\ rw [MAX_DEF])
    \\ rename [`_ = (SOME res,s2)`]
    \\ reverse (Cases_on `?x y. res = Result x y`)
    THEN1
     (`s1 = s2 /\ res <> Error` by (
        qpat_x_assum`_ = (_,s1)`mp_tac >>
        simp_tac(srw_ss())[CaseEq"result"] >>
        strip_tac >> rveq >> ntac 2 (pop_assum mp_tac) >>
        simp_tac(srw_ss())[] >>
        qpat_x_assum`x <> x`mp_tac >> simp_tac(srw_ss())[] ) >>
      rveq >>
      last_x_assum drule >> simp_tac(srw_ss())[find_code_def] >>
      last_x_assum drule >> simp_tac(srw_ss())[find_code_def] >>
      rpt(first_x_assum(qspec_then`ARB`kall_tac)) >>
      simp[] >>
      disch_then (qspecl_then [`delete name funs`,
           `name`,`[name]`,`funs2`] mp_tac)
      \\ fs [max_depth_def,max_depth_mk_Branch]
      \\ fs [find_code_def]
      \\ impl_tac THEN1 (fs [subspt_lookup,lookup_delete]
                         \\ fs [call_env_def,domain_lookup] \\ res_tac
                           \\ fs [])
      \\ fs [max_depth_graphs_def]
      \\ fs [push_env_def] \\ pairarg_tac \\ fs []
      \\ fs [dec_clock_def,call_env_def]
      \\ fs [subspt_lookup] \\ res_tac \\ fs []
      \\ fs [stack_size_def,stack_size_frame_def]
      \\ fs [GSYM stack_size_def,max_depth_def,
               max_depth_mk_Branch
                 ,backendPropsTheory.option_map2_max_add]
      \\ fs [subspt_lookup] \\ res_tac \\ fs [] \\ rveq \\ fs []
      \\ Cases_on `lookup name s.stack_size` THEN1 (fs [OPTION_MAP2_DEF]
        \\ rpt strip_tac \\ fs [])
      \\ Cases_on `lookup n s.stack_size` THEN1 (fs [OPTION_MAP2_DEF] \\
        rpt strip_tac \\ fs [])
      \\ Cases_on `max_depth s.stack_size (call_graph
                      (delete name funs) name [name] (size funs2) body)`
      THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs [])
      \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size
        funs2) x3)`
      THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs [])
      \\ Cases_on `max_depth_graphs s.stack_size ns ns funs funs2`
      THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs [])
      \\ `(res' = NONE \/ (?k. res' = SOME (Break k)) \/ (?k. res' =
        SOME (Continue k))) ==> s1.locals_size = s.locals_size` by
        (strip_tac \\ fs [CaseEq"wordSem$result"]) \\ fs []
      \\ Cases_on `stack_size s.stack` THEN1 (fs [OPTION_MAP2_DEF] \\
        rpt strip_tac \\ fs [])
      \\ Cases_on `s.stack_max` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
        strip_tac \\ fs [])
      \\ Cases_on `s1.stack_max` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
        strip_tac \\ fs [])
      \\ simp[]
      \\ qmatch_goalsub_abbrev_tac`xxxx ∧ _`
      \\ rpt strip_tac \\ gvs[])
    \\ pop_assum strip_assume_tac \\ rveq
    \\ qpat_x_assum`_ = (_,s1)`mp_tac
    \\ simp_tac(srw_ss())[]
    \\ IF_CASES_TAC
    >- (
      simp_tac(srw_ss())[]
      \\ strip_tac \\ rveq
      \\ simp_tac(srw_ss())[]
      \\ qpat_x_assum(`yx <> yx`)mp_tac
      \\ simp_tac(srw_ss())[] )
    \\ simp_tac(srw_ss())[CaseEq"option"]
    \\ strip_tac \\ rveq
    >- (  qpat_x_assum(`yx <> yx`)mp_tac \\ simp_tac std_ss [])
    \\ pop_assum mp_tac
    \\ simp_tac(srw_ss())[CaseEq"bool"]
    \\ reverse strip_tac \\ rveq
    >- (  qpat_x_assum(`yx <> yx`)mp_tac \\ simp_tac std_ss [])
    \\ rename [`evaluate (_,set_vars _ y s2) = (res3,s3)`]
    \\ last_x_assum $ drule_then drule
    \\ simp_tac(srw_ss())[find_code_def]
    \\ last_x_assum $ drule_then drule
    \\ simp_tac(srw_ss())[find_code_def]
    \\ qhdtm_x_assum`lookup`mp_tac
    \\ simp_tac(srw_ss())[] \\ strip_tac
    \\ disch_then $ funpow 4 drule_then drule
    \\ disch_then (qspecl_then [`delete name funs`,
         `name`,`[name]`,`funs2`] mp_tac)
    \\ impl_tac THEN1 (fs [subspt_lookup,lookup_delete,call_env_def]
                       \\ fs [domain_lookup] \\ metis_tac [])
    \\ last_x_assum $ drule_then drule
    \\ simp_tac(srw_ss())[find_code_def]
    \\ last_x_assum $ drule_then drule
    \\ simp[find_code_def]
    \\ disch_then (qspecl_then [`funs`,`n`,`ns`,`funs2`] mp_tac)
    \\ strip_tac
    \\ `lookup name funs2 = SOME (a,body) /\
        lookup name s.code = SOME (a,body)`
          by (fs [subspt_lookup,lookup_delete,call_env_def]
                       \\ fs [domain_lookup] \\ metis_tac [])
    \\ fs [max_depth_graphs_def]
    \\ simp [call_env_def,dec_clock_def]
    \\ rename [`pop_env s1 = SOME s2`]
    \\ `s1.stack_max = s2.stack_max` by (imp_res_tac pop_env_const \\ fs
      [])
    \\ fs
      [max_depth_def,max_depth_mk_Branch
      ,backendPropsTheory.option_map2_max_add]
    \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `lookup name s.stack_size` THEN1 (fs [OPTION_MAP2_DEF]
      \\ rpt strip_tac \\ fs [])
    \\ Cases_on `max_depth s.stack_size
            (call_graph (delete name funs) name [name] (size funs2)
              body)`
    THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs []) \\ fs []
    \\ Cases_on `s1.stack_size = s.stack_size` \\ fs []
    \\ `stack_size s2.stack = stack_size s.stack /\
        s2.locals_size = s.locals_size` by
     (qmatch_assum_abbrev_tac `evaluate (body,s8) = _`
      \\ qspecl_then [`body`,`s8`] mp_tac evaluate_stack_swap
      \\ fs [] \\ strip_tac \\ pop_assum kall_tac
      \\ fs [Abbr`s8`,call_env_def] \\ ntac 2 (pop_assum mp_tac)
      \\ fs [push_env_def] \\ pairarg_tac \\ fs []
      \\ Cases_on `s1.stack` \\ fs [s_key_eq_def]
      \\ Cases_on `h` \\ fs [s_key_eq_def]
      \\ Cases_on `o0` \\ fs [s_key_eq_def,s_frame_key_eq_def]
      \\ fs [pop_env_def] \\ rveq \\ fs []
      \\ rw [] \\ imp_res_tac s_key_eq_stack_size \\ fs [])
    \\ qpat_x_assum`_ ==> _`mp_tac
    \\ impl_tac THEN1
       (imp_res_tac evaluate_code_only_grows \\ fs [call_env_def]
        \\ imp_res_tac subspt_trans \\ imp_res_tac pop_env_const \\ fs
          []
        \\ fs [set_var_def]) \\ fs []
    \\ `s2.stack_size = s1.stack_size` by (imp_res_tac pop_env_const \\
      fs [])
    \\ fs []
    \\ Cases_on `max_depth_graphs s.stack_size ns ns funs funs2`
    THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs []) \\ fs []
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size
      funs2) x3)`
    THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs []) \\ fs []
    \\ strip_tac \\ strip_tac
    \\ reverse conj_tac
    >- ( strip_tac >> gvs[] )
    \\ match_mp_tac backendPropsTheory.option_le_trans
    \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ pop_assum mp_tac
    \\ fs [push_env_def] \\ pairarg_tac \\ fs []
    \\ fs [stack_size_def,stack_size_frame_def]
    \\ fs [GSYM stack_size_def]
    \\ Cases_on `lookup n s.stack_size` THEN1 (fs [OPTION_MAP2_DEF] \\
      rpt strip_tac \\ fs [])
    \\ Cases_on `stack_size s.stack` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
      strip_tac \\ fs [])
    \\ Cases_on `s.stack_max` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
      strip_tac \\ fs [])
    \\ Cases_on `s2.stack_max` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
      strip_tac \\ fs [])
    \\ fs [OPTION_MAP2_DEF])
  \\ rename [`Call _ _ _ (SOME h)`]
  \\ PairCases_on `h`
  \\ simp_tac (srw_ss())
    [evaluate_def,CaseEq"option",CaseEq"bool",pair_case_eq
    ,find_code_def]
  \\ Cases_on `res = SOME Error` \\ pop_assum mp_tac \\ simp_tac std_ss
    []
  \\ simp_tac std_ss [PULL_EXISTS] \\ asm_rewrite_tac []
  \\ rpt (disch_then assume_tac) \\ rpt gen_tac \\ strip_tac \\ rveq
  THEN1
   (fs [flush_state_def,option_le_X_MAX_X]
    \\ fs [call_env_def,push_env_def] \\ pairarg_tac \\ fs []
    \\ fs [stack_size_def,stack_size_frame_def]
    \\ fs [GSYM stack_size_def,max_depth_def,
           max_depth_mk_Branch]
    \\ Cases_on `lookup name s.stack_size` THEN1 (fs [OPTION_MAP2_DEF]
      \\ rpt strip_tac \\ fs [])
    \\ Cases_on `s.stack_max` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
      strip_tac \\ fs [])
    \\ Cases_on `lookup n s.stack_size` THEN1 (fs [OPTION_MAP2_DEF] \\
      rpt strip_tac \\ fs [])
    \\ Cases_on `stack_size s.stack` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
      strip_tac \\ fs [])
    \\ Cases_on `max_depth s.stack_size
                  (call_graph (delete name funs) name [name] (size
                    funs2) body)`
    THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs [])
    \\ Cases_on `max_depth_graphs s.stack_size ns ns funs funs2`
    THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs [])
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size
      funs2) x3)`
    THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs [])
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size
      funs2) h1)`
    THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs [])
    \\ fs [] \\ rw [MAX_DEF])
  \\ rename [`_ = (SOME res,s2)`]
  \\ reverse (Cases_on `(?x y. res = Result x y) \/ (∃x y. res =
    Exception x y)`)
  \\ pop_assum mp_tac \\ simp_tac std_ss []
  THEN1
   (strip_tac
    \\ `s1 = s2 /\ res <> Error` by
     (rpt (qpat_x_assum `!x y z. _` kall_tac)
      \\ fs [CaseEq"bool",CaseEq"option",CaseEq"wordSem$result"] \\ rfs
        [])
    \\ qpat_x_assum `!x y z. _` kall_tac
    \\ qpat_x_assum `!x y z. _` kall_tac
    \\ rveq \\ fs []
    \\ fs [max_depth_def,max_depth_mk_Branch]
    \\ fs [find_code_def]
    \\ first_x_assum (qspecl_then [`delete name funs`,
         `name`,`[name]`,`funs2`] mp_tac)
    \\ impl_tac THEN1 (fs [subspt_lookup,lookup_delete]
                       \\ fs [call_env_def,domain_lookup] \\ res_tac \\
                         fs [])
    \\ fs [max_depth_graphs_def]
    \\ fs [push_env_def] \\ pairarg_tac \\ fs []
    \\ fs [dec_clock_def,call_env_def]
    \\ fs [subspt_lookup] \\ res_tac \\ fs []
    \\ fs [stack_size_def,stack_size_frame_def]
    \\ fs [GSYM stack_size_def,max_depth_def,
             max_depth_mk_Branch,backendPropsTheory.option_map2_max_add]
    \\ fs [subspt_lookup] \\ res_tac \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `lookup name s.stack_size` THEN1 (fs [OPTION_MAP2_DEF]
      \\ rpt strip_tac \\ fs [])
    \\ Cases_on `lookup n s.stack_size` THEN1 (fs [OPTION_MAP2_DEF] \\
      rpt strip_tac \\ fs [])
    \\ Cases_on `max_depth s.stack_size (call_graph
                    (delete name funs) name [name] (size funs2) body)`
    THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs [])
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size
      funs2) x3)`
    THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs [])
    \\ Cases_on `max_depth_graphs s.stack_size ns ns funs funs2`
    THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs [])
    \\ `(res' = NONE \/ (?k. res' = SOME (Break k)) \/ (?k. res' = SOME
      (Continue k))) ==> s1.locals_size = s.locals_size` by
      (strip_tac \\ fs [CaseEq"wordSem$result"]) \\ fs []
    \\ Cases_on `stack_size s.stack` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
      strip_tac \\ fs [])
    \\ Cases_on `s.stack_max` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
      strip_tac \\ fs [])
    \\ Cases_on `s1.stack_max` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
      strip_tac \\ fs [])
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size
      funs2) h1)`
    THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs [])
    \\ fs []
      \\ qmatch_goalsub_abbrev_tac`xxxx ∧ _`
      \\ rpt strip_tac \\ gvs[])
  \\ strip_tac
  THEN1
   (qpat_x_assum `_ = (_,_)` mp_tac \\ asm_rewrite_tac []
    \\ simp_tac (srw_ss()) [CaseEq"bool",CaseEq"option"]
    \\ asm_simp_tac std_ss [] \\ strip_tac
    \\ rveq \\ fs [find_code_def]
    \\ rename [`evaluate (_,set_vars _ y s2) = (res3,s3)`]
    \\ last_x_assum (qspecl_then [`delete name funs`,
         `name`,`[name]`,`funs2`] mp_tac)
    \\ impl_tac THEN1 (fs [subspt_lookup,lookup_delete,call_env_def]
                       \\ fs [domain_lookup] \\ metis_tac [])
    \\ `lookup name funs2 = SOME (a,body) /\
        lookup name s.code = SOME (a,body)`
          by (fs [subspt_lookup,lookup_delete,call_env_def]
                       \\ fs [domain_lookup] \\ metis_tac [])
    \\ fs [max_depth_graphs_def]
    \\ simp [call_env_def,dec_clock_def]
    \\ rename [`pop_env s1 = SOME s2`]
    \\ `s1.stack_max = s2.stack_max` by (imp_res_tac pop_env_const \\ fs
      [])
    \\ fs
      [max_depth_def,max_depth_mk_Branch
      ,backendPropsTheory.option_map2_max_add]
    \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `lookup name s.stack_size` THEN1 (fs [OPTION_MAP2_DEF]
      \\ rpt strip_tac \\ fs [])
    \\ Cases_on `max_depth s.stack_size
            (call_graph (delete name funs) name [name] (size funs2)
              body)`
    THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs []) \\ fs []
    \\ Cases_on `s1.stack_size = s.stack_size` \\ fs []
    \\ last_x_assum (qspecl_then [`funs`,`n`,`ns`,`funs2`] mp_tac)
    \\ `stack_size s2.stack = stack_size s.stack /\
        s2.locals_size = s.locals_size` by
     (qmatch_assum_abbrev_tac `evaluate (body,s8) = _`
      \\ qspecl_then [`body`,`s8`] mp_tac evaluate_stack_swap
      \\ fs [] \\ strip_tac \\ pop_assum kall_tac
      \\ fs [Abbr`s8`,call_env_def] \\ ntac 2 (pop_assum mp_tac)
      \\ fs [push_env_def] \\ pairarg_tac \\ fs []
      \\ Cases_on `s1.stack` \\ fs [s_key_eq_def]
      \\ Cases_on `h` \\ fs [s_key_eq_def]
      \\ Cases_on `o0` \\ fs [s_key_eq_def,s_frame_key_eq_def]
      \\ fs [pop_env_def] \\ rveq \\ fs []
      \\ rw [] \\ imp_res_tac s_key_eq_stack_size \\ fs []
      \\ rw [] \\ fs [])
    \\ impl_tac THEN1
       (imp_res_tac evaluate_code_only_grows \\ fs [call_env_def]
        \\ imp_res_tac subspt_trans \\ imp_res_tac pop_env_const \\ fs
          []
        \\ fs [set_var_def]) \\ fs []
    \\ `s2.stack_size = s1.stack_size` by (imp_res_tac pop_env_const \\
      fs [])
    \\ fs []
    \\ Cases_on `max_depth_graphs s.stack_size ns ns funs funs2`
    THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs []) \\ fs []
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size
      funs2) x3)`
    THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs []) \\ fs []
    \\ ntac 2 strip_tac
    \\ reverse conj_tac
    >- ( strip_tac >> gvs[] )
    \\ match_mp_tac backendPropsTheory.option_le_trans
    \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ pop_assum mp_tac
    \\ fs [push_env_def] \\ pairarg_tac \\ fs []
    \\ fs [stack_size_def,stack_size_frame_def]
    \\ fs [GSYM stack_size_def]
    \\ Cases_on `lookup n s.stack_size` THEN1 (fs [OPTION_MAP2_DEF] \\
      rpt strip_tac \\ fs [])
    \\ Cases_on `stack_size s.stack` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
      strip_tac \\ fs [])
    \\ Cases_on `s.stack_max` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
      strip_tac \\ fs [])
    \\ Cases_on `s2.stack_max` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
      strip_tac \\ fs [])
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size
      funs2) h1)`
    THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs []) \\ fs [])
  THEN1 (* exception with handler *)
   (qpat_x_assum `_ = (_,_)` mp_tac \\ asm_rewrite_tac []
    \\ simp_tac (srw_ss()) [CaseEq"bool",CaseEq"option"]
    \\ asm_simp_tac std_ss [] \\ strip_tac
    \\ rveq \\ fs [find_code_def]
    \\ rename [`evaluate (_,set_var _ y s2) = (res3,s3)`]
    \\ last_x_assum (qspecl_then [`delete name funs`,
         `name`,`[name]`,`funs2`] mp_tac)
    \\ impl_tac THEN1 (fs [subspt_lookup,lookup_delete,call_env_def]
                       \\ fs [domain_lookup] \\ metis_tac [])
    \\ `lookup name funs2 = SOME (a,body) /\
        lookup name s.code = SOME (a,body)`
          by (fs [subspt_lookup,lookup_delete,call_env_def]
                       \\ fs [domain_lookup] \\ metis_tac [])
    \\ fs [max_depth_graphs_def]
    \\ simp [call_env_def,dec_clock_def]
    \\ rveq \\ fs []
    \\ fs
      [max_depth_def,max_depth_mk_Branch
      ,backendPropsTheory.option_map2_max_add]
    \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `lookup name s.stack_size` THEN1 (fs [OPTION_MAP2_DEF]
      \\ rpt strip_tac \\ fs [])
    \\ Cases_on `max_depth s.stack_size
            (call_graph (delete name funs) name [name] (size funs2)
              body)`
    THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs []) \\ fs []
    \\ Cases_on `s2.stack_size = s.stack_size` \\ fs []
    \\ last_x_assum (qspecl_then [`funs`,`n`,`ns`,`funs2`] mp_tac)
    \\ `stack_size s2.stack = stack_size s.stack /\
        s2.locals_size = s.locals_size` by
     (qmatch_assum_abbrev_tac `evaluate (body,s8) = _`
      \\ qspecl_then [`body`,`s8`] mp_tac evaluate_stack_swap
      \\ fs [] \\ strip_tac \\ pop_assum kall_tac
      \\ fs [Abbr`s8`,call_env_def] \\ ntac 2 (pop_assum mp_tac)
      \\ fs [push_env_def] \\ pairarg_tac \\ fs [miscTheory.LASTN_LEMMA]
      \\ rveq \\ fs [] \\ rw [] \\ imp_res_tac s_key_eq_stack_size \\ fs
        [])
    \\ impl_tac THEN1
       (imp_res_tac evaluate_code_only_grows \\ fs [call_env_def]
        \\ imp_res_tac subspt_trans \\ imp_res_tac pop_env_const \\ fs
          []
        \\ fs [set_var_def]) \\ fs []
    \\ Cases_on `max_depth_graphs s.stack_size ns ns funs funs2`
    THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs []) \\ fs []
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size
      funs2) x3)`
    THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs []) \\ fs []
    \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size
      funs2) h1)`
    THEN1 (fs [OPTION_MAP2_DEF] \\ rpt strip_tac \\ fs []) \\ fs []
    \\ ntac 2 strip_tac
    \\ reverse conj_tac >- (strip_tac \\ gvs[])
    \\ match_mp_tac backendPropsTheory.option_le_trans
    \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ pop_assum mp_tac
    \\ fs [push_env_def] \\ pairarg_tac \\ fs []
    \\ fs [stack_size_def,stack_size_frame_def]
    \\ fs [GSYM stack_size_def]
    \\ Cases_on `lookup n s.stack_size` THEN1 (fs [OPTION_MAP2_DEF] \\
      rpt strip_tac \\ fs [])
    \\ Cases_on `stack_size s.stack` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
      strip_tac \\ fs [])
    \\ Cases_on `s.stack_max` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
      strip_tac \\ fs [])
    \\ Cases_on `s2.stack_max` THEN1 (fs [OPTION_MAP2_DEF] \\ rpt
      strip_tac \\ fs [])
    \\ fs [OPTION_MAP2_DEF])
QED
*)


(* HOL4 ML code, not ported:
Resume max_depth_call_graph_lemma[Loop]:
  rpt gen_tac \\ simp [evaluate_def, call_graph_def]
  \\ TOP_CASE_TAC \\ fs [] THEN1 (rw [])
  \\ pairarg_tac \\ fs [] \\ strip_tac
  \\ qpat_x_assum `cut_state _ _ = _` mp_tac
  \\ simp [cut_state_def, AllCaseEqs()] \\ strip_tac \\ gvs []
  \\ `res' <> SOME Error` by
    (CCONTR_TAC \\ fs [cont_loop_def, exit_loop_def] \\ gvs
      [AllCaseEqs()])
  \\ first_x_assum (qspecl_then [`funs`,`n`,`ns`,`funs2`] mp_tac)
  \\ (impl_tac >- fs []) \\ strip_tac
  \\ Cases_on `max_depth s.stack_size (call_graph funs n ns (size funs2)
    c)`
  THEN1 (fs [OPTION_MAP2_DEF]
    \\ gvs [AllCaseEqs(), exit_loop_def, cut_state_def,
      flush_state_def])
  \\ Cases_on `max_depth_graphs s.stack_size ns ns funs funs2`
  THEN1 (fs [OPTION_MAP2_DEF]
    \\ gvs [AllCaseEqs(), exit_loop_def, cut_state_def,
      flush_state_def])
  \\ fs []
  \\ gvs [AllCaseEqs(), exit_loop_def, cut_state_def, flush_state_def,
          STOP_def, call_graph_def, dec_clock_def]
*)
  (* cont_loop case: res' = NONE or Continue 0 *)
(* HOL4 ML code, not ported:
  >- (qspecl_then [`c`,`s with locals := env`] mp_tac
    evaluate_stack_swap
     \\ fs [] \\ strip_tac \\ gvs [cont_loop_def]
     \\ Cases_on `res'` \\ gvs [cont_loop_def]
*)
     (* res' = NONE *)
(* HOL4 ML code, not ported:
     >- (first_x_assum (qspecl_then [`funs`,`n`,`ns`,`funs2`] mp_tac)
        \\ simp [STOP_def, call_graph_def, dec_clock_def]
        \\ (impl_tac >-
          (imp_res_tac evaluate_code_only_grows
           \\ fs [] \\ imp_res_tac subspt_trans \\ fs []))
        \\ strip_tac
        \\ imp_res_tac s_key_eq_stack_size \\ gvs []
        \\ conj_tac
        >- (irule option_le_trans \\ first_x_assum (irule_at Any)
            \\ fs [option_le_max, option_le_max_right,
              option_le_eq_eqns])
        >- fs [])
*)
     (* res' = SOME (Continue 0) *)
(* HOL4 ML code, not ported:
     >- (Cases_on `x''` \\ gvs [cont_loop_def]
        \\ first_x_assum (qspecl_then [`funs`,`n`,`ns`,`funs2`] mp_tac)
        \\ simp [STOP_def, call_graph_def, dec_clock_def]
        \\ (impl_tac >-
          (imp_res_tac evaluate_code_only_grows
           \\ fs [] \\ imp_res_tac subspt_trans \\ fs []))
        \\ strip_tac
        \\ imp_res_tac s_key_eq_stack_size \\ gvs []
        \\ conj_tac
        >- (irule option_le_trans \\ first_x_assum (irule_at Any)
            \\ fs [option_le_max, option_le_max_right,
              option_le_eq_eqns])
        >- fs []))
*)
  (* exit_loop case — Break 0 auto-solved by gvs with strengthened IH *)
(* HOL4 ML code, not ported:
  >- (Cases_on `res'` \\ gvs [cont_loop_def, exit_loop_def]
     \\ Cases_on `x''` \\ gvs [exit_loop_def])
QED
*)

(* HOL4 ML code, not ported:
Finalise max_depth_call_graph_lemma;
*)
