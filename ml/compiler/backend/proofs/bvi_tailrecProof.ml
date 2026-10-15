(* ======================================================== *)
(*  bvi_tailrecProof: ported from HOL4's
    compiler/backend/proofs/bvi_tailrecProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for bvi_tailrec
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi_tailrec.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/semanticPrimitives.ml";;

(* TODO

   - It should be possible to prove that we can replace the simplified
     compile_exp by the old compile_exp without touching the evaluate-
     theorem. Benefits:
       * Less code duplication
       * Can inline auxiliary calls more easily
*)

(* HOL4 ML code, not ported:
val find_code_def = bvlSemTheory.find_code_def;
val s = mk_var("s",
  type_of ``bviSem$evaluate`` |> strip_fun |> snd |> dest_prod |> snd
  |> type_subst [alpha|->``:num#'c``,beta|->``:'ffi``]);
*)

let ty_rel_def = cake_define
  `ty_rel = LIST_REL
     (\v t. (t = Int ==> (?k. v = Number k)) /\
            (t = List ==> (?ys. v_to_list v = SOME ys)))`;;

(* HOL4 ML code, not ported:
val v_ty_cases = TypeBase.case_eq_of ``:v_ty``
val assoc_op_cases = TypeBase.case_eq_of ``:assoc_op``
val case_eq_thms = CONJ v_ty_cases (CONJ assoc_op_cases
  bviPropsTheory.case_eq_thms)
*)

(* HOL4 ML code, not ported:
val s1 = mk_var("s",
  type_of ``bviSem$evaluate`` |> strip_fun |> snd |> dest_prod |> snd
  |> type_subst [alpha|->``:'c``,beta|->``:'ffi``]);
*)

(* HOL4 ML code, not ported:
fun cases_on_op q = Cases_on q
  >>> TRY_LT (SELECT_LT_THEN (Q.RENAME_TAC [‘WordOp w_’]) (Cases_on
    `w_`))
  >>> TRY_LT (SELECT_LT_THEN (Q.RENAME_TAC [‘BlockOp b_’]) (Cases_on
    `b_`))
  >>> TRY_LT (SELECT_LT_THEN (Q.RENAME_TAC [‘GlobOp g_’]) (Cases_on
    `g_`))
  >>> TRY_LT (SELECT_LT_THEN (Q.RENAME_TAC [‘MemOp m_’]) (Cases_on
    `m_`));
*)

let op_id_val_def = cake_define_list
  [`op_id_val Plus = Number (&0)`;
   `op_id_val Times = Number (&1)`;
   `op_id_val Append = Block nil_tag []`;
   `op_id_val Noop = Number (&6333)`];;

let env_rel_def = cake_define
  `bvi_tailrecProof_env_rel ty opt acc env1 env2 <=>
     isPREFIX env1 env2 /\
     (opt ==>
       LENGTH env1 = acc /\
       LENGTH env2 > acc /\
       (match ty with
         Int -> (?k. EL acc env2 = Number k) | List -> (?ys.
           v_to_list (EL acc env2) = SOME ys) | Any -> F))`;;
hol4_overload "env_rel" "bvi_tailrecProof_env_rel";;

(* HOL4 overload (expanded in the port):
     in_ns_2 = λn. n MOD bvl_to_bvi_namespaces = 2 *)

let code_rel_def = cake_define
  `bvi_tailrecProof_code_rel c1 c2 <=>
     (!loc arity exp op.
       lookup loc c1 = SOME (arity,exp) ==>
       (check_exp loc arity exp = NONE ==>
         lookup loc c2 = SOME (arity,exp)) /\
       (check_exp loc arity exp = SOME op ==>
         (?n.
           !exp_aux exp_opt.
           compile_exp loc n arity exp = SOME (exp_aux,exp_opt) ==>
             lookup loc c2 = SOME (arity,exp_aux) /\
             lookup n c2 = SOME (arity + 1,exp_opt))))`;;
hol4_overload "code_rel" "bvi_tailrecProof_code_rel";;

let optimized_code_def = cake_define
  `optimized_code loc arity exp n c op =
     (?exp_aux exp_opt.
         compile_exp loc n arity exp = SOME (exp_aux,exp_opt) /\
         check_exp loc arity exp = SOME op /\
         lookup loc c = SOME (arity,exp_aux) /\
         lookup n c = SOME (arity + 1,exp_opt))`;;

let free_names_def = cake_define
  `bvi_tailrecProof_free_names n (name:num) <=> (!k. ~(n +
  bvl_to_bvi_namespaces * k = name))`;;
hol4_overload "free_names" "bvi_tailrecProof_free_names";;

let namespace_rel_def = cake_define
  `bvi_tailrecProof_namespace_rel (c1:'a spt) (c2:'a spt) <=>
     (!n. n IN domain c2 /\ bvl_num_stubs <= n ==> (if (\n. n MOD
       bvl_to_bvi_namespaces = 2) n then ~(n IN domain c1) else n IN
       domain c1)) /\
     (!n. n IN domain c1 /\ bvl_num_stubs <= n ==> ~((\n. n MOD
       bvl_to_bvi_namespaces = 2) n)) /\
     (!n. n IN domain c2 /\ n < bvl_num_stubs ==> n IN domain c1)`;;
hol4_overload "namespace_rel" "bvi_tailrecProof_namespace_rel";;

let input_condition_def = cake_define
  `bvi_tailrecProof_input_condition next prog <=>
     EVERY (free_names next o FST) prog /\
    ALL_DISTINCT (MAP FST prog) /\
    EVERY ((~) o (\n. n MOD bvl_to_bvi_namespaces = 2) o FST) (FILTER
      ((<=) bvl_num_stubs o FST) prog) /\
    bvl_num_stubs <= next /\ (\n. n MOD bvl_to_bvi_namespaces = 2)
      next`;;
hol4_overload "input_condition" "bvi_tailrecProof_input_condition";;

let state_rel_def = cake_define
  `bvi_tailrecProof_state_rel s (t:('a,'ffi)bviSem_state) <=> ?_refs
     t = ?_refs s /\ ?_clock
     t = ?_clock s /\ bviSem_state_global
     t = bviSem_state_global s /\ ?_ffi
     t = ?_ffi s /\ ?_compile_oracle
     t = state_co compile_each (?_compile_oracle s) /\ ?_compile
     s = state_cc compile_each (?_compile t) /\
     code_rel (?_code s) (?_code t) /\
     namespace_rel (?_code s) (?_code t) /\
     (!n. let ((next,cfg),prog) = ?_compile_oracle s n in
             input_condition next prog) /\
     (!n. n IN domain (?_code t) /\ (\n. n MOD
       bvl_to_bvi_namespaces = 2) n ==> n < FST (FST
       (?_compile_oracle s 0)))`;;
hol4_overload "state_rel" "bvi_tailrecProof_state_rel";;

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tail[NIL]:
     (fs [evaluate_def] \\ rw [])
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tail[CONS]:
   (simp [evaluate_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ reverse PURE_TOP_CASE_TAC \\ fs []
    >-
     (rw []
      \\ first_assum (qspecl_then [`[h]`,`s`] mp_tac)
      \\ simp [bviTheory.exp_size_def]
      \\ rpt (disch_then drule) \\ fs []
      \\ rw [] \\ fs [])
    \\ qmatch_goalsub_rename_tac `evaluate (y::ys, env1, s2)`
    \\ first_assum (qspecl_then [`[h]`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ strip_tac
    \\ ntac 2 PURE_TOP_CASE_TAC \\ fs [] \\ rveq
    \\ strip_tac
    \\ first_assum (qspecl_then [`y::ys`,`s2`] mp_tac)
    \\ imp_res_tac evaluate_clock
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ impl_tac
    >- (strip_tac \\ fs [])
    \\ rw [] \\ fs []
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ metis_tac [])
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tail[Var]:
   (simp [evaluate_def]
    \\ `LENGTH env1 ≤ LENGTH env2` by metis_tac [env_rel_def,
      IS_PREFIX_LENGTH]
    \\ fs [env_rel_def, scan_expr_def] \\ rw []
    \\ fs [is_prefix_el])
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tail[Tick]:
   (simp [evaluate_def]
    \\ imp_res_tac state_rel_const
    \\ rw [] \\ fs []
    >- (fs [rewrite_def, evaluate_def, apply_op_def, ELIM_UNCURRY,
      env_rel_def])
    \\ first_x_assum (qspecl_then [`[x1]`,`dec_clock 1 s`] mp_tac)
    \\ impl_tac
    >- fs [bviTheory.exp_size_def, evaluate_clock, dec_clock_def]
    \\ `state_rel (dec_clock 1 s) (dec_clock 1 s')` by fs
      [dec_clock_def, state_rel_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ disch_then (qspec_then `loc` mp_tac) \\ rw [] \\ fs []
    \\ rw [rewrite_def] \\ fs []
    \\ first_x_assum drule \\ fs [scan_expr_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rw []
    \\ rfs [evaluate_def, apply_op_def, env_rel_def])
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tail[Raise]:
   (simp [scan_expr_def, evaluate_def, rewrite_def]
    \\ `env_rel ty F acc env1 env2` by fs [env_rel_def]
    \\ CASE_TAC \\ fs []
    \\ fs [pair_case_eq, case_eq_thms, case_elim_thms, bool_case_eq,
      PULL_EXISTS]
    \\ first_x_assum (qspecl_then [`[x1]`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ rw [] \\ rfs [])
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tail[Let]:
   (simp [evaluate_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ strip_tac
    \\ first_assum (qspecl_then [`xs`,`s`] mp_tac)
    \\ impl_tac >- simp [bviTheory.exp_size_def]
    \\ `env_rel ty F acc env1 env2` by fs [env_rel_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ impl_tac >- fs [pair_case_eq, case_eq_thms, case_elim_thms,
      bool_case_eq]
    \\ rw [] \\ fs []
    \\ reverse PURE_TOP_CASE_TAC \\ fs [] \\ rw []
    >- (fs [rewrite_def, scan_expr_def, ELIM_UNCURRY, evaluate_def,
            apply_op_def, env_rel_def])
    \\ rename1 `evaluate (xs,env1,s) = (Rval zz, s2)`
    \\ sg `env_rel ty opt (LENGTH zz + acc) (zz ++ env1) (zz ++ env2)`
    >-
     (fs [env_rel_def]
      \\ strip_tac
      \\ fs [IS_PREFIX_LENGTH, IS_PREFIX_APPEND, EL_LENGTH_APPEND,
        EL_APPEND1]
      \\ simp_tac std_ss [ADD_ASSOC] \\ fs []
      \\ rfs [case_eq_thms, case_elim_thms, bool_case_eq, v_ty_cases,
              EL_LENGTH_APPEND, EL_APPEND1, EL_APPEND2])
    \\ qabbrev_tac `ttt = scan_expr ts loc xs`
    \\ sg `ty_rel (zz ++ env1) (MAP (FST o SND) ttt ++
           (case LAST1 ttt of SOME z => FST z | NONE => ts))`
    >-
     (match_mp_tac ty_rel_APPEND
      \\ Q.ISPECL_THEN [`ts`,`loc`,`xs`,`env1`,`ttt`,`s`] mp_tac
        scan_expr_ty_rel
      \\ disch_then drule \\ fs [] \\ rw []
      \\ qunabbrev_tac `ttt`
      \\ CASE_TAC \\ fs []
      \\ imp_res_tac EVERY_LAST1 \\ fs [])
    \\ qunabbrev_tac `ttt`
    \\ imp_res_tac evaluate_clock
    \\ first_assum (qspecl_then [`[x1]`,`s2`] mp_tac)
    \\ impl_tac >- simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then `loc` mp_tac) \\ fs [] \\ rw []
    \\ imp_res_tac evaluate_code_mono \\ fs [] \\ rw [] \\ fs []
    \\ `lookup loc s2.code = lookup loc s.code` by fs [subspt_lookup]
    \\ `optimized_code loc arity exp n t'.code op`
      by fs [optimized_code_def, subspt_lookup]
    \\ first_x_assum (qspec_then `op` mp_tac) \\ fs []
    \\ disch_then drule \\ fs [scan_expr_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ `acc < LENGTH env2` by fs [env_rel_def]
    \\ qhdtm_x_assum `rewrite` mp_tac
    \\ rw [rewrite_def] \\ pairarg_tac \\ fs [] \\ rw []
    \\ `LENGTH xs = LENGTH zz` by metis_tac [evaluate_IMP_LENGTH] \\ rw
      []
    \\ fs [rewrite_def, evaluate_def, apply_op_def, EL_LENGTH_APPEND,
      EL_APPEND2]
    \\ rfs [])
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tail[If]:
   (simp [evaluate_def]
    \\ `env_rel ty F acc env1 env2` by fs [env_rel_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ reverse PURE_TOP_CASE_TAC \\ fs []
    >-
     (strip_tac \\ rveq \\ fs []
      \\ first_assum (qspecl_then [`[x1]`,`s`] mp_tac)
      \\ simp [bviTheory.exp_size_def]
      \\ rpt (disch_then drule) \\ fs [] \\ rw []
      \\ fs [rewrite_def, ELIM_UNCURRY, evaluate_def, apply_op_def,
        env_rel_def]
      \\ rw [] \\ fs [])
    \\ first_assum (qspecl_then [`[x1]`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ strip_tac
    \\ rename1 `evaluate ([x1],_,s) = (_,s2)`
    \\ reverse (Cases_on `opt`) \\ fs []
    >-
     (IF_CASES_TAC \\ fs []
      >-
       (strip_tac
        \\ first_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
        \\ imp_res_tac evaluate_clock
        \\ simp [bviTheory.exp_size_def]
        \\ rpt (disch_then drule) \\ fs [])
      \\ IF_CASES_TAC \\ fs []
      \\ strip_tac
      \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ imp_res_tac evaluate_clock
      \\ simp [bviTheory.exp_size_def]
      \\ rpt (disch_then drule) \\ fs [])
    \\ strip_tac
    \\ simp [LEFT_EXISTS_AND_THM, CONJ_ASSOC]
    \\ conj_tac
    >-
     (IF_CASES_TAC \\ fs []
      >-
       (first_x_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
        \\ imp_res_tac evaluate_clock \\ fs []
        \\ simp [bviTheory.exp_size_def]
        \\ rpt (disch_then drule) \\ fs [])
      \\ IF_CASES_TAC \\ fs []
      \\ first_x_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ imp_res_tac evaluate_clock \\ fs []
      \\ simp [bviTheory.exp_size_def]
      \\ rpt (disch_then drule) \\ fs [])
    \\ rw []
    \\ fs [rewrite_def, evaluate_def, scan_expr_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ sg `ty_rel env1 ti`
    >-
     (drule (GEN_ALL (ISPEC s (Q.GEN `s` (SPEC_ALL scan_expr_ty_rel))))
      \\ rpt (disch_then drule)
      \\ rw [])
    \\ rw []
    >- (* xt ∧ xe optimized *)
     (qpat_x_assum `_ = (r, t)` mp_tac
      \\ IF_CASES_TAC \\ fs []
      >-
       (strip_tac
        \\ first_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
        \\ impl_tac >- (imp_res_tac evaluate_clock \\ simp
          [bviTheory.exp_size_def])
        \\ disch_then drule
        \\ disch_then (qspec_then `T` drule)
        \\ rpt (disch_then drule)
        \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
        \\ sg `lookup loc s2.code = lookup loc s.code`
        >- (imp_res_tac evaluate_code_mono \\ fs [subspt_lookup])
        \\ sg `optimized_code loc arity exp n t'.code op`
        >-
         (imp_res_tac evaluate_code_mono
          \\ fs [optimized_code_def, subspt_lookup])
        \\ fs []
        \\ first_x_assum drule
        \\ disch_then drule \\ fs []
        \\ impl_tac
        >-
         (drule rewrite_scan_expr \\ fs []
          \\ CASE_TAC \\ fs []
          \\ qpat_x_assum `rewrite _ _ _ _ _ x3 = _` kall_tac
          \\ drule rewrite_scan_expr \\ fs []
          \\ CASE_TAC \\ fs [] \\ rveq
          \\ imp_res_tac scan_expr_op_type \\ fs []
          \\ Cases_on `ty1` \\ fs [decide_ty_def])
        \\ rw [evaluate_def, apply_op_def] \\ rw [] \\ rfs
          [env_rel_def])
      \\ IF_CASES_TAC \\ fs [] \\ rw []
      \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ impl_tac >- (imp_res_tac evaluate_clock \\ simp
        [bviTheory.exp_size_def])
      \\ sg `lookup loc s2.code = lookup loc s.code`
      >- (imp_res_tac evaluate_code_mono \\ fs [subspt_lookup])
      \\ sg `optimized_code loc arity exp n t'.code op`
      >-
       (imp_res_tac evaluate_code_mono
        \\ fs [optimized_code_def, subspt_lookup])
      \\ fs []
      \\ disch_then drule
      \\ disch_then (qspec_then `T` drule)
      \\ rpt (disch_then drule) \\ fs []
      \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
      \\ first_x_assum drule \\ fs []
      \\ impl_tac
      >-
       (drule rewrite_scan_expr \\ fs [] \\ CASE_TAC \\ fs []
        \\ qpat_x_assum `rewrite _ _ _ _ _ x3 = _` kall_tac
        \\ drule rewrite_scan_expr \\ fs [] \\ CASE_TAC \\ fs [] \\ rveq
        \\ imp_res_tac scan_expr_op_type \\ fs []
        \\ imp_res_tac scan_expr_not_Noop \\ fs []
        \\ metis_tac [decide_ty_imp, decide_ty_simp])
      \\ rw [evaluate_def, apply_op_def] \\ rw []
      \\ rfs [env_rel_def])
    >- (* xt optimized, xe untouched *)
     (qpat_x_assum `_ = (r, t)` mp_tac
      \\ IF_CASES_TAC \\ fs []
      >-
       (strip_tac
        \\ first_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
        \\ impl_tac >- (imp_res_tac evaluate_clock \\ simp
          [bviTheory.exp_size_def])
        \\ sg `lookup loc s2.code = lookup loc s.code`
        >- (imp_res_tac evaluate_code_mono \\ fs [subspt_lookup])
        \\ sg `optimized_code loc arity exp n t'.code op`
        >-
         (imp_res_tac evaluate_code_mono
          \\ fs [optimized_code_def, subspt_lookup])
        \\ disch_then drule
        \\ disch_then (qspec_then `T` drule)
        \\ rpt (disch_then drule)
        \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
        \\ first_x_assum drule \\ fs []
        \\ impl_tac
        >-
         (qpat_x_assum `rewrite _ _ _ _ _ x3 = _` kall_tac
          \\ drule rewrite_scan_expr \\ fs []
          \\ CASE_TAC \\ fs [] \\ rveq
          \\ metis_tac [decide_ty_imp, decide_ty_simp])
        \\ rw [evaluate_def, apply_op_def] \\ rw []
        \\ rfs [env_rel_def])
      \\ IF_CASES_TAC \\ fs [] \\ rw []
      \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ impl_tac >- (imp_res_tac evaluate_clock \\ simp
        [bviTheory.exp_size_def])
      \\ sg `lookup loc s2.code = lookup loc s.code`
      >- (imp_res_tac evaluate_code_mono \\ fs [subspt_lookup])
      \\ sg `optimized_code loc arity exp n t'.code op`
      >-
       (imp_res_tac evaluate_code_mono
        \\ fs [optimized_code_def, subspt_lookup])
      \\ rpt (disch_then drule) \\ fs []
      \\ `acc < LENGTH env2` by fs [env_rel_def]
      \\ rw [evaluate_def, apply_op_def] \\ rw [] \\ rfs [] \\ fs []
      \\ rpt (CASE_TAC \\ rw []) \\ fs []
      \\ imp_res_tac do_app_to_op_state \\ fs [])
    >- (* xe optimized, xt untouched *)
     (qpat_x_assum `_ = (r, t)` mp_tac
      \\ IF_CASES_TAC \\ fs []
      >-
       (strip_tac
        \\ first_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
        \\ impl_tac
        >- (imp_res_tac evaluate_clock \\ simp [bviTheory.exp_size_def])
        \\ rpt (disch_then drule) \\ fs []
        \\ `acc < LENGTH env2` by fs [env_rel_def]
        \\ rw [evaluate_def, apply_op_def] \\ rw []
        \\ rpt (CASE_TAC \\ rw []) \\ fs []
        \\ imp_res_tac do_app_to_op_state \\ fs [])
      \\ IF_CASES_TAC \\ fs [] \\ rw []
      \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ impl_tac >- (imp_res_tac evaluate_clock \\ simp
        [bviTheory.exp_size_def])
      \\ sg `lookup loc s2.code = lookup loc s.code`
      >- (imp_res_tac evaluate_code_mono \\ fs [subspt_lookup])
      \\ sg `optimized_code loc arity exp n t'.code op`
      >-
       (imp_res_tac evaluate_code_mono
        \\ fs [optimized_code_def, subspt_lookup])
      \\ disch_then drule
      \\ disch_then (qspec_then `T` drule)
      \\ rpt (disch_then drule)
      \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
      \\ first_x_assum drule \\ fs []
      \\ impl_tac
      >-
       (drule rewrite_scan_expr \\ fs []
        \\ qpat_x_assum `rewrite _ _ _ _ _ x3 = _` kall_tac
        \\ drule rewrite_scan_expr \\ fs []
        \\ rw [case_elim_thms]
        \\ drule scan_expr_op_type \\ fs [] \\ rw []
        \\ metis_tac [decide_ty_imp, decide_ty_simp])
      \\ rw [evaluate_def, apply_op_def] \\ rw []
      \\ rfs [env_rel_def])
    \\ qpat_x_assum `_ = (r, t)` mp_tac
    \\ IF_CASES_TAC \\ fs []
    >-
     (strip_tac
      \\ first_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
      \\ impl_tac
      >-
       (imp_res_tac evaluate_clock
        \\ simp [bviTheory.exp_size_def])
      \\ rpt (disch_then drule)
      \\ rw [evaluate_def, apply_op_def]
      \\ `acc < LENGTH env2` by fs[env_rel_def]
      \\ rw[]
      \\ CASE_TAC \\ rw[]
      \\ CASE_TAC \\ rw[]
      \\ CASE_TAC \\ rw[]
      \\ imp_res_tac do_app_to_op_state \\ fs[])
    \\ IF_CASES_TAC \\ fs [] \\ rw []
    \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
    \\ impl_tac >- (imp_res_tac evaluate_clock \\ simp
      [bviTheory.exp_size_def])
    \\ rpt (disch_then drule)
    \\ rw [evaluate_def, apply_op_def]
    \\ `acc < LENGTH env2` by fs[env_rel_def]
    \\ rpt (CASE_TAC \\ rw[]) \\ fs []
    \\ imp_res_tac do_app_to_op_state \\ fs[])
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tail[Op]:
   (simp [evaluate_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ strip_tac
    \\ simp [LEFT_EXISTS_AND_THM, CONJ_ASSOC]
    \\ conj_tac
    >-
     (gvs []
      \\ first_x_assum (qspecl_then [`xs`, `s`] mp_tac)
      \\ simp [bviTheory.exp_size_def]
      \\ `env_rel ty F acc env1 env2` by fs [env_rel_def]
      \\ rpt (disch_then drule) \\ fs []
      \\ impl_tac >- (strip_tac \\ fs [])
      \\ rw [] \\ fs []
      \\ Cases_on `op = Install`
      >- (
        reverse (fs[bvlPropsTheory.case_eq_thms] \\ rveq \\
          fs[do_app_def])
        >-
         (fs[do_install_def,bvlPropsTheory.case_eq_thms]
          \\ rveq \\ fs[]
          \\ rpt(pairarg_tac \\ fs[bvlPropsTheory.case_eq_thms])
          \\ rveq \\ fs[])
        \\ fs[do_install_def,bvlPropsTheory.case_eq_thms] \\ rveq \\
          fs[]
        \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[]
        \\ qhdtm_x_assum`state_rel`mp_tac
        \\ simp[state_rel_def, backendPropsTheory.state_co_def,
          backendPropsTheory.state_cc_def]
        \\ strip_tac \\ fs[]
        \\ rpt(pairarg_tac \\ fs[]) \\ rveq
        \\ rename1`compile_each next1 prog1 = (next2, prog2)`
        \\ `LENGTH prog1 ≤ LENGTH prog2` by
          metis_tac[compile_each_LENGTH,SND,GREATER_EQ]
        \\ `prog1 ≠ []` by (strip_tac \\ fs[])
        \\ `prog2 ≠ []` by (strip_tac \\ fs[])
        \\ fs[bvlPropsTheory.case_eq_thms,pair_case_eq,PULL_EXISTS]
        \\ fs[shift_seq_def]
        \\ qpat_x_assum`_ = FST _`(assume_tac o SYM) \\ fs[]
        \\ pairarg_tac \\ fs[]
        \\ pairarg_tac \\ fs[] \\ rveq
        \\ simp[RIGHT_EXISTS_AND_THM]
        \\ simp[LEFT_EXISTS_AND_THM]
        \\ qmatch_assum_rename_tac`code_rel src.code tgt.code`
        \\ qmatch_assum_abbrev_tac`compile_each next1 prog1 = (next2,
          prog2)`
        \\ `DISJOINT (domain src.code) (set (MAP FST prog1))` by
          simp[Abbr`prog1`]
        \\ `in_ns_2 next1` by (fs[input_condition_def] \\
          rpt(first_x_assum(qspec_then`0`mp_tac) \\ simp[]))
        \\ qpat_x_assum`compile_each next1 prog1 = _`assume_tac
        \\ drule (GEN_ALL compile_each_code_rel)
        \\ impl_tac
        >- (
          simp[Abbr`prog1`]
          \\ fs[input_condition_def]
          \\ rpt(first_x_assum(qspec_then`0`mp_tac) \\ simp[] ))
        \\ strip_tac
        \\ `∀n. in_ns_2 n ∧ bvl_num_stubs <= n ⇒ ¬MEM n (MAP FST prog1)`
        by (
          rw[] \\ fs[input_condition_def] \\
          qpat_x_assum`∀n. _ (src.compile_oracle
            n)`(qspec_then`0`mp_tac) \\
          simp[] \\
          strip_tac \\ fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,MEM_FILTER]
          \\ metis_tac[] )
        \\ conj_asm1_tac
        >- (
          fs[IN_DISJOINT]
          \\ qx_gen_tac`n`
          \\ spose_not_then strip_assume_tac
          \\ qpat_x_assum`∀n. _ (src.compile_oracle
            n)`(qspec_then`0`mp_tac)
          \\ simp[input_condition_def]
          \\ CCONTR_TAC \\ fs[]
          \\ Cases_on`in_ns_2 n ∧ bvl_num_stubs <= n`
          >- (
            `¬MEM n (MAP FST prog1)` by ( metis_tac[] )
            \\ drule (GEN_ALL compile_each_MEM)
            \\ disch_then drule \\ simp[]
            \\ CCONTR_TAC \\ fs[]
            \\ res_tac \\ fs[] )
          \\ qhdtm_x_assum`namespace_rel`mp_tac
          \\ simp[namespace_rel_def]
          \\ spose_not_then strip_assume_tac
          \\ `n ∈ domain src.code` by metis_tac[NOT_LESS]
          \\ drule (GEN_ALL compile_each_MEM)
          \\ disch_then drule
          \\ strip_tac >- metis_tac[]
          \\ fs[backend_commonTheory.bvl_to_bvi_namespaces_def]
          \\ res_tac \\ fs[])
        \\ qpat_x_assum`∀n. _ (src.compile_oracle
          n)`(qspec_then`0`mp_tac)
        \\ simp[] \\ strip_tac
        \\ conj_asm1_tac
        >- ( drule compile_each_ALL_DISTINCT \\ fs[input_condition_def]
          )
        \\ conj_tac >- (
          Cases_on`prog2` \\ fs[compile_each_def,Abbr`prog1`]
          \\ Cases_on`prog` \\ fs[compile_each_def,case_eq_thms]
          \\ pairarg_tac \\ fs[] \\ rw[] )
        \\ conj_asm1_tac
        >- (
          match_mp_tac code_rel_union
          \\ fs[domain_fromAList,DISJOINT_SYM]
          \\ gvs[Abbr‘prog1’])
        \\ `namespace_rel (fromAList prog1) (fromAList prog2)`
        by (
          match_mp_tac (GEN_ALL compile_each_namespace_rel)
          \\ asm_exists_tac \\ fs[input_condition_def])
        \\ conj_asm1_tac
        >- (
          match_mp_tac namespace_rel_union
          \\ fs[domain_fromAList,DISJOINT_SYM]
          \\ gs[Abbr‘prog1’])
        \\ simp[domain_union]
        \\ imp_res_tac compile_each_next_mono
        \\ rveq \\ rw[]
        >- ( res_tac \\ simp[] )
        \\ fs[domain_fromAList,input_condition_def]
        \\ drule (GEN_ALL compile_each_MEM)
        \\ disch_then drule
        \\ strip_tac \\ fs[]
        \\ Cases_on`n < bvl_num_stubs` >- decide_tac
        \\ fs[NOT_LESS] \\ metis_tac[])
      \\ Cases_on`∃n. op = Label n`
      >- (
        fs[] \\ rveq \\
        fs[do_app_def,do_app_aux_def] \\
        imp_res_tac state_rel_code_rel \\
        imp_res_tac code_rel_domain \\
        fs[SUBSET_DEF] \\
        fs[case_eq_thms] \\ rveq \\ fs[] ) \\ fs[]
      \\ Cases_on`∃n. op = BlockOp (Build n)`
      >-
       (fs[] \\ rveq \\
        fs[do_app_def,do_app_aux_def,bvlSemTheory.do_app_def] \\
        imp_res_tac state_rel_code_rel \\
        imp_res_tac code_rel_domain \\
        fs[SUBSET_DEF] \\
        fs[case_eq_thms] \\ rveq \\ fs[] \\
        rpt (pairarg_tac \\ fs []) \\ gvs [state_rel_def] \\
        gvs [bvl_to_bvi_def,bvi_to_bvl_def] \\
        gvs [EVERY_MEM] \\ rw [] \\ res_tac \\ fs []) \\ fs[]
      \\ fs[case_eq_thms] \\ rveq \\ fs[]
      \\ imp_res_tac state_rel_do_app \\ fs[]
      \\ imp_res_tac state_rel_do_app_err \\ fs[])
    \\ rw []
    \\ pairarg_tac \\ fs []
    \\ drule (GEN_ALL scan_expr_Op)
    \\ disch_then drule \\ rw []
    \\ drule scan_expr_op_type \\ rw []
    \\ rename1 `op_type op1 = op_type op2` \\ fs [] \\ rw []
    \\ `env_rel (op_type op') F acc env1 env2` by fs [env_rel_def]
    \\ first_assum (qspecl_then [`xs`, `s`] mp_tac)
    \\ impl_tac >- fs [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ impl_tac >- fs [bool_case_eq, case_eq_thms, case_elim_thms]
    \\ rw []
    \\ qhdtm_x_assum `rewrite` mp_tac
    \\ simp [rewrite_def]
    \\ sg `to_op op2 <> Install /\ (!n. to_op op2 <> Label n)`
    >- (Cases_on `op2` \\ fs [to_op_def])
    \\ sg `to_op op1 <> Install /\ (!n. to_op op1 <> Label n)`
    >- (Cases_on `op1` \\ fs [to_op_def])
    \\ sg `to_op op' <> Install /\ (!n. to_op op' <> Label n)`
    >- (Cases_on `op'` \\ fs [to_op_def])
    \\ PURE_TOP_CASE_TAC \\ fs []
    >-
     (rw [apply_op_def, evaluate_def]
      \\ rw [evaluate_def]
      \\ `acc < LENGTH env2` by fs [env_rel_def] \\ fs []
      \\ every_case_tac \\ fs [] \\ rw []
      \\ imp_res_tac do_app_to_op_state \\ fs [])
    \\ drule (GEN_ALL check_op_thm)
    \\ once_rewrite_tac [METIS_PROVE [] ``p \/ q <=> ~p ==> q``]
    \\ strip_tac \\ rveq \\ fs []
    \\ PURE_TOP_CASE_TAC \\ fs []
    >- (rw [apply_op_def, evaluate_def] \\ imp_res_tac
      do_app_to_op_state \\ fs [])
    \\ rw [] \\ fs []
    \\ qhdtm_x_assum `scan_expr` mp_tac
    \\ fs [rewrite_def, scan_expr_def, opbinargs_def]
    \\ rename1 `op_type op`
    \\ Cases_on `op = Noop`
    >- fs [case_eq_thms, case_elim_thms, bool_case_eq, PULL_EXISTS]
    \\ strip_tac \\ rveq
*)
    (*\\ qhdtm_x_assum `check_op` mp_tac*)
    (*\\ simp [check_op_def, opbinargs_def, get_bin_args_def]*)
    (*\\ rw []*)
(* HOL4 ML code, not ported:
    \\ rename1 `is_rec loc f`
    \\ sg `∃ticks args. f = Call ticks (SOME loc) args NONE`
    >-
     (Cases_on `f` \\ fs [is_rec_def]
      \\ rename1 `_ /\ z = NONE`
      \\ Cases_on `z` \\ fs [is_rec_def])
    \\ rw []
    \\ simp [args_from_def, push_call_def, apply_op_def]
*)
    (*\\ rename1 `evaluate ([_;e2],env1,s)`*)
(* HOL4 ML code, not ported:
    \\ Cases_on `evaluate ([y], env1, s)`
    \\ drule (GEN_ALL (ISPEC s (Q.GEN `s` (SPEC_ALL term_ok_SING))))
    \\ rpt (disch_then drule) \\ rw []
    \\ rename1 `([y], env1, s)`
    \\ sg `ty_rel env2 (ts ++ (REPLICATE (LENGTH env2 - LENGTH env1)
      Any))`
    >-
     (fs [ty_rel_def, LIST_REL_EL_EQN]
      \\ `LENGTH ts < LENGTH env2` by fs [env_rel_def, IS_PREFIX_LENGTH]
      \\ rw []
      \\ Cases_on `n' < LENGTH ts`
      \\ TRY
       (imp_res_tac is_prefix_el \\ rfs [env_rel_def]
        \\ fs [EL_REPLICATE, EL_LENGTH_APPEND, EL_APPEND1, EL_APPEND2]
        \\ `n' < LENGTH ts` by fs []
        \\ first_x_assum drule
        \\ rw []
        \\ drule is_prefix_el
        \\ fs [IS_PREFIX_LENGTH]
        \\ disch_then drule
        \\ rw [] \\ metis_tac [])
      \\ fs [EL_APPEND2]
      \\ `n' - LENGTH ts < LENGTH env2 - LENGTH ts` by fs []
      \\ fs [EL_REPLICATE])
    \\ drule term_ok_extend
    \\ disch_then (qspec_then `REPLICATE (LENGTH env2 - LENGTH env1)
      Any` mp_tac)
    \\ rw []
    \\ Cases_on `evaluate ([y], env2, s')`
    \\ drule (GEN_ALL term_ok_SING)
    \\ rpt (disch_then drule) \\ rw []
    \\ rename1 `evaluate ([y],env2,s') = (Rval [v1],_)`
    \\ qmatch_assum_abbrev_tac `xs <> A ==> _`
    \\ Cases_on `xs = A` \\ fs [Abbr`A`] \\ rveq
    \\ qpat_x_assum `evaluate ([_;_],env1,s) = _` mp_tac
    \\ qmatch_goalsub_abbrev_tac `_ ==> goal`
    \\ simp [evaluate_def]
    \\ CASE_TAC \\ fs []
    \\ rename1 `_ = (res_args, st_args)`
    \\ strip_tac
    \\ `res_args <> Rerr (Rabort Rtype_error)`
      by (fs [pair_case_eq, case_eq_thms, case_elim_thms, bool_case_eq]
        \\ rw [])
    \\ qunabbrev_tac `goal`
    \\ simp [evaluate_def]
    \\ once_rewrite_tac [evaluate_APPEND]
    \\ `acc < LENGTH env2` by fs [env_rel_def] \\ fs []
    \\ first_assum (qspecl_then [`args`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs [] \\ rw [] \\ fs []
    \\ simp [evaluate_def] \\ rfs [] \\ fs []
    \\ `v = v1` by
     (first_x_assum (qspecl_then [`[y]`, `s`] mp_tac)
      \\ simp [bviTheory.exp_size_def]
      \\ imp_res_tac evaluate_clock \\ fs []
      \\ Cases_on `evaluate ([y],env1,s)`
      \\ rpt (disch_then drule) \\ fs [] \\ rw []
      \\ first_x_assum (qspec_then `s` assume_tac)
      \\ first_x_assum (qspec_then `s'` assume_tac)
      \\ rfs [] \\ rw [])
    \\ rveq \\ fs []
    \\ rename1 `state_rel st_args t_args`
    \\ `?val.
           do_app (to_op op) [v; EL acc env2] t_args =
             Rval (val, t_args) /\
           case op_type op of
             Int => ?k. val = Number k
           | List => ?ys. v_to_list val = SOME ys
           | Any => T` by
     (Cases_on `op` \\ fs [to_op_def, from_op_def, op_type_def]
      \\ fs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def,
        env_rel_def,
              bvlSemTheory.do_int_app_def]
      \\ fs [bvl_to_bvi_id])
    \\ fs []
    \\ (reverse (Cases_on `res_args`) \\ fs []
        >- (rw [] \\ fs [] \\ rw [] \\ fs []))
    \\ `code_rel st_args.code t_args.code`
      by (imp_res_tac state_rel_code_rel \\ fs [])
    \\ pop_assum mp_tac
    \\ rw [code_rel_def]
    \\ fs [find_code_def]
    \\ (Cases_on `lookup loc st_args.code` \\ fs [] >- (rw [] \\ fs []))
    \\ PairCases_on `x`
    \\ first_x_assum drule
    \\ imp_res_tac evaluate_code_mono
    \\ fs [subspt_lookup, optimized_code_def]
    \\ rfs [] \\ rveq
    \\ first_x_assum drule \\ strip_tac \\ fs []
    \\ first_x_assum drule \\ strip_tac \\ fs []
    \\ first_x_assum drule \\ strip_tac \\ fs []
    \\ rveq \\ fs []
    \\ disch_then (qspec_then `op` mp_tac) \\ fs []
    \\ simp [check_exp_def]
    \\ strip_tac \\ fs []
    \\ (reverse IF_CASES_TAC \\ fs [] >- (rw [] \\ fs []))
    \\ (IF_CASES_TAC \\ fs []
        >-
         (imp_res_tac state_rel_const \\ fs []
          \\ rveq \\ rfs [] \\ fs [] \\ rw []
          \\ `code_rel st_args.code t_args.code` by imp_res_tac
            state_rel_code_rel
          \\ pop_assum mp_tac
          \\ simp [code_rel_def]
          \\ disch_then (qspec_then `loc` drule)
          \\ rw [check_exp_def, compile_exp_def]
          \\ pairarg_tac \\ fs []
          \\ fs [state_rel_with_clock]))
    \\ `~(st_args.clock < ticks+1)` by (imp_res_tac state_rel_const \\
      fs[])
    \\ fs []
    \\ qpat_x_assum `_ = (q,_)` mp_tac
    \\ PURE_CASE_TAC \\ fs []
    \\ strip_tac
    \\ rename1 `evaluate ([exp], a, _) = (res_exp, st_exp)`
    \\ `res_exp <> Rerr (Rabort Rtype_error)` by
      (fs [pair_case_eq, case_eq_thms, case_elim_thms] \\ rw [])
    \\ rveq \\ rfs []
    \\ `env_rel (op_type op) T (LENGTH a) a (a ++ [val])`
      by (fs [env_rel_def]
          \\ Cases_on `op` \\ fs [op_type_def, EL_APPEND1,
            EL_LENGTH_APPEND])
    \\ `ty_rel a (REPLICATE (LENGTH a) Any)`
      by fs [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
    \\ first_assum (qspecl_then [`[exp]`, `dec_clock (ticks+1) st_args`]
      mp_tac)
    \\ (impl_tac >- (imp_res_tac evaluate_clock \\ fs [dec_clock_def]))
    \\ `state_rel (dec_clock (ticks+1) st_args) (dec_clock (ticks+1)
      t_args)`
      by (imp_res_tac state_rel_const \\ fs
        [state_rel_with_clock,dec_clock_def])
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
    \\ first_x_assum (qspecl_then [`op`,`n`] mp_tac) \\ fs []
    \\ (impl_tac >- (imp_res_tac evaluate_code_mono \\ fs
      [subspt_lookup]))
    \\ pairarg_tac \\ fs []
    \\ simp [apply_op_def]
    \\ strip_tac
    \\ qhdtm_x_assum `compile_exp` mp_tac
    \\ simp [compile_exp_def, check_exp_def] \\ rw [] \\ fs []
    \\ `env_rel (op_type op) T (LENGTH a) a (a ++ [op_id_val op] ++ a)`
      by (fs [env_rel_def]
          \\ Cases_on `op` \\ fs [op_id_val_def, op_type_def,
            EL_APPEND1,
                                  EL_LENGTH_APPEND, IS_PREFIX_APPEND,
                                  bvlSemTheory.v_to_list_def])
    \\ first_x_assum (qspecl_then [`[exp]`, `dec_clock (ticks+1)
      st_args`] mp_tac)
    \\ (impl_tac >- (imp_res_tac evaluate_clock \\ fs [dec_clock_def]))
    \\ rpt (disch_then drule) \\ fs []
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
    \\ (Cases_on `compile_exp loc n' (LENGTH a) exp` \\ fs []
        >-
         (fs [compile_exp_def, check_exp_def]
          \\ rfs []
          \\ pairarg_tac \\ fs []))
    \\ PairCases_on `x` \\ fs []
    \\ first_x_assum (qspecl_then [`op`, `n'`] mp_tac) \\ fs []
    \\ pairarg_tac \\ fs []
    \\ simp [evaluate_def, apply_op_def]
    \\ rw [] \\ rfs [] \\ fs []
    \\ qpat_x_assum `evaluate ([_;_],_,_) = _` mp_tac
    \\ simp [evaluate_def, find_code_def]
    \\ fs [compile_exp_def, check_exp_def] \\ rfs []
    \\ pairarg_tac \\ fs [] \\ rveq
    \\ fs [evaluate_let_wrap] \\ rfs []
    \\ qpat_x_assum `_ = (rrr,_)` mp_tac
    \\ simp [evaluate_def]
    \\ strip_tac
    \\ (reverse (Cases_on `res_exp`) \\ fs []
        >-
         (rw [] \\ fs []
          \\ rw [] \\ fs []
          \\ pop_assum mp_tac
          \\ rpt (PURE_CASE_TAC \\ fs []) \\ rw []))
    \\ fs [env_rel_def, EL_LENGTH_APPEND, EL_APPEND1]
    \\ rw [] \\ fs []
    \\ drule (INST_TYPE [alpha|->``:num#'c``,beta|->``:'ffi``]
      scan_expr_ty_rel)
    \\ rpt (disch_then drule) \\ fs [] \\ rw []
    \\ pop_assum mp_tac
    \\ simp [ty_rel_def] \\ rw []
    \\ Cases_on `op` \\ fs [to_op_def, op_type_def, op_id_val_def] \\ rw
      []
    \\ gvs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def,
      bvlSemTheory.do_int_app_def,
       bvlSemTheory.v_to_list_def]
    \\ fs [bvl_to_bvi_id] \\ rveq \\ fs []
    \\ fs [bvl_to_bvi_id]
    \\ rfs [] \\ rveq
    \\ TRY intLib.COOPER_TAC
    \\ fs [bvl_to_bvi_id] \\ rw []
    \\ fs [check_op_def, try_swap_def, opbinargs_def, get_bin_args_def,
      apply_op_def]
    \\ rw [] \\ metis_tac [is_rec_term_ok])
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tail[Force]:
     (
    gvs [scan_expr_def, evaluate_def]
    \\ ‘LENGTH env1 ≤ LENGTH env2’ by metis_tac [env_rel_def,
      IS_PREFIX_LENGTH]
    \\ imp_res_tac state_rel_const \\ gvs []
    \\ rw [] \\ gvs [AllCaseEqs(), PULL_EXISTS]
    >- (
      gvs [oneline dest_thunk_def, env_rel_def, AllCaseEqs(),
        PULL_EXISTS]
      \\ drule_then drule is_prefix_el \\ simp []
      \\ disch_then $ assume_tac o GSYM \\ gvs [])
    >- (
      gvs [oneline dest_thunk_def, env_rel_def, AllCaseEqs(),
        PULL_EXISTS]
      \\ drule_then drule is_prefix_el \\ simp []
      \\ disch_then $ assume_tac o GSYM \\ gvs []
      \\ gvs [find_code_def, AllCaseEqs()]
      \\ simp [GSYM PULL_EXISTS] \\ reverse $ rw []
      >- gvs [state_rel_def, state_component_equality]
      \\ drule state_rel_code_rel \\ rw [code_rel_def]
      \\ first_x_assum drule \\ rw []
      \\ gvs [compile_exp_def]
      \\ Cases_on `check_exp force_loc 2 exp` \\ gvs []
      \\ pairarg_tac \\ gvs [])
    \\ last_assum $ qspecl_then [‘[exp]’, ‘dec_clock 1 s’] mp_tac
    \\ gvs [dec_clock_def]
    \\ disch_then drule
    \\ gvs [find_code_def, oneline dest_thunk_def, AllCaseEqs(),
      PULL_EXISTS]
    \\ ‘state_rel (s with clock := s.clock - 1) (s' with clock :=
      s'.clock - 1)’
      by gvs [state_rel_def]
    \\ disch_then $ drule_at (Pat ‘state_rel _ _’) \\ gvs []
    \\ ‘ty_rel [RefPtr F ptr; v] [Any; Any]’ by gvs [ty_rel_def]
    \\ disch_then $ drule_at (Pat ‘ty_rel _ _’) \\ gvs []
    \\ disch_then $ qspec_then ‘F’ mp_tac \\ simp [env_rel_def]
    \\ disch_then $ qspec_then ‘[RefPtr F ptr; v]’ mp_tac \\ rw []
    \\ ‘EL n env2 = EL n env1’ by (
      gvs [env_rel_def] \\ drule_then drule is_prefix_el \\ rw [])
    \\ gvs [PULL_EXISTS]
    \\ qpat_x_assum ‘state_rel (s with clock := _) (s' with clock := _)’
         assume_tac
    \\ drule state_rel_code_rel \\ simp [code_rel_def]
    \\ disch_then drule \\ rw []
    \\ Cases_on ‘check_exp force_loc 2 exp’ \\ gvs []
    \\ gvs [compile_exp_def, AllCaseEqs()]
    \\ pairarg_tac \\ gvs []
    \\ imp_res_tac scan_expr_not_Noop
    \\ drule evaluate_let_wrap
    \\ qabbrev_tac ‘a = [RefPtr F ptr; v]’
    \\ disch_then $ qspecl_then [‘opt'’, ‘a’,
                                 ‘s' with clock := s'.clock - 1’]
                                   assume_tac
    \\ ‘LENGTH a = 2’ by (unabbrev_all_tac \\ gvs []) \\ gvs []
    \\ ntac 2 (pop_assum kall_tac)
    \\ first_assum (qspecl_then [‘[exp]’,‘dec_clock 1 s’] mp_tac)
    \\ impl_tac >- (imp_res_tac evaluate_clock \\ fs [dec_clock_def])
    \\ ‘env_rel (op_type x) T (LENGTH a) a (a ++ [op_id_val x] ++ a)’ by
      (
      Cases_on ‘x’
      \\ gvs [op_id_val_def, op_type_def, env_rel_def, EL_LENGTH_APPEND,
             EL_APPEND1, IS_PREFIX_APPEND, bvlSemTheory.v_to_list_def])
    \\ ‘ty_rel a [Any; Any]’ by gvs [ty_rel_def, LIST_REL_EL_EQN,
      EL_REPLICATE]
    \\ gvs [dec_clock_def]
    \\ rpt (disch_then drule) \\ gvs []
    \\ disch_then (qspec_then ‘force_loc’ mp_tac) \\ rw []
    \\ unabbrev_all_tac \\ gvs []
    \\ ‘REPLICATE 2 Any = [Any; Any]’ by gvs [REPLICATE_compute] \\ gvs
      []
    \\ first_x_assum $ qspecl_then [‘x’,‘n'’] mp_tac \\ rw [] \\ gvs []
    \\ gvs [optimized_code_def, compile_exp_def, check_exp_def]
    \\ gvs [evaluate_def, apply_op_def, AllCaseEqs()]
    \\ (
      scan_expr_ty_rel
        |> SPEC_ALL
        |> INST_TYPE [alpha|->“:num#'c”,beta|->“:'ffi”]
        |> GEN_ALL
        |> drule
      \\ rpt (disch_then drule) \\ strip_tac \\ gvs []
      \\ pop_assum mp_tac \\ gvs [] \\ once_rewrite_tac [ty_rel_def]
      \\ strip_tac \\ gvs []
      \\ PRED_ASSUM is_forall kall_tac
      \\ Cases_on ‘x’
      \\ gvs [op_type_def, to_op_def, do_app_def, do_app_aux_def,
        op_id_val_def,
              bvlSemTheory.do_app_def, bvlSemTheory.v_to_list_def,
              list_to_v_imp, oneline bvlSemTheory.do_int_app_def,
              AllCaseEqs()]))
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tail[Call]:
   (simp [scan_expr_def, evaluate_def]
    \\ IF_CASES_TAC >- fs []
    \\ `dest = NONE ⇒ ¬IS_SOME hdl` by fs []
    \\ qpat_x_assum `¬(_)` kall_tac
    \\ TOP_CASE_TAC
    \\ first_assum (qspecl_then [`xs`, `s`] mp_tac)
    \\ impl_tac >- gvs []
    \\ simp [bviTheory.exp_size_def]
    \\ sg `env_rel ty F acc env1 env2` >- fs [env_rel_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ strip_tac
    \\ reverse PURE_TOP_CASE_TAC \\ fs [] >- (rw [] \\ fs [])
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    >-
     (rw [pair_case_eq, case_eq_thms, case_elim_thms, bool_case_eq,
       PULL_EXISTS]
      \\ rename1 `state_rel t t'`
      \\ `code_rel t.code t'.code` by (imp_res_tac state_rel_code_rel \\
        fs [])
      \\ Cases_on `find_code dest a t'.code` \\ fs [] \\ rveq
      >-
       (Cases_on `dest` \\ fs []
        \\ metis_tac [code_rel_find_code_NONE, code_rel_find_code_SOME])
      \\ PairCases_on `x` \\ fs [state_rel_def])
    \\ rename1 `state_rel t1 t2`
    \\ rename1 `([exp],args, _)`
    \\ Cases_on `dest` \\ fs []
    >- (strip_tac
      \\ PURE_TOP_CASE_TAC \\ fs []
      >- metis_tac [evaluate_code_mono, code_rel_find_code_NONE,
        state_rel_code_rel]
      \\ PURE_TOP_CASE_TAC \\ fs []
      \\ qpat_x_assum `_ = (r, t)` mp_tac
      \\ PURE_TOP_CASE_TAC \\ fs []
      \\ rpt (qpat_x_assum `find_code _ _ _ = _` mp_tac)
      \\ simp [find_code_def]
      \\ ntac 3 (CASE_TAC \\ fs [])
      \\ strip_tac \\ rveq
      \\ ntac 2 (CASE_TAC \\ fs [])
      \\ strip_tac \\ rveq
      \\ imp_res_tac state_rel_code_rel \\ fs []
      \\ pop_assum kall_tac
      \\ qpat_assum `code_rel _ _` mp_tac
      \\ simp_tac std_ss [code_rel_def]
      \\ disch_then drule
      \\ simp [compile_exp_def]
      \\ CASE_TAC \\ fs []
      >-
       (strip_tac \\ rveq
        \\ sg `env_rel ty F (LENGTH (FRONT a)) (FRONT a) (FRONT a)`
        >- fs [env_rel_def]
        \\ sg `ty_rel (FRONT a) (REPLICATE (LENGTH (FRONT a)) Any)`
        >- fs [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
        \\ first_assum (qspecl_then [`[exp]`,`dec_clock (ticks+1) t1`]
          mp_tac)
        \\ impl_tac >- (imp_res_tac evaluate_clock \\ simp
          [dec_clock_def])
        \\ simp []
        \\ sg `state_rel (dec_clock (ticks+1) t1) (dec_clock (ticks+1)
          t2)`
        >- (imp_res_tac state_rel_const \\ fs [dec_clock_def,
          state_rel_with_clock])
        \\ rpt (disch_then drule) \\ fs []
        \\ fs [pair_case_eq, case_eq_thms, case_elim_thms, bool_case_eq,
          PULL_EXISTS]
        \\ rw [] \\ fs [state_rel_def])
      \\ strip_tac
      \\ pairarg_tac \\ fs [] \\ rveq
      \\ IF_CASES_TAC \\ fs []
      >- (imp_res_tac state_rel_const \\ fs [])
      \\ rename1 `let_wrap qs _ _`
      \\ `qs = LENGTH (FRONT a)` by fs [LENGTH_FRONT]
      \\ pop_assum (fn th => fs [th])
      \\ imp_res_tac scan_expr_not_Noop
      \\ fs [evaluate_let_wrap]
      \\ sg `env_rel (op_type x) T (LENGTH (FRONT a)) (FRONT a)
                                   (FRONT a ++ [op_id_val x] ++ FRONT
                                     a)`
      >-
        (fs [env_rel_def, EL_LENGTH_APPEND, EL_APPEND1,
          IS_PREFIX_APPEND]
         \\ Cases_on `x` \\ fs [op_id_val_def, op_type_def, v_ty_cases,
                                bvlSemTheory.v_to_list_def])
      \\ sg `ty_rel (FRONT a) (REPLICATE (LENGTH (FRONT a)) Any)`
      >- fs [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
      \\ Cases_on `q' = Rerr (Rabort Rtype_error)`
      >- fs [pair_case_eq, bool_case_eq, case_eq_thms, case_elim_thms]
      \\ first_assum (qspecl_then [`[exp]`,`dec_clock (ticks+1) t1`]
        mp_tac)
      \\ impl_tac >- (imp_res_tac evaluate_clock \\ simp
        [dec_clock_def])
      \\ simp []
      \\ sg `state_rel (dec_clock (ticks+1) t1) (dec_clock (ticks+1)
        t2)`
      >- (imp_res_tac state_rel_const \\ fs [dec_clock_def,
        state_rel_with_clock])
      \\ rpt (disch_then drule) \\ fs []
      \\ disch_then (qspec_then `n` mp_tac) \\ fs []
      \\ strip_tac
      \\ first_x_assum (qspecl_then [`x`,`n'`] mp_tac) \\ rw [] \\ fs []
      \\ rfs [optimized_code_def, compile_exp_def, check_exp_def]
      \\ fs [apply_op_def]
      \\ rfs [] \\ rveq
      \\ fs [evaluate_def, apply_op_def, EL_LENGTH_APPEND, EL_APPEND1]
      \\ fs [pair_case_eq, case_eq_thms, case_elim_thms, bool_case_eq]
      \\ fs [PULL_EXISTS] \\ rw []
      \\ drule (GEN_ALL (INST_TYPE
        [alpha|->``:num#'c``,beta|->``:'ffi``] (SPEC_ALL
        scan_expr_ty_rel)))
      \\ rpt (disch_then drule) \\ strip_tac \\ fs []
      \\ pop_assum mp_tac \\ fs [] \\ once_rewrite_tac [ty_rel_def] \\
        strip_tac
      \\ fs []
      \\ PRED_ASSUM is_forall kall_tac
      \\ Cases_on `x`
      \\ gvs [to_op_def, op_id_val_def, do_app_def, do_app_aux_def,
             bvlSemTheory.do_app_def, bvlSemTheory.do_int_app_def,
             bvl_to_bvi_id, op_type_def]
      \\ fs [bvlSemTheory.v_to_list_def]
      \\ fs [case_eq_thms, case_elim_thms, pair_case_eq, bool_case_eq]
        \\ rw []
      \\ fs [bvl_to_bvi_id, list_to_v_imp])
    >-
     (PURE_TOP_CASE_TAC \\ fs [] \\ strip_tac
    \\ PURE_TOP_CASE_TAC \\ fs []
    >- (imp_res_tac state_rel_code_rel \\ metis_tac
      [code_rel_find_code_SOME])
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    >- (imp_res_tac state_rel_const \\ fs [])
    \\ first_assum (qspecl_then [`[exp]`, `dec_clock (ticks+1) t1`]
      mp_tac)
    \\ impl_tac >- (imp_res_tac evaluate_clock \\ simp [dec_clock_def])
    \\ `env_rel ty F acc args args` by fs [env_rel_def]
    \\ sg `ty_rel args (REPLICATE (LENGTH args) Any)`
    >- fs [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
    \\ sg `state_rel (dec_clock (ticks+1) t1) (dec_clock (ticks+1) t2)`
    >- (imp_res_tac state_rel_const \\ fs [state_rel_with_clock,
      dec_clock_def])
    \\ rpt (disch_then drule) \\ fs []
    \\ impl_tac
    >- (strip_tac \\ gvs [])
    \\ rpt (qhdtm_x_assum `find_code` mp_tac)
    \\ simp [find_code_def]
    \\ ntac 4 (PURE_TOP_CASE_TAC \\ fs []) \\ rw []
    \\ imp_res_tac state_rel_code_rel
    \\ qpat_assum `code_rel t1.code _` mp_tac
    \\ simp_tac std_ss [code_rel_def]
    \\ disch_then drule \\ fs []
    \\ simp [compile_exp_def]
    \\ CASE_TAC \\ fs []
    >-
     (fs [pair_case_eq, case_eq_thms, case_elim_thms, bool_case_eq,
          PULL_EXISTS] \\ rw []
      \\ rename1 `([z], aa::env1, s2)`
      \\ first_x_assum (qspecl_then [`[z]`,`s2`] mp_tac)
      \\ impl_tac
      >- (imp_res_tac evaluate_clock \\ fs [dec_clock_def])
      \\ `env_rel ty F (LENGTH env1 + 1) (aa::env1) (aa::env2)` by fs
        [env_rel_def]
      \\ sg `ty_rel (aa::env1) (Any::ts)`
      >- fs [ty_rel_def, LIST_REL_EL_EQN]
      \\ imp_res_tac state_rel_const \\ fs []
      \\ rpt (disch_then drule) \\ rw []
      \\ fs [ty_rel_def, LIST_REL_EL_EQN]
      \\ imp_res_tac evaluate_clock \\ fs [dec_clock_def])
    \\ rw []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ imp_res_tac scan_expr_not_Noop \\ fs []
    \\ simp [evaluate_let_wrap]
    \\ first_assum (qspecl_then [`[exp]`,`dec_clock (ticks+1) t1`]
      mp_tac)
    \\ impl_tac >- (imp_res_tac evaluate_clock \\ fs [dec_clock_def])
    \\ sg `env_rel (op_type x') T (LENGTH a) a (a ++ [op_id_val x'] ++
      a)`
    >-
     (Cases_on `x'`
      \\ fs [op_id_val_def, op_type_def, env_rel_def, EL_LENGTH_APPEND,
             EL_APPEND1, IS_PREFIX_APPEND, bvlSemTheory.v_to_list_def])
    \\ sg `ty_rel a (REPLICATE (LENGTH a) Any)`
    >- fs [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
    \\ rpt (disch_then drule) \\ fs []
    \\ disch_then (qspec_then `x` mp_tac)
    \\ impl_tac >- (strip_tac \\ gvs [])
    \\ simp [optimized_code_def, compile_exp_def, check_exp_def,
      apply_op_def, evaluate_def]
    \\ rw []
    \\ first_x_assum (qspecl_then [`x'`,`n`] mp_tac)
    \\ simp [optimized_code_def,compile_exp_def, check_exp_def]
    \\ simp [apply_op_def, evaluate_def]
    \\ reverse (PURE_CASE_TAC \\ fs [])
    >-
     (fs [case_eq_thms, PULL_EXISTS, pair_case_eq, case_elim_thms] \\ rw
       []
      \\ rename1 `([z], aa::env1, s2)`
      \\ qpat_x_assum `code_rel t1.code _` mp_tac
      \\ simp [code_rel_def]
      \\ disch_then drule \\ fs []
      \\ rw [compile_exp_def, check_exp_def]
      \\ pairarg_tac \\ fs [] \\ rw []
      \\ first_x_assum (qspecl_then [`[z]`,`s2`] mp_tac)
      \\ impl_tac >- (imp_res_tac evaluate_clock \\ fs [dec_clock_def])
      \\ `env_rel ty F (LENGTH env1 + 1) (aa::env1) (aa::env2)` by fs
        [env_rel_def]
      \\ `ty_rel (aa::env1) (Any::ts)` by fs [ty_rel_def]
      \\ rpt (disch_then drule) \\ rw []
      \\ imp_res_tac evaluate_clock \\ fs [dec_clock_def])
    \\ rw [] \\ fs []
    \\ qpat_x_assum `_ = (rrr,_)` mp_tac
    \\ simp [EL_LENGTH_APPEND, EL_APPEND1]
    \\ drule (GEN_ALL (INST_TYPE [alpha|->``:num#'c``,beta|->``:'ffi``]
      (SPEC_ALL scan_expr_ty_rel)))
    \\ rpt (disch_then drule) \\ fs [] \\ strip_tac
    \\ pop_assum mp_tac
    \\ simp [ty_rel_def] \\ strip_tac \\ fs []
    \\ PRED_ASSUM is_forall kall_tac
    \\ Cases_on `x'`
    \\ fs [to_op_def, op_type_def, do_app_def, do_app_aux_def,
      op_id_val_def,
           bvlSemTheory.do_app_def,bvlSemTheory.do_int_app_def,
           bvl_to_bvi_id, bvlSemTheory.v_to_list_def]
    \\ rw [] \\ fs []
    \\ fs [list_to_v_imp]
    \\ fs [bvl_to_bvi_id]))
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tail[Return]:
   (simp [scan_expr_def, evaluate_def, rewrite_def]
    \\ `env_rel ty F acc env1 env2` by fs [env_rel_def]
    \\ CASE_TAC \\ fs []
    \\ fs [pair_case_eq, case_eq_thms, case_elim_thms, bool_case_eq,
      PULL_EXISTS]
    \\ first_x_assum (qspecl_then [`es`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ rw [] \\ rfs [])
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tail[LetCall]:
   (simp [scan_expr_def, evaluate_def]
    \\ `env_rel ty F acc env1 env2` by fs [env_rel_def]
    \\ TOP_CASE_TAC
    \\ first_assum (qspecl_then [`es`, `s`] mp_tac)
    \\ impl_tac >- gvs []
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ strip_tac
    \\ reverse PURE_TOP_CASE_TAC \\ fs []
    >- (rw [] \\ fs [])
    >- (PURE_TOP_CASE_TAC \\ fs []
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    >-
     (rw [pair_case_eq, case_eq_thms, case_elim_thms, bool_case_eq,
       PULL_EXISTS]
      \\ rename1 `state_rel t t'`
      \\ `code_rel t.code t'.code` by (imp_res_tac state_rel_code_rel \\
        fs [])
      \\ Cases_on `find_code (SOME dest) a t'.code` \\ fs [] \\ rveq
      >- metis_tac [code_rel_find_code_SOME]
      \\ PairCases_on `x` \\ fs [state_rel_def])
    \\ rename1 `state_rel t1 t2`
    \\ rename1 `([exp],args, _)`
    >- (strip_tac
    \\ imp_res_tac state_rel_code_rel
    \\ `find_code (SOME dest) a t2.code <> NONE` by metis_tac
      [code_rel_find_code_SOME]
    \\ Cases_on `find_code (SOME dest) a t2.code` \\ fs []
    \\ PairCases_on `x` \\ fs []
    \\ `t2.clock = t1.clock` by (imp_res_tac state_rel_const \\ fs [])
    \\ fs []
    \\ `x0 = args` by (fs [find_code_def, AllCaseEqs()])
    \\ gvs []
    \\ Cases_on `evaluate ([exp],args,dec_clock (ticks + 1) t1)` \\ fs
      []
    \\ first_assum (qspecl_then [`[exp]`, `dec_clock (ticks+1) t1`]
      mp_tac)
    \\ impl_tac >- (imp_res_tac evaluate_clock \\ simp [dec_clock_def])
    \\ `env_rel ty F acc args args` by fs [env_rel_def]
    \\ sg `ty_rel args (REPLICATE (LENGTH args) Any)`
    >- fs [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
    \\ sg `state_rel (dec_clock (ticks+1) t1) (dec_clock (ticks+1) t2)`
    >- (imp_res_tac state_rel_const \\ fs [state_rel_with_clock,
      dec_clock_def])
    \\ rpt (disch_then drule) \\ fs []
    \\ impl_tac >- (strip_tac \\ gvs [])
    \\ strip_tac
    \\ rpt (qhdtm_x_assum `find_code` mp_tac)
    \\ simp [find_code_def]
    \\ ntac 4 (PURE_TOP_CASE_TAC \\ fs []) \\ rw []
    \\ qpat_assum `code_rel t1.code _` mp_tac
    \\ simp_tac std_ss [code_rel_def]
    \\ disch_then drule \\ fs []
    \\ simp [compile_exp_def]
    \\ CASE_TAC \\ fs []
    >- (strip_tac \\ gvs []
    \\ gvs [AllCaseEqs()]
    \\ last_assum (qspecl_then [`[y]`, `r'`] mp_tac)
    \\ impl_tac >- (imp_res_tac evaluate_clock \\ fs [dec_clock_def])
    \\ `env_rel ty F acc (ret_vs ++ env1) (ret_vs ++ env2)` by
         (gvs [env_rel_def, IS_PREFIX_APPEND])
    \\ `ty_rel (ret_vs ++ env1) (REPLICATE (LENGTH (ret_vs ++ env1))
      Any)` by
         fs [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
    \\ rpt (disch_then drule) \\ fs [])
    >- (rw []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ imp_res_tac scan_expr_not_Noop \\ fs []
    \\ simp [evaluate_let_wrap]
    \\ first_assum (qspecl_then [`[exp]`,`dec_clock (ticks+1) t1`]
      mp_tac)
    \\ impl_tac >- (imp_res_tac evaluate_clock \\ fs [dec_clock_def])
    \\ sg `env_rel (op_type x) T (LENGTH a) a (a ++ [op_id_val x] ++ a)`
    >-
     (Cases_on `x`
      \\ fs [op_id_val_def, op_type_def, env_rel_def, EL_LENGTH_APPEND,
             EL_APPEND1, IS_PREFIX_APPEND, bvlSemTheory.v_to_list_def])
    \\ sg `ty_rel a (REPLICATE (LENGTH a) Any)`
    >- fs [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
    \\ rpt (disch_then drule) \\ fs []
    \\ disch_then (qspec_then `dest` mp_tac)
    \\ impl_tac >- (strip_tac \\ gvs [])
    \\ strip_tac
    \\ first_x_assum (qspecl_then [`x`,`n`] mp_tac)
    \\ simp [optimized_code_def, compile_exp_def, check_exp_def]
    \\ simp [apply_op_def, evaluate_def]
    \\ strip_tac
    \\ Cases_on `q` \\ gvs []
    \\ gvs [AllCaseEqs()]
    \\ qmatch_goalsub_abbrev_tac `evaluate ([y],ret_vs ++ env2,T1)`
    \\ `env_rel ty F acc (ret_vs ++ env1) (ret_vs ++ env2)` by
         (gvs [env_rel_def, IS_PREFIX_APPEND])
    \\ `ty_rel (ret_vs ++ env1) (REPLICATE (LENGTH (ret_vs ++ env1))
      Any)` by
         fs [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
    \\ last_assum (qspecl_then [`[y]`, `r'`] mp_tac)
    \\ impl_tac >- (imp_res_tac evaluate_clock \\ fs [dec_clock_def])
    \\ disch_then (qspecl_then
         [`ret_vs ++ env1`,`r`,`t`,`F`,`T1`,`acc`,`ret_vs ++
           env2`,`dest`,
          `REPLICATE (LENGTH (ret_vs ++ env1)) Any`,`ty`] mp_tac)
    \\ impl_tac >- fs []
    \\ rw []))))
QED
*)

(* HOL4 ML code, not ported:
Finalise evaluate_rewrite_tail;
*)
