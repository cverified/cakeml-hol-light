(* ======================================================== *)
(*  inferComplete: ported from HOL4's
    compiler/inference/proofs/inferCompleteScript.sml  *)
(* ======================================================== *)

(*
  Proves completeness of the type inferencer, i.e. if there is a type
  for the program, then the type inferencer will find a type (the most
  general type).
*)

needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/proofs/envRel.ml";;
needs "compiler/inference/proofs/infer_eComplete.ml";;
needs "compiler/inference/proofs/infer_eSound.ml";;
needs "compiler/inference/proofs/type_dCanon.ml";;
needs "compiler/inference/proofs/type_eDeterm.ml";;
needs "compiler/inference/unify.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

(* HOL4 ML code, not ported:
val t_ind = t_induction
  |> Q.SPECL[`P`,`EVERY P`]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> SIMP_RULE (srw_ss()) []
  |> Q.GEN`P`;
*)


(* HOL4 ML code, not ported:
fun str_assums strs = ConseqConv.DISCH_ASM_CONSEQ_CONV_TAC
        (ConseqConv.CONSEQ_REWRITE_CONV ([], strs, []));
*)

(*
Theorem check_specs_complete:
   !mn tenvT specs decls tenv.
    type_specs mn tenvT specs decls tenv ⇒
    ∀st1 extra_idecls extra_ienv.
      tenv_abbrev_ok tenvT ⇒
      ?st2 idecls new_ienv.
        decls = convert_decls idecls ∧
        env_rel tenv new_ienv ∧
        check_specs mn tenvT extra_idecls extra_ienv specs st1 =
          (M_success (append_decls idecls extra_idecls,extend_dec_ienv
            new_ienv extra_ienv), st2)
Proof
  ho_match_mp_tac type_specs_ind >>
  rw [check_specs_def, success_eqns]
  >- (
    fs [extend_dec_ienv_def, empty_decls_def, convert_decls_def,
      append_decls_def,
        inf_decls_component_equality, inf_env_component_equality] >>
    qexists_tac `empty_inf_decls` >>
    qexists_tac `<| inf_v := nsEmpty; inf_c := nsEmpty; inf_t := nsEmpty
      |>` >>
    rw [empty_inf_decls_def])
  >- (
    drule (CONJUNCT1 check_freevars_t_to_freevars) >>
    disch_then (qspec_then `st1` strip_assume_tac) >>
    rw [PULL_EXISTS] >>
    qho_match_abbrev_tac
      `?st2 idecls new_ienv. _ idecls ∧ _ new_ienv ∧ check_specs _ _ _
        (extra_ienv with inf_v := nsBind name new extra_ienv.inf_v) _ _
        = (M_success (_ idecls new_ienv), st2)` >>
    simp [] >>
    first_x_assum (qspecl_then [`st'`, `extra_idecls`, `(extra_ienv with
      inf_v := nsBind name new extra_ienv.inf_v)`] mp_tac) >>
    rw [] >>
    rw [] >>
    qexists_tac `idecls` >>
    qexists_tac `extend_dec_ienv new_ienv <| inf_v := nsSing name new;
      inf_c := nsEmpty; inf_t := nsEmpty |>` >>
    unabbrev_all_tac >>
    rw []
    >- (
      irule env_rel_extend >>
      rw [] >>
      irule env_rel_binding >>
      rw [] >>
      irule check_freevars_type_name_subst >>
      rw [] >>
      metis_tac [t_to_freevars_check])
    >- (
      rw [extend_dec_ienv_def] >>
      simp_tac std_ss [GSYM nsAppend_assoc, nsAppend_nsSing]))
 >- (
    qho_match_abbrev_tac
      `?st2 idecls new_ienv. _ idecls ∧ _ new_ienv ∧ _ ∧ check_specs _ _
        eid'
         <| inf_v := _ ; inf_c := nsAppend new_ctors _; inf_t :=
           nsAppend new_t _ |> _ _ = (M_success (_ idecls new_ienv),
           st2)` >>
    simp [] >>
    `tenv_abbrev_ok new_t`
      by (
        unabbrev_all_tac >>
        simp [typeSoundInvariantsTheory.tenv_abbrev_ok_def] >>
        irule nsAll_alist_to_ns >>
        simp [EVERY_MAP, LAMBDA_PROD, check_freevars_def, EVERY_MEM] >>
        REWRITE_TAC [ELIM_UNCURRY]) >>
    `tenv_abbrev_ok (nsAppend new_t tenvT)` by metis_tac
      [tenv_abbrev_ok_merge] >>
    fs [] >>
    first_x_assum (qspecl_then [`st1`, `eid'`,
       `<|inf_v := extra_ienv.inf_v; inf_c := nsAppend new_ctors
         extra_ienv.inf_c; inf_t := nsAppend new_t extra_ienv.inf_t|>`]
         mp_tac) >>
    rw [] >>
    rw [] >>
    qexists_tac `append_decls idecls <| inf_defined_types := MAP
      (λ(tvs,tn,ctors). mk_id mn tn) td;
              inf_defined_mods := []; inf_defined_exns := []|>` >>
    qexists_tac `extend_dec_ienv new_ienv <| inf_v := nsEmpty; inf_c :=
      new_ctors; inf_t := new_t |>` >>
    unabbrev_all_tac >>
    rw []
    >- (
      simp [convert_append_decls] >>
      rw [convert_decls_def])
    >- (
      irule env_rel_extend >>
      rw [] >>
      qmatch_abbrev_tac `env_rel tenv' ienv'` >>
      `ienv_ok {} ienv'`
        by (
          unabbrev_all_tac >>
          simp [ienv_ok_def, ienv_val_ok_def] >>
          irule check_ctor_tenv_ok >>
          simp []) >>
      `tenv' = ienv_to_tenv ienv'`
        by (
          unabbrev_all_tac >>
          rw [ienv_to_tenv_def]) >>
      rw [] >>
      irule env_rel_ienv_to_tenv >>
      unabbrev_all_tac >>
      rw [ienv_ok_def])
    >- rw [append_decls_def]
    >- rw [extend_dec_ienv_def])
  >- (
    qho_match_abbrev_tac
      `?st2 idecls new_ienv. _ idecls ∧ _ new_ienv ∧ check_specs _ _
        eid' (_ with inf_t := nsBind name new_t _) _ _ = (M_success (_
        idecls new_ienv), st2)` >>
    simp [] >>
    `tenv_abbrev_ok (nsBind name new_t tenvT)`
      by (
        fs [typeSoundInvariantsTheory.tenv_abbrev_ok_def] >>
        irule nsAll_nsBind >>
        unabbrev_all_tac >>
        rw [] >>
        metis_tac [typeSoundInvariantsTheory.tenv_abbrev_ok_def,
          check_freevars_type_name_subst]) >>
    first_x_assum (qspecl_then [`st1`, `eid'`, `extra_ienv with inf_t :=
      nsBind name new_t extra_ienv.inf_t`] mp_tac) >>
    rw [] >>
    rw [] >>
    qexists_tac `idecls` >>
    qexists_tac `extend_dec_ienv new_ienv <| inf_v := nsEmpty; inf_c :=
      nsEmpty; inf_t := nsSing tn (tvs,type_name_subst tenvT t)|>` >>
    unabbrev_all_tac >>
    rw []
    >- (
      irule env_rel_extend >>
      simp [] >>
      qmatch_abbrev_tac `env_rel tenv' ienv'` >>
      `tenv' = ienv_to_tenv ienv'`
        by (
          unabbrev_all_tac >>
          rw [ienv_to_tenv_def]) >>
      simp [] >>
      irule env_rel_ienv_to_tenv >>
      unabbrev_all_tac >>
      rw [ienv_ok_def, ienv_val_ok_def,
        typeSoundInvariantsTheory.tenv_abbrev_ok_def] >>
      metis_tac [check_freevars_type_name_subst]) >>
    simp [extend_dec_ienv_def] >>
    simp_tac std_ss [nsAppend_nsSing, GSYM nsAppend_assoc])
  >- (
    fs [] >>
    qho_match_abbrev_tac
      `?st2 idecls new_ienv. _ idecls ∧ _ new_ienv ∧ check_specs _ _
        eid' (extra_ienv with inf_c := nsBind name new_c
        extra_ienv.inf_c) _ _ = (M_success (_ idecls new_ienv), st2)` >>
    simp [] >>
    first_x_assum (qspecl_then [`st1`, `eid'`, `extra_ienv with inf_c :=
      nsBind name new_c extra_ienv.inf_c`] mp_tac) >>
    rw [] >>
    rw [] >>
    qexists_tac `append_decls idecls <| inf_defined_types := [];
      inf_defined_mods := []; inf_defined_exns := [mk_id mn name]|>` >>
    qexists_tac `extend_dec_ienv new_ienv <| inf_v := nsEmpty; inf_c :=
      nsSing name ([],MAP (type_name_subst tenvT) ts, TypeExn (mk_id mn
      name)); inf_t := nsEmpty |>` >>
    unabbrev_all_tac >>
    simp [convert_append_decls] >>
    rw [convert_decls_def]
    >- (
      irule env_rel_extend >>
      simp [] >>
      qmatch_abbrev_tac `env_rel tenv' ienv'` >>
      `tenv' = ienv_to_tenv ienv'`
        by (
          unabbrev_all_tac >>
          rw [ienv_to_tenv_def]) >>
      simp [] >>
      irule env_rel_ienv_to_tenv >>
      unabbrev_all_tac >>
      rw [ienv_ok_def, ienv_val_ok_def,
        typeSoundInvariantsTheory.tenv_ctor_ok_def] >>
      fs [EVERY_MEM, EVERY_MAP, check_exn_tenv_def] >>
      metis_tac [check_freevars_type_name_subst])
    >- simp [append_decls_def]
    >- (
      simp [extend_dec_ienv_def] >>
      simp_tac std_ss [nsAppend_nsSing, GSYM nsAppend_assoc] >>
      metis_tac []))
  >- (
    qho_match_abbrev_tac
      `?st2 idecls new_ienv. _ idecls ∧ _ new_ienv ∧ check_specs _ _
        eid' (_ with inf_t := nsBind name new_t _) _ _ = (M_success (_
        idecls new_ienv), st2)` >>
    simp [] >>
    `tenv_abbrev_ok (nsBind name new_t tenvT)`
      by (
        fs [typeSoundInvariantsTheory.tenv_abbrev_ok_def] >>
        irule nsAll_nsBind >>
        unabbrev_all_tac >>
        rw [check_freevars_def, EVERY_MAP, EVERY_MEM]) >>
    first_x_assum (qspecl_then [`st1`, `eid'`, `extra_ienv with inf_t :=
      nsBind name new_t extra_ienv.inf_t`] mp_tac) >>
    rw [] >>
    rw [] >>
    qexists_tac `append_decls idecls <| inf_defined_types := [mk_id mn
      name]; inf_defined_mods := []; inf_defined_exns := []|>` >>
    qexists_tac `extend_dec_ienv new_ienv <| inf_v := nsEmpty; inf_c :=
      nsEmpty; inf_t := nsSing tn (tvs,Tapp (MAP Tvar tvs) (TC_name
      (mk_id mn tn)))|>` >>
    unabbrev_all_tac >>
    rw []
    >- (
      simp [convert_append_decls] >>
      simp [convert_decls_def])
    >- (
      irule env_rel_extend >>
      simp [] >>
      qmatch_abbrev_tac `env_rel tenv' ienv'` >>
      `tenv' = ienv_to_tenv ienv'`
        by (
          unabbrev_all_tac >>
          rw [ienv_to_tenv_def]) >>
      simp [] >>
      irule env_rel_ienv_to_tenv >>
      unabbrev_all_tac >>
      rw [ienv_ok_def, ienv_val_ok_def,
        typeSoundInvariantsTheory.tenv_abbrev_ok_def] >>
      rw [check_freevars_def, EVERY_MAP, EVERY_MEM])
    >- simp [append_decls_def]
    >- (
      simp [extend_dec_ienv_def] >>
      simp_tac std_ss [nsAppend_nsSing, GSYM nsAppend_assoc]))
QED

Theorem n_fresh_uvar_rw[local]:
  ∀n st.n_fresh_uvar n st = (M_success (GENLIST
    (λi.Infer_Tuvar(i+st.next_uvar)) n), st with next_uvar :=
    st.next_uvar + n)
Proof
  Induct>>simp[Once n_fresh_uvar_def]
  >-
    (EVAL_TAC>>fs[infer_st_component_equality])
  >>
    rw[st_ex_bind_def,fresh_uvar_def,st_ex_return_def,ADD1]>>
    simp[GENLIST_CONS,GSYM ADD1]>>
    AP_THM_TAC>>AP_TERM_TAC>>fs[o_DEF]>>
    fs[FUN_EQ_THM]
QED

Theorem t_walkstar_infer_deBruijn_subst[local]:
  t_wfs s ∧
 LENGTH ls = tvs ∧
 EVERY (check_t y {}) ls ∧
 (∀n. n < tvs ⇒ t_walkstar s (Infer_Tuvar n) = EL n ls)
 ⇒
  ((∀t.
  check_t tvs {} t
  ⇒
  t_walkstar s (infer_deBruijn_subst ls t) =
  t_walkstar s (infer_deBruijn_subst (GENLIST Infer_Tuvar tvs) t)) ∧
  (∀ts.
  EVERY (check_t tvs {}) ts
  ⇒
  MAP ((t_walkstar s) o (infer_deBruijn_subst ls)) ts =
  MAP ((t_walkstar s) o (infer_deBruijn_subst (GENLIST Infer_Tuvar
    tvs))) ts))
Proof
  strip_tac>>ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[check_t_def,infer_deBruijn_subst_alt]>>
  fs[EVERY_MEM,MEM_EL]
  >-
    metis_tac[t_walkstar_no_vars]
  >>
    fs[t_walkstar_eqn1,MAP_MAP_o,MAP_EQ_f]
QED

Theorem infer_deBruijn_subst_check_t[local]:
  EVERY (check_t tvs {}) ls
  ⇒
  (∀t.
  check_t (LENGTH ls) {} t
  ⇒
  check_t tvs {} (infer_deBruijn_subst ls t)) ∧
  (∀ts.
  EVERY (check_t (LENGTH ls) {}) ts
  ⇒
  EVERY (check_t tvs {}) (MAP (infer_deBruijn_subst ls) ts))
Proof
  strip_tac>>ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[check_t_def,infer_deBruijn_subst_alt]>>
  fs[EVERY_MEM,MEM_EL]>>
  metis_tac[]
QED

Theorem check_tscheme_inst_complete:
   !tvs_spec t_spec tvs_impl t_impl id.
    check_t tvs_impl {} t_impl ∧
    check_t tvs_spec {} t_spec ∧
    tscheme_approx 0 FEMPTY (tvs_spec,t_spec) (tvs_impl,t_impl) ⇒
    check_tscheme_inst id (tvs_spec,t_spec) (tvs_impl,t_impl)
Proof
  rw [tscheme_approx_def, check_tscheme_inst_def] >>
  fs [t_walkstar_FEMPTY] >>
  simp [st_ex_bind_def, init_state_def, init_infer_state_def,
    st_ex_return_def,
        add_constraint_def] >>
  simp[n_fresh_uvar_rw]>>
  imp_res_tac infer_deBruijn_subst_id2>>
  ntac 2 (pop_assum kall_tac)>>
  first_x_assum(qspec_then`GENLIST Infer_Tvar_db tvs_spec` mp_tac)>>
  qpat_abbrev_tac`ls = MAP (infer_deBruijn_subst A) B`>>
  rw[]>>fs[]>>rfs[]>>
  `EVERY (check_t tvs_spec {}) ls` by
    (fs[Abbr`ls`,EVERY_MAP,MAP_MAP_o,EVERY_MEM]>>
    rw[]>>
    match_mp_tac
      (infer_deBruijn_subst_check_t|>UNDISCH|>CONJUNCT1|>DISCH_ALL
      |>GEN_ALL|>(SIMP_RULE (srw_ss()) [PULL_FORALL,AND_IMP_INTRO]))>>
    CONJ_TAC>-
      fs[EVERY_GENLIST,check_t_def]>>
    fs[LENGTH_GENLIST])>>
  Q.ISPECL_THEN [`init_infer_state`,`[]:(infer_t,infer_t)
    alist`,`FEMPTY:num|->infer_t`,`MAP convert_t ls`,`tvs_spec`] mp_tac
    extend_multi_props>>
  impl_tac>-
    (fs[init_infer_state_def,pure_add_constraints_def]>>
    fs[t_wfs_def,EVERY_MAP,EVERY_MEM,Abbr`ls`]>>
    metis_tac[check_t_to_check_freevars])>>
  BasicProvers.LET_ELIM_TAC>>fs[init_infer_state_def]>>
  `targs = ls` by
    (fs[Abbr`targs`,MAP_MAP_o,MAP_EQ_ID]>>
    metis_tac[check_t_empty_unconvert_convert_id,EVERY_MEM])>>fs[]>>
  imp_res_tac (t_walkstar_infer_deBruijn_subst)>>
  ntac 3 (pop_assum kall_tac)>>
  pop_assum mp_tac>>
  ntac 8 (pop_assum kall_tac)>>
  simp[]>>
  disch_then (qspec_then`t_impl`mp_tac)>>
  qmatch_goalsub_abbrev_tac`t_unify A B C`>>
  strip_tac>>
  `∃D. t_unify A B C = SOME D` by
    (match_mp_tac (GEN_ALL eqs_t_unify)>>
    qexists_tac`s'`>>
    fs[markerTheory.Abbrev_def]>>
    rpt var_eq_tac>>
    fs[t_walkstar_FEMPTY,ETA_AX,t_wfs_def])>>
  fs[]
QED

Theorem check_weak_ienv_complete:
   !tenv_impl tenv_spec ienv_impl ienv_spec.
    weak_tenv tenv_impl tenv_spec ∧
    env_rel tenv_impl ienv_impl ∧
    env_rel tenv_spec ienv_spec
    ⇒
    check_weak_ienv ienv_impl ienv_spec
Proof
  rw [weak_tenv_def, check_weak_ienv_def, GSYM nsSub_compute_thm]
  >- (
    fs [namespaceTheory.nsSub_def, env_rel_def, env_rel_sound_def,
        lookup_var_def, env_rel_complete_def] >>
    rw [] >>
    rpt (first_x_assum drule) >>
    rw [] >>
    rpt (first_x_assum drule) >>
    rw [] >>
    fs [tscheme_inst2_def] >>
    PairCases_on `v2` >>
    rpt (first_x_assum drule) >>
    rw [] >>
    fs [] >>
    match_mp_tac check_tscheme_inst_complete>>
    fs[ienv_ok_def,ienv_val_ok_def]>>
    imp_res_tac nsLookup_nsAll>>
    rfs[]>>
    metis_tac [tscheme_approx_trans, tscheme_inst_to_approx]) >>
  fs [env_rel_def, env_rel_sound_def]
QED

Theorem check_weak_decls_complete:
   !idecls1 idecls2.
    weak_decls (convert_decls idecls1) (convert_decls idecls2)
    ⇒
    check_weak_decls idecls1 idecls2
Proof
  rw [weak_decls_def, check_weak_decls_def, convert_decls_def,
    SUBSET_DEF,
      list_subset_def, list_set_eq_def] >>
  fs [EVERY_MEM]
QED
*)
