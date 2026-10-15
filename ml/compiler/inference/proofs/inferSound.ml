(* ======================================================== *)
(*  inferSound: ported from HOL4's
    compiler/inference/proofs/inferSoundScript.sml  *)
(* ======================================================== *)

(*
  Proves soundness of the type inferencer: any type assignment
  produced by the type inferencer is a valid type for the program.
*)

needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/proofs/envRel.ml";;
needs "compiler/inference/proofs/infer_eComplete.ml";;
needs "compiler/inference/proofs/infer_eSound.ml";;
needs "compiler/inference/proofs/type_eDeterm.ml";;
needs "compiler/inference/unify.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

(* TODO: This should be generalized eventually *)

(* TODO: The generated set of type identifiers (tids)
  must be related to st2.next_id in some way
  The current relation might be wrong *)

(* the set of ids n1 .... n2-1 *)
let set_ids_def = cake_define
  `set_ids n1 (n2:num) = {m | n1 <= m /\ m < n2}`;;

(* HOL4 ML code, not ported:
fun str_tac strs = ConseqConv.CONSEQ_CONV_TAC
  (ConseqConv.CONSEQ_REWRITE_CONV ([], strs, []));
*)

(*
Theorem check_tscheme_inst_sound:
   !tvs_impl t_impl tvs_spec t_spec.
    check_t tvs_impl {} t_impl ∧
    check_t tvs_spec {} t_spec ∧
    check_tscheme_inst x (tvs_spec,t_spec) (tvs_impl,t_impl)
    ⇒
    tscheme_inst (tvs_spec, convert_t t_spec) (tvs_impl, convert_t
      t_impl)
Proof
  rw [check_tscheme_inst_def, tscheme_inst_def] >>
  every_case_tac >>
  fs [success_eqns] >>
  rw [] >>
  fs [init_state_def, init_infer_state_def] >>
  var_eq_tac >>
  fs [] >>
  `t_wfs FEMPTY` by rw [t_wfs_def] >>
  old_drule t_unify_apply >>
  disch_then old_drule >>
  rw [] >>
  old_drule t_unify_wfs >>
  disch_then old_drule >>
  strip_tac >>
  `t_walkstar s t_spec = t_spec` by metis_tac [t_walkstar_no_vars] >>
  fs [] >>
  rw [db_subst_infer_subst_swap2] >>
  rw [MAP_MAP_o, combinTheory.o_DEF] >>
  `?s'. ALL_DISTINCT (MAP FST s') ∧
     (FEMPTY |++ s' = FUN_FMAP (\x. Infer_Tapp [] Tc_int) (count
       tvs_impl DIFF FDOM s))`
    by metis_tac [fmap_to_list] >>
  `FINITE (count tvs_impl DIFF FDOM s)` by metis_tac [FINITE_COUNT,
    FINITE_DIFF] >>
  `t_wfs (s |++ s')`
    by (
      `t_vR s = t_vR (s |++ s')`
        by (
          rw [t_vR_eqn, FUN_EQ_THM] >>
          cases_on `FLOOKUP (s |++ s') x'` >>
          fs [flookup_update_list_none, flookup_update_list_some] >>
          cases_on `FLOOKUP s x'` >>
          fs [flookup_update_list_none, flookup_update_list_some] >>
          `FLOOKUP (FEMPTY |++ s') x' = SOME x''` by rw
            [flookup_update_list_some] >>
          pop_assum mp_tac >>
          rw [FLOOKUP_FUN_FMAP, t_vars_eqn] >>
          rw [FLOOKUP_FUN_FMAP, t_vars_eqn] >>
          fs [FLOOKUP_DEF]) >>
       fs [t_wfs_eqn]) >>
  qexists_tac `MAP (\n. convert_t (t_walkstar (s |++ s') (Infer_Tuvar
    n))) (COUNT_LIST tvs_impl)` >>
  rw [LENGTH_COUNT_LIST, check_t_to_check_freevars, EVERY_MAP] >>
  `FDOM (FEMPTY |++ s') = count tvs_impl DIFF FDOM s` by metis_tac
    [FDOM_FMAP] >>
  `check_s tvs_spec (count tvs_impl) s`
    by (
     old_drule t_unify_check_s >>
     simp [] >>
     disch_then irule >>
     simp [check_s_def, check_t_infer_db_subst2] >>
     metis_tac [check_t_more, check_t_more2, arithmeticTheory.ADD_COMM])
  >- (
    rw [EVERY_MEM] >>
    irule check_t_to_check_freevars >>
    irule t_walkstar_check >>
    simp [check_t_def, FDOM_FUPDATE_LIST]
    >> conj_tac >- (
      fs [check_s_def, fdom_fupdate_list2] >>
      rw [] >>
      rw [FUPDATE_LIST_APPLY_NOT_MEM] >>
      `count tvs_impl ⊆ FDOM s ∪ set (MAP FST s')` by rw [SUBSET_DEF]
      >- metis_tac [check_t_more5]
      >- metis_tac [check_t_more5] >>
      `FLOOKUP (s |++ s') uv = SOME ((s |++ s') ' uv)`
        by rw [FLOOKUP_DEF, FDOM_FUPDATE_LIST] >>
      fs [flookup_update_list_some]
      >- (
        imp_res_tac ALOOKUP_MEM >>
        fs[] >>
        imp_res_tac (GSYM mem_to_flookup) >>
        fs[] >>
        ntac 2 (pop_assum mp_tac) >>
        rw [FLOOKUP_FUN_FMAP] >>
        rw [check_t_def])
      >- (
        pop_assum mp_tac >>
        rw [FLOOKUP_DEF]))
    >- (
      fs [EXTENSION, MEM_COUNT_LIST] >>
      res_tac >>
      fs [FDOM_FUPDATE_LIST]))
  >- (
    imp_res_tac t_walkstar_no_vars >>
    fs [] >>
    rw [SIMP_RULE (srw_ss()) [MAP_MAP_o, combinTheory.o_DEF] (GSYM
      db_subst_infer_subst_swap2)] >>
    AP_TERM_TAC >>
    simp[MAP_GENLIST,COUNT_LIST_GENLIST,ETA_AX] >>
    match_mp_tac (SIMP_RULE (srw_ss()) [GSYM
      RIGHT_FORALL_IMP_THM,AND_IMP_INTRO] no_vars_extend_subst) >>
    rw []
    >- (
      rw [DISJOINT_DEF, EXTENSION] >>
      metis_tac [])
    >- (
      imp_res_tac check_t_t_vars  >>
      fs [EXTENSION, SUBSET_DEF, COUNT_LIST_GENLIST, MAP_GENLIST] >>
      metis_tac []))
QED

Theorem weak_tenv_ienv_to_tenv:
   !ienv1 ienv2.
    ienv_ok {} ienv1 ∧ ienv_ok {} ienv2 ∧
    check_weak_ienv ienv1 ienv2 ⇒ weak_tenv (ienv_to_tenv ienv1)
      (ienv_to_tenv ienv2)
Proof
  rw [check_weak_ienv_def, weak_tenv_def, ienv_to_tenv_def, GSYM
    nsSub_compute_thm] >>
  simp [nsSub_nsMap] >>
  fs [tscheme_inst2_def] >>
  irule nsSub_mono2 >>
  rw [] >>
  HINT_EXISTS_TAC >>
  rw [] >>
  pairarg_tac >>
  fs [] >>
  pairarg_tac >>
  fs [] >>
  rw [] >>
  fs [ienv_ok_def, ienv_val_ok_def] >>
  old_drule nsLookup_nsAll >>
  disch_then old_drule >>
  rw [] >>
  qpat_x_assum `nsAll _ ienv2.inf_v` mp_tac >>
  old_drule nsLookup_nsAll >>
  disch_then old_drule >>
  rw [] >>
  metis_tac [check_tscheme_inst_sound]
QED

Theorem weak_decls_ienv_to_tenv:
   !idecls1 idecls2.
    check_weak_decls idecls1 idecls2 ⇒ weak_decls (convert_decls
      idecls1) (convert_decls idecls2)
Proof
  rw [check_weak_decls_def, weak_decls_def, convert_decls_def,
    SUBSET_DEF,
      EVERY_MEM, list_subset_def, list_set_eq_def, EXTENSION] >>
  metis_tac []
QED

Theorem check_freevars_nub[local]:
  (!t x fvs.
  check_freevars x fvs t ⇒
  check_freevars x (nub fvs) t) ∧
 (!ts x fvs.
  EVERY (check_freevars x fvs) ts ⇒
  EVERY (check_freevars x (nub fvs)) ts)
Proof
  Induct >>
rw [check_freevars_def] >> metis_tac[]
QED

Theorem check_specs_sound[local]:
  !mn tenvT idecls1 ienv1 specs st1 idecls2 ienv2 st2.
    check_specs mn tenvT idecls1 ienv1 specs st1 = (M_success
      (idecls2,ienv2), st2) ∧
    tenv_abbrev_ok tenvT
    ⇒
    ?decls3 ienv3.
      type_specs mn tenvT specs decls3 (ienv_to_tenv ienv3) ∧
      convert_decls idecls2 = union_decls decls3 (convert_decls idecls1)
        ∧
      ienv2 = extend_dec_ienv ienv3 ienv1
Proof
  ho_match_mp_tac check_specs_ind >>
  rw [check_specs_def, success_eqns]
  >- (
    rw [Once type_specs_cases] >>
    qexists_tac `<|inf_v := nsEmpty; inf_c := nsEmpty; inf_t :=
      nsEmpty|>` >>
    rw [ienv_to_tenv_def, extend_dec_ienv_def,
      inf_env_component_equality])
  >- (
    first_x_assum old_drule >>
    rw [] >>
    qexists_tac `decls3` >>
    qmatch_assum_abbrev_tac
      `check_specs _ _ _ (ienv1 with inf_v := nsBind name new_binding
        ienv1.inf_v) _ _ = _` >>
    simp [Once type_specs_cases] >>
    qexists_tac `ienv3 with inf_v := nsAppend ienv3.inf_v (nsSing name
      new_binding)` >>
    rw [extend_dec_ienv_def, extend_dec_tenv_def, ienv_to_tenv_def,
      nsMap_nsAppend,
        nsAppend_nsSing]
    >- (
      HINT_EXISTS_TAC >>
      rw [ienv_to_tenv_def] >>
      unabbrev_all_tac >>
      fs [] >>
      qexists_tac `nub fvs` >>
      conj_asm2_tac
      >- (
        rpt AP_TERM_TAC >>
        old_drule check_freevars_type_name_subst >>
        disch_then old_drule >>
        disch_then old_drule >>
        rw [convert_t_subst, LENGTH_COUNT_LIST, MAP_MAP_o,
          combinTheory.o_DEF,
            convert_t_def, MAP_GENLIST, COUNT_LIST_GENLIST])
      >- metis_tac [t_to_freevars_check, check_freevars_nub])
    >- metis_tac [GSYM nsAppend_assoc, nsAppend_nsSing])
  >- (
    first_x_assum old_drule >>
    impl_tac
    >- (
      irule tenv_abbrev_ok_merge >>
      simp [] >>
      rw [typeSoundInvariantsTheory.tenv_abbrev_ok_def] >>
      irule nsAll_alist_to_ns >>
      simp [EVERY_MAP] >>
      rw [EVERY_MEM] >>
      pairarg_tac >>
      simp [] >>
      pairarg_tac >>
      simp [] >>
      pairarg_tac >>
      fs [] >>
      rw [check_freevars_def, EVERY_MAP, EVERY_MEM]) >>
    rw [] >>
    simp [Once type_specs_cases, PULL_EXISTS] >>
    qmatch_assum_abbrev_tac
      `check_specs _ _ _ <| inf_v := _;
                            inf_c := nsAppend new_ctors _;
                            inf_t := nsAppend new_tdefs _ |> _ _ = _` >>
    qexists_tac `extend_dec_ienv ienv3 <| inf_v := nsEmpty; inf_c :=
      new_ctors;
                                    inf_t := new_tdefs |>` >>
    qexists_tac `ienv_to_tenv ienv3` >>
    qexists_tac `decls3` >>
    rw [ienv_to_tenv_def, extend_dec_ienv_def, extend_dec_tenv_def] >>
    rw [union_decls_def, convert_decls_def] >>
    rw [EXTENSION] >>
    metis_tac [])
  >- (
    simp [Once type_specs_cases, PULL_EXISTS] >>
    first_x_assum (qspec_then `nsBind tn (tvs,type_name_subst tenvT t)
      nsEmpty` mp_tac) >>
    simp [] >>
    disch_then old_drule >>
    impl_tac
    >- (
      fs [typeSoundInvariantsTheory.tenv_abbrev_ok_def] >>
      irule nsAll_nsBind >>
      simp [] >>
      irule check_freevars_type_name_subst >>
      simp [typeSoundInvariantsTheory.tenv_abbrev_ok_def]) >>
    rw [] >>
    qmatch_assum_abbrev_tac
      `check_specs _ _ _ (ienv1 with inf_t := nsBind name new_t _) _ _ =
        _` >>
    qexists_tac `decls3` >>
    qexists_tac `ienv3 with inf_t := nsAppend ienv3.inf_t (nsSing name
      new_t)` >>
    qexists_tac `ienv_to_tenv ienv3` >>
    rw [ienv_to_tenv_def, extend_dec_ienv_def, extend_dec_tenv_def] >>
    metis_tac [nsAppend_nsSing, nsAppend_assoc])
  >- (
    first_x_assum old_drule >>
    rw [] >>
    simp [Once type_specs_cases, PULL_EXISTS] >>
    qmatch_assum_abbrev_tac
      `check_specs _ _ _ (ienv1 with inf_c := nsBind name new_binding
        ienv1.inf_c) _ _ = _` >>
    qexists_tac `ienv3 with inf_c := nsAppend ienv3.inf_c (nsSing name
      new_binding)` >>
    rw [extend_dec_ienv_def, extend_dec_tenv_def, ienv_to_tenv_def,
      nsMap_nsAppend,
        nsAppend_nsSing] >>
    qexists_tac `ienv_to_tenv ienv3` >>
    simp [] >>
    HINT_EXISTS_TAC >>
    rw [ienv_to_tenv_def, union_decls_def, convert_decls_def] >>
    metis_tac [GSYM nsAppend_assoc, nsAppend_nsSing, INSERT_SING_UNION,
      UNION_ASSOC])
  >- (
    simp [Once type_specs_cases, PULL_EXISTS] >>
    first_x_assum (qspec_then `nsBind tn (tvs,Tapp (MAP Tvar tvs)
      (TC_name (mk_id mn tn))) nsEmpty` mp_tac) >>
    simp [] >>
    disch_then old_drule >>
    impl_tac
    >- (
      fs [typeSoundInvariantsTheory.tenv_abbrev_ok_def] >>
      irule nsAll_nsBind >>
      simp [check_freevars_def, EVERY_MAP, EVERY_MEM]) >>
    rw [] >>
    qmatch_assum_abbrev_tac
      `check_specs _ _ _ (ienv1 with inf_t := nsBind name new_binding
        ienv1.inf_t) _ _ = _` >>
    qexists_tac `ienv3 with inf_t := nsAppend ienv3.inf_t (nsSing name
      new_binding)` >>
    qexists_tac `ienv_to_tenv ienv3` >>
    qexists_tac `decls3` >>
    simp [ienv_to_tenv_def, extend_dec_tenv_def, extend_dec_ienv_def,
          union_decls_def, convert_decls_def] >>
    metis_tac [GSYM nsAppend_assoc, nsAppend_nsSing, INSERT_SING_UNION,
      UNION_ASSOC])
QED

Theorem infer_top_sound:
   !idecls ienv t_op st1 idecls' ienv' st2 tenv.
    infer_top idecls ienv t_op st1 = (M_success (idecls',ienv'), st2) ∧
    env_rel tenv ienv
    ⇒
    type_top T (convert_decls idecls) tenv t_op (convert_decls idecls')
      (ienv_to_tenv ienv')
Proof
  rw [] >>
  Cases_on `t_op` >>
  fs [infer_top_def, success_eqns, type_top_cases] >>
  pairarg_tac >>
  fs []
  >- (
    fs [success_eqns] >>
    pairarg_tac >>
    fs [success_eqns] >>
    rpt var_eq_tac >>
    old_drule infer_ds_sound >>
    disch_then old_drule >>
    rw [] >>
    rename1 `check_signature _ ienv.inf_t _ idecls2 ienv2 sig st2 =
               (M_success (idecls3,ienv3), st3)` >>
    Cases_on `sig` >>
    fs [check_signature_def, typeSystemTheory.check_signature_cases,
        success_eqns]
    >- (
      rpt var_eq_tac >>
      qexists_tac `ienv_to_tenv ienv2` >>
      qexists_tac `convert_decls idecls2` >>
      rw [convert_decls_def, union_decls_def, GSYM INSERT_SING_UNION,
        ienv_to_tenv_lift]) >>
    pairarg_tac >>
    fs [success_eqns] >>
    rpt var_eq_tac >>
    qexists_tac `ienv_to_tenv ienv2` >>
    rename1 `check_weak_ienv _ ienv3` >>
    qexists_tac `ienv_to_tenv ienv3` >>
    qexists_tac `convert_decls idecls2` >>
    rename1 `check_weak_decls _ idecls3` >>
    qexists_tac `convert_decls idecls3` >>
    rw [ienv_to_tenv_lift]
    >- simp [convert_decls_def, union_decls_def, GSYM INSERT_SING_UNION]
    >- simp [convert_decls_def]
    >- (
      irule weak_tenv_ienv_to_tenv >>
      fs [env_rel_def]
      >> conj_tac >- metis_tac [infer_ds_check] >>
      old_drule infer_ds_check >>
      rw [] >>
      old_drule check_specs_check >>
      disch_then irule >>
      fs [ienv_ok_def, ienv_val_ok_def])
    >- metis_tac [weak_decls_ienv_to_tenv]
    >- (
      old_drule check_specs_sound >>
      fs [env_rel_def, ienv_ok_def] >>
      rw [] >>
      fs [convert_decls_def, empty_inf_decls_def, extend_dec_ienv_def,
          union_decls_def, ienv_to_tenv_def, env_rel_sound_def] >>
      `<|defined_mods := decls3.defined_mods;
         defined_types := decls3.defined_types;
         defined_exns := decls3.defined_exns|> = decls3`
        by rw [decls_component_equality] >>
      metis_tac []))
  >- (
    irule infer_d_sound >>
    rw [] >>
    fs [success_eqns] >>
    metis_tac [])
QED

Theorem infer_prog_sound:
   !idecls ienv prog st1 idecls' ienv' st2 tenv.
    infer_prog idecls ienv prog st1 = (M_success (idecls',ienv'), st2) ∧
    env_rel tenv ienv
    ⇒
    type_prog T (convert_decls idecls) tenv prog (convert_decls idecls')
      (ienv_to_tenv ienv')
Proof
  induct_on `prog` >>
  rw [infer_prog_def, success_eqns]
  >- rw [empty_decls_def,convert_decls_def, empty_inf_decls_def]
  >- rw [ienv_to_tenv_def] >>
  rw [Once type_prog_cases] >>
  pairarg_tac >>
  fs [success_eqns] >>
  pairarg_tac >>
  fs [success_eqns] >>
  rpt var_eq_tac >>
  old_drule infer_top_sound >>
  disch_then old_drule >>
  strip_tac >>
  rename1 `infer_top idecls1 ienv1 _ _ = (M_success (idecls2, ienv2),
    _)` >>
  rename1 `infer_prog _ _ _ _ = (M_success (idecls3, ienv3), _)` >>
  qexists_tac `ienv_to_tenv ienv2` >>
  qexists_tac `ienv_to_tenv ienv3` >>
  qexists_tac `convert_decls idecls2` >>
  qexists_tac `convert_decls idecls3` >>
  simp [ienv_to_tenv_extend, GSYM convert_append_decls] >>
  first_x_assum irule >>
  qexists_tac `extend_dec_ienv ienv2 ienv1` >>
  simp [] >>
  metis_tac [env_rel_extend, env_rel_ienv_to_tenv, env_rel_def,
  infer_top_invariant]
QED
*)
