(* ======================================================== *)
(*  weakening: ported from HOL4's
    semantics/proofs/weakeningScript.sml  *)
(* ======================================================== *)

(*
  Weakening lemmas used in type soundness
*)

needs "semantics/ast.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
(* HOL4 ancestors outside the port: option rich_list alist *)

let weak_tenvE_def = cake_define
  `weak_tenvE tenv tenv' =
     (num_tvs tenv >= num_tvs tenv' /\
      (!n inc tvs t.
       (tveLookup n inc tenv' = SOME (tvs,t)) <=>
       (tveLookup n inc tenv = SOME (tvs,t))))`;;

let weakS_def = cake_define
  `weakS tenvS tenvS' <=> tenvS' SUBMAP tenvS`;;

(*
Theorem weak_tenvT_refl:
   ∀n x. weak_tenvT n x x
Proof
 rw []
 >> PairCases_on `x`
 >> rw [weak_tenvT_def]
QED
 *)

      (*
Theorem weakE_lookup[local]:
  !n env env' tvs t.
  weakE env' env ∧
  (ALOOKUP env n = SOME (tvs, t))
  ⇒
  ?tvs' t' subst.
    (ALOOKUP env' n = SOME (tvs', t')) ∧
    check_freevars tvs' [] t' ∧
    (LENGTH subst = tvs') ∧
    EVERY (check_freevars tvs []) subst ∧
    (deBruijn_subst 0 subst t' = t)
Proof
  rw [weakE_def] >>
 qpat_x_assum `!cn. P cn` (MP_TAC o Q.SPEC `n`) >>
 rw [] >>
 every_case_tac >>
 fs [] >>
 metis_tac []
QED

Theorem weak_tenvM_lookup_lem[local]:
  !tvs.
  EVERY (λx. check_freevars tvs [] (Tvar_db x)) (COUNT_LIST tvs)
Proof
  Induct >>
rw [COUNT_LIST_def, check_freevars_def, EVERY_MAP] >>
fs [check_freevars_def]
QED

Theorem weak_tenvM_lookup[local]:
  !mn tenvM tenvM' tenv tenv' tvs t.
  weakM tenvM' tenvM ∧
  FLOOKUP tenvM mn = SOME tenv
  ⇒
  ?tenv'.
    FLOOKUP tenvM' mn = SOME tenv' ∧
    weakE tenv' tenv
Proof
  rw [weakM_def]
QED

 *)

let weak_def = cake_define
  `weak tenv' tenv <=> type_env_t
     tenv' = type_env_t tenv /\ weak_tenv tenv' tenv`;;

let weakCT_def = cake_define
  `weakCT cenv_impl cenv_spec <=> cenv_spec SUBMAP cenv_impl`;;

 (*
Definition weakCT_only_other_mods_def:
weakCT_only_other_mods mn ctMap' ctMap =
  !cn tn.
    ((cn,tn) ∈ FDOM ctMap' ∧ (cn,tn) ∉ FDOM ctMap)
    ⇒
    (?mn' x. mn ≠ SOME mn' ∧ (tn = TypeId (Long mn' x) ∨ tn = TypeExn
      (Long mn' x)))
End

Theorem weakCT_only_other_mods_merge[local]:
  !mn ctMap1 ctMap2 ctMap3.
  weakCT_only_other_mods mn ctMap2 ctMap3
  ⇒
  weakCT_only_other_mods mn (FUNION ctMap1 ctMap2) (FUNION ctMap1
    ctMap3)
Proof
  rw [weakCT_only_other_mods_def] >>
metis_tac []
QED

Theorem weak_decls_only_mods_union:
 !decls1 decls2 decls3.
  weak_decls_only_mods decls2 decls3
  ⇒
  weak_decls_only_mods (union_decls decls1 decls2) (union_decls decls1
    decls3)
Proof
 rw [] >>
 fs [weak_decls_only_mods_def, union_decls_def] >>
 metis_tac []
QED

Theorem weak_decls_only_mods_union2:
 !decls1 decls2 decls3 decls1'.
  weak_decls_only_mods decls1 decls1' ∧
  weak_decls_only_mods decls2 decls3
  ⇒
  weak_decls_only_mods (union_decls decls1 decls2) (union_decls decls1'
    decls3)
Proof
 rw [] >>
 fs [weak_decls_only_mods_def, union_decls_def] >>
 metis_tac []
QED

Theorem weak_decls_refl:
 !decls. weak_decls decls decls
Proof
 rw [weak_decls_def]
QED

Theorem weak_decls_trans:
 !decls1 decls2 decls3.
  weak_decls decls1 decls2 ∧
  weak_decls decls2 decls3
  ⇒
  weak_decls decls1 decls3
Proof
 rw [] >>
 fs [weak_decls_def, SUBSET_DEF]
QED

Definition weak_decls_other_mods_def:
weak_decls_other_mods mn d' d ⇔
  (!tid. tid ∈ d'.defined_types ∧ tid ∉ d.defined_types ⇒ ¬?tn. tid =
    mk_id mn tn) ∧
  (!cid. cid ∈ d'.defined_exns ∧ cid ∉ d.defined_exns ⇒ ¬?cn. cid =
    mk_id mn cn)
End

Theorem weak_decls_other_mods_refl:
 !mn decls. weak_decls_other_mods mn decls decls
Proof
 rw [] >>
 rw [weak_decls_other_mods_def]
QED
 *)

   (*
Theorem weak_decls_union:
 !decls1 decls2 decls3.
  weak_decls decls1 decls2
  ⇒
  weak_decls (union_decls decls3 decls1) (union_decls decls3 decls2)
Proof
 rw [] >>
 fs [weak_decls_def, union_decls_def, SUBSET_DEF] >>
 metis_tac []
QED

Theorem weak_decls_union:
 !decls1 decls2 decls3.
  weak_decls decls1 decls2
  ⇒
  weak_decls (union_decls decls3 decls1) (union_decls decls3 decls2)
Proof
 rw [] >>
 fs [weak_decls_def, union_decls_def, SUBSET_DEF] >>
 metis_tac []
QED

Theorem weak_decls_union2:
 !decls1 decls2 decls3.
  decls1.defined_mods = {}
  ⇒
  weak_decls (union_decls decls1 decls2) decls2
Proof
 rw [] >>
 fs [weak_decls_def, union_decls_def, SUBSET_DEF]
QED

Theorem weak_decls_union3:
 !decls1 decls2 decls3.
  weak_decls decls1 decls2
  ⇒
  weak_decls (union_decls decls1 decls3) (union_decls decls2 decls3)
Proof
 rw [] >>
 fs [weak_decls_def, union_decls_def, SUBSET_DEF] >>
 metis_tac []
QED

Theorem weak_decls_other_mods_union:
 !mn decls1 decls2 decls3.
  weak_decls_other_mods mn decls1 decls2
  ⇒
  weak_decls_other_mods mn (union_decls decls3 decls1) (union_decls
    decls3 decls2)
Proof
 rw [] >>
 fs [weak_decls_other_mods_def, union_decls_def] >>
 metis_tac []
QED

Theorem weak_decls_other_mods_only_mods_NIL:
 weak_decls_only_mods tdecs_no_sig tdecs1 ∧
 weak_decls tdecs_no_sig tdecs1
 ⇒
 weak_decls_other_mods [] tdecs_no_sig tdecs1
Proof
 fs [weak_decls_only_mods_def, weak_decls_other_mods_def,
   weak_decls_def, namespaceTheory.mk_id_def]
 >> metis_tac []
QED

Theorem weak_decls_other_mods_only_mods_SOME:
 decls_ok tdecs_no_sig ∧
 mn ≠ [] ∧
 mn ∉ tdecs1.defined_mods ∧
 weak_decls tdecs_no_sig tdecs1
 ⇒
 weak_decls_other_mods mn tdecs_no_sig tdecs1
Proof
 fs [weak_decls_only_mods_def, weak_decls_other_mods_def,
   weak_decls_def,
     namespaceTheory.mk_id_def, decls_ok_def, decls_to_mods_def,
       SUBSET_DEF]
 >> fsrw_tac[boolSimps.DNF_ss][decls_to_mods_def,GSPECIFICATION]
 >> rw []
 >> rw [METIS_PROVE [] ``¬x ∨ y ⇔ x ⇒ y``]
 >> res_tac
 >> fs [id_to_mods_mk_id]
 >> metis_tac []
QED

Theorem type_ds_weak_decls_only_mods:
  !mn tdecs_no_sig tenv ds decls tenv' decls'.
  type_ds F mn tdecs_no_sig tenv ds decls tenv' ∧
  mn ≠ []
  ⇒
  weak_decls_only_mods decls decls'
Proof
 rw [weak_decls_only_mods_def]
 >> drule type_ds_mod
 >> srw_tac [DNF_ss] [decls_to_mods_def, SUBSET_DEF, GSPECIFICATION]
 >> res_tac
 >> fs [namespaceTheory.id_to_mods_def]
QED

Theorem weak_tenv_extend_dec_tenv:
   !tenv1 tenv2 tenv3.
    tenv_val_ok tenv1.v ∧
    weak_tenv tenv2 tenv3 ⇒
    weak_tenv (extend_dec_tenv tenv1 tenv2) (extend_dec_tenv tenv1
      tenv3)
Proof
 rw []
 >> drule weak_tenv_refl
 >> fs [weak_tenv_def, extend_dec_tenv_def]
 >> rw []
 >> irule nsSub_nsAppend2
 >> simp []
QED

Theorem type_ds_weakening:
  !uniq mn decls tenv ds decls' tenv'.
   type_ds uniq mn decls tenv ds decls' tenv' ⇒
   !decls'' tenv''.
   uniq = F ∧
   weak_decls decls'' decls ∧
   weak_decls_other_mods mn decls'' decls ∧
   tenv_ok tenv'' ∧
   weak tenv'' tenv
   ⇒
   type_ds F mn decls'' tenv'' ds decls' tenv'
Proof
  ho_match_mp_tac type_ds_ind >>
  rw [] >>
  rw [Once type_ds_cases] >>
  imp_res_tac type_d_weakening >>
  rename1 `weak_decls decls2 decls'` >>
  first_x_assum (qspec_then `union_decls decls1 decls2` mp_tac)
  >> rw []
  >> qexists_tac `tenv1`
  >> qexists_tac `tenv'`
  >> qexists_tac `decls1`
  >> qexists_tac `decls''`
  >> rw []
  >> pop_assum irule >> rpt conj_tac
  >- metis_tac [extend_dec_tenv_ok, type_d_tenv_ok]
  >- (
    fs [weak_def]
    >> rw []
    >- rw [extend_dec_tenv_def]
    >> irule weak_tenv_extend_dec_tenv
    >> simp []
    >> drule type_d_tenv_ok_helper
    >> rw [tenv_ok_def])
  >- metis_tac [weak_decls_union]
  >- metis_tac [weak_decls_other_mods_union]
QED
 *)

  (*
Theorem consistent_decls_weakening:
 !decls1 decls2 decls3.
  consistent_decls decls1 decls3 ∧
  weak_decls decls2 decls3
  ⇒
  consistent_decls decls1 decls2
Proof
 rw [] >>
 fs [consistent_decls_def, RES_FORALL, weak_decls_def] >>
 rw [] >>
 every_case_tac >>
 fs [SUBSET_DEF] >>
 res_tac >>
 fs []
QED

Theorem consistent_ctMap_weakening:
 !ctMap tdecls tdecls'.
  consistent_ctMap tdecls ctMap ∧
  weak_decls tdecls' tdecls
  ⇒
  consistent_ctMap tdecls' ctMap
Proof
 rw [] >>
 fs [weak_decls_def, consistent_ctMap_def, RES_FORALL] >>
 rw [] >>
 PairCases_on `x` >>
 rw [] >>
 every_case_tac >>
 fs [] >>
 res_tac >>
 fs [SUBSET_DEF]
QED
 *)
