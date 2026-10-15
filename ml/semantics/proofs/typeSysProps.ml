(* ======================================================== *)
(*  typeSysProps: ported from HOL4's
    semantics/proofs/typeSysPropsScript.sml  *)
(* ======================================================== *)

(*
  Theorems about the type system.
*)

needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

(* HOL4 ML code, not ported:
val find_recfun_def = semanticPrimitivesTheory.find_recfun_def;
*)
(*
val same_tid_def = semanticPrimitivesTheory.same_tid_def;
val check_dup_ctors_cons =
  semanticPrimitivesPropsTheory.check_dup_ctors_cons;
val no_dup_types_def = semanticPrimitivesTheory.no_dup_types_def;
val decs_to_types_def = semanticPrimitivesTheory.decs_to_types_def;
*)

(* HOL4 ML code, not ported:
val _ = export_rewrites [
  "typeSystem.Tarray_def",
  "typeSystem.Tbool_def",
  "typeSystem.Tchar_def",
  "typeSystem.Texn_def",
  "typeSystem.Tfn_def",
  "typeSystem.Tint_def",
  "typeSystem.Tlist_def",
  "typeSystem.Tref_def",
  "typeSystem.Tstring_def",
  "typeSystem.Ttup_def",
  "typeSystem.Tvector_def",
  "typeSystem.Tword64_def",
  "typeSystem.Tword8_def",
  "typeSystem.Tword8array_def",
  "typeSystem.Tdouble_def"]
*)

(* ----------- Basic stuff ----------- *)

 (*
Theorem union_decls_assoc[simp]:
 !decls1 decls2 decls3.
  union_decls decls1 (union_decls decls2 decls3)
  =
  union_decls (union_decls decls1 decls2) decls3
Proof
 srw_tac[][] >>
 srw_tac[][union_decls_def] >>
 metis_tac [UNION_ASSOC]
QED

Theorem union_decls_sym:
 !decls1 decls2. union_decls decls1 decls2 = union_decls decls2 decls1
Proof
 rw [union_decls_def] >>
 rw [UNION_COMM]
QED

Theorem union_decls_mods[simp]:
  (union_decls d1 d2).defined_mods = d1.defined_mods ∪ d2.defined_mods
Proof
 rw [union_decls_def]
QED

Theorem union_decls_empty[simp]:
   !d. union_decls empty_decls d = d ∧ union_decls d empty_decls = d
Proof
 rw [union_decls_def, decls_component_equality, empty_decls_def]
QED
 *)

let type_pes_def = cake_define
  `type_pes tvs tvs' tenv tenvE pes t1 t2 <=>
     (RES_FORALL (set_of_list pes) (\(p,e).
       ?bindings.
         ALL_DISTINCT (pat_bindings p) /\
         type_p tvs tenv p t1 bindings /\
         type_e tenv (bind_var_list tvs' bindings tenvE) e t2))`;;

(* ---------- check_freevars ---------- *)

(* ---------- type_subst ---------- *)

(* ---------- deBruijn_inc ---------- *)

(* ---------- deBruijn_subst ---------- *)

(* ---------- tenv_abbrev stuff ---------- *)

(* ---------- tenv_ctor stuff ----------*)

(* ---------- tenv_val_exp stuff ---------- *)

let deBruijn_subst_tenvE_def = cake_define_list
  [`deBruijn_subst_tenvE targs Empty = Empty`;
   `deBruijn_subst_tenvE targs (Bind_tvar tvs env) =
      Bind_tvar tvs (deBruijn_subst_tenvE targs env)`;
   `deBruijn_subst_tenvE targs (Bind_name x tvs t env) =
      Bind_name x tvs (deBruijn_subst (tvs + num_tvs env)
                              (MAP (deBruijn_inc 0 (tvs + num_tvs
                                env)) targs)
                              t)
           (deBruijn_subst_tenvE targs env)`];;

let db_merge_def = cake_define_list
  [`db_merge Empty e = e`;
   `db_merge (Bind_tvar tvs e1) e2 = Bind_tvar tvs (db_merge e1 e2)`;
   `db_merge (Bind_name x tvs t e1) e2 = Bind_name x tvs t (db_merge
  e1 e2)`];;

(* ---------- type_op ---------- *)

(* HOL4 ML code, not ported:
val op_thms = { nchotomy = op_nchotomy, case_def = op_case_def };
val list_thms = { nchotomy = list_nchotomy, case_def = list_case_def };
val t_thms = { nchotomy = t_nchotomy, case_def = t_case_def };
val word_size_thms = { nchotomy = word_size_nchotomy, case_def =
  word_size_case_def };
val id_thms = { nchotomy = id_nchotomy, case_def = id_case_def };
val thms = [ op_thms, list_thms, t_thms, word_size_thms, id_thms ];
val eqs = ([pair_case_eq,bool_case_eq]@(List.map TypeBase.case_eq_of
  [``:op``, ``:'a list``, ``:t``, ``:word_size``, ``:('a,'b) id``]));
val elims = List.map prove_case_elim_thm thms;
*)

(* ---------- type_p ---------- *)

(* ---------- type_e, type_es, type_funs ---------- *)

(* Recursive functions have function type *)

(* Recursive functions can be looked up in the execution environment. *)

(* Functions in the type environment can be found *)

(* No duplicate function definitions in a single let rec *)


 (*
(* ---------- tid_exn_to_tc ---------- *)

Theorem tid_exn_to_tc_11:
 !x y. (tid_exn_to_tc x = tid_exn_to_tc y) = same_tid x y
Proof
cases_on `x` >>
cases_on `y` >>
srw_tac[][tid_exn_to_tc_def, same_tid_def]
QED

Theorem tid_exn_not:
 (!tn. tid_exn_to_tc tn ≠ TC_int) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_char) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_string) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_ref) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_tup) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_fn) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_word8) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_word64) ∧
 (!tn wz. tid_exn_to_tc tn ≠ TC_word wz) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_word8array) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_vector) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_array)
Proof
 srw_tac[][] >>
 cases_on `tn` >>
 full_simp_tac(srw_ss())[tid_exn_to_tc_def] >>
 Cases_on`wz` \\ EVAL_TAC >>
 metis_tac []
QED
 *)

(* ---------- ctMap stuff ---------- *)


let type_def_to_ctMap_def = cake_define_list
  [`type_def_to_ctMap tenvT next_stamp [] [] = []`;
   `type_def_to_ctMap tenvT next_stamp ((tvs,tn,ctors) :: tds) (id' ::
  ids) =
        type_def_to_ctMap tenvT (next_stamp + 1) tds ids ++
        REVERSE
          (MAP (\(cn,ts).
            (TypeStamp cn next_stamp,(tvs,MAP (type_name_subst
              tenvT) ts,id')))
            ctors)`];;


 (*
Theorem ctMap_ok_type_decs:
  !mn tds. tenv_abbrev_ok tenvT ∧ check_ctor_tenv tenvT tds ⇒ ctMap_ok
    (type_decs_to_ctMap mn tenvT tds)
Proof
 rw [check_ctor_tenv_def, ctMap_ok_def, type_decs_to_ctMap_def,
   FEVERY_ALL_FLOOKUP, FUPDATE_LIST_alist_to_fmap]
 >> drule ALOOKUP_MEM
 >> simp [MEM_FLAT, MEM_MAP]
 >> pairarg_tac
 >> simp []
 >> pairarg_tac
 >> simp []
 >> rw []
 >> pairarg_tac
 >> fs [MEM_MAP]
 >> pairarg_tac
 >> fs []
 >> rw []
 >> fs [EVERY_MEM]
 >> first_x_assum drule
 >> pairarg_tac
 >> fs []
 >> rw []
 >> first_x_assum drule
 >> pairarg_tac
 >> fs []
 >> rw []
 >> fs [MEM_MAP]
 >> metis_tac [check_freevars_type_name_subst]
QED

Theorem consistent_ctMap_union:
  !tdecs1 tdecs2 ctMap1 ctMap2.
  consistent_ctMap tdecs1 ctMap1 ∧
  consistent_ctMap tdecs2 ctMap2
  ⇒
  consistent_ctMap (union_decls tdecs1 tdecs2) (FUNION ctMap1 ctMap2)
Proof
 rw [consistent_ctMap_def, RES_FORALL]
 >> pairarg_tac
 >> fs []
 >> CASE_TAC
 >> fs [union_decls_def]
 >> first_x_assum drule
 >> simp []
QED

Theorem consistent_ctMap_union2:
  !tdecs1 tdecs2 ctMap.
  consistent_ctMap tdecs2 ctMap
  ⇒
  consistent_ctMap (union_decls tdecs1 tdecs2) ctMap
Proof
 rw [consistent_ctMap_def, RES_FORALL]
 >> pairarg_tac
 >> fs []
 >> CASE_TAC
 >> fs [union_decls_def]
 >> first_x_assum drule
 >> simp []
QED

Theorem consistent_ctMap_disjoint:
 !mn (tds:type_def) (ctMap:ctMap) tdecs tabbrev.
  DISJOINT (set (MAP (λ(tvs,tn,ctors). mk_id mn tn) tds))
    tdecs.defined_types ∧
  consistent_ctMap tdecs ctMap
  ⇒
  DISJOINT (IMAGE SND (FDOM (type_decs_to_ctMap mn tabbrev tds))) (IMAGE
    SND (FDOM ctMap))
Proof
 rw [consistent_ctMap_def,
     type_decs_to_ctMap_def, RES_FORALL, FUPDATE_LIST_alist_to_fmap,
       DISJOINT_DEF,
     EXTENSION, MEM_MAP]
 >> rw [METIS_PROVE [] ``y ∨ x ⇔ ~y ⇒ x``]
 >> fs [MEM_FLAT, MEM_MAP]
 >> rw []
 >> pairarg_tac
 >> fs [MEM_MAP]
 >> rw []
 >> pairarg_tac
 >> fs []
 >> CCONTR_TAC
 >> fs []
 >> first_x_assum drule
 >> pairarg_tac
 >> fs []
 >> rw []
 >> fs [METIS_PROVE [] ``y ∨ x ⇔ ~y ⇒ x``, PULL_EXISTS]
 >> first_x_assum drule
 >> simp []
QED
 *)

 (*
Theorem check_ctor_tenv_type_decs_to_ctMap_lemma[local]:
  !tenvT tds mn tvs tn c cn ts.
    check_ctor_tenv tenvT (REVERSE tds) ∧
    MEM (tvs,tn,c) (REVERSE tds) ∧
    MEM (cn,ts) c
    ⇒
    FLOOKUP (type_decs_to_ctMap mn tenvT (REVERSE tds)) (cn, TypeId
      (mk_id mn tn)) = SOME (tvs, MAP (type_name_subst tenvT) ts)
Proof
  Induct_on `tds`
 >> rw [check_ctor_tenv_def]
 >> fs [MEM_MAP]
 >- (
   simp [type_decs_to_ctMap_def, flookup_fupdate_list, REVERSE_APPEND,
     ALOOKUP_APPEND]
   >> `ALL_DISTINCT (MAP FST (MAP (λ(cn,ts). ((cn,TypeId (mk_id mn
     tn)),tvs, MAP (type_name_subst tenvT) ts)) c))`
     by (
       rw [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
       >> fs [check_dup_ctors_thm, ALL_DISTINCT_APPEND]
       >> metis_tac [all_distinct_map_fst_lemma])
   >> simp [alookup_distinct_reverse]
   >> `ALOOKUP (MAP (λ(cn,ts).  ((cn,TypeId (mk_id mn tn)),tvs, MAP
     (type_name_subst tenvT) ts)) c)
               (cn,TypeId (mk_id mn tn)) = SOME (tvs,MAP
                 (type_name_subst tenvT) ts)`
     suffices_by rw []
   >> irule ALOOKUP_ALL_DISTINCT_MEM
   >> simp [MEM_MAP]
   >> qexists_tac `(cn,ts)`
   >> simp [])
 >- (
   fs [check_ctor_tenv_def, GSYM CONJ_ASSOC, ALL_DISTINCT_APPEND]
   >> `check_dup_ctors (REVERSE tds)` by fs [check_dup_ctors_thm,
     ALL_DISTINCT_APPEND]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [type_decs_to_ctMap_def, flookup_fupdate_list,
     ALOOKUP_APPEND, REVERSE_APPEND]
   >> pairarg_tac
   >> rw []
   >> fs []
   >> `ALOOKUP (REVERSE (MAP (λ(cn,ts). ((cn,TypeId (mk_id mn
     tn')),tvs', MAP (type_name_subst tenvT) ts)) ctors))
               (cn,TypeId (mk_id mn tn)) = NONE`
     suffices_by rw []
   >> fs [MEM_MAP]
   >> first_x_assum (qspec_then `(tvs,tn,c)` mp_tac)
   >> rw [ALOOKUP_NONE, MEM_MAP]
   >> rw [METIS_PROVE [] ``x ∨ y ⇔ ~x ⇒ y``]
   >> pairarg_tac
   >> fs [])
QED

Theorem check_ctor_tenv_type_decs_to_ctMap:
   !tenvT tds mn tvs tn c cn ts.
    check_ctor_tenv tenvT tds ∧
    MEM (tvs,tn,c) tds ∧
    MEM (cn,ts) c
    ⇒
    FLOOKUP (type_decs_to_ctMap mn tenvT tds) (cn, TypeId (mk_id mn tn))
      = SOME (tvs, MAP (type_name_subst tenvT) ts)
Proof
 metis_tac [REVERSE_REVERSE, check_ctor_tenv_type_decs_to_ctMap_lemma]
QED
 *)

(* ---------- consistent_decls ---------- *)

(*
Theorem consistent_decls_union:
  !defined_types1 defined_types2 tdecs1 tdecs2.
  consistent_decls defined_types1 tdecs1 ∧
  consistent_decls defined_types2 tdecs2
  ⇒
  consistent_decls (defined_types1 ∪ defined_types2) (union_decls tdecs1
    tdecs2)
Proof
 rw [consistent_decls_def, union_decls_def, RES_FORALL]
 >> CASE_TAC
 >> fs []
 >> first_x_assum drule
 >> rw []
 >> metis_tac []
QED

Theorem consistent_decls_union2:
  !defined_types tdecs1 tdecs2.
  consistent_decls defined_types tdecs2
  ⇒
  consistent_decls defined_types (union_decls tdecs1 tdecs2)
Proof
 rw [consistent_decls_def, union_decls_def, RES_FORALL]
 >> CASE_TAC
 >> fs []
 >> first_x_assum drule
 >> rw []
 >> metis_tac []
QED

Theorem consistent_decls_add_mod:
 !decls d mn.
  consistent_decls decls d
  ⇒
  consistent_decls decls (d with defined_mods := {mn} ∪ d.defined_mods)
Proof
 srw_tac[][consistent_decls_def, RES_FORALL] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 res_tac >>
 full_simp_tac(srw_ss())[]
QED
 *)

(* ---------- type_v  ---------- *)

(* HOL4 ML code, not ported:
val type_subst_lem1 =
(GEN_ALL o
 SIMP_RULE (srw_ss()++ARITH_ss) [] o
 Q.SPECL [`[]`, `t`, `0`, `targs`, `tvs`] o
 SIMP_RULE (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM])
check_freevars_subst;
*)

  (*
(* --------- decls_ok ------------ *)

Theorem decls_ok_union:
  ∀d1 d2.
  decls_ok d1 ∧
  decls_ok d2
  ⇒
  decls_ok (union_decls d1 d2)
Proof
 rw [decls_ok_def, union_decls_def, SUBSET_DEF, decls_to_mods_def,
   GSPECIFICATION]
 >> full_simp_tac (srw_ss()++DNF_ss) []
 >> metis_tac []
QED
 *)

(* ---------- type_d ---------- *)

 (*
Theorem type_d_mod:
 !uniq mn tdecs tenv d tdecs' new_tenv.
  type_d uniq mn tdecs tenv d tdecs' new_tenv
  ⇒
  tdecs'.defined_mods = {} ∧
  decls_to_mods tdecs' ⊆ { mn }
Proof
 srw_tac[][type_d_cases, decls_to_mods_def, SUBSET_DEF,
   FDOM_FUPDATE_LIST] >>
 full_simp_tac(srw_ss())[build_ctor_tenv_def, MEM_FLAT, MEM_MAP] >>
 srw_tac[][empty_decls_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[EXISTS_PROD, empty_decls_def,
   decls_to_mods_def, mk_id_def, MEM_MAP] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[GSPECIFICATION] >>
 TRY (PairCases_on `y`) >>
 full_simp_tac(srw_ss())[]
QED
 *)

(* ---------- type_ds ---------- *)

 (*
Theorem type_ds_mod:
 !uniq mn tdecs tenv ds tdecs' new_tenv.
  type_ds uniq mn tdecs tenv ds tdecs' new_tenv
  ⇒
  tdecs'.defined_mods = {} ∧
  decls_to_mods tdecs' ⊆ {mn}
Proof
 induct_on `ds` >>
 srw_tac[][Once type_ds_cases]
 >- srw_tac[][decls_to_mods_def, empty_decls_def, SUBSET_DEF,
   FDOM_FUPDATE_LIST, MEM_MAP]
 >- srw_tac[][decls_to_mods_def, empty_decls_def, SUBSET_DEF,
   FDOM_FUPDATE_LIST, MEM_MAP] >>
 imp_res_tac type_d_mod >>
 res_tac >>
 full_simp_tac(srw_ss())[] >>
 full_simp_tac(srw_ss())[union_decls_def, decls_to_mods_def] >>
 rpt (pop_assum mp_tac) >>
 ONCE_REWRITE_TAC [SUBSET_DEF] >>
 REWRITE_TAC [GSPECIFICATION] >>
 rw_tac (bool_ss) [] >>
 metis_tac []
QED
 *)

 (*
Theorem type_ds_no_dup_types_helper[local]:
  !uniq mn decls tenv ds decls' tenv'.
  type_ds uniq mn decls tenv ds decls' tenv'
  ⇒
  DISJOINT decls.defined_types decls'.defined_types ∧
  decls'.defined_types =
  set (FLAT (MAP (λd.
                case d of
                  Dlet _ v6 v7 => []
                | Dletrec _ v8 => []
                | Dtabbrev _ x y z => []
                | Dtype _ tds => MAP (λ(tvs,tn,ctors). mk_id mn tn) tds
                | Dexn _ v10 v11 => []) ds))
Proof
  induct_on `ds` >>
 srw_tac[][empty_decls_def] >>
 pop_assum (assume_tac o SIMP_RULE (srw_ss()) [Once
   type_ds_cases,EXISTS_PROD]) >>
 full_simp_tac(srw_ss())[empty_decls_def,EXISTS_PROD
   ,extend_dec_tenv_def] >>
 TRY(PairCases_on`decls''''`)>>
 TRY(PairCases_on`decls'''`)>>
 srw_tac[][] >>
 every_case_tac >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[type_d_cases] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[empty_decls_def, union_decls_def] >>
 srw_tac[][] >>
 res_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[DISJOINT_DEF, EXTENSION] >>
 metis_tac []
QED

Theorem type_ds_no_dup_types:
 !uniq mn decls tenv ds decls' tenv'.
  type_ds uniq mn decls tenv ds decls' tenv'
  ⇒
  no_dup_types ds
Proof
 induct_on `ds` >>
 srw_tac[][no_dup_types_def, decs_to_types_def] >>
 pop_assum (assume_tac o SIMP_RULE (srw_ss()) [Once type_ds_cases]) >>
 full_simp_tac(srw_ss())[EXISTS_PROD,extend_dec_tenv_def] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[no_dup_types_def, type_d_cases,
   decs_to_types_def] >>
 srw_tac[][ALL_DISTINCT_APPEND]
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- full_simp_tac(srw_ss())[check_ctor_tenv_def, LAMBDA_PROD]
 >- metis_tac []
 >- (full_simp_tac(srw_ss())[union_decls_def] >>
     imp_res_tac type_ds_no_dup_types_helper >>
     full_simp_tac(srw_ss())[DISJOINT_DEF, EXTENSION, METIS_PROVE [] ``P
       ∨ Q ⇔ ¬P ⇒ Q``] >>
     pop_assum kall_tac >>
     pop_assum (qspec_then `mk_id mn e` mp_tac) >>
     `MEM (mk_id mn e) (MAP (λ(tvs,tn,ctors). mk_id mn tn) tdefs)`
               by (full_simp_tac(srw_ss())[MEM_MAP] >>
                   qexists_tac `y` >>
                   srw_tac[][] >>
                   PairCases_on `y` >>
                   srw_tac[][]) >>
     simp [] >>
     rpt (pop_assum (fn _ => all_tac)) >>
     srw_tac[][MEM_FLAT, MEM_MAP] >>
     CCONTR_TAC >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[MEM_MAP] >>
     srw_tac[][] >>
     rename [`MEM (Dtype locs l) ds`] >>
     FIRST_X_ASSUM (qspecl_then [`MAP (mk_id mn o FST o SND) l`] mp_tac)
       >>
     srw_tac[][]
     >- (qexists_tac `Dtype locs l` >>
         srw_tac[][LAMBDA_PROD, combinTheory.o_DEF])
     >- (srw_tac[][combinTheory.o_DEF, MEM_MAP, EXISTS_PROD] >>
         srw_tac[][LAMBDA_PROD] >>
         rename [`UNCURRY _ y`] >>
         PairCases_on `y` >>
         full_simp_tac(srw_ss())[] >>
         metis_tac []))
 >- metis_tac []
 >- metis_tac []
QED

Theorem type_ds_decls_ok:
  !mn tenv decls' tenv' ds tdecs_no_sig.
  type_ds F mn tdecs_no_sig tenv ds decls' tenv' ∧
  mn ≠ []
  ⇒
  decls_ok (union_decls <|defined_mods := {mn}; defined_types := ∅;
    defined_exns := ∅ |> decls')
Proof
 rw [decls_ok_def, union_decls_def]
 >> imp_res_tac type_ds_mod
 >> full_simp_tac (srw_ss()++DNF_ss) [decls_to_mods_def, SUBSET_DEF,
   GSPECIFICATION]
 >> rw []
 >> fs [weak_decls_def, SUBSET_DEF]
QED
 *)

(* ---------- type_specs ---------- *)

(*
Theorem type_specs_tenv_ok:
   !mn tenvT specs decls' tenv'.
    type_specs mn tenvT specs decls' tenv' ⇒
    tenv_abbrev_ok tenvT
    ⇒
    tenv_ok tenv'
Proof
 ho_match_mp_tac type_specs_ind
 >> rw []
 >- (
   irule extend_dec_tenv_ok
   >> simp []
   >> rw [tenv_ok_def, tenv_val_ok_def]
   >> irule check_freevars_subst_single
   >> simp [EVERY_MAP, EVERY_GENLIST, check_freevars_def]
   >> irule check_freevars_type_name_subst
   >> simp []
   >> metis_tac [check_freevars_add, DECIDE ``x ≥ 0n``])
 >- (
   match_mp_tac extend_dec_tenv_ok
   >> simp [Once CONJ_SYM]
   >> simp [Once tenv_ok_def, GSYM CONJ_ASSOC]
   >> simp [Once CONJ_SYM]
   >> simp [GSYM CONJ_ASSOC]
   >> conj_asm1_tac
   >- (
     fs [tenv_abbrev_ok_def]
     >> irule nsAll_alist_to_ns
     >> simp [EVERY_MAP, EVERY_MEM]
     >> rw []
     >> pairarg_tac
     >> simp []
     >> rpt (pairarg_tac >> fs [])
     >> rw [check_freevars_def, EVERY_MAP, EVERY_MEM])
   >> rw []
   >- (
     first_x_assum irule
     >> fs [tenv_abbrev_ok_def]
     >> irule nsAll_nsAppend
     >> metis_tac [])
   >- (
     irule check_ctor_tenv_ok
     >> simp [tenv_abbrev_ok_def]
     >> irule nsAll_nsAppend
     >> fs [tenv_abbrev_ok_def]))
 >- (
   `tenv_abbrev_ok (nsAppend (nsSing tn (tvs,type_name_subst tenvT t))
     tenvT)`
     by (
       fs [tenv_abbrev_ok_def]
       >> irule nsAll_nsBind
       >> simp []
       >> irule check_freevars_type_name_subst
       >> simp [tenv_abbrev_ok_def])
   >> fs []
   >> irule extend_dec_tenv_ok
   >> simp [tenv_ok_def, tenv_abbrev_ok_def]
   >> irule check_freevars_type_name_subst
   >> simp [tenv_abbrev_ok_def])
 >- (
   fs []
   >> irule extend_dec_tenv_ok
   >> simp [tenv_ok_def, tenv_ctor_ok_def, EVERY_MAP]
   >> fs [check_exn_tenv_def]
   >> fs [EVERY_MEM]
   >> rw []
   >> first_x_assum drule
   >> first_x_assum drule
   >> rw []
   >> irule check_freevars_type_name_subst
   >> simp [])
 >- (
   `tenv_abbrev_ok (nsSing tn (tvs,Tapp (MAP Tvar tvs) (TC_name (mk_id
     mn tn))))`
     by simp [tenv_abbrev_ok_def, check_freevars_def, EVERY_MEM,
       EVERY_MAP]
   >> irule extend_dec_tenv_ok >> conj_tac
   >- (
     first_x_assum irule
     >> simp [tenv_abbrev_ok_def]
     >> irule nsAll_nsBind
     >> simp [check_freevars_def, EVERY_MAP, EVERY_MEM]
     >> fs [tenv_abbrev_ok_def])
   >> simp [tenv_ok_def]
   >> fs [tenv_abbrev_ok_def])
QED

Theorem type_specs_no_mod:
 !mn tenvT specs decls' new_tenv.
  type_specs mn tenvT specs decls' new_tenv ⇒
  decls'.defined_mods = {}
Proof
 ho_match_mp_tac type_specs_strongind >>
 srw_tac[][empty_decls_def] >>
 imp_res_tac type_d_mod >>
 full_simp_tac(srw_ss())[union_decls_def]
QED

Theorem check_signature_tenv_ok:
  !mn tenv decls tenv' specs decls' tenv'' ds tdecs1 tenvT''.
   check_signature [mn] tenvT'' decls tenv' specs decls' tenv'' ∧
   type_ds F [mn] tdecs1 tenv ds decls tenv' ∧
   tenv_ok tenv ∧
   tenvT'' = tenv.t
   ⇒
   tenv_ok (extend_dec_tenv <| v := nsLift mn tenv''.v; c := nsLift mn
     tenv''.c; t := nsLift mn tenv''.t |> tenv)
Proof
 rw [check_signature_cases]
 >- (
   drule type_ds_tenv_ok_helper
   >> rw []
   >> irule extend_dec_tenv_ok
   >> simp []
   >> fs [tenv_ok_def, tenv_ctor_ok_def, tenv_val_ok_def,
     tenv_abbrev_ok_def])
 >- (
   drule type_specs_tenv_ok
   >> rw []
   >> irule extend_dec_tenv_ok
   >> simp []
   >> fs [tenv_ok_def, tenv_ctor_ok_def, tenv_val_ok_def,
     tenv_abbrev_ok_def])
QED
   *)

(* ---------------- type_top, type_prog ---------- *)
(*

Theorem type_prog_empty[simp]:
  !u mn decls tenv decls' r.
  type_prog u decls tenv [] decls' r ⇔ decls' = empty_decls ∧ r = <| v
    := nsEmpty; c := nsEmpty; t := nsEmpty |>
Proof
 rw [Once type_prog_cases]
QED

Theorem type_prog_sing[simp]:
  !u mn decls tenv d decls' r.
  type_prog u decls tenv [d] decls' r ⇔ type_top u decls tenv d decls' r
Proof
 simp [Once type_prog_cases] >>
 rw [] >>
 eq_tac >>
 rw [extend_dec_tenv_def]
QED

Theorem type_top_check_uniq:
 !uniq tdecs tenv top tdecs' new_tenv.
  type_top uniq tdecs tenv top tdecs' new_tenv
  ⇒
  type_top F tdecs tenv top tdecs' new_tenv
Proof
 srw_tac[][type_top_cases] >>
 metis_tac [type_d_check_uniq, type_ds_check_uniq]
QED

Theorem type_prog_check_uniq:
 !uniq tdecs tenv prog tdecs' new_tenv.
  type_prog uniq tdecs tenv prog tdecs' new_tenv
  ⇒
  type_prog F tdecs tenv prog tdecs' new_tenv
Proof
 ho_match_mp_tac type_prog_ind >>
 srw_tac[][] >>
 srw_tac[][Once type_prog_cases] >>
 metis_tac [type_top_check_uniq]
QED

Theorem type_top_decls_ok:
 !uniq tdecs tenv top tdecs' new_tenv.
  type_top uniq tdecs tenv top tdecs' new_tenv
  ⇒
  decls_ok tdecs'
Proof
 rw [type_top_cases]
 >> simp [decls_ok_def]
 >- (
   drule type_d_mod
   >> simp_tac (srw_ss()++DNF_ss) [SUBSET_DEF, decls_to_mods_def,
     SUBSET_DEF, GSPECIFICATION])
 >- (
   rw [union_decls_mods]
   >> fs [union_decls_def, check_signature_cases]
   >> rw []
   >> TRY (drule type_ds_mod)
   >> TRY (drule type_specs_no_mod)
   >> simp_tac (srw_ss()++DNF_ss) [SUBSET_DEF, decls_to_mods_def,
     SUBSET_DEF, GSPECIFICATION]
   >> rw []
   >> fs [weak_decls_def, SUBSET_DEF])
QED

Theorem type_prog_decls_ok:
 !uniq tdecs tenv prog tdecs' new_tenv.
  type_prog uniq tdecs tenv prog tdecs' new_tenv
  ⇒
  decls_ok tdecs'
Proof
 ho_match_mp_tac type_prog_ind >>
 srw_tac[][] >>
 srw_tac[][Once type_prog_cases]
 >- simp [decls_ok_def, empty_decls_def, decls_to_mods_def]
 >> irule decls_ok_union
 >> simp []
 >> metis_tac [type_top_decls_ok]
QED

Theorem type_no_dup_top_types_lem[local]:
  !uniq decls1 tenv prog decls1' res.
  type_prog uniq decls1 tenv prog decls1' res
  ⇒
  ALL_DISTINCT (prog_to_top_types prog) ∧
  DISJOINT decls1.defined_types (IMAGE (mk_id []) (set
    (prog_to_top_types prog)))
Proof
  ho_match_mp_tac type_prog_ind >>
 srw_tac[][semanticPrimitivesTheory.prog_to_top_types_def] >>
 every_case_tac >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[type_top_cases] >>
 srw_tac[][ALL_DISTINCT_APPEND, empty_decls_def]
 >- (full_simp_tac(srw_ss())[type_d_cases,
   semanticPrimitivesTheory.decs_to_types_def] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[check_ctor_tenv_def] >>
     full_simp_tac(srw_ss())[LAMBDA_PROD])
 >- (`mk_id [] e ∈ decls1'.defined_types`
            by (full_simp_tac(srw_ss())[type_d_cases,
              semanticPrimitivesTheory.decs_to_types_def] >>
                srw_tac[][] >>
                full_simp_tac(srw_ss())[mk_id_def] >>
                full_simp_tac(srw_ss())[MEM_MAP, LAMBDA_PROD,
                  EXISTS_PROD] >>
                metis_tac []) >>
     full_simp_tac(srw_ss())[union_decls_def, DISJOINT_DEF, EXTENSION]
       >>
     metis_tac [])
 >- (srw_tac[][semanticPrimitivesTheory.decs_to_types_def] >>
     full_simp_tac(srw_ss())[type_d_cases] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[DISJOINT_DEF, EXTENSION] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[MEM_MAP,LAMBDA_PROD, EXISTS_PROD,
       mk_id_def, FORALL_PROD] >>
     metis_tac [])
 >- (full_simp_tac(srw_ss())[union_decls_def, DISJOINT_DEF, EXTENSION]
   >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[MEM_MAP,LAMBDA_PROD, EXISTS_PROD,
       mk_id_def, FORALL_PROD] >>
     metis_tac [])
 >- (full_simp_tac(srw_ss())[type_d_cases, empty_decls_def] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[DISJOINT_DEF, EXTENSION, union_decls_def]
       >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[MEM_MAP,LAMBDA_PROD, EXISTS_PROD,
       mk_id_def, FORALL_PROD] >>
     metis_tac [])
QED

Theorem type_no_dup_top_types_lem2[local]:
  !uniq decls1 tenv prog decls1' tenv'.
  type_prog uniq decls1 tenv prog decls1' tenv'
  ⇒
  no_dup_top_types prog (IMAGE TypeId decls1.defined_types)
Proof
  srw_tac[][semanticPrimitivesTheory.no_dup_top_types_def]
 >- metis_tac [type_no_dup_top_types_lem] >>
 imp_res_tac type_no_dup_top_types_lem >>
 full_simp_tac(srw_ss())[DISJOINT_DEF, EXTENSION] >>
 srw_tac[][] >>
 cases_on `x` >>
 srw_tac[][MEM_MAP] >>
 full_simp_tac(srw_ss())[mk_id_def] >>
 metis_tac []
QED

Theorem type_no_dup_top_types:
 !decls1 tenv prog decls1' tenv' uniq decls2 decls_no_sig.
  type_prog uniq decls1 tenv prog decls1' tenv' ∧
  consistent_decls decls2 decls_no_sig ∧
  weak_decls_only_mods decls_no_sig decls1
  ⇒
  no_dup_top_types prog decls2
Proof
 srw_tac[][] >>
 `no_dup_top_types prog (IMAGE TypeId decls1.defined_types)`
         by metis_tac [type_no_dup_top_types_lem2] >>
 full_simp_tac(srw_ss())[semanticPrimitivesTheory.no_dup_top_types_def]
   >>
 full_simp_tac(srw_ss())[RES_FORALL, DISJOINT_DEF, SUBSET_DEF,
   EXTENSION, weak_decls_only_mods_def, consistent_decls_def] >>
 srw_tac[][] >>
 CCONTR_TAC >>
 full_simp_tac(srw_ss())[] >>
 res_tac >>
 every_case_tac >>
 full_simp_tac(srw_ss())[MEM_MAP] >>
 srw_tac[][] >>
 metis_tac []
QED

Theorem type_no_dup_mods_lem[local]:
  !uniq decls1 tenv prog decls1' res.
  type_prog uniq decls1 tenv prog decls1' res
  ⇒
  ALL_DISTINCT (prog_to_mods prog) ∧
  DISJOINT decls1.defined_mods (set (prog_to_mods prog))
Proof
  ho_match_mp_tac type_prog_ind >>
 srw_tac[][semanticPrimitivesTheory.prog_to_mods_def] >>
 every_case_tac >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[type_top_cases] >>
 srw_tac[][ALL_DISTINCT_APPEND, empty_decls_def]
 >- (full_simp_tac(srw_ss())[union_decls_def, DISJOINT_DEF, EXTENSION]
   >>
     metis_tac [])
 >- (full_simp_tac(srw_ss())[union_decls_def, DISJOINT_DEF, EXTENSION]
   >>
     metis_tac [])
 >- (full_simp_tac(srw_ss())[union_decls_def, DISJOINT_DEF, EXTENSION]
   >>
     metis_tac [])
QED

Theorem type_no_dup_mods:
 !uniq decls1 tenv prog decls1' tenv'.
  type_prog uniq decls1 tenv prog decls1' tenv'
  ⇒
  no_dup_mods prog decls1.defined_mods
Proof
 srw_tac[][semanticPrimitivesTheory.no_dup_mods_def] >>
 metis_tac [type_no_dup_mods_lem, DISJOINT_SYM]
QED

 *)
 (*

(* closed *)

Overload tmenv_dom =
  ``λmenv. {Long m x | (m,x) | ∃e.  FLOOKUP menv m = SOME e ∧ MEM x (MAP
    FST e)}``

open boolSimps semanticPrimitivesPropsTheory

Definition tenv_names_def[simp]:
  (tenv_names Empty = {}) ∧
  (tenv_names (Bind_tvar _ e) = tenv_names e) ∧
  (tenv_names (Bind_name n _ _ e) = n INSERT tenv_names e)
End

Theorem lookup_tenv_names:
   ∀tenv n inc x. lookup_tenv_val n inc tenv = SOME x ⇒ n ∈ tenv_names
     tenv
Proof
  Induct >> simp[lookup_tenv_val_def] >> metis_tac[]
QED

Theorem tenv_names_bind_var_list:
   ∀n l1 l2. tenv_names (bind_var_list n l1 l2) = set (MAP FST l1) ∪
     tenv_names l2
Proof
  ho_match_mp_tac bind_var_list_ind >>
  simp[bind_var_list_def,EXTENSION] >>
  metis_tac[]
QED

Theorem tenv_names_bind_var_list2:
   ∀l1 tenv. tenv_names (bind_var_list2 l1 tenv) = set (MAP FST l1) ∪
     tenv_names tenv
Proof
  Induct >> TRY(qx_gen_tac`p`>>PairCases_on`p`) >>
    simp[bind_var_list2_def] >>
  simp[EXTENSION] >> metis_tac[]
QED

Theorem type_p_closed[local]:
  (∀tvs tcenv p t tenv.
       type_p tvs tcenv p t tenv ⇒
       pat_bindings p = MAP FST tenv) ∧
    (∀tvs cenv ps ts tenv.
      type_ps tvs cenv ps ts tenv ⇒
      pats_bindings ps = MAP FST tenv)
Proof
  ho_match_mp_tac type_p_ind >>
  srw_tac[][astTheory.pat_bindings_def] >>
  full_simp_tac(srw_ss())[]
QED

Theorem type_funs_dom[local]:
  !tenv funs tenv'.
    type_funs tenv funs tenv'
    ⇒
    IMAGE FST (set funs) = IMAGE FST (set tenv')
Proof
  Induct_on `funs` >>
   srw_tac[][Once type_e_cases] >>
   srw_tac[][] >>
   metis_tac []
QED

Theorem type_e_closed[local]:
  (∀tenv e t.
      type_e tenv e t
      ⇒
      FV e ⊆ (IMAGE Short (tenv_names tenv.v) ∪ tmenv_dom tenv.m)) ∧
    (∀tenv es ts.
      type_es tenv es ts
      ⇒
      FV_list es ⊆ (IMAGE Short (tenv_names tenv.v) ∪ tmenv_dom tenv.m))
        ∧
    (∀tenv funs ts.
      type_funs tenv funs ts ⇒
      FV_defs funs ⊆ (IMAGE Short (tenv_names tenv.v)) ∪ tmenv_dom
        tenv.m)
Proof
  ho_match_mp_tac type_e_strongind >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- (
    simp[RES_FORALL_THM,FORALL_PROD,tenv_names_bind_var_list] >>
    rpt gen_tac >> strip_tac >>
    simp[FV_pes_MAP] >>
    simp_tac(srw_ss()++DNF_ss)[SUBSET_DEF,UNCURRY,FORALL_PROD,MEM_MAP]
      >>
    srw_tac[][] >> res_tac >>
    qmatch_assum_rename_tac`MEM (p1,p2) pes` >>
    first_x_assum(qspecl_then[`p1`,`p2`]mp_tac) >>
    simp[EXISTS_PROD] >> disch_then(Q.X_CHOOSE_THEN`tv`strip_assume_tac)
      >>
    imp_res_tac type_p_closed >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,EXISTS_PROD,FORALL_PROD] >>
      metis_tac[] ) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    imp_res_tac alistTheory.ALOOKUP_MEM >>
    simp[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    imp_res_tac alistTheory.ALOOKUP_MEM >>
    simp[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[t_lookup_var_id_def] >>
    rpt gen_tac >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    simp[MEM_FLAT,MEM_MAP,EXISTS_PROD] >-
      metis_tac[lookup_tenv_names] >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    simp_tac(srw_ss()++DNF_ss)[MEM_MAP,EXISTS_PROD] >>
    srw_tac[][] >>
    imp_res_tac ALOOKUP_MEM >>
    metis_tac [] ) >>
  strip_tac >- (
    simp[] >>
    srw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[] ) >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- (
    simp[RES_FORALL_THM,FORALL_PROD,tenv_names_bind_var_list] >>
    rpt gen_tac >> strip_tac >>
    simp[FV_pes_MAP] >>
    simp_tac(srw_ss()++DNF_ss)[SUBSET_DEF,UNCURRY,FORALL_PROD,MEM_MAP]
      >>
    srw_tac[][] >> res_tac >>
    qmatch_assum_rename_tac`MEM (p1,p2) pes` >>
    first_x_assum(qspecl_then[`p1`,`p2`]mp_tac) >>
    simp[EXISTS_PROD] >> disch_then(Q.X_CHOOSE_THEN`tv`strip_assume_tac)
      >>
    imp_res_tac type_p_closed >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,EXISTS_PROD,FORALL_PROD] >>
      metis_tac[]) >>
  strip_tac >- (
    simp[] >>
    srw_tac[DNF_ss][SUBSET_DEF,bind_tvar_def] >>
    every_case_tac >>
    full_simp_tac(srw_ss())[opt_bind_name_def] >>
    metis_tac[] ) >>
    (* COMPLETENESS
  strip_tac >- (
    simp[] >>
    srw_tac[DNF_ss][SUBSET_DEF,bind_tvar_def] >>
    every_case_tac >>
    full_simp_tac(srw_ss())[opt_bind_name_def] >>
    metis_tac[] ) >> *)
  strip_tac >- (
    simp[tenv_names_bind_var_list] >>
    rpt gen_tac >> strip_tac >>
    imp_res_tac type_funs_dom >>
    full_simp_tac(srw_ss())[SUBSET_DEF] >>
    srw_tac[][] >>
    res_tac >>
    full_simp_tac(srw_ss())[MEM_MAP] >>
    `tenv_names (bind_tvar tvs tenv.v) = tenv_names tenv.v`
               by (srw_tac[][bind_tvar_def] >>
                   every_case_tac >>
                   full_simp_tac(srw_ss())[tenv_names_def]) >>
    full_simp_tac(srw_ss())[] >>
    srw_tac[][] >>
    res_tac >>
    full_simp_tac(srw_ss())[] >>
    srw_tac[][] >>
    full_simp_tac(srw_ss())[EXTENSION] >>
    metis_tac []) >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  simp[] >>
  srw_tac[][SUBSET_DEF] >>
  res_tac >>
  fsrw_tac[DNF_ss][MEM_MAP,FV_defs_MAP,UNCURRY] >>
  srw_tac[][] >>
  metis_tac []
QED

Theorem type_d_closed[local]:
  ∀uniq mno decls tenv d w x.
      type_d uniq mno decls tenv d w x ⇒
        FV_dec d ⊆ (IMAGE Short (tenv_names tenv.v) ∪ tmenv_dom tenv.m)
Proof
  ho_match_mp_tac type_d_ind >>
  strip_tac >- (
    simp[bind_tvar_def] >>
    rpt gen_tac >>
    Cases_on`tvs=0`>>simp[]>>strip_tac>>
    imp_res_tac (CONJUNCT1 type_e_closed) >> full_simp_tac(srw_ss())[])
      >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    imp_res_tac (CONJUNCT1 type_e_closed) >> full_simp_tac(srw_ss())[])
      >>
  strip_tac >- (
    srw_tac[][] >>
    imp_res_tac (CONJUNCT2 type_e_closed) >>
    full_simp_tac(srw_ss())[tenv_names_bind_var_list,LET_THM] >>
    `tenv_names (bind_tvar tvs tenv.v) = tenv_names tenv.v`
              by (srw_tac[][bind_tvar_def] >>
                  every_case_tac >>
                  srw_tac[][tenv_names_def]) >>
    full_simp_tac(srw_ss())[SUBSET_DEF] >>
    srw_tac[][] >>
    full_simp_tac(srw_ss())[MEM_MAP] >>
    res_tac >>
    srw_tac[][] >>
    imp_res_tac type_funs_dom >>
    full_simp_tac(srw_ss())[EXTENSION] >>
    metis_tac[]) >>
  simp[]
QED

  (*
Theorem type_d_new_dec_vs[local]:
  !uniq mn decls tenv d decls' new_tenv.
    type_d uniq mn decls tenv d decls' new_tenv
    ⇒
    set (new_dec_vs d) = set (MAP FST tenv')
Proof
  srw_tac[][type_d_cases, new_dec_vs_def] >>
   srw_tac[][new_dec_vs_def] >>
   imp_res_tac type_p_closed >>
   srw_tac[][tenv_add_tvs_def, MAP_MAP_o, combinTheory.o_DEF,
     LAMBDA_PROD] >>
   full_simp_tac(srw_ss())[LET_THM, LIST_TO_SET_MAP, FST_pair,
     IMAGE_COMPOSE] >>
   metis_tac [type_funs_dom]
QED
   *)

   (*
Theorem type_ds_closed[local]:
  ∀uniq mn decls tenv ds w x. type_ds uniq mn decls tenv ds w x ⇒
     !mn'. mn = SOME mn' ⇒
      FV_decs ds ⊆ (IMAGE Short (tenv_names tenv.v) ∪ tmenv_dom tenv.m)
Proof
  ho_match_mp_tac type_ds_ind >>
  srw_tac[][FV_decs_def] >>
  imp_res_tac type_d_closed >>
  full_simp_tac(srw_ss())[tenv_names_bind_var_list2] >>
  srw_tac[][SUBSET_DEF] >>
  `x ∈ IMAGE Short (set (MAP FST tenv')) ∪ IMAGE Short (tenv_names
    tenv.v) ∪ tmenv_dom tenv.m`
           by full_simp_tac(srw_ss())[SUBSET_DEF] >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[MEM_MAP] >>
  metis_tac [type_d_new_dec_vs,MEM_MAP]
QED
  *)

  (*
Theorem type_top_closed:
   ∀uniq decls tenv top decls' new_tenv.
      type_top uniq decls tenv top decls' new_tenv
      ⇒
      FV_top top ⊆ (IMAGE Short (tenv_names tenv.v) ∪ tmenv_dom tenv.m)
Proof
  ho_match_mp_tac type_top_ind >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    metis_tac [type_d_closed]) >>
  simp[] >>
  rpt gen_tac >> strip_tac >>
  imp_res_tac type_ds_closed >>
  full_simp_tac(srw_ss())[]
QED
  *)

Theorem type_env_dom[local]:
  !ctMap tenvS env tenv.
    type_env ctMap tenvS env tenv ⇒
    IMAGE Short (set (MAP FST env)) = IMAGE Short (tenv_names tenv)
Proof
  induct_on `env` >>
   ONCE_REWRITE_TAC [typeSoundInvariantsTheory.type_v_cases] >>
   full_simp_tac(srw_ss())[tenv_names_def] >>
   full_simp_tac(srw_ss())[tenv_names_def] >>
   srw_tac[][] >>
   srw_tac[][] >>
   metis_tac []
QED

Theorem weakM_dom[local]:
  !tenvM1 tenvM2.
    weakM tenvM1 tenvM2
    ⇒
    tmenv_dom tenvM2 ⊆ tmenv_dom tenvM1
Proof
  srw_tac[][weakM_def, SUBSET_DEF] >>
   res_tac >>
   srw_tac[][] >>
   full_simp_tac(srw_ss())[weakE_def] >>
   qpat_x_assum `!x. P x` (mp_tac o Q.SPEC `x'`) >>
   every_case_tac >>
   full_simp_tac(srw_ss())[ALOOKUP_FAILS] >>
   srw_tac[][] >>
   imp_res_tac ALOOKUP_MEM >>
   full_simp_tac(srw_ss())[MEM_MAP] >>
   metis_tac [FST, pair_CASES]
QED

Theorem type_env_dom2[local]:
  !ctMap tenvS env tenv.
    type_env ctMap tenvS env (bind_var_list2 tenv Empty) ⇒
    (set (MAP FST env) = set (MAP FST tenv))
Proof
  induct_on `env` >>
   ONCE_REWRITE_TAC [typeSoundInvariantsTheory.type_v_cases] >>
   full_simp_tac(srw_ss())[bind_var_list2_def, tenv_names_def] >>
   full_simp_tac(srw_ss())[tenv_names_def] >>
   srw_tac[][] >>
   srw_tac[][] >>
   cases_on `tenv` >>
   TRY (PairCases_on `h`) >>
   full_simp_tac(srw_ss())[bind_var_list2_def] >>
   metis_tac []
QED

Theorem consistent_mod_env_dom[local]:
  !tenvS tenvC envM tenvM.
    consistent_mod_env tenvS tenvC envM tenvM
    ⇒
    (tmenv_dom tenvM = {Long m x | ∃e. ALOOKUP envM m = SOME e ∧ MEM x
      (MAP FST e)})
Proof
  induct_on `envM` >>
   srw_tac[][]
   >- (Cases_on `tenvM` >>
       full_simp_tac(srw_ss())[Once type_v_cases]) >>
   pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
   srw_tac[][] >>
   res_tac >>
   srw_tac[][] >>
   imp_res_tac type_env_dom2 >>
   full_simp_tac(srw_ss())[EXTENSION, FLOOKUP_UPDATE] >>
   srw_tac[][] >>
   eq_tac >>
   srw_tac[][] >>
   every_case_tac >>
   srw_tac[][] >>
   full_simp_tac(srw_ss())[MEM_MAP] >>
   srw_tac[][] >>
   res_tac >>
   full_simp_tac(srw_ss())[] >>
   metis_tac []
QED
   *)

   (*
Theorem type_sound_inv_closed:
   ∀uniq top rs new_tenvM new_tenvC new_tenv new_decls new_tenvT decls'
     store.
    type_top uniq rs.tdecs rs.tenvT rs.tenvM rs.tenvC rs.tenv top
      new_decls new_tenvT new_tenvM new_tenvC new_tenv ∧
    type_sound_invariants NONE
      (rs.tdecs,rs.tenvT,rs.tenvM,rs.tenvC,rs.tenv,decls',rs.sem_env
      ,store)
    ⇒
    FV_top top ⊆ all_env_dom
      (rs.sem_env.sem_envM,rs.sem_env.sem_envC,rs.sem_env.sem_envE)
Proof
  srw_tac[][] >>
  imp_res_tac type_top_closed >>
  `(?err. r = Rerr err) ∨ (?menv env. r = Rval (menv,env))`
          by (cases_on `r` >>
              srw_tac[][] >>
              PairCases_on `a` >>
              full_simp_tac(srw_ss())[])  >>
  full_simp_tac(srw_ss())[all_env_dom_def, type_sound_invariants_def,
    update_type_sound_inv_def] >>
  srw_tac[][] >>
  imp_res_tac weakM_dom >>
  imp_res_tac type_env_dom >>
  imp_res_tac (GSYM consistent_mod_env_dom) >>
  full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[SUBSET_DEF] >>
  metis_tac []
QED
  *)
