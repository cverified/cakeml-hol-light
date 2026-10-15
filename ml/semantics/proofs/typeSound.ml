(* ======================================================== *)
(*  typeSound: ported from HOL4's
    semantics/proofs/typeSoundScript.sml  *)
(* ======================================================== *)

(*
  Proof of type soundness: a type-correct program does not crash.
*)

needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/primSemEnv.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/proofs/weakening.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/semantics.ml";;
needs "semantics/typeSystem.ml";;

(* HOL4 ML code, not ported:
val type_num_defs = LIST_CONJ [
    Tarray_num_def,
    Tbool_num_def,
    Tchar_num_def,
    Texn_num_def,
    Tfn_num_def,
    Tint_num_def,
    Tlist_num_def,
    Tref_num_def,
    Tstring_num_def,
    Ttup_num_def,
    Tvector_num_def,
    Tword64_num_def,
    Tword8_num_def,
    Tword8array_num_def,
    Tdouble_num_def];
*)

(* Classifying values of basic types *)

(* HOL4 ML code, not ported:
val type_v_exn = SIMP_RULE (srw_ss()) [] (Q.prove (
                                           `!tvs cenv senv.
                                             ctMap_has_exns cenv ⇒
                                           type_v tvs cenv senv (Conv
                                             (SOME chr_stamp) []) Texn ∧
                                           type_v tvs cenv senv (Conv
                                             (SOME subscript_stamp) [])
                                             Texn ∧
                                           type_v tvs cenv senv (Conv
                                             (SOME bind_stamp) []) Texn
                                             ∧
                                           type_v tvs cenv senv (Conv
                                             (SOME div_stamp) []) Texn`,
                                                  ONCE_REWRITE_TAC
                                                    [type_v_cases] >>
                                           srw_tac[][ctMap_has_exns_def]
                                             >>
                                           metis_tac [type_v_rules]));
*)

let store_type_extension_def = cake_define
  `store_type_extension tenvS1 tenvS2 =
   (?tenvS'. (tenvS2 = FUNION tenvS' tenvS1) /\
            (!l. (FLOOKUP tenvS' l = NONE) \/ (FLOOKUP tenvS1 l =
              NONE)))`;;

(*
Theorem store_lookup_type_sound:
  !ctMap tenvS store n st.
  type_s ctMap store tenvS ∧
  FLOOKUP tenvS n = SOME st
  ⇒
  ?sv.
    store_lookup n store = SOME sv ∧
    type_sv ctMap tenvS sv st
Proof
 rw [type_s_def]
 >> metis_tac []
QED

*)

(* HOL4 ML code, not ported:
val pat_sound_tac =
 CCONTR_TAC >>
 full_simp_tac(srw_ss())[Once type_v_cases, Once type_p_cases,
   lit_same_type_def] >>
 srw_tac[][] >>
 imp_res_tac type_funs_Tfn >>
 imp_res_tac nsAll2_nsLookup2 >>
 fs [prim_type_nums_def, type_num_defs, ctMap_ok_def] >>
 TRY (rename1 `type_ctor _ _ v _` >> PairCases_on `v` >> Cases_on `v1`)
   >>
 fs [type_ctor_def] >>
 TRY (rename1 `FLOOKUP _ stamp = SOME _` >> Cases_on `stamp`) >>
 fs [] >>
 res_tac >>
 rw [] >>
 fs [] >>
 NO_TAC;
*)

(* TODO: Move *)

(* HOL4 ML code, not ported:
val let_tac =
  rw []
  >> Cases_on `r1`
  >> fs []
  >> rw []
  >- ( (* a value *)
    `type_all_env ctMap tenvS'' env tenv`
      by metis_tac [good_ctMap_def, type_all_env_weakening, weakCT_refl,
        store_type_extension_weakS]
    >> fs [good_ctMap_def, type_all_env_def]
    >> drule (CONJUNCT1 pat_type_sound)
    >> rpt (disch_then drule)
    >> disch_then (qspecl_then [`[]`, `[]`] mp_tac)
    >> rw []
    >- ( (* No match *)
      qexists_tac `ctMap`
      >> qexists_tac `tenvS''`
      >> rw [weakCT_refl, type_v_exn, bind_exn_v_def] >>
      metis_tac [consistent_ctMap_def])
    >- ( (* match *)
      qexists_tac `ctMap`
      >> qexists_tac `tenvS''`
      >> simp [weakCT_refl]
      >> simp [extend_dec_env_def, extend_dec_tenv_def]
      >> fs []
      >> conj_asm1_tac
      >- (
        irule nsAll2_alist_to_ns
        >> fs [tenv_add_tvs_def, EVERY2_MAP, LAMBDA_PROD])
      >> conj_asm1_tac
      >- metis_tac [consistent_ctMap_def]
      >> irule nsAll2_nsAppend
      >> simp []))
  >- ( (* An exception *)
    Cases_on `e'`
    >> fs []
    >- (
      qexists_tac `ctMap`
      >> qexists_tac `tenvS''`
      >> fs [weakCT_refl, type_all_env_def, good_ctMap_def]
      >> conj_tac
      >- metis_tac [consistent_ctMap_def]
      >> irule nsAll2_mono
      >> qexists_tac `(λi v (tvs,t). type_v tvs ctMap tenvS v t)`
      >> rw []
      >> pairarg_tac
      >> fs []
      >> metis_tac [weakCT_refl, type_v_weakening,
        store_type_extension_weakS])
    >- metis_tac [DIFF_EQ_EMPTY, weakCT_refl]);
*)
