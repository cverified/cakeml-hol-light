(* ======================================================== *)
(*  infer_eSound: ported from HOL4's
    compiler/inference/proofs/infer_eSoundScript.sml  *)
(* ======================================================== *)

(*
  Prove soundness of the type inferencer for the expression-level.
*)

needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/proofs/envRel.ml";;
needs "compiler/inference/unify.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* ---------- sub_completion ---------- *)

(* ---------- Soundness ---------- *)

(* HOL4 ML code, not ported:
val binop_tac =
 imp_res_tac infer_e_wfs >>
 imp_res_tac t_unify_wfs >>
 fsrw_tac[] [] >>
 imp_res_tac sub_completion_unify2 >>
 imp_res_tac sub_completion_infer >>
 fsrw_tac[] [] >>
 res_tac >>
 fsrw_tac[] [] >>
 imp_res_tac t_unify_apply >>
 imp_res_tac sub_completion_apply >>
 imp_res_tac t_unify_wfs >>
 imp_res_tac sub_completion_wfs >>
 fsrw_tac[] [t_walkstar_eqn, t_walk_eqn, convert_t_def,
   deBruijn_inc_def, check_t_def] >>
 srw_tac[] [type_op_cases, Tint_def, Tstring_def, Tref_def, Tfn_def,
   Texn_def, Tchar_def,word_tc_cases] >>
 metis_tac [MAP, infer_e_next_uvar_mono, check_env_more,
   word_size_nchotomy];
*)

(* HOL4 ML code, not ported:
val log_tac =
 ( (* Log *)
   imp_res_tac t_unify_wfs
   >> imp_res_tac infer_e_wfs
   >> imp_res_tac sub_completion_wfs
   >> `t_wfs s` by metis_tac []
   >> rw [t_walkstar_eqn1, convert_t_def]
   >> NO_TAC)
 ORELSE
 ( (* Log *)
   imp_res_tac (CONJUNCT1 infer_e_wfs)
   >> fs []
   >> imp_res_tac t_unify_wfs
   >> fs []
   >> first_x_assum drule
   >> first_x_assum drule
   >> rename1 `infer_e _ _ e _ = (M_success t1, st1)`
   >> rename1 `infer_e _ _ e1 st1 = (M_success t2, st2)`
   >> `ienv_ok (count st1.next_uvar) ienv` by metis_tac [ienv_ok_more,
     infer_e_next_uvar_mono]
   >> simp []
   >> disch_then drule
   >> strip_tac
   >> disch_then drule
   >> strip_tac
   >> rename1 `t_unify s1 _ _ = SOME s2`
   >> `t_walkstar s1 t1 = t_walkstar s1 (Infer_Tapp [] Tbool_num)`
     by (irule t_unify_apply >> metis_tac [])
   >> `t_walkstar s2 t2 = t_walkstar s2 (Infer_Tapp [] Tbool_num)`
     by (irule t_unify_apply >> metis_tac [])
   >> fs []
   >> drule sub_completion_unify2
   >> disch_then drule
   >> strip_tac
   >> qpat_x_assum `t_unify _ _ _ = _` mp_tac
   >> drule sub_completion_unify2
   >> disch_then drule
   >> rw []
   >> imp_res_tac sub_completion_infer
   >> first_x_assum drule
   >> first_x_assum drule
   >> imp_res_tac sub_completion_apply
   >> `t_wfs s` by metis_tac [sub_completion_wfs]
   >> simp [t_walkstar_eqn1, convert_t_def]);
*)
