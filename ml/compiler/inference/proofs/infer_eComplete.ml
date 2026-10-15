(* ======================================================== *)
(*  infer_eComplete: ported from HOL4's
    compiler/inference/proofs/infer_eCompleteScript.sml  *)
(* ======================================================== *)

(*
  Prove completeness of the type inferencer for the expression-level.
*)

needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/proofs/envRel.ml";;
needs "compiler/inference/unify.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

(*Useful lemmas about pure add constraints, some of these imply the
   others*)

(*t_compat is preserved over certain types of pure_add_constraints*)

(*If pure add constraints succeeds then the constraints all unify*)

(*behaves like a function if the first 2 arguments are equal*)

(*1 direction is sufficient to imply the other*)

(* HOL4 ML code, not ported:
val pure_add_constraints_swap = GEN_ALL pure_add_constraints_swap;
*)

(*End pure_add_constraints stuff*)

(*Can't find a version of this in the right direction*)

(*Ignore increment on deBrujin vars*)

(*Adding a list of keys that did not already exist is safe*)

(*t_compat preserves all grounded (no unification variable after walk)
   terms*)

(*Remove every uvar in the FDOM if we walkstar using a completed map*)

(*Double sided t_compat thm*)

(*Free properties when extending the completed map with uvar->ground
   var*)

(*This occurs when looking up a list updated fmap*)
(* HOL4 ML code, not ported:
val ALOOKUP_lemma = GEN_ALL (prove(
``
  n<LENGTH ls ⇒
  ALOOKUP (REVERSE (ZIP ((MAP (\n. offset + n) (COUNT_LIST (LENGTH
    ls))),ls))) (offset+n)
  = SOME (EL n ls)``,
  rw[]>>
  qmatch_abbrev_tac `ALOOKUP (REVERSE L) k = SOME Y`>>
  Q.ISPECL_THEN [`L`,`k`] mp_tac alookup_distinct_reverse>>
  impl_keep_tac>-
    (rw[Abbr`L`,MAP_ZIP,LENGTH_COUNT_LIST]>>
    match_mp_tac ALL_DISTINCT_MAP_INJ>>
    fs[all_distinct_count_list])>>
  rw[]>>
  unabbrev_all_tac>>
  match_mp_tac ALOOKUP_ALL_DISTINCT_MEM>>fs[]>>
  fs[MEM_ZIP,LENGTH_COUNT_LIST]>>HINT_EXISTS_TAC>>
  fs[EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST]));
*)

(*Useful tactics, mainly for constrain_op*)

(* HOL4 ML code, not ported:
val unconversion_tac =
  rpt (qpat_x_assum `convert_t A = B` (assume_tac o (Q.AP_TERM
    `unconvert_t`)))>>
  imp_res_tac check_t_empty_unconvert_convert_id>>
  fs[unconvert_t_def];
*)

(* HOL4 ML code, not ported:
fun pure_add_constraints_combine_tac ls =
  case ls of [st,constraints,s]
  =>
    (`pure_add_constraints ^(st).subst (^(constraints) ++ ls) ^(s)` by
      (fs[pure_add_constraints_append]>>
      Q.EXISTS_TAC`^(s)`>>fs[])>>
      Q.SPECL_THEN [`^(s)`,`^(st).subst`,`ls`,`^(constraints)`]
        assume_tac
        pure_add_constraints_swap>>
      rfs[])
  | _ => ALL_TAC;
*)

(* HOL4 ML code, not ported:
fun pure_add_constraints_rest_tac ls =
  case ls of [constraints,s]
  =>
  (Q.EXISTS_TAC`si`>>
  Q.EXISTS_TAC`^(constraints)`>>
  Q.SPECL_THEN [`n`,`si`,`^(s)`] assume_tac (GEN_ALL
    t_compat_bi_ground)>>
  rfs[]>>
  rw[]
  >-
    metis_tac[pure_add_constraints_success]
  >>
    TRY(`t_wfs si` by metis_tac[pure_add_constraints_wfs]>>
    fs[pure_add_constraints_wfs,convert_t_def,t_walkstar_eqn
      ,t_walk_eqn]>>NO_TAC))
  | _ => ALL_TAC;
*)

(* HOL4 ML code, not ported:
fun pure_add_constraints_ignore_tac s =
     byA(`pure_add_constraints ^(s) ls ^(s)`,
      (match_mp_tac pure_add_constraints_ignore >>
      fs[Abbr`ls`,t_walkstar_eqn,t_walk_eqn]))
*)

(* copied from src/1/Tactical *)

(* HOL4 ML code, not ported:
val Q_TAC = fn tac => fn t => fn g => tac (parse_with_goal t g) g
*)

(* Q_TAC except the argument is a list of terms *)
(* HOL4 ML code, not ported:
val list_Q_TAC = fn tac => fn ts => fn g => tac (map (fn t=>
  parse_with_goal t g) ts) g
*)

(* HOL4 ML code, not ported:
val pure_add_constraints_ignore_tac = Q_TAC
  pure_add_constraints_ignore_tac
val pure_add_constraints_combine_tac = list_Q_TAC
  pure_add_constraints_combine_tac
val pure_add_constraints_rest_tac = list_Q_TAC
  pure_add_constraints_rest_tac
*)

(*For grounded ones*)
(* HOL4 ML code, not ported:
val pac_tac =
  pure_add_constraints_ignore_tac `s`>>
  pure_add_constraints_combine_tac [`st`,`constraints`,`s`]>>
  fs[pure_add_constraints_append]>>
  Q.EXISTS_TAC `<|subst:=s2' ; next_uvar := st.next_uvar; next_id :=
    st.next_id |>` >>fs[]>>
  pure_add_constraints_rest_tac [`constraints`,`s`];
*)

(* HOL4 ML code, not ported:
fun flip_converts th =
  let
    val (l,r) = dest_eq (concl th)
  in
    if same_const (rator r) ``convert_t`` then
      CONV_RULE (REWR_CONV EQ_SYM_EQ) th
    else th
  end handle HOL_ERR _ => th
*)

(* HOL4 ML code, not ported:
fun extend_uvar_tac t=
  `check_freevars n [] ^(t)` by
  (imp_res_tac check_t_to_check_freevars>>
  rfs[check_freevars_def])>>
  Q.SPECL_THEN [`^(t)`,`st`,`s`,`n`,`constraints`] mp_tac (GEN_ALL
    extend_one_props)>>
  impl_tac>- fs[]>>
  qpat_abbrev_tac `s' = s|++A`>>
  Q.ABBREV_TAC `constraints' = constraints++[Infer_Tuvar
    st.next_uvar,unconvert_t ^(t)]`>>
  rfs[LET_THM]>>
  imp_res_tac pure_add_constraints_success>>
  unconversion_tac>>
  rw[];
*)

(* HOL4 ML code, not ported:
val replace_uvar_tac =
  rpt (qpat_x_assum `t_walkstar s A = B` (fn th =>
  (((Q.SUBGOAL_THEN `t_walkstar s' h = ^(th|>concl|>rhs)` assume_tac))>-
  (metis_tac[check_t_def,submap_t_walkstar_replace,th]))) )
*)

(* HOL4 ML code, not ported:
val rest_uvar_tac =
  pure_add_constraints_ignore_tac `s'`>>
  pure_add_constraints_combine_tac [`st`,`constraints'`,`s'`]>>
  `t_compat s si` by metis_tac[t_compat_trans]>>
  fs[pure_add_constraints_append]>>
  Q.EXISTS_TAC `<|subst:=s2' ; next_uvar := st.next_uvar+1 ; next_id :=
    st.next_id|>` >>fs[]>>
  pure_add_constraints_rest_tac [`constraints'`,`s'`]>>
  TRY(metis_tac[check_freevars_empty_convert_unconvert_id]);
*)

(* HOL4 ML code, not ported:
val extend_uvar_tac = Q_TAC extend_uvar_tac;
*)

(* HOL4 ML code, not ported:
fun TRY1 tac = TRY (tac >> NO_TAC)
*)

let simp_tenv_invC_def = cake_define
  `simp_tenv_invC s tvs tenv tenvE <=>
   (!n t.
   ALOOKUP tenvE n = SOME t ==>
   check_freevars tvs [] t /\
   (?t'. ALOOKUP tenv n = SOME t' /\
        unconvert_t t = t_walkstar s t')) /\
   (!n t'. ALOOKUP tenv n = SOME t' ==>
   (?t. ALOOKUP tenvE n = SOME t))`;;

(*convert on both sides of eqn*)

(*Substituting every tvs away with something that has no tvs leaves none
   left*)

(*Specialize check_t_less a bit since we use this form a lot*)

(*This should be general enough to prove both Mat and Handle cases*)
