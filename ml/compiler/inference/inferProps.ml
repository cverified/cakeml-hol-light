(* ======================================================== *)
(*  inferProps: ported from HOL4's
    compiler/inference/inferPropsScript.sml  *)
(* ======================================================== *)

(*
  Various lemmas that are handy in the soundness and completeness
  proofs of the type inferencer.
*)

needs "compiler/inference/infer.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/unify.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* ---------- Facts about deBruijn increment ---------- *)

(* ---------- Type substitution ---------- *)

(* HOL4 ML code, not ported:
val infer_t_induction = infer_tTheory.infer_t_induction;
*)

(* ---------- Dealing with the monad ---------- *)

(* TODO: update *)

(* HOL4 ML code, not ported:
val op_data = {nchotomy = op_nchotomy, case_def = op_case_def};
val op_case_eq = TypeBase.case_eq_of ``:op``;
val op_case_rand = prove_case_rand_thm op_data;
val list_data = {nchotomy = list_nchotomy, case_def = list_case_def}
val list_case_eq = TypeBase.case_eq_of ``:'a list``;
val list_case_rand = prove_case_rand_thm list_data;
*)

(* HOL4 ML code, not ported:
val bool_data = {nchotomy = TypeBase.nchotomy_of bool,
        case_def = TypeBase.case_def_of bool}
val bool_case_rand = prove_case_rand_thm bool_data;
*)

(* HOL4 ML code, not ported:
fun mk_case_rator case_rand =
  case_rand
  |> GEN (case_rand |> concl |> lhs |> rator)
  |> ISPEC (let val z = genvar(gen_tyvar())
                val r = genvar(type_of z --> gen_tyvar())
            in mk_abs(r,mk_comb(r,z)) end)
  |> BETA_RULE
*)

(* HOL4 ML code, not ported:
val list_case_rator = mk_case_rator list_case_rand
val op_case_rator = mk_case_rator op_case_rand
val bool_case_rator = mk_case_rator bool_case_rand
*)

(* HOL4 ML code, not ported:
val constrain_op_success =
  ``(constrain_op l op ts st = (M_success v, st'))``
  |> (REWRITE_CONV [Once constrain_op_op_case, op_case_eq]
    THENC SIMP_CONV (srw_ss () ++ CONJ_ss) [constrain_op_case_def,
        op_simple_constraints_def, LET_THM, bool_case_eq,
        st_ex_bind_success,st_ex_return_success,
        add_constraint_success,failwith_success,
        add_constraints_cons2_success,
        add_constraints_nil2_success,
        list_case_rator, list_case_eq, bool_case_rator, bool_case_eq,
        PULL_EXISTS]
  )
*)

(* HOL4 ML code, not ported:
val apply_subst_list_success =
  SIMP_CONV (srw_ss()) [apply_subst_list_def, LET_THM]
  ``(apply_subst_list ts st = (M_success v, st'))``
*)

(* HOL4 ML code, not ported:
val success_eqns =
  LIST_CONJ [st_ex_return_success, st_ex_bind_success,
    st_ex_ignore_bind_success,
             fresh_uvar_success,
             apply_subst_success, add_constraint_success,
               lookup_st_ex_success,
             n_fresh_uvar_success, failwith_success,
               add_constraints_success,
             oneTheory.one, check_type_definition_success,
             get_next_uvar_success, apply_subst_list_success,
               guard_success,
             read_def, option_case_eq, check_dups_success,
             type_name_check_subst_success,
             check_ctor_types_success,
             check_ctors_success];
*)

(* ---------- Simple structural properties ---------- *)

(* ---------- Dealing with the constraint set ---------- *)

(* ---------- The next unification variable is monotone non-decreasing
   ---------- *)

(* ---------- The inferencer builds well-formed substitutions ----------
   *)

(* ---------- The invariants of the inferencer ---------- *)

(* moved this one around a bit *)

(* HOL4 ML code, not ported:
val check_t_more_0 =
  check_t_more2 |> CONJUNCT1 |> Q.SPECL[`t`,`0`] |>
    SIMP_RULE(srw_ss())[]
*)

(* HOL4 ML code, not ported:
val check_t_more_1 =
  check_t_more3 |> CONJUNCT1 |> SPEC_ALL |>
    SIMP_RULE(srw_ss())[PULL_FORALL] |> Q.SPEC`1`
*)

let ienv_ok_def = cake_define
  `ienv_ok uvars ienv <=>
     ienv_val_ok uvars (inf_env_inf_v ienv) /\
     tenv_ctor_ok (inf_env_inf_c ienv) /\
     tenv_abbrev_ok (inf_env_inf_t ienv)`;;

let infer_subst_var_def = cake_define
  `infer_subst_var s t =
        match t with
          Infer_Tuvar n ->
     (match FLOOKUP s n with NONE -> Infer_Tuvar n | SOME tv ->
       Infer_Tvar_db tv)
        | t -> t`;;

(* Rename (type_system) type identifiers with a function *)
let _ = size_thms "t";;
(* HOL4 termination: >> rw [] >> induct_on `ts` >> rw [t_size_def] >>
   res_tac >> decide_tac *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let ts_tid_rename_def = cake_define_tac (
  `MEASURE (\(_1,y). t_size y)`,
  CHEAT_TAC)
  `ts_tid_rename f t =
        match t with
          Tapp ts tn -> Tapp (MAP (ts_tid_rename f) ts) (f tn)
        | t -> t`;;

(* HOL4 ML code, not ported:
val ts_tid_rename_ind = theorem"ts_tid_rename_ind";
*)

(* All type ids in a type belonging to a set *)
let _ = size_thms "t";;
(* HOL4 termination: >> rw [] >> induct_on `ts` >> rw [t_size_def] >>
   res_tac >> decide_tac *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let set_tids_def = cake_define_tac (
  `MEASURE t_size`,
  CHEAT_TAC)
  `set_tids x1 =
        match x1 with
          Tapp ts tn -> tn INSERT (BIGUNION (set_of_list (MAP
            set_tids ts)))
        | _2 -> {}`;;

(* HOL4 ML code, not ported:
val set_tids_ind = theorem"set_tids_ind";
*)

let set_tids_subset_def = cake_define
  `set_tids_subset tids t <=> set_tids t SUBSET tids`;;

let _ = size_thms "t";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 termination: >> rw [] >> induct_on `ts` >> rw [t_size_def] >>
   full_simp_tac (srw_ss()++ARITH_ss) [] *)
let unconvert_t_def = cake_define_list_try (fun () ->
  `MEASURE t_size`)
  [`unconvert_t (Tvar_db n) = Infer_Tvar_db n`;
   `unconvert_t (Tapp ts tc) = Infer_Tapp (MAP unconvert_t ts) tc`;
   `unconvert_t (Tvar v) = Infer_Tuvar ARB`];;

(* HOL4 ML code, not ported:
val unconvert_t_ind = theorem"unconvert_t_ind"
*)

(* Properties about inferencer type identifiers *)
let _ = size_thms "infer_t";;
(* HOL4 termination: >> rw [] >> induct_on `ts` >> rw
   [infer_tTheory.infer_t_size_def] >> res_tac >> decide_tac *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let inf_set_tids_def = cake_define_tac (
  `MEASURE infer_t_size`,
  CHEAT_TAC)
  `inf_set_tids x1 =
        match x1 with
          Infer_Tapp ts tn -> tn INSERT (BIGUNION (set_of_list (MAP
            inf_set_tids ts)))
        | _3 -> {}`;;

let inf_set_tids_subset_def = cake_define
  `inf_set_tids_subset tids t <=> inf_set_tids t SUBSET tids`;;

(* all the tids used in a tenv *)
let inf_set_tids_ienv_def = cake_define
  `inf_set_tids_ienv tids (ienv:inf_env) <=>
   nsAll (\i (ls,t). inf_set_tids_subset tids (unconvert_t t))
     (inf_env_inf_t ienv) /\
   nsAll (\i (ls,ts,tid). EVERY (\t. inf_set_tids_subset tids
     (unconvert_t t)) ts /\ tid IN tids) (inf_env_inf_c ienv) /\
   nsAll (\i (n,t). inf_set_tids_subset tids t) (inf_env_inf_v
     ienv)`;;

let inf_set_tids_subst_def = cake_define
  `inf_set_tids_subst tids subst <=>
   (!t. t IN FRANGE subst ==> inf_set_tids_subset tids t)`;;

let prim_tids_def = cake_define
  `prim_tids contain' tids <=>
     EVERY (\x. x IN tids <=> contain') (Tlist_num :: Tbool_num ::
       prim_type_nums)`;;

(* HOL4 ML code, not ported:
val let_tac =
   old_drule (CONJUNCT1 infer_e_check_t)
   >> old_drule (CONJUNCT1 infer_e_check_s)
   >> simp []
   >> disch_then old_drule
   >> old_drule (CONJUNCT1 infer_e_wfs)
   >> old_drule (CONJUNCT1 infer_p_check_t)
   >> fs [ienv_ok_def]
   >> rw []
   >> old_drule (CONJUNCT1 infer_p_check_s)
   >> simp []
   >> disch_then old_drule
   >> rw []
   >> old_drule (CONJUNCT1 infer_p_wfs)
   >> disch_then old_drule
   >> rw []
   >> old_drule t_unify_check_s
   >> rpt (disch_then old_drule)
   >> old_drule (CONJUNCT1 infer_e_next_uvar_mono)
   >> old_drule (CONJUNCT1 infer_p_next_uvar_mono)
   >> rw []
   >> rename1 `infer_p _ _ _ st2 = (M_success (t2, env2), st3)`
   >> `check_t 0 (count st3.next_uvar) t1` by metis_tac [check_t_more4]
   >> fs []
   >> old_drule t_unify_wfs
   >> disch_then old_drule
   >> rw []
   >> old_drule generalise_complete
   >> rpt (disch_then old_drule)
   >> fs [every_shim]
   >> rw [ienv_val_ok_def]
   >> irule nsAll_alist_to_ns
   >> simp [EVERY_MEM, MEM_ZIP]
   >> rw []
   >> rw [EL_MAP]
   >> irule (CONJUNCT1 check_t_walkstar)
   >> simp []
   >> fs [sub_completion_def, EVERY_MEM, MEM_MAP, PULL_EXISTS]
   >> metis_tac [check_t_more2, check_t_more5, MEM_EL, DECIDE ``x + 0n =
     x``];
*)

let remap_tenv_def = cake_define
  `remap_tenv f tenv =
   mk_type_env (nsMap (\(n,t). (n,ts_tid_rename f t)) (type_env_v
     tenv)) (nsMap (\(ls,ts,tid). (ls,MAP (ts_tid_rename f) ts,f
     tid)) (type_env_c tenv)) (nsMap (\(ls,t). (ls,ts_tid_rename f
     t)) (type_env_t tenv))`;;

let hide_def = cake_define
  `inferProps_hide x = x`;;
hol4_overload "hide" "inferProps_hide";;
