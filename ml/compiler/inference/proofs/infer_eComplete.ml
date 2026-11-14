(* ======================================================== *)
(*  infer_eComplete: ported from HOL4's
    compiler/inference/proofs/infer_eCompleteScript.sml
    A proof theory, with 1 definition and 48 theorems.  Needed by
    inferComplete.ml, inferSound.ml and type_eDeterm.ml.  *)
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
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "infer_eComplete"
  ["ast"; "envRel"; "infer"; "inferProps"; "infer_t"; "namespace";
   "namespaceProps"; "semanticPrimitives"; "typeSysProps";
   "typeSystem"; "unify"];;

let _ = do_list hide_constant ["id"];;

(*Useful lemmas about pure add constraints, some of these imply the others*)
let pure_add_constraints_success = prove
 (`!s constraints s'.
   t_wfs s /\
   pure_add_constraints s constraints s' ==>
   s SUBMAP s' /\
   FDOM s SUBSET FDOM s' /\
   t_compat s s' /\
   t_wfs s'`,
  CHEAT_TAC);;

(*t_compat is preserved over certain types of pure_add_constraints*)
let t_compat_pure_add_constraints_1 = prove
 (`!ls s sx.
    t_compat s sx /\ ALL (\(x,y). t_walkstar sx x = t_walkstar sx y)
      ls ==>
    (?si. pure_add_constraints s ls si /\ t_compat si sx)`,
  CHEAT_TAC);;

(*If pure add constraints succeeds then the constraints all unify*)
let t_compat_pure_add_constraints_2 = prove
 (`!ls s sx.
    t_wfs s /\
    pure_add_constraints s ls sx ==>
    ALL (\(x,y). t_walkstar sx x = t_walkstar sx y) ls`,
  CHEAT_TAC);;

(*behaves like a function if the first 2 arguments are equal*)
let pure_add_constraints_functional = prove
 (`!constraints s s' s''.
    t_wfs s /\
    pure_add_constraints s constraints s' /\
    pure_add_constraints s constraints s'' ==> s' = s''`,
  CHEAT_TAC);;

(*1 direction is sufficient to imply the other*)
(* [local] *)
let pure_add_constraints_swap_lemma = prove
 (`t_wfs s /\
   pure_add_constraints s (APPEND a b) sx ==>
   (?si. pure_add_constraints s (APPEND b a) si /\
        t_compat si sx)`,
  CHEAT_TAC);;

let pure_add_constraints_swap = prove
 (`t_wfs s /\
    pure_add_constraints s (APPEND a b) sx ==>
    (?si. pure_add_constraints s (APPEND b a) si /\
         t_compat si sx /\
         t_compat sx si)`,
  CHEAT_TAC);;

(* HOL4 infer_eCompleteScript.sml:122: ML code, not ported *)

(*End pure_add_constraints stuff*)

(* [local] *)
let extend_t_vR_WF = prove
 (`(check_t lim {} (n) /\
   WF (t_vR s)) ==>
   WF (t_vR (s |+ (uvar,n)))`,
  CHEAT_TAC);;

(* [local] *)
let not_t_oc = prove
 (`(!t s v lim. t_wfs s /\ check_t lim {} t ==> ~(t_oc s t v)) /\
   (!ts s t v lim. t_wfs s /\ ALL (check_t lim {}) ts ==> ~(EX (\t.
     t_oc s t v) ts))`,
  CHEAT_TAC);;

(* [local] *)
let FDOM_extend = prove
 (`FDOM s = count next_uvar ==>
    FDOM (s |+ (next_uvar,n)) = count (SUC next_uvar)`,
  CHEAT_TAC);;

let pure_add_constraints_exists = prove
 (`!s ts next_uvar lim.
    t_wfs s /\
    FDOM s = count next_uvar /\
    ALL (check_freevars lim []) ts ==>
    (let tys = MAP (\n. (next_uvar + n)) (COUNT_LIST (LENGTH ts)) in
    let targs = MAP unconvert_t ts in
    let constraints = ZIP (MAP Infer_Tuvar tys) targs in
    let extension = ZIP tys targs in
    pure_add_constraints s constraints (s |++ extension))`,
  CHEAT_TAC);;

(*Can't find a version of this in the right direction*)
(* [local] *)
let check_t_t_walkstar = prove
 (`t_wfs s ==>
   (!tvs (uvars:num->bool) t. check_t tvs {} (t_walkstar s t) ==>
     check_t tvs (FDOM s) t)`,
  CHEAT_TAC);;

(*Ignore increment on deBrujin vars*)
(* [local] *)
let t_walkstar_ignore_inc = prove
 (`t_wfs s ==>
   (!t.
   (!uv. uv IN FDOM s ==> check_t 0 {} (t_walkstar s (Infer_Tuvar
     uv))) ==>
   t_walkstar (infer_deBruijn_inc tvs o_f s) t = t_walkstar s t) /\
   (!ts. (!t.
   (!uv. uv IN FDOM s ==> check_t 0 {} (t_walkstar s (Infer_Tuvar
     uv))) ==>
   ALL (\t. t_walkstar (infer_deBruijn_inc tvs o_f s) t =
     t_walkstar s t) ts))`,
  CHEAT_TAC);;

(*Adding a list of keys that did not already exist is safe*)
(* [local] *)
let SUBMAP_FUPDATE_LIST_NON_EXIST = prove
 (`set_of_list (MAP FST ls) INTER (FDOM s) = {} ==>
   s SUBMAP (s |++ ls)`,
  CHEAT_TAC);;

(* [local] *)
let t_vwalk_o_f_id = prove
 (`t_wfs s ==>
   (!t. t_vwalk (infer_deBruijn_inc 0 o_f s) t = t_vwalk s t)`,
  CHEAT_TAC);;

(* [local] *)
let t_walkstar_o_f_id = prove
 (`t_wfs s ==>
   (!t. t_walkstar ((infer_deBruijn_inc 0) o_f s) t = t_walkstar s
     t)`,
  CHEAT_TAC);;

(* deBruijn_subst_id[local] *)
let infer_eComplete_deBruijn_subst_id = prove
 (`(!t. deBruijn_subst 0 [] t = t) /\
   (!ts. MAP (deBruijn_subst 0 []) ts = ts)`,
  CHEAT_TAC);;

(* [local] *)
let tscheme_approx_weakening2 = prove
 (`tscheme_approx tvs s t1 t2 /\ t_compat s s' /\ FDOM s SUBSET FDOM s'
  ==>
   tscheme_approx tvs s' t1 t2`,
  CHEAT_TAC);;

(* [local] *)
let env_rel_complete_t_compat = prove
 (`t_compat s s' /\
   FDOM s SUBSET FDOM s' /\
   t_wfs s' /\
   env_rel_complete s ienv tenv tenvE ==>
   env_rel_complete s' ienv tenv tenvE`,
  CHEAT_TAC);;

(* [local] *)
let NOT_SOME_NONE = prove
 (`(!x. ~(A = SOME x)) ==> A = NONE`,
  CHEAT_TAC);;

(* [local] *)
let t_walk_submap_walkstar = prove
 (`!s s'.
   s SUBMAP s' /\ t_wfs s /\ t_wfs s' ==>
   (!h. t_walk s (t_walkstar s' h) = t_walkstar s' h) /\
   (!hs. MAP ((t_walk s) o t_walkstar s') hs = MAP (t_walkstar s')
     hs)`,
  CHEAT_TAC);;

(* [local] *)
let t_unify_to_pure_add_constraints = prove
 (`!s s' h t constraints s''.
   pure_add_constraints s (APPEND constraints [h,t]) s'' ==>
   (?s'. pure_add_constraints s constraints s' /\
   t_unify s' h t = SOME s'')`,
  CHEAT_TAC);;

(* [local] *)
let add_constraint_success2 = prove
 (`!l t1 t2 st st' x.
   add_constraint l t1 t2 st = (M_success x,st') <=>
   x = one /\
   pure_add_constraints (infer_st_subst st) [t1,t2] (infer_st_subst
     st') /\ infer_st_next_uvar
   st' = infer_st_next_uvar st /\ infer_st_next_id
   st' = infer_st_next_id st`,
  CHEAT_TAC);;

(* [local] *)
let pure_add_constraints_combine = prove
 (`(?st'. (pure_add_constraints (infer_st_subst st) ls (infer_st_subst
  st') /\ infer_st_next_uvar st' = x1 /\ infer_st_next_id st' = x2) /\
   (pure_add_constraints (infer_st_subst st') ls' (infer_st_subst
     st'') /\ y1 = infer_st_next_uvar st' /\ y2 = infer_st_next_id st'))
     <=>
   pure_add_constraints (infer_st_subst st) (APPEND ls ls')
     (infer_st_subst st'') /\ y1 = x1 /\ y2 = x2`,
  CHEAT_TAC);;

(* [local] *)
let t_unify_ignore = prove
 (`(!s t t'.
   t_wfs s ==>
   t_walkstar s t = t_walkstar s t' ==>
   t_unify s t t' = SOME s) /\
   (!s ts ts'.
   t_wfs s ==>
   MAP (t_walkstar s) ts = MAP (t_walkstar s) ts' ==>
   ts_unify s ts ts' = SOME s)`,
  CHEAT_TAC);;

let pure_add_constraints_ignore = prove
 (`!s ls.
    t_wfs s /\ ALL (\(x,y). t_walkstar s x = t_walkstar s y) ls ==>
      pure_add_constraints s ls s`,
  CHEAT_TAC);;

(*t_compat preserves all grounded (no unification variable after walk) terms*)
(* [local] *)
let t_compat_ground = prove
 (`t_compat a b ==>
   (!uv.
        uv IN FDOM a /\
        check_t tvs {} (t_walkstar a (Infer_Tuvar uv)) ==> uv IN FDOM
          b /\
          check_t tvs {} (t_walkstar b (Infer_Tuvar uv)))`,
  CHEAT_TAC);;

(* [local] *)
let t_walkstar_tuvar_props2 = prove
 (`t_wfs s /\ t_walkstar s x = Infer_Tuvar uv ==>
   (?k. x = Infer_Tuvar k /\
       (k = uv ==> ~(k IN FDOM s)) /\
       (~(k = uv) ==> k IN FDOM s))`,
  CHEAT_TAC);;

(*Remove every uvar in the FDOM if we walkstar using a completed map*)
let check_t_less = prove
 (`(!t.
   t_wfs s /\
   (!uv. uv IN FDOM s ==> check_t n {} (t_walkstar s (Infer_Tuvar
     uv))) /\
   check_t 0 uvars t ==>
   check_t n (uvars INTER (COMPL (FDOM s))) (t_walkstar s t)) /\
   (!ts.
   t_wfs s /\
   (!uv. uv IN FDOM s ==> check_t n {} (t_walkstar s (Infer_Tuvar
     uv))) /\
   ALL (check_t 0 uvars) ts ==>
   ALL (check_t n (uvars INTER (COMPL (FDOM s)))) (MAP (t_walkstar
     s) ts))`,
  CHEAT_TAC);;

(*Double sided t_compat thm*)
let t_compat_bi_ground = prove
 (`(!uv. uv IN FDOM a ==> check_t n {} (t_walkstar a (Infer_Tuvar uv)))
  /\
    t_compat a b /\
    t_compat b a ==>
    (!uv. uv IN FDOM b ==> check_t n {} (t_walkstar b (Infer_Tuvar
      uv))) /\
    FDOM a = FDOM b /\
    ((!t. t_walkstar a t = t_walkstar b t) /\
    (!ts. MAP (t_walkstar a) ts = MAP (t_walkstar b) ts))`,
  CHEAT_TAC);;

(*Free properties when extending the completed map with uvar->ground var*)
(* [local] *)
let extend_one_props = prove
 (`t_wfs (infer_st_subst st) /\
   t_wfs s /\
   pure_add_constraints (infer_st_subst st) constraints s /\
   (!uv. uv IN FDOM s ==> check_t n {} (t_walkstar s (Infer_Tuvar
     uv))) /\
   check_freevars n [] t /\
   FDOM s = count (infer_st_next_uvar st) ==>
   (let s' = s |++ [(infer_st_next_uvar st,unconvert_t t)] in
   t_wfs s' /\
   pure_add_constraints s [Infer_Tuvar (infer_st_next_uvar
     st),unconvert_t t] s' /\
   s SUBMAP s' /\ infer_st_subst
   st SUBMAP s' /\
   pure_add_constraints (infer_st_subst st)
     (APPEND constraints [(Infer_Tuvar (infer_st_next_uvar
       st),unconvert_t t)]) s' /\
   FDOM s' = count (infer_st_next_uvar st + 1) /\
   t_walkstar s' (Infer_Tuvar (infer_st_next_uvar st)) = unconvert_t
     t /\
   (!uv. uv IN FDOM s' ==> check_t n {} (t_walkstar s' (Infer_Tuvar
     uv))))`,
  CHEAT_TAC);;

(*This occurs when looking up a list updated fmap*)
(* HOL4 infer_eCompleteScript.sml:629-645: a proof *)

(* [local] *)
let submap_t_walkstar_replace = prove
 (`t_wfs s' /\
   s SUBMAP s' /\
   check_t n {} (t_walkstar s h) ==>
   t_walkstar s h = t_walkstar s' h`,
  CHEAT_TAC);;

let extend_multi_props = prove
 (`!st constraints s ts n.
    t_wfs (infer_st_subst st) /\
    t_wfs s /\
    pure_add_constraints (infer_st_subst st) constraints s /\
    (!uv. uv IN FDOM s ==> check_t n {} (t_walkstar s (Infer_Tuvar
      uv))) /\
    ALL (check_freevars n []) ts /\
    FDOM s = count (infer_st_next_uvar st) ==>
    (let tys = MAP (\n. (infer_st_next_uvar st + n)) (COUNT_LIST
      (LENGTH ts)) in
    let targs = MAP unconvert_t ts in
    let new_constraints = ZIP (MAP Infer_Tuvar tys) targs in
    let extension = ZIP tys targs in
    let s' = s |++ extension in
    pure_add_constraints s new_constraints s' /\
    pure_add_constraints (infer_st_subst st) (APPEND constraints
      new_constraints) s' /\
    t_wfs s' /\
    s SUBMAP s' /\ infer_st_subst
    st SUBMAP s' /\
    FDOM s' = count (infer_st_next_uvar st + LENGTH ts) /\
    (!n. n < LENGTH ts ==>
    t_walkstar s' (Infer_Tuvar (infer_st_next_uvar st + n)) = EL n
      targs) /\
    (!uv. uv IN FDOM s' ==> check_t n {} (t_walkstar s'
      (Infer_Tuvar uv))))`,
  CHEAT_TAC);;

(*Useful tactics, mainly for constrain_op*)

(* HOL4 infer_eCompleteScript.sml:745-748: a proof *)

(* HOL4 infer_eCompleteScript.sml:750-759: a proof *)

(* HOL4 infer_eCompleteScript.sml:761-774: a proof *)

(* HOL4 infer_eCompleteScript.sml:776-779: a proof *)

(* copied from src/1/Tactical *)

(* HOL4 infer_eCompleteScript.sml:789: ML code, not ported *)

(* Q_TAC except the argument is a list of terms *)
(* HOL4 infer_eCompleteScript.sml:792: ML code, not ported *)

(* HOL4 infer_eCompleteScript.sml:794-796: ML code, not ported *)

(*For grounded ones*)
(* HOL4 infer_eCompleteScript.sml:799-804: a proof *)

(* HOL4 infer_eCompleteScript.sml:806-813: ML code, not ported *)

(* HOL4 infer_eCompleteScript.sml:815-826: a proof *)

(* HOL4 infer_eCompleteScript.sml:828-831: a proof *)

(* HOL4 infer_eCompleteScript.sml:833-840: a proof *)

(* HOL4 infer_eCompleteScript.sml:842: ML code, not ported *)

(* HOL4 infer_eCompleteScript.sml:844: ML code, not ported *)

(* [local] *)
let constrain_op_complete_simple_helper = prove
 (`!n.
     sub_completion n (infer_st_next_uvar st) (infer_st_subst st)
       constraints s /\
     type_op op ts t /\
     MAP (convert_t o (t_walkstar s)) ts' = ts /\
     FST (op_simple_constraints op) /\
     FDOM (infer_st_subst st) SUBSET count (infer_st_next_uvar st) /\
     FDOM s = count (infer_st_next_uvar st) /\
     t_wfs (infer_st_subst st) /\
     ALL (check_t n {}) (MAP (t_walkstar s) ts') /\
     check_freevars n [] t ==>
     (?st' xs t'.
     t = convert_t (t_walkstar s t') /\
     pure_add_constraints s xs s /\
     (!l st'. infer_st_next_uvar
       st' = infer_st_next_uvar st /\ infer_st_next_id
       st' = infer_st_next_id st /\
       pure_add_constraints (infer_st_subst st) xs (infer_st_subst
         st') ==>
       constrain_op l op ts' st = (M_success t',st')))`,
  CHEAT_TAC);;

(* [local] *)
let constrain_op_complete = prove
 (`!n.
   type_op op ts t /\
   sub_completion n (infer_st_next_uvar st) (infer_st_subst st)
     constraints s /\
   FDOM (infer_st_subst st) SUBSET count (infer_st_next_uvar st) /\
   FDOM s = count (infer_st_next_uvar st) /\
   t_wfs (infer_st_subst st) /\
   MAP (convert_t o (t_walkstar s)) ts' = ts /\
   ALL (check_t n {}) (MAP (t_walkstar s) ts') /\
   check_freevars n [] t ==>
   (?t' st' s' constraints'.
   constrain_op l op ts' st = (M_success t',st') /\
   sub_completion n (infer_st_next_uvar st') (infer_st_subst st')
     constraints' s' /\
   t_compat s s' /\
   FDOM (infer_st_subst st') SUBSET count (infer_st_next_uvar st') /\
   FDOM s' = count (infer_st_next_uvar st') /\
   t = convert_t (t_walkstar s' t'))`,
  CHEAT_TAC);;

let simp_tenv_invC_def = new_definition
  `simp_tenv_invC s tvs tenv tenvE <=>
   (!n t.
   ALOOKUP tenvE n = SOME t ==>
   check_freevars tvs [] t /\
   (?t'. ALOOKUP tenv n = SOME t' /\
        unconvert_t t = t_walkstar s t')) /\
   (!n t'. ALOOKUP tenv n = SOME t' ==>
   (?t. ALOOKUP tenvE n = SOME t))`;;

(* [local] *)
let simp_tenv_invC_empty = prove
 (`simp_tenv_invC s n [] []`,
  CHEAT_TAC);;

(* [local] *)
let simp_tenv_invC_more = prove
 (`simp_tenv_invC s tvs tenv tenvE /\
   t_compat s s' ==>
   simp_tenv_invC s' tvs tenv tenvE`,
  CHEAT_TAC);;

(* [local] *)
let simp_tenv_invC_append = prove
 (`simp_tenv_invC s'' tvs tenv tenvE /\
   simp_tenv_invC s'' tvs tenv' tenvE' ==>
   simp_tenv_invC s'' tvs (APPEND tenv' tenv) (APPEND tenvE' tenvE)`,
  CHEAT_TAC);;

(*convert on both sides of eqn*)
let convert_bi_remove = prove
 (`convert_t A = convert_t B /\
    check_t n {} A /\
    check_t m {} B ==>
    A = B`,
  CHEAT_TAC);;

(*Substituting every tvs away with something that has no tvs leaves none left*)
(* [local] *)
let infer_type_subst_check_t_less = prove
 (`LENGTH ls = LENGTH tvs /\
   ALL (check_t n {}) ls ==>
   (!t.
   check_freevars n tvs t ==>
   check_t n {} (infer_type_subst (ZIP tvs ls) t)) /\
   (!ts.
   ALL (check_freevars n tvs) ts ==>
   ALL (check_t n {}) (MAP (infer_type_subst (ZIP tvs ls)) ts))`,
  CHEAT_TAC);;

let infer_p_complete = prove
 (`(!tvs tenv p t tenvE.
   type_p tvs tenv p t tenvE ==>
   (!l s ienv st constraints.
   tenv_ctor_ok (type_env_c tenv) /\ inf_env_inf_c
   ienv = type_env_c tenv /\ inf_env_inf_t
   ienv = type_env_t tenv /\
   tenv_abbrev_ok (type_env_t tenv) /\
   t_wfs (infer_st_subst st) /\
   sub_completion tvs (infer_st_next_uvar st) (infer_st_subst st)
     constraints s /\
   FDOM (infer_st_subst st) SUBSET count (infer_st_next_uvar st) /\
   FDOM s = count (infer_st_next_uvar st) ==>
   (?t' new_bindings st' s' constraints'.
     infer_p l ienv p st = (M_success (t',new_bindings),st') /\
     sub_completion tvs (infer_st_next_uvar st') (infer_st_subst st')
       constraints' s' /\
     FDOM (infer_st_subst st') SUBSET count (infer_st_next_uvar st')
       /\
     FDOM s' = count (infer_st_next_uvar st') /\
     t_compat s s' /\
     simp_tenv_invC s' tvs new_bindings tenvE /\
     t = convert_t (t_walkstar s' t')))) /\
   (!tvs tenv ps ts tenvE.
   type_ps tvs tenv ps ts tenvE ==>
   (!l s ienv st constraints.
   tenv_ctor_ok (type_env_c tenv) /\ inf_env_inf_c
   ienv = type_env_c tenv /\ inf_env_inf_t
   ienv = type_env_t tenv /\
   tenv_abbrev_ok (type_env_t tenv) /\
   t_wfs (infer_st_subst st) /\
   sub_completion tvs (infer_st_next_uvar st) (infer_st_subst st)
     constraints s /\
   FDOM (infer_st_subst st) SUBSET count (infer_st_next_uvar st) /\
   FDOM s = count (infer_st_next_uvar st) ==>
   (?ts' new_bindings st' s' constraints'.
     infer_ps l ienv ps st = (M_success (ts',new_bindings),st') /\
     sub_completion tvs (infer_st_next_uvar st') (infer_st_subst st')
       constraints' s' /\
     FDOM (infer_st_subst st') SUBSET count (infer_st_next_uvar st')
       /\
     FDOM s' = count (infer_st_next_uvar st') /\
     t_compat s s' /\
     simp_tenv_invC s' tvs new_bindings tenvE /\
     ts = MAP (convert_t o t_walkstar s') ts')))`,
  CHEAT_TAC);;

(*Specialize check_t_less a bit since we use this form a lot*)
let sub_completion_completes = prove
 (`t_wfs s /\
    check_t 0 (count n) t /\
    FDOM s = count n /\
    (!uv. uv < n ==>
      check_t tvs {} (t_walkstar s (Infer_Tuvar uv))) ==>
    check_t tvs {} (t_walkstar s t)`,
  CHEAT_TAC);;

(* [local] *)
let lookup_var_bind_var_list = prove
 (`!bindings.
   lookup_var x (bind_var_list 0 bindings tenvE) tenv =
   (match x with
   Short id' ->
     (match ALOOKUP bindings id' with
       SOME t -> SOME (0,t) | NONE -> lookup_var x tenvE tenv) | _1
         -> lookup_var x tenvE tenv)`,
  CHEAT_TAC);;

(*This should be general enough to prove both Mat and Handle cases*)
(* [local] *)
let infer_pes_complete = prove
 (`!pes st' constraints' s'.
   ~(pes = []) /\
   ienv_ok (count uvar) ienv /\
   uvar <= infer_st_next_uvar st' /\
   t_wfs (infer_st_subst st') /\
   env_rel_complete s' ienv tenv tenvE /\
   (RES_FORALL (set_of_list pes) (\x.
     ?bindings.
       ALL_DISTINCT (ast_pat_bindings (FST x)) /\
       type_p (num_tvs tenvE) tenv (FST x) t1 bindings /\
       type_e tenv (bind_var_list 0 bindings tenvE) (SND x) t2 /\
       (!l s'' ienv' st'' constraints''.
         ienv_ok (count (infer_st_next_uvar st'')) ienv' /\ t_wfs
           (infer_st_subst st'') /\
         FDOM (infer_st_subst st'') SUBSET count (infer_st_next_uvar
           st'') /\
         sub_completion (num_tvs (bind_var_list 0 bindings tenvE))
           (infer_st_next_uvar st'') (infer_st_subst st'') constraints''
           s'' /\
         FDOM s'' = count (infer_st_next_uvar st'') /\
         env_rel_complete s'' ienv' tenv (bind_var_list 0 bindings
           tenvE) ==>
         (?t'' st''' s''' constraints'''.
           infer_e l ienv' (SND x) st'' = (M_success t'',st''') /\
           sub_completion (num_tvs tenvE) (infer_st_next_uvar st''')
             (infer_st_subst st''') constraints''' s''' /\
           FDOM (infer_st_subst st''') SUBSET count
             (infer_st_next_uvar st''') /\
           FDOM s''' = count (infer_st_next_uvar st''') /\ t_compat
             s'' s''' /\
           t2 = convert_t (t_walkstar s''' t''))))) /\
   sub_completion (num_tvs tenvE) (infer_st_next_uvar st')
     (infer_st_subst st') constraints' s' /\
   FDOM (infer_st_subst st') SUBSET count (infer_st_next_uvar st') /\
   FDOM s' = count (infer_st_next_uvar st') /\
   unconvert_t t1 = t_walkstar s' t1' /\
   unconvert_t t2 = t_walkstar s' t2' ==>
   (?st'' s'' constraints''.
   infer_pes l ienv pes t1' t2' st' = (M_success one,st'') /\
   sub_completion (num_tvs tenvE) (infer_st_next_uvar st'')
     (infer_st_subst st'') constraints'' s'' /\
   FDOM (infer_st_subst st'') SUBSET count (infer_st_next_uvar st'')
     /\
   FDOM s'' = count (infer_st_next_uvar st'') /\
   t_compat s' s'')`,
  CHEAT_TAC);;

(* [local] *)
let deBrujin_subst_excess = prove
 (`(!n targs t t'.
   check_freevars (LENGTH targs) [] t /\
   deBruijn_subst n targs t = t' ==>
   (!ls.
   deBruijn_subst n (APPEND targs ls) t = t'))`,
  CHEAT_TAC);;

(* [local] *)
let convert_infer_deBruijn_subst = prove
 (`!subst t.
   check_t (LENGTH subst) {} t ==>
   convert_t (infer_deBruijn_subst subst t) =
   deBruijn_subst 0 (MAP convert_t subst) (convert_t t)`,
  CHEAT_TAC);;

(* [local] *)
let t_walkstar_infer_db_subst = prove
 (`!s s' uvars subst tvs.
   s SUBMAP s' /\ t_wfs s' /\
   FDOM s = count uvars /\
   (!n. n < uvars ==> check_t tvs {} (t_walkstar s (Infer_Tuvar n)))
     /\
   (!n. n < LENGTH subst ==> t_walkstar s' (Infer_Tuvar (n + uvars))
     = t_walkstar s (EL n subst)) ==>
   (!t.
   check_t (LENGTH subst) (count uvars) t ==>
   t_walkstar s (infer_deBruijn_subst subst t) =
   t_walkstar s' (infer_deBruijn_subst (MAP (\n. Infer_Tuvar (n +
     uvars)) (COUNT_LIST (LENGTH subst))) t)) /\
   (!ts.
   ALL (check_t (LENGTH subst) (count uvars)) ts ==>
   MAP (t_walkstar s o infer_deBruijn_subst subst) ts =
   MAP (t_walkstar s' o infer_deBruijn_subst (MAP (\n. Infer_Tuvar
     (n + uvars)) (COUNT_LIST (LENGTH subst)))) ts)`,
  CHEAT_TAC);;

(* [local] *)
let ienv_val_ok_more = prove
 (`(ienv_val_ok cuvs env /\ cuvs SUBSET cuvs' ==>
   ienv_val_ok cuvs' env) /\
   (ienv_val_ok (count uvs) env /\ uvs <= uvs' ==>
   ienv_val_ok (count uvs') env)`,
  CHEAT_TAC);;

let infer_e_complete = prove
 (`(!tenv tenvE e t.
    type_e tenv tenvE e t ==>
    (!loc s ienv st constraints.
      // Invariants on the typing and inferencer envs
      // check_menv ienv.inf_m ∧
      // menv_alpha ienv.inf_m tenv.m ∧
      ienv_ok (count (infer_st_next_uvar st)) ienv /\
      // Invariants on inferencer state
      t_wfs (infer_st_subst st) /\
      FDOM (infer_st_subst st) SUBSET count (infer_st_next_uvar st)
        /\
      // Subcompletion
      sub_completion (num_tvs tenvE) (infer_st_next_uvar st)
        (infer_st_subst st) constraints s /\
      FDOM s = count (infer_st_next_uvar st) /\
      env_rel_complete s ienv tenv tenvE ==>
      (?t' st' s' constraints'.
        infer_e loc ienv e st = (M_success t',st') /\
        sub_completion (num_tvs tenvE) (infer_st_next_uvar st')
          (infer_st_subst st') constraints' s' /\
        FDOM (infer_st_subst st') SUBSET count (infer_st_next_uvar
          st') /\
        FDOM s' = count (infer_st_next_uvar st') /\
        t_compat s s' /\
        t = convert_t (t_walkstar s' t')))) /\
   (!tenv tenvE es ts.
    type_es tenv tenvE es ts ==>
    (!loc s ienv st constraints.
      // check_menv ienv.inf_m ∧
      // menv_alpha ienv.inf_m tenv.m ∧
      ienv_ok (count (infer_st_next_uvar st)) ienv /\
      t_wfs (infer_st_subst st) /\
      FDOM (infer_st_subst st) SUBSET count (infer_st_next_uvar st)
        /\
      sub_completion (num_tvs tenvE) (infer_st_next_uvar st)
        (infer_st_subst st) constraints s /\
      FDOM s = count (infer_st_next_uvar st) /\
      env_rel_complete s ienv tenv tenvE ==>
      (?ts' st' s' constraints'.
        infer_es loc ienv es st = (M_success ts',st') /\
        sub_completion (num_tvs tenvE) (infer_st_next_uvar st')
          (infer_st_subst st') constraints' s' /\
        FDOM (infer_st_subst st') SUBSET count (infer_st_next_uvar
          st') /\
        FDOM s' = count (infer_st_next_uvar st') /\
        t_compat s s' /\
        ts = MAP (convert_t o t_walkstar s') ts'))) /\
   (!tenv tenvE funs env.
    type_funs tenv tenvE funs env ==>
    (!loc s ienv st constraints.
      // check_menv ienv.inf_m ∧
      // menv_alpha ienv.inf_m tenv.m ∧
      ienv_ok (count (infer_st_next_uvar st)) ienv /\
      t_wfs (infer_st_subst st) /\
      FDOM (infer_st_subst st) SUBSET count (infer_st_next_uvar st)
        /\
      sub_completion (num_tvs tenvE) (infer_st_next_uvar st)
        (infer_st_subst st) constraints s /\
      FDOM s = count (infer_st_next_uvar st) /\
      env_rel_complete s ienv tenv tenvE ==>
      (?env' st' s' constraints'.
        infer_funs loc ienv funs st = (M_success env',st') /\
        sub_completion (num_tvs tenvE) (infer_st_next_uvar st')
          (infer_st_subst st') constraints' s' /\
        FDOM (infer_st_subst st') SUBSET count (infer_st_next_uvar
          st') /\
        FDOM s' = count (infer_st_next_uvar st') /\
        t_compat s s' /\
        MAP SND env = MAP (convert_t o t_walkstar s') env')))`,
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["id"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
