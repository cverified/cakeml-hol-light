(* ======================================================== *)
(*  envRel: ported from HOL4's
    compiler/inference/proofs/envRelScript.sml
    A proof theory, with 8 definitions and 37 theorems.  Needed by
    compilerProof.ml, inferComplete.ml, inferSound.ml,
    infer_eComplete.ml, infer_eSound.ml and type_eDeterm.ml.  *)
(* ======================================================== *)

(*
  Relating inference and type system environments.
*)

needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/unify.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

let _ = do_list hide_constant ["id"];;

(* ---------- Converting infer types and envs to type system ones ---------- *)

let _ = size_thms "infer_t";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 envRelScript.sml:16-23: the tactic that proves the
   termination *)
let convert_t_def = cake_define_list_try (fun () ->
  `MEASURE infer_t_size`)
  [`convert_t (Infer_Tvar_db n) = Tvar_db n`;
   `convert_t (Infer_Tapp ts tc) = Tapp (MAP convert_t ts) tc`];;

let convert_env_def = cake_define
  `convert_env s env = MAP (\(x,t). (x,convert_t (t_walkstar s t)))
  env`;;

(* HOL4 envRelScript.sml:29-42: code that the source has in a comment *)

let check_convert_freevars = prove
 (`(!tvs uvs t. check_t tvs uvs t ==> (uvs = {}) ==> check_freevars
  tvs [] (convert_t t))`,
  CHEAT_TAC);;

let check_t_to_check_freevars = prove
 (`!tvs (n:num->bool) t. check_t tvs {} t ==> check_freevars tvs []
  (convert_t t)`,
  CHEAT_TAC);;

let convert_inc = prove
 (`!t tvs tvs'.
    check_t tvs' {} t ==>
    (convert_t (infer_deBruijn_inc tvs t) = deBruijn_inc 0 tvs
      (convert_t t))`,
  CHEAT_TAC);;

(* HOL4 envRelScript.sml:74: ML code, not ported *)

let db_subst_infer_subst_swap = prove
 (`(!t s tvs uvar n.
    t_wfs s /\
    count (uvar + tvs) SUBSET FDOM s /\
    (!uv. uv IN FDOM s ==> check_t n {} (t_walkstar s (Infer_Tuvar
      uv))) /\
    check_t tvs (FDOM s) t ==>
    (convert_t
      (t_walkstar s
         (infer_deBruijn_subst
            (MAP (\n. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs))
            t)) =
     deBruijn_subst 0
      (MAP (convert_t o t_walkstar s)
         (MAP (\n. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs)))
      (convert_t (t_walkstar (infer_deBruijn_inc tvs o_f s) t)))) /\
   (!ts s tvs uvar n.
    t_wfs s /\
    count (uvar + tvs) SUBSET FDOM s /\
    (!uv. uv IN FDOM s ==> check_t n {} (t_walkstar s (Infer_Tuvar
      uv))) /\
    EVERY (\t. check_t tvs (FDOM s) t) ts ==>
    (MAP (convert_t o
         t_walkstar s o
         infer_deBruijn_subst (MAP (\n. Infer_Tuvar (uvar + n))
           (COUNT_LIST tvs)))
        ts =
     MAP (deBruijn_subst 0 (MAP (convert_t o t_walkstar s) (MAP (\n.
       Infer_Tuvar (uvar + n)) (COUNT_LIST tvs))) o
         convert_t o
         t_walkstar (infer_deBruijn_inc tvs o_f s))
        ts))`,
  CHEAT_TAC);;

let inc_convert_t = prove
 (`(!t tvs' tvs. check_t tvs' {} t ==> (deBruijn_inc tvs' tvs (convert_t
  t) = convert_t t)) /\
   (!ts tvs' tvs. EVERY (check_t tvs' {}) ts ==> (MAP (deBruijn_inc
     tvs' tvs o convert_t) ts = MAP convert_t ts))`,
  CHEAT_TAC);;

let convert_t_subst = prove
 (`(!t tvs ts'.
      (LENGTH tvs = LENGTH ts') /\
      check_freevars 0 tvs t ==>
      convert_t (infer_type_subst (ZIP tvs ts') t) =
      type_subst (alist_to_fmap (ZIP tvs (MAP convert_t ts'))) t) /\
   (!ts tvs ts'.
      (LENGTH tvs = LENGTH ts') /\
      EVERY (check_freevars 0 tvs) ts ==>
      MAP convert_t (MAP (infer_type_subst (ZIP tvs ts')) ts) =
      MAP (type_subst (alist_to_fmap (ZIP tvs (MAP convert_t
        ts')))) ts)`,
  CHEAT_TAC);;

let deBruijn_subst_convert = prove
 (`(!t.
   check_t n {} t ==>
   deBruijn_subst 0 (MAP convert_t subst) (convert_t t) =
   convert_t (infer_deBruijn_subst subst t)) /\
   (!ts.
   EVERY (check_t n {}) ts ==>
   MAP ((deBruijn_subst 0 (MAP convert_t subst)) o convert_t) ts =
   MAP (convert_t o (infer_deBruijn_subst subst)) ts)`,
  CHEAT_TAC);;

let check_freevars_empty_convert_unconvert_id = prove
 (`!t. check_freevars n [] t ==> convert_t (unconvert_t t) = t`,
  CHEAT_TAC);;

let check_t_empty_unconvert_convert_id = prove
 (`!t n. check_t n {} t ==>
    unconvert_t (convert_t t) = t`,
  CHEAT_TAC);;

let check_freevars_to_check_t = prove
 (`!t z. check_freevars n [] t ==> check_t n {} (unconvert_t t)`,
  CHEAT_TAC);;

let infer_type_subst_nil = prove
 (`(!t. check_freevars n [] t ==> infer_type_subst [] t = unconvert_t t)
  /\
    (!ts. EVERY (check_freevars n []) ts ==> MAP (infer_type_subst
      []) ts = MAP unconvert_t ts)`,
  CHEAT_TAC);;

(* ---------- relating inference and type system environments ---------- *)


(* We want tscheme_approx max_tvs s (tvs, t) (tvs', t') to hold iff (tvs', t') is
 * more general than (tvs, t) under substitution s constraining unification
 * variables.
 *
 * In general, there are 4 classes of variables that can appear in ts and ts':
 * - de Bruijn variables less than tvs, and hence bound by the type scheme,
 * - de Bruijn variables ≥ tvs that are bound in the enclosing context which
 *     binds max_tvs variables, appearing in t as tvs to tvs + max_tvs,
 * - unification variables constrained by s, and
 * - other unification variables.
 *
 * We assume that s only mentions de Bruijn variables bound in the context, but
 * unlike in t, they appear as 0 to max_tvs (since the substitution is not under
 * the typescheme binder).
 *
 * We'd like to instantiate the bound de Bruijn variables in t' so that it
 * matches t. To do so, we must apply s to both t and t', since they may contain
 * different bound unification variables that are constrained to be the same by
 * s. However, since s may contain de Bruijn type variables, we have to either
 * shift it by tvs/tvs' to avoid capture, or first instantiate both type schemes.
 * Since we have to instantiate one anyway, we choose the latter option.
 *
 * The main question is how to instantiate t. Crucially, we don't want to
 * over-specialise t, so that a less general t' can be matched to t. One
 * approach would be to instantiate t with fresh variables of some sort;
 * however, that does not work well with our general setup which requires all
 * type variables to be explicitly bound somewhere. Instead, we require that t'
 * be able to match the result of any instantiation of t. In fact, we slightly
 * restrict the form of instantiation to be on in which the instantiation has
 * only good de Bruijn and unification variables, and the substitution for t is
 * also applied to the substitution for t'. So t''s substitution is just
 * matching t, and then instantiation of t is making things good for the
 * walkstar
 *
 * *)

let tscheme_approx_def = cake_define
  `tscheme_approx max_tvs s (tvs,t) (tvs',t') <=>
     (?subst'.
       LENGTH subst' = tvs' /\
       EVERY (check_t (max_tvs + tvs) (FDOM s)) subst' /\
       (!subst.
        LENGTH subst = tvs ==>
        t_walkstar s (infer_deBruijn_subst subst t) =
        t_walkstar s (infer_deBruijn_subst (MAP
          (infer_deBruijn_subst subst) subst') t')))`;;

let tscheme_approx_thm = prove
 (`!t' max_tvs s tvs tvs' t.
    t_wfs s ==>
    (tscheme_approx max_tvs s (tvs,t) (tvs',t') ==>
     (!subst.
      LENGTH subst = tvs /\
      EVERY (check_t max_tvs {}) subst ==>
      (?subst'.
        LENGTH subst' = tvs' /\
        EVERY (check_t max_tvs (FDOM s)) subst' /\
        t_walkstar s (infer_deBruijn_subst subst t) = t_walkstar s
          (infer_deBruijn_subst subst' t'))))`,
  CHEAT_TAC);;

let tscheme_approx_refl = prove
 (`!max_tvs s tvs t. tscheme_approx max_tvs s (tvs,t) (tvs,t)`,
  CHEAT_TAC);;

(* TODO: should be able to use max_tvs in place of 0 *)
let tscheme_approx_trans = prove
 (`tscheme_approx max_tvs s (tvs1,t1) (tvs2,t2) /\
   tscheme_approx 0 s (tvs2,t2) (tvs3,t3) ==>
   tscheme_approx max_tvs s (tvs1,t1) (tvs3,t3)`,
  CHEAT_TAC);;

let unconvert_db_subst = prove
 (`!t subst fvs l.
     check_freevars l [] t ==>
     unconvert_t (deBruijn_subst 0 subst t) =
     infer_deBruijn_subst (MAP unconvert_t subst) (unconvert_t t)`,
  CHEAT_TAC);;

let tscheme_inst_to_approx = prove
 (`tscheme_inst (tvs,t) (tvs',t') ==>
   tscheme_approx 0 FEMPTY (tvs,unconvert_t t) (tvs',unconvert_t
     t')`,
  CHEAT_TAC);;

let env_rel_sound_def = cake_define
  `env_rel_sound s ienv tenv tenvE <=> inf_env_inf_t
     ienv = type_env_t tenv /\ inf_env_inf_c
     ienv = type_env_c tenv /\
     (!x ts.
       nsLookup (inf_env_inf_v ienv) x = SOME ts ==>
       (?tvs' t'.
         check_freevars (tvs' + num_tvs tenvE) [] t' /\
         lookup_var x tenvE tenv = SOME (tvs',t') /\
         tscheme_approx (num_tvs tenvE) s ts (tvs',unconvert_t
           t')))`;;

let env_rel_sound_lookup_none = prove
 (`!ienv tenv s tenvE id'.
    env_rel_sound s ienv tenv tenvE /\
    lookup_var id' tenvE tenv = NONE ==>
    nsLookup (inf_env_inf_v ienv) id' = NONE`,
  CHEAT_TAC);;

let env_rel_sound_lookup_some = prove
 (`!id' ts s ienv tenv tenvE.
    nsLookup (inf_env_inf_v ienv) id' = SOME ts /\ env_rel_sound s
      ienv tenv tenvE ==>
    (?tvs' t'.
      check_freevars (tvs' + num_tvs tenvE) [] t' /\
      lookup_var id' tenvE tenv = SOME (tvs',t') /\
      tscheme_approx (num_tvs tenvE) s ts (tvs',unconvert_t t'))`,
  CHEAT_TAC);;

let db_subst_infer_subst_swap3 = prove
 (`!t tvs s subst.
    t_wfs s /\
    check_freevars tvs [] t ==>
    convert_t (t_walkstar s (infer_deBruijn_subst subst (unconvert_t
      t))) =
    deBruijn_subst 0 (MAP (convert_t o t_walkstar s) subst) t`,
  CHEAT_TAC);;

let tscheme_approx_weakening = prove
 (`!tvs tvs' s1 s2 ts1 ts2.
    tscheme_approx tvs s1 ts1 ts2 /\
    t_wfs s2 /\
    s1 SUBMAP s2 /\
    tvs <= tvs' ==>
    tscheme_approx tvs' s2 ts1 ts2`,
  CHEAT_TAC);;

let env_rel_sound_extend_tvs = prove
 (`!s ienv tenv bindings tvs.
    t_wfs s /\
    env_rel_sound s ienv tenv typeSystem_Empty ==>
    env_rel_sound s ienv tenv (bind_tvar tvs typeSystem_Empty)`,
  CHEAT_TAC);;

let tscheme_approx0 = prove
 (`!tvs s t. t_wfs s ==> tscheme_approx tvs s (0,t) (0,t_walkstar s t)`,
  CHEAT_TAC);;

let env_rel_sound_extend0 = prove
 (`!s x t ienv tenv tenvE.
    env_rel_sound s ienv tenv tenvE /\
    t_wfs s /\
    check_t (num_tvs tenvE) (FDOM s) t /\
    (!uv. uv IN FDOM s ==> check_t (num_tvs tenvE) {} (t_walkstar s
      (Infer_Tuvar uv))) ==>
    env_rel_sound s (inf_env_inf_v_fupd (K (nsBind x (0,t)
      (inf_env_inf_v ienv))) ienv)
      tenv (typeSystem_Bind_name x 0 (convert_t (t_walkstar s t))
        tenvE)`,
  CHEAT_TAC);;

let env_rel_sound_merge0 = prove
 (`!s ienv bindings tenv tenvE.
    t_wfs s /\
    (!uv. uv IN FDOM s ==> check_t (num_tvs tenvE) {} (t_walkstar s
      (Infer_Tuvar uv))) /\
    EVERY (\(x,t). check_t 0 (FDOM s) t) bindings /\
    env_rel_sound s ienv tenv tenvE ==>
    env_rel_sound s
       (inf_env_inf_v_fupd (K (nsAppend (alist_to_ns (MAP (\(n,t).
         (n,0,t)) bindings)) (inf_env_inf_v ienv))) ienv)
       tenv
       (bind_var_list 0 (convert_env s bindings) tenvE)`,
  CHEAT_TAC);;

let env_rel_e_sound_letrec_merge0 = prove
 (`!funs ienv tenv tenvE s uvs.
    t_wfs s /\
    (!uv. uv IN FDOM s ==> check_t (num_tvs tenvE) {} (t_walkstar s
      (Infer_Tuvar uv))) /\
    count (uvs + LENGTH funs) SUBSET FDOM s /\
    env_rel_sound s ienv tenv tenvE ==>
    env_rel_sound s
      (inf_env_inf_v_fupd (K
        (nsAppend
          (alist_to_ns
            (MAP2 (\(f,x,e) uvar. (f,0,uvar))
              funs
              (MAP (\n. Infer_Tuvar (uvs + n)) (COUNT_LIST (LENGTH
                funs))))) (inf_env_inf_v
          ienv))) ienv)
      tenv
      (bind_var_list 0 (MAP2 (\(f,x,e) t. (f,t))
                         funs
                         (MAP (\n. convert_t (t_walkstar s
                           (Infer_Tuvar (uvs + n))))
                           (COUNT_LIST (LENGTH funs)))) tenvE)`,
  CHEAT_TAC);;

let env_rel_complete_def = cake_define
  `env_rel_complete s ienv tenv tenvE <=> inf_env_inf_t
     ienv = type_env_t tenv /\ inf_env_inf_c
     ienv = type_env_c tenv /\
     (!x tvs t.
       lookup_var x tenvE tenv = SOME (tvs,t) ==>
       (
        // t cannot have tyvars inside
        ?n. check_freevars n [] t) /\
       (?tvs' t'.
         nsLookup (inf_env_inf_v ienv) x = SOME (tvs',t') /\
         // A stronger version is guaranteed by ienv_ok
         // check_t (tvs' + num_tvs tenvE) {} t' ∧
         tscheme_approx (num_tvs tenvE) s (tvs,unconvert_t t)
           (tvs',t')))`;;

let env_rel_complete_lookup_none = prove
 (`!ienv tenv s tenvE x.
    env_rel_complete s ienv tenv tenvE /\
    nsLookup (inf_env_inf_v ienv) x = NONE ==>
    nsLookup (type_env_v tenv) x = NONE`,
  CHEAT_TAC);;

let env_rel_e_sound_empty_to = prove
 (`!s ienv tenv tenvE.
    t_wfs s /\ ienv_ok {} ienv /\ env_rel_sound FEMPTY ienv tenv
      tenvE ==>
    env_rel_sound s ienv tenv tenvE`,
  CHEAT_TAC);;

(* Environment relation at infer_d and above *)
let envRel_env_rel_def = cake_define
  `envRel_env_rel tenv ienv <=>
    ienv_ok {} ienv /\
    tenv_ok tenv /\
    (
     // To rule out 1 env with an empty module and the other without that module at all
     !x. nsLookupMod (inf_env_inf_v ienv) x = NONE <=> nsLookupMod
       (type_env_v tenv) x = NONE) /\
    env_rel_sound FEMPTY ienv tenv typeSystem_Empty /\
    env_rel_complete FEMPTY ienv tenv typeSystem_Empty`;;
hol4_overload "env_rel" "envRel_env_rel";;

(* [simp] *)
let lookup_varE_empty = prove
 (`!x. lookup_varE x (typeSystem_Empty:tenv_val_exp) = NONE`,
  CHEAT_TAC);;

let env_rel_extend = prove
 (`!tenv1 ienv1 tenv2 ienv2.
    envRel_env_rel tenv1 ienv1 /\
    envRel_env_rel tenv2 ienv2 ==>
    envRel_env_rel (extend_dec_tenv tenv1 tenv2) (extend_dec_ienv
      ienv1 ienv2)`,
  CHEAT_TAC);;

(* [simp] *)
let env_rel_empty = prove
 (`envRel_env_rel (mk_type_env nsEmpty nsEmpty nsEmpty)
           (mk_inf_env nsEmpty nsEmpty nsEmpty)`,
  CHEAT_TAC);;

let env_rel_lift = prove
 (`!tenv ienv mn. envRel_env_rel tenv ienv ==> envRel_env_rel
  (tenvLift mn tenv) (lift_ienv mn ienv)`,
  CHEAT_TAC);;

let ienv_to_tenv_def = cake_define
  `ienv_to_tenv ienv =
     mk_type_env (nsMap (\(tvs,t). (tvs,convert_t t))
       (inf_env_inf_v ienv)) (inf_env_inf_c ienv) (inf_env_inf_t
       ienv)`;;

let ienv_to_tenv_extend = prove
 (`!ienv1 ienv2.
    ienv_to_tenv (extend_dec_ienv ienv2 ienv1) =
    extend_dec_tenv (ienv_to_tenv ienv2) (ienv_to_tenv ienv1)`,
  CHEAT_TAC);;

let ienv_to_tenv_lift = prove
 (`!mn ienv. ienv_to_tenv (lift_ienv mn ienv) = tenvLift mn
  (ienv_to_tenv ienv)`,
  CHEAT_TAC);;

let env_rel_ienv_to_tenv = prove
 (`!ienv. ienv_ok {} ienv ==> envRel_env_rel (ienv_to_tenv ienv) ienv`,
  CHEAT_TAC);;

let tenv_to_ienv_def = cake_define
  `tenv_to_ienv tenv =
     mk_inf_env (nsMap (\(tvs,t). (tvs,unconvert_t t)) (type_env_v
       tenv)) (type_env_c tenv) (type_env_t tenv)`;;

let tenv_to_ienv_extend = prove
 (`!tenv1 tenv2.
    tenv_to_ienv (extend_dec_tenv tenv2 tenv1) =
    extend_dec_ienv (tenv_to_ienv tenv2) (tenv_to_ienv tenv1)`,
  CHEAT_TAC);;

let env_rel_tenv_to_ienv = prove
 (`!tenv. tenv_ok tenv ==> envRel_env_rel tenv (tenv_to_ienv tenv)`,
  CHEAT_TAC);;

let tenv_to_ienv_lift = prove
 (`!mn tenv. tenv_to_ienv (tenvLift mn tenv) = lift_ienv mn
  (tenv_to_ienv tenv)`,
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["id"];;
