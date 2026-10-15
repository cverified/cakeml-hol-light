(* ======================================================== *)
(*  envRel: ported from HOL4's
    compiler/inference/proofs/envRelScript.sml  *)
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

(* ---------- Converting infer types and envs to type system ones
   ---------- *)

let convert_t_def = cake_define_list
  [`convert_t (Infer_Tvar_db n) = Tvar_db n`;
   `convert_t (Infer_Tapp ts tc) = Tapp (MAP convert_t ts) tc`];;

let convert_env_def = cake_define
  `convert_env s env = MAP (\(x,t). (x,convert_t (t_walkstar s t)))
  env`;;

(*
Definition convert_decls_def:
  convert_decls idecls =
  <| defined_mods := set idecls.inf_defined_mods;
     defined_types :=  set idecls.inf_defined_types;
     defined_exns := set idecls.inf_defined_exns|>
End

Theorem convert_append_decls:
 !decls1 decls2. convert_decls (append_decls decls1 decls2) =
   union_decls (convert_decls decls1) (convert_decls decls2)
Proof
 rw [convert_decls_def, append_decls_def, union_decls_def]
QED
*)

(* HOL4 ML code, not ported:
val infer_t_induction = infer_tTheory.infer_t_induction;
*)

(* ---------- relating inference and type system environments ----------
   *)


(* We want tscheme_approx max_tvs s (tvs, t) (tvs', t') to hold iff
   (tvs', t') is
 * more general than (tvs, t) under substitution s constraining
   unification
 * variables.
 *
 * In general, there are 4 classes of variables that can appear in ts
   and ts':
 * - de Bruijn variables less than tvs, and hence bound by the type
   scheme,
 * - de Bruijn variables ≥ tvs that are bound in the enclosing context
   which
 *     binds max_tvs variables, appearing in t as tvs to tvs + max_tvs,
 * - unification variables constrained by s, and
 * - other unification variables.
 *
 * We assume that s only mentions de Bruijn variables bound in the
   context, but
 * unlike in t, they appear as 0 to max_tvs (since the substitution is
   not under
 * the typescheme binder).
 *
 * We'd like to instantiate the bound de Bruijn variables in t' so that
   it
 * matches t. To do so, we must apply s to both t and t', since they may
   contain
 * different bound unification variables that are constrained to be the
   same by
 * s. However, since s may contain de Bruijn type variables, we have to
   either
 * shift it by tvs/tvs' to avoid capture, or first instantiate both type
   schemes.
 * Since we have to instantiate one anyway, we choose the latter option.
 *
 * The main question is how to instantiate t. Crucially, we don't want
   to
 * over-specialise t, so that a less general t' can be matched to t. One
 * approach would be to instantiate t with fresh variables of some sort;
 * however, that does not work well with our general setup which
   requires all
 * type variables to be explicitly bound somewhere. Instead, we require
   that t'
 * be able to match the result of any instantiation of t. In fact, we
   slightly
 * restrict the form of instantiation to be on in which the
   instantiation has
 * only good de Bruijn and unification variables, and the substitution
   for t is
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

(* TODO: should be able to use max_tvs in place of 0 *)

let env_rel_sound_def = cake_define
  `env_rel_sound s ienv tenv tenvE <=> inf_env_inf_t
     ienv = type_env_t tenv /\ inf_env_inf_c
     ienv = c tenv /\
     (!x ts.
       nsLookup (inf_env_inf_v ienv) x = SOME ts ==>
       (?tvs' t'.
         check_freevars (tvs' + num_tvs tenvE) [] t' /\
         lookup_var x tenvE tenv = SOME (tvs',t') /\
         tscheme_approx (num_tvs tenvE) s ts (tvs',unconvert_t
           t')))`;;

let env_rel_complete_def = cake_define
  `env_rel_complete s ienv tenv tenvE <=> inf_env_inf_t
     ienv = type_env_t tenv /\ inf_env_inf_c
     ienv = c tenv /\
     (!x tvs t.
       lookup_var x tenvE tenv = SOME (tvs,t) ==>
       (?n. check_freevars n [] t) /\
       (?tvs' t'.
         nsLookup (inf_env_inf_v ienv) x = SOME (tvs',t') /\
         tscheme_approx (num_tvs tenvE) s (tvs,unconvert_t t)
           (tvs',t')))`;;

(* Environment relation at infer_d and above *)
let env_rel_def = cake_define
  `envRel_env_rel tenv ienv <=>
    ienv_ok {} ienv /\
    tenv_ok tenv /\
    (!x. nsLookupMod (inf_env_inf_v ienv) x = NONE <=> nsLookupMod (v
      tenv) x = NONE) /\
    env_rel_sound FEMPTY ienv tenv typeSystem_Empty /\
    env_rel_complete FEMPTY ienv tenv typeSystem_Empty`;;

let ienv_to_tenv_def = cake_define
  `ienv_to_tenv ienv =
     mk_type_env (nsMap (\(tvs,t). (tvs,convert_t t))
       (inf_env_inf_v ienv)) (inf_env_inf_c ienv) (inf_env_inf_t
       ienv)`;;

let tenv_to_ienv_def = cake_define
  `tenv_to_ienv tenv =
     mk_inf_env (nsMap (\(tvs,t). (tvs,unconvert_t t)) (v tenv))
       (c tenv) (type_env_t tenv)`;;
