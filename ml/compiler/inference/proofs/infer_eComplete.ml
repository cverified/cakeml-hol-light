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
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

(*Useful lemmas about pure add constraints, some of these imply the others*)

(*t_compat is preserved over certain types of pure_add_constraints*)

(*If pure add constraints succeeds then the constraints all unify*)

(*behaves like a function if the first 2 arguments are equal*)

(*1 direction is sufficient to imply the other*)

(* HOL4 infer_eCompleteScript.sml:122: ML code, not ported *)

(*End pure_add_constraints stuff*)

(*Can't find a version of this in the right direction*)

(*Ignore increment on deBrujin vars*)

(*Adding a list of keys that did not already exist is safe*)

(*t_compat preserves all grounded (no unification variable after walk) terms*)

(*Remove every uvar in the FDOM if we walkstar using a completed map*)

(*Double sided t_compat thm*)

(*Free properties when extending the completed map with uvar->ground var*)

(*This occurs when looking up a list updated fmap*)
(* HOL4 infer_eCompleteScript.sml:629-645: a proof *)

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

(*Substituting every tvs away with something that has no tvs leaves none left*)

(*Specialize check_t_less a bit since we use this form a lot*)

(*This should be general enough to prove both Mat and Handle cases*)
