(* ======================================================== *)
(*  type_eDeterm: ported from HOL4's
    compiler/inference/proofs/type_eDetermScript.sml  *)
(* ======================================================== *)

(*
  Prove determinism lemmas about the type inferencer.
*)

needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/proofs/envRel.ml";;
needs "compiler/inference/proofs/infer_eComplete.ml";;
needs "compiler/inference/proofs/infer_eSound.ml";;
needs "compiler/inference/unify.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

 (*From ¬check_t 0 {} (t_walkstar s tt) it should follow that
   t_walkstar s tt must contain some unification variables.
   (*
   first_assum(
     mp_tac o (MATCH_MP (GEN_ALL(CONTRAPOS(SPEC_ALL(CONJUNCT1
       check_t_walkstar)))))) >>
   *)
   But we know that s is completed by s1 and s2 therefore those
   unification variables are exactly bound in s1 and s2 to
   Infer_Tbool and Infer_Tint, hence the walkstars must differ *)
