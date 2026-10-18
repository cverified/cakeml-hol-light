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

(* HOL4 type_eDetermScript.sml:442-450: code that the source has in a
   comment *)
