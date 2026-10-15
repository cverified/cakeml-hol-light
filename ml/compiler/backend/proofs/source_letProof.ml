(* ======================================================== *)
(*  source_letProof: ported from HOL4's
    compiler/backend/proofs/source_letProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness for the source_let pass.
 *)

needs "compiler/backend/proofs/source_evalProof.ml";;
needs "compiler/backend/source_let.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/semantics.ml";;
