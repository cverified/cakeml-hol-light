(* ======================================================== *)
(*  source_to_sourceProof: ported from HOL4's
    compiler/backend/proofs/source_to_sourceProofScript.sml
    A proof theory about source_to_source.ml, with no definitions
    and 2 theorems.  Needed by backendProof.ml.  *)
(* ======================================================== *)

(*
  Proof of correctness for source_to_source.
 *)

needs "compiler/backend/proofs/source_evalProof.ml";;
needs "compiler/backend/proofs/source_letProof.ml";;
needs "compiler/backend/source_to_source.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/semantics.ml";;
