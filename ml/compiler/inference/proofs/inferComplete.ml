(* ======================================================== *)
(*  inferComplete: ported from HOL4's
    compiler/inference/proofs/inferCompleteScript.sml  *)
(* ======================================================== *)

(*
  Proves completeness of the type inferencer, i.e. if there is a type
  for the program, then the type inferencer will find a type (the most
  general type).
*)

needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/proofs/envRel.ml";;
needs "compiler/inference/proofs/infer_eComplete.ml";;
needs "compiler/inference/proofs/infer_eSound.ml";;
needs "compiler/inference/proofs/type_dCanon.ml";;
needs "compiler/inference/proofs/type_eDeterm.ml";;
needs "compiler/inference/unify.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

(* HOL4 inferCompleteScript.sml:39-45: ML code, not ported *)


(* HOL4 inferCompleteScript.sml:569-570: ML code, not ported *)

(* HOL4 inferCompleteScript.sml:1446-1788: code that the source has
   in a comment *)
