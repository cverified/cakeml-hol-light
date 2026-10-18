(* ======================================================== *)
(*  primSemEnv: ported from HOL4's
    semantics/proofs/primSemEnvScript.sml
    A proof theory, with no definitions and 2 theorems.  Needed by
    backendProof.ml and typeSound.ml.  *)
(* ======================================================== *)

(*
  Proof about the primitive semantic environment
*)

needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;
needs "semantics/primTypes.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/semantics.ml";;
needs "semantics/typeSystem.ml";;
