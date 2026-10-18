(* ======================================================== *)
(*  infer_eSound: ported from HOL4's
    compiler/inference/proofs/infer_eSoundScript.sml  *)
(* ======================================================== *)

(*
  Prove soundness of the type inferencer for the expression-level.
*)

needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/proofs/envRel.ml";;
needs "compiler/inference/unify.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* ---------- sub_completion ---------- *)

(* ---------- Soundness ---------- *)

(* HOL4 infer_eSoundScript.sml:435-450: ML code, not ported *)

(* HOL4 infer_eSoundScript.sml:518-560: ML code, not ported *)
