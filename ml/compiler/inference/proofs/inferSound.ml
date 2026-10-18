(* ======================================================== *)
(*  inferSound: ported from HOL4's
    compiler/inference/proofs/inferSoundScript.sml
    A proof theory, with 1 definition and 11 theorems.  Needed by
    compilerProof.ml.  *)
(* ======================================================== *)

(*
  Proves soundness of the type inferencer: any type assignment
  produced by the type inferencer is a valid type for the program.
*)

needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/proofs/envRel.ml";;
needs "compiler/inference/proofs/infer_eComplete.ml";;
needs "compiler/inference/proofs/infer_eSound.ml";;
needs "compiler/inference/proofs/type_eDeterm.ml";;
needs "compiler/inference/unify.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

(* TODO: This should be generalized eventually *)

(* TODO: The generated set of type identifiers (tids)
  must be related to st2.next_id in some way
  The current relation might be wrong *)

(* the set of ids n1 .... n2-1 *)
let set_ids_def = cake_define
  `set_ids n1 (n2:num) = {m | n1 <= m /\ m < n2}`;;

(* HOL4 inferSoundScript.sml:133-134: ML code, not ported *)

(* HOL4 inferSoundScript.sml:754-1137: code that the source has in a
   comment *)
