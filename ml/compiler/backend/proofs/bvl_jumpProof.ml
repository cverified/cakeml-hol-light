(* ======================================================== *)
(*  bvl_jumpProof: ported from HOL4's
    compiler/backend/proofs/bvl_jumpProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for bvl_jump
*)

needs "compiler/backend/bvl_jump.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
