(* ======================================================== *)
(*  bvl_jumpProof: ported from HOL4's
    compiler/backend/proofs/bvl_jumpProofScript.sml
    A proof theory about bvl_jump.ml, with no definitions and 3
    theorems.  Needed by clos_to_bvlProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for bvl_jump
*)

needs "compiler/backend/bvl_jump.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
