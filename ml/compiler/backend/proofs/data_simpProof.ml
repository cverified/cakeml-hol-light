(* ======================================================== *)
(*  data_simpProof: ported from HOL4's
    compiler/backend/proofs/data_simpProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for data_simp
*)

needs "compiler/backend/data_simp.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;

(* The Seq-with-Skip continuation is the identity on a result pair: the
   inner lambda from unfolding `evaluate (Seq _ Skip)` collapses. *)
