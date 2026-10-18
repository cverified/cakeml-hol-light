(* ======================================================== *)
(*  data_simpProof: ported from HOL4's
    compiler/backend/proofs/data_simpProofScript.sml
    A proof theory about data_simp.ml, with no definitions and 6
    theorems.  Needed by bvi_to_dataProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for data_simp
*)

needs "compiler/backend/data_simp.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;

(* The Seq-with-Skip continuation is the identity on a result pair: the
   inner lambda from unfolding `evaluate (Seq _ Skip)` collapses. *)
