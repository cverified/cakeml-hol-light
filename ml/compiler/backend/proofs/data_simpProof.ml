(* ======================================================== *)
(*  data_simpProof: ported from HOL4's
    compiler/backend/proofs/data_simpProofScript.sml
    A proof theory about data_simp.ml, with no definitions and 6
    theorems.  Needed by bvi_to_dataProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for data_simp
*)

needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_simp.ml";;
needs "compiler/backend/reg_alloc/linear_scan.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "semantics/evaluate.ml";;

let evaluate_Seq_Skip = cake_theorem "evaluate_Seq_Skip[local]"
  (fun () ->
    `!c s. evaluate ((Seq c Skip:live_tree),s) = evaluate (c,s)`)
  CHEAT_TAC;;

let evaluate_pSeq = cake_theorem "evaluate_pSeq[local]"
  (fun () ->
    `evaluate (pSeq c1 c2,s) = evaluate (Seq c1 c2,s)`)
  CHEAT_TAC;;

(* The Seq-with-Skip continuation is the identity on a result pair: the
   inner lambda from unfolding `evaluate (Seq _ Skip)` collapses. *)
let lam_skip_id = cake_theorem "lam_skip_id[local]"
  (fun () ->
    `(\(res,s1). if res = NONE then evaluate (Skip,s1) else (res,s1))
  x = x`)
  CHEAT_TAC;;

let evaluate_simp = cake_theorem "evaluate_simp[local]"
  (fun () ->
    `!c1 s c2. evaluate (simp c1 c2,s) = evaluate (Seq c1 c2,s)`)
  CHEAT_TAC;;

let simp_correct = cake_theorem "simp_correct"
  (fun () ->
    `!c s. evaluate (simp c Skip,s) = evaluate (c,s)`)
  CHEAT_TAC;;

let get_code_labels_simp = cake_theorem "get_code_labels_simp"
  (fun () ->
    `!x y. dataProps_get_code_labels (simp x y) SUBSET
  dataProps_get_code_labels x UNION dataProps_get_code_labels y`)
  CHEAT_TAC;;
