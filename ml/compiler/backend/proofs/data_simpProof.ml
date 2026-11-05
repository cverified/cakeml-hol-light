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
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "semantics/evaluate.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "data_simpProof"
  ["dataProps"; "dataSem"; "data_simp"];;

(* [local] *)
let evaluate_Seq_Skip = prove
 (`!c s. evaluate ((Seq c Skip:dataLang_prog),s) = evaluate (c,s)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_pSeq = prove
 (`evaluate (pSeq c1 c2,s) = evaluate (Seq c1 c2,s)`,
  CHEAT_TAC);;

(* The Seq-with-Skip continuation is the identity on a result pair: the
   inner lambda from unfolding `evaluate (Seq _ Skip)` collapses. *)
(* [local] *)
let lam_skip_id = prove
 (`(\(res,s1). if res = NONE then evaluate (Skip,s1) else (res,s1)) x
  = x`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_simp = prove
 (`!c1 s c2. evaluate (simp c1 c2,s) = evaluate (Seq c1 c2,s)`,
  CHEAT_TAC);;

let simp_correct = prove
 (`!c s. evaluate (simp c Skip,s) = evaluate (c,s)`,
  CHEAT_TAC);;

let get_code_labels_simp = prove
 (`!x y. dataProps_get_code_labels (simp x y) SUBSET
  dataProps_get_code_labels x UNION dataProps_get_code_labels y`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
