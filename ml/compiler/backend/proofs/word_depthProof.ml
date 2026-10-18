(* ======================================================== *)
(*  word_depthProof: ported from HOL4's
    compiler/backend/proofs/word_depthProofScript.sml  *)
(* ======================================================== *)

(*
  Proves correctness of the max_depth applied to the call graph of a
  wordLang program as produced by the word_depth$call_graph function.
*)

needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_depth.ml";;

(* HOL4 word_depthProofScript.sml:290-382: ML code, not ported *)
  (* non-tail-call case *)
(* HOL4 word_depthProofScript.sml:384-732: ML code, not ported *)


(* HOL4 word_depthProofScript.sml:735-753: ML code, not ported *)
  (* cont_loop case: res' = NONE or Continue 0 *)
(* HOL4 word_depthProofScript.sml:755-757: ML code, not ported *)
     (* res' = NONE *)
(* HOL4 word_depthProofScript.sml:759-769: ML code, not ported *)
     (* res' = SOME (Continue 0) *)
(* HOL4 word_depthProofScript.sml:771-782: ML code, not ported *)
  (* exit_loop case — Break 0 auto-solved by gvs with strengthened IH *)
(* HOL4 word_depthProofScript.sml:784-786: ML code, not ported *)

(* HOL4 word_depthProofScript.sml:788: ML code, not ported *)
