(* ======================================================== *)
(*  word_removeProof: ported from HOL4's
    compiler/backend/proofs/word_removeProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for word_remove
*)

needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/word_remove.ml";;

let compile_state_def = cake_define
  `compile_state clk c s = wordSem_state_compile_fupd (K c)
  (wordSem_state_compile_oracle_fupd (K ((I ## (MAP (I ## I ##
  remove_must_terminate))) o wordSem_state_compile_oracle s))
  (wordSem_state_code_fupd (K (sptree_map (I ## remove_must_terminate)
  (wordSem_state_code s))) (wordSem_state_termdep_fupd (K 0)
  (state_clock_fupd (K (state_clock s + clk))
     s))))`;;

(* HOL4 word_removeProofScript.sml:401-428: a proof *)

(* HOL4 word_removeProofScript.sml:430: a proof *)
