(* ======================================================== *)
(*  word_unreachProof: ported from HOL4's
    compiler/backend/proofs/word_unreachProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for word_unreach
*)

needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_unreach.ml";;

(* HOL4 word_unreachProofScript.sml:10: ML code, not ported *)

(* -- proofs about semantics -- *)

let copy_vars_def = cake_define_list
  [`word_unreachProof_copy_vars [] from to = to`;
   `word_unreachProof_copy_vars ((l,r) :: rest) from to =
      sptree_insert l (THE (sptree_lookup r from))
        (word_unreachProof_copy_vars rest from to)`];;
hol4_overload "copy_vars" "word_unreachProof_copy_vars";;

(* HOL4 word_unreachProofScript.sml:351-364: ML code, not ported *)

(* HOL4 word_unreachProofScript.sml:366: ML code, not ported *)
