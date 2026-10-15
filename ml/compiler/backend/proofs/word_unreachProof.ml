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

(* HOL4 ML code, not ported:
val s = ``s:('a,'c,'ffi) wordSem$state``
*)

(* -- proofs about semantics -- *)

let copy_vars_def = cake_define_list
  [`word_unreachProof_copy_vars [] from to = to`;
   `word_unreachProof_copy_vars ((l,r) :: rest) from to =
      sptree_insert l (THE (sptree_lookup r from))
        (word_unreachProof_copy_vars rest from to)`];;
hol4_overload "copy_vars" "word_unreachProof_copy_vars";;

(* HOL4 ML code, not ported:
Resume evaluate_Seq_assoc_right_lemma[Loop]:
  irule evaluate_SimpSeq \\ gvs[] \\
  qpat_x_assum `evaluate (Seq _ _, _) = _` mp_tac \\
  simp[Once evaluate_def] \\
  pairarg_tac \\ fs[] \\ strip_tac \\
  simp[Once evaluate_def] \\
  mp_tac (evaluate_Loop_body_eq
    |> INST_TYPE [beta |-> gamma, gamma |-> ``:'ffi``]
    |> Q.INST [`p2` |-> `Seq_assoc_right p1 Skip`]) \\
  impl_tac >- fs[evaluate_Seq_Skip] \\
  disch_then drule \\
  impl_tac >- (strip_tac \\ fs[]) \\
  strip_tac \\ fs[]
QED
*)

(* HOL4 ML code, not ported:
Finalise evaluate_Seq_assoc_right_lemma;
*)
