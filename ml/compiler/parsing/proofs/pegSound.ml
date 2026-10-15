(* ======================================================== *)
(*  pegSound: ported from HOL4's
    compiler/parsing/proofs/pegSoundScript.sml  *)
(* ======================================================== *)

(*
  Soundness proof for the parser. If the parser returns a parse tree,
  then it is valid w.r.t. the specification grammar.
*)

needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/parsing/cmlPEG.ml";;
needs "lib/grammar.ml";;
needs "lib/peg.ml";;
needs "semantics/gram.ml";;
needs "semantics/proofs/gramProps.ml";;
needs "semantics/typeSystem.ml";;

(* Set up ML bindings *)
(* HOL4 ML code, not ported:
open pegTheory cmlPEGTheory gramTheory gramPropsTheory grammarTheory;
*)

(* HOL4 ML code, not ported:
infix >*
fun t1 >* t2 = (t1 >> conj_tac) >- t2
*)
(* HOL4 overload (expanded in the port):
     choicel = cmlPEG$choicel *)

(* HOL4 ML code, not ported:
val _ = augment_srw_ss [rewrites [
  peg_eval_seql_CONS, peg_eval_tok_SOME, tokeq_def, bindNT_def,
    mktokLf_def,
  peg_eval_choicel_CONS, pegf_def, peg_eval_seq_SOME, pnt_def,
    peg_eval_try,
  try_def,resultmap_EQ_Success]]
*)

let pegsym_to_sym_def = cake_define
  `pegsym_to_sym x1 =
        match x1 with
          (tok P f) -> if f = mktokLf then
            {(TOK:tokens_token->(tokens_token,MMLnonT)grammar_symbol) t
            | P t} else {}
        | (nt N f) -> {NT N}
        | _1 -> {}`;;

(* HOL4 ML code, not ported:
val ptree_list_loc_def = grammarTheory.ptree_list_loc_def
*)

(* left recursive rules in the grammar turn into calls to rpt in the
   PEG,
   and this in turn requires inductions *)

(* HOL4 ML code, not ported:
val pmap_cases =
  rpt ((rename [‘(_,_) = (_ ## _) pair’] >> Cases_on ‘pair’ >> fs[] >>
    rveq)
         ORELSE
       (rename [‘(_ ## _) pair = (_,_)’] >> Cases_on ‘pair’ >> fs[] >>
         rveq))
*)
