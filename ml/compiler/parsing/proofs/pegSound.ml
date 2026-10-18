(* ======================================================== *)
(*  pegSound: ported from HOL4's
    compiler/parsing/proofs/pegSoundScript.sml
    A proof theory, with 1 definition and 42 theorems.  Needed by
    compilerProof.ml and pegComplete.ml.  *)
(* ======================================================== *)

(*
  Soundness proof for the parser. If the parser returns a parse tree,
  then it is valid w.r.t. the specification grammar.
*)

needs "compiler/parsing/cmlPEG.ml";;
needs "lib/grammar.ml";;
needs "lib/peg.ml";;
needs "semantics/gram.ml";;
needs "semantics/proofs/gramProps.ml";;

(* Set up ML bindings *)
(* HOL4 pegSoundScript.sml:12: ML code, not ported *)

(* HOL4 pegSoundScript.sml:14-15: ML code, not ported *)
(* HOL4 pegSoundScript.sml:18-19: the overload choicel, which the
   port expands *)

(* HOL4 pegSoundScript.sml:115-118: ML code, not ported *)

let pegsym_to_sym_def = cake_define
  `pegsym_to_sym x1 =
        match x1 with
          peg_tok P f -> (if f = mktokLf then
            {(grammar_TOK:tokens_token->(tokens_token
            ,MMLnonT)grammar_symbol) t | P t} else {})
        | (peg_nt N f) -> {grammar_NT N}
        | _1 -> {}`;;

(* HOL4 pegSoundScript.sml:233: ML code, not ported *)

(* left recursive rules in the grammar turn into calls to rpt in the PEG,
   and this in turn requires inductions *)

(* HOL4 pegSoundScript.sml:479-482: a proof *)
