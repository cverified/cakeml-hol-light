(* ======================================================== *)
(*  caml_parser: ported from HOL4's
    compiler/parsing/ocaml/caml_parserScript.sml
    A definition theory, with 5 definitions and no theorems.  Needed
    by caml_parserProg.ml.  *)
(* ======================================================== *)

(*
  Parser entry-point for the OCaml parser.
 *)

needs "basis/pure/mlint.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/parsing/ocaml/camlPEG.ml";;
needs "compiler/parsing/ocaml/camlPtreeConversion.ml";;
needs "compiler/parsing/ocaml/caml_lex.ml";;
needs "lib/location.ml";;
needs "lib/pegexec.ml";;
needs "lib/simpleSexpParse.ml";;
needs "misc/misc.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "caml_parser"
  ["camlPEG"; "camlPtreeConversion"; "caml_lex"; "misc"; "mlint"; "mlstring"];;

(* Run the lexer and return all tokens, or a list of all errors.
 *)

let run_lexer_def = new_definition
  `run_lexer inp =
     let toks = caml_lex_lexer_fun inp in let
         errs = MAP SND (FILTER (\(peg_tok,locs). peg_tok =
           caml_lex_LexErrorT) toks) in if NULL errs then
       camlPtreeConversion_return toks
     else camlPtreeConversion_fail errs`;;

(* HOL4 caml_parserScript.sml:27-28: the overload camlpegexec, which the
   port expands *)

let caml_parser_destResult_def = new_definition
  `caml_parser_destResult x1 =
   match x1 with
     pegexec_Result (peg_Success [] x eo) ->
     peg_Success [] x eo
   | pegexec_Result (peg_Success (CONS (_,l) _) _ _) ->
     peg_Failure l "Expected to be at EOF"
   | pegexec_Result (peg_Failure fl fe) ->
     peg_Failure fl fe
   | _ ->
     peg_Failure unknown_loc "Something catastrophic happened"`;;

let caml_parser_peg_def = define_cases
  `(caml_parser_peg (peg_Failure locn err) = camlPtreeConversion_fail
    (locn,implode err)) /\
   (caml_parser_peg (peg_Success (_:(caml_lex_token#locs) list) x _) =
    camlPtreeConversion_return x)`;;

let run_parser_def,run_parser_ind = define_guess
  `run_parser toks =
     (OPTION_BIND) (caml_parser_peg (caml_parser_destResult ((\n t. peg_exec
       camlPEG (camlPEG_pnt n) t [] NONE [] pegexec_done pegexec_failed)
       camlPEG_nStart toks))) (\pt.
       match pt with
         [ptree] ->
           (match ptree_Start ptree with
             sum_INR x -> sum_INR x
           | sum_INL (loc,err) -> camlPtreeConversion_fail (loc,err))
       | _ -> camlPtreeConversion_fail (unknown_loc,(implode
         "Impossible: run_parser")))`;;

let caml_parser_run_def = new_definition
  `caml_parser_run inp =
     match run_lexer inp with
       sum_INL locs -> sum_INL (HD locs,(implode "LEXER ERROR"))
     | sum_INR toks ->
         (match run_parser toks with
           sum_INL (loc,err) -> sum_INL (loc,err)
         | sum_INR tree -> sum_INR tree)`;;

(* and the interface *)
let _ = unhide_overloads ();;
