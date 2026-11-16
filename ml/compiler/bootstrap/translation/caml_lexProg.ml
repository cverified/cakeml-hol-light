(* ======================================================== *)
(*  caml_lexProg: ported from HOL4's
    compiler/bootstrap/translation/caml_lexProgScript.sml
    A definition theory, with no definitions and 6 theorems.  Needed
    by caml_parserProg.ml.  *)
(* ======================================================== *)

(*
  Translation of the OCaml lexer.
 *)

needs "compiler/bootstrap/translation/parserProg.ml";;
needs "compiler/parsing/ocaml/caml_lex.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "caml_lexProg"
  ["caml_lex"; "ml_translator"; "parserProg"];;

(* HOL4 caml_lexProgScript.sml:10-11: ML code, not ported *)

(* HOL4 caml_lexProgScript.sml:13: ML code, not ported *)

(* -------------------------------------------------------------------------
 * Translator setup
 * ------------------------------------------------------------------------- *)

(* HOL4 caml_lexProgScript.sml:19-29: ML code, not ported *)

(* HOL4 caml_lexProgScript.sml:31: ML code, not ported *)

(* NOT_NIL_AND_LEMMA *)
let caml_lexProg_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 caml_lexProgScript.sml:39: ML code, not ported *)

(* HOL4 caml_lexProgScript.sml:41-56: ML code, not ported *)

(* HOL4 caml_lexProgScript.sml:58: ML code, not ported *)

(* HOL4 caml_lexProgScript.sml:60: ML code, not ported *)

(* HOL4 caml_lexProgScript.sml:62-73: ML code, not ported *)

(* HOL4 caml_lexProgScript.sml:75-78: ML code, not ported *)

(* [local] *)
let hex2num_side = prove
 (`!x. hex2num_side x`,
  CHEAT_TAC);;

(* HOL4 caml_lexProgScript.sml:89: ML code, not ported *)

(* [local] *)
let oct2num_side = prove
 (`!x. oct2num_side x`,
  CHEAT_TAC);;

(* HOL4 caml_lexProgScript.sml:100: ML code, not ported *)

(* [local] *)
let bin2num_side = prove
 (`!x. bin2num_side x`,
  CHEAT_TAC);;

(* HOL4 caml_lexProgScript.sml:111: ML code, not ported *)

(* [local] *)
let dec2num_side = prove
 (`!x. dec2num_side x`,
  CHEAT_TAC);;

(* HOL4 caml_lexProgScript.sml:122: ML code, not ported *)

(* HOL4 caml_lexProgScript.sml:124: ML code, not ported *)

(* [local] *)
let scan_escseq_side = prove
 (`!x y. scan_escseq_side x y`,
  CHEAT_TAC);;

(* HOL4 caml_lexProgScript.sml:149: ML code, not ported *)

(* HOL4 caml_lexProgScript.sml:151-155: ML code, not ported *)

(* HOL4 caml_lexProgScript.sml:157: ML code, not ported *)

(* HOL4 caml_lexProgScript.sml:159: ML code, not ported *)


(* HOL4 caml_lexProgScript.sml:162: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
