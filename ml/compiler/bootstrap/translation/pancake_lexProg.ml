(* ======================================================== *)
(*  pancake_lexProg: ported from HOL4's
    compiler/bootstrap/translation/pancake_lexProgScript.sml
    A definition theory, with no definitions and 7 theorems.  Needed
    by pancake_parseProg.ml.  *)
(* ======================================================== *)

(*
  Translate pancake's lexer
*)

needs "compiler/bootstrap/translation/caml_parserProg.ml";;
needs "lib/location.ml";;
needs "pancake/parser/panLexer.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "pancake_lexProg"
  ["caml_parserProg"; "ml_translator"; "panLexer"];;

(* HOL4 pancake_lexProgScript.sml:10-13: ML code, not ported *)

(* HOL4 pancake_lexProgScript.sml:15: ML code, not ported *)

(* HOL4 pancake_lexProgScript.sml:17: ML code, not ported *)

(* HOL4 pancake_lexProgScript.sml:19-29: ML code, not ported *)

(* HOL4 pancake_lexProgScript.sml:31-32: ML code, not ported *)

(* NOT_NIL_AND_LEMMA *)
let pancake_lexProg_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 pancake_lexProgScript.sml:40: ML code, not ported *)

(* HOL4 pancake_lexProgScript.sml:42-58: ML code, not ported *)

(* HOL4 pancake_lexProgScript.sml:60: ML code, not ported *)

(* HOL4 pancake_lexProgScript.sml:62: ML code, not ported *)

(* HOL4 pancake_lexProgScript.sml:64: ML code, not ported *)

(* HOL4 pancake_lexProgScript.sml:66: ML code, not ported *)

(* [local] *)
let unhex_alt_1_side = prove
 (`!x. unhex_alt_1_side x`,
  CHEAT_TAC);;

(* HOL4 pancake_lexProgScript.sml:80: ML code, not ported *)

(* [local] *)
let num_from_dec_string_alt_1_side = prove
 (`!x. num_from_dec_string_alt_1_side x`,
  CHEAT_TAC);;

(* HOL4 pancake_lexProgScript.sml:96: ML code, not ported *)

(* [local] *)
let next_atom_side = prove
 (`!x y. next_atom_side x y`,
  CHEAT_TAC);;

(* HOL4 pancake_lexProgScript.sml:108: ML code, not ported *)

(* [local] *)
let next_token_2_side = prove
 (`!x y. next_token_2_side x y`,
  CHEAT_TAC);;

(* HOL4 pancake_lexProgScript.sml:116: ML code, not ported *)

(* [local] *)
let pancake_lex_aux_side = prove
 (`!s n. pancake_lex_aux_side s n`,
  CHEAT_TAC);;

(* HOL4 pancake_lexProgScript.sml:125: ML code, not ported *)

(* [local] *)
let pancake_lex_side = prove
 (`!x. pancake_lex_side x`,
  CHEAT_TAC);;

(* HOL4 pancake_lexProgScript.sml:133: ML code, not ported *)


(* HOL4 pancake_lexProgScript.sml:136-137: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
