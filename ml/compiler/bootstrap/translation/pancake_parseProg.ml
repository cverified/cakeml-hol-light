(* ======================================================== *)
(*  pancake_parseProg: ported from HOL4's
    compiler/bootstrap/translation/pancake_parseProgScript.sml
    A definition theory, with no definitions and 2 theorems.  Needed
    by reg_allocProg.ml.  *)
(* ======================================================== *)

(*
  Translate pancake's parser
*)

needs "compiler/bootstrap/translation/pancake_lexProg.ml";;
needs "pancake/parser/panPEG.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "pancake_parseProg"
  ["ml_translator"; "panPEG"; "pancake_lexProg"];;

(* HOL4 pancake_parseProgScript.sml:10-13: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:15: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:17: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:19-29: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:31-32: ML code, not ported *)

(* NOT_NIL_AND_LEMMA *)
let pancake_parseProg_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 pancake_parseProgScript.sml:40: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:42-58: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:60: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:62-63: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:65-67: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:69: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:71: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:73-75: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:77: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:79: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:81: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:83: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:85: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:87: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:89: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:91: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:93: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:95: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:97: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:99: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:101: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:103: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:105: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:107: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:109-131: a theorem that HOL4 states as
   the value of an ML expression: parse_side_lemma *)

(* HOL4 pancake_parseProgScript.sml:133: ML code, not ported *)

(* HOL4 pancake_parseProgScript.sml:135: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
