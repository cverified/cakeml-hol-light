(* ======================================================== *)
(*  lexerProg: ported from HOL4's
    compiler/bootstrap/translation/lexerProgScript.sml
    A definition theory, with no definitions and 3 theorems.  Needed
    by parserProg.ml.  *)
(* ======================================================== *)

(*
  Translate the compiler's lexer.
*)

needs "compiler/bootstrap/translation/to_dataProg.ml";;
needs "compiler/parsing/lexer_impl.ml";;
needs "semantics/lexer_fun.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "lexerProg"
  ["lexer_fun"; "lexer_impl"; "ml_translator"; "to_dataProg"];;

(* HOL4 lexerProgScript.sml:10-12: ML code, not ported *)

(* HOL4 lexerProgScript.sml:16: ML code, not ported *)

(* HOL4 lexerProgScript.sml:18: ML code, not ported *)

(* HOL4 lexerProgScript.sml:20: ML code, not ported *)

(* HOL4 lexerProgScript.sml:22-32: ML code, not ported *)

(* HOL4 lexerProgScript.sml:34-35: ML code, not ported *)

(* NOT_NIL_AND_LEMMA *)
let lexerProg_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 lexerProgScript.sml:43: ML code, not ported *)

(* HOL4 lexerProgScript.sml:45-61: ML code, not ported *)

(* HOL4 lexerProgScript.sml:63: ML code, not ported *)

(* HOL4 lexerProgScript.sml:65: ML code, not ported *)

(* HOL4 lexerProgScript.sml:67: ML code, not ported *)

(* HOL4 lexerProgScript.sml:69: ML code, not ported *)

(* HOL4 lexerProgScript.sml:71: ML code, not ported *)

(* HOL4 lexerProgScript.sml:73: ML code, not ported *)

(* HOL4 lexerProgScript.sml:75-76: ML code, not ported *)

let l2n_side = prove
 (`!b a. ~(a = 0) ==> l2n_side a b`,
  CHEAT_TAC);;

(* HOL4 lexerProgScript.sml:85: ML code, not ported *)

(* HOL4 lexerProgScript.sml:87-97: a theorem that HOL4 states as the value
   of an ML expression: num_from_dec_string_alt_side *)

(* HOL4 lexerProgScript.sml:99-109: a theorem that HOL4 states as the value
   of an ML expression: num_from_hex_string_alt_side *)

(* [local] *)
let next_sym_alt_side = prove
 (`!x l. next_sym_alt_side x l <=> T`,
  CHEAT_TAC);;

(* HOL4 lexerProgScript.sml:120-125: a theorem that HOL4 states as the value
   of an ML expression: lexer_fun_aux_side *)

(* HOL4 lexerProgScript.sml:127-129: a theorem that HOL4 states as the value
   of an ML expression: lexer_fun_side *)


(* HOL4 lexerProgScript.sml:132: ML code, not ported *)

(* HOL4 lexerProgScript.sml:134: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
