(* ======================================================== *)
(*  sexp_parserProg: ported from HOL4's
    compiler/bootstrap/translation/sexp_parserProgScript.sml
    A definition theory, with 4 definitions and 17 theorems.  Needed
    by basis_defProg.ml.  *)
(* ======================================================== *)

(*
  Translate the alternative s-expression parser.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/bootstrap/translation/decodeProg.ml";;
needs "compiler/parsing/fromSexp.ml";;
needs "compiler/parsing/lexer_impl.ml";;
needs "lib/ASCIInumbers.ml";;
needs "lib/peg.ml";;
needs "lib/simpleSexp.ml";;
needs "lib/simpleSexpPEG.ml";;
needs "lib/simpleSexpParse.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "sexp_parserProg"
  ["decodeProg"; "fromSexp"; "ml_translator"];;

let _ = do_list hide_constant ["C"];;

(* HOL4 sexp_parserProgScript.sml:11-13: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:17: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:19-20: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:22: ML code, not ported *)

(* OPTION_BIND_THM *)
let sexp_parserProg_OPTION_BIND_THM = prove
 (`!x y. OPTION_BIND x y = match x with NONE -> NONE | SOME i -> y i`,
  CHEAT_TAC);;
(* -- *)

(* HOL4 sexp_parserProgScript.sml:31-36: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:38-54: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:56-61: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:63-84: a theorem that HOL4 states as the
   value of an ML expression: parse_sexp_side *)

(* HOL4 sexp_parserProgScript.sml:86-88: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:90-91: ML code, not ported *)


(* TODO: move (used?) *)
let isHexDigit_cases = prove
 (`isHexDigit c <=>
   isDigit c \/
   c IN {(CHR 97),(CHR 98),(CHR 99),(CHR 100),(CHR 101),(CHR 102)} \/
   c IN {(CHR 65),(CHR 66),(CHR 67),(CHR 68),(CHR 69),(CHR 70)}`,
  CHEAT_TAC);;

let isHexDigit_UNHEX_LESS = prove
 (`isHexDigit c ==> UNHEX c < 16`,
  CHEAT_TAC);;

let num_from_hex_string_alt_length_2 = prove
 (`num_from_hex_string_alt [d1; d2] < 256`,
  CHEAT_TAC);;
(* -- *)

let num_from_hex_string_alt_intro = prove
 (`ALL isHexDigit ls ==>
   num_from_hex_string ls =
   num_from_hex_string_alt ls`,
  CHEAT_TAC);;

(* lemma[local] *)
let sexp_parserProg_lemma = prove
 (`isHexDigit x /\ isHexDigit y /\ A /\ B /\ ~(isPrint (CHR
  (num_from_hex_string [x; y]))) <=>
   isHexDigit x /\ isHexDigit y /\ A /\ B /\ ~(isPrint (CHR
     (num_from_hex_string_alt [x; y])))`,
  CHEAT_TAC);;

(* [local] *)
let lemma2 = prove
 (`isHexDigit x /\ isHexDigit y ==>
   num_from_hex_string [x; y] = num_from_hex_string_alt [x; y]`,
  CHEAT_TAC);;

(* HOL4 sexp_parserProgScript.sml:172: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:174-176: ML code, not ported *)

(* [local] *)
let decode_control_ind = prove
 (`decode_control_ind`,
  CHEAT_TAC);;

(* HOL4 sexp_parserProgScript.sml:192: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:194-205: a theorem that HOL4 states as the
   value of an ML expression: decode_control_side *)

let decode_control_wrapper_def = new_definition
  `decode_control_wrapper s =
     match decode_control (explode s) with
       NONE -> NONE
     | SOME x -> SOME (implode x)`;;

(* HOL4 sexp_parserProgScript.sml:214: ML code, not ported *)

let decode_control_eq = prove
 (`decode_control s =
   OPTION_MAP (\x. explode x) (decode_control_wrapper (implode s))`,
  CHEAT_TAC);;

(* HOL4 sexp_parserProgScript.sml:224-227: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:229-231: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:233: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:235: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:237-239: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:241: ML code, not ported *)

(*
val r = fromSexpTheory.sexpspec_def
        |> SIMP_RULE std_ss [OPTION_BIND_THM,monad_unitbind_assert,sexptype_alt_intro1]
        |> translate;

val sexpspec_side = Q.prove(
  `∀x. sexpspec_side x = T`,
  EVAL_TAC \\ rw[] \\ strip_tac \\ fs[])
  |> update_precondition;
*)

(* HOL4 sexp_parserProgScript.sml:254-256: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:258-260: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:262-264: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:266-268: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:270-273: a theorem that HOL4 states as the
   value of an ML expression: sexplit_side *)

(* HOL4 sexp_parserProgScript.sml:275: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:277-278: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:280-282: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:284-285: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:287: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:289: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:291: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:293-300: a theorem that HOL4 states as the
   value of an ML expression: sexpdec_alt_side *)

(* HOL4 sexp_parserProgScript.sml:302-304: a theorem that HOL4 states as the
   value of an ML expression: strip_dot_alt *)

(* HOL4 sexp_parserProgScript.sml:306: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:308: ML code, not ported *)


(* TODO: translator failed for some reason if I just prove these as equations on print_sexp *)
(* the termination relation that HOL4 gives is
     MEASURE mlsexp_sexp_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 sexp_parserProgScript.sml:325-334: the tactic that proves the
   termination *)
let print_sexp_alt_def,print_sexp_alt_ind = define_guess
  `print_sexp_alt s =
     match s with
       SX_SYM s -> s
     | SX_NUM n -> explode (integer_word_toString n)
     | SX_STR s -> APPEND (APPEND "\"" (IMPLODE (escape_string s))) "\""
     | s ->
      (let (ls,n) = strip_dot s in
      match n with NONE ->
        if LENGTH ls = 2 /\ HD ls = SX_SYM "quote" then APPEND "'"
          (print_sexp_alt (EL 1 ls))
        else APPEND (APPEND "(" (print_space_separated (MAP print_sexp_alt
          ls))) ")"
      | SOME lst -> APPEND (APPEND (APPEND (APPEND "("
        (print_space_separated (MAP print_sexp_alt ls))) " . ")
        (print_sexp_alt lst)) ")")`;;

let strip_dot_EQ_NILSOME = prove
 (`strip_dot s = ([],SOME x) ==> s = x`,
  CHEAT_TAC);;

let toString_toString_explode = prove
 (`integer_word_toString n = explode (integer_word_toString (n:num))`,
  CHEAT_TAC);;

let print_sexp_alt_thm = prove
 (`print_sexp s = print_sexp_alt s`,
  CHEAT_TAC);;

(* HOL4 sexp_parserProgScript.sml:379: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:381: ML code, not ported *)

(* [local] *)
let listsexp_alt = prove
 (`listsexp = FOLDR (\s1 s2. SX_CONS s1 s2) (SX_SYM "nil")`,
  CHEAT_TAC);;

(* HOL4 sexp_parserProgScript.sml:389: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:391: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:393: ML code, not ported *)

(* [local] *)
let l2n_side_thm = prove
 (`!n l. l2n_side n l <=> (~(l = []) ==> ~(n = 0))`,
  CHEAT_TAC);;

(* [local] *)
let s2n_side_thm = prove
 (`!n f l. s2n_side n f l <=> (~(l = []) ==> ~(n = 0))`,
  CHEAT_TAC);;

let hex_alt_def = new_definition
  `hex_alt x = if x < 16 then HEX x else (CHR 48)`;;

let num_to_hex_string_alt = new_definition
  `num_to_hex_string_alt = n2s 16 hex_alt`;;

let num_to_hex_string_alt_intro = prove
 (`!n. num_to_hex_string n = num_to_hex_string_alt n`,
  CHEAT_TAC);;

(* HOL4 sexp_parserProgScript.sml:430: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:432-434: a theorem that HOL4 states as the
   value of an ML expression: _ *)

(* HOL4 sexp_parserProgScript.sml:436: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:438-443: a theorem that HOL4 states as the
   value of an ML expression: n2l_side_thm *)

(* HOL4 sexp_parserProgScript.sml:445: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:447-450: a theorem that HOL4 states as the
   value of an ML expression: n2s_side_thm *)

(* HOL4 sexp_parserProgScript.sml:452: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:454: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:456: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:458: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:460: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:462-464: a theorem that HOL4 states as the
   value of an ML expression: litsexp_side_thm *)

(* HOL4 sexp_parserProgScript.sml:466-478: ML code, not ported *)

(* HOL4 sexp_parserProgScript.sml:480: ML code, not ported *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["C"];;

(* and the interface *)
let _ = unhide_overloads ();;
