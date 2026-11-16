(* ======================================================== *)
(*  parserProg: ported from HOL4's
    compiler/bootstrap/translation/parserProgScript.sml
    A definition theory, with no definitions and 13 theorems.
    Needed by caml_lexProg.ml and inferProg.ml.  *)
(* ======================================================== *)

(*
  Translate the compiler's parser.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/bootstrap/translation/lexerProg.ml";;
needs "compiler/parsing/cmlPEG.ml";;
needs "compiler/parsing/cmlParse.ml";;
needs "lib/grammar.ml";;
needs "lib/location.ml";;
needs "semantics/cmlPtreeConversion.ml";;
needs "semantics/namespace.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "parserProg"
  ["cmlPEG"; "cmlParse"; "lexerProg"; "ml_translator"; "semanticPrimitives"];;

(* HOL4 parserProgScript.sml:10-13: ML code, not ported *)

(* HOL4 parserProgScript.sml:17: ML code, not ported *)

(* HOL4 parserProgScript.sml:19: ML code, not ported *)

(* translator setup *)

(* HOL4 parserProgScript.sml:23-33: ML code, not ported *)

(* HOL4 parserProgScript.sml:35-36: ML code, not ported *)

(* NOT_NIL_AND_LEMMA *)
let parserProg_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 parserProgScript.sml:44: ML code, not ported *)

(* HOL4 parserProgScript.sml:46-62: ML code, not ported *)

(* HOL4 parserProgScript.sml:64: ML code, not ported *)

(* parsing: peg_exec and cmlPEG *)

(* HOL4 parserProgScript.sml:68-69: ML code, not ported *)

(* checking GRAMMAR_PARSETREE_TYPE etc is known to be an EqualityType *)
(* HOL4 parserProgScript.sml:72: ML code, not ported *)

(* HOL4 parserProgScript.sml:74: the ML values that the definitions below
   antiquote *)

let locnle = prove
 (`locnle x y =
     match (x,y) with (UNKNOWNpt,_) -> T
     | (_,EOFpt) -> T
     | (POSN x1 x2,POSN y1 y2) -> ((x1 < y1) \/ (x1 = y1) /\ (x2 <= y2))
     | _ -> F`,
  CHEAT_TAC);;

(* HOL4 parserProgScript.sml:88: ML code, not ported *)

(* [local] *)
let validaddsym_side_lemma = prove
 (`!x. validaddsym_side x = T`,
  CHEAT_TAC);;
(* HOL4 parserProgScript.sml:95: ML code, not ported *)

(* HOL4 parserProgScript.sml:97: the ML values that the definitions below
   antiquote *)

let not_mlstring_emp = prove
 (`~(x = (implode "")) ==>
     0 < strlen x`,
  CHEAT_TAC);;
add_simp not_mlstring_emp;;

(* [local] *)
let cmlpeg_side = prove
 (`cmlpeg_side <=> T`,
  CHEAT_TAC);;

(* HOL4 parserProgScript.sml:117: ML code, not ported *)

let INTRO_FLOOKUP = prove
 (`(if n IN FDOM (rules G) then
      pegexec_EV (FAPPLY (rules G) n) i r eo errs (pegexec_appf1 tf3 k) fk
    else pegexec_Looped) =
   (match FLOOKUP (rules G) n with
      NONE -> pegexec_Looped
    | SOME x -> pegexec_EV x i r eo errs (pegexec_appf1 tf3 k) fk)`,
  CHEAT_TAC);;

(* HOL4 parserProgScript.sml:130-131: the ML values that the definitions
   below antiquote *)

(* HOL4 parserProgScript.sml:133: the ML values that the definitions below
   antiquote *)

(* parsing: cmlvalid *)

(* monad_unitbind_assert *)
let parserProg_monad_unitbind_assert = prove
 (`!b x. OPTION_IGNORE_BIND (OPTION_GUARD b) x = if b then x else NONE`,
  CHEAT_TAC);;

(* HOL4 parserProgScript.sml:143: ML code, not ported *)

(* parsing: ptree converstion *)

let OPTION_BIND_THM = prove
 (`!x y. OPTION_BIND x y = match x with NONE -> NONE | SOME i -> y i`,
  CHEAT_TAC);;

(* HOL4 parserProgScript.sml:153-154: ML code, not ported *)

let maybe_handleRef_eq = prove
 (`!p. maybe_handleRef p =
       match p with (ast_Pcon (SOME (Short n)) [pat]) -> if n = (implode
         "Ref") then ast_Pref pat else p
       | _ -> p`,
  CHEAT_TAC);;

(* HOL4 parserProgScript.sml:167: ML code, not ported *)

(* HOL4 parserProgScript.sml:169: the ML values that the definitions below
   antiquote *)

(* HOL4 parserProgScript.sml:171: the ML values that the definitions below
   antiquote *)

(* HOL4 parserProgScript.sml:173: the ML values that the definitions below
   antiquote *)

(* HOL4 parserProgScript.sml:175: the ML values that the definitions below
   antiquote *)

(* HOL4 parserProgScript.sml:177-181: ML code, not ported *)

(* HOL4 parserProgScript.sml:183: ML code, not ported *)

(* HOL4 parserProgScript.sml:185: the ML values that the definitions below
   antiquote *)

(* [local] *)
let ptree_Decls = prove
 (`ptree_Decls x =
      match x with Lf t -> ptree_Decls (Lf t)
      | Nd (a1,a2) b -> ptree_Decls (Nd (a1,a2) b)`,
  CHEAT_TAC);;

(* [local] *)
let ptree_Structure = prove
 (`ptree_Structure x =
      match x with Lf t -> ptree_Structure (Lf t)
      | Nd (a1,a2) b -> ptree_Structure (Nd (a1,a2) b)`,
  CHEAT_TAC);;

(* HOL4 parserProgScript.sml:207-217: ML code, not ported *)

(* HOL4 parserProgScript.sml:219: ML code, not ported *)

(* [local] *)
let ind_lemma = prove
 (`ptree_decl_ind`,
  CHEAT_TAC);;

(* HOL4 parserProgScript.sml:238: ML code, not ported *)

(* HOL4 parserProgScript.sml:240: the ML values that the definitions below
   antiquote *)

(* parsing: top-level parser *)

(* HOL4 parserProgScript.sml:244: ML code, not ported *)

(* HOL4 parserProgScript.sml:246-254: a theorem that HOL4 states as the
   value of an ML expression: parse_prog_side_lemma *)

(* HOL4 parserProgScript.sml:256: ML code, not ported *)

(* HOL4 parserProgScript.sml:258: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
