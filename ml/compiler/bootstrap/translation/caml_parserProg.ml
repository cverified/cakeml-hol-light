(* ======================================================== *)
(*  caml_parserProg: ported from HOL4's
    compiler/bootstrap/translation/caml_parserProgScript.sml
    A definition theory, with no definitions and 13 theorems.
    Needed by pancake_lexProg.ml.  *)
(* ======================================================== *)

(*
  Translation of the functions in caml_parserScript.sml
 *)

needs "compiler/bootstrap/translation/caml_lexProg.ml";;
needs "compiler/parsing/ocaml/camlPEG.ml";;
needs "compiler/parsing/ocaml/camlPtreeConversion.ml";;
needs "compiler/parsing/ocaml/caml_parser.ml";;
needs "misc/misc.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "caml_parserProg"
  ["camlPEG"; "camlPtreeConversion"; "caml_lexProg"; "caml_parser"; "misc";
   "ml_translator"];;

(* HOL4 caml_parserProgScript.sml:11-13: ML code, not ported *)


(* HOL4 caml_parserProgScript.sml:16: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:18-25: an overload that the source brings
   to the front: nType, written out as camlPEG_nType *)
(* HOL4 caml_parserProgScript.sml:18-25: an overload that the source brings
   to the front: nPattern, written out as camlPEG_nPattern *)
(* HOL4 caml_parserProgScript.sml:18-25: an overload that the source brings
   to the front: pegf, written out as camlPEG_pegf *)
(* HOL4 caml_parserProgScript.sml:18-25: an overload that the source brings
   to the front: seql, written out as camlPEG_seql *)
(* HOL4 caml_parserProgScript.sml:18-25: an overload that the source brings
   to the front: choicel, written out as camlPEG_choicel *)
(* HOL4 caml_parserProgScript.sml:18-25: an overload that the source brings
   to the front: pnt, written out as camlPEG_pnt *)

(* -------------------------------------------------------------------------
 * Translator setup
 * ------------------------------------------------------------------------- *)

(* HOL4 caml_parserProgScript.sml:31-41: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:43: ML code, not ported *)

(* NOT_NIL_AND_LEMMA *)
let caml_parserProg_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 caml_parserProgScript.sml:51-56: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:58-71: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:73: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:75: ML code, not ported *)

(* -------------------------------------------------------------------------
 * Ptree conversion
 * ------------------------------------------------------------------------- *)

(* HOL4 caml_parserProgScript.sml:81: ML code, not ported *)

let bind_thm = prove
 (`camlPtreeConversion_bind x f = match x with sum_INL err -> sum_INL err |
  sum_INR y -> f y`,
  CHEAT_TAC);;

(* HOL4 caml_parserProgScript.sml:89-90: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:92: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:94: ML code, not ported *)

(* [local] *)
let ptree_op_side = prove
 (`!x. camlptreeconversion_ptree_op_side x`,
  CHEAT_TAC);;

(* HOL4 caml_parserProgScript.sml:104: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:106: ML code, not ported *)

(* [local] *)
let ptree_literal_side = prove
 (`!x. camlptreeconversion_ptree_literal_side x`,
  CHEAT_TAC);;

(* HOL4 caml_parserProgScript.sml:117: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:119: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:121: ML code, not ported *)

let precparse_side = prove
 (`!x y. precparser_precparse_side x y`,
  CHEAT_TAC);;

(* HOL4 caml_parserProgScript.sml:134: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:136: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:138: ML code, not ported *)

(* [local] *)
let ptree_PPattern_side = prove
 (`(!x. camlptreeconversion_ptree_ppattern_side x) /\
   (!x. camlptreeconversion_ptree_ppatternlist_side x) /\
   (!x y. camlptreeconversion_grabpairs_side x y)`,
  CHEAT_TAC);;

(* HOL4 caml_parserProgScript.sml:150: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:152: ML code, not ported *)

(* This takes a long time.
 *)

(* HOL4 caml_parserProgScript.sml:157: ML code, not ported *)

(* [local] *)
let ptree_Expr_preconds = prove
 (`(!x y. camlptreeconversion_ptree_expr_side x y) /\
   (!x. camlptreeconversion_ptree_letrecbinding_side x) /\
   (!x. camlptreeconversion_ptree_letrecbindings_side x) /\
   (!x. camlptreeconversion_ptree_letbinding_side x) /\
   (!x. camlptreeconversion_ptree_letbindings_side x) /\
   (!x. camlptreeconversion_ptree_patternmatches_side x) /\
   (!x. camlptreeconversion_ptree_patternmatch_side x) /\
   (!x. camlptreeconversion_ptree_exprlist_side x) /\
   (!x. camlptreeconversion_ptree_exprcommas_side x) /\
   (!x. camlptreeconversion_ptree_update_side x) /\
   (!x. camlptreeconversion_ptree_updates_side x) /\
   (!x. camlptreeconversion_ptree_index_side x)`,
  CHEAT_TAC);;

(* HOL4 caml_parserProgScript.sml:193: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:195: ML code, not ported *)

(* [local] *)
let camlptreeconversion_partition_types_side = prove
 (`camlptreeconversion_partition_types_side x`,
  CHEAT_TAC);;

(* HOL4 caml_parserProgScript.sml:213: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:215-218: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:220: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:222-223: ML code, not ported *)

(* [local] *)
let destresult_side = prove
 (`pegexec_destresult_side v = (?r. v = holSyntaxLib_Result r)`,
  CHEAT_TAC);;

let ptree_definition_side = prove
 (`(!x. camlptreeconversion_ptree_definition_side x) /\
   (!x. camlptreeconversion_ptree_modexpr_side x) /\
   (!x. camlptreeconversion_ptree_moduleitems_side x) /\
   (!x. camlptreeconversion_ptree_moduleitem_side x) /\
   (!x. camlptreeconversion_ptree_exprordefn_side x)`,
  CHEAT_TAC);;

(* HOL4 caml_parserProgScript.sml:252: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:254: ML code, not ported *)

(* -------------------------------------------------------------------------
 * Parser front-end
 * ------------------------------------------------------------------------- *)

(* HOL4 caml_parserProgScript.sml:260: ML code, not ported *)

(* [local] *)
let and_or_imp_lemma = prove
 (`(b \/ c <=> (if b then T else c)) /\
   (b /\ c <=> (if b then c else F)) /\
   ((b ==> c) <=> (if b then c else T)) /\
   ((if ~b then x else y) = (if b then y else x))`,
  CHEAT_TAC);;

(* HOL4 caml_parserProgScript.sml:271: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:273-274: ML code, not ported *)

(* [local] *)
let run_parser_side = prove
 (`!x. caml_parser_run_parser_side x`,
  CHEAT_TAC);;

(* HOL4 caml_parserProgScript.sml:287: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:289: ML code, not ported *)

(* [local] *)
let run_side = prove
 (`!x. caml_parser_run_side x`,
  CHEAT_TAC);;

(* HOL4 caml_parserProgScript.sml:297: ML code, not ported *)

(* HOL4 caml_parserProgScript.sml:299: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
