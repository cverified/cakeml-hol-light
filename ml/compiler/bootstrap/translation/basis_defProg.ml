(* ======================================================== *)
(*  basis_defProg: ported from HOL4's
    compiler/bootstrap/translation/basis_defProgScript.sml
    A definition theory, with no definitions and no theorems.
    Needed by printingProg.ml and to_word32Prog.ml.  *)
(* ======================================================== *)

(*
  Translate the basis library term.
*)

needs "compiler/bootstrap/translation/sexp_parserProg.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "basis_defProg"
  ["ml_translator"; "sexp_parserProg"];;

(* HOL4 basis_defProgScript.sml:10-11: ML code, not ported *)

(* HOL4 basis_defProgScript.sml:13-14: ML code, not ported *)

(* HOL4 basis_defProgScript.sml:16: ML code, not ported *)

(* HOL4 basis_defProgScript.sml:18-19: ML code, not ported *)

(* HOL4 basis_defProgScript.sml:21: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
