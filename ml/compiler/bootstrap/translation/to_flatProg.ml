(* ======================================================== *)
(*  to_flatProg: ported from HOL4's
    compiler/bootstrap/translation/to_flatProgScript.sml
    A definition theory, with no definitions and 1 theorem.  Needed
    by to_closProg.ml.  *)
(* ======================================================== *)

(*
  Translate backend phases up to and including flatLang.
*)

needs "compiler/backend/source_to_flat.ml";;
needs "compiler/backend/source_to_source.ml";;
needs "compiler/bootstrap/translation/decProg.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "to_flatProg"
  ["decProg"; "ml_translator"; "source_to_flat"; "source_to_source"];;

(* HOL4 to_flatProgScript.sml:11: ML code, not ported *)

(* HOL4 to_flatProgScript.sml:15: ML code, not ported *)

(* HOL4 to_flatProgScript.sml:17: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* Setup                                                                     *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_flatProgScript.sml:23-33: ML code, not ported *)

(* HOL4 to_flatProgScript.sml:35-36: ML code, not ported *)

(* [local] *)
let NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 to_flatProgScript.sml:44: ML code, not ported *)

(* HOL4 to_flatProgScript.sml:46-59: ML code, not ported *)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
(* HOL4 to_flatProgScript.sml:63-64: ML code, not ported *)

(* HOL4 to_flatProgScript.sml:66: ML code, not ported *)

(* HOL4 to_flatProgScript.sml:68: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* source_to_flat                                                            *)
(* ------------------------------------------------------------------------- *)

(* TODO:
 *   - This is a discrepancy between HOL's standard libraries and mllist.
 *     Probably the compiler should be using the mllist versions?
 *)
(* HOL4 to_flatProgScript.sml:78-83: a theorem that HOL4 states as the value
   of an ML expression: list_el_side *)

(* -- *)

(* HOL4 to_flatProgScript.sml:87-89: ML code, not ported *)

(* HOL4 to_flatProgScript.sml:91-92: ML code, not ported *)

(* HOL4 to_flatProgScript.sml:94-98: ML code, not ported *)

(* HOL4 to_flatProgScript.sml:100-101: ML code, not ported *)

(* HOL4 to_flatProgScript.sml:103-104: ML code, not ported *)
(* ------------------------------------------------------------------------- *)
(* source_to_source                                                          *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_flatProgScript.sml:109: ML code, not ported *)

(* HOL4 to_flatProgScript.sml:111-112: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* flat_elim                                                                 *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_flatProgScript.sml:118-119: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* flat_pattern                                                              *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_flatProgScript.sml:125-129: ML code, not ported *)

(* HOL4 to_flatProgScript.sml:131: ML code, not ported *)

(* HOL4 to_flatProgScript.sml:133-134: ML code, not ported *)

(* HOL4 to_flatProgScript.sml:136: ML code, not ported *)

(* HOL4 to_flatProgScript.sml:138: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* source_to_flat                                                            *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_flatProgScript.sml:144: ML code, not ported *)

(* HOL4 to_flatProgScript.sml:146: ML code, not ported *)

(* HOL4 to_flatProgScript.sml:148-149: ML code, not ported *)

(* HOL4 to_flatProgScript.sml:151: ML code, not ported *)

(* HOL4 to_flatProgScript.sml:153-154: ML code, not ported *)

(* ------------------------------------------------------------------------- *)

(* HOL4 to_flatProgScript.sml:158-159: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
