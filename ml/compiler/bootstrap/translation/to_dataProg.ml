(* ======================================================== *)
(*  to_dataProg: ported from HOL4's
    compiler/bootstrap/translation/to_dataProgScript.sml
    A definition theory, with no definitions and 3 theorems.  Needed
    by lexerProg.ml.  *)
(* ======================================================== *)

(*
  Translate the backend phase from BVI to dataLang.
*)

needs "compiler/backend/backend.ml";;
needs "compiler/bootstrap/translation/to_bviProg.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "to_dataProg"
  ["backend"; "ml_translator"; "to_bviProg"];;

(* HOL4 to_dataProgScript.sml:10: ML code, not ported *)

(* HOL4 to_dataProgScript.sml:14: ML code, not ported *)

(* HOL4 to_dataProgScript.sml:16: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* Setup                                                                     *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_dataProgScript.sml:22-32: ML code, not ported *)

(* HOL4 to_dataProgScript.sml:34-35: ML code, not ported *)

(* NOT_NIL_AND_LEMMA[local] *)
let to_dataProg_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 to_dataProgScript.sml:43: ML code, not ported *)

(* HOL4 to_dataProgScript.sml:45-58: ML code, not ported *)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
(* HOL4 to_dataProgScript.sml:62-63: ML code, not ported *)

(* HOL4 to_dataProgScript.sml:65: ML code, not ported *)

(* HOL4 to_dataProgScript.sml:67: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* bvi_to_data                                                               *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_dataProgScript.sml:73-74: ML code, not ported *)

(* TODO:
 *   - For some reason, the following def on sptrees fails to translate in a
 *     standalone manner (when the rest of this file's translation isn't
 *     loaded). Needs investigation.
 *)
(* HOL4 to_dataProgScript.sml:81: ML code, not ported *)

(* HOL4 to_dataProgScript.sml:83: ML code, not ported *)

(* [local] *)
let bvi_to_data_compile_ind = prove
 (`bvi_to_data_compile_ind`,
  CHEAT_TAC);;

(* HOL4 to_dataProgScript.sml:101: ML code, not ported *)

(* [local] *)
let bvi_to_data_compile_side = prove
 (`!a b c d e. bvi_to_data_compile_side a b c d e <=> T`,
  CHEAT_TAC);;

(* HOL4 to_dataProgScript.sml:124: ML code, not ported *)

(* TODO:
 *   - pmatch for bvl_space is broken
 *)
(* HOL4 to_dataProgScript.sml:129: ML code, not ported *)

(* HOL4 to_dataProgScript.sml:131-132: ML code, not ported *)

(* HOL4 to_dataProgScript.sml:134: ML code, not ported *)

(* ------------------------------------------------------------------------- *)

(* HOL4 to_dataProgScript.sml:138-139: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
