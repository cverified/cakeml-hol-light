(* ======================================================== *)
(*  to_closProg: ported from HOL4's
    compiler/bootstrap/translation/to_closProgScript.sml
    A definition theory, with no definitions and 6 theorems.  Needed
    by to_bvlProg.ml.  *)
(* ======================================================== *)

(*
  Translate the backend phase from flatLang to closLang.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/clos_call.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/clos_mti.ml";;
needs "compiler/backend/clos_number.ml";;
needs "compiler/backend/flat_to_clos.ml";;
needs "compiler/bootstrap/translation/to_flatProg.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "to_closProg"
  ["clos_annotate"; "clos_call"; "clos_known"; "clos_mti"; "clos_number";
   "flat_to_clos"; "ml_translator"; "to_flatProg"];;

(* HOL4 to_closProgScript.sml:13: ML code, not ported *)

(* HOL4 to_closProgScript.sml:17: ML code, not ported *)

(* HOL4 to_closProgScript.sml:19: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* Setup                                                                     *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_closProgScript.sml:25-35: ML code, not ported *)

(* HOL4 to_closProgScript.sml:37-38: ML code, not ported *)

(* NOT_NIL_AND_LEMMA[local] *)
let to_closProg_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 to_closProgScript.sml:46: ML code, not ported *)

(* HOL4 to_closProgScript.sml:48-61: ML code, not ported *)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
(* HOL4 to_closProgScript.sml:65-66: ML code, not ported *)

(* HOL4 to_closProgScript.sml:68: ML code, not ported *)

(* HOL4 to_closProgScript.sml:70: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* flat_to_clos                                                               *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_closProgScript.sml:76-79: ML code, not ported *)

(* HOL4 to_closProgScript.sml:84: ML code, not ported *)

(* HOL4 to_closProgScript.sml:86: ML code, not ported *)

(* HOL4 to_closProgScript.sml:88: the ML values that the definitions below
   antiquote *)

(* HOL4 to_closProgScript.sml:90: ML code, not ported *)

(* HOL4 to_closProgScript.sml:95: ML code, not ported *)

(* HOL4 to_closProgScript.sml:97: ML code, not ported *)

(* HOL4 to_closProgScript.sml:99-108: ML code, not ported *)

(* HOL4 to_closProgScript.sml:110: a theorem that HOL4 states as the value
   of an ML expression: can_interpret_ind *)
(* HOL4 to_closProgScript.sml:111: a theorem that HOL4 states as the value
   of an ML expression: check_size_ind *)

(* HOL4 to_closProgScript.sml:113-114: ML code, not ported *)

(* HOL4 to_closProgScript.sml:116: ML code, not ported *)

(* HOL4 to_closProgScript.sml:118: ML code, not ported *)

(* HOL4 to_closProgScript.sml:120-124: ML code, not ported *)

(* HOL4 to_closProgScript.sml:126-127: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* clos_mti                                                                  *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_closProgScript.sml:133: ML code, not ported *)

(* HOL4 to_closProgScript.sml:135-144: a theorem that HOL4 states as the
   value of an ML expression: clos_mti_intro_multi_side *)

(* HOL4 to_closProgScript.sml:146-147: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* clos_number                                                               *)
(* ------------------------------------------------------------------------- *)

(* TODO:
 *   - make this not have to be explicitly translated, probably by renaming it
 *     to renumber_code_locs_list_def
 *)
(* HOL4 to_closProgScript.sml:157: ML code, not ported *)

(* HOL4 to_closProgScript.sml:159-161: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* clos_op                                                                   *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_closProgScript.sml:167-178: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* clos_known                                                                *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_closProgScript.sml:184: ML code, not ported *)

(* [local] *)
let num_abs_intro = prove
 (`!x. (decProg_Tyapp (implode "num") []) x = if 0 <= x then (decProg_Tyapp
  (implode "num") []) (abs x) else (decProg_Tyapp (implode "num") []) x`,
  CHEAT_TAC);;

(* HOL4 to_closProgScript.sml:192-194: ML code, not ported *)

(* HOL4 to_closProgScript.sml:196-201: a theorem that HOL4 states as the
   value of an ML expression: clos_known_known_op_side *)

(* HOL4 to_closProgScript.sml:203: ML code, not ported *)

(* HOL4 to_closProgScript.sml:205-214: a theorem that HOL4 states as the
   value of an ML expression: clos_known_free_side *)

(* HOL4 to_closProgScript.sml:216: ML code, not ported *)

(* [local] *)
let clos_known_get_size_sc_aux_ind = prove
 (`clos_known_get_size_sc_aux_ind`,
  CHEAT_TAC);;

(* HOL4 to_closProgScript.sml:231: ML code, not ported *)

(* HOL4 to_closProgScript.sml:233: ML code, not ported *)

(* HOL4 to_closProgScript.sml:235: ML code, not ported *)

(* HOL4 to_closProgScript.sml:237-245: a theorem that HOL4 states as the
   value of an ML expression: clos_known_known_side *)

(* HOL4 to_closProgScript.sml:247: ML code, not ported *)

(* HOL4 to_closProgScript.sml:249-258: a theorem that HOL4 states as the
   value of an ML expression: clos_ticks_remove_ticks_side *)

(* HOL4 to_closProgScript.sml:260: ML code, not ported *)

(* HOL4 to_closProgScript.sml:262-271: a theorem that HOL4 states as the
   value of an ML expression: clos_letop_let_op_side *)

(* HOL4 to_closProgScript.sml:273: ML code, not ported *)

(* HOL4 to_closProgScript.sml:275-284: a theorem that HOL4 states as the
   value of an ML expression: clos_fvs_remove_fvs_side *)

(* HOL4 to_closProgScript.sml:286: ML code, not ported *)

(* HOL4 to_closProgScript.sml:288-293: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* clos_call                                                                 *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_closProgScript.sml:299: ML code, not ported *)

(* HOL4 to_closProgScript.sml:301-307: a theorem that HOL4 states as the
   value of an ML expression: clos_call_free_side *)

let clos_call_calls_side = prove
 (`!a b. clos_call_calls_side a b <=> T`,
  CHEAT_TAC);;
  (*Move from calls proof*)
(* HOL4 to_closProgScript.sml:313-323: a proof *)

(* HOL4 to_closProgScript.sml:325-327: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* clos_annotate                                                             *)
(* ------------------------------------------------------------------------- *)

(* HOL4 to_closProgScript.sml:333: ML code, not ported *)

(* HOL4 to_closProgScript.sml:335-343: a theorem that HOL4 states as the
   value of an ML expression: clos_annotate_shift_side *)

(* HOL4 to_closProgScript.sml:345: ML code, not ported *)

(* HOL4 to_closProgScript.sml:347-354: a theorem that HOL4 states as the
   value of an ML expression: clos_annotate_alt_free_side *)

(* HOL4 to_closProgScript.sml:356-360: a theorem that HOL4 states as the
   value of an ML expression: clos_annotate_compile_side *)

(* HOL4 to_closProgScript.sml:362: ML code, not ported *)

(* HOL4 to_closProgScript.sml:364-366: a theorem that HOL4 states as the
   value of an ML expression: clos_annotate_compile_inc_side *)

(* HOL4 to_closProgScript.sml:368-370: ML code, not ported *)

(* ------------------------------------------------------------------------- *)

(* HOL4 to_closProgScript.sml:374-375: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
