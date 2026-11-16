(* ======================================================== *)
(*  decodeProg: ported from HOL4's
    compiler/bootstrap/translation/decodeProgScript.sml
    A definition theory, with no definitions and 9 theorems.  Needed
    by sexp_parserProg.ml.  *)
(* ======================================================== *)

(*
  Translate the compiler's state decoder.
*)

needs "compiler/backend/serialiser/backend_enc_dec.ml";;
needs "compiler/backend/serialiser/num_list_enc_dec.ml";;
needs "compiler/backend/serialiser/num_tree_enc_dec.ml";;
needs "compiler/bootstrap/translation/explorerProg.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "decodeProg"
  ["backend_enc_dec"; "cf"; "explorerProg"; "ml_translator";
   "num_list_enc_dec"; "num_tree_enc_dec"];;

(* HOL4 decodeProgScript.sml:11-13: ML code, not ported *)

(* HOL4 decodeProgScript.sml:15: ML code, not ported *)

(* HOL4 decodeProgScript.sml:17-18: ML code, not ported *)

(* translator setup *)

(* HOL4 decodeProgScript.sml:22-32: ML code, not ported *)

(* HOL4 decodeProgScript.sml:34-35: ML code, not ported *)

(* NOT_NIL_AND_LEMMA *)
let decodeProg_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 decodeProgScript.sml:43: ML code, not ported *)

(* HOL4 decodeProgScript.sml:45-61: ML code, not ported *)

(* HOL4 decodeProgScript.sml:63: ML code, not ported *)

(* --- *)

(* HOL4 decodeProgScript.sml:67-68: ML code, not ported *)

(* HOL4 decodeProgScript.sml:70: ML code, not ported *)

let IsTypeRep_BACKEND_CONFIG_v = prove
 (`IsTypeRep BACKEND_CONFIG_v BACKEND_CONFIG_TYPE`,
  CHEAT_TAC);;

(* HOL4 decodeProgScript.sml:108-109: a theorem that HOL4 states as the
   value of an ML expression: EqualityType_BACKEND_CONFIG_TYPE *)

let INJ_BACKEND_CONFIG_v = prove
 (`INJ BACKEND_CONFIG_v UNIV UNIV`,
  CHEAT_TAC);;
add_simp INJ_BACKEND_CONFIG_v;;

(* --- *)

(* HOL4 decodeProgScript.sml:121-124: ML code, not ported *)

let list_dec'_eq_MAP = prove
 (`!f t. num_tree_enc_dec_list_dec' f t = MAP f (num_tree_enc_dec_list_dec' I
  t)`,
  CHEAT_TAC);;

let option_dec'_eq_OPTION_MAP = prove
 (`!f t. option_dec' f t =
   match option_dec' I t with
     NONE -> NONE
   | SOME res -> SOME (f res)`,
  CHEAT_TAC);;

(* HOL4 decodeProgScript.sml:142-144: ML code, not ported *)

(* HOL4 decodeProgScript.sml:146-164: ML code, not ported *)

(* --- *)

(* HOL4 decodeProgScript.sml:168-176: ML code, not ported *)

(* --- *)

(* HOL4 decodeProgScript.sml:180-192: ML code, not ported *)

(* HOL4 decodeProgScript.sml:194-197: ML code, not ported *)

(* HOL4 decodeProgScript.sml:199-200: ML code, not ported *)

(* HOL4 decodeProgScript.sml:202: ML code, not ported *)

(* HOL4 decodeProgScript.sml:204-206: ML code, not ported *)

(* HOL4 decodeProgScript.sml:208-210: ML code, not ported *)

(* [local] *)
let bvi_exp_dec'_ind = prove
 (`bvi_exp_dec'_ind`,
  CHEAT_TAC);;

(* HOL4 decodeProgScript.sml:227: ML code, not ported *)

(* HOL4 decodeProgScript.sml:229: ML code, not ported *)

let pair_dec'_eq = prove
 (`pair_dec' d1 d2 = (\t. (d1 (num_tree_enc_dec_nth 0
  (num_tree_enc_dec_list_dec' I t)),d2 (num_tree_enc_dec_nth 1
  (num_tree_enc_dec_list_dec' I t))))`,
  CHEAT_TAC);;

(* HOL4 decodeProgScript.sml:238-242: ML code, not ported *)

(* [local] *)
let closlang_exp_dec'_ind = prove
 (`closlang_exp_dec'_ind`,
  CHEAT_TAC);;

(* HOL4 decodeProgScript.sml:272: ML code, not ported *)

(* HOL4 decodeProgScript.sml:274-276: ML code, not ported *)

(* HOL4 decodeProgScript.sml:278-279: ML code, not ported *)

(* HOL4 decodeProgScript.sml:281-284: ML code, not ported *)

(* HOL4 decodeProgScript.sml:286: ML code, not ported *)


(* HOL4 decodeProgScript.sml:289: ML code, not ported *)

(* HOL4 decodeProgScript.sml:291: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
