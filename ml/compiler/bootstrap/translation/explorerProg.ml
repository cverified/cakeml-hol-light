(* ======================================================== *)
(*  explorerProg: ported from HOL4's
    compiler/bootstrap/translation/explorerProgScript.sml
    A definition theory, with no definitions and 2 theorems.  Needed
    by decodeProg.ml.  *)
(* ======================================================== *)

(*
  Translate the compiler explorer parts of the compiler.
*)

needs "compiler/backend/presLang.ml";;
needs "compiler/bootstrap/translation/inferProg.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "explorerProg"
  ["inferProg"; "ml_translator"];;

(* HOL4 explorerProgScript.sml:10-12: ML code, not ported *)

(* HOL4 explorerProgScript.sml:16: ML code, not ported *)

(* HOL4 explorerProgScript.sml:18-19: ML code, not ported *)

(* TODO: this is copied in many bootstrap translation files - should be in a lib? *)
(* HOL4 explorerProgScript.sml:22-35: ML code, not ported *)

(* HOL4 explorerProgScript.sml:37: ML code, not ported *)

(* HOL4 explorerProgScript.sml:39: ML code, not ported *)

(* HOL4 explorerProgScript.sml:41-42: ML code, not ported *)

(* HOL4 explorerProgScript.sml:44: ML code, not ported *)

(* [local] *)
let json_to_mlstring_ind = prove
 (`json_to_mlstring_ind`,
  CHEAT_TAC);;

(* HOL4 explorerProgScript.sml:56: ML code, not ported *)

(* displayLang *)

(* HOL4 explorerProgScript.sml:60: ML code, not ported *)

(* presLang *)

(* HOL4 explorerProgScript.sml:64-66: ML code, not ported *)

(* HOL4 explorerProgScript.sml:68: ML code, not ported *)

(* HOL4 explorerProgScript.sml:70-71: ML code, not ported *)

(* HOL4 explorerProgScript.sml:73: ML code, not ported *)

(* HOL4 explorerProgScript.sml:75-80: a theorem that HOL4 states as the
   value of an ML expression: num_to_varn_aux_side *)

(* HOL4 explorerProgScript.sml:82: ML code, not ported *)

(* HOL4 explorerProgScript.sml:84-86: ML code, not ported *)

(* HOL4 explorerProgScript.sml:88-90: ML code, not ported *)

(* HOL4 explorerProgScript.sml:92-94: ML code, not ported *)

(* HOL4 explorerProgScript.sml:96-98: ML code, not ported *)

(* [local] *)
let string_imp_thm = prove
 (`string_imp = (\s. display_String s)`,
  CHEAT_TAC);;

(* HOL4 explorerProgScript.sml:106-108: ML code, not ported *)

(* HOL4 explorerProgScript.sml:110-111: ML code, not ported *)


(* HOL4 explorerProgScript.sml:114: ML code, not ported *)

(* HOL4 explorerProgScript.sml:116: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
