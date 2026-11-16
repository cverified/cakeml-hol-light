(* ======================================================== *)
(*  VectorProg: ported from HOL4's
    basis/VectorProgScript.sml
    A definition theory, with no definitions and 9 theorems.  Needed
    by StringProg.ml.  *)
(* ======================================================== *)

(*
  Module about the built-in 'a vector.
*)

needs "basis/ListProg.ml";;
needs "basis/pure/mlvector.ml";;
needs "lib/regexp_compiler.ml";;
needs "semantics/ast.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "VectorProg"
  ["ListProg"; "ast"; "ml_prog"; "ml_translator"; "mlvector"];;

(* HOL4 VectorProgScript.sml:11: ML code, not ported *)

(* HOL4 VectorProgScript.sml:13: ML code, not ported *)

(* HOL4 VectorProgScript.sml:15: ML code, not ported *)

(* HOL4 VectorProgScript.sml:17-18: ML code, not ported *)

(* HOL4 VectorProgScript.sml:20-22: the ML values that the definitions below
   antiquote *)

(* HOL4 VectorProgScript.sml:24-25: ML code, not ported *)

(* HOL4 VectorProgScript.sml:27-29: ML code, not ported *)

(* HOL4 VectorProgScript.sml:31-32: ML code, not ported *)

(* HOL4 VectorProgScript.sml:34-35: ML code, not ported *)

(* HOL4 VectorProgScript.sml:37-38: ML code, not ported *)

(* HOL4 VectorProgScript.sml:40-43: ML code, not ported *)

(* HOL4 VectorProgScript.sml:45-48: ML code, not ported *)

(* HOL4 VectorProgScript.sml:50-52: ML code, not ported *)

(* [local] *)
let foldli_aux_side_thm = prove
 (`!f e vec n len. n + len = length vec ==> foldli_aux_side f e vec n len`,
  CHEAT_TAC);;

(* HOL4 VectorProgScript.sml:60-62: a theorem that HOL4 states as the value
   of an ML expression: foldli_side_thm *)

(* HOL4 VectorProgScript.sml:64-67: ML code, not ported *)

(* HOL4 VectorProgScript.sml:69-71: ML code, not ported *)

(* [local] *)
let foldl_aux_side_thm = prove
 (`!f e vec n len. n + len = length vec ==> foldl_aux_side f e vec n len`,
  CHEAT_TAC);;

(* HOL4 VectorProgScript.sml:79-81: a theorem that HOL4 states as the value
   of an ML expression: foldl_side_thm *)

(* HOL4 VectorProgScript.sml:83-86: ML code, not ported *)

(* HOL4 VectorProgScript.sml:88-90: ML code, not ported *)

(* [local] *)
let foldri_aux_side_thm = prove
 (`!f e vec len. len <= length vec ==> foldri_aux_side f e vec len`,
  CHEAT_TAC);;

(* HOL4 VectorProgScript.sml:98-100: a theorem that HOL4 states as the value
   of an ML expression: foldri_side_thm *)

(* HOL4 VectorProgScript.sml:102-105: ML code, not ported *)

(* HOL4 VectorProgScript.sml:107-109: ML code, not ported *)

(* [local] *)
let foldr_aux_side_thm = prove
 (`!f e vec len. len <= length vec ==> foldr_aux_side f e vec len`,
  CHEAT_TAC);;

(* HOL4 VectorProgScript.sml:117-119: a theorem that HOL4 states as the
   value of an ML expression: foldr_side_thm *)

(* HOL4 VectorProgScript.sml:121-124: ML code, not ported *)

(* HOL4 VectorProgScript.sml:126-128: ML code, not ported *)

(* [local] *)
let findi_aux_side_thm = prove
 (`!f vec n len. n + len = length vec ==> findi_aux_side f vec n len`,
  CHEAT_TAC);;

(* HOL4 VectorProgScript.sml:136-138: a theorem that HOL4 states as the
   value of an ML expression: findi_side_thm *)

(* HOL4 VectorProgScript.sml:140-143: ML code, not ported *)

(* HOL4 VectorProgScript.sml:145-147: ML code, not ported *)

(* [local] *)
let find_aux_side_thm = prove
 (`!f vec n len. n + len = length vec ==> find_aux_side f vec n len`,
  CHEAT_TAC);;

(* HOL4 VectorProgScript.sml:155-157: a theorem that HOL4 states as the
   value of an ML expression: find_side_thm *)

(* HOL4 VectorProgScript.sml:159-162: ML code, not ported *)

(* HOL4 VectorProgScript.sml:164-166: ML code, not ported *)

(* [local] *)
let exists_aux_side_thm = prove
 (`!f vec n len. n + len = length vec ==> exists_aux_side f vec n len`,
  CHEAT_TAC);;

(* HOL4 VectorProgScript.sml:174-176: a theorem that HOL4 states as the
   value of an ML expression: exists_side_thm *)

(* HOL4 VectorProgScript.sml:178-181: ML code, not ported *)

(* HOL4 VectorProgScript.sml:183-185: ML code, not ported *)

(* [local] *)
let all_aux_side_thm = prove
 (`!f vec n len. n + len = length vec ==> all_aux_side f vec n len`,
  CHEAT_TAC);;

(* HOL4 VectorProgScript.sml:193-195: a theorem that HOL4 states as the
   value of an ML expression: all_side_thm *)

(* HOL4 VectorProgScript.sml:197-200: ML code, not ported *)

(* HOL4 VectorProgScript.sml:202-204: ML code, not ported *)

(* [local] *)
let collate_aux_side_thm = prove
 (`!f vec1 vec2 n ord len. n + len =
     (if length vec1 < length vec2 then length vec1
     else length vec2) ==>
         collate_aux_side f vec1 vec2 n ord len`,
  CHEAT_TAC);;

(* HOL4 VectorProgScript.sml:216-218: a theorem that HOL4 states as the
   value of an ML expression: collate_side_thm *)

(* HOL4 VectorProgScript.sml:220-221: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
