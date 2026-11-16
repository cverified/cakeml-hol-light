(* ======================================================== *)
(*  StringProg: ported from HOL4's
    basis/StringProgScript.sml
    A definition theory, with no definitions and 6 theorems.  Needed
    by mlbasicsProg.ml.  *)
(* ======================================================== *)

(*
  Module about the built-in string type.
*)

needs "basis/VectorProg.ml";;
needs "basis/pure/mlstring.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "StringProg"
  ["VectorProg"; "ml_prog"; "ml_translator"; "mlstring"];;

(* HOL4 StringProgScript.sml:10-11: ML code, not ported *)

(* HOL4 StringProgScript.sml:13: ML code, not ported *)

(* HOL4 StringProgScript.sml:15: ML code, not ported *)

(* HOL4 StringProgScript.sml:17-18: ML code, not ported *)

(* HOL4 StringProgScript.sml:20-23: the ML values that the definitions below
   antiquote *)

(* HOL4 StringProgScript.sml:25-30: the ML values that the definitions below
   antiquote *)

(* HOL4 StringProgScript.sml:32-40: the ML values that the definitions below
   antiquote *)

(* HOL4 StringProgScript.sml:42: ML code, not ported *)

(* HOL4 StringProgScript.sml:44-47: a theorem that HOL4 states as the value
   of an ML expression: extract_side_thm *)

(* HOL4 StringProgScript.sml:49-50: ML code, not ported *)

(* HOL4 StringProgScript.sml:52-53: ML code, not ported *)

(* HOL4 StringProgScript.sml:55-58: ML code, not ported *)

(* HOL4 StringProgScript.sml:60-62: ML code, not ported *)

(* [local] *)
let translate_aux_side_thm = prove
 (`!f s n len. n + len = strlen s ==> translate_aux_side f s n len`,
  CHEAT_TAC);;

(* HOL4 StringProgScript.sml:70-72: a theorem that HOL4 states as the value
   of an ML expression: translate_side_thm *)

(* HOL4 StringProgScript.sml:74-76: ML code, not ported *)

(* HOL4 StringProgScript.sml:78-79: ML code, not ported *)

(* HOL4 StringProgScript.sml:81: ML code, not ported *)

(* HOL4 StringProgScript.sml:83: ML code, not ported *)

(* HOL4 StringProgScript.sml:85: ML code, not ported *)

(* HOL4 StringProgScript.sml:87: ML code, not ported *)

(* HOL4 StringProgScript.sml:89-91: ML code, not ported *)

(* [local] *)
let tokens_alt_aux_side_thm = prove
 (`!f s i j k. i <= j /\ j <= k /\ k <= strlen s ==> tokens_alt_aux_side f s
  i j k`,
  CHEAT_TAC);;

(* HOL4 StringProgScript.sml:101-103: a theorem that HOL4 states as the
   value of an ML expression: tokens_side_thm *)

(* HOL4 StringProgScript.sml:105: ML code, not ported *)

(* HOL4 StringProgScript.sml:107-108: ML code, not ported *)

(* HOL4 StringProgScript.sml:110: ML code, not ported *)

(* HOL4 StringProgScript.sml:112-114: ML code, not ported *)

(* [local] *)
let fields_alt_aux_side_thm = prove
 (`!f s i j k. i <= j /\ j <= k /\ k <= strlen s ==> fields_alt_aux_side f s
  i j k`,
  CHEAT_TAC);;

(* HOL4 StringProgScript.sml:124-126: a theorem that HOL4 states as the
   value of an ML expression: fields_side_thm *)

(* HOL4 StringProgScript.sml:128-129: ML code, not ported *)

(* HOL4 StringProgScript.sml:131-134: ML code, not ported *)

(* [local] *)
let isStringThere_aux_side_thm = prove
 (`!s1 s2 s1i s2i len.
      s1i + len <= strlen s1 /\ s2i + len <= strlen s2 ==>
      isstringthere_aux_side s1 s2 s1i s2i len`,
  CHEAT_TAC);;

(* HOL4 StringProgScript.sml:144-146: ML code, not ported *)
(* [local] *)
let isSubstring_aux_side_thm = prove
 (`!s1 s2 lens1 n len.
     (lens1 = strlen s1) /\ n + len + lens1 <= strlen s2 + 1 ==>
     issubstring_aux_side s1 s2 lens1 n len`,
  CHEAT_TAC);;

(* HOL4 StringProgScript.sml:157-162: a theorem that HOL4 states as the
   value of an ML expression: isSubstring_side_thm *)

(* HOL4 StringProgScript.sml:164-169: a theorem that HOL4 states as the
   value of an ML expression: isSuffix_thm *)

(* HOL4 StringProgScript.sml:171-176: a theorem that HOL4 states as the
   value of an ML expression: isPrefix_thm *)

(* HOL4 StringProgScript.sml:178-179: ML code, not ported *)

(* HOL4 StringProgScript.sml:181-184: ML code, not ported *)

(* HOL4 StringProgScript.sml:186-188: ML code, not ported *)

(* collate_aux_side_thm[local] *)
let StringProg_collate_aux_side_thm = prove
 (`!f s1 s2 ord n len. (n + len =
     (if strlen s1 < strlen s2 then strlen s1
     else strlen s2)) ==> collate_aux_side f s1 s2 ord n len`,
  CHEAT_TAC);;

(* HOL4 StringProgScript.sml:199-201: a theorem that HOL4 states as the
   value of an ML expression: collate_side_thm *)

(* HOL4 StringProgScript.sml:203-208: ML code, not ported *)

(* HOL4 StringProgScript.sml:210-211: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
