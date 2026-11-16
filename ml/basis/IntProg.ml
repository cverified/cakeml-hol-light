(* ======================================================== *)
(*  IntProg: ported from HOL4's
    basis/IntProgScript.sml
    A definition theory, with no definitions and 9 theorems.  Needed
    by PrettyPrinterProg.ml and RatProg.ml.  *)
(* ======================================================== *)

(*
  Module about the built-in integer type. Note that CakeML uses
  arbitrary precision integers (the mathematical integers).
*)

needs "basis/mlbasicsProg.ml";;
needs "basis/pure/mlint.ml";;
needs "basis/pure/mlstring.ml";;
needs "lib/ternaryComparisons.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "IntProg"
  ["ml_prog"; "ml_translator"; "mlbasicsProg"; "mlint"];;
(* HOL4 ancestors outside the port: gcd *)

(* HOL4 IntProgScript.sml:11: ML code, not ported *)

(* HOL4 IntProgScript.sml:13: ML code, not ported *)

(* HOL4 IntProgScript.sml:15-16: ML code, not ported *)

(* HOL4 IntProgScript.sml:18-27: the ML values that the definitions below
   antiquote *)

(* HOL4 IntProgScript.sml:29: ML code, not ported *)

(* HOL4 IntProgScript.sml:31-32: ML code, not ported *)

(* HOL4 IntProgScript.sml:34: ML code, not ported *)

(* [local] *)
let tochar_side_dec = prove
 (`i < 10 ==> tochar_side i`,
  CHEAT_TAC);;

(* [local] *)
let num_to_chars_side = prove
 (`!i j k acc. num_to_chars_side i j k acc`,
  CHEAT_TAC);;
(* HOL4 IntProgScript.sml:50: ML code, not ported *)

(* HOL4 IntProgScript.sml:52: ML code, not ported *)

(* HOL4 IntProgScript.sml:54: ML code, not ported *)

(* HOL4 IntProgScript.sml:56-57: ML code, not ported *)

(* HOL4 IntProgScript.sml:59-67: a theorem that HOL4 states as the value of
   an ML expression: Eval_NUM_toString *)

(* HOL4 IntProgScript.sml:69: ML code, not ported *)

(* HOL4 IntProgScript.sml:71: ML code, not ported *)

(* HOL4 IntProgScript.sml:73-75: the ML values that the definitions below
   antiquote *)

(* HOL4 IntProgScript.sml:77-78: ML code, not ported *)

(* HOL4 IntProgScript.sml:80: ML code, not ported *)
(* HOL4 IntProgScript.sml:81-84: a theorem that HOL4 states as the value of
   an ML expression: fromChars_unsafe_ind *)

(* HOL4 IntProgScript.sml:86: ML code, not ported *)

(* HOL4 IntProgScript.sml:88-90: ML code, not ported *)

let fromchars_unsafe_side_thm = prove
 (`!n s. n <= LENGTH s ==> fromchars_unsafe_side n (implode s)`,
  CHEAT_TAC);;

(* HOL4 IntProgScript.sml:99-106: a theorem that HOL4 states as the value of
   an ML expression: fromString_unsafe_side *)

let fromChar_thm = prove
 (`fromChar char =
     let vc = ORD char in
     if 48 <= vc /\ vc <= 57 then
       SOME (vc - 48) else NONE`,
  CHEAT_TAC);;

(* HOL4 IntProgScript.sml:117-118: ML code, not ported *)

(* HOL4 IntProgScript.sml:120-123: a theorem that HOL4 states as the value
   of an ML expression: fromChars_ind *)

(* HOL4 IntProgScript.sml:125: ML code, not ported *)

(* HOL4 IntProgScript.sml:127-131: ML code, not ported *)

let fromchars_side_thm = prove
 (`!n s. n <= LENGTH s ==> fromchars_side n (implode s)`,
  CHEAT_TAC);;

(* HOL4 IntProgScript.sml:140-147: a theorem that HOL4 states as the value
   of an ML expression: fromString_side *)

(* HOL4 IntProgScript.sml:149-150: ML code, not ported *)

(* GCD *)

(* HOL4 IntProgScript.sml:154: ML code, not ported *)

(* HOL4 IntProgScript.sml:156: ML code, not ported *)

(* HOL4 IntProgScript.sml:158: ML code, not ported *)

(* HOL4 IntProgScript.sml:160-161: ML code, not ported *)

let gcd_v_thm = prove
 (`(NUM (Arrow) NUM (Arrow) NUM) gcd int_gcd_v`,
  CHEAT_TAC);;

(* HOL4 IntProgScript.sml:178: ML code, not ported *)

(* compare *)

(* HOL4 IntProgScript.sml:182-183: ML code, not ported *)

let num_cmp_v_thm = prove
 (`(NUM (Arrow) NUM (Arrow) ORDERING_TYPE)
  (semanticPrimitives_num_cmp:num->num->ordering) int_cmp_v`,
  CHEAT_TAC);;

(* HOL4 IntProgScript.sml:200: ML code, not ported *)

(* HOL4 IntProgScript.sml:202: ML code, not ported *)

(* HOL4 IntProgScript.sml:204: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
