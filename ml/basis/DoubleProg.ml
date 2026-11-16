(* ======================================================== *)
(*  DoubleProg: ported from HOL4's
    basis/DoubleProgScript.sml
    A definition theory, with 24 definitions and 25 theorems.
    Needed by MarshallingProg.ml.  *)
(* ======================================================== *)

(*
  Module for the built-in double floating-point type.
  Defines basic arithmetic operations like +,-,*,/, and FMA,
  logical operations <, <=, >, >=, and =
  and to-/fromString functions for parsing and pretty-printing constants
*)

needs "basis/CommandLineProg.ml";;
needs "basis/pure/mlstring.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/binary_ieeeProps.ml";;
needs "lib/machine_ieee.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "DoubleProg"
  ["CommandLineProg"; "ml_prog"; "ml_translator"];;

let _ = do_list hide_constant ["unit"];;
(* HOL4 ancestors outside the port: words real *)

(* HOL4 DoubleProgScript.sml:14: ML code, not ported *)

(* Double module -- translated *)

(* HOL4 DoubleProgScript.sml:18: ML code, not ported *)

(* HOL4 DoubleProgScript.sml:20: ML code, not ported *)

(* HOL4 DoubleProgScript.sml:22-23: ML code, not ported *)

(* HOL4 DoubleProgScript.sml:25: ML code, not ported *)

(* --------------------------------------------------------------------------
 * Byte array for the FFI communication
 * ------------------------------------------------------------------------- *)

(* HOL4 DoubleProgScript.sml:31-49: the ML values that the definitions below
   antiquote *)

(* --------------------------------------------------------------------------
 * Helper functions
 * ------------------------------------------------------------------------- *)

let byte_0_def = new_definition
  `byte_0 (d:word64) = ((w2w d):word8)`;;

let byte_1_def = new_definition
  `byte_1 (d:word64) = ((w2w (d >>> 8)):word8)`;;

let byte_2_def = new_definition
  `byte_2 (d:word64) = ((w2w (d >>> 16)):word8)`;;

let byte_3_def = new_definition
  `byte_3 (d:word64) = ((w2w (d >>> 24)):word8)`;;

let byte_4_def = new_definition
  `byte_4 (d:word64) = ((w2w (d >>> 32)):word8)`;;

let byte_5_def = new_definition
  `byte_5 (d:word64) = ((w2w (d >>> 40)):word8)`;;

let byte_6_def = new_definition
  `byte_6 (d:word64) = ((w2w (d >>> 48)):word8)`;;

let byte_7_def = new_definition
  `byte_7 (d:word64) = ((w2w (d >>> 56)):word8)`;;

(* HOL4 DoubleProgScript.sml:87-94: ML code, not ported *)

let is_0_byte_def = new_definition
  `is_0_byte (c:word8) = (c = n2w 0)`;;

(* HOL4 DoubleProgScript.sml:100: ML code, not ported *)

(* HOL4 DoubleProgScript.sml:102-116: ML code, not ported *)

(* HOL4 DoubleProgScript.sml:118-132: ML code, not ported *)

let prepareString_def = new_definition
  `prepareString (s:mlstring) = mlstring_translate (\c. if c = (CHR 126)
  then (CHR 45) else c) s`;;
(* HOL4 DoubleProgScript.sml:137: ML code, not ported *)

(* HOL4 DoubleProgScript.sml:139: ML code, not ported *)

(* HOL4 DoubleProgScript.sml:141-143: ML code, not ported *)

(* HOL4 DoubleProgScript.sml:145-147: ML code, not ported *)

(* --------------------------------------------------------------------------
 * Functions that use the FFI
 * ------------------------------------------------------------------------- *)

(* 0: Double.fromString *)
(* HOL4 DoubleProgScript.sml:154-165: ML code, not ported *)

(* 1: Double.toString *)
(* HOL4 DoubleProgScript.sml:168-177: ML code, not ported *)

(* 2: Double.fromInt *)
(* HOL4 DoubleProgScript.sml:180-188: ML code, not ported *)

(* 3: Double.toInt *)
(* HOL4 DoubleProgScript.sml:191-199: ML code, not ported *)

(* 4: Double.pow *)
(* HOL4 DoubleProgScript.sml:202-211: ML code, not ported *)

(* 5: Double.ln *)
(* HOL4 DoubleProgScript.sml:214-222: ML code, not ported *)

(* 6: Double.exp *)
(* HOL4 DoubleProgScript.sml:225-233: ML code, not ported *)

(* 7: Double.floor *)
(* HOL4 DoubleProgScript.sml:236-244: ML code, not ported *)

(* --------------------------------------------------------------------------
 * Ternary operations
 * ------------------------------------------------------------------------- *)

(* HOL4 DoubleProgScript.sml:250-253: ML code, not ported *)

(* --------------------------------------------------------------------------
 * Binary operations
 * ------------------------------------------------------------------------- *)

(* HOL4 DoubleProgScript.sml:259-264: ML code, not ported *)

(* HOL4 DoubleProgScript.sml:266-270: ML code, not ported *)

(* --------------------------------------------------------------------------
 * Unary operations
 * ------------------------------------------------------------------------- *)

(* HOL4 DoubleProgScript.sml:276-278: ML code, not ported *)

(* ----------------------------------------------------------------------
    Taking floats apart
   ---------------------------------------------------------------------- *)

new_type_abbrev("float64",`:(52,11)float`);;

let significand_def = new_definition
  `significand f = float_to_fp64 f && (n2w 0xFFFFFFFFFFFFF)`;;

let significand_correct = prove
 (`significand f = w2w (float_Significand f)`,
  CHEAT_TAC);;

let significand_correct' = prove
 (`float_Significand
     f = w2w (significand f)`,
  CHEAT_TAC);;

let exponent_def = new_definition
  `exponent f = (float_to_fp64 f >>> 52) && (n2w 0x7FF)`;;

let exponent_correct = prove
 (`exponent f = w2w (float_Exponent f)`,
  CHEAT_TAC);;

let exponent_correct' = prove
 (`float_Exponent
     f = w2w (exponent f)`,
  CHEAT_TAC);;

let sign_def = new_definition
  `DoubleProg_sign f = (float_to_fp64 f >>> 63) && (n2w 1)`;;

let sign_correct = prove
 (`DoubleProg_sign f = w2w (float_Sign f)`,
  CHEAT_TAC);;

let sign_correct' = prove
 (`float_Sign
     f = w2w (DoubleProg_sign f)`,
  CHEAT_TAC);;

(* HOL4 DoubleProgScript.sml:372-374: ML code, not ported *)

(* ----------------------------------------------------------------------
    Putting a float together from its constituent parts (layout order)
   ---------------------------------------------------------------------- *)

let construct_def = new_definition
  `construct (sgn:word64) (exp:word64) (sgf:word64) =
     fp64_to_float (
       ((sgn && (n2w 1)) << 63) ||
       ((exp && (n2w 0x7FF)) << 52) ||
       (sgf && (n2w 0xFFFFFFFFFFFFF)))`;;

(* HOL4 DoubleProgScript.sml:389: a theorem that HOL4 states as the value of
   an ML expression: w2w'_11 *)
(* HOL4 DoubleProgScript.sml:390: a theorem that HOL4 states as the value of
   an ML expression: w2w'_52 *)
(* HOL4 DoubleProgScript.sml:391: a theorem that HOL4 states as the value of
   an ML expression: w2w'_01 *)

(* HOL4 DoubleProgScript.sml:393-396: a theorem that HOL4 states as the
   value of an ML expression: w2w_range_11 *)
(* HOL4 DoubleProgScript.sml:397-401: a theorem that HOL4 states as the
   value of an ML expression: w2w_range_52 *)
(* HOL4 DoubleProgScript.sml:402-406: a theorem that HOL4 states as the
   value of an ML expression: w2w_range_01 *)


let construct_correct = prove
 (`construct sig exp sgf = mk_float (w2w sig) (w2w exp) (w2w sgf)`,
  CHEAT_TAC);;

let construct_correct' = prove
 (`mk_float sig exp sgf =
   construct (w2w sig) (w2w exp) (w2w sgf)`,
  CHEAT_TAC);;

(* HOL4 DoubleProgScript.sml:441: ML code, not ported *)

let fnext_hi_def = new_definition
  `fnext_hi f = fp64_to_float (float_to_fp64 f + (n2w 1))`;;

let fnext_lo_def = new_definition
  `fnext_lo f = fp64_to_float (float_to_fp64 f - (n2w 1))`;;

(* HOL4 DoubleProgScript.sml:451-452: ML code, not ported *)

(* HOL4 DoubleProgScript.sml:454: the overload f2r, which the port expands *)
(* HOL4 DoubleProgScript.sml:455: the overload nl, which the port expands *)

let float_is_finite_characterisation = prove
 (`float_is_finite f <=> ~(exponent f = (n2w 0x7FF))`,
  CHEAT_TAC);;

(* HOL4 DoubleProgScript.sml:469: ML code, not ported *)

let float_is_zero_characterisation = prove
 (`float_is_zero f <=> exponent f = (n2w 0) /\ significand f = (n2w 0)`,
  CHEAT_TAC);;

(* HOL4 DoubleProgScript.sml:478: ML code, not ported *)

let flt_max_def = new_definition
  `(flt_max:(52,11)float) =
   mk_float (n2w 0) (n2w 0x7FE) (n2w 0xFFFFFFFFFFFFF)`;;

(* HOL4 DoubleProgScript.sml:485: ML code, not ported *)

let flt_max_correct = prove
 (`flt_max = float_top (:52#11)`,
  CHEAT_TAC);;

(* HOL4 DoubleProgScript.sml:493: the overload precision, which the port
   expands *)

let maxulp_def = new_definition
  `(maxulp:(52,11)float) = mk_float (n2w 0) (n2w 1994) (n2w 0)`;;

(* HOL4 DoubleProgScript.sml:502: ML code, not ported *)

let twicemaxulp_def = new_definition
  `(twicemaxulp:(52,11)float) = mk_float (n2w 0) (n2w 1995) (n2w 0)`;;

(* HOL4 DoubleProgScript.sml:510: ML code, not ported *)

let ffloat_ulp_def = new_definition
  `ffloat_ulp (f0:(52,11)float) =
   let f = float64_abs f0 in
     if float_is_finite f then
       if f = flt_max then maxulp
       else float64_sub (fnext_hi f) f
     else twicemaxulp`;;
(* HOL4 DoubleProgScript.sml:522: ML code, not ported *)

let posinf64_def = new_definition
  `(posinf64:(52,11)float) = mk_float (n2w 0) (n2w 0x7ff) (n2w 0)`;;
(* HOL4 DoubleProgScript.sml:529: ML code, not ported *)

let neginf64_def = new_definition
  `(neginf64:(52,11)float) = mk_float (n2w 1) (n2w 0x7ff) (n2w 0)`;;
(* HOL4 DoubleProgScript.sml:536: ML code, not ported *)

let posmin64_def = new_definition
  `posmin64 = (mk_float (n2w 0) (n2w 0) (n2w 1))`;;
(* HOL4 DoubleProgScript.sml:541: ML code, not ported *)

let poszero64_def = new_definition
  `poszero64 = (mk_float (n2w 0) (n2w 0) (n2w 0))`;;
(* HOL4 DoubleProgScript.sml:546: ML code, not ported *)

let word_addR_concat = prove
 (`FINITE (UNIV:'a->bool) /\ FINITE (UNIV:'b->bool) /\
   w2n w2 + y < 2 EXP dimindex (:'b) ==>
   (w1:'a word) @@ (w2:'b word) + n2w y = ((w1 @@ (w2 + n2w y)):'c word)`,
  CHEAT_TAC);;

let fp64_word_concat_assoc = prove
 (`(w1:1 word) @@ (((w2:11 word) @@ (w3:52 word)):63 word) =
   (((w1 @@ w2):12 word):word64)`,
  CHEAT_TAC);;

(* HOL4 DoubleProgScript.sml:621-623: ML code, not ported *)

let next_hi_fnext_hi = prove
 (`float_is_finite f ==> next_hi f = fnext_hi f`,
  CHEAT_TAC);;

let next_lo_fnext_lo = prove
 (`float_is_finite f /\ ~(float_is_zero f) ==> next_lo f = fnext_lo f`,
  CHEAT_TAC);;

let maxulp_correct = prove
 (`float_to_real maxulp = (float_ulp) (float_top (:52#11))`,
  CHEAT_TAC);;

(* HOL4 DoubleProgScript.sml:697: the overload abs, which the port expands *)

(* HOL4 DoubleProgScript.sml:699: a theorem that HOL4 states as the value of
   an ML expression: ABS_REFL' *)

(* HOL4 DoubleProgScript.sml:701: ML code, not ported *)

(* HOL4 DoubleProgScript.sml:703-705: a theorem that HOL4 states as the
   value of an ML expression: abs_sub_lemma *)

let ffloat_ulp_correct = prove
 (`float_is_finite f ==>
   float_to_real (ffloat_ulp f) = (float_ulp) f`,
  CHEAT_TAC);;

(* --------------------------------------------------------------------------
 * Pretty-printer
 * ------------------------------------------------------------------------- *)

(* HOL4 DoubleProgScript.sml:755-760: the ML values that the definitions
   below antiquote *)

(* HOL4 DoubleProgScript.sml:762-763: ML code, not ported *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["unit"];;

(* and the interface *)
let _ = unhide_overloads ();;
