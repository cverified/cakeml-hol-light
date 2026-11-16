(* ======================================================== *)
(*  RatProg: ported from HOL4's
    basis/RatProgScript.sml
    A definition theory, with 19 definitions and 27 theorems.
    Needed by CharProg.ml.  *)
(* ======================================================== *)

(*
  Module for computing over the rational numbers.
*)

needs "basis/IntProg.ml";;
needs "basis/PrettyPrinterProg.ml";;
needs "basis/pure/mlprettyprinter.ml";;
needs "basis/pure/mlrat.ml";;
needs "basis/pure/mlvector.ml";;
needs "lib/rat.ml";;
needs "lib/ternaryComparisons.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "RatProg"
  ["IntProg"; "PrettyPrinterProg"; "ml_prog"; "ml_translator"; "mlrat";
   "mlvector"];;

let _ = do_list hide_constant ["ABS"];;
(* HOL4 ancestors outside the port: gcd *)

(* HOL4 RatProgScript.sml:11: ML code, not ported *)

(* HOL4 RatProgScript.sml:13: ML code, not ported *)

(* HOL4 RatProgScript.sml:15-17: ML code, not ported *)

let RatProg_div_gcd_def = new_definition
  `RatProg_div_gcd a b =
     let d = hol4_gcd (ml_translator_num_of_int a) b in
       if d = 0 \/ d = 1 then RatPair a b else RatPair (a / &d) (b DIV d)`;;

(* HOL4 RatProgScript.sml:25: ML code, not ported *)

(* HOL4 RatProgScript.sml:27: ML code, not ported *)

(* HOL4 RatProgScript.sml:29: ML code, not ported *)

(* provides the Map.map name for the map type *)
(* HOL4 RatProgScript.sml:32-33: ML code, not ported *)

(* refinement invariants *)

let RAT_TYPE_def = new_definition
  `RAT_TYPE (r:rat) =
     (\v. ?(n:int) (d:num). (r = (rat_of_int n) / &d) /\
                           hol4_gcd (cfFFIType_Num (abs n)) d = 1 /\ ~(d =
                             0) /\
                           RATIONAL_TYPE (RatPair n d) v)`;;

(* HOL4 RatProgScript.sml:44: the ML values that the definitions below
   antiquote *)

let REAL_TYPE_def = new_definition
  `REAL_TYPE (r:real) =
     (\v. ?(x:rat). RAT_TYPE x v /\ (real_of_rat x = r))`;;

(* HOL4 RatProgScript.sml:51: the ML values that the definitions below
   antiquote *)

(* transfer *)

(* [local] *)
let RAT_RAT = prove
 (`(!r1. real_of_rat (f1 r1) = f2 (real_of_rat r1)) ==>
    (!v. (RAT_TYPE (Arrow) RAT_TYPE) f1 v ==>
        (REAL_TYPE (Arrow) REAL_TYPE) f2 v)`,
  CHEAT_TAC);;

(* [local] *)
let RAT_RAT_RAT = prove
 (`(!r1 r2. real_of_rat (f1 r1 r2) = f2 (real_of_rat r1) (real_of_rat r2)) ==>
    (!v. (RAT_TYPE (Arrow) RAT_TYPE (Arrow) RAT_TYPE) f1 v ==>
        (REAL_TYPE (Arrow) REAL_TYPE (Arrow) REAL_TYPE) f2 v)`,
  CHEAT_TAC);;

(* [local] *)
let RAT_RAT_BOOL = prove
 (`(!r1 r2. f1 r1 r2 <=> f2 (real_of_rat r1) (real_of_rat r2)) ==>
    (!v. (RAT_TYPE (Arrow) RAT_TYPE (Arrow) BOOL) f1 v ==>
        (REAL_TYPE (Arrow) REAL_TYPE (Arrow) BOOL) f2 v)`,
  CHEAT_TAC);;

(* [local] *)
let RAT_BOOL = prove
 (`(!r1. (f1 r1) = f2 (real_of_rat r1)) ==>
    (!v. (RAT_TYPE (Arrow) BOOL) f1 v ==>
        (REAL_TYPE (Arrow) BOOL) f2 v)`,
  CHEAT_TAC);;

(* [local] *)
let RAT_INT = prove
 (`(!r1. (f1 r1) = f2 (real_of_rat r1)) ==>
    (!v. (RAT_TYPE (Arrow) INT) f1 v ==>
        (REAL_TYPE (Arrow) INT) f2 v)`,
  CHEAT_TAC);;


(* -- *)

(* HOL4 RatProgScript.sml:132-133: ML code, not ported *)

(* HOL4 RatProgScript.sml:135-146: a theorem that HOL4 states as the value
   of an ML expression: Eval_RAT_INT *)

(* HOL4 RatProgScript.sml:148-153: a theorem that HOL4 states as the value
   of an ML expression: Eval_RAT_NUM *)

(* HOL4 RatProgScript.sml:155-166: a theorem that HOL4 states as the value
   of an ML expression: Eval_REAL_INT *)

(* HOL4 RatProgScript.sml:168-173: a theorem that HOL4 states as the value
   of an ML expression: Eval_REAL_NUM *)

let pair_le_def = new_definition
  `pair_le (RatPair n1 d1) (RatPair n2 d2) = (n1 * &d2 <= n2 * ((&d1):int))`;;

(* HOL4 RatProgScript.sml:179-180: ML code, not ported *)

(* HOL4 RatProgScript.sml:182: ML code, not ported *)

(* HOL4 RatProgScript.sml:184-205: a theorem that HOL4 states as the value
   of an ML expression: Eval_RAT_LE *)

(* HOL4 RatProgScript.sml:207-212: a theorem that HOL4 states as the value
   of an ML expression: Eval_REAL_LE *)

(* HOL4 RatProgScript.sml:214-215: ML code, not ported *)

(* HOL4 RatProgScript.sml:217-223: a theorem that HOL4 states as the value
   of an ML expression: Eval_REAL_GE *)

let pair_lt_def = new_definition
  `pair_lt (RatPair n1 d1) (RatPair n2 d2) = (n1 * &d2 < n2 * ((&d1):int))`;;

(* HOL4 RatProgScript.sml:229-230: ML code, not ported *)

(* HOL4 RatProgScript.sml:232-253: a theorem that HOL4 states as the value
   of an ML expression: Eval_RAT_LT *)

(* HOL4 RatProgScript.sml:255-260: a theorem that HOL4 states as the value
   of an ML expression: Eval_REAL_LT *)

(* HOL4 RatProgScript.sml:262-263: ML code, not ported *)

(* HOL4 RatProgScript.sml:265-271: a theorem that HOL4 states as the value
   of an ML expression: Eval_REAL_GT *)

let RatProg_pair_compare_def = new_definition
  `RatProg_pair_compare (RatPair n1 d1) (RatPair n2 d2) =
     let x1 = n1 * &d2 in
     let x2 = n2 * &d1 in
       if x1 < x2 then LESS else if x2 < x1 then GREATER else EQUAL`;;

let rat_compare_def = new_definition
  `rat_compare (r1:rat) r2 =
     if r1 < r2 then LESS else if r2 < r1 then GREATER else EQUAL`;;

(* HOL4 RatProgScript.sml:286-287: ML code, not ported *)

(* HOL4 RatProgScript.sml:289-311: a theorem that HOL4 states as the value
   of an ML expression: Eval_RAT_COMPARE *)

(* HOL4 RatProgScript.sml:313-314: ML code, not ported *)

(* HOL4 RatProgScript.sml:316-323: a theorem that HOL4 states as the value
   of an ML expression: Eval_REAL_MIN *)

(* HOL4 RatProgScript.sml:325-326: ML code, not ported *)

(* HOL4 RatProgScript.sml:328-337: a theorem that HOL4 states as the value
   of an ML expression: Eval_REAL_MAX *)

(* [local] *)
let gcd_LESS_EQ = prove
 (`!m n. ~(n = 0) ==> gcd m n <= n`,
  CHEAT_TAC);;

(* DIV_EQ_0 *)
let RatProg_DIV_EQ_0 = prove
 (`0 < n ==> ((m DIV n = 0) <=> m < n)`,
  CHEAT_TAC);;

let DIV_GCD_NONZERO = prove
 (`(0 < m ==> 0 < m DIV hol4_gcd m n) /\ (0 < n ==> 0 < n DIV hol4_gcd m n)`,
  CHEAT_TAC);;

(* [local] *)
let INT_NEG_DIV_FACTOR = prove
 (`0 < (x:num) ==> (--(&(x * y):int) (&x) = --(&y))`,
  CHEAT_TAC);;

(* [local] *)
let PAIR_TYPE_IMP_RAT_TYPE = prove
 (`r = rat_of_int m / &n /\ ~(n = 0) ==>
   RATIONAL_TYPE (RatProg_div_gcd m n) v ==> RAT_TYPE r v`,
  CHEAT_TAC);;

let pair_add_def = new_definition
  `pair_add (RatPair n1 d1) (RatPair n2 d2) =
     RatProg_div_gcd ((n1 * &d2) + (n2 * &d1)) (d1 * d2)`;;

(* HOL4 RatProgScript.sml:440-441: ML code, not ported *)

(* [local] *)
let abs_rat_ONTO = prove
 (`!r. ?f. abs_rat f = r`,
  CHEAT_TAC);;

(* HOL4 RatProgScript.sml:449-473: a theorem that HOL4 states as the value
   of an ML expression: Eval_RAT_ADD *)

(* HOL4 RatProgScript.sml:475-480: a theorem that HOL4 states as the value
   of an ML expression: Eval_REAL_ADD *)

let pair_sub_def = new_definition
  `pair_sub (RatPair n1 d1) (RatPair n2 d2) =
     RatProg_div_gcd ((n1 * &d2) - (n2 * &d1)) (d1 * d2)`;;

(* HOL4 RatProgScript.sml:487-488: ML code, not ported *)

(* HOL4 RatProgScript.sml:490-513: a theorem that HOL4 states as the value
   of an ML expression: Eval_RAT_SUB *)

(* HOL4 RatProgScript.sml:515-520: a theorem that HOL4 states as the value
   of an ML expression: Eval_REAL_SUB *)

(* [local] *)
let rat_neg_lem = prove
 (`!(x:rat). --x = 0 - x`,
  CHEAT_TAC);;

(* HOL4 RatProgScript.sml:528-529: ML code, not ported *)

(* HOL4 RatProgScript.sml:531-538: a theorem that HOL4 states as the value
   of an ML expression: Eval_REAL_NEG *)

let pair_mul_def = new_definition
  `pair_mul (RatPair n1 d1) (RatPair n2 d2) = RatProg_div_gcd (n1 *
  (n2:int)) (d1 * (d2:num))`;;

(* HOL4 RatProgScript.sml:544-545: ML code, not ported *)

(* HOL4 RatProgScript.sml:547-569: a theorem that HOL4 states as the value
   of an ML expression: Eval_RAT_MUL *)

(* HOL4 RatProgScript.sml:571-576: a theorem that HOL4 states as the value
   of an ML expression: Eval_REAL_MUL *)

let pair_inv_def = new_definition
  `pair_inv (RatPair n1 d1) =
     (RatPair (if n1 < (&0) then --(&d1) else (&d1):int)
       (ml_translator_num_of_int n1))`;;

(* HOL4 RatProgScript.sml:583-584: ML code, not ported *)

(* HOL4 RatProgScript.sml:586-613: a theorem that HOL4 states as the value
   of an ML expression: Eval_RAT_INV *)

(* HOL4 RatProgScript.sml:615-632: a theorem that HOL4 states as the value
   of an ML expression: Eval_REAL_INV *)

(* HOL4 RatProgScript.sml:634-635: ML code, not ported *)

(* HOL4 RatProgScript.sml:637-639: ML code, not ported *)

let real_of_rat_eq_0 = prove
 (`~(real_of_rat r = 0) ==> ~(r = 0)`,
  CHEAT_TAC);;

(* [local] *)
let Eval_REAL_DIV_lemma = prove
 (`!v. (!v1 v2. PRECONDITION (rat_div_side v1 v2) ==>
                (ml_translator_Eq RAT_TYPE v1 (Arrow) ml_translator_Eq
                  RAT_TYPE v2 (Arrow) RAT_TYPE) (/) v) ==>
       PRECONDITION (~(r = 0)) ==> (REAL_TYPE (Arrow) ml_translator_Eq
         REAL_TYPE r (Arrow) REAL_TYPE) (/) v`,
  CHEAT_TAC);;

(* HOL4 RatProgScript.sml:677-680: ML code, not ported *)

(* HOL4 RatProgScript.sml:682-683: ML code, not ported *)

(* [local] *)
let real_to_str_lemma = prove
 (`(RATIONAL_TYPE (Arrow) STRING_TYPE) mlrat_toString v ==>
   (REAL_TYPE (Arrow) STRING_TYPE) real_to_str v`,
  CHEAT_TAC);;

(* HOL4 RatProgScript.sml:705-707: a theorem that HOL4 states as the value
   of an ML expression: real_to_str_v_thm *)

let pp_rat_def = new_definition
  `pp_rat r = pp_token (mlrat_toString r)`;;

(* HOL4 RatProgScript.sml:713-714: ML code, not ported *)

let rat_of_int_MUL_num = prove
 (`rat_of_int n * &(m:num) = rat_of_int (n * &m) /\
   &(m:num) * rat_of_int n = rat_of_int (&m * n)`,
  CHEAT_TAC);;

let SGN_ABS = prove
 (`SGN n * abs n = n`,
  CHEAT_TAC);;

let Int_Num_ABS = prove
 (`&(cfFFIType_Num (abs n)) = abs n`,
  CHEAT_TAC);;

(* Num_le *)
let num_le = prove
 (`x <= y /\ x >= 0 ==>
   cfFFIType_Num x <= cfFFIType_Num y`,
  CHEAT_TAC);;

let int_divides_ABS = prove
 (`x int_divides y ==>
   x int_divides (abs y)`,
  CHEAT_TAC);;

let gcd_RATND = prove
 (`hol4_gcd (cfFFIType_Num (abs n)) d = 1 /\ 0 < d ==>
   RATN (rat_of_int n / &d) = n /\
   RATD (rat_of_int n / &d) = d`,
  CHEAT_TAC);;

let pair_num_def = new_definition
  `pair_num (RatPair i n) = i`;;

(* HOL4 RatProgScript.sml:831-832: ML code, not ported *)

(* HOL4 RatProgScript.sml:834-847: a theorem that HOL4 states as the value
   of an ML expression: Eval_RAT_RATN *)

let pair_denom_def = new_definition
  `pair_denom (RatPair i n) = n`;;

(* HOL4 RatProgScript.sml:853-854: ML code, not ported *)

(* HOL4 RatProgScript.sml:856-869: a theorem that HOL4 states as the value
   of an ML expression: Eval_RAT_RATD *)

let pair_floor_def = new_definition
  `pair_floor (RatPair n d) = n / &d`;;

(* HOL4 RatProgScript.sml:875-876: ML code, not ported *)

let RAT_INT_FLOOR_def = new_definition
  `RAT_INT_FLOOR r = INT_FLOOR (real_of_rat r)`;;

let RAT_INT_FLOOR_compute = prove
 (`RAT_INT_FLOOR r =
   RATN r / &(RATD r)`,
  CHEAT_TAC);;

(* HOL4 RatProgScript.sml:894-912: a theorem that HOL4 states as the value
   of an ML expression: Eval_RAT_FLOOR *)

(* HOL4 RatProgScript.sml:914-920: a theorem that HOL4 states as the value
   of an ML expression: Eval_REAL_FLOOR *)

let RAT_INT_CEILING_def = new_definition
  `RAT_INT_CEILING r = INT_CEILING (real_of_rat r)`;;

let RAT_INT_CEILING_compute = prove
 (`RAT_INT_CEILING r =
   let i = RAT_INT_FLOOR r in
     if rat_of_int i = r then i else i + 1`,
  CHEAT_TAC);;

(* HOL4 RatProgScript.sml:936-937: ML code, not ported *)

(* HOL4 RatProgScript.sml:939-945: a theorem that HOL4 states as the value
   of an ML expression: Eval_REAL_CEILING *)

let pair_is_int_def = new_definition
  `pair_is_int (RatPair n d) <=> d = 1`;;

(* HOL4 RatProgScript.sml:951-952: ML code, not ported *)

let RAT_is_int_def = new_definition
  `RAT_is_int (x:rat) <=>
   x = rat_of_int (RAT_INT_FLOOR x)`;;

let RAT_is_int_compute = prove
 (`RAT_is_int x <=> RATD x = 1`,
  CHEAT_TAC);;

(* HOL4 RatProgScript.sml:971-984: a theorem that HOL4 states as the value
   of an ML expression: Eval_RAT_is_int *)

(* HOL4 RatProgScript.sml:986-993: a theorem that HOL4 states as the value
   of an ML expression: Eval_REAL_is_int *)

(* HOL4 RatProgScript.sml:995: ML code, not ported *)

(* HOL4 RatProgScript.sml:997-1008: a theorem that HOL4 states as the value
   of an ML expression: EqualityType_RAT_TYPE *)

(* HOL4 RatProgScript.sml:1010-1016: a theorem that HOL4 states as the value
   of an ML expression: EqualityType_REAL_TYPE *)

(* HOL4 RatProgScript.sml:1018: ML code, not ported *)

(* HOL4 RatProgScript.sml:1020-1021: ML code, not ported *)

(* HOL4 RatProgScript.sml:1023: ML code, not ported *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["ABS"];;

(* and the interface *)
let _ = unhide_overloads ();;
