(* ======================================================== *)
(*  binary_ieee: ported from HOL4's
    src/floating-point/binary_ieeeScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 14 files of the port.  *)
(* ======================================================== *)

needs "lib/integer_word.ml";;

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: words real intreal pred_set
   set_relation arithmetic *)

(* HOL4 binary_ieeeScript.sml:25: the overload tc, which the port
   expands *)

let float_FIELDS = define_record "float"
  ["Sign","word1";
   "Exponent","'w word";
   "Significand","'t word"];;
(* HOL4 binary_ieeeScript.sml:34: the overload fsign, which the port
   expands *)
(* HOL4 binary_ieeeScript.sml:35: the overload sign, which the port
   expands *)

let float_value_INDUCT,float_value_RECURSION = define_datatype
  "float_value =
     Float real
   | Infinity
   | NaN";;

(* HOL4 binary_ieeeScript.sml:44: the overload precision, which the
   port expands *)
(* HOL4 binary_ieeeScript.sml:45: the overload bias, which the port
   expands *)

let float_to_real_def = new_definition
  `float_to_real (x:('t,'w)float) =
      (if float_Exponent x = (n2w 0) then --(&1:real) pow (w2n
        (float_Sign x)) *
              ((&2:real) / (&2:real) pow (INT_MAX (:'w))) *
              (&(w2n (float_Significand x)) / (&2:real) pow (dimindex
                (:'t))) else --(&1:real) pow (w2n (float_Sign x)) *
           ((&2:real) pow (w2n (float_Exponent x)) / (&2:real) pow
             (INT_MAX (:'w))) *
           ((&1:real) + &(w2n (float_Significand x)) / (&2:real)
             pow (dimindex (:'t))))`;;

let float_value_def = new_definition
  `float_value (x:('t,'w)float) =
      (if float_Exponent x = word_T then if float_Significand x =
        (n2w 0) then Infinity else NaN else Float (float_to_real x))`;;

let float_is_nan_def = new_definition
  `float_is_nan (x:('t,'w)float) =
      (match float_value x with
         NaN -> T | _1 -> F)`;;

let float_is_signalling_def = new_definition
  `float_is_signalling (x:('t,'w)float) <=>
      float_is_nan x /\ ~(word_msb (float_Significand x))`;;

let float_is_infinite_def = new_definition
  `float_is_infinite (x:('t,'w)float) =
      (match float_value x with
         Infinity -> T | _2 -> F)`;;

let float_is_zero_def = new_definition
  `float_is_zero (x:('t,'w)float) =
      (match float_value x with
         Float r -> r = (&0) | _3 -> F)`;;

let float_is_finite_def = new_definition
  `float_is_finite (x:('t,'w)float) =
      (match float_value x with
         Float _4 -> T | _5 -> F)`;;

let float_negate_def = new_definition
  `float_negate (x:('t,'w)float) = float_Sign_fupd (K (word_not
  (float_Sign x))) x`;;

let float_abs_def = new_definition
  `float_abs (x:('t,'w)float) = float_Sign_fupd (K (n2w 0)) x`;;

let float_plus_infinity_def = new_definition
  `float_plus_infinity (:'t#'w) =
      mk_float (n2w 0) (word_T:'w word) ((n2w 0):'t word)`;;

let float_plus_zero_def = new_definition
  `float_plus_zero (:'t#'w) =
      mk_float (n2w 0) ((n2w 0):'w word) ((n2w 0):'t word)`;;

let float_top_def = new_definition
  `float_top (:'t#'w) =
      mk_float (n2w 0) (word_T - ((n2w 1):'w word)) (word_T:'t
        word)`;;

let float_minus_infinity_def = new_definition
  `float_minus_infinity (:'t#'w) =
      float_negate (float_plus_infinity (:'t#'w))`;;

let float_minus_zero_def = new_definition
  `float_minus_zero (:'t#'w) = float_negate (float_plus_zero
  (:'t#'w))`;;

let float_bottom_def = new_definition
  `float_bottom (:'t#'w) = float_negate (float_top (:'t#'w))`;;

let flags_FIELDS = define_record "flags"
  ["DivideByZero","bool";
   "InvalidOp","bool";
   "Overflow","bool";
   "Precision","bool";
   "Underflow_BeforeRounding","bool";
   "Underflow_AfterRounding","bool"];;

let clear_flags_def = new_definition
  `clear_flags = mk_flags F F F F F F`;;

let invalidop_flags_def = new_definition
  `invalidop_flags = flags_InvalidOp_fupd (K T) clear_flags`;;

let dividezero_flags_def = new_definition
  `dividezero_flags = flags_DivideByZero_fupd (K T) clear_flags`;;

let rounding_INDUCT,rounding_RECURSION = define_datatype
  "rounding =
     roundTiesToEven
   | roundTowardPositive
   | roundTowardNegative
   | roundTowardZero";;

let is_closest_def = new_definition
  `is_closest s x a <=>
      a IN s /\
      (!b. b IN s ==> abs (float_to_real a - x) <= abs
        (float_to_real b - x))`;;

let closest_such_def = new_definition
  `closest_such p s x =
      (@a. is_closest s x a /\ (!b. is_closest s x b /\ p b ==> p
        a))`;;

let closest_def = new_definition
  `closest = closest_such (K T)`;;

let largest_def = new_definition
  `largest (:'t#'w) =
      ((&2:real) pow (UINT_MAX (:'w) - 1) / (&2:real) pow (INT_MAX
        (:'w))) *
      ((&2:real) - inv ((&2:real) pow dimindex (:'t)))`;;

let threshold_def = new_definition
  `threshold (:'t#'w) =
      ((&2:real) pow (UINT_MAX (:'w) - 1) / (&2:real) pow (INT_MAX
        (:'w))) *
      ((&2:real) - inv ((&2:real) pow SUC (dimindex (:'t))))`;;

let round_def = new_definition
  `round mode (x:real) =
   (match mode with
      roundTiesToEven ->
        (let t = threshold (:'t#'w) in
          if x <= --t then float_minus_infinity (:'t#'w) else if x >=
            t then float_plus_infinity (:'t#'w) else closest_such (\a.
            ~(word_lsb (float_Significand a))) float_is_finite x) |
            roundTowardZero ->
        (let t = largest (:'t#'w) in
          if x < --t then float_bottom (:'t#'w) else if x > t then
            float_top (:'t#'w) else closest
                 {a | float_is_finite a /\ abs (float_to_real a) <=
                   abs x} x) | roundTowardPositive ->
        (let t = largest (:'t#'w) in
          if x < --t then float_bottom (:'t#'w) else if x > t then
            float_plus_infinity (:'t#'w) else closest {a |
            float_is_finite a /\ float_to_real a >= x} x) |
            roundTowardNegative ->
        (let t = largest (:'t#'w) in
          if x < --t then float_minus_infinity (:'t#'w) else if x
            > t then float_top (:'t#'w) else closest {a |
            float_is_finite a /\ float_to_real a <= x} x))`;;

let fp_op_INDUCT,fp_op_RECURSION = define_datatype
  "fp_op =
     binary_ieee_FP_Sqrt rounding (('t,'w)float)
   | binary_ieee_FP_Add rounding (('t,'w)float) (('t,'w)float)
   | binary_ieee_FP_Sub rounding (('t,'w)float) (('t,'w)float)
   | binary_ieee_FP_Mul rounding (('t,'w)float) (('t,'w)float)
   | binary_ieee_FP_Div rounding (('t,'w)float) (('t,'w)float)
   | binary_ieee_FP_MulAdd rounding (('t,'w)float) (('t,'w)float)
       (('t,'w)float)
   | binary_ieee_FP_MulSub rounding (('t,'w)float) (('t,'w)float)
       (('t,'w)float)";;

let float_some_qnan_def = new_definition
  `float_some_qnan (fp_op:('t,'w)fp_op) =
   ((@f. let qnan = f fp_op in float_is_nan qnan /\
     ~(float_is_signalling qnan))
     fp_op:('t,'w)float)`;;

let float_round_def = new_definition
  `float_round mode toneg r =
      (let x = round mode r in
         if float_is_zero x then if toneg then float_minus_zero
           (:'t#'w) else float_plus_zero (:'t#'w) else x)`;;

let float_round_with_flags_def = new_definition
  `float_round_with_flags mode to_neg r =
   (let x = (float_round mode to_neg r:('t,'w)float) and a = abs r in
   let inexact = (~(float_value x = Float r)) in
     ((flags_Precision_fupd (K inexact)
       (flags_Underflow_AfterRounding_fupd (K
              (inexact /\
               (float_Exponent (float_round mode to_neg
                 r:('t,'w+1)float) <=+
                n2w (INT_MIN (:'w)))))
                  (flags_Underflow_BeforeRounding_fupd (K (inexact /\ a
                  < (&2) / (&2) pow (INT_MAX (:'w))))
                  (flags_Overflow_fupd (K (float_is_infinite x \/ (&2)
                  pow (INT_MIN (:'w)) <= a)) clear_flags)))),x))
   // IEEE-754 permits a number of ways to detect underflow. Below
   // are two possible methods.`;;

let check_for_signalling_def = new_definition
  `check_for_signalling l = flags_InvalidOp_fupd (K (EX
  float_is_signalling l))
   clear_flags`;;

let real_to_float_def = new_definition
  `real_to_float m = float_round m (m = roundTowardNegative)`;;

let float_to_int_def = new_definition
  `float_to_int mode (x:('t,'w)float) =
   (match float_value x with
      Float r ->
       SOME (match mode with
                roundTiesToEven ->
                  (let f = INT_FLOOR r in
                  let df = abs (r - real_of_int f) in
                  if (df < (&1:real) / (&2)) \/ (df = (&1:real) /
                    (&2)) /\ EVEN (num_of_int (abs f)) then
                    f else
                    INT_CEILING r) | roundTowardPositive ->
                      INT_CEILING r | roundTowardNegative -> INT_FLOOR r
                      | roundTowardZero ->
                  (if float_Sign x = (n2w 1) then INT_CEILING r
                    else INT_FLOOR r)) | _6 -> NONE)`;;

let float_sqrt_def = new_definition
  `float_sqrt mode (x:('t,'w)float) =
      (if float_Sign x = (n2w 0) then
         match float_value x with
            NaN -> (check_for_signalling [x],float_some_qnan
              (binary_ieee_FP_Sqrt mode x)) | Infinity ->
              (clear_flags,float_plus_infinity (:'t#'w)) | Float r ->
              (float_round_with_flags mode F (sqrt r)) else if x =
              float_minus_zero (:'t#'w) then
        (clear_flags,float_minus_zero (:'t#'w)) else
        (invalidop_flags,float_some_qnan (binary_ieee_FP_Sqrt mode
          x)))`;;

let float_add_def = new_definition
  `float_add mode (x:('t,'w)float) (y:('t,'w)float) =
      (match (float_value x,float_value y) with (
         NaN,_7) -> (check_for_signalling [x; y],
                    float_some_qnan (binary_ieee_FP_Add mode x y)) |
                      (_8,NaN) -> (check_for_signalling [y],
                    float_some_qnan (binary_ieee_FP_Add mode x y)) |
                      (Infinity,Infinity) ->
            (if float_Sign x = float_Sign y then
               (clear_flags,x) else
               (invalidop_flags,float_some_qnan (binary_ieee_FP_Add
                 mode x y))) | (Infinity,_9) -> (clear_flags,x) |
                 (_10,Infinity) -> (clear_flags,y) | (Float r1,Float r2)
                 ->
            float_round_with_flags mode
               (if (r1 = (&0)) /\ (r2 = (&0)) /\ (float_Sign x =
                 float_Sign y) then float_Sign
                  x = (n2w 1) else mode = roundTowardNegative) (r1
                    + r2))`;;

let float_sub_def = new_definition
  `float_sub mode (x:('t,'w)float) (y:('t,'w)float) =
      (match (float_value x,float_value y) with (
         NaN,_11) -> (check_for_signalling [x; y],
                    float_some_qnan (binary_ieee_FP_Sub mode x y)) |
                      (_12,NaN) -> (check_for_signalling [y],
                    float_some_qnan (binary_ieee_FP_Sub mode x y)) |
                      (Infinity,Infinity) ->
            (if float_Sign x = float_Sign y then
               (invalidop_flags,float_some_qnan (binary_ieee_FP_Sub
                 mode x y)) else
               (clear_flags,x)) | (Infinity,_13) -> (clear_flags,x) |
                 (_14,Infinity) -> (clear_flags,float_negate y) | (Float
                 r1,Float r2) ->
            float_round_with_flags mode
               (if (r1 = (&0)) /\ (r2 = (&0)) /\ ~(float_Sign x =
                 float_Sign y) then float_Sign
                  x = (n2w 1) else mode = roundTowardNegative) (r1
                    - r2))`;;

let float_mul_def = new_definition
  `float_mul mode (x:('t,'w)float) (y:('t,'w)float) =
      (match (float_value x,float_value y) with (
         NaN,_15) -> (check_for_signalling [x; y],
                    float_some_qnan (binary_ieee_FP_Mul mode x y)) |
                      (_16,NaN) -> (check_for_signalling [y],
                    float_some_qnan (binary_ieee_FP_Mul mode x y)) |
                      (Infinity,Float r) ->
            (if r = (&0) then
               (invalidop_flags,float_some_qnan (binary_ieee_FP_Mul
                 mode x y)) else
               (clear_flags,
                (if float_Sign x = float_Sign y then
                   float_plus_infinity (:'t#'w) else
                     float_minus_infinity (:'t#'w)))) | (Float
                     r,Infinity) ->
            (if r = (&0) then
               (invalidop_flags,float_some_qnan (binary_ieee_FP_Mul
                 mode x y)) else
               (clear_flags,
                (if float_Sign x = float_Sign y then
                   float_plus_infinity (:'t#'w) else
                     float_minus_infinity (:'t#'w)))) |
                     (Infinity,Infinity) ->
            (clear_flags,
             (if float_Sign x = float_Sign y then
                float_plus_infinity (:'t#'w) else
                  float_minus_infinity (:'t#'w))) | (Float r1,Float r2)
                  ->
            float_round_with_flags mode (~(float_Sign x =
              float_Sign y)) (r1 * r2))`;;

let float_div_def = new_definition
  `float_div mode (x:('t,'w)float) (y:('t,'w)float) =
      (match (float_value x,float_value y) with (
         NaN,_17) -> (check_for_signalling [x; y],
                    float_some_qnan (binary_ieee_FP_Div mode x y)) |
                      (_18,NaN) -> (check_for_signalling [y],
                    float_some_qnan (binary_ieee_FP_Div mode x y)) |
                      (Infinity,Infinity) ->
            (invalidop_flags,float_some_qnan (binary_ieee_FP_Div mode
              x y)) | (Infinity,_19) ->
            (clear_flags,
             (if float_Sign x = float_Sign y then
                float_plus_infinity (:'t#'w) else
                  float_minus_infinity (:'t#'w))) | (_20,Infinity) ->
            (clear_flags,
             (if float_Sign x = float_Sign y then
                float_plus_zero (:'t#'w) else float_minus_zero
                  (:'t#'w))) | (Float r1,Float r2) ->
            (if r2 = (&0) then if r1 = (&0) then
                       (invalidop_flags,float_some_qnan
                         (binary_ieee_FP_Div mode x y)) else
                       (dividezero_flags,
                        (if float_Sign x = float_Sign y then
                           float_plus_infinity (:'t#'w) else
                             float_minus_infinity (:'t#'w))) else
                             float_round_with_flags mode
                             (~(float_Sign x = float_Sign y)) (r1 /
                             r2)))`;;

let float_mul_add_def = new_definition
  `float_mul_add mode (x:('t,'w)float) (y:('t,'w)float) (z:('t,'w)float)
  =
      (let signP = float_Sign x ?? float_Sign y in
      let infP = (float_is_infinite x \/ float_is_infinite y) in
         if float_is_nan x \/ float_is_nan y \/ float_is_nan z then
            (check_for_signalling [x; y; z],
             float_some_qnan (binary_ieee_FP_MulAdd mode x y z)) else
               if float_is_infinite x /\ float_is_zero y \/
                 float_is_zero x /\ float_is_infinite y \/
                 float_is_infinite z /\ infP /\ ~(signP = float_Sign
                   z) then
            (invalidop_flags,float_some_qnan (binary_ieee_FP_MulAdd
              mode x y z)) else if float_is_infinite z /\ (float_Sign z
              = (n2w 0)) \/ infP /\ (signP = (n2w 0)) then
              (clear_flags,float_plus_infinity (:'t#'w)) else if
              float_is_infinite z /\ (float_Sign z = (n2w 1)) \/ infP /\
              (signP = (n2w 1)) then (clear_flags,float_minus_infinity
              (:'t#'w)) else
           let r1 = float_to_real x * float_to_real y in let
               r2 = float_to_real z in let
               r = r1 + r2 in
             float_round_with_flags
               mode
               ((r = (&0)) /\
                (if (r1 = (&0)) /\ (r2 = (&0)) /\ (signP = float_Sign
                  z) then
                   signP = (n2w 1) else mode = roundTowardNegative)
                     \/
                r < (&0))
               r)`;;

let float_compare_INDUCT,float_compare_RECURSION = define_datatype
  "float_compare =
     LT
   | EQ
   | GT
   | UN";;

let float_compare_def = new_definition
  `float_compare (x:('t,'w)float) (y:('t,'w)float) =
      (match (float_value x,float_value y) with (
         NaN,_21) -> UN | (_22,NaN) -> UN | (Infinity,Infinity) ->
            (if float_Sign x = float_Sign y then EQ else if
              float_Sign x = (n2w 1) then LT else GT) | (Infinity,_23)
              -> (if float_Sign x = (n2w 1) then LT else GT) |
              (_24,Infinity) -> (if float_Sign y = (n2w 1) then GT else
              LT) | (Float r1,Float r2) ->
            (if r1 < r2 then LT else if r1 = r2 then EQ else GT))`;;

let float_less_than_def = new_definition
  `float_less_than (x:('t,'w)float) y =
      (float_compare x y = LT)`;;

let float_less_equal_def = new_definition
  `float_less_equal (x:('t,'w)float) y =
      (match float_compare x y with
         LT -> T | EQ -> T | _25 -> F)`;;

let float_greater_than_def = new_definition
  `float_greater_than (x:('t,'w)float) y =
      (float_compare x y = GT)`;;

let float_greater_equal_def = new_definition
  `float_greater_equal (x:('t,'w)float) y =
      (match float_compare x y with
         GT -> T | EQ -> T | _26 -> F)`;;

let float_equal_def = new_definition
  `float_equal (x:('t,'w)float) y =
      (float_compare x y = EQ)`;;
