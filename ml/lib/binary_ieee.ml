(* ======================================================== *)
(*  binary_ieee: ported from HOL4's
    src/floating-point/binary_ieeeScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

(* HOL4 ancestors outside the port: words real intreal pred_set set_relation arithmetic *)
(* HOL4 overload (expanded in the port):
     tc = transitive_closure *)
let float_FIELDS = define_record "float"
  ["Sign","word1";
   "Exponent","'w word";
   "Significand","'t word"];;
(* HOL4 overload (expanded in the port):
     fsign = λa. -1 pow w2n a.Sign *)
(* HOL4 overload (expanded in the port):
     sign = fsign *)
let float_value_INDUCT,float_value_RECURSION = define_datatype
  "float_value = Float (real) | Infinity | NaN";;
(* HOL4 overload (expanded in the port):
     precision = fcp$dimindex *)
(* HOL4 overload (expanded in the port):
     bias = words$INT_MAX *)
let float_to_real_def = cake_define
  `float_to_real (x:('t,'w)float) =
      (if float_Exponent x = (n2w 0) then --1r pow (w2n (float_Sign
        x)) *
              (2r / 2r pow ((INT_MAX) (:'w))) *
              (&(w2n (float_Significand x)) / 2r pow ((dimindex)
                (:'t))) else --1r pow (w2n (float_Sign x)) *
           (2r pow (w2n (float_Exponent x)) / 2r pow ((INT_MAX)
             (:'w))) *
           (1r + &(w2n (float_Significand x)) / 2r pow ((dimindex)
             (:'t))))`;;
let float_value_def = cake_define
  `float_value (x:('t,'w)float) =
      (if float_Exponent x = UINT_MAXw then if float_Significand x =
        (n2w 0) then Infinity else NaN else Float (float_to_real x))`;;
let float_is_nan_def = cake_define
  `float_is_nan (x:('t,'w)float) =
      (match float_value x with
         NaN -> T | _1 -> F)`;;
let float_is_signalling_def = cake_define
  `float_is_signalling (x:('t,'w)float) <=>
      float_is_nan x /\ ~word_msb (float_Significand x)`;;
let float_is_infinite_def = cake_define
  `float_is_infinite (x:('t,'w)float) =
      (match float_value x with
         Infinity -> T | _2 -> F)`;;
let float_is_zero_def = cake_define
  `float_is_zero (x:('t,'w)float) =
      (match float_value x with
         Float r -> r = 0 | _3 -> F)`;;
let float_is_finite_def = cake_define
  `float_is_finite (x:('t,'w)float) =
      (match float_value x with
         Float _4 -> T | _5 -> F)`;;
let float_negate_def = cake_define
  `float_negate (x:('t,'w)float) = float_Sign_fupd (K (~float_Sign x)) x`;;
let float_plus_infinity_def = cake_define
  `float_plus_infinity (:'t#'w) =
      mk_float (n2w 0) (UINT_MAXw:'w word) ((n2w 0):'t word)`;;
let float_plus_zero_def = cake_define
  `float_plus_zero (:'t#'w) =
      mk_float (n2w 0) ((n2w 0):'w word) ((n2w 0):'t word)`;;
let float_top_def = cake_define
  `float_top (:'t#'w) =
      mk_float (n2w 0) (UINT_MAXw - ((n2w 1):'w word)) (UINT_MAXw:'t
        word)`;;
let float_minus_infinity_def = cake_define
  `float_minus_infinity (:'t#'w) =
      float_negate (float_plus_infinity (:'t#'w))`;;
let float_minus_zero_def = cake_define
  `float_minus_zero (:'t#'w) = float_negate (float_plus_zero (:'t#'w))`;;
let float_bottom_def = cake_define
  `float_bottom (:'t#'w) = float_negate (float_top (:'t#'w))`;;
let flags_FIELDS = define_record "flags"
  ["DivideByZero","bool";
   "InvalidOp","bool";
   "Overflow","bool";
   "Precision","bool";
   "Underflow_BeforeRounding","bool";
   "Underflow_AfterRounding","bool"];;
let clear_flags_def = cake_define
  `clear_flags = mk_flags F F F F F F`;;
let invalidop_flags_def = cake_define
  `invalidop_flags = flags_InvalidOp_fupd (K T) clear_flags`;;
let rounding_INDUCT,rounding_RECURSION = define_datatype
  "rounding = roundTiesToEven | roundTowardPositive | roundTowardNegative | roundTowardZero";;
let is_closest_def = cake_define
  `is_closest s x a <=>
      a IN s /\
      (!b. b IN s ==> abs (float_to_real a - x) <= abs (float_to_real
        b - x))`;;
let closest_such_def = cake_define
  `closest_such p s x =
      (@a. is_closest s x a /\ (!b. is_closest s x b /\ p b ==> p a))`;;
let closest_def = cake_define
  `closest = closest_such (K T)`;;
let largest_def = cake_define
  `largest (:'t#'w) =
      (2r pow (UINT_MAX (:'w) - 1) / 2r pow (INT_MAX (:'w))) *
      (2r - inv (2r pow dimindex (:'t)))`;;
let threshold_def = cake_define
  `threshold (:'t#'w) =
      (2r pow (UINT_MAX (:'w) - 1) / 2r pow (INT_MAX (:'w))) *
      (2r - inv (2r pow SUC (dimindex (:'t))))`;;
let round_def = cake_define
  `round mode (x:real) =
   (match mode with
      roundTiesToEven ->
        let t = threshold (:'t#'w) in
          if x <= --t then float_minus_infinity (:'t#'w) else if x >=
            t then float_plus_infinity (:'t#'w) else closest_such (\a.
            ~word_lsb (float_Significand a)) float_is_finite x |
            roundTowardZero ->
        let t = largest (:'t#'w) in
          if x < --t then float_bottom (:'t#'w) else if x > t then
            float_top (:'t#'w) else closest
                 {a | float_is_finite a /\ abs (float_to_real a) <=
                   abs x} x | roundTowardPositive ->
        let t = largest (:'t#'w) in
          if x < --t then float_bottom (:'t#'w) else if x > t then
            float_plus_infinity (:'t#'w) else closest {a |
            float_is_finite a /\ float_to_real a >= x} x |
            roundTowardNegative ->
        let t = largest (:'t#'w) in
          if x < --t then float_minus_infinity (:'t#'w) else if x > t
            then float_top (:'t#'w) else closest {a | float_is_finite a
            /\ float_to_real a <= x} x)`;;
let fp_op_INDUCT,fp_op_RECURSION = define_datatype
  "fp_op = binary_ieee_FP_Sqrt (rounding) (('t,'w)float) | binary_ieee_FP_Add (rounding) (('t,'w)float) (('t,'w)float) | binary_ieee_FP_Sub (rounding) (('t,'w)float) (('t,'w)float) | binary_ieee_FP_Mul (rounding) (('t,'w)float) (('t,'w)float) | binary_ieee_FP_Div (rounding) (('t,'w)float) (('t,'w)float) | binary_ieee_FP_MulAdd (rounding) (('t,'w)float) (('t,'w)float) (('t,'w)float) | binary_ieee_FP_MulSub (rounding) (('t,'w)float) (('t,'w)float) (('t,'w)float)";;
let float_some_qnan_def = cake_define
  `float_some_qnan (fp_op:('t,'w)fp_op) =
   ((@f. let qnan = f fp_op in float_is_nan qnan /\
     ~float_is_signalling qnan)
     fp_op:('t,'w)float)`;;
let float_round_def = cake_define
  `float_round mode toneg r =
      (let x = round mode r in
         if float_is_zero x then if toneg then float_minus_zero
           (:'t#'w) else float_plus_zero (:'t#'w) else x)`;;
let float_round_with_flags_def = cake_define
  `float_round_with_flags mode to_neg r =
   (let x = float_round mode to_neg r:('t,'w)float and a = abs r in
   let inexact = (~(float_value x = Float r)) in
     ((flags_Precision_fupd (K inexact)
       (flags_Underflow_AfterRounding_fupd (K
              (inexact /\
               (float_Exponent (float_round mode to_neg
                 r:('t,'w+1)float) <=+
                n2w (INT_MIN (:'w)))))
                  (flags_Underflow_BeforeRounding_fupd (K (inexact /\ a
                  < 2 / 2 pow ((INT_MAX) (:'w)))) (flags_Overflow_fupd
                  (K (float_is_infinite x \/ 2 pow (INT_MIN (:'w)) <=
                  a)) clear_flags)))),x))`;;
let check_for_signalling_def = cake_define
  `check_for_signalling l = flags_InvalidOp_fupd (K (EXISTS
  float_is_signalling l))
   clear_flags`;;
(* PORT FAILED: Definition float_mul_add_def: expected 'in' but found ';' at 974
Definition float_mul_add_def[nocompute]:
   float_mul_add mode
      (x: ('t, 'w) float) (y: ('t, 'w) float) (z: ('t, 'w) float) =
      let signP = x.Sign ?? y.Sign in
      let infP = (float_is_infinite x \/ float_is_infinite y)
      in
         if float_is_nan x \/ float_is_nan y \/ float_is_nan z then
            (check_for_signalling [x; y; z],
             float_some_qnan (FP_MulAdd mode x y z))
         else if float_is_infinite x /\ float_is_zero y \/
                 float_is_zero x /\ float_is_infinite y \/
                 float_is_infinite z /\ infP /\ signP <> z.Sign then
            (invalidop_flags, float_some_qnan (FP_MulAdd mode x y z))
         else if float_is_infinite z /\ (z.Sign = 0w) \/ infP /\ (signP = 0w)
            then (clear_flags, float_plus_infinity (:'t # 'w))
         else if float_is_infinite z /\ (z.Sign = 1w) \/ infP /\ (signP = 1w)
            then (clear_flags, float_minus_infinity (:'t # 'w))
         else
           let r1 = float_to_real x * float_to_real y ;
               r2 = float_to_real z ;
               r = r1 + r2 ;
           in
             float_round_with_flags
               mode
               ((r = 0) /\
                (if (r1 = 0) /\ (r2 = 0) /\ (signP = z.Sign) then
                   signP = 1w
                 else mode = roundTowardNegative) \/
                r < 0)
               r
End
*)

