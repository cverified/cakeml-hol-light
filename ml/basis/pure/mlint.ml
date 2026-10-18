(* ======================================================== *)
(*  mlint: ported from HOL4's
    basis/pure/mlintScript.sml
    A definition theory, with 20 definitions and 41 theorems.
    Needed by compiler.ml, displayLang.ml, export.ml, infer_t.ml,
    jsonLang.ml and presLang.ml.  *)
(* ======================================================== *)

(*
  Pure functions for the Int module.
*)

needs "basis/pure/mlstring.ml";;
needs "lib/ternaryComparisons.ml";;
(* HOL4 ancestors outside the port: gcd *)

let toChar_def = cake_define
  `toChar digit = (if digit < 10 then CHR (ORD (CHR 48) + digit) else
  CHR ((ORD (CHR 65) + digit) - 10))`;;

(* decimal encoding is very slightly faster if we avoid dividing large big-ints
   by 10, and instead divide them by a power of 10 that fits in 28 bits *)
let exp_for_dec_enc_def = cake_define
  `exp_for_dec_enc = 8`;;

(* compatibility with previous version*)
let padLen_DEC_def = cake_define
  `padLen_DEC = exp_for_dec_enc`;;
let maxSmall_DEC_def1 = cake_define
  `maxSmall_DEC = 10 EXP exp_for_dec_enc`;;

(* HOL4 mlintScript.sml:37-38: the ML values that the definitions
   below antiquote *)

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 mlintScript.sml:45-54: the tactic that proves the termination *)
let num_to_chars_def = cake_define_list_try (fun () ->
  `inv_image (MEASURE I LEX MEASURE I)
          (\(i,j,k,_1). (i * (10 EXP j)) + k,exp_for_dec_enc - j)`)
  [`num_to_chars i 0 k acc = num_to_chars (i DIV (10 EXP
  exp_for_dec_enc))
          exp_for_dec_enc ((i MOD (10 EXP exp_for_dec_enc)) + k)
            acc`;
   `num_to_chars i (SUC j) k acc = (if k < 10 /\ i = 0 then toChar
  k :: acc else num_to_chars i j (k DIV 10) (toChar (k MOD 10) ::
  acc))`];;

let int_to_string_def = cake_define
  `int_to_string neg_char i =
     (if (&0) <= i then implode (num_to_chars (num_of_int i) 0 0
       []) else implode (neg_char :: num_to_chars (num_of_int (abs
       i)) 0 0 []))`;;

let toString_def1 = cake_define
  `mlint_toString i = int_to_string (CHR 126) i`;;
hol4_overload "toString" "mlint_toString";;

let num_to_str_def = cake_define
  `num_to_str (n:num) = toString (&n)`;;

hol4_overload "toString" "num_to_str";;

(* fromString Definitions *)
let fromChar_unsafe_def = cake_define
  `fromChar_unsafe char' = ORD char' - ORD (CHR 48)`;;

let fromChar_def = cake_define
  `fromChar char' =
     (match char' with (CHR 48) -> SOME 0 | (CHR 49) -> SOME 1 |
       (CHR 50) -> SOME 2 | (CHR 51) -> SOME 3 | (CHR 52) -> SOME 4 |
       (CHR 53) -> SOME 5 | (CHR 54) -> SOME 6 | (CHR 55) -> SOME 7 |
       (CHR 56) -> SOME 8 | (CHR 57) -> SOME 9 | _2 -> NONE)`;;

(* Equivalence between the safe and unsafe versions of fromChar *)

let fromChars_range_unsafe_def = cake_define_list
  [`fromChars_range_unsafe l 0 str = 0`;
   `fromChars_range_unsafe l (SUC n) str =
      fromChars_range_unsafe l n str * 10 + fromChar_unsafe
        (strsub str (l + n))`];;

let fromChars_range_def = cake_define_list
  [`fromChars_range l 0 str = SOME 0`;
   `fromChars_range l (SUC n) str =
      (let rest = OPTION_MAP ((*) 10) (fromChars_range l n str) and
          head = fromChar (strsub str (l + n)) in OPTION_MAP2
            (+) rest head)`];;

(* HOL4 mlintScript.sml:188-190: the tactic that proves the
   termination *)
let fromChars_unsafe_def = cake_define_wf
  `MEASURE FST`
  `fromChars_unsafe n str =
      match n with
        0 -> 0
      | n ->
     (if n <= padLen_DEC then fromChars_range_unsafe 0 n str else let
       n' = n - padLen_DEC in let
              front = fromChars_unsafe n' str * maxSmall_DEC in let
              back = fromChars_range_unsafe n' padLen_DEC str in
                front + back)`;;
(* HOL4 mlintScript.sml:191: ML code, not ported *)

(* HOL4 mlintScript.sml:202-204: the tactic that proves the
   termination *)
let fromChars_def = cake_define_wf
  `MEASURE FST`
  `fromChars n str =
      match n with
        0 -> NONE
      | n ->
     (if n <= padLen_DEC then fromChars_range 0 n str else let n' = n
       - padLen_DEC in let
              front = OPTION_MAP ((*) maxSmall_DEC) (fromChars n'
                str) in let
              back = fromChars_range n' padLen_DEC str in
                OPTION_MAP2 (+) front back)`;;
(* HOL4 mlintScript.sml:205: ML code, not ported *)

let fromString_unsafe_def = cake_define
  `fromString_unsafe str =
     (if strlen str = 0 then (&0) else if strsub str 0 = (CHR 126)
       then -- &(fromChars_unsafe (strlen str - 1)
                              (substring str 1 (strlen str - 1)))
                                else &(fromChars_unsafe (strlen str)
                                str))`;;

let fromString_def = cake_define
  `mlint_fromString str =
     (if strlen str = 0 then (NONE:int option) else if strsub str 0 =
       (CHR 126) \/
             strsub str 0 = (CHR 45) then OPTION_MAP ((--) o (&))
              (fromChars (strlen str - 1)
                         (substring str 1 (strlen str - 1))) else if
                           strsub str 0 = (CHR 43) then OPTION_MAP (&)
              (fromChars (strlen str - 1)
                         (substring str 1 (strlen str - 1))) else
                           OPTION_MAP (&) (fromChars (strlen str)
                           str))`;;
hol4_overload "fromString" "mlint_fromString";;

let fromNatString_def = cake_define
  `fromNatString str =
     (match fromString str with
       NONE -> NONE | SOME i -> (if (&0) <= i then SOME
         (num_of_int i) else NONE))`;;

(* fromString auxiliar lemmas *)

(* fromString proofs *)

(* this formulation avoids a comparsion using = for better performance *)
let int_cmp_def = cake_define
  `mlint_int_cmp i (j:int) = (if i < j then LESS else
                       if j < i then GREATER else EQUAL)`;;
hol4_overload "int_cmp" "mlint_int_cmp";;

let num_gcd_def = cake_define
  `mlint_num_gcd a b = (if a = 0 then b else mlint_num_gcd (b MOD a)
  a)`;;

let int_gcd_def = cake_define
  `mlint_int_gcd (m:int) (n:int) = (&(mlint_num_gcd (num_of_int (abs
  m)) (num_of_int (abs n))):int)`;;

(* lemmas *)
