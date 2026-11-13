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
needs "lib/ASCIInumbers.ml";;
needs "lib/ternaryComparisons.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "mlint"
  ["mlstring"];;
(* HOL4 ancestors outside the port: gcd *)

let toChar_def = new_definition
  `toChar digit = (if digit < 10 then CHR (ORD (CHR 48) + digit) else
  CHR ((ORD (CHR 65) + digit) - 10))`;;

let toChar_HEX = prove
 (`d < 16 ==> (toChar d = HEX d)`,
  CHEAT_TAC);;

(* decimal encoding is very slightly faster if we avoid dividing large big-ints
   by 10, and instead divide them by a power of 10 that fits in 28 bits *)
let exp_for_dec_enc_def = new_definition
  `exp_for_dec_enc = 8`;;

(* compatibility with previous version*)
let padLen_DEC_def = new_definition
  `padLen_DEC = exp_for_dec_enc`;;
(* HOL4 mlintScript.sml:31: a theorem that HOL4 states as the value
   of an ML expression: padLen_DEC_eq *)
let maxSmall_DEC_def1 = new_definition
  `maxSmall_DEC = 10 EXP exp_for_dec_enc`;;
(* HOL4 mlintScript.sml:35: a theorem that HOL4 states as the value
   of an ML expression: maxSmall_DEC_def *)

(* HOL4 mlintScript.sml:37-38: the ML values that the definitions
   below antiquote *)

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 mlintScript.sml:45-54: the tactic that proves the termination *)
let num_to_chars_def,num_to_chars_ind = define_wf
  `inv_image (MEASURE I LEX MEASURE I)
       (\(i,j,k,_1). (i * (10 EXP j)) + k,exp_for_dec_enc - j)`
  [`num_to_chars i 0 k acc = num_to_chars (i DIV (10 EXP
  exp_for_dec_enc))
          exp_for_dec_enc ((i MOD (10 EXP exp_for_dec_enc)) + k)
            acc`;
   `num_to_chars i (SUC j) k acc = (if k < 10 /\ i = 0 then toChar
  k :: acc else num_to_chars i j (k DIV 10) (toChar (k MOD 10) ::
  acc))`];;

(* [local] *)
let add_lt_divisible_iff = prove
 (`y MOD n = 0 ==> (x + y < n <=> x < n /\ y = 0)`,
  CHEAT_TAC);;

let num_to_chars_thm = prove
 (`!i j k acc.
     num_to_chars i j k acc =
     num_to_dec_string (k + (i * (10 EXP j))) ++ acc`,
  CHEAT_TAC);;

let int_to_string_def = new_definition
  `int_to_string neg_char i =
     (if (&0:int) <= i then implode (num_to_chars (num_of_int i) 0
       0 []) else implode (neg_char :: num_to_chars (num_of_int (abs
       i)) 0 0 []))`;;

let toString_def1 = new_definition
  `mlint_toString i = int_to_string (CHR 126) i`;;
hol4_overload "toString" "mlint_toString";;

(* HOL4 mlintScript.sml:95: a theorem that HOL4 states as the value
   of an ML expression: toString_def *)

let int_to_string_thm = prove
 (`int_to_string neg_char i =
   implode ((if i < (&0:int) then [neg_char] else []) ++
     num_to_dec_string (num_of_int (abs i)))`,
  CHEAT_TAC);;

let toString_thm = prove
 (`toString i = implode ((if i < (&0:int) then "~" else "") ++
  num_to_dec_string (num_of_int (abs i)))`,
  CHEAT_TAC);;

let num_to_str_def = new_definition
  `num_to_str (n:num) = toString (&n)`;;

hol4_overload "toString" "num_to_str";;

let num_to_str_thm = prove
 (`num_to_str n = implode (num_to_dec_string n)`,
  CHEAT_TAC);;

(* fromString Definitions *)
let fromChar_unsafe_def = new_definition
  `fromChar_unsafe char' = ORD char' - ORD (CHR 48)`;;

let fromChar_def = new_definition
  `fromChar char' =
     (match char' with (CHR 48) -> SOME 0 | (CHR 49) -> SOME 1 |
       (CHR 50) -> SOME 2 | (CHR 51) -> SOME 3 | (CHR 52) -> SOME 4 |
       (CHR 53) -> SOME 5 | (CHR 54) -> SOME 6 | (CHR 55) -> SOME 7 |
       (CHR 56) -> SOME 8 | (CHR 57) -> SOME 9 | _2 -> NONE)`;;

(* Equivalence between the safe and unsafe versions of fromChar *)
let fromChar_eq_unsafe = prove
 (`!char'. isDigit char' ==> fromChar char' = SOME (fromChar_unsafe
  char')`,
  CHEAT_TAC);;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let fromChars_range_unsafe_def,fromChars_range_unsafe_ind = define_wf
  `MEASURE (\(x0,x1,x2). (\n. n) x1)`
  [`fromChars_range_unsafe l 0 str = 0`;
   `fromChars_range_unsafe l (SUC n) str =
      fromChars_range_unsafe l n str * 10 + fromChar_unsafe
        (strsub str (l + n))`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let fromChars_range_def,fromChars_range_ind = define_wf
  `MEASURE (\(x0,x1,x2). (\n. n) x1)`
  [`fromChars_range l 0 str = SOME 0`;
   `fromChars_range l (SUC n) str =
      (let rest = OPTION_MAP ((*) 10) (fromChars_range l n str) and
          head = fromChar (strsub str (l + n)) in OPTION_MAP2
            (+) rest head)`];;

let fromChars_range_eq_unsafe = prove
 (`!str l r. EVERY isDigit str /\ l + r <= STRLEN str ==>
     fromChars_range l r (implode str) =
     SOME (fromChars_range_unsafe l r (implode str))`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 mlintScript.sml:188-190: the tactic that proves the
   termination *)
let fromChars_unsafe_def,fromChars_unsafe_ind = define_wf
  `MEASURE FST`
  [`fromChars_unsafe n str =
      match n with
        0 -> 0
      // Shouldn't happend
      | n ->
     (if n <= padLen_DEC then fromChars_range_unsafe 0 n str else
       let n' = n - padLen_DEC in let
              front = fromChars_unsafe n' str * maxSmall_DEC in let
              back = fromChars_range_unsafe n' padLen_DEC str in
                front + back)`];;
(* HOL4 mlintScript.sml:191: ML code, not ported *)

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 mlintScript.sml:202-204: the tactic that proves the
   termination *)
let fromChars_def,fromChars_ind = define_wf
  `MEASURE FST`
  [`fromChars n str =
      match n with
        0 -> NONE
      // Shouldn't happend
      | n ->
     (if n <= padLen_DEC then fromChars_range 0 n str else let n' =
       n - padLen_DEC in let
              front = OPTION_MAP ((*) maxSmall_DEC) (fromChars n'
                str) in let
              back = fromChars_range n' padLen_DEC str in
                OPTION_MAP2 (+) front back)`];;
(* HOL4 mlintScript.sml:205: ML code, not ported *)

let fromChars_eq_unsafe = prove
 (`!n s. EVERY isDigit (explode s) /\ n <= strlen s /\ n >= 1 ==>
    fromChars n s = SOME (fromChars_unsafe n s)`,
  CHEAT_TAC);;

let fromString_unsafe_def = new_definition
  `fromString_unsafe str =
     (if strlen str = 0 then (&0:int) else if strsub str 0 = (CHR
       126) then --(&(fromChars_unsafe (strlen str - 1)
                              (substring str 1 (strlen str - 1))))
                                else &(fromChars_unsafe (strlen str)
                                str))`;;

let fromString_def = new_definition
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

let fromNatString_def = new_definition
  `fromNatString str =
     (match fromString str with
       NONE -> NONE | SOME i -> (if (&0) <= i then SOME
         (num_of_int i) else NONE))`;;

(* fromString auxiliar lemmas *)
let fromChars_range_unsafe_0_substring_thm = prove
 (`!m r s. r <= m ==>
    fromChars_range_unsafe 0 r s =
      fromChars_range_unsafe 0 r (substring s 0 m)`,
  CHEAT_TAC);;

let fromChars_range_unsafe_split = prove
 (`!m n s.
    ~(m = 0) /\ m < n ==> fromChars_range_unsafe 0 n s =
        10 EXP m * fromChars_range_unsafe 0 (n - m) s +
          fromChars_range_unsafe (n - m) m s`,
  CHEAT_TAC);;

(* fromString proofs *)
let fromChar_unsafe_thm = prove
 (`!h. isDigit h ==> fromChar_unsafe h = num_from_dec_string [h]`,
  CHEAT_TAC);;

let fromChars_range_unsafe_thm = prove
 (`!str. EVERY isDigit str ==>
    fromChars_range_unsafe 0 (STRLEN str) (implode str) =
      num_from_dec_string str`,
  CHEAT_TAC);;

let fromChars_range_unsafe_eq = prove
 (`!n s. n <= (strlen s) ==> fromChars_unsafe n s =
  fromChars_range_unsafe 0 n s`,
  CHEAT_TAC);;

let fromString_unsafe_thm = prove
 (`!str. (~(HD str = (CHR 126)) ==> EVERY isDigit str) /\
         (HD str = (CHR 126) ==> EVERY isDigit (DROP 1 str)) ==>
         fromString_unsafe (implode str) =
           (if HD str = (CHR 126) then --(&(num_from_dec_string
             (DROP 1 str))) else &(num_from_dec_string str))`,
  CHEAT_TAC);;

(* HOL4 mlintScript.sml:355-362: a theorem that HOL4 states as the
   value of an ML expression: fromChars_range_lemma *)

let fromString_thm = prove
 (`!str. ~(str = "") /\
     (~(HD str = (CHR 126)) /\ ~(HD str = (CHR 45)) /\ ~(HD str =
       (CHR 43)) ==> EVERY isDigit str) /\
     (HD str = (CHR 126) \/ HD str = (CHR 45) \/ HD str = (CHR 43)
       ==> EVERY isDigit (DROP 1 str) /\ STRLEN str >= 2) ==>
       fromString (implode str) = SOME
         (if HD str = (CHR 126) \/ HD str = (CHR 45) then
           --(&(num_from_dec_string (DROP 1 str))) else if HD str =
           (CHR 43) then &(num_from_dec_string (DROP 1 str)) else
           &(num_from_dec_string str))`,
  CHEAT_TAC);;

(* HOL4 mlintScript.sml:386-387: a theorem that HOL4 states as the
   value of an ML expression: fromString_eq_unsafe *)

let fromString_toString_Num = prove
 (`(&0) <= n ==> fromString (implode (num_to_dec_string (num_of_int
  n))) = SOME n`,
  CHEAT_TAC);;

(* [local] *)
let fromString_helper = prove
 (`HD (toString (i:num)) = c ==> isDigit c`,
  CHEAT_TAC);;

(* [local] *)
let fromString_hd = prove
 (`HD (toString (i:num)) = c ==> isDigit c`,
  CHEAT_TAC);;

(* [local] *)
let toString_len = prove
 (`STRLEN (toString (i:num)) + 1 >= 2`,
  CHEAT_TAC);;

(* [local] *)
let toString_len_1 = prove
 (`~(HD (toString (i:num)) = (CHR 126)) /\
   ~(HD (toString (i:num)) = (CHR 45)) /\
   ~(HD (toString (i:num)) = (CHR 43))`,
  CHEAT_TAC);;

(* [simp] *)
let fromString_int_to_string = prove
 (`neg_char = (CHR 126) \/ neg_char = (CHR 45) ==>
   fromString (int_to_string neg_char i) = SOME i`,
  CHEAT_TAC);;

(* [simp] *)
let fromString_toString = prove
 (`!(i:int). fromString (toString i) = SOME i`,
  CHEAT_TAC);;

(* [simp] *)
let fromNatString_toString = prove
 (`!(n:num). fromNatString (toString n) = SOME n`,
  CHEAT_TAC);;

let fromChar_IS_SOME_IFF = prove
 (`IS_SOME (fromChar c) <=> isDigit c`,
  CHEAT_TAC);;

let fromChars_range_IS_SOME_IFF = prove
 (`!s x y. (x + y <= strlen s) ==> (IS_SOME (fromChars_range x y s)
  <=> EVERY isDigit (TAKE y (DROP x (explode s))))`,
  CHEAT_TAC);;

let fromChars_IS_SOME_IFF = prove
 (`!n s. n <= strlen s /\ n >= 1 ==> (IS_SOME (fromChars n s) <=>
  EVERY isDigit (TAKE n (explode s)))`,
  CHEAT_TAC);;

let fromString_EQ_NONE = prove
 (`~(isDigit c) /\ ~(c = (CHR 43)) /\ ~(c = (CHR 126)) /\ ~(c = (CHR
  45)) ==>
   fromString (implode (STRING c x)) = NONE`,
  CHEAT_TAC);;

(* this formulation avoids a comparsion using = for better performance *)
let mlint_int_cmp_def = new_definition
  `mlint_int_cmp i (j:int) = (if i < j then LESS else
                       if j < i then GREATER else EQUAL)`;;
hol4_overload "int_cmp" "mlint_int_cmp";;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let num_gcd_def,num_gcd_ind = define_wf
  `MEASURE (\(x0,x1). (\n. n) x0)`
  [`mlint_num_gcd a b = (if a = 0 then b else mlint_num_gcd (b MOD
  a) a)`];;

let num_gcd_eq_gcd = prove
 (`mlint_num_gcd = hol4_gcd`,
  CHEAT_TAC);;

let int_gcd_def = new_definition
  `mlint_int_gcd (m:int) (n:int) = (&(mlint_num_gcd (num_of_int (abs
  m)) (num_of_int (abs n))):int)`;;

(* lemmas *)

let num_to_str_11 = prove
 (`num_to_str n0 = num_to_str n1 <=> n0 = (n1:num)`,
  CHEAT_TAC);;

let num_to_str_not_nil = prove
 (`num_to_str (i:num) = implode s ==> ~(s = "")`,
  CHEAT_TAC);;

(* [local] *)
let ORD_HEX_BOUND1 = prove
 (`i < 10 ==> 48 <= ORD (HEX (i:num))`,
  CHEAT_TAC);;

(* [local] *)
let ORD_HEX_BOUND2 = prove
 (`i < 10 ==> ORD (HEX (i:num)) <= 57`,
  CHEAT_TAC);;

let num_to_str_every = prove
 (`num_to_str (i:num) = implode s ==> EVERY (\x. 48 <= ORD x /\ ORD x
  <= 57) s`,
  CHEAT_TAC);;

let num_to_str_imp_cons = prove
 (`toString (i:num) = implode s ==>
   (?x xs. s = x :: xs /\ 48 <= ORD x /\ ORD x <= 57 /\ EVERY (\x.
     48 <= ORD x /\ ORD x <= 57) xs)`,
  CHEAT_TAC);;

let num_to_str_APPEND_11 = prove
 (`STRCAT s1 (STRING x1 xs1) = STRCAT s2 (STRING x2 xs2) /\
   toString n1 = implode s1 /\
   toString n2 = implode s2 /\
   ~(48 <= ORD x1 /\ ORD x1 <= 57) /\
   ~(48 <= ORD x2 /\ ORD x2 <= 57) ==>
   n1 = n2 /\ x1 :: xs1 = x2 :: xs2`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
