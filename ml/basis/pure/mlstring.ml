(* ======================================================== *)
(*  mlstring: ported from HOL4's
    basis/pure/mlstringScript.sml
    A definition theory, with 49 definitions, 2 datatypes and 113
    theorems.  Needed by 64 files of the port.  *)
(* ======================================================== *)

(*
  Pure functions for the String module.

  Defines mlstring as a separate type from string in HOL's standard library (a
  synonym for char list).
*)

needs "basis/pure/mllist.ml";;
needs "lib/comparison.ml";;
needs "lib/ternaryComparisons.ml";;
needs "misc/misc.ml";;
(* HOL4 ancestors outside the port: toto *)

(* HOL4 mlstringScript.sml:13-14: the ML values that the definitions
   below antiquote *)

(* Defines strings as a separate type from char list. This theory should be
   moved into HOL, either as its own theory, or as an addendum to stringTheory *)

let mlstring_INDUCT,mlstring_RECURSION = define_datatype
  "mlstring = implode (string)";;
(* HOL4 mlstringScript.sml:22: the ML values that the definitions
   below antiquote *)

(* backwards compatibility: strlit used to be the mlstring constructor and
   implode a simple wrapper. *)
(* HOL4 mlstringScript.sml:26: the overload strlit, which the port
   expands *)

let strlen_def = cake_define
  `strlen (implode s) = LENGTH s`;;

let strsub_def = cake_define
  `strsub (implode s) n = EL n s`;;

(* the test here is because underspecification is annoying (and SEG is underspecified) *)
(* the underlying primitive (CopyStrStr) raises an exception if the test is false *)
let substring_def = cake_define
  `substring (implode s) off len = implode (if off + len <= LENGTH s
  then SEG len off s else if off <= LENGTH s then DROP off s else "")`;;

let concat_def = cake_define
  `mlstring_concat l = implode (FLAT (MAP (\s. match s with implode x
  -> x) l))`;;
hol4_overload "concat" "mlstring_concat";;

let concat_nil = cake_theorem "concat_nil[simp]"
  (fun () ->
    `mlstring_concat [] = (implode "")`)
  CHEAT_TAC;;

let explode_aux_def = cake_define_list
  [`explode_aux s n 0 = []`;
   `explode_aux s n (SUC len) =
        strsub s n :: (explode_aux s (n + 1) len)`];;

let explode_aux_thm = cake_theorem "explode_aux_thm"
  (fun () ->
    `!max' n ls.
      (n + max' = LENGTH ls) ==>
      (explode_aux (implode ls) n max' = DROP n ls)`)
  CHEAT_TAC;;

let explode_def = cake_define
  `explode s = explode_aux s 0 (strlen s)`;;

let explode_thm = cake_theorem "explode_thm[simp]"
  (fun () ->
    `explode (implode ls) = ls`)
  CHEAT_TAC;;

let explode_implode = cake_theorem "explode_implode[simp]"
  (fun () ->
    `!x. explode (implode x) = x`)
  CHEAT_TAC;;

let implode_explode = cake_theorem "implode_explode[simp]"
  (fun () ->
    `!x. implode (explode x) = x`)
  CHEAT_TAC;;

let explode_11 = cake_theorem "explode_11[simp]"
  (fun () ->
    `!s1 s2. (explode s1 = explode s2) <=> (s1 = s2)`)
  CHEAT_TAC;;

let implode_BIJ = cake_theorem "implode_BIJ"
  (fun () ->
    `BIJ implode UNIV UNIV`)
  CHEAT_TAC;;

let explode_BIJ = cake_theorem "explode_BIJ"
  (fun () ->
    `BIJ explode UNIV UNIV`)
  CHEAT_TAC;;

let LENGTH_explode = cake_theorem "LENGTH_explode[simp]"
  (fun () ->
    `LENGTH (explode s) = strlen s`)
  CHEAT_TAC;;

let concat_thm = cake_theorem "concat_thm"
  (fun () ->
    `mlstring_concat l = implode (FLAT (MAP explode l))`)
  CHEAT_TAC;;

let strlen_implode = cake_theorem "strlen_implode[simp]"
  (fun () ->
    `strlen (implode s) = LENGTH s`)
  CHEAT_TAC;;

let strlen_substring = cake_theorem "strlen_substring"
  (fun () ->
    `strlen (substring s i j) = (if i + j <= strlen s then j else if i
  <= strlen s then strlen s - i else 0)`)
  CHEAT_TAC;;

let extract_def = cake_define
  `mlstring_extract s i opt =
     (if strlen s <= i then implode [] else match opt with
         SOME x -> substring s i (MIN (strlen s - i) x) | NONE ->
           substring s i (strlen s - i))`;;
hol4_overload "extract" "mlstring_extract";;

let strlen_extract_le = cake_theorem "strlen_extract_le"
  (fun () ->
    `!s x y. strlen (mlstring_extract s x y) <= strlen s - x`)
  CHEAT_TAC;;

let strsub_substring_0_thm = cake_theorem "strsub_substring_0_thm"
  (fun () ->
    `!m n l. m < n ==> strsub (substring l 0 n) m = strsub l m`)
  CHEAT_TAC;;

let substring_full = cake_theorem "substring_full[simp]"
  (fun () ->
    `substring s 0 (strlen s) = s`)
  CHEAT_TAC;;

let substring_too_long = cake_theorem "substring_too_long"
  (fun () ->
    `strlen s <= i ==> substring s i j = (implode "")`)
  CHEAT_TAC;;

let strcat_def = cake_define
  `strcat s1 s2 = mlstring_concat [s1; s2]`;;

let concat_cons = cake_theorem "concat_cons"
  (fun () ->
    `mlstring_concat (h :: t) = strcat h (mlstring_concat t)`)
  CHEAT_TAC;;

let strcat_thm = cake_theorem "strcat_thm"
  (fun () ->
    `strcat s1 s2 = implode (explode s1 ++ explode s2)`)
  CHEAT_TAC;;

let strcat_assoc = cake_theorem "strcat_assoc[simp]"
  (fun () ->
    `!s1 s2 s3. strcat
      s1 (strcat s2 s3) = strcat (strcat s1 s2) s3`)
  CHEAT_TAC;;

let strcat_o = cake_theorem "strcat_o"
  (fun () ->
    `strcat x o strcat y = strcat (strcat x y)`)
  CHEAT_TAC;;

let strcat_nil = cake_theorem "strcat_nil[simp]"
  (fun () ->
    `(strcat (implode "") s = s) /\
     (strcat s (implode "") = s)`)
  CHEAT_TAC;;

let mlstring_common_prefix = cake_theorem "mlstring_common_prefix[simp]"
  (fun () ->
    `!s t1 t2. strcat s t1 = strcat s t2 <=> t1 = t2`)
  CHEAT_TAC;;

let mlstring_common_char_prefix =
  cake_theorem "mlstring_common_char_prefix[simp]"
  (fun () ->
    `!c1 s1 s2 t2 t2. (strcat (implode (c1 :: s1)) t1) = (strcat
  (implode (c2 :: s2)) t2) <=>
       c1 = c2 /\ strcat (implode s1) t1 = strcat (implode s2) t2`)
  CHEAT_TAC;;

let mlstring_common_suffix = cake_theorem "mlstring_common_suffix[simp]"
  (fun () ->
    `!s t1 t2. strcat t1 s = strcat t2 s <=> t1 = t2`)
  CHEAT_TAC;;

let concat_append = cake_theorem "concat_append"
  (fun () ->
    `mlstring_concat (xs ++ ys) = strcat (mlstring_concat xs)
  (mlstring_concat ys)`)
  CHEAT_TAC;;

let implode_STRCAT = cake_theorem "implode_STRCAT"
  (fun () ->
    `!l1 l2.
      implode (STRCAT l1 l2) = strcat (implode l1) (implode l2)`)
  CHEAT_TAC;;

let explode_strcat = cake_theorem "explode_strcat[simp]"
  (fun () ->
    `explode (strcat s1 s2) = explode s1 ++ explode s2`)
  CHEAT_TAC;;

let strlen_strcat = cake_theorem "strlen_strcat[simp]"
  (fun () ->
    `strlen (strcat s1 s2) = strlen s1 + strlen s2`)
  CHEAT_TAC;;

let concatWith_def = cake_define
  `concatWith s l = mlstring_concat (intersperse s l)`;;

let chr_to_str_def = cake_define
  `chr_to_str (c:char) = implode [c]`;;

hol4_overload "toString" "chr_to_str";;

let explode_toString = cake_theorem "explode_toString[simp]"
  (fun () ->
    `explode (toString c) = [c]`)
  CHEAT_TAC;;

let strlen_toString = cake_theorem "strlen_toString[simp]"
  (fun () ->
    `strlen (toString c) = 1`)
  CHEAT_TAC;;

let translate_aux_def = cake_define_list
  [`translate_aux f s n 0 = []`;
   `translate_aux f s n (SUC len) = f (strsub s n) :: translate_aux
  f s (n + 1) len`];;

let translate_def = cake_define
  `translate f s = implode (translate_aux f s 0 (strlen s))`;;

let translate_aux_thm = cake_theorem "translate_aux_thm[local]"
  (fun () ->
    `!f s n len. (n + len = strlen s) ==> (translate_aux f s n len =
  MAP f (DROP n (explode s)))`)
  CHEAT_TAC;;

let translate_thm = cake_theorem "translate_thm"
  (fun () ->
    `!f s. translate f s = implode (MAP f (explode s))`)
  CHEAT_TAC;;

let splitl_aux_def = cake_define_wf
  `inv_image (<) (\(x,s,i). strlen s - i)`
  `splitl_aux P s i =
     (if i < strlen s /\ P (strsub s i) then
         splitl_aux P s (i + 1) else (mlstring_extract s 0 (SOME
           i),mlstring_extract s i NONE))`;;

(* HOL4 mlstringScript.sml:316: ML code, not ported *)

let splitl_def = cake_define
  `splitl P s = splitl_aux P s 0`;;

let splitl_aux_SPLITP = cake_theorem "splitl_aux_SPLITP"
  (fun () ->
    `!P s i.
      splitl_aux P s i =
      (implode o ((++) (TAKE i (explode s))) ## implode)
        (SPLITP ((~) o P) (DROP i (explode s)))`)
  CHEAT_TAC;;

let splitl_SPLITL = cake_theorem "splitl_SPLITL"
  (fun () ->
    `splitl P s = (implode ## implode) (SPLITL P (explode s))`)
  CHEAT_TAC;;

let tokens_aux_def = cake_define_list
  [`tokens_aux f s [] n 0 = []`;
   `tokens_aux f s (h :: t) n 0 = [implode (REVERSE (h :: t))]`;
   `tokens_aux f s [] n (SUC len) =
        (if f (strsub s n) then tokens_aux f s [] (n + 1) len
          else tokens_aux f s [strsub s n] (n + 1) len)`;
   `tokens_aux f s (h :: t) n (SUC len) =
        (if f (strsub s n) then (implode (REVERSE (h :: t))) ::
          (tokens_aux f s [] (n + 1) len) else tokens_aux f s
          (strsub s n :: (h :: t)) (n + 1) len)`];;

(* HOL4 mlstringScript.sml:384: ML code, not ported *)

let tokens_def = cake_define
  `tokens f s = tokens_aux f s [] 0 (strlen s)`;;


let tokens_aux_filter = cake_theorem "tokens_aux_filter[local]"
  (fun () ->
    `!f s ss n len. (n + len = strlen s) ==> (mlstring_concat
  (tokens_aux f s ss n len) =
         implode (REVERSE ss ++ FILTER ((~) o f) (DROP n (explode
           s))))`)
  CHEAT_TAC;;

let tokens_filter = cake_theorem "tokens_filter"
  (fun () ->
    `!f s. mlstring_concat (tokens f s) = implode (FILTER ((~) o f)
  (explode s))`)
  CHEAT_TAC;;

let TOKENS_eq_tokens_aux = cake_theorem "TOKENS_eq_tokens_aux"
  (fun () ->
    `!P ls ss n len. (n + len = LENGTH (explode ls)) ==>
        (MAP explode (tokens_aux P ls ss n len) = (match ss with (h
          :: t) -> (if (~(len = 0)) /\ ((~) (P (EL n (explode ls))))
          then
            (REVERSE (h :: t) ++ HD (TOKENS P (DROP n (explode
              ls)))) :: TL (TOKENS P (DROP n (explode ls))) else if
              (~(len = 0)) then
                REVERSE (h :: t) :: (TOKENS P (DROP n (explode
                  ls))) else [REVERSE (h :: t)]) | [] -> (TOKENS P
                  (DROP n (explode ls)))))`)
  CHEAT_TAC;;
(* HOL4 mlstringScript.sml:462-470: code that the source has in a
   comment *)


let TOKENS_eq_tokens = cake_theorem "TOKENS_eq_tokens"
  (fun () ->
    `!P ls. (MAP explode' (tokens P ls) = TOKENS P (explode' ls))`)
  CHEAT_TAC;;

(* HOL4 mlstringScript.sml:479-485: code that the source has in a
   comment *)

(* HOL4 mlstringScript.sml:487-491: a theorem that HOL4 states as the
   value of an ML expression *)


let tokens_append = cake_theorem "tokens_append"
  (fun () ->
    `!P s1 x s2.
      P x ==>
        (tokens P (strcat (strcat s1 (toString x)) s2) = tokens P
          s1 ++ tokens P s2)`)
  CHEAT_TAC;;

(* HOL4 mlstringScript.sml:520-522: the tactic that proves the
   termination *)
let tokens_alt_aux_def = cake_define_wf
  `MEASURE (\(f,s,i,j,n). n - j)`
  `(tokens_alt_aux f s i j n =
   (if j < n then
     (if f (strsub s j) then
       (if i = j then tokens_alt_aux f s (i + 1) (j + 1) n else
         substring s i (j - i) ::
         (tokens_alt_aux f s (j + 1) (j + 1) n)) else
       tokens_alt_aux f s i (j + 1) n) else
     if i = j then [] else [substring s i (j - i)]))`;;

let substring_1_strsub = cake_theorem "substring_1_strsub"
  (fun () ->
    `i < strlen s ==>
     substring s i 1 = toString (strsub s i)`)
  CHEAT_TAC;;

let substring_0 = cake_theorem "substring_0[simp]"
  (fun () ->
    `substring s i 0 = (implode "")`)
  CHEAT_TAC;;

let substring_add = cake_theorem "substring_add"
  (fun () ->
    `i + x + y <= strlen s ==>
     substring s i (x + y) = strcat
     (substring s i x) (substring s (i + x) y)`)
  CHEAT_TAC;;

let tokens_alt_tokens_alt_aux = cake_theorem "tokens_alt_tokens_alt_aux"
  (fun () ->
    `!f s acc j l i.
     i <= j /\ j <= strlen s /\
     strlen s - j = l /\
     acc = REVERSE (explode (substring s i (j - i))) ==>
     tokens_aux f s acc j l =
     tokens_alt_aux f s i j (strlen s)`)
  CHEAT_TAC;;

let tokens_alt = cake_theorem "tokens_alt"
  (fun () ->
    `tokens f s =
     tokens_alt_aux f s 0 0 (strlen s)`)
  CHEAT_TAC;;

let fields_aux_def = cake_define_list
  [`fields_aux f s ss n 0 = [implode (REVERSE ss)]`;
   `fields_aux f s ss n (SUC len) =
        (if f (strsub s n) then implode (REVERSE ss) ::
          (fields_aux f s [] (n + 1) len) else fields_aux f s
          (strsub s n :: ss) (n + 1) len)`];;


let fields_def = cake_define
  `fields f s = fields_aux f s [] 0 (strlen s)`;;


let fields_aux_filter = cake_theorem "fields_aux_filter[local]"
  (fun () ->
    `!f s ss n len. (n + len = strlen s) ==> (mlstring_concat
  (fields_aux f s ss n len) =
         implode (REVERSE ss ++ FILTER ((~) o f) (DROP n (explode
           s))))`)
  CHEAT_TAC;;

let fields_filter = cake_theorem "fields_filter"
  (fun () ->
    `!f s. mlstring_concat (fields f s) = implode (FILTER ((~) o f)
  (explode s))`)
  CHEAT_TAC;;

let fields_aux_length = cake_theorem "fields_aux_length[local]"
  (fun () ->
    `!f s ss n len. (n + len = strlen s) ==>
       (LENGTH (fields_aux f s ss n len) = LENGTH (FILTER f (DROP
         n (explode s))) + 1)`)
  CHEAT_TAC;;


let fields_length = cake_theorem "fields_length"
  (fun () ->
    `!f s. LENGTH (fields f s) = (LENGTH (FILTER f (explode s)) + 1)`)
  CHEAT_TAC;;

(* HOL4 mlstringScript.sml:677-679: the tactic that proves the
   termination *)
let fields_alt_aux_def = cake_define_wf
  `MEASURE (\(f,s,i,j,n). n - j)`
  `(fields_alt_aux f s i j n =
   (if j < n then
     (if f (strsub s j) then
         substring s i (j - i) ::
         (fields_alt_aux f s (j + 1) (j + 1) n) else
       fields_alt_aux f s i (j + 1) n) else
     [substring s i (j - i)]))`;;

let fields_alt_fields_alt_aux = cake_theorem "fields_alt_fields_alt_aux"
  (fun () ->
    `!l acc j i.
     i <= j /\ j <= strlen s /\
     strlen s - j = l /\
     acc = REVERSE (explode (substring s i (j - i))) ==>
     fields_aux f s acc j l =
     fields_alt_aux f s i j (strlen s)`)
  CHEAT_TAC;;

let fields_alt = cake_theorem "fields_alt"
  (fun () ->
    `fields f s =
     fields_alt_aux f s 0 0 (strlen s)`)
  CHEAT_TAC;;


let str_findi_def = cake_define_wf
  `MEASURE (\(P,i,s). strlen s - i)`
  `str_findi P i s = (if i < strlen s then if P (strsub s i) then
  SOME i else str_findi P (i + 1) s else NONE)`;;

let str_findi_range = cake_theorem "str_findi_range"
  (fun () ->
    `!P i s. str_findi P i s = SOME j ==> i <= j /\ j < strlen s`)
  CHEAT_TAC;;

let OLEAST_LE_STEP = cake_theorem "OLEAST_LE_STEP"
  (fun () ->
    `(OLEAST (\j. i <= j /\ P j)) = (if P i then SOME i else (OLEAST
  (\j. i + 1 <= j /\ P j)))`)
  CHEAT_TAC;;

let str_findi_OLEAST = cake_theorem "str_findi_OLEAST"
  (fun () ->
    `!P i s. str_findi P i s = (OLEAST (\j. i <= j /\ j < strlen s /\
  P (strsub s j)))`)
  CHEAT_TAC;;

let isStringThere_aux_def = cake_define_list
  [`isStringThere_aux s1 s2 s1i s2i 0 = T`;
   `isStringThere_aux s1 s2 s1i s2i (SUC len) =
        (if strsub s1 s1i = strsub s2 s2i then
          isStringThere_aux s1 s2 (s1i + 1) (s2i + 1) len else F)`];;


(* HOL4 mlstringScript.sml:771-781: code that the source has in a
   comment *)

let isPrefix_def = cake_define
  `isPrefix s1 s2 =
     (if strlen s1 <= strlen s2 then isStringThere_aux s1 s2 0 0
       (strlen s1) else F)`;;

let exists_mlstring = cake_theorem "exists_mlstring"
  (fun () ->
    `(?(x:mlstring). P x) <=> (?s. P (implode s))`)
  CHEAT_TAC;;

let isprefix_thm_aux = cake_theorem "isprefix_thm_aux[local]"
  (fun () ->
    `!ys xs zs.
       LENGTH ys <= LENGTH zs ==>
       (isStringThere_aux (implode (xs ++ ys)) (implode (xs ++ zs))
          (LENGTH xs) (LENGTH xs) (LENGTH ys) <=>
          ys <<= zs)`)
  CHEAT_TAC;;

let isprefix_thm = cake_theorem "isprefix_thm"
  (fun () ->
    `isPrefix s₁ s₂ <=> explode s₁ <<= explode s₂`)
  CHEAT_TAC;;

let isprefix_strcat = cake_theorem "isprefix_strcat"
  (fun () ->
    `!s₁ s₂. isPrefix s₁ s₂ = (?s₃. s₂ = strcat s₁ s₃)`)
  CHEAT_TAC;;

let isSuffix_def = cake_define
  `isSuffix s1 s2 =
     (if strlen s1 <= strlen s2 then isStringThere_aux s1 s2 0
       (strlen s2 - strlen s1) (strlen s1) else F)`;;

let isSubstring_aux_def = cake_define_list
  [`isSubstring_aux s1 s2 lens1 n 0 = F`;
   `isSubstring_aux s1 s2 lens1 n (SUC len) =
        (if (isStringThere_aux s1 s2 0 n lens1) then T else
          isSubstring_aux s1 s2 lens1 (n + 1) len)`];;

let isSubstring_def = cake_define
  `isSubstring s1 s2 =
   (if strlen s1 <= strlen s2 then isSubstring_aux s1 s2 (strlen
     s1) 0 ((strlen s2) - (strlen s1) + 1) else F)`;;

(* proof that isSubstring has the right sort of properties *)
let isStringThere_SEG = cake_theorem "isStringThere_SEG"
  (fun () ->
    `!i1 i2.
       i1 + n <= LENGTH s1 /\ i2 + n <= LENGTH s2 ==>
       (isStringThere_aux (implode s1) (implode s2) i1 i2 n <=>
         (SEG n i1 s1 = SEG n i2 s2))`)
  CHEAT_TAC;;

let isSubstring_aux_lemma = cake_theorem "isSubstring_aux_lemma"
  (fun () ->
    `!i len.
       i + len <= strlen s2 ==>
       (isSubstring_aux s1 s2 lens1 i len <=>
        (?n. n < len /\ isStringThere_aux s1 s2 0 (n + i) lens1))`)
  CHEAT_TAC;;

let isSubstring_SEG = cake_theorem "isSubstring_SEG"
  (fun () ->
    `isSubstring (implode s1) (implode s2) <=>
     (?i. i + LENGTH s1 <= LENGTH s2 /\ SEG (LENGTH s1) i s2 =
       s1)`)
  CHEAT_TAC;;

let strlit_STRCAT = cake_theorem "strlit_STRCAT"
  (fun () ->
    `strcat
        (implode a) (implode b) = implode (a ++ b)`)
  CHEAT_TAC;;

let isSubString_spec = cake_theorem "isSubString_spec"
  (fun () ->
    `isSubstring s1 s2 <=> (?p s. s2 = strcat (strcat p s1) s)`)
  CHEAT_TAC;;

(* String orderings *)
let compare_aux_def = cake_define
  `compare_aux (s1:mlstring) s2 ord start' len =
     (if len = 0 then
       ord else if strsub s2 start' < strsub s1 start' then
         GREATER else if strsub s1 start' < strsub s2 start' then
         LESS else compare_aux s1 s2 ord (start' + 1) (len - 1))`;;

let compare_def = cake_define
  `mlstring_compare s1 s2 = (if (strlen s1) < (strlen s2) then
  compare_aux s1 s2 LESS 0 (strlen s1) else if (strlen s2) < (strlen
  s1) then compare_aux s1 s2 GREATER 0 (strlen s2) else compare_aux
  s1 s2 EQUAL 0 (strlen s2))`;;
hol4_overload "compare" "mlstring_compare";;

let mlstring_lt_def = cake_define
  `mlstring_lt s1 s2 <=> (mlstring_compare s1 s2 = LESS)`;;

let mlstring_le_def = cake_define
  `mlstring_le s1 s2 <=> (~(mlstring_compare s1 s2 = GREATER))`;;

let mlstring_gt_def = cake_define
  `mlstring_gt s1 s2 <=> (mlstring_compare s1 s2 = GREATER)`;;

let mlstring_ge_def = cake_define
  `mlstring_ge s1 s2 <=> (~(mlstring_compare s1 s2 = LESS))`;;

let compare_thm = cake_theorem "compare_thm"
  (fun () ->
    `mlstring_compare s1 s2 =
       (if mlstring_lt s1 s2 then LESS else
       if mlstring_le s1 s2 then EQUAL else GREATER)`)
  CHEAT_TAC;;

hol4_overload "<" "mlstring_lt";;
hol4_overload "<=" "mlstring_le";;
hol4_overload ">" "mlstring_gt";;
hol4_overload ">=" "mlstring_ge";;

let fast_lt_def = cake_define
  `fast_lt s1 s2 =
     (if strlen s1 = strlen s2 then mlstring_lt s1 s2 else strlen
       s1 < strlen s2)`;;

let fast_le_def = cake_define
  `fast_le s1 s2 =
     (if strlen s1 = strlen s2 then mlstring_le s1 s2 else strlen
       s1 <= strlen s2)`;;

let fast_gt_def = cake_define
  `fast_gt s1 s2 =
     (if strlen s1 = strlen s2 then mlstring_gt s1 s2 else strlen
       s1 > strlen s2)`;;

let fast_ge_def = cake_define
  `fast_ge s1 s2 =
     (if strlen s1 = strlen s2 then mlstring_ge s1 s2 else strlen
       s1 >= strlen s2)`;;

(* Properties of string orderings *)

(* HOL4 mlstringScript.sml:991: ML code, not ported *)
(* HOL4 mlstringScript.sml:992: the overload flip_ord, which the port
   expands *)

let compare_aux_spec = cake_theorem "compare_aux_spec[local]"
  (fun () ->
    `!s1 s2 ord_in start' len.
       len + start' <= strlen s1 /\ len + start' <= strlen s2 ==>
       (compare_aux s1 s2 ord_in start' len =
         (if TAKE len (DROP start' (explode s1)) = TAKE len (DROP
           start' (explode s2)) then
           ord_in else if string_lt (TAKE len (DROP start' (explode
             s1))) (TAKE len (DROP start' (explode s2))) then
           LESS else
           GREATER))`)
  CHEAT_TAC;;

let compare_aux_refl = cake_theorem "compare_aux_refl[local]"
  (fun () ->
    `!s1 s2 start' len.
       start' + len <= strlen s1 /\ start' + len <= strlen s2 ==>
       (
        (compare_aux s1 s2 EQUAL start' len = EQUAL) <=>
        (TAKE len (DROP start' (explode s1)) = TAKE len (DROP
          start' (explode s2))))`)
  CHEAT_TAC;;

let compare_aux_equal = cake_theorem "compare_aux_equal[local]"
  (fun () ->
    `!s1 s2 ord_in start' len.
       (compare_aux s1 s2 ord_in start' len = EQUAL) ==> (ord_in
         = EQUAL)`)
  CHEAT_TAC;;

let compare_aux_sym = cake_theorem "compare_aux_sym[local]"
  (fun () ->
    `!s1 s2 ord_in start' len ord_out.
       (compare_aux s1 s2 ord_in start' len = ord_out) <=>
       (compare_aux s2 s1 (invert_comparison ord_in) start' len =
         invert_comparison ord_out)`)
  CHEAT_TAC;;

let string_lt_take_mono = cake_theorem "string_lt_take_mono[local]"
  (fun () ->
    `!s1 s2 x.
       s1 < s2 ==> TAKE x s1 < TAKE x s2 \/ (TAKE x s1 = TAKE x
         s2)`)
  CHEAT_TAC;;

let string_lt_remove_take = cake_theorem "string_lt_remove_take[local]"
  (fun () ->
    `!s1 s2 x. TAKE x s1 < TAKE x s2 ==> s1 < s2`)
  CHEAT_TAC;;

let string_prefix_le = cake_theorem "string_prefix_le[local]"
  (fun () ->
    `!s1 s2. s1 <<= s2 ==> s1 <= s2`)
  CHEAT_TAC;;

let take_prefix = cake_theorem "take_prefix[local]"
  (fun () ->
    `!l s. TAKE l s <<= s`)
  CHEAT_TAC;;

let mlstring_lt_inv_image = cake_theorem "mlstring_lt_inv_image"
  (fun () ->
    `mlstring_lt = inv_image string_lt explode`)
  CHEAT_TAC;;

let TotOrd_compare = cake_theorem "TotOrd_compare"
  (fun () ->
    `TotOrd mlstring_compare`)
  CHEAT_TAC;;

let good_cmp_compare = cake_theorem "good_cmp_compare"
  (fun () ->
    `good_cmp mlstring_compare`)
  CHEAT_TAC;;

let mlstring_lt_antisym = cake_theorem "mlstring_lt_antisym"
  (fun () ->
    `!s t. ~(s < t /\ t < s)`)
  CHEAT_TAC;;

let mlstring_lt_cases = cake_theorem "mlstring_lt_cases"
  (fun () ->
    `!s t. (s = t) \/ s < t \/ t < s`)
  CHEAT_TAC;;

let mlstring_lt_nonrefl = cake_theorem "mlstring_lt_nonrefl"
  (fun () ->
    `!s. ~(s < s)`)
  CHEAT_TAC;;

let mlstring_lt_trans = cake_theorem "mlstring_lt_trans"
  (fun () ->
    `!s1 s2 s3. s1 < s2 /\ s2 < s3 ==> s1 < s3`)
  CHEAT_TAC;;

let mlstring_le_thm = cake_theorem "mlstring_le_thm"
  (fun () ->
    `!s1 s2. s1 <= s2 <=> (s1 = s2) \/ s1 < s2`)
  CHEAT_TAC;;

let mlstring_gt_thm = cake_theorem "mlstring_gt_thm"
  (fun () ->
    `!s1 s2. s1 > s2 <=> s2 < s1`)
  CHEAT_TAC;;

let mlstring_ge_thm = cake_theorem "mlstring_ge_thm"
  (fun () ->
    `!s1 s2. s1 >= s2 <=> s2 <= s1`)
  CHEAT_TAC;;

let transitive_mlstring_le = cake_theorem "transitive_mlstring_le"
  (fun () ->
    `transitive mlstring_le`)
  CHEAT_TAC;;

let antisymmetric_mlstring_le = cake_theorem "antisymmetric_mlstring_le"
  (fun () ->
    `antisymmetric mlstring_le`)
  CHEAT_TAC;;

let char_lt_total = cake_theorem "char_lt_total"
  (fun () ->
    `!(c1:char) c2. ~(c1 < c2) /\ ~(c2 < c1) ==> c1 = c2`)
  CHEAT_TAC;;

let string_lt_total = cake_theorem "string_lt_total"
  (fun () ->
    `!(s1:string) s2. ~(s1 < s2) /\ ~(s2 < s1) ==> s1 = s2`)
  CHEAT_TAC;;

let total_mlstring_le = cake_theorem "total_mlstring_le"
  (fun () ->
    `total mlstring_le`)
  CHEAT_TAC;;

let transitive_mlstring_lt =
  cake_theorem "transitive_mlstring_lt[local]"
  (fun () ->
    `transitive mlstring_lt`)
  CHEAT_TAC;;

let strlit_le_strlit = cake_theorem "strlit_le_strlit"
  (fun () ->
    `implode s1 <= implode s2 <=> s1 <= s2`)
  CHEAT_TAC;;

let irreflexive_mlstring_lt =
  cake_theorem "irreflexive_mlstring_lt[local]"
  (fun () ->
    `irreflexive mlstring_lt`)
  CHEAT_TAC;;

let trichotomous_mlstring_lt =
  cake_theorem "trichotomous_mlstring_lt[local]"
  (fun () ->
    `trichotomous mlstring_lt`)
  CHEAT_TAC;;

let StrongLinearOrder_mlstring_lt =
  cake_theorem "StrongLinearOrder_mlstring_lt"
  (fun () ->
    `StrongLinearOrder mlstring_lt`)
  CHEAT_TAC;;

let fast_lt_nonrefl = cake_theorem "fast_lt_nonrefl"
  (fun () ->
    `!s. ~fast_lt s s`)
  CHEAT_TAC;;

let fast_lt_trans = cake_theorem "fast_lt_trans"
  (fun () ->
    `!s1 s2 s3. fast_lt s1 s2 /\ fast_lt s2 s3 ==> fast_lt s1 s3`)
  CHEAT_TAC;;

let fast_le_thm = cake_theorem "fast_le_thm"
  (fun () ->
    `!s1 s2. fast_le s1 s2 <=> s1 = s2 \/ fast_lt s1 s2`)
  CHEAT_TAC;;

let fast_gt_thm = cake_theorem "fast_gt_thm"
  (fun () ->
    `!s1 s2. fast_gt s1 s2 <=> fast_lt s2 s1`)
  CHEAT_TAC;;

let fast_ge_thm = cake_theorem "fast_ge_thm"
  (fun () ->
    `!s1 s2. fast_ge s1 s2 <=> fast_le s2 s1`)
  CHEAT_TAC;;

let transitive_fast_le = cake_theorem "transitive_fast_le"
  (fun () ->
    `transitive fast_le`)
  CHEAT_TAC;;

let antisymmetric_fast_le = cake_theorem "antisymmetric_fast_le"
  (fun () ->
    `antisymmetric fast_le`)
  CHEAT_TAC;;

let total_fast_le = cake_theorem "total_fast_le"
  (fun () ->
    `total fast_le`)
  CHEAT_TAC;;

let transitive_fast_lt = cake_theorem "transitive_fast_lt"
  (fun () ->
    `transitive fast_lt`)
  CHEAT_TAC;;

let irreflexive_fast_lt = cake_theorem "irreflexive_fast_lt"
  (fun () ->
    `irreflexive fast_lt`)
  CHEAT_TAC;;

let trichotomous_fast_lt = cake_theorem "trichotomous_fast_lt"
  (fun () ->
    `trichotomous fast_lt`)
  CHEAT_TAC;;

let StrongLinearOrder_fast_lt = cake_theorem "StrongLinearOrder_fast_lt"
  (fun () ->
    `StrongLinearOrder fast_lt`)
  CHEAT_TAC;;

let collate_aux_def = cake_define_list
  [`mlstring_collate_aux f (s1:mlstring) s2 ord n 0 = ord`;
   `mlstring_collate_aux f (s1:mlstring) s2 ord n (SUC len) =
        (if f (strsub s1 n) (strsub s2 n) = EQUAL then
          mlstring_collate_aux f s1 s2 ord (n + 1) len else f
          (strsub s1 n) (strsub s2 n))`];;
hol4_overload "collate_aux" "mlstring_collate_aux";;

let collate_def = cake_define
  `mlstring_collate f s1 s2 =
   (if (strlen s1) < (strlen s2) then mlstring_collate_aux f s1 s2
     LESS 0 (strlen s1) else if (strlen s2) < (strlen s1) then
     mlstring_collate_aux f s1 s2 GREATER 0 (strlen s2) else
     mlstring_collate_aux f s1 s2 EQUAL 0 (strlen s2))`;;
hol4_overload "collate" "mlstring_collate";;


let collate_aux_less_thm = cake_theorem "collate_aux_less_thm[local]"
  (fun () ->
    `!f s1 s2 n len.
       n + len = strlen s1 /\ strlen s1 < strlen s2 ==>
       mlstring_collate_aux f s1 s2 LESS n len =
       mllist_collate f (DROP n (explode s1)) (DROP n (explode
         s2))`)
  CHEAT_TAC;;

let collate_aux_equal_thm = cake_theorem "collate_aux_equal_thm[local]"
  (fun () ->
    `!f s1 s2 n len.
       n + len = strlen s2 /\ strlen s1 = strlen s2 ==>
       mlstring_collate_aux f s1 s2 EQUAL n len =
       mllist_collate f (DROP n (explode s1)) (DROP n (explode
         s2))`)
  CHEAT_TAC;;

let collate_aux_greater_thm =
  cake_theorem "collate_aux_greater_thm[local]"
  (fun () ->
    `!f s1 s2 n len.
       n + len = strlen s2 /\ strlen s2 < strlen s1 ==>
       mlstring_collate_aux f s1 s2 GREATER n len =
       mllist_collate f (DROP n (explode s1)) (DROP n (explode
         s2))`)
  CHEAT_TAC;;

let collate_thm = cake_theorem "collate_thm"
  (fun () ->
    `!f s1 s2. collate f s1 s2 = mllist_collate f (explode s1)
  (explode s2)`)
  CHEAT_TAC;;

let char_escape_seq_def = cake_define
  `char_escape_seq c =
     (if c = (CHR 9) then SOME (implode "\\t") else if c = (CHR
       10) then SOME (implode "\\n") else if c = (CHR 92) then SOME
       (implode "\\\\") else if c = (CHR 34) then SOME (implode
       "\\\"") else NONE)`;;

let char_escaped_def = cake_define
  `char_escaped c = (match char_escape_seq c with
     NONE -> [c] | SOME s -> explode s)`;;

let escape_str_def = cake_define
  `escape_str s = implode ("\"" ++ FLAT (MAP char_escaped (explode
  s)) ++ "\"")`;;

let escape_char_def = cake_define
  `escape_char c = implode ("#\"" ++ char_escaped c ++ "\"")`;;

let ALL_DISTINCT_MAP_implode =
  cake_theorem "ALL_DISTINCT_MAP_implode[simp]"
  (fun () ->
    `ALL_DISTINCT ls ==> ALL_DISTINCT (MAP implode ls)`)
  CHEAT_TAC;;

let ALL_DISTINCT_MAP_explode =
  cake_theorem "ALL_DISTINCT_MAP_explode[simp]"
  (fun () ->
    `!ls. ALL_DISTINCT (MAP explode' ls) <=> ALL_DISTINCT ls`)
  CHEAT_TAC;;

(* optimising mlstring app_list *)

let app_list_ann_INDUCT,app_list_ann_RECURSION = define_datatype
  "app_list_ann = BigList ('a list) | BigAppend (app_list_ann) \
   (app_list_ann) | Small ('a app_list)";;

let sum_sizes_def = cake_define_list
  [`sum_sizes [] k = k`;
   `sum_sizes (l :: ls) k = sum_sizes ls (strlen l + k)`];;

(* HOL4 mlstringScript.sml:1502: the overload size_limit, which the
   port expands *)

let make_app_list_ann_def = cake_define
  `make_app_list_ann input =
     (match input with misc_Nil -> (Small input,0) | misc_Append l1
       l2 ->
         (let (x1,n1) = make_app_list_ann l1 in
          let (x2,n2) = make_app_list_ann l2 in
          let n = n1 + n2 in
            if n < (2048:num) then
              (Small input,n) else
              (BigAppend x1 x2,n)) | misc_List ls ->
         (let n = sum_sizes ls 0 in
            if n < (2048:num) then
              (Small input,n) else (BigList ls,n)))`;;

let shrink_def = cake_define_list
  [`shrink (Small t) = misc_List [mlstring_concat (append t)]`;
   `shrink (BigList ls) = misc_List ls`;
   `shrink (BigAppend l1 l2) = misc_Append (shrink l1) (shrink l2)`];;

let str_app_list_opt_def = cake_define
  `str_app_list_opt l =
     (let (t,n) = make_app_list_ann l in
       shrink t)`;;

let str_app_list_opt_test = cake_theorem "str_app_list_opt_test[local]"
  (fun () ->
    `str_app_list_opt (misc_Append (misc_List [(implode "Hello");
  (implode " there")])
                              (misc_List [(implode "!")])) =
     misc_List [(implode "Hello there!")]`)
  CHEAT_TAC;;

let str_app_list_opt_thm = cake_theorem "str_app_list_opt_thm"
  (fun () ->
    `mlstring_concat (append (str_app_list_opt l)) = mlstring_concat
  (append l)`)
  CHEAT_TAC;;

let concat_sing = cake_theorem "concat_sing[simp]"
  (fun () ->
    `mlstring_concat [x] = x`)
  CHEAT_TAC;;

let char_to_word8_def = cake_define
  `char_to_word8 (c:char) = (n2w (ORD c):word8)`;;

let word8_to_char_def = cake_define
  `word8_to_char (w:word8) = (CHR (w2n w):char)`;;

(* The translator turns each `empty_ffi s` into a call to the FFI with
   an empty name and passing `s` as the argument. The empty FFI is
   used for logging/timing purposes. *)
let empty_ffi_def = cake_define
  `empty_ffi (s:mlstring) = one`;;
