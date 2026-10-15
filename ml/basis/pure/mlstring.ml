(* ======================================================== *)
(*  mlstring: ported from HOL4's
    basis/pure/mlstringScript.sml  *)
(* ======================================================== *)

(*
  Pure functions for the String module.

  Defines mlstring as a separate type from string in HOL's standard
    library (a
  synonym for char list).
*)

needs "basis/pure/mllist.ml";;
needs "lib/ternaryComparisons.ml";;
needs "misc/misc.ml";;
(* HOL4 ancestors outside the port: toto *)

(* HOL4 ML code, not ported:
val cpn_distinct = TypeBase.distinct_of ``:ordering``
val cpn_nchotomy = TypeBase.nchotomy_of ``:ordering``
*)

(* Defines strings as a separate type from char list. This theory should
   be
   moved into HOL, either as its own theory, or as an addendum to
     stringTheory *)

let mlstring_INDUCT,mlstring_RECURSION = define_datatype
  "mlstring = implode (string)";;
(* HOL4 ML code, not ported:
val _ = add_strliteral_form{inj=“implode”, ldelim = "«"};
*)

(* backwards compatibility: strlit used to be the mlstring constructor
   and
   implode a simple wrapper. *)
(* HOL4 overload (expanded in the port):
     strlit = implode *)

let strlen_def = cake_define
  `strlen ((implode) s) = LENGTH s`;;

let strsub_def = cake_define
  `strsub ((implode) s) n = EL n s`;;

(* the test here is because underspecification is annoying (and SEG is
   underspecified) *)
(* the underlying primitive (CopyStrStr) raises an exception if the test
   is false *)
let substring_def = cake_define
  `substring ((implode) s) off len = (implode) (if off + len <=
  LENGTH s then SEG len off s else if off <= LENGTH s then DROP off s
  else "")`;;

let concat_def = cake_define
  `mlstring_concat l = (implode) (FLAT (MAP (\s. match s with
  (implode) x -> x) l))`;;
hol4_overload "concat" "mlstring_concat";;

let explode_aux_def = cake_define
  `(explode_aux s n 0 = []) /\
   (explode_aux s n (SUC len) =
     strsub s n :: (explode_aux s (n + 1) len))`;;

let explode_def = cake_define
  `explode s = explode_aux s 0 (strlen s)`;;

let extract_def = cake_define
  `mlstring_extract s i opt =
     (if strlen s <= i then implode [] else match opt with
         SOME x -> substring s i (MIN (strlen s - i) x) | NONE ->
           substring s i (strlen s - i))`;;
hol4_overload "extract" "mlstring_extract";;

let strcat_def = cake_define
  `strcat s1 s2 = concat [s1; s2]`;;
(* HOL4 overload (expanded in the port):
     None =  *)

let concatWith_def = cake_define
  `concatWith s l = concat (intersperse s l)`;;

let chr_to_str_def = cake_define
  `chr_to_str (c:char) = implode [c]`;;

(* HOL4 overload (expanded in the port):
     toString = chr_to_str *)

let translate_aux_def = cake_define
  `(translate_aux f s n 0 = []) /\
   (translate_aux f s n (SUC len) = f (strsub s n) ::
     translate_aux f s (n + 1) len)`;;

let translate_def = cake_define
  `translate f s = implode (translate_aux f s 0 (strlen s))`;;

(* HOL4 termination: *)
let splitl_aux_def = cake_define_wf
  `inv_image (<) (\(x,s,i). strlen s - i)`
  `splitl_aux P s i =
     (if i < strlen s /\ P (strsub s i) then
         splitl_aux P s (i + 1) else (extract s 0 (SOME i),extract
           s i NONE))`;;

(* HOL4 ML code, not ported:
val splitl_aux_ind = theorem"splitl_aux_ind";
*)

let splitl_def = cake_define
  `splitl P s = splitl_aux P s 0`;;

let tokens_aux_def = cake_define
  `(tokens_aux f s [] n 0 = []) /\
   (tokens_aux f s (h :: t) n 0 = [implode (REVERSE (h :: t))]) /\
   (tokens_aux f s [] n (SUC len) =
     (if f (strsub s n) then tokens_aux f s [] (n + 1) len else
       tokens_aux f s [strsub s n] (n + 1) len)) /\
   (tokens_aux f s (h :: t) n (SUC len) =
     (if f (strsub s n) then (implode (REVERSE (h :: t))) ::
       (tokens_aux f s [] (n + 1) len) else tokens_aux f s (strsub s
       n :: (h :: t)) (n + 1) len))`;;

(* HOL4 ML code, not ported:
val tokens_aux_ind = theorem"tokens_aux_ind";
*)

let tokens_def = cake_define
  `tokens f s = tokens_aux f s [] 0 (strlen s)`;;
(*
  >> TRY (
  recogniser (e.g., rename1_tac or qmatch_goalsub_rename_tac ...) >>
  ... >> NO_TAC)
  >> TRY (
  ... >> NO_TAC)
  >> TRY (
  ... >> NO_TAC)
*)

(*
Theorem TOKENS_eq_tokens_sym
  `!P ls. tokens P ls = MAP implode (TOKENS P (explode ls))`
  (rw[]
  \\ Q.ISPEC_THEN`explode`match_mp_tac INJ_MAP_EQ
  \\ simp[MAP_MAP_o,INJ_DEF,explode_11,o_DEF,explode_implode
    ,TOKENS_eq_tokens]
*)

(* HOL4 termination: >>rw[] *)
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

let fields_aux_def = cake_define
  `(fields_aux f s ss n 0 = [implode (REVERSE ss)]) /\
   (fields_aux f s ss n (SUC len) =
     (if f (strsub s n) then implode (REVERSE ss) :: (fields_aux f
       s [] (n + 1) len) else fields_aux f s (strsub s n :: ss) (n +
       1) len))`;;


let fields_def = cake_define
  `fields f s = fields_aux f s [] 0 (strlen s)`;;

(* HOL4 termination: >>rw[] *)
let fields_alt_aux_def = cake_define_wf
  `MEASURE (\(f,s,i,j,n). n - j)`
  `(fields_alt_aux f s i j n =
   (if j < n then
     (if f (strsub s j) then
         substring s i (j - i) ::
         (fields_alt_aux f s (j + 1) (j + 1) n) else
       fields_alt_aux f s i (j + 1) n) else
     [substring s i (j - i)]))`;;


(* HOL4 termination: *)
let str_findi_def = cake_define_wf
  `MEASURE (\(P,i,s). strlen s - i)`
  `str_findi P i s = (if i < strlen s then if P (strsub s i) then
  SOME i else str_findi P (i + 1) s else NONE)`;;

let isStringThere_aux_def = cake_define
  `(isStringThere_aux s1 s2 s1i s2i 0 = T) /\
   (isStringThere_aux s1 s2 s1i s2i (SUC len) =
     (if strsub s1 s1i = strsub s2 s2i then isStringThere_aux s1
       s2 (s1i + 1) (s2i + 1) len else F))`;;


(*

val isStringThere_thm = Q.prove (
  `!s1 s2 s1i s2i len. (s2i + len <= strlen s2) /\ (s1i + len = strlen
    s1) /\
  (strlen s1 <= strlen s2) /\ (s1i <= s2i) /\ (isStringThere_aux s1 s2 0
    s2i (strlen s1)) ==>
  (SEG len s2i (explode s2) = TAKE len (explode s1))`
  Cases_on `s1` \\ Cases_on `s2` \\
  rw [strlen_def, explode_thm, SEG, SEG_TAKE_DROP] \\
  Cases_on `len` \\ rw [SEG] \\ `s2i < STRLEN s'` by DECIDE_TAC \\
);
*)

let isPrefix_def = cake_define
  `isPrefix s1 s2 =
     (if strlen s1 <= strlen s2 then isStringThere_aux s1 s2 0 0
       (strlen s1) else F)`;;

let isSuffix_def = cake_define
  `isSuffix s1 s2 =
     (if strlen s1 <= strlen s2 then isStringThere_aux s1 s2 0
       (strlen s2 - strlen s1) (strlen s1) else F)`;;

let isSubstring_aux_def = cake_define
  `(isSubstring_aux s1 s2 lens1 n 0 = F) /\
   (isSubstring_aux s1 s2 lens1 n (SUC len) =
     (if (isStringThere_aux s1 s2 0 n lens1) then T else
       isSubstring_aux s1 s2 lens1 (n + 1) len))`;;

let isSubstring_def = cake_define
  `isSubstring s1 s2 =
   (if strlen s1 <= strlen s2 then isSubstring_aux s1 s2 (strlen
     s1) 0 ((strlen s2) - (strlen s1) + 1) else F)`;;

(* proof that isSubstring has the right sort of properties *)

(* String orderings *)
let compare_aux_def = cake_define
  `compare_aux (s1:mlstring) s2 ord start len =
     (if len = 0 then
       ord else if strsub s2 start < strsub s1 start then GREATER
         else if strsub s1 start < strsub s2 start then LESS else
         compare_aux s1 s2 ord (start + 1) (len - 1))`;;

let compare_def = cake_define
  `mlstring_compare s1 s2 = (if (strlen s1) < (strlen s2) then
  compare_aux s1 s2 LESS 0 (strlen s1) else if (strlen s2) < (strlen
  s1) then compare_aux s1 s2 GREATER 0 (strlen s2) else compare_aux
  s1 s2 EQUAL 0 (strlen s2))`;;
hol4_overload "compare" "mlstring_compare";;

let mlstring_lt_def = cake_define
  `mlstring_lt s1 s2 <=> (compare s1 s2 = LESS)`;;

let mlstring_le_def = cake_define
  `mlstring_le s1 s2 <=> (~(compare s1 s2 = GREATER))`;;

let mlstring_gt_def = cake_define
  `mlstring_gt s1 s2 <=> (compare s1 s2 = GREATER)`;;

let mlstring_ge_def = cake_define
  `mlstring_ge s1 s2 <=> (~(compare s1 s2 = LESS))`;;

(* HOL4 overload (expanded in the port):
     None =  *)
(* HOL4 overload (expanded in the port):
     None =  *)
(* HOL4 overload (expanded in the port):
     None =  *)
(* HOL4 overload (expanded in the port):
     None =  *)

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

(* HOL4 ML code, not ported:
val flip_ord_def = ternaryComparisonsTheory.invert_comparison_def
*)
(* HOL4 overload (expanded in the port):
     flip_ord = invert_comparison *)

let collate_aux_def = cake_define
  `(mlstring_collate_aux f (s1:mlstring) s2 ord n 0 = ord) /\
   (mlstring_collate_aux f s1 s2 ord n (SUC len) =
     (if f (strsub s1 n) (strsub s2 n) = EQUAL then
       mlstring_collate_aux f s1 s2 ord (n + 1) len else f (strsub s1
       n) (strsub s2 n)))`;;
hol4_overload "collate_aux" "mlstring_collate_aux";;

let collate_def = cake_define
  `mlstring_collate f s1 s2 =
   (if (strlen s1) < (strlen s2) then collate_aux f s1 s2 LESS 0
     (strlen s1) else if (strlen s2) < (strlen s1) then collate_aux f
     s1 s2 GREATER 0 (strlen s2) else collate_aux f s1 s2 EQUAL 0
     (strlen s2))`;;
hol4_overload "collate" "mlstring_collate";;

let char_escape_seq_def = cake_define
  `char_escape_seq c =
     (if c = (CHR 9) then SOME (implode "\\t") else if c = (CHR
       10) then SOME (implode "\\n") else if c = (CHR 92) then SOME
       (implode "\\\\") else if c = (CHR 34) then SOME ((implode)
       "\\\"") else NONE)`;;

let char_escaped_def = cake_define
  `char_escaped c = (match char_escape_seq c with
     NONE -> [c] | SOME s -> explode s)`;;

let escape_str_def = cake_define
  `escape_str s = implode ("\"" ++ FLAT (MAP char_escaped (explode
  s)) ++ "\"")`;;

let escape_char_def = cake_define
  `escape_char c = implode ("#\"" ++ char_escaped c ++ "\"")`;;

(* optimising mlstring app_list *)

let app_list_ann_INDUCT,app_list_ann_RECURSION = define_datatype
  "app_list_ann = BigList ('a list) | BigAppend (app_list_ann) \
   (app_list_ann) | Small ('a app_list)";;

let sum_sizes_def = cake_define
  `sum_sizes [] k = k /\
   sum_sizes (l :: ls) k = sum_sizes ls (strlen l + k)`;;

(* HOL4 overload (expanded in the port):
     size_limit = 2048:num *)

let make_app_list_ann_def = cake_define
  `make_app_list_ann input =
     (match input with Nil -> (Small input,0) | Append l1 l2 ->
         (let (x1,n1) = make_app_list_ann l1 in
          let (x2,n2) = make_app_list_ann l2 in
          let n = n1 + n2 in
            if n < (2048:num) then
              (Small input,n) else
              (BigAppend x1 x2,n)) | List ls ->
         (let n = sum_sizes ls 0 in
            if n < (2048:num) then
              (Small input,n) else (BigList ls,n)))`;;

let shrink_def = cake_define
  `shrink (Small t) = List [concat (append t)] /\
   shrink (BigList ls) = List ls /\
   shrink (BigAppend l1 l2) = Append (shrink l1) (shrink l2)`;;

let str_app_list_opt_def = cake_define
  `str_app_list_opt l =
     (let (t,n) = make_app_list_ann l in
       shrink t)`;;

let char_to_word8_def = cake_define
  `char_to_word8 (c:char) = (n2w (ORD c):word8)`;;

let word8_to_char_def = cake_define
  `word8_to_char (w:word8) = (CHR (w2n w):char)`;;

(* The translator turns each `empty_ffi s` into a call to the FFI with
   an empty name and passing `s` as the argument. The empty FFI is
   used for logging/timing purposes. *)
let empty_ffi_def = cake_define
  `empty_ffi (s:mlstring) = one`;;
