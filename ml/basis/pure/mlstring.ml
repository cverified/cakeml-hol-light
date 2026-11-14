(* ======================================================== *)
(*  mlstring: ported from HOL4's
    basis/pure/mlstringScript.sml
    A definition theory, with 49 definitions, 2 datatypes and 113
    theorems.  Needed by 67 files of the port.  *)
(* ======================================================== *)

(*
  Pure functions for the String module.

  Defines mlstring as a separate type from string in HOL's standard library (a
  synonym for char list).
*)

needs "basis/pure/mllist.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/comparison.ml";;
needs "lib/ternaryComparisons.ml";;
needs "lib/toto.ml";;
needs "misc/misc.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "mlstring"
  ["misc"; "mllist"];;

let _ = do_list hide_constant ["Equal"; "Greater"; "Less"];;

(* HOL4 mlstringScript.sml:13-14: ML code, not ported *)

(* Defines strings as a separate type from char list. This theory should be
   moved into HOL, either as its own theory, or as an addendum to stringTheory *)

let mlstring_INDUCT,mlstring_RECURSION = define_datatype
  "mlstring =
     implode string";;
(* HOL4 mlstringScript.sml:22: the ML values that the definitions
   below antiquote *)

(* backwards compatibility: strlit used to be the mlstring constructor and
   implode a simple wrapper. *)
(* HOL4 mlstringScript.sml:26: the overload strlit, which the port
   expands *)

let strlen_def = define_general
  [`strlen (implode s) = LENGTH s`];;
add_simp strlen_def;;

let strsub_def = define_general
  [`strsub (implode s) n = EL n s`];;
add_simp strsub_def;;

(* the test here is because underspecification is annoying (and SEG is underspecified) *)
(* the underlying primitive (CopyStrStr) raises an exception if the test is false *)
let substring_def = define_general
  [`substring (implode s) off len = implode (if off + len <= LENGTH
  s then SEG len off s else if off <= LENGTH s then DROP off s else
  "")`];;

let concat_def = new_definition
  `mlstring_concat l = implode (FLAT (MAP (\s. match s with implode x
  -> x) l))`;;

let concat_nil = prove
 (`mlstring_concat [] = (implode "")`,
  (REWRITE_TAC[concat_def; MAP; FLAT]));;
add_simp concat_nil;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let explode_aux_def,explode_aux_ind = define_wf
  `MEASURE (\(x0,x1,x2). (\n. n) x2)`
  [`explode_aux s n 0 = []`;
   `explode_aux s n (SUC len) = CONS (strsub s n) (explode_aux s (n
    + 1) len)`];;
add_simp explode_aux_def;;

let explode_aux_thm = prove
 (`!max' n ls.
    (n + max' = LENGTH ls) ==>
    (explode_aux (implode ls) n max' = DROP n ls)`,
  CHEAT_TAC);;

let explode_def = new_definition
  `explode s = explode_aux s 0 (strlen s)`;;

let explode_thm = prove
 (`explode (implode ls) = ls`,
  (REWRITE_TAC[explode_def; strlen_def] THEN
   SIMP_TAC[explode_aux_thm; ADD_CLAUSES; DROP_0]));;
add_simp explode_thm;;

let explode_implode = prove
 (`!x. explode (implode x) = x`,
  (REWRITE_TAC[explode_thm]));;
add_simp explode_implode;;

let implode_explode = prove
 (`!x. implode (explode x) = x`,
  (MATCH_MP_TAC mlstring_INDUCT THEN REWRITE_TAC[explode_thm]));;
add_simp implode_explode;;

let explode_11 = prove
 (`!s1 s2. (explode s1 = explode s2) <=> (s1 = s2)`,
  (MESON_TAC[implode_explode]));;
add_simp explode_11;;

let implode_BIJ = prove
 (`BIJ implode UNIV UNIV`,
  (REWRITE_TAC[BIJ; INJ; SURJ; IN_UNIV] THEN
   MESON_TAC[explode_implode; implode_explode]));;

let explode_BIJ = prove
 (`BIJ explode UNIV UNIV`,
  (REWRITE_TAC[BIJ; INJ; SURJ; IN_UNIV] THEN
   MESON_TAC[explode_implode; implode_explode]));;

let LENGTH_explode = prove
 (`LENGTH (explode s) = strlen s`,
  (MP_TAC(SPEC `s:mlstring` (cases "mlstring")) THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[explode_thm; strlen_def]));;
add_simp LENGTH_explode;;

let concat_thm = prove
 (`mlstring_concat l = implode (FLAT (MAP explode l))`,
  CHEAT_TAC);;

let strlen_implode = prove
 (`strlen (implode s) = LENGTH s`,
  (REWRITE_TAC[strlen_def]));;
add_simp strlen_implode;;

let strlen_substring = prove
 (`strlen (substring s i j) = (if i + j <= strlen s then j else if i
  <= strlen s then strlen s - i else 0)`,
  CHEAT_TAC);;

let extract_def = new_definition
  `mlstring_extract s i opt =
     (if strlen s <= i then implode [] else match opt with
         SOME x -> substring s i (MIN (strlen s - i) x) | NONE ->
           substring s i (strlen s - i))`;;

let strlen_extract_le = prove
 (`!s x y. strlen (mlstring_extract s x y) <= strlen s - x`,
  CHEAT_TAC);;

let strsub_substring_0_thm = prove
 (`!m n l. m < n ==> strsub (substring l 0 n) m = strsub l m`,
  CHEAT_TAC);;

let substring_full = prove
 (`substring s 0 (strlen s) = s`,
  CHEAT_TAC);;
add_simp substring_full;;

let substring_too_long = prove
 (`strlen s <= i ==> substring s i j = (implode "")`,
  CHEAT_TAC);;

let strcat_def = new_definition
  `strcat s1 s2 = mlstring_concat [s1; s2]`;;
(* HOL4 mlstringScript.sml:183: the overload ^, which the port writes
   as an application of strcat *)

let concat_cons = prove
 (`mlstring_concat (CONS h t) = strcat h (mlstring_concat t)`,
  (REWRITE_TAC[strcat_def; concat_thm; MAP; FLAT; explode_thm;
    APPEND_NIL]));;

let strcat_thm = prove
 (`strcat s1 s2 = implode (APPEND (explode s1) (explode s2))`,
  (REWRITE_TAC[strcat_def; concat_thm; MAP; FLAT; APPEND_NIL]));;

let strcat_assoc = prove
 (`!s1 s2 s3. strcat s1 (strcat s2 s3) = strcat (strcat s1 s2) s3`,
  (REWRITE_TAC[strcat_thm; explode_thm; APPEND_ASSOC]));;
add_simp strcat_assoc;;

let strcat_o = prove
 (`strcat x o strcat y = strcat (strcat x y)`,
  (REWRITE_TAC[FUN_EQ_THM; o_THM; strcat_assoc]));;

let strcat_nil = prove
 (`(strcat (implode "") s = s) /\
   (strcat s (implode "") = s)`,
  (REWRITE_TAC[strcat_thm; explode_thm; APPEND; APPEND_NIL;
    implode_explode]));;
add_simp strcat_nil;;

let mlstring_common_prefix = prove
 (`!s t1 t2. strcat s t1 = strcat s t2 <=> t1 = t2`,
  (REWRITE_TAC[strcat_thm; injectivity "mlstring"; APPEND_LCANCEL;
    explode_11]));;
add_simp mlstring_common_prefix;;

let mlstring_common_char_prefix = prove
 (`!c1 s1 s2 t2 t2. (strcat (implode (CONS c1 s1)) t1) = (strcat
  (implode (CONS c2 s2)) t2) <=>
     c1 = c2 /\ strcat (implode s1) t1 = strcat (implode s2) t2`,
  (REWRITE_TAC[strcat_thm; injectivity "mlstring"; explode_thm;
    APPEND; CONS_11]));;
add_simp mlstring_common_char_prefix;;

let mlstring_common_suffix = prove
 (`!s t1 t2. strcat t1 s = strcat t2 s <=> t1 = t2`,
  (REWRITE_TAC[strcat_thm; injectivity "mlstring"; APPEND_RCANCEL;
    explode_11]));;
add_simp mlstring_common_suffix;;

let concat_append = prove
 (`mlstring_concat (APPEND xs ys) = strcat (mlstring_concat xs)
  (mlstring_concat ys)`,
  CHEAT_TAC);;

let implode_STRCAT = prove
 (`!l1 l2.
    implode (APPEND l1 l2) = strcat (implode l1) (implode l2)`,
  (REWRITE_TAC[strcat_thm; explode_thm]));;

let explode_strcat = prove
 (`explode (strcat s1 s2) = APPEND (explode s1) (explode s2)`,
  (REWRITE_TAC[strcat_thm; explode_thm]));;
add_simp explode_strcat;;

let strlen_strcat = prove
 (`strlen (strcat s1 s2) = strlen s1 + strlen s2`,
  (REWRITE_TAC[strcat_thm; strlen_def; LENGTH_APPEND;
    LENGTH_explode]));;
add_simp strlen_strcat;;

let concatWith_def = new_definition
  `concatWith s l = mlstring_concat (intersperse s l)`;;

let chr_to_str_def = new_definition
  `chr_to_str (c:char) = implode [c]`;;

(* HOL4 mlstringScript.sml:270: the overload toString, which the port
   expands *)

let explode_toString = prove
 (`explode (integer_word_toString c) = [c]`,
  CHEAT_TAC);;
add_simp explode_toString;;

let strlen_toString = prove
 (`strlen (integer_word_toString c) = 1`,
  CHEAT_TAC);;
add_simp strlen_toString;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let translate_aux_def,translate_aux_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3). (\n. n) x3)`
  [`translate_aux f s n 0 = []`;
   `translate_aux f s n (SUC len) = CONS (f (strsub s n))
    (translate_aux f s (n + 1) len)`];;

let translate_def = new_definition
  `translate f s = implode (translate_aux f s 0 (strlen s))`;;

(* [local] *)
let translate_aux_thm = prove
 (`!f s n len. (n + len = strlen s) ==> (translate_aux f s n len = MAP
  f (DROP n (explode s)))`,
  CHEAT_TAC);;

let translate_thm = prove
 (`!f s. translate f s = implode (MAP f (explode s))`,
  (SIMP_TAC[translate_def; translate_aux_thm; ADD_CLAUSES; DROP_0]));;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let splitl_aux_def,splitl_aux_ind = define_wf
  `inv_image (<) (\(x,s,i). strlen s - i)`
  [`splitl_aux P s i =
     (if i < strlen s /\ P (strsub s i) then
         splitl_aux P s (i + 1) else (mlstring_extract s 0 (SOME
           i),mlstring_extract s i NONE))`];;

(* HOL4 mlstringScript.sml:316: ML code, not ported *)

let splitl_def = new_definition
  `splitl P s = splitl_aux P s 0`;;

let splitl_aux_SPLITP = prove
 (`!P s i.
    splitl_aux P s i =
    (implode o (APPEND (TAKE i (explode s))) ## implode)
      (SPLITP ((~) o P) (DROP i (explode s)))`,
  CHEAT_TAC);;

let splitl_SPLITL = prove
 (`splitl P s = (implode ## implode) (SPLITL P (explode s))`,
  CHEAT_TAC);;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let tokens_aux_def,tokens_aux_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3,x4). (\n. n) x4)`
  [`tokens_aux f s [] n 0 = []`;
   `tokens_aux f s (CONS h t) n 0 = [implode (REVERSE (CONS h t))]`;
   `tokens_aux f s [] n (SUC len) =
        (if f (strsub s n) then tokens_aux f s [] (n + 1) len
            else tokens_aux f s [strsub s n] (n + 1) len)`;
   `tokens_aux f s (CONS h t) n (SUC len) =
        (if f (strsub s n) then CONS (implode (REVERSE (CONS h
            t))) (tokens_aux f s [] (n + 1) len) else tokens_aux f
            s (CONS (strsub s n) (CONS h t)) (n + 1) len)`];;

(* HOL4 mlstringScript.sml:384: ML code, not ported *)

let tokens_def = new_definition
  `tokens f s = tokens_aux f s [] 0 (strlen s)`;;


(* [local] *)
let tokens_aux_filter = prove
 (`!f s ss n len. (n + len = strlen s) ==> (mlstring_concat (tokens_aux
  f s ss n len) =
       implode (APPEND (REVERSE ss) (FILTER ((~) o f) (DROP n
         (explode s)))))`,
  CHEAT_TAC);;

let tokens_filter = prove
 (`!f s. mlstring_concat (tokens f s) = implode (FILTER ((~) o f)
  (explode s))`,
  (SIMP_TAC[tokens_def; tokens_aux_filter; ADD_CLAUSES; REVERSE;
    APPEND; DROP_0]));;

let TOKENS_eq_tokens_aux = prove
 (`!P ls ss n len. (n + len = LENGTH (explode ls)) ==>
      (MAP explode (tokens_aux P ls ss n len) = (match ss with
        (CONS h t) -> (if (~(len = 0)) /\ ((~) (P (EL n (explode
        ls)))) then CONS (APPEND (REVERSE (CONS h t)) (HD (TOKENS P
        (DROP n (explode ls))))) (TL (TOKENS P (DROP n (explode ls))))
        else if (~(len = 0)) then CONS (REVERSE (CONS h t)) (TOKENS P
        (DROP n (explode ls))) else [REVERSE (CONS h t)]) | [] ->
        (TOKENS P (DROP n (explode ls)))))`,
  CHEAT_TAC);;
(* HOL4 mlstringScript.sml:462-470: code that the source has in a
   comment *)


let TOKENS_eq_tokens = prove
 (`!P ls. (MAP explode (tokens P ls) = TOKENS P (explode ls))`,
  CHEAT_TAC);;

(* HOL4 mlstringScript.sml:479-485: code that the source has in a
   comment *)

(* HOL4 mlstringScript.sml:487-491: a theorem that HOL4 states as the
   value of an ML expression: TOKENS_eq_tokens_sym *)


let tokens_append = prove
 (`!P s1 x s2.
    P x ==>
      (tokens P (strcat (strcat s1 (integer_word_toString x)) s2) =
        APPEND (tokens P s1) (tokens P s2))`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 mlstringScript.sml:520-522: the tactic that proves the
   termination *)
let tokens_alt_aux_def,tokens_alt_aux_ind = define_wf
  `MEASURE (\(f,s,i,j,n). n - j)`
  [`(tokens_alt_aux f s i j n =
   (if j < n then
     (if f (strsub s j) then
       (if i = j then tokens_alt_aux f s (i + 1) (j + 1) n else CONS
         (substring s i (j - i))
         (tokens_alt_aux f s (j + 1) (j + 1) n)) else
       tokens_alt_aux f s i (j + 1) n) else
     if i = j then [] else [substring s i (j - i)]))`];;

let substring_1_strsub = prove
 (`i < strlen s ==>
   substring s i 1 = integer_word_toString (strsub s i)`,
  CHEAT_TAC);;

let substring_0 = prove
 (`substring s i 0 = (implode "")`,
  CHEAT_TAC);;
add_simp substring_0;;

let substring_add = prove
 (`i + x + y <= strlen s ==>
   substring s i (x + y) = strcat (substring s i x) (substring s (i
     + x) y)`,
  CHEAT_TAC);;

let tokens_alt_tokens_alt_aux = prove
 (`!f s acc j l i.
   i <= j /\ j <= strlen s /\
   strlen s - j = l /\
   acc = REVERSE (explode (substring s i (j - i))) ==>
   tokens_aux f s acc j l =
   tokens_alt_aux f s i j (strlen s)`,
  CHEAT_TAC);;

let tokens_alt = prove
 (`tokens f s =
   tokens_alt_aux f s 0 0 (strlen s)`,
  (REWRITE_TAC[tokens_def] THEN MATCH_MP_TAC
    tokens_alt_tokens_alt_aux THEN
   REWRITE_TAC[LE_REFL; LE_0; SUB_0; SUB_REFL; substring_0;
     explode_thm; REVERSE]));;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let fields_aux_def,fields_aux_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3,x4). (\n. n) x4)`
  [`fields_aux f s ss n 0 = [implode (REVERSE ss)]`;
   `fields_aux f s ss n (SUC len) =
        (if f (strsub s n) then CONS (implode (REVERSE ss))
            (fields_aux f s [] (n + 1) len) else fields_aux f s
            (CONS (strsub s n) ss) (n + 1) len)`];;


let fields_def = new_definition
  `fields f s = fields_aux f s [] 0 (strlen s)`;;


(* [local] *)
let fields_aux_filter = prove
 (`!f s ss n len. (n + len = strlen s) ==> (mlstring_concat (fields_aux
  f s ss n len) =
       implode (APPEND (REVERSE ss) (FILTER ((~) o f) (DROP n
         (explode s)))))`,
  CHEAT_TAC);;

let fields_filter = prove
 (`!f s. mlstring_concat (fields f s) = implode (FILTER ((~) o f)
  (explode s))`,
  (SIMP_TAC[fields_def; fields_aux_filter; ADD_CLAUSES; REVERSE;
    APPEND; DROP_0]));;

(* [local] *)
let fields_aux_length = prove
 (`!f s ss n len. (n + len = strlen s) ==>
     (LENGTH (fields_aux f s ss n len) = LENGTH (FILTER f (DROP n
       (explode s))) + 1)`,
  CHEAT_TAC);;


let fields_length = prove
 (`!f s. LENGTH (fields f s) = (LENGTH (FILTER f (explode s)) + 1)`,
  (SIMP_TAC[fields_def; fields_aux_length; ADD_CLAUSES; DROP_0]));;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 mlstringScript.sml:677-679: the tactic that proves the
   termination *)
let fields_alt_aux_def,fields_alt_aux_ind = define_wf
  `MEASURE (\(f,s,i,j,n). n - j)`
  [`(fields_alt_aux f s i j n =
   (if j < n then
     (if f (strsub s j) then CONS (substring s i (j - i))
         (fields_alt_aux f s (j + 1) (j + 1) n) else
       fields_alt_aux f s i (j + 1) n) else
     [substring s i (j - i)]))`];;

let fields_alt_fields_alt_aux = prove
 (`!l acc j i.
   i <= j /\ j <= strlen s /\
   strlen s - j = l /\
   acc = REVERSE (explode (substring s i (j - i))) ==>
   fields_aux f s acc j l =
   fields_alt_aux f s i j (strlen s)`,
  CHEAT_TAC);;

let fields_alt = prove
 (`fields f s =
   fields_alt_aux f s 0 0 (strlen s)`,
  (REWRITE_TAC[fields_def] THEN MATCH_MP_TAC
    fields_alt_fields_alt_aux THEN
   REWRITE_TAC[LE_REFL; LE_0; SUB_0; SUB_REFL; substring_0;
     explode_thm; REVERSE]));;


(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let str_findi_def,str_findi_ind = define_wf
  `MEASURE (\(P,i,s). strlen s - i)`
  [`str_findi P i s = (if i < strlen s then if P (strsub s i) then
  SOME i else str_findi P (i + 1) s else NONE)`];;

let str_findi_range = prove
 (`!P i s. str_findi P i s = SOME j ==> i <= j /\ j < strlen s`,
  (MATCH_MP_TAC str_findi_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
   ONCE_REWRITE_TAC[str_findi_def] THEN
   ASM_CASES_TAC `i < strlen s` THEN ASM_REWRITE_TAC[distinctness
     "option"] THEN
   ASM_CASES_TAC `(P:char->bool) (strsub s i)` THEN
   ASM_REWRITE_TAC[injectivity "option"] THENL
    [DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[LE_REFL];
     DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))
       THEN
     ASM_REWRITE_TAC[] THEN ARITH_TAC]));;

let OLEAST_LE_STEP = prove
 (`(OLEAST (\j. i <= j /\ P j)) = (if P i then SOME i else (OLEAST
  (\j. i + 1 <= j /\ P j)))`,
  CHEAT_TAC);;

let str_findi_OLEAST = prove
 (`!P i s. str_findi P i s = (OLEAST (\j. i <= j /\ j < strlen s /\ P
  (strsub s j)))`,
  CHEAT_TAC);;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let isStringThere_aux_def,isStringThere_aux_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3,x4). (\n. n) x4)`
  [`isStringThere_aux s1 s2 s1i s2i 0 = T`;
   `isStringThere_aux s1 s2 s1i s2i (SUC len) =
        (if strsub s1 s1i = strsub s2 s2i then
            isStringThere_aux s1 s2 (s1i + 1) (s2i + 1) len else F)`];;


(* HOL4 mlstringScript.sml:771-781: code that the source has in a
   comment *)

let isPrefix_def = new_definition
  `isPrefix s1 s2 =
     (if strlen s1 <= strlen s2 then isStringThere_aux s1 s2 0 0
       (strlen s1) else F)`;;

let exists_mlstring = prove
 (`(?(x:mlstring). P x) <=> (?s. P (implode s))`,
  (MESON_TAC[cases "mlstring"]));;

(* [local] *)
let isprefix_thm_aux = prove
 (`!ys xs zs.
     LENGTH ys <= LENGTH zs ==>
     (isStringThere_aux (implode (APPEND xs ys)) (implode (APPEND xs
       zs))
        (LENGTH xs) (LENGTH xs) (LENGTH ys) <=>
        ys <<= zs)`,
  CHEAT_TAC);;

let isprefix_thm = prove
 (`isPrefix s1 s2 <=> explode s1 <<= explode s2`,
  CHEAT_TAC);;

let isprefix_strcat = prove
 (`!s1 s2. isPrefix s1 s2 = (?s3. s2 = strcat s1 s3)`,
  CHEAT_TAC);;

let isSuffix_def = new_definition
  `isSuffix s1 s2 =
     (if strlen s1 <= strlen s2 then isStringThere_aux s1 s2 0
       (strlen s2 - strlen s1) (strlen s1) else F)`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let isSubstring_aux_def,isSubstring_aux_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3,x4). (\n. n) x4)`
  [`isSubstring_aux s1 s2 lens1 n 0 = F`;
   `isSubstring_aux s1 s2 lens1 n (SUC len) =
        (if (isStringThere_aux s1 s2 0 n lens1) then T else
            isSubstring_aux s1 s2 lens1 (n + 1) len)`];;

let isSubstring_def = new_definition
  `isSubstring s1 s2 =
   (if strlen s1 <= strlen s2 then isSubstring_aux s1 s2 (strlen
     s1) 0 ((strlen s2) - (strlen s1) + 1) else F)`;;

(* proof that isSubstring has the right sort of properties *)
let isStringThere_SEG = prove
 (`!i1 i2.
     i1 + n <= LENGTH s1 /\ i2 + n <= LENGTH s2 ==>
     (isStringThere_aux (implode s1) (implode s2) i1 i2 n <=>
       (SEG n i1 s1 = SEG n i2 s2))`,
  CHEAT_TAC);;

let isSubstring_aux_lemma = prove
 (`!i len.
     i + len <= strlen s2 ==>
     (isSubstring_aux s1 s2 lens1 i len <=>
      (?n. n < len /\ isStringThere_aux s1 s2 0 (n + i) lens1))`,
  (ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
   INDUCT_TAC THEN REWRITE_TAC[isSubstring_aux_def; CONJUNCT1 LT]
     THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `i + 1`) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
   EQ_TAC THENL
    [COND_CASES_TAC THEN REWRITE_TAC[] THENL
      [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ADD_CLAUSES; LT_0];
       DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
       EXISTS_TAC `m + 1` THEN
       ASM_REWRITE_TAC[ARITH_RULE `m + 1 < SUC len <=> m < len`;
                       ARITH_RULE `(m + 1) + i = m + i + 1`]];
     DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
     COND_CASES_TAC THEN REWRITE_TAC[] THEN
     DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `k:num`
       SUBST_ALL_TAC)
       (SPEC `m:num` num_CASES) THENL
      [ASM_MESON_TAC[ADD_CLAUSES];
       EXISTS_TAC `k:num` THEN CONJ_TAC THENL [ASM_ARITH_TAC;
         ALL_TAC] THEN
       UNDISCH_TAC `isStringThere_aux s1 s2 0 (SUC k + i) lens1` THEN
       REWRITE_TAC[ARITH_RULE `SUC k + i = k + i + 1`]]]));;

let isSubstring_SEG = prove
 (`isSubstring (implode s1) (implode s2) <=>
   (?i. i + LENGTH s1 <= LENGTH s2 /\ SEG (LENGTH s1) i s2 = s1)`,
  CHEAT_TAC);;

let strlit_STRCAT = prove
 (`strcat (implode a) (implode b) = implode (APPEND a b)`,
  (REWRITE_TAC[strcat_thm; explode_thm]));;

let isSubString_spec = prove
 (`isSubstring s1 s2 <=> (?p s. s2 = strcat (strcat p s1) s)`,
  CHEAT_TAC);;

(* String orderings *)
let _ = size_thms "mlstring";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let compare_aux_def,compare_aux_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3,x4). mlstring_size x0)`
  [`compare_aux (s1:mlstring) s2 ord start' len =
     (if len = 0 then
       ord else if strsub s2 start' < strsub s1 start' then
         GREATER else if strsub s1 start' < strsub s2 start' then
         LESS else compare_aux s1 s2 ord (start' + 1) (len - 1))`];;

let mlstring_compare_def = new_definition
  `mlstring_compare s1 s2 = (if (strlen s1) < (strlen s2) then
  compare_aux s1 s2 LESS 0 (strlen s1) else if (strlen s2) < (strlen
  s1) then compare_aux s1 s2 GREATER 0 (strlen s2) else compare_aux
  s1 s2 EQUAL 0 (strlen s2))`;;

let mlstring_lt_def = new_definition
  `mlstring_lt s1 s2 <=> (mlstring_compare s1 s2 = LESS)`;;

let mlstring_le_def = new_definition
  `mlstring_le s1 s2 <=> (~(mlstring_compare s1 s2 = GREATER))`;;

let mlstring_gt_def = new_definition
  `mlstring_gt s1 s2 <=> (mlstring_compare s1 s2 = GREATER)`;;

let mlstring_ge_def = new_definition
  `mlstring_ge s1 s2 <=> (~(mlstring_compare s1 s2 = LESS))`;;

let compare_thm = prove
 (`mlstring_compare s1 s2 =
     (if mlstring_lt s1 s2 then LESS else
     if mlstring_le s1 s2 then EQUAL else GREATER)`,
  (REWRITE_TAC[mlstring_lt_def; mlstring_le_def] THEN
   STRUCT_CASES_TAC (ISPEC `mlstring_compare s1 s2` (cases
     "ordering")) THEN
   REWRITE_TAC[distinctness "ordering"]));;

hol4_overload "<" "mlstring_lt";;
hol4_overload "<=" "mlstring_le";;
hol4_overload ">" "mlstring_gt";;
hol4_overload ">=" "mlstring_ge";;

let fast_lt_def = new_definition
  `fast_lt s1 s2 =
     (if strlen s1 = strlen s2 then mlstring_lt s1 s2 else strlen
       s1 < strlen s2)`;;

let fast_le_def = new_definition
  `fast_le s1 s2 =
     (if strlen s1 = strlen s2 then mlstring_le s1 s2 else strlen
       s1 <= strlen s2)`;;

let fast_gt_def = new_definition
  `fast_gt s1 s2 =
     (if strlen s1 = strlen s2 then mlstring_gt s1 s2 else strlen
       s1 > strlen s2)`;;

let fast_ge_def = new_definition
  `fast_ge s1 s2 =
     (if strlen s1 = strlen s2 then mlstring_ge s1 s2 else strlen
       s1 >= strlen s2)`;;

(* Properties of string orderings *)

(* HOL4 mlstringScript.sml:991: ML code, not ported *)
(* HOL4 mlstringScript.sml:992: the overload flip_ord, which the port
   expands *)

(* [local] *)
let compare_aux_spec = prove
 (`!s1 s2 ord_in start' len.
     len + start' <= strlen s1 /\ len + start' <= strlen s2 ==>
     (compare_aux s1 s2 ord_in start' len =
       (if TAKE len (DROP start' (explode s1)) = TAKE len (DROP
         start' (explode s2)) then
         ord_in else if string_lt (TAKE len (DROP start' (explode
           s1))) (TAKE len (DROP start' (explode s2))) then
         LESS else
         GREATER))`,
  CHEAT_TAC);;

(* [local] *)
let compare_aux_refl = prove
 (`!s1 s2 start' len.
     start' + len <= strlen s1 /\ start' + len <= strlen s2 ==>
     (
      (compare_aux s1 s2 EQUAL start' len = EQUAL) <=>
      (TAKE len (DROP start' (explode s1)) = TAKE len (DROP start'
        (explode s2))))`,
  CHEAT_TAC);;

(* [local] *)
let compare_aux_equal = prove
 (`!s1 s2 ord_in start' len.
     (compare_aux s1 s2 ord_in start' len = EQUAL) ==> (ord_in =
       EQUAL)`,
  (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
   ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
   ONCE_REWRITE_TAC[compare_aux_def] THEN REWRITE_TAC[NOT_SUC;
     SUC_SUB1] THEN
   GEN_TAC THEN REPEAT COND_CASES_TAC THEN
   ASM_REWRITE_TAC[distinctness "ordering"]));;

(* [local] *)
let compare_aux_sym = prove
 (`!s1 s2 ord_in start' len ord_out.
     (compare_aux s1 s2 ord_in start' len = ord_out) <=>
     (compare_aux s2 s1 (invert_comparison ord_in) start' len =
       invert_comparison ord_out)`,
  CHEAT_TAC);;

(* [local] *)
let string_lt_take_mono = prove
 (`!s1 s2 x.
     s1 < s2 ==> TAKE x s1 < TAKE x s2 \/ (TAKE x s1 = TAKE x s2)`,
  CHEAT_TAC);;

(* [local] *)
let string_lt_remove_take = prove
 (`!s1 s2 x. TAKE x s1 < TAKE x s2 ==> s1 < s2`,
  CHEAT_TAC);;

(* [local] *)
let string_prefix_le = prove
 (`!s1 s2. s1 <<= s2 ==> s1 <= s2`,
  CHEAT_TAC);;

(* [local] *)
let take_prefix = prove
 (`!l s. TAKE l s <<= s`,
  CHEAT_TAC);;

let mlstring_lt_inv_image = prove
 (`mlstring_lt = inv_image string_lt explode`,
  CHEAT_TAC);;

let TotOrd_compare = prove
 (`TotOrd mlstring_compare`,
  CHEAT_TAC);;

let good_cmp_compare = prove
 (`good_cmp mlstring_compare`,
  CHEAT_TAC);;

let mlstring_lt_antisym = prove
 (`!s t. ~(s < t /\ t < s)`,
  (REWRITE_TAC[mlstring_lt_def] THEN
   MESON_TAC[TotOrd_compare; TotOrd; distinctness "ordering"]));;

let mlstring_lt_cases = prove
 (`!s t. (s = t) \/ s < t \/ t < s`,
  (REWRITE_TAC[mlstring_lt_def] THEN
   MESON_TAC[TotOrd_compare; TotOrd; cases "ordering"]));;

let mlstring_lt_nonrefl = prove
 (`!s. ~(s < s)`,
  (REWRITE_TAC[mlstring_lt_def] THEN
   MESON_TAC[TotOrd_compare; TotOrd; distinctness "ordering"]));;

let mlstring_lt_trans = prove
 (`!s1 s2 s3. s1 < s2 /\ s2 < s3 ==> s1 < s3`,
  (REWRITE_TAC[mlstring_lt_def] THEN MESON_TAC[TotOrd_compare;
    TotOrd]));;

let mlstring_le_thm = prove
 (`!s1 s2. s1 <= s2 <=> (s1 = s2) \/ s1 < s2`,
  (REWRITE_TAC[mlstring_le_def; mlstring_lt_def] THEN
   MESON_TAC[TotOrd_compare; TotOrd; distinctness "ordering"; cases
     "ordering"]));;

let mlstring_gt_thm = prove
 (`!s1 s2. s1 > s2 <=> s2 < s1`,
  (REWRITE_TAC[mlstring_gt_def; mlstring_lt_def] THEN
   MESON_TAC[TotOrd_compare; TotOrd]));;

let mlstring_ge_thm = prove
 (`!s1 s2. s1 >= s2 <=> s2 <= s1`,
  (REWRITE_TAC[mlstring_ge_def; mlstring_le_def] THEN
   MESON_TAC[TotOrd_compare; TotOrd]));;

let transitive_mlstring_le = prove
 (`transitive mlstring_le`,
  CHEAT_TAC);;

let antisymmetric_mlstring_le = prove
 (`antisymmetric mlstring_le`,
  CHEAT_TAC);;

let char_lt_total = prove
 (`!(c1:char) c2. ~(c1 < c2) /\ ~(c2 < c1) ==> c1 = c2`,
  CHEAT_TAC);;

let string_lt_total = prove
 (`!(s1:string) s2. ~(s1 < s2) /\ ~(s2 < s1) ==> s1 = s2`,
  CHEAT_TAC);;

let total_mlstring_le = prove
 (`total mlstring_le`,
  (REWRITE_TAC[total_def; mlstring_le_thm] THEN
    MESON_TAC[mlstring_lt_cases]));;

(* [local] *)
let transitive_mlstring_lt = prove
 (`transitive mlstring_lt`,
  CHEAT_TAC);;

let strlit_le_strlit = prove
 (`implode s1 <= implode s2 <=> s1 <= s2`,
  CHEAT_TAC);;

(* [local] *)
let irreflexive_mlstring_lt = prove
 (`irreflexive mlstring_lt`,
  (REWRITE_TAC[irreflexive_def; mlstring_lt_nonrefl]));;

(* [local] *)
let trichotomous_mlstring_lt = prove
 (`trichotomous mlstring_lt`,
  (REWRITE_TAC[trichotomous] THEN MESON_TAC[mlstring_lt_cases]));;

let StrongLinearOrder_mlstring_lt = prove
 (`StrongLinearOrder mlstring_lt`,
  (REWRITE_TAC[StrongLinearOrder; StrongOrder;
    trichotomous_mlstring_lt;
   irreflexive_mlstring_lt; transitive_mlstring_lt]));;

let fast_lt_nonrefl = prove
 (`!s. ~(fast_lt s s)`,
  (REWRITE_TAC[fast_lt_def; mlstring_lt_nonrefl]));;

let fast_lt_trans = prove
 (`!s1 s2 s3. fast_lt s1 s2 /\ fast_lt s2 s3 ==> fast_lt s1 s3`,
  (REWRITE_TAC[fast_lt_def] THEN REPEAT GEN_TAC THEN
   ASM_CASES_TAC `strlen s1 = strlen s2` THEN
   ASM_CASES_TAC `strlen s2 = strlen s3` THEN ASM_REWRITE_TAC[] THENL
    [MESON_TAC[mlstring_lt_trans];
     ARITH_TAC;
     ARITH_TAC;
     ASM_CASES_TAC `strlen s1 = strlen s3` THEN ASM_REWRITE_TAC[]
       THEN
     ASM_ARITH_TAC]));;

let fast_le_thm = prove
 (`!s1 s2. fast_le s1 s2 <=> s1 = s2 \/ fast_lt s1 s2`,
  (REWRITE_TAC[fast_le_def; fast_lt_def] THEN REPEAT GEN_TAC THEN
   ASM_CASES_TAC `strlen s1 = strlen s2` THEN
   ASM_REWRITE_TAC[mlstring_le_thm] THEN
   ASM_CASES_TAC `s1:mlstring = s2` THEN ASM_REWRITE_TAC[] THEN
   ASM_ARITH_TAC));;

let fast_gt_thm = prove
 (`!s1 s2. fast_gt s1 s2 <=> fast_lt s2 s1`,
  (REWRITE_TAC[fast_gt_def; fast_lt_def; mlstring_gt_thm] THEN
   REPEAT GEN_TAC THEN ASM_CASES_TAC `strlen s1 = strlen s2` THEN
   ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC));;

let fast_ge_thm = prove
 (`!s1 s2. fast_ge s1 s2 <=> fast_le s2 s1`,
  (REWRITE_TAC[fast_ge_def; fast_le_def; mlstring_ge_thm] THEN
   REPEAT GEN_TAC THEN ASM_CASES_TAC `strlen s1 = strlen s2` THEN
   ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC));;

let transitive_fast_le = prove
 (`transitive fast_le`,
  (REWRITE_TAC[transitive_def; fast_le_thm] THEN
    MESON_TAC[fast_lt_trans]));;

let antisymmetric_fast_le = prove
 (`antisymmetric fast_le`,
  (REWRITE_TAC[antisymmetric_def; fast_le_thm] THEN
   MESON_TAC[fast_lt_trans; fast_lt_nonrefl]));;

let total_fast_le = prove
 (`total fast_le`,
  (REWRITE_TAC[total_def; fast_le_def] THEN REPEAT GEN_TAC THEN
   ASM_CASES_TAC `strlen x = strlen y` THEN ASM_REWRITE_TAC[] THENL
    [MP_TAC total_mlstring_le THEN REWRITE_TAC[total_def] THEN
      MESON_TAC[];
     ASM_ARITH_TAC]));;

let transitive_fast_lt = prove
 (`transitive fast_lt`,
  (REWRITE_TAC[transitive_def] THEN MESON_TAC[fast_lt_trans]));;

let irreflexive_fast_lt = prove
 (`irreflexive fast_lt`,
  (REWRITE_TAC[irreflexive_def; fast_lt_nonrefl]));;

let trichotomous_fast_lt = prove
 (`trichotomous fast_lt`,
  (REWRITE_TAC[trichotomous; fast_lt_def] THEN REPEAT GEN_TAC THEN
   ASM_CASES_TAC `strlen a = strlen b` THEN ASM_REWRITE_TAC[] THENL
    [MESON_TAC[mlstring_lt_cases]; ASM_ARITH_TAC]));;

let StrongLinearOrder_fast_lt = prove
 (`StrongLinearOrder fast_lt`,
  (REWRITE_TAC[StrongLinearOrder; StrongOrder; trichotomous_fast_lt;
   irreflexive_fast_lt; transitive_fast_lt]));;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let collate_aux_def,collate_aux_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3,x4,x5). (\n. n) x5)`
  [`mlstring_collate_aux f (s1:mlstring) s2 ord n 0 = ord`;
   `mlstring_collate_aux f (s1:mlstring) s2 ord n (SUC len) =
        (if f (strsub s1 n) (strsub s2 n) = EQUAL then
            mlstring_collate_aux f s1 s2 ord (n + 1) len else f
            (strsub s1 n) (strsub s2 n))`];;

let mlstring_collate_def = new_definition
  `mlstring_collate f s1 s2 =
   (if (strlen s1) < (strlen s2) then mlstring_collate_aux f s1 s2
     LESS 0 (strlen s1) else if (strlen s2) < (strlen s1) then
     mlstring_collate_aux f s1 s2 GREATER 0 (strlen s2) else
     mlstring_collate_aux f s1 s2 EQUAL 0 (strlen s2))`;;


(* [local] *)
let collate_aux_less_thm = prove
 (`!f s1 s2 n len.
     n + len = strlen s1 /\ strlen s1 < strlen s2 ==>
     mlstring_collate_aux f s1 s2 LESS n len =
     mllist_collate f (DROP n (explode s1)) (DROP n (explode s2))`,
  CHEAT_TAC);;

(* [local] *)
let collate_aux_equal_thm = prove
 (`!f s1 s2 n len.
     n + len = strlen s2 /\ strlen s1 = strlen s2 ==>
     mlstring_collate_aux f s1 s2 EQUAL n len =
     mllist_collate f (DROP n (explode s1)) (DROP n (explode s2))`,
  CHEAT_TAC);;

(* [local] *)
let collate_aux_greater_thm = prove
 (`!f s1 s2 n len.
     n + len = strlen s2 /\ strlen s2 < strlen s1 ==>
     mlstring_collate_aux f s1 s2 GREATER n len =
     mllist_collate f (DROP n (explode s1)) (DROP n (explode s2))`,
  CHEAT_TAC);;

let collate_thm = prove
 (`!f s1 s2. mlstring_collate f s1 s2 = mllist_collate f (explode s1)
  (explode s2)`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[mlstring_collate_def] THEN
   REPEAT COND_CASES_TAC THEN
   ASM_SIMP_TAC[collate_aux_greater_thm; collate_aux_equal_thm;
                collate_aux_less_thm; ADD_CLAUSES; DROP_0] THEN
   MP_TAC(SPECL [`f:char->char->ordering`; `s1:mlstring`;
     `s2:mlstring`; `0`;
                 `strlen s2`] collate_aux_equal_thm) THEN
   REWRITE_TAC[DROP_0; ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_ARITH_TAC));;

let char_escape_seq_def = new_definition
  `char_escape_seq c =
     (if c = (CHR 9) then SOME (implode "\\t") else if c = (CHR
       10) then SOME (implode "\\n") else if c = (CHR 92) then SOME
       (implode "\\\\") else if c = (CHR 34) then SOME (implode
       "\\\"") else NONE)`;;

let char_escaped_def = new_definition
  `char_escaped c = (match char_escape_seq c with
     NONE -> [c] | SOME s -> explode s)`;;

let escape_str_def = new_definition
  `escape_str s = implode (APPEND (APPEND "\"" (FLAT (MAP
  char_escaped (explode s)))) "\"")`;;

let escape_char_def = new_definition
  `escape_char c = implode (APPEND (APPEND "#\"" (char_escaped c))
  "\"")`;;

let ALL_DISTINCT_MAP_implode = prove
 (`ALL_DISTINCT ls ==> ALL_DISTINCT (MAP implode ls)`,
  CHEAT_TAC);;
add_simp ALL_DISTINCT_MAP_implode;;

let ALL_DISTINCT_MAP_explode = prove
 (`!ls. ALL_DISTINCT (MAP explode ls) <=> ALL_DISTINCT ls`,
  CHEAT_TAC);;
add_simp ALL_DISTINCT_MAP_explode;;

(* optimising mlstring app_list *)

let app_list_ann_INDUCT,app_list_ann_RECURSION = define_datatype
  "app_list_ann =
     BigList ('a list)
   | BigAppend app_list_ann app_list_ann
   | Small ('a app_list)";;

let sum_sizes_def,sum_sizes_ind = define_rec
  [`sum_sizes [] k = k`;
   `sum_sizes (CONS l ls) k = sum_sizes ls (strlen l + k)`];;

(* HOL4 mlstringScript.sml:1502: the overload size_limit, which the
   port expands *)

let _ = size_thms "app_list";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let make_app_list_ann_def,make_app_list_ann_ind = define_wf
  `MEASURE (\x0. app_list_size mlstring_size x0)`
  [`make_app_list_ann input =
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
              (Small input,n) else (BigList ls,n)))`];;

let shrink_def,shrink_ind = define_rec
  [`shrink (Small t) = misc_List [mlstring_concat (append t)]`;
   `shrink (BigList ls) = misc_List ls`;
   `shrink (BigAppend l1 l2) = misc_Append (shrink l1) (shrink l2)`];;

let str_app_list_opt_def = new_definition
  `str_app_list_opt l =
     (let (t,n) = make_app_list_ann l in
       shrink t)`;;

(* [local] *)
let str_app_list_opt_test = prove
 (`str_app_list_opt (misc_Append (misc_List [(implode "Hello"); (implode
  " there")])
                            (misc_List [(implode "!")])) =
   misc_List [(implode "Hello there!")]`,
  CHEAT_TAC);;

let str_app_list_opt_thm = prove
 (`mlstring_concat (append (str_app_list_opt l)) = mlstring_concat
  (append l)`,
  CHEAT_TAC);;

let concat_sing = prove
 (`mlstring_concat [x] = x`,
  (REWRITE_TAC[concat_cons; concat_nil; strcat_nil]));;
add_simp concat_sing;;

let char_to_word8_def = new_definition
  `char_to_word8 (c:char) = (n2w (ORD c):word8)`;;
add_simp char_to_word8_def;;

let word8_to_char_def = new_definition
  `word8_to_char (w:word8) = (CHR (w2n w):char)`;;
add_simp word8_to_char_def;;

(* The translator turns each `empty_ffi s` into a call to the FFI with
   an empty name and passing `s` as the argument. The empty FFI is
   used for logging/timing purposes. *)
let empty_ffi_def = new_definition
  `empty_ffi (s:mlstring) = one`;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["Equal";
   "Greater";
   "Less"];;
