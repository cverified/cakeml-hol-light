(* ======================================================== *)
(*  fromSexp: ported from HOL4's
    compiler/parsing/fromSexpScript.sml
    A definition theory, with 46 definitions and 129 theorems.
    Needed by compiler.ml.  *)
(* ======================================================== *)

(*
  Definitions of functions for conversion between an S-expression encoding of
  the CakeML abstract syntax and the abstract syntax type itself.

  The S-expressions are parsed as *per* the PEG in HOL’s
  `examples/formal-language/context-free/simpleSexpPEGScript.sml`.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/parsing/cmlPEG.ml";;
needs "lib/ASCIInumbers.ml";;
needs "lib/comparison.ml";;
needs "lib/location.ml";;
needs "lib/numposrep.ml";;
needs "lib/simpleSexp.ml";;
needs "semantics/ast.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/namespace.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "fromSexp"
  ["ast"; "fpSem"; "mlstring"];;

let _ = do_list hide_constant ["assert"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["return","errorMonad_return"];;
(* HOL4 ancestors outside the port: quantHeuristics *)

hol4_overload "++" "OPTION_CHOICE";;

(* TODO: this is duplicated in parserProgTheory *)
(* [local] *)
let monad_unitbind_assert = prove
 (`!b x. OPTION_IGNORE_BIND (OPTION_GUARD b) x = (if b then x else
  NONE)`,
  CHEAT_TAC);;

(* HOL4 fromSexpScript.sml:26: the overload lift, which the port
   expands *)

(* TODO: move*)

let OPTION_APPLY_MAP3 = prove
 (`OPTION_APPLY (OPTION_APPLY (OPTION_MAP f x) y) z = SOME r <=>
   (?a b c. x = SOME a /\ y = SOME b /\ z = SOME c /\ f a b c = r)`,
  CHEAT_TAC);;

let OPTION_APPLY_MAP4 = prove
 (`OPTION_APPLY (OPTION_APPLY (OPTION_APPLY (OPTION_MAP f x) y) z) t =
  SOME r <=>
   (?a b c d. x = SOME a /\ y = SOME b /\ z = SOME c /\ t = SOME d
     /\ f a b c d = r)`,
  CHEAT_TAC);;

let FOLDR_SX_CONS_INJ = prove
 (`!l1 l2. ITLIST SX_CONS l1 (SX_SYM "nil") = ITLIST SX_CONS l2
  (SX_SYM "nil") <=> l1 = l2`,
  CHEAT_TAC);;

let strip_sxcons_11 = prove
 (`!s1 s2 x. strip_sxcons s1 = SOME x /\ strip_sxcons s2 = SOME x ==>
  s1 = s2`,
  CHEAT_TAC);;

let dstrip_sexp_size = prove
 (`!s sym args. dstrip_sexp s = SOME (sym,args) ==>
                 (!e. MEM e args ==> simpleSexp_sexp_size e <
                   simpleSexp_sexp_size s)`,
  CHEAT_TAC);;

let dstrip_sexp_SOME = prove
 (`dstrip_sexp s = SOME x <=>
   (?sym sa args. s =
     SX_CONS (SX_SYM sym) sa /\
     strip_sxcons sa = SOME args /\
     (x = (sym,args)))`,
  CHEAT_TAC);;

(* [simp] *)
let strip_sxcons_SOME_NIL = prove
 (`strip_sxcons s = SOME [] <=> s = (SX_SYM "nil")`,
  CHEAT_TAC);;

(* [simp] *)
let strip_sxcons_EQ_CONS = prove
 (`strip_sxcons s = SOME (h :: t) <=>
     (?s0. s = SX_CONS h s0 /\ strip_sxcons s0 = SOME t)`,
  CHEAT_TAC);;

(* HOL4 fromSexpScript.sml:103-108: ML code, not ported *)

(* HOL4 fromSexpScript.sml:110-115: ML code, not ported *)

(* HOL4 fromSexpScript.sml:117-122: ML code, not ported *)

(* HOL4 fromSexpScript.sml:124-129: ML code, not ported *)

(* end TODO *)

let encode_control_def,encode_control_ind = define_rec
  [`encode_control "" = ""`;
   `encode_control (c :: cs) =
        (if c = (CHR 92) then c :: c :: (encode_control cs) else if
          isPrint c then c :: (encode_control cs) else
             ((CHR 92) :: ((if ORD c < 16 then "0" else "") ++
               num_to_hex_string (ORD c))) ++ (encode_control cs))`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let decode_control_def,decode_control_ind = define_wf
  `MEASURE (\x0. list_size char_size x0)`
  [`decode_control "" = SOME ""`;
   `decode_control (c :: cs) =
         (if c = (CHR 92) then
         match cs with (CHR 92) :: cs -> OPTION_MAP (CONS c)
           (decode_control cs) | d1 :: d2 :: cs ->
           OPTION_IGNORE_BIND (OPTION_GUARD
             (isHexDigit d1 /\
              isHexDigit d2 /\
              (isAlpha d1 ==> isUpper d1) /\
              (isAlpha d2 ==> isUpper d2) /\ ~(isPrint (CHR
                (num_from_hex_string [d1; d2])))))
           (OPTION_MAP (CONS (CHR (num_from_hex_string [d1;
             d2]))) (decode_control cs)) | _2 -> NONE else
             OPTION_IGNORE_BIND (OPTION_GUARD (isPrint c))
             (OPTION_MAP (CONS c) (decode_control cs)))`];;

let EVERY_isPrint_encode_control = prove
 (`!ls. EVERY isPrint (encode_control ls)`,
  CHEAT_TAC);;

(* [simp] *)
let decode_encode_control = prove
 (`!ls. decode_control (encode_control ls) = SOME ls`,
  CHEAT_TAC);;

(* [local] *)
let isHexDigit_alt = prove
 (`isHexDigit c <=> c IN set_of_list "0123456789abcdefABCDEF"`,
  CHEAT_TAC);;

(* [local] *)
let UNHEX_lt16 = prove
 (`isHexDigit c ==> UNHEX c < 16`,
  CHEAT_TAC);;

let isAlpha_isUpper_isLower = prove
 (`isAlpha c ==> (~(isUpper c = isLower c))`,
  CHEAT_TAC);;

let isLower_isAlpha = prove
 (`isLower c ==> isAlpha c`,
  CHEAT_TAC);;

let encode_decode_control = prove
 (`!ls r. decode_control ls = SOME r ==> ls = encode_control r`,
  CHEAT_TAC);;

let SEXSTR_def = new_definition
  `SEXSTR s = SX_STR (encode_control s)`;;

(* [simp] *)
let SEXSTR_11 = prove
 (`SEXSTR s1 = SEXSTR s2 <=> s1 = s2`,
  CHEAT_TAC);;

(* [simp] *)
let SEXSTR_distinct = prove
 (`(~(SEXSTR s = SX_SYM sym)) /\
   (~(SEXSTR s = SX_NUM num)) /\
   (~(SEXSTR s = SX_CONS a d)) /\
   ((SEXSTR s = SX_STR s') <=> s' = encode_control s)`,
  CHEAT_TAC);;

let odestSEXSTR_def = new_definition
  `odestSEXSTR x1 =
        match x1 with
          SX_STR s -> OPTION_MAP implode (decode_control s)
        | _3 -> NONE`;;

let encode_control_remove = prove
 (`!s. EVERY isPrint s /\ ~((CHR 92) IN set_of_list s) ==>
  encode_control s = s`,
  CHEAT_TAC);;

let SEXSTR_remove = prove
 (`EVERY isPrint s /\ ~((CHR 92) IN set_of_list s) ==> SEXSTR s =
  SX_STR s`,
  CHEAT_TAC);;

let odestSXSTR_def = new_definition
  `odestSXSTR x1 =
        match x1 with
          SX_STR s -> SOME (implode s)
        | _4 -> NONE`;;

let odestSXSYM_def = new_definition
  `odestSXSYM x1 =
        match x1 with
          SX_SYM s -> SOME (implode s)
        | _5 -> NONE`;;

let odestSXNUM_def = new_definition
  `odestSXNUM x1 =
        match x1 with
          SX_NUM n -> SOME n
        | _6 -> NONE`;;

(* [simp] *)
let odestSXNUM_SEXSTR = prove
 (`odestSXNUM (SEXSTR str) = NONE`,
  CHEAT_TAC);;

let sexpopt_def = new_definition
  `sexpopt p s =
     OPTION_BIND (odestSXSYM s) (\
        nm. OPTION_IGNORE_BIND
        (OPTION_GUARD (nm = (implode "NONE"))) (
        SOME NONE)) ++
     OPTION_BIND (dstrip_sexp s) (\
       (nm,args). OPTION_IGNORE_BIND
       (OPTION_GUARD (nm = "SOME" /\ LENGTH args = 1)) (
       OPTION_MAP SOME (p (HD args))))`;;

let sexplist_def,sexplist_ind = define_shaped_rec
  "match"
  [`sexplist p s =
     (match s with
       SX_CONS h t ->
         OPTION_BIND (p h) (\
           ph. OPTION_BIND (sexplist p t) (\
           pt.
           SOME (ph :: pt))) | SX_SYM s -> (if s = "nil" then
             SOME [] else NONE) | _7 -> NONE)`];;

(* [simp] *)
let sexplist_thm = prove
 (`sexplist p (SX_CONS h t) =
     OPTION_BIND (p h) (\ph. OPTION_BIND (sexplist p t) (\pt. SOME
       (ph :: pt))) /\
   (sexplist p (SX_SYM s) = (if s = "nil" then SOME [] else NONE)) /\
   sexplist p (&n) = NONE /\
   sexplist p (SX_STR str) = NONE`,
  CHEAT_TAC);;

let sexppair_def = new_definition
  `sexppair p1 p2 s =
     (match s with
       SX_CONS s1 s2 -> OPTION_MAP2 (,) (p1 s1) (p2 s2) | _8 ->
         NONE)`;;

(* [defncong] *)
let sexppair_CONG = prove
 (`!s1 s2 p1 p1' p2 p2'.
       s1 = s2 /\
       (!s. (?s'. s2 = SX_CONS s s') ==> p1 s = p1' s) /\
       (!s. (?s'. s2 = SX_CONS s' s) ==> p2 s = p2' s) ==>
       sexppair p1 p2 s1 = sexppair p1' p2' s2`,
  CHEAT_TAC);;


let strip_sxcons_FAIL_sexplist_FAIL = prove
 (`!s. (strip_sxcons s = NONE) ==> (sexplist p s = NONE)`,
  CHEAT_TAC);;

let monad_bind_FAIL = prove
 (`monad_bind m1 (\x. NONE) = NONE`,
  CHEAT_TAC);;

(* [defncong] *)
let monad_unitbind_CONG = prove
 (`!m11 m21 m12 m22.
      m11 = m12 /\ (m12 = SOME one ==> m21 = m22) ==>
      OPTION_IGNORE_BIND m11 m21 = OPTION_IGNORE_BIND m12 m22`,
  CHEAT_TAC);;

(* [simp] *)
let strip_sxcons_thm = prove
 (`strip_sxcons (SX_CONS (h) (t)) = OPTION_MAP (CONS h) (strip_sxcons t)
  /\
   strip_sxcons (&n) = NONE /\
   strip_sxcons (SX_STR str) = NONE /\
   strip_sxcons (SX_SYM s) = (if s = "nil" then SOME [] else NONE)`,
  CHEAT_TAC);;

(* [defncong] *)
let sexplist_CONG = prove
 (`!s1 s2 p1 p2.
     s1 = s2 /\ (!e. sxMEM e s2 ==> p1 e = p2 e) ==>
     sexplist p1 s1 = sexplist p2 s2`,
  CHEAT_TAC);;

(* HOL4 fromSexpScript.sml:431: the overload guard, which the port
   expands *)

(* the termination relation that HOL4 gives is
     MEASURE (simpleSexp_sexp_size o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 fromSexpScript.sml:442-445: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let sexpid_def,sexpid_ind = define_guess_cheat
  [`sexpid p s =
     OPTION_BIND (dstrip_sexp s) (\
        (nm,args).
        ((\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Short"
          /\ LENGTH args = 1)
               (OPTION_MAP Short (p (EL 0 args))) ++
         (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Long"
           /\ LENGTH args = 2)
               (OPTION_MAP2 Long (odestSEXSTR (EL 0 args))
                 (sexpid p (EL 1 args)))))`];;

(* the termination relation that HOL4 gives is
     MEASURE simpleSexp_sexp_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 fromSexpScript.sml:461-465: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let sexptype_def,sexptype_ind = define_guess_cheat
  [`sexptype s =
     OPTION_BIND (dstrip_sexp s) (\
        (s,args).
        ((\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (s = "Atvar"
          /\ LENGTH args = 1)
               (OPTION_MAP Atvar (odestSEXSTR (EL 0 args))) ++
         (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (s = "Atfun"
           /\ LENGTH args = 2)
               (OPTION_MAP2 Atfun (sexptype (EL 0 args)) (sexptype
                 (EL 1 args))) ++
         (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (s = "Attup"
           /\ LENGTH args = 1)
               (OPTION_MAP Attup (sexplist sexptype (EL 0 args))) ++
         (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (s = "Atapp"
           /\ LENGTH args = 2)
               (OPTION_MAP2 Atapp (sexplist sexptype (EL 0 args))
                      (sexpid odestSEXSTR (EL 1 args)))))`];;

(* translator friendly version for bootstrapping *)
(* the termination relation that HOL4 gives is
     inv_image (MEASURE simpleSexp_sexp_size)
                        (\x. match x with INL y -> y | INR y -> y)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 fromSexpScript.sml:493-498: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let sexptype_alt_def,sexptype_alt_ind = define_mutual_guess_cheat
  [`sexptype_alt s =
        (match dstrip_sexp s with NONE -> NONE | SOME (nm,args) ->
          (if nm = "Atvar" /\ LENGTH args = 1 then
            OPTION_MAP Atvar (odestSEXSTR (EL 0 args)) else if nm =
              "Atfun" /\ LENGTH args = 2 then
            OPTION_MAP2 Atfun (sexptype_alt (EL 0 args))
              (sexptype_alt (EL 1 args)) else if nm = "Attup" /\ LENGTH
              args = 1 then
            OPTION_MAP Attup (sexptype_list (EL 0 args)) else if nm
              = "Atapp" /\ LENGTH args = 2 then
            OPTION_MAP2 Atapp (sexptype_list (EL 0 args)) (sexpid
              odestSEXSTR (EL 1 args)) else NONE))`;
   `sexptype_list s =
        (match s with SX_SYM nm -> (if nm = "nil" then SOME [] else
          NONE) | SX_CONS a d ->
          (match sexptype_alt a with NONE -> NONE | SOME h ->
           (match sexptype_list d with NONE -> NONE | SOME t ->
             SOME (h :: t))) | _9 -> NONE)`];;

let sexptype_alt_intro = prove
 (`(!s. sexptype s = sexptype_alt s) /\
   (!s. sexptype_list s = sexplist sexptype s)`,
  CHEAT_TAC);;

let sexptype_alt_intro1 = prove
 (`sexptype = sexptype_alt /\ sexplist sexptype = sexptype_list`,
  CHEAT_TAC);;

let sexplit_def = new_definition
  `sexplit s =
     OPTION_MAP (ast_IntLit o (&)) (odestSXNUM s) ++
     OPTION_MAP ast_StrLit (odestSEXSTR s) ++
     OPTION_BIND (dstrip_sexp s) (\
       (nm,args). OPTION_IGNORE_BIND
       (OPTION_GUARD (LENGTH args = 1)) (
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "-")
             (OPTION_BIND (odestSXNUM (HD args))
                          (\n. if n = 0 then NONE else SOME
                            (ast_IntLit (--(&n))))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "char")
             (OPTION_BIND (odestSEXSTR (HD args)) (\
               cs. OPTION_IGNORE_BIND
               (OPTION_GUARD (strlen cs = 1)) (
               SOME (ast_Char (strsub cs 0))))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "word8")
             (OPTION_BIND (odestSXNUM (HD args)) (\
               n. OPTION_IGNORE_BIND
               (OPTION_GUARD (n < 256)) (
               SOME (ast_Word8 (n2w n))))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "word64")
             (OPTION_BIND (odestSXNUM (HD args)) (\
               n. OPTION_IGNORE_BIND
               (OPTION_GUARD (n < 2 EXP 64)) (
               SOME (ast_Word64 (n2w n))))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "float64")
             (OPTION_BIND (odestSXNUM (HD args)) (\
               n. OPTION_IGNORE_BIND
               (OPTION_GUARD (n < 2 EXP 64)) (
               SOME (ast_Float64 (n2w n)))))))`;;

(* don't require Pvar constructors; bare strings can be pattern variables.
   Unclear if this sort of special-casing is ever likely to be helpful *)
(* the termination relation that HOL4 gives is
     MEASURE simpleSexp_sexp_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 fromSexpScript.sml:582-594: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let sexppat_def,sexppat_ind = define_guess_cheat
  [`sexppat s =
     OPTION_MAP ast_Pvar (odestSEXSTR s) ++
     OPTION_BIND (dstrip_sexp s) (\
       (nm,args).
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Pany" /\
         LENGTH args = 0)
             (SOME ast_Pany) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Plit" /\
         LENGTH args = 1)
             (OPTION_MAP ast_Plit (sexplit (EL 0 args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Pcon" /\
         LENGTH args = 2)
             (OPTION_MAP2 ast_Pcon (sexpopt (sexpid odestSEXSTR) (EL
               0 args))
                         (sexplist sexppat (EL 1 args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Pas" /\
         LENGTH args = 2)
             (OPTION_MAP2 ast_Pas (sexppat (EL 0 args))
                        (odestSEXSTR (EL 1 args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Pref" /\
         LENGTH args = 1) (OPTION_MAP ast_Pref (sexppat (EL 0 args)))
         ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Ptannot"
         /\ LENGTH args = 2)
             (OPTION_MAP2 ast_Ptannot (sexppat (EL 0 args))
               (sexptype (EL 1 args))))`];;

(* translator friendly version for bootstrapping *)
(* the termination relation that HOL4 gives is
     inv_image (MEASURE simpleSexp_sexp_size) (\x. match x with INL y ->
       y | INR y -> y)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 fromSexpScript.sml:629-633: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let sexppat_alt_def,sexppat_alt_ind = define_mutual_guess_cheat
  [`sexppat_alt s =
        OPTION_MAP ast_Pvar (odestSEXSTR s) ++
        (match dstrip_sexp s with NONE -> NONE | SOME (nm,args) ->
          (if nm = "Pany" /\ LENGTH args = 0 then
            SOME ast_Pany else if nm = "Plit" /\ LENGTH args = 1
              then
            OPTION_MAP ast_Plit (sexplit (EL 0 args)) else if nm =
              "Pcon" /\ LENGTH args = 2 then
            OPTION_MAP2 ast_Pcon (sexpopt (sexpid odestSEXSTR) (EL 0
              args))
              (sexppat_list (EL 1 args)) else if nm = "Pas" /\
                LENGTH args = 2 then
            OPTION_MAP2 ast_Pas (sexppat_alt (EL 0 args))
                            (odestSEXSTR (EL 1 args)) else if nm =
                              "Pref" /\ LENGTH args = 1 then
            OPTION_MAP ast_Pref (sexppat_alt (EL 0 args)) else if nm
              = "Ptannot" /\ LENGTH args = 2 then
            OPTION_MAP2 ast_Ptannot (sexppat_alt (EL 0 args))
              (sexptype_alt (EL 1 args)) else NONE))`;
   `sexppat_list s =
        (match s with SX_SYM nm -> (if nm = "nil" then SOME [] else
          NONE) | SX_CONS a d ->
          (match sexppat_alt a with NONE -> NONE | SOME h ->
           (match sexppat_list d with NONE -> NONE | SOME t ->
             SOME (h :: t))) | _10 -> NONE)`];;

(* HOL4 fromSexpScript.sml:635: ML code, not ported *)

let sexppat_alt_intro = prove
 (`(!s. sexppat s = sexppat_alt s) /\ (!s. sexppat_list s = sexplist
  sexppat s)`,
  CHEAT_TAC);;

let sexppat_alt_intro1 = prove
 (`sexppat = sexppat_alt /\ sexplist sexppat = sexppat_list`,
  CHEAT_TAC);;

let decode_thunk_mode_def = new_definition
  `decode_thunk_mode s =
     (if s = "Evaluated" then SOME Evaluated else if s =
       "NotEvaluated" then SOME NotEvaluated else NONE)`;;

let encode_thunk_mode_def = define_cases
  [`encode_thunk_mode Evaluated = "Evaluated"`;
   `encode_thunk_mode NotEvaluated = "NotEvaluated"`];;

let fromSexp_decode_test_def = new_definition
  `fromSexp_decode_test x1 =
      match x1 with
        SX_SYM s ->
     (if s = "Equal" then SOME Equal else
      if s = "Less" then SOME (ast_Compare ast_Lt) else
      if s = "LessEq" then SOME (ast_Compare ast_Leq) else
      if s = "Greater" then SOME (ast_Compare ast_Gt) else
      if s = "GreaterEq" then SOME (ast_Compare ast_Geq) else
      if s = "AltLess" then SOME (ast_AltCompare ast_Lt) else
      if s = "AltLessEq" then SOME (ast_AltCompare ast_Leq) else
      if s = "AltGreater" then SOME (ast_AltCompare ast_Gt) else
      if s = "AltGreaterEq" then SOME (ast_AltCompare ast_Geq) else
        NONE)
      | _11 -> NONE`;;
hol4_overload "decode_test" "fromSexp_decode_test";;

let decode_prim_type_def = new_definition
  `decode_prim_type x1 =
      match x1 with
        SX_SYM s ->
     (if s = "BoolT" then SOME ast_BoolT else
      if s = "IntT" then SOME ast_IntT else
      if s = "CharT" then SOME ast_CharT else
      if s = "StrT" then SOME ast_StrT else
      if s = "Word8T" then SOME (ast_WordT ast_W8) else
      if s = "Word64T" then SOME (ast_WordT ast_W64) else
      if s = "Float64T" then SOME ast_Float64T else NONE)
      | _12 -> NONE`;;

let sexparith_def = new_definition
  `sexparith x1 =
      match x1 with
        SX_SYM s ->
     (if s = "Add" then SOME ast_Add else
      if s = "Sub" then SOME ast_Sub else
      if s = "Mul" then SOME ast_Mul else
      if s = "Div" then SOME ast_Div else
      if s = "Mod" then SOME ast_Mod else
      if s = "Neg" then SOME ast_Neg else
      if s = "Abs" then SOME ast_Abs else
      if s = "And" then SOME ast_And else
      if s = "Xor" then SOME ast_Xor else
      if s = "Or" then SOME ast_Or else
      if s = "Not" then SOME ast_Not else
      if s = "Sqrt" then SOME ast_Sqrt else
      if s = "FMA" then SOME ast_FMA else NONE)
      | _13 -> NONE`;;

let sexplog_def = new_definition
  `sexplog x1 =
      match x1 with
        SX_SYM s ->
     (if s = "Andalso" then SOME Andalso else
      if s = "Orelse" then SOME Orelse else NONE)
      | _14 -> NONE`;;

let sexpop_def = new_definition
  `sexpop x1 =
        match x1 with
          SX_SYM s ->
     (if s = "Equality" then SOME ast_Equality else
     if s = "Opapp" then SOME ast_Opapp else
     if s = "Opassign" then SOME ast_Opassign else
     if s = "Opref" then SOME ast_Opref else
     if s = "Opderef" then SOME ast_Opderef else
     if s = "Aw8alloc" then SOME ast_Aw8alloc else
     if s = "Aw8sub" then SOME ast_Aw8sub else
     if s = "Aw8length" then SOME ast_Aw8length else
     if s = "Aw8update" then SOME ast_Aw8update else
     if s = "Aw8subunsafe" then SOME ast_Aw8sub_unsafe else
     if s = "Aw8updateunsafe" then SOME ast_Aw8update_unsafe else
     if s = "CopyStrStr" then SOME ast_CopyStrStr else
     if s = "CopyStrAw8" then SOME ast_CopyStrAw8 else
     if s = "CopyAw8Str" then SOME ast_CopyAw8Str else
     if s = "CopyAw8Aw8" then SOME ast_CopyAw8Aw8 else
     if s = "XorAw8Strunsafe" then SOME ast_XorAw8Str_unsafe else
     if s = "Implode" then SOME ast_Implode else
     if s = "Explode" then SOME ast_Explode else
     if s = "Strsub" then SOME ast_Strsub else
     if s = "Strlen" then SOME ast_Strlen else
     if s = "Strcat" then SOME ast_Strcat else
     if s = "VfromList" then SOME ast_VfromList else
     if s = "Vsub" then SOME ast_Vsub else
     if s = "Vsubunsafe" then SOME ast_Vsub_unsafe else
     if s = "Vlength" then SOME ast_Vlength else
     if s = "ListAppend" then SOME ast_ListAppend else
     if s = "Aalloc" then SOME ast_Aalloc else
     if s = "AallocEmpty" then SOME ast_AallocEmpty else
     if s = "AallocFixed" then SOME ast_AallocFixed else
     if s = "Asub" then SOME ast_Asub else
     if s = "Alength" then SOME ast_Alength else
     if s = "Aupdate" then SOME ast_Aupdate else
     if s = "Asubunsafe" then SOME ast_Asub_unsafe else
     if s = "Aupdateunsafe" then SOME ast_Aupdate_unsafe else
     if s = "ForceThunk" then SOME (ast_ThunkOp ForceThunk) else
     if s = "ConfigGC" then SOME ast_ConfigGC else
     if s = "Eval" then SOME ast_Eval else
     if s = "Envid" then SOME ast_Env_id else NONE)
        | (SX_CONS (SX_SYM s) (SX_STR s')) ->
        (if s = "FFI" then OPTION_MAP (ast_FFI o implode)
          (decode_control s') else NONE)
        | (SX_CONS (SX_SYM s) (SX_SYM t)) ->
        (match decode_thunk_mode t with NONE -> NONE | SOME m ->
            (if s = "AllocThunk" then SOME (ast_ThunkOp (AllocThunk
              m)) else
            if s = "UpdateThunk" then SOME (ast_ThunkOp (UpdateThunk
              m)) else NONE))
        | (SX_CONS (SX_SYM s) (SX_NUM n)) ->
       (if s = "Shift8Lsl" then SOME (ast_Shift ast_W8 Lsl n) else
       if s = "Shift8Lsr" then SOME (ast_Shift ast_W8 Lsr n) else
       if s = "Shift8Asr" then SOME (ast_Shift ast_W8 Asr n) else
       if s = "Shift8Ror" then SOME (ast_Shift ast_W8 Ror n) else
       if s = "Shift64Lsl" then SOME (ast_Shift ast_W64 Lsl n) else
       if s = "Shift64Lsr" then SOME (ast_Shift ast_W64 Lsr n) else
       if s = "Shift64Asr" then SOME (ast_Shift ast_W64 Asr n) else
       if s = "Shift64Ror" then SOME (ast_Shift ast_W64 Ror n) else
         NONE)
        | (SX_CONS (SX_SYM s) (SX_CONS x y)) ->
       (if s = "Arith" then
         (match (sexparith x,decode_prim_type y) with (SOME a,SOME
           prim_type) -> SOME (ast_Arith a prim_type) | _15 -> NONE)
           else if s = "FromTo" then
         (match (decode_prim_type x,decode_prim_type y) with (SOME
           ty1,SOME ty2) -> SOME (ast_FromTo ty1 ty2) | _16 -> NONE)
           else if s = "Test" then
         (match (fromSexp_decode_test x,decode_prim_type y) with
           (SOME test,SOME prim_type) -> SOME (ast_Test test prim_type)
           | _17 -> NONE) else NONE)
        | _18 -> NONE`;;

let sexplocpt_def = new_definition
  `sexplocpt s =
        match s with
          SX_SYM s ->
       (if s = "unk" then SOME UNKNOWNpt else if s = "eof" then SOME
         EOFpt else NONE)
        | s ->
      OPTION_BIND (strip_sxcons s) (\
        ls.
        (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (LENGTH ls = 2)
          (OPTION_MAP2 POSN
                              (odestSXNUM (EL 0 ls))
                              (odestSXNUM (EL 1 ls))))`;;

let sexplocn_def = new_definition
  `sexplocn s =
     OPTION_BIND (strip_sxcons s) (\
       ls.
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (LENGTH ls = 2)
             (OPTION_MAP2 Locs
              (sexplocpt (EL 0 ls))
              (sexplocpt (EL 1 ls))))`;;

(* the termination relation that HOL4 gives is
     MEASURE simpleSexp_sexp_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 fromSexpScript.sml:875-881: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let sexpexp_def,sexpexp_ind = define_guess_cheat
  [`sexpexp s =
     OPTION_BIND (dstrip_sexp s) (\
       (nm,args).
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Raise"
         /\ LENGTH args = 1)
             (OPTION_MAP ast_Raise (sexpexp (EL 0 args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Handle"
         /\ LENGTH args = 2)
             (OPTION_MAP2 ast_Handle
                    (sexpexp (EL 0 args))
                    (sexplist (sexppair sexppat sexpexp) (EL 1
                      args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Lit" /\
         LENGTH args = 1)
             (OPTION_MAP ast_Lit (sexplit (EL 0 args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Con" /\
         LENGTH args = 2)
             (OPTION_MAP2 ast_Con
                    (sexpopt (sexpid odestSEXSTR) (EL 0 args))
                    (sexplist sexpexp (EL 1 args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Var" /\
         LENGTH args = 1)
             (OPTION_MAP ast_Var (sexpid odestSEXSTR (EL 0 args)))
               ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Fun" /\
         LENGTH args = 2)
             (OPTION_MAP2 ast_Fun (odestSEXSTR (EL 0 args)) (sexpexp
               (EL 1 args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "App" /\
         LENGTH args = 2)
             (OPTION_MAP2 ast_App (sexpop (EL 0 args)) (sexplist
               sexpexp (EL 1 args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Log" /\
         LENGTH args = 3)
             (OPTION_APPLY (OPTION_APPLY (OPTION_MAP ast_Log
               (sexplog (EL 0 args)))
                       (sexpexp (EL 1 args)))
                       (sexpexp (EL 2 args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "If" /\
         LENGTH args = 3)
             (OPTION_APPLY (OPTION_APPLY (OPTION_MAP ast_If (sexpexp
               (EL 0 args)))
                      (sexpexp (EL 1 args)))
                      (sexpexp (EL 2 args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Mat" /\
         LENGTH args = 2)
             (OPTION_MAP2 ast_Mat
               (sexpexp (EL 0 args))
               (sexplist (sexppair sexppat sexpexp) (EL 1 args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Let" /\
         LENGTH args = 3)
             (OPTION_APPLY (OPTION_APPLY (OPTION_MAP ast_Let
               (sexpopt odestSEXSTR (EL 0 args)))
                       (sexpexp (EL 1 args)))
                       (sexpexp (EL 2 args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Letrec"
         /\ LENGTH args = 2)
             (OPTION_MAP2 ast_Letrec
               (sexplist (sexppair odestSEXSTR (sexppair odestSEXSTR
                 sexpexp)) (EL 0 args))
               (sexpexp (EL 1 args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Tannot"
         /\ LENGTH args = 2)
             (OPTION_MAP2 ast_Tannot
               (sexpexp (EL 0 args))
               (sexptype (EL 1 args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Lannot"
         /\ LENGTH args = 2)
             (OPTION_MAP2 ast_Lannot
               (sexpexp (EL 0 args))
               (sexplocn (EL 1 args))))`];;

(* translator friendly version for bootstrapping *)
let sexpexp_alt_def,sexpexp_alt_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`sexpexp_alt s =
         (match dstrip_sexp s with NONE -> NONE | SOME (nm,args) ->
              (if nm = "Raise" /\ LENGTH args = 1 then
                 OPTION_MAP ast_Raise (sexpexp_alt (EL 0 args)) else
              if nm = "Handle" /\ LENGTH args = 2 then
                 OPTION_MAP2 ast_Handle (sexpexp_alt (EL 0 args))
                   (sexppes (EL 1 args)) else
              if nm = "Lit" /\ LENGTH args = 1 then
                 OPTION_MAP ast_Lit (sexplit (EL 0 args)) else
              if nm = "Con" /\ LENGTH args = 2 then
                 OPTION_MAP2 ast_Con (sexpopt (sexpid odestSEXSTR)
                   (EL 0 args))
                   (sexpexp_list (EL 1 args)) else
              if nm = "Var" /\ LENGTH args = 1 then
                 OPTION_MAP ast_Var (sexpid odestSEXSTR (EL 0 args))
                   else
              if nm = "Fun" /\ LENGTH args = 2 then
                 OPTION_MAP2 ast_Fun (odestSEXSTR (EL 0 args))
                   (sexpexp_alt (EL 1 args)) else
              if nm = "App" /\ LENGTH args = 2 then
                 OPTION_MAP2 ast_App (sexpop (EL 0 args))
                   (sexpexp_list (EL 1 args)) else
              if nm = "Log" /\ LENGTH args = 3 then OPTION_APPLY
                (OPTION_APPLY (OPTION_MAP ast_Log (sexplog (EL 0 args)))
                (sexpexp_alt (EL 1 args)))
                 (sexpexp_alt (EL 2 args)) else
              if nm = "If" /\ LENGTH args = 3 then OPTION_APPLY
                (OPTION_APPLY (OPTION_MAP ast_If (sexpexp_alt (EL 0
                args))) (sexpexp_alt (EL 1 args)))
                 (sexpexp_alt (EL 2 args)) else
              if nm = "Mat" /\ LENGTH args = 2 then
                 OPTION_MAP2 ast_Mat (sexpexp_alt (EL 0 args))
                   (sexppes (EL 1 args)) else
              if nm = "Let" /\ LENGTH args = 3 then OPTION_APPLY
                (OPTION_APPLY (OPTION_MAP ast_Let (sexpopt odestSEXSTR
                (EL 0 args)))
                 (sexpexp_alt (EL 1 args))) (sexpexp_alt (EL 2
                   args)) else
              if nm = "Letrec" /\ LENGTH args = 2 then
                 OPTION_MAP2 ast_Letrec
                   (sexpfuns (EL 0 args))
                   (sexpexp_alt (EL 1 args)) else
              if nm = "Tannot" /\ LENGTH args = 2 then
                 OPTION_MAP2 ast_Tannot (sexpexp_alt (EL 0 args))
                   (sexptype_alt (EL 1 args)) else
              if nm = "Lannot" /\ LENGTH args = 2 then
                OPTION_MAP2 ast_Lannot (sexpexp_alt (EL 0 args))
                  (sexplocn (EL 1 args)) else NONE))`;
   `sexpexp_list s =
          (match s with SX_SYM nm -> (if nm = "nil" then SOME []
            else NONE) | SX_CONS a d ->
            (match sexpexp_alt a with NONE -> NONE | SOME h ->
             (match sexpexp_list d with NONE -> NONE | SOME t ->
               SOME (h :: t))) | _19 -> NONE)`;
   `sexppes s =
       (match s with SX_SYM nm -> (if nm = "nil" then SOME [] else
         NONE) | SX_CONS a d ->
         (match sexppatexp a with NONE -> NONE | SOME h ->
          (match sexppes d with NONE -> NONE | SOME t -> SOME (h
            :: t))) | _20 -> NONE)`;
   `sexpfuns s =
       (match s with SX_SYM nm -> (if nm = "nil" then SOME [] else
         NONE) | SX_CONS a d ->
         (match sexpfun a with NONE -> NONE | SOME h ->
          (match sexpfuns d with NONE -> NONE | SOME t -> SOME (h
            :: t))) | _21 -> NONE)`;
   `sexppatexp s =
        (match s with SX_CONS a d ->
          (match (sexppat_alt a,sexpexp_alt d) with (SOME p,SOME
            e) -> SOME (p,e) | _22 -> NONE) | _23 -> NONE)`;
   `sexpfun s =
         (match s with SX_CONS a d ->
           (match d with SX_CONS b d ->
           (match (odestSEXSTR a,odestSEXSTR b,sexpexp_alt d)
             with (SOME x,SOME y,SOME z) -> SOME (x,y,z) | _24 ->
             NONE) | _25 -> NONE) | _26 -> NONE)`];;

let sexpexp_alt_intro = prove
 (`(!s. sexpexp s = sexpexp_alt s) /\
   (!s. sexplist sexpexp s = sexpexp_list s) /\
   (!s. sexplist (sexppair sexppat sexpexp) s = sexppes s) /\
   (!s. sexplist (sexppair odestSEXSTR (sexppair odestSEXSTR
     sexpexp)) s = sexpfuns s) /\
   (!s. sexppair sexppat sexpexp s = sexppatexp s) /\
   (!s. sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp) s =
     sexpfun s)`,
  CHEAT_TAC);;

let sexpexp_alt_intro1 = prove
 (`sexpexp = sexpexp_alt /\
   sexplist (sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp)) =
     sexpfuns`,
  CHEAT_TAC);;

let sexptype_def_def = new_definition
  `sexptype_def =
   sexplist
     (sexppair (sexplist odestSEXSTR)
       (sexppair odestSEXSTR
         (sexplist (sexppair odestSEXSTR (sexplist sexptype)))))`;;

(* the termination relation that HOL4 gives is
     MEASURE simpleSexp_sexp_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 fromSexpScript.sml:1104-1108: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let sexpdec_def,sexpdec_ind = define_guess_cheat
  [`sexpdec s =
     OPTION_BIND (dstrip_sexp s) (\
       (nm,args).
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Dlet" /\
         LENGTH args = 3)
             (OPTION_APPLY (OPTION_APPLY (OPTION_MAP Dlet (sexplocn
               (HD args)))
                        (sexppat (EL 1 args)))
                        (sexpexp (EL 2 args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Dletrec"
         /\ LENGTH args = 2)
             (OPTION_MAP2 Dletrec (sexplocn (HD args))
                            (sexplist (sexppair odestSEXSTR
                              (sexppair odestSEXSTR sexpexp)) (EL 1
                              args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Dtype"
         /\ LENGTH args = 2)
             (OPTION_MAP2 Dtype (sexplocn (HD args)) (sexptype_def
               (EL 1 args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm =
         "Dtabbrev" /\ LENGTH args = 4)
             (OPTION_APPLY (OPTION_APPLY (OPTION_APPLY (OPTION_MAP
               Dtabbrev (sexplocn (EL 0 args)))
                            (sexplist odestSEXSTR (EL 1 args)))
                            (odestSEXSTR (EL 2 args)))
                            (sexptype (EL 3 args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Denv" /\
         LENGTH args = 1)
             (OPTION_MAP Denv (odestSEXSTR (EL 0 args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Dexn" /\
         LENGTH args = 3)
             (OPTION_APPLY (OPTION_APPLY (OPTION_MAP Dexn (sexplocn
               (EL 0 args)))
                        (odestSEXSTR (EL 1 args)))
                        (sexplist sexptype (EL 2 args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Dmod" /\
         LENGTH args = 2)
             (OPTION_MAP2 Dmod (odestSEXSTR (EL 0 args))
                         (sexplist sexpdec (EL 1 args))) ++
       (\b m. OPTION_IGNORE_BIND (OPTION_GUARD b) m) (nm = "Dlocal"
         /\ LENGTH args = 2)
             (OPTION_MAP2 Dlocal (sexplist sexpdec (EL 0 args))
                 (sexplist sexpdec (EL 1 args))))`];;

(* translator friendly version for bootstrapping *)
(* the termination relation that HOL4 gives is
     inv_image (MEASURE simpleSexp_sexp_size)
            (\x. match x with INL y -> y | INR y -> y)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 fromSexpScript.sml:1153-1160: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let sexpdec_alt_def,sexpdec_alt_ind = define_mutual_guess_cheat
  [`sexpdec_alt s =
        (match dstrip_sexp s with NONE -> NONE | SOME (nm,args) ->
          (if nm = "Dlet" /\ LENGTH args = 3 then
              (OPTION_APPLY (OPTION_APPLY (OPTION_MAP Dlet (sexplocn
                (HD args)))
                           (sexppat_alt (EL 1 args)))
                           (sexpexp_alt (EL 2 args))) else
          if nm = "Dletrec" /\ LENGTH args = 2 then
                (OPTION_MAP2 Dletrec (sexplocn (HD args))
                              (sexpfuns (EL 1 args))) else
          if nm = "Dtype" /\ LENGTH args = 2 then
                (OPTION_MAP2 Dtype (sexplocn (HD args))
                  (sexptype_def (EL 1 args))) else
          if nm = "Dtabbrev" /\ LENGTH args = 4 then
                (OPTION_APPLY (OPTION_APPLY (OPTION_APPLY
                  (OPTION_MAP Dtabbrev (sexplocn (EL 0 args)))
                              (sexplist odestSEXSTR (EL 1 args)))
                              (odestSEXSTR (EL 2 args)))
                              (sexptype_alt (EL 3 args))) else
          if nm = "Denv" /\ LENGTH args = 1 then
                (OPTION_MAP Denv (odestSEXSTR (EL 0 args))) else
          if nm = "Dexn" /\ LENGTH args = 3 then
                (OPTION_APPLY (OPTION_APPLY (OPTION_MAP Dexn
                  (sexplocn (EL 0 args)))
                           (odestSEXSTR (EL 1 args)))
                           (sexptype_list (EL 2 args))) else
          if nm = "Dmod" /\ LENGTH args = 2 then
                (OPTION_MAP2 Dmod (odestSEXSTR (EL 0 args))
                            (sexpdec_list (EL 1 args))) else
          if nm = "Dlocal" /\ LENGTH args = 2 then
                (OPTION_MAP2 Dlocal (sexpdec_list (EL 0 args))
                            (sexpdec_list (EL 1 args))) else
                              NONE))`;
   `sexpdec_list s =
          (match s with SX_SYM nm -> (if nm = "nil" then SOME []
            else NONE) | SX_CONS a d ->
            (match sexpdec_alt a with NONE -> NONE | SOME h ->
             (match sexpdec_list d with NONE -> NONE | SOME t
               -> SOME (h :: t))) | _27 -> NONE)`];;

(* HOL4 fromSexpScript.sml:1162: ML code, not ported *)

let sexpdec_alt_intro = prove
 (`(!s. sexpdec s = sexpdec_alt s) /\
   (!s. sexplist sexpdec s = sexpdec_list s)`,
  CHEAT_TAC);;

let sexpdec_alt_intro1 = prove
 (`sexpdec = sexpdec_alt /\
   sexplist sexpdec = sexpdec_list`,
  CHEAT_TAC);;

(* now the reverse: toSexp *)

let listsexp_def = new_definition
  `listsexp = FOLDR SX_CONS (SX_SYM "nil")`;;

(* [simp] *)
let listsexp_thm = prove
 (`listsexp [] = (SX_SYM "nil") /\ listsexp (h :: t) = SX_CONS h
  (listsexp t)`,
  CHEAT_TAC);;

(* [simp] *)
let listsexp_11 = prove
 (`!l1 l2. listsexp l1 = listsexp l2 <=> l1 = l2`,
  CHEAT_TAC);;

let optsexp_def = define_cases
  [`optsexp NONE = SX_SYM "NONE"`;
   `optsexp (SOME x) = listsexp [SX_SYM "SOME"; x]`];;

(* [simp] *)
let optsexp_11 = prove
 (`optsexp o1 = optsexp o2 <=> o1 = o2`,
  CHEAT_TAC);;

let idsexp_def,idsexp_ind = define_rec
  [`idsexp (Short n) = listsexp [SX_SYM "Short"; SEXSTR (explode n)]`;
   `idsexp (Long ns n) = listsexp [SX_SYM "Long"; SEXSTR (explode
  ns); idsexp n]`];;

(* [simp] *)
let idsexp_11 = prove
 (`!i1 i2. idsexp i1 = idsexp i2 <=> i1 = i2`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE ast_t_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 fromSexpScript.sml:1233-1237: the tactic that proves the
   termination *)
let typesexp_def,typesexp_ind = define_shaped_rec
  "nested"
  [`typesexp (Atvar s) = listsexp [SX_SYM "Atvar"; SEXSTR (explode
  s)]`;
   `typesexp (Atfun t1 t2) = listsexp [SX_SYM "Atfun"; typesexp t1;
  typesexp t2]`;
   `typesexp (Attup ts) = listsexp [SX_SYM "Attup"; listsexp (MAP
  typesexp ts)]`;
   `typesexp (Atapp ts tc) = listsexp [SX_SYM "Atapp"; listsexp
  (MAP typesexp ts); idsexp tc]`];;

(* [simp] *)
let typesexp_11 = prove
 (`!t1 t2. typesexp t1 = typesexp t2 <=> t1 = t2`,
  CHEAT_TAC);;

let litsexp_def = define_cases
  [`litsexp (ast_IntLit i) =
       (if i < (&0) then listsexp [SX_SYM "-"; SX_NUM (num_of_int
         (--i))] else SX_NUM (num_of_int i))`;
   `litsexp (ast_Char c) = listsexp [SX_SYM "char"; SEXSTR [c]]`;
   `litsexp (ast_StrLit s) = SEXSTR (explode s)`;
   `litsexp (ast_Word8 w) = listsexp [SX_SYM "word8"; SX_NUM (w2n w)]`;
   `litsexp (ast_Word64 w:lit) = listsexp [SX_SYM "word64"; SX_NUM
  (w2n w)]`;
   `litsexp (ast_Float64 w) = listsexp [SX_SYM "float64"; SX_NUM
  (w2n w)]`];;

(* [simp] *)
let litsexp_11 = prove
 (`!l1 l2. litsexp l1 = litsexp l2 <=> l1 = l2`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE ast_pat_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 fromSexpScript.sml:1277-1284: the tactic that proves the
   termination *)
let patsexp_def,patsexp_ind = define_shaped_rec
  "nested"
  [`patsexp (ast_Pany:ast_pat) = listsexp [SX_SYM "Pany"]`;
   `patsexp (ast_Pvar s:ast_pat) = SEXSTR (explode s)`;
   `patsexp (ast_Plit l:ast_pat) = listsexp [SX_SYM "Plit"; litsexp
  l]`;
   `patsexp (ast_Pcon cn ps:ast_pat) = listsexp [SX_SYM "Pcon";
  optsexp (OPTION_MAP idsexp cn); listsexp (MAP patsexp ps)]`;
   `patsexp (ast_Pas p i:ast_pat) = listsexp [SX_SYM "Pas"; patsexp
  p; SEXSTR (explode i)]`;
   `patsexp (ast_Pref p:ast_pat) = listsexp [SX_SYM "Pref"; patsexp
  p]`;
   `patsexp (ast_Ptannot p t) = listsexp [SX_SYM "Ptannot"; patsexp
  p; typesexp t]`];;

(* [simp] *)
let patsexp_11 = prove
 (`!p1 p2. patsexp p1 = patsexp p2 <=> p1 = p2`,
  CHEAT_TAC);;

let testsexp_def = new_definition
  `testsexp x1 =
      match x1 with
        (Equal:test) -> SX_SYM "Equal"
      | (ast_Compare ast_Lt) -> SX_SYM "Less"
      | (ast_Compare ast_Leq) -> SX_SYM "LessEq"
      | (ast_Compare ast_Gt) -> SX_SYM "Greater"
      | (ast_Compare ast_Geq) -> SX_SYM "GreaterEq"
      | (ast_AltCompare ast_Lt) -> SX_SYM "AltLess"
      | (ast_AltCompare ast_Leq) -> SX_SYM "AltLessEq"
      | (ast_AltCompare ast_Gt) -> SX_SYM "AltGreater"
      | (ast_AltCompare ast_Geq) -> SX_SYM "AltGreaterEq"`;;

(* [simp] *)
let testsexp_11 = prove
 (`!l1 l2. testsexp l1 = testsexp l2 <=> l1 = l2`,
  CHEAT_TAC);;

(* [simp] *)
let sexptest_testsexp = prove
 (`!x. fromSexp_decode_test (testsexp x) = SOME x`,
  CHEAT_TAC);;

let arithsexp_def = define_cases
  [`arithsexp (ast_Add:ast_arith) = SX_SYM "Add"`;
   `arithsexp (ast_Sub:ast_arith) = SX_SYM "Sub"`;
   `arithsexp (ast_Mul:ast_arith) = SX_SYM "Mul"`;
   `arithsexp (ast_Div:ast_arith) = SX_SYM "Div"`;
   `arithsexp (ast_Mod:ast_arith) = SX_SYM "Mod"`;
   `arithsexp (ast_And:ast_arith) = SX_SYM "And"`;
   `arithsexp (ast_Xor:ast_arith) = SX_SYM "Xor"`;
   `arithsexp (ast_Or:ast_arith) = SX_SYM "Or"`;
   `arithsexp (ast_Not:ast_arith) = SX_SYM "Not"`;
   `arithsexp ast_Neg = SX_SYM "Neg"`;
   `arithsexp ast_Abs = SX_SYM "Abs"`;
   `arithsexp ast_Sqrt = SX_SYM "Sqrt"`;
   `arithsexp ast_FMA = SX_SYM "FMA"`];;

(* [simp] *)
let arithsexp_11 = prove
 (`!l1 l2. arithsexp l1 = arithsexp l2 <=> l1 = l2`,
  CHEAT_TAC);;

(* [simp] *)
let arithsexp_sexparith = prove
 (`!x. sexparith (arithsexp x) = SOME x`,
  CHEAT_TAC);;

let prim_typesexp_def = new_definition
  `prim_typesexp x1 =
      match x1 with
        ast_BoolT -> SX_SYM "BoolT"
      | ast_IntT -> SX_SYM "IntT"
      | ast_CharT -> SX_SYM "CharT"
      | ast_StrT -> SX_SYM "StrT"
      | (ast_WordT ast_W8) -> SX_SYM "Word8T"
      | (ast_WordT ast_W64) -> SX_SYM "Word64T"
      | ast_Float64T -> SX_SYM "Float64T"`;;

let sexplist_listsexp_matchable = prove
 (`!g gl. (!x. MEM x l ==> f (g x) = SOME x) /\ (gl = MAP g l) ==>
   sexplist f (listsexp gl) = SOME l`,
  CHEAT_TAC);;

(* [simp] *)
let dstrip_sexp_SX_STR = prove
 (`dstrip_sexp (SX_STR s) = NONE`,
  CHEAT_TAC);;

(* [simp] *)
let dstrip_sexp_SEXSTR = prove
 (`dstrip_sexp (SEXSTR s) = NONE`,
  CHEAT_TAC);;

(* [simp] *)
let odestSXSTR_SOME = prove
 (`(odestSXSTR s = SOME y <=> s = SX_STR (explode y)) /\
   (SOME y = odestSXSTR s <=> s = SX_STR (explode y))`,
  CHEAT_TAC);;

(* [simp] *)
let odestSEXSTR_SOME = prove
 (`(odestSEXSTR s = SOME y <=> s = SEXSTR (explode y)) /\
   (SOME y = odestSEXSTR s <=> s = SEXSTR (explode y))`,
  CHEAT_TAC);;

(* [simp] *)
let odestSXNUM_SOME = prove
 (`(odestSXNUM s = SOME n <=> s = &n) /\
   (SOME n = odestSXNUM s <=> s = &n)`,
  CHEAT_TAC);;

(* [simp] *)
let odestSXSTR_SX_STR = prove
 (`(odestSXSTR (SX_STR s) = SOME (implode s))`,
  CHEAT_TAC);;

(* [simp] *)
let odestSEXSTR_SEXSTR = prove
 (`odestSEXSTR (SEXSTR s) = SOME (implode s)`,
  CHEAT_TAC);;

(* [simp] *)
let odestSXNUM_SX_NUM = prove
 (`odestSXNUM (SX_NUM n) = SOME n`,
  CHEAT_TAC);;

(* [simp] *)
let odestSXSYM_SX_SYM = prove
 (`odestSXSYM (SX_SYM s) = SOME (implode s)`,
  CHEAT_TAC);;

(* [simp] *)
let odestSXSTR_listsexp = prove
 (`odestSXSTR (listsexp l) = NONE`,
  CHEAT_TAC);;

(* [simp] *)
let odestSEXSTR_listsexp = prove
 (`odestSEXSTR (listsexp l) = NONE`,
  CHEAT_TAC);;

(* [simp] *)
let odestSXNUM_listsexp = prove
 (`odestSXNUM (listsexp l) = NONE`,
  CHEAT_TAC);;

(* [simp] *)
let strip_sxcons_listsexp = prove
 (`strip_sxcons (listsexp ls) = SOME ls`,
  CHEAT_TAC);;

(* [simp] *)
let dstrip_sexp_listsexp = prove
 (`(dstrip_sexp (listsexp ls) =
    (match ls with (SX_SYM x :: xs) -> SOME (x,xs) | _28 -> NONE))`,
  CHEAT_TAC);;

(* [simp] *)
let sexplist_listsexp_rwt = prove
 (`(!x. MEM x l ==> f (g x) = SOME x) ==>
   (sexplist f (listsexp (MAP g l)) = SOME l)`,
  CHEAT_TAC);;

let sexplist_listsexp_imp = prove
 (`sexplist f (listsexp l1) = SOME l2 ==>
   (!n. n < LENGTH l1 ==> f (EL n l1) = SOME (EL n l2))`,
  CHEAT_TAC);;

(* [simp] *)
let sexpopt_optsexp = prove
 (`(!y. (x = SOME y) ==> (f (g y) = x)) ==>
   (sexpopt f (optsexp (OPTION_MAP g x)) = SOME x)`,
  CHEAT_TAC);;

(* [simp] *)
let sexpid_odestSEXSTR_idsexp = prove
 (`sexpid odestSEXSTR (idsexp i) = SOME i`,
  CHEAT_TAC);;

(* [simp] *)
let dstrip_sexp_thm = prove
 (`dstrip_sexp (SX_CONS (SX_SYM s) (args)) = OPTION_MAP (\t. (s,t))
  (strip_sxcons args) /\
   dstrip_sexp (SX_CONS (&n) (args)) = NONE /\
   dstrip_sexp (SX_CONS (SX_STR str) (args)) = NONE /\
   dstrip_sexp (SX_CONS ((SX_CONS (s1) (s2))) (args)) = NONE /\
   dstrip_sexp (&n) = NONE /\
   dstrip_sexp (SX_SYM s) = NONE /\
   dstrip_sexp (SX_STR str) = NONE`,
  CHEAT_TAC);;

(* [simp] *)
let sexptype_typesexp = prove
 (`sexptype (typesexp t) = SOME t`,
  CHEAT_TAC);;

(* [simp] *)
let sexpprim_type_testsexp = prove
 (`!x. decode_prim_type (prim_typesexp x) = SOME x`,
  CHEAT_TAC);;

(* [simp] *)
let prim_typesexp_11 = prove
 (`!l1 l2. prim_typesexp l1 = prim_typesexp l2 <=> l1 = l2`,
  CHEAT_TAC);;

let opsexp_def = new_definition
  `opsexp x1 =
        match x1 with
          (ast_Shift ast_W8 Lsl n:ast_op) -> SX_CONS (SX_SYM
            "Shift8Lsl") (SX_NUM n)
        | (ast_Shift ast_W8 Lsr n) -> SX_CONS (SX_SYM "Shift8Lsr")
          (SX_NUM n)
        | (ast_Shift ast_W8 Asr n) -> SX_CONS (SX_SYM "Shift8Asr")
          (SX_NUM n)
        | (ast_Shift ast_W8 Ror n) -> SX_CONS (SX_SYM "Shift8Ror")
          (SX_NUM n)
        | (ast_Shift ast_W64 Lsl n) -> SX_CONS (SX_SYM "Shift64Lsl")
          (SX_NUM n)
        | (ast_Shift ast_W64 Lsr n) -> SX_CONS (SX_SYM "Shift64Lsr")
          (SX_NUM n)
        | (ast_Shift ast_W64 Asr n) -> SX_CONS (SX_SYM "Shift64Asr")
          (SX_NUM n)
        | (ast_Shift ast_W64 Ror n) -> SX_CONS (SX_SYM "Shift64Ror")
          (SX_NUM n)
        | ast_Equality -> SX_SYM "Equality"
        | ast_Opapp -> SX_SYM "Opapp"
        | ast_Opassign -> SX_SYM "Opassign"
        | ast_Opref -> SX_SYM "Opref"
        | ast_Opderef -> SX_SYM "Opderef"
        | ast_Aw8alloc -> SX_SYM "Aw8alloc"
        | ast_Aw8sub -> SX_SYM "Aw8sub"
        | ast_Aw8length -> SX_SYM "Aw8length"
        | ast_Aw8update -> SX_SYM "Aw8update"
        | ast_Aw8sub_unsafe -> SX_SYM "Aw8subunsafe"
        | ast_Aw8update_unsafe -> SX_SYM "Aw8updateunsafe"
        | ast_CopyStrStr -> SX_SYM "CopyStrStr"
        | ast_CopyStrAw8 -> SX_SYM "CopyStrAw8"
        | ast_CopyAw8Str -> SX_SYM "CopyAw8Str"
        | ast_CopyAw8Aw8 -> SX_SYM "CopyAw8Aw8"
        | ast_XorAw8Str_unsafe -> SX_SYM "XorAw8Strunsafe"
        | ast_Implode -> SX_SYM "Implode"
        | ast_Explode -> SX_SYM "Explode"
        | ast_Strsub -> SX_SYM "Strsub"
        | ast_Strlen -> SX_SYM "Strlen"
        | ast_Strcat -> SX_SYM "Strcat"
        | ast_VfromList -> SX_SYM "VfromList"
        | ast_Vsub -> SX_SYM "Vsub"
        | ast_Vsub_unsafe -> SX_SYM "Vsubunsafe"
        | ast_Vlength -> SX_SYM "Vlength"
        | ast_ListAppend -> SX_SYM "ListAppend"
        | ast_Aalloc -> SX_SYM "Aalloc"
        | ast_AallocEmpty -> SX_SYM "AallocEmpty"
        | ast_AallocFixed -> SX_SYM "AallocFixed"
        | ast_Asub -> SX_SYM "Asub"
        | ast_Alength -> SX_SYM "Alength"
        | ast_Aupdate -> SX_SYM "Aupdate"
        | ast_Asub_unsafe -> SX_SYM "Asubunsafe"
        | ast_Aupdate_unsafe -> SX_SYM "Aupdateunsafe"
        | ast_ConfigGC -> SX_SYM "ConfigGC"
        | ast_Eval -> SX_SYM "Eval"
        | ast_Env_id -> SX_SYM "Envid"
        | (ast_FFI s) -> SX_CONS (SX_SYM "FFI") (SEXSTR (explode s))
        | (ast_ThunkOp ForceThunk) -> SX_SYM "ForceThunk"
        | (ast_ThunkOp (AllocThunk m)) ->
       SX_CONS (SX_SYM "AllocThunk") (SX_SYM (encode_thunk_mode m))
        | (ast_ThunkOp (UpdateThunk m)) ->
       SX_CONS (SX_SYM "UpdateThunk") (SX_SYM (encode_thunk_mode m))
        | (ast_Arith a prim_type) ->
       SX_CONS (SX_SYM "Arith")
       (SX_CONS (arithsexp a)
               (prim_typesexp prim_type))
        | (ast_FromTo ty1 ty2) ->
       SX_CONS (SX_SYM "FromTo")
       (SX_CONS (prim_typesexp ty1)
               (prim_typesexp ty2))
        | (ast_Test test prim_type) ->
       SX_CONS (SX_SYM "Test")
       (SX_CONS (testsexp test)
               (prim_typesexp prim_type))`;;

(* [simp] *)
let sexpop_opsexp = prove
 (`sexpop (opsexp op) = SOME op`,
  CHEAT_TAC);;

(* [simp] *)
let opsexp_11 = prove
 (`!o1 o2. opsexp o1 = opsexp o2 <=> o1 = o2`,
  CHEAT_TAC);;

let logsexp_def = define_cases
  [`logsexp Andalso = SX_SYM "Andalso"`;
   `logsexp Orelse = SX_SYM "Orelse"`];;

(* [simp] *)
let logsexp_11 = prove
 (`!l1 l2. logsexp l1 = logsexp l2 <=> l1 = l2`,
  CHEAT_TAC);;

let locnsexp_def = define_cases
  [`locnsexp (POSN n1 n2) = listsexp (MAP SX_NUM [n1; n2])`;
   `locnsexp UNKNOWNpt = SX_SYM "unk"`;
   `locnsexp EOFpt = SX_SYM "eof"`];;

(* [simp] *)
let locnsexp_11 = prove
 (`locnsexp p1 = locnsexp p2 <=> p1 = p2`,
  CHEAT_TAC);;

let locssexp_def = define_general
  [`locssexp (Locs p1 p2) = listsexp (MAP locnsexp [p1; p2])`];;

(* [simp] *)
let locssexp_11 = prove
 (`!l1 l2. locssexp l1 = locssexp l2 <=> l1 = l2`,
  CHEAT_TAC);;

let expsexp_def,expsexp_ind = define_shaped_rec
  "nested"
  [`expsexp (ast_Raise e:ast_exp) = (SX_CONS (SX_SYM "Raise")
  (SX_CONS (expsexp e) (SX_SYM "nil")))`;
   `expsexp (ast_Handle e pes:ast_exp) =
      (SX_CONS (SX_SYM "Handle") (SX_CONS (expsexp e) (SX_CONS (
       listsexp (MAP (\(p,e). SX_CONS (patsexp p) (expsexp e))
         pes)) (SX_SYM "nil"))))`;
   `expsexp (ast_Lit l:ast_exp) = listsexp [SX_SYM "Lit"; litsexp l]`;
   `expsexp (ast_Con cn es:ast_exp) =
      listsexp [SX_SYM "Con"; optsexp (OPTION_MAP idsexp cn);
                listsexp (MAP expsexp es)]`;
   `expsexp (ast_Var id':ast_exp) = listsexp [SX_SYM "Var"; idsexp
  id']`;
   `expsexp (ast_Fun x e:ast_exp) = listsexp [SX_SYM "Fun"; SEXSTR
  (explode x); expsexp e]`;
   `expsexp (ast_App op es:ast_exp) =
      listsexp [SX_SYM "App"; opsexp op; listsexp (MAP expsexp
        es)]`;
   `expsexp (ast_Log lop e1 e2) = (SX_CONS (SX_SYM "Log") (SX_CONS
  (logsexp lop) (SX_CONS (expsexp e1) (SX_CONS (expsexp e2) (SX_SYM
  "nil")))))`;
   `expsexp (ast_If e1 e2 e3:ast_exp) = (SX_CONS (SX_SYM "If")
  (SX_CONS (expsexp e1) (SX_CONS (expsexp e2) (SX_CONS (expsexp e3)
  (SX_SYM "nil")))))`;
   `expsexp (ast_Mat e pes:ast_exp) =
      (SX_CONS (SX_SYM "Mat") (SX_CONS (expsexp e) (SX_CONS (
       listsexp (MAP (\(p,e). SX_CONS (patsexp p) (expsexp e))
         pes)) (SX_SYM "nil"))))`;
   `expsexp (ast_Let so e1 e2:ast_exp) =
      (SX_CONS (SX_SYM "Let") (SX_CONS (optsexp (OPTION_MAP
        (SEXSTR o explode) so)) (SX_CONS (expsexp e1) (SX_CONS
        (expsexp e2) (SX_SYM "nil")))))`;
   `expsexp (ast_Letrec funs e:ast_exp) =
    (SX_CONS (SX_SYM "Letrec") (SX_CONS (
     listsexp (MAP (\(x,y,z). SX_CONS (SEXSTR (explode x))
                              (SX_CONS (SEXSTR (explode y)) (expsexp
                                z))) funs)) (SX_CONS (
     expsexp e) (SX_SYM "nil"))))`;
   `expsexp (ast_Tannot e t) = (SX_CONS (SX_SYM "Tannot") (SX_CONS
  (expsexp e) (SX_CONS (typesexp t) (SX_SYM "nil"))))`;
   `expsexp (ast_Lannot e loc) = (SX_CONS (SX_SYM "Lannot")
  (SX_CONS (expsexp e) (SX_CONS (locssexp loc) (SX_SYM "nil"))))`];;

(* [local] *)
let SEXSTR_explode_11 = prove
 (`(SEXSTR o explode) s1 = (SEXSTR o explode) s2 ==> s1 = s2`,
  CHEAT_TAC);;

(* [simp] *)
let expsexp_11 = prove
 (`!e1 e2. expsexp e1 = expsexp e2 ==> e1 = e2`,
  CHEAT_TAC);;

let type_defsexp_def = new_definition
  `type_defsexp = listsexp o
     MAP (\(xs,x,ls).
       SX_CONS (listsexp (MAP (SEXSTR o explode) xs))
         (SX_CONS (SEXSTR (explode x))
           (listsexp (MAP (\(y,ts). SX_CONS (SEXSTR (explode y))
             (listsexp (MAP typesexp ts))) ls))))`;;

(* [simp] *)
let type_defsexp_11 = prove
 (`!t1 t2. type_defsexp t1 = type_defsexp t2 <=> t1 = t2`,
  CHEAT_TAC);;

(* HOL4 fromSexpScript.sml:1737-1741: a theorem whose statement the
   port cannot state yet: dec1_size_eq *)

let mem_size_lemma = prove
 (`list_size sz xs < N ==> (MEM x xs ==> sz x < N)`,
  CHEAT_TAC);;

let decsexp_def,decsexp_ind = define_shaped_rec
  "nested"
  [`decsexp (Dlet locs p e) =
      (SX_CONS (SX_SYM "Dlet") (SX_CONS (locssexp locs) (SX_CONS
        (patsexp p) (SX_CONS (expsexp e) (SX_SYM "nil")))))`;
   `decsexp (Dletrec locs funs) =
       listsexp [
           SX_SYM "Dletrec";
           locssexp locs;
           listsexp
             (MAP (\(f,x,e). SX_CONS (SEXSTR (explode f)) (SX_CONS
               (SEXSTR (explode x)) (expsexp e)))
              funs)]`;
   `decsexp (Dtype locs td) = (SX_CONS (SX_SYM "Dtype") (SX_CONS
  (locssexp locs) (SX_CONS (type_defsexp td) (SX_SYM "nil"))))`;
   `decsexp (Dtabbrev locs ns x t) = (SX_CONS (SX_SYM "Dtabbrev")
  (SX_CONS (locssexp locs) (SX_CONS (listsexp (MAP (SEXSTR o explode)
  ns)) (SX_CONS (SEXSTR (explode x)) (SX_CONS (typesexp t) (SX_SYM
  "nil"))))))`;
   `decsexp (Denv name) = (SX_CONS (SX_SYM "Denv") (SX_CONS (SEXSTR
  (explode name)) (SX_SYM "nil")))`;
   `decsexp (Dexn locs x ts) =
      (SX_CONS (SX_SYM "Dexn") (SX_CONS (locssexp locs) (SX_CONS
        (SEXSTR (explode x)) (SX_CONS (listsexp (MAP typesexp ts))
        (SX_SYM "nil")))))`;
   `decsexp (Dmod name decs) =
      (SX_CONS (SX_SYM "Dmod") (SX_CONS (SEXSTR (explode name))
        (SX_CONS (listsexp (MAP decsexp decs)) (SX_SYM "nil"))))`;
   `decsexp (Dlocal ldecs decs) =
      listsexp [SX_SYM "Dlocal"; listsexp (MAP decsexp ldecs);
                listsexp (MAP decsexp decs)]`];;

(* [simp] *)
let decsexp_11 = prove
 (`!d1 d2. decsexp d1 = decsexp d2 <=> d1 = d2`,
  CHEAT_TAC);;

(* round trip *)

(* HOL4 fromSexpScript.sml:1784-1789: ML code, not ported *)

(* [simp] *)
let sexptype_def_type_defsexp = prove
 (`sexptype_def (type_defsexp l) = SOME l`,
  CHEAT_TAC);;

(* [simp] *)
let sexplit_litsexp = prove
 (`sexplit (litsexp l) = SOME l`,
  CHEAT_TAC);;

(* [simp] *)
let sexppat_patsexp = prove
 (`sexppat (patsexp p) = SOME p`,
  CHEAT_TAC);;

(* [simp] *)
let sexplocpt_locnsexp = prove
 (`sexplocpt (locnsexp p) = SOME p`,
  CHEAT_TAC);;

(* [simp] *)
let sexplocn_locnsexp = prove
 (`sexplocn (locssexp l) = SOME l`,
  CHEAT_TAC);;

(* [simp] *)
let sexplog_logsexp = prove
 (`sexplog (logsexp l) = SOME l`,
  CHEAT_TAC);;

(* [simp] *)
let sexpexp_expsexp = prove
 (`sexpexp (expsexp e) = SOME e`,
  CHEAT_TAC);;

(* [simp] *)
let sexpdec_decsexp = prove
 (`!d. sexpdec (decsexp d) = SOME d`,
  CHEAT_TAC);;

(* [simp] *)
let odestSXSYM_EQ_SOME = prove
 (`(odestSXSYM s = SOME str <=> s = SX_SYM (explode str)) /\
   (SOME str = odestSXSYM s <=> s = SX_SYM (explode str))`,
  CHEAT_TAC);;

let sexpopt_SOME = prove
 (`sexpopt f s = SOME opt <=>
     opt = NONE /\ s = SX_SYM "NONE" \/
     (?x s0. opt = SOME x /\ f s0 = SOME x /\ s = listsexp [SX_SYM
       "SOME"; s0])`,
  CHEAT_TAC);;

let listsexp_MAP_EQ_f = prove
 (`(!x. MEM x ls ==> f1 x = f2 x) ==>
    listsexp (MAP f1 ls) = listsexp (MAP f2 ls)`,
  CHEAT_TAC);;

let sexplist_SOME = prove
 (`sexplist f s = SOME ls <=> (?l. s = listsexp l /\ MAP f l = MAP
  SOME ls)`,
  CHEAT_TAC);;

let sexppair_SOME = prove
 (`sexppair f1 f2 s = SOME p <=>
     (?x y a b. f1 x = SOME a /\ f2 y = SOME b /\ s = SX_CONS x y
       /\ p = (a,b))`,
  CHEAT_TAC);;

let OPTION_CHOICE_EQ_SOME = OPTION_CHOICE_EQUALS_OPTION;;

(* [simp] *)
let odestSXNUM_EQ_SOME = prove
 (`(odestSXNUM s = SOME n <=> s = &n) /\
   (SOME n = odestSXNUM s <=> s = &n)`,
  CHEAT_TAC);;

let litsexp_sexplit = prove
 (`(sexplit s = SOME l <=> litsexp l = s) /\
   (SOME l = sexplit s <=> litsexp l = s)`,
  CHEAT_TAC);;

let idsexp_sexpid_odestSEXSTR = prove
 (`!y x. sexpid odestSEXSTR x = SOME y <=> x = idsexp y`,
  CHEAT_TAC);;

(* [simp] *)
let idsexp_sexpid_odestSEXSTR' = prove
 (`(sexpid odestSEXSTR x = SOME y <=> x = idsexp y) /\
   (SOME y = sexpid odestSEXSTR x <=> x = idsexp y)`,
  CHEAT_TAC);;

let typesexp_sexptype = prove
 (`!s t. (sexptype s = SOME t <=> typesexp t = s) /\
         (SOME t = sexptype s <=> typesexp t = s)`,
  CHEAT_TAC);;

let patsexp_sexppat0 = prove
 (`!s p. sexppat s = SOME p ==> patsexp p = s`,
  CHEAT_TAC);;

let patsexp_sexppat = prove
 (`(sexppat s = SOME p <=> patsexp p = s) /\
   (SOME p = sexppat s <=> patsexp p = s)`,
  CHEAT_TAC);;

let decode_test_testsexp = prove
 (`fromSexp_decode_test s = SOME test ==> testsexp test = s`,
  CHEAT_TAC);;

let sexparith_arithsexp = prove
 (`sexparith s = SOME arith ==> arithsexp arith = s`,
  CHEAT_TAC);;

let decode_prim_type_prim_typesexp = prove
 (`decode_prim_type s0 = SOME prim_type ==>
   prim_typesexp prim_type = s0`,
  CHEAT_TAC);;

let opsexp_sexpop = prove
 (`sexpop s = SOME p ==> opsexp p = s`,
  CHEAT_TAC);;

let locnsexp_sexplocpt0 = prove
 (`sexplocpt s = SOME z ==> locnsexp z = s`,
  CHEAT_TAC);;

(* [simp] *)
let locnsexp_sexplocpt = prove
 (`(sexplocpt s = SOME z <=> locnsexp z = s) /\
   (SOME z = sexplocpt s <=> locnsexp z = s)`,
  CHEAT_TAC);;

let locnsexp_sexplocn = prove
 (`(sexplocn s = SOME z <=> locssexp z = s) /\
   (SOME z = sexplocn s <=> locssexp z = s)`,
  CHEAT_TAC);;

let logsexp_sexplog = prove
 (`(sexplog s = SOME z <=> logsexp z = s) /\
   (SOME z = sexplog s <=> logsexp z = s)`,
  CHEAT_TAC);;

let expsexp_sexpexp = prove
 (`(sexpexp s = SOME e <=> expsexp e = s) /\
   (SOME e = sexpexp s <=> expsexp e = s)`,
  CHEAT_TAC);;

let type_defsexp_sexptype_def = prove
 (`(sexptype_def s = SOME x <=> type_defsexp x = s) /\
   (SOME x = sexptype_def s <=> type_defsexp x = s)`,
  CHEAT_TAC);;

let decsexp_sexpdec = prove
 (`(sexpdec s = SOME d <=> decsexp d = s) /\
   (SOME d = sexpdec s <=> decsexp d = s)`,
  CHEAT_TAC);;

(* valid sexps *)

(* [simp] *)
let SEXSTR_valid = prove
 (`valid_sexp (SEXSTR s)`,
  CHEAT_TAC);;

let listsexp_valid = prove
 (`!ls. EVERY valid_sexp ls ==> valid_sexp (listsexp ls)`,
  CHEAT_TAC);;

(* [simp] *)
let idsexp_valid = prove
 (`!i. valid_sexp (idsexp i)`,
  CHEAT_TAC);;

(* [simp] *)
let typesexp_valid = prove
 (`!t. valid_sexp (typesexp t)`,
  CHEAT_TAC);;

(* [simp] *)
let litsexp_valid = prove
 (`!l. valid_sexp (litsexp l)`,
  CHEAT_TAC);;

let optsexp_valid = prove
 (`!x. (!y. x = SOME y ==> valid_sexp y) ==> valid_sexp (optsexp x)`,
  CHEAT_TAC);;

(* [simp] *)
let patsexp_valid = prove
 (`!p. valid_sexp (patsexp p)`,
  CHEAT_TAC);;

(* [simp] *)
let type_defsexp_valid = prove
 (`!t. valid_sexp (type_defsexp t)`,
  CHEAT_TAC);;

(* [simp] *)
let valid_sexp_prim_typesexp = prove
 (`!t. valid_sexp (prim_typesexp t)`,
  CHEAT_TAC);;

(* [local,simp] *)
let valid_sexp_arithsexp = prove
 (`valid_sexp (arithsexp a)`,
  CHEAT_TAC);;

(* [local,simp] *)
let valid_sexp_logsexp = prove
 (`valid_sexp (logsexp a)`,
  CHEAT_TAC);;

(* [simp] *)
let opsexp_valid = prove
 (`!op. valid_sexp (opsexp op)`,
  CHEAT_TAC);;

(* [simp] *)
let locnsexp_valid = prove
 (`!p. valid_sexp (locnsexp p)`,
  CHEAT_TAC);;

(* [simp] *)
let locssexp_valid = prove
 (`!l. valid_sexp (locssexp l)`,
  CHEAT_TAC);;

(* [simp] *)
let expsexp_valid = prove
 (`!e. valid_sexp (expsexp e)`,
  CHEAT_TAC);;

(* [simp] *)
let decsexp_valid = prove
 (`!d. valid_sexp (decsexp d)`,
  CHEAT_TAC);;

hol4_only "++" "APPEND";;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["assert"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
