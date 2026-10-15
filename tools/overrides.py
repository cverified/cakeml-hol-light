"""Per theory corrections that the translation cannot guess.

ACCESSORS: the record fields that HOL4 declares with ML code
  (add_record_field), so that they are not in a Datatype block
FIELD_OF: the record type of a field name where several record
  types have a field of that name
"""

# HOL4 names of notions that HOL Light has under another name
NAME_MAP = {
  'measure': 'MEASURE',
  'unit': 'one',
  'set': 'set_of_list',
  '()': 'one',
  'Num': 'num_of_int',
  'ABS': 'abs',
  'ARB': 'ARB',
  # the word constants of HOL4's wordsTheory
  'INT_MINw': 'word_L',
  'INT_MAXw': 'word_H',
  'UINT_MAXw': 'word_T',
  'UNCURRY': 'UNCURRY',
  'I': 'I',
}

ACCESSORS = {
  'location': {'row': 'locnrow', 'col': 'locncol'},
}

FIELD_OF = {
  # both grammar and peg have a field rules
  'pegexec': {'rules': 'peg'},
  'peg': {'rules': 'peg'},
}

# names in the HOL4 libraries that the port does not really need:
# the dependency analysis found them because a CakeML definition
# happens to use a variable of that name
NOT_NEEDED = set([
  # CakeML's mlint has its own toString and fromString
  ('integer_word', 'toString'), ('integer_word', 'fromString'),
  ('toto', 'comp'), ('toto', 'cpn'), ('toto', 'lexTO'),
  ('toto', 'lextoto'), ('toto', 'TO_of_LinearOrder'),
])

# theories that a file needs although HOL4's Ancestors do not say so
EXTRA_NEEDS = {
  'integer_word': ['ASCIInumbers'],
}

# names that the dependency analysis misses, because the CakeML
# sources use them through HOL4 syntax that mentions them only
# indirectly (a record field declared with ML code, say)
ALSO_NEEDED = set([
  # set_sep's separating conjunction is the overloaded *, and
  # SEP_EXISTS is a binder, so the dependency analysis does not see
  # that the port needs them
  ('set_sep', 'STAR'), ('set_sep', 'SEP_EXISTS'),
  ('set_sep', 'SPLIT'), ('set_sep', 'SEP_T'),
  ('location', 'locnrow'), ('location', 'locncol'),
  # HOL4 generates the fp64 encoding of machine_ieee with ML code
  # (machine_ieeeLib), which the port writes out by hand; these are
  # the binary_ieee definitions that it uses
  ('binary_ieee', 'float_to_real'), ('binary_ieee', 'float_to_int'),
  ('binary_ieee', 'real_to_float'), ('binary_ieee', 'float_sqrt'),
  ('binary_ieee', 'float_negate'), ('binary_ieee', 'float_abs'),
  ('binary_ieee', 'float_is_nan'), ('binary_ieee', 'float_add'),
  ('binary_ieee', 'float_sub'), ('binary_ieee', 'float_mul'),
  ('binary_ieee', 'float_div'), ('binary_ieee', 'float_compare'),
  ('binary_ieee', 'float_equal'),
  ('binary_ieee', 'float_less_than'),
  ('binary_ieee', 'float_less_equal'),
  ('binary_ieee', 'float_greater_than'),
  ('binary_ieee', 'float_greater_equal'),
  ('binary_ieee', 'float_mul_add'),
])

# definitions in which the numerals are integers or reals, not
# natural numbers (HOL Light writes both as &n; the exponent of pow,
# EXP and ** stays a natural number)
INT_NUMERALS = set([
  ('multiword', 'i2mw_def'),
  ('multiword', 'int_op_def'),
  ('binary_ieee', 'float_is_zero_def'),
  ('binary_ieee', 'float_round_with_flags_def'),
  ('binary_ieee', 'float_to_int_def'),
  ('binary_ieee', 'float_add_def'),
  ('binary_ieee', 'float_sub_def'),
  ('binary_ieee', 'float_mul_def'),
  ('binary_ieee', 'float_div_def'),
  ('binary_ieee', 'float_mul_add_def'),
  ('integer_word', 'toString_def'),
  ('integer_word', 'fromString_def'),
])

# definitions in which a prefix ~ is the complement of a word, not
# the negation of a proposition
WORD_NOT = set([
  ('binary_ieee', 'float_negate_def'),
])

# definitions in which the same variable name has different types in
# different clauses, which HOL4 allows (it typechecks every clause on
# its own) and one HOL Light quotation does not; the port writes the
# clauses as separate quotations
CLAUSE_FORM = set([
  ('ast', 'every_exp_def'),
])

# definitions whose clauses overlap, so that they depend on HOL4's
# first match semantics; they are ported as one clause with a
# `match', which has the same semantics in HOL Light
MATCH_FORM = set([
  ('mergesort', 'mergesortN_def'),
  ('mergesort', 'mergesortN_tail_def'),
  ('mergesort', 'merge_def'),
  ('mergesort', 'merge_tail_def'),
])

# an explicit termination relation, where HOL Light cannot guess one
# and the HOL4 source does not give one either
MEASURE = {
  # the measure is the size of the expression; without it the port
  # searches through the candidates, which takes minutes here
  ('mergesort', 'mergesortN_def'): 'MEASURE (\\(R,n,l). n)',
  ('mergesort', 'mergesortN_tail_def'):
    'MEASURE (\\(negate,R,n,l). n)',
}

# definitions that are ported by hand (the text replaces the whole
# translation of the Definition block)
REPLACE = {
  # HOL4 proves the termination with the induction principle
  # of llistTheory's eventually; the port proves the
  # existence of the function with the number of steps to
  # the first tail that satisfies P as the witness (the
  # lemmas that it needs are in ml/lib/llist.ml)
  ('misc', 'lnext_def'): r'''
let lnext_def =
  let th = prove
   (`?Lnext. !P (ll:A llist).
       Lnext P ll = if eventually P ll then
                      if P ll then 0
                      else SUC (Lnext P (THE (LTL ll)))
                    else ARB`,
    EXISTS_TAC
     `\P (ll:A llist).
        if eventually P ll
        then minimal n. ?u. LDROP n ll = SOME u /\ P u
        else ARB` THEN
    REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC MINIMAL_UNIQUE THEN BETA_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `ll:A llist` THEN ASM_REWRITE_TAC[LDROP_0];
        REWRITE_TAC[LT]];
      MP_TAC(SPECL [`P:A llist->bool`; `ll:A llist`]
                   eventually_LTL) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:A llist` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[THE] THEN
      MP_TAC(SPEC `\n. ?u. LDROP n (ll:A llist) = SOME u /\ P u`
                  MINIMAL_SUC) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `eventually (P:A llist->bool) ll` THEN
          REWRITE_TAC[eventually] THEN MESON_TAC[];
          REWRITE_TAC[LDROP_0; injectivity "option"] THEN
          ASM_MESON_TAC[]];
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
      ASM_MESON_TAC[LDROP_SUC]]) in
  new_specification ["Lnext"] th;;
''',
  # HOL4 computes the value with EVAL (of the expression below) and
  # states the numeral; the port states the expression, which is the
  # same number
  ('infer', 'start_type_id_def'): '''
let start_type_id_def = cake_define
  `start_type_id =
     ITLIST MAX (Tlist_num :: Tbool_num :: prim_type_nums) 0 + 1`;;
''',
  # HOL4 overloads * with the separating conjunction (and ~ with
  # SEP_HIDE, which the port does not need)
  ('set_sep', 'STAR_def'): '''
let STAR_def = cake_define
  `STAR p q = (\\s. ?u v. SPLIT s (u,v) /\\ p u /\\ q v)`;;

overload_interface("*",
  `STAR:((A->bool)->bool)->((A->bool)->bool)->(A->bool)->bool`);;
''',
  # HOL4 matches the number of elements with overlapping patterns and
  # a catch-all clause; the port uses nested conditionals, so that the
  # termination conditions have the guards that they need
  ('mergesort', 'mergesortN_def'): '''
let mergesortN_def = cake_define_wf
  `MEASURE (\\(R,n,l). n)`
  `mergesortN R n l =
     if n = 0 then [] else
     if n = 1 then (match l with [] -> [] | x :: l -> [x]) else
     if n = 2 then
       (match l with
          [] -> []
        | [x] -> [x]
        | x :: y :: l -> sort2 R x y) else
     if n = 3 then
       (match l with
          [] -> []
        | [x] -> [x]
        | [x; y] -> sort2 R x y
        | x :: y :: z :: l -> sort3 R x y z) else
     let len1 = DIV2 n in
       mergesort_merge R
         (mergesortN R (DIV2 n) l)
         (mergesortN R (n - len1) (DROP len1 l))`;;
''',
  ('mergesort', 'mergesortN_tail_def'): '''
let mergesortN_tail_def = cake_define_wf
  `MEASURE (\\(negate,R,n,l). n)`
  `mergesortN_tail negate R n l =
     if n = 0 then [] else
     if n = 1 then (match l with [] -> [] | x :: l -> [x]) else
     if n = 2 then
       (match l with
          [] -> []
        | [x] -> [x]
        | x :: y :: l -> sort2_tail negate R x y) else
     if n = 3 then
       (match l with
          [] -> []
        | [x] -> [x]
        | [x; y] -> sort2_tail negate R x y
        | x :: y :: z :: l -> sort3_tail negate R x y z) else
     let len1 = DIV2 n in
     let neg = ~negate in
       merge_tail neg R (mergesortN_tail neg R (DIV2 n) l)
                        (mergesortN_tail neg R (n - len1)
                                         (DROP len1 l))
                        []`;;
''',
}

# definitions that the port does not have yet, with the reason; the
# port writes the HOL4 text in a comment, so that the gap is visible
# in the file (PENDING.md lists them all)
NOT_YET = {
  ('data_to_word', 'AnyArith_call_tree_def'):
    'the value is the call graph that HOL4 computes with EVAL;\n'
    '   the expression that it evaluates has a free variable\n'
    '   (data_conf), so the port has to compute the value as well',
}

# Type blocks whose type HOL4 computes with ML code, with the type
# that it computes
TYPE_TEXT = {
  # type_of ``primTypes$prim_tenv.t``, the type of the t field of a
  # type_env, which typeSystem calls tenv_abbrev
  ('infer', 'err_var'): 'tenv_abbrev',
}

# definitions that HOL4 generates with ML code, so that there is no
# Definition block to translate; the port has them by hand, and they
# are put just after the needs of the file
EXTRA_HEAD = {
  'machine_ieee': r'''
(* HOL4 generates the definitions of the fp16, fp32 and fp64
   encodings of floating point numbers with ML code (the function
   mk_fp_encoding of machine_ieeeLib), so there is nothing to
   translate here; these are the fp64 definitions that the CakeML
   port needs, in the order in which HOL4 generates them  *)

let fp64_to_float_def = cake_define
  `fp64_to_float (w:word64) =
     (mk_float ((63 >< 63) w) ((62 >< 52) w)
               ((51 >< 0) w)):(52,11)float`;;

let float_to_fp64_def = cake_define
  `float_to_fp64 (x:(52,11)float) =
     (((float_Sign x @@ float_Exponent x):word12) @@
      float_Significand x):word64`;;

let real_to_fp64_def = cake_define
  `real_to_fp64 mode = float_to_fp64 o real_to_float mode`;;

let int_to_fp64_def = cake_define
  `int_to_fp64 mode a = real_to_fp64 mode (real_of_int a)`;;

let fp64_to_int_def = cake_define
  `fp64_to_int mode = float_to_int mode o fp64_to_float`;;

let fp64_abs_def = cake_define
  `fp64_abs = float_to_fp64 o float_abs o fp64_to_float`;;

let fp64_negate_def = cake_define
  `fp64_negate = float_to_fp64 o float_negate o fp64_to_float`;;

let fp64_isNan_def = cake_define
  `fp64_isNan = float_is_nan o fp64_to_float`;;

let fp64_sqrt_def = cake_define
  `fp64_sqrt mode =
     float_to_fp64 o SND o float_sqrt mode o fp64_to_float`;;

let fp64_add_def = cake_define
  `fp64_add mode a b =
     float_to_fp64 (SND (float_add mode (fp64_to_float a)
                                        (fp64_to_float b)))`;;

let fp64_sub_def = cake_define
  `fp64_sub mode a b =
     float_to_fp64 (SND (float_sub mode (fp64_to_float a)
                                        (fp64_to_float b)))`;;

let fp64_mul_def = cake_define
  `fp64_mul mode a b =
     float_to_fp64 (SND (float_mul mode (fp64_to_float a)
                                        (fp64_to_float b)))`;;

let fp64_div_def = cake_define
  `fp64_div mode a b =
     float_to_fp64 (SND (float_div mode (fp64_to_float a)
                                        (fp64_to_float b)))`;;

let fp64_compare_def = cake_define
  `fp64_compare a b =
     float_compare (fp64_to_float a) (fp64_to_float b)`;;

let fp64_equal_def = cake_define
  `fp64_equal a b = float_equal (fp64_to_float a) (fp64_to_float b)`;;

let fp64_lessThan_def = cake_define
  `fp64_lessThan a b =
     float_less_than (fp64_to_float a) (fp64_to_float b)`;;

let fp64_lessEqual_def = cake_define
  `fp64_lessEqual a b =
     float_less_equal (fp64_to_float a) (fp64_to_float b)`;;

let fp64_greaterThan_def = cake_define
  `fp64_greaterThan a b =
     float_greater_than (fp64_to_float a) (fp64_to_float b)`;;

let fp64_greaterEqual_def = cake_define
  `fp64_greaterEqual a b =
     float_greater_equal (fp64_to_float a) (fp64_to_float b)`;;

let fp64_mul_add_def = cake_define
  `fp64_mul_add mode a b c =
     float_to_fp64 (SND (float_mul_add mode (fp64_to_float a)
                                            (fp64_to_float b)
                                            (fp64_to_float c)))`;;
''',
}
