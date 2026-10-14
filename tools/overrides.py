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
  'LEAST': 'minimal',
  'ARB': 'ARB',
  'UNCURRY': 'UNCURRY',
  'I': 'I',
}

ACCESSORS = {
  'location': {'row': 'locnrow', 'col': 'locncol'},
}

FIELD_OF = {
}

# names in the HOL4 libraries that the port does not really need:
# the dependency analysis found them because a CakeML definition
# happens to use a variable of that name
NOT_NEEDED = set([
  ('toto', 'comp'), ('toto', 'cpn'), ('toto', 'lexTO'),
  ('toto', 'lextoto'), ('toto', 'TO_of_LinearOrder'),
])

# names that the dependency analysis misses, because the CakeML
# sources use them through HOL4 syntax that mentions them only
# indirectly (a record field declared with ML code, say)
ALSO_NEEDED = set([
  ('location', 'locnrow'), ('location', 'locncol'),
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
  ('mergesort', 'mergesortN_def'): 'MEASURE (\\(R,n,l). n)',
  ('mergesort', 'mergesortN_tail_def'):
    'MEASURE (\\(negate,R,n,l). n)',
}

# definitions that are ported by hand (the text replaces the whole
# translation of the Definition block)
REPLACE = {
  # as valid_ptree below: the recursive call is under a bounded
  # quantifier, so the port defines the function together with its
  # list version and derives the definition as HOL4 states it
  ('grammar', 'valid_locs_def'): '''
let valid_locs_list_def,valid_locs_def =
  let ths = cake_define
    `(valid_locs (Lf _6) <=> T) /\\
     (valid_locs (Nd (_7,l) children) <=>
        l = merge_list_locs (MAP ptree_loc children) /\\
        valid_locs_list children) /\\
     (valid_locs_list [] <=> T) /\\
     (valid_locs_list (p :: ps) <=>
        valid_locs p /\\ valid_locs_list ps)` in
  let lem = prove
   (`!l. valid_locs_list l <=> ALL valid_locs l`,
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ths; ALL]) in
  ths,
  prove
   (`(valid_locs (Lf _6) <=> T) /\\
     (valid_locs (Nd (_7,l) children) <=>
        l = merge_list_locs (MAP ptree_loc children) /\\
        (!pt. MEM pt children ==> valid_locs pt))`,
    REWRITE_TAC[ths; lem; GSYM ALL_MEM]);;
''',
  # HOL Light's machinery for the admissibility of a recursion cannot
  # see that the recursive call under the quantifier is on a smaller
  # tree, so the port defines the function together with its list
  # version, and derives the definition as HOL4 states it
  ('grammar', 'valid_ptree_def'): '''
let valid_ptree_list_def,valid_ptree_def =
  let ths = cake_define
    `(valid_ptree G (Lf _1) <=> T) /\\
     (valid_ptree G (Nd (nt,l) children) <=>
        nt IN FDOM (grammar_rules G) /\\
        MAP grammar_ptree_head children IN
          FAPPLY (grammar_rules G) nt /\\
        valid_ptree_list G children) /\\
     (valid_ptree_list G [] <=> T) /\\
     (valid_ptree_list G (p :: ps) <=>
        valid_ptree G p /\\ valid_ptree_list G ps)` in
  let lem = prove
   (`!G l. valid_ptree_list G l <=> ALL (valid_ptree G) l`,
    GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[ths; ALL]) in
  ths,
  prove
   (`(valid_ptree G (Lf _1) <=> T) /\\
     (valid_ptree G (Nd (nt,l) children) <=>
        nt IN FDOM (grammar_rules G) /\\
        MAP grammar_ptree_head children IN
          FAPPLY (grammar_rules G) nt /\\
        (!pt. pt IN set_of_list children ==> valid_ptree G pt))`,
    REWRITE_TAC[ths; lem; IN_SET_OF_LIST; GSYM ALL_MEM]);;
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
