"""Per theory corrections that the translation cannot guess.

ACCESSORS: the record fields that HOL4 declares with ML code
  (add_record_field), so that they are not in a Datatype block
FIELD_OF: the record type of a field name where several record
  types have a field of that name
"""

# HOL4 names of notions that HOL Light has under another name
NAME_MAP = {
  'measure': 'MEASURE',
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
  # HOL4's option theory overloads lift2 with OPTION_MAP2
  'lift2': 'OPTION_MAP2',
  # monadsyntax's unit bind, which the overloads of a source that
  # enables the option monad expand to (fromSexp's guard)
  'monad_unitbind': 'OPTION_IGNORE_BIND',
  # the failure of the option monad, which
  # option_monadsyntax.add_option_monadsyntax overloads with NONE
  'fail': 'NONE',
}

# HOL4 type names of types that HOL Light has under another name
TYPE_MAP = {
  # HOL4's one (and its abbreviation unit) is the type with one
  # element, which HOL Light calls 1 (its element is one, as in
  # HOL4)
  'one': '1',
  'unit': '1',
}

ACCESSORS = {
  'location': {'row': 'locnrow', 'col': 'locncol'},
}

# UPDATERS: the field updates that HOL4 declares with ML code
# (add_record_fupdate)
UPDATERS = {
  'location': {'row': 'locn_rowupdate', 'col': 'locn_colupdate'},
  'lexer_fun': {'row': 'locn_rowupdate', 'col': 'locn_colupdate'},
}

# RECORD_OF: the record type of a literal of a definition where the
# fields that it gives do not say which record type it is
RECORD_OF = {
  ('bviSem', 'bvi_to_bvl_def'): 'bvlSem_state',
  # the record of the initial state that define_run makes has the
  # fields of the state record of the monad
  ('reg_alloc', 'reg_alloc_aux_def'): 'ira_state',
  ('linear_scan', 'run_linear_reg_alloc_intervals_def'):
    'i_linear_scan_hidden_state',
  # the environment that env_all_rel relates is a sem_env, of
  # which it writes the c and the v: the global_env of the file
  # has those fields as well
  ('source_to_flatProof', 'env_all_rel'): 'sem_env',
}

# FIELD_DEFAULT: the record type that a field name means where
# several record types in scope have it and nothing says which one.
# A field that has a default is not an overloaded name, so the port
# does not have to rename the variables that are called after it
# (v and c are the fields of sem_env and the names of a great many
# variables of the CakeML sources)
FIELD_DEFAULT = {
  'v': 'sem_env',
  'c': 'sem_env',
  'max_app': 'closSem_state',
}

# the record type of a variable, where one theory uses two record
# types that have a field of the same name and the type of the
# variable is the only thing that says which one it is
# the theories that a source restricts its grammar to with
# set_grammar_ancestry: a name that it writes without a theory in
# front of it is one of these (and of their ancestors), not of
# whichever ancestor has it (backendProof's config is backend's,
# although compiler is an ancestor of it too)
GRAMMAR_ANCESTRY = {
  'backendProof': ['backend', 'backend_common', 'backendProps',
                   'primSemEnv', 'semanticsProps', 'labProps',
                   'source_evalProof'],
}

FIELD_VAR = {
  'typeSoundInvariants': {'tenv': 'type_env'},
  # prim_tenv is the type environment of the primitive types,
  # whose c and t the inferencer's init_config takes over
  'infer': {'prim_tenv': 'type_env',
            'primTypes$prim_tenv': 'type_env'},
  # a tenv is a type environment in the theories about the
  # inferencer, and an env an environment of flatSem in the
  # ones about the flat language
  'inferProps': {'tenv': 'type_env'},
  'envRel': {'tenv': 'type_env'},
  'type_dCanon': {'tenv1': 'type_env', 'tenv2': 'type_env',
                  'tenv': 'type_env'},
  'flat_elimProof': {'env': 'flatSem_environment'},
  'flat_patternProof': {'env1': 'flatSem_environment',
                        'env2': 'flatSem_environment',
                        'env': 'flatSem_environment'},
  # t is the state of wordSem and s the one of dataSem in the
  # invariant that these relate them with
  'data_to_word_gcProof': {'t': 'wordSem_state'},
  # s is the state of stackSem and t the one of labSem in the
  # invariant that these relate them with
  'stack_to_labProof': {'s': 'stackSem_state', 't': 'labSem_state'},
  # the state that make_init makes is a stackSem state, and the
  # fields that it sets are of several records
  'stack_allocProof': {'s': 'stackSem_state'},
  # t and u are the states of wordSem that state_rel_ext relates
  'data_to_wordProof': {'t': 'wordSem_state', 'u': 'wordSem_state'},
  # the c of the three definitions that have one is the
  # configuration of clos_to_bvl, whose max_app the state of
  # closSem has as well
  'clos_to_bvlProof': {'c': 'clos_to_bvl_config'},
  # the v of genv is the one of the global_env of the file (what
  # FIELD_OF says), of env the one of a sem_env, of comp_map the
  # one of source_to_flat's environment and of the local
  # environments the one of flatSem's
  # the state that these are about is the one of their own
  # semantics, which the overloaded accessors do not say
  'bvlProps': {'s': 'bvlSem_state'},
  'source_to_flatProof': {
    'env': 'sem_env',
    'comp_map': 'source_to_flat_environment',
    "env_v_local'": 'flatSem_environment',
    'flat_env': 'flatSem_environment'},
}

# SIZE_OF: the theory of the type of a size function that a
# theory writes without one, where the scope of the theory does
# not give the one that HOL4 means (closProps is about the exp of
# closLang, and the last theory of its scope that has an exp is
# flatLang)
SIZE_OF = {
  'closProps': {'exp_size': 'closLang'},
}

# CON_BODY: the theory of a constructor in the _body_ of a
# clause, where the pattern of the same clause means the one of
# another theory with that name.  The evaluate of wordSem and of
# stackSem matches on the Break and the Continue of the language
# and gives the ones of its own result type; '*' stands for every
# constructor name of the theory.
CON_BODY = {
  ('wordSem', 'evaluate_def'): {'*': 'wordSem'},
  ('stackSem', 'evaluate_def'): {'*': 'stackSem'},
}

# FIELD_VAR_DEF: the same for one definition, where the theory
# uses the name for another record there (the s of
# stack_to_labProof is the state of stackSem everywhere except in
# make_init, which builds one out of a state of labSem)
FIELD_VAR_DEF = {
  ('stack_to_labProof', 'make_init_def'): {'s': 'labSem_state'},
  # the var_map of env_domain_eq is an environment of
  # source_to_flat, where the v and the c of this theory are
  # the ones of its own global_env
  ('source_to_flatProof', 'env_domain_eq_def'):
    {'var_map': 'source_to_flat_environment'},
  # the t that the evaluate of halt_assum gives is a state of
  # stackSem, where the s of this theory is one of labSem
  ('stack_to_labProof', 'halt_assum_def'): {'t': 'stackSem_state'},
  # the t of memory_assumption is a state of labSem, where the
  # regs of this theory are the ones of stackSem; the s is the
  # variable of the overload read_reg (\r s. s.regs r)
  ('stack_to_labProof', 'memory_assumption_def'):
    {'t': 'labSem_state', 's': 'labSem_state'},
  # the s whose oracle orac_rel_inner reads is the state of an
  # EvalOracle
  ('source_to_flatProof', 'orac_rel_inner_def'):
    {'s': 'eval_oracle_state'},
}

FIELD_OF = {
  # both grammar and peg have a field rules
  'pegexec': {'rules': 'peg'},
  'peg': {'rules': 'peg'},
  # source_to_flat's environment has the fields of sem_env
  'source_to_flat': {'v': 'source_to_flat_environment',
                     'c': 'source_to_flat_environment'},
  'source_to_flatProof': {'v': 'global_env',
                          'c': 'global_env'},
  'flatSem': {'v': 'flatSem_environment'},
  # the environment of flatProps' evaluate_match is the one of
  # flatSem, whose v is an association list
  'flatProps': {'v': 'flatSem_environment'},
  # the environment that these proofs are about is flatSem's,
  # whose v is an association list
  'flat_to_closProof': {'v': 'flatSem_environment'},
  'typeSystem': {'v': 'type_env',
                 'c': 'type_env'},
  'clos_to_bvl': {'max_app': 'clos_to_bvl_config'},
}

# names in the HOL4 libraries that the port does not really need:
# the dependency analysis found them because a CakeML definition
# happens to use a variable of that name
# the names that the port takes from a HOL4 library theory, where
# it only needs a part of it: the other definitions of the theory
# are not in the port's namespace at all (of regexp_compiler the
# port only needs the vector that CakeML's mlvector is about)
ONLY_NAMES = {
  'regexp_compiler': set(['vector', 'Vector', 'sub_def', 'sub',
                          'length_def', 'length']),
  # of simpleSexp the port needs the s-expressions that fromSexp
  # reads the CakeML abstract syntax from, not the parser of them
  'simpleSexp': set(['sexp', 'SX_CONS', 'SX_SYM', 'SX_NUM',
                     'SX_STR', 'destSXNUM_def', 'destSXNUM',
                     'destSXSYM_def', 'destSXSYM',
                     'destSXCONS_def', 'destSXCONS',
                     'strip_sxcons_def', 'strip_sxcons',
                     'sxMEM_def', 'sxMEM',
                     'dstrip_sexp_def', 'dstrip_sexp',
                     'arb_sexp_def', 'arb_sexp',
                     # the empty s-expression list, which the
                     # brackets of an s-expression list end in
                     'nil']),
}

NOT_NEEDED = set([
  # CakeML's mlint has its own toString and fromString
  ('integer_word', 'toString'), ('integer_word', 'fromString'),
  ('toto', 'comp'), ('toto', 'cpn'), ('toto', 'lexTO'),
  ('toto', 'lextoto'), ('toto', 'TO_of_LinearOrder'),
  # of regexp_compiler the port only needs the vector that
  # mlvector is about, not the sets of a regular expression
  ('regexp_compiler', 'union'), ('regexp_compiler', 'set'),
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
  # comparison's num_cmp is an overload of ternaryComparisons'
  # num_compare, which HOL4 reaches through toto
  ('ternaryComparisons', 'num_compare'),
  # HOL4 declares the field updates of locn with ML code
  ('location', 'locn_rowupdate'), ('location', 'locn_colupdate'),
  # clos_to_bvl's init_code uses sptree$fromList and
  # bvi_inlineProof's cache_code_labels sptree$toList, which the
  # dependency analysis took for the ones of llist
  ('sptree', 'fromList'),
  ('sptree', 'toList'),
])

# the name that the port gives a constant where the usual rules
# would give it one that is taken: llist's fromList is one of the
# hand written constants of ml/lib, so sptree's needs a name of
# its own
RENAME = {
  ('sptree', 'fromList'): 'sptree_fromList',
  ('sptree', 'toList'): 'sptree_toList',
  # comparison overloads these with the constructors of the
  # ordering of ternaryComparisons, which the port has under the
  # names that HOL4 gives them there
  ('comparison', 'Less'): 'LESS',
  ('comparison', 'Equal'): 'EQUAL',
  ('comparison', 'Greater'): 'GREATER',
  # HOL4's optionTheory overloads assert with OPTION_GUARD, which
  # the library layer has; the port writes that name, because
  # asmSem and labSem have an assert of their own and HOL Light
  # resolves a name over the whole namespace
  ('cmlPEG', 'assert'): 'OPTION_GUARD',
  ('cmlPtreeConversion', 'assert'): 'OPTION_GUARD',
  ('fromSexp', 'assert'): 'OPTION_GUARD',
}

# the same for a constant whose name a type of the same theory
# has as well: the type keeps the name, which HOL Light holds
# apart from the names of the constants
RENAME_CONST = {
  # the semantics of every intermediate language is called
  # semantics, and the one of CakeML itself is in the theory
  # semantics, so the port cannot keep that name for the
  # constant: the definition would be parsed with the overloads
  # that the other theories declared for theirs before it
  ('semantics', 'semantics'): 'semantics_semantics',
}

# the constant that a name means in one theory of the port, where
# the name is one of the hand written library layer as well (the
# fromList of data_to_word and flat_pattern is sptree's, the one
# of the semantics theories is llist's)
LOCAL_NAMES = {
  ('bvi_inlineProof', 'toList'): 'sptree_toList',
  # the stack that this measures is the one of wordSem (the port
  # gives wordSem's stack_size the plain name), and nothing in
  # the invariant says so
  # (a CON_OF for the same name does not work: the branch for a
  # size function looks the type `stack` up, which is dataSem's)
  ('data_to_word_gcProof', 'stack_size'): 'stack_size',
  # the v_rel of source_to_flatProof's result_rel and the Eval of
  # word_bignumProof's Corr are the ones of their own theory; the
  # clause says nothing about the type (every proof theory has a
  # v_rel, and ast has an Eval of its own)
  ('source_to_flatProof', 'v_rel'): 'source_to_flatProof_v_rel',
  # the id of source_evalProof's v_rel is a variable of the rule,
  # and linear_scanProof overloads id with a constant of its own,
  # which HOL Light (one namespace) reads it as
  ('source_evalProof', 'id'): "id'",
  ('word_bignumProof', 'Eval'): 'word_bignumProof_Eval',
  ('data_to_word', 'fromList'): 'sptree_fromList',
  ('flat_pattern', 'fromList'): 'sptree_fromList',
  ('clos_to_bvl', 'fromList'): 'sptree_fromList',
}

# constants that the port declares itself (cake_declare), which
# the HOL4 sources make with ML code, so that the database knows
# their names: a variable of that name is renamed, as it is for
# any other constant (semantics/ffi has an oracle called oc)
# a datatype that the port takes over although the theory that
# has it is not ported: the constructors and the type of every
# argument, so that the db knows the names (the port writes the
# datatype itself in EXTRA_HEAD)
EXTRA_DATATYPES = {
  # compiler's compile_error has StaticError staterr in it, and
  # staterr is a datatype of Pancake's panStatic, which the port
  # does not have; without it compile_error is polymorphic where
  # HOL4's is not, and the constructors in the match of
  # error_to_str are variables
  ('compiler', 'staterr'): [('ScopeErr', ['mlstring']),
                            ('WarningErr', ['mlstring']),
                            ('GenErr', ['mlstring']),
                            ('ShapeErr', ['mlstring'])],
}

EXTRA_DEFS = [
  ('walk', 'vwalk'), ('walkstar', 'walkstar'),
  ('walkstar', 'oc'), ('unifDef', 'unify'),
  ('word_bignum', 'mc_iop_code'),
]

# the HOL Light constant that an infix of HOL4 means where no
# CakeML source overloads it with one of its own; a source that does
# (bvl_to_bvi overloads ++ with SmartAppend) has the port declare
# that overload before its definitions and this one after them, so
# that the files that come after mean this one again
BASE_INFIX_CONST = {'++': 'APPEND'}

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
  ('backend_common', 'small_enough_int_def'),
  ('bvl_const', 'SmartOp2_def'),
  ('clos_op', 'int_op_def'),
  ('integer_word', 'fromString_def'),
  ('semanticPrimitives', 'copy_array_def'),
  # the number of the instruction that the intervals start from
  # is the integer 0
  ('linear_scan', 'get_intervals_ct_def'),
  ('linear_scan', 'get_intervals_ct_monad_def'),
  # the size of a clash tree is an integer (2i and 1i in the
  # first two clauses)
  ('linear_scan', 'size_of_clash_tree_def'),
  # the IntT arm compares the integer v2 with 0
  ('semanticPrimitives', 'do_arith_def'),
  # the elements of the list are the integers of an int spt
  ('linear_scanProof', 'sptree_eq_list_def'),
  # the number of the arguments of a closure is the integer of
  # bvlSem's Number
  ('clos_to_bvlProof', 'unpack_closure'),
])

# the arguments of a definition that hold an integer, where no
# clause of it says so and the clauses would get different types
# (multiword's int_op adds its two arguments in one clause and
# compares them with &1 in another)
INT_ARGS = {
  # the two integers that the bignum operation is applied to
  ('data_to_word_bignumProof', 'int_op_def'): ['i', 'j'],
  ('multiword', 'int_op_def'): ['i', 'j'],
  # n is the number of the instruction, an integer; only the
  # type of P, which is applied to n - 1, says so
  ('linear_scan', 'check_number_property_def'): ['n'],
  ('linear_scan', 'check_number_property_strong_def'): ['n'],
  # n1 and n are the integers that a let or a do notation binds,
  # which the annotation of the argument n does not reach
  ('linear_scan', 'get_intervals_ct_aux_def'): ['n1'],
  ('linear_scan', 'get_intervals_ct_def'): ['n'],
  ('linear_scan', 'get_intervals_ct_monad_aux_def'): ['n1'],
  ('linear_scan', 'get_intervals_ct_monad_def'): ['n'],
  # the beginnings and the ends of the live intervals are
  # integers, which only the array that they come from says
  ('linear_scan', 'numset_list_add_if_lt_monad_def'):
    ['begr', 'v'],
  ('linear_scan', 'numset_list_add_if_gt_monad_def'):
    ['begr', 'v'],
  ('linear_scan', 'linear_reg_alloc_step_pass1_def'):
    ['rbeg', 'rend'],
  ('linear_scan', 'linear_reg_alloc_step_pass2_def'):
    ['rbeg', 'rend'],
}

# definitions whose result is an integer, where no clause of it
# says so (multiword's int_op has a clause whose right hand side
# is the &1 of an integer, which HOL Light reads as a real)
# the type of an argument of a definition, where the definition
# itself says it nowhere and the overloaded names in it are
# resolved by it
ARG_TYPES = {
  # the second state is one of stackSem as well, which the
  # accessors that the two are compared with do not say
  ('stack_removeProof', 'state_rel_def'):
    {'s2': "('a,'c,'ffi)stackSem_state"},
  # the state that this makes the initial one of is stackSem's,
  # which the overloaded accessors in it do not say
  ('stack_allocProof', 'make_init_def'):
    {'s': "('a,'c,'ffi)stackSem_state"},
}

# definitions whose clauses HOL4 writes with <=>, although what
# they give is not a truth value: HOL4's <=> is its = at any
# type, HOL Light's is the one of the booleans
IFF_EQ = set([
  # word_mem_eq gives a bool option
  ('data_to_word_memoryProof', 'word_mem_eq_def'),
])

INT_RESULT = set([
  ('multiword', 'int_op_def'),
  # the size of a clash tree is an integer, which only the
  # numerals of the first two clauses say
  ('linear_scan', 'size_of_clash_tree_def'),
])

# definitions whose <=> is plain equality, not the equality of two
# propositions: HOL4's <=> is its = with another precedence, and a
# source may write it where the two sides are not of type bool,
# which HOL Light's <=> does not allow
IFF_IS_EQ = set([
  # the two sides are of type (α wordLang$prog) option
  ('word_alloc', 'oracle_colour_ok_def'),
])

# definitions in which a ~ without an argument ($~) is the negation
# of an integer, which HOL Light writes --
INT_NEG = set([
  ('mlint', 'fromString_def'),
])

# definitions in which a prefix ~ is the complement of a word, not
# the negation of a proposition
# definitions where ++ is the append of two lists, which the
# source overloads with the choice of a monad: the port writes
# APPEND there, because nothing says the type of the two sides
PLAIN_APPEND = set([
  # the bindings that the two patterns of a pattern list bind
  ('infer', 'infer_p_def'),
])

WORD_NOT = set([
  ('binary_ieee', 'float_negate_def'),
  ('wordLang', 'word_op_def'),
  # these state the word of all ones as ~0w
  ('word_inst', 'op_consts_def'),
  ('data_to_word', 'tag_mask_def'),
  ('data_to_word', 'all_ones_def'),
  ('data_to_word', 'assign_WordFromInt_def'),
  ('data_to_word', 'comp_def'),
  ('word_bignum', 'SeqTempImmNot_def'),
])

# definitions in which the same variable name has different types in
# different clauses, which HOL4 allows (it typechecks every clause on
# its own) and one HOL Light quotation does not; the port writes the
# clauses as separate quotations
CLAUSE_FORM = set([
  ('ast', 'every_exp_def'),
  # a variable of these has one type in the clauses of one of the
  # functions and another in those of the next, which only shows
  # in the right hand sides, where clause_clash does not look
  ('bvi_tmc', 'bvi_to_cb_aux_def'),
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
  # the elements of the vector that are left, which HOL4 gives in
  # the Termination of the definition
  ('mlvector', 'toList_aux_def'): 'MEASURE (\\(vec,n). length vec - n)',
  # the measure is the size of the expression; without it the port
  # searches through the candidates, which takes minutes here
  ('mergesort', 'mergesortN_def'): 'MEASURE (\\(R,n,l). n)',
  ('mergesort', 'mergesortN_tail_def'):
    'MEASURE (\\(negate,R,n,l). n)',
  # the size function of a list of the expressions of a language,
  # which HOL4 writes as the auxiliary size function of the
  # family (exp1_size of bvl, exp2_size of bvi, exp3_size of
  # closLang, exp6_size of flatLang) and the port with list_size
  ('bvi_let', 'compile_def'):
    'MEASURE (list_size bvi_exp_size o SND o SND)',
  ('bvl_to_bvi', 'global_count_sing_def'):
    'MEASURE (\\x. match x with INL e -> bvl_exp_size e'
    ' | INR es -> list_size bvl_exp_size es)',
  ('clos_call', 'calls_def'):
    'MEASURE (list_size closLang_exp_size o FST)',
  ('clos_op', 'lift_exps_def'):
    'MEASURE (\\(xs,n,binds). list_size closLang_exp_size xs)',
  ('clos_to_bvl', 'compile_exps_def'):
    'MEASURE (list_size closLang_exp_size o FST o SND)',
  ('clos_to_bvl', 'compile_exp_sing_def'):
    'MEASURE (\\x. match x with INL (_7,e,_8) -> bvl_exp_size e'
    ' | INR (_9,es,_10) -> list_size closLang_exp_size es)',
  ('clos_to_bvl', 'get_src_names_def'):
    'MEASURE (list_size closLang_exp_size o FST)',
  ('clos_to_bvl', 'get_src_names_sing_def'):
    'MEASURE (\\x. match x with INL (e,_70) -> closLang_exp_size e'
    ' | INR (es,_71) -> list_size closLang_exp_size es)',
  ('flat_to_clos', 'compile_def'):
    'MEASURE (list_size flatLang_exp_size o SND)',
  ('bvlProps', 'bVarBound_def'):
    'MEASURE (list_size bvl_exp_size o SND)',
  ('bvlProps', 'bEvery_def'):
    'MEASURE (list_size bvl_exp_size o SND)',
  ('bvl_handleProof', 'handle_ok_def'):
    'MEASURE (list_size bvl_exp_size)',
  # HOL4's exp2_size is the size function of a list of the
  # expressions of bvi
  ('bvi_inline', 'inline_exp_def'):
    'MEASURE (\\x. match x with INL (_2,e) -> bvi_exp_size e'
    ' | INR (_3,es) -> list_size bvi_exp_size es)',
  ('bvi_inline', 'remove_ticks_exp_def'):
    'MEASURE (\\x. match x with INL e -> bvi_exp_size e'
    ' | INR es -> list_size bvi_exp_size es)',
  # HOL4's exp1_size is the size function of a list of the
  # expressions of bvl, which the port writes with list_size (it
  # numbers the types of a family in another order than HOL4)
  ('bvl_to_bvi', 'compile_exps_def'):
    'MEASURE (list_size bvl_exp_size o SND)',
  ('bvl_to_bvi', 'compile_exps_sing_def'):
    'MEASURE (\\x. match x with INL (n,e) -> bvl_exp_size e'
    ' | INR (n,es) -> list_size bvl_exp_size es)',
  # HOL4's exp_size and pat_size here are the ones of ast (the
  # arguments are the expressions of the source language), which
  # the port resolves to flatLang's and pattern_semantics'
  ('source_to_flat', 'compile_exp_def'):
    'inv_image (<) (\\x. match x with'
    ' INL (t,x,e) -> ast_exp_size e'
    ' | INR (INL (t,x,es)) -> list_size ast_exp_size es'
    ' | INR (INR (INL (t,x,pes))) ->'
    ' list_size (pair_size ast_pat_size ast_exp_size) pes'
    ' | INR (INR (INR (t,x,funs))) ->'
    ' list_size (pair_size mlstring_size'
    ' (pair_size mlstring_size ast_exp_size)) funs)',
}

# definitions whose clauses are one quotation, not one each: the
# clauses only typecheck together, because one of them says what
# the type of the result is and the others have a constructor whose
# name several theories in scope have (bvl_to_bvi's compile_exps
# gives back a bvi expression, which only its Var clause says)
ONE_QUOTATION = set([
  # the result is a bvi expression, which only the Var clause says
  ('bvl_to_bvi', 'compile_exps_def'),
  ('bvl_to_bvi', 'compile_exps_sing_def'),
  # the Var of the right hand side is the one of bvl, which only
  # the other clauses say (db_vars has a Var of its own, and it is
  # the one that HOL Light takes in a clause of its own)
  ('bvl_handle', 'handle_adj_vars_def'),
  # the Writes clause gives an integer, which is what says that
  # the + of the Branch clause is the one of the integers
  ('linear_scan', 'size_of_live_tree_def'),
  # the Jump of the right hand side is the one of asm, which
  # only the LocValue clause says (it annotates the word)
  ('lab_to_target', 'lab_inst_def'),
  # the Seq of the last clause is wordLang's, which only the
  # clause of the empty list says (it gives wordLang's Skip)
  ('data_to_word', 'list_Seq_def'),
  # the clauses of these do not say the type of a variable or of
  # the result on their own, so HOL Light resolves an overloaded
  # name in one clause differently from another; typechecked
  # together they fit (asm's word_cmp compares machine words,
  # which only the clause with <+ in it says)
  ('asm', 'word_cmp_def'),
  ('linear_scan', 'check_startlive_prop_def'),
  ('displayLang', 'display_to_json_def'),
  ('source_to_flat', 'compile_pat_def'),
  ('stack_remove', 'store_list_code_def'),
  ('word_to_stack', 'call_dest_def'),
  ('bvlSem', 'evaluate_def'),
  # the clauses that give LESS and EQUAL say nothing about the
  # type of the result, and asm has constructors of those names
  # as well (the clause with GREATER in it is the one that says
  # that the result is an ordering)
  ('word_cse', 'listCmp_def'),
])

# the theory whose constructor a name means in one definition,
# where nothing in the definition says it and HOL4 resolves it by
# its scope (stack_remove's single_stack_free builds the Inst of
# stackLang, and the port is loaded in one namespace, where the
# Inst of wordLang comes later)
CON_OF = {
  ('stack_remove', 'single_stack_free_def'): {'Inst': 'stackLang'},
  # the right hand sides build flatLang expressions, where the
  # patterns are the constructors of ast, which has the same
  # names ('*' is every constructor name of that theory)
  ('source_to_flat', 'compile_exp_def'): {'*': 'flatLang'},
  # the values that these relations relate are the ones of bvl,
  # which the rules do not say (every intermediate language has
  # a Number and a Word64)
  ('bvi_tmcProof', 'v_rel'): {'*': 'bvlSem'},
  ('bvi_tmcProof', 'ref_rel'): {'*': 'bvlSem'},
  # the Var and the Const of the two clauses that evaluate a
  # wordLang expression are wordLang's (the ones of stackLang
  # and of every other language have the name as well)
  # the result that evaluate gives is stackSem's, which a clause
  # with a match in it does not say (the function that the clause
  # defines is a variable while it is parsed, so nothing fixes
  # the type of Error)
  # the Get and the Set that it evaluates are stackLang's (whose
  # second argument is a register, where wordLang's is an
  # expression), and the Var and the Const of the two clauses
  # that evaluate a wordLang expression are wordLang's
  # the prog_size of the measure is the one of stackLang as well
  # the Break and the Continue that it matches on are
  # stackLang's, where the ones it gives back are stackSem's
  # (CON_BODY), and wordLang has the name as well
  ('stackSem', 'evaluate_def'): {'Var': 'wordLang',
                                 'Const': 'wordLang',
                                 'Break': 'stackLang',
                                 'Continue': 'stackLang',
                                 'FFI': 'stackLang',
                                 'Get': 'stackLang',
                                 'Set': 'stackLang',
                                 'prog_size': 'stackLang',
                                 'CodeBufferWrite': 'stackLang',
                                 'DataBufferWrite': 'stackLang',
                                 'If': 'stackLang',
                                 'Inst': 'stackLang',
                                 'Install': 'stackLang',
                                 'OpCurrHeap': 'stackLang',
                                 'Raise': 'stackLang',
                                 'Seq': 'stackLang',
                                 'Tick': 'stackLang'},
  # these build wordLang programs, whose constructor names
  # linear_scan's live trees and word_bignum's language have too
  ('word_alloc', 'ssa_cc_trans_def'): {'*': 'wordLang'},
  # this gives back a clash tree of reg_alloc, whose constructor
  # names linear_scan's live trees have as well
  ('linear_scan', 'apply_bij_on_clash_tree_def'): {'*': 'reg_alloc'},
  ('word_alloc', 'apply_colour_def'): {'*': 'wordLang'},
  # this builds a clash tree of reg_alloc, whose Seq and Set
  # wordLang has as well
  ('word_alloc', 'get_clash_tree_def'): {'*': 'reg_alloc'},
  ('word_alloc', 'full_ssa_cc_trans_def'): {'*': 'wordLang'},
  # these compare a program with Skip, or give Skip back, where
  # nothing else in the definition says which language it is of
  # (word_bignum's mini and stackLang have a Skip as well)
  ('word_alloc', 'mk_prio_def'): {'Skip': 'wordLang'},
  ('data_to_word', 'StoreEach_def'): {'*': 'wordLang'},
  ('word_simp', 'drop_consts_def'): {'*': 'wordLang'},
  ('word_cse', 'seqs_def'): {'*': 'wordLang'},
  # the Shift and the Div that this canonicalises are asm's
  ('word_cse', 'canonicalArith_def'): {'*': 'asm'},
  # the garbage collector that this picks is stackLang code, and
  # nothing else in the definition says so
  ('stack_alloc', 'word_gc_partial_or_full_def'):
    {'Get': 'stackLang', 'Set': 'stackLang', 'If': 'stackLang',
     'Inst': 'stackLang'},
  # the comparison that this negates is asm's cmp, which the
  # clauses that give one back do not say (Less and Equal are
  # comparison's ordering as well)
  ('stack_to_lab', 'negate_def'): {'*': 'asm'},
  # the exp_size of the measure of these is the size function of
  # the expressions of the theory itself (the measure says
  # nothing about the type, and the port resolved the name to
  # flatLang's); vsgc_free measures closSem$v_size
  ('bvlSem', 'evaluate_def'): {'exp_size': 'bvl'},
  ('closProps', 'contains_App_SOME_def'): {'exp_size': 'closLang'},
  ('closProps', 'vsgc_free_def'): {'v_size': 'closSem'},
  # the stack of dataSem holds a sptree, so this is sptree's
  # toList, not the one of llist
  ('dataSem', 'extract_stack_def'): {'toList': 'sptree'},
  ('dataSem', 'stack_to_vs_def'): {'toList': 'sptree'},
  # the location that this puts in front of the arguments of a
  # call is a word_loc of wordLang
  ('wordSem', 'add_ret_loc_def'): {'Loc': 'wordLang'},
  # the program that this takes apart is stackLang's, which only
  # the annotation on the second component says
  ('stackSem', 'dest_Seq_def'): {'Seq': 'stackLang'},
  # the prog_comp with three arguments in front of the program is
  # stack_remove's, the one without arguments stack_alloc's
  ('stack_to_lab', 'compile_no_stubs_def'):
    {'prog_comp': {3: 'stack_remove', 0: 'stack_alloc'}},
  # these are about the programs of stackLang and of bvl, which
  # the patterns alone do not say
  ('stackProps', 'extract_labels_def'): {'*': 'stackLang'},
  ('bvl_inlineProof', 'exp_rel'): {'*': 'bvl'},
  # these pass from one language to another one that has the same
  # constructor names: the body is of the second one
  ('flat_to_clos', 'compile_def'): {'*': 'closLang'},
  ('word_to_stackProof', 'compile_result_def'): {'*': 'stackSem'},
  ('bvi_tailrecProof', 'op_id_val_def'): {'*': 'bvlSem'},
  ('bvl_to_bviProof', 'adjust_bv_def'): {'*': 'bvlSem'},
  # the term that this encodes an inferencer type as is the one
  # of the unification library
  ('unify', 'encode_infer_t_def'): {'Var': 'term'},
  # this gives back a wordLang program, whose Seq, Set and If
  # word_alloc's live_tree and word_bignum's mini have as well
  ('word_cse', 'word_cse_def'): {'*': 'wordLang'},
  # the comp that this is about is the one of stack_remove
  ('stack_removeProof', 'code_rel_def'): {'comp': 'stack_remove'},
  # the values of the semantics of bvi are bvlSem's
  ('bvi_tailrecProof', 'env_rel_def'): {'*': 'bvlSem'},
  # the op whose size this adds is closLang's
  ('closSem', 'exp_alt_size_def'): {'op_size': 'closLang'},
  # the values that these relations are about are flatSem's
  ('flat_patternProof', 'v_rel'): {'*': 'flatSem'},
  # the program comparison of stack_alloc, whose pass this is
  ('stack_allocProof', 'make_init_def'): {'prog_comp': 'stack_alloc'},
}

# NB: the key of an override is (theory, name of the OCaml
# binding), and the name of the binding lowercases a name that
# starts with a capital and has no other capital in it: the
# override of word_cse's Seqs_def is keyed ('word_cse',
# 'seqs_def').

# definitions whose patterns need the type of their constructor on
# them: the name is one that several theories in scope have, and
# the definition does not say which one it is anywhere else
ANNOTATE = set([
])

# definitions that are ported by hand (the text replaces the whole
# translation of the Definition block)
REPLACE = {
  # the int_beg and int_end arrays of the state hold integers and
  # the others natural numbers, which the port cannot tell from
  # the numerals of the record that gives the initial values
  ('linear_scan', 'run_linear_reg_alloc_intervals_def'): r'''
let run_linear_reg_alloc_intervals_def = cake_define
  `run_linear_reg_alloc_intervals ct k forced moves
     reglist_unsorted invbij nmax =
     run_i_linear_scan_hidden_state
       (linear_reg_alloc_and_extract_coloration ct k forced moves
         reglist_unsorted invbij nmax)
       (mk_i_linear_scan_hidden_state (nmax + 1,0)
         ((nmax + 1,&1):num#int) ((nmax + 1,&1):num#int)
         (nmax + 1,0) (LENGTH moves,(0,(0,0))))`;;
''',
  # HOL4 states the call tree that EVAL computes for the
  # expression below, in which the type and the fields of the
  # configuration other than the two that are given are free
  # (the value does not depend on them, or EVAL could not have
  # computed it); the port states the expression, with the type
  # and the configuration instantiated, which is the same tree
  ('data_to_word', 'AnyArith_call_tree_def'): r'''
let AnyArith_call_tree_def = cake_define
  `AnyArith_call_tree =
     full_call_graph AnyArith_location
       (fromAList (stubs (:1)
          (data_to_word_config_has_longdiv_fupd (K F)
             (data_to_word_config_call_empty_ffi_fupd (K F) ARB))))`;;
''',
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
# the ML values that a source antiquotes into a definition and
# that ML code computes: the port writes the expression that HOL4
# evaluates, which is provably the same value (see PENDING.md)
ANTIQUOTE = {
  # exp_tm is rhs (concl (EVAL ``10n ** exp_for_dec_enc``))
  ('mlint', 'exp_tm'): '10 EXP exp_for_dec_enc',
}

NOT_YET = {
  # the tail recursive versions of the unification algorithm, which
  # HOL4 makes with ML code (tcallify_th of tcallUnifLib turns the
  # equation of a function into the step function of a TAILREC):
  # the port cannot run that code, and nothing outside this part of
  # the file uses what it makes
  ('unify', 'cvwalk_code_def'): 'tcallify_th makes it with ML code',
  ('unify', 'tcvwalk_def'): 'the tail recursion of cvwalk',
  ('unify', 'tcwalk_def'): 'the tail recursion of cwalk',
  ('unify', 'kcocwl_code_def'): 'tcallify_th makes it with ML code',
  ('unify', 'tcocwl_def'): 'the tail recursion of cocwl',
  ('unify', 'kcwalkstarwl_code_def'):
    'tcallify_th makes it with ML code',
  ('unify', 'tcwalkstarwl_def'): 'the tail recursion of cwalkstarwl',
  ('unify', 'tcwalkstar_p1_def'): 'the tail recursion of cwalkstar',
  ('unify', 'tcwalkstar_p2_def'): 'the tail recursion of cwalkstar',
  ('unify', 'cunify_code_def'): 'tcallify_th makes it with ML code',
  ('unify', 'tcunify_def'): 'the tail recursion of cunify',
  # Pancake is a second source language of the same compiler
  # backend, which the CakeML correctness theorem does not mention,
  # so the port does not have the theories that this definition
  # needs (panStatic's static_check, pan_to_target's
  # pan_compile_tap, panPtreeConversion's parse_topdecs_to_ast)
  ('compiler', 'compile_pancake_def'):
    'Pancake, which the port does not have',
  ('compiler', 'compile_pancake_64_def'):
    'Pancake, which the port does not have',
  ('compiler', 'compile_pancake_32_def'):
    'Pancake, which the port does not have',
  # the two command line drivers of the compiler binary, which
  # compile Pancake when the flag says so
  ('compiler', 'full_compile_64_def'):
    'Pancake, which the port does not have',
  ('compiler', 'full_compile_32_def'):
    'Pancake, which the port does not have',
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
# EXTRA_BEFORE: text that the port writes before a definition
EXTRA_BEFORE = {
  # the termination of every evaluate: HOL4 proves it with
  ('wordSem', 'evaluate_def'): r'''
let fix_clock_IMP =
  try prove
   (`!s x res s1. wordSem_fix_clock s x = (res,s1)
                  ==> wordSem_state_clock s1 <=
                      wordSem_state_clock s /\
                      wordSem_state_termdep s1 =
                      wordSem_state_termdep s`,
    REWRITE_TAC[FORALL_PAIR_THM; fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "wordSem_state") THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nfix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

cake_term_facts := fix_clock_IMP :: (!cake_term_facts);;
''',
  ('flatSem', 'evaluate_def'): r'''
let fix_clock_IMP =
  try prove
   (`!s x s1 res. flatSem_fix_clock s x = (s1,res)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "flatSem_state") THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nfix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

cake_term_facts := fix_clock_IMP :: (!cake_term_facts);;
''',
  # imp_res_tac fix_clock_IMP
  ('bvlSem', 'evaluate_def'): r'''
let fix_clock_IMP =
  try prove
   (`!s x res s1. bvlSem_fix_clock s x = (res,s1)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "bvlSem_state") THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nfix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

cake_term_facts := fix_clock_IMP :: (!cake_term_facts);;
''',
  ('bviSem', 'evaluate_def'): r'''
let fix_clock_IMP =
  try prove
   (`!s x res s1. bviSem_fix_clock s x = (res,s1)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "bviSem_state") THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nfix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

cake_term_facts := fix_clock_IMP :: (!cake_term_facts);;
''',
  ('dataSem', 'evaluate_def'): r'''
let fix_clock_IMP =
  try prove
   (`!s x res s1. dataSem_fix_clock s x = (res,s1)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "dataSem_state") THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nfix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

cake_term_facts := fix_clock_IMP :: (!cake_term_facts);;
''',
  ('closSem', 'evaluate_def'): r'''
let fix_clock_IMP =
  try prove
   (`!s x res s1. closSem_fix_clock s x = (res,s1)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "closSem_state") THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nfix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

cake_term_facts := fix_clock_IMP :: (!cake_term_facts);;
''',
  ('stackSem', 'evaluate_def'): r'''
let fix_clock_IMP =
  try prove
   (`!s x res s1. stackSem_fix_clock s x = (res,s1)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "stackSem_state") THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nfix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

cake_term_facts := fix_clock_IMP :: (!cake_term_facts);;
''',
  # the fact that HOL4's Termination of term_ok_int and
  # term_ok_any uses with imp_res_tac: the two arguments that
  # get_bin_args gives are smaller than the expression it took
  # them from
  ('bvi_tailrec', 'term_ok_int_def'): r'''
let _ = size_thms "bvi_exp";;

let exp_size_get_bin_args = prove
 (`!x x1 x2. get_bin_args x = SOME (x1,x2)
             ==> bvi_exp_size x1 + bvi_exp_size x2 < bvi_exp_size x`,
  GEN_TAC THEN
  STRUCT_CASES_TAC
    (ISPEC `x:bvi_exp` (CONJUNCT1 (cases "bvi_exp"))) THEN
  REWRITE_TAC[get_bin_args_def; distinctness "option"] THEN
  STRUCT_CASES_TAC (ISPEC `a1:bvi_exp list` list_CASES) THEN
  REWRITE_TAC[distinctness "option"] THEN
  STRUCT_CASES_TAC (ISPEC `t:bvi_exp list` list_CASES) THEN
  REWRITE_TAC[distinctness "option"] THEN
  STRUCT_CASES_TAC (ISPEC `t':bvi_exp list` list_CASES) THEN
  REWRITE_TAC[distinctness "option"; injectivity "option";
              PAIR_EQ] THEN
  REWRITE_TAC(all_size_thms()) THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

cake_term_facts := exp_size_get_bin_args :: (!cake_term_facts);;
''',
  ('word_bignum', 'generated_bignum_stubs_def'): r'''
(* HOL4 generates the deep embedding of the bignum routines with ML
   code (to_deep of this file), which runs the shallow definitions
   through a translator of its own.  The port cannot run it, so it
   declares the constant that the rest of the file uses and says
   nothing about its value.  *)

cake_declare "mc_iop_code" `:(A)mini`;;
''',
}

# a definition of the port that goes after the one of the source
# that it belongs behind
EXTRA_AFTER = {
  # HOL4 makes unify with new_specification, out of a theorem
  # that says that the tail recursive tunify satisfies the
  # equation for a wellfounded substitution.  The port cannot
  # prove that yet, so it takes the graph of the equation
  # (without the hypothesis, which only says that the recursion
  # stops) and defines the constant as a value of it; HOL4's
  # equation is then a theorem of the second pass.
  ('unifDef', 'ext_s_check_def'): r'''
let UNIFYR_RULES,UNIFYR_INDUCT,UNIFYR_CASES =
  new_inductive_definition
  `(!s t1 t2 v1 v2.
      walk s t1 = term_Var v1 /\ walk s t2 = term_Var v2
      ==> UNIFYR s t1 t2
            (SOME (if v1 = v2 then s
                   else s |+ (v1,term_Var v2)))) /\
   (!s t1 t2 v1.
      walk s t1 = term_Var v1 /\
      (!v2. ~(walk s t2 = term_Var v2))
      ==> UNIFYR s t1 t2 (ext_s_check s v1 (walk s t2))) /\
   (!s t1 t2 v2.
      (!v1. ~(walk s t1 = term_Var v1)) /\
      walk s t2 = term_Var v2
      ==> UNIFYR s t1 t2 (ext_s_check s v2 (walk s t1))) /\
   (!s t1 t2 t1a t1d t2a t2d sx r.
      walk s t1 = term_Pair t1a t1d /\
      walk s t2 = term_Pair t2a t2d /\
      UNIFYR s t1a t2a (SOME sx) /\ UNIFYR sx t1d t2d r
      ==> UNIFYR s t1 t2 r) /\
   (!s t1 t2 t1a t1d t2a t2d.
      walk s t1 = term_Pair t1a t1d /\
      walk s t2 = term_Pair t2a t2d /\
      UNIFYR s t1a t2a NONE
      ==> UNIFYR s t1 t2 NONE) /\
   (!s t1 t2 c1 c2.
      walk s t1 = term_Const c1 /\ walk s t2 = term_Const c2
      ==> UNIFYR s t1 t2 (if c1 = c2 then SOME s else NONE)) /\
   (!s t1 t2 t1a t1d c2.
      walk s t1 = term_Pair t1a t1d /\ walk s t2 = term_Const c2
      ==> UNIFYR s t1 t2 NONE) /\
   (!s t1 t2 c1 t2a t2d.
      walk s t1 = term_Const c1 /\ walk s t2 = term_Pair t2a t2d
      ==> UNIFYR s t1 t2 NONE)`;;

let unify_def = new_definition
  `unify s t1 t2 = @r. UNIFYR s t1 t2 r`;;
''',
}

EXTRA_HEAD = {
  # the datatype of the static errors of Pancake (panStatic's
  # staterr), which compiler's compile_error has in it; Pancake
  # itself is not ported, but compile_error is not Pancake's and
  # error_to_str matches on these constructors
  'compiler': r'''
let staterr_INDUCT,staterr_RECURSION = define_datatype
  "staterr = ScopeErr (mlstring) | WarningErr (mlstring) \
             | GenErr (mlstring) | ShapeErr (mlstring)";;
''',
  # HOL4 makes vwalk, walkstar and oc with a schema
  # (xDefineSchema, under the hypothesis wfs s that the
  # substitution is wellfounded), which HOL Light has no
  # counterpart for: the port takes the graph of the equation as
  # an inductive relation and defines the constant as a value of
  # it (HOL4's equation is then a theorem of the second pass).
  'walk': r'''
let VWALKR_RULES,VWALKR_INDUCT,VWALKR_CASES =
  new_inductive_definition
  `(!s v. FLOOKUP s v = NONE ==> VWALKR s v (term_Var v)) /\
   (!s v t. FLOOKUP s v = SOME t /\ (!u. ~(t = term_Var u))
      ==> VWALKR s v t) /\
   (!s v u r. FLOOKUP s v = SOME (term_Var u) /\ VWALKR s u r
      ==> VWALKR s v r)`;;

let vwalk_def = new_definition
  `vwalk s v = @r. VWALKR s v r`;;
''',
  'walkstar': r'''
let WALKSTARR_RULES,WALKSTARR_INDUCT,WALKSTARR_CASES =
  new_inductive_definition
  `(!s t t1 t2 r1 r2.
      walk s t = term_Pair t1 t2 /\ WALKSTARR s t1 r1 /\
      WALKSTARR s t2 r2
      ==> WALKSTARR s t (term_Pair r1 r2)) /\
   (!s t. (!t1 t2. ~(walk s t = term_Pair t1 t2))
      ==> WALKSTARR s t (walk s t))`;;

let walkstar_def = new_definition
  `walkstar s t = @r. WALKSTARR s t r`;;

(* the occurs check, which HOL4 makes with Hol_reln in the same
   file (walkstarScript.sml) *)

let oc_RULES,oc_INDUCT,oc_CASES =
  new_inductive_definition
  `(!s t v. v IN vars t /\ ~(v IN FDOM s) ==> oc s t v) /\
   (!s t v u t'. u IN vars t /\ vwalk s u = t' /\ oc s t' v
      ==> oc s t v)`;;
''',
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
