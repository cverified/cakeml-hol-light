"""Per theory corrections that the translation cannot guess.

ACCESSORS: the record fields that HOL4 declares with ML code
  (add_record_field), so that they are not in a Datatype block
FIELD_OF: the record type of a field name where several record
  types have a field of that name
"""
import os, re

SRC = (os.path.dirname(os.path.dirname(os.path.abspath(__file__))) +
       '/cakeml-src/')


def ocaml_string(text, width=60):
  """the text as the OCaml string literals of a port, one per line
     of the text and split where a line is too long to fit"""
  out = []
  for line in text.split('\n')[:-1] if text.endswith('\n') \
      else text.split('\n'):
    s = line.replace('\\', '\\\\').replace('"', '\\"') + '\\n'
    while len(s) > width:
      k = width
      while k > 1 and s[k-1] == '\\': k -= 1
      out.append('"' + s[:k] + '"'); s = s[k:]
    out.append('"' + s + '"')
  return out


def help_string():
  """compiler's help_string is the quotation of the --help text at
     the head of the source without its first line, which HOL4
     takes with the ML code of help_string_tm.  The port writes the
     text out as an OCaml string and makes the term of it, because
     a string literal of HOL Light holds the characters that are in
     it, and this text has newlines and a backquote in it."""
  src = open(SRC + 'compiler/compilerScript.sml',
             encoding='utf-8').read()
  m = re.search(r'val help_string =.*?\u2018(.*?)\u2019', src, re.S)
  text = m.group(1)
  text = text[text.index('\n') + 1:]
  body = ' ^\n   '.join(ocaml_string(text))
  return ("""
(* HOL4 takes this string from the quotation of the --help text at
   the head of the source, without its first line (the ML code of
   help_string_tm above).  The port writes the text out and makes
   the term of it, because a string literal of HOL Light holds the
   characters that are in it, and this text has newlines and a
   backquote in it. *)

let help_string_def = cake_define
  (mk_eq(`help_string:mlstring`,
         mk_comb(`implode`, mk_string
  (""" + body + "))));;\n")

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
  # combin's flip is its C (the export theories of the targets
  # filter the symbols with flip MEM)
  'flip': 'C',
  # the gcd of HOL4 takes its two arguments one at a time where
  # the one of HOL Light takes a pair (ml/lib/hol4.ml)
  'gcd': 'hol4_gcd',
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
  # labProps hides mem from its parser (its statements use it for
  # a variable of their own), where the field syntax of HOL4 reads
  # the field all the same: the mem of its statements is the one
  # of a labSem state
  'labProps': {'mem': 'labSem_state_mem',
               'mem_fupd': 'labSem_state_mem_fupd'},
}

# THM_ACCESSORS: the accessor that a statement reads a record
# field with, where the overloaded name of the field is a variable
# of the statement itself.  Where the record of the variable is
# known (overrides.FIELD_VAR) that one settles it, which is the
# first thing to try.
THM_ACCESSORS = {
  # the v of this statement is the v of a sem_env three times
  # over, the third of them of the sem_env that extend_env gives
  # (a field of an application, which the record of a variable
  # cannot say)
  ('source_to_flatProof', 'nsAll_extend_env'):
    {'v': 'source_to_flat_environment_v'},
  # this one has a variable compile and a variable compile_oracle,
  # so it is read with the overloads of the field names taken
  # away, and the stack that it updates is the one of a wordSem
  # state (the clock of it is read through the name that HOL4
  # gives that accessor, which keeps its overload)
  ('wordProps', 'get_var_imm_with_const'):
    {'stack': 'wordSem_state_stack'},
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

# THM_RECLITS: the record types of the literals of a statement, in
# the order in which they stand in it, where several record types
# have the fields that they give and what each literal is an
# argument of is the only thing that says which
THM_RECLITS = {
  # the second argument of global_env_inv is an environment of
  # source_to_flat and the fourth a sem_env, and both of the
  # literals give a v and a c
  ('source_to_flatProof', 'global_env_inv_extend'):
    ['source_to_flat_environment', 'sem_env'],
  ('source_to_flatProof', 'invariant_make_varls'):
    ['source_to_flat_environment', 'sem_env'],
  # the build_env that this one builds is a sem_env, and the two
  # literals after it are the environments of source_to_flat that
  # global_env_inv and env_domain_eq take
  ('source_to_flatProof', 'alloc_tags_invariant'):
    ['sem_env', 'source_to_flat_environment',
     'source_to_flat_environment'],
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
  # a tenv is a type environment in the theories about the type
  # system and about the soundness of the inferencer as well
  'typeSound': {'tenv': 'type_env'},
  'typeSysProps': {'tenv': 'type_env'},
  # the environments that weakening is about are type
  # environments, whose v and c a sem_env has as well
  'weakening': {'tenv': 'type_env', 'tenv1': 'type_env',
                'tenv2': 'type_env', "tenv'": 'type_env'},
  'infer_eSound': {'tenv': 'type_env'},
  'infer_eComplete': {'tenv': 'type_env'},
  'envRel': {'tenv': 'type_env'},
  'type_dCanon': {'tenv1': 'type_env', 'tenv2': 'type_env',
                  'tenv': 'type_env'},
  # the machine configuration, the state of labSem and the state
  # of the target that the theory relates: the fields that it
  # reads of them (mem, ffi_names, pc, ...) are the fields of a
  # dozen records, and ffi_names is a variable of a statement of
  # its own as well
  'lab_to_targetProof': {'mc_conf': 'machine_config',
                         's1': 'labSem_state', 't1': 'asm_state'},
  # the hidden state of the monad that linear_scan runs in: the
  # port has two records of that name (the one of the arrays,
  # whose int_beg is a list, and the one of the indices that the
  # monad's define_run makes, whose int_beg is a pair), and the
  # statements are about the first
  'linear_scanProof': {'sth': 'linear_scan_hidden_state',
                       'sthout': 'linear_scan_hidden_state',
                       'sth1': 'linear_scan_hidden_state',
                       'sth2': 'linear_scan_hidden_state'},
  'flat_elimProof': {'env': 'flatSem_environment'},
  'flat_patternProof': {'env1': 'flatSem_environment',
                        'env2': 'flatSem_environment',
                        'env3': 'flatSem_environment',
                        'an_env': 'flatSem_environment',
                        'env': 'flatSem_environment'},
  # t is the state of wordSem and s the one of dataSem in the
  # invariant that these relate them with
  'data_to_word_gcProof': {'t': 'wordSem_state'},
  # s is the state of stackSem and t the one of labSem in the
  # invariant that these relate them with
  # s and s1 are the states of stackSem that this theory relates
  # with the states t, t1 and t2 of labSem (s1 is read with the
  # mdomain, the memory and the be of a stackSem state, and t1 and
  # t2 with the pc, the ptr_reg and the mem of a labSem one)
  'stack_to_labProof': {'s': 'stackSem_state', 't': 'labSem_state',
                        's1': 'stackSem_state', 't1': 'labSem_state',
                        't2': 'labSem_state'},
  # the state that make_init makes is a stackSem state, and the
  # fields that it sets are of several records
  'stack_allocProof': {'s': 'stackSem_state'},
  # t and u are the states of wordSem that state_rel_ext relates
  'data_to_wordProof': {'t': 'wordSem_state', 'u': 'wordSem_state'},
  # the c of the three definitions that have one is the
  # configuration of clos_to_bvl, whose max_app the state of
  # closSem has as well
  # the configuration of clos_to_bvl, whose max_app the state of
  # closSem has as well
  'clos_to_bvlProof': {'c': 'clos_to_bvl_config',
                       "c'": 'clos_to_bvl_config'},
  # the v of genv is the one of the global_env of the file (what
  # FIELD_OF says), of env the one of a sem_env, of comp_map the
  # one of source_to_flat's environment and of the local
  # environments the one of flatSem's
  # the state that these are about is the one of their own
  # semantics, which the overloaded accessors do not say
  'bvlProps': {'s': 'bvlSem_state'},
  # the states that these theories are about, whose clock, code,
  # stack, ffi and compile oracle every other state has as well
  'wordProps': {'s': 'wordSem_state', 's1': 'wordSem_state',
                's2': 'wordSem_state'},
  'bvl_inlineProof': {'s1': 'bvlSem_state', 's2': 'bvlSem_state',
                      't1': 'bvlSem_state', 't2': 'bvlSem_state'},
  'data_to_word_memoryProof': {'s': 'dataSem_state'},
  'source_to_flatProof': {
    'env': 'sem_env',
    'comp_map': 'source_to_flat_environment',
    # senv is the environment of the source that the invariant
    # relates, comp_map2 one of source_to_flat as comp_map is,
    # and e1 and e2 the two sem_envs that extend_env extends
    'senv': 'sem_env',
    # env' is the sem_env of a Recclosure, as env is
    "env'": 'sem_env',
    # gen is the store of the generations of the environments,
    # whose generation and next the oracle state of
    # semanticPrimitives has as well
    'gen': 'environment_generation_store',
    # c is the configuration of source_to_flat, whose envs and
    # next several records have (the c of orac_rel_inner is a
    # state of flatSem, which FIELD_VAR_DEF says)
    'c': 'source_to_flat_config',
    'comp_map2': 'source_to_flat_environment',
    # the extend_env of this theory is source_to_flat's, so the
    # two environments that nsAll_extend_env is about are its
    'e1': 'source_to_flat_environment',
    'e2': 'source_to_flat_environment',
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
  # the exp_size of the induction principles of these two is the
  # one of bvi, the language that they are about (flatLang has an
  # exp as well, and it is the last theory of their scope that
  # has one)
  'bvi_tailrecProof': {'exp_size': 'bvi'},
  'bvi_tmcProof': {'exp_size': 'bvi'},
  # the exp_size of the induction principle of this one is bvl's,
  # the language of the evaluate that it is about
  'bvl_to_bviProof': {'exp_size': 'bvl'},
  # the prog_size of the relation of dataSem's evaluate is the one
  # of dataLang (wordLang has a prog as well)
  'dataSem': {'prog_size': 'dataLang'},
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
  # the s2 of this statement is the state of labSem that the
  # semantics is taken of, where the s2 of the statements about
  # evaluate is the state of stackSem that it gives
  ('stack_to_labProof', 'flatten_semantics'): {'s2': 'labSem_state'},
  # the s1 of these four is a state of the target, where the s1
  # of the theory is one of labSem (the asm_step_nop of the
  # definition is a step of the target machine)
  ('lab_to_targetProof', 'asm_step_nop_def'): {'s1': 'asm_state'},
  ('lab_to_targetProof', 'upd_pc_with_pc'): {'s1': 'asm_state'},
  ('lab_to_targetProof', 'evaluate_nop_steps'): {'s1': 'asm_state'},
  ('lab_to_targetProof', 'asm_step_IMP_evaluate_step_nop'):
    {'s1': 'asm_state'},
  # the env that make_varls is evaluated in is an environment of
  # flatSem, where the env of this theory is a sem_env
  ('source_to_flatProof', 'evaluate_make_varls'):
    {'env': 'flatSem_environment'},
  ('source_to_flatProof', 'invariant_make_varls'):
    {'env': 'flatSem_environment'},
  # the env whose v this one updates is an environment of flatSem,
  # which the annotation of the other side of the equation says
  ('source_to_flatProof', 'env_updated_lem'):
    {'env': 'flatSem_environment'},
  # the c of this definition is the state of flatSem whose compile
  # and compile_oracle it is about, where the c of the theory is
  # the configuration of source_to_flat
  ('source_to_flatProof', 'orac_rel_inner_def'): {'c': 'flatSem_state'},
  # the var_map of env_domain_eq is an environment of
  # source_to_flat, where the v and the c of this theory are
  # the ones of its own global_env
  ('source_to_flatProof', 'env_domain_eq_def'):
    {'var_map': 'source_to_flat_environment'},
  # the s of these two is the state of dataSem whose locals
  # AllocVar cuts and the r the state of wordSem that the
  # evaluate of it gives (the s of the statements about the
  # garbage collector is a gc_state, which has an r and an h of
  # its own)
  ('data_to_word_gcProof', 'AllocVar_thm_gen'):
    {'s': 'dataSem_state', 'r': 'wordSem_state'},
  ('data_to_word_gcProof', 'AllocVar_thm'):
    {'s': 'dataSem_state', 'r': 'wordSem_state'},
  # the t that the evaluate of halt_assum gives is a state of
  # stackSem, where the s of this theory is one of labSem
  ('stack_to_labProof', 'halt_assum_def'): {'t': 'stackSem_state'},
  # the t that the evaluate of the hypothesis of this one gives is
  # a state of stackSem, where the t of the theory is one of
  # labSem (the halt_assum of the definition above says the same
  # of its own t)
  ('stack_to_labProof', 'flatten_call_correct'):
    {'t': 'stackSem_state'},
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
  # compile_pancake matches on the error of errorMonad, which the
  # port writes with the names of that theory (LOCAL_NAMES), so
  # the scan of the source does not see where they come from
  'compiler': ['errorMonad'],
}

# names that the dependency analysis misses, because the CakeML
# sources use them through HOL4 syntax that mentions them only
# indirectly (a record field declared with ML code, say)
ALSO_NEEDED = set([
  # the ~> and <~ of peg are the infixes that its ML code maps to
  # ignoreL and ignoreR, which the dependency scan does not see
  ('peg', 'ignoreL'), ('peg', 'ignoreR'), ('peg', 'wfpeg'),
  # bvl_handleProof's env_rel uses indexedLists' LIST_RELi, which
  # indexedLists is not an ancestor of
  ('indexedLists', 'LIST_RELi'),
  # set_sep's separating conjunction is the overloaded *, and
  # SEP_EXISTS is a binder, so the dependency analysis does not see
  # that the port needs them
  ('set_sep', 'STAR'), ('set_sep', 'SEP_EXISTS'),
  ('set_sep', 'SPLIT'), ('set_sep', 'SEP_T'),
  ('location', 'locnrow'), ('location', 'locncol'),
  # the tail recursion of the bignum library: mc_multiword builds
  # its functions with the ML of mc_tailrecLib, which the port
  # mirrors (ml/lib/mc_tailrec.ml), so the scan of the sources
  # does not see that it needs these four
  ('tailrec', 'TAILREC'), ('tailrec', 'TAILREC_PRE'),
  ('tailrec', 'SHORT_TAILREC'), ('tailrec', 'SHORT_TAILREC_PRE'),
  # the factorial of mc_multiword, which HOL4 defines with a
  # measure and the step function of its mc_use_fac calls (the
  # example of the deep embedding that produces a Rec)
  ('mc_multiword', 'mc_fac'), ('mc_multiword', 'mc_fac_pre'),
  # the error of errorMonad is the result type of Pancake's static
  # check, which compiler's compile_pancake matches on; the port
  # declares the check itself, so the scan only sees the two
  # constructors
  ('errorMonad', 'error'), ('errorMonad', 'return'),
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
  # the C of combinTheory, which relationTheory hides from HOL4's
  # parser: a statement that means the combinator writes combin$C
  # and one that writes a bare C means a variable of its own, so
  # the qualified name is a constant of the library layer that the
  # cake_hide of C does not touch
  ('combin', 'C'): 'hol4_C',
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
  # While's TAILREC is in the library layer by hand already
  ('tailrec', 'TAILREC'): 'tailrec_TAILREC',

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
  # the toString of a number is ASCIInumbers' num_to_dec_string
  # (mlint has a toString of its own, so the port qualifies the
  # name, and the qualified one is not the constant)
  ('simpleSexpParse', 'toString'): 'num_to_dec_string',
  # mkNT is the ML overload of simpleSexp for INL, which the port
  # does not see (the one of gram is an Overload block)
  ('simpleSexpPEG', 'mkNT'): 'INL',
  ('simpleSexpParse', 'mkNT'): 'INL',
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
  # the values of bvi_tailrecProof are bviSem's, which are the
  # ones of bvlSem (dataSem is not an ancestor of it, and in the
  # one namespace of the port its v comes later); nothing in
  # env_rel says the type, and its sibling op_id_val, which the
  # type of its result says it for, has bvlSem's
  ('bvi_tailrecProof', 'Number'): 'bvlSem_Number',
  ('bvi_tailrecProof', 'v_to_list'): 'bvlSem_v_to_list',
  # the error and the return of compile_pancake's match are the
  # constructors of errorMonad's error, which is the result type
  # of Pancake's static check (peg has an error of its own, and
  # several theories of the port a return)
  ('compiler', 'error'): 'errorMonad_error',
  ('compiler', 'return'): 'errorMonad_return',
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

# the variables of the statement of a theorem that hold an
# integer, where nothing in the statement says so: the port writes
# the numerals that they are compared with as integers then.  The
# entries come from what HOL Light says of a statement that it
# cannot typecheck ("n cannot have type num and int
# simultaneously"), which tools/mkintvars.py turns into this
# table.
# the statements whose type variables the port leaves out: HOL4
# unifies the type variables that a statement writes and HOL Light
# does not, so a statement about two states of types ('a,'b) and
# ('c,'d) whose fields have to agree does not typecheck there.
# Without the annotations HOL Light infers the types, which are
# the ones that HOL4 gives the theorem.
# a name that one statement means another constant by: HOL4's
# set_relationTheory has a domain and a range of a relation, which
# the port cannot have under those names (sptree's domain is what
# the port means by domain everywhere else), and HOL4's GSPEC
# takes a function to a pair while HOL Light's takes a predicate.
# The library layer has them under a name of their own and the
# statements that mean them say so here.
THM_NAMES = {
  ('misc', 'domain_rrestrict_subset'): {'domain': 'set_relation_domain'},
  ('misc', 'range_rrestrict_subset'): {'range': 'set_relation_range'},
  # HOL4's GSPEC takes a function to a pair of an element and a
  # condition, where HOL Light's takes the predicate itself, so
  # the library layer has HOL4's under a name of its own
  ('misc', 'GSPEC_o'): {'GSPEC': 'hol4_GSPEC'},
  ('cmlNTProps', 'IMAGE_GSPEC1'): {'GSPEC': 'hol4_GSPEC'},
  ('cmlNTProps', 'BIGUNION_singletons'): {'GSPEC': 'hol4_GSPEC'},
  ('gramProps', 'GSPEC_INTER'):
    {'GSPEC': 'hol4_GSPEC', 'S': 'hol4_S'},
  # the S of HOL4's combinTheory, which the port has under a name
  # of its own because a source uses the name for a variable
  ('word_allocProof', "LET_FORALL_ELIM'"): {'S': 'hol4_S'},
}

# the statements whose annotations say the same type with other
# type variables, which HOL4 unifies and HOL Light cannot (a type
# variable that a quotation writes is rigid there): the port writes
# the type variables of the first annotation of a type operator in
# every other annotation of it, which is the type that HOL4 gives
# the theorem.  THM_NO_TYVARS leaves such an annotation out
# instead, which loses the record type with it.
THM_TYVARS = set([
  # the two states of these are one state in HOL4: the result of
  # the do_app of the one is compared with a value of the other
  ('bvlProps', 'do_app_Rval_swap'),
  ('bvlProps', 'do_app_Rerr_swap'),
])

THM_NO_TYVARS = set([
  # the state of this one is of 'a and the ffi_state that it is
  # updated with of 'b, which the update unifies in HOL4
  ('evaluateProps', 'evaluate_ffi_intro'),
  ('bvi_inlineProof', 'do_app_state_swap_Rval'),
  ('bvi_inlineProof', 'do_app_state_swap_Rerr'),
  ('bviProps', 'do_app_cfg_swap_Rval'),
  ('bviProps', 'do_app_cfg_swap_Rerr'),
  ('bviProps', 'do_install_adj_orac'),
  ('bviProps', 'evaluate_adj_orac_rel'),
  ('closProps', 'evaluate_adj_orac'),
  ('dataProps', 'cut_state_opt_cc_co_full'),
  ('dataProps', 'cut_cc_co'),
  ('dataProps', 'evaluate_cc_co_only_diff'),
  ('flatProps', 'pmatch_state'),
])

THM_INT_VARS = {
  ('bvlSem', 'do_int_app_eq_some'): ['n2'],
  # the maps of the beginnings and the ends of the intervals of
  # linear_scan hold integers, so the 0 of the the that reads one
  # of them is an integer (the type of get_intervals says it, and
  # the table of the integer arguments of a constant says which
  # arguments are integers themselves and not which hold a map of
  # them)
  ('linear_scanProof', 'get_intervals_beg_less_end'):
    ['beg_in', 'end_in', 'beg_out', 'end_out'],
  ('data_to_word_assignProof', 'INT_EQ_NUM_LEMMA'): ['i'],
  ('data_to_word_assignProof', 'NONNEG_INT'): ['i'],
  ('data_to_word_assignProof', 'do_app_RefByte_eq'): ['i'],
  ('data_to_word_assignProof', 'evaluate_LoadBignum'): ['i'],
  ('data_to_word_assignProof', 'small_int_INT_MIN_MAX'): ['i'],
  ('data_to_word_assignProof', 'state_rel_Number_IMP'): ['i1'],
  ('data_to_word_memoryProof', 'memory_rel_Number_bignum_IMP'): ['i'],
  ('data_to_word_memoryProof', 'small_int_IMP_MIN_MAX'): ['i'],
  ('data_to_word_memoryProof', 'w2i_i2w_IMP'): ['i'],
  # the nout of this one is the number that
  # get_intervals_ct_aux gives, which is an integer: the table of
  # the integer arguments says the arguments of a constant and not
  # the components of its result
  ('linear_scanProof', 'get_intervals_ct_monad_aux_correct'):
    ['n', 'nout'],
  ('linear_scanProof', 'numset_list_add_if_gt_monad_correct'): ['v'],
  ('linear_scanProof', 'numset_list_add_if_lt_monad_correct'): ['v'],
  ('mlint', 'fromString_toString_Num'): ['n'],
  ('source_evalProof', 'Num_11'): ['i'],
}

# the constants of HOL4's own libraries that HOL4 hides from its
# parser (relationTheory and hrealScript both say Parse.hide "C"
# of combinTheory's C), so that a source writes the name for a
# variable of its own: the statements of a file that uses one are
# read with that constant hidden (db.hidden_for), and a
# definition that means the constant writes it qualified
# (mips_target's mips_enc is a combin$C of LIST_BIND)
# a name that HOL4 reads as a variable and the port has as a
# constant of HOL Light: relationTheory hides combinTheory's C
# from the parser of HOL4 (Parse.hide "C"), and HOL4 cannot have a
# constant called val at all, because val is a keyword of SML,
# while HOL Light's words library has one (the number of a word).
# The statements that write these names are read with the constant
# of HOL Light hidden (tools/db.py's hidden_for).
HOL4_HIDDEN = set(['C', 'val'])

# HOL4's Definition foo[schematic] has a free variable in its
# body, which HOL4 makes the first argument of the constant:
# NTproperties defines nullableML and firstSetML for a grammar G
# that the clauses do not take, and cmlNTProps applies them to
# cmlG.  The port adds the variables of the list below as the
# first arguments of the constant, which it has to do itself: the
# port reads a definition as it stands, and a free variable in one
# is a definition that it cannot make (ml/CHEATS.md).
SCHEMATIC = {
  ('NTproperties', 'nullableML_def'): ['G'],
  ('NTproperties', 'firstSetML_def'): ['G'],
}

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
  # the compiler of orac_rel_inner takes the v of
  # semanticPrimitives, where the v of this theory is flatSem's
  ('source_to_flatProof', 'orac_rel_inner_def'):
    {'s_compiler': 'compiler_fun'},
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
  # the statement about that definition says Word (~w) of a word
  # as well
  ('word_bignumProof', 'evaluate_SeqTempImmNot'),
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
  # the parts of a constant are closLang's const_part, which only
  # the Str clause says (the Int, the W64 and the Con of the other
  # clauses are the ones of dataLang's obj in this scope)
  ('clos_constantProof', 'parts_def'),
  ('clos_constantProof', 'to_parts_def'),
  # the value that this builds is closSem's, which the Number, the
  # ByteVector and the Block of the other clauses say and the
  # Word64 of the third one does not (dataSem has one as well)
  ('clos_constantProof', "build_part'_def"),
  # the memop that these give is asm's, which only the clauses of
  # the byte and of the halfword say (the Load and the Store of
  # the other two are the ones of wordLang in this scope)
  ('panLang', 'load_op_def'), ('panLang', 'store_op_def'),
  # the + of the Op Add clause adds machine words, which only the
  # Const clause says (it gives the word of the constant), and the
  # shifts of the Shift clauses then shift a word as well
  ('word_bignumProof', 'eval_exp_def'),
])

# the theory whose constructor a name means in one definition,
# where nothing in the definition says it and HOL4 resolves it by
# its scope (stack_remove's single_stack_free builds the Inst of
# stackLang, and the port is loaded in one namespace, where the
# Inst of wordLang comes later)
CON_OF = {
  ('stack_remove', 'single_stack_free_def'): {'Inst': 'stackLang'},
  # the get_var of this one is dataSem's, which takes the map of
  # the locals itself (the get_var of wordSem and of stackSem take
  # a state, so the port gave var_corr a state as its third
  # argument and the statements about it did not typecheck)
  ('dataProps', 'var_corr_def'): {'get_var': 'dataSem'},
  # the Seq and the Skip of these two statements are the ones of
  # the language that the theory is about, which the evaluate in
  # them does not say: every intermediate language has both, and
  # the port read the Seq of the one as word_bignum's and of the
  # other as wordLang's
  ('data_simpProof', 'evaluate_Seq_Skip'):
    {'Seq': 'dataLang', 'Skip': 'dataLang'},
  ('dataProps', 'Seq_Skip'): {'Seq': 'dataLang', 'Skip': 'dataLang'},
  # the expressions that this one relates are bvi's, and the port
  # read its Var as the one of db_vars and annotated it with the
  # type of that one (the wildcard says the theory of every
  # constructor name of bvi that the port overloads)
  ('bvi_inlineProof', 'exp_rel_inv'): {'*': 'bvi'},
  # the ThunkOp that the do_app of dataSem takes is closLang's (ast
  # has one as well, and it is the closer theory of the two here),
  # which the port annotated the operation of the statement with
  ('data_to_word_assignProof', 'do_app_AllocThunk'):
    {'ThunkOp': 'closLang'},
  ('word_to_stackProof', 'evaluate_Seq_Skip'):
    {'Seq': 'stackLang', 'Skip': 'stackLang'},
  # the values of these are bvlSem's, which bviSem's evaluate
  # takes: dataSem has a RefPtr and a MutBlock of its own, and the
  # port read those, which made the extras of the definition a
  # list of dataSem's values (tools/bin/types found it)
  ('bvi_tmcProof', 'alloc_hole_has_val_def'):
    {'RefPtr': 'bvlSem', 'MutBlock': 'bvlSem'},
  ('bvi_tmcProof', 'evaluate_cb'): {'RefPtr': 'bvlSem'},
  # the refs that this one relates are closSem's on the left and
  # bvlSem's on the right (the ByteArray of the one takes a flag
  # and of the other does not), and the port wrote the left hand
  # ones out as bvlSem's
  ('clos_to_bvlProof', 'ref_rel_simp'):
    {'ValueArray': 'closSem', 'Thunk': 'closSem',
     'ByteArray': 'closSem'},
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
  # loc_ok says of a word_loc of wordLang that it is a code
  # pointer with the offset zero (the theorems about it filter a
  # list of word_locs with isWord)
  ('data_to_word_gcProof', 'loc_ok_def'): {'Loc': 'wordLang'},
  # mk_loc gives the word_loc of wordLang that a handler of
  # wordSem jumps to, which nothing in its clause says
  ('data_to_word_gcProof', 'mk_loc_def'): {'Loc': 'wordLang'},
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

# the ML code of a source that the port has in OCaml: the key is a
# string of the first ML block of the run that the OCaml replaces,
# the value is (a string of the last block of the run, the OCaml).
# The port writes the OCaml where the source has its ML and drops
# the blocks in between -- they are ported, so there is no reason
# to keep them in a comment
ML_PORTED = {
  # the body of CopyByteStr and of CopyByteAw8 is built by the ML
  # of the source from the term of the copy and a function that
  # gives the variable of an argument
  ('flat_to_clos', 'fun var_fun'):
    ('val checkF',
     open(os.path.dirname(os.path.abspath(__file__)) +
          '/flat_to_clos_check.ml').read()),
  ('word_bignum', 'val Skip_tm'):
    ('val def = mc_use_fac_def',
     open(os.path.dirname(os.path.abspath(__file__)) +
          '/word_bignum_todeep.ml').read()),
}

# definitions that are ported by hand (the text replaces the whole
# translation of the Definition block)
REPLACE = {
  ('compiler', 'help_string_def'): help_string(),
  # HOL4 states the string that EVAL computes from the git commit
  # of CakeML, the one of HOL4, the version of PolyML and the time
  # of the build; a source level port cannot have any of the four,
  # so it states the expression that HOL4 evaluates, with the
  # three versions absent and the date the empty string
  ('compiler', 'current_build_info_str_def'): r"""
let current_build_info_str_def = cake_define
  `current_build_info_str =
     (let commit = print_option (implode "CakeML:")
                     (NONE:mlstring option) in
     let hol = print_option (implode "HOL4:  ")
                 (NONE:mlstring option) in
     let poly = print_option (implode "PolyML:")
                  (NONE:mlstring option) in
       mlstring_concat
         [implode "The CakeML compiler\n\n";
          implode "Version details:\n"; implode "";
          implode "\n"; commit; hol; poly])`;;
""",
  # HOL4 builds the bodies of these two with the ML function
  # check1 of the source file, which takes the term of the copy
  # and a function that gives the variable of an argument: the
  # port writes out what check1 computes (the variable of the
  # argument n of CopyByteStr is Var t (2 - n) and the one of
  # CopyByteAw8 is Var t (4 - n))
  ('flat_to_clos', 'CopyByteStr_def'): r"""
let CopyByteStr_def = cake_define
  (mk_eq (`(CopyByteStr (t:tra)):closLang_exp`,checkT));;
""",
  ('flat_to_clos', 'CopyByteAw8_def'): r"""
let CopyByteAw8_def = cake_define
  (mk_eq (`(CopyByteAw8 (t:tra)):closLang_exp`,checkF));;
""",
  # the compiler that the oracle relation takes is a compiler_fun,
  # whose v is the one of semanticPrimitives; the port expands the
  # abbreviation in the theory that uses it, where v is flatSem's
  ('source_to_flatProof', 'orac_rel_inner_def'): r'''
let orac_rel_inner_def = cake_define
  `orac_rel_inner dec s (s_compiler:compiler_fun) (g:dec list->dec
  list) c <=>
     (!k env_id state_v decs. eval_oracle_state_oracle s k =
       (env_id,state_v,decs) ==>
         (let x = THE (dec state_v) in
         let f_decs = SND (inc_compile_prog env_id (FST x) (g decs))
           in install_config_compile_oracle
         c k = (SND x,f_decs) /\
         (~(s_compiler (env_id,state_v,decs) = NONE) ==>
             (?bytes words f_st st_v2. install_config_compile
             c (SND x) f_decs = SOME (bytes,words,f_st) /\
             s_compiler (env_id,state_v,decs) = SOME
               (st_v2,bytes,words) /\
             (!x2. dec st_v2 = SOME x2 ==> SND x2 = f_st)))))`;;
''',
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
  # the word of the immediate is the one of the state, which HOL4
  # ties by typechecking the clauses together where the port
  # typechecks each of them on its own (the pre version of the
  # source says the types, and this says the same ones)
  ('word_bignumProof', 'eval_ri_def'): r'''
let eval_ri_def = cake_define_list
  [`eval_ri (s:'a word_bignumProof_state) (Reg r) =
      eval_exp s ((Var r):'a wordLang_exp)`;
   `eval_ri (s:'a word_bignumProof_state) (Imm (w:'a word)) = w`];;
''',
  # the ~ of HOL4 is the complement of a word as well as the
  # negation of a truth value, which the port can only tell from
  # the type: here it is the word one (word_1comp)
  ('multiword', 'single_sub_def'): r'''
let single_sub_def = cake_define
  `single_sub (x:'a word) (y:'a word) c =
     single_add x (word_1comp y) c`;;
''',
  # HOL4 states the list that EVAL computes for the expression
  # below, in which the type and the configuration are free (the
  # names of the stubs depend on neither, or EVAL could not have
  # computed the list); the port states the expression, with the
  # two of them instantiated, which is the same list
  ('data_to_wordProof', 'stubs_fst_def'): r'''
let stubs_fst_def = cake_define
  `stubs_fst = MAP FST (data_to_word_stubs (:1)
                 (ARB:data_to_word_config))`;;
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
  # the state variables that ML code makes with a type that it
  # computes from the type of an evaluate: the state of the
  # semantics that the theorems of the file are about
  ('bvi_tailrecProof', 's'): "(s:(num#'c,'ffi) bviSem$state)",
  ('bvi_tailrecProof', 's1'): "(s:('c,'ffi) bviSem$state)",
  ('source_to_flatProof', 's'):
    "(s:'ffi semanticPrimitives$state)",
}

NOT_YET = {
  # the two command line drivers of the compiler binary: they read
  # the input and write the output of the binary, so their type is
  # the file system of the basis library (fsFFI's IO_fs), which
  # needs the characteristic formulae of HOL4's cfHeapsBase, and
  # the port has neither.  `compiler$compile`, which the
  # correctness theorem is about, does not use them
  ('compiler', 'full_compile_64_def'):
    'the file system of the basis library, which the port does'
    '\nnot have (add_stdout, add_stderr, fastForwardFD)',
  ('compiler', 'full_compile_32_def'):
    'the file system of the basis library, which the port does'
    '\nnot have (add_stdout, add_stderr, fastForwardFD)',
  # the step functions of the tail recursive versions of the
  # unification algorithm, which HOL4 makes with ML code
  # (tcallify_th of tcallUnifLib turns the equation of a function
  # into the step function of a TAILREC): the port cannot run that
  # code, so it declares the four constants (EXTRA_BEFORE below)
  # and ports the seven definitions that use them
  ('unify', 'cvwalk_code_def'): 'tcallify_th makes it with ML code',
  ('unify', 'kcocwl_code_def'): 'tcallify_th makes it with ML code',
  ('unify', 'kcwalkstarwl_code_def'):
    'tcallify_th makes it with ML code',
  ('unify', 'cunify_code_def'): 'tcallify_th makes it with ML code',
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
  # the step functions of the tail recursions of the unification
  # algorithm: HOL4 builds the body of each with the ML code of the
  # source (tcallify_th, which turns the equation of a function
  # into the step function of a TAILREC), so the port declares the
  # constant with the type that the TAILREC below uses it at and
  # says nothing about its value (see PENDING.md)
  ('unify', 'cvwalk_code_def'): r"""
cake_declare "cvwalk_code" `:infer_t spt -> num -> num + infer_t`;;
""",
  ('unify', 'kcocwl_code_def'): r"""
cake_declare "kcocwl_code"
  `:infer_t spt -> num -> kcockont -> kcockont + bool`;;
""",
  ('unify', 'kcwalkstarwl_code_def'): r"""
cake_declare "kcwalkstarwl_code"
  `:infer_t spt -> bool#infer_t list#kclkont list ->
    (bool#infer_t list#kclkont list) + infer_t list`;;
""",
  ('unify', 'cunify_code_def'): r"""
cake_declare "cunify_code"
  `:(infer_t spt)#kcunifkont ->
    ((infer_t spt)#kcunifkont) + (infer_t spt)option`;;
""",
  # the basis program: HOL4 computes the list of its declarations
  # with the ML code of its translator (basisProg, which is out of
  # the scope of the port), so the port declares the constant and
  # says nothing about its value -- which is all that the
  # definitions below need of it
  ('compiler', 'compile_64_def'): r'''
cake_declare "basis" `:dec list`;;
''',
  # the three entry points of Pancake that the compiler of Pancake
  # goes through: Pancake is a second source language of the same
  # backend, which the CakeML correctness theorem does not mention,
  # so its parser, its static checker and its own backend are
  # outside the port (only its abstract syntax, panLang, is in,
  # because the definitions below have it in their type); the port
  # declares the three with the type that they are used at and
  # says nothing about their value
  ('compiler', 'compile_pancake_def'): r'''
cake_declare "parse_topdecs_to_ast"
  `:string -> (('a)decl)list + (mlstring#locs)list`;;
cake_declare "static_check"
  `:(('a)decl)list -> (1,staterr)errorMonad_error#(staterr)list`;;
cake_declare "pan_compile_tap"
  `:('a)asm_config -> backend_config -> (('a)decl)list ->
    ((((8)word)list#(('a)word)list#backend_config)option)#
    (mlstring)app_list`;;
''',
  # the asm configuration of a target: the one field of it that
  # is not data is the encoder, which needs a machine model of
  # HOL4 (x64_step and the five others), and those are not part
  # of the CakeML sources, so the six encoder theories are
  # outside the port (tools/excluded.txt).  The port declares the
  # six constants with the type that the command line of the
  # compiler uses them at and says nothing about their value.
  # (The configuration of the backend, `<target>_backend_config`,
  # is data, and is a definition of the port, in the file of the
  # target that HOL4 has it in.)
  ('compiler', 'parse_target_64_def'): r'''
cake_declare "x64_config" `:(64)asm_config`;;
cake_declare "arm8_config" `:(64)asm_config`;;
cake_declare "mips_config" `:(64)asm_config`;;
cake_declare "riscv_config" `:(64)asm_config`;;
cake_declare "arm7_config" `:(32)asm_config`;;
cake_declare "ag32_config" `:(32)asm_config`;;
''',
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
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "wordSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nfix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl fix_clock_IMP <> `T` then
  cake_term_facts := fix_clock_IMP :: (!cake_term_facts);;
''',
  ('flatSem', 'evaluate_def'): r'''
let fix_clock_IMP =
  try prove
   (`!s x s1 res. flatSem_fix_clock s x = (s1,res)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "flatSem_state") THEN
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "flatSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nfix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl fix_clock_IMP <> `T` then
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
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "bvlSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nfix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl fix_clock_IMP <> `T` then
  cake_term_facts := fix_clock_IMP :: (!cake_term_facts);;
''',
  ('bviSem', 'evaluate_def'): r'''
let fix_clock_IMP =
  try prove
   (`!s x res s1. bviSem_fix_clock s x = (res,s1)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "bviSem_state") THEN
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "bviSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nfix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl fix_clock_IMP <> `T` then
  cake_term_facts := fix_clock_IMP :: (!cake_term_facts);;
''',
  ('dataSem', 'evaluate_def'): r'''
let fix_clock_IMP =
  try prove
   (`!s x res s1. dataSem_fix_clock s x = (res,s1)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "dataSem_state") THEN
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "dataSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nfix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl fix_clock_IMP <> `T` then
  cake_term_facts := fix_clock_IMP :: (!cake_term_facts);;
''',
  ('closSem', 'evaluate_def'): r'''
let fix_clock_IMP =
  try prove
   (`!s x res s1. closSem_fix_clock s x = (res,s1)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "closSem_state") THEN
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "closSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nfix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl fix_clock_IMP <> `T` then
  cake_term_facts := fix_clock_IMP :: (!cake_term_facts);;
''',
  ('stackSem', 'evaluate_def'): r'''
let fix_clock_IMP =
  try prove
   (`!s x res s1. stackSem_fix_clock s x = (res,s1)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "stackSem_state") THEN
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "stackSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nfix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl fix_clock_IMP <> `T` then
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
}

# a definition of the port that goes after the one of the source
# that it belongs behind
EXTRA_AFTER = {
  # HOL4's Datatype defines the case constant of every type it
  # makes (foo_CASE v f1 ... fn), which the statements of the
  # sources use; the port's define_datatype does not, so the four
  # types whose case constant a statement needs have it here.  The
  # ones of the types that HOL Light has are in ml/lib/hol4.ml
  # (list_CASE, option_CASE, sum_CASE, pair_CASE).
  ('term', 'pair_count_def'): r"""
(* HOL4 termScript.sml: the case constant that its Datatype makes *)

let term_CASE = new_recursive_definition term_RECURSION
  `(term_CASE (term_Var n) vf pf cf = vf n) /\
   (term_CASE (term_Pair t1 t2) vf pf cf = pf t1 t2) /\
   (term_CASE (term_Const c) vf pf cf = cf c)`;;
""",
  ('infer_t', 'id_to_string_def'): r"""
(* HOL4 infer_tScript.sml: the case constant that its Datatype
   makes *)

let infer_t_CASE = new_recursive_definition infer_t_RECURSION
  `(infer_t_CASE (Infer_Tvar_db n) dbf appf uvf = dbf n) /\
   (infer_t_CASE (Infer_Tapp its n) dbf appf uvf = appf its n) /\
   (infer_t_CASE (Infer_Tuvar n) dbf appf uvf = uvf n)`;;
""",
  ('reg_alloc', 'st_ex_FOREACH_def'): r"""
(* HOL4 reg_allocScript.sml: the case constant that its Datatype
   makes for the tag of a register *)

let reg_alloc_tag_CASE =
  new_recursive_definition reg_alloc_tag_RECURSION
  `(reg_alloc_tag_CASE (Fixed n) ff af sf = ff n) /\
   (reg_alloc_tag_CASE Atemp ff af sf = af) /\
   (reg_alloc_tag_CASE Stemp ff af sf = sf)`;;
""",
  ('unify', 'apply_kclkont_def'): r"""
(* HOL4 unifyScript.sml: the case constant that its Datatype makes
   for the continuation of the walk *)

let kclkont_CASE = new_recursive_definition kclkont_RECURSION
  `(kclkont_CASE (DBk n) dbf appf uvf consf = dbf n) /\
   (kclkont_CASE (APPk its n) dbf appf uvf consf = appf its n) /\
   (kclkont_CASE (UVk n) dbf appf uvf consf = uvf n) /\
   (kclkont_CASE (CONSk its n) dbf appf uvf consf = consf its n)`;;
""",
  # HOL4 has w2s and word_to_hex_string in its words theory, which
  # the port cannot: the hand written words layer of the port is
  # loaded before this theory and the two need its n2s.  The
  # statement of presLang$num_to_hex_eq is about this
  # word_to_hex_string, which was a free variable of it before
  ('ASCIInumbers', 'num_to_hex_string_def'): r'''
(* HOL4 wordsScript.sml:76,114: the definitions of w2s and of
   word_to_hex_string, which the port has here because they need
   the n2s of this theory, while the words layer of the port is
   loaded before it *)

let w2s_def = cake_define
  `w2s b f (w:'a word) = n2s b f (w2n w)`;;

let word_to_hex_string_def = cake_define
  `word_to_hex_string = w2s 16 HEX`;;
''',
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
  # the routines of the bignum library are defined from their step
  # function by ML code of HOL4 (mc_tailrecLib), which the port
  # has in OCaml
  'mc_multiword': r'''
needs "lib/mc_tailrec.ml";;
''',

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
