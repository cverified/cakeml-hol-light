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
               'mem_fupd': 'labSem_state_mem_fupd',
               # four statements of it have a variable mem and
               # read the mem_domain of a labSem state, which the
               # name of the field would lose with the others
               'mem_domain': 'labSem_state_mem_domain'},
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
  # these read a field through the name of it and have a variable
  # of the name of another field, so the overloads of the field
  # names are taken away and the accessor has to be written out
  # (tools/diag.py finds them: it says which statement applies a
  # name that the port made a variable, where the source reads a
  # field of that name)
  ('backendProof', 'compile_correct_is_safe_for_space'):
    {'ffi_names': 'lab_to_target_config_ffi_names'},
  ('data_to_wordProof', 'compile_semantics'):
    {'be': 'data_to_word_config_be'},
  ('data_to_word_assignProof', 'parts_to_words_NONE'):
    {'has_fp_ops': 'data_to_word_config_has_fp_ops'},
  # the t whose mem this one reads is a state of the target: the
  # bytes_in_mem of the statement takes a memory of bytes, which
  # the mem of an asm_state is and the mem of a labSem state
  # (a memory of word_loc) is not
  ('lab_to_targetProof', 'asm_fetch_NOT_ffi_entry_pcs'):
    {'mem': 'asm_state_mem'},
  ('stack_allocProof', 'inst_correct'):
    {'compile_oracle': 'stackSem_state_compile_oracle',
     'stack': 'stackSem_state_stack'},
  ('stack_removeProof', 'evaluate_init_code'):
    {'compile_oracle': 'stackSem_state_compile_oracle'},
  ('stack_removeProof', 'init_semantics'):
    {'compile_oracle': 'stackSem_state_compile_oracle'},
  ('stack_removeProof', 'make_init_opt_SOME_semantics'):
    {'compile_oracle': 'stackSem_state_compile_oracle'},
  # the stack that state_rel compares is the one of the stackSem
  # state of the two
  ('word_to_stackProof', 'evaluate_wLive'):
    {'stack': 'stackSem_state_stack'},
  ('word_to_stackProof', 'alloc_IMP_alloc'):
    {'stack': 'stackSem_state_stack'},
  ('targetProps', 'ffi_interfer_ok_post_ffi_asm'):
    {'ffi_names': 'machine_config_ffi_names'},
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
  # the compile of the s and the t of this theory is the field of
  # a stackSem state, where a bare compile is the constant of a
  # compiler pass (the port has 28 of those under that name)
  'stack_namesProof': {'s': 'stackSem_state', 't': 'stackSem_state'},
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
  # the s that the read_reg of this one reads is a state of
  # labSem, where the s of the theory is one of stackSem (the
  # port puts the argument into the body of the overload, so the
  # record of that argument is the one it writes the accessor of)
  ('stack_to_labProof', 'FLOOKUP_regs'): {'s': 'labSem_state'},
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
  # the occurs check of walkstar is in the hand written part of
  # that file already (EXTRA_HEAD below), where its rules are
  # closed over the substitution: HOL4 leaves that one free
  ('walkstar', 'oc'),
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
  # exp2_size is the size function that HOL4 generates for a list
  # of the expressions of bvi, which the port calls bvi_exp_size1
  # (tools/port.py writes a size prelude with that name)
  ('bvi_let', 'exp2_size_APPEND'): {'exp2_size': 'bvi_exp_size1'},
  ('bvi_letProof', 'exp_size_APPEND'): {'exp2_size': 'bvi_exp_size1'},
}

# the statements whose annotations say the same type with other
# type variables, which HOL4 unifies and HOL Light cannot (a type
# variable that a quotation writes is rigid there): the port writes
# the type variables of the first annotation of a type operator in
# every other annotation of it, which is the type that HOL4 gives
# the theorem.  THM_NO_TYVARS leaves such an annotation out
# instead, which loses the record type with it.
# the statements of the theorems that HOL4 binds to the value of an
# ML expression, where phase three has done the computation that
# the expression is: the statement is written in HOL4's notation
# and tools/port.py translates it like any other statement of the
# source.  PENDING.md says which of the 454 these are and why the
# rest are still pointers; the proof is a section of the file's
# proof store, under the name of the theorem.
THM_VALUE = {
  # compile_exp_def |> SRULE [compile_sing]: the compiled singleton
  # is a singleton, so the match of compile_exp reduces to its head
  ('bvi_let', 'compile_exp_eq'):
    '!x. compile_exp x = compile_sing [] 0 x',
  # evaluate_env_rel |> Q.SPECL [`xs`,`env`,`s1`,`[]`,`env`,`res`,
  # `s2`,`ys`,`0`] |> GEN_ALL |> SIMP_RULE (srw_ss()) [env_rel_def]:
  # env_rel [] 0 env env is env = DROP 0 env, which is T, so the
  # antecedent that is left is the evaluation and the type error
  # compile_exp_def |> SRULE [compile_eq]: the same for bvl_const,
  # whose compile_exp has no depth to carry
  ('bvl_const', 'compile_exp_eq'):
    '!x. compile_exp x = compile_sing [] x',
  # the same for bvl_const, whose env_rel takes no depth: env_rel
  # [] env env is env = env, so the antecedent that is left is the
  # evaluation and the type error
  ('bvl_constProof', 'compile_thm'):
    '!xs env (s1:(\'c,\'ffi) bvlSem$state) res s2 ys.'
    ' (evaluate (xs,env,s1) = (res,s2)) /\\'
    ' res <> Rerr (Rabort Rtype_error) ==>'
    ' (evaluate (compile [] xs,env,s1) = (res,s2))',
  ('bvi_letProof', 'compile_thm'):
    '!xs env (s1:(\'c,\'ffi) bviSem$state) res s2 ys.'
    ' (evaluate (xs,env,s1) = (res,s2)) /\\'
    ' res <> Rerr (Rabort Rtype_error) ==>'
    ' (evaluate (compile [] 0 xs,env,s1) = (res,s2))',
}

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
  # the i of this one is an integer in the source (`0i`), and
  # nothing else of the statement says a type, so the port read
  # the comparison as one of reals and the statement was false
  ('data_to_word_memoryProof', 'exists_num'): ['i'],
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

# definitions of a family whose clauses overlap in one of the
# functions only: a match is one clause, so it cannot define a
# family (the two functions would share the variables that HOL
# Light's pattern matching makes, and their types clash), and what
# the port writes is the list of clauses of the definition with the
# clauses of the named constants written as one clause with a match
# each.  The text is the comment that goes over the definition.
MATCH_CLAUSES = {
  # the mutual vb_eq_size/vb_eq_size_list of
  # data_to_word_memoryProof, which is the same shape as the do_eq
  # above: the last clause of each catches what the earlier ones
  # have already given a value, and as a list of clauses that is
  # inconsistent (`vb_eq_size refs (Number n1) (Number n2)` is
  # both `SOME (1,n1 = n2)` and `NONE`)
  ('data_to_word_memoryProof', 'vb_eq_size_def'):
    (['vb_eq_size', 'vb_eq_size_list'], """
(* the clauses of the source overlap -- the last one says NONE of a
   pair that an earlier one has already given a value -- and HOL4
   takes the first that matches, so the port writes them as a
   match, which takes the first arm (see ml/lib/define.ml, "A
   definition whose clauses overlap").  As a list of clauses they
   would be inconsistent. *)
"""),
  # the mutual do_eq/do_eq_list of the five semantics: the last
  # clause of each catches the pairs that the earlier ones have
  # already given a value, and the port did not see it (the
  # clauses are written out one by one and the overlap is between
  # two of them, not between a clause and a catch-all of the same
  # shape), so a list of clauses would be inconsistent
  ('dataSem', 'do_eq_def'): (['do_eq', 'do_eq_list'], """
(* the clauses of the source overlap -- a later one says
   Eq_type_error of a pair that an earlier one has already given a
   value -- and HOL4 takes the first that matches, so the port
   writes them as a match, which takes the first arm (see
   ml/lib/define.ml, "A definition whose clauses overlap").  As a
   list of clauses they would be inconsistent. *)
"""),
  ('bvlSem', 'do_eq_def'): (['do_eq', 'do_eq_list'], """
(* the clauses of the source overlap -- a later one says
   Eq_type_error of a pair that an earlier one has already given a
   value -- and HOL4 takes the first that matches, so the port
   writes them as a match, which takes the first arm (see
   ml/lib/define.ml, "A definition whose clauses overlap").  As a
   list of clauses they would be inconsistent. *)
"""),
  ('closSem', 'do_eq_def'): (['do_eq_list'], """
(* the clauses of do_eq_list overlap -- the last one says Eq_val F
   of the two lists that the first two have already given a value
   -- and HOL4 takes the first that matches, so the port writes
   them as a match, which takes the first arm (see ml/lib/define.ml,
   "A definition whose clauses overlap").  As a list of clauses they
   would be inconsistent. *)
"""),
  ('flatSem', 'do_eq_def'): (['do_eq_list'], """
(* the clauses of do_eq_list overlap -- the last one says Eq_val F
   of the two lists that the first two have already given a value
   -- and HOL4 takes the first that matches, so the port writes
   them as a match, which takes the first arm (see ml/lib/define.ml,
   "A definition whose clauses overlap").  As a list of clauses they
   would be inconsistent. *)
"""),
  ('semanticPrimitives', 'do_eq_def'): (['do_eq_list'], """
(* the clauses of do_eq_list overlap -- the last one says Eq_val F
   of the two lists that the first two have already given a value
   -- and HOL4 takes the first that matches, so the port writes
   them as a match, which takes the first arm (see ml/lib/define.ml,
   "A definition whose clauses overlap").  As a list of clauses they
   would be inconsistent. *)
"""),
}

# an explicit termination relation, where HOL Light cannot guess one
# and the HOL4 source does not give one either
# TERMINATION: the tactic that proves the termination condition of
# a definition, written by hand (phase three).  It goes where the
# CHEAT_TAC of the first pass goes; the definition is then made for
# real, and the next run says so, because the cheat list comes out
# of ml/CHEATS.md, which a run writes.
TERMINATION = {
  # the mutual definition of compile_sing and compile_list: the
  # relation that HOL4 gives discharges its conditions once the two
  # size facts of EXTRA_BEFORE are in cake_term_facts, so nothing
  # is left over -- and what the port writes here is the tactic it
  # would prove a leftover with, not a cheat
  ('bvi_let', 'compile_sing_def'): 'TERM_TAC',
}

# the definitions whose termination the port proves with the
# relation that HOL4 gives, handed straight to define_single.  The
# strategy chain of cake_define_gen tries eight strategies before
# the relation, and one of them declares the constant and then
# fails, after which `with Failure _ when not (declared ())` tries
# nothing more and the definition is assumed: with the relation
# first there is no cheat and no axiom.
DEFINE_REL = set([
  # the Let clause compiles the body in an environment that the
  # result of the first recursive call builds, and the measure of
  # HOL4's relation is on the third argument alone, so the nested
  # call's condition does not mention the environment at all.  What
  # the conditions need besides the size theorems is the two facts
  # that EXTRA_BEFORE adds to cake_term_facts below.
  ('bvi_let', 'compile_def'),
  # and the same definition one language down: the Let clause of
  # bvl_const's compile builds the environment of its nested call
  # out of the result of the first one, and the measure of the
  # relation is on the list it compiles, which that does not touch
  ('bvl_const', 'compile_def'),
])

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
  ('bvl_const', 'compile_def'):
    'MEASURE (list_size bvl_exp_size o SND)',
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
  # the Const of Unit (and of the assign_* family below it) is
  # wordLang's: HOL4's Ancestors of data_to_word open wordLang and
  # word_bignum, and word_bignum has a Const of its own (of the
  # term of its deep embedding), which the port read.  Unit was
  # then a term and not an expression, and the first definition
  # that gives it to an Assign had no resolution at all -- the
  # ninety definitions of the file below that line were lost with
  # it (ISSUES.md)
  ('data_to_word', 'unit_def'): {'Const': 'wordLang'},
  # and the Load and the Shift of word_inst's pull_exp: the Op of
  # the clauses above them says wordLang, but these two clauses
  # have nothing else in them, and word_bignum's term has a Load
  # and a Shift of its own
  ('word_inst', 'pull_exp_def'): {'Load': 'wordLang',
                                  'Shift': 'wordLang'},
  # and the Const of op_consts, which is the only constructor of
  # that definition: op_consts was a term of word_bignum and not an
  # expression of wordLang, which the pull_exp below it then could
  # not typecheck at all
  ('word_inst', 'op_consts_def'): {'Const': 'wordLang'},
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
  ('data_to_word_memoryProof', 'update_ref_thm'): r"""
(* the port's own: the steps that the proofs of update_ref_thm and
   of the four update theorems after it take.  A store into the
   element of a reference leaves the heap as good as it was
   (heap_ok_store_el, unused_store_el, roots_ok_iso,
   heap_split_store_ref, gc_kind_store_ref), and an update of the
   references that leaves what the invariant says of every value
   (the three transfers of VA_trans) leaves the invariant of every
   reference that it did not write (bc_ref_inv_update_gen over the
   four arms of bc_ref_inv, with the INJ of f to tell the two
   addresses apart).  The lemmas with gen in the name take the
   transfers as hypotheses, so that the update of a thunk and the
   one of a mutable block can take the same steps *)

(* the rewrites that decide a guard whose pattern is a reference
   (PORTING-GUIDE.md entry 45) *)
let ref_rws =
  let ds = CONJUNCTS (distinctness "bvlSem_ref") in
  injectivity "option" :: distinctness "option" ::
  injectivity "bvlSem_ref" :: ds @ map GSYM ds;;

let LIST_REL_APPEND_IMP = prove
 (`!(P:A->B->bool) xs ys xs1 ys1.
     EVERY2 P (xs ++ xs1) (ys ++ ys1) /\ LENGTH xs = LENGTH ys
     ==> EVERY2 P xs ys /\ EVERY2 P xs1 ys1`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[APPEND; LENGTH] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(ys:B list) = []` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TRY (REWRITE_RULE[APPEND]) THEN
    ASM_REWRITE_TAC[APPEND; ALL2_DEF];
    REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(ISPEC `ys:B list` (cases_of `:(B)list`)) THEN
    REWRITE_TAC[APPEND; LENGTH; ALL2_DEF; HD; TL; NOT_CONS_NIL;
                NOT_SUC; SUC_INJ] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let EVERY2_MEM_MONO = prove
 (`!(P:A->B->bool) Q l1 l2.
     (!x y. MEM (x,y) (ZIP l1 l2) /\ P x y ==> Q x y) /\
     EVERY2 P l1 l2 ==> EVERY2 Q l1 l2`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` (cases_of `:(B)list`)) THEN
  REWRITE_TAC[ZIP; ALL2_DEF; MEM; HD; TL; NOT_CONS_NIL;
              PAIR_EQ] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let reach_refptr = prove
 (cake_as_vars (fun () ->
    `MEM (RefPtr b ptr) stack' ==> reachable_refs stack' refs ptr`),
  REWRITE_TAC[reachable_refs_def] THEN STRIP_TAC THEN
  EXISTS_TAC (cake_as_vars (fun () -> `RefPtr b ptr:dataSem_v`)) THEN
  EXISTS_TAC `ptr:num` THEN
  ASM_REWRITE_TAC[get_refs_def; MEM] THEN
  MESON_TAC[RTC_RULES]);;

let roots_ok_iso = prove
 (`roots_ok roots heap /\
   (!a. isSomeDataElement (heap_lookup a heap2) =
        isSomeDataElement (heap_lookup a heap))
   ==> roots_ok roots heap2`,
  REWRITE_TAC[roots_ok_def] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* the heap after a store of any element whose pointers are
   addresses of the heap *)
let heap_ok_store_el = prove
 (`heap_ok heap limit' /\
   (!ptr u. MEM (gc_shared_Pointer ptr u) ws
            ==> isSomeDataElement (heap_lookup ptr heap)) /\
   (!a. isSomeDataElement (heap_lookup a heap2) =
        isSomeDataElement (heap_lookup a heap)) /\
   heap_length heap2 = heap_length heap /\
   FILTER isForwardPointer heap2 = FILTER isForwardPointer heap /\
   (!xs l d. MEM (DataElement xs l d) heap2
             ==> (DataElement xs l d = DataElement ws l2 d2) \/
                 MEM (DataElement xs l d) heap)
   ==> heap_ok heap2 limit'`,
  REWRITE_TAC[heap_ok_def] THEN STRIP_TAC THEN
  SPLIT_ASM_TAC THEN
  REPEAT CONJ_TAC THEN TRY (SOLVED (ASM_REWRITE_TAC[])) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  W(fun gl ->
    let mm = the_asm (fun c ->
      let bd = snd (strip_forall c) in
      is_imp bd && is_disj (rand bd)) gl in
    let mh = the_asm (fun c -> hd_is "MEM" c &&
      hd_is "DataElement" (el 0 (snd (strip_comb c)))) gl in
    STRIP_ASSUME_TAC (MATCH_MP (SPEC_ALL mm) mh)) THENL
   [(* the element written: its pointers are addresses of their own *)
    RULE_ASSUM_TRY (REWRITE_RULE[injectivity "heap_element"]) THEN
    SPLIT_ASM_TAC THEN
    REPEAT (FIRST_X_ASSUM (fun e ->
      let c = concl e in
      if not (is_eq c) || not (is_var (lhand c)) then fail() else
      SUBST_ALL_TAC e)) THEN
    W(fun gl ->
      let m = the_asm (fun c -> hd_is "MEM" c &&
        hd_is "gc_shared_Pointer" (el 0 (snd (strip_comb c)))) gl in
      let pw = the_asm (fun c ->
        let vs,bd = strip_forall c in
        length vs = 2 && is_imp bd &&
        hd_is "isSomeDataElement" (rand bd)) gl in
      ACCEPT_TAC (MATCH_MP pw m));
    (* an old element of a heap that was good *)
    W(fun gl ->
      let ho = the_asm (fun c ->
        length (fst (strip_forall c)) = 5) gl in
      let md = the_asm (fun c -> hd_is "MEM" c &&
        hd_is "DataElement" (el 0 (snd (strip_comb c)))) gl in
      let mp = the_asm (fun c -> hd_is "MEM" c &&
        hd_is "gc_shared_Pointer" (el 0 (snd (strip_comb c)))) gl in
      ACCEPT_TAC (MATCH_MP ho (CONJ md mp)))]);;

(* and so the one for a store of a RefBlock *)
let heap_ok_store_ws = prove
 (`heap_ok heap limit' /\
   (!ptr u. MEM (gc_shared_Pointer ptr u) ws
            ==> isSomeDataElement (heap_lookup ptr heap)) /\
   (!a. isSomeDataElement (heap_lookup a heap2) =
        isSomeDataElement (heap_lookup a heap)) /\
   heap_length heap2 = heap_length heap /\
   FILTER isForwardPointer heap2 = FILTER isForwardPointer heap /\
   (!xs l d. MEM (DataElement xs l d) heap2
             ==> (DataElement xs l d = RefBlock ws) \/
                 MEM (DataElement xs l d) heap)
   ==> heap_ok heap2 limit'`,
  REWRITE_TAC[RefBlock_def] THEN MATCH_ACCEPT_TAC heap_ok_store_el);;

(* and so the heap after a store of the roots of the new values,
   whose pointers are addresses because the roots are good *)

let heap_ok_store_ref = prove
 (`heap_ok heap limit' /\ roots_ok (rs ++ (r :: roots2)) heap /\
   (!a. isSomeDataElement (heap_lookup a heap2) =
        isSomeDataElement (heap_lookup a heap)) /\
   heap_length heap2 = heap_length heap /\
   FILTER isForwardPointer heap2 = FILTER isForwardPointer heap /\
   (!xs l d. MEM (DataElement xs l d) heap2
             ==> (DataElement xs l d = RefBlock rs) \/
                 MEM (DataElement xs l d) heap)
   ==> heap_ok heap2 limit'`,
  STRIP_TAC THEN
  W(fun gl ->
    let ho = the_asm (hd_is "heap_ok") gl in
    let ro = REWRITE_RULE[roots_ok_def]
               (the_asm (hd_is "roots_ok") gl) in
    let rs = lhand (el 0 (snd (strip_comb
               (concl (the_asm (hd_is "roots_ok") gl))))) in
    let iso = the_asm (fun c ->
      let vs,bd = strip_forall c in
      length vs = 1 && is_eq bd) gl in
    let hlen = the_asm (fun c -> is_eq c &&
                 hd_is "heap_length" (lhand c)) gl in
    let flt = the_asm (fun c -> is_eq c &&
                hd_is "FILTER" (lhand c)) gl in
    let mm = the_asm (fun c ->
      let bd = snd (strip_forall c) in
      is_imp bd && is_disj (rand bd)) gl in
    let vs,bd = strip_forall (concl ro) in
    let pw = list_mk_forall(vs,
               mk_imp(list_mk_icomb "MEM" [lhand (lhand bd); rs],
                      rand bd)) in
    SUBGOAL_THEN pw (fun pwt ->
      ACCEPT_TAC (MATCH_MP heap_ok_store_ws
        (CONJ ho (CONJ pwt (CONJ iso (CONJ hlen (CONJ flt mm))))))) THEN
    MP_TAC ro THEN POP_ASSUM_LIST (K ALL_TAC) THEN
    REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[]));;

(* the unused space after a store of a data element where a data
   element was: the unused one is not a data element, so it is not
   the one written and the store left it where it was *)
let unused_store_el = prove
 (`unused_space_inv a l heap /\
   heap_length heap2 = heap_length heap /\
   heap_lookup p heap = SOME el1 /\ isDataElement el1 /\
   isDataElement el2 /\
   (!m x. ~(m = p) /\ heap_lookup m heap = SOME x
          ==> heap_lookup m heap2 = SOME x) /\
   heap_store p [el2] heap = (heap2,T)
   ==> unused_space_inv a l heap2`,
  REWRITE_TAC[unused_space_inv_def] THEN STRIP_TAC THEN
  SPLIT_ASM_TAC THEN
  REPEAT CONJ_TAC THEN TRY (SOLVED (ASM_REWRITE_TAC[])) THENL
   [(* the unused element is not the one written, so the store left
        it where it was *)
    DISCH_TAC THEN
    W(fun (asl,w as gl) ->
      let nz = the_asm (fun c -> is_neg c && is_eq (rand c) &&
                 rand (rand c) = `0`) gl in
      let impl = the_asm (fun c -> is_imp c && is_eq (rand c) &&
                   (try hd_is "heap_lookup" (lhand (rand c))
                    with Failure _ -> false)) gl in
      let lk = MP impl nz in
      let tr = the_asm (fun c ->
                 length (fst (strip_forall c)) = 2) gl in
      let hl1 = the_asm (fun c -> is_eq c &&
                  hd_is "heap_lookup" (lhand c) &&
                  hd_is "SOME" (rand c)) gl in
      let isd = the_asm (fun c -> hd_is "isDataElement" c &&
                  rand c = rand (rand (concl hl1))) gl in
      let a = el 0 (snd (strip_comb (lhand (concl lk)))) in
      let p = el 0 (snd (strip_comb (lhand (concl hl1)))) in
      SUBGOAL_THEN (mk_neg (mk_eq (a,p)))
        (fun ne -> ACCEPT_TAC (MATCH_MP tr (CONJ ne lk))) THEN
      POP_ASSUM_LIST (K ALL_TAC) THEN
      MP_TAC isd THEN MP_TAC hl1 THEN MP_TAC lk THEN
      REWRITE_TAC[isDataElement_def] THEN
      MESON_TAC[injectivity "option"; distinctness "heap_element"]);
    (* and the data below it is still data *)
    W(fun gl ->
      let du = the_asm (hd_is "data_up_to") gl in
      let st = the_asm (fun c -> is_eq c &&
                 hd_is "heap_store" (lhand c)) gl in
      let el2 = lhand (el 1 (snd (strip_comb (lhand (concl st))))) in
      let isd = the_asm (fun c -> hd_is "isDataElement" c &&
                  rand c = el2) gl in
      ACCEPT_TAC (MATCH_MP data_up_to_heap_store
        (CONJ du (CONJ st isd))))]);;

let unused_store_ref = prove
 (`unused_space_inv a l heap /\ RefBlock_inv heap heap2 /\
   heap_length heap2 = heap_length heap /\
   heap_store p [RefBlock rs] heap = (heap2,T)
   ==> unused_space_inv a l heap2`,
  REWRITE_TAC[unused_space_inv_def] THEN STRIP_TAC THEN
  SPLIT_ASM_TAC THEN
  REPEAT CONJ_TAC THEN TRY (SOLVED (ASM_REWRITE_TAC[])) THENL
   [(* the unused element is not a reference, so it is still there *)
    DISCH_TAC THEN
    FIRST_X_ASSUM (fun ri ->
      if not (hd_is "RefBlock_inv" (concl ri)) then fail() else
      MATCH_MP_TAC (CONJUNCT1 (REWRITE_RULE[RefBlock_inv_def] ri))) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[isRefBlock_def; RefBlock_def] THEN
      REWRITE_TAC[distinctness "heap_element"] THEN MESON_TAC[]];
    (* and the data before it is still data *)
    W(fun gl ->
      let du = the_asm (hd_is "data_up_to") gl in
      let st = the_asm (fun c -> is_eq c &&
                 hd_is "heap_store" (lhand c)) gl in
      let y = lhand (el 1 (snd (strip_comb (lhand (concl st))))) in
      SUBGOAL_THEN (list_mk_icomb "isDataElement" [y])
        (fun isd -> ACCEPT_TAC (MATCH_MP data_up_to_heap_store
          (CONJ du (CONJ st isd)))) THEN
      REWRITE_TAC[isDataElement_def; RefBlock_def] THEN
      MESON_TAC[])]);;

let DRESTRICT_DEF = prove
 (`!(fm:(A,B)fmap) s.
     FDOM (DRESTRICT fm s) = FDOM fm INTER s /\
     (!x. x IN s ==> FAPPLY (DRESTRICT fm s) x = FAPPLY fm x)`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[FDOM; FMAP_FN_DRESTRICT; EXTENSION; IN_INTER;
                IN_ELIM_THM] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[fmap_apply; FMAP_FN_DRESTRICT] THEN
    ASM_REWRITE_TAC[]]);;

let domain_insert = prove
 (`!k (v:A) t. domain (sptree_insert k v t) = k INSERT domain t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; domain_lookup; IN_INSERT; lookup_insert] THEN
  GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  MESON_TAC[]);;

let INJ_SUBSET_DOM = prove
 (`!(g:A->B) s t u. INJ g s u /\ t SUBSET s ==> INJ g t u`,
  REWRITE_TAC[INJ; SUBSET] THEN MESON_TAC[]);;

let INJ_DRESTRICT = prove
 (`!(tf:(A,B)fmap) s P.
     INJ (FAPPLY tf) (FDOM tf) s
     ==> INJ (FAPPLY (DRESTRICT tf P)) (FDOM (DRESTRICT tf P)) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[INJ; (CONJUNCT1 o SPEC_ALL) DRESTRICT_DEF;
              IN_INTER] THEN
  STRIP_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[(CONJUNCT2 o SPEC_ALL) DRESTRICT_DEF] THEN
  ASM_MESON_TAC[(CONJUNCT2 o SPEC_ALL) DRESTRICT_DEF]);;

let mem_zip_left = prove
 (`!(l1:A list) (l2:B list) x y.
     LENGTH l1 = LENGTH l2 /\ MEM (x,y) (ZIP l1 l2) ==> MEM x l1`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `l2:B list` THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` (cases_of `:(B)list`)) THEN
  REWRITE_TAC[ZIP; MEM; PAIR_EQ; LENGTH; NOT_SUC;
              ARITH_RULE `~(0 = SUC n)`; SUC_INJ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let mem_zip_right = prove
 (`!(l1:A list) (l2:B list) x y.
     LENGTH l1 = LENGTH l2 /\ MEM (x,y) (ZIP l1 l2) ==> MEM y l2`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `l2:B list` THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` (cases_of `:(B)list`)) THEN
  REWRITE_TAC[ZIP; MEM; PAIR_EQ; LENGTH; NOT_SUC;
              ARITH_RULE `~(0 = SUC n)`; SUC_INJ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let MEM_ref_all_vs = prove
 (cake_as_vars (fun () ->
    `sptree_lookup n refs = SOME (bvlSem_ValueArray l) /\ MEM v l
     ==> v IN all_vs refs stack'`),
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN
  REPEAT DISJ1_TAC THEN
  EXISTS_TAC `n:num` THEN
  EXISTS_TAC (cake_as_vars (fun () -> `l:(dataSem_v)list`)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEM_v_all_vs THEN FIRST_ASSUM ACCEPT_TAC);;

(* the halves of the split after a store above the first one: the
   second half is the old one with the element replaced, so it is
   still all references (HOL4 does this inline, with
   heap_split_length of gen_gc_partialTheory) *)

let heap_split_store_ref = prove
 (`heap_split k heap = SOME (h1,h2) /\
   heap_lookup p heap = SOME (RefBlock zs) /\
   ~(p < k) /\ LENGTH rs = LENGTH zs /\
   heap_store p [RefBlock rs] heap = (heap2,T) /\
   EVERY isRef h2
   ==> (?h3. heap_split k heap2 = SOME (h1,h3) /\ EVERY isRef h3)`,
  STRIP_TAC THEN
  (* the heap is its two halves, and the first is of the length *)
  FIRST_ASSUM (fun hs ->
    if not (is_eq (concl hs)) ||
       not (hd_is "heap_split" (lhand (concl hs))) then fail() else
    STRIP_ASSUME_TAC (MATCH_MP heap_split_heap_length hs)) THEN
  FIRST_X_ASSUM (fun e ->
    let c = concl e in
    if not (is_eq c) || not (hd_is "APPEND" (lhand c)) ||
       not (is_var (rand c)) then fail() else
    SUBST_ALL_TAC (SYM e)) THEN
  (* so the element written is in the second half *)
  FIRST_X_ASSUM (fun hl ->
    let c = concl hl in
    if not (is_eq c) || not (hd_is "heap_lookup" (lhand c))
    then fail() else
    ASSUME_TAC (REWRITE_RULE[heap_lookup_APPEND] hl)) THEN
  ASM_FS_TAC THEN
  (* and the second half splits there *)
  W(fun gl ->
    let hl2 = the_asm (fun c -> is_eq c &&
                hd_is "heap_lookup" (lhand c) &&
                hd_is "SOME" (rand c)) gl in
    STRIP_ASSUME_TAC (MATCH_MP heap_lookup_SPLIT hl2)) THEN
  REPEAT (FIRST_X_ASSUM (fun e ->
    let c = concl e in
    if not (is_eq c) || not (is_var (lhand c)) then fail() else
    SUBST_ALL_TAC e)) THEN
  (* the address written is the length of what lies before it *)
  W(fun gl ->
    let e = the_asm (fun c -> is_eq c &&
              hd_is "-" (lhand c) &&
              hd_is "heap_length" (rand c)) gl in
    let ha = rand (rand (concl e)) in
    let hl1 = the_asm (fun c -> is_eq c &&
                hd_is "heap_length" (lhand c) &&
                not (hd_is "APPEND" (rand (lhand c)))) gl in
    let h1 = rand (lhand (concl hl1)) in
    let p = lhand (lhand (concl e)) in
    SUBGOAL_THEN (mk_eq (p, list_mk_icomb "heap_length"
                              [list_mk_icomb "APPEND" [h1; ha]]))
      ASSUME_TAC THENL
     [REWRITE_TAC[heap_length_APPEND] THEN ASM_ARITH_TAC;
      ALL_TAC]) THEN
  FIRST_X_ASSUM (fun e ->
    let c = concl e in
    if not (is_eq c) || not (is_var (lhand c)) ||
       not (hd_is "heap_length" (rand c)) then fail() else
    SUBST_ALL_TAC e) THEN
  (* so the store writes the new element in the middle *)
  RULE_ASSUM_TRY (REWRITE_RULE[APPEND_ASSOC]) THEN
  RULE_ASSUM_TRY (REWRITE_RULE[heap_store_lemma; PAIR_EQ]) THEN
  SPLIT_ASM_TAC THEN
  REPEAT (FIRST_X_ASSUM (fun e ->
    let c = concl e in
    if not (is_eq c) || not (is_var (rand c)) ||
       not (hd_is "APPEND" (lhand c)) then fail() else
    SUBST_ALL_TAC (SYM e))) THEN
  (* so the split of the new heap keeps the first half *)
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  W(fun gl ->
    let e = the_asm (fun c -> is_eq c &&
              hd_is "heap_length" (lhand c) &&
              is_var (rand (lhand c)) && is_var (rand c)) gl in
    ONCE_REWRITE_TAC[SYM e]) THEN
  REWRITE_TAC[heap_split_length] THEN
  W(fun (asl,w) ->
    let bod = snd (strip_exists w) in
    let sm = rand (lhand (hd (conjuncts bod))) in
    EXISTS_TAC (rand sm)) THEN
  REWRITE_TAC[] THEN
  (* and the second half is the old one with the new element *)
  RULE_ASSUM_TRY (REWRITE_RULE[ALL_APPEND; ALL]) THEN
  REWRITE_TAC[ALL_APPEND; ALL] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[isRef_def; RefBlock_def] THEN
  MATCH_REDUCE_TAC THEN
  REWRITE_TAC[isMutTag_def]);;

(* and so the kind of the collection survives the store *)

let gc_kind_store_ref = prove
 (cake_as_vars (fun () ->
    `gc_kind_inv conf a sp sp1 gens heap /\
     heap_store p [RefBlock rs] heap = (heap2,T) /\
     heap_lookup p heap = SOME (RefBlock zs) /\
     LENGTH rs = LENGTH zs
     ==> gc_kind_inv conf a sp sp1 gens heap2`),
  REWRITE_TAC[gc_kind_inv_def] THEN STRIP_TAC THEN
  W(fun (asl,w) ->
    CASES_ON_TAC (find_term
      (hd_is "data_to_word_config_gc_kind") w)) THEN
  RULE_ASSUM_TRY (CONV_RULE(TOP_DEPTH_CONV MATCH_CONV)) THEN
  MATCH_REDUCE_TAC THEN
  TRY (SOLVED (FIRST_ASSUM ACCEPT_TAC)) THEN
  SPLIT_ASM_TAC THEN
  FIRST_X_ASSUM (fun ex ->
    if not (is_exists (concl ex)) then fail() else
    STRIP_ASSUME_TAC ex) THEN
  (* a RefBlock is a reference, so the element written is not in
     the half of the split that holds none *)
  W(fun (asl,w as gl) ->
    let hs = the_asm (fun c -> is_eq c &&
               hd_is "heap_split" (lhand c)) gl in
    let hl = the_asm (fun c -> is_eq c &&
               hd_is "heap_lookup" (lhand c)) gl in
    let k = el 0 (snd (strip_comb (lhand (concl hs)))) in
    let p = el 0 (snd (strip_comb (lhand (concl hl)))) in
    SUBGOAL_THEN (mk_neg (mk_binop `(<):num->num->bool` p k))
      ASSUME_TAC THENL
     [DISCH_TAC THEN
      MP_TAC (MATCH_MP heap_lookup_heap_split (CONJ hs hl)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      W(fun (asl,w as gl) ->
        let m = the_asm (hd_is "MEM") gl in
        let ev = the_asm (fun c -> hd_is "ALL" c &&
                   el 1 (snd (strip_comb c)) = rand (concl m)) gl in
        MP_TAC (MATCH_MP (REWRITE_RULE[GSYM ALL_MEM] ev) m)) THEN
      REWRITE_TAC[isRef_def; RefBlock_def] THEN
      MATCH_REDUCE_TAC THEN
      REWRITE_TAC[isMutTag_def];
      ALL_TAC]) THEN
  CONJ_TAC THENL
   [(* the generation state: the store is above the nursery *)
    W(fun gl ->
      let st = the_asm (fun c -> is_eq c &&
                 hd_is "heap_store" (lhand c)) gl in
      let gs = the_asm (hd_is "gen_state_ok") gl in
      let p = el 0 (snd (strip_comb (lhand (concl st)))) in
      let a = el 0 (snd (strip_comb (concl gs))) in
      SUBGOAL_THEN (mk_binop `(<=):num->num->bool` a p)
        (fun le -> MATCH_ACCEPT_TAC
          (MATCH_MP update_ref_gen_state_ok
            (CONJ st (CONJ le gs)))) THEN
      POP_ASSUM_LIST (fun l -> MAP_EVERY ASSUME_TAC (filter
        (fun t -> let c = concl t in
           hd_is "<" c || (is_neg c && hd_is "<" (rand c)) ||
           hd_is "<=" c) l)) THEN
      ASM_ARITH_TAC);
    (* and the two halves of the new heap *)
    W(fun gl ->
      let hs = the_asm (fun c -> is_eq c &&
                 hd_is "heap_split" (lhand c)) gl in
      let hl = the_asm (fun c -> is_eq c &&
                 hd_is "heap_lookup" (lhand c)) gl in
      let nlt = the_asm (fun c -> is_neg c && hd_is "<" (rand c)) gl in
      let len = the_asm (fun c -> is_eq c &&
                  hd_is "LENGTH" (lhand c)) gl in
      let st = the_asm (fun c -> is_eq c &&
                 hd_is "heap_store" (lhand c)) gl in
      let h2 = rand (rand (rand (concl hs))) in
      let ev = the_asm (fun c -> hd_is "ALL" c &&
                 el 1 (snd (strip_comb c)) = h2) gl in
      STRIP_ASSUME_TAC (MATCH_MP heap_split_store_ref
        (CONJ hs (CONJ hl (CONJ nlt (CONJ len (CONJ st ev))))))) THEN
    W(fun gl ->
      let hs2 = the_asm (fun c -> is_eq c &&
                  hd_is "heap_split" (lhand c) &&
                  hd_is "SOME" (rand c)) gl in
      EXISTS_TAC (lhand (rand (rand (concl hs2)))) THEN
      EXISTS_TAC (rand (rand (rand (concl hs2))))) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* an insert of an array where an array was leaves what a value
   says of a thunk *)
let dest_thunk_insert_ValueArray = prove
 ((cake_as_vars (fun () ->
    `sptree_lookup ptr refs = SOME (bvlSem_ValueArray as1)
     ==> dest_thunk v (insert ptr (ValueArray vls) refs) =
         dest_thunk v refs`)),
  STRIP_TAC THEN
  STRUCT_CASES_TAC(ISPEC (cake_as_vars (fun () -> `v:dataSem_v`))
                     (cases_of `:dataSem_v`)) THEN
  REWRITE_TAC[dataSem_dest_thunk_def] THEN
  MATCH_REDUCE_TAC THEN TRY (SOLVED (REWRITE_TAC[])) THEN
  ASM_CASES_TAC `a1:num = ptr` THEN
  ASM_REWRITE_TAC[lookup_insert] THEN
  (let ds = [distinctness "option"; distinctness "bvlSem_ref"] in
   REWRITE_TAC (injectivity "option" :: ds @ map GSYM ds)) THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  REWRITE_TAC[SELECT_REFL; EXISTS_UNIQUE_REFL] THEN
  MATCH_REDUCE_TAC THEN REWRITE_TAC[]);;

(* the value of a thunk of the references is one of the values *)
let MEM_thunk_all_vs = prove
 ((cake_as_vars (fun () ->
    `sptree_lookup n refs = SOME (bvlSem_Thunk ev x)
     ==> x IN all_vs refs stack'`)),
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN
  DISJ2_TAC THEN DISJ1_TAC THEN
  EXISTS_TAC `n:num` THEN
  EXISTS_TAC (cake_as_vars (fun () -> `ev:thunk_mode`)) THEN
  EXISTS_TAC (cake_as_vars (fun () -> `x:dataSem_v`)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEM_v_all_vs THEN REWRITE_TAC[MEM]);;

(* and so is a value of a MutBlock *)
let MEM_mutblock_all_vs = prove
 ((cake_as_vars (fun () ->
    `sptree_lookup n refs = SOME (bvlSem_MutBlock tg fin l c r) /\
     MEM v (l ++ [c] ++ r)
     ==> v IN all_vs refs stack'`)),
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN
  DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
  EXISTS_TAC `n:num` THEN
  MAP_EVERY EXISTS_TAC
    [cake_as_vars (fun () -> `tg:num`);
     cake_as_vars (fun () -> `fin:bool`);
     cake_as_vars (fun () -> `l:(dataSem_v)list`);
     cake_as_vars (fun () -> `c:dataSem_v`);
     cake_as_vars (fun () -> `r:(dataSem_v)list`)] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEM_v_all_vs THEN FIRST_ASSUM ACCEPT_TAC);;

(* two keys of an injective map have two addresses *)
let INJ_FAPPLY_NEQ = prove
 (`!(f:(A,B)fmap) s n m.
     INJ (FAPPLY f) (FDOM f) s /\ n IN FDOM f /\ m IN FDOM f /\
     ~(n = m) ==> ~(FAPPLY f n = FAPPLY f m)`,
  REWRITE_TAC[INJ] THEN MESON_TAC[]);;

(* an address that no timestamp has still has none when the map of
   the timestamps is cut down *)
let IMAGE_DRESTRICT_NOT = prove
 (`!(tf:(A,B)fmap) P x.
     ~(x IN IMAGE (FAPPLY tf) (FDOM tf))
     ==> ~(x IN IMAGE (FAPPLY (DRESTRICT tf P))
                  (FDOM (DRESTRICT tf P)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_IMAGE; (CONJUNCT1 o SPEC_ALL) DRESTRICT_DEF;
              IN_INTER] THEN
  MESON_TAC[(CONJUNCT2 o SPEC_ALL) DRESTRICT_DEF]);;

(* ---- the assumptions that each arm goes by ----------------------- *)

let g_ins (asl,w) = find_term (hd_is "sptree_insert") w;;

let g_ptr gl = el 0 (snd (strip_comb (g_ins gl)));;

let a_ri gl = the_asm (hd_is "RefBlock_inv") gl;;

let a_neq gl = the_asm (fun c -> is_neg c && is_eq (rand c) &&
                 hd_is "fmap_apply" (rand (rand c))) gl;;

let a_tr gl = the_asm (fun c ->
                let vs,bd = strip_forall c in
                length vs = 2 && is_imp bd &&
                hd_is "heap_lookup" (lhand (rand bd))) gl;;

let a_lkptr gl = the_asm (fun c -> is_eq c &&
                   hd_is "sptree_lookup" (lhand c) &&
                   el 0 (snd (strip_comb (lhand c))) = g_ptr gl &&
                   not (hd_is "sptree_insert" (rand (lhand c)))) gl;;

let a_lknew gl = the_asm (fun c -> is_eq c &&
                   hd_is "sptree_lookup" (lhand c) &&
                   hd_is "sptree_insert" (rand (lhand c))) gl;;

let a_hlold gl =
  let heap = el 0 (snd (strip_comb (concl (a_ri gl)))) in
  the_asm (fun c -> is_eq c && hd_is "heap_lookup" (lhand c) &&
             el 1 (snd (strip_comb (lhand c))) = heap &&
             hd_is "SOME" (rand c)) gl;;

let a_heap2 gl = el 1 (snd (strip_comb (concl (a_ri gl))));;

let a_hlnew gl =
  let h2 = a_heap2 gl in
  the_asm (fun c -> is_eq c && hd_is "heap_lookup" (lhand c) &&
             el 1 (snd (strip_comb (lhand c))) = h2 &&
             hd_is "SOME" (rand c)) gl;;

(* the pickers that the generic lemmas and their proofs go by *)
let a_vtr gl = the_asm (fun c ->
                 let vs,bd = strip_forall c in
                 length vs = 2 && is_imp bd &&
                 hd_is "v_inv" (rand bd)) gl;;
let a_dtr gl = the_asm (fun c ->
                 let vs,bd = strip_forall c in
                 length vs = 1 && is_imp bd &&
                 (try hd_is "dataSem_dest_thunk" (lhand (lhand bd))
                  with Failure _ -> false)) gl;;
let a_ltr gl = the_asm (fun c ->
                 let vs,bd = strip_forall c in
                 length vs = 1 && is_imp bd && is_eq (rand bd) &&
                 hd_is "sptree_lookup" (lhand (rand bd))) gl;;
let g_heap gl =
  let bd = snd (strip_forall (concl (a_tr gl))) in
  el 1 (snd (strip_comb (lhand (rand (lhand bd)))));;
let a_hlgen gl =
  let heap = g_heap gl in
  the_asm (fun c -> is_eq c && hd_is "heap_lookup" (lhand c) &&
             el 1 (snd (strip_comb (lhand c))) = heap &&
             hd_is "SOME" (rand c)) gl;;
let a_lkref r gl = the_asm (fun c -> is_eq c &&
                     hd_is "sptree_lookup" (lhand c) &&
                     el 1 (snd (strip_comb (lhand c))) = r &&
                     hd_is "SOME" (rand c)) gl;;

(* the arm of the old invariant and the arm of the new one, from the
   two lookups that each of them goes by *)
let USE_ARMS =
  W(fun (asl,_) ->
    let pick p = filter (fun (_,th) -> p (concl th)) asl in
    let lk2s = pick (fun c -> is_eq c && hd_is "sptree_lookup" (lhand c)
                              && hd_is "SOME" (rand c)) in
    let lk1s = pick (fun c -> is_eq c && hd_is "FLOOKUP" (lhand c) &&
                              hd_is "SOME" (rand c)) in
    let arms = [arm_VA; arm_BA; arm_TH; arm_MB] in
    let ths =
      itlist (fun (_,lk1) a ->
        itlist (fun (_,lk2) b ->
          itlist (fun arm c ->
            (try [MATCH_MP arm (CONJ lk1 lk2)] with Failure _ -> [])
            @ c) arms b) lk2s a) lk1s [] in
    RULE_ASSUM_TRY (REWRITE_RULE ths) THEN REWRITE_TAC ths);;

(* the reduction of a match whose scrutinee the patterns cannot
   decide by themselves: the guards have the pattern on the left,
   so the distinctness of the constructors is needed in both
   directions (PORTING-GUIDE.md entry 45) *)
let REDUCE_MATCH_HARD =
  MATCH_REDUCE_TAC THEN
  (let ds = [distinctness "option"; distinctness "bvlSem_ref"] in
   REWRITE_TAC (injectivity "option" :: injectivity "bvlSem_ref" ::
                PAIR_EQ :: ds @ map GSYM ds)) THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  REWRITE_TAC[SELECT_REFL; EXISTS_UNIQUE_REFL] THEN
  TRY MATCH_REDUCE_TAC THEN REWRITE_TAC[];;

(* what the invariant says of a value survives an update of the
   references that keeps it, and the cut of the timestamps to the
   ones of the new references and the stack *)
let v_inv_update_gen = prove
 (cake_as_vars (fun () ->
    `(!w1 w2. v_inv conf w1 refs (w2,f,tf,heap)
              ==> v_inv conf w1 refs2 (w2,f,tf,heap2)) /\
     v_inv conf v1 refs (v2,f,tf,heap) /\
     v1 IN all_vs refs2 stack'
     ==> v_inv conf v1 refs2
           (v2,f,DRESTRICT tf (all_ts refs2 stack'),heap2)`),
  STRIP_TAC THEN
  MATCH_MP_TAC v_inv_tf_restrict THEN
  EXISTS_TAC (cake_as_vars (fun () -> `stack':(dataSem_v)list`)) THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (GEN_ALL MEM_in_all_ts) THEN
    EXISTS_TAC (cake_as_vars (fun () -> `v1:dataSem_v`)) THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[]]);;

(* and so does what it says of the values of a list *)
let EVERY2_v_inv_update_gen = prove
 (cake_as_vars (fun () ->
    `(!w1 w2. v_inv conf w1 refs (w2,f,tf,heap)
              ==> v_inv conf w1 refs2 (w2,f,tf,heap2)) /\
     (!v. MEM v ys ==> v IN all_vs refs2 stack') /\
     EVERY2 (\z y. v_inv conf y refs (z,f,tf,heap)) zs ys
     ==> EVERY2 (\z y. v_inv conf y refs2
           (z,f,DRESTRICT tf (all_ts refs2 stack'),heap2)) zs ys`),
  STRIP_TAC THEN
  MATCH_MP_TAC EVERY2_MEM_MONO THEN
  W(fun gl ->
    let old = the_asm (hd_is "ALL2") gl in
    EXISTS_TAC (el 0 (snd (strip_comb (concl old))))) THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    STRIP_TAC THEN
    W(fun gl ->
      let old = the_asm (hd_is "ALL2") gl in
      let len = MATCH_MP LIST_REL_LENGTH old in
      let mz = the_asm (fun c -> hd_is "MEM" c &&
                 hd_is "ZIP" (rand c)) gl in
      let mem = the_asm (fun c ->
                  length (fst (strip_forall c)) = 1) gl in
      let vi = the_asm (hd_is "v_inv") gl in
      let inn = MATCH_MP mem (MATCH_MP mem_zip_right (CONJ len mz)) in
      MATCH_ACCEPT_TAC (MATCH_MP v_inv_update_gen
        (CONJ (a_vtr gl) (CONJ vi inn))));
    FIRST_ASSUM ACCEPT_TAC]);;

(* the values of a list of an arm, from the transfer that the
   update leaves *)
let EVERY2_ARM_GEN_TAC memlem =
  W(fun (asl,w as gl) ->
    let gargs = snd (strip_comb w) in
    let old = the_asm (fun c -> hd_is "ALL2" c &&
                el 1 (snd (strip_comb c)) = el 1 gargs &&
                el 2 (snd (strip_comb c)) = el 2 gargs) gl in
    let ys = el 2 gargs in
    let ats = find_term (hd_is "all_ts") w in
    let refs2 = lhand ats in
    let v = genvar (hd (snd (dest_type (type_of (rand ats))))) in
    SUBGOAL_THEN
      (mk_forall(v, mk_imp(list_mk_icomb "MEM" [v; ys],
         list_mk_icomb "IN"
           [v; list_mk_icomb "all_vs" [refs2; rand ats]])))
      (fun mem -> ACCEPT_TAC (MATCH_MP EVERY2_v_inv_update_gen
         (CONJ (a_vtr gl) (CONJ mem old)))) THEN
    REPEAT STRIP_TAC THEN
    W(fun gl ->
      let mm = the_asm (hd_is "MEM") gl in
      MATCH_ACCEPT_TAC (MATCH_MP memlem
        (CONJ (a_lkref refs2 gl) mm))));;

(* and so the invariant of a reference that the update did not
   write: its element is where it was, because the store only
   touched the address of the one written *)
let bc_ref_inv_update_gen = prove
 (cake_as_vars (fun () ->
    `INJ (FAPPLY (f:(num,num)fmap)) (FDOM f) s /\
     n IN FDOM f /\ ptr IN FDOM f /\ ~(n = ptr) /\
     FLOOKUP f n = SOME x /\
     (!w1 w2. v_inv conf w1 refs (w2,f,tf,heap)
              ==> v_inv conf w1 refs2 (w2,f,tf,heap2)) /\
     (!w. dest_thunk w refs = NotThunk
          ==> dest_thunk w refs2 = NotThunk) /\
     (!m. ~(m = ptr)
          ==> sptree_lookup m refs2 = sptree_lookup m refs) /\
     (!m y. ~(m = FAPPLY f ptr) /\ heap_lookup m heap = SOME y
            ==> heap_lookup m heap2 = SOME y) /\
     bc_ref_inv conf n refs (f,tf,heap,be')
     ==> bc_ref_inv conf n refs2
           (f,DRESTRICT tf (all_ts refs2 stack'),heap2,be')`),
  STRIP_TAC THEN
  (* the address of the key, and so the two addresses are not one *)
  SUBGOAL_THEN (cake_as_vars (fun () ->
    `FAPPLY (f:(num,num)fmap) (n:num) = x`)) ASSUME_TAC THENL
   [FIRST_ASSUM (fun lk ->
      if not (is_eq (concl lk)) ||
         not (hd_is "FLOOKUP" (lhand (concl lk))) then fail() else
      MP_TAC (REWRITE_RULE[FLOOKUP_DEF] lk)) THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[distinctness "option"; injectivity "option"];
    ALL_TAC] THEN
  SUBGOAL_THEN (cake_as_vars (fun () ->
    `~((x:num) = FAPPLY (f:(num,num)fmap) ptr)`)) ASSUME_TAC THENL
   [POP_ASSUM_LIST (fun l ->
      MAP_EVERY ASSUME_TAC (mapfilter (fun th ->
        let c = concl th in
        if hd_is "INJ" c then REWRITE_RULE[INJ] th
        else if hd_is "IN" c ||
                (is_eq c && hd_is "fmap_apply" (lhand c)) ||
                (is_neg c && is_eq (rand c) && is_var (lhand (rand c)))
        then th
        else fail()) l)) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the new references hold at the key what the old ones held *)
  W(fun (asl,w as gl) ->
    let n = el 1 (snd (strip_comb (concl (the_asm
              (hd_is "bc_ref_inv") gl)))) in
    let neq = the_asm (fun c -> is_neg c && is_eq (rand c) &&
                lhand (rand c) = n) gl in
    ASSUME_TAC (MATCH_MP (a_ltr gl) neq)) THEN
  (* and the kind of what it holds says which arm the invariant is *)
  W(fun gl ->
    let lk = the_asm (fun c -> is_eq c &&
               hd_is "sptree_lookup" (lhand c) &&
               hd_is "sptree_lookup" (rand c)) gl in
    NAMED_CASES_TAC (rand (concl lk)) [[]; ["rv"]]) THEN
  TRY (SOLVED (FIRST_X_ASSUM (fun inv ->
    if not (hd_is "bc_ref_inv" (concl inv)) then fail() else
    MP_TAC (REWRITE_RULE[bc_ref_inv_def] inv)) THEN
    ASM_REWRITE_TAC[] THEN REDUCE_MATCH_HARD)) THEN
  NAMED_CASES_TAC (cake_as_vars (fun () ->
    `rv:(dataSem_v)bvlSem_ref`))
    [["l"]; ["flag"; "bs"]; ["ev"; "vv"];
     ["tg"; "fin"; "ll"; "cc"; "rr"]] THEN
  USE_ARMS THEN
  SPLIT_ASM_TAC THEN
  REPEAT (FIRST_X_ASSUM (fun th ->
    if is_exists (concl th) then CHOOSE_TAC th else fail())) THEN
  SPLIT_ASM_TAC THEN
  (* the array of values: the element is where it was and its values
     are values of the new references *)
  TRY (SOLVED
        (W(fun gl ->
           let hl = a_hlgen gl in
           EXISTS_TAC (rand (rand (rand (concl hl)))) THEN
           CONJ_TAC THENL
            [ACCEPT_TAC (MATCH_MP (a_tr gl) (CONJ (a_neq gl) hl));
             EVERY2_ARM_GEN_TAC MEM_ref_all_vs]))) THEN
  (* the array of bytes: only the element *)
  TRY (SOLVED
        (CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
         RULE_ASSUM_TRY (CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
         W(fun gl ->
           ACCEPT_TAC (MATCH_MP (a_tr gl)
             (CONJ (a_neq gl) (a_hlgen gl)))))) THEN
  (* the thunk: the element, that it is still not a thunk, and its
     value *)
  TRY (SOLVED
        (W(fun gl ->
           let hl = a_hlgen gl in
           EXISTS_TAC (rand (rand (rand (concl hl)))) THEN
           REPEAT CONJ_TAC THENL
            [ACCEPT_TAC (MATCH_MP (a_tr gl) (CONJ (a_neq gl) hl));
             DISCH_THEN (fun ee ->
               W(fun gl ->
                 let impl = the_asm (fun c -> is_imp c &&
                              (try hd_is "dataSem_dest_thunk"
                                     (lhand (rand c))
                               with Failure _ -> false)) gl in
                 ACCEPT_TAC (MATCH_MP (a_dtr gl) (MP impl ee))));
             W(fun (asl,w as gl) ->
               let vi = the_asm (hd_is "v_inv") gl in
               let refs2 = lhand (find_term (hd_is "all_ts") w) in
               let inn = MATCH_MP MEM_thunk_all_vs
                           (a_lkref refs2 gl) in
               MATCH_ACCEPT_TAC (MATCH_MP v_inv_update_gen
                 (CONJ (a_vtr gl) (CONJ vi inn))))]))) THEN
  (* the mutable block: the kind of the collection, the address that
     no timestamp has, the element and its values *)
  TRY (SOLVED
        (REPEAT CONJ_TAC THEN
         TRY (SOLVED (FIRST_ASSUM ACCEPT_TAC)) THEN
         TRY (SOLVED
               (W(fun gl ->
                  let impl = the_asm (fun c -> is_imp c &&
                               is_neg (lhand c) &&
                               is_neg (rand c)) gl in
                  DISCH_THEN (fun nf -> MATCH_ACCEPT_TAC
                    (MATCH_MP IMAGE_DRESTRICT_NOT (MP impl nf)))))) THEN
         W(fun gl ->
           let hl = a_hlgen gl in
           EXISTS_TAC (rand (rand (rand (concl hl)))) THEN
           CONJ_TAC THENL
            [ACCEPT_TAC (MATCH_MP (a_tr gl) (CONJ (a_neq gl) hl));
             EVERY2_ARM_GEN_TAC MEM_mutblock_all_vs]))));;

(* a reference of the invariant has an address *)
let bc_ref_inv_FLOOKUP = prove
 ((cake_as_vars (fun () ->
    `bc_ref_inv conf n refs ((f:(num,num)fmap),tf,heap,be')
     ==> ?x. FLOOKUP f n = SOME x`)),
  STRIP_TAC THEN
  NAMED_CASES_TAC (cake_as_vars (fun () ->
    `FLOOKUP (f:(num,num)fmap) (n:num)`)) [[]; ["x"]] THENL
   [FIRST_X_ASSUM (fun inv ->
      if not (hd_is "bc_ref_inv" (concl inv)) then fail() else
      MP_TAC (REWRITE_RULE[bc_ref_inv_def] inv)) THEN
    ASM_REWRITE_TAC[] THEN REDUCE_MATCH_HARD;
    EXISTS_TAC `x:num` THEN REWRITE_TAC[]]);;

(* the invariant of a reference that an update did not write, with
   no hypothesis about the address of the key: the invariant of the
   reference has one *)
let bc_ref_inv_update_other_gen = prove
 (cake_as_vars (fun () ->
    `INJ (FAPPLY (f:(num,num)fmap)) (FDOM f) s /\
     ptr IN FDOM f /\ ~(n = ptr) /\
     (!w1 w2. v_inv conf w1 refs (w2,f,tf,heap)
              ==> v_inv conf w1 refs2 (w2,f,tf,heap2)) /\
     (!w. dest_thunk w refs = NotThunk
          ==> dest_thunk w refs2 = NotThunk) /\
     (!m. ~(m = ptr)
          ==> sptree_lookup m refs2 = sptree_lookup m refs) /\
     (!m y. ~(m = FAPPLY f ptr) /\ heap_lookup m heap = SOME y
            ==> heap_lookup m heap2 = SOME y) /\
     bc_ref_inv conf n refs (f,tf,heap,be')
     ==> bc_ref_inv conf n refs2
           (f,DRESTRICT tf (all_ts refs2 stack'),heap2,be')`),
  STRIP_TAC THEN
  FIRST_ASSUM (fun inv ->
    if not (hd_is "bc_ref_inv" (concl inv)) then fail() else
    CHOOSE_THEN ASSUME_TAC (MATCH_MP bc_ref_inv_FLOOKUP inv)) THEN
  SUBGOAL_THEN (cake_as_vars (fun () ->
    `(n:num) IN FDOM (f:(num,num)fmap)`)) ASSUME_TAC THENL
   [FIRST_ASSUM (fun lk ->
      let c = concl lk in
      if not (is_eq c) || not (hd_is "FLOOKUP" (lhand c)) then fail()
      else MP_TAC (REWRITE_RULE[FLOOKUP_DEF] lk)) THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[distinctness "option"];
    ALL_TAC] THEN
  W(fun (asl,w as gl) ->
    let bargs = snd (strip_comb (concl (the_asm
                 (hd_is "bc_ref_inv") gl))) in
    let n = el 1 bargs in
    let fm = el 0 (tparts (el 3 bargs)) in
    let inj = the_asm (fun c -> hd_is "INJ" c &&
                rand (el 0 (snd (strip_comb c))) = fm) gl in
    let nin = the_asm (fun c -> hd_is "IN" c &&
                hd_is "FDOM" (rand c) &&
                el 0 (snd (strip_comb c)) = n) gl in
    let pin = the_asm (fun c -> hd_is "IN" c &&
                hd_is "FDOM" (rand c) &&
                not (el 0 (snd (strip_comb c)) = n)) gl in
    let neq = the_asm (fun c -> is_neg c && is_eq (rand c) &&
                lhand (rand c) = n) gl in
    let lk1 = the_asm (fun c -> is_eq c &&
                hd_is "FLOOKUP" (lhand c)) gl in
    let inv = the_asm (hd_is "bc_ref_inv") gl in
    MATCH_ACCEPT_TAC (MATCH_MP bc_ref_inv_update_gen
      (CONJ inj (CONJ nin (CONJ pin (CONJ neq (CONJ lk1
        (CONJ (a_vtr gl) (CONJ (a_dtr gl) (CONJ (a_ltr gl)
          (CONJ (a_tr gl) inv))))))))))));;

(* the three transfers that an insert of an array of values leaves:
   what the invariant says of a value, what a value says of a
   thunk, and what the references hold at another key *)
let VA_trans = prove
 (cake_as_vars (fun () ->
    `RefBlock_inv heap heap2 /\
     sptree_lookup ptr refs = SOME (bvlSem_ValueArray as1)
     ==> (!w1 w2. v_inv conf w1 refs (w2,f,tf,heap)
                  ==> v_inv conf w1 (insert ptr (ValueArray vls) refs)
                        (w2,f,tf,heap2)) /\
         (!w. dest_thunk w refs = NotThunk
              ==> dest_thunk w (insert ptr (ValueArray vls) refs) =
                  NotThunk) /\
         (!m. ~(m = ptr)
              ==> sptree_lookup m
                    (insert ptr (ValueArray vls) refs) =
                  sptree_lookup m refs)`),
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC v_inv_ValueArray_insert THEN
    W(fun gl ->
      EXISTS_TAC (el 0 (snd (strip_comb (concl (a_ri gl)))))) THEN
    REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
    ASM_MESON_TAC[];
    GEN_TAC THEN
    W(fun gl ->
      REWRITE_TAC[MATCH_MP dest_thunk_insert_ValueArray
                    (a_lkptr gl)]) THEN
    DISCH_THEN ACCEPT_TAC;
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[lookup_insert]]);;

(* the values of a list of an arm, for an insert of an array *)
let EVERY2_ARM_TAC memlem =
  W(fun (asl,w as gl) ->
    let ins = find_term (hd_is "sptree_insert") w in
    let tr = CONJUNCT1 (MATCH_MP VA_trans
               (CONJ (a_ri gl) (a_lkptr gl))) in
    let v = find_term (fun t -> is_var t &&
              fst (dest_var t) = "vls") (concl tr) in
    ASSUME_TAC (INST [rand (el 1 (snd (strip_comb ins))),v] tr)) THEN
  EVERY2_ARM_GEN_TAC memlem;;

(* what the invariant says of a value of the stack survives the
   update of the reference and the cut of the timestamps *)
let v_inv_update_ref = prove
 (cake_as_vars (fun () ->
    `RefBlock_inv heap heap2 /\
     sptree_lookup ptr refs = SOME (bvlSem_ValueArray as1) /\
     v_inv conf v1 refs (v2,f,tf,heap) /\ MEM v1 stack'
     ==> v_inv conf v1 (insert ptr (ValueArray vls) refs)
           (v2,f,
            DRESTRICT tf (all_ts (insert ptr (ValueArray vls) refs)
                            stack'),heap2)`),
  STRIP_TAC THEN
  W(fun (asl,w as gl) ->
    let ins = find_term (hd_is "sptree_insert") w in
    let tr = CONJUNCT1 (MATCH_MP VA_trans
               (CONJ (a_ri gl) (a_lkptr gl))) in
    let vi = the_asm (hd_is "v_inv") gl in
    let mm = the_asm (hd_is "MEM") gl in
    let margs = snd (strip_comb (concl mm)) in
    let inn = MP (SPECL [el 0 margs; el 1 margs; ins]
                    MEM_stack_all_vs) mm in
    MATCH_ACCEPT_TAC (MATCH_MP v_inv_update_gen
      (CONJ tr (CONJ vi inn)))));;

(* and the invariant of a reference that is not the one written *)
let bc_ref_inv_update_ref_other = prove
 (cake_as_vars (fun () ->
    `INJ (FAPPLY (f:(num,num)fmap)) (FDOM f) s /\
     ptr IN FDOM f /\ ~(n = ptr) /\
     RefBlock_inv heap heap2 /\
     (!m y. ~(m = FAPPLY f ptr) /\ heap_lookup m heap = SOME y
            ==> heap_lookup m heap2 = SOME y) /\
     sptree_lookup ptr refs = SOME (bvlSem_ValueArray as1) /\
     bc_ref_inv conf n refs (f,tf,heap,be')
     ==> bc_ref_inv conf n (insert ptr (ValueArray vls) refs)
           (f,DRESTRICT tf (all_ts (insert ptr (ValueArray vls) refs)
                              stack'),heap2,be')`),
  STRIP_TAC THEN
  FIRST_ASSUM (fun inv ->
    if not (hd_is "bc_ref_inv" (concl inv)) then fail() else
    CHOOSE_THEN ASSUME_TAC (MATCH_MP bc_ref_inv_FLOOKUP inv)) THEN
  SUBGOAL_THEN (cake_as_vars (fun () ->
    `(n:num) IN FDOM (f:(num,num)fmap)`)) ASSUME_TAC THENL
   [FIRST_ASSUM (fun lk ->
      let c = concl lk in
      if not (is_eq c) || not (hd_is "FLOOKUP" (lhand c)) then fail()
      else MP_TAC (REWRITE_RULE[FLOOKUP_DEF] lk)) THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[distinctness "option"];
    ALL_TAC] THEN
  W(fun (asl,w as gl) ->
    let pt = g_ptr gl in
    let inj = the_asm (hd_is "INJ") gl in
    let pin = the_asm (fun c -> hd_is "IN" c && hd_is "FDOM" (rand c) &&
                el 0 (snd (strip_comb c)) = pt) gl in
    let nin = the_asm (fun c -> hd_is "IN" c && hd_is "FDOM" (rand c) &&
                not (el 0 (snd (strip_comb c)) = pt)) gl in
    let neq = the_asm (fun c -> is_neg c && is_eq (rand c) &&
                rand (rand c) = pt) gl in
    let lk1 = the_asm (fun c -> is_eq c &&
                hd_is "FLOOKUP" (lhand c)) gl in
    let inv = the_asm (hd_is "bc_ref_inv") gl in
    let trs = CONJUNCTS (MATCH_MP VA_trans
                (CONJ (a_ri gl) (a_lkptr gl))) in
    MATCH_ACCEPT_TAC (MATCH_MP bc_ref_inv_update_gen
      (CONJ inj (CONJ nin (CONJ pin (CONJ neq (CONJ lk1
        (CONJ (el 0 trs) (CONJ (el 1 trs) (CONJ (el 2 trs)
          (CONJ (a_tr gl) inv))))))))))));;

(* the invariant of the reference written: it is the array of the
   new values, and its element is the one stored *)
let bc_ref_inv_update_ref_at = prove
 ((cake_as_vars (fun () ->
    `RefBlock_inv heap heap2 /\
     FLOOKUP (f:(num,num)fmap) ptr = SOME p /\
     heap_lookup p heap2 = SOME (RefBlock t1) /\
     sptree_lookup ptr refs = SOME (bvlSem_ValueArray as1) /\
     EVERY2 (\z y. v_inv conf y refs (z,f,tf,heap)) t1 vls
     ==> bc_ref_inv conf ptr (insert ptr (ValueArray vls) refs)
           (f,DRESTRICT tf (all_ts (insert ptr (ValueArray vls) refs)
                              stack'),heap2,be')`)),
  STRIP_TAC THEN
  SUBGOAL_THEN (cake_as_vars (fun () ->
    `sptree_lookup (ptr:num)
       (insert ptr (ValueArray vls)
          (refs:((dataSem_v)bvlSem_ref)spt)) =
     SOME (bvlSem_ValueArray vls)`)) ASSUME_TAC THENL
   [REWRITE_TAC[lookup_insert]; ALL_TAC] THEN
  W(fun gl ->
    let lk1 = the_asm (fun c -> is_eq c &&
                hd_is "FLOOKUP" (lhand c)) gl in
    REWRITE_TAC[MATCH_MP arm_VA (CONJ lk1 (a_lknew gl))]) THEN
  W(fun gl ->
    let hl = the_asm (fun c -> is_eq c &&
               hd_is "heap_lookup" (lhand c)) gl in
    EXISTS_TAC (rand (rand (rand (concl hl)))) THEN
    CONJ_TAC THENL
     [ACCEPT_TAC hl;
      EVERY2_ARM_TAC MEM_ref_all_vs]));;
""",

  ('data_to_word_memoryProof', 'update_ref_thm1'): r"""
(* the port's own: what the proofs of the four update theorems
   after update_ref_thm add to the block above its statement.  A
   store of one value writes the root of it into the element's
   place for it (LUPDATE), so the pointers of the element written
   are that root and the ones it had (ptrs_store_LUPDATE), the
   values of the new array are the one written and the old ones
   (reach_refs_update_ref1), and the arm of the reference written
   is the old relation with one pair replaced
   (bc_ref_inv_update_ref_at1) *)

(* the head of a list that is not empty is one of its values *)
let MEM_HD = prove
 (`!(l:A list). 0 < LENGTH l ==> MEM (HD l) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; HD; MEM; LT_REFL]);;

(* the pointers of the element that an update of one value writes:
   the root put in, or a pointer that the element had *)
let ptrs_store_LUPDATE = prove
 (`heap_ok heap limit' /\ roots_ok (rs ++ (r :: roots2)) heap /\
   0 < LENGTH rs /\ heap_lookup p heap = SOME (RefBlock zs)
   ==> (!ptr u. MEM (gc_shared_Pointer ptr u) (LUPDATE (HD rs) i zs)
                ==> isSomeDataElement (heap_lookup ptr heap))`,
  REWRITE_TAC[heap_ok_def; roots_ok_def] THEN STRIP_TAC THEN
  SPLIT_ASM_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM (fun m ->
    if not (hd_is "MEM" (concl m)) then fail() else
    STRIP_ASSUME_TAC (MATCH_MP MEM_LUPDATE_E m)) THENL
   [(* the root written *)
    POP_ASSUM_LIST (fun l -> MAP_EVERY ASSUME_TAC (mapfilter (fun th ->
      let c = concl th in
      if (let vs,bd = strip_forall c in
          length vs = 2 && is_imp bd && hd_is "MEM" (lhand bd) &&
          hd_is "APPEND" (rand (lhand bd))) ||
         (is_eq c && hd_is "HD" (rand c)) || hd_is "<" c
      then th else fail()) l)) THEN
    ASM_MESON_TAC[MEM_HD; MEM_APPEND];
    (* a pointer of the element, which was in a good heap *)
    W(fun gl ->
      let ho = the_asm (fun c ->
        length (fst (strip_forall c)) = 5) gl in
      let hl = the_asm (fun c -> is_eq c &&
                 hd_is "heap_lookup" (lhand c)) gl in
      let md = REWRITE_RULE[RefBlock_def]
                 (MATCH_MP heap_lookup_MEM hl) in
      let mp = the_asm (fun c -> hd_is "MEM" c &&
                 hd_is "gc_shared_Pointer"
                   (el 0 (snd (strip_comb c)))) gl in
      ACCEPT_TAC (MATCH_MP ho (CONJ md mp)))]);;

(* the first pair of two lists that a relation relates *)
let EVERY2_HD = prove
 (`!(P:A->B->bool) xs ys. EVERY2 P xs ys /\ 0 < LENGTH xs
                          ==> P (HD xs) (HD ys)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; LT_REFL] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ys:B list` (cases_of `:(B)list`)) THEN
  REWRITE_TAC[ALL2_DEF; HD; TL; NOT_CONS_NIL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* a reference that the stack reaches through the array with one
   value replaced was reachable before the update: a value of the
   new array is the one written, which is on the stack, or one that
   the old array held (reachable_refs_UPDATE1) *)
let reach_refs_update_ref1 = prove
 (cake_as_vars (fun () ->
    `reachable_refs (xs ++ (RefPtr b ptr :: stack))
       (insert ptr (ValueArray (LUPDATE (HD xs) i xs1)) refs) n /\
     sptree_lookup ptr refs = SOME (bvlSem_ValueArray xs1) /\
     0 < LENGTH xs
     ==> reachable_refs (xs ++ (RefPtr b ptr :: stack)) refs n`),
  STRIP_TAC THEN
  FIRST_ASSUM (fun rr ->
    if not (hd_is "reachable_refs" (concl rr)) then fail() else
    MATCH_MP_TAC (MATCH_MP reachable_refs_UPDATE1 rr)) THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM (fun m ->
    if not (hd_is "MEM" (concl m)) then fail() else
    STRIP_ASSUME_TAC (MATCH_MP MEM_LUPDATE_E m)) THENL
   [(* the value written, which is on the stack *)
    POP_ASSUM_LIST (fun l -> MAP_EVERY ASSUME_TAC (mapfilter (fun th ->
      let c = concl th in
      if (is_neg c && hd_is "MEM" (rand c)) ||
         (is_eq c && hd_is "HD" (rand c)) || hd_is "<" c
      then th else fail()) l)) THEN
    ASM_MESON_TAC[MEM_HD];
    (* a value that the old array held *)
    W(fun gl ->
      let lk = the_asm (fun c -> is_eq c &&
                 hd_is "sptree_lookup" (lhand c) &&
                 not (hd_is "sptree_insert" (rand (lhand c)))) gl in
      EXISTS_TAC (rand (rand (rand (concl lk))))) THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* the invariant of the reference written when one of its values is
   replaced: the array with that value replaced, and the element
   with the root of it replaced (EVERY2_LUPDATE_same) *)
let bc_ref_inv_update_ref_at1 = prove
 (cake_as_vars (fun () ->
    `RefBlock_inv heap heap2 /\
     FLOOKUP (f:(num,num)fmap) ptr = SOME p /\
     heap_lookup p heap2 = SOME (RefBlock (LUPDATE t i zs)) /\
     sptree_lookup ptr refs = SOME (bvlSem_ValueArray xs1) /\
     EVERY2 (\z y. v_inv conf y refs (z,f,tf,heap)) zs xs1 /\
     v_inv conf v refs (t,f,tf,heap)
     ==> bc_ref_inv conf ptr
           (insert ptr (ValueArray (LUPDATE v i xs1)) refs)
           (f,DRESTRICT tf
                (all_ts (insert ptr
                   (ValueArray (LUPDATE v i xs1)) refs) stack'),
            heap2,be')`),
  STRIP_TAC THEN
  (* the new references hold the array with the value replaced *)
  W(fun (asl,w) ->
    let ins = find_term (hd_is "sptree_insert") w in
    let args = snd (strip_comb ins) in
    SUBGOAL_THEN
      (mk_eq (list_mk_icomb "sptree_lookup" [el 0 args; ins],
              list_mk_icomb "SOME" [el 1 args]))
      ASSUME_TAC THENL
     [REWRITE_TAC[lookup_insert]; ALL_TAC]) THEN
  (* which is the arm of a ValueArray *)
  W(fun gl ->
    let lk1 = the_asm (fun c -> is_eq c &&
                hd_is "FLOOKUP" (lhand c)) gl in
    REWRITE_TAC[MATCH_MP arm_VA (CONJ lk1 (a_lknew gl))]) THEN
  (* the element is the one stored, and its values are the old ones
     with the value written in its place *)
  W(fun (asl,w as gl) ->
    let hl = the_asm (fun c -> is_eq c &&
               hd_is "heap_lookup" (lhand c)) gl in
    let old = the_asm (hd_is "ALL2") gl in
    let vi = the_asm (hd_is "v_inv") gl in
    let oargs = snd (strip_comb (concl old)) in
    let vargs = snd (strip_comb (concl vi)) in
    let lup = find_term (hd_is "LUPDATE") (rand (concl hl)) in
    let i = el 1 (snd (strip_comb lup)) in
    let th = CONV_RULE(TOP_DEPTH_CONV BETA_CONV)
               (ISPECL [el 0 oargs; el 1 oargs; el 2 oargs; i;
                        el 0 (tparts (el 3 vargs)); el 1 vargs]
                  EVERY2_LUPDATE_same) in
    EXISTS_TAC (rand (rand (rand (concl hl)))) THEN
    CONJ_TAC THENL
     [ACCEPT_TAC hl;
      ASSUME_TAC (MATCH_MP th (CONJ vi old)) THEN
      EVERY2_ARM_TAC MEM_ref_all_vs]));;

(* the assumption that a list is not empty *)
let a_pos t gl = the_asm (fun c -> hd_is "<" c && lhand c = `0` &&
                   rand c = list_mk_icomb "LENGTH" [t]) gl;;
""",

  ('data_to_word_memoryProof', 'update_thunk_thm'): r"""
(* the port's own: what the proof of update_thunk_thm adds to the
   block above update_ref_thm.  The store writes a thunk where a
   thunk that was not evaluated was, so the halves of the split and
   the kind of the collection behave as they do for a store of a
   reference (heap_split_store_thunk, gc_kind_store_thunk), and the
   three transfers that the update leaves are TH_trans, over HOL4's
   v_inv_Thunk_insert and dest_thunk_insert_Thunk *)

let heap_split_store_thunk = prove
 (`heap_split k heap = SOME (h1,h2) /\
   heap_lookup p heap = SOME (ThunkBlock m y) /\
   ~(p < k) /\
   heap_store p [ThunkBlock ev r] heap = (heap2,T) /\
   EVERY isRef h2
   ==> (?h3. heap_split k heap2 = SOME (h1,h3) /\ EVERY isRef h3)`,
  STRIP_TAC THEN
  (* the heap is its two halves, and the first is of the length *)
  FIRST_ASSUM (fun hs ->
    if not (is_eq (concl hs)) ||
       not (hd_is "heap_split" (lhand (concl hs))) then fail() else
    STRIP_ASSUME_TAC (MATCH_MP heap_split_heap_length hs)) THEN
  FIRST_X_ASSUM (fun e ->
    let c = concl e in
    if not (is_eq c) || not (hd_is "APPEND" (lhand c)) ||
       not (is_var (rand c)) then fail() else
    SUBST_ALL_TAC (SYM e)) THEN
  (* so the element written is in the second half *)
  FIRST_X_ASSUM (fun hl ->
    let c = concl hl in
    if not (is_eq c) || not (hd_is "heap_lookup" (lhand c))
    then fail() else
    ASSUME_TAC (REWRITE_RULE[heap_lookup_APPEND] hl)) THEN
  ASM_FS_TAC THEN
  (* and the second half splits there *)
  W(fun gl ->
    let hl2 = the_asm (fun c -> is_eq c &&
                hd_is "heap_lookup" (lhand c) &&
                hd_is "SOME" (rand c)) gl in
    STRIP_ASSUME_TAC (MATCH_MP heap_lookup_SPLIT hl2)) THEN
  REPEAT (FIRST_X_ASSUM (fun e ->
    let c = concl e in
    if not (is_eq c) || not (is_var (lhand c)) then fail() else
    SUBST_ALL_TAC e)) THEN
  (* the address written is the length of what lies before it *)
  W(fun gl ->
    let e = the_asm (fun c -> is_eq c &&
              hd_is "-" (lhand c) &&
              hd_is "heap_length" (rand c)) gl in
    let ha = rand (rand (concl e)) in
    let hl1 = the_asm (fun c -> is_eq c &&
                hd_is "heap_length" (lhand c) &&
                not (hd_is "APPEND" (rand (lhand c)))) gl in
    let h1 = rand (lhand (concl hl1)) in
    let p = lhand (lhand (concl e)) in
    SUBGOAL_THEN (mk_eq (p, list_mk_icomb "heap_length"
                              [list_mk_icomb "APPEND" [h1; ha]]))
      ASSUME_TAC THENL
     [REWRITE_TAC[heap_length_APPEND] THEN ASM_ARITH_TAC;
      ALL_TAC]) THEN
  FIRST_X_ASSUM (fun e ->
    let c = concl e in
    if not (is_eq c) || not (is_var (lhand c)) ||
       not (hd_is "heap_length" (rand c)) then fail() else
    SUBST_ALL_TAC e) THEN
  (* so the store writes the new element in the middle *)
  RULE_ASSUM_TRY (REWRITE_RULE[APPEND_ASSOC]) THEN
  RULE_ASSUM_TRY (REWRITE_RULE[heap_store_lemma; PAIR_EQ]) THEN
  SPLIT_ASM_TAC THEN
  REPEAT (FIRST_X_ASSUM (fun e ->
    let c = concl e in
    if not (is_eq c) || not (is_var (rand c)) ||
       not (hd_is "APPEND" (lhand c)) then fail() else
    SUBST_ALL_TAC (SYM e))) THEN
  (* so the split of the new heap keeps the first half *)
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  W(fun gl ->
    let e = the_asm (fun c -> is_eq c &&
              hd_is "heap_length" (lhand c) &&
              is_var (rand (lhand c)) && is_var (rand c)) gl in
    ONCE_REWRITE_TAC[SYM e]) THEN
  REWRITE_TAC[heap_split_length] THEN
  W(fun (asl,w) ->
    let bod = snd (strip_exists w) in
    let sm = rand (lhand (hd (conjuncts bod))) in
    EXISTS_TAC (rand sm)) THEN
  REWRITE_TAC[] THEN
  (* and the second half is the old one with the new element *)
  RULE_ASSUM_TRY (REWRITE_RULE[ALL_APPEND; ALL]) THEN
  REWRITE_TAC[ALL_APPEND; ALL] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[isRef_def; ThunkBlock_def] THEN
  MATCH_REDUCE_TAC THEN
  REWRITE_TAC[isMutTag_def] THEN MESON_TAC[]);;

(* and so the kind of the collection survives the store *)

let gc_kind_store_thunk = prove
 (cake_as_vars (fun () ->
    `gc_kind_inv conf a sp sp1 gens heap /\
     heap_store p [ThunkBlock ev r] heap = (heap2,T) /\
     heap_lookup p heap = SOME (ThunkBlock m y)
     ==> gc_kind_inv conf a sp sp1 gens heap2`),
  REWRITE_TAC[gc_kind_inv_def] THEN STRIP_TAC THEN
  W(fun (asl,w) ->
    CASES_ON_TAC (find_term
      (hd_is "data_to_word_config_gc_kind") w)) THEN
  RULE_ASSUM_TRY (CONV_RULE(TOP_DEPTH_CONV MATCH_CONV)) THEN
  MATCH_REDUCE_TAC THEN
  TRY (SOLVED (FIRST_ASSUM ACCEPT_TAC)) THEN
  SPLIT_ASM_TAC THEN
  FIRST_X_ASSUM (fun ex ->
    if not (is_exists (concl ex)) then fail() else
    STRIP_ASSUME_TAC ex) THEN
  (* a RefBlock is a reference, so the element written is not in
     the half of the split that holds none *)
  W(fun (asl,w as gl) ->
    let hs = the_asm (fun c -> is_eq c &&
               hd_is "heap_split" (lhand c)) gl in
    let hl = the_asm (fun c -> is_eq c &&
               hd_is "heap_lookup" (lhand c)) gl in
    let k = el 0 (snd (strip_comb (lhand (concl hs)))) in
    let p = el 0 (snd (strip_comb (lhand (concl hl)))) in
    SUBGOAL_THEN (mk_neg (mk_binop `(<):num->num->bool` p k))
      ASSUME_TAC THENL
     [DISCH_TAC THEN
      MP_TAC (MATCH_MP heap_lookup_heap_split (CONJ hs hl)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      W(fun (asl,w as gl) ->
        let m = the_asm (hd_is "MEM") gl in
        let ev = the_asm (fun c -> hd_is "ALL" c &&
                   el 1 (snd (strip_comb c)) = rand (concl m)) gl in
        MP_TAC (MATCH_MP (REWRITE_RULE[GSYM ALL_MEM] ev) m)) THEN
      REWRITE_TAC[isRef_def; ThunkBlock_def] THEN
      MATCH_REDUCE_TAC THEN
      REWRITE_TAC[isMutTag_def] THEN MESON_TAC[];
      ALL_TAC]) THEN
  CONJ_TAC THENL
   [(* the generation state: the store is above the nursery *)
    W(fun gl ->
      let st = the_asm (fun c -> is_eq c &&
                 hd_is "heap_store" (lhand c)) gl in
      let gs = the_asm (hd_is "gen_state_ok") gl in
      let p = el 0 (snd (strip_comb (lhand (concl st)))) in
      let a = el 0 (snd (strip_comb (concl gs))) in
      SUBGOAL_THEN (mk_binop `(<=):num->num->bool` a p)
        (fun le -> MATCH_ACCEPT_TAC
          (MATCH_MP update_thunk_gen_state_ok
            (CONJ st (CONJ le gs)))) THEN
      POP_ASSUM_LIST (fun l -> MAP_EVERY ASSUME_TAC (filter
        (fun t -> let c = concl t in
           hd_is "<" c || (is_neg c && hd_is "<" (rand c)) ||
           hd_is "<=" c) l)) THEN
      ASM_ARITH_TAC);
    (* and the two halves of the new heap *)
    W(fun gl ->
      let hs = the_asm (fun c -> is_eq c &&
                 hd_is "heap_split" (lhand c)) gl in
      let hl = the_asm (fun c -> is_eq c &&
                 hd_is "heap_lookup" (lhand c)) gl in
      let nlt = the_asm (fun c -> is_neg c && hd_is "<" (rand c)) gl in
      let st = the_asm (fun c -> is_eq c &&
                 hd_is "heap_store" (lhand c)) gl in
      let h2 = rand (rand (rand (concl hs))) in
      let ev = the_asm (fun c -> hd_is "ALL" c &&
                 el 1 (snd (strip_comb c)) = h2) gl in
      STRIP_ASSUME_TAC (MATCH_MP heap_split_store_thunk
        (CONJ hs (CONJ hl (CONJ nlt (CONJ st ev)))))) THEN
    W(fun gl ->
      let hs2 = the_asm (fun c -> is_eq c &&
                  hd_is "heap_split" (lhand c) &&
                  hd_is "SOME" (rand c)) gl in
      EXISTS_TAC (lhand (rand (rand (concl hs2)))) THEN
      EXISTS_TAC (rand (rand (rand (concl hs2))))) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* what the invariant says of the values of the stack, which it
   relates to the roots the other way round *)
let EVERY2_v_inv_update_stack = prove
 (cake_as_vars (fun () ->
    `(!w1 w2. v_inv conf w1 refs (w2,f,tf,heap)
              ==> v_inv conf w1 refs2 (w2,f,tf,heap2)) /\
     (!v. MEM v vs ==> v IN all_vs refs2 stack') /\
     EVERY2 (\v x. v_inv conf v refs (x,f,tf,heap)) vs rs
     ==> EVERY2 (\v x. v_inv conf v refs2
           (x,f,DRESTRICT tf (all_ts refs2 stack'),heap2)) vs rs`),
  STRIP_TAC THEN
  MATCH_MP_TAC EVERY2_MEM_MONO THEN
  W(fun gl ->
    let old = the_asm (hd_is "ALL2") gl in
    EXISTS_TAC (el 0 (snd (strip_comb (concl old))))) THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    STRIP_TAC THEN
    W(fun gl ->
      let old = the_asm (hd_is "ALL2") gl in
      let len = MATCH_MP LIST_REL_LENGTH old in
      let mz = the_asm (fun c -> hd_is "MEM" c &&
                 hd_is "ZIP" (rand c)) gl in
      let mem = the_asm (fun c ->
                  length (fst (strip_forall c)) = 1) gl in
      let vi = the_asm (hd_is "v_inv") gl in
      let inn = MATCH_MP mem (MATCH_MP mem_zip_left (CONJ len mz)) in
      MATCH_ACCEPT_TAC (MATCH_MP v_inv_update_gen
        (CONJ (a_vtr gl) (CONJ vi inn))));
    FIRST_ASSUM ACCEPT_TAC]);;

(* HOL4 data_to_word_memoryProofScript.sml:4636-4640: the theorem
   that HOL4 states as the value of an ML expression, which is the
   lemma with the counter of the induction generalised away *)
let v_inv_Thunk_insert =
  let ckv,_ = dest_forall (concl v_inv_Thunk_insert_lemma) in
  GEN_ALL (DISCH_ALL (REWRITE_RULE[GSYM v_inv_eq]
    (GEN ckv (UNDISCH (SPEC_ALL v_inv_Thunk_insert_lemma)))));;

(* an insert of a thunk where a thunk that was not evaluated was
   leaves what a value says of a thunk: a value that said NotThunk
   is not a pointer to that reference *)
let dest_thunk_insert_Thunk = prove
 (cake_as_vars (fun () ->
    `dest_thunk w refs = NotThunk /\
     sptree_lookup ptr refs = SOME (bvlSem_Thunk NotEvaluated v)
     ==> dest_thunk w (insert ptr (Thunk ev h) refs) = NotThunk`),
  STRIP_TAC THEN
  CASES_ON_TAC (cake_as_vars (fun () -> `w:dataSem_v`)) THEN
  REWRITE_TAC[dataSem_dest_thunk_def] THEN
  MATCH_REDUCE_TAC THEN TRY (SOLVED (REWRITE_TAC[])) THEN
  ASM_CASES_TAC `a1:num = ptr` THENL
   [(* the reference written: the value did not say NotThunk *)
    FIRST_X_ASSUM (fun dt ->
      let c = concl dt in
      if not (is_eq c) ||
         not (hd_is "dataSem_dest_thunk" (lhand c)) then fail()
      else MP_TAC dt) THEN
    ASM_REWRITE_TAC[dataSem_dest_thunk_def] THEN
    REDUCE_MATCH_HARD THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[distinctness "dataSem_dest_thunk_ret"];
    (* another one: the references hold there what they held *)
    ASM_REWRITE_TAC[lookup_insert] THEN
    FIRST_X_ASSUM (fun dt ->
      let c = concl dt in
      if not (is_eq c) ||
         not (hd_is "dataSem_dest_thunk" (lhand c)) then fail()
      else MP_TAC dt) THEN
    REWRITE_TAC[dataSem_dest_thunk_def] THEN
    MATCH_REDUCE_TAC THEN REWRITE_TAC[]]);;

(* the three transfers that an insert of a thunk leaves *)
let TH_trans = prove
 (cake_as_vars (fun () ->
    `INJ (FAPPLY (f:(num,num)fmap)) (FDOM f)
       {a | isSomeDataElement (heap_lookup a heap)} /\
     ptr IN FDOM f /\
     sptree_lookup ptr refs = SOME (bvlSem_Thunk NotEvaluated v) /\
     heap_lookup (FAPPLY f ptr) heap =
       SOME (ThunkBlock NotEvaluated y) /\
     v_inv conf v refs (y,f,tf,heap) /\
     (ev = Evaluated ==> dest_thunk h refs = NotThunk) /\
     heap_store (FAPPLY f ptr) [ThunkBlock ev q] heap = (heap2,T) /\
     heap_lookup (FAPPLY f ptr) heap2 = SOME (ThunkBlock ev q) /\
     (!m x. ~(m = FAPPLY f ptr) /\ heap_lookup m heap = SOME x
            ==> heap_lookup m heap2 = SOME x) /\
     v_inv conf h refs (q,f,tf,heap)
     ==> (!w1 w2. v_inv conf w1 refs (w2,f,tf,heap)
                  ==> v_inv conf w1 (insert ptr (Thunk ev h) refs)
                        (w2,f,tf,heap2)) /\
         (!w. dest_thunk w refs = NotThunk
              ==> dest_thunk w (insert ptr (Thunk ev h) refs) =
                  NotThunk) /\
         (!m. ~(m = ptr)
              ==> sptree_lookup m (insert ptr (Thunk ev h) refs) =
                  sptree_lookup m refs)`),
  DISCH_THEN (fun hs ->
    REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN
      DISCH_THEN (fun vi ->
        MATCH_ACCEPT_TAC (MATCH_MP v_inv_Thunk_insert (CONJ vi hs)));
      GEN_TAC THEN DISCH_THEN (fun dt ->
        MATCH_ACCEPT_TAC (MATCH_MP dest_thunk_insert_Thunk
          (CONJ dt (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 hs))))));
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[lookup_insert]]));;

(* the invariant of the reference written when a thunk is updated:
   the element is the thunk stored, the value put in is the one of
   the stack, and that it says nothing of a thunk is what the
   update was given *)
let bc_ref_inv_update_thunk_at = prove
 (cake_as_vars (fun () ->
    `FLOOKUP (f:(num,num)fmap) ptr = SOME p /\
     heap_lookup p heap2 = SOME (ThunkBlock ev q) /\
     (ev = Evaluated ==> dest_thunk h refs = NotThunk) /\
     v_inv conf h refs (q,f,tf,heap) /\
     MEM h stack' /\
     (!w1 w2. v_inv conf w1 refs (w2,f,tf,heap)
              ==> v_inv conf w1 (insert ptr (Thunk ev h) refs)
                    (w2,f,tf,heap2)) /\
     (!w. dest_thunk w refs = NotThunk
          ==> dest_thunk w (insert ptr (Thunk ev h) refs) = NotThunk)
     ==> bc_ref_inv conf ptr (insert ptr (Thunk ev h) refs)
           (f,DRESTRICT tf
                (all_ts (insert ptr (Thunk ev h) refs) stack'),
            heap2,be')`),
  STRIP_TAC THEN
  (* the new references hold the thunk at the key *)
  W(fun (asl,w) ->
    let ins = find_term (hd_is "sptree_insert") w in
    let args = snd (strip_comb ins) in
    SUBGOAL_THEN
      (mk_eq (list_mk_icomb "sptree_lookup" [el 0 args; ins],
              list_mk_icomb "SOME" [el 1 args]))
      ASSUME_TAC THENL
     [REWRITE_TAC[lookup_insert]; ALL_TAC]) THEN
  (* which is the arm of a thunk *)
  W(fun (asl,w as gl) ->
    let lk1 = the_asm (fun c -> is_eq c &&
                hd_is "FLOOKUP" (lhand c)) gl in
    let ins = find_term (hd_is "sptree_insert") w in
    REWRITE_TAC[MATCH_MP arm_TH (CONJ lk1 (a_lkref ins gl))]) THEN
  (* the element stored, the thunk it says nothing of, and the
     value put in *)
  W(fun gl ->
    let hl = the_asm (fun c -> is_eq c &&
               hd_is "heap_lookup" (lhand c)) gl in
    EXISTS_TAC (rand (rand (rand (concl hl)))) THEN
    REPEAT CONJ_TAC THENL
     [ACCEPT_TAC hl;
      DISCH_THEN (fun ee ->
        W(fun gl ->
          let impl = the_asm (fun c -> is_imp c &&
                       (try hd_is "dataSem_dest_thunk"
                              (lhand (rand c))
                        with Failure _ -> false)) gl in
          ACCEPT_TAC (MATCH_MP (a_dtr gl) (MP impl ee))));
      W(fun (asl,w as gl) ->
        let vi = the_asm (hd_is "v_inv") gl in
        let mm = the_asm (hd_is "MEM") gl in
        let margs = snd (strip_comb (concl mm)) in
        let ins = lhand (find_term (hd_is "all_ts") w) in
        let inn = MP (SPECL [el 0 margs; el 1 margs; ins]
                        MEM_stack_all_vs) mm in
        MATCH_ACCEPT_TAC (MATCH_MP v_inv_update_gen
          (CONJ (a_vtr gl) (CONJ vi inn))))]));;
""",

  ('data_to_word_memoryProof', 'update_mutblock_thm'): r"""
(* the port's own: what the proof of update_mutblock_thm adds to
   the block above update_ref_thm.  The update fills the hole of a
   mutable block, so the store writes a BlockRep where one was and
   the three transfers it leaves are MB_trans, over HOL4's
   v_inv_BlockRep_upd (which asks that no timestamp points at the
   cell, which the arm of an unfinalised block gives) and
   v_inv_MutBlock_hole; of the kind of the collection there is
   nothing to say, because such a block is not in a heap that a
   generational collection goes through (gc_kind_not_gen) *)

(* a cell that no timestamp has is not the value of the map *)
let IMAGE_NOT_point = prove
 (`!(tf:(A,B)fmap) p. ~(p IN IMAGE (FAPPLY tf) (FDOM tf))
                      ==> (!t. t IN FDOM tf ==> ~(FAPPLY tf t = p))`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

(* a heap that no generational collection goes through says no more
   of the kind of the collection than the unused space, which a
   store does not touch *)
let gc_kind_not_gen = prove
 (cake_as_vars (fun () ->
    `gc_kind_inv conf a sp sp1 gens heap /\
     (!gs. ~(data_to_word_config_gc_kind conf =
             data_to_word_Generational gs))
     ==> gc_kind_inv conf a sp sp1 gens heap2`),
  REWRITE_TAC[gc_kind_inv_def] THEN STRIP_TAC THEN
  W(fun (asl,w) ->
    CASES_ON_TAC (find_term
      (hd_is "data_to_word_config_gc_kind") w)) THEN
  RULE_ASSUM_TRY (CONV_RULE(TOP_DEPTH_CONV MATCH_CONV)) THEN
  MATCH_REDUCE_TAC THEN
  TRY (SOLVED (FIRST_ASSUM ACCEPT_TAC)) THEN
  (* the case of a generational collection is out: the kind of this
     one is not that, and the case analysis put the kind into the
     assumption that says so *)
  W(fun gl ->
    let ng = the_asm (fun c ->
               let vs,bd = strip_forall c in
               length vs = 1 && is_neg bd) gl in
    MP_TAC ng) THEN
  MESON_TAC[]);;

(* HOL4 data_to_word_memoryProofScript.sml: the theorem that HOL4
   states as the value of an ML expression, which is the lemma with
   the counter of the induction generalised away *)
let v_inv_BlockRep_upd =
  let ckv,_ = dest_forall (concl v_inv_BlockRep_upd_lemma) in
  GEN_ALL (DISCH_ALL (REWRITE_RULE[GSYM v_inv_eq]
    (GEN ckv (UNDISCH (SPEC_ALL v_inv_BlockRep_upd_lemma)))));;

(* an insert of a mutable block where one was leaves what a value
   says of a thunk *)
let dest_thunk_insert_MutBlock = prove
 (cake_as_vars (fun () ->
    `sptree_lookup ptr refs = SOME (bvlSem_MutBlock tag fin l cv r)
     ==> dest_thunk v (insert ptr (MutBlock tag fin2 l h r) refs) =
         dest_thunk v refs`),
  STRIP_TAC THEN
  CASES_ON_TAC (cake_as_vars (fun () -> `v:dataSem_v`)) THEN
  REWRITE_TAC[dataSem_dest_thunk_def] THEN
  MATCH_REDUCE_TAC THEN TRY (SOLVED (REWRITE_TAC[])) THEN
  ASM_CASES_TAC `a1:num = ptr` THEN
  ASM_REWRITE_TAC[lookup_insert] THEN
  (let ds = [distinctness "option"; distinctness "bvlSem_ref"] in
   REWRITE_TAC (injectivity "option" :: ds @ map GSYM ds)) THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  REWRITE_TAC[SELECT_REFL; EXISTS_UNIQUE_REFL] THEN
  MATCH_REDUCE_TAC THEN REWRITE_TAC[]);;

(* the pointers of the element that an update of one value writes:
   the pointer put in, or one that the element had *)
let ptrs_store_el = prove
 (`heap_ok heap limit' /\
   (!pt u. w = gc_shared_Pointer pt u
           ==> isSomeDataElement (heap_lookup pt heap)) /\
   heap_lookup p heap = SOME (DataElement zs l2 d2)
   ==> (!pt u. MEM (gc_shared_Pointer pt u) (LUPDATE w i zs)
               ==> isSomeDataElement (heap_lookup pt heap))`,
  REWRITE_TAC[heap_ok_def] THEN STRIP_TAC THEN
  SPLIT_ASM_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM (fun m ->
    if not (hd_is "MEM" (concl m)) then fail() else
    STRIP_ASSUME_TAC (MATCH_MP MEM_LUPDATE_E m)) THENL
   [(* the pointer written *)
    W(fun gl ->
      let pw = the_asm (fun c ->
                 let vs,bd = strip_forall c in
                 length vs = 2 && is_imp bd &&
                 hd_is "isSomeDataElement" (rand bd)) gl in
      let eq = the_asm (fun c -> is_eq c &&
                 hd_is "gc_shared_Pointer" (lhand c)) gl in
      ACCEPT_TAC (MATCH_MP pw (SYM eq)));
    (* a pointer of the element, which was in a good heap *)
    W(fun gl ->
      let ho = the_asm (fun c ->
        length (fst (strip_forall c)) = 5) gl in
      let hl = the_asm (fun c -> is_eq c &&
                 hd_is "heap_lookup" (lhand c)) gl in
      let md = MATCH_MP heap_lookup_MEM hl in
      let mp = the_asm (fun c -> hd_is "MEM" c &&
                 hd_is "gc_shared_Pointer"
                   (el 0 (snd (strip_comb c)))) gl in
      ACCEPT_TAC (MATCH_MP ho (CONJ md mp)))]);;

(* the three transfers that an update of the hole of a mutable
   block leaves: over the heap (v_inv_BlockRep_upd, which asks that
   no timestamp points at the cell) and over the references
   (v_inv_MutBlock_hole) *)
let MB_trans = prove
 (cake_as_vars (fun () ->
    `heap_lookup p heap = SOME (BlockRep tag zs) /\
     (!t. t IN FDOM (tf:(num,num)fmap) ==> ~(FAPPLY tf t = p)) /\
     (!m y. ~(m = p) /\ heap_lookup m heap = SOME y
            ==> heap_lookup m heap2 = SOME y) /\
     sptree_lookup ptr refs = SOME (bvlSem_MutBlock tag2 fin l cv r)
     ==> (!w1 w2. v_inv conf w1 refs (w2,f,tf,heap)
                  ==> v_inv conf w1
                        (insert ptr (MutBlock tag2 fin2 l h r) refs)
                        (w2,f,tf,heap2)) /\
         (!w. dest_thunk w refs = NotThunk
              ==> dest_thunk w (insert ptr
                    (MutBlock tag2 fin2 l h r) refs) = NotThunk) /\
         (!m. ~(m = ptr)
              ==> sptree_lookup m
                    (insert ptr (MutBlock tag2 fin2 l h r) refs) =
                  sptree_lookup m refs)`),
  DISCH_THEN (fun hs ->
    let hl = CONJUNCT1 hs in
    let tfc = CONJUNCT1 (CONJUNCT2 hs) in
    let tr = CONJUNCT1 (CONJUNCT2 (CONJUNCT2 hs)) in
    let lk = CONJUNCT2 (CONJUNCT2 (CONJUNCT2 hs)) in
    REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN
      DISCH_THEN (fun vi ->
        MATCH_ACCEPT_TAC (MATCH_MP v_inv_MutBlock_hole
          (CONJ (MATCH_MP v_inv_BlockRep_upd
                   (CONJ vi (CONJ hl (CONJ tfc tr)))) lk)));
      GEN_TAC THEN
      REWRITE_TAC[MATCH_MP dest_thunk_insert_MutBlock lk] THEN
      DISCH_THEN ACCEPT_TAC;
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[lookup_insert]]));;

(* the invariant of the reference written when the hole of a
   mutable block is filled: the element is the one stored, and its
   values are the old ones with the value put in its place *)
let bc_ref_inv_update_mutblock_at = prove
 (cake_as_vars (fun () ->
    `FLOOKUP (f:(num,num)fmap) ptr = SOME p /\
     heap_lookup p heap2 =
       SOME (BlockRep tag (LUPDATE rr (LENGTH l) zs)) /\
     sptree_lookup ptr refs = SOME (bvlSem_MutBlock tag F l cv r) /\
     EVERY2 (\z y. v_inv conf y refs (z,f,tf,heap)) zs
       (l ++ [cv] ++ r) /\
     v_inv conf h refs (rr,f,tf,heap) /\
     (!gs. ~(data_to_word_config_gc_kind conf =
             data_to_word_Generational gs)) /\
     ~(p IN IMAGE (FAPPLY (tf:(num,num)fmap)) (FDOM tf)) /\
     (!w1 w2. v_inv conf w1 refs (w2,f,tf,heap)
              ==> v_inv conf w1
                    (insert ptr (MutBlock tag F l h r) refs)
                    (w2,f,tf,heap2)) /\
     (!v. MEM v (l ++ [h] ++ r)
          ==> v IN all_vs (insert ptr (MutBlock tag F l h r) refs)
                    stack')
     ==> bc_ref_inv conf ptr
           (insert ptr (MutBlock tag F l h r) refs)
           (f,DRESTRICT tf
                (all_ts (insert ptr (MutBlock tag F l h r) refs)
                   stack'),heap2,be')`),
  STRIP_TAC THEN
  (* the new references hold the block with the hole filled *)
  W(fun (asl,w) ->
    let ins = find_term (hd_is "sptree_insert") w in
    let args = snd (strip_comb ins) in
    SUBGOAL_THEN
      (mk_eq (list_mk_icomb "sptree_lookup" [el 0 args; ins],
              list_mk_icomb "SOME" [el 1 args]))
      ASSUME_TAC THENL
     [REWRITE_TAC[lookup_insert]; ALL_TAC]) THEN
  (* which is the arm of a mutable block *)
  W(fun (asl,w as gl) ->
    let lk1 = the_asm (fun c -> is_eq c &&
                hd_is "FLOOKUP" (lhand c)) gl in
    let ins = find_term (hd_is "sptree_insert") w in
    REWRITE_TAC[MATCH_MP arm_MB (CONJ lk1 (a_lkref ins gl))]) THEN
  REPEAT CONJ_TAC THEN
  TRY (SOLVED (FIRST_ASSUM ACCEPT_TAC)) THEN
  (* no timestamp points at the cell, and the map only shrinks *)
  TRY (SOLVED
        (W(fun gl ->
           let nim = the_asm (fun c -> is_neg c &&
                       hd_is "IN" (rand c)) gl in
           MATCH_ACCEPT_TAC
             (MATCH_MP IMAGE_DRESTRICT_NOT nim)))) THEN
  (* the element is the one stored, and its values are the old ones
     with the value put in the place of the hole *)
  W(fun (asl,w as gl) ->
    let hl = the_asm (fun c -> is_eq c &&
               hd_is "heap_lookup" (lhand c)) gl in
    let lup = rand (rand (rand (concl hl))) in
    let old = the_asm (fun c -> hd_is "ALL2" c) gl in
    let oargs = snd (strip_comb (concl old)) in
    let vi = the_asm (hd_is "v_inv") gl in
    let vargs = snd (strip_comb (concl vi)) in
    let i = el 1 (snd (strip_comb lup)) in
    let hv = el 1 vargs in
    let newys = list_mk_icomb "LUPDATE" [hv; i; el 2 oargs] in
    let bod = snd (strip_exists w) in
    let goalys = el 2 (snd (strip_comb (rand bod))) in
    EXISTS_TAC lup THEN
    CONJ_TAC THENL
     [ACCEPT_TAC hl;
      SUBGOAL_THEN (mk_eq (goalys,newys))
        (fun e -> ONCE_REWRITE_TAC[e]) THENL
       [REWRITE_TAC[APPEND; LUPDATE_LENGTH];
        ALL_TAC] THEN
      W(fun (asl,w as gl) ->
        let th = CONV_RULE(TOP_DEPTH_CONV BETA_CONV)
                   (ISPECL [el 0 oargs; el 1 oargs; el 2 oargs; i;
                            el 0 (tparts (el 3 vargs)); hv]
                      EVERY2_LUPDATE_same) in
        let old2 = MATCH_MP th (CONJ vi old) in
        let mem = ONCE_REWRITE_RULE[ASSUME (mk_eq (goalys,newys))]
                    (the_asm (fun c ->
                       length (fst (strip_forall c)) = 1 &&
                       is_imp (snd (strip_forall c)) &&
                       hd_is "MEM" (lhand (snd (strip_forall c))))
                       gl) in
        ACCEPT_TAC (MATCH_MP EVERY2_v_inv_update_gen
          (CONJ (a_vtr gl) (CONJ mem old2))))]));;
""",

  ('data_to_word_memoryProof', 'update_byte_ref_thm'): r"""
(* the port's own: what the proof of update_byte_ref_thm adds to
   the block above update_ref_thm.  The update writes an array of
   bytes where one of the same length was, so the heap is given as
   an append and not by a heap_store: the element replaced is of
   the length it had (samelen_bytes), whence the addresses that
   hold data are the ones that held data, the heap and the unused
   space stay good, and the kind of the collection survives
   (gc_kind_byte_update, over the halves of a split of the new
   heap).  The three transfers of such a store are BA_trans, over
   HOL4's v_inv_IMP and v_inv_ByteArray_insert *)

(* the heap of a store into a byte array, out of a term that holds
   it: the append whose middle element is the array of bytes *)
let byte_heap t =
  find_term (fun s -> hd_is "APPEND" s &&
    (try hd_is "Bytes" (lhand (lhand (rand s)))
     with Failure _ -> false)) t;;

(* and the one whose element is not the element given *)
let byte_heap_not u t =
  find_term (fun s -> hd_is "APPEND" s &&
    (try hd_is "Bytes" (lhand (lhand (rand s))) &&
         not (lhand (lhand (rand s)) = u)
     with Failure _ -> false)) t;;

(* tools/wip-update_byte.ml: the lemmas that the proof of
   update_byte_ref_thm of data_to_word_memoryProof needs, each
   proved in a session cut at the statement (tools/bin/trybase) and
   waiting for the proof itself.  Nothing loads this file: the
   lemmas go into the EXTRA_BEFORE block of the statement when the
   proof is done, and the file is deleted then.

   What is still to write: gc_kind_byte_update (the halves of the
   split of the new heap, over the port's own heap_split_replace),
   bc_ref_inv_update_byte_at (the arm of the reference written) and
   the proof itself, which is update_thunk_thm's with a byte array
   for the thunk -- except that the heap is given as an append
   (h1 ++ [Bytes ...] ++ h2) and not by a heap_store. *)

(* the two elements of a byte array that is written are of a
   length, whatever the bytes are *)
let samelen_bytes = prove
 (cake_as_vars (fun () ->
    `el_length (Bytes be fl ys ws) = el_length (Bytes be fl xs ws)`),
  REWRITE_TAC[bytes_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[el_length_def; LENGTH_write_bytes]);;

(* the element of a byte array is data *)
let isSomeDataElement_Bytes = prove
 (cake_as_vars (fun () ->
    `isSomeDataElement (SOME (Bytes be fl bs ws))`),
  REWRITE_TAC[isSomeDataElement_def; bytes_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  W(fun (asl,w) ->
    let vs,bod = strip_exists w in
    MAP_EVERY EXISTS_TAC
      (snd (strip_comb (rand (lhand bod))))) THEN
  REWRITE_TAC[]);;

(* so the addresses that hold data are the ones that held data *)
let isSomeDataElement_byte_update = prove
 (cake_as_vars (fun () ->
    `!n. isSomeDataElement
           (heap_lookup n (ha ++ [Bytes be fl ys ws] ++ hb)) =
         isSomeDataElement
           (heap_lookup n (ha ++ [Bytes be fl xs ws] ++ hb))`),
  GEN_TAC THEN
  REWRITE_TAC[GSYM APPEND_ASSOC;
              data_to_word_memoryProof_heap_lookup_APPEND;
              heap_length_clauses; ADD_CLAUSES; heap_lookup_def;
              samelen_bytes] THEN
  REPEAT (COND_CASES_TAC THEN
          ASM_REWRITE_TAC[isSomeDataElement_Bytes]) THEN
  REWRITE_TAC[isSomeDataElement_Bytes]);;

(* the heap stays good when a byte array is written: it is as long
   as it was, it has the forward pointers it had, and the element
   written holds no pointer *)
let heap_ok_byte_update = prove
 (cake_as_vars (fun () ->
    `heap_ok (ha ++ [Bytes be fl xs ws] ++ hb) limit' /\
     LENGTH xs = LENGTH ys
     ==> heap_ok (ha ++ [Bytes be fl ys ws] ++ hb) limit'`),
  REWRITE_TAC[heap_ok_def; heap_length_APPEND;
              heap_length_clauses; ADD_CLAUSES; samelen_bytes;
              FILTER_APPEND; FILTER] THEN
  REWRITE_TAC[bytes_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[isForwardPointer_def; LENGTH_write_bytes] THEN
  STRIP_TAC THEN SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MEM_APPEND; MEM] THEN
  STRIP_TAC THEN
  (let isd = REWRITE_RULE[LENGTH_write_bytes]
               (CONV_RULE(TOP_DEPTH_CONV let_CONV)
                 (REWRITE_RULE[bytes_def]
                    isSomeDataElement_byte_update)) in
   REWRITE_TAC[isd]) THEN
  FIRST_ASSUM (fun ho ->
    if not (length (fst (strip_forall (concl ho))) = 5) then fail()
    else MATCH_MP_TAC ho) THEN
  REWRITE_TAC[MEM_APPEND; MEM] THEN
  RULE_ASSUM_TRY (REWRITE_RULE[injectivity "heap_element"]) THEN
  SPLIT_ASM_TAC THEN
  REPEAT (FIRST_X_ASSUM (fun e ->
    let c = concl e in
    if not (is_eq c) || not (is_var (lhand c)) then fail() else
    SUBST_ALL_TAC e)) THEN
  TRY (SOLVED (ASM_MESON_TAC[MEM])) THEN
  ASM_MESON_TAC[MEM]);;

(* an insert of a byte array where one was leaves what a value says
   of a thunk *)
let dest_thunk_insert_ByteArray = prove
 (cake_as_vars (fun () ->
    `sptree_lookup ptr refs = SOME (bvlSem_ByteArray fl xs)
     ==> dest_thunk v (insert ptr (ByteArray fl ys) refs) =
         dest_thunk v refs`),
  STRIP_TAC THEN
  CASES_ON_TAC (cake_as_vars (fun () -> `v:dataSem_v`)) THEN
  REWRITE_TAC[dataSem_dest_thunk_def] THEN
  MATCH_REDUCE_TAC THEN TRY (SOLVED (REWRITE_TAC[])) THEN
  ASM_CASES_TAC `a1:num = ptr` THEN
  ASM_REWRITE_TAC[lookup_insert] THEN
  (let ds = [distinctness "option"; distinctness "bvlSem_ref"] in
   REWRITE_TAC (injectivity "option" :: ds @ map GSYM ds)) THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  REWRITE_TAC[SELECT_REFL; EXISTS_UNIQUE_REFL] THEN
  MATCH_REDUCE_TAC THEN REWRITE_TAC[]);;

(* what the insert of a byte array asks of the cell it writes *)
let ByteArray_in_domain = prove
 (cake_as_vars (fun () ->
    `sptree_lookup ptr refs = SOME (bvlSem_ByteArray fl xs)
     ==> (ptr IN domain refs
          ==> ?a b. sptree_lookup ptr refs =
                    SOME (bvlSem_ByteArray a b))`),
  STRIP_TAC THEN DISCH_THEN (K ALL_TAC) THEN
  EXISTS_TAC (cake_as_vars (fun () -> `fl:bool`)) THEN
  EXISTS_TAC (cake_as_vars (fun () -> `xs:(word8)list`)) THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* a byte array has no edge to another reference, so a reference
   that the stack reaches after the update it reached before *)
let reach_refs_update_byte = prove
 (cake_as_vars (fun () ->
    `reachable_refs stack' (insert ptr (ByteArray fl ys) refs) n /\
     sptree_lookup ptr refs = SOME (bvlSem_ByteArray fl xs)
     ==> reachable_refs stack' refs n`),
  STRIP_TAC THEN
  REWRITE_TAC[reachable_refs_def] THEN
  SUBGOAL_THEN (cake_as_vars (fun () ->
    `ref_edge (insert ptr (ByteArray fl ys)
       (refs:((dataSem_v)bvlSem_ref)spt)) = ref_edge refs`))
    (fun e -> FIRST_X_ASSUM (fun rr ->
       if not (hd_is "reachable_refs" (concl rr)) then fail() else
       ACCEPT_TAC (REWRITE_RULE[e]
         (REWRITE_RULE[reachable_refs_def] rr)))) THEN
  REWRITE_TAC[FUN_EQ_THM; ref_edge_def; lookup_insert] THEN
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_REDUCE_TAC THEN REWRITE_TAC[]);;

(* the three transfers that a store into a byte array leaves: of
   the element written the lookup of the heap says which one it is,
   so the heaps of the transfers are the ones of the store *)
let BA_trans = prove
 (cake_as_vars (fun () ->
    `sptree_lookup ptr refs = SOME (bvlSem_ByteArray fl xs) /\
     heap_lookup p (ha ++ [Bytes be fl xs ws] ++ hb) =
       SOME (Bytes be fl xs ws) /\
     LENGTH xs = LENGTH ys
     ==> (!w1 w2. v_inv conf w1 refs
                    (w2,f,tf,ha ++ [Bytes be fl xs ws] ++ hb)
                  ==> v_inv conf w1
                        (insert ptr (ByteArray fl ys) refs)
                        (w2,f,tf,ha ++ [Bytes be fl ys ws] ++ hb)) /\
         (!w. dest_thunk w refs = NotThunk
              ==> dest_thunk w (insert ptr (ByteArray fl ys) refs) =
                  NotThunk) /\
         (!m. ~(m = ptr)
              ==> sptree_lookup m
                    (insert ptr (ByteArray fl ys) refs) =
                  sptree_lookup m refs)`),
  DISCH_THEN (fun hs ->
    let lk = CONJUNCT1 hs in
    REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN
      DISCH_THEN (fun vi ->
        MATCH_ACCEPT_TAC (MATCH_MP v_inv_ByteArray_insert
          (CONJ (MATCH_MP v_inv_IMP vi)
            (MATCH_MP ByteArray_in_domain lk))));
      GEN_TAC THEN
      REWRITE_TAC[MATCH_MP dest_thunk_insert_ByteArray lk] THEN
      DISCH_THEN ACCEPT_TAC;
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[lookup_insert]]));;

(* the element that a heap holds at the length of a prefix *)
let heap_lookup_at = prove
 (  `!ha u hb. heap_lookup (heap_length ha) (ha ++ [u] ++ hb) = SOME u`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM APPEND_ASSOC;
              data_to_word_memoryProof_heap_lookup_APPEND;
              LT_REFL; SUB_REFL; heap_length_clauses;
              ADD_CLAUSES] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[APPEND; heap_lookup_def] THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[] THEN
  MESON_TAC[el_length_NOT_0; ARITH_RULE
    `!n. ~(n = 0) ==> 0 < n`]);;

(* the halves of the split of a heap whose element is replaced by
   one of its length, when the cut is above the element: the second
   half is the one it was, and the first is the one it was with the
   element replaced *)
let heap_split_replace2 = prove
 (`!e ha u v hb h1 h2.
     heap_split e (ha ++ [u] ++ hb) = SOME (h1,h2) /\
     el_length u = el_length v /\ heap_length ha < e
     ==> ?h1'. heap_split e (ha ++ [v] ++ hb) = SOME (h1',h2) /\
               (!z. MEM z h1' ==> MEM z h1 \/ z = v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* the lengths of the halves of the old split, and their append *)
  FIRST_ASSUM (fun hs ->
    if not (is_eq (concl hs)) ||
       not (hd_is "heap_split" (lhand (concl hs))) then fail() else
    STRIP_ASSUME_TAC (MATCH_MP heap_split_heap_length hs)) THEN
  (* so the first half is ha and a piece of what follows it, or ha
     is the first half and a piece, which the cut's place forbids *)
  W(fun (asl,w as gl) ->
    let ap = the_asm (fun c -> is_eq c &&
               hd_is "APPEND" (lhand c) &&
               hd_is "APPEND" (rand c)) gl in
    STRIP_ASSUME_TAC (MATCH_MP APPEND_EQ_APPEND ap)) THEN
  TRY (SOLVED
        (W(fun (asl,w as gl) ->
           let eq = the_asm (fun c -> is_eq c &&
                      hd_is "heap_length" (lhand c) &&
                      is_var (rand c)) gl in
           let lf = rator (lhand (concl eq)) in
           let aps = mapfilter (fun (_,th) ->
             let c = concl th in
             if is_eq c && is_var (lhand c) &&
                type_of (lhand c) = type_of (rand (lhand (concl eq)))
             then AP_TERM lf th else fail()) asl in
           let lt = the_asm (fun c -> hd_is "<" c) gl in
           MAP_EVERY MP_TAC (eq :: lt :: aps)) THEN
         REWRITE_TAC[heap_length_APPEND] THEN ARITH_TAC)) THEN
  (* the piece that the first half has past ha begins with the
     element, so the first half is ha, the element and the rest *)
  W(fun (asl,w as gl) ->
    let eq = the_asm (fun c -> is_eq c && is_var (lhand c) &&
               hd_is "APPEND" (rand c)) gl in
    CASES_ON_TAC (rand (rand (concl eq)))) THEN
  RULE_ASSUM_TRY (REWRITE_RULE[APPEND; APPEND_NIL; CONS_11]) THEN
  SPLIT_ASM_TAC THEN
  TRY (SOLVED
        (W(fun (asl,w as gl) ->
           let eq = the_asm (fun c -> is_eq c &&
                      hd_is "heap_length" (lhand c) &&
                      is_var (rand c)) gl in
           let lf = rator (lhand (concl eq)) in
           let aps = mapfilter (fun (_,th) ->
             let c = concl th in
             if is_eq c && is_var (lhand c) &&
                type_of (lhand c) = type_of (rand (lhand (concl eq)))
             then AP_TERM lf th else fail()) asl in
           let lt = the_asm (fun c -> hd_is "<" c) gl in
           MAP_EVERY MP_TAC (eq :: lt :: aps)) THEN
         REWRITE_TAC[heap_length_APPEND; heap_length_clauses;
                     ADD_CLAUSES] THEN ARITH_TAC)) THEN
  REPEAT (FIRST_X_ASSUM (fun e ->
    let c = concl e in
    if not (is_eq c) || not (is_var (lhand c)) ||
       is_var (rand c) then fail() else SUBST_ALL_TAC e)) THEN
  (* so the new heap is ha, the new element and the rest, and the
     split of it at the length of that front is what the goal says
     (heap_split_length) *)
  W(fun (asl,w as gl) ->
    let hl = the_asm (fun c -> is_eq c &&
               hd_is "heap_length" (lhand c) &&
               is_var (rand c)) gl in
    let front = rand (lhand (concl hl)) in
    let ha = lhand front in
    let p = rand (rand front) in
    let vt = find_term (fun t -> is_var t &&
               fst (dest_var t) = "v") w in
    let newfront = list_mk_icomb "APPEND"
                     [ha; list_mk_icomb "CONS" [vt; p]] in
    EXISTS_TAC newfront THEN
    SUBGOAL_THEN (mk_eq (rand (concl hl),
                         list_mk_icomb "heap_length" [newfront]))
      (fun e -> ONCE_REWRITE_TAC[e]) THENL
     [MP_TAC hl THEN
      (let el = the_asm (fun c -> is_eq c &&
                  hd_is "el_length" (lhand c)) gl in
       let ue = mapfilter (fun (_,th) ->
         let c = concl th in
         if not (is_eq c) || not (is_var (lhand c)) ||
            not (is_var (rand c)) ||
            not (type_of (lhand c) = type_of vt) then fail()
         else if fst (dest_var (lhand c)) = "u" then GSYM th
         else th) asl in
       REWRITE_TAC (heap_length_APPEND :: heap_length_clauses ::
                    el :: ue)) THEN
      ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[APPEND] THEN
    REWRITE_TAC[GSYM (CONJUNCT2 APPEND)] THEN
    REWRITE_TAC[APPEND_ASSOC] THEN
    REWRITE_TAC[heap_split_length] THEN
    REWRITE_TAC[MEM_APPEND; MEM] THEN
    MESON_TAC[]));;

(* a byte array is no reference *)
let isRef_Bytes = prove
 (cake_as_vars (fun () ->
    `~(data_to_word_memoryProof_isRef (Bytes be fl bs ws))`),
  REWRITE_TAC[isRef_def; bytes_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MATCH_REDUCE_TAC THEN
  (let ds = [distinctness "data_to_word_memoryProof_tag"] in
   REWRITE_TAC (isMutTag_def :: ds @ map GSYM ds)));;

(* the kind of the collection survives a store into a byte array:
   the element replaced is no reference, so it is in the first half
   of the split, and the second half is the one it was *)
let gc_kind_byte_update = prove
 (cake_as_vars (fun () ->
    `gc_kind_inv conf a sp sp1 gens
       (ha ++ [Bytes be fl xs ws] ++ hb) /\
     LENGTH xs = LENGTH ys
     ==> gc_kind_inv conf a sp sp1 gens
           (ha ++ [Bytes be fl ys ws] ++ hb)`),
  REWRITE_TAC[gc_kind_inv_def] THEN STRIP_TAC THEN
  W(fun (asl,w) ->
    CASES_ON_TAC (find_term
      (hd_is "data_to_word_config_gc_kind") w)) THEN
  RULE_ASSUM_TRY (CONV_RULE(TOP_DEPTH_CONV MATCH_CONV)) THEN
  MATCH_REDUCE_TAC THEN
  TRY (SOLVED (FIRST_ASSUM ACCEPT_TAC)) THEN
  SPLIT_ASM_TAC THEN
  REPEAT (FIRST_X_ASSUM (fun th ->
    if is_exists (concl th) then CHOOSE_TAC th else fail())) THEN
  SPLIT_ASM_TAC THEN
  CONJ_TAC THENL
   [(* the generation state (gen_state_ok_update_byte) *)
    W(fun gl ->
      let gs = the_asm (hd_is "gen_state_ok") gl in
      MATCH_ACCEPT_TAC (MATCH_MP gen_state_ok_update_byte gs));
    ALL_TAC] THEN
  (* the element replaced is in the first half, because the second
     holds references only and a byte array is none *)
  W(fun (asl,w as gl) ->
    let hs = the_asm (fun c -> is_eq c &&
               hd_is "heap_split" (lhand c)) gl in
    let args = snd (strip_comb (lhand (concl hs))) in
    let k = el 0 args in
    let hp = el 1 args in
    let lk = ISPECL [lhand hp; lhand (lhand (rand hp));
                     rand (rand hp)] heap_lookup_at in
    SUBGOAL_THEN (list_mk_icomb "<"
                    [list_mk_icomb "heap_length" [lhand hp]; k])
      ASSUME_TAC THENL
     [MP_TAC (MATCH_MP heap_lookup_heap_split (CONJ hs lk)) THEN
      COND_CASES_TAC THENL
       [DISCH_THEN (K ALL_TAC) THEN REWRITE_TAC[];
        DISCH_TAC THEN
        W(fun gl ->
          let ev = the_asm (fun c -> hd_is "ALL" c &&
                     not (is_abs (el 0 (snd (strip_comb c))))) gl in
          let m = the_asm (hd_is "MEM") gl in
          MP_TAC (MATCH_MP (REWRITE_RULE[GSYM ALL_MEM] ev) m)) THEN
        REWRITE_TAC[isRef_Bytes]];
      ALL_TAC]) THEN
  (* so the split of the new heap keeps the second half *)
  W(fun (asl,w as gl) ->
    let hs = the_asm (fun c -> is_eq c &&
               hd_is "heap_split" (lhand c)) gl in
    let lt = the_asm (fun c -> hd_is "<" c &&
               hd_is "heap_length" (lhand c)) gl in
    let hp = el 1 (snd (strip_comb (lhand (concl hs)))) in
    let k = el 0 (snd (strip_comb (lhand (concl hs)))) in
    let u = lhand (lhand (rand hp)) in
    let vt = find_term (fun t -> hd_is "Bytes" t &&
               not (t = u)) w in
    let pr = rand (rand (concl hs)) in
    let th = ISPECL [k; lhand hp; u; vt; rand (rand hp);
                     lhand pr; rand pr] heap_split_replace2 in
    (* samelen_bytes carries the type variable of the proof that
       made it, so it is matched against the element of the goal *)
    let sl = PART_MATCH lhs (GSYM samelen_bytes)
               (list_mk_icomb "el_length" [u]) in
    STRIP_ASSUME_TAC (MP th (CONJ hs (CONJ sl lt)))) THEN
  W(fun (asl,w as gl) ->
    let hs2 = the_asm (fun c -> is_eq c &&
                hd_is "heap_split" (lhand c) &&
                not (can (find_term (fun t -> is_var t &&
                       fst (dest_var t) = "xs")) (lhand c))) gl in
    let pr = rand (rand (concl hs2)) in
    EXISTS_TAC (lhand pr) THEN EXISTS_TAC (rand pr) THEN
    REPEAT CONJ_TAC THEN
    TRY (SOLVED (FIRST_ASSUM ACCEPT_TAC)) THEN
    (* the first half holds no reference: its elements are the old
       ones or the byte array written *)
    REWRITE_TAC[GSYM ALL_MEM] THEN
    REPEAT STRIP_TAC THEN
    W(fun gl ->
      let bd = the_asm (fun c ->
                 length (fst (strip_forall c)) = 1 &&
                 is_imp (snd (strip_forall c)) &&
                 is_disj (rand (snd (strip_forall c)))) gl in
      let m = the_asm (hd_is "MEM") gl in
      STRIP_ASSUME_TAC (MATCH_MP (SPEC_ALL bd) m)) THEN
    TRY (SOLVED
          (W(fun gl ->
             let ev = the_asm (fun c -> hd_is "ALL" c &&
                        is_abs (el 0 (snd (strip_comb c)))) gl in
             let m = the_asm (fun c -> hd_is "MEM" c) gl in
             MP_TAC (MATCH_MP (REWRITE_RULE[GSYM ALL_MEM] ev) m)) THEN
           CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
           ASM_REWRITE_TAC[])) THEN
    ASM_MESON_TAC[isRef_Bytes]));;

(* the element singled out of a heap, as an append of three *)
let APPEND_SINGLE = prove
 (`!(ha:A list) x hb. ha ++ (x :: hb) = ha ++ [x] ++ hb`,
  REWRITE_TAC[APPEND]);;

(* the annotation that the root of a reference carries is zero
   unless the reference holds a mutable block *)
let ref_ptr_annot_ByteArray = prove
 (cake_as_vars (fun () ->
    `sptree_lookup ptr refs = SOME (bvlSem_ByteArray fl xs)
     ==> ref_ptr_annot conf (sptree_lookup ptr refs) =
         (wordLang_Word (n2w 0):'a word_loc)`),
  DISCH_THEN (fun lk -> REWRITE_TAC[lk; ref_ptr_annot_def]) THEN
  MATCH_REDUCE_TAC THEN REWRITE_TAC[]);;

(* the elements of a heap other than the one replaced are where
   they were: a lookup below the element lands in the front, and
   one above it skips an element of the length it had *)
let heap_lookup_other_replace = prove
 (`!ha u v hb.
     el_length u = el_length v
     ==> !m y. ~(m = heap_length ha) /\
               heap_lookup m (ha ++ [u] ++ hb) = SOME y
               ==> heap_lookup m (ha ++ [v] ++ hb) = SOME y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM APPEND_ASSOC;
              data_to_word_memoryProof_heap_lookup_APPEND;
              heap_length_clauses; ADD_CLAUSES; heap_lookup_def] THEN
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  (* the element itself is not looked up, so the lookup is past it *)
  W(fun (asl,w) ->
    let c = find_term (fun t -> is_eq t && hd_is "-" (lhand t) &&
              rand t = `0`) w in
    SUBGOAL_THEN (mk_neg c) ASSUME_TAC) THENL
   [W(fun gl ->
      let lt = the_asm (fun c -> is_neg c && hd_is "<" (rand c)) gl in
      let ne = the_asm (fun c -> is_neg c && is_eq (rand c) &&
                 hd_is "heap_length" (rand (rand c))) gl in
      MP_TAC lt THEN MP_TAC ne) THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* which for a store into a byte array is the heap transfer that
   the lemmas about the invariant of another reference ask for *)
let heap_lookup_byte_other = prove
 (cake_as_vars (fun () ->
    `heap_lookup p (ha ++ [Bytes be fl xs ws] ++ hb) =
       SOME (Bytes be fl xs ws) /\
     p = heap_length ha /\
     LENGTH xs = LENGTH ys
     ==> !m y. ~(m = p) /\
               heap_lookup m (ha ++ [Bytes be fl xs ws] ++ hb) =
                 SOME y
               ==> heap_lookup m (ha ++ [Bytes be fl ys ws] ++ hb) =
                     SOME y`),
  STRIP_TAC THEN
  FIRST_X_ASSUM (fun e ->
    let c = concl e in
    if not (is_eq c) || not (is_var (lhand c)) ||
       not (hd_is "heap_length" (rand c)) then fail() else
    SUBST_ALL_TAC e) THEN
  W(fun (asl,w as gl) ->
    let hl = the_asm (fun c -> is_eq c &&
               hd_is "heap_lookup" (lhand c)) gl in
    let old = el 1 (snd (strip_comb (lhand (concl hl)))) in
    let u = lhand (lhand (rand old)) in
    let nw = byte_heap_not u w in
    let v = lhand (lhand (rand nw)) in
    MATCH_ACCEPT_TAC (MP (ISPECL [lhand old; u; v; rand (rand old)]
                            heap_lookup_other_replace)
      (PART_MATCH lhs (GSYM samelen_bytes)
         (list_mk_icomb "el_length" [u])))));;

(* the invariant of the reference written when a byte array is
   stored: the element is the one the store wrote, and the bytes
   are as many as they were *)
let bc_ref_inv_update_byte_at = prove
 (cake_as_vars (fun () ->
    `FLOOKUP (f:(num,num)fmap) ptr = SOME p /\
     heap_lookup p (ha ++ [Bytes be fl xs ws] ++ hb) =
       SOME (Bytes be fl xs ws) /\
     p = heap_length ha /\
     sptree_lookup ptr refs = SOME (bvlSem_ByteArray fl xs) /\
     LENGTH xs = LENGTH ys /\
     ws = REPLICATE (LENGTH xs DIV (dimindex (:'a) DIV 8) + 1)
            ((n2w 0):'a word)
     ==> bc_ref_inv conf ptr (insert ptr (ByteArray fl ys) refs)
           (f,tf2,ha ++ [Bytes be fl ys ws] ++ hb,be)`),
  STRIP_TAC THEN
  W(fun (asl,w as gl) ->
    let lk1 = the_asm (fun c -> is_eq c &&
                hd_is "FLOOKUP" (lhand c)) gl in
    let ins = find_term (hd_is "sptree_insert") w in
    let iargs = snd (strip_comb ins) in
    SUBGOAL_THEN (mk_eq (list_mk_icomb "sptree_lookup"
                           [el 0 iargs; ins],
                         list_mk_icomb "SOME" [el 1 iargs]))
      (fun lkn -> REWRITE_TAC[MATCH_MP arm_BA (CONJ lk1 lkn)]) THENL
     [REWRITE_TAC[lookup_insert]; ALL_TAC]) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  W(fun gl ->
    let pe = the_asm (fun c -> is_eq c && is_var (lhand c) &&
               hd_is "heap_length" (rand c)) gl in
    ONCE_REWRITE_TAC[pe]) THEN
  ASM_REWRITE_TAC[heap_lookup_at]);;
""",

  ('data_to_word_memoryProof', 'memory_rel_bignum_cmp'): r"""
(* the port's own: what the proof of memory_rel_bignum_cmp needs.
   The invariant says of a bignum both that the element of the heap
   holds its header (memory_rel_Number_bignum_header) and what the
   header is made of (memory_rel_Number_bignum_IMP_ALT), of one
   address but with a root of its own each time, so the two are put
   together into one statement (bignum_header) first.  Of two
   bignums whose elements are not one, the signs then cannot be one
   when the lengths are (bignum_cmp_sign), because a header is the
   sign and the length *)

(* the element of the heap that holds a bignum is its header: what
   the invariant says of the number twice over, as the element and
   as the header, is of one address *)
let bignum_elt_eq = prove
 (cake_as_vars (fun () ->
    `(v:'a word_loc) = wordLang_Word w /\
     get_real_addr c st w = SOME a /\ m a = wordLang_Word x /\
     v = wordLang_Word w2 /\ get_real_addr c st w2 = SOME a2 /\
     m a2 = wordLang_Word y
     ==> (x:'a word) = y`),
  REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[injectivity "word_loc"; injectivity "option"]);;

(* of two bignums whose elements are not one: if the headers have
   one length then the signs are not one, because a header is the
   sign and the length *)
let bignum_cmp_sign = prove
 (cake_as_vars (fun () ->
    `(x1:'a word) = make_header c (b2w ((i1:int) < (&0)) << 2 ||
       (n2w 3)) l1 /\
     x2 = make_header c (b2w ((i2:int) < (&0)) << 2 || (n2w 3))
       l2 /\
     decode_length c x1 = n2w l1 /\ decode_length c x2 = n2w l2 /\
     l1 < dimword (:'a) /\ l2 < dimword (:'a) /\
     ((x1 && (n2w 16) = (n2w 0)) <=> (&0) <= i1) /\
     ((x2 && (n2w 16) = (n2w 0)) <=> (&0) <= i2)
     ==> (~(x1 = x2)
          ==> decode_length c x1 = decode_length c x2
          ==> ~(((n2w 16) && x1 = (n2w 0)) <=>
                ((n2w 16) && x2 = (n2w 0))))`),
  STRIP_TAC THEN SPLIT_ASM_TAC THEN
  DISCH_TAC THEN DISCH_TAC THEN
  (* the signs, which the two iffs of the assumptions give once the
     AND of each is in the order that the rewriter puts it *)
  W(fun (asl,_) ->
    let sgs = mapfilter (fun (_,th) ->
                let c = concl th in
                if is_eq c && type_of (lhand c) = bool_ty &&
                   can (find_term (hd_is "word_and")) (lhand c)
                then REWRITE_RULE[WORD_AND_SYM] th else fail()) asl in
    REWRITE_TAC (WORD_AND_SYM :: sgs)) THEN
  STRIP_TAC THEN
  (* the two lengths are one, because the headers' are *)
  SUBGOAL_THEN `(l1:num) = l2` ASSUME_TAC THENL
   [MATCH_MP_TAC n2w_eq_LENGTH THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  (* and so are the signs *)
  FIRST_ASSUM (fun th -> ASSUME_TAC (MATCH_MP int_sign_iff th)) THEN
  (* so the headers are one, which the elements are not *)
  FIRST_X_ASSUM (fun ne ->
    if not (is_neg (concl ne)) || not (is_eq (rand (concl ne)))
    then fail() else MP_TAC (NOT_ELIM ne)) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* what the invariant says of a bignum, with the element of the
   heap read as the header that it is *)
let bignum_header = prove
 (cake_as_vars (fun () ->
    `memory_rel c be ts refs sp st m dm ((Number i,v) :: vars) /\
     ~(small_int (:'a) i) /\ good_dimindex (:'a)
     ==> (?w a x.
            v = wordLang_Word w /\
            get_real_addr c st w = SOME a /\
            m a = wordLang_Word (x:'a word) /\
            x = make_header c (b2w ((i:int) < (&0)) << 2 ||
                  (n2w 3))
                  (LENGTH (n2mw (num_of_int (abs i)):('a word)
                     list)) /\
            decode_length c x = n2w (LENGTH (n2mw (num_of_int
              (abs i)):('a word) list)) /\
            LENGTH (n2mw (num_of_int (abs i)):('a word) list)
              < dimword (:'a) /\
            ((x && (n2w 16) = (n2w 0)) <=> (&0) <= i))`),
  STRIP_TAC THEN
  (* the element of the heap, and the header that the invariant
     says of the same address *)
  W(fun gl ->
    let mr = the_asm (hd_is "memory_rel") gl in
    let ns = the_asm (fun c -> is_neg c &&
               hd_is "small_int" (rand c)) gl in
    let gd = the_asm (hd_is "good_dimindex") gl in
    STRIP_ASSUME_TAC (MATCH_MP memory_rel_Number_bignum_IMP_ALT
      (CONJ mr (CONJ ns gd))) THEN
    STRIP_ASSUME_TAC (MATCH_MP memory_rel_Number_bignum_header
      (CONJ mr (CONJ ns gd)))) THEN
  W(fun (asl,gw as gl) ->
    let mr = the_asm (hd_is "memory_rel") gl in
    let margs = snd (strip_comb (concl mr)) in
    let mem = el 6 margs in
    let vt = rand (lhand (el 8 margs)) in
    let elts = mapfilter (fun (_,th) ->
      let c = concl th in
      if is_eq c && is_comb (lhand c) &&
         rator (lhand c) = mem && hd_is "wordLang_Word" (rand c)
      then th else fail()) asl in
    let triple e =
      let a = rand (lhand (concl e)) in
      let ga = the_asm (fun c -> is_eq c &&
                 hd_is "get_real_addr" (lhand c) &&
                 rand (rand c) = a) gl in
      let wv = el 2 (snd (strip_comb (lhand (concl ga)))) in
      let vw = the_asm (fun c -> is_eq c && lhand c = vt &&
                 rand c = list_mk_icomb "wordLang_Word" [wv]) gl in
      (vw,ga,e) in
    let alt = find (fun e -> is_var (rand (rand (concl e)))) elts in
    let hdr = find (fun e ->
                not (is_var (rand (rand (concl e))))) elts in
    let (va,ga,ma) = triple alt in
    let (vh,gh,mh) = triple hdr in
    let xeq = MATCH_MP bignum_elt_eq
                (CONJ va (CONJ ga (CONJ ma
                  (CONJ vh (CONJ gh mh))))) in
    MAP_EVERY EXISTS_TAC
      [el 2 (snd (strip_comb (lhand (concl ga))));
       rand (lhand (concl ma)); rand (rand (concl ma))] THEN
    REPEAT CONJ_TAC THEN
    TRY (SOLVED (FIRST_ASSUM ACCEPT_TAC)) THEN
    TRY (SOLVED (ACCEPT_TAC xeq))));;
""",

  ('data_to_word_memoryProof', 'gc_kind_update_Ref'): r"""
(* the port's own: what the proof of gc_kind_update_Ref needs.  The
   store writes an element of the length it replaces, and the
   element is a reference, so it is at or above the pointer -- the
   first half of the split of a generational heap holds no
   reference.  The halves of the new split are then the first one
   it was and the second with the element written in it
   (heap_split_replace3), and the state of the generations is the
   one it was, because every start of one is at or below the
   pointer (gen_start_ok_replace, gen_state_ok_replace) *)

(* two elements of one length and one tag are of one length *)
let el_length_DataElement = prove
 (`!(xs:((A)heap_address)list) (ys:((A)heap_address)list) l (d:B).
     el_length (DataElement xs l d) = el_length (DataElement ys l d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[el_length_def]);;

(* an element of a reference is a reference *)
let isRef_RefTag = prove
 (`data_to_word_memoryProof_isRef (DataElement xs l (RefTag,[]))`,
  REWRITE_TAC[isRef_def] THEN MATCH_REDUCE_TAC THEN
  REWRITE_TAC[isMutTag_def]);;

(* the halves of the split of a heap whose element is replaced by
   one of its length, when the cut is at or before the element: the
   first half is the one it was, and the second is the one it was
   with the element replaced *)
let heap_split_replace3 = prove
 (`!e ha u v hb h1 h2.
     heap_split e (ha ++ [u] ++ hb) = SOME (h1,h2) /\
     el_length u = el_length v /\ ~(heap_length ha < e)
     ==> ?h2'. heap_split e (ha ++ [v] ++ hb) = SOME (h1,h2') /\
               (!z. MEM z h2' ==> MEM z h2 \/ z = v)`,
  REPEAT GEN_TAC THEN
  (* the element and what follows it, as one list: a split of the
     heap is then a split of the front or of that list *)
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[heap_split_SOME_APPEND] THEN
  COND_CASES_TAC THEN
  STRIP_TAC THEN SPLIT_ASM_TAC THEN
  REPEAT (FIRST_X_ASSUM (fun th ->
    if is_exists (concl th) then CHOOSE_TAC th else fail())) THEN
  SPLIT_ASM_TAC THENL
   [(* the cut is below the element, so the halves of the front are
       the ones they were and the element is in the second *)
    W(fun (asl,w as gl) ->
      let hs = the_asm (fun c -> is_eq c &&
                 hd_is "heap_split" (lhand c)) gl in
      let pr = rand (rand (concl hs)) in
      let vt = find_term (fun t -> is_var t &&
                 fst (dest_var t) = "v") w in
      let hb = find_term (fun t -> is_var t &&
                 fst (dest_var t) = "hb") w in
      let tail = list_mk_icomb "CONS" [vt; hb] in
      EXISTS_TAC (list_mk_icomb "APPEND" [rand pr; tail]) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[] THEN
        EXISTS_TAC (lhand pr) THEN EXISTS_TAC (rand pr) THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[MEM_APPEND; MEM] THEN MESON_TAC[]]);
    (* and the cut is at the element, so the first half is what is
       before it and the second begins with the element *)
    W(fun (asl,w as gl) ->
      let sub = in_goal gl (fun t -> hd_is "-" t &&
                  hd_is "heap_length" (rand t)) in
      SUBGOAL_THEN (mk_eq (sub, `0`)) ASSUME_TAC THENL
       [W(fun (asl,_) ->
          MAP_EVERY MP_TAC (mapfilter (fun (_,th) ->
            let c = concl th in
            if is_neg c && hd_is "<" (rand c) then th else fail())
            asl)) THEN
        ARITH_TAC;
        ALL_TAC]) THEN
    W(fun gl ->
      let z = the_asm (fun c -> is_eq c && hd_is "-" (lhand c) &&
                rand c = `0`) gl in
      RULE_ASSUM_TRY (REWRITE_RULE[z; heap_split_def;
        injectivity "option"; PAIR_EQ]) THEN
      REWRITE_TAC[z]) THEN
    SPLIT_ASM_TAC THEN
    REPEAT (FIRST_X_ASSUM (fun e ->
      let c = concl e in
      if not (is_eq c) || not (is_var (rand c)) then fail() else
      SUBST_ALL_TAC (SYM e))) THEN
    W(fun (asl,w) ->
      let vt = find_term (fun t -> is_var t &&
                 fst (dest_var t) = "v") w in
      let hb = find_term (fun t -> is_var t &&
                 fst (dest_var t) = "hb") w in
      EXISTS_TAC (list_mk_icomb "CONS" [vt; hb])) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[heap_split_def; injectivity "option";
                      PAIR_EQ] THEN
      CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
      ASM_REWRITE_TAC[APPEND_NIL];
      ASM_REWRITE_TAC[MEM] THEN MESON_TAC[]]]);;

(* the pointer condition of a generation survives a store that
   writes an element of the length it replaces at or above the
   start of the generation: the half that the condition is about is
   the one it was (heap_split_replace3) *)
let gen_start_ok_replace = prove
 (cake_as_vars (fun () ->
    `gen_start_ok (ha ++ [u] ++ hb) k s /\
     el_length u = el_length v /\ ~(heap_length ha < s)
     ==> gen_start_ok (ha ++ [v] ++ hb) k s`),
  REWRITE_TAC[gen_start_ok_def] THEN
  STRIP_TAC THEN SPLIT_ASM_TAC THEN
  REPEAT (FIRST_X_ASSUM (fun th ->
    if is_exists (concl th) then CHOOSE_TAC th else fail())) THEN
  SPLIT_ASM_TAC THEN
  W(fun gl ->
    let hs = the_asm (fun c -> is_eq c &&
               hd_is "heap_split" (lhand c)) gl in
    let le = the_asm (fun c -> is_eq c &&
               hd_is "el_length" (lhand c)) gl in
    let lt = the_asm (fun c -> is_neg c && hd_is "<" (rand c)) gl in
    STRIP_ASSUME_TAC (MATCH_MP heap_split_replace3
      (CONJ hs (CONJ le lt)))) THEN
  W(fun (asl,w as gl) ->
    let vt = find_term (fun t -> is_var t &&
               fst (dest_var t) = "v") w in
    let hs2 = the_asm (fun c -> is_eq c &&
                hd_is "heap_split" (lhand c) &&
                can (find_term (fun t -> t = vt)) (lhand c)) gl in
    let pr = rand (rand (concl hs2)) in
    EXISTS_TAC (lhand pr) THEN EXISTS_TAC (rand pr) THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC));;

(* and so does the state of the generations, because every start of
   one is at or below the pointer and the element is above it *)
let gen_state_ok_replace = prove
 (cake_as_vars (fun () ->
    `gen_state_ok a k (ha ++ [u] ++ hb) gens /\
     el_length u = el_length v /\ ~(heap_length ha < a)
     ==> gen_state_ok a k (ha ++ [v] ++ hb) gens`),
  W(fun (asl,w) ->
    let gens = find_term (fun t -> is_var t &&
                 fst (dest_var t) = "gens") w in
    STRUCT_CASES_TAC (ISPEC gens (cases_of `:gen_state`))) THEN
  REWRITE_TAC[gen_state_ok_def] THEN
  STRIP_TAC THEN SPLIT_ASM_TAC THEN
  CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT STRIP_TAC THEN
  W(fun gl ->
    let mm = the_asm (hd_is "MEM") gl in
    let s = el 0 (snd (strip_comb (concl mm))) in
    let evs = mapfilter (fun (_,th) ->
      let c = concl th in
      if hd_is "ALL" c then
        MP (SPEC s (REWRITE_RULE[GSYM ALL_MEM] th)) mm
      else fail()) (fst gl) in
    MAP_EVERY (fun th ->
      ASSUME_TAC (CONV_RULE(TOP_DEPTH_CONV BETA_CONV) th)) evs) THEN
  W(fun gl ->
    let le = the_asm (fun c -> is_eq c &&
               hd_is "el_length" (lhand c)) gl in
    let gs = the_asm (hd_is "gen_start_ok") gl in
    let s = el 2 (snd (strip_comb (concl gs))) in
    let lt = the_asm (fun c -> is_neg c && hd_is "<" (rand c)) gl in
    let sle = the_asm (fun c -> hd_is "<=" c && lhand c = s) gl in
    let hl = lhand (rand (concl lt)) in
    SUBGOAL_THEN (mk_neg (list_mk_icomb "<" [hl; s]))
      (fun nlt -> MATCH_ACCEPT_TAC (MATCH_MP gen_start_ok_replace
         (CONJ gs (CONJ le nlt)))) THEN
    MP_TAC lt THEN MP_TAC sle THEN ARITH_TAC));;
""",

  ('data_to_word_memoryProof', 'abs_ml_inv_stack_permute'): r"""
(* the port's own: what the proof of abs_ml_inv_stack_permute
   needs.  The stack changes and the references and the heap do
   not, so every transfer of the generic machinery above
   update_ref_thm is the identity here and what is left is the
   timestamps: they are cut to the ones of the new stack, which is
   what v_inv_restrict_gen, EVERY2_v_inv_restrict (the values of a
   stack), EVERY2_v_inv_restrict_gen (the values of the arm of a
   reference, the other way round -- entry 53) and
   bc_ref_inv_restrict say.  The pairs of the new stack are pairs
   of the old one, which is what the four after them say of the
   roots, of a map and of the relation between the values and the
   roots *)

(* what the invariant says of a value, of the values of a stack and
   of the values of the arm of a reference, with the timestamps cut
   to the ones of a stack: the references and the heap are the ones
   they were, so the transfer of each generic lemma is the identity *)
let v_inv_restrict_gen = prove
 (cake_as_vars (fun () ->
    `v_inv conf v1 refs (v2,f,tf,heap) /\
     v1 IN all_vs refs stack'
     ==> v_inv conf v1 refs
           (v2,f,DRESTRICT tf (all_ts refs stack'),heap)`),
  STRIP_TAC THEN
  MATCH_MP_TAC v_inv_update_gen THEN
  REPEAT CONJ_TAC THEN
  TRY (SOLVED (FIRST_ASSUM ACCEPT_TAC)) THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let EVERY2_v_inv_restrict = prove
 (cake_as_vars (fun () ->
    `(!v. MEM v vs ==> v IN all_vs refs stack') /\
     EVERY2 (\v x. v_inv conf v refs (x,f,tf,heap)) vs rs
     ==> EVERY2 (\v x. v_inv conf v refs
           (x,f,DRESTRICT tf (all_ts refs stack'),heap)) vs rs`),
  STRIP_TAC THEN
  MATCH_MP_TAC EVERY2_v_inv_update_stack THEN
  REPEAT CONJ_TAC THEN
  TRY (SOLVED (FIRST_ASSUM ACCEPT_TAC)) THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let EVERY2_v_inv_restrict_gen = prove
 (cake_as_vars (fun () ->
    `(!v. MEM v ys ==> v IN all_vs refs stack') /\
     EVERY2 (\z y. v_inv conf y refs (z,f,tf,heap)) zs ys
     ==> EVERY2 (\z y. v_inv conf y refs
           (z,f,DRESTRICT tf (all_ts refs stack'),heap)) zs ys`),
  STRIP_TAC THEN
  MATCH_MP_TAC EVERY2_v_inv_update_gen THEN
  REPEAT CONJ_TAC THEN
  TRY (SOLVED (FIRST_ASSUM ACCEPT_TAC)) THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* the values of the arm of a reference are values of the stack,
   whichever arm it is: the lemma that says so is the argument *)
let EVERY2_ARM_RESTRICT_TAC memlem =
  W(fun (asl,w as gl) ->
    let ats = find_term (hd_is "all_ts") w in
    let refs2 = lhand ats in
    let ys = el 2 (snd (strip_comb w)) in
    let v = genvar (hd (snd (dest_type (type_of (rand ats))))) in
    SUBGOAL_THEN
      (mk_forall(v, mk_imp(list_mk_icomb "MEM" [v; ys],
         list_mk_icomb "IN"
           [v; list_mk_icomb "all_vs" [refs2; rand ats]])))
      (fun mem ->
         let old = the_asm (hd_is "ALL2") gl in
         MATCH_ACCEPT_TAC (MATCH_MP EVERY2_v_inv_restrict_gen
           (CONJ mem old))) THEN
    REPEAT STRIP_TAC THEN
    W(fun gl ->
      let mm = the_asm (hd_is "MEM") gl in
      MATCH_ACCEPT_TAC (MATCH_MP memlem
        (CONJ (a_lkref refs2 gl) mm))));;

(* and so the invariant of a reference with the timestamps cut *)
let bc_ref_inv_restrict = prove
 (cake_as_vars (fun () ->
    `bc_ref_inv conf n refs ((f:(num,num)fmap),tf,heap,be')
     ==> bc_ref_inv conf n refs
           (f,DRESTRICT tf (all_ts refs stack'),heap,be')`),
  STRIP_TAC THEN
  (* the key has an address *)
  FIRST_ASSUM (fun inv ->
    if not (hd_is "bc_ref_inv" (concl inv)) then fail() else
    CHOOSE_THEN ASSUME_TAC (MATCH_MP bc_ref_inv_FLOOKUP inv)) THEN
  (* and the kind of what the key holds says which arm it is *)
  W(fun gl ->
    let inv = the_asm (hd_is "bc_ref_inv") gl in
    let args = snd (strip_comb (concl inv)) in
    NAMED_CASES_TAC (list_mk_icomb "sptree_lookup"
                       [el 1 args; el 2 args]) [[]; ["rv"]]) THEN
  TRY (SOLVED (FIRST_X_ASSUM (fun inv ->
    if not (hd_is "bc_ref_inv" (concl inv)) then fail() else
    MP_TAC (REWRITE_RULE[bc_ref_inv_def] inv)) THEN
    ASM_REWRITE_TAC[] THEN REDUCE_MATCH_HARD)) THEN
  NAMED_CASES_TAC (cake_as_vars (fun () ->
    `rv:(dataSem_v)bvlSem_ref`))
    [["l"]; ["flag"; "bs"]; ["ev"; "vv"];
     ["tg"; "fin"; "ll"; "cc"; "rr"]] THEN
  USE_ARMS THEN
  SPLIT_ASM_TAC THEN
  REPEAT (FIRST_X_ASSUM (fun th ->
    if is_exists (concl th) then CHOOSE_TAC th else fail())) THEN
  SPLIT_ASM_TAC THEN
  (* the array of values: the element is where it was and its
     values are values of the stack *)
  TRY (SOLVED
        (W(fun gl ->
           let hl = the_asm (fun c -> is_eq c &&
                      hd_is "heap_lookup" (lhand c) &&
                      hd_is "SOME" (rand c)) gl in
           EXISTS_TAC (rand (rand (rand (concl hl)))) THEN
           CONJ_TAC THENL
            [ACCEPT_TAC hl;
             EVERY2_ARM_RESTRICT_TAC MEM_ref_all_vs]))) THEN
  (* the array of bytes: only the element *)
  TRY (SOLVED
        (CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
         RULE_ASSUM_TRY (CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
         FIRST_ASSUM ACCEPT_TAC)) THEN
  (* the thunk: the element, that it is still not a thunk, and its
     value *)
  TRY (SOLVED
        (W(fun gl ->
           let hl = the_asm (fun c -> is_eq c &&
                      hd_is "heap_lookup" (lhand c) &&
                      hd_is "SOME" (rand c)) gl in
           EXISTS_TAC (rand (rand (rand (concl hl)))) THEN
           REPEAT CONJ_TAC THEN
           TRY (SOLVED (ACCEPT_TAC hl)) THEN
           TRY (SOLVED (FIRST_ASSUM ACCEPT_TAC)) THEN
           W(fun (asl,w as gl) ->
             let vi = the_asm (hd_is "v_inv") gl in
             let refs2 = lhand (find_term (hd_is "all_ts") w) in
             let inn = MATCH_MP MEM_thunk_all_vs
                         (a_lkref refs2 gl) in
             MATCH_ACCEPT_TAC (MATCH_MP v_inv_restrict_gen
               (CONJ vi inn)))))) THEN
  (* the mutable block: the kind of the collection, the address
     that no timestamp has, the element and its values *)
  TRY (SOLVED
        (REPEAT CONJ_TAC THEN
         TRY (SOLVED (FIRST_ASSUM ACCEPT_TAC)) THEN
         TRY (SOLVED
               (W(fun gl ->
                  let impl = the_asm (fun c -> is_imp c &&
                               is_neg (lhand c) &&
                               is_neg (rand c)) gl in
                  DISCH_THEN (fun nf -> MATCH_ACCEPT_TAC
                    (MATCH_MP IMAGE_DRESTRICT_NOT (MP impl nf)))))) THEN
         W(fun gl ->
           let hl = the_asm (fun c -> is_eq c &&
                      hd_is "heap_lookup" (lhand c) &&
                      hd_is "SOME" (rand c)) gl in
           EXISTS_TAC (rand (rand (rand (concl hl)))) THEN
           CONJ_TAC THENL
            [ACCEPT_TAC hl;
             EVERY2_ARM_RESTRICT_TAC MEM_mutblock_all_vs]))));;

(* the roots of a stack that the other stack has are good when the
   other's are *)
let roots_ok_subset = prove
 (`(!x. MEM x rs2 ==> MEM x rs1) /\ roots_ok rs1 heap
   ==> roots_ok rs2 heap`,
  REWRITE_TAC[roots_ok_def] THEN MESON_TAC[]);;

(* and what one list of pairs has of the other, after a map *)
let MEM_MAP_subset = prove
 (`!(g:A->B) ys xs l.
     (!p. MEM p ys ==> MEM p xs)
     ==> !x. MEM x (MAP g ys ++ l) ==> MEM x (MAP g xs ++ l)`,
  REWRITE_TAC[MEM_APPEND; MEM_MAP] THEN MESON_TAC[]);;

(* a relation between the values and the roots of a list of pairs
   holds of every list of its pairs *)
let EVERY2_FST_SND_subset = prove
 (`!(P:A->B->bool) ys xs.
     (!p. MEM p ys ==> MEM p xs) /\
     EVERY2 P (MAP FST xs) (MAP SND xs)
     ==> EVERY2 P (MAP FST ys) (MAP SND ys)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EVERY2_MAP_FST_SND; GSYM ALL_MEM] THEN
  MESON_TAC[]);;

(* so the values of a stack that the other stack has are related to
   their roots when the other's are *)
let EVERY2_stack_permute = prove
 (cake_as_vars (fun () ->
    `(!p. MEM p ys ==> MEM p xs) /\
     EVERY2 P (MAP FST xs ++ stack) (MAP SND xs ++ roots)
     ==> EVERY2 P (MAP FST ys ++ stack) (MAP SND ys ++ roots)`),
  STRIP_TAC THEN
  W(fun gl ->
    let old = the_asm (hd_is "ALL2") gl in
    let args = snd (strip_comb (concl old)) in
    let l1 = lhand (el 1 args) in
    let l2 = lhand (el 2 args) in
    let leq = prove(mk_eq (list_mk_icomb "LENGTH" [l1],
                           list_mk_icomb "LENGTH" [l2]),
                    REWRITE_TAC[LENGTH_MAP]) in
    STRIP_ASSUME_TAC (MATCH_MP LIST_REL_APPEND_IMP
      (CONJ old leq))) THEN
  MATCH_MP_TAC LIST_REL_APPEND_I THEN
  CONJ_TAC THEN
  TRY (SOLVED (FIRST_ASSUM ACCEPT_TAC)) THEN
  W(fun gl ->
    let sub = the_asm (fun c ->
                length (fst (strip_forall c)) = 1 &&
                is_imp (snd (strip_forall c)) &&
                hd_is "MEM" (lhand (snd (strip_forall c)))) gl in
    let e2 = the_asm (fun c -> hd_is "ALL2" c &&
               hd_is "MAP" (el 1 (snd (strip_comb c)))) gl in
    MATCH_ACCEPT_TAC (MATCH_MP EVERY2_FST_SND_subset
      (CONJ sub e2))));;
""",

  ('data_to_word_memoryProof', 'word_ml_inv_rearrange'): r"""
(* the port's own: what the proof of word_ml_inv_rearrange needs.
   The roots of the new stack are the ones the old stack gave its
   pairs, which the lookup of a pair in the association of the old
   stack with its roots finds (ALOOKUP_root); the relation between
   the values and the roots then holds pair by pair
   (EVERY2_rearrange_roots), and the invariant itself is
   abs_ml_inv_stack_permute with nothing on the stack but the pairs
   (abs_ml_inv_rearrange, which has to say the stack of the one and
   of the other as a MAP over one list of pairs) *)

(* the root that a pair of the stack has: the pairs before the
   first one that is it are not it, so the lookup lands there *)
let ALOOKUP_root = prove
 (`!(xs:(A)list) (hs:(B)list) y.
     LENGTH hs = LENGTH xs /\ MEM y xs
     ==> ?n. n < LENGTH xs /\ EL n xs = y /\
             THE (ALOOKUP (ZIP xs hs) y) = EL n hs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPLIT_ASM_TAC THEN
  FIRST_X_ASSUM (fun m ->
    if not (hd_is "MEM" (concl m)) then fail() else
    STRIP_ASSUME_TAC (REWRITE_RULE[MEM_FIRST_EL] m)) THEN
  W(fun gl ->
    let eq = the_asm (fun c -> is_eq c && hd_is "EL" (lhand c)) gl in
    EXISTS_TAC (lhand (lhand (concl eq)))) THEN
  REPEAT CONJ_TAC THEN
  TRY (SOLVED (FIRST_ASSUM ACCEPT_TAC)) THEN
  W(fun gl ->
    let eq = the_asm (fun c -> is_eq c && hd_is "EL" (lhand c)) gl in
    let lt = the_asm (fun c -> hd_is "<" c) gl in
    let le = the_asm (fun c -> is_eq c &&
               hd_is "LENGTH" (lhand c)) gl in
    let mn = the_asm (fun c ->
               length (fst (strip_forall c)) = 1 &&
               is_imp (snd (strip_forall c)) &&
               is_neg (rand (snd (strip_forall c)))) gl in
    let al = MATCH_MP ALOOKUP_ZIP_EL (CONJ lt (CONJ le mn)) in
    MATCH_ACCEPT_TAC (MATCH_MP IMP_THE_EQ
      (ONCE_REWRITE_RULE[eq] al))));;

(* the roots of a stack that the other stack has: each pair of the
   one is a pair of the other, and the lookup finds its root *)
let EVERY2_rearrange_roots = prove
 (`!(P:C->B->bool) (ys:(A#B)list) xs (hs:(C)list).
     (!x. MEM x ys ==> MEM x xs) /\ LENGTH hs = LENGTH xs /\
     ALL2 P hs (MAP SND xs)
     ==> ALL2 P (MAP (\y. THE (ALOOKUP (ZIP xs hs) y)) ys)
                (MAP SND ys)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPLIT_ASM_TAC THEN
  REWRITE_TAC[EVERY2_MAP_MAP; GSYM ALL_MEM] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT STRIP_TAC THEN
  (* the pair is one of the old stack, so the lookup finds the
     root that the old stack gave it *)
  W(fun gl ->
    let m = the_asm (hd_is "MEM") gl in
    let sub = the_asm (fun c ->
                length (fst (strip_forall c)) = 1 &&
                is_imp (snd (strip_forall c)) &&
                hd_is "MEM" (rand (snd (strip_forall c)))) gl in
    let le = the_asm (fun c -> is_eq c &&
               hd_is "LENGTH" (lhand c)) gl in
    STRIP_ASSUME_TAC (MATCH_MP ALOOKUP_root
      (CONJ le (MP (SPEC (el 0 (snd (strip_comb (concl m)))) sub)
                  m)))) THEN
  W(fun gl ->
    let thq = the_asm (fun c -> is_eq c &&
                hd_is "THE" (lhand c)) gl in
    let eqy = the_asm (fun c -> is_eq c &&
                hd_is "EL" (lhand c)) gl in
    let e2 = the_asm (hd_is "ALL2") gl in
    let le = the_asm (fun c -> is_eq c &&
               hd_is "LENGTH" (lhand c)) gl in
    let lt = the_asm (fun c -> hd_is "<" c) gl in
    let n = lhand (lhand (concl eqy)) in
    let xs = rand (lhand (concl eqy)) in
    let el = MATCH_MP ALL2_EL
               (CONJ e2 (ONCE_REWRITE_RULE[GSYM le] lt)) in
    let mp = MP (ISPECL [lhand (rand (concl e2)); n; xs]
                   EL_MAP) lt in
    ONCE_REWRITE_TAC[thq] THEN
    ACCEPT_TAC (REWRITE_RULE[mp; eqy] el)));;

(* abs_ml_inv_stack_permute with nothing on the stack but the
   pairs, which is how HOL4 instantiates it as well *)
let abs_ml_inv_stack_permute_nil =
  let th = abs_ml_inv_stack_permute in
  let fvs = frees (concl th) in
  let pick n = find (fun v -> fst (dest_var v) = n) fvs in
  let nil_like v = rand (lhand (concl (ISPEC v APPEND_NIL))) in
  let st = pick "stack" and rt = pick "roots" in
  REWRITE_RULE[APPEND_NIL]
    (INST [nil_like st,st; nil_like rt,rt] th);;

(* the invariant over a stack that the other stack has: the pairs
   of the one are pairs of the other, with the root that the lookup
   finds, so the lemma above says it *)
let abs_ml_inv_rearrange = prove
 (cake_as_vars (fun () ->
    `(!x. MEM x ys ==> MEM x xs) /\ LENGTH hs = LENGTH xs /\
     abs_ml_inv conf (MAP FST xs) refs
       (hs,heap,be,a,sp,sp1,gens) limit ts
     ==> abs_ml_inv conf (MAP FST ys) refs
           (MAP (\y. THE (ALOOKUP (ZIP xs hs) y)) ys,
            heap,be,a,sp,sp1,gens) limit ts`),
  STRIP_TAC THEN SPLIT_ASM_TAC THEN
  W(fun (asl,w as gl) ->
    let inv = the_asm (hd_is "abs_ml_inv") gl in
    let iargs = snd (strip_comb (concl inv)) in
    let fstm = lhand (el 1 iargs) in
    let xs = rand (el 1 iargs) in
    let hs = el 0 (tparts (el 3 iargs)) in
    let gargs = snd (strip_comb w) in
    let ys = rand (el 1 gargs) in
    let rts = el 0 (tparts (el 3 gargs)) in
    let g = lhand rts in
    let v,bod = dest_abs g in
    let pairf = mk_abs (v, mk_pair (mk_comb (fstm,v), bod)) in
    let pty = type_of v in
    let vty = hd (snd (dest_type pty)) in
    let rty = type_of bod in
    let zpty = mk_type("prod",[vty; rty]) in
    let fstz = mk_mconst("FST", mk_fun_ty zpty vty) in
    let sndz = mk_mconst("SND", mk_fun_ty zpty rty) in

    let zs = list_mk_icomb "MAP" [pairf; ys] in

    let ws = list_mk_icomb "ZIP"
               [list_mk_icomb "MAP" [fstm; xs]; hs] in
    let le = the_asm (fun c -> is_eq c &&
               hd_is "LENGTH" (lhand c)) gl in
    let lz = TRANS (ISPECL [xs; fstm] LENGTH_MAP) (SYM le) in

    let maps = [MATCH_MP MAP_FST_ZIP lz; MATCH_MP MAP_SND_ZIP lz] in

    let lv = genvar (type_of ys) in
    let mapstep = LIST_INDUCT_TAC THEN REWRITE_TAC[MAP] THEN
                  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
                  ASM_REWRITE_TAC[FST; SND] in
    let eq1 = SPEC ys (prove(mk_forall(lv,
                 mk_eq (list_mk_icomb "MAP"
                          [fstz; list_mk_icomb "MAP" [pairf; lv]],
                        list_mk_icomb "MAP" [fstm; lv])),
                 mapstep)) in
    let eq2 = SPEC ys (prove(mk_forall(lv,
                 mk_eq (list_mk_icomb "MAP"
                          [sndz; list_mk_icomb "MAP" [pairf; lv]],
                        list_mk_icomb "MAP" [g; lv])),
                 mapstep)) in

    let perm = REWRITE_RULE (eq1 :: eq2 :: maps)
                 (ISPECL [ws; zs] abs_ml_inv_stack_permute_nil) in
    (* the pairs of the new stack are pairs of the old one: the
       root of each is the one the lookup finds *)
    SUBGOAL_THEN (list_mk_icomb "SUBSET"
                    [list_mk_icomb "set_of_list" [zs];
                     list_mk_icomb "set_of_list" [ws]])
      (fun ss -> MATCH_ACCEPT_TAC (MATCH_MP perm (CONJ inv ss))) THEN
    (REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_MAP] THEN
      REPEAT STRIP_TAC THEN
      W(fun gl ->
        let m = the_asm (fun c -> hd_is "MEM" c) gl in
        let sub = the_asm (fun c ->
                    length (fst (strip_forall c)) = 1 &&
                    is_imp (snd (strip_forall c)) &&
                    hd_is "MEM" (rand (snd (strip_forall c)))) gl in
        STRIP_ASSUME_TAC (MATCH_MP ALOOKUP_root
          (CONJ le (MP (SPEC (el 0 (snd (strip_comb (concl m)))) sub)
                      m)))) THEN
      W(fun (asl,w as gl) ->
        let eqy = the_asm (fun c -> is_eq c &&
                    hd_is "EL" (lhand c)) gl in
        let thq = the_asm (fun c -> is_eq c &&
                    hd_is "THE" (lhand c)) gl in
        let lt = the_asm (fun c -> hd_is "<" c) gl in
        let n = lhand (lhand (concl eqy)) in
        let ltm = ONCE_REWRITE_RULE
                    [SYM (ISPECL [xs; fstm] LENGTH_MAP)] lt in
        let mem = MP (ISPECL [list_mk_icomb "MAP" [fstm; xs]; hs; n]
                        MEM_ZIP_EL) (CONJ ltm (SYM lz)) in
        let elm = MP (ISPECL [fstm; n; xs] EL_MAP) lt in
        ASM_REWRITE_TAC[] THEN
        CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
        ASM_REWRITE_TAC[] THEN
        ACCEPT_TAC (REWRITE_RULE[elm; eqy; thq] mem)))));;
""",

  ('data_to_word_memoryProof', 'IMP_heap_store_unused'): r"""
(* the clauses of heap_length, which the lemmas of this block and
   of the ones after it rewrite with *)
let heap_length_clauses = prove
 (`heap_length [] = 0 /\
   (!x xs. heap_length (CONS x xs) =
           el_length x + heap_length xs)`,
  REWRITE_TAC[heap_length_def; MAP; SUM_DEF; ITLIST]);;

(* the port's own: what the proof of IMP_heap_store_unused needs.
   A store into the unused space writes the space that is left, the
   element, and what followed the space -- an append of four, which
   the rewriter puts to the right.  The element is then at the end
   of what was unused (heap_lookup_at_end) and the space that is
   left in front of it (heap_lookup_unused_left); outside the space
   the heap is the one it was (heap_lookup_store_outside), because
   the space and what the store wrote into it are of one length,
   and inside it neither heap holds data
   (heap_lookup_store_inside, heap_lookup_in_unused).  The last two
   put those together into what the theorem says of the addresses
   that hold data (isSome_store_unused) and of the elements the
   heap keeps (heap_store_rel_store_unused) *)

(* a store into the unused space writes the space that is left, the
   element, and what followed; the element is at the end of what
   was unused and the space that is left is in front of it *)
let heap_lookup_at_end = prove
 (`!ha k x hb.
     heap_lookup (heap_length ha + k)
       (ha ++ ((heap_expand k ++ [x]) ++ hb)) = SOME x`,
  REPEAT GEN_TAC THEN
  W(fun (asl,w) ->
    MP_TAC (ISPEC (rand (rand w)) el_length_GT_0)) THEN
  DISCH_TAC THEN
  REWRITE_TAC[data_to_word_memoryProof_heap_lookup_APPEND;
              heap_length_APPEND; heap_length_heap_expand;
              heap_length_clauses; ADD_CLAUSES; LT_REFL; SUB_REFL;
              heap_lookup_def] THEN
  REPEAT (CHANGED_TAC
            (COND_CASES_TAC THEN
             ASM_REWRITE_TAC[heap_lookup_def; LT_REFL; SUB_REFL;
                             ADD_CLAUSES])) THEN
  TRY (SOLVED (ASM_ARITH_TAC)));;

let heap_lookup_unused_left = prove
 (`!ha k x hb.
     ~(k = 0) ==>
     heap_lookup (heap_length ha)
       (ha ++ ((heap_expand k ++ [x]) ++ hb)) = SOME (Unused (k - 1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[heap_expand_def] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[data_to_word_memoryProof_heap_lookup_APPEND;
              heap_length_APPEND; heap_length_clauses;
              ADD_CLAUSES; LT_REFL; SUB_REFL; heap_lookup_def;
              el_length_def] THEN
  REPEAT (CHANGED_TAC
            (COND_CASES_TAC THEN
             ASM_REWRITE_TAC[heap_lookup_def; LT_REFL; SUB_REFL;
                             ADD_CLAUSES; el_length_def])) THEN
  TRY (SOLVED (ASM_ARITH_TAC)));;

(* outside the space that the store wrote, the heap is the one it
   was: what is before it is where it was, and what follows it is
   as far from the front as it was, because the space and what was
   written into it are of one length *)
let heap_lookup_store_outside = prove
 (`!ha sp e x hb y.
     ~(sp = 0) /\ el_length x = e /\ e <= sp /\
     (y < heap_length ha \/ heap_length ha + sp <= y)
     ==> heap_lookup y (ha ++ ((heap_expand (sp - e) ++ [x]) ++ hb)) =
         heap_lookup y (ha ++ (Unused (sp - 1) :: hb))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPLIT_ASM_TAC THENL
   [(* before the space: the lookup lands in the front *)
    W(fun gl ->
      let lt = the_asm (fun c -> hd_is "<" c &&
                 hd_is "heap_length" (rand c)) gl in
      REWRITE_TAC[MATCH_MP LESS_IMP_heap_lookup lt]);
    (* and past it: the front and the space are as long as they
       were *)
    W(fun (asl,w as gl) ->
      let ge = the_asm (fun c -> hd_is "<=" c &&
                 hd_is "+" (lhand c)) gl in
      let a = lhand (lhand (concl ge)) in
      let sp = rand (lhand (concl ge)) in
      let y = rand (concl ge) in
      let nlt = MP (ISPECL [a; sp; y] (ARITH_RULE
                  `!a s y. (a:num) + s <= y ==> ~(y < a)`)) ge in
      REWRITE_TAC[MATCH_MP NOT_LESS_IMP_heap_lookup nlt]) THEN
    W(fun gl ->
      let le = the_asm (fun c -> hd_is "<=" c &&
                 not (hd_is "+" (lhand c))) gl in
      let eq = the_asm (fun c -> is_eq c &&
                 hd_is "el_length" (lhand c)) gl in
      let sp = rand (concl le) in
      let e = lhand (concl le) in
      let ne0 = the_asm (fun c -> is_neg c && is_eq (rand c) &&
                  rand (rand c) = `0`) gl in
      let seq = MP (ISPECL [sp; e] (ARITH_RULE
                  `!s e. (e:num) <= s ==> (s - e) + e = s`)) le in
      let s1 = MP (ISPEC sp (ARITH_RULE
                 `!s. ~((s:num) = 0) ==> s - 1 + 1 = s`)) ne0 in
      REWRITE_TAC[data_to_word_memoryProof_heap_lookup_APPEND;
                  heap_length_APPEND; heap_length_heap_expand;
                  heap_length_clauses; ADD_CLAUSES; eq; seq; s1;
                  heap_lookup_def; el_length_def]) THEN
    W(fun gl ->
      let ge = the_asm (fun c -> hd_is "<=" c &&
                 hd_is "+" (lhand c)) gl in
      let ne = the_asm (fun c -> hd_is "<=" c &&
                 not (hd_is "+" (lhand c))) gl in
      MP_TAC ge THEN MP_TAC ne) THEN
    REPEAT STRIP_TAC THEN
    REPEAT (CHANGED_TAC
              (COND_CASES_TAC THEN
               ASM_REWRITE_TAC[heap_lookup_def; ADD_CLAUSES])) THEN
    ASM_ARITH_TAC]);;

(* and inside that space, away from the element written, neither
   heap holds data: the one has what is left of the space there and
   the other the space it had *)
let heap_lookup_store_inside = prove
 (`!ha sp e x hb y.
     ~(sp = 0) /\ el_length x = e /\ 1 <= e /\ e <= sp /\
     ~(y < heap_length ha) /\ y < heap_length ha + sp /\
     ~(y = heap_length ha + (sp - e))
     ==> ~isSomeDataElement
           (heap_lookup y
              (ha ++ ((heap_expand (sp - e) ++ [x]) ++ hb))) /\
         ~isSomeDataElement
           (heap_lookup y (ha ++ (Unused (sp - 1) :: hb)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPLIT_ASM_TAC THEN
  W(fun gl ->
    let nlt = the_asm (fun c -> is_neg c && hd_is "<" (rand c) &&
                hd_is "heap_length" (rand (rand c))) gl in
    REWRITE_TAC[MATCH_MP NOT_LESS_IMP_heap_lookup nlt]) THEN
  W(fun gl ->
    let le = the_asm (fun c -> hd_is "<=" c && is_var (lhand c) &&
               is_var (rand c)) gl in
    let eq = the_asm (fun c -> is_eq c &&
               hd_is "el_length" (lhand c)) gl in
    let ne0 = the_asm (fun c -> is_neg c && is_eq (rand c) &&
                rand (rand c) = `0`) gl in
    let sp = rand (concl le) in
    let e = lhand (concl le) in
    let seq = MP (ISPECL [sp; e] (ARITH_RULE
                `!s e. (e:num) <= s ==> (s - e) + e = s`)) le in
    let s1 = MP (ISPEC sp (ARITH_RULE
               `!s. ~((s:num) = 0) ==> s - 1 + 1 = s`)) ne0 in
    REWRITE_TAC[data_to_word_memoryProof_heap_lookup_APPEND;
                heap_length_APPEND; heap_length_heap_expand;
                heap_length_clauses; ADD_CLAUSES; eq; seq; s1;
                heap_expand_def; heap_lookup_def;
                el_length_def]) THEN
  CONJ_TAC THEN
  REPEAT (CHANGED_TAC
            (COND_CASES_TAC THEN
             ASM_REWRITE_TAC[heap_lookup_def; ADD_CLAUSES;
                             el_length_def])) THEN
  REWRITE_TAC[isSomeDataElement_def] THEN
  (let ds = [distinctness "heap_element"] in
   REWRITE_TAC (injectivity "option" :: distinctness "option" ::
                NOT_EXISTS_THM :: ds @ map GSYM ds)) THEN
  TRY (SOLVED (REWRITE_TAC[])) THEN
  TRY (SOLVED (ASM_ARITH_TAC)));;

(* the address that the store writes held no data: it is inside the
   unused element, which is no data element *)
let heap_lookup_in_unused = prove
 (`!ha sp e hb.
     ~(sp = 0) /\ 1 <= e /\ e <= sp
     ==> ~isSomeDataElement
           (heap_lookup (heap_length ha + (sp - e))
              (ha ++ (Unused (sp - 1) :: hb)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPLIT_ASM_TAC THEN
  W(fun (asl,w as gl) ->
    let lk = find_term (hd_is "heap_lookup") w in
    let j = el 0 (snd (strip_comb lk)) in
    let a = lhand j in
    let sp = lhand (rand j) in
    let e = rand (rand j) in
    let le = the_asm (fun c -> hd_is "<=" c && lhand c = e) gl in
    let nlt = MP (ISPECL [a; sp; e] (ARITH_RULE
                `!a s e. e <= s ==> ~((a:num) + (s - e) < a)`)) le in
    let seq = MP (ISPECL [a; sp; e] (ARITH_RULE
                `!a s e. e <= s
                         ==> ((a:num) + (s - e)) - a = s - e`)) le in
    REWRITE_TAC[MATCH_MP NOT_LESS_IMP_heap_lookup nlt; seq]) THEN
  REWRITE_TAC[heap_lookup_def; el_length_def] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[isSomeDataElement_def] THEN
  (let ds = [distinctness "heap_element"] in
   REWRITE_TAC (injectivity "option" :: distinctness "option" ::
                NOT_EXISTS_THM :: ds @ map GSYM ds)) THEN
  TRY (SOLVED (REWRITE_TAC[])) THEN
  ASM_ARITH_TAC);;

(* the three regions of a store into the unused space, as the
   addresses that hold data: the ones the heap had and the one the
   store wrote *)
let isSome_store_unused = prove
 (`!ha sp e x hb.
     ~(sp = 0) /\ el_length x = e /\ 1 <= e /\ e <= sp /\
     isDataElement x
     ==> {a | isSomeDataElement
                (heap_lookup a
                   (ha ++ ((heap_expand (sp - e) ++ [x]) ++ hb)))} =
         (heap_length ha + (sp - e)) INSERT
         {a | isSomeDataElement
                (heap_lookup a (ha ++ (Unused (sp - 1) :: hb)))}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPLIT_ASM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
  GEN_TAC THEN
  W(fun (asl,w as gl) ->
    let addr = rand (lhand (rand w)) in
    let y = lhand (lhand (rand w)) in
    let a = lhand addr in
    let sp = lhand (rand addr) in
    let e = rand (rand addr) in
    let hp = el 1 (snd (strip_comb
               (find_term (hd_is "heap_lookup") (lhand w)))) in
    let ha = lhand hp in
    let x = lhand (rand (lhand (rand hp))) in
    let hb = rand (rand hp) in
    let ne0 = the_asm (fun c -> is_neg c && is_eq (rand c) &&
                rand (rand c) = `0`) gl in
    let eq = the_asm (fun c -> is_eq c &&
               hd_is "el_length" (lhand c)) gl in
    let one = the_asm (fun c -> hd_is "<=" c &&
                lhand c = `1`) gl in
    let le = the_asm (fun c -> hd_is "<=" c && is_var (lhand c) &&
               is_var (rand c)) gl in
    let isd = the_asm (hd_is "isDataElement") gl in
    (* the address of the element written *)
    ASM_CASES_TAC (mk_eq (y, addr)) THENL
     [ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ISPECL [ha; list_mk_icomb "-" [sp; e]; x; hb]
                    heap_lookup_at_end] THEN
      MP_TAC isd THEN
      REWRITE_TAC[isDataElement_def; isSomeDataElement_def] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    (* before the space or past it: the lookups are the ones they
       were; inside it, neither heap holds data *)
    DISJ_CASES_TAC (ISPECL [y; a; sp] (ARITH_RULE
      `!y a s. (y < a \/ a + s <= y) \/ (~(y < a) /\ y < a + s)`)) THENL
     [W(fun gl ->
        let d = the_asm is_disj gl in
        REWRITE_TAC[MATCH_MP (ISPECL [ha; sp; e; x; hb; y]
                                heap_lookup_store_outside)
                      (CONJ ne0 (CONJ eq (CONJ le d)))]);
      W(fun gl ->
        let d = the_asm (fun c -> is_conj c && is_neg (lhand c)) gl in
        let nq = the_asm (fun c -> is_neg c && is_eq (rand c) &&
                   rand (rand c) = addr) gl in
        let ins = MATCH_MP (ISPECL [ha; sp; e; x; hb; y]
                              heap_lookup_store_inside)
                    (CONJ ne0 (CONJ eq (CONJ one (CONJ le
                      (CONJ (CONJUNCT1 d) (CONJ (CONJUNCT2 d)
                        nq)))))) in
        REWRITE_TAC[CONJUNCT1 ins; CONJUNCT2 ins])]));;

(* and so a store into the unused space keeps every element that
   the heap had: the ones outside the space are where they were,
   and inside it the heap held none *)
let heap_store_rel_store_unused = prove
 (`!ha sp e x hb.
     ~(sp = 0) /\ el_length x = e /\ 1 <= e /\ e <= sp
     ==> heap_store_rel (ha ++ (Unused (sp - 1) :: hb))
           (ha ++ ((heap_expand (sp - e) ++ [x]) ++ hb))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPLIT_ASM_TAC THEN
  REWRITE_TAC[heap_store_rel_def] THEN
  GEN_TAC THEN DISCH_TAC THEN
  W(fun (asl,w as gl) ->
    let hp = el 1 (snd (strip_comb
               (find_term (hd_is "heap_lookup") (lhand w)))) in
    let ha = lhand hp in
    let x = lhand (rand (lhand (rand hp))) in
    let hb = rand (rand hp) in
    let a = list_mk_icomb "heap_length" [ha] in
    let ne0 = the_asm (fun c -> is_neg c && is_eq (rand c) &&
                rand (rand c) = `0`) gl in
    let eq = the_asm (fun c -> is_eq c &&
               hd_is "el_length" (lhand c)) gl in
    let one = the_asm (fun c -> hd_is "<=" c &&
                lhand c = `1`) gl in
    let le = the_asm (fun c -> hd_is "<=" c && is_var (lhand c) &&
               is_var (rand c)) gl in
    let sp = rand (concl le) in
    let e = lhand (concl le) in
    let ptr = el 0 (snd (strip_comb
                (find_term (hd_is "heap_lookup") (lhand w)))) in
    let addr = list_mk_icomb "+"
                 [a; list_mk_icomb "-" [sp; e]] in
    DISJ_CASES_TAC (ISPECL [ptr; a; sp] (ARITH_RULE
      `!y a s. (y < a \/ a + s <= y) \/
               (~(y < a) /\ y < a + s)`)) THENL
     [W(fun gl ->
        let d = the_asm is_disj gl in
        ACCEPT_TAC (MATCH_MP (ISPECL [ha; sp; e; x; hb; ptr]
                                heap_lookup_store_outside)
                      (CONJ ne0 (CONJ eq (CONJ le d)))));
      (* inside the space the old heap held no data, so there is
         nothing to keep *)
      ASM_CASES_TAC (mk_eq (ptr, addr)) THENL
       [W(fun gl ->
          let isd = the_asm (hd_is "isSomeDataElement") gl in
          let nd = MATCH_MP (ISPECL [ha; sp; e; hb]
                               heap_lookup_in_unused)
                     (CONJ ne0 (CONJ one le)) in
          let eqp = the_asm (fun c -> is_eq c && lhand c = ptr) gl in
          CONTR_TAC (MP (NOT_ELIM nd)
            (ONCE_REWRITE_RULE[eqp] isd)));
        W(fun gl ->
          let d = the_asm (fun c -> is_conj c &&
                    is_neg (lhand c)) gl in
          let nq = the_asm (fun c -> is_neg c && is_eq (rand c) &&
                     lhand (rand c) = ptr) gl in
          let isd = the_asm (hd_is "isSomeDataElement") gl in
          let ins = MATCH_MP (ISPECL [ha; sp; e; x; hb; ptr]
                                heap_lookup_store_inside)
                      (CONJ ne0 (CONJ eq (CONJ one (CONJ le
                        (CONJ (CONJUNCT1 d) (CONJ (CONJUNCT2 d)
                          nq)))))) in
          CONTR_TAC (MP (NOT_ELIM (CONJUNCT2 ins)) isd))]]));;
""",

  ('data_to_word_memoryProof', 'IMP_heap_store_unused_alt'): r"""
(* the port's own: what the proof of IMP_heap_store_unused_alt
   needs.  This store writes the element first and the space that
   is left after it, so the element is at the start of what was
   unused (heap_lookup_alt_at_start) and the space that is left
   behind it (heap_lookup_alt_unused); outside the space the heap
   is the one it was and inside it neither heap holds data, as for
   the other store, and the last three lemmas put that together
   into the addresses that hold data, the elements the heap keeps,
   and what is below the space that is left (the element written is
   data, which is why the theorem asks for isDataElement) *)

(* the other store into the unused space writes the element first
   and the space that is left after it *)
let heap_lookup_alt_at_start = prove
 (`!ha k x hb.
     heap_lookup (heap_length ha)
       (ha ++ (([x] ++ heap_expand k) ++ hb)) = SOME x`,
  REPEAT GEN_TAC THEN
  W(fun (asl,w) -> MP_TAC (ISPEC (rand (rand w)) el_length_GT_0)) THEN
  DISCH_TAC THEN
  REWRITE_TAC[data_to_word_memoryProof_heap_lookup_APPEND;
              LT_REFL; SUB_REFL; APPEND; heap_length_clauses;
              ADD_CLAUSES; heap_lookup_def] THEN
  REPEAT (CHANGED_TAC
            (COND_CASES_TAC THEN
             ASM_REWRITE_TAC[heap_lookup_def; ADD_CLAUSES])) THEN
  TRY (SOLVED (ASM_ARITH_TAC)));;

let heap_lookup_alt_unused = prove
 (`!ha k x hb.
     ~(k = 0) ==>
     heap_lookup (heap_length ha + el_length x)
       (ha ++ (([x] ++ heap_expand k) ++ hb)) = SOME (Unused (k - 1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[heap_expand_def] THEN
  REWRITE_TAC[APPEND] THEN
  W(fun (asl,w) ->
    MP_TAC (ISPEC (rand (rand (el 0 (snd (strip_comb (lhand w))))))
              el_length_GT_0)) THEN
  DISCH_TAC THEN
  REWRITE_TAC[data_to_word_memoryProof_heap_lookup_APPEND;
              heap_length_APPEND; heap_length_clauses;
              ADD_CLAUSES; LT_REFL; SUB_REFL; heap_lookup_def;
              el_length_def] THEN
  REPEAT (CHANGED_TAC
            (COND_CASES_TAC THEN
             ASM_REWRITE_TAC[heap_lookup_def; LT_REFL; SUB_REFL;
                             ADD_CLAUSES; el_length_def])) THEN
  ASM_ARITH_TAC);;

(* outside the space that the store wrote, the heap is the one it
   was, as for the other store *)
let heap_lookup_alt_outside = prove
 (`!ha sp e x hb y.
     ~(sp = 0) /\ el_length x = e /\ e <= sp /\
     (y < heap_length ha \/ heap_length ha + sp <= y)
     ==> heap_lookup y (ha ++ (([x] ++ heap_expand (sp - e)) ++ hb)) =
         heap_lookup y (ha ++ (Unused (sp - 1) :: hb))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPLIT_ASM_TAC THENL
   [W(fun gl ->
      let lt = the_asm (fun c -> hd_is "<" c &&
                 hd_is "heap_length" (rand c)) gl in
      REWRITE_TAC[MATCH_MP LESS_IMP_heap_lookup lt]);
    W(fun (asl,w as gl) ->
      let ge = the_asm (fun c -> hd_is "<=" c &&
                 hd_is "+" (lhand c)) gl in
      let a = lhand (lhand (concl ge)) in
      let sp = rand (lhand (concl ge)) in
      let y = rand (concl ge) in
      let nlt = MP (ISPECL [a; sp; y] (ARITH_RULE
                  `!a s y. (a:num) + s <= y ==> ~(y < a)`)) ge in
      REWRITE_TAC[MATCH_MP NOT_LESS_IMP_heap_lookup nlt]) THEN
    W(fun gl ->
      let le = the_asm (fun c -> hd_is "<=" c &&
                 not (hd_is "+" (lhand c))) gl in
      let eq = the_asm (fun c -> is_eq c &&
                 hd_is "el_length" (lhand c)) gl in
      let ne0 = the_asm (fun c -> is_neg c && is_eq (rand c) &&
                  rand (rand c) = `0`) gl in
      let sp = rand (concl le) in
      let e = lhand (concl le) in
      let seq = MP (ISPECL [sp; e] (ARITH_RULE
                  `!s e. (e:num) <= s ==> e + (s - e) = s`)) le in
      let s1 = MP (ISPEC sp (ARITH_RULE
                 `!s. ~((s:num) = 0) ==> s - 1 + 1 = s`)) ne0 in
      REWRITE_TAC[data_to_word_memoryProof_heap_lookup_APPEND;
                  heap_length_APPEND; heap_length_heap_expand;
                  heap_length_clauses; ADD_CLAUSES; eq; seq; s1;
                  heap_lookup_def; el_length_def]) THEN
    REPEAT (CHANGED_TAC
              (COND_CASES_TAC THEN
               ASM_REWRITE_TAC[heap_lookup_def; ADD_CLAUSES])) THEN
  ASM_ARITH_TAC]);;

(* and inside it, away from the element written, neither heap holds
   data *)
let heap_lookup_alt_inside = prove
 (`!ha sp e x hb y.
     ~(sp = 0) /\ el_length x = e /\ 1 <= e /\ e <= sp /\
     ~(y < heap_length ha) /\ y < heap_length ha + sp /\
     ~(y = heap_length ha)
     ==> ~isSomeDataElement
           (heap_lookup y
              (ha ++ (([x] ++ heap_expand (sp - e)) ++ hb))) /\
         ~isSomeDataElement
           (heap_lookup y (ha ++ (Unused (sp - 1) :: hb)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPLIT_ASM_TAC THEN
  W(fun gl ->
    let nlt = the_asm (fun c -> is_neg c && hd_is "<" (rand c) &&
                hd_is "heap_length" (rand (rand c))) gl in
    REWRITE_TAC[MATCH_MP NOT_LESS_IMP_heap_lookup nlt]) THEN
  W(fun gl ->
    let le = the_asm (fun c -> hd_is "<=" c && is_var (lhand c) &&
               is_var (rand c)) gl in
    let eq = the_asm (fun c -> is_eq c &&
               hd_is "el_length" (lhand c)) gl in
    let ne0 = the_asm (fun c -> is_neg c && is_eq (rand c) &&
                rand (rand c) = `0`) gl in
    let sp = rand (concl le) in
    let e = lhand (concl le) in
    let seq = MP (ISPECL [sp; e] (ARITH_RULE
                `!s e. (e:num) <= s ==> e + (s - e) = s`)) le in
    let s1 = MP (ISPEC sp (ARITH_RULE
               `!s. ~((s:num) = 0) ==> s - 1 + 1 = s`)) ne0 in
    REWRITE_TAC[data_to_word_memoryProof_heap_lookup_APPEND;
                heap_length_APPEND; heap_length_heap_expand;
                heap_length_clauses; ADD_CLAUSES; eq; seq; s1;
                heap_expand_def; heap_lookup_def;
                el_length_def]) THEN
  CONJ_TAC THEN
  REPEAT (CHANGED_TAC
            (COND_CASES_TAC THEN
             ASM_REWRITE_TAC[heap_lookup_def; ADD_CLAUSES;
                             el_length_def])) THEN
  REWRITE_TAC[isSomeDataElement_def] THEN
  (let ds = [distinctness "heap_element"] in
   REWRITE_TAC (injectivity "option" :: distinctness "option" ::
                NOT_EXISTS_THM :: ds @ map GSYM ds)) THEN
  TRY (SOLVED (REWRITE_TAC[])) THEN
  ASM_ARITH_TAC);;

(* the addresses that hold data, after the other store: the ones
   the heap had and the one the store wrote *)
let isSome_store_unused_alt = prove
 (`!ha sp e x hb.
     ~(sp = 0) /\ el_length x = e /\ 1 <= e /\ e <= sp /\
     isDataElement x
     ==> {a | isSomeDataElement
                (heap_lookup a
                   (ha ++ (([x] ++ heap_expand (sp - e)) ++ hb)))} =
         heap_length ha INSERT
         {a | isSomeDataElement
                (heap_lookup a (ha ++ (Unused (sp - 1) :: hb)))}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPLIT_ASM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
  GEN_TAC THEN
  W(fun (asl,w as gl) ->
    let addr = rand (lhand (rand w)) in
    let y = lhand (lhand (rand w)) in
    let hp = el 1 (snd (strip_comb
               (find_term (hd_is "heap_lookup") (lhand w)))) in
    let ha = lhand hp in
    let x = lhand (lhand (lhand (rand hp))) in
    let hb = rand (rand hp) in
    let ne0 = the_asm (fun c -> is_neg c && is_eq (rand c) &&
                rand (rand c) = `0`) gl in
    let eq = the_asm (fun c -> is_eq c &&
               hd_is "el_length" (lhand c)) gl in
    let one = the_asm (fun c -> hd_is "<=" c &&
                lhand c = `1`) gl in
    let le = the_asm (fun c -> hd_is "<=" c && is_var (lhand c) &&
               is_var (rand c)) gl in
    let sp = rand (concl le) in
    let e = lhand (concl le) in
    let isd = the_asm (hd_is "isDataElement") gl in
    (* the address of the element written *)
    ASM_CASES_TAC (mk_eq (y, addr)) THENL
     [ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ISPECL [ha; list_mk_icomb "-" [sp; e]; x; hb]
                    heap_lookup_alt_at_start] THEN
      MP_TAC isd THEN
      REWRITE_TAC[isDataElement_def; isSomeDataElement_def] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISJ_CASES_TAC (ISPECL [y; addr; sp] (ARITH_RULE
      `!y a s. (y < a \/ a + s <= y) \/
               (~(y < a) /\ y < a + s)`)) THENL
     [W(fun gl ->
        let d = the_asm is_disj gl in
        REWRITE_TAC[MATCH_MP (ISPECL [ha; sp; e; x; hb; y]
                                heap_lookup_alt_outside)
                      (CONJ ne0 (CONJ eq (CONJ le d)))]);
      W(fun gl ->
        let d = the_asm (fun c -> is_conj c &&
                  is_neg (lhand c)) gl in
        let nq = the_asm (fun c -> is_neg c && is_eq (rand c) &&
                   rand (rand c) = addr) gl in
        let ins = MATCH_MP (ISPECL [ha; sp; e; x; hb; y]
                              heap_lookup_alt_inside)
                    (CONJ ne0 (CONJ eq (CONJ one (CONJ le
                      (CONJ (CONJUNCT1 d) (CONJ (CONJUNCT2 d)
                        nq)))))) in
        REWRITE_TAC[CONJUNCT1 ins; CONJUNCT2 ins])]));;

(* and the elements that the heap had, it keeps *)
let heap_store_rel_alt = prove
 (`!ha sp e x hb.
     ~(sp = 0) /\ el_length x = e /\ 1 <= e /\ e <= sp
     ==> heap_store_rel (ha ++ (Unused (sp - 1) :: hb))
           (ha ++ (([x] ++ heap_expand (sp - e)) ++ hb))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPLIT_ASM_TAC THEN
  REWRITE_TAC[heap_store_rel_def] THEN
  GEN_TAC THEN DISCH_TAC THEN
  W(fun (asl,w as gl) ->
    let hp = el 1 (snd (strip_comb
               (find_term (hd_is "heap_lookup") (lhand w)))) in
    let ha = lhand hp in
    let x = lhand (lhand (lhand (rand hp))) in
    let hb = rand (rand hp) in
    let a = list_mk_icomb "heap_length" [ha] in
    let ne0 = the_asm (fun c -> is_neg c && is_eq (rand c) &&
                rand (rand c) = `0`) gl in
    let eq = the_asm (fun c -> is_eq c &&
               hd_is "el_length" (lhand c)) gl in
    let one = the_asm (fun c -> hd_is "<=" c &&
                lhand c = `1`) gl in
    let le = the_asm (fun c -> hd_is "<=" c && is_var (lhand c) &&
               is_var (rand c)) gl in
    let sp = rand (concl le) in
    let e = lhand (concl le) in
    let ptr = el 0 (snd (strip_comb
                (find_term (hd_is "heap_lookup") (lhand w)))) in
    DISJ_CASES_TAC (ISPECL [ptr; a; sp] (ARITH_RULE
      `!y a s. (y < a \/ a + s <= y) \/
               (~(y < a) /\ y < a + s)`)) THENL
     [W(fun gl ->
        let d = the_asm is_disj gl in
        ACCEPT_TAC (MATCH_MP (ISPECL [ha; sp; e; x; hb; ptr]
                                heap_lookup_alt_outside)
                      (CONJ ne0 (CONJ eq (CONJ le d)))));
      ASM_CASES_TAC (mk_eq (ptr, a)) THENL
       [W(fun gl ->
          let isd = the_asm (hd_is "isSomeDataElement") gl in
          let eqp = the_asm (fun c -> is_eq c && lhand c = ptr) gl in
          MP_TAC (ONCE_REWRITE_RULE[eqp] isd) THEN
          REWRITE_TAC[heap_lookup_PREFIX; isSomeDataElement_def] THEN
          (let ds = [distinctness "heap_element"] in
           REWRITE_TAC (injectivity "option" ::
                        NOT_EXISTS_THM :: ds @ map GSYM ds)) THEN
          REWRITE_TAC[]);
        W(fun gl ->
          let d = the_asm (fun c -> is_conj c &&
                    is_neg (lhand c)) gl in
          let nq = the_asm (fun c -> is_neg c && is_eq (rand c) &&
                     lhand (rand c) = ptr) gl in
          let isd = the_asm (hd_is "isSomeDataElement") gl in
          let ins = MATCH_MP (ISPECL [ha; sp; e; x; hb; ptr]
                                heap_lookup_alt_inside)
                      (CONJ ne0 (CONJ eq (CONJ one (CONJ le
                        (CONJ (CONJUNCT1 d) (CONJ (CONJUNCT2 d)
                          nq)))))) in
          CONTR_TAC (MP (NOT_ELIM (CONJUNCT2 ins)) isd))]]));;

(* what is below the unused space after the other store: what was
   below it and the element written *)
let data_up_to_alt = prove
 (`!ha x he hb.
     EVERY isDataElement ha /\ isDataElement x
     ==> data_up_to (heap_length ha + el_length x)
           (ha ++ (([x] ++ he) ++ hb))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  W(fun (asl,w as gl) ->
    let args = snd (strip_comb w) in
    let addr = el 0 args in
    let hp = el 1 args in
    let ha = lhand hp in
    let x = lhand (lhand (lhand (rand hp))) in
    let he = rand (lhand (rand hp)) in
    let hb = rand (rand hp) in
    let front = list_mk_icomb "APPEND" [ha; mk_flist [x]] in
    let nw = list_mk_icomb "APPEND"
               [front; list_mk_icomb "APPEND" [he; hb]] in
    SUBGOAL_THEN (mk_eq (hp, nw))
      (fun e -> ONCE_REWRITE_TAC[e]) THENL
     [REWRITE_TAC[APPEND_ASSOC]; ALL_TAC] THEN
    SUBGOAL_THEN (mk_eq (addr, list_mk_icomb "heap_length" [front]))
      (fun e -> ONCE_REWRITE_TAC[e]) THENL
     [REWRITE_TAC[heap_length_APPEND; heap_length_clauses;
                  ADD_CLAUSES];
      ALL_TAC]) THEN
  REWRITE_TAC[data_up_to_APPEND; ALL_APPEND; ALL] THEN
  ASM_REWRITE_TAC[]);;
""",

  ('data_to_word_memoryProof', 'el_thm'): r"""
(* the port's own: the steps that the lemmas about abs_ml_inv of a
   stack take.  A value put on the stack only adds timestamps
   (all_ts_mono) and reaches no more references than the Block it
   comes out of (reach_block); the pointers of an element of a good
   heap are addresses of it (heap_ok_in), which is what the new root
   of such a lemma asks for (roots_ok_el); heap_el reads the element
   of a Block's representation (heap_el_block); and the values of
   the two stacks are related elementwise (all2_el_cons) *)

let all_ts_mono = prove
 (cake_as_vars (fun () ->
    `all_ts refs stack' SUBSET all_ts refs (v :: stack')`),
  REWRITE_TAC[all_ts_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; MEM] THEN
  MESON_TAC[]);;

let reach_block = prove
 (cake_as_vars (fun () ->
    `MEM v ys /\ reachable_refs (v :: Block ts tag ys :: stack') refs n
     ==> reachable_refs (Block ts tag ys :: stack') refs n`),
  REWRITE_TAC[reachable_refs_def; MEM] THEN
  REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[refs_in_block]);;

let heap_ok_in = prove
 (`heap_ok heap limit' /\
   heap_lookup a heap = SOME (DataElement xs l d)
   ==> (!ptr u. MEM (gc_shared_Pointer ptr u) xs
                ==> isSomeDataElement (heap_lookup ptr heap))`,
  REWRITE_TAC[heap_ok_def] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[heap_lookup_MEM]);;

let heap_el_block = prove
 (`heap_lookup ptr heap = SOME (BlockRep n ys) /\ i < LENGTH ys
   ==> heap_el (gc_shared_Pointer ptr u) i heap = (EL i ys,T)`,
  STRIP_TAC THEN
  FIRST
   [SOLVED (ASM_REWRITE_TAC[heap_el_def; BlockRep_def] THEN
            MATCH_REDUCE_TAC THEN ASM_REWRITE_TAC[]);
    SOLVED (REWRITE_TAC[heap_el_def] THEN MATCH_REDUCE_TAC THEN
            ASM_REWRITE_TAC[BlockRep_def] THEN MATCH_TIDY_TAC THEN
            MATCH_REDUCE_TAC THEN MATCH_TIDY_TAC THEN
            ASM_REWRITE_TAC[]);
    SOLVED (REWRITE_TAC[heap_el_def] THEN SAFE_MATCH_REDUCE_TAC THEN
            ASM_REWRITE_TAC[BlockRep_def] THEN
            SAFE_MATCH_REDUCE_TAC THEN ASM_REWRITE_TAC[]);
    SOLVED (ASM_REWRITE_TAC[heap_el_def; BlockRep_def] THEN
            CONV_TAC(TOP_DEPTH_CONV MATCH_CONV) THEN
            CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
            ASM_REWRITE_TAC[])]);;

let roots_ok_el = prove
 (`heap_ok heap limit' /\
   heap_lookup ptr heap = SOME (BlockRep n ys) /\
   i < LENGTH ys /\ roots_ok rs heap
   ==> roots_ok (EL i ys :: rs) heap`,
  STRIP_TAC THEN
  FIRST_X_ASSUM (fun ro ->
    if not (hd_is "roots_ok" (concl ro)) then fail() else
    MP_TAC (REWRITE_RULE[roots_ok_def] ro)) THEN
  REWRITE_TAC[roots_ok_def; MEM] THEN
  DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [(* the new root is a pointer of the Block's element *)
    FIRST_ASSUM (fun ho ->
      if not (hd_is "heap_ok" (concl ho)) then fail() else
      FIRST_ASSUM (fun hl ->
        if not (is_eq (concl hl)) ||
           not (hd_is "heap_lookup" (lhand (concl hl))) then fail()
        else MP_TAC (MATCH_MP heap_ok_in (CONJ ho
               (REWRITE_RULE[BlockRep_def] hl))))) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    W(fun gl ->
      let e = the_asm (fun c -> is_eq c &&
                hd_is "gc_shared_Pointer" (lhand c)) gl in
      EXISTS_TAC (rand (lhand (concl e))) THEN
      ONCE_REWRITE_TAC[e]) THEN
    FIRST [SOLVED (REWRITE_TAC[MEM_EL] THEN EXISTS_TAC `i:num` THEN
                   ASM_REWRITE_TAC[]);
           SOLVED (MATCH_MP_TAC MEM_EL THEN ASM_ARITH_TAC);
           SOLVED (ASM_SIMP_TAC[MEM_EL])];
    (* and the old roots are what they were *)
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    W(fun gl ->
      let m = the_asm (hd_is "MEM") gl in
      EXISTS_TAC (rand (el 0 (snd (strip_comb (concl m)))))) THEN
    FIRST_ASSUM ACCEPT_TAC]);;

let all2_el_cons = prove
 (`!(P:A->B->bool) xs ys i a b st rs.
     EVERY2 P xs ys /\ i < LENGTH xs /\ P a b /\ EVERY2 P st rs
     ==> EVERY2 P (EL i xs :: a :: st) (EL i ys :: b :: rs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ALL2_DEF; HD; TL; NOT_CONS_NIL] THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  MP_TAC (SPEC `i:num` (CONJUNCT2 (REWRITE_RULE[LIST_REL_EL_EQN]
    (ASSUME `EVERY2 (P:A->B->bool) xs ys`)))) THEN
  ASM_REWRITE_TAC[]);;

(* the assumption that says what the heap holds for a Block *)

let blockrep_asm =
  the_asm (fun c -> is_eq c && hd_is "heap_lookup" (lhand c) &&
             can (fun t -> hd_is "BlockRep" (rand t)) (rand c));;
""",

  ('data_to_word_memoryProof', 'bc_stack_ref_inv_gc_inline'): r"""
(* the port's own: the steps that a lemma about gc_inline takes.
   The relation of the two heaps moves an element and relates
   the values in it, and gc_heap_inline_rel_v_inv carries v_inv
   over for one of them; the proofs of this part of the file
   share them *)

(* that a value of a list is one of its elements *)
let MEM_CLOSE =
  FIRST
   [SOLVED (REWRITE_TAC[MEM] THEN ASM_REWRITE_TAC[]);
    SOLVED (REWRITE_TAC[MEM_EL] THEN EXISTS_TAC `i:num` THEN
            ASM_REWRITE_TAC[] THEN
            POP_ASSUM_LIST (fun l -> MAP_EVERY ASSUME_TAC (filter
              (fun t -> let c = concl t in
                 hd_is "<" c ||
                 (is_eq c && (hd_is "LENGTH" (lhand c) ||
                              hd_is "LENGTH" (rand c)))) l)) THEN
            ASM_ARITH_TAC);
    SOLVED (MATCH_MP_TAC MEM_EL THEN ASM_ARITH_TAC);
    SOLVED (ASM_SIMP_TAC[MEM_EL])];;

let AT_I nm =
  (* the rest inside the search: two assumptions can be about the
     same relation, and only one of them has an index bound that
     the goal gives (PORTING-GUIDE.md entry 42) *)
  FIRST_X_ASSUM (fun th ->
    let b = snd (strip_forall (concl th)) in
    if not (is_imp b) || not (hd_is nm (rand b)) then fail() else
    MP_TAC (SPEC `i:num` th) THEN
    (ANTS_TAC THENL
      [POP_ASSUM_LIST (fun l -> MAP_EVERY ASSUME_TAC (filter
         (fun t -> let c = concl t in
            hd_is "<" c ||
            (is_eq c && (hd_is "LENGTH" (lhand c) ||
                         hd_is "LENGTH" (rand c)))) l)) THEN
       ASM_ARITH_TAC;
       ALL_TAC]) THEN
    DISCH_TAC);;

(* the element of the new heap that the relation gives for the one
   the arm names *)
let MOVE_INLINE =
  W(fun (asl,w as gl) ->
    let lr = the_asm (fun c -> hd_is "ALL2" c &&
               hd_is "gc_heap_inline_rel"
                 (el 0 (snd (strip_comb c)))) gl in
    let hl = the_asm (fun c -> is_eq c &&
               hd_is "heap_lookup" (lhand c) &&
               hd_is "SOME" (rand c)) gl in
    let hl' = CONV_RULE(TOP_DEPTH_CONV let_CONV)
                (REWRITE_RULE[RefBlock_def; BlockRep_def;
                              ThunkBlock_def; bytes_def] hl) in
    STRIP_ASSUME_TAC (MATCH_MP
      (MATCH_MP LIST_REL_gc_heap_inline_DataElement lr) hl'));;

(* the value of an element of the old heap, in the new one *)
let SURVIVES =
  MATCH_MP_TAC (GEN_ALL gc_heap_inline_rel_v_inv) THEN
  W(fun gl ->
    let vi = the_asm (hd_is "v_inv") gl in
    let xs = tparts (rand (concl vi)) in
    let bri = the_asm (fun c ->
      let b = snd (strip_forall c) in
      is_imp b && hd_is "bc_ref_inv" (rand b)) gl in
    let bs = tparts (rand (rand (snd (strip_forall (concl bri))))) in
    EXISTS_TAC (el 3 bs) THEN EXISTS_TAC (el 2 bs) THEN
    EXISTS_TAC (el 0 xs)) THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  TRY (SOLVED (REWRITE_TAC[LIST_REL_EL_EQN] THEN
               ASM_REWRITE_TAC[])) THEN
  (* and the references it reaches are reachable from the stack *)
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (fun bri ->
    let b = snd (strip_forall (concl bri)) in
    if not (is_imp b) || not (hd_is "bc_ref_inv" (rand b))
    then fail() else MATCH_MP_TAC bri) THEN
  CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  FIRST
   [(* the value is on the stack *)
    SOLVED (MATCH_MP_TAC (GEN_ALL reach_mem) THEN
    W(fun gl ->
      let rr = the_asm (fun c -> hd_is "reachable_refs" c &&
                 hd_is "CONS" (el 0 (snd (strip_comb c)))) gl in
      EXISTS_TAC (lhand (el 0 (snd (strip_comb (concl rr)))))) THEN
    CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
    MEM_CLOSE);
    (* or inside a reference that the stack reaches *)
    SOLVED (W(fun gl ->
      let rr2 = the_asm (fun c -> hd_is "reachable_refs" c &&
                  hd_is "CONS" (el 0 (snd (strip_comb c)))) gl in
      let v = lhand (el 0 (snd (strip_comb (concl rr2)))) in
      let rr1 = the_asm (fun c -> hd_is "reachable_refs" c &&
                  not (hd_is "CONS"
                         (el 0 (snd (strip_comb c))))) gl in
      let args = snd (strip_comb (concl rr1)) in
      let r2 = mk_var("r2", type_of (el 2 args)) in
      let tm = mk_forall (r2,
        mk_imp (list_mk_icomb "MEM" [r2; list_mk_icomb "get_refs" [v]],
                list_mk_icomb "ref_edge" [el 1 args; el 2 args; r2])) in
      SUBGOAL_THEN tm (fun edges ->
        ACCEPT_TAC (MATCH_MP reach_val
          (CONJ rr1 (CONJ edges rr2)))) THEN
      (* the value is one of the reference's own *)
      REWRITE_TAC[ref_edge_def] THEN ASM_REWRITE_TAC[] THEN
      MATCH_REDUCE_TAC THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC (GEN_ALL refs_in_block) THEN
      EXISTS_TAC v THEN
      CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
      MEM_CLOSE))];;
""",

  ('data_to_word_memoryProof', 'bc_ref_inv_related'): r"""
(* the port's own: the arms of bc_ref_inv, one lemma each, and the
   steps that every lemma about a collection of the heap takes.
   They stand here because the proofs of this file share them (the
   first of them is bc_ref_inv_related): the two lookups of the
   invariant decide which arm it is, and the maps and the heap of
   the arm lemma stay free, so one lemma reads the old invariant
   and the new one alike (PORTING-GUIDE.md entry 43) *)

let arm_VA = prove
 (cake_as_vars (fun () ->
    `FLOOKUP f n = SOME x /\
     sptree_lookup n refs = SOME (bvlSem_ValueArray ys)
     ==> (bc_ref_inv conf n refs (f,tf,heap,be') <=>
          (?zs. heap_lookup x heap = SOME (RefBlock zs) /\
                EVERY2 (\z y. v_inv conf y refs (z,f,tf,heap))
                  zs ys))`),
  STRIP_TAC THEN ASM_REWRITE_TAC[bc_ref_inv_def] THEN
  MATCH_REDUCE_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[]);;

let arm_BA = prove
 (cake_as_vars (fun () ->
    `FLOOKUP f n = SOME x /\
     sptree_lookup n refs = SOME (bvlSem_ByteArray flag bs)
     ==> (bc_ref_inv conf n refs (f,tf,heap,be') <=>
          (let ws = LENGTH bs DIV (dimindex (:'a) DIV 8) + 1 in
            (heap_lookup x heap = SOME (Bytes be' flag bs (REPLICATE
              ws ((n2w 0):'a word))))))`),
  STRIP_TAC THEN ASM_REWRITE_TAC[bc_ref_inv_def] THEN
  MATCH_REDUCE_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[]);;

let arm_TH = prove
 (cake_as_vars (fun () ->
    `FLOOKUP f n = SOME x /\
     sptree_lookup n refs = SOME (bvlSem_Thunk ev v)
     ==> (bc_ref_inv conf n refs (f,tf,heap,be') <=>
          (?(z:('a word_loc) heap_address).
             heap_lookup x heap = SOME (ThunkBlock ev z) /\
             (ev = Evaluated ==> dest_thunk v refs = NotThunk) /\
             v_inv conf v refs (z,f,tf,heap)))`),
  STRIP_TAC THEN ASM_REWRITE_TAC[bc_ref_inv_def] THEN
  MATCH_REDUCE_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[]);;

let arm_MB = prove
 (cake_as_vars (fun () ->
    `FLOOKUP f n = SOME x /\
     sptree_lookup n refs = SOME (bvlSem_MutBlock tg fin l c r)
     ==> (bc_ref_inv conf n refs (f,tf,heap,be') <=>
          ((!gs. ~(data_to_word_config_gc_kind conf =
                   data_to_word_Generational gs)) /\
           (~fin ==> ~(x IN IMAGE (FAPPLY tf) (FDOM tf))) /\
           (?zs. heap_lookup x heap = SOME (BlockRep tg zs) /\
                 EVERY2 (\z y. v_inv conf y refs (z,f,tf,heap)) zs
                   (l ++ [c] ++ r))))`),
  STRIP_TAC THEN ASM_REWRITE_TAC[bc_ref_inv_def] THEN
  MATCH_REDUCE_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[]);;

(* the arm of the old invariant and the arm of the new one, from
   the two lookups that each of them goes by *)

let USE_ARM =
  W(fun (asl,w as gl) ->
    let lk2 = the_asm (fun c -> is_eq c &&
                hd_is "sptree_lookup" (lhand c) &&
                hd_is "SOME" (rand c)) gl in
    let lk1s = filter (fun (_,th) ->
                 let c = concl th in
                 is_eq c && hd_is "FLOOKUP" (lhand c) &&
                 hd_is "SOME" (rand c)) asl in
    let arms = [arm_VA; arm_BA; arm_TH; arm_MB] in
    let ths =
      itlist (fun (_,lk1) a ->
        itlist (fun arm b ->
          (try [MATCH_MP arm (CONJ lk1 lk2)] with Failure _ -> [])
          @ b) arms a) lk1s [] in
    RULE_ASSUM_TRY (REWRITE_RULE ths) THEN REWRITE_TAC ths);;

(* the collection takes the address of an element to its own and
   what lies there to the element with its pointers mapped *)

let heap_move = prove
 (`gc_related g heap1 heap2 /\ a IN FDOM g /\
   heap_lookup a heap1 = SOME (DataElement xs l d)
   ==> heap_lookup (FAPPLY g a) heap2 =
       SOME (DataElement (ADDR_MAP (FAPPLY g) xs) l d) /\
       (!ptr u. MEM (gc_shared_Pointer ptr u) xs ==> ptr IN FDOM g)`,
  REWRITE_TAC[gc_related_def] THEN MESON_TAC[]);;

let addr1 = prove
 (`!f (z:(A)heap_address). ADDR_MAP f [z] = [ADDR_APPLY f z]`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `z:(A)heap_address`
                     (cases_of `:(A)heap_address`)) THEN
  REWRITE_TAC[ADDR_MAP_def; ADDR_APPLY_def]);;

(* and it is injective on its domain *)

let G_INJ = prove
 (`gc_related g heap1 heap2
   ==> (!a b. a IN FDOM g /\ b IN FDOM g /\
              (FAPPLY g a:num) = FAPPLY g b ==> a = b)`,
  REWRITE_TAC[gc_related_def] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM (fun inj ->
    if not (hd_is "INJ" (concl inj)) then fail() else
    MATCH_MP_TAC (CONJUNCT2 (REWRITE_RULE[INJ] inj))) THEN
  ASM_REWRITE_TAC[]);;

let v_inv_moved = GEN_ALL (DISCH_ALL (CONJUNCT1
  (UNDISCH (SPEC_ALL (GEN_ALL v_inv_related)))));;

(* the element at the collected address, from the arm's own
   equation *)

let MOVE =
  W(fun (asl,w as gl) ->
    let hl = the_asm (fun c -> is_eq c &&
               hd_is "heap_lookup" (lhand c)) gl in
    let hl' = CONV_RULE(TOP_DEPTH_CONV let_CONV)
                (REWRITE_RULE[RefBlock_def; BlockRep_def;
                              ThunkBlock_def; bytes_def] hl) in
    let gc = the_asm (hd_is "gc_related") gl in
    let ins = filter (fun (_,th) -> hd_is "IN" (concl th)) asl in
    STRIP_ASSUME_TAC (tryfind (fun (_,i) ->
      MATCH_MP heap_move (CONJ gc (CONJ i hl'))) ins));;

(* and what the arm says of a value of the old heap says of the
   mapped value in the new one *)

let USE_V_REL =
  MATCH_MP_TAC v_inv_moved THEN
  W(fun gl ->
    let gc = the_asm (hd_is "gc_related") gl in
    EXISTS_TAC (el 1 (snd (strip_comb (concl gc))))) THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (fun mp ->
    let b = snd (strip_forall (concl mp)) in
    if not (is_imp b) || not (hd_is "MEM" (lhand b)) then fail()
    else MATCH_MP_TAC mp) THEN
  POP_ASSUM_LIST (fun l -> MAP_EVERY ASSUME_TAC (filter
    (fun th -> let c = concl th in
       hd_is "MEM" c || (is_eq c && is_var (lhand c))) l)) THEN
  ASM_MESON_TAC[MEM];;

(* the port's own: what reaches a reference.  reachable_refs is a
   path of ref_edge from a reference of a value of the stack, so a
   value of the stack reaches no more than the stack does, and a
   value inside a reference that the stack reaches reaches no more
   either.  The proofs about a collection and about an update of the
   references share these *)

let reach_mem = prove
 (cake_as_vars (fun () ->
    `MEM v stack' /\ reachable_refs [v] refs n
     ==> reachable_refs stack' refs n`),
  REWRITE_TAC[reachable_refs_def; MEM] THEN
  STRIP_TAC THEN ASM_MESON_TAC[]);;

let reach_val = prove
 (cake_as_vars (fun () ->
    `reachable_refs stack' refs m /\
     (!r2. MEM r2 (get_refs v) ==> ref_edge refs m r2) /\
     reachable_refs [v] refs n
     ==> reachable_refs stack' refs n`),
  REWRITE_TAC[reachable_refs_def; MEM] THEN
  REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[RTC_RTC; RTC_RULES]);;

let refs_in_block = prove
 (cake_as_vars (fun () ->
    `MEM v ys /\ MEM r (get_refs v)
     ==> MEM r (get_refs (Block ts tag ys))`),
  REWRITE_TAC[get_refs_def; MEM_FLAT; MEM_MAP] THEN
  ASM_MESON_TAC[]);;
""",

  # the port's own facts about the alignment of the address of a
  # byte of a word, which the lemmas about bytes_to_word share (the
  # first of them is get_byte_bytes_to_word).  They stand here
  # because they are about byte_align and the dimindex, which the
  # file itself reasons about all the time.
  ('data_to_word_memoryProof', 'get_byte_bytes_to_word'): r"""
(* the port's own: the address of a byte of the first word of a
   memory is below the bytes in a word, and the facts that the
   proofs about such an address need of it -- that it is aligned to
   the word, and that two of them are different words *)

(* LOG2 of a numeral, by the equation that defines it *)
let LOG2_RED =
  REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV(REWR_CONV LOG2) THENC
                       NUM_REDUCE_CONV THENC REWRITE_CONV[]));;

(* the slice that takes the bits from p up is the word shifted down
   by p and up again *)
let slice_shl = prove
 (`!p (w:(N)word).
     word_slice (dimindex (:N) - 1) p w = word_shl (word_ushr w p) p`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_slice; word_bits; WORD_EQ_BITS_ALT;
              BIT_WORD_SHL; BIT_WORD_SUBWORD; BIT_WORD_USHR] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `p:num <= i` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `i - p < MIN ((dimindex (:N) - 1 + 1) - p) (dimindex (:N))`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ARITH_RULE `MIN a b = if a <= b then a else b`] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `p + (i - p) = (i - p) + p`]]);;

(* a number below two to the p has nothing left when it is shifted
   down by p *)
let ushr_small = prove
 (`!x p. x < 2 EXP p /\ p <= dimindex (:'a)
         ==> word_ushr ((n2w x):'a word) p = n2w 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_USHR; VAL_WORD] THEN
  MATCH_MP_TAC DIV_LT THEN
  MP_TAC (SPECL [`x:num`; `2 EXP dimindex (:'a)`] MOD_LE) THEN
  ASM_ARITH_TAC);;

(* so the address of a byte of the first word is aligned to it *)
let align_small = prove
 (`!x. good_dimindex (:'a) /\ x < dimindex (:'a) DIV 8
       ==> byte_align ((n2w x):'a word) = n2w 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[byte_align_def; align_def; slice_shl] THEN
  SUBGOAL_THEN `word_ushr ((n2w x):'a word)
                  (LOG2 (dimindex (:'a) DIV 8)) = n2w 0`
    SUBST1_TAC THENL
   [MATCH_MP_TAC ushr_small THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN (fun eq ->
      RULE_ASSUM_TAC(REWRITE_RULE[eq]) THEN SUBST1_TAC eq) o
      REWRITE_RULE[good_dimindex_def]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC LOG2_RED THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    REWRITE_TAC[word_shl; VAL_WORD_0; MULT_CLAUSES]]);;

(* and two numbers below the width of a word are different words *)
let n2w_ne = prove
 (`!a b. a < 2 EXP dimindex (:'a) /\ b < 2 EXP dimindex (:'a) /\
         ~(a = b) ==> ~(((n2w a):'a word) = n2w b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD] THEN
  ASM_SIMP_TAC[MOD_LT]);;

let ne_small = prove
 (`!a b. good_dimindex (:'a) /\ a < dimindex (:'a) DIV 8 /\
         b < dimindex (:'a) DIV 8 /\ ~(a = b)
         ==> ~(((n2w a):'a word) = n2w b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC n2w_ne THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (fun eq ->
    RULE_ASSUM_TAC(REWRITE_RULE[eq]) THEN SUBST1_TAC eq) o
    REWRITE_RULE[good_dimindex_def]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;
""",
  # the induction and the three cases of a RefPtr that the
  # lemmas about a change of the refs, of the heap or of tf share
  # (the first of them is v_inv_tf_update_thm_alt_lemma).  They stand here and not
  # at the head of the file because they are about v_inv_ck and
  # v_inv_def, which the file itself states.
  ('data_to_word_memoryProof', 'v_inv_tf_update_thm_alt_lemma'): r"""
(* the port's own: what the lemmas about a change of the refs
   share.  Each of them says that the clocked relation holds of a
   value after a cell of the refs is put in or changed, and each is
   the same complete induction on the clock, with the same four
   facts about the lookups of the new refs to be proved of the cell
   in question. *)

(* the port's own: a key that the refs do not have has no lookup *)
let no_lk = prove
 (`~(ptr IN domain (refs:(A)spt)) ==> lookup ptr refs = NONE`,
  REWRITE_TAC[domain_lookup] THEN
  STRUCT_CASES_TAC(ISPEC `lookup ptr (refs:(A)spt)`
    (cases_of `:(A)option`)) THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  MESON_TAC[]);;

(* and a key of f is a key of the refs, so it is not one that the
   refs do not have *)
let notptr = prove
 (`lookup ptr refs = NONE /\
   (!x. x IN FDOM f ==> x IN domain refs) /\ k IN FDOM f
   ==> ~(k = ptr)`,
  REWRITE_TAC[domain_lookup] THEN
  MESON_TAC[distinctness "option"]);;

let v_inv_ck_rules = CONJUNCTS (let (vr,_,_) = v_inv_ck in vr);;

(* the b of a RefPtr that the two thunk rules ask to be false *)
let NOT_VAR_TAC =
  FIRST_ASSUM(fun nb ->
    if is_neg(concl nb) && is_var(rand(concl nb))
    then SUBST_ALL_TAC(EQF_INTRO nb) else fail());;

(* the four facts that such a lemma proves of its own refs -- the
   lookup of a thunk, the annotation of a pointer, the dest_thunk
   of a value and the condition of a plain reference, of the new
   refs against the old ones -- which its own `same` gives when it
   is applied to the assumption that says what the refs are *)
let v_inv_refs_parts same lk =
  let s = MATCH_MP same lk in
  (CONJUNCT1 s,CONJUNCT1(CONJUNCT2 s),
   CONJUNCT1(CONJUNCT2(CONJUNCT2 s)),
   CONJUNCT2(CONJUNCT2(CONJUNCT2 s)));;

(* the case of a plain reference, whose annotation is the one it
   was *)
let V_INV_REFS_PLAIN same =
  REPEAT SUBST_LHS_TAC THEN
  FIRST_ASSUM(fun lk ->
    let (t_eq,a_eq,_,m_imp) = v_inv_refs_parts same lk in
    REWRITE_TAC[GSYM a_eq] THEN
    MATCH_MP_TAC(el 4 v_inv_ck_rules) THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM MATCH_ACCEPT_TAC;
      ASM_REWRITE_TAC[t_eq];
      MATCH_MP_TAC m_imp THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

(* and the case of a thunk, whose value and heap element the rule
   names and not its conclusion, so MESON applies the rule *)
let V_INV_REFS_THUNK same n =
  let lt1 = ARITH_RULE `~(ck = 0) ==> ck - 1 < ck` in
  NOT_VAR_TAC THEN REPEAT SUBST_LHS_TAC THEN
  FIRST_ASSUM(fun lk ->
    let (t_eq,_,dt,_) = v_inv_refs_parts same lk in
    FIRST_ASSUM(fun ih ->
      ASM_MESON_TAC[el n v_inv_ck_rules; t_eq; dt;
                    SPEC `ck - 1` ih; lt1]));;

(* the three cases of a RefPtr where the refs do not change and the
   heap does: a plain reference reads nothing of the heap, and the
   heap element of a thunk is the one that the lemma's own
   hypothesis about the two heaps carries over, which is the
   argument.  The witnesses of the two thunk rules are the ones
   that the assumptions name: the thunk of the refs and the
   element of the heap. *)

let V_INV_HEAP_PLAIN =
  REPEAT SUBST_LHS_TAC THEN
  MATCH_MP_TAC(el 4 v_inv_ck_rules) THEN ASM_REWRITE_TAC[];;

let V_INV_HEAP_THUNK hp n =
  let wit =
    W(fun (asl,w) ->
      let thunk = tryfind (fun (_,th) ->
        let t = concl th in
        if is_eq t && hd_is "bvlSem_Thunk" (rand(rhs t))
        then rand(rhs t) else fail()) asl in
      if n = 5 then
        let x = tryfind (fun (_,th) ->
          let t = concl th in
          if is_eq t && hd_is "ThunkBlock" (rand(rhs t))
          then rand(rand(rhs t)) else fail()) asl in
        MAP_EVERY EXISTS_TAC [lhand thunk; rand thunk; x]
      else EXISTS_TAC (rand thunk)) in
  NOT_VAR_TAC THEN REPEAT SUBST_LHS_TAC THEN
  MATCH_MP_TAC(el n v_inv_ck_rules) THEN wit THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM MATCH_ACCEPT_TAC; hp;
         DISCH_TAC THEN CK_IH_TAC];;

(* the induction that the lemmas about a change of the refs share.
   It is the complete induction on the ck of the relation that
   v_inv_SUBMAP_lemma does by hand: the value is taken apart with
   v_inv_def and the rule of the relation for that shape is
   applied, where the maps are the ones they were and what a Block
   asks of its elements is the induction hypothesis at ck - 1.  The
   arguments are the tactic that applies the induction hypothesis
   (CK_IH_TAC where it takes the assumptions as they stand), the
   one that proves the FLOOKUP of tf of a Block (an assumption
   where tf does not change), the tactic that derives from the
   lemma's own hypothesis what its cases use, the one that proves a
   heap_lookup of the new heap (ALL_TAC where the heap does not
   change), and the three of a RefPtr: a plain reference and the
   two thunks. *)
let V_INV_REFS_TAC_IH ih tp prep hp d5 d6 d7 =
  let rl = v_inv_ck_rules in
  let VAL_CASES_TAC (asl,w) =
    CASES_ON_TAC (el 2 (snd(strip_comb w))) (asl,w) in
  let setup =
    MATCH_MP_TAC num_WF THEN X_GEN_TAC `ck:num` THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) ORELSE
     DISCH_TAC) THEN
    prep THEN VAL_CASES_TAC THEN USE_CHANGED [v_inv_def] in
  (* a Number is a small one or a Bignum of the heap *)
  let c1 =
    COND_CASES_TAC THEN STRIP_TAC THEN SUBST_LHS_TAC THENL
     [MATCH_MP_TAC(el 0 rl) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(el 1 rl) THEN ASM_REWRITE_TAC[] THEN hp] in
  let c2 =
    STRIP_TAC THEN REPEAT SUBST_LHS_TAC THEN
    MATCH_MP_TAC(el 2 rl) THEN ASM_REWRITE_TAC[] THEN hp in
  (* a Block is a BlockNil or a BlockRep whose elements the
     induction hypothesis carries over one by one *)
  let c3 =
    COND_CASES_TAC THEN STRIP_TAC THEN REPEAT SUBST_LHS_TAC THENL
     [MATCH_MP_TAC(el 7 rl) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(el 8 rl) THEN REPEAT CONJ_TAC THENL
       [FIRST_ASSUM MATCH_ACCEPT_TAC;
        DISCH_TAC THEN
        FIRST_ASSUM(fun a2th ->
          if can (term_match [] `EVERY2 (p:A->B->bool) l m`)
                 (concl a2th)
          then MP_TAC a2th else fail()) THEN
        (* the elements come with their membership of the two
           lists, which the hypothesis of a lemma about the
           timestamps asks for *)
        ONCE_REWRITE_TAC[LIST_REL_MEM] THEN
        MATCH_MP_TAC MONO_ALL2 THEN BETA_TAC THEN
        REPEAT STRIP_TAC THEN
        TRY(FIRST_ASSUM(fun imp ->
          FIRST_ASSUM(fun m1 -> FIRST_ASSUM(fun m2 ->
            ASSUME_TAC(MP imp (CONJ m1 m2)))))) THEN
        ih;
        tp;
        ASM_REWRITE_TAC[] THEN hp]] in
  let c4 = STRIP_TAC THEN REPEAT SUBST_LHS_TAC THEN
           MATCH_ACCEPT_TAC(el 3 rl) in
  let c5 =
    DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC
      (DISJ_CASES_THEN2 STRIP_ASSUME_TAC STRIP_ASSUME_TAC)) THENL
     [d5; d6; d7] in
  setup THENL [c1; c2; c3; c4; c5];;

(* and the induction as the lemmas whose hypothesis the induction
   hypothesis takes as it stands use it *)

let V_INV_REFS_TAC =
  V_INV_REFS_TAC_IH CK_IH_TAC (FIRST_ASSUM MATCH_ACCEPT_TAC);;
""",
  # the two lemmas about a heap in which one element is replaced by
  # one of the same length, which the proofs about a store into a
  # byte array ask for (v_inv_IMP_lemma is the first of them).  They
  # stand here and not at the head of the file because the second
  # one needs heap_lookup_APPEND, which the file itself proves.
  # what the six lemmas about a copy of a part of a list into
  # another share (the first of them is list_copy_fwd_eq)
  # what the three lemmas about the chain of conses that
  # list_to_v builds share (the first of them is
  # Block_NOT_IN_all_vs)
  # what says that the words of a constant part are counted
  # by part_space_req (the first user is
  # part_to_words_LENGTH)
  # what the four lemmas about the words of a constant part
  # share (the first user is part_to_words_add)
  # what says that the words of a constant part are good_loc
  # (the first user is const_parts_to_words_good_loc)
  ('data_to_word_memoryProof', 'const_parts_to_words_good_loc'): r"""
(* the port's own: what says that the words of a constant part are
   good_loc.  Nothing a part writes is a Loc: it writes words, and
   the entries of the map, which the invariant of the induction
   keeps good. *)

let good_loc_Word = prove
 (`!s w. good_loc s (wordLang_Word w) = T`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [good_loc_def] THEN
  MATCH_REDUCE_TAC THEN REWRITE_TAC[]);;

let good_loc_LN = prove
 (`!s k. good_loc s
           (SND (lookup_mem (LN:(bool#('a word_loc))spt) k))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[lookup_mem_def; lookup_def] THEN
  MATCH_REDUCE_TAC THEN REWRITE_TAC[SND; good_loc_Word]);;

let part_gl = prove
 (`(!k. good_loc s (SND (lookup_mem m k))) /\
   part_to_words c m h (off:'a word) = SOME ((y0,y1),y2)
   ==> good_loc s y1 /\ EVERY (good_loc s o SND) y2`,
  STRIP_TAC THEN
  RULE_ASSUM_TRY (CONV_RULE(REWRITE_CONV[part_to_words_def])) THEN
  POP_ASSUM MP_TAC THEN
  CASES_ON_NAME "h" THEN
  REWRITE_TAC[part_to_words_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  TRY PAIRARG_TAC THEN
  RULE_ASSUM_TRY (CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  TRY(CONV_TAC(TOP_DEPTH_CONV let_CONV)) THEN
  EVERY_CASE_COND_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option";
              PAIR_EQ] THEN
  STRIP_TAC THEN VAR_EQ_TAC THEN
  ASM_REWRITE_TAC[ALL; ALL_MAP; good_loc_Word; o_DEF; SND;
                  make_ptr_def; make_cons_ptr_def] THEN
  ASM_REWRITE_TAC[good_loc_Word; ALL_T]);;

let ins_loc = prove
 (`(!k. good_loc s (SND (lookup_mem m k))) /\ good_loc s y1
   ==> (!k. good_loc s
              (SND (lookup_mem (insert i ((y0:bool),y1) m) k)))`,
  STRIP_TAC THEN GEN_TAC THEN REWRITE_TAC[lookup_mem_insert] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SND]);;
""",

  ('data_to_word_memoryProof', 'part_to_words_add'): r"""
(* the port's own: what the four lemmas about the words of a
   constant part share.  HOL4 gets the sum of two aligned words
   from alignmentTheory; here a shifted word is aligned by the
   definition of align, and each aligned word is a shifted one
   (byte_aligned_IMP_shift). *)

let LOG2_RED =
  REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV(REWR_CONV LOG2) THENC
                       NUM_REDUCE_CONV THENC REWRITE_CONV[]));;

let shl_add = prove
 (`!(a:N word) b n.
     word_shl (word_add a b) n =
     word_add (word_shl a n) (word_shl b n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD_ADD] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[]);;

let byte_aligned_shl = prove
 (`good_dimindex (:'a) ==>
   byte_aligned (word_shl (u:'a word)
                   (backend_common_word_shift (:'a)))`,
  REWRITE_TAC[byte_aligned_def; aligned_def; align_def] THEN
  STRIP_TAC THEN
  (SUBGOAL_THEN `LOG2 (dimindex (:'a) DIV 8) =
                 backend_common_word_shift (:'a)` SUBST1_TAC THENL
    [FIRST_ASSUM MP_TAC THEN
     REWRITE_TAC[good_dimindex_def; word_shift_def] THEN
     DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
     CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC LOG2_RED;
     ALL_TAC]) THEN
  REWRITE_TAC[word_slice; word_bits; WORD_EQ_BITS_ALT;
              BIT_WORD_SHL; BIT_WORD_SUBWORD;
              ARITH_RULE `MIN a b = if a <= b then a else b`] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REPEAT COND_CASES_TAC THEN
  ASM_CASES_TAC `word_shift (:'a) <= i` THEN ASM_REWRITE_TAC[] THEN
  (SUBGOAL_THEN
     `(word_shift (:'a) + i - word_shift (:'a)) -
      word_shift (:'a) = i - word_shift (:'a)` SUBST1_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN
     `i - word_shift (:'a) <
        (dimindex (:'a) - 1 + 1) - word_shift (:'a) /\
      word_shift (:'a) <= word_shift (:'a) + i - word_shift (:'a) /\
      word_shift (:'a) + i - word_shift (:'a) < dimindex (:'a)`
     STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM MP_TAC THEN
     REWRITE_TAC[good_dimindex_def; word_shift_def] THEN
     ASM_ARITH_TAC;
     ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN
  (SUBGOAL_THEN `i - word_shift (:'a) < dimindex (:'a)`
     ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  ASM_REWRITE_TAC[]);;

let byte_aligned_add = prove
 (`good_dimindex (:'a) /\ byte_aligned (a:'a word) /\ byte_aligned b
   ==> byte_aligned (a + b)`,
  STRIP_TAC THEN
  FIRST_ASSUM(fun gd ->
    if not (hd_is "good_dimindex" (concl gd)) then fail() else
    REPEAT(FIRST_X_ASSUM(fun ba ->
      if not (hd_is "byte_aligned" (concl ba)) then fail() else
      CHOOSE_THEN SUBST_ALL_TAC
        (MATCH_MP byte_aligned_IMP_shift (CONJ ba gd)))) THEN
    REWRITE_TAC[GSYM shl_add] THEN
    MATCH_ACCEPT_TAC(GEN_ALL(MATCH_MP byte_aligned_shl gd))));;

(* the header of a bignum, which the two definitions write
   differently: the deep embedding takes the sign bit of a word and
   the shallow one the number 7 or 3 *)

let or43 = prove
 (`((n2w 4):'a word) || n2w 3 = n2w 7`, WORD_NUM_BIT_TAC 3);;

let or03 = prove
 (`((n2w 0):'a word) || n2w 3 = n2w 3`, WORD_NUM_BIT_TAC 2);;

let hdr_bits = prove
 (`good_dimindex (:'a) ==>
   w2n ((b2w sign << 2 || (n2w 3)):'a word) =
   (if sign then 7 else 3)`,
  REWRITE_TAC[b2w_def] THEN DISCH_TAC THEN
  STRUCT_CASES_TAC(SPEC `sign:bool` BOOL_CASES_AX) THEN
  REWRITE_TAC[b2n_def; WORD_SHL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[or43; or03; VAL_WORD] THEN
  FIRST_ASSUM(fun gd ->
    STRIP_ASSUME_TAC(REWRITE_RULE[good_dimindex_def] gd)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* what word_cond_add does to a word that is a pointer and to one
   that is not *)

let cond_add_F = prove
 (`!c a x. word_cond_add c a (F,x) = x`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [word_cond_add_def] THEN
  MATCH_REDUCE_TAC THEN REWRITE_TAC[]);;

let cond_add_T = prove
 (`!c a (w:'a word). word_cond_add c a (T,wordLang_Word w) =
     wordLang_Word (w + a << (shift_length c -
       backend_common_word_shift (:'a)))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [word_cond_add_def] THEN
  MATCH_REDUCE_TAC THEN REWRITE_TAC[]);;

(* the map of the deep embedding with a word put in: what it looks
   up, read as the function of the shallow side with that word put
   in, and the condition of the two maps carried over it *)

let lookup_mem_insert = prove
 (`!m i v j. lookup_mem (insert i v m) j =
             (if j = i then v else lookup_mem m j)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[lookup_mem_def; lookup_insert] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_REDUCE_TAC THEN REWRITE_TAC[]);;

let upd_lookup = prove
 (`!m i (v:bool#('a word_loc)).
     (\j. SND (lookup_mem (insert i v m) j)) =
     ((i =+ SND v) (\j. SND (lookup_mem m j)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[UPDATE] THEN BETA_TAC THEN
  REWRITE_TAC[lookup_mem_insert] THEN
  (ASM_CASES_TAC `(i:num) = j` THENL
    [FIRST_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[];
     ASM_REWRITE_TAC[] THEN
     (SUBGOAL_THEN `~((j:num) = i)` (fun th -> REWRITE_TAC[th])
        THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
     REWRITE_TAC[]]));;

let ins_cond = prove
 (`(!j. SND (lookup_mem m1 j) =
        word_cond_add c a (lookup_mem m j)) /\
   SND v = word_cond_add c a w
   ==> (!j. SND (lookup_mem (insert i v m1) j) =
            word_cond_add c a (lookup_mem (insert i w m) j))`,
  STRIP_TAC THEN X_GEN_TAC `j:num` THEN
  REWRITE_TAC[lookup_mem_insert] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* two lists that a map takes to the same list are of one length *)

let len_of_map = prove
 (`!(l1:A list) (l2:B list) f g.
     MAP (f:A->C) l1 = MAP (g:B->C) l2 ==> LENGTH l1 = LENGTH l2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `LENGTH:C list->num`) THEN
  REWRITE_TAC[LENGTH_MAP]);;

(* the witnesses of an existential whose body says what each of
   them is, the assumption that is an induction hypothesis and the
   one that is the condition of the two maps *)

let EXISTS_EQ_TAC =
  W(fun (asl,w) ->
    if not (is_exists w) then fail() else
    let vs,body = strip_exists w in
    let eqs = conjuncts body in
    let wit = map (fun v ->
      lhs(find (fun t -> is_eq t && rhs t = v) eqs)) vs in
    MAP_EVERY EXISTS_TAC wit);;

let is_ih t = is_forall t && is_imp(snd(strip_forall t));;

let is_cond t = is_forall t && is_eq(snd(strip_forall t));;

(* and the call of a recursion in an assumption, split into its
   result and that result into a pair *)

let pw_is_lhs n t = (try hd_is n (lhs t) with Failure _ -> false);;

let pw_has_call n t =
  (try hd_is n (find_term (hd_is n) t) with Failure _ -> false);;

let PW_SPLIT_CALL_TAC n =
  W(fun g ->
    let th = av_find (pw_has_call n) g in
    CASES_ON_TAC (find_term (hd_is n) (concl th))) THEN
  TRY SAFE_MATCH_REDUCE_ASM_TAC THEN
  RULE_ASSUM_TRY (REWRITE_RULE[distinctness "option"]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  TRY(W(fun g ->
    let th = av_find (fun t -> pw_is_lhs n t &&
                               hd_is "SOME" (rhs t)) g in
    CASES_ON_TAC (rand(rhs(concl th))))) THEN
  TRY SAFE_MATCH_REDUCE_ASM_TAC THEN
  RULE_ASSUM_TRY (REWRITE_RULE[distinctness "option";
                               injectivity "option"; PAIR_EQ]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  TRY SAFE_MATCH_REDUCE_ASM_TAC;;
""",

  ('data_to_word_memoryProof', 'part_to_words_LENGTH'): r"""
(* the port's own: a number that is below 2 EXP 29 is a small int,
   whichever of the two word sizes it is -- which is what says that
   the words of a constant part are counted by part_space_req *)

let small_29 = prove
 (`good_dimindex (:'a) /\ num_of_int (abs i) < 2 EXP 29
   ==> small_int (:'a) i`,
  REWRITE_TAC[good_dimindex_def; small_int_def; dimword] THEN
  STRIP_TAC THEN
  (SUBGOAL_THEN `abs (i:int) < &(2 EXP 29)` MP_TAC THENL
    [FIRST_ASSUM(fun lt ->
       if not (is_binary "<" (concl lt)) then fail() else
       ACCEPT_TAC(ONCE_REWRITE_RULE
         [MATCH_MP INT_OF_NUM_OF_INT (SPEC `i:int` INT_ABS_POS)]
         (REWRITE_RULE[GSYM INT_OF_NUM_LT] lt)));
     ALL_TAC]) THEN
  ASM_REWRITE_TAC[ARITH_RULE `2 EXP 32 DIV 8 = 2 EXP 29`;
                  ARITH_RULE `2 EXP 64 DIV 8 = 2 EXP 61`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC);;
""",

  ('data_to_word_memoryProof', 'Block_NOT_IN_all_vs'): r"""
(* the port's own: what the three lemmas about the chain of conses
   that list_to_v builds share.  Each of them is an induction on the
   list the chain is of, and what the steps need is the three ways
   in which a value is one of the values of the refs and the stack,
   and the two ways in which a value of the chain and the stack is
   one of the chain's own. *)

(* a value of the head of the stack, a value of the rest of it, and
   a value of a shorter stack, are values of the refs and the
   stack *)

let av_in_stack = prove
 (`!x refs stack'.
     MEM x (v_all_vs stack') ==> x IN all_vs refs stack'`,
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let av_in_cons = prove
 (`!x refs v l.
     MEM x (v_all_vs [v]) ==> x IN all_vs refs (v :: l)`,
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[MEM_v_all_vs_extend_tl]);;

let av_in_tl = prove
 (`!x refs v l. x IN all_vs refs l ==> x IN all_vs refs (v :: l)`,
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[MEM_v_all_vs_extend_hd]);;

(* and a value of the refs and a stack is one of the stack or one
   of the refs and any other stack *)

let av_in_refs = prove
 (`!x refs l1 l2.
     x IN all_vs refs l1
     ==> MEM x (v_all_vs l1) \/ x IN all_vs refs l2`,
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[]);;

(* the set of a stack without one of its values is a part of the
   set with it, and the other way about *)

let av_shrink2 = prove
 (`!x refs t h h' l.
     ~(x IN all_vs refs (t :: h :: h' :: l))
     ==> ~(x IN all_vs refs (t :: h' :: l))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MEM_v_all_vs_split; MEM_v_all_vs_extend_hd;
                MEM_v_all_vs_extend_tl]);;

let av_shrink = prove
 (`!x refs t h l.
     ~(x IN all_vs refs (t :: h :: l))
     ==> ~(x IN all_vs refs (t :: l))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MEM_v_all_vs_split; MEM_v_all_vs_extend_hd;
                MEM_v_all_vs_extend_tl]);;

let av_grow = prove
 (`!x refs t h l.
     x IN all_vs refs (t :: l) ==> x IN all_vs refs (t :: h :: l)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[MEM_v_all_vs_split; MEM_v_all_vs_extend_hd;
            MEM_v_all_vs_extend_tl]);;

(* a value of the values of a chain of conses and a stack is the
   first Block of the chain, a value of the element it holds, or a
   value of the rest of the chain and the stack *)

let av_decomp = prove
 (`!x ts t h xs stack'.
     MEM x (v_all_vs (list_to_v ts t (h :: xs) :: stack')) ==>
     x = Block ts cons_tag [h; list_to_v (ts + 1) t xs] \/
     MEM x (v_all_vs [h]) \/
     MEM x (v_all_vs (list_to_v (ts + 1) t xs :: stack'))`,
  (let (_,vsing,_,_) = v_all_vs_clauses () in
   REPEAT GEN_TAC THEN REWRITE_TAC[dataSem_list_to_v_def] THEN
   DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC o
               MATCH_MP MEM_v_all_vs_split) THENL
    [FIRST_ASSUM(fun m ->
       if not (hd_is "MEM" (concl m)) then fail() else
       MP_TAC(REWRITE_RULE[vsing; MEM] m)) THEN
     DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
      [ASM_REWRITE_TAC[];
       FIRST_ASSUM(fun m ->
         if not (hd_is "MEM" (concl m)) then fail() else
         DISJ_CASES_THEN ASSUME_TAC
           (MATCH_MP MEM_v_all_vs_split m)) THEN
       ASM_MESON_TAC[MEM_v_all_vs_extend_tl;
                     MEM_v_all_vs_extend_hd]];
     ASM_MESON_TAC[MEM_v_all_vs_extend_hd]]));;

(* and of the two ways that are left when the value is none of the
   list and the stack, the one through the element the chain holds
   is out, because that element is on the stack *)

let av_decomp2 = prove
 (`!x refs ts t h xs stack'.
     MEM x (v_all_vs (list_to_v ts t (h :: xs) :: stack')) /\
     ~(x IN all_vs refs (t :: ((h :: xs) ++ stack'))) ==>
     x = Block ts cons_tag [h; list_to_v (ts + 1) t xs] \/
     MEM x (v_all_vs (list_to_v (ts + 1) t xs :: stack'))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[APPEND] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun m ->
    if not (hd_is "MEM" (concl m)) then fail() else
    STRIP_ASSUME_TAC(MATCH_MP av_decomp m)) THEN
  ASM_MESON_TAC[av_in_cons; av_in_tl]);;

(* a Block of the chain's own timestamp that is a value of the rest
   of the chain is a value of the list and the stack *)

let av_no_mix = prove
 (`!refs ts t h xs stack' a2 xs2.
     MEM (Block ts a2 xs2)
       (v_all_vs (list_to_v (ts + 1) t xs :: stack'))
     ==> Block ts a2 xs2 IN
           all_vs refs (t :: ((h :: xs) ++ stack'))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun m ->
    MP_TAC(MATCH_MP v_all_vs_list_to_v1
      (CONJ (ARITH_RULE `ts < ts + 1`) m))) THEN
  REWRITE_TAC[APPEND] THEN
  ASM_MESON_TAC[av_in_stack; av_grow]);;

(* and one below the chain's timestamps that is a value of the refs
   and the chain is a value of the refs and the list *)

let av_in_shift = prove
 (`!refs ts t xs stack' t1 a1 xs1.
     t1 < ts /\
     Block t1 a1 xs1 IN all_vs refs (list_to_v ts t xs :: stack')
     ==> Block t1 a1 xs1 IN all_vs refs (t :: (xs ++ stack'))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_MESON_TAC[v_all_vs_list_to_v1]);;

(* while one of the chain's timestamps that is a value of the refs
   and the chain is a value of the chain itself: a value of the
   refs would be one of the list and the stack, which
   blocks_unique_GT_ts says it is not *)

let av_in_mem = prove
 (`!refs ts t xs stack' t1 a1 xs1.
     blocks_unique ts (all_vs refs (t :: (xs ++ stack'))) /\
     ts <= t1 /\ ~(xs1 = []) /\
     Block t1 a1 xs1 IN all_vs refs (list_to_v ts t xs :: stack')
     ==> MEM (Block t1 a1 xs1)
           (v_all_vs (list_to_v ts t xs :: stack'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun inn ->
    if not (is_binary "IN" (concl inn)) then fail() else
    DISJ_CASES_THEN2 ACCEPT_TAC
      (fun inn2 ->
         ASSUME_TAC inn2 THEN
         ASM_MESON_TAC[GEN_ALL blocks_unique_GT_ts;
                       ARITH_RULE `!a b:num. b <= a ==> a >= b`])
      (SPEC `(t:dataSem_v) :: (xs ++ stack')`
         (MATCH_MP av_in_refs inn))));;

(* the Block of an assumption that says a value is one of the refs
   and a stack, the list it holds, and the assumption that says
   that list is not empty *)

let av_blocks (asl,w) =
  map snd (filter (fun (_,th) ->
    is_binary "IN" (concl th) &&
    hd_is "all_vs" (rand(concl th))) asl);;

let av_xs_of th = last(snd(strip_comb(lhand(concl th))));;

let av_a_of th = el 1 (snd(strip_comb(lhand(concl th))));;

let av_find p (asl,w) =
  snd(find (fun (_,th) -> p (concl th)) asl);;

let av_nn g x =
  av_find (fun t -> is_neg t && is_eq (dest_neg t) &&
                    lhand(dest_neg t) = x) g;;
""",

  ('data_to_word_memoryProof', 'list_copy_fwd_eq'): r"""
(* the port's own: what the six lemmas about a copy of a part of a
   list into another share.  HOL4 proves each of them by the
   induction of its definition, which the port has not got (see
   PORTING-GUIDE entry 35), so each is a complete induction on the
   number of elements to copy, in which the four updates of a
   clause of the definition are done one element at a time (the
   step), the first of them against the destination as it stands
   (the base), and the result of the recursion is put together with
   them (the glue). *)

(* an update at the length of a first list is one at the head of
   the second *)

let copy_upd_at = prove
 (`!(l1:A list) l2 x.
     LUPDATE x (LENGTH l1) (l1 ++ l2) = l1 ++ LUPDATE x 0 l2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; APPEND; LUPDATE; NOT_SUC; SUC_SUB1]);;

(* and one at the end of a first list, whose length the index is
   given as, is one of the head of the second *)

let copy_upd_pre = prove
 (`!(l1:A list) k. LENGTH l1 = k ==>
     !e rest x.
        LUPDATE x k (l1 ++ (e :: rest)) = l1 ++ (x :: rest)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[copy_upd_at; LUPDATE]);;

(* one element more of a copy that goes forward: the update is at
   the head of what is left of the destination, and what it writes
   is the next element of the source *)

let copy_step = prove
 (`!(xs:A list) ys xp yp j.
     xp + (j + 1) <= LENGTH xs /\ yp + (j + 1) <= LENGTH ys ==>
     LUPDATE (EL (xp + j) xs) (yp + j)
       (TAKE yp ys ++ TAKE j (DROP xp xs) ++ DROP (j + yp) ys) =
     TAKE yp ys ++ TAKE (j + 1) (DROP xp xs) ++
       DROP ((j + 1) + yp) ys`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `LENGTH (TAKE yp (ys:A list)) = yp` ASSUME_TAC THENL
    [MATCH_MP_TAC LENGTH_TAKE THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `LENGTH (TAKE j (DROP xp (xs:A list))) = j`
     ASSUME_TAC THENL
    [MATCH_MP_TAC LENGTH_TAKE THEN REWRITE_TAC[LENGTH_DROP] THEN
     ASM_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `yp + j =
     LENGTH (TAKE yp (ys:A list) ++ TAKE j (DROP xp (xs:A list)))`
     SUBST1_TAC THENL
    [ASM_REWRITE_TAC[LENGTH_APPEND]; ALL_TAC]) THEN
  REWRITE_TAC[APPEND_ASSOC; copy_upd_at] THEN
  MP_TAC(SPECL [`ys:A list`; `j + yp`] DROP_EL_CONS) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LUPDATE] THEN
  (SUBGOAL_THEN `TAKE (j + 1) (DROP xp (xs:A list)) =
                 TAKE j (DROP xp xs) ++ [EL (xp + j) xs]`
     SUBST1_TAC THENL
    [REWRITE_TAC[TAKE_SUM] THEN AP_TERM_TAC THEN
     REWRITE_TAC[DROP_DROP] THEN
     MP_TAC(SPECL [`xs:A list`; `j + xp`] DROP_EL_CONS) THEN
     (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC[TAKE; TAKE_0; ARITH_EQ; ADD_AC;
                 ARITH_RULE `1 - 1 = 0`];
     ALL_TAC]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND;
              ARITH_RULE `(j + 1) + yp = SUC (j + yp)`]);;

(* the first of them, where the destination is the list itself *)

let copy_base =
  GEN_ALL(REWRITE_RULE[TAKE_0; APPEND; ADD_CLAUSES; TAKE_DROP]
    (SPECL [`xs:A list`; `ys:A list`; `xp:num`; `yp:num`; `0`]
      copy_step));;

(* the four updates of a clause, and what the recursion copies of
   the destination they made, are the copy *)

let copy_glue = prove
 (`!(xs:A list) ys xp yp n.
     4 <= n /\ xp + n <= LENGTH xs /\ yp + n <= LENGTH ys ==>
     TAKE (yp + 4)
       (TAKE yp ys ++ TAKE 4 (DROP xp xs) ++ DROP (4 + yp) ys) ++
     TAKE (n - 4) (DROP (xp + 4) xs) ++
     DROP ((n - 4) + (yp + 4))
       (TAKE yp ys ++ TAKE 4 (DROP xp xs) ++ DROP (4 + yp) ys) =
     TAKE yp ys ++ TAKE n (DROP xp xs) ++ DROP (n + yp) ys`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `LENGTH (TAKE yp (ys:A list)) = yp` ASSUME_TAC THENL
    [MATCH_MP_TAC LENGTH_TAKE THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `LENGTH (TAKE 4 (DROP xp (xs:A list))) = 4`
     ASSUME_TAC THENL
    [MATCH_MP_TAC LENGTH_TAKE THEN REWRITE_TAC[LENGTH_DROP] THEN
     ASM_ARITH_TAC; ALL_TAC]) THEN
  (* the first yp + 4 elements of the destination are the part
     before the copy and the four elements copied *)
  (SUBGOAL_THEN
     `TAKE (yp + 4)
        (TAKE yp (ys:A list) ++ TAKE 4 (DROP xp (xs:A list)) ++
           DROP (4 + yp) ys) =
      TAKE yp ys ++ TAKE 4 (DROP xp xs)` SUBST1_TAC THENL
    [REWRITE_TAC[APPEND_ASSOC] THEN
     (SUBGOAL_THEN `yp + 4 =
        LENGTH (TAKE yp (ys:A list) ++ TAKE 4 (DROP xp (xs:A list)))`
        SUBST1_TAC THENL
       [ASM_REWRITE_TAC[LENGTH_APPEND]; ALL_TAC]) THEN
     MATCH_ACCEPT_TAC TAKE_LENGTH_APPEND;
     ALL_TAC]) THEN
  (* and from the end of the copy on it is the destination's own *)
  (SUBGOAL_THEN
     `DROP ((n - 4) + (yp + 4))
        (TAKE yp (ys:A list) ++ TAKE 4 (DROP xp (xs:A list)) ++
           DROP (4 + yp) ys) = DROP (n + yp) ys` SUBST1_TAC THENL
    [REWRITE_TAC[APPEND_ASSOC] THEN
     (SUBGOAL_THEN `(n - 4) + (yp + 4) = (n - 4) +
        LENGTH (TAKE yp (ys:A list) ++ TAKE 4 (DROP xp (xs:A list)))`
        SUBST1_TAC THENL
       [ASM_REWRITE_TAC[LENGTH_APPEND]; ALL_TAC]) THEN
     REWRITE_TAC[GSYM DROP_DROP] THEN
     REWRITE_TAC[DROP_LENGTH_APPEND] THEN
     REWRITE_TAC[DROP_DROP] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
     ALL_TAC]) THEN
  (* the four elements and the rest of the copy are the copy *)
  REWRITE_TAC[APPEND_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`DROP xp (xs:A list)`; `4`; `n - 4`] TAKE_SUM) THEN
  REWRITE_TAC[DROP_DROP] THEN
  (SUBGOAL_THEN `4 + (n - 4) = n` SUBST1_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `4 + xp = xp + 4` SUBST1_TAC THENL
    [ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN(ACCEPT_TAC o SYM));;

(* the same of an alias, where the copy is of the list it is
   written into: what the four updates wrote is below the source of
   the rest, so the rest reads the list it started with *)

let copy_glue_alias = prove
 (`!(ys:A list) xp yp n.
     yp <= xp /\ 4 <= n /\ xp + n <= LENGTH ys /\
     yp + n <= LENGTH ys ==>
     TAKE (yp + 4)
       (TAKE yp ys ++ TAKE 4 (DROP xp ys) ++ DROP (4 + yp) ys) ++
     TAKE (n - 4)
       (DROP (xp + 4)
         (TAKE yp ys ++ TAKE 4 (DROP xp ys) ++
            DROP (4 + yp) ys)) ++
     DROP ((n - 4) + (yp + 4))
       (TAKE yp ys ++ TAKE 4 (DROP xp ys) ++ DROP (4 + yp) ys) =
     TAKE yp ys ++ TAKE n (DROP xp ys) ++ DROP (n + yp) ys`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `LENGTH (TAKE yp (ys:A list)) = yp` ASSUME_TAC THENL
    [MATCH_MP_TAC LENGTH_TAKE THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `LENGTH (TAKE 4 (DROP xp (ys:A list))) = 4`
     ASSUME_TAC THENL
    [MATCH_MP_TAC LENGTH_TAKE THEN REWRITE_TAC[LENGTH_DROP] THEN
     ASM_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN
     `DROP (xp + 4)
        (TAKE yp (ys:A list) ++ TAKE 4 (DROP xp ys) ++
           DROP (4 + yp) ys) = DROP (xp + 4) ys` SUBST1_TAC THENL
    [REWRITE_TAC[APPEND_ASSOC] THEN
     (SUBGOAL_THEN
        `DROP (xp + 4)
           ((TAKE yp (ys:A list) ++ TAKE 4 (DROP xp ys)) ++
              DROP (4 + yp) ys) =
         DROP ((xp + 4) -
           LENGTH (TAKE yp ys ++ TAKE 4 (DROP xp ys)))
             (DROP (4 + yp) ys)`
        SUBST1_TAC THENL
       [MATCH_MP_TAC DROP_APPEND2 THEN
        ASM_REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC;
        ALL_TAC]) THEN
     ASM_REWRITE_TAC[LENGTH_APPEND; DROP_DROP] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
     ALL_TAC]) THEN
  MATCH_MP_TAC copy_glue THEN ASM_ARITH_TAC);;

(* one element more of a copy that goes backward: the update is at
   the end of the part of the destination that is still its own *)

let copy_step_bwd = prove
 (`!(xs:A list) ys xp yp j.
     j <= xp /\ xp < LENGTH xs /\ j <= yp /\ yp < LENGTH ys ==>
     LUPDATE (EL (xp - j) xs) (yp - j)
       (TAKE ((yp + 1) - j) ys ++
          TAKE j (DROP ((xp + 1) - j) xs) ++ DROP (yp + 1) ys) =
     TAKE ((yp + 1) - (j + 1)) ys ++
       TAKE (j + 1) (DROP ((xp + 1) - (j + 1)) xs) ++
         DROP (yp + 1) ys`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `(yp + 1) - j = (yp - j) + 1` SUBST1_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `(yp + 1) - (j + 1) = yp - j` SUBST1_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `(xp + 1) - (j + 1) = xp - j` SUBST1_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `LENGTH (TAKE (yp - j) (ys:A list)) = yp - j`
     ASSUME_TAC THENL
    [MATCH_MP_TAC LENGTH_TAKE THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  (* the element of the destination that this update writes over *)
  (SUBGOAL_THEN
     `TAKE ((yp - j) + 1) (ys:A list) =
      TAKE (yp - j) ys ++ [EL (yp - j) ys]` SUBST1_TAC THENL
    [REWRITE_TAC[TAKE_SUM] THEN AP_TERM_TAC THEN
     MP_TAC(SPECL [`ys:A list`; `yp - j`] DROP_EL_CONS) THEN
     (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC[TAKE; TAKE_0; ARITH_EQ; ARITH_RULE `1 - 1 = 0`];
     ALL_TAC]) THEN
  (* and the element of the source that it writes, which heads what
     is copied *)
  (SUBGOAL_THEN
     `TAKE (j + 1) (DROP (xp - j) (xs:A list)) =
      [EL (xp - j) xs] ++ TAKE j (DROP ((xp + 1) - j) xs)`
     SUBST1_TAC THENL
    [(SUBGOAL_THEN `j + 1 = 1 + j` SUBST1_TAC THENL
       [ARITH_TAC; ALL_TAC]) THEN
     REWRITE_TAC[TAKE_SUM; DROP_DROP] THEN
     (SUBGOAL_THEN `1 + (xp - j) = (xp + 1) - j` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC]) THEN
     (SUBGOAL_THEN `TAKE 1 (DROP (xp - j) (xs:A list)) =
                    [EL (xp - j) xs]` SUBST1_TAC THENL
       [MP_TAC(SPECL [`xs:A list`; `xp - j`] DROP_EL_CONS) THEN
        (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
        DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[TAKE; TAKE_0; ARITH_EQ;
                    ARITH_RULE `1 - 1 = 0`];
        ALL_TAC]) THEN
     REFL_TAC;
     ALL_TAC]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  FIRST_ASSUM(fun len ->
    if not (hd_is "LENGTH" (lhs(concl len))) then fail() else
    REWRITE_TAC[MATCH_MP copy_upd_pre len]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

let copy_base_bwd =
  GEN_ALL(REWRITE_RULE[SUB_0; LE_0; TAKE_0; APPEND; ADD_CLAUSES;
                       TAKE_DROP]
    (SPECL [`xs:A list`; `ys:A list`; `xp:num`; `yp:num`; `0`]
      copy_step_bwd));;

(* the glue of a copy that goes backward.  The destination may have
   no four elements below the one that is written first, and then
   the recursion is of none, because the number that the definition
   recurses on is a natural one *)

let copy_glue_bwd = prove
 (`!(xs:A list) ys xp yp n.
     4 <= n /\ n <= xp + 1 /\ xp < LENGTH xs /\ n <= yp + 1 /\
     yp < LENGTH ys ==>
     TAKE (((yp - 4) + 1) - (n - 4))
       (TAKE ((yp + 1) - 4) ys ++
          TAKE 4 (DROP ((xp + 1) - 4) xs) ++ DROP (yp + 1) ys) ++
     TAKE (n - 4) (DROP (((xp - 4) + 1) - (n - 4)) xs) ++
     DROP ((yp - 4) + 1)
       (TAKE ((yp + 1) - 4) ys ++
          TAKE 4 (DROP ((xp + 1) - 4) xs) ++ DROP (yp + 1) ys) =
     TAKE ((yp + 1) - n) ys ++ TAKE n (DROP ((xp + 1) - n) xs) ++
       DROP (yp + 1) ys`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `LENGTH (TAKE ((yp + 1) - 4) (ys:A list)) =
                 (yp + 1) - 4` ASSUME_TAC THENL
    [MATCH_MP_TAC LENGTH_TAKE THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN
     `LENGTH (TAKE 4 (DROP ((xp + 1) - 4) (xs:A list))) = 4`
     ASSUME_TAC THENL
    [MATCH_MP_TAC LENGTH_TAKE THEN REWRITE_TAC[LENGTH_DROP] THEN
     ASM_ARITH_TAC; ALL_TAC]) THEN
  (ASM_CASES_TAC `4 <= yp` THENL
    [ALL_TAC;
     (SUBGOAL_THEN `yp = 3 /\ n = 4` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC]) THEN
     ASM_REWRITE_TAC[ARITH; TAKE_0; APPEND; TAKE_DROP] THEN
     NO_TAC]) THEN
  (SUBGOAL_THEN `(yp - 4) + 1 = (yp + 1) - 4` SUBST1_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `((yp + 1) - 4) - (n - 4) = (yp + 1) - n`
     SUBST1_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC]) THEN
  (* what the recursion keeps of the destination is the part below
     the copy, and what it drops is the four elements copied *)
  (SUBGOAL_THEN
     `TAKE ((yp + 1) - n)
        (TAKE ((yp + 1) - 4) (ys:A list) ++
           TAKE 4 (DROP ((xp + 1) - 4) (xs:A list)) ++
             DROP (yp + 1) ys) = TAKE ((yp + 1) - n) ys`
     SUBST1_TAC THENL
    [MP_TAC(SPECL [`TAKE ((yp + 1) - 4) (ys:A list)`;
                   `TAKE 4 (DROP ((xp + 1) - 4) (xs:A list)) ++
                      DROP (yp + 1) (ys:A list)`;
                   `(yp + 1) - n`] TAKE_APPEND1) THEN
     (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
     DISCH_THEN SUBST1_TAC THEN
     MATCH_MP_TAC TAKE_TAKE THEN ASM_ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `DROP ((yp + 1) - 4)
        (TAKE ((yp + 1) - 4) (ys:A list) ++
           TAKE 4 (DROP ((xp + 1) - 4) (xs:A list)) ++
             DROP (yp + 1) ys) =
      TAKE 4 (DROP ((xp + 1) - 4) xs) ++ DROP (yp + 1) ys`
     SUBST1_TAC THENL
    [FIRST_ASSUM(fun len ->
       if not (hd_is "TAKE" (rand(lhs(concl len)))) then fail() else
       GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV)
         [SYM len]) THEN
     MATCH_ACCEPT_TAC DROP_LENGTH_APPEND;
     ALL_TAC]) THEN
  (* and the four elements complete the copy *)
  AP_TERM_TAC THEN REWRITE_TAC[APPEND_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  (ASM_CASES_TAC `4 <= xp` THENL
    [(SUBGOAL_THEN `((xp - 4) + 1) - (n - 4) = (xp + 1) - n`
        SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC]) THEN
     MP_TAC(SPECL [`DROP ((xp + 1) - n) (xs:A list)`; `n - 4`; `4`]
       TAKE_SUM) THEN
     REWRITE_TAC[DROP_DROP] THEN
     (SUBGOAL_THEN `(n - 4) + ((xp + 1) - n) = (xp + 1) - 4`
        SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC]) THEN
     (SUBGOAL_THEN `(n - 4) + 4 = n` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC]) THEN
     DISCH_THEN(ACCEPT_TAC o SYM);
     (* the source has no four elements below the first it is read
        at either, so the recursion copies none *)
     (SUBGOAL_THEN `n = 4` SUBST_ALL_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC]) THEN
     REWRITE_TAC[ARITH; TAKE_0; APPEND]]));;

(* and of an alias, where what the four updates wrote is above the
   source of the rest *)

let copy_glue_bwd_alias = prove
 (`!(ys:A list) xp yp n.
     xp <= yp /\ 4 <= n /\ n <= xp + 1 /\ xp < LENGTH ys /\
     n <= yp + 1 /\ yp < LENGTH ys ==>
     TAKE (((yp - 4) + 1) - (n - 4))
       (TAKE ((yp + 1) - 4) ys ++
          TAKE 4 (DROP ((xp + 1) - 4) ys) ++ DROP (yp + 1) ys) ++
     TAKE (n - 4)
       (DROP (((xp - 4) + 1) - (n - 4))
         (TAKE ((yp + 1) - 4) ys ++
            TAKE 4 (DROP ((xp + 1) - 4) ys) ++
              DROP (yp + 1) ys)) ++
     DROP ((yp - 4) + 1)
       (TAKE ((yp + 1) - 4) ys ++
          TAKE 4 (DROP ((xp + 1) - 4) ys) ++ DROP (yp + 1) ys) =
     TAKE ((yp + 1) - n) ys ++ TAKE n (DROP ((xp + 1) - n) ys) ++
       DROP (yp + 1) ys`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `LENGTH (TAKE ((yp + 1) - 4) (ys:A list)) =
                 (yp + 1) - 4` ASSUME_TAC THENL
    [MATCH_MP_TAC LENGTH_TAKE THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN
     `TAKE (n - 4)
        (DROP (((xp - 4) + 1) - (n - 4))
          (TAKE ((yp + 1) - 4) (ys:A list) ++
             TAKE 4 (DROP ((xp + 1) - 4) ys) ++
               DROP (yp + 1) ys)) =
      TAKE (n - 4) (DROP (((xp - 4) + 1) - (n - 4)) ys)`
     SUBST1_TAC THENL
    [(ASM_CASES_TAC `n = 4` THENL
       [POP_ASSUM SUBST_ALL_TAC THEN
        REWRITE_TAC[ARITH; TAKE_0];
        ALL_TAC]) THEN
     (SUBGOAL_THEN `((xp - 4) + 1) - (n - 4) = (xp + 1) - n`
        SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC]) THEN
     MP_TAC(SPECL [`TAKE ((yp + 1) - 4) (ys:A list)`;
                   `TAKE 4 (DROP ((xp + 1) - 4) (ys:A list)) ++
                      DROP (yp + 1) (ys:A list)`;
                   `(xp + 1) - n`] DROP_APPEND1) THEN
     (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
     DISCH_THEN SUBST1_TAC THEN
     MP_TAC(SPECL [`DROP ((xp + 1) - n)
                      (TAKE ((yp + 1) - 4) (ys:A list))`;
                   `TAKE 4 (DROP ((xp + 1) - 4) (ys:A list)) ++
                      DROP (yp + 1) (ys:A list)`;
                   `n - 4`] TAKE_APPEND1) THEN
     (ANTS_TAC THENL
       [REWRITE_TAC[LENGTH_DROP] THEN ASM_ARITH_TAC; ALL_TAC]) THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC[DROP_TAKE] THEN
     MATCH_MP_TAC TAKE_TAKE THEN ASM_ARITH_TAC;
     ALL_TAC]) THEN
  MATCH_MP_TAC copy_glue_bwd THEN ASM_ARITH_TAC);;

(* the bounds of the shape a + k <= b, and of the shape k <= v for
   a copy that goes backward, that arithmetic gives of the goal for
   the four k that the clauses of a definition use, and the length
   of every TAKE of it *)

let COPY_BNDS_TAC =
  W(fun (asl,w) ->
    let bnds = itlist (fun (_,th) acc ->
      (try let l,r = dest_binary "<=" (concl th) in
           let a,_ = dest_binary "+" l in
           (map (fun k -> mk_binary "<="
                   (mk_binary "+" (a,mk_small_numeral k), r))
                [1; 2; 3; 4]) @ acc
       with Failure _ -> acc)) asl [] in
    MAP_EVERY (fun tm ->
      TRY(SUBGOAL_THEN tm ASSUME_TAC THENL
           [ASM_ARITH_TAC; ALL_TAC])) (setify bnds));;

let COPY_BNDS_B_TAC =
  W(fun (asl,w) ->
    let vs = setify(filter (fun v -> type_of v = `:num`)
      (itlist (fun (_,th) acc -> frees(concl th) @ acc) asl
         (frees w))) in
    MAP_EVERY (fun (k,v) ->
      TRY(SUBGOAL_THEN (mk_binary "<=" (mk_small_numeral k, v))
            ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]))
      (allpairs (fun k v -> (k,v)) [1; 2; 3] vs));;

let COPY_LEN_TAC =
  W(fun (asl,w) ->
    let takes = setify(find_terms (fun t ->
      hd_is "TAKE" t && length (snd(strip_comb t)) = 2) w) in
    MAP_EVERY (fun t ->
      let k = hd(snd(strip_comb t)) in
      TRY(SUBGOAL_THEN (mk_eq(mk_icomb(`LENGTH`,t), k)) ASSUME_TAC
           THENL
           [MATCH_MP_TAC LENGTH_TAKE THEN
            REWRITE_TAC[LENGTH_DROP] THEN ASM_ARITH_TAC;
            ALL_TAC])) takes);;
""",

  ('data_to_word_memoryProof', 'v_inv_IMP_lemma'): r"""
(* the port's own: a heap in which one element is replaced by one
   of the same length.  A split of it gives the halves of the old
   heap, up to that element, and a lookup in it is the old one
   unless it is that element that is found.  Both are used by the
   theorems about a store into a byte array, of which
   v_inv_IMP_lemma is the first. *)

let heap_split_replace = prove
 (`!e ha u v hb h1 h2.
     heap_split e (ha ++ [u] ++ hb) = SOME (h1,h2) /\
     el_length u = el_length v
     ==> ?h1' h2'. heap_split e (ha ++ [v] ++ hb) = SOME (h1',h2') /\
                   (!z. MEM z h1' ==> MEM z h1 \/ z = v)`,
  (* the witnesses are what the equations of the goal say *)
  let witness =
    W(fun (asl,w) ->
      let vs,bod = strip_exists w in
      MAP_EVERY EXISTS_TAC (map lhs (conjuncts (lhand bod)))) THEN
    REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(fun eq ->
      if is_eq (concl eq) && is_var (rhs (concl eq)) &&
         not (lhs (concl eq) = rhs (concl eq))
      then SUBST_ALL_TAC (SYM eq) else fail())) THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[APPEND_NIL; APPEND; MEM_APPEND; MEM] THEN
    CONV_TAC TAUT in
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[heap_split_APPEND_if] THEN COND_CASES_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[heap_length_clauses; heap_split_def] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  EVERY_CASE_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option";
              PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN witness);;

let heap_lookup_replace = prove
 (`!n ha u v hb z.
     heap_lookup n (ha ++ [u] ++ hb) = SOME z /\
     el_length u = el_length v /\ ~(z = u)
     ==> heap_lookup n (ha ++ [v] ++ hb) = SOME z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[data_to_word_memoryProof_heap_lookup_APPEND] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[heap_lookup_def; heap_length_clauses] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
  ASM_MESON_TAC[]);;
""",
  # the two facts about the size of a list that the termination of
  # bvi_let's compile needs: its Let clause recurses on the list
  # without its last expression and on that last expression, and
  # ml/lib/define.ml invites a ported file to add the lemmas that
  # its own definitions ask for.  They are taken back after
  # compile_sing, which is the other definition that needs them
  # (overrides.EXTRA_AFTER).
  ('bvi_let', 'compile_def'): r"""
(* the size facts that the termination of the two definitions of
   this file needs, which ml/lib/define.ml takes from here, and the
   budget that their recursion asks for: eight seconds is what a
   definition of the port is given before it is assumed instead,
   and these two take about twenty each *)

let bvi_let_term_facts = !cake_term_facts;;
let bvi_let_budget = !cake_cheat_budget;;
cake_term_facts := list_size_BUTLAST :: list_size_LAST ::
                   (!cake_term_facts);;
cake_cheat_budget := 300;;
""",
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
(* HOL4 x64_targetScript.sml:226-248, arm8_targetScript.sml:298-341,
   mips_targetScript.sml:118-337, riscv_targetScript.sml:88-303,
   arm7_targetScript.sml:263-293 and ag32_targetScript.sml:243-265:
   the asm configuration of the six targets.  Every field of one of
   them is data, except the encoder -- and the valid_imm of arm8 and
   of arm7, which needs the model as well (arm8's is data but for
   the EncodeBitMask of it, arm7's is IS_SOME o EncodeARMImmediate).
   Those get an implicit definition, which says nothing about their
   value; the configurations themselves are definitions of the port.
   The fields of an asm_config, in the order in which the port
   declares them (compiler/encoders/asm/asm.ml), are ISA, encode,
   big_endian, code_alignment, link_reg, avoid_regs, reg_count,
   fp_reg_count, two_reg_arith, valid_imm, addr_offset, hw_offset,
   byte_offset, jump_offset, cjump_offset and loc_offset; the
   comments below name the ones of every line.  Where the source
   antiquotes a word that its ML computes, the port writes the
   expression that the ML evaluates, as it does everywhere else *)

cake_declare "x64_enc" `:(64)asm->word8 list`;;
cake_declare "arm8_enc" `:(64)asm->word8 list`;;
cake_declare "mips_enc" `:(64)asm->word8 list`;;
cake_declare "riscv_enc" `:(64)asm->word8 list`;;
cake_declare "arm7_enc" `:(32)asm->word8 list`;;
cake_declare "ag32_enc" `:(32)asm->word8 list`;;
cake_declare "arm8_valid_immediate" `:binop+cmp->(64)word->bool`;;
cake_declare "arm7_valid_immediate" `:(32)word->bool`;;

let x64_config_def = cake_define
  `x64_config =
     mk_asm_config
       // ISA encode big_endian code_alignment link_reg avoid_regs
       x86_64 x64_enc F 0 NONE [4; 5]
       // reg_count fp_reg_count two_reg_arith
       16 8 T
       // valid_imm
       (\b i. sw2sw (INT_MINw:(32)word) <= i /\
              i <= sw2sw (INT_MAXw:(32)word))
       // addr_offset hw_offset byte_offset
       (sw2sw (INT_MINw:(32)word),sw2sw (INT_MAXw:(32)word))
       (sw2sw (INT_MINw:(32)word),sw2sw (INT_MAXw:(32)word))
       (sw2sw (INT_MINw:(32)word),sw2sw (INT_MAXw:(32)word))
       // jump_offset cjump_offset loc_offset
       (sw2sw (INT_MINw:(32)word) + n2w 13,
        sw2sw (INT_MAXw:(32)word) + n2w 5)
       (sw2sw (INT_MINw:(32)word) + n2w 13,
        sw2sw (INT_MAXw:(32)word) + n2w 5)
       (sw2sw (INT_MINw:(32)word) + n2w 7,
        sw2sw (INT_MAXw:(32)word) + n2w 7)`;;

let arm8_config_def = cake_define
  `arm8_config =
     mk_asm_config
       // ISA encode big_endian code_alignment link_reg
       ARMv8 arm8_enc F 2 (SOME 30)
       // avoid_regs: register x18 is reserved on some platforms,
       // e.g., Apple platforms
       [18; 26; 31]
       // reg_count fp_reg_count two_reg_arith valid_imm
       32 0 F arm8_valid_immediate
       // addr_offset hw_offset, each (-off_max12 + off_min9,
       // off_max12 + off_max9)
       (--(w2w (UINT_MAXw:(12)word)) + sw2sw (INT_MINw:(9)word),
        w2w (UINT_MAXw:(12)word) + sw2sw (INT_MAXw:(9)word))
       (--(w2w (UINT_MAXw:(12)word)) + sw2sw (INT_MINw:(9)word),
        w2w (UINT_MAXw:(12)word) + sw2sw (INT_MAXw:(9)word))
       // byte_offset
       (sw2sw (INT_MINw:(9)word),w2w (UINT_MAXw:(12)word))
       // jump_offset cjump_offset loc_offset
       (sw2sw (INT_MINw:(28)word),sw2sw (INT_MAXw:(28)word))
       (sw2sw (INT_MINw:(21)word) + n2w 4,
        sw2sw (INT_MAXw:(21)word) + n2w 4)
       (sw2sw (INT_MINw:(32)word),sw2sw (INT_MAXw:(32)word))`;;

let mips_config_def = cake_define
  `mips_config =
     mk_asm_config
       // ISA encode big_endian code_alignment link_reg avoid_regs
       MIPS mips_enc T 2 (SOME 31) [0; 1; 25; 26; 27; 28; 29; 30]
       // reg_count fp_reg_count two_reg_arith
       32
       // 32
       0 F
       // valid_imm
       (\b i. if b IN {INL And,INL Or,INL Xor,INR Test,
                       INR NotTest}
              then n2w 0 <= i /\ i <= w2w (UINT_MAXw:(16)word)
              else (if b = INL Sub then sw2sw (INT_MINw:(16)word) < i
                    else sw2sw (INT_MINw:(16)word) <= i) /\
                   i <= sw2sw (INT_MAXw:(16)word))
       // addr_offset hw_offset byte_offset
       (sw2sw (INT_MINw:(16)word),sw2sw (INT_MAXw:(16)word))
       (sw2sw (INT_MINw:(16)word),sw2sw (INT_MAXw:(16)word))
       (sw2sw (INT_MINw:(16)word),sw2sw (INT_MAXw:(16)word))
       // jump_offset cjump_offset loc_offset
       (sw2sw (INT_MINw:(32)word) + n2w 12,
        sw2sw (INT_MAXw:(32)word) + n2w 8)
       (sw2sw (INT_MINw:(18)word) + n2w 8,
        sw2sw (INT_MAXw:(18)word) + n2w 4)
       (sw2sw (INT_MINw:(32)word) + n2w 12,
        sw2sw (INT_MAXw:(32)word) + n2w 8)`;;

let riscv_config_def = cake_define
  `riscv_config =
     mk_asm_config
       // ISA encode big_endian code_alignment link_reg
       RISC_V riscv_enc F 2 (SOME 1)
       // avoid_regs: calling conventions:
       // https://riscv.org/specifications/, p109
       // 0 - hardwired zero
       // 2 - stack pointer
       // 3 - global pointer
       // 4 - thread pointer
       // 31 - used by encoder above
       [0; 2; 3; 4; 31]
       // reg_count fp_reg_count two_reg_arith
       32 0 F
       // valid_imm
       (\b i. (if b = INL Sub then sw2sw (INT_MINw:(12)word) < i
               else sw2sw (INT_MINw:(12)word) <= i) /\
              i <= sw2sw (INT_MAXw:(12)word))
       // addr_offset hw_offset byte_offset
       (sw2sw (INT_MINw:(12)word),sw2sw (INT_MAXw:(12)word))
       (sw2sw (INT_MINw:(12)word),sw2sw (INT_MAXw:(12)word))
       (sw2sw (INT_MINw:(12)word),sw2sw (INT_MAXw:(12)word))
       // jump_offset cjump_offset loc_offset
       (sw2sw (INT_MINw:(32)word),n2w 2147481599)
       (sw2sw (INT_MINw:(21)word) + n2w 8,
        sw2sw (INT_MAXw:(21)word) + n2w 4)
       (sw2sw (INT_MINw:(32)word),n2w 2147481599)`;;

let arm7_config_def = cake_define
  `arm7_config =
     mk_asm_config
       // ISA encode big_endian code_alignment link_reg avoid_regs
       ARMv7 arm7_enc F 2 (SOME 14) [13; 15]
       // reg_count fp_reg_count two_reg_arith
       16 32 F
       // valid_imm
       (\c i. arm7_valid_immediate i)
       // addr_offset
       (--(w2w (UINT_MAXw:(12)word)),w2w (UINT_MAXw:(12)word))
       // hw_offset
       (--(w2w (UINT_MAXw:(8)word)),w2w (UINT_MAXw:(8)word))
       // byte_offset
       (--(w2w (UINT_MAXw:(12)word)),w2w (UINT_MAXw:(12)word))
       // jump_offset cjump_offset loc_offset
       (sw2sw (INT_MINw:(26)word) + n2w 8,
        sw2sw (INT_MAXw:(26)word) + n2w 8)
       (sw2sw (INT_MINw:(26)word) + n2w 12,
        sw2sw (INT_MAXw:(26)word) + n2w 12)
       (INT_MINw,INT_MAXw)`;;

let ag32_config_def = cake_define
  `ag32_config =
     mk_asm_config
       // ISA encode big_endian code_alignment link_reg avoid_regs
       Ag32 ag32_enc F 2 (SOME 0) [63]
       // reg_count fp_reg_count two_reg_arith
       64 0 F
       // valid_imm
       (\i n. if ISL i
              then --(n2w 8388607) <= n /\ n < n2w 8388607
              else --(n2w 32) <= n /\ n < n2w 32)
       // addr_offset hw_offset byte_offset
       (--(n2w 8388607),n2w 8388607)
       (--(n2w 8388607),n2w 8388607)
       (--(n2w 32),n2w 31)
       // jump_offset cjump_offset loc_offset
       (--(n2w 2147483647) + n2w 4,n2w 2147483647)
       (--(n2w 2147483647) + n2w 4,n2w 2147483647)
       (--(n2w 2147483647) + n2w 4,n2w 2147483647)`;;
''',
  # the termination of every evaluate: HOL4 proves it with
  ('wordSem', 'evaluate_def'): r'''
let wordSem_fix_clock_IMP =
  try prove
   (`!s x res s1. wordSem_fix_clock s x = (res,s1)
                  ==> wordSem_state_clock s1 <=
                      wordSem_state_clock s /\
                      wordSem_state_termdep s1 =
                      wordSem_state_termdep s`,
    REWRITE_TAC[FORALL_PAIR_THM; wordSem_fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "wordSem_state") THEN
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "wordSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nwordSem_fix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl wordSem_fix_clock_IMP <> `T` then
  cake_term_facts := wordSem_fix_clock_IMP :: (!cake_term_facts);;
''',
  ('flatSem', 'evaluate_def'): r'''
let flatSem_fix_clock_IMP =
  try prove
   (`!s x s1 res. flatSem_fix_clock s x = (s1,res)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; flatSem_fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "flatSem_state") THEN
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "flatSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nflatSem_fix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl flatSem_fix_clock_IMP <> `T` then
  cake_term_facts := flatSem_fix_clock_IMP :: (!cake_term_facts);;
''',
  # imp_res_tac fix_clock_IMP
  ('bvlSem', 'evaluate_def'): r'''
let bvlSem_fix_clock_IMP =
  try prove
   (`!s x res s1. bvlSem_fix_clock s x = (res,s1)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; bvlSem_fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "bvlSem_state") THEN
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "bvlSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nbvlSem_fix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl bvlSem_fix_clock_IMP <> `T` then
  cake_term_facts := bvlSem_fix_clock_IMP :: (!cake_term_facts);;
''',
  ('bviSem', 'evaluate_def'): r'''
let bviSem_fix_clock_IMP =
  try prove
   (`!s x res s1. bviSem_fix_clock s x = (res,s1)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; bviSem_fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "bviSem_state") THEN
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "bviSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nbviSem_fix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl bviSem_fix_clock_IMP <> `T` then
  cake_term_facts := bviSem_fix_clock_IMP :: (!cake_term_facts);;
''',
  ('dataSem', 'evaluate_def'): r'''
let dataSem_fix_clock_IMP =
  try prove
   (`!s x res s1. dataSem_fix_clock s x = (res,s1)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; dataSem_fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "dataSem_state") THEN
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "dataSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\ndataSem_fix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl dataSem_fix_clock_IMP <> `T` then
  cake_term_facts := dataSem_fix_clock_IMP :: (!cake_term_facts);;
''',
  ('closSem', 'evaluate_def'): r'''
let closSem_fix_clock_IMP =
  try prove
   (`!s x res s1. closSem_fix_clock s x = (res,s1)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; closSem_fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "closSem_state") THEN
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "closSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nclosSem_fix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl closSem_fix_clock_IMP <> `T` then
  cake_term_facts := closSem_fix_clock_IMP :: (!cake_term_facts);;
''',
  ('stackSem', 'evaluate_def'): r'''
let stackSem_fix_clock_IMP =
  try prove
   (`!s x res s1. stackSem_fix_clock s x = (res,s1)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; stackSem_fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "stackSem_state") THEN
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "stackSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nstackSem_fix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl stackSem_fix_clock_IMP <> `T` then
  cake_term_facts := stackSem_fix_clock_IMP :: (!cake_term_facts);;
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
  # HOL4's basicSizeTheory has a num_size of its own (the size
  # function of a numeral, which ml/lib/hol4.ml has), and
  # data_space's definition shadows it in every theory that has
  # data_spaceTheory as an ancestor, so the num_size of a later
  # statement is this one.  The port knows of only one num_size
  # (ml/lib/hol4.ml is hand written and no source of the port
  # declares it), so the overload is said here.
  ('data_space', 'num_size_def'): r"""
(* HOL4's basicSizeTheory has a num_size of its own (the size
   function of a numeral, which ml/lib/hol4.ml has), and this
   definition shadows it in every theory that has data_spaceTheory
   as an ancestor -- so the num_size of a later statement is this
   one.  Without the overload the port would read those statements
   as the size function, and two of
   compiler/backend/proofs/data_to_word_memoryProof.ml would say
   something false (see ISSUES.md). *)
hol4_overload "num_size" "data_space_num_size";;
""",
  # the size facts and the budget of bvi_let's two definitions are
  # taken back, so that the files after it see what they had
  ('bvi_let', 'compile_sing_def'): r"""
cake_term_facts := bvi_let_term_facts;;
cake_cheat_budget := bvi_let_budget;;
""",
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
