# Deviations from the HOL4 sources

Everything that the port does differently from CakeML's HOL4
sources, and why.

## Names

- HOL Light has one flat namespace, so a CakeML name that is used
  in more than one theory (or that clashes with a HOL Light name)
  is prefixed with its theory name: `closLang_Var`, `wordSem_state`.
  This mirrors HOL4's own `closLang$Var` qualification.
  See `PLAN.md` and `tools/db.py`.
- A name that several theories of the port define (there are 301
  of them, `Var`, `Add`, `If`, ... of the intermediate languages)
  is an _overloaded_ name in HOL4, which resolves it by the type.
  HOL Light can do that too, so the port declares the name as an
  overload of all the constants that have it
  (`hol4_overload "Var" "closLang_Var"`), and the sources of the
  port then read as the CakeML sources do.
- A HOL4 definition may use the same variable name with two
  different types in two clauses (`every_exp` of `ast` does),
  because HOL4 typechecks every clause on its own.  One HOL Light
  quotation cannot, so such a definition is written as a list of
  quotations (`cake_define_list`).
- Where the name of a constructor in a pattern is ambiguous, the
  clause says which constructor it is.  If the type of the
  constructor has no parameters the pattern carries that type
  (`(Var t v:closLang_exp)`); if it has parameters the pattern
  has the name of the constant instead, because a type variable
  that the port writes is rigid in HOL Light and the definition
  may use the type at a more special one.
- A bound variable whose name is a constant of HOL Light or of the
  port is renamed (`get_byte` becomes `get_byte'`): HOL4 lets a
  variable shadow a constant, HOL Light does not.
- A constant whose name the port keeps although other theories
  have the name too is declared as an overload of itself
  (`walk` of the theory `walk`, `evaluate` of `evaluate`): an
  overload that another theory declares for its own constant
  would otherwise hide it, because HOL Light looks a name up in
  the interface before the constants.
- Where a constant and a type of the same theory have the same
  name and the name is one that other theories use as well, the
  type keeps it and the constant is prefixed
  (`semantics$semantics` is `semantics_semantics`, the type
  `semantics` stays): the definition of the constant would
  otherwise be parsed with the overloads that the other
  theories declared for their own `semantics`.
- The hand written files of `ml/lib` stand for HOL4 theories, so
  a name of theirs that a ported theory has as well is
  overloaded like any other (`fromList` is the one of `llist`
  and the one of `sptree`).
- The name of the OCaml binding of a definition cannot start with
  a capital letter unless the name has another capital in it
  (HOL Light's parser), so `Lnext_def` becomes `lnext_def`.  The
  constant itself keeps its name.
- A constant whose name HOL Light's term parser reserves (`match`
  of `pattern_semantics`; the other reserved words are `let`, `in`,
  `and`, `if`, `then`, `else`, `with`, `function` and `when`) is
  renamed as a clashing name is.
- Several record types have a field of the same name, and HOL4
  resolves such a name by the type of the record.  The port
  declares the accessor and the update of such a field as overloads
  so that HOL Light resolves it the same way: with the name that
  HOL4 gives the accessor (`state_clock`) where the record types
  all have the same name, and with the name of the field itself
  (`be`, `limit`, `stack`, ...) where they do not.  A variable that
  is called after one of the latter is renamed (`pc` becomes
  `pc'`).  The fields `v`, `c` and `max_app`, which a great many
  variables are called after, have a default record type instead
  (`FIELD_DEFAULT` of `tools/overrides.py`).

## Syntax

- HOL4's `simpleSexp` writes an s-expression list as
  `⟪x; y; z⟫` and a cons as `⟪h • t⟫`
  (`add_listform` and `add_rule`); the port writes out the
  `SX_CONS` chain that those stand for, ending in the `nil`
  that the theory overloads with the symbol `"nil"`.

- Record fields: `r.fld` becomes `ty_fld r`, `r with fld := v`
  becomes `ty_fld_fupd (K v) r` and `<|fld := v|>` becomes
  `mk_ty v ...`, because HOL Light has no record syntax.  A
  literal that does not give every field (`bviSem`'s `bvi_to_bvl`)
  gets `ARB` for the fields it leaves out, where HOL4 updates an
  arbitrary record of the type; both leave those fields
  unspecified, but the two terms are not the same.  The record
  type of a literal is the one whose fields are exactly the ones
  that the literal gives; where several types fit (a literal of a
  `c` and a `v` is a `sem_env`, and one of a `v` on its own an
  environment of `flatSem`, while the `global_env` of
  `source_to_flatProof` has a `c`, a `v` and a `tys`),
  `RECORD_OF` in `tools/overrides.py` names it.
- HOL4's `Overload`s are parse abbreviations; the port expands
  them, so that it does not introduce constants that HOL4 does
  not have.  An overload of one constant whose name another
  theory of the port uses for a constant of its own (`Less` of
  `comparison`, which `closLang` and `asm` have as a
  constructor) is an exception: expanding it would resolve the
  name the wrong way in those theories, so the port declares it
  as an overload of HOL Light instead.  An overload that is a
  lambda (`mlstring`'s `^`, which is `\x y. strcat x y`) is
  written as that lambda applied to its arguments, where HOL4
  reduces it away.
- HOL4 type abbreviations with parameters (`('a,'b) alist`) are
  expanded as well, as HOL Light has no parameterised type
  abbreviations.
- Type variables that the CakeML sources write as Greek letters
  become `'ga`, `'gb`, ... (HOL Light has no Greek letters); a
  Greek letter that a source uses for a _term_ variable (`μ`, `σ`,
  `τ` and `ρ` of `parmove`) becomes `mu`, `sigma`, `tau`, `rho`.
- HOL4's `one`, the type with one element, is HOL Light's `1`
  (its element is `one` in both).
- A restricted quantifier (`!x::s. P`) is `RES_FORALL s (\x. P)`,
  as HOL4's `res_quan` defines it; `l❲i❳` is `EL i l` and
  `l❲i |-> v❳` is `LUPDATE v i l`; `R^*` is `RTC R`.
- A definition that HOL4 makes in ML from a quotation that it
  keeps in a value (`SmartOp2` of `bvl_const` and five others) is
  ported as the definition that the quotation gives.
- An infix that a source declares itself and overloads with one
  constant (`backend_common`'s `§`, `parmove`'s `▷` and `↪`) is
  written as an application of that constant: HOL Light's lexer
  has no such symbols.
- A relation that a source defines with ML code (`Hol_reln` with
  `replace_quote`: `step` and `dstep` of `parmove`) is ported as
  an inductive definition of the rules that the ML code builds.
- A definition that a source makes with ML code is ported like the
  others: `Define` with any wrapper around it (`data_to_word` has
  sixty definitions behind its own `assign_Define`), `tDefine`,
  and a definition from a quotation that the source keeps in a
  value (`stack_rawcall`'s `comp` and six others).
- `^x` is HOL4's antiquotation of an ML value, which the port
  splices in (the sources use it for the state variable of a
  semantics: `dataSem` writes `evaluate (If n c1 c2,^s)`).
- The monadic machinery that `ml_monadBaseLib` generates with ML
  code for `reg_alloc` and `linear_scan` (the accessors of the
  state record, the manipulators of its fixed size arrays, the
  functions of its exception type and the run function of an
  initial state: about ninety definitions) is written out by the
  port.
- `do x <- e; f od` is the bind of the monad that the source has
  enabled with `monadsyntax` (`st_ex_bind` of `ml_monadBase`,
  `pegresult_bind` of `cmlParse`, `OPTION_BIND` of the option
  monad), and `return` is its unit; where no monad is enabled it is
  HOL4's overloaded `monad_bind`, which a source may overload
  itself (`cmlPEG` does).
- HOL4's `&` is a prefix that binds looser than application, so
  `&LENGTH l` is `&(LENGTH l)`.
- HOL Light's numerals are natural numbers, so a numeral of type
  `int` is written `&n`.  The port does that for the definitions of
  `INT_NUMERALS`, for a numeral with a type annotation of `int` or
  `real`, for an argument of a constructor whose type is one of
  them, and for a numeral in a comparison or a sum with a variable
  that a pattern binds to such an argument.
- Lines of the ported files are at most 72 characters, with one
  exception: `export$preamble` is a list of the lines of a C
  preprocessor prelude, and one of those strings is longer than
  that by itself.

- HOL4 resolves the name of a constant in the scope of the
  theory that uses it; the port has one namespace, in which the
  overload of a theory that is loaded later is in the way.  Where
  the type decides, both resolve it the same way.  Where it does
  not, the port writes the name of the constant out: in a pattern
  it does that by itself, and in the body of a definition `CON_OF`
  in `tools/overrides.py` says which theory is meant
  (`stack_remove$single_stack_free` builds the `Inst` of
  `stackLang`).
- A name of a theory that `set_grammar_ancestry` leaves out is
  not in the scope of the source, although HOL4 has it as an
  ancestor: `backendProof`'s `config` is `backend`'s and not
  `compiler`'s (`GRAMMAR_ANCESTRY` in `tools/overrides.py`).
- The type of the argument of a constructor says which theory an
  ambiguous constructor inside it is of, where every constructor
  of that name says the same (the argument of a `Litv` is an
  `ast$lit`, whichever `Litv` it is).
- The relations of an `Inductive` get the overloads of HOL4 that
  the constants of a `Definition` get: without them a later
  block that writes the name as HOL4 does
  (`source_to_flatProof$env_all_rel` says `env_rel`) gets the
  constant of another theory that has that name.  The names
  that a `CON_OF` of a definition sets are restored to what
  they were after the block, not removed, and a name that was
  not an overload does not become one.

- The relation that the port takes from a `Termination` is
  parsed in a function (`cake_define_list_try`), so that a
  relation that does not typecheck only costs the measure
  rather than being an error that the file does not survive;
  `tools/relcheck.py` says which they are.

- Where one theory uses two record types that have a field of the
  same name, `FIELD_VAR` says which record a variable is of
  (`typeSoundInvariants` has the `c` of a `sem_env` and the `c` of
  a `type_env` in one rule), and the port writes the accessor and
  the update of that record out.  `FIELD_VAR_DEF` says it for
  one definition, where the theory uses the name for another
  record there (the `s` of `stack_to_labProof` is the state of
  stackSem everywhere except in `make_init`, which builds one
  out of a state of labSem); the overloads whose body reads a
  field of it are expanded again for such a definition.
- The overload that a file makes for `++` (the choice of a monad
  that it enables, or an append of its own) is taken back at the
  end of the file with `hol4_only`: an overload stays in HOL
  Light's interface until it is overridden, and a later file where
  nothing says the type of the two sides would then mean the wrong
  one.  Where a file uses `++` for the append of two lists and has
  the overload itself, the port writes `APPEND`
  (`PLAIN_APPEND` of `tools/overrides.py`).
- The rules of an `Inductive` that HOL4 writes with a label in
  front of each of them (`[~Number:]`) are conjuncts of their own
  in the port, which is what HOL4 makes of them.
- The value of a record update binds tighter than `=` and `/\` in
  HOL4 (`D with locals := D.locals = D` is an equation), which the
  port's parser follows.
- Of a HOL4 library theory that the port only needs a part of, the
  rest is not in the port's namespace at all (`ONLY_NAMES`): of
  `regexp_compiler` the port takes the `vector` that CakeML's
  `mlvector` is about, and of `simpleSexp` the s-expressions that
  `fromSexp` reads, and nothing else.
- HOL4's `oHD`, `MAX_LIST`, `splitAtPki`, `isHexDigit`, `EVERY2`
  and `STRING` are in the library layer (`ml/lib/hol4.ml`), the
  first four as definitions and the last two as the names that
  HOL Light has for them (`ALL2` and `CONS`).
- `fail` is the failure of the option monad (`NONE`),
  `monad_unitbind` its unit bind (`OPTION_IGNORE_BIND`) and
  `lift2` HOL4's `OPTION_MAP2`; `assert` (an overload of HOL4's
  `optionTheory`) is the `OPTION_GUARD` of the library layer,
  which the port has to write out because `asmSem` and `labSem`
  define an `assert` of their own and HOL Light resolves a name
  over the whole namespace; and `comparison`'s `Less`,
  `Equal` and `Greater` are the constructors of the `ordering` of
  `ternaryComparisons`.
- A symbolic prefix and what follows it are kept apart, because
  HOL Light's lexer takes the longest symbol (`-- &n`, not
  `--&n`).
- HOL4's `<>` is a notation for the negated equality, which the
  port writes out; where it stands on its own (`EVERY ((<>) x o
  FST) l`) the port writes the lambda that says the same.
- The size function of a datatype that a definition uses is made
  in front of it (`size_thms`), unless a constant of the port has
  that name already (`balanced_map`'s `size`).
- HOL4's `<=>` is its `=` with another precedence, so a source
  writes it where the two sides are not of type `bool`, which HOL
  Light's `<=>` does not allow (`word_alloc$oracle_colour_ok`
  gives an option).  `IFF_IS_EQ` marks those.
- Two constants of a theory can be given the same name by the
  prefix that the port puts before a name that several theories
  have (`clos_to_bvl` defines `compile_inc` as well as
  `clos_to_bvl_compile_inc`); the renamed one then gets a prime.
  A type and a constant of the same name do not clash.

## Definitions

- A definition whose clauses overlap relies on HOL4's
  first-match semantics (the last clause of `clos_mti`'s
  `collect_args` catches what the first one does not).  The
  port writes such a definition as one clause with a `match`,
  whose arms HOL Light tries in the order in which they stand,
  so that the port means what HOL4 means.  The port finds the
  overlapping clauses itself (`overlapping` in `tools/port.py`);
  `MATCH_FORM` in `tools/overrides.py` names the ones where it
  cannot see the overlap.
- A recursive call under a `MAP` (or an `EVERY`) over a list of
  _pairs_ is not primitive recursive in HOL Light's sense: the
  recursion theorem of a datatype family that nests such a list
  has a function for the list, and one for the pair as well.  The
  port defines those functions too (`define_nested` in
  `ml/lib/define.ml`) and derives the equations as HOL4 states
  them.  Without them `ast$every_exp` took six minutes and failed;
  with them it takes half a second.
- The clauses of a definition by patterns are a quotation each,
  because HOL4 typechecks them one by one and the same variable
  can have another type in another clause.  That loses what one
  clause says about the type of another one, and where a
  constructor name is one that several theories in scope have,
  HOL Light then takes the one of the theory that declared the
  overload last, which need not be the one HOL4 means
  (`bvl_handle$handle_adj_vars` gives back a `bvl` expression,
  and `db_vars`, loaded just before it, has a `Var` of its own).
  Such a definition is one quotation instead
  (`ONE_QUOTATION` in `tools/overrides.py`), in which HOL Light's
  overload resolution sees all the clauses at once.
- Definitions that are not primitive recursive need a
  termination measure.  Where HOL4's `Termination` gives one, the
  port uses it; where HOL4 guessed one, the port uses the sum of
  the sizes of the arguments that are matched on (see
  `auto_measure` in `ml/lib/define.ml`).
- An inductive definition that HOL Light does not make is
  assumed as well: the relations are declared and the rules are
  an axiom.  That is weaker than the definition (it does not
  say that the relation is the least one the rules give), so
  there is no induction theorem, and the second pass has to
  make the definition itself.
- HOL4's first match semantics also shows in a definition of a
  _family_ of functions, where the port cannot write one clause
  with a match (that would be one function).  The clause of a
  constructor that has none of its own is therefore the last
  clause of the function if its pattern is a variable
  (`bvi_tailrec$has_rec_sing` ends with
  `has_rec_sing loc x = F`), which is what HOL4 means by it.

- A list function may fold with a conditional instead of a
  connective (`if f x then T else g xs`), which is how HOL4
  writes `f x \/ g xs`.  The port rewrites the clauses with the
  two tautologies, gives them to the strategy for a list
  function and derives the clauses as they were given
  (`define_cond_bool`).

- A termination goal is alpha-renamed before it is taken apart:
  the goal of a definition by cases has assumptions like
  `(?op xs. Op op xs = expr)` whose bound names are the
  variables of the clause, and HOL Light's `STRIP_TAC` takes an
  existential apart under the name it has, so that `CHOOSE`
  fails and the whole termination proof dies with an exception
  rather than an unproved goal (`FRESH_BOUND_CONV`).

- Where HOL4's `Termination` uses a lemma of its own with
  `imp_res_tac`, the port proves that lemma before the
  definition and puts it in `cake_term_facts` (`EXTRA_BEFORE` in
  `tools/overrides.py`; `bvi_tailrec$term_ok_int` and
  `term_ok_any` are made with `exp_size_get_bin_args`, and every
  `evaluate` of the semantics theories asks for `fix_clock_IMP`).
  `FACTS_TAC` uses such a fact on the assumptions of the goal,
  both ways round, as the equation that a match gives is
  `SOME (x,y) = f e`.

- A definition of one clause whose body is a `match` on its last
  argument and whose arms give `SOME` of the parts of the
  pattern is a _destructor_ (`bvl_handle$dest_Seq`,
  `bvi_tailrec$get_bin_args`, `stackLang$dest_Seq`).  The
  termination proof of a definition that takes an expression
  apart with one asks for the fact that the parts are smaller
  than what they were taken from, which HOL4 states and proves
  by hand (`bvi_tailrec$exp_size_get_bin_args`).  The port proves
  it with the definition itself and puts it in
  `cake_term_facts` (`dest_size_fact` in `ml/lib/define.ml`);
  a part of a type that has no size function of its own counts
  for nothing, and a fact in which no part counts is not made.
  Without it `bvl_handle$compile_seqs` could not be made.  An
  arm that looks at the value of another function
  (`clos_op$dest_Op` gives the parts when `f op` is `SOME i`)
  has that value taken apart first, and only the lists that a
  match still looks at are split: the variables that stand for
  the parts are what the arm says they are.

- Where HOL4's `Termination` gives a relation, the port uses it
  (`cake_define_wf`), also for a definition whose clauses are a
  quotation each (`cake_define_list_wf`): 107 of the 205
  `Termination` blocks of the ported sources are of such a
  definition, and their relation used to be dropped.  HOL4
  numbers the size functions of the types of a family in another
  order than HOL Light does (of `closLang$exp`, HOL4's
  `exp1_size` is the one of a `(num # exp) list` and ours is the
  one of an `exp list`), so a relation that names one keeps the
  name as a variable, and `fix_measure` writes the size function
  of the port down once the type of the variable is known (which
  is where `discharge_conditions` instantiates the relation for
  the condition).  A relation that still has a free variable in
  it is dropped.

- HOL Light's machinery for the admissibility of the recursive
  calls has gaps that the CakeML definitions run into, which
  `ml/lib/fastdef.ml` fills:
  - a call under a `MAP2` has no proforma at all
    (`ADMISSIBLE_MAP2`, with `MAP2_EQ_EL`).  HOL Light's `MAP2`
    takes the elements of the second list with `HD` and `TL`, so
    the proforma is about the element at a position and not
    about the members of the lists, and `EL_list_size` is the
    fact that its goal asks for;
  - `ADMISSIBLE_COND` is proved and not used: the dispatch only
    has a case for a conditional in tail position, so a call
    under a conditional that is not a tail call was proved
    admissible without what the condition says
    (`clos_known$merge` recurses on the elements of two lists
    under `if LENGTH xs = LENGTH ys ...`);
  - a combination is only taken apart where the function does
    not occur as an argument anywhere in it, so a call under a
    `MAP` that is not the whole body is not reached
    (`clos_op$cons_measure` is
    `SUM (MAP cons_measure xs) + LENGTH xs + 1`).  Taking the
    combination apart leaves the `MAP` to the proforma of a
    `MAP`; `ADMISSIBLE_RAND`, which HOL Light proves and does
    not use either, is the cheaper way where the function part
    does not use the function.

- A destructor that gives a _tuple_ and not an option has a
  default for the arm that does not match (`bvl_to_bvi$destLet`
  gives `([],Var 0)`), so its parts are not smaller than the
  argument but not larger either and the fact says `<=`, which
  is what the termination goal of a definition that recurses on
  them asks for.  HOL Light's rewriting does not use the
  injectivity of a datatype of its own accord, so the
  assumptions are rewritten with the injectivity and the
  distinctness of the datatypes that they mention
  (`CON_EQ_TAC`).

- A recursive call in the body of a `let` is proved admissible
  without the equation that the let gives (HOL Light has no
  proforma for a `LET`), so the termination goal of a call on
  what the let binds has nothing to say about it:
  `bvl_to_bvi$compile_exps` recurses on the `args` of
  `let (args,x0) = destLet x2` and its goal arrives without a
  single assumption.  `ADMISSIBLE_LET` carries the equation
  into the body.

- The conditions of a definition arrive as one conjunction,
  which the port used to give to the proof of a measure goal as
  a whole.  An admissibility condition among them asks for
  another proof, so `TERM_TAC` splits the conjunction first and
  sends every conjunct to the proof that fits it.

- The proformas of HOL Light only take an admissibility
  condition apart when the machinery is given no relation, and
  the port gives one, so the condition used to arrive at
  `AGREE_TAC` whole.  It is the proformas that carry the
  equation of a pattern into the condition of a recursive call
  under it, which `AGREE_TAC` cannot do, so `ADMISS_TERM_TAC`
  tries them first (`cake_admiss_tac`, which `ml/lib/fastdef.ml`
  exports for it).

- A pattern variable that the arm of a match does not use stays
  an existential in the body of the admissibility condition, and
  HOL Light has no proforma for one (`ADMISSIBLE_EXISTS`).  Its
  bound variable is renamed before the proforma is applied: the
  handler of `wordLang$Call` binds `l1` and `l2`, which the
  return of the same `Call` binds too, and the match of the
  proforma confuses the two.  Together with `ADMISSIBLE_LET` and
  the one substitution at a time of `SUBST_VAR_TAC` this makes
  the definitions of the shape of `wordLang$max_var`.

- The tail of `ml/lib/define.ml` that `tools/bin/mkpatch`
  writes out declares the registries of the machinery again,
  which makes them empty.  A session of a run that it is loaded
  over keeps what the port put in them only because
  `tmp/patchall.ml` puts them back: without the recursion
  theorems (`the_rec_thms`) and the size functions
  (`the_size_fns`) every candidate measure over a datatype is a
  `\x. 0`, and the measurement says nothing.

- A reason of the shape "timeout in <strategy>" says only that
  the budget ran out in that strategy, not that a bigger budget
  would make the definition.  Made again with no budget at all,
  `presLang$ast_t_to_display` still fails after two seconds
  (`existence`) and `presLang$clos_to_display` after nineteen
  minutes, so the budget of thirty seconds of processor time is
  what keeps a run of two hours from being a much longer one.
  The reasons to work on are the ones that a definition reaches
  before the budget does.

- Setting `cake_proforma` writes the dispatch of the
  admissibility proof, and the goals that no proforma takes, to
  `cakeml/tmp/proforma.txt`: that says which proforma the
  library layer is missing.

- The dispatch of the admissibility proof takes the proformas
  that a later file of the library layer registers in
  `admissible_extra`: the one of an `OPTION_MAP` is about the
  `OPTION_MAP` that `ml/lib/hol4.ml` defines, which
  `ml/lib/fastdef.ml` cannot name.

- `SUBST_VAR_TAC` takes one equation at a time, from the
  assumptions as they are then: a substitution rewrites the
  other assumptions, so the theorems of a list made before it
  are stale.  (It lost the pattern of `wordLang$Call`, where the
  injectivity of the constructor first gives `ret' = ret`.)

- A measure may go down by a constant without arguments, which
  only the definition of the constant says the value of
  (`mlint$fromChars` subtracts `padLen_DEC`), so `NUM_CONST_TAC`
  rewrites with the definitions of the ones in the goal.  A
  constant that a specification made says nothing, and is left
  alone.

- A termination goal may need a fact of the one side of an
  equation between its assumptions and of the other, so every
  assumption is copied with the equations used on it
  (`EQ_COPY_TAC`; `clos_known$merge` has `i < LENGTH xs` and
  `LENGTH xs = LENGTH ys`, and the fact about the second list
  asks for `i < LENGTH ys`).

- `FACTS_TAC` instantiates a fact by matching it against the
  goal, and the test that the match determines every variable
  of the fact compared those variables with the ones of the
  instantiation.  HOL Light's `term_match` leaves out an
  instantiation that changes nothing and instantiates the types
  of the variables, so the test threw away every instance of a
  fact that has a type variable (all the ones about a list) or
  whose variable has the name that the goal gives it.  A fact
  that an assumption gives (`imp_res_tac`) is matched against
  the goal as well, because its own variables (the size
  function of `MEM_ZIP_FST`) are not determined by the
  assumption, and a fact whose antecedent is a conjunction is
  given two assumptions.

- The size function of a type that the library layer has one
  for is not defined a second time: `the_rec_thms` has the
  recursion theorem of HOL Light's `list`, so `size_thms "list"`
  defined a `list_size1` of its own, and from then on every
  candidate measure over a list used that one, which none of
  the lemmas (`MEM_list_size`, `list_size_TAKE`, the size
  theorems of the datatypes) is about.

- `define_size` also proves, for every type of a family that is
  a pair, that the size of a `MAP FST` and of a `MAP SND` of a
  list of them is not larger than the size of the list (HOL4
  has it as `list_size_pair_size_MAP_FST_SND`), and puts them
  among the facts.  A fact whose constants are not among the
  ones of the goal is skipped, because there is such a lemma
  for every datatype of the port.

- **The first pass assumes the definitions that none of that
  makes.**  `cake_define` gives every way of making a definition
  a budget of `cake_timeout` seconds (twenty), and states the
  clauses as an axiom when they all fail; `ml/CHEATS.md` lists
  them and `length (axioms ())` counts them (three plus one for
  every assumed definition, or one for every clause of it where
  the clauses had to be assumed one by one).  The second pass has
  to replace each of them by a real definition; until then the
  port is not conservative over HOL Light.

- A termination condition that HOL Light leaves as an
  _admissibility_ (`admissible (<<) p s t`) is proved from the
  definition of `admissible`: the two functions of it agree below
  the measure, so every subterm `f x` of the goal is rewritten
  with that assumption, and what is left is an equation between
  the same terms.  HOL Light's own `ADMISSIBLE_LAMBDA` does not
  reach these, because the argument of the function is a tuple
  of the variables of the clause; the recursive calls of the
  monadic definitions (`reg_alloc`, `linear_scan`, `infer`) and
  of the ones that read an option (`fromSexp`) are under the
  lambda of a bind and have that form.
- The monadic machinery that `ml_monadBaseLib` makes with ML code
  is written out by the port (`monad_access`, `monad_exceptions`,
  `monad_arrays` and `monad_run` in `tools/port.py`).  A theory
  that uses the exception type of another theory gets the
  functions of that type a second time in HOL4
  (`linear_scan` uses `reg_alloc`'s `state_exn`); the port has
  one namespace and the definitions are the same, so it keeps
  the ones of the theory that has the type.

- HOL4 makes CakeML's grammar (`gram$cmlG`) and the datatype of
  its nonterminals (`MMLnonT`) with the ML code of `grammarLib`,
  out of the BNF that the source states.  The port parses that
  BNF itself (`tools/grammardef.py`) and writes the datatype and
  the grammar out: the rules are the finite map from a
  nonterminal to the set of the lists of symbols of its
  alternatives, as `mk_grammar_def` builds it.

## Hand written parts of the library layer

HOL Light has no finite maps, no lazy lists, no bags, no closure
of a relation and no words with HOL4's names, so
`ml/lib/finite_map.ml`, `ml/lib/llist.ml`, `ml/lib/bag.ml`,
`ml/lib/relation.ml` and `ml/lib/words4.ml` are written by hand:

- a finite map is a function to an option type with a finite
  domain, and the operations are HOL4's;
- a lazy list is the function that gives its elements, which is
  `NONE` from the end of the list onwards.  HOL4's `LUNFOLD` is
  coinductive, so the port defines it with a helper
  (`LUNFOLD_state`) that HOL4 does not have;
- the word operations are HOL Light's, under HOL4's names; the
  ones HOL Light does not have are defined in terms of them;
- a bag is the function that gives the number of times an element
  occurs in it, and the reflexive transitive closure is the
  inductive definition that HOL4 has;
- the fold over a finite map (`ITFMAP`) is the relation that says
  what a fold gives and a value that it gives, as HOL4's
  `finite_mapTheory` has it;
- `FOLDR`, whose arguments are in another order than the
  `ITLIST` of HOL Light, and `cwc` of HOL4's `cpsScript` (the
  port does not have that theory), which `unify` uses.

Where HOL Light has a notion of HOL4 under another name, the
port says so with an `override_interface` in `ml/lib/hol4.ml`
(HOL4's `EVERY` is `ALL`, its `BIGUNION` is `UNIONS`, its
`LIST_REL` and `EVERY2` are `ALL2`, its `STRING` is `CONS`),
so that the sources of the port read as the CakeML sources do.

`ml/lib/fastdef.ml` is not a HOL4 theory but a copy of the block
of HOL Light's own `define.ml` that makes
`instantiate_casewise_recursion`,
`pure_prove_recursive_function_exists` and
`prove_general_recursive_function_exists`, word for word, with
two things kept that HOL Light makes anew every time: the
proformas of the admissibility proof (they only depend on a
number of arguments and a theorem) and the last eight existence
theorems (the strategies of `define.ml` ask for the same one over
and over).  The names of HOL Light are then bound to the
functions of that file.  Of the 105 seconds that the existence
theorem of `bvi_let$compile_sing` (twelve clauses) took, 96 went
into the fifteen proformas that it asks for 54 times; with them
kept the theorem takes 9 seconds, and the definition, which the
budget of thirty seconds could not make at all, is made in 25.

HOL4's `pathTheory` is not ported: the dependency analysis found
it only because CakeML definitions use variables called `el`,
`first`, `exists` and `length`.

## Definitions whose form deviates

Every definition of the ported files is in the port.  A handful
state the expression that HOL4's ML code evaluates instead of the
value that it finds, one (`misc$Lnext`) is proved to exist by
hand, and two constants are declared without a value because HOL4
computes them with ML code; `PENDING.md` lists them all, with the
reason.

## The scope of the dependency closure

A source may have more than one `Ancestors` block: the second one
of `clos_to_bvlProof` is `Ancestors[ignore_grammar]`, and it is
the one that has `clos_knownProof` in it.  The dependency scan
(`tools/deps.py`) only read the first, which left twelve
`clos_*Proof` theories out of the closure; they are in since
2026-10-17.  `tools/order1b.py` generates the list of the proof
theories of the pass (the closure minus the definition theories
of `tools/order.txt` and the targets of `tools/excluded.txt`), so
that this cannot drift by hand any more.

## The escapes of a string literal

Both parsers read the escapes of a string literal, and the two
sets are almost the same: HOL4 reads the ones of SML, HOL Light
the ones of OCaml (`parser.ml`'s `escapecode`).  The port writes
the OCaml ones, so an `\a`, `\f`, `\v` or `\u` of SML (which
OCaml does not know) becomes `\007`, `\012`, `\011` and
`\\u`, and a backquote becomes `\096` because it would close
the quotation.  `tools/literals.py` checks the round trip of
every literal of every definition.

## The complement of a word

HOL4 writes the complement of a word `~w`, as it writes the
negation of a truth value: only the type tells the two apart,
which the port cannot do, so the one definition that has it
(`multiword$single_sub`) is ported by hand with `word_1comp`.

## What is not ported

See the list in `PLAN.md`: the L3 instruction set models and the
CakeML theories that instantiate the compiler for one concrete
target, the basis library program with the proof producing
translator and characteristic formulae, and Pancake.

Of the HOL4 library theories (in `ml/lib/`) only the definitions
that the port needs are ported, not the whole theories.

Five definitions of `compiler` are left out for the same reason:
`compile_pancake`, `compile_pancake_64`, `compile_pancake_32` and
the two command line drivers `full_compile_64` and
`full_compile_32`, which compile Pancake when the flag says so.
They need `panStatic$static_check`, `pan_to_target$pan_compile_tap`
and `panPtreeConversion$parse_topdecs_to_ast`, and their patterns
need the constructors of Pancake's error type, so the port cannot
even state them.  `compiler$compile`, which the correctness
theorem is about, does not use them.
