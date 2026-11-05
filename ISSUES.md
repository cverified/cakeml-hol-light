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

## The statements of the theorems (phase two)

- A **definition** of a source is a binding as well, and the
  binding is unique: 249 names are the name of a definition in
  two files or more (`compile_def` in 28 of them), and OCaml has
  one namespace, so the first file to take a name keeps it and a
  later one gets the name of its theory in front
  (`bvi_let_compile_def`).  That is the same rule as for a
  theorem, because one namespace holds both; the inductive
  relations and the definitions of the monadic machinery go
  through it too, so no two files of the port bind one name.  A
  proof names the definition it means, and `cake_def "<const>"`
  is left only in `ml/lib/tactics.ml`, which loads before the
  files whose definitions its tactics unfold.
- A theorem of a source is written the way HOL Light writes one:
  `let name = prove (`...`, CHEAT_TAC);;`, with the attributes
  that HOL4 gives it in a comment over it, and with the name of
  the source in that comment as well where the binding is not
  that name (two files that state a theorem of one name: the
  second gets the name of its theory in front, and so does a
  theorem whose name a definition of an earlier file has).  A statement the
  port cannot read at all is a comment that points at the source
  and names it.
- **The name of a record field is a variable.**  HOL4 has no
  constant of the name of a field: `r.stack` is syntax there, and
  a bare `stack` is a variable of the statement.  The port
  overloads the accessors of a field that several record types
  have with the name of the field, so a statement that uses that
  name for a variable **says the type of that variable**
  (`tools/fieldvars.py`).  Ten statements
  cannot say it -- the type has a variable of its own, or HOL4
  computes the statement -- and those are read with the overloads
  taken away (`cake_as_vars`, 41 statements); the 31 files that
  need the accessors of a field and read the name of that field
  as a variable as well take those pairs out of the interface
  (`hide_overloads`).
- **A name that no theory in scope defines is a variable.**  Each
  file hides those names with HOL Light's own `hide_constant`,
  right after its `needs`, and unhides them at its end (HOL4's
  `Parse.hide` is file-scoped as well).  HOL4 reads such a name
  as a variable because the theory that defines it is not an
  ancestor; the port has every constant in one namespace, so it
  has to hide it.
- A **schematic definition** of HOL4 (`Definition
  foo[schematic]`) has a free variable in its body, which HOL4
  takes into the constant as its **first argument**:
  NTproperties' `nullableML` and `firstSetML` are defined for a
  grammar `G` that their clauses do not mention, and every
  theorem about them applies them to one.  The port writes that
  argument itself (`overrides.SCHEMATIC`), because it reads a
  definition as it stands and a free variable in one is a
  definition it cannot make.
- A comment **inside** a statement is dropped: HOL Light's term
  parser has no comments (`1 + (* two *) 2` is an error there), so
  the `(* gc + dummy *)` of `stack_remove$check_init_stubs_length`
  and the comments of seventy other statements are not in the
  port.  The comments **around** a statement are.
- A theorem that HOL4 states as the value of an ML expression is
  a comment that points at the source and names the theorem: the
  statement is not in the source, HOL4 computes it (`PENDING.md`).
- A statement that **HOL Light's parser does not read** is a
  comment that points at the source as well.  HOL4 gives a
  variable the type that the clause it stands in asks for and
  resolves an overload by what is around it; HOL Light's parser
  has less to go on, so a statement of a source may typecheck
  there and not here.  While a theorem of the port was a
  statement that a wrapper registered, such a statement printed
  `NOT STATED` and the file loaded on; a plain `prove` has no such
  slack, so the names are harvested (`tools/bin/harvestall`,
  `tools/unstated.py`) and the port writes the pointer in their
  place.  Every one of them is a statement to win back
  (PORTING-GUIDE.md, entry 33).
- A statement whose variables hold integers says so nowhere, so
  the port reads it with the types of the constants it applies:
  `tools/intargs.txt` says which argument of a constant is an
  `int` (and which is a function of an `int`), and a numeral in
  such a place is `&n`.

## Syntax

- A **prefix of HOL Light takes the atom after it and no more**:
  `~MEM x l` is `(~MEM) x l` there, while HOL4 reads it as
  `~(MEM x l)`.  The port parenthesises the operand of a `~` and
  of a `-`, and the prefix takes the infixes that bind tighter
  than it does with it (HOL4's `'` is the bit of a word, so
  `~(Smallnum i:'a word) ' 0` says that the bit is not set).
- The **value of a record update stops at an equation**: HOL4
  reads `tenv with v := tenv.v = tenv` as the equation it looks
  like, not as an update whose value is an equation.
- The **finite map and function postfixes bind to the atom**
  before them: `FAPPLY tf⟨ts2 ↦ x⟩` applies `FAPPLY` to the
  updated map, and `map0⦇i ↦ b⦈ k` is `(i =+ b) map0 k`.
- A theorem that the **ML code of a source states itself**
  (`val foo = Q.prove(`...`, tactic)`) is a theorem of the source
  with its statement in it, and the port states it as it states a
  `Theorem`; one whose value is a rule applied to such a theorem
  (`|> SIMP_RULE ...`) is a pointer that names it.

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

## Arithmetic that HOL4 and HOL Light read differently

- HOL4 gives `+` and `-` the same precedence and makes them
  associate to the left, so `h + 1 - l` is `(h + 1) - l`.  HOL
  Light binds `-` tighter than `+` and both to the right, so the
  same text is `h + (1 - l)` there -- a different term, and with
  truncated subtraction a different value (`l = 2` makes it
  `h`, not `h - 1`).  The port's generated files do not have the
  pattern (the translator builds the term), but
  `ml/lib/words4.ml`, which is written by hand, did: `word_bits`,
  the `><` extract and `bit_field_insert` all took the width of
  the field to be `h + 1 - l`.  So `word_bits h l` was the field
  of width `h + (1 - l)` instead of `(h + 1) - l`, which is the
  right one only for `l = 0` and `l = 1`, and a theorem about a
  slice that starts higher up (`all_ones_bit` of
  data_to_word_memoryProof) was **false** as the port stated it.
  The three places now have the parentheses.  A hand-written term
  of the port that mixes `+` and `-` has to be read twice.

- HOL4 types a numeral by what stands around it, and the port has
  to say which type it is: `&n` is the integer (and the real) of
  HOL Light, and a plain numeral is a natural number.
  `tools/hterm.py` turns the integers on where a numeral stands
  beside something that holds one -- a variable the pattern binds
  as an integer, a field of that type, an application of a
  constant whose result is an integer (`tools/intres.txt`) -- and
  that last one reaches too far: the regenerated table has
  `fromString_unsafe` in it, whose result **is** an integer, so
  every numeral of its body became one and `mlint` wrote

      if strlen str = (&0) then (&0:int) else
      if strsub str (&0) = (CHR 126) then ...

  of a source that says `0i` for the one numeral that is an
  integer and `0` for the two that are of natural numbers.  Those
  two do not typecheck, and the file lost the 35 blocks after the
  definition.  A numeral beside an application of a constant of
  the port whose result is of another type is a numeral of that
  type now, whatever the type of the term around the two of them.
  What the rule still cannot see is a numeral in an **argument**
  of such a constant that no comparison stands in: there the port
  would write `&n` where the argument is of a natural number, and
  `tools/bin/intargs` would have to dump the argument positions
  whose type is a concrete type other than `int` for the port to
  know.  None of the 270 files has one today (the two of `mlint`
  were both in a comparison), so the table is not there yet.

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
- The overlap of the clauses of a definition is **not** always
  seen, and where it is not, the axiom that the port assumes
  instead of the definition is **inconsistent**: `|- false`
  follows from it.  `tools/port.py`'s `overlapping` gives up as
  soon as the clause list defines more than one function ("a match
  is one clause, so it cannot define a family"), and that is
  exactly the shape in which the sources write a mutual recursion
  with a catch-all clause per function.  A scan of the axioms of
  the closure of `data_to_word_memoryProof` (2613 of them) finds
  six such definitions:

  | definition | file | what follows |
  | --- | --- | --- |
  | `vb_eq_size` | `compiler/backend/proofs/data_to_word_memoryProof.ml` | `SOME (1,n1 = n2) = NONE` |
  | `vs_depth` | `compiler/backend/semantics/dataSem.ml` | `vs_depth_list ls = 0` |
  | `do_eq` | `semantics/semanticPrimitives.ml` | the `Eq_val` of a pair is `Eq_type_error` |
  | `pmatch`/`pmatch_list` | `semantics/semanticPrimitives.ml` | `Match env = Match_type_error` |
  | `pmatch` | `compiler/backend/pattern_matching/pattern_semantics.ml` | `PMatchSuccess = PTypeFailure` |
  | `has_Eval` | `compiler/backend/flat_elim.ml` | `op = Src Eval \/ has_Eval_list es <=> false` |

  The `vb_eq_size` of `data_to_word_memoryProof` and the
  `vs_depth` of `dataSem` are now in `MATCH_CLAUSES` of
  `tools/overrides.py` and the port writes each of them as a
  match; the other four need the same entry and a run of their
  files.  (`vs_depth` was fixed because `word_eq_thm0` of
  `data_to_word_memoryProof` has it in its statement: a proof of
  that theorem which rewrites with an inconsistent `vs_depth_def`
  would say nothing.)  (The scan also flags thirteen definitions of the
  `*_sing`/`*_list` shape -- `remove_ticks`, `let_op`, `calls`,
  `alt_free`, `scan_expr` and the like -- where the catch-all
  clause and the specific one agree, so those are consistent, only
  redundant.)

- The overlap of the clauses of a definition is **not** always
  seen.  `dataSem$do_eq` (and the `do_eq` of `bvlSem`, `closSem`,
  `flatSem` and `semanticPrimitives`, which are the same
  definition) is a mutual recursion of `do_eq` and `do_eq_list`
  whose clauses are written out one by one, and the last clause of
  each of the two catches what the earlier ones have already given
  a value; as a list of clauses that is inconsistent.  The five are
  now in `MATCH_FORM` of `tools/overrides.py` and the port writes
  them as a match, as it does for every overlapping definition it
  does see.
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
of a relation, no paths and no words with HOL4's names, so
`ml/lib/finite_map.ml`, `ml/lib/llist.ml`, `ml/lib/bag.ml`,
`ml/lib/relation.ml`, `ml/lib/path.ml` and `ml/lib/words4.ml` are
written by hand:

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
- a path is a state and a lazy list of label and state pairs,
  which is the type that HOL4's `pathTheory` makes the type of a
  path of; HOL Light has no greatest fixed point, so the one that
  `okpath` is of HOL4's `okpath_f` is written out, and HOL4's
  `first` is `path_first`, because the port has one namespace and
  `first` is a variable of statements of its own;
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

A definition whose clauses overlap is one clause with a `match`,
which has HOL4's first match semantics (the clauses of a list
would contradict each other).  Where the definition defines a
**family** and only one of its functions has the overlap, a
single match cannot stand for both -- HOL Light's pattern
matching gives the arms of the two functions the same generated
variable, and the two types clash -- so the definition stays a
list of clauses and the clauses of each overlapping function are
one entry of that list, with a match of their own
(`overrides.MATCH_CLAUSES`).  The five are the
`do_eq`/`do_eq_list` of `dataSem`, `bvlSem`, `closSem`,
`flatSem` and `semanticPrimitives`.

## A statement that means another theory's constant

HOL4 reads an overloaded name as the constant of the theory in the
**ancestry** of the file that writes it.  The port has one
interface, so every theory's overload of a name is in it and the
one that was declared last wins where the types do not decide.  A
statement whose types do not pin the name down therefore means
what the file that loaded last says, which is not what HOL4 says.

Two proofs of the port failed for that reason, and only in a
**run** (where the whole load order is in the session); each of
them went through when its own file was loaded in its own closure,
which is why `tools/bin/verifyfile` said they were fine:

- `compiler/backend/proofs/bvi_letProof.ml`, `compile_code_labels`:
  the inline lemma `labs_APPEND` says `MAP get_code_labels (a ++
  b)` with nothing to fix the type of `a`, so in a run it is
  another theory's `get_code_labels` and the rewrite does not fire.
  The type of the list is written down now.
- `compiler/backend/proofs/bvl_constProof.ml`,
  `evaluate_delete_var_Rerr`: the run of 2026-11-04 failed at it
  with `Failure "tryfind"`.  The statement of the source is
  `evaluate (xs,env2,s) = (Rerr e,r) ==> evaluate (MAP delete_var
  xs,env2,s) = (Rerr e,r)`, and the proof rewrites with
  `bvlProps$evaluate_CONS` -- whose own statement

      evaluate (x :: xs,env,s) =
        (match evaluate ([x],env,s) with ...)

  pins no type at all, so in the run it was about
  **`bviSem_evaluate`**: the rewrite fired nowhere, said nothing,
  and the tactic that followed it failed three steps later.  In a
  verify of that one file it passed, because `bviSem.ml` is not in
  its closure.

Both were failing before the port's theorems became bindings as
well: the shape that preceded it caught the failure, wrote NOT
PROVED and made the statement an axiom, so a run reported nothing.

**How wide it is.**  `tools/mkcsts.py` writes the constants of
every theorem that a session has, which are the statements as the
port really read them, and `tools/thyscope.py` says which of them
come out of a theory that the source of the file cannot see: **72
names in 64 theorems** that the scope of the file has a constant of
the same overloaded name for, so that the statement means that one
and the port had it wrong.  `bvlProps` reads `bviSem_evaluate` 13
times, `closProps` and `bviProps` and `bvlProps` read
`dataSem_do_app`, `bvi_tailrecProof` reads `bvi_tmc_compile_exp`,
`dataProps` reads `stackSem_evaluate`.

**The fix** (2026-11-05) is the one this entry called for: the
constants of the theories outside a file's ancestry come out of the
interface while that file loads.  Every file of the port says, in a
line that `tools/port.py` writes under its `needs` lines, which
theories its source can see:

    let _ = hol4_ancestors "bvlProps"
      ["backend_common"; "bvl"; "bvlSem"; "bvl_const"];;

`hol4_ancestors` (`ml/lib/theorem.ml`) takes the overloads of every
other theory out of the interface, and the `unhide_overloads ()` at
the end of the file puts the interface back as it stood -- not with
the pairs in front, which would decide another name for the file
after it.  The theory of an overload is the file that registered
it, which announced its name (`the_overload_thy` in
`ml/lib/define.ml`), and not a guess from the name of the constant:
`backend_common` defines `bvl_to_bvi_namespaces`.  The list is the
`Ancestors` block of the source, and the library closes it over the
lists of those theories themselves (`tools/db.py`, `announce`), so
the 1085 names in the files stand for the 5518 of the closure.

What it does **not** settle is a name that more than one theory
*in* the scope defines: there the interface decides again, by the
order the files loaded in.  That order agrees with HOL4 in the
cases seen -- HOL4 takes the theory closest in the ancestry, which
loads last of them, and the interface tries the one registered last
first -- and `bvi_letProof`'s `delete_var` (`bvi_let`'s, with
`bvl_const`'s in scope as well) is right in the port for that
reason.

The other thing it leaves standing is the **library layer**: a pair
that a HOL4 library theory of `ml/lib` registers is in the scope of
every file (it says so itself, with `hol4_lib`), because a `needs`
of such a file stands inside a file that is a theory and the pair
would otherwise go down as that theory.  So `sptree`'s `lookup` and
`balanced_map`'s are still told apart by the order of the
interface, and what gives `data_to_word_memoryProof` the right one
is a `bring_to_front_overload` of `data_spaceProof`, 27 files
earlier in the load order.  Reading those by the ancestry as well
is the next step of this; it needs its own measurement, because
`tools/deps.py` has the ancestry of a library theory out of the
`Libs` line of the source and a name cut by mistake there breaks a
statement that nothing else can read.

Four faults of the cut itself cost a run each, and all four were
about which theory an overload is of:

- the library layer registered its pairs while a theory was
  loading (above), so `sptree`'s `lookup` came out of the
  interface of `data_to_word_memoryProof` and `balanced_map`'s won;
- the restore of the interface was undoing the file's own
  `bring_to_front_overload`, which HOL4 keeps for the files after
  it.  `ml/lib/define.ml` tracks what a file registers for that
  reason;
- the theory of a pair was the one of its **first** registration,
  so a pair that the library layer registers and that a file of
  the port registers again stayed one of the library layer, in the
  scope of every file.  `ml/lib/simpleSexp.ml` overloads `++` with
  `OPTION_CHOICE`, as its source does, and gives the name back to
  `APPEND` at the end of the file; `unify`, `cmlPtreeConversion`
  and `fromSexp` overload it with `OPTION_CHOICE` again, each in a
  theory of its own, and `closProps` can see none of the three --
  but the pair was the library layer's, so `OPTION_CHOICE` stood
  in front of `APPEND` while `closProps` loaded, the `c1 ++ c2` of
  `code_locs` read as an option, its thirteen clauses did not fit
  together and the run assumed them one by one (twelve axioms).
  The theories of a pair are kept together now, and a pair is in
  the scope of a file where **any** of them is; a pair that
  `override_interface` takes out of the interface altogether
  (`hol4_only`) is of no theory any more, as if the library layer
  had never had it;
- and the restore put the file's own registrations in front of the
  interface it saved, which leaves a **second** entry of a pair
  that was in the interface already.  `overload_interface` moves
  such a pair to the front instead, and a second entry is one that
  no `override_interface` of a later file can take out, so the
  restore drops the entry further back.

`tools/smoke.ml` has a test of each of the four, and of what a
scope is: `SMOKEANCESTORS`, `SMOKEANCLIB`, `SMOKEANCONLY`,
`SMOKEANCTWICE` and `SMOKEANCBACK` (the last is the shape of the
port's `++`: the library layer gives the name to HOL Light's
constant, a file overloads it and gives it back, and the file
after it has to see the one it was given back to).

One axiom of the port moved when the cut came in, and it moved the
right way: `compiler/parsing/fromSexp.ml` adds **137** axioms with
the cut where it added 136 without it (the run of 01:33, the last
one before every file said its theories).  Loading that file on its
own closure -- its eleven `needs` and nothing else -- adds 137 as
well, and the same 137 statements, whether `hol4_ancestors` cuts the
interface or is made a no-op: with only the file's own closure
loaded there is hardly anything to cut.  So 137 is what the file
says by itself, 136 was what the load order of 157 other files made
of it, and the cut is what makes a run agree with the closure that
a proof of the file is written against.  That is the whole point of
it (`bvlProps$evaluate_CONS` is the same disagreement the other way
round), so the extra axiom is the cut working, not a regression:
a definition of the file reads what its source says now, and needs
one assumption more than the reading the load order gave it.

`tools/scope.ml` reads every statement again with the interface cut
down, to see what the cut would break, and `tools/scope.py` reads
that against the same reading without the cut: of the 559
statements that the cut cannot read, **all 559** are statements
that the session cannot read either, not one statement gains a free
variable, and not one reads another constant than it does without
the cut.  So the cut breaks nothing.

That last number is zero because a re-reading is not what a run
does: the interface of a session that has the whole port loaded is
in another order than the one each file saw, so **113** statements
read another constant there than the theorem the run made of them
-- which is the drift this entry is about, and what the cut takes
away at the time that matters, when the file loads.

The same holds for the statements that such a session cannot read
at all: `tools/bin/diag` reads all 10424 of them again in the
session of a finished run and **125** do not go through, 123 of
them with a name that resolves to more than one constant (32 in
`lab_to_targetProof`, 25 in `stack_removeProof`, 13 in `misc`, ten
in `word_to_stackProof`, nine each in `word_instProof` and
`targetProps`, and the rest in six files more).  The second entry
of a pair that the restore left in the interface was the obvious
suspect, because such an entry is one that no later
`override_interface` takes out; it is not the cause.  The run with
the restore put right has the same 123, so what those statements
need is the interface of their own file and not of the whole port
-- a re-reading in a session that has everything loaded is simply
not what the file saw, and `tools/bin/scope` (which does read each
statement with its file's own scope) says **0** names of a theory
out of the scope of the source, in 0 theorems.

## The order in which the port is loaded

The files of the port are loaded in the order of
`tools/load.txt` (what `tools/bin/runall` does), and a file's
`needs` lines name what it needs, so loading one file loads its
own closure.  One thing depends on the order all the same: a
definition whose constant has the **name of its own theory**
keeps that name (`evaluate$evaluate` is `evaluate` in the port,
not `evaluate_evaluate`, and so are `semantics`, `term`, `walk`
and `asm`), and the other theories that define a constant of that
name overload it.  The definition is read before those overloads
exist, which the load order gives; read after them, the name of
the constant that it defines would be one of the overloads and the
definition would not typecheck.  So a file of the port has to be
loaded in the order of the port.

A run does that, and a `needs` chain does **not**: the recursion
takes the needs of a file in the order they stand in it, so a file
of the load order can land after one that stands behind it.  In
the closure of `data_to_word_memoryProof` built by `needs`,
`compiler/backend/semantics/closSem.ml` comes before
`semantics/evaluate.ml`, five theories have overloaded `evaluate`
by then, and `evaluate.ml` does not load at all -- it and
`dataProps.ml`, which needs it, are missing from the session, with
one line of its pane to say so.  A session that is to read the
port as a run reads it therefore loads the closure in the order of
`tools/load.txt`, which `tools/needsorder.py` writes and
`tools/bin/verifyfile` uses.

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
negation of a truth value and the negation of a number: only the
type tells the three apart, which a source level port cannot do
in general.

Where the argument is a word **literal** the port can: `~0w` is
the word of all ones and `~1w` the one with every bit but the
lowest set, so a `~` in front of a literal is `word_not`.  That
is what `tools/stmtshape.py` found, by counting the connectives
of a statement of a source and of the port's: the port read the
`~0w` of `word_inst$op_consts` (the identity of `And`) and the
`~1w` of `data_to_word_memoryProof$word_addr` (the mask that
clears the tag bit) as the negation of a number and wrote
`--(n2w 0)` and `--(n2w 1)`, which are `0w` and the word of all
ones.

Where the argument is a **variable** only the type says it, so
the definitions that have one are listed
(`overrides.WORD_NOT`), and `multiword$single_sub` (whose `~y`
is the complement in the two's complement subtraction) is ported
by hand with `word_1comp`, the name that the words layer gives
HOL Light's `word_not`.

## The record that a field of a statement is of

Every intermediate language of CakeML has a state with a `clock`,
a `code` and a `ffi`, and the sources have four kinds of
environment with a `v` and a `c`, so the port overloads the
accessors of a field with the name of the field and leaves it to
HOL Light to resolve them by the type, as HOL4 does.  Where
nothing in the statement says the type, that fails, and these are
the things that say it:

- an **annotation of the record** (`(s:('a,'c,'ffi)labSem$state)`),
  which the port now reads: it takes the annotations of a term
  before it prints it, so an annotated variable has the record of
  its annotation wherever the statement reads a field of it;
- the **record of a variable** of a theory (`overrides.FIELD_VAR`:
  the `t` of data_to_word_gcProof is a state of wordSem) or of one
  definition or statement (`FIELD_VAR_DEF`: the `s` of
  stack_to_labProof is a state of stackSem in most of its
  statements and one of labSem in two of them);
- the **record of a literal**, in the order of the literals of a
  statement (`THM_RECLITS`: the two literals of
  source_to_flatProof's `global_env_inv_extend` are an environment
  of source_to_flat and a sem_env, and both give a `v` and a `c`);
- the **accessor** itself, for one statement (`THM_ACCESSORS`),
  where the record is of a term and not of a variable (the third
  `v` of `nsAll_extend_env` is the one of the environment that
  `extend_env` gives).

A statement that uses the name of a field for a variable of its
own is read with the overloads of the field names taken away
(`cake_as_vars`, which 404 statements need).  That cannot work for
a statement that does both, so the fields of those statements are
written out: `lab_to_targetProof$asm_fetch_NOT_ffi_entry_pcs` has
a variable `ffi_names` and reads the `ffi_names` of its machine
configuration.

Two things are **not** taken away with them:

- the overload of the name that HOL4 gives the accessor itself.
  Where every record that has the field is called `state` in
  HOL4, the name of the accessor there is `state_clock`, and the
  port overloads that name and not `clock`: HOL4 has those
  constants, so a statement that reads the field through one of
  them keeps it where one that writes `clock` for a variable of
  its own has the names of the fields taken away
  (`stack_to_labProof$flatten_call_correct` reads the `ffi` of a
  state of stackSem and has a variable `regs`).
- the accessor in the **body of an overload**.  That body is read
  in the theory that declares the overload, so the record of a
  field in it is known and the accessor is written out: labSem's
  `read_reg` is `\r s. s.regs r`, which ten statements of two
  files read with the overloads taken away -- and the `regs` in
  it was then the variable of the statement and not the field of
  a labSem state.

  Where such an overload is **applied**, the port puts the
  arguments into the body (a beta reduction of the application),
  so that the field is read with the record of the argument that
  is there: HOL4 resolves the name of an `Overload` by the type
  of each occurrence, and the `read_reg` of
  `lab_to_targetProof$word_cmp_lemma` is the `regs` of a labSem
  state on one side of the equation and of an `asm_state` on the
  other.  It reads better as well
  (`labSem_state_regs s1 r` for `(\r s. labSem_state_regs s r) r
  s1`), and 45 files of the port have such an application.

## The constants that HOL4 hides from its parser

HOL4's `relationTheory` does `Parse.hide "C"`, so the `C` of
`combinTheory` is not a constant of the parser in any theory that
has `relation` as an ancestor -- which every CakeML source has --
and a statement that writes `C` means a variable of its own
(`word_allocProof$INJ_union` is about `INJ f (A UNION B) C`).  The
port has HOL Light's `C` (the combinator that swaps two
arguments), so those statements are read with it hidden:
`overrides.HOL4_HIDDEN` names it and `tools/db.py`'s `hidden_for`
puts it in the `cake_hide` of every file whose statements write
it.  A statement that does mean the combinator writes `combin$C`
for it, which the port reads as the `hol4_C` of the library layer
-- a constant that the `cake_hide` of `C` does not touch.

HOL4 cannot have a constant called `val` at all, because `val` is
a keyword of SML, while HOL Light's words library has one (the
number of a word), so `val` is hidden the same way.

A name that the port **overloads** is hidden as well where no
theory of the ancestry defines it: `linear_scanProof`'s `id` is
`linear_scanProof_id` and `id` is an overload of it, so
`source_to_flatProof$declare_env_store_env_id` read its own
variable `id` as that constant.

What the ancestry is, for all of this, is the Ancestors **and the
Libs** of the source: a `Libs` entry brings the grammar of the
theory of that name, and `misc` has `ASCIInumbersLib` in its
`Libs` and uses the `num_to_hex_string` of `ASCIInumbersTheory`,
which is in no `Ancestors` block of it.

A source hides a name of its own with `Parse.hide` as well, and
from the line where it says so: `data_to_word_memoryProof` hides
`el` and `sign` at its head and `free` in the middle of itself
(line 17834 of 18,800), because the statements after that line
use `free` for a variable and the port has the `free` of
`clos_call`.  The port says it where the source says it, with
`cake_hide_more`, which adds to the list of the file instead of
replacing it.  47 such lines are in the sources, of 14 names;
`mem` is 26 of them.

A name that the accessors of a **record field** have as well is
not hidden, because hiding it would take those with it: `failed`
is the field of a labSem state and of an `asm_state`, and
`pegexec` has a constructor `failed` of its `kont` that no theory
in the ancestry of `labProps`, `lab_filterProof`,
`lab_to_targetProof` or `gen_gc_partial` defines.  Hiding the
name made those four files read `failed s` as a variable applied
to a state, which typechecks and says something else than the
source does.  `cake_hide_consts` takes the one constant out of
the interface instead, so the accessors keep the name and HOL
Light resolves them by the type of the record, as HOL4 does.

Where HOL4 hides the name of a field that the port needs all the
same, the accessor is written out: `labProps` hides `mem` (its
statements use it for a variable), and HOL4's field syntax
`s.mem` reads the field after that, so `overrides.ACCESSORS` says
which record the `mem` of its statements is of.

## What is not ported

See the list in `PLAN.md`: the L3 instruction set models and the
CakeML theories that instantiate the compiler for one concrete
target, the basis library program with the proof producing
translator and characteristic formulae, and Pancake.

The seven theories of `tools/excluded.txt` are the encoder of
each of the six targets and the one machine model that the CakeML
sources do have.  An encoder needs the machine model of its
target, which is a theory of HOL4's `examples/l3-machine-code`
(`x64_step`, `arm8_step`, ...) and not part of the CakeML
sources; the model that the sources do have, `ag32` (the Silver
ISA), is a file that L3 generated, and it builds its types and
its definitions by calling the ML of HOL4's `Import` library,
which a source level port cannot follow.  Of each of those
theories `compiler$parse_target_64` and `parse_target_32` pass on
one constant, `<target>_config`, the asm configuration, whose
`encode` field is the encoder, so the port declares those six
(`PENDING.md`).

What a concrete target has besides its encoder is in the port:
the configuration of the backend and the register names
(`compiler/backend/<target>/<target>_configScript.sml`, which
needs nothing of the machine model) and the theory that exports
its code (which needs only `export`).

Of the HOL4 library theories (in `ml/lib/`) only the definitions
that the port needs are ported, not the whole theories.

The three definitions of `compiler` that compile Pancake
(`compile_pancake`, `compile_pancake_64` and
`compile_pancake_32`) are in the port all the same, because they
are definitions of a ported source: the port declares the three
entry points that they go through
(`panPtreeConversion$parse_topdecs_to_ast`,
`panStatic$static_check` and `pan_passes$pan_compile_tap`) and
has what their type is made of -- `panLang`, the abstract syntax
of Pancake, whose ancestors the port has anyway, the datatype of
the static errors and the `error` of `errorMonad`.
`compiler$compile`, which the correctness theorem is about, does
not use them.

The two command line drivers of the compiler binary
(`full_compile_64` and `full_compile_32`, which call those three
when the flag says so) are the only two definition blocks of a
ported source that the port does not have, and for another
reason: they read the input of the binary and write its output,
so their type is the file system of the basis library
(`fsFFI$IO_fs`), and the three constants that they use
(`add_stdout`, `add_stderr`, `fastForwardFD`) are of `fsFFIProps`
and of `TextIOProof`, whose ancestors are the characteristic
formulae and the proof producing translator.  That is the part of
CakeML that the scope of the port leaves out, and
`compilerProof$compile_correct` does not mention these two.

## data_to_word stopped loading at its Unit (fixed)

_Fixed on 2026-10-22 by the three `CON_OF` entries that
`tools/overrides.py` now has for `unit_def` of `data_to_word` and
for `op_consts_def` and `pull_exp_def` of `word_inst`; the file
loads to its last definition.  What it was:_

`ml/compiler/backend/data_to_word.ml` did not load past line
1327 (`assign_SetGlobalsPtr_def`), and the ninety definitions of
the file below that line (`write_bytes`, `small_int`,
`make_cons_ptr`, `byte_len`, the `assign_*` family, ...) were
therefore not there.  The error was `typechecking error (overload
resolution)`, and the reason was the definition above it:

```
let Unit_def = cake_define
  `data_to_word_Unit = Const (n2w 2)`;;
```

HOL4's `Unit = Const 2w` is a `wordLang$exp`, because its
Ancestors open `wordLang` and `word_bignum`, and HOL4's overload
resolution prefers `wordLang$Const` of the two.  The port read
it as `word_bignum$Const`, so `data_to_word$Unit` had the type
`('a word) term` instead of `'a wordLang_exp`, and the first
definition that uses it as an expression
(`Assign (adjust_var dest) Unit` of `assign_SetGlobalsPtr`) has
no resolution at all: in the port `Assign` is
`word_bignum$Assign` as well (`num -> 'a wordLang_exp -> 'a
mini`), and the argument it is given is not an expression.

What it cost the proofs: of the 611 theorems of
`data_to_word_memoryProof` 60 stated something about a definition
that was missing, and those statements had a free variable where
HOL4 has the constant (21 of them `small_int`, 10
`write_bytes`).  The definition of `v_inv_ck` of that file was in
the same position -- its first rule says `small_int (:'a) i`,
which the port read as a free variable and the inductive
definition then quantified -- so a proof that unfolds `v_inv_ck`
was about a relation that said less than HOL4's.

What it taught: a session built out of a `needs` closure can be
missing a whole file, and nothing but one line of its pane says
so.  A _run_ had no trouble with `data_to_word.ml` at all (its
report of 2026-10-19 gives the file 72 s and no error, and
`tools/stmtfree.py` found no statement with a free variable where
HOL4 has a constant), because the load order gives `Const` the
resolution that HOL4 gives it.  So the overrides are what makes
the file read the same way in both, and a test bed is built in
the order of the load order (`tools/needsorder.py`, "The order in
which the port is loaded").

## A statement whose two variables became one name

`all_ts_permute` of `data_to_word_memoryProof` says in HOL4

```
∀(refs : v ref num_map) stack stack'.
  PERM stack stack' ⇒ all_ts refs stack = all_ts refs stack'
```

and in the port

```
`!(refs:(dataSem_v bvlSem_ref) spt) stack' stack'.
   PERM stack' stack' ==> all_ts refs stack' = all_ts refs
     stack'`
```

because `stack` is a constant of the port (see "The constants
that HOL4 hides from its parser") and the renaming that the port
does for it, `stack` to `stack'`, gave HOL4's `stack` the name
that HOL4's `stack'` already had.  The second binder shadows the
first, so what the port states is `!refs s1 s2. PERM s2 s2 ==>
all_ts refs s2 = all_ts refs s2`: a tautology, and weaker than
the source.

Where it bites: nothing of the port uses `all_ts_permute` (HOL4
does not either -- it is stated and never used), so no proof
rests on the weaker statement.  Its proof of phase three is
`REWRITE_TAC[]`, with a comment that says why.

What to do about it: the statement has to be restated, with the
two variables apart (`stack'` and `stack''`), and then proved
with `PERM_IND` and `all_ts_head` the way HOL4 does.  That is a
change of a statement, which phase three does not do, so it is
recorded here and waits for a pass that may restate.

How many more there are: `tools/dupbind.py` reads the quoted
terms of `ml/` and reports every `!` or `?` chain that binds one
name twice.  It finds **25**, and they are of two kinds, so each
one has to be read next to its source:

- the source binds one name twice as well, and the port is
  faithful.  `memory_rel_do_build` of this very file is one
  (`data_to_word_memoryProofScript.sml:17837` binds `v` twice),
  and HOL4 reads the second binder the same way, so the port
  says what the source says.
- the renaming collapsed two names into one, as here.  Two more
  that it did: `wordPropsScript.sml:4004` (`!n stack stack' x`)
  and `word_to_stackProofScript.sml:2108` (`!stack stack'`),
  both of them `stack`/`stack'`.

## The precedence of a word's bitwise operators

HOL4 declares the bitwise operators of a word with
`add_infixes 490 RIGHT [("&&", word_and)]`, `485` for `??` and
`482` for `||` (`hol4-src/src/n-bit/wordsScript.sml:168-180`),
and HOL4's `+` is `500`.  A **higher** number binds **tighter**
there, so a bitwise operator binds looser than an addition and

```
-2w && 16w * tag + 2w     is     -2w && (16w * tag + 2w)
```

The port declares them in `ml/lib/words4.ml:106-112` as `&&` at
`20`, `||` at `16` and `??` at `16`, and HOL Light's `+` is `16`,
where a higher number binds tighter.  So in the port `&&` binds
**tighter** than `+`:

```
-2w && 16w * tag + 2w     is     (-2w && 16w * tag) + 2w
```

and `||` and `??`, which sit at `+`'s own level and are right
associative, group HOL4's way only when the bitwise operator comes
first (`a || b + c` is `a || (b + c)` in both, but `a + b || c` is
`a + (b || c)` in the port and `(a + b) || c` in HOL4).

Where it bites: `tools/wordprec.py` reads the quoted terms of
`ml/` and reports the operand chains where a bitwise operator
meets a `+` or a `-` with no parenthesis between them.  It finds
**one**: `BlockNil_and_lemma` of
`data_to_word_memoryProof`, where HOL4 says
`-2w && (16w * tag + 2w) = 16w * tag + 2w` and the port says
`(-2w && 16w * tag) + 2w = 16w * tag + 2w`.  Both are true (the
two lowest bits of `16w * tag` are clear either way), and the
proof of phase three proves what the port states, with a comment
that says so.

What that costs further on: `memory_rel_Cons_empty` is the theorem
HOL4 proves *with* `BlockNil_and_lemma`, and what it needs is
HOL4's reading of it -- the and of the complement with the **sum**,
which is what the root of an empty Block is.  The port's statement
of the lemma does not give that, so the proof of
`memory_rel_Cons_empty` proves the fact again, in four lines of its
own.  Every later use of a statement that this entry lists pays the
same way.

What to do about it: the fixities of `ml/lib/words4.ml` have to be
the ones that give HOL4's grouping (`&&` below `+`, and `||` and
`??` below that), which is a change of the library layer and of
what every statement with those operators means -- a pass of its
own, with a run and a re-verification, and not a thing for phase
three.  Until then `tools/wordprec.py` is what says which
statements it would change: today one, and it is to be run again
whenever a file with word arithmetic is ported.

## The empty list that HOL4's TL has a value for

HOL4's `TL` is **total**: `listTheory.TL_DEF` is

```
TL [] = [] /\ TL (h::t) = t
```

HOL Light's `TL` (`lists.ml:31`) has the second clause only, so
`TL []` is whatever the recursion theorem's witness makes it and
nothing can be proved of it.  `ml/lib/hol4.ml:13` lists `TL` among
the constants HOL Light has "with the same meaning as in HOL4",
which is right for every non empty list and wrong for the empty
one.

Where it bites: a statement that takes the tail of a list the
statement does not say is non empty.  `grep -w TL ml/` finds one,
`memory_rel_elements_list_distinct` of
`data_to_word_memoryProof` (HOL4
`data_to_word_memoryProofScript.sml:13673`):

```
memory_rel c be ts refs sp st m dm vars' /\ elements_list vs /\
vs = MAP FST vars' /\ good_dimindex (:'a)
==> ALL_DISTINCT (MAP SND (TL vars'))
```

With `vars' = []` every antecedent holds (`elements_list [] = T`,
and the memory relation of the empty list is the one of an empty
stack), and the conclusion is `ALL_DISTINCT (MAP SND (TL []))`,
which in HOL Light was a statement about an unspecified list, so
the theorem was **not provable as it stood**.  Its neighbour
`memory_rel_elements_list_words` says `~(vars' = [])` and was not
affected.

**Fixed.**  `ml/lib/hol4.ml` has HOL4's tail as `hol4_TL` (both
clauses), and the last line of `ml/lib/preamble.ml` gives the name
`TL` to it, so every statement of a source means HOL4's.  The
override is in the preamble and not in `hol4.ml` because the files
of the library below it are HOL Light's own and their proofs take
HOL Light's `TL` apart (one of `ml/lib/string4.ml` does, and broke
when the override stood higher up); `EL` keeps HOL Light's `TL` in
its definition, which is what the rewrite sets of the proofs
reduce.

## `memory_rel_El'` and `memory_rel_El_any` say the same thing

The two statements of `data_to_word_memoryProof` differ only in an
existential that neither of them uses (`i_w` in the first, `y` in
the second): both say that the root of a Block is a `Word`, that
`get_real_addr` of it is an address, and that the memory relation
survives putting the `index`th element of the Block beside it.
The source proves the second one again, through `memory_rel_El`
with a `Number` put into the list so that `get_real_offset`
applies; the port's proof of it is the first one, which stands
earlier in the file.  That is a deviation from the source's proof
(not from its statement), and it is recorded in the section's
comment as well.

## `IS_PREFIX` was a free variable, so four statements said nothing

HOL4's `rich_listTheory` has two relations that CakeML's garbage
collector states its lemmas with: `IS_SUFFIX l1 l2` (l2 is a suffix
of l1) and `IS_PREFIX l1 l2` (l2 is a prefix of l1).  The port had
the first (`ml/lib/hol4.ml`) and not the second, and `isPREFIX` of
`listTheory`, which the port does have, is the same relation with
its arguments the other way round -- so it is no overload of it.

What that cost: `IS_PREFIX` in a statement of the port was read as
a **free variable** applied to two lists, so the statement said
nothing about the prefix and, being universally quantified over
that variable when the theorem is proved, was not provable as it
stood.  Four statements are concerned, all of them still assumed:
`gc_move_IMP` and `gc_move_list_IMP` of `gen_gc` (what a move of
the collector leaves of the state: `h2` grows at the end and `r4`
at the front), `lookup_fromList2_prefix` of `word_to_stackProof`,
`nsLookupMod_FOLDR_nsLift_none` of `namespaceProps` and
`constrain_op_error_msg_sanity` of `infer` (where it stands in a
definition as well).

**Fixed.**  `ml/lib/hol4.ml` defines `IS_PREFIX` beside
`IS_SUFFIX`, in the form that HOL4's `IS_PREFIX_APPEND` gives it:

```ocaml
let IS_PREFIX = new_definition
  `IS_PREFIX l1 (l2:A list) <=> ?l. l1 = APPEND l2 l`;;
```

The rule it illustrates: a name that HOL4 resolves to a constant of
a library theory and the port does not have is read as a variable
and nothing says so, which `tools/stmtfree.py` is the check for.

## Five names that a lemma of the port's own takes from a theorem

When `tools/stmts.py` gave `tools/attrs.py` and
`tools/stmtshape.py` their statements back (they had looked for
`cake_theorem`, so they had reported `0 statements of the port`
since phase two ended), the two checks found seven statements to
read, and all seven are the same thing: a file of the port binds
one name to two theorems, because an override table adds a lemma
of its own before the proof that needs it and gives it the name
that the source has for a theorem of its own.  OCaml takes the
later binding from there on, so the proofs on either side of the
second one use what they mean to use and the port loads -- but the
name says two things in one file, and the checks cannot pair a
statement with its source.

The five, with the line of each in its file of the port and which
of the two the generator wrote (the one with the attributes of the
source over it):

| name | the port's own | the source's | what was done |
|---|---|---|---|
| `ref_edge_ValueArray` | 18311 | 10438 `[local]` | the same statement, and the source's stands first: the copy is gone |
| `ref_edge_Thunk` | 19245 | 10447 `[local]` | the same: the copy is gone (a note in its place says where the two stand) |
| `dest_thunk_insert_MutBlock` | 16028 | 30568 `[local]` | the copy is the general form (the fourth component of the block may change) and stands first, so it is `dest_thunk_insert_MutBlock_any` now |
| `data_up_to_alt` | 6399 | 12569 `[local]` | another statement altogether (what is below the unused space after a store, against the source's two clauses of `data_up_to`), so it is `data_up_to_written` now |
| `exp_size_get_bin_args` | `bvi_tailrec` 235 | `bvi_tailrec` 181 | the copy is the source's statement proved, where the source's own place still has the `CHEAT_TAC` of phase two: it is `exp_size_get_bin_args_term` now, and the proof of the source's own belongs in the store |

All five are in `tools/overrides.py`, so a re-port carries them;
`tools/attrs.py` says 0 since 2026-11-05.

Two of the seven were a fault of the check instead, and are
gone: the scan for the comment that says the name and the
attributes ran back to the blank line over the binding, and where
a pointer at the source stands between two theorems with no blank
line after the `;;`, the second one took the note of the first
(`dataProps$do_stack_const` and `pegComplete$MAP_EQ_CONS`), so the
check saw one name with two statements.

The rule it illustrates: a lemma that the port adds of its own
needs a name that no theorem of the file has, or the file says two
things with one name.  `tools/attrs.py` is the check -- it counts
the statements of a name against the bindings the source has of
it -- and it reports the lemmas of the port's own apart (296 of
them) so that the ones with a name of the source stand out.
