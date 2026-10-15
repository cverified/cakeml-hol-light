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

- Record fields: `r.fld` becomes `ty_fld r`, `r with fld := v`
  becomes `ty_fld_fupd (K v) r` and `<|fld := v|>` becomes
  `mk_ty v ...`, because HOL Light has no record syntax.  A
  literal that does not give every field (`bviSem`'s `bvi_to_bvl`)
  gets `ARB` for the fields it leaves out, where HOL4 updates an
  arbitrary record of the type; both leave those fields
  unspecified, but the two terms are not the same.
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
  first-match semantics, and HOL4's returned theorem is for the
  split clauses, not for the clauses as written.  In the port
  such clauses are made disjoint by hand; each place says so in
  a comment.  So far: `location$merge_list_locs`.
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
- **The first pass assumes the definitions that none of that
  makes.**  `cake_define` gives every way of making a definition
  a budget of `cake_timeout` seconds (twenty), and states the
  clauses as an axiom when they all fail; `ml/CHEATS.md` lists
  them and `length (axioms ())` counts them (three plus one for
  every assumed definition, or one for every clause of it where
  the clauses had to be assumed one by one).  The second pass has
  to replace each of them by a real definition; until then the
  port is not conservative over HOL Light.

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
  inductive definition that HOL4 has.

HOL4's `pathTheory` is not ported: the dependency analysis found
it only because CakeML definitions use variables called `el`,
`first`, `exists` and `length`.

## Definitions whose form deviates

Every definition of the ported files is in the port.  Three of
them state the expression that HOL4's ML code evaluates instead of
the value that it finds, and one (`misc$Lnext`) is proved to exist
by hand; `PENDING.md` lists all four, with the reason.

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
