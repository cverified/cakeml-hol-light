# Theorems whose statement the port does not have

Phase two states every theorem of the sources with its name, its
attributes and its statement (`CLAUDE.md`).  Of the 10,688
theorems of the 270 sources the port states 9,973 and points at
715 with a comment that names them
(`CAKE_KINDS=1 python3 -I tools/coverage.py`):

| | stated | a pointer |
|---|---|---|
| `Theorem` (and `Triviality`) | 9,900 | 234 |
| `ThmValue` (the value of an ML expression) | 38 | 441 |
| a theorem that ML code states (`Q.prove`) | 35 | 40 |

The `Theorem` row grew as the harvest got more honest, not as the
port got worse: 188 of its 234 are statements that HOL Light's
parser rejects, and a run finds one only when the file it is in
loads far enough to reach it.  `tools/unstated.py` is that list,
and every entry of it is a statement to win back -- 104 of them
are in `data_to_word_assignProof` alone, so one cause may account
for most of them.

What the 715 are, and why the port cannot state them:

- **441 theorems that HOL4 states as the value of an ML
  expression** (`Theorem foo[simp] = CONV_RULE (RAND_CONV EVAL)
  foo_def`, `Theorem bar = SIMP_RULE bool_ss [] baz`, `Theorem
  baz = theorem"baz_ind"`).  The statement is not in the source:
  HOL4 computes it from another theorem, so writing it down means
  doing the computation.  The port could do most of them in phase
  three, where it has the theorem that the expression starts from
  and HOL Light's own rules to apply, but none of it is a
  statement that phase two can read off the source.

  Phase three does one as soon as the theorem it starts from is
  proved, and then the computation is **done** rather than
  guessed: `overrides.THM_VALUE` holds the statement in HOL4's
  notation, `tools/port.py` translates it like any other statement
  of the source, and the proof is a section of the file's proof
  store.  Four of the 479 are in that way:

  | theorem | the ML expression, and what it computes |
  |---|---|
  | `bvi_let$compile_exp_eq` | `compile_exp_def \|> SRULE [compile_sing]`: the compiled list of one is a singleton, so the `match` of `compile_exp` reduces to its head, and the theorem is `compile_exp x = compile_sing [] 0 x` |
  | `bvi_letProof$compile_thm` | `evaluate_env_rel \|> Q.SPECL [...] \|> GEN_ALL \|> SIMP_RULE (srw_ss()) [env_rel_def]` at `ax = []` and `d = 0`, where `env_rel [] 0 env env` is `env = DROP 0 env` and so `T`: what is left of the antecedent is the evaluation and the type error |
  | `bvl_const$compile_exp_eq` | the same expression one language up, where `compile_exp` carries no depth: `compile_exp x = compile_sing [] x` |
  | `bvl_constProof$compile_thm` | `evaluate_env_rel` at `ax = []`, where `env_rel [] env env` is `env = env`: what is left is the evaluation and the type error |
- **40 theorems that ML code states as the value of a rule
  applied to another one** (`val foo = Q.prove(...) |> SIMP_RULE
  ...`, `save_thm("foo", th)`): the same case, with the statement
  of the theorem that the rule starts from in the source.
- **three theorems whose statement is an ML expression**:
  `word_to_stackProof$comp_correct`,
  `clos_to_bvlProof$not_isClos` and
  `bvi_to_dataProof$compile_exp_correct` are stated as
  `^(ind_thm |> concl |> rand)` and the like -- the conclusion of
  an induction theorem that HOL4's machinery built.  The same
  case as the one above, with the expression in the statement
  instead of in the place of it.

Where the value is a `prove` of a quotation and nothing but
`SPEC_ALL`, `GEN_ALL` or `check_thm` is applied to it, the
quotation is the statement and the port states it: thirty-four of
the theorems above are these, and the theorem that HOL4 binds is
the one of the quotation with its variables free or closed, which
says the same.

Everything else of the sources is in: `tools/coverage.py` counts
the blocks and the theorems of every source against its port, and
what it reports missing is the two blocks below, the 481 that
this section is about, and the 234 `Theorem` statements that HOL
Light's parser rejects.

**Forty-two statements use an auxiliary size function of a
datatype family** (`exp1_size`, `exp3_size`, `v1_size`, ...).  HOL4's
`Datatype` makes one of these for every type that the family
needs besides the type itself (`exp1_size` of closLang is the
size of a `(num # exp) list`), and HOL Light numbers the types of
a family in another order, so a name of HOL4's says nothing about
which function of the port it is.  The port writes a pointer that
names the theorem: a statement with a free variable where the
source has a constant would say something else than the source
does, which is worse than saying nothing.

A statement of this kind is stated as soon as a proof of phase
three needs it, because then the identification is **checked**
rather than guessed: `bvi_let$exp2_size_APPEND` and
`bvi_letProof$exp_size_APPEND` (the same statement, which the two
sources both state) say it of `exp2_size`, the size of a
`bvi$exp list`, and the size prelude of the port calls that one
`bvi_exp_size1` -- which `size_thms "bvi_exp"` states as
`bvi_exp_size1 l = list_size bvi_exp_size l`, a list of
`bvi_exp`, so the identification is the theorem itself.
`overrides.THM_NAMES` is where the port says that a statement
means it.  Two of the forty-four were these.

No statement uses a constant of a HOL4 library that the port does
not have any more; `tools/libnames.py` is the check.  There were
six, and each has its name in the library layer now:

| theorem | what it needed |
|---|---|
| `misc$domain_rrestrict_subset`, `misc$range_rrestrict_subset`, `misc$GSPEC_o` | the `domain` and the `range` of `set_relationTheory` and HOL4's `GSPEC`, which `ml/lib/hol4.ml` has under a name of its own (`overrides.THM_NAMES` says which statements mean them) |
| `misc$toPath_fromList`, `misc$steps_rel_okpath` | `pathTheory`: the type of a path (a state and a lazy list of transitions), with `toPath`, `stopped_at`, `pcons` and `okpath`, which `ml/lib/path.ml` has (HOL Light has no greatest fixed point, so the one that `okpath` is of HOL4's `okpath_f` is written out) |
| `presLang$num_to_hex_eq` | `words$word_to_hex_string`, which is `w2s 16 HEX` and needs the `n2s` of ASCIInumbers: HOL4 has both in its words theory and the port has them at the end of `ml/lib/ASCIInumbers.ml`, because the hand written words layer of the port is loaded before that theory |

The theorems of the **HOL4 library theories** of `ml/lib` are not
in the port either, and are not counted: of a library theory the
port has the definitions that CakeML needs (which is what the
preface of such a file says), and the theorems of it that a proof
of phase three needs are proved when that proof needs them.  The
10,688 are the theorems of the CakeML sources.

# What the port has of the ML code of a source

A source is not only its blocks: 2,435 blocks of the 270 are the
ML code of HOL4 between them, and this is what the port has of
each.

- **the ML of a library theory** (611): of a
  library theory the port has the definitions that CakeML needs,
  and nothing else is in.
- **the bookkeeping of HOL4** (183): a parse option, a
  `temp_delsimps`, an `export_theory`, an `add_record_field`.
  There is nothing in it for the port to have (`IGNORE_ML` in
  `tools/port.py` is the list).
- **the ML that states a theorem** (75): a `val foo =
  Q.prove(...)` of a source is a theorem named `foo`.  Phase two
  states 35 of them, where the quotation is what the theorem
  says, and points at the other 40, where a rule of HOL4 makes
  something else of it (`|> SIMP_RULE ...`).
- **the ML that the port has in OCaml** (63): the code that
  builds the deep embedding of `word_bignum`, the monadic
  machinery of `reg_alloc` and `linear_scan`, the grammar of
  `gram` and of `simpleSexpPEG`, and the terms that
  `flat_to_clos` builds with `check1`.  `ML_PORTED` and
  `EXTRA_BEFORE` in `tools/overrides.py` say where the OCaml
  goes, and it takes the place of the blocks that it covers.
- **everything else** (1,544): a pointer at the lines of the
  source says what is there (a proof, the ML values that the
  definitions below antiquote, or ML code that is not ported).
  `tools/nohol4.py` checks that every pointer points at what it
  says.

# Statements that the port cannot read yet

**None.**  Of the 10,122 statements of the port the run of 15:18
read every one (the run of 20:17 could not read a hundred, the one
of 22:57 twenty-six, the one of 01:40 four; `PLAN.md` says what
the rounds were about).  The last one to go was
`lab_to_targetProof$word_cmp_lemma`, whose `read_reg` is the
`regs` of a labSem state on one side of the equation and of an
`asm_state` on the other: HOL4 resolves the name of an `Overload`
by the type of each occurrence, and the port now expands the body
of one (`\r s. s.regs r`) per occurrence, with the record of the
argument that is there, which is a beta reduction of the
application (`tools/port.py`'s `beta_overloads`).

That a statement reads is not that it says what the source says,
so three more checks run over them after every run: `tools/diag.py`
says which statement applies a name that the port made a variable,
`tools/stmtfree.py` which free variable of one is a name that a
theory of the scope of its source defines (HOL4 reads a constant
there), and `tools/bin/types` which constant of one has a type
outside the scope of its theory.  All three are at zero.

# Definitions that the port assumes with a free variable

**None.**  Fifteen of the definitions of `ml/CHEATS.md` were once
assumed with a **free variable** in them (`free: ...`), which is
the kind of cheat that a decision or a missing piece has to settle
and not a proof.  Two things settled them: the clauses of a mutual
recursion that HOL4 writes as one `Definition` go to HOL Light as
one definition as well (closProps' `set_globals` and
`elist_globals`, semanticPrimitivesProps' `sv_rel`, `result_rel`
and `exc_rel`), and the argument of a `with ... updated_by f` is
the **field** and not the record, so the variable that such an `f`
binds has the type of the field (`backend_passes`' `to_bvi_all`
and the two like it).  `tools/bin/freevars` is the check, and the
run of 15:18 reports no definition with a free variable.

# Definitions whose form deviates from HOL4's

The first pass ports every `Datatype`, `Type`, `Overload`,
`Definition` and `Inductive` of the 270 files of the port: 4482
blocks, of which all but two are in (`tools/coverage.py`, and
`tools/overloads.py` for the `Overload` and the `Type` blocks);
the
ones that HOL4 makes in a way that the port has no counterpart
for are declared constants (`cake_declare`), which the list below
has.  A declared constant is no axiom: it gets an **implicit
definition** (`new_specification` of `?x. T`), which says nothing
about its value, because the value is one that HOL4 computes with
the ML code of a source and the port cannot say it yet.  So every
constant of the port is introduced by a definition, and the
sixteen whose value is not said are counted in `ml/CHEATS.md`
and named here: the four step functions of the unification
algorithm, the three entry points of Pancake, the basis program,
the six encoders of the targets and the two `valid_immediate` of
`arm8` and `arm7`.
`tools/fidelity.py` checks that no definition lost a name or a
constructor argument on the way, and `tools/literals.py` that
its strings, its characters and its numerals are the same ones
(`tools/bin/checks` runs both).

Three of them are definitions whose value HOL4 computes with ML
code (`EVAL` or `type_of`) and states as the value it finds.  The
port states the expression that HOL4 evaluates, which is provably
the same value; `REPLACE` in `tools/overrides.py` has the text.
(To compute the value in HOL Light instead, the call by value
machinery of `compute.ml` of the HOL Light distribution, which is
a translation of HOL4's `computeLib`, and the fuller version at
https://github.com/hol-light-family/compute-hol-light are what to
use; nothing of the first pass evaluates anything.)

| definition | what the port says |
|---|---|
| `infer$start_type_id` | `ITLIST MAX (Tlist_num :: Tbool_num :: prim_type_nums) 0 + 1` |
| `infer$err_var` (a `Type`) | `tenv_abbrev`, the type of the `t` field of a `type_env` |
| `mlint$exp_tm` (the value that `num_to_chars` divides by) | `10 EXP exp_for_dec_enc` |
| `data_to_word$AnyArith_call_tree` | `full_call_graph AnyArith_location (fromAList (stubs (:1) ...))`, the call graph of the bignum stubs for a configuration with `call_empty_ffi` and `has_longdiv` false |
| `data_to_wordProof$stubs_fst` | `MAP FST (data_to_word_stubs (:1) ARB)`, the names of the bignum stubs (HOL4's `EVAL` computes the list, in which the type of the stubs and the configuration are free) |

One definition of `compiler` and the five `<target>_export` have
a body that HOL4 builds with ML code of the source file, which
the port writes out instead:

| definition | what HOL4 does |
|---|---|
| `compiler$help_string` | the text of the `--help` quotation at the head of the source without its first line.  The port makes the term of the text with `mk_string`, because the text has a backquote in it |
| `export_x64$x64_export` and the four other `<target>_export` of a target with an FFI block | the FFI block of the assembly, the Windows one and the entry point code are ML values of the source, each the `EVAL` of a term that the ML code before it builds; the port writes the term that HOL4 evaluates (`tools/hol4.py` reads both terms of the binding that gives the value for the two values of the flag) |

One definition cannot be ported as it stands, because its value
is the one of the machine that built the theory:

| definition | what HOL4 does |
|---|---|
| `compiler$current_build_info_str` | `EVAL` of a string that holds the git commit of CakeML, the one of HOL4, the version of PolyML and the time of the build.  The port states the expression that HOL4 evaluates, with the three versions absent (`NONE`) and the date the empty string |

In HOL4's `AnyArith_call_tree` the type of the stubs and the other
fields of the configuration are free, and `EVAL` computes a value
that has neither in it, so the value does not depend on them; the
port instantiates the type with `:1` and the configuration with
`ARB`, which is therefore the same call graph.

The three definitions of `compiler` that compile Pancake are
stated with three declared constants.  Pancake is a second
source language of the same backend, which the correctness
theorem does not mention, so its parser, its static checker and
its own backend are outside the port, and the port declares
`panPtreeConversion$parse_topdecs_to_ast`,
`panStatic$static_check` and `pan_passes$pan_compile_tap` with
the type that the five definitions use them at.  What their type
is made of is in the port: `panLang`, the abstract syntax of
Pancake, whose ancestors (`mlstring`, `asm`, `backend_common`)
the port has, the datatype of the static errors
(`panStatic$staterr`, which `compiler`'s `compile_error` has in
it) and the `error` of `errorMonad`, the result type of the
static check, which the library layer takes over.

One constant has no value in the port, because HOL4 makes it in
a way that HOL Light has no counterpart for.  The port declares
it (`cake_declare`, which adds no axiom) and says nothing about
its value:

| constant | what HOL4 does |
|---|---|
| `basisProg$basis` | the declarations of the standard basis library, which the proof producing translator of HOL4 (`ml_progLib`) builds; the basis library is outside the port (see `ISSUES.md`), and `compiler$compile_64` and `compile_32` only pass the constant on |

The deep embedding of the bignum routines
(`word_bignum$mc_iop_code` and the ten others) is built by the
port, as HOL4 builds it: `to_deep` of `word_bignumScript.sml`
runs the shallow definitions of `mc_multiword` through a
translator written in the ML of that source, which the port has
in OCaml (`tools/word_bignum_todeep.ml`, which `ML_PORTED` of
`tools/overrides.py` writes where the source has its ML).  The
shallow definitions themselves are made the way HOL4 makes them
as well: each is the `SHORT_TAILREC` of a step function
(`ml/lib/mc_tailrec.ml`, the counterpart of HOL4's
`mc_tailrecLib`), and the equation that unfolds it, which HOL4
proves there, is assumed -- 132 of the assumed theorems of the
port are these.

Eight constants are declared for another reason: the one field of
the asm configuration of a target that is not data is its
encoder, and an encoder needs a machine model of HOL4 (`x64_step`
and the five others), which is not part of the CakeML sources, so
the six encoder theories are outside the port
(`tools/excluded.txt`).  The configuration itself is data, so the
port has it by hand, in the form the source gives it: for each of
`x64`, `arm8`, `mips`, `riscv` (64 bits) and `arm7`, `ag32` (32
bits) `<target>_config` is a definition of the port, with its
sixteen fields as the source has them and `<target>_enc` declared
-- and, for `arm8` and `arm7`, `<target>_valid_immediate` as
well, because the one of `arm8` is data but for the
`EncodeBitMask` of the model and the one of `arm7` is
`IS_SOME o EncodeARMImmediate`.  Where the source antiquotes a
word that its ML computes (`^min32`), the port writes the
expression that the ML evaluates (`sw2sw (INT_MINw:word32)`), as
it does everywhere else; `EXTRA_BEFORE` in `tools/overrides.py`
has the text.

The configuration of the backend for a target is data, and is a
definition of the port, in the file that HOL4 has it in: the six
`compiler/backend/<target>/<target>_configScript.sml` are ported
(`<target>_names`, the register names, and
`<target>_backend_config`, the configuration of the eight passes),
and they need nothing of the machine model.  HOL4 writes the
configurations of `clos_to_bvl`, `bvl_to_bvi`, `data_to_word`,
`word_to_word`, `word_to_stack`, `stack_to_lab` and
`lab_to_target` into it with the ML code of the file, and the port
states the expression that this ML code evaluates, as it does
everywhere else (`tools/hol4.py` reads the quotation of a binding
whose ML reads it, `rconc (EVAL ...)` as well as `eval ...`).
The theory that exports the code of a target needs only `export`,
which the port has, so `<target>_export` is a definition of the
port as well.

Four constants of the triangular unification algorithm are
defined by the graph of their equation, because HOL4 defines
them with a schema (`xDefineSchema`, for `vwalk` and `walkstar`)
or with `new_specification` out of a theorem about a tail
recursive version (`unify`): the equation holds under the
hypothesis that the substitution is wellfounded (`wfs s`), and
the recursion terminates only then.  The port states the graph
of the equation as an inductive relation and takes a value of
it (`vwalk s v = @r. VWALKR s v r`), which adds no axiom; HOL4's
equation is a theorem of the second pass.  (`unifDef$oc` is a
`Hol_reln` in HOL4 already, and is ported as it stands.)

Four more constants are declared, for the same reason: the step
functions of the tail recursive versions of the unification
algorithm, which HOL4 builds with the ML code of the source
(`tcallify_th` of `tcallUnifLib` turns the equation of a function
into the step function of a `TAILREC`).  The port cannot run that
code, so it declares `cvwalk_code`, `kcocwl_code`,
`kcwalkstarwl_code` and `cunify_code` with the type that the
`TAILREC` uses them at, and the seven definitions that use them
(`tcvwalk`, `tcwalk`, `tcocwl`, `tcwalkstarwl`, `tcwalkstar_p1`,
`tcwalkstar_p2` and `tcunify`) are ported as they stand.

Two definitions of `compiler` are not ported: `full_compile_64`
and `full_compile_32`, the command line drivers of the compiler
binary.  They read the input of the binary and write its output,
so their type is the file system of the basis library
(`fsFFI$IO_fs`), which needs the characteristic formulae of
`cfHeapsBase`, and the port has neither (`add_stdout`,
`add_stderr` and `fastForwardFD` are the three constants that
they use).  `compiler$compile`, which the correctness theorem is
about, does not use them.

One definition of the first pass is not ported, because HOL4
makes it from a theorem that the second pass has to prove first
(`new_specification` of a Skolem form):

| definition | what HOL4 does |
|---|---|
| `pegComplete$fFail` (`fFAIL1`, `fFAIL2`) | the Skolem functions of `peg_respects_firstSets`, which say where the parser fails on a token outside the first set.  Only the proofs of `pegComplete` use them |

One definition is proved to exist by hand, because HOL Light
cannot find the termination argument that HOL4 gives:

| definition | how |
|---|---|
| `misc$Lnext` | HOL4 proves the termination with the induction principle of `llistTheory`'s `eventually`; the port proves the existence of the function with `new_specification`, from the number of steps to the first tail that satisfies the predicate (`MINIMAL_SUC`, `eventually_LTL` and `LDROP_SUC` of `ml/lib/llist.ml`) |

Two definitions cost the port a run to work out, and cost it
nothing now: `bvi_let$compile` and `bvi_let$compile_sing`.  Their
`Let` clause compiles the body in an environment that the result
of the first recursive call builds, which reads like a nested
recursion -- and is not one as far as HOL Light is concerned,
because the measure of HOL4's relation is on the third argument
alone and that inner call sits in the first.  What they needed was
three things, and none of them a proof:

| what | why |
|---|---|
| `list_size f (BUTLAST l) <= list_size f l` and `~(l = []) ==> f (LAST l) <= list_size f l` in `cake_term_facts` | the `Let` clause recurses on the list without its last expression and on that last expression, and `ml/lib/define.ml` invites a ported file to add the facts that its own definitions ask for (`overrides.EXTRA_BEFORE` adds them, `EXTRA_AFTER` takes them back) |
| a budget of more than eight seconds | eight is what a definition of the port gets before it is assumed instead, and these two take about twenty each |
| the relation handed to `define_single` rather than to `cake_define_gen` (`overrides.DEFINE_REL`) | the chain of `cake_define_gen` tries eight strategies before the relation, one of them declares the constant and then fails, and `with Failure _ when not (declared ())` tries nothing after that -- so the relation never got its turn |

With the three in place `compiler/backend/bvi_let.ml` adds **no
axiom**: both constants come from `new_specification` and their
clauses are theorems.  It took a wrong diagnosis first, and that
one is in `PORTING-GUIDE.md` entry 17, because the way it went
wrong is the part worth keeping.
