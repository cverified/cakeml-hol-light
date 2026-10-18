# Theorems whose statement the port does not have

Phase two states every theorem of the sources with its name, its
attributes and its statement (`CLAUDE.md`).  Of the 10,688
theorems of the 270 sources the port states 10,131 and points at
557 with a comment that names them:

| | stated | a pointer |
|---|---|---|
| `Theorem` (and `Triviality`) | 10,089 | 45 |
| `ThmValue` (the value of an ML expression) | 11 | 468 |
| a theorem that ML code states (`Q.prove`) | 31 | 44 |

What the 557 are, and why the port cannot state them:

- **468 theorems that HOL4 states as the value of an ML
  expression** (`Theorem foo[simp] = CONV_RULE (RAND_CONV EVAL)
  foo_def`, `Theorem bar = SIMP_RULE bool_ss [] baz`, `Theorem
  baz = theorem"baz_ind"`).  The statement is not in the source:
  HOL4 computes it from another theorem, so writing it down means
  doing the computation.  The port could do most of them in phase
  three, where it has the theorem that the expression starts from
  and HOL Light's own rules to apply, but none of it is a
  statement that phase two can read off the source.
- **44 theorems that ML code states as the value of a rule
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

Everything else of the sources is in: `tools/coverage.py` counts
the blocks and the theorems of every source against its port, and
what it reports missing is the two blocks below and these 515.

**Forty-four statements use an auxiliary size function of a
datatype family** (`exp1_size`, `exp3_size`, `v1_size`, ...).  HOL4's
`Datatype` makes one of these for every type that the family
needs besides the type itself (`exp1_size` of closLang is the
size of a `(num # exp) list`), and HOL Light numbers the types of
a family in another order, so a name of HOL4's says nothing about
which function of the port it is.  The port writes a pointer that
names the theorem: a statement with a free variable where the
source has a constant would say something else than the source
does, which is worse than saying nothing.

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
10,613 are the theorems of the CakeML sources.

# Definitions that the port assumes with a free variable

Fifteen of the definitions that `ml/CHEATS.md` lists are assumed
with a **free variable** in them (`free: ...`), which is the kind
of cheat that a decision or a missing piece has to settle and not
a proof:

- a **mutual recursion of two functions** that the port writes as
  two definitions, so that each clause of the one mentions the
  other as a free variable (closProps' `set_globals` and
  `elist_globals` are one `Definition` of HOL4, with a
  `sum_size` measure; the same for `semanticPrimitivesProps`'
  `sv_rel` and `result_rel`, and for `exc_rel`).  The clauses of
  the two have to go to HOL Light as one definition, which the
  define layer can do where the recursion is over one datatype
  family.
- a definition whose body uses a constant that the port does not
  have (`gc_fun_ok` of `data_to_word_gcProof`).

Until then the constant is there with the right type and its
clauses are assumed, so the statements about it typecheck; what
is wrong is the clause, which is an axiom over the free variable
as well.  Phase three has to make the definition.

# Definitions whose form deviates from HOL4's

The first pass ports every `Datatype`, `Type`, `Overload`,
`Definition` and `Inductive` of the 269 files of the port: 4444
blocks, of which all but two are in (see `tools/coverage.py`); the
ones that HOL4 makes in a way that the port has no counterpart
for are declared constants (`cake_declare`, which adds no
axiom), which the list below has.
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

Six constants are declared for another reason (of the fourteen
that the port declares in all): the one field of the asm
configuration of a target that is not data is its
encoder, and an encoder needs a machine model of HOL4 (`x64_step`
and the five others), which is not part of the CakeML sources, so
the six encoder theories are outside the port
(`tools/excluded.txt`).  For each of `x64`, `arm8`, `mips`,
`riscv` (64 bits) and `arm7`, `ag32` (32 bits) the port therefore
declares `<target>_config`, with the type that
`compiler$parse_target_64` and `parse_target_32`, which the
command line of the compiler goes through, use it at
(`EXTRA_BEFORE` in `tools/overrides.py` has the text).

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
