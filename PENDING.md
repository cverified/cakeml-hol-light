# Definitions whose form deviates from HOL4's

The first pass ports every `Datatype`, `Type`, `Overload`,
`Definition` and `Inductive` of the 262 files of the port: 4426
blocks, of which every one is in (see `tools/coverage.py`); the
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

Twelve constants are declared for another reason: the encoder of
a target needs a machine model of HOL4 (`x64_step` and the five
others), which is not part of the CakeML sources, so the encoders
and the configurations that have one in them are outside the port
(`tools/excluded.txt`), and `compiler$parse_target_64` and
`parse_target_32`, which the command line of the compiler goes
through, only pass them on.  For each of `x64`, `arm8`, `mips`,
`riscv` (64 bits) and `arm7`, `ag32` (32 bits) the port declares
`<target>_backend_config` and `<target>_config`, with the types
that the two definitions use them at (`EXTRA_BEFORE` in
`tools/overrides.py` has the text).  The theory that exports the
code of a target needs only `export`, which the port has, so
`<target>_export` is a definition of the port.

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
