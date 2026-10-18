# Plan for the first pass (all definitions)

_Policy (2026-10-17, from the user): in this pass **proofs are
irrelevant**, and the rule that nothing may depend on a cheat is
**suspended** until the definitions are done.  A termination
condition that HOL Light's machinery does not discharge is
assumed with `CHEAT_TAC` when the condition is evidently true,
and the definition is then made by `new_specification` -- one
axiom, a real constant, real clauses.  No time goes on looking
for a measure or on a lemma to help one.  What is left to work
on is the definitions that HOL Light cannot make **at all**: a
body with a type variable that the constant does not reflect,
or a constant that the port does not have.  See `CLAUDE.md`._

_State: the port has every definition block of the 263 files that
it has to have but two (4430 of 4432, which `tools/coverage.py`
checks: every `Datatype`, `Type`, `Overload`, `Definition` and
`Inductive` of every ported source; the two are the command line
drivers of the compiler binary, which need the file system of the
basis library -- see `PENDING.md`).  `tools/bin/checkseq` loads
the files one after the other in the order of `tools/load.txt`:
in the run of 2026-10-18 00:53 **every file loads to the end**,
and of the 454 theorems that the pass assumes (`ml/CHEATS.md`)

- **302 are the termination of a definition** (`CHEAT_TAC` on the
  condition): the constant is introduced by `new_specification`,
  it has the right type and its clauses are theorems, so
  everything after it is ported as if the definition were there,
  because it is;
- **132 are the equation of a tail recursion** of the bignum
  library: `mc_multiword` defines each of its 66 routines as the
  `SHORT_TAILREC` of a step function and its precondition as the
  `SHORT_TAILREC_PRE` of it, which the port does as well
  (`ml/lib/mc_tailrec.ml`), and HOL4's `mc_tailrecLib` then
  proves the equation that unfolds each of the two, which the
  pass assumes;
- **20 are a constant that is declared** without a value, because
  HOL4 makes the value in a way that the port has no counterpart
  for (`PENDING.md` lists them: the twelve configurations of the
  targets, the basis program, the four step functions of the tail
  recursions of `unify` and the three entry points of Pancake);
- **none is a definition that the port does not make**.

That was `length (axioms ()) = 338` and 5185 s, no cheat has a
free variable (`tools/bin/freevars`), no definition has clauses
that do not typecheck apart (`tools/conjfail.log`) and no
constant has a type outside the scope of its theory
(`tools/bin/types`).  The runs of this round were 17:21 (323
assumed, 335 axioms, 5 files that die), 19:34 (325, 370, 2),
22:26 (295, 340, 2), 01:12 (292, 304, 2), 03:14 (290, 299, 1),
05:37 (291, 303, **0**), 10:35 (38 not made, 239, 1), 12:04 (35
not made, 239, 0), 16:49 (25 not made, 250, 0), 18:43 (one not
made, 232, 0), 20:39 (**none not made**, 205, 0), 22:11 (none,
208, 0, with `panLang`, the exports of the targets and the
Pancake definitions of `compiler` in it) and 00:53 (none, 338, 0,
with the bignum routines built as HOL4 builds them)._

_What the port builds the way HOL4 builds it (2026-10-18, from
the user: if HOL4 builds a definition from a source file, the
port should do that too, and the port should be as similar in
structure to the HOL4 version as reasonable):_

- _the deep embedding of the bignum routines
  (`word_bignum$mc_iop_code` and ten others): the `to_deep` of
  `word_bignumScript.sml` is `tools/word_bignum_todeep.ml` in
  OCaml, which `ML_PORTED` writes where the source has its ML;_
- _the routines that it translates: the 66 `tailrec_define`s of
  `mc_multiword` are 66 calls of the port's own
  `tailrec_define`;_
- _the bodies that the `check1` of `flat_to_closScript.sml`
  builds (`CopyByteStr`, `CopyByteAw8`):
  `tools/flat_to_clos_check.ml`;_
- _the FFI blocks of the assembly of the six targets, which the
  ML of each `export_<target>Script.sml` builds and `EVAL`
  computes: the port writes the term that HOL4 evaluates (both
  terms of a binding of two, which `tools/hol4.py` reads now);_
- _what is left of that kind: the basis program (the proof
  producing translator of HOL4 builds it) and the four step
  functions of the tail recursions of `unify` (HOL4's
  `tcallify_th` makes each from a theorem that the second pass
  has to prove first).  Both are declared constants._

_What the last one was.  `word_bignumProof$Eval` is an
`Inductive` whose rules apply `eval_exp` to a `wordLang$exp` that
nothing in them types, because the constant of the port (unlike
HOL4's) did not tie the type of its expression to the one of its
state: the clauses of `eval_exp` went to HOL Light one by one,
the `+` of its `Op Add` clause had nothing in that clause to say
that it adds machine words and became the `+` of the numbers, so
the types of the eleven clauses no longer fitted together and the
port fell back to assuming them one at a time with the type of
the first.  `tools/conjfail.log` of a run says where that
happens; there were four such definitions in the whole port
(`eval_exp` and three of `clos_constantProof`, where the `Int`,
the `W64` and the `Con` of a constant part and a `Word64` of
closSem went the same way).  All four are one quotation now
(`ONE_QUOTATION`), which typechecks the clauses together, and
with them 28 axioms are gone: both files are free of cheats._

_What the round repaired.  The admissibility machinery: the
termination conditions of a definition arrive as one
conjunction, which the port gave to the proof of a measure goal
as a whole, and an admissibility condition among them needs the
proformas of HOL Light instead (which the port only reached
when it gave no relation).  With the proforma of an existential
(and its bound variable renamed), of a `let`, of an `EVERY` and
of an `EXISTS`, one substitution at a time, the value of a
constant without arguments, the two size lemmas of a pair one
at a time, the measure of a family, the length of a `DROP` and
the parts of each side of a sum that a destructor gives, the
definitions of the shape of `wordLang$max_var` are made:
wordLang, word_inst, word_simp, word_remove, word_unreach,
stack_names, stack_remove, jsonLang, mlint and typeSystem
assume nothing any more, and word_alloc went from 8 to 4.
`tools/smoke.ml` holds a definition of every shape that the
round repaired.  The five files that died are repaired by
giving the port the theory of a constructor (the `Break`, the
`Continue` and the `FFI` that the `evaluate` of stackSem
matches on are stackLang's) and the record of a variable (the
`var_map` of `source_to_flatProof$env_domain_eq`, the `t` of
`stack_to_labProof$halt_assum` and of `memory_assumption`, the
`s` of `source_to_flatProof$orac_rel_inner`); the `evaluate` of
stackSem is a definition now, which was 35 axioms on its own._

## What is ported

The dependency closure of `compilerProofTheory.compile_correct`
consists of 222 HOL4 theories, of which 139 are "definition
theories" (the others only contain proofs; see
`tools/closure2.txt` and `tools/order.txt`, which are
generated by `tools/closure2.py` and `tools/order.py`).

The first pass ports, in the topological order of
`tools/order.txt`:

1. the HOL4 library theories that CakeML uses and that HOL
   Light does not have (`ml/lib/`, see below);
2. all `Datatype`, `Type`, `Overload`, `Definition` and
   `Inductive` blocks of the 139 definition theories
   (`ml/<same path as in cakeml-src>`);
3. the definitions that occur in the proof theories of the
   closure (they are needed to _state_ the correctness
   theorems of the second pass; `backend_config_ok`,
   `mc_conf_ok`, `env_rel`, ... are of this kind), in the order
   of `tools/order1b.txt`: 83 theories with 928 blocks, which
   together with the 3023 blocks of the 120 definition theories
   and the 240 blocks of the 33 HOL4 library theories of
   `ml/lib` make the 4191 blocks of the first pass.

A definition that a source makes with ML code counts as well:
`Define` with any wrapper around it (`data_to_word` has 60
definitions behind its own `assign_Define`), `tDefine`,
`Hol_reln` (`parmove`'s `step` and `dstep`), a definition from
a quotation that the source keeps in a value (`stack_rawcall`'s
`comp` and six others), the monadic machinery that
`ml_monadBaseLib` makes (`reg_alloc` and `linear_scan`) and the
grammar that `grammarLib`'s `mk_grammar_def` makes out of a BNF
(`gram`'s `MMLnonT` and `cmlG`, see `tools/grammardef.py`).

`tools/portall.py` translates all of them (in seven seconds).

Not ported (and why):

- the L3 instruction set models (`x64_step`, `arm8_step`,
  `arm_step`, `mips_step`, `riscv_step`) and the CakeML
  theories that encode the instructions of a concrete target
  with one of them (`compiler/encoders/*/..._target`, and
  `ag32`, which is L3's model of the Silver ISA).  These are
  machine-generated HOL4 models of real processors, they live
  outside CakeML, and the main correctness theorem is generic
  in the target (`mc`, `asm_config`).  What the port does have
  of a concrete target is what needs no model of it: the
  configuration of the backend and the register names
  (`compiler/backend/*/..._config`) and the theory that
  exports its code (`export_*`).
- the basis library program (`basisProg`), the proof-producing
  translator and characteristic formulae (`translator/`,
  `characteristic/`): `compiler$compile` takes the prelude as
  an argument, so the main theorem does not mention them.
- Pancake (`pancake/`, `pan_to_target`, `panPtreeConversion`):
  a second source language of the same compiler backend, not
  mentioned by the CakeML correctness theorem.

## Infrastructure (`ml/lib/`)

- `hol4.ml`      HOL4's list/option/arithmetic vocabulary that
                 HOL Light lacks (`EVERY`, `FOLDL`, `THE`,
                 `ALOOKUP`, `GENLIST`, `TAKE`, ...)
- `records.ml`   a record package (HOL Light has none):
                 `define_record` makes the type, the field
                 accessors `ty_fld`, the updates `ty_fld_fupd`
                 and the literal constructor
- `fastdef.ml`   HOL Light's own machinery for a definition by
                 cases, copied word for word with the proformas
                 of its admissibility proof and the last
                 existence theorems kept (they are the better
                 part of the time of a definition with many
                 clauses); the names of HOL Light are bound to
                 the functions of this file
- `define.ml`    HOL4's `Definition` for HOL Light.
                 `cake_define` tries, in this order:
                 `new_definition` (one clause, not recursive),
                 `define_prim_rec` (the recursion theorem of the
                 datatype family, which also defines a family of
                 functions at once), `define_nested` (a recursive
                 call under a map, and the composition of a
                 function of the block with a map),
                 `define_maplist` (a function of a list that is
                 the map, the conjunction, the disjunction or the
                 concatenation of a function of the block over
                 it), `define_cond_bool` (the same where HOL4
                 writes the fold with a conditional),
                 `define_sing`, `define_cases` (patterns inside
                 patterns: compiled into functions on the types
                 of the family, with FST/SND for a pair and a
                 conditional for an option), `define_match` (the
                 same for a definition written with a match),
                 `define_lift_if` (a conditional around a
                 recursive call lifted to the top of the clause),
                 and finally HOL Light's wellfounded recursion
                 with the measure of HOL4's `Termination` or a
                 guessed one.  Everything but the last derives
                 the clauses as HOL4 states them.
                 `cake_inductive` is HOL4's `Inductive`
- `mc_tailrec.ml` HOL4's `mc_tailrecLib` for HOL Light: the
                 routines of the bignum library are defined from
                 their step function, as the `SHORT_TAILREC` of
                 it (and their precondition as its
                 `SHORT_TAILREC_PRE`), and the equation that
                 unfolds each of the two is assumed
- then the HOL4 library theories themselves: `sptree.ml`,
  `finite_map.ml`, `balanced_map.ml`, `words4.ml`,
  `integer_word.ml`, `alignment.ml`, `bitstring.ml`,
  `byte.ml`, `binary_ieee.ml`, `machine_ieee.ml`, `llist.ml`,
  `lprefix_lub.ml`, `path.ml`, `set_sep.ml`, `peg.ml`,
  `pegexec.ml`, `grammar.ml`, `ASCIInumbers.ml`,
  `numposrep.ml`, `mergesort.ml`, `comparison.ml`, `toto.ml`,
  `state_transformer.ml`, `spt_closure.ml`, `unification.ml`,
  `multiword.ml`, `mc_multiword.ml` (the bignum routines, which
  `tailrec.ml` and `mc_tailrec.ml` are for), `errorMonad.ml`

## Names

HOL Light has one flat namespace, CakeML has one per theory,
and CakeML reuses names heavily (every intermediate language
has `Var`, `Call`, `exp`, `state`, ...).  Therefore:

> A CakeML name is kept as it is when it is unique in the
> whole port (and does not clash with HOL Light); otherwise it
> is prefixed with the name of its theory and an underscore
> (`closLang_Var`, `wordSem_state`).

A name that _several theories of the port_ define is an
overloaded name in HOL4, which resolves it by the type.  HOL
Light can do that too, so such a name is declared as an
overload of all its constants (`hol4_overload "Var"
"closLang_Var"`) and the sources of the port use it exactly
where the CakeML sources use it.  A name that clashes with a
HOL Light name is not overloaded (HOL Light's own constant
would be in the way) but written out (`set_sep_one`).

The table of all names and their translations is generated by
`tools/names.py` into `tools/names.txt`, so the choice is
deterministic and does not change while the port grows.

## Record and case syntax

- `r.fld` becomes `ty_fld r`, `r with fld := v` becomes
  `ty_fld_fupd (K v) r`, `<| fld := v; ... |>` becomes
  `mk_ty v ...` (all fields, in declaration order)
- `case x of p => e | ...` becomes HOL Light's
  `match x with p -> e | ...` (same first-match semantics)

## Definitions by patterns

HOL4's `Define` compiles the patterns of a definition into a
decision tree.  HOL Light's machinery for a definition by
patterns is only usable when the patterns are on _one_
argument; with patterns on two arguments (`balanced_map`'s
`balanceL`) it does not finish.  So:

- patterns on one argument stay as they are;
- a definition that is not recursive and has patterns on
  several arguments becomes one clause with a `match` on the
  tuple of those arguments;
- a definition whose clauses overlap becomes one clause with a
  `match` as well (HOL Light's `match` has HOL4's first match
  semantics);
- a definition in which a variable name can have different
  types in different clauses (HOL4 typechecks the clauses on
  their own) becomes a list of clauses (`cake_define_list`).

## Per file

For each file: translate with `tools/port.py` (or all of them
with `tools/portall.py`), load it into a HOL Light session, fix
what fails, keep the loading time of the file in
`ml/TIMINGS.md`, and commit.  `tools/bin/checkseq` loads the
files of the port one after the other in one session and
reports the time, the number of axioms and the first failure of
each, which is the measure of how far the pass is.  With `MARK=1`
it also says which phrase of the file fails.

The other checks:

- `tools/coverage.py`  every block of every HOL4 source that the
                       port has to have is in
- `tools/fidelity.py`  no definition of the port lost a name or a
                       constructor argument on the way
- `tools/literals.py`  the strings, the characters and the
                       numerals of a definition are the same ones
                       in the port (the escapes of a literal are
                       read by both parsers, in almost the same
                       way)
- `tools/lets.py`      a `let` that binds a function abstracts its
                       arguments (HOL Light takes the left hand
                       side of a binding for a pattern)
- `tools/bin/checks`   the checks above that need no session
- `tools/bin/runall`   start a run on the whole load order
- `tools/bin/postrun`  the reports of a run that finished, in the
                       order in which they have to be made
- `tools/bin/cycle`    everything between two runs: the reports,
                       the cheat list, the port, the checks, the
                       template, the smoke test and the next run
                       (with NORUN=1 it stops before the run and
                       keeps a clone of its session as hol-try)
- `tools/conjfail.log` the definitions of a run whose clauses do
                       not typecheck apart (`postrun` reports it):
                       each needs `ONE_QUOTATION`
- `tools/bin/quotes`   which quotation of a file does not parse
                       (in a session that has the file loaded);
                       `tools/bin/quotesall` does that for every
                       file that the last run reports
- `tools/bin/locate`   which phrase of a file fails
- `tools/bin/retry`    load a file from the phrase that failed on,
                       in a clone of the session of the last run
- `tools/grammardef.py` the BNF of a grammar that HOL4 turns into
                       a datatype and a definition with ML code
- `tools/bin/deps`     load only what a file needs
- `tools/bin/cheats`   write `ml/CHEATS.md` from `cake_cheats ()`
- `tools/bin/timings`  write `ml/TIMINGS.md` from the last run
- `tools/bin/types`    the type of every constant stays in the
                       scope of its own theory (a constant whose
                       type mentions a theory that the HOL4 source
                       does not have as an ancestor got an
                       overloaded name of a theory that is not in
                       its scope)
- `tools/bin/freevars` which constants the definitions that the
                       first pass assumes miss (a free variable is
                       a constant that the port does not have)
- `tools/bin/trydef`   make the definitions that the first pass
                       assumes again, with their constants
                       renamed, in a clone of the session of the
                       last run: that is how a change to the
                       strategies of `ml/lib/define.ml` is tried
                       without a run (`PATCH=` loads the changed
                       part of the library first,
                       `tools/tailpatch.py` cuts it out)
- `tools/bin/shapes`   classify the assumed definitions by their
                       shape (not recursive, a recursive call
                       under a lambda, more than one function, a
                       call on a term that the clause builds)
- `tools/bin/whereis`  which HOL4 theory defines a name, whether
                       the port has that theory, and what the
                       port calls the constant
- `tools/bin/slow`     which definitions of the last run took the
                       longest
- `tools/bin/source4`  the HOL4 source of a definition of the
                       port, with its Termination
- `tools/conjtest.py`  whether a definition of the port is made
                       the way `cake_define` makes it (the clauses
                       of a clause list have to fit together),
                       with the constants renamed, so that a
                       session that has them already does not give
                       them their old types

A definition that takes minutes is a bug.  The two that bit so
far: HOL Light's machinery for a definition by patterns is slow
(use `define_prim_rec` or a `match`), and a recursive call under
a map over a list of pairs needs the functions of the recursion
theorem for the pair as well (`define_nested`).

## What is left of the first pass

Every definition is in and the files load, but the definitions
that none of the strategies of `cake_define` makes are _assumed_
(`ml/CHEATS.md`).  Making them is the rest of the first pass:

- a definition whose clauses the port has to assume one by one is
  a bug of the port, not of HOL Light: the clauses are
  typechecked on their own and got types that do not fit
  together.  `cake_define_list` says why, a run writes every one
  of them to `tools/conjfail.log` (which `tools/bin/postrun`
  reports), and `tools/bin/conjs` asks the same question of a
  file that is loaded.  The four of the run of 18:43 are one
  quotation now (`ONE_QUOTATION` in `tools/overrides.py`), which
  typechecks their clauses together.
- a definition that only the timeout stops needs a better
  strategy or a termination measure, not more seconds.  The
  measure is usually not the problem: `clos_fvs$remove_fvs` is
  made with the measure that `candidate_measures` gives it
  (`MEASURE (\(x0,x1). closLang_exp_size1 x1)`), but the
  existence proof of HOL Light takes seven minutes over its
  thirteen clauses.  As one clause with a `match` it takes ten
  minutes and does not get there at all.  What the twenty or so
  definitions of this shape (the recursions over `closLang$exp`
  of the clos phases, each with its `_sing` companion) need is a
  faster way of proving the termination conditions, not another
  measure or another form.
