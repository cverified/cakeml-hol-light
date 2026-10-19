# Plan for phase two (the statements)

_Phase two states every theorem of the CakeML sources: its name,
its attributes and its statement, with `CHEAT_TAC` where HOL4 has
its proof, and every comment of the source in its place
(`CLAUDE.md`).  The test is to read a source and its port next to
each other: they have to read "the same"._

_State: the port has 10,129 of the 10,688 theorems of the 270
files with their statement and 559 as a pointer that names them
(`tools/coverage.py` counts both; `PENDING.md` says what the 559
are).  **Every one of the 270 files loads to the end**, and of
the statements the run of 01:40 could read all but **four**: the
first phase-two run of 14:03 could not read 688 statements, the
one of 16:30 could not read 295, the one of 18:21 141, the one of
20:17 100 and the one of 22:57 26 (that run also stopped
`lab_to_targetProof` at the 34th of its 476 blocks, where the
`s1` of its `asm_step_nop` is a state of the target and the
annotation of the theory made it one of labSem).  436 statements
are read with the overloads of the record field names taken away._

_Of those four, three read now: the `compile` of the `s` and the
`t` of `stack_namesProof` is the field of a stackSem state (a
bare `compile` is the constant of a compiler pass, and the port
has 28 of those), and `mw_ok` of HOL4's `multiwordTheory` was not
in the library layer at all.  The fourth is
`lab_to_targetProof$word_cmp_lemma`, whose `read_reg` is the
`regs` of a labSem state on one side of the equation and of an
`asm_state` on the other: the port expands the body of an
overload once per theory (with the accessor of the field written
out, which a statement that is read with the field names taken
away needs), and that is one record too few.  What would settle
it is to expand such an overload **per occurrence**, with the
record of the argument that is there, which comes to a beta
reduction of the application; `PENDING.md` has it._

_**The main correctness theorem of CakeML is stated.**
`compilerProof` gives `compile_correct` as the value of a `prove`
of a quotation of it with `check_thm` applied to the result, and
that quotation has a comment in the middle of it, which cut the
block in two: the port had a pointer where the statement was in
the source all along._

_What the round after the run of 01:40 also found, with the two
checks that a session needs:_

- _`tools/bin/types` (every constant's type only mentions types of
  theories in its own scope) found that the `extras` of
  `bvi_tmcProof$alloc_hole_has_val` were a list of dataSem's
  values, where bviSem's `evaluate` takes bvlSem's.  It had
  looked at the constants that the port renames only, which is
  one in ten._
- _`tools/stmtfree.py` (a free variable of a statement whose name
  a theory of the scope defines) found that **67 statements of
  `pegComplete`** read `peg_eval`, `peg0`, `peg_eval_list` and
  `pegfail` as variables of their own: what a HOL4 library theory
  has to provide is computed from the names that its blocks
  define, and an `Inductive` names its relations in the
  conclusions of its rules.  `ml/lib/peg.ml` makes the four
  relations now._

_What the run of 16:30 also found: `tools/bin/checkseq` read the
word "timeout" anywhere in the output of a step as the timeout of
`repl-step`, and `grep -q` ends the step as soon as it matches, so
the file that was loading was interrupted in the middle.  Six
files lost their tails that way (and everything that needed
them).  The test is the line that `repl-step` writes, and the
message of a statement that HOL Light cannot read goes out as one
line now, because a line of the output that starts with a `#` is
the prompt of the toplevel as far as the scripts are concerned._

_What the checks of the statements say (`tools/bin/checks`, none
of which needs a session): the blocks of every one of the 228
ported files that have one are in the **order** of the source and
so are the comments (`tools/order.py`), every statement has the
**attributes** of its theorem (`tools/attrs.py`), no statement
lost a **constant** of the source (`tools/stmtnames.py`), no
statement uses a name of a HOL4 **library** that the port has not
(`tools/libnames.py`), every **comment** of a source is in its
port or a pointer says where the code in it is
(`tools/comments.py`), and no statement counts the
**connectives** of the source differently but the 24 that
`tools/shapeok.txt` accounts for, where the port writes out what
HOL4 says with a name (`tools/stmtshape.py`).  What needs a
session: `tools/bin/types` checks that the **type** of every
constant of the port only mentions types of theories that its own
theory has as an ancestor; it looked at the constants that the
port renames only, which is one in ten, and with all of them it
found that the `extras` of `bvi_tmcProof$alloc_hole_has_val` were
a list of dataSem's values.  The last of those
is what found that the port read the `~0w` of HOL4 (the word of
all ones) as the negation of a number._

- **A theorem is a cheat of its own.**  `cake_theorem name mkterm
  tac` (`ml/lib/theorem.ml`) reads the statement in a function,
  so one that does not typecheck is recorded in
  `cake_unstated ()` and the file goes on; `tools/bin/thms`
  reports them per run.  No exception leaves it: five files died
  on a statement that is not a formula in the first run and lost
  everything after it.
- **The name of a record field is a variable.**  HOL4 has no
  constant of the name of a field (`r.stack` is syntax there), so
  a statement that uses `stack` or `limit` or `pc` for a variable
  of its own is read with the overloads of the field names taken
  away (`cake_as_vars`), and `cake_fieldvars ()` says which
  statements of the port needed that.
- **A name out of scope is a variable.**  Every file says which
  names no theory in the ancestry of its source defines
  (`cake_hide`), and its statements are read with those constants
  hidden: HOL4 reads them as variables, while the port has every
  constant in one namespace (the unification library's `vars`
  against the `vars` of data_to_word_memoryProof).
- **A numeral of type int is `&n`.**  `tools/intargs.txt` has the
  arguments of the constants of the port whose type is `int`
  (`tools/bin/intargs` dumps it out of a session), and the
  translator writes a numeral there as an integer.
- **The notation of the statements.**  What phase one never met:
  `|==>` and `===>` (the function relation of HOL4's transfer
  library), `###` (the pair relation), `⋲` (bag membership), `⇎`
  (`<>` on bool), `◁` (walkstar), `⊕` (the xor of two words),
  `f⦇k ↦ v⦈` (a function update), `!!` (the or of two words), a
  subscript in a name (mlstring's `s₁`), and the name of an
  `Overload` as HOL4 escapes it (parmove's `"\226\137\161"` is
  `≡`).
- **The readings that were wrong.**  What the statements of phase
  two brought to light, each of which the port now reads as HOL4
  does:
  - a prefix of HOL Light takes the atom after it and no more, so
    `~MEM x l` is `(~MEM) x l` there (467 lines of 70 files, and
    stackSem's `evaluate` was assumed because of it);
  - the value of a record update stops at an equation, and the
    update itself is a postfix of the whole application
    (`initial_state f c co cc k with clock := k1`);
  - the finite map and function postfixes bind to the atom before
    them (`FAPPLY tf⟨ts2 ↦ x⟩`);
  - a statement is not a definition, so its left hand side binds
    nothing: 122 statements had a constant of HOL Light in them as
    a primed variable (`MAP (SND' o SND')`);
  - the body of an overload is read in the theory that declares it
    (labSem's `read_reg` is `s.regs` of a labSem state);
  - a token that a theory overloads itself is read as its own, and
    the grammar of a file is in place before its overloads are
    read (parmove's `▷*` is the `RTC` of its own `step`, and
    backend_common overloads the same token with its `Cons`);
  - an ambiguous constructor is the one of the closest theory of
    the ancestry, as HOL4's overload resolution takes the one that
    its own ancestry loads last (`Loc` of data_to_word_gcProof is
    wordLang's);
  - only the symbol of `BAG_UNION`, `FUNION` and `BAG_IN` is an
    infix, and `LEX` and `o_f` are infixes by name;
  - HOL4 unifies the type variables that a statement writes and
    HOL Light does not, so the port leaves the annotations of the
    eleven statements that need the unification out
    (`overrides.THM_NO_TYVARS`) or, better, writes the type
    variables of the first annotation of a type operator in every
    other annotation of it, which is the type that HOL4 gives the
    theorem (`overrides.THM_TYVARS`: leaving the annotation out
    takes the record type with it);
  - the `~` of a word literal is the complement of a word
    (`~0w` is the word of all ones) and not the negation of a
    number, and the `<=` of two bags is HOL4's `SUB_BAG` (its
    `bagTheory` overloads `<=` and `<`, and sends both to the back
    of its resolution order);
  - a field of a record that a statement says the type of is read
    with the accessor of that record and not with the overloaded
    name of the field, and the states that a proof theory relates
    say which record they are (`overrides.FIELD_VAR`, per theory,
    and `FIELD_VAR_DEF`, per statement);
  - the theory whose constructor a statement means is the one of
    its own grammar (`overrides.CON_OF` per statement: the `Seq`
    and the `Skip` of `data_simpProof$evaluate_Seq_Skip` are
    dataLang's, and every intermediate language has both);
  - a statement whose statement is an **ML expression** is a
    pointer, also where the ML parses as a term (the two of
    `wordProps` are `^(let fun sel s = ... end)`, a conjunction
    that an ML function of the source builds);
  - a theory in front of a symbolic name is dropped
    (`prim_rec$<`), a subscript in a name is a digit, and the
    name of an `Overload` is read through `sml_string`.
  - a `Parse.hide` of a source hides a name from there on, which
    the port says where the source says it (`cake_hide_more`):
    `data_to_word_memoryProof` hides `free`, `el` and `sign`, and
    its statements after that line use them for variables of
    their own;
  - the overload of the name that HOL4 gives an accessor itself
    (`state_ffi`, where every record of the name is a `state`) is
    not one that `cake_as_vars` takes away, because HOL4 has that
    constant: a statement that reads a field through it lost it
    with the names of the fields;
  - a name that the accessors of a field have as well is not
    hidden either, and only the constant that the file cannot see
    goes out of the interface (`cake_hide_consts`): the `failed`
    of `labProps` is the field of a state and not the constructor
    `failed` of pegexec's `kont`, which four files read as a
    variable;
  - the body of an overload is read in the theory that declares
    it, so the accessor of a field in it is written out: labSem's
    `read_reg` is the `regs` of a labSem state, where a statement
    with a variable `regs` read that variable (ten statements of
    two files);
  - a numeral beside an element of a field that holds integers is
    `&n` as well (`0 < EL i sth.int_beg` of `linear_scanProof`),
    for which the types of the fields of a record are in the
    database now.
- **The library layer of the statements.**  The statements of the
  sources now seed the set of definitions that the port needs of
  a HOL4 library theory, which `TotOrd`, `good_cmp`, `SORTS` and
  `lprefix_chain` were missing for; `toto` is ported, and
  `relation`, `bag`, `finite_map` and `hol4` gained the thirty
  definitions of HOL4's core theories that the statements use
  (`transitive`, `StrongLinearOrder`, `BAG_IMAGE`, `f_o_f`,
  `FUN_REL`, `RPROD`, `BIT`, `COMPL`, `AFUPDKEY`, `surj`, ...).
  The last gaps of it are closed as well (`PENDING.md` has the
  table): `ml/lib/path.ml` is the part of HOL4's `pathTheory`
  that the two statements of `misc` about a path need, and
  `w2s` and `word_to_hex_string` are at the end of the port's
  `ASCIInumbers`, because HOL4 has them in its words theory and
  the hand written words layer of the port is loaded before
  `ASCIInumbers` -- they need its `n2s`.

_What is left of phase two:_

1. _every statement that the port has **typechecks**: a run says
   which do not (`tools/bin/thms` from `cake_unstated ()`), and
   `tools/bin/diag` says the same without a run of its own.  One
   is left (`word_cmp_lemma`, above);_
2. _no statement is **silently weaker** than the source's.  Four
   checks say it, and `tools/bin/cycle` runs all four between two
   runs: `tools/diag.py` reports a statement that applies a name
   the port made a variable, `tools/stmtfree.py` a free variable
   whose name a theory of the scope defines, `tools/bin/types` a
   constant whose type mentions a theory outside its scope, and
   `tools/libnames.py` a name of HOL4's libraries that the port
   has not;_
3. _then phase two is done, and phase three starts -- by hand,
   one theorem at a time._

_What is in: every `Theorem` of the 270 sources with its name, its
attributes and its statement (10,131 of 10,134), the 33 theorems
that the ML code of a source states itself, every comment (the
prose of it), and a pointer that names each of the theorems whose
statement HOL4 computes._

_What the port does not state (`PENDING.md`): the 479 theorems
that HOL4 states as the value of an ML expression (it computes
the statement with `EVAL` or a rule, which the port cannot), and
three whose statement is itself an ML expression
(`word_to_stackProof$comp_correct` and two others).  Each is a
pointer at the source lines, with the name of the theorem in it._

# Phase one (done): all definitions

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

_State: the port has every definition block of the 269 files that
it has to have but two (4442 of 4444, which `tools/coverage.py`
checks: every `Datatype`, `Type`, `Overload`, `Definition` and
`Inductive` of every ported source; the two are the command line
drivers of the compiler binary, which need the file system of the
basis library -- see `PENDING.md`).  `tools/bin/checkseq` loads
the files one after the other in the order of `tools/load.txt`:
in the run of 2026-10-18 09:53 **every file loads to the end**,
and of the 448 theorems that the pass assumes (`ml/CHEATS.md`)

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
- **14 are a constant that is declared** without a value, because
  HOL4 makes the value in a way that the port has no counterpart
  for (`PENDING.md` lists them: the six asm configurations of the
  targets, whose `encode` field is the encoder of a machine model
  that the CakeML sources do not have, the basis program, the
  four step functions of the tail recursions of `unify` and the
  three entry points of Pancake);
- **none is a definition that the port does not make**.

That was `length (axioms ()) = 338` and 4883 s, no cheat has a
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
Pancake definitions of `compiler` in it) 00:53 (none, 338, 0,
with the bignum routines built as HOL4 builds them), 02:43 (none,
338, 0, and 4964 s: the translator of the bignum embedding only
matches what can match, which took `word_bignum.ml` from 448 s to
48 s) and 09:53 (none, 338, 0, 4883 s, with the configurations of
the backend of the six targets in it and no HOL4 code left in the
port)._

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

What it cannot translate it **points at**.  The port holds no HOL4
code, so where a source has ML code that builds something the port
has no counterpart for, or a tactic that proves a termination, or
an `Overload` or a `Type` that the port expands, or a definition
that `PENDING.md` says is not ported, or a comment whose body is
HOL4 code that the source has commented out, the port writes the
file and the lines to read instead:

```
(* HOL4 x64_configScript.sml:41-43: the ML values that the
   definitions below antiquote *)
```

`Porter.at` writes them, `tools/hol4.py` gives every block the
lines of the source that it spans, and `tools/nohol4.py` is the
check that nothing of HOL4 is left in `ml/`.  Taking the HOL4 code
out of the port (phase one and a half) took it from 124158 lines
to 83019.

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
- `tools/nohol4.py`    no HOL4 code is in the port, in a comment
                       or anywhere else (a ground rule of
                       `CLAUDE.md`)
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
