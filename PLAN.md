# Plan for the pass that is going on: the HOL Light idiom

_A theorem of the port is written the way HOL Light writes one:_

```ocaml
(* [simp] *)
let small_int_w2n = prove
 (`good_dimindex (:'a) ==> small_int (:'a) (&(w2n (w:word8)))`,
  (* a byte is below 256 ... *)
  REWRITE_TAC[...]);;
```

_and a proof names another theorem by its binding
(`memory_rel_El`), not by a lookup under its HOL4 name
(`cake_thm "memory_rel_El"`).  What the registry did is gone with
it:_

- _the attributes that HOL4 gives a theorem stand in a comment
  over it, which is where a reader of the source expects them;_
- _a name that HOL4 reads as a variable because no theory in
  scope defines it is hidden with HOL Light's own
  `hide_constant`, at the head of the file and unhidden at its
  end (HOL4's `Parse.hide` is file-scoped as well);_
- _a variable whose name the port overloads with a record
  accessor says its type in the statement
  (`tools/fieldvars.py`); ten statements
  of the port cannot say it -- the type has a variable of its
  own, or HOL4 computes the statement -- and those are read with
  `cake_as_vars`;_
- _a file that needs the accessors of a field and reads the name
  of that field as a variable as well takes those pairs out of
  the interface with `hide_overloads` (32 files);_
- _two files that state a theorem of one name each get a binding
  of their own, the later one with the theory in front of it, so
  nothing can pick up the other one by mistake._

_What to look at, when the pass is reviewed:_

- _`tools/port.py`: `annot_vars` (the type a statement says of a
  variable), `state` (the shape of a theorem block and where its
  proof comes from) and the two hide/unhide emissions;_
- _`tools/hterm.py`: the `rawtyped` node, which prints a variable
  with the type the table gives it;_
- _`ml/lib/theorem.ml`: what is left of it (two functions), and
  `ml/lib/tactics.ml`, where `V_INV_TAC` takes the theorem that
  says what `v_inv` is instead of looking it up;_
- _`tools/fieldvars.py`: 389 statements say the type of a
  variable and 25 are read with `cake_as_vars`.  The
  table was harvested once, from a session of the old shape;
  `tools/fieldvars.py` says how a new entry is found;_
- _the statements that keep `cake_as_vars` (41 of them) and the 31 files
  that keep `hide_overloads` -- the only places where the port
  still says something HOL Light has no primitive for;_
- _`tools/bindrefs.py`, which rewrote the 255 theorem and 976
  definition references of the proof store and renamed the 28
  sections whose theorem has a binding of its own; it is
  idempotent, so running it again says nothing;_
- _and the one behaviour that changed: a proof that fails is an
  error of the file now, where `cake_theorem` turned it into an
  axiom and let the file load on;_
- _`tools/overrides.py`: `MATCH_CLAUSES`, which the pass needed
  because the five `do_eq`/`do_eq_list` of the semantics are a
  family whose clauses overlap in one function -- `MATCH_FORM`
  wrote both functions as one match and `ml/semantics/`
  `semanticPrimitives.ml` would not typecheck (PORTING-GUIDE.md,
  entry 32).  The five files had the right shape by hand before,
  which a re-port threw away; now the generator writes it;_
- _`tools/coverage.py` (`bound`) and `tools/thms.py`, which both
  had to learn the two shapes a binding can have: the theory in
  front of the name, and a `prove` on the line below where the
  binding is too long for one line._

_The proofs name a definition by its binding as well
(`memory_rel_def`, not `cake_def "memory_rel"`): 976 references.
A binding of a definition is unique, as a binding of a theorem
is: 249 names were the name of a definition in two files or more
(`compile_def` in 28 of them), so the plain name would be
whichever file loaded last, and 32 of the 976 references did
denote another theory's definition until `tools/port.py`'s
`bindname` gave every definition, inductive relation and monadic
definition a binding of its own (PORTING-GUIDE.md, entry 9).  No
two files of the port bind one name now._

_`cake_def` is left for the three tactics of `ml/lib/tactics.ml`
that reach into the definitions of the file they are applied in
(`MEMORY_REL_TAC` unfolds four of them): that file is part of the
library layer and loads before the files whose definitions it
unfolds, so there is no binding there to name._

_What is left of the pass: how the definitions are made.
`cake_define` is a chain of strategies, because no single HOL
Light primitive takes what HOL4 writes; a run harvests which
strategy each definition needed (`cake_strategies`), and the files
then say `new_definition` or `new_recursive_definition` themselves
where that is what the definition is, and keep the chain where it
is not._

# Plan for phase two (the statements)

_Phase two states every theorem of the CakeML sources: its name,
its attributes and its statement, with `CHEAT_TAC` where HOL4 has
its proof, and every comment of the source in its place
(`CLAUDE.md`).  The test is to read a source and its port next to
each other: they have to read "the same"._

_State: **phase two is done**, but for what the port cannot say.
The port has 10,146 of the 10,688 theorems of the 270 files with
their statement and 542 as a pointer that names them
(`tools/coverage.py` counts both; `PENDING.md` says what the 542
are, and none of them is a statement that phase two can read off
the source -- HOL4 computes it with ML code).  **Every one of the
270 files loads to the end** and **every statement reads**: the
run of 15:18 read all 10,122 of them, where the first phase-two
run of 14:03 could not read 688 (then 295, 141, 100, 26, 4 and 1
in the runs after it).  438 statements are read with the
overloads of the record field names taken away._

_And no statement says less than the source does, as far as four
checks can tell: none applies a name that the port made a
variable (`tools/diag.py`), no free variable of one is a name
that a theory of the scope of its source defines
(`tools/stmtfree.py`), no constant of one has a type outside the
scope of its theory (`tools/bin/types`), and the eleven names of
HOL4's libraries that a statement uses and the port has not are
variables in HOL4 as well (`tools/libnames.py`)._

_Every comment of every source is in the port, in its place:
2,344 comment blocks, of which 133 are HOL4 code with a pointer
at it, and all 1,218 comments that stand **inside** a block --
between the constructors of a `Datatype`, between the fields of a
record, between the clauses of a `Definition` or in a statement
-- which HOL Light reads as the `//` comment of a term
(`tools/comments.py`).  Every `Overload` and every `Type` of a
source has a counterpart as well (`tools/overloads.py`): an
overload of HOL Light, or a pointer where the port writes out
what the name stands for._

_The last statement to read was `lab_to_targetProof$word_cmp_lemma`,
whose `read_reg` is the `regs` of a labSem state on one side of
the equation and of an `asm_state` on the other.  HOL4 resolves
the name of an `Overload` by the type of each occurrence; the port
expanded the body of one (`\r s. s.regs r`) once per theory, and
that was one record too few.  It expands such an overload per
occurrence now, with the record of the argument that is there,
which is a beta reduction of the application
(`tools/port.py`'s `beta_overloads`)._

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

Every definition is in and the files load; no definition is
assumed with a **free variable** in it any more, and every
constant of the port is introduced by a definition -- the sixteen
whose value HOL4 computes with the ML code of a source get an
implicit one (`new_specification` of `?x. T`), which says nothing
about the value and adds no axiom.  What is left are the 438
definitions that `ml/CHEATS.md` lists: 306 whose **termination**
is assumed (the constant, its type and its clauses are the real
ones) and 132 that are the equation of a **tail recursion** that
HOL4 proves in `mc_tailrecLib`.  Those are a proof each, which is
phase three; a definition whose form is wrong is not, and these
are the two shapes of that:

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

# Phase three (next): the proofs

_Phase three replaces every `CHEAT_TAC` of the port by a proof,
until `length (axioms ())` is 3 (the three axioms of HOL Light's
kernel).  **The proofs are written by hand:** HOL4's proof is
read, understood, and then written as a HOL Light proof.  There
is no tactic translator and there will be none (`CLAUDE.md`)._

_It does not start before phase two is finished -- the statements
are all in and the port loads -- and then one theorem at a time,
in an order that makes every proof stand on proofs and not on
cheats:_

1. _the **termination** of the definitions of phase one (300 of
   them, `ml/CHEATS.md`): each is the condition that HOL Light's
   machinery could not discharge, and HOL4's `Termination`
   tactic says what the measure is.  Every definition of the port
   rests on one, so these come first.  The 132 equations of the
   tail recursions of the bignum library (`mc_multiword`) are of
   the same kind: HOL4 proves each with `mc_tailrecLib`, and the
   port has to unfold `SHORT_TAILREC` itself._
2. _the **definitions that the port does not make** (14 declared
   constants and 3 with a free variable, `PENDING.md`): each
   needs a decision or a missing piece, not a proof._
3. _the **theorems of the library theories** (`ml/lib/`), which
   the CakeML theories rest on and which are small and standard._
4. _the **theorems of the CakeML theories**, in the order of
   `tools/load.txt` (which is HOL4's own order), file by file: a
   theorem of a file only uses what the files before it and the
   theorems before it in the file give._

_What the port counts the whole time: `length (axioms ())`, which
`tools/bin/postrun` reports per run, and `ml/CHEATS.md`, which
says of every cheat what kind it is.  Phase three is done when
both say 3 and nothing._

## How a proof gets into the port

_Before writing one, read `PORTING-GUIDE.md`: the HOL4 idioms the
sources use over and over, what each one actually does, and the
tactic of the port that stands in for it -- with the versions that
did not work.  Every idiom that costs more than ten minutes gets an
entry there when it is solved, which is what keeps the next file
from paying for it again._

_`ml/` is generated, so a proof does not live there: it is a
section of `proofs/<path>.prf` that names the theorem of the HOL4
source, and `tools/port.py` splices it in where the `CHEAT_TAC` of
phase two stands (`tools/proofstore.py`; `tools/proofs.py` checks
that every section still names a theorem that the port states, the
one thing a re-port cannot show).  A theorem with no section keeps
its cheat, so the proofs come one at a time and a re-port never
loses one.  The termination of a definition is not a theorem of the
source: that tactic goes in `overrides.TERMINATION`, keyed by
(theory, the name of the block), where it already went._

_Working on a file means a session with the **needs closure of
that file** loaded (a clone of `hol-template-cakeml` and the
`needs` lines of the file: 529 s for `bvi_letProof`, against 4,131
s for the whole load order up to it).  The closure is the template
for the file, cloned per attempt; a change in `ml/lib` costs it
again, because `retemplate` rebuilds the clone tree._

## What the first file measured

_`compiler/backend/proofs/bvi_letProof.ml`, the first file of
phase three: 17 theorems, 118 lines of HOL4 tactic script (the
median file of the port has 183).  Nine of the 17 proved, every
proof timed from reading HOL4's to a verified HOL Light one:_

| | seconds |
|---|---|
| IMP_COMM, compile_CONS, compile_APPEND (1-3 lines of HOL4) | 25, 19, 9 |
| evaluate_delete_var_Rerr_SING, env_rel_LLOOKUP_NONE | 18, 46 |
| env_rel_REPLICATE_0, env_rel_LOOKUP_SOME | 95, 166 |
| dest_var_code_labels | 206 |
| env_rel_length (the first proof over a `match` definition; the
  two tactics below came out of it) | 700 |
| EL_DROP, a list lemma of HOL4 that HOL Light has not | 71 |

_Nine proofs and one library lemma: 1,355 s in all, median 71 s,
mean 73 s without the one that found the idioms.  One more
(`evaluate_delete_var_Rerr`, 10 lines of HOL4) was given 219 s and
is **not** done: it needs the case analysis of the BVI semantics,
which is the shape of the eight that are left in the file._

_Three things came out of the file that every other file needs:_

- _an overload that a source **brings to the front**
  (`bring_to_front_overload`) is part of what its statements say.
  Without it `compile` in `bvi_letProof` is `clos_mti_compile`:
  the statement reads, every check passes, and the theorem is
  about another constant.  `tools/port.py` writes the
  `hol4_overload` now, in 16 files; five calls of five more go
  through an ML helper of the source and get a pointer instead._
- _a definition keeps the name of its block, so 28 files of the
  port bind a `compile_def` and OCaml sees the one of the file
  that loaded last.  A proof names the definition it needs by the
  constant, which is unique: `cake_def "bvi_let_compile"`
  (`ml/lib/define.ml`)._
- _the eight that are left all turn on a `case evaluate (...) of`
  of the source, which the port writes as a HOL Light `match`.
  **This is the gate of phase three**, and not a detail of one
  file: the 228 CakeML sources use `every_case_tac`, `CaseEq`,
  `AllCaseEqs` or a `*CASE_TAC` **7,559 times, in 145 of them**,
  and they have 2,809 `case` expressions in the definitions and
  the statements that those tactics take apart.  An hour of
  trying to write the tactic for the port (four versions) says
  that HOL Light's encoding of a `match` resists it: `REPEATC`
  never fails, so a `MATCH_REDUCE_CONV` under a traversal does
  nothing; `MATCH_CONV` can return a no-change theorem, so a
  `REPEAT` of it spins; a scrutinee the patterns cannot decide
  becomes an epsilon term; and once one epsilon is in the goal
  the next reduction grows it without bound.  A fifth version
  works, and `EVERY_CASE_TAC` is in `ml/lib/tactics.ml` now: on the
  goal of `evaluate_SNOC_Rval` it does in 8 seconds what HOL4
  does.  What the four tries were missing, beside those traps: the
  **innermost** scrutinee first, the **equation kept** for a
  compound one, the impossible branches **closed at once** with
  the distinctness of that type (without which the goals multiply
  with every split), HOL Light's own `UNWIND_CONV` for the guard
  that `MATCH_CONV` leaves, and `VAR_EQ_TAC` (HOL4's `rveq`).
  `PORTING-GUIDE.md` entry 1 has it all, with the four tactics
  that did not work and why._
- _`MATCH_REDUCE_TAC` and `LIST_CASES_TAC` (`ml/lib/tactics.ml`):
  the definitions of the port are `match`es, and a proof that
  unfolds one has to reduce it and to take the right variables
  apart.  `MATCH_REDUCE_CONV` cannot be used under a traversal
  (`REPEATC` never fails, so `ONCE_DEPTH_CONV` stops at the top)
  and `LIST_SPLIT_TAC` takes every list variable of the match
  apart, which loses the one the induction hypothesis is about._

## Where the first file stands

_`compiler/backend/proofs/bvi_letProof.ml`: **all 17 of its theorems
are proved**, and the file adds **no axiom**.  It is the first file
of the port that is done.  What the proofs of this pass needed is in
`PORTING-GUIDE.md`._

- _`evaluate_env_rel` -- the correctness of bvi_let, which HOL4
  writes as `completeInduct_on` and **eleven `Resume` blocks**, 150
  of the file's 118 lines of tactic script (the Resume blocks are
  counted apart).  The port has the induction on the measure the
  definition was made with (HOL Light keeps no induction theorem for
  a definition, and `bvi_exp_INDUCT` does not reach a recursion on
  `BUTLAST`), and the eleven cases next to it.  The three that cost
  the work: **Let** (the tail-position move -- `SNOC` and its laws,
  `evaluate_SNOC`, `env_rel_MAP`, and the two `delete_var` theorems
  of the pass before), **Call** and **LetCall** (where the order of
  the case split decides whether the side conditions of the
  hypothesis are provable at all -- guide entry 14)._
- _`evaluate_compile_exp` is proved out of it at `ax = []` and
  `d = 0`, where `env_rel [] 0 env env` is `env = DROP 0 env`._

_`compiler/backend/bvi_let.ml`, the definition file that it is
about, is done too: **all five of its theorems are proved** and
**both of its definitions are made**, so the pass as a whole adds
no axiom.  The theorems are `exp2_size_APPEND` (which phase two
could only point at until the identification of HOL4's `exp2_size`
was checked), `compile_sing` by a mutual measure induction,
`compile_length`, `compile_HD_SING` and `compile_exp_eq` (one of
the two that HOL4 states as the value of an ML expression).  The
two definitions wanted three things and not one proof: the two
size facts of a recursion on `BUTLAST` and `LAST` in
`cake_term_facts`, a budget over the eight seconds a definition
gets before it is assumed, and HOL4's relation handed to
`define_single` instead of to the strategy chain of
`cake_define_gen`, which declares the constant in an earlier
strategy and then never reaches the relation.  `PENDING.md` has
the three and guide entry 17 has the hour that went into a wrong
diagnosis first._

_The five idioms that this pass had to settle, all in the guide:
`evaluate_def` with `fix_clock` removed (13), the order of a `case`
split (14), a non-empty list written as a `SNOC` (15), a session
loaded out of the port's order (16), and a definition the
machinery will not make (17).  The first took every record update
out of the file's proofs; the second is the rule that a condition
of a branch is decided before the induction hypothesis is used
inside it; the last two are both the same lesson, that a test bed
built by hand lies about what is wrong -- once about the overloads
and once about which names are constants._

_What the pass added to the machinery, all of it reloadable in a
second: `NAMED_CASES_TAC` (a case split under names of the proof's
own, which the goals of `EVERY_CASE_TAC` cannot give),
`COND_SPLIT_TAC`, `CASE_SPLIT_TAC`, `RECORD_CASES_TAC`,
`ASM_FS_TAC`, `RULE_ASSUM_TRY`, `PRUNE_TAC`, `SPLIT_ASM_TAC`,
`RES1_THEN`, `RES2_THEN`, `SOLVED`, and in `ml/lib/lemmas.ml` the
`oEL` and `list_size` lemmas that HOL4 takes from its own
libraries._

## Where the second file stands

_`compiler/backend/proofs/bvl_constProof.ml`: **all 23 of its
theorems are proved**, the one that HOL4 states as the value of an
ML expression (`compile_thm`) with them, and the file adds **no
axiom**.  `compiler/backend/bvl_const.ml`, the definition file it
is about, is done too: **all eleven of its theorems are proved**
(the seven `pmatch` restatements, `compile_eq`, `compile_length`,
`compile_HD_SING` and `compile_exp_eq`) and **its `compile` is
made** with the relation of `DEFINE_REL`, so the pass as a whole
adds no axiom.  The two files verify in a closure built from their
own `needs`: `AXIOMS-ADDED 0`, no error and no warning._

_It was picked because bvl_const is the same transformation one
language up -- its own comment says "bvi_let is a simpler version
of this optimisation" -- so it is the test of whether the recipe
of `PORTING-GUIDE.md` carries.  It does, for the shape: the three
`delete_var` theorems transferred with the names changed, and so
did the definition file's four theorems and the skeleton of
`evaluate_env_rel` (the measure induction, the cases, the
`deep_case` loop).  What it does not carry is what the pass does
that bvi_let does not: **the constant folding**.  `SmartOp2_thm`
alone was two thirds of the work of the file, and it brought six
idioms to the guide (18 to 23): a relation that HOL4 states as
clauses and the port as one match, an argument a definition uses
only for its length, `do_app` as one match over every operation,
the arguments of a binary operation (the semantics gives `do_app`
the `REVERSE` of them), `MAP_FIRST` evaluating its list eagerly,
and the arithmetic of a folding that is a ring identity and not a
linear one._

_What the file's proofs are made of, beyond the recipe: the clause
form of `env_rel` and of `v_rel` (which every proof of the file
starts with), an index lemma that says where the compiled
environment holds the value of a variable, a lemma that says an
entry which is not a `Var` evaluates to that value whatever the
state, the evaluation of an operation of one and of two
expressions, the clause of `do_app` for the integer operations and
the two it compares (`El` against `ElemAt`, `Equal` against
`EqualConst`), and nine folding lemmas whose atoms the proof names
because `EVERY_CASE_TAC`'s are its own._

## Where the third file stands

_`compiler/backend/proofs/data_to_word_memoryProof.ml`, the memory
invariant of data_to_word: **410 of its 611 theorems are proved**
and 201 are still a cheat (213 `CHEAT_TAC` lines, the rest of them
the definitions and terminations), so the file adds 213 cheats
where it added 340 when phase three began.  It is the largest proof
theory of the port (11,000 lines, 625 blocks that need a proof),
and it was taken because every later file of data_to_word rests on
its `memory_rel`._

_What the proofs of this file are made of, beyond the recipe of
the guide: `MEMORY_REL_TAC` and `V_INV_TAC` (the invariant
unfolded and the rule of `v_inv` taken apart, guide entry 24), the
`v_inv_ck` machinery and `v_inv_def` that the whole `v_inv` family
goes through, the mutual induction of `dataSem_v` for the values
of a value (entry 28), `WORD_NUM_BIT_TAC` for a bitwise identity
of numerals at a dimindex that is not known, `ARITH_NO_BIT_TAC`
and `ARITH_NO_DIV_TAC` for a goal whose context is half
arithmetic, and the word-bit toolkit of HOL Light
(`WORD_EQ_BITS_ALT`, `BIT_WORD_*`, `WORD_ADD_OR`,
`BIT_WORD_POW2`).  `ALL_IMP` carries a property along an `EVERY`,
`MEASURE_INDUCT_TAC` stands for HOL4's `recInduct`, and
`var_by_name`/`CASES_BY_NAME` of `ml/lib/tactics.ml` take a
variable out of the goal where a quotation would invent one._

_Two toolkits were built for whole families of the file, and each
one unlocked its family in an afternoon:_

- _**the bytes of a word.**  `bsb0` reads a bit of a `set_byte`
  off (`bit j (set_byte a b h bb)` is the bit of `b` inside the
  byte's range and the bit of `h` outside it), `bixval` says the
  byte index of a number below the bytes of a word is eight times
  it (or eight times its mirror), `wobbit` says the bit of
  `word_of_byte (w2w w)` at j is the bit of `w` at `j MOD 8`, and
  `MOD_8_SUB`-style facts turn the index inside a range into the
  one modulo eight.  The bit-level proofs then go by the **byte
  ranges** (four or eight of them), never by the 32 or 64 bits:
  `set_byte_eq_ARB`, `set_byte_all_32`, `set_byte_all_64`,
  `word_xor_set_byte`, `word_of_byte_set_byte_32`,
  `word_of_byte_set_byte_64`, `set_byte_word_of_byte` and
  `set_byte_sort` are all done that way, and the toolkit is in
  `tmp/toolkit.ml` for the sections that still need it
  (`byte_index` lives in `ml/lib/byte.ml`, outside the preamble,
  so these lemmas cannot go to `ml/lib/lemmas.ml`)._
- _**the separation logic of the memory.**  `ml/lib/set_sep.ml`
  now has the ten theorems of HOL4's `set_sepTheory` that a proof
  needs: `SEP_EXISTS_THM`, `cond_STAR`, `STAR_cond`,
  `SPLIT_LEMMA`, `one_STAR`, `IN_fun2set`, `read_fun2set`,
  `write_fun2set`, `STAR_AC` (the permutative rewrite that stands
  for HOL4's `fs [AC STAR_ASSOC STAR_COMM]`) and `STAR_SEP_T`.
  `read_fun2set` and `write_fun2set` are HOL4's `SEP_R_TAC` and
  `SEP_W_TAC` as a rule each, applied by hand to the assumption.
  With them `word_list_exists_thm`, `store_list_thm`,
  `word_el_IMP_word_list_exists`,
  `word_heap_IMP_word_list_exists` and
  `word_list_AND_word_list_exists_IMP` are proved, and the rest of
  the `word_list_exists` family is open rather than blocked._

- _What it cost to find: a term that a tactic writes gets the
  parser's types, and an arithmetic one gets an invented type
  variable that no later step matches (entry 25); a theorem of the
  port is instantiated **at the goal** with
  `INSTANTIATE (term_match [] (rand (concl th)) w) th` (entry 25,
  way 4), because two statements never share an invented variable;
  a statement of the port may have **two** invented type variables
  where a reader sees one (the address word and the contents of
  `word_list`), so an `aux` lemma that stands in for it needs both;
  a `REWRITE_RULE` inside a `FIRST_ASSUM` never fails, so the
  wrong assumption is taken and the failure comes five lines later
  (entry 29: `USE_CHANGED`); a match whose scrutinee is a call
  needs `EVERY_CASE_TAC` before any reduce (entry 26);
  `MATCH_ACCEPT_TAC` fails where `ACCEPT_TAC` works, and it needs
  the goal's quantifiers stripped first; `SPEC` of a lemma with a
  type variable has to be `ISPEC`; the `&` of a quotation is a
  **real** and its `<` is a **word's** unless the quotation says
  `:int` or `:num` (entry 25); `lhand` of `ALL P l` is `P`, not
  what `rand (lhand ...)` gives; `REPEAT VAR_EQ_TAC` loops
  (entry 3); a `THENL` after a tactic that branches needs
  brackets round it; and a `STRIP_ASSUME_TAC` of a disjunction
  multiplies the goals, where `MP_TAC` and a `STRIP_TAC` after it
  do not._
- _What is blocked, and why: `do_eq_list_F_IMP_MEM`,
  `memory_rel_ptr_eq` and `do_eq_IFF_vb_eq_size`, on the
  inconsistent `do_eq` of ISSUES.md (its clauses as the port
  assumes them prove `Eq_val T = Eq_val F`, so a proof through
  them would be worthless);
  `memory_rel_elements_list_distinct`, on the `TL` of HOL Light
  that has no value for the empty list (ISSUES.md, "The empty list
  that HOL4's TL has a value for"); the
  `vb_eq_size`/`list_copy_fwd`/`finalise_cons`/`word_eq` family,
  on HOL4's `recInduct` of a `cake_define_wf` definition, which
  `MEASURE_INDUCT_TAC` can stand for once the measure's decrease
  is a lemma (for `finalise_cons` that is `sptree_size (delete ptr
  refs) < sptree_size refs`); `memory_rel_FromList` and the rest
  of the `copy_list` family, on `copy_list_thm`, which HOL4 states
  as the value of an ML expression and the port therefore has only
  as a pointer (`PENDING.md`) -- a proof of one of them has to
  state and prove it as a local lemma first; and
  `gc_move_data_refs_split`, where the `let` of a pair pattern
  inside the definition of `gen_gc$gc_move` is not reduced by
  `let_CONV` and `PAIRARG_TAC` together, so the pair equation of
  the state stays unsplit._

## The sessions of phase three

_What loading costs, measured: the whole port in load order 5,656 s
(94 min, 21 s a file); the `needs` closure of one file 485 s on
average (802 s for a proof theory); a clone of a loaded session 1 s;
`tools/bin/reload` of the tactics and the lemmas under a second.
One closure per file would be **36 hours** over the 270, so the work
goes in load order in **one frontier session** (`tools/bin/frontier`,
`hol-front`), which is cloned for every attempt and never typed in._

_A clone is a fork of the session it comes from, so killing one kills
its clones: `hol-front` hangs off `hol-base` and loads the preamble
itself, because a clone of `hol-template-cakeml` dies whenever the
template is rebuilt._

_Where a utility function goes decides what it costs: a tactic in
`ml/lib/tactics.ml` and a shared lemma in `ml/lib/lemmas.ml` cost a
second (`reload`), because those two files define nothing; a lemma
that one proof needs stays in that proof; and anything that defines
something (`ml/lib/hol4.ml`, `ml/lib/define.ml`) costs the session,
so it is batched and done between files.  `SESSIONS.md` has the
table and the commands._

_What is still missing is a checkpoint on disk.  HOL4 has it
(`HOLHEAP`, Poly/ML's `SaveState`, which is how CakeML's bootstrap
starts from `cv_translator/cake_compile_heap`); HOL Light has no
equivalent, but `DMTCP` or `criu` can snapshot the process, and a
snapshot restores in seconds and survives a crash or a reboot, which
the fork tree does not.  Worth a spike before the long haul._

## Trying a batch of proofs in one load of the session

`tools/bh.ml` (loaded into the working session) is what a round of
phase three looks like now.  A round is one file with several
attempts in it:

- `bt <name> <thm> (fun () -> <tactic>)` tries an attempt under a
  processor-time budget.  When it fails it prints the exception
  and, if the tactic merely left goals, the goals themselves, and
  then the next attempt goes on; nothing an attempt does reaches
  the next one, so a failure costs only its own line of the log.
- `bsteps <name> <thm> [<tactic>; ...]` applies the steps of a
  proof one at a time and says which one failed and what the goal
  state was, which is what the interactive `e` used to be for.
  Each step goes to the first goal, as `e` does.
- `b_open <file>` sends everything to a log file as well, which
  has no scrollback limit (the tmux pane has one), and `b_asm`
  turns the assumptions of the printed goals on.

So one round of the REPL -- a minute or two -- gives the feedback
of a whole batch instead of one step of one proof.  The attempts
of a round are written as `tmp/*.ml` files with `pt` (the same
thing as `bt`) so that `tmp/mksec2.py` can turn a successful one
into a section of the `.prf`, inlining the pieces of
`tmp/toolkit.ml` that it uses.  A section that binds what it does
not use is a warning, so the toolkit is one piece per binding and
a section asks for exactly the ones it needs.

## Where the third file stands after the batch rounds

424 of the 611 theorems are proved and 184 cheats are left.  What
the rounds of this pass added, in the order they went in:
memory_rel_Number_bignum_header, word_mem_eq_thm, write_bytes_same,
memory_rel_IMP_word_list_exists, v_inv_Block_tag_limit,
heap_lookup_BlockRep_lemma, memory_rel_ByteArray_words_IMP,
memory_rel_ValueArray_IMP, memory_rel_Block_IMP,
memory_rel_space_max, memory_rel_El_any, memory_rel_Number_EQ,
memory_rel_ByteArray_IMP_store, memory_rel_El' and
memory_rel_Deref'.

- _What the family of El/Deref/Update costs:_ the primed ones
  (`memory_rel_El'`, `memory_rel_Deref'`) are the ones with the
  separation logic in them, and they are done.  The unprimed ones
  carry the index as a `Number` of the stack, and a proof of them
  out of the primed one needs the index to be small, which comes
  from the Block's (or the array's) length -- and the theorems
  that say that (`memory_rel_Block_IMP`,
  `memory_rel_ValueArray_IMP`, `memory_rel_Number_IMP`,
  `memory_rel_swap`) all stand **later** in the file, so a section
  may not use them (`tools/prfcheck.py` says so).  Both proofs
  exist and were thrown away for that reason.  What the source
  does instead is read the bound off the `cond` of the `word_el`,
  which the separation part of the proof has in its hands
  anyway:
  so the unprimed ones are the primed proof again with the
  Number's root taken apart as well, and that is the next thing to
  write.
- _What was blocked, and what was done about it:_ the four things
  that stood in the way are **fixed in the port** and the
  theorems that waited for them are ordinary work again.
  `do_eq` and `do_eq_list` of the five semantics are written as a
  match, so their clauses are consistent (they were not, and the
  cheat of the definition made them axioms);
  `data_space.ml` overloads `num_size`, so the statements that
  mention it mean the source's function and not HOL4's size
  function; `ml/lib/hol4.ml` has HOL4's total `TL` and the
  preamble gives the name to it; and `copy_list_thm` is not
  missing from the port -- HOL4 states a general lemma and
  specializes it with ML, so the general one belongs inside the
  proof of `memory_rel_FromList`, which is work and not a block.
  What is still blocked: `vb_eq_size_IMP_vb_size` and
  `finalise_cons_none` on the induction theorem of a HOL4
  `Definition`, which the port's `cake_define_list` does not
  make.
- _What the gc's `data_refs_split` family needs:_ the proofs are
  short in the source (`EVERY_CASE_TAC` and a `metis_tac`), and
  the port gets as far as the cases of `gc_move`; what is left is
  the accessors of a record over its updates
  (`gc_state_h2 (gc_state_ok_fupd (K F) s)`), which the port has
  no simp set for.

## Where the third file stands after the repair of the pass

_The rework of the shape cost the port a week of small repairs,
which the harvest in the file's own place found one after the
other (PORTING-GUIDE.md, entries 9, 32 and 33).  All of them are
in now and the memory file loads with 160 axioms and no failure._

_Of its 611 statements 154 still have a cheat.  Eight went in the
round after the repair:_

- _the three `reachable_refs` lemmas of an update of a reference
  (a path through the new references is an old path or starts at
  a root of its own, by induction along the reflexive transitive
  closure);_
- _`reachable_refs_MutBlock_UPDATE`, the same of an update of a
  MutBlock's centre;_
- _`heap_store_unused_thm` and its `_alt`, where the split is as
  long as the space, so what is left of it after the unused
  element is empty and `heap_store_lemma` says what the heap
  becomes;_
- _`update_ref_gen_state_ok` and `update_thunk_gen_state_ok`, two
  stores above the generations, which keep `gen_state_ok` because
  `heap_split_heap_store` gives the same first half._

_What is next, and what the half-finished attempts are:_

- _`gen_state_ok_update_byte` and `unused_space_inv_byte_update`
  replace the contents of a `Bytes` element by another of the same
  length.  The lemma they both want is in
  `tmp/next-split_replace.ml`: a split of a heap in which one
  element is replaced by one of the same length gives the halves
  of the old one, up to that element.  Its case analysis is done
  (every branch closes) but the one tactic that closes them all is
  not: the witnesses of the existential are read off the goal's
  own equations, and in one branch of `heap_split` the shape is
  another one.  Finish it branch by branch._
- _the four attempts of the earlier waves that the round left
  unproved: `write_bytearray_append` (MATCH_MP of a statement that
  is not an implication yet), `gc_move_refs_data_refs_split` and
  `gc_move_data_data_refs_split` (a MESON that is too deep), and
  `memory_rel_bignum_cmp` (over the budget)._
- _a proof may only name what the port has: the helpers of the
  scratch prelude (`hd_is`, `grab`, `hlen_cl`) are defined inside
  the section that uses them, which is what the sections of the
  store do._

## The wave of 2026-10-25

_Eighteen proofs, in five families, and the loop that
`~/.claude/.../memory/proof-loop-speed.md` asks for: the closure
session stays, a scratch layer holds what a proof under development
needs, and a batch of proofs costs one regeneration and one
`verifyquick`._

- _the finalised MutBlock on the stack: `all_vs_MutBlock_T` and
  `reachable_refs_MutBlock_T` (the payload of the cell moves into
  the new Block, so the values and the edges are the old ones);_
- _the six lemmas about a change of the refs
  (`v_inv_ByteArray_insert_lemma`, `v_inv_ValueArray_insert_lemma`,
  `v_inv_MutBlock_insert_lemma`, `v_inv_MutBlock_fin_lemma`,
  `v_inv_MutBlock_hole_lemma`, `v_inv_new_Thunk_insert_lemma`),
  which share the complete induction on the clock of the relation
  (`V_INV_REFS_TAC` of `overrides.EXTRA_BEFORE`) and differ only in
  the four facts about the lookups of the new refs;_
- _the collector's data/refs split: `gen_gc_data_refs_split` and
  `gc_move_refs_data_refs_split` (an induction on the list that r2
  is, because the port has no induction theorem of the
  definition);_
- _`gc_move_data_data_refs_split`, the third of the collector's
  family, whose recursion is on the measure
  `limit - heap_length h1` and whose element comes out of `h2` of
  the state **after** the move of its list: a complete induction on
  that measure, with the port's `TL` (which HOL4 has at the empty
  list as well);_
- _the four lemmas about `v_inv` and a **heap** that changes, which
  the same induction does with a heap tactic
  (`V_INV_HEAP_PLAIN` and `V_INV_HEAP_THUNK` of the shared block):
  `v_inv_BlockRep_upd_lemma` (every lookup is away from the
  BlockRep at p), `v_inv_Ref_lemma` (the heaps agree on everything
  that is no RefBlock), `v_inv_IMP_lemma` (a store into a byte
  array, where `heap_lookup_replace` carries the lookups over) and
  `cons_thm_EMPTY` (the empty Block, whose root is a Data);_
- _`reachable_addresses_related`: the path of the old heap is a
  path of the new one, address by address (an RTC induction);_
- _`num_eq_thm`: the root of a small integer is the word of four
  times it, and four times a small integer is within the range of
  the word, so the word determines the integer._

_What is open:_
- _`ml/lib/hol4.ml` now defines `IS_PREFIX` (ISSUES.md): the
  sessions were built before it, so a `tools/bin/retemplate` and a
  `tools/bin/pfbase` are owed before the next whole run.  Nothing
  of the memory file uses it, so the proofs of this wave were
  verified without it._

## Every statement of data_to_word_memoryProof has an attempt

The 115 statements of
`compiler/backend/proofs/data_to_word_memoryProof.ml` that are not
proved yet no longer stand as a bare `CHEAT_TAC`.  Each carries the
attempt that its source proof suggests -- the facts the HOL4 proof
names, rewritten with and then closed by arithmetic or by MESON --
under `ATTEMPT_TAC 5` of `ml/lib/tactics.ml`, which gives the
attempt five seconds of processor time and falls back on the cheat
when it does not close the goal.

So what is left to do is in the port and not in a list beside it:
the attempt of a statement is where its proof gets written, the
facts it names are the ones the source proof uses, and
`length (axioms())` still counts exactly the statements that are
not proved -- an attempt that starts to go through takes its cheat
away by itself.

What it costs is the load: an attempt that fails fast costs
nothing, and the twenty or so that search cost their five seconds
each.

## The bytes of a word, and nine proofs of 2026-10-26

Nine of the statements of
`compiler/backend/proofs/data_to_word_memoryProof.ml` that carried
an attempt carry a proof now (115 of them were left, 106 are), and
`verifyquick` loads the file in 724 seconds with 152 axioms, six
fewer than the round before it:

- `write_bytearray_append`: the load that the statement assumes at
  the first byte makes its store go through, so both sides take the
  `SOME` branch of the match;
- `xor_bytes_bytes_to_word` and `xor_bytes_xor_words`: the xor of
  two words is the word of the xor of the bytes;
- `set_byte_bytes_to_word` and `get_byte_bytes_to_word`: where the
  source takes the list of bytes apart into the four or the eight
  bytes of a word, one lemma does it for every length, by the
  induction of `bytes_to_word` over the list;
- `write_bytes_change_extra` and `write_bytes_inj`: the words that
  a list of bytes fills, with `DIV_SUB_STEP` for the count;
- `list_to_BlockReps_Pointer_lem` and
  `bc_stack_ref_inv_MutBlock_centre`: a pointer of a block of a
  list, and the centre of a MutBlock on the stack of the
  invariant.

Three things came out of them that outlast them:

- `ml/lib/lemmas.ml` has `DIV_SUB_STEP` and `DIV_SUB` (HOL4's
  `DIV_SUB` of `arithmeticTheory`): taking the bytes of one word
  off the front of a list takes one off the count of the words it
  fills, which every proof about `write_bytes` needs;
- `overrides.py` puts a block of the port's own before
  `get_byte_bytes_to_word`: `slice_shl`, `ushr_small`,
  `align_small` (the address of a byte of the first word is
  aligned to it) and `ne_small` (two of them are different words),
  which is what the lemmas about `set_byte` and `get_byte` share;
- `ml/lib/tactics.ml` has `in_goal`, which takes a subterm of the
  goal or of one of its assumptions, because the types of the goal
  are not the types a term written by hand gets.

Entries 40 to 42 of `PORTING-GUIDE.md` say what cost a run to find:
the epsilon term that `MATCH_CONV` leaves and the three steps that
take it apart, the type variable an inner lemma has to be stated
with for `SPECL`, and the three ways a tactic loses what it was
given.

## The inconsistent definitions of the port

`vb_eq_size` of `data_to_word_memoryProof` was assumed as a list of
clauses of which the last one,
`vb_eq_size _104 _105 _106 = NONE`, catches the pairs that the
earlier ones have already given a value.  As a conjunction that is
inconsistent, and `|- false` follows from it in four steps:
instantiate the catch-all at `(Number n1,Number n2)` and compare it
with the clause above it.

`ISSUES.md` said already that the port writes an overlapping
definition as one clause with a `match` and that `overlapping` of
`tools/port.py` finds the overlaps itself -- but it gives up as
soon as the clause list defines more than one function ("a match is
one clause, so it cannot define a family"), and that is exactly the
shape in which the sources write a mutual recursion with a
catch-all clause per function.  `do_eq` of the five semantics was
put in `MATCH_CLAUSES` for that reason; `vb_eq_size` is there now
as well, and the file loads with 149 axioms instead of 152.

A scan of the axioms of the closure (2613 of them) finds five more
of the same shape, in other files: `vs_depth` of `dataSem`, `do_eq`
and `pmatch`/`pmatch_list` of `semanticPrimitives`, `pmatch` of
`pattern_semantics` and `has_Eval` of `flat_elim`.  Each is one
`MATCH_CLAUSES` entry and a run of its file; `ISSUES.md` lists them
with what follows from each.  (The scan also flags thirteen
definitions of the `*_sing`/`*_list` shape, where the catch-all
clause and the specific one agree -- those are consistent, only
redundant.)

The scan itself is four lines of the session: an axiom is
suspicious when its clauses, grouped by the function each defines,
give one function both a clause whose arguments are all variables
and another clause.

## The round of 2026-10-26, after the nine

Three more proofs of `data_to_word_memoryProof` are in, and the
file stands at 103 unproved statements of 611 (147 axioms added,
702 seconds):

- `bc_stack_ref_inv_gc_related_roots_heap`: the two maps of the new
  invariant are `g f_o_f f` and `g f_o_f tf`, so `ml/lib/lemmas.ml`
  now has what the composition of two finite maps is
  (`FMAP_FN_f_o_f`, `FAPPLY_f_o_f` and HOL4's `f_o_f_DEF`);
- `memory_rel_RefPtr_EQ`, from the round before it;
- `finalise_cons_none`, the first proof of the port that needed an
  induction of a definition that the port does not have.

`PORTING-GUIDE.md` entries 44 to 47 are what that last one cost:

- 44: the complete induction on the measure to write where HOL4
  takes `foo_ind`, the decrease as the one real lemma, and that a
  lemma about a tree cannot stand in `ml/lib/lemmas.ml`, because
  `ml/lib/preamble.ml` loads that file before `ml/lib/sptree.ml`;
- 45: `MATCH_CONV`'s guard has the pattern on the **left**, so
  `distinctness` needs its `GSYM`s as well (and `case_rws` of
  `ml/lib/tactics.ml` has only the one orientation);
- 46: a rewrite with a recursive definition in *every* assumption
  opens the call of the induction hypothesis as well, and the
  proof dies of a stack overflow several steps later;
- 47: the file's own `let is_cond` (line 24033) shadows HOL
  Light's, so a tactic of a proof earlier in the file behaves one
  way in the file and another in the session that writes it.

### What is next

`bc_ref_inv_related`, with the four arms of `bc_ref_inv` as a
lemma each (entry 43's advice: derive the clause once), and then
the lemmas that the collection theorems share: `v_inv_related_lemma`
and `bc_stack_ref_inv_gc_inline`.

A by-product to pick up: `lookup_zero` of `ml/misc/misc.ml` is
assumed and the proof of it is now written (it stands in
`finalise_cons_none`); the same holds for the termination of
`dataSem`'s `finalise_cons`, which is `size_delete_LESS` and the
measure HOL4 gives.  Both are a cheat of another file, so they wait
until this file is done.

## update_ref_thm, and the three theorems after it

`update_ref_thm` is proved (99 of the 611 sections of
`data_to_word_memoryProof` are unproved now), and its machinery
stands in the `EXTRA_BEFORE` block of its statement
(`tools/overrides.py`), because the three update theorems after it
(`update_ref_thm1`, `update_thunk_thm`, `update_mutblock_thm`,
`update_byte_ref_thm`) take the same steps and share it:

- the heap after a store into a RefBlock: `roots_ok_iso`,
  `heap_ok_store_ref`, `unused_store_ref`, and for the kind of the
  collection `heap_split_store_ref` and `gc_kind_store_ref`;
- the timestamps cut down to the ones of the new stack:
  `DRESTRICT_DEF` (HOL4's), `INJ_DRESTRICT`, `INJ_SUBSET_DOM`,
  `IMAGE_DRESTRICT_NOT`;
- what reaches a reference: `reach_refptr`; the lists:
  `LIST_REL_APPEND_IMP`, `EVERY2_MEM_MONO`, `mem_zip_left`,
  `mem_zip_right`;
- the transfers of `v_inv` over the update, for a value of the
  stack, for one inside a reference and for any value of the new
  references: `v_inv_update_ref`, `v_inv_update_ref_ref`,
  `v_inv_update_ref_vs`, with `MEM_ref_all_vs`,
  `MEM_thunk_all_vs`, `MEM_mutblock_all_vs` for the memberships and
  `EVERY2_v_inv_update_ref` (and `EVERY2_ARM_TAC`) for a list of
  them;
- the four arms of `bc_ref_inv` from the two lookups (`USE_ARMS`
  over `arm_VA` .. `arm_MB` of the earlier block), the pickers of
  the assumptions that each arm goes by (`a_ri`, `a_tr`,
  `a_lkptr`, `a_lknew`, `a_hlold`, `a_hlnew`, `a_neq`), and
  `REDUCE_MATCH_HARD` for a match that the patterns cannot decide;
- and the two cases themselves: `bc_ref_inv_update_ref_at` for the
  reference written (its invariant is the array of the new values)
  and `bc_ref_inv_update_ref_other` for any other one (its element
  is where it was, because the store only touched the address of
  the one written, which `INJ_FAPPLY_NEQ` tells apart), with
  `bc_ref_inv_FLOOKUP` for the address that the invariant of a
  reference has.

`update_ref_thm1`, the store of one value of the array, is proved
as well, from the same shape of proof with `LUPDATE` in place of
the whole array: its own lemmas (`MEM_HD`, `EVERY2_HD`,
`ptrs_store_LUPDATE`, `reach_refs_update_ref1`,
`bc_ref_inv_update_ref_at1`, `a_pos`) are in the `EXTRA_BEFORE`
block of its statement, and the three theorems of HOL4's
`listTheory` that it names (`LENGTH_LUPDATE`, `MEM_LUPDATE_E`,
`EVERY2_LUPDATE_same`) are in `ml/lib/lemmas.ml`.  The lemmas of
the shared block name the array that is written `vls`, because a
proof whose own `xs` is another list cannot aim a lemma whose free
variable is `xs` (PORTING-GUIDE.md entry 55).

`update_thunk_thm` is proved as well, and with it the block of
`update_ref_thm` has been turned round: the lemmas that do the work
now take the three transfers that an update of the references
leaves -- what the invariant says of a value, what a value says of
a thunk, and what the references hold at another key -- as
hypotheses (`v_inv_update_gen`, `EVERY2_v_inv_update_gen`,
`bc_ref_inv_update_gen`, `bc_ref_inv_update_other_gen`), and the
kind of the update only has to say what its three transfers are
(`VA_trans` for an array of values, `TH_trans` for a thunk).  The
four arms of `bc_ref_inv` are gone through once, in
`bc_ref_inv_update_gen`, for every update.

So what is left of the four is `update_mutblock_thm` (a store into
a mutable block, HOL4 `data_to_word_memoryProofScript.sml:5609`)
and `update_byte_ref_thm` (a store into a byte array, `:5934`),
which replaces the element of the heap in place instead of storing
into it.

## Where to pick up (97 of the 611 sections unproved)

The last verify of the file: `AXIOMS-ADDED 140`, `OWN-AXIOMS 15`,
753 s, no load error.  One warning (`unused variable gl`, a binder
of the proof of `update_thunk_thm`) is put right since, so the next
`tools/bin/verifyquick` of the file has to report no warning at
all; that is the only thing still owed on what is in.

`update_mutblock_thm` is the next one, and it is
`update_thunk_thm`'s proof with a mutable block for the thunk:

- the stack is `h :: RefPtr F ptr :: stack` again, so
  `SPLIT_ROOTS_TAC` twice, and the root of the pointer comes from
  the **first** of the three ways a pointer is related (the
  reference is no thunk, and `~b` holds because the block is
  unfinalised), not the second;
- the element is `BlockRep tag vs1` and the store writes
  `BlockRep tag (LUPDATE rr (LENGTH l) vs1)`, with HOL4's
  `heap_store_BlockRep`;
- the three transfers are an `MB_trans` over HOL4's
  `v_inv_BlockRep_upd` (which needs that no timestamp points at the
  cell, from the unfinalised block's own arm) and
  `v_inv_MutBlock_hole`, with a `dest_thunk_insert_MutBlock` that
  takes the steps of `dest_thunk_insert_ValueArray`;
- `gc_kind_inv` is free: the arm of a mutable block says the
  collection is not a generational one;
- the heap: `heap_ok_store_el` again, with the pointers of the
  element written from `MEM_LUPDATE_E` -- which asks for
  `ptrs_store_LUPDATE` to be restated for an element that is any
  `DataElement zs l2 d2` (it is stated for a `RefBlock zs` now) and
  for the written root to be given as `MEM w roots` rather than as
  the head of the roots of a stack prefix;
- the arm of the reference written needs `l ++ [h] ++ r =
  LUPDATE h (LENGTH l) (l ++ [cv] ++ r)` (HOL4's `LUPDATE_LENGTH`)
  and `blocks_unique_update_mutblock`,
  `reachable_refs_MutBlock_UPDATE`.

`update_mutblock_thm` is proved as well, from the same shape of
proof with the hole of a mutable block for the thunk: its own
lemmas are in the `EXTRA_BEFORE` block of its statement
(`IMAGE_NOT_point`, `gc_kind_not_gen`, `v_inv_BlockRep_upd` derived
from HOL4's lemma, `dest_thunk_insert_MutBlock`, `ptrs_store_el`,
`MB_trans`, `bc_ref_inv_update_mutblock_at`), and HOL4's
`LUPDATE_LENGTH` is in `ml/lib/lemmas.ml` with the other three
theorems about `LUPDATE`.

`update_byte_ref_thm` is proved as well, and with it **all five
update theorems**.  It is the one that does not go through
`heap_store`: the store writes an array of bytes of the length it
replaces, so the heap is given as an append (`h1 ++ [Bytes be fl ys
ws] ++ h2`) and the proof needs its own account of it.  Its block
(the `EXTRA_BEFORE` of its statement) holds, in the order it needs
them: `byte_heap` and `byte_heap_not` (the pickers that read a
heap of such a store off a term, entry 59), `samelen_bytes`,
`isSomeDataElement_Bytes` and `isSomeDataElement_byte_update`,
`heap_ok_byte_update`, `dest_thunk_insert_ByteArray`,
`ByteArray_in_domain`, `reach_refs_update_byte`, `BA_trans`,
`heap_lookup_at`, `heap_split_replace2`, `isRef_Bytes`,
`gc_kind_byte_update`, `APPEND_SINGLE`,
`ref_ptr_annot_ByteArray`, `heap_lookup_other_replace`,
`heap_lookup_byte_other` and `bc_ref_inv_update_byte_at`; HOL4's
`APPEND_EQ_APPEND` is in `ml/lib/lemmas.ml` with the other
theorems of `listTheory` that the port needs.

The hard one of those was `gc_kind_byte_update`: in the
generational case `gc_kind_inv` asks for a split of the heap whose
first half holds no reference and whose second holds only
references.  The element replaced is in the first half
(`heap_lookup_at` says the heap holds it at `heap_length ha`,
`heap_lookup_heap_split` says a lookup lands in the half its
address falls in, and `EVERY isRef h2` keeps a byte array out of
the second), so `heap_length ha < e`; then `heap_split_replace2`
gives the split of the new heap with the same second half, over
`heap_split_heap_length`, `APPEND_EQ_APPEND` and
`heap_split_length` of `gen_gc_partial`.  Two routes that are dead
ends as they stand: rewriting with `heap_split_APPEND_if` and
bashing the case tree (a false goal is left, and MESON goes
"solve_goal: Too deep"), and strengthening the port's
`heap_split_replace` (its `CONV_TAC TAUT` endgame carries no
conjunct about the second half).

What the five cost: `verifyquick` of the file is **783 seconds**
with `AXIOMS-ADDED 102` and `OWN-AXIOMS 15`, where the round
before the byte array was 741 seconds and 103.

## Where to pick up (89 of the 611 sections unproved)

The round of 2026-10-27 landed, in this order:
`update_byte_ref_thm` (the last of the five update theorems),
`memory_rel_bignum_cmp`, `gc_kind_update_Ref`,
`abs_ml_inv_stack_permute`, `word_ml_inv_rearrange`,
`IMP_heap_store_unused` and `IMP_heap_store_unused_alt`.  Each one
verified: `AXIOMS-ADDED` went from 103 to 96 and the file loads in
about 690 seconds.

What that bought, beyond the seven theorems:

- the **stack layer**: `abs_ml_inv_stack_permute` keeps the heap
  and the references and changes only the stack, so the four
  `*_restrict` lemmas (`v_inv_restrict_gen`,
  `EVERY2_v_inv_restrict`, `EVERY2_v_inv_restrict_gen`,
  `bc_ref_inv_restrict`) are in the port now, and
  `word_ml_inv_rearrange` -- which `memory_rel_rearrange`,
  `memory_rel_tail` and `memory_rel_rotate3` were all proved from
  as a cheat -- is a theorem.
- the **allocation layer**: both stores into the unused space are
  proved, with thirteen lemmas about the regions of such a store
  (the element at one end, the space that is left at the other,
  the heap outside the space, no data inside it, the addresses
  that hold data, the elements the heap keeps).  Everything that
  allocates goes through them: `new_ref_thm`, `new_thunk_thm`,
  `cons_thm_alt`, `word64_alt_thm`, `bignum_alt_thm`,
  `mutcons_thm_alt`, `new_byte_alt_thm`.

So the allocation family is what to do next, and the way to do it
is to read two of them side by side first (`mutcons_thm_alt` is
the shortest at 87 lines of HOL4, `cons_thm_alt` the one the
others are written after at 138) and to put what they share in one
block, as the update theorems' shared block was put together.

What the rest of the file needs, by layer (the count is the lines
of the HOL4 proof):

- **no induction, no separation logic**: 48 of the 89, among them
  `get_real_addr_get_addr` (58), `deref_thm` (97),
  `v_inv_list_to_v_lem` (95), `bc_stack_ref_inv_MutBlock_F` (115),
  the four `word_copy_*` (63-92) and the GC theorems
  (`gc_combined_thm` 22, `full_gc_thm` 34, `gen_gc_thm` 43,
  `gen_gc_partial_thm` 129).
- **an induction the port does not have** (entry 44 says how):
  `vb_eq_size_IMP_vb_size`, `do_eq_IFF_vb_eq_size`,
  `word_eq_LESS_EQ`, `word_eq_add_clock`,
  `bc_stack_ref_inv_FinaliseCons_lemma`, `memory_rel_depth_limit`,
  `v_inv_related_lemma`.  The first three are what entry 43 owes,
  and all of them want the same piece first: the clause of each
  pair of constructors derived once from the match.
- **the separation logic of the word level** (`word_heap`,
  `word_el`, `word_payload`, `SEP_R_TAC`, `SEP_W_TAC`): the
  `memory_rel_*` family, about 30 of them.  `ml/lib/set_sep.ml`
  has `read_fun2set` and `write_fun2set` for HOL4's two tactics,
  and `memory_rel_Number_bignum_header` of the port shows the
  shape; none of this round touched that layer.

`memory_rel_ptr_eq` looks like the cheapest of all (three lines of
HOL4) and is not: it leans on `memory_rel_pointer_eq`, which HOL4
states as the value of an ML expression and the port does not
state (PENDING.md), so its eighty lines of induction have to be a
lemma of the block first.

A cleanup that is owed: `ptrs_store_LUPDATE` (in the block of
`update_ref_thm1`) is the special case of `ptrs_store_el` (in the
block of `update_mutblock_thm`) for a `RefBlock` and the head of
the roots, and one of them should be derived from the other.

## The allocation layer is in (this round)

Five of the allocation theorems are proved and the machinery they
share stands in two blocks:

- the block of `cons_thm_alt` (the first of them in the file) has
  what every allocation needs: `gc_kind_store_unused_alt` (the
  kind of the collection survives a store into the unused space at
  its low end, the generational case included), `bc_ref_inv_step`
  (the invariant of a reference that a step did not touch, with
  its hypotheses an implication each so that a proof hands over
  what it has -- `IMP_CONJ`), `EVERY2_v_inv_alloc` and its stack
  twin, `INJ_FUPDATE_fresh`, `IMAGE_FUPDATE_fresh`, `INJ_bigger`,
  `heap_split_pre`, `isSome_lookup`, `isRef_BlockRep`,
  `reachable_refs_cons` and `v_inv_cons_step`;
- the block of `new_ref_thm` has the same for a store at the *top*
  of the unused space (`gc_kind_store_unused`, where the element
  is a reference and so lands above the split) and
  `all_ts_insert_SUBSET`.

What each of the five costs the reader is now its own block of
five to eight lemmas (the shape of its element, the edges that its
key adds, the transfer of `v_inv`) and a proof that is the same
eight steps: split the invariant, split the roots, write the
element, give the witnesses, then `roots_ok`, `heap_ok`,
`gc_kind_inv`, the unused space and `bc_stack_ref_inv`.

What is left of the family: `word64_alt_thm` and `bignum_alt_thm`,
which are the two that *shrink* the stack (`ws ++ stack` becomes
`Word64 w64 :: stack`), so their timestamps have to be cut
(`DRESTRICT tf (all_ts refs stack)`) and they want the restrict
layer -- which sits in the block of `abs_ml_inv_stack_permute`
eight thousand lines later and rests on `v_inv_update_gen` and
`EVERY2_v_inv_update_stack` (9986, 11577), both of them after
these two statements.  Moving that layer up is the piece to do
first, and `deref_thm` (which reads a reference and changes
nothing) is the cheapest one that needs none of it.

## What the round after the allocation layer did

Two more, of two other kinds:

- `gc_combined_thm`, which is the three kinds of collection and
  nothing else: the one that does nothing, `full_gc_thm`,
  `gen_gc_partial_thm` and `gen_gc_thm` (all three still cheats of
  their own), with the arithmetic of the heap that the collection
  wrote on top -- it holds data, so its data length is its heap
  length.  Its own block is one inline lemma
  (`gen_gc_conf_limit (make_gc_conf l) = l`).
- `deref_thm`, which reads a reference, and with it the generic
  half of `el_thm`'s block: `all_ts_mono`, `heap_ok_in`,
  `heap_el_data`, `roots_ok_data`, `all2_el_cons` and `reach_ref`
  now stand in `deref_thm`'s block, and `el_thm`'s two lemmas are
  the generic ones with a Block's shape put in.  The five kinds
  that a key can hold are three claims of nothing and two of
  something, and the two are the same proof with another element.

So the file is at 82 cheats, and what the layers look like now:

- the allocation layer: done but for `word64_alt_thm` and
  `bignum_alt_thm`, which want the restrict layer moved up;
- the stack layer: `el_thm`, `deref_thm` and the `*_restrict`
  lemmas are in, `bc_stack_ref_inv_MutBlock_F` and
  `v_inv_list_to_v_lem` are not;
- the collection: `gc_combined_thm` is in, the three theorems it
  rests on are not (and they are the ones that ask for the GC
  theories' own lemmas, of which `ml/compiler/backend/gc/` has
  many as cheats);
- the word level (`memory_rel_*`, about thirty of them): nothing of
  it yet, and `ml/lib/set_sep.ml` is where it would start.

## The collection, two of its three

`full_gc_thm` and `gen_gc_thm` are in, and they are one proof twice:
what the collection leaves is what its two theorems of the GC
theory say (`full_gc_related`/`full_gc_ok`,
`gen_gc_related`/`gen_gc_ok`, all four still cheats of
`ml/compiler/backend/gc/`), the two say it of one collection so its
value is one, and then

- the heap it wrote holds data up to the space that is left, which
  is the expansion (`data_up_to_APPEND`, `heap_lookup_APPEND`);
- the stack and the references go over with
  `bc_stack_ref_inv_related`, where the inlining its relation
  allows is the identity one (`all2_refl` of `gc_inline_rel` and of
  `gc_heap_inline_rel`) and what is left is
  `gc_related_roots_heap`, whose third condition is that a pointer
  of the roots is an address they reach;
- the heap is reachable from the roots it returned
  (`IMP_all_reachable_from_roots`).

`gen_gc_thm` adds the kind of the collection: the generations that
`reset_gens` makes all start where the first heap ends
(`gen_state_ok_reset`) and the split at the end of the space has
the data below it and the references above
(`gen_gc_data_refs_split`, `heap_split_length`,
`heap_expand_not_isRef`).

So `gen_gc_partial_thm` is the one of the three that is left, and
it is the same shape again with the old heap in front (its state
has `old`, and the split is at the start of the generation rather
than at the end of the first heap).  129 lines of HOL4, the longest
of the three.

## What the shortest remaining proofs cost (measured, not guessed)

`tools/` has no ranking for this, so here it is: the HOL4 proofs of
the 80 that are left, shortest first, with what each one really
wants.

| HOL4 lines | theorem | what it wants first |
|---|---|---|
| 3 | `memory_rel_ptr_eq` | `memory_rel_pointer_eq`, which HOL4 states as the value of an ML expression and the port does not state (PENDING.md) |
| 6, 10 | `vb_eq_size_IMP_vb_size`, `do_eq_IFF_vb_eq_size` | the clause of each pair of constructors of `vb_eq_size` derived once (entry 43); the proofs are written and too slow, not missing |
| 11 | `memory_rel_FromList` | `copy_list_thm`, another of HOL4's ML-expression theorems that the port does not state |
| 11, 13 | `word_eq_LESS_EQ`, `word_eq_add_clock` | the same clause-at-a-time treatment of `word_eq` |
| 14-16 | `bytes_to_word_eq_lemma`, `word_cmp_loop_thm`, `memory_rel_copy_array_NONE`, `memory_rel_RefPtr_gen_IMP` | the word level: `word_heap`, `SEP_R_TAC`/`SEP_W_TAC` over `ml/lib/set_sep.ml` |

So there is no cheap one left: the three kinds of work that remain
are the clause-at-a-time treatment of the two big `match`
definitions, the theorems that HOL4 never names (which have to be
stated first), and the word level, which nothing of the port has
touched yet.  `gen_gc_partial_thm` (129 lines) is the one big proof
whose pieces are all in the port already -- its `heap_gen_ok heap
cc` alone is thirty lines of HOL4 about `heap_split` and
`heap_segment`.

## The two theorems of entry 43, and what made them cheap

`vb_eq_size_IMP_vb_size` and `do_eq_IFF_vb_eq_size` were the two
whose proofs were "written and too slow": the definition of
`vb_eq_size` is the one `match` that HOL4 means, so a proof that
takes two values apart reduces that match in each of twenty-five
cases.  The round that landed them did not write the clause of each
pair of constructors (entry 43's remedy, nine lemmas) but **one
inversion lemma per function** (entry 71): what a `SOME` of
`vb_eq_size` can be, and what a `SOME` of `vb_eq_size_list` can be.
The twenty-five cases are paid once, inside the lemma.

The two theorems are then the complete induction on the size of the
value (entry 44) with those two lemmas and arithmetic.  Measured in
the session: the block of six lemmas 0.9 seconds, the two theorems
0.2 and 1.3.  Two theorems that the file already proved *from*
`do_eq_IFF_vb_eq_size` (`do_eq_IMP_vb_eq_size`,
`vb_eq_size_IMP_do_eq`) no longer rest on a cheat.

Two traps cost a round each and are in the guide: a definition
unfolded with `ONCE_REWRITE_TAC` reaches the **conclusion** as well
as the antecedent (entry 72), and the failure report of
`tools/bh.ml` follows the first goal only, so a report that looks
impossible means the tactic has to be made total and run again
(entry 73).

So the file is at 78 attempts, and of the "shortest remaining" table
the first two rows are gone.  What is next, in order: `word_eq`'s own
two (`word_eq_LESS_EQ`, `word_eq_add_clock`), the same shape with the
budget `l` as the measure -- `fix_clock_IMP` bounds the inner
comparison for the first, and `fix_clock_word_eq` (which the file
proves from the first) removes the `fix_clock` altogether for the
second; then `gen_gc_partial_thm`; then the word level.

## word_eq's two, and what opening a case tree costs

`word_eq_LESS_EQ` and `word_eq_add_clock` are the other two that
entry 43 had parked, and they are one shape twice: the complete
induction on the budget `l` (entry 44), the definition unfolded
once, and then its case tree -- two conditions, the headers of the
two words, the memory at the two addresses, the inner comparison,
six more conditions and the comparison of the two contents.

What the round learned about opening such a tree is in entry 74 and
in the block above `word_eq_LESS_EQ`:

- `EVERY_CASE_COND_TAC` over the whole tree does not come back: the
  conditions of an arm are under a match that is not reduced yet,
  so the splits it makes there are vacuous and it makes them again
  in every branch;
- splitting *every variable of a product type* splits the two
  records of the arguments into their fields -- 88368 steps and no
  progress.  `CASE_SPLIT_TAC` splits a variable only where a
  pattern looks into it, and the one scrutinee it does not find
  (`m a1`, an application of a variable) is split by hand;
- a leaf has to be closed as soon as a split settles it, with
  `ASM_REWRITE_TAC[LE_REFL]` and the constructor rewrites of the
  goal *and* the assumptions, not with `ASM_ARITH_TAC` per leaf
  (entry 43).

`fix_clock_word_eq`, which the file proves from `word_eq_LESS_EQ`,
is what makes the second theorem tractable: it removes the
`fix_clock` of the inner comparison from both sides, so the two
case trees differ only in the clock, and `ADD_EQ_0` makes the guard
of a zero clock decidable on the side where the clock is `ck + n`.

## Entry 43's debt is paid

All four theorems that `PORTING-GUIDE.md` entry 43 had parked as
"written and too slow" are proofs now:

| theorem | what made it cheap |
|---|---|
| `vb_eq_size_IMP_vb_size` | one inversion lemma per function (entry 71), 0.2 s |
| `do_eq_IFF_vb_eq_size` | the same two lemmas, both definitions reduced together, 1.3 s |
| `word_eq_LESS_EQ` | the case tree opened in the order the definition has it, leaves closed as the splits settle them (entry 74) |
| `word_eq_add_clock` | one tree, not two: the assumption unfolded and the goal left folded (entry 75) |

and three theorems the file proved *from* them
(`do_eq_IMP_vb_eq_size`, `vb_eq_size_IMP_do_eq`,
`fix_clock_word_eq`) no longer rest on a cheat.  The file is at
**76** attempts.

So the "shortest remaining" table has only its last two rows left:
`memory_rel_ptr_eq` and `memory_rel_FromList`, which want theorems
HOL4 states as the value of an ML expression and the port does not
state at all (`PENDING.md`), and the word level.  What is next, in
order:

1. `gen_gc_partial_thm` -- the third of the collection template,
   129 lines of HOL4 whose pieces are all in the port:
   `partial_gc_related` gives the collection's value, the heap it
   wrote and `gc_related`; `gen_gc_partial_partial_gc_IMP` gives
   `a = heap_length (old ++ h1)` (the `partial_gc_IMP` that PLAN
   said was missing is the *other* one, at
   `gen_gc_partial.ml:175`); `roots_ok` of the result comes from
   `gc_related` and `MEM_ADDR_MAP`.  The one real piece of work is
   `heap_gen_ok heap cc`, thirty lines of HOL4 about
   `heap_split_heap_split`, `gen_start_ok` and `data_up_to` --
   `tmp/try880.ml` has the field lemmas of `make_partial_conf` and
   the "prefix of a prefix" lemma for it.
2. the word level (`memory_rel_*`, about thirty of them), which
   starts at `ml/lib/set_sep.ml` and `word_heap`.

## The collection, all three

`gen_gc_partial_thm` is in, so the three collections of
`gc_combined` are proved and `gc_combined_thm` no longer rests on a
cheat of this file (the GC theories' own `partial_gc_related`,
`gen_gc_related`, `full_gc_related` and the rest are still cheats of
`ml/compiler/backend/gc/`, which is where they belong).

What the third one needed beyond the template of the other two:

- `heap_gen_ok heap cc`, the thirty HOL4 lines that are the real
  work, now `heap_gen_ok_inv` above the statement: the start of the
  generation splits the heap through the split at the end of the
  space (`heap_split_heap_split`) and through the split at the end
  of the data, so the three pieces are the segment that
  `heap_segment` names and what is below the start is data;
- `ref_EVERY_d`, which turns the invariant's "no element of this
  piece has reference data" into `EVERY`, in both directions;
- `similar_isRef`, that what the collection copied holds a
  reference only where what it copied from does -- which is what
  `EVERY2 (similar_data c) refs r1` of `partial_gc_IMP` is for;
- and one tactic per conjunct (entry 76), because the five pieces
  of the invariant are five different proofs and a `TRY (SOLVED ..)`
  chain hides which one broke.

So the file is at **75** attempts, and the verify of the five
proofs of this pass says it: no error, no warning,
`AXIOMS-ADDED 82` where the pass began at 95 and
`OWN-AXIOMS 15`, in 783 seconds.  What is left, in order:

1. `memory_rel_ptr_eq` and `memory_rel_FromList`, which want
   theorems HOL4 states as the value of an ML expression
   (`memory_rel_pointer_eq`, `copy_list_thm`) and the port does not
   state at all (`PENDING.md`);
2. the word level (`memory_rel_*`, about thirty of them), which
   starts at `ml/lib/set_sep.ml` and `word_heap`;
3. the rest of the stack layer (`bc_stack_ref_inv_MutBlock_F`,
   `v_inv_list_to_v_lem`, `word64_alt_thm`, `bignum_alt_thm`).

## The string level

Four theorems of this pass are the comparison of two strings, which
is where the word level and the string library of the port meet:

- `word_cmp_loop_thm`, the first of them, and the block above it
  (`sep_read`, `star_front`, `word_list_SNOC`, `addr_step`,
  `addr_prev`, `len_step`) which is what the port needs of a
  separating conjunction and of the address arithmetic of a loop --
  entry 77 of the guide says what each of them is for;
- `word_str_loop_thm`, the loop over the bytes of a string, by
  induction on the number of bytes it has still to read, with
  `loads_cons` above it: the head of a list is the byte at the
  address and the tail is what the induction is about;
- `find_diff_str_cmp_thm1` and `find_diff_str_cmp_thm2`, that the
  byte where two strings first differ decides every one of the
  eight comparisons of `str_cmp`.  What these needed of the
  characters is `ord_chr`, that the eight bits of a character of
  the port spell the number it came from (HOL4 gets it from
  `EVAL_TAC`), and `val_n2w_lt`, the number of a word made of one
  below the word size.  `find_diff_str_cmp_thm2` has the four cases
  of two lists, and in its last one the first character decides
  whatever the two lengths are, which is why the three branches of
  `mlstring_compare` all give the same answer there.

Two things of this level are worth keeping in mind:

- `REAL_ARITH`, which `ARITH_TAC` is built on, does not case split
  on a disequality: `~(a = b) ==> a < b \/ b < a` is *not* an
  `ARITH_RULE`.  What works is `LT_CASES` and then `CONTRA_TAC` on
  the case that the disequality rules out.
- the assumption that says what the memory holds is a *conditional
  rewrite*, so `ASM_SIMP_TAC` will rewrite a load at `a + n2w i`
  with it and leave the goal's load at `(a + n2w 1) + n2w i`
  untouched; the goal's address has to be rewritten back
  (`GSYM wsl_addr`) first.

`memory_rel_str_cmp` is what the four of them are for, and
`memory_rel_ByteArray_IMP` hands it the shifted header
(`x >>> (dimindex (:'a) - c.len_size - 2) = n2w (LENGTH vals + 4)`),
so the one real step that is left there is the case of
`good_dimindex` and the two calls of `word_str_loop_thm`.

## The word level, and its template

`memory_rel_Word64_IMP` is the first of the thirty theorems that
read the heap out of a `memory_rel`, and it is the one that settles
how the rest of them go: `memory_rel_ValueArray_IMP` was already
proved and is the template, entry 79 of the guide writes the steps
out, and the only thing the port needed beyond it was the reading
of *several* cells of one element -- `read_fun2set` wants the cell
at the front of the separating conjunction, so each cell is brought
there by `STAR_AC` in turn.

With that in hand the remaining word-level theorems are a matter of
which element of the heap they are about:

- `memory_rel_Word64_alt`, `memory_rel_RefByte_content`,
  `memory_rel_ByteArray_IMP` and `memory_rel_Thunk_IMP` are the
  same shape at another element;
- `memory_rel_write`, `memory_rel_Update` and the rest of the
  writing ones go the other way, with `write_fun2set`;
- and `memory_rel_Number_bignum_IMP_ALT` and the two
  `memory_rel_..._const_test` ones put a `Bignum` in place of the
  `Word64Rep`.

## What the next theorem of the file needs

`memory_rel_elements_list_distinct_lemma` is in, and what the port
had to add for it is the little that HOL4 gets from `SORTED_APPEND`
-- `sorted_tl`, `sorted_drop`, `sorted_head` and `sorted_pair`, the
block above its statement: of two elements of a sorted list the
earlier one relates to the later.  Anything else of the file that
needs a sorted list has them now.
