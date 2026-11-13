# Porting CakeML from HOL4 to HOL Light

## Goal

Port the CakeML formalization (verified compiler for a subset
of Standard ML, developed in HOL4) to HOL Light.

Scope: everything that is needed for the main correctness
theorem, which in HOL4 is `compilerProofTheory.compile_correct`
in `compiler/proofs/compilerProofScript.sml`.

The work has three phases:

1. _Phase one (done):_ **all** definitions (and type
   definitions) of the HOL4 sources in the dependency closure
   of the main correctness theorem.  No theorems, no proofs.
   "All of them" means all of them: this phase is only done when
   every `Datatype`, `Type`, `Overload`, `Definition` and
   `Inductive` of every ported source file has a HOL Light
   counterpart.  `tools/coverage.py` is what checks it, and the
   handful of blocks that are out are in `PENDING.md`, each with
   the reason.

2. _Phase two (done, but for `PENDING.md`):_ **everything else
   of the sources except the proofs** -- every `Theorem` (and
   `Triviality`, and the theorems that HOL4 binds to the value
   of an ML expression), with its statement and its name and its
   attributes, and every comment, in the order of the source.
   Every proof is `CHEAT_TAC`.

   The test of this phase is to read a HOL4 source and its port
   next to each other: they have to **clearly read "the same"**.
   Same blocks in the same order, same names, same statements,
   same comments in the same places; where HOL4 has `Proof ...
   QED` the port has a cheat, and that is the only difference
   that a reader should see.

   So phase two is where every _statement_ of CakeML is settled.
   That is worth doing before any proof, because a statement
   that changes afterwards throws its proof away, and because a
   statement that will not even typecheck is the one real test
   of whether phase one got the definitions, the types, the
   notation and the names right.

   Attributes (`[simp]`, `[compute]`, `[local]`,
   `[allow_rebind]`) are kept, because they are part of what the
   source says, but they are not load bearing: phase three does
   not replay HOL4's automation.

3. _Phase three (current):_ the proofs.  Every `CHEAT_TAC` of
   phases one and two is replaced by a real proof, until
   `length (axioms ())` is 3.  Then the port is done.

   **A statement is settled before its proof is written.**  That
   was the point of doing phase two first, and it still is the
   rule: a proof is written for a file whose statements are all
   in, because a statement that changes afterwards throws its
   proof away.  Phase two is in except for what `PENDING.md`
   says, so a file whose statements are all in may be proved;
   one that is still missing statements gets those first.

   **The proofs of phase three are written by hand.**  They are
   not a mechanical conversion of HOL4's tactics: the HOL4 proof
   is read, understood and then written as a HOL Light proof.
   Do not build a tactic translator.

**In phases one and two proofs are irrelevant.**  Not "kept
short", irrelevant: no time goes on one.  HOL Light will not
make a recursive definition without a termination proof, so when
its machinery does not discharge the termination condition and
the condition is evidently true, it is assumed with `CHEAT_TAC`
and the definition is made.  Do not look for a measure, do not
prove a lemma to help one, do not spend a budget on one.  The
same holds for any other condition that stands between a source
definition and its HOL Light counterpart, and it holds for every
theorem of phase two: the statement is the work, the proof is a
cheat, and a cheat that another cheat depends on is fine.

## Ground rules

- The HOL4 sources are a _cloned release_ (tag `v3479`) of
  https://github.com/CakeML/cakeml in `cakeml-src/`.
  That directory is read-only reference material and is not
  part of this git repo (see `.gitignore`).
- Do **not** run HOL4 (it is installed on this machine, but the
  port is a source-level port, not an export/import).
- The HOL Light sources must be _as similar in style to the
  original CakeML sources as possible_: same directory layout,
  same file names (`fooScript.sml` becomes `foo.ml`), same
  order of the blocks, same names of constants and of theorems,
  and the original comments kept in place.
- A comment of a source is kept **unaltered**, whatever it is
  about -- a comment about HOL4 is a comment of the source and
  stays as it stands.  It is not reflowed and not shortened, so
  a line of one may be longer than 72 characters (691 of them
  are); `tools/lines.py` is the check, and what it has to report
  is no line over 72 _outside_ a comment.  The one thing that is
  put right is a quote that OCaml would read as the start of a
  string.
- Every file of the port starts with a **preface**: a comment
  that says what the file is (a definition theory of CakeML, a
  proof theory and of which file, or a HOL4 library theory of
  which the port has what CakeML needs), how many definitions,
  datatypes and theorems its source has, and which files of the
  port need it.  It is at most **eight lines**, the empty line
  after it counted, and `tools/preface.py` writes it (after the
  port, because which files need a file is only known when every
  file has its `needs` lines).
- **No HOL4 code in the port.**  Not in a definition, not in a
  proof and not in a comment: no SML, no HOL4 tactic, no HOL4
  quotation, not even one line of it.  Where the port cannot say
  what the source says (the ML code of a source that builds a
  term, the tactic of a `Termination`, an `Overload` or a `Type`
  that the port expands), it puts a comment that **points at the
  HOL4 source** instead -- the file and the line range, or
  something more precise:

  ```
  (* HOL4 word_bignumScript.sml:243-389: the ML code that builds
     the deep embedding *)
  ```

  The port's own prose about what HOL4 does is not HOL4 code and
  stays.  The reference material is in `cakeml-src/`, which is
  always there to read; copying it into the port only makes two
  copies of it to keep in step.
- The HOL Light files must **load efficiently**.  A definition
  that takes minutes to process is a bug; fix it (or record the
  timing in a comment if there really is no alternative).
- Lines in `.ml` files are at most 72 characters.
- The port must not add **any axiom** _when the whole port is
  done_: `length (axioms())` has to be 3 then, the three axioms
  of HOL Light's kernel.  So in the end no `mk_thm`, no
  `new_axiom` and no cheat is left, and every definition goes
  through `new_definition`, `new_specification` or `define_type`.

  **Until phase three this rule is suspended, and so is the
  rule that nothing may depend on a cheat.**  A cheat is how
  phase one gets on with the next definition and how phase two
  gets on with the next statement.  What it costs is visible
  and counted the whole time: `ml/CHEATS.md` lists every one
  with the reason, and `length (axioms())` counts them.  There
  are four kinds, and the first three are the good ones.  Each of
  them says so where it stands, so a file is read for what it
  assumes and not only `ml/CHEATS.md`:

  - a _theorem of the source_ is assumed: its statement is
    stated, with its name, and `CHEAT_TAC` stands where HOL4's
    proof is.  This is what phase two does, and what phase
    three turns into a proof, one theorem at a time.
  - the _termination_ of a definition is assumed (a way whose
    name ends in `_cheat`), and the definition itself is made:
    the constant is introduced by `new_specification`, it has the
    right type, and its clauses are theorems.  One axiom, and
    everything after it can be ported as if the definition were
    there, because it is.
  - the _induction theorem_ of a definition is assumed, which is
    what happens when its termination is: the statement is read
    off the clauses either way and is right, but it rests on the
    same assumption the definition does.  One axiom, and the load
    says `foo_ind ASSUMED`.
  - the _definition_ is assumed (`assume_definition`, with the
    reason as its first argument), or the constant is declared
    without a value (`cake_declare`), because HOL Light cannot
    make the definition at all: the body has a type variable that
    the constant's type does not reflect, or it uses a constant
    that the port does not have.  These are the ones to work on,
    and they need a decision or a missing piece ported, not a
    proof.

  Paying the debt back is phase three, with HOL4's own proof (or
  its `Termination` tactic) to transliterate.

## Layout of this directory

- `CLAUDE.md`     this file
- `PLAN.md`       the plan of the current pass
- `PORTING-GUIDE.md`
                  the HOL4 idioms that cost work to port and what
                  the port does about each; **read it before writing
                  a proof, and add to it whenever an idiom takes
                  more than ten minutes to get right**
- `cakeml-src/`   the HOL4 CakeML release (reference, untracked)
- `tools/`        scripts for analysing the HOL4 sources and
                  for the translation
- `ml/`           the HOL Light port; mirrors the directory
                  structure of `cakeml-src/`
- `SESSIONS.md`   which tmux HOL Light sessions exist and what
                  has been loaded in them

## Running HOL Light

The opam HOL Light needs its own opam switch, so first

```
. tools/holenv.sh
```

which puts `hol.sh` and the `repl-*` scripts in the path.
Then use the `repl-*` scripts as described in the CLAUDE.md
one directory up (`repl-clone`, `repl-step`, `repl-kill`, ...).

A _run_ (`tools/bin/checkseq`, which `tools/bin/runall` starts on
the whole load order) loads the files of `ml/` one after the
other in one session, which takes over an hour.  **While a run
is going, nothing may write into `ml/`**: a file that the run
has not reached yet would be loaded in a state that no report
describes, and a file that a `needs` of a later file reloads
with another digest is an error of its own.  `tools/port.py`
refuses to write while a run is going, and `tools/bin/trydef`
refuses to use the session of one.
