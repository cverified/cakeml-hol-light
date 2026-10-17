# Porting CakeML from HOL4 to HOL Light

## Goal

Port the CakeML formalization (verified compiler for a subset
of Standard ML, developed in HOL4) to HOL Light.

Scope: everything that is needed for the main correctness
theorem, which in HOL4 is `compilerProofTheory.compile_correct`
in `compiler/proofs/compilerProofScript.sml`.

The work has two passes:

1. _First pass (current):_ port **all** definitions (and type
   definitions) of the HOL4 sources in the dependency closure
   of the main correctness theorem.  No theorems, no proofs.
   "All of them" means all of them: this pass is only done when
   every `Datatype`, `Type`, `Overload` and `Definition` of
   every ported source file has a HOL Light counterpart.

2. _Second pass (later):_ the theorems and their proofs.

**In the first pass proofs are irrelevant.**  Not "kept short",
irrelevant: no time goes on one.  HOL Light will not make a
recursive definition without a termination proof, so when its
machinery does not discharge the termination condition and the
condition is evidently true, it is assumed with `CHEAT_TAC` and
the definition is made.  Do not look for a measure, do not
prove a lemma to help one, do not spend a budget on one.  The
same holds for any other condition that stands between a source
definition and its HOL Light counterpart.

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
  order of definitions, same names of constants, and the
  original comments kept in place.
- The HOL Light files must **load efficiently**.  A definition
  that takes minutes to process is a bug; fix it (or record the
  timing in a comment if there really is no alternative).
- Lines in `.ml` files are at most 72 characters.
- The port must not add **any axiom** _when the whole port is
  done_: `length (axioms())` has to be 3 then, the three axioms
  of HOL Light's kernel.  So in the end no `mk_thm`, no
  `new_axiom` and no cheat is left, and every definition goes
  through `new_definition`, `new_specification` or `define_type`.

  **Until the definitions are done this rule is suspended, and
  so is the rule that nothing may depend on a cheat.**  A cheat
  is how the first pass gets on with the next definition.  What
  it costs is visible and counted the whole time: `ml/CHEATS.md`
  lists every one with the reason, and `length (axioms())`
  counts them.  There are two kinds, and the first is much the
  better one:

  - the _termination_ of a definition is assumed (`CHEAT_TAC` on
    the condition), and the definition itself is made: the
    constant is introduced by `new_specification`, it has the
    right type, and its clauses are theorems.  One axiom, and
    everything after it can be ported as if the definition were
    there, because it is.
  - the _definition_ is assumed (`cake_cheat`), because HOL
    Light cannot make it at all: the body has a type variable
    that the constant's type does not reflect, or it uses a
    constant that the port does not have.  These are the ones to
    work on, and they need a decision or a missing piece ported,
    not a proof.

  Paying the debt back -- making every assumed termination real
  -- comes after the definitions are all in, with HOL4's own
  `Termination` tactic to transliterate.

## Layout of this directory

- `CLAUDE.md`     this file
- `PLAN.md`       the plan of the current pass
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

A _run_ (`tools/bin/checkseq`, which `tmp/run-cs.sh` starts on
the whole load order) loads the files of `ml/` one after the
other in one session, which takes over an hour.  **While a run
is going, nothing may write into `ml/`**: a file that the run
has not reached yet would be loaded in a state that no report
describes, and a file that a `needs` of a later file reloads
with another digest is an error of its own.  `tools/port.py`
refuses to write while a run is going, and `tools/bin/trydef`
refuses to use the session of one.
