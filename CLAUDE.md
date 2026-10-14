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
- The port must not add **any axiom**: after loading everything,
  `length (axioms())` has to be 3, the three axioms of HOL Light's
  kernel.  So no `mk_thm`, no `new_axiom`, and no cheating: every
  definition goes through `new_definition`, `new_specification` or
  `define_type`.

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
