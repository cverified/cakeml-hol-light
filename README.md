# CakeML in HOL Light

A source-level port of the [CakeML](https://cakeml.org) verified
compiler from HOL4 to [HOL
Light](https://github.com/jrh13/hol-light).

The scope is everything in the dependency closure of CakeML's main
correctness theorem, which in HOL4 is
`compilerProofTheory.compile_correct` in
`compiler/proofs/compilerProofScript.sml`.  The port is not an
export/import through a proof term: it is a port of the *sources*,
file by file, so that a HOL4 script and its HOL Light counterpart
read the same -- same blocks in the same order, same names, same
statements, and the original comments in place.

The reference is the CakeML release tagged `v3479`
(commit `e8eca63`, 2026-08-24).

## Status

The work has three phases.

1. **Definitions -- done.**  Every `Datatype`, `Type`, `Overload`,
   `Definition` and `Inductive` of every ported source file has a
   HOL Light counterpart: 4480 of 4482 blocks, the two exceptions
   and their reasons in `PENDING.md`.
2. **Statements -- done.**  Every `Theorem`, `Triviality` and
   ML-bound theorem of the sources, with its name, its statement
   and its attributes, in the order of the source, with `CHEAT_TAC`
   where HOL4 has a proof.  693 theorems are not stated but have a
   comment pointing at the HOL4 lines instead; `tools/coverage.py`
   is the check.
3. **Proofs -- under way.**  Every cheat becomes a real proof,
   until `length (axioms ())` is 3 (HOL Light's own three).  The
   last full run stood at **9607**.  670 proofs are in, in five
   files.

`ml/CHEATS.md` lists every assumed definition with the reason,
`ISSUES.md` every place the port knowingly says something other
than the source, and `PENDING.md` what is left out and why.

286 files live under `ml/`: 228 are ports of CakeML sources, and 58
in `ml/lib/` are the HOL4 library theories (and the port's own
support) that CakeML needs and HOL Light does not have.

## Loading it

You need HOL Light; the only library of it the port asks for is
`Library/words.ml`.  Start HOL Light with `ml/` as the current
directory, so that the `needs` lines resolve, and load any file you
like -- its `needs` lines pull in its whole closure:

    loadt "compiler/backend/bvi_let.ml";;

Loading everything takes over an hour and about 1.2 GB of live
heap, so load the closure of what you care about instead.

You do **not** need HOL4, and you do not need the HOL4 sources, to
load the port or to read it.

## The shape of a definition

Every definition of the port is made by `cake_define`
(`ml/lib/define.ml`), and there are 4296 of them.  It takes the
whole definition as one term and tries a ladder of strategies:
`new_definition`, then the recursion theorem of the type, then
eight ways of rearranging the clauses, then a measure, and at the
end a guess.  Whichever works, works.

It has a wart, and it is the first thing to say about it.  When no
strategy works, or the time budget runs out, `cake_define`
**assumes** the definition and records the reason in
`ml/CHEATS.md`.  So a `cake_define` at a call site does not tell a
reader whether a definition or an axiom came out of it; only
`ml/CHEATS.md` does, and `length (axioms ())` counts them.  The
same name covers both, which is exactly what one does not want.

Where this is going: the port already harvests which strategy won
each definition (`cake_strategies ()`, `tools/bin/strategies`).
With that recorded, a file can say the primitive itself --
`new_definition`, or `new_recursive_definition`, or a `define` with
the measure it needed -- and `cake_define` leaves the surface of
the port altogether, which is both faster to load and honest about
what each line does.  An assumed definition then says so in a word
of its own.  Comments on that plan are welcome.

## Writing a proof

Proofs do not live in `ml/`.  **The files under `ml/` are
generated** by `tools/port.py` from the HOL4 source and a store of
proofs, so an edit to one of them is overwritten by the next
re-port.  A proof goes into `proofs/<path>/<theory>.prf`, in a
section headed by the name of the theorem:

    ### exp2_size_APPEND
      (REWRITE_TAC (size_thms "bvi_exp") THEN
       MATCH_ACCEPT_TAC (ISPEC `bvi_exp_size` list_size_APPEND))

Then `python3 -I tools/port.py <theory>` rewrites
`ml/<path>/<theory>.ml` with the proof in the place of the cheat.
Re-porting a file reads its HOL4 source, so for that you do need
the reference material:

    git clone --depth 1 --branch v3479 \
      https://github.com/CakeML/cakeml cakeml-src
    git clone --depth 1 https://github.com/HOL-Theorem-Prover/HOL \
      hol4-src

Both are in `.gitignore`: they are read-only reference, and the
port never copies code out of them.

The rules a proof has to keep are in `CLAUDE.md`, and the ones that
bite are these: the statement of a theorem is not adjusted to suit
a proof; a proof is written as a HOL Light proof, by hand, and is
not a mechanical transliteration of HOL4's tactics; lines in `.ml`
files are at most 72 characters; and no HOL4 code appears anywhere
in the port, not even in a comment -- where the port cannot say
what the source says, it puts a comment pointing at the HOL4 file
and line range.

`PORTING-GUIDE.md` is the long answer to "how does one say *this*
in HOL Light": every HOL4 idiom that cost more than ten minutes,
and what the port does about it.  It is worth a look before a first
proof.

## The checks

The `tools/*.py` scripts are standalone and need only Python:

    python3 -I tools/coverage.py     # every block of every source
    python3 -I tools/fidelity.py     # names and arities
    python3 -I tools/comments.py     # the comments of the sources
    python3 -I tools/lines.py        # line lengths
    python3 -I tools/nohol4.py       # no HOL4 code, pointers resolve

They are what keeps the port faithful, and they read `cakeml-src/`.

## What to ignore

This repository is a working directory, and some of it is about the
way its maintainer works rather than about the port:

- `SESSIONS.md` is a log of his tmux HOL Light sessions.
- The scripts in `tools/bin/` drive those sessions through
  `repl-step` and friends, which live **outside** this repository.
  Without them, `tools/bin/*` will not run; the Python checks and
  `tools/port.py` do not need them.
- `tools/holenv.sh` has absolute paths from his machine.
- `CLAUDE.md` is addressed to Claude Code, which wrote much of this
  port.  Read it anyway: it is also the specification of the port,
  and the rules in it are the rules.

## Licence

The port's own text is BSD 3-Clause; see `LICENSE`.

It carries material from two BSD-licensed projects, whose notices
travel with it:

- CakeML, `LICENSE-CakeML`.  The port keeps the comments of the
  CakeML sources unaltered, and its statements, names and file
  layout follow them.
- HOL4, `LICENSE-HOL4`.  The theories under `ml/lib/` are ports of
  HOL4's own library theories, with their comments.
