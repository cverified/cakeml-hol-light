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
   where HOL4 has a proof.  715 theorems are not stated but have a
   comment pointing at the HOL4 lines instead; `tools/coverage.py`
   is the check.
3. **Proofs -- under way.**  Every cheat becomes a real proof,
   until `length (axioms ())` is 3 (HOL Light's own three).
   1262 of the port's 10543 proofs are real: 670 of them in the
   proof store (`proofs/`), the rest written beside the port in
   `tools/extra/` or taken from LightCake (see below).

`ml/CHEATS.md` lists every assumed definition with the reason,
`ISSUES.md` every place the port knowingly says something other
than the source, and `PENDING.md` what is left out and why.

290 files live under `ml/`: 228 are ports of CakeML sources, and
62 in `ml/lib/` are the HOL4 library theories (and the port's own
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

A definition of the port says how it is made, and nothing is
searched for while a file loads:

```ocaml
let lookup_def,lookup_ind = define_wf `MEASURE FST`
  [`sptree_lookup k LN = NONE`;
   `sptree_lookup k (LS a) = (if k = 0 then SOME a else NONE)`;
   ...];;
```

The ways are `new_definition` (HOL Light's own: no recursion, one
clause), `define_cases` (several clauses and no recursion, by the
recursion theorem of the type that is matched on), `define_rec`
(structural recursion, by that same theorem), `define_general`
(clauses that neither of those takes, by HOL Light's machinery),
`define_wf` (the relation written out, which is what HOL4's
`Termination` gives), `define_guess` (HOL Light finds the
termination argument itself), `define_shaped` (clauses HOL Light
cannot take as HOL4 writes them -- a recursion through a `MAP`, a
pattern inside a pattern -- with the word that says which
rewriting of them it goes through), and `assume_definition`, which
assumes the definition and says so in its name.  `_cheat` on a
name says the termination is assumed, `_tac` that a tactic for it
is given, and `_mutual` that it is a family that recurses through
itself.  The ones that say cheat or assume, and no others, add an
axiom; `ml/CHEATS.md` lists every one and `length (axioms ())`
counts them.

Three of the rewritings hand what comes out back to a way of
making a definition, and the word says that one too, after a `>`:
`define_shaped_rec "sing>nested"` is "read the clauses as a
function of one element of a list, and make what comes out by the
nested way".  So a call site says the whole of how its definition
is made, however deep it goes.

Which way each definition needs was harvested from a run
(`tools/strategies.py`, `tools/bin/strategies`): of the 4184 it
has, 2862 are `new_definition`, 481 need a measure (406 of them
with the relation a run found), 332 the recursion theorem of
their type, 197 that theorem without recursing, 103 are assumed,
86 need HOL Light's machinery, 41 a nested recursion compiled,
33 a guess, 32 a match and 3 a case split; 14 go through a
rewriting of the clauses and say both ways in one word.

**Writing a new definition.**  `find_definition_way` runs the
chain of strategies that the port used to run on every load, and
`print_definition_way` says what it found as the line a file
writes:

```ocaml
# print_definition_way [`w [] = []`;
    `w (x :: y :: xs) = HD (w [x]) :: w (y :: xs)`;
    `w [x] = [x + 1]`];;

let w_def,w_ind = define_shaped_rec
  "sing>new_definition"
  [`...`];;
```

It makes the definition as a side effect, so it belongs in a
session of its own; no file of the port calls it.

Each recursive way gives the **induction theorem** with the
definition, as HOL4 does.  That is what a proof needs to do
induction over a recursion -- `recInduct foo_ind` and
`ho_match_mp_tac foo_ind`, 1271 uses in the sources the port
covers -- and HOL Light has nothing that makes one, so the port
does (`ml/lib/induction.ml`).

Its statement is read off the clauses: one antecedent per clause,
with a hypothesis for every recursive call of that clause under
the guards that lead to it, and a match taken apart into the
clauses it stands for.  Nothing is proved to arrive at it.  The
proof is well-founded induction on the relation the definition was
made with, then the clause whose pattern the arguments match, and
then the termination condition that was proved to make the
definition.  A family of functions that recurse through one
another gets the theorem HOL4 gives it -- a predicate for each of
them and a conjunction of conclusions -- by the same induction on
the sum of the arguments of its members, which is what such a
definition is made on.

## Loading it without the proofs

`tools/bin/abstract` loads the whole port with `ml/lib/fast.ml` in
front of it: every definition makes its constant and **assumes**
its equations, every induction theorem is its statement assumed,
and every proof is skipped.  On `lib/sptree.ml` that is 0.6
seconds against 13.

`tools/bin/abstract <session> <file>` stops in front of a file
and does not load it, which is how a proof of that file is
developed: what it stands on is there in a few minutes, and the
file itself is then loaded for real.  In front of the file the
session gets the real ways and the real `prove` back
(`ml/lib/real.ml`), so what is loaded after that is proved.

`tools/bin/tryfile <file>` is that as one command, with a marker
before every phrase: it says which phrase of the file fails and
why, in about five minutes instead of the hour a run takes.

Nothing is proved in such a session and `length (axioms ())` says
nothing while it is on.  What makes it safe to develop against is
that the statements are the same terms either way: the induction
theorem's statement is computed from the clauses, and a real load
computes it the same way and then proves it.  An abstract has no
second copy of what a file says, so it cannot drift from the port.

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

`lightcake-src/` is a third one: LightCake, the other port of
CakeML to HOL Light.  It is somebody else's private repository,
and its owner has put a read-only deploy key on it, so the clone
pulls on its own (`core.sshCommand` points at the key, as the
push of this repo does at its own).

Where there is no such key, `tools/bin/lightcake-puller` is the
way: its owner starts it in a shell of his own, where his
credential is, and `tools/bin/lightcake-pull` asks it for a pull
and says what came of it.  The whole of what can be asked for is
that one pull of that one repository, so nothing of the
credential is delegated.

## Taking a proof from LightCake

LightCake's HOL4 library layer is proved, and of those theories
this port has only the definitions that CakeML needs.  What it
proves of them can be taken:

    tools/bin/lightcake-take sptree

which imports, tries every block of the import on its own,
imports again without the ones that do not go through, and
writes the file.  The import itself is the file
`tools/lightcake/sptree.ml`, which a re-port appends to
`ml/lib/sptree.ml` as it appends `tools/extra/`.  Nothing of it
reaches `ml/` until every block of it has been run, because a
block that fails stops the file it is in.

The statements and the proofs are LightCake's, with its constants
under the names this port gives them: both ports name after
HOL4, so the HOL4 name is what joins them (its `doc/names.tsv`
and this port's own renaming).  A name of the closure can be a
word of HOL Light as well, so that map is only used inside a
quotation and never for a name the block binds.

A block is taken only when every name it uses is one this port
has, and never when it **binds** one this port binds: a block
that did would shadow what this port says, and every later file
reads the name as this port writes it.  So a definition of
LightCake's is never taken -- this port makes its own, its own
way -- and neither is a theorem that this port states itself.

Which name is which is read off the two files, and the file of
this port is what says how this port names the theory's
constants: this port's `tailrec_TAILREC` is HOL4's
`tailrec$TAILREC` under the name LightCake gives it too, while
`TAILREC` is `While`'s, which is another constant altogether.
A file of this port is read up to the block an import appended
to it, or the import would be read back as what this port says.

A name of LightCake's **proof kit** never counts as one it has:
its `size_def` makes a size function and this port's is the size
function of sptree, so the word says nothing.  That is also what
keeps HOL4-style tactics out -- they are all kit names.  Where
HOL Light has something suitable, a line of `tools/extra/` says
so and lets those proofs in: `SPTAUX_CASES_TAC` is LightCake's
case split, and HOL Light's is `STRUCT_CASES_TAC` with
`cases_of`.

`lightcake-check`, which the loop runs, loads the blocks one at
a time and writes the ones that do not go through into
`tools/lightcake/<theory>.bad`, which the next import leaves
out, with the reason.

A theorem this port **states and cheats** is the other half:

    tools/bin/lightcake-fill mlstring

writes LightCake's proof of it into `proofs/<path>.prf`, under
the same name rule, ports, loads the file with every theorem in
a try so that every proof that does not go through is reported
and not only the first, takes those out of the store again, and
ports once more.  Here the statement is this port's and the
proof is LightCake's, and the only way to know that the two fit
is to run them: this port's `implode_STRCAT` is about `STRCAT`
where LightCake's is about `APPEND`, and LightCake's proof does
not reach it.  The two halves of the loop are also there on
their own (`lightcake.py fill`, `TOLERANT=1 tools/bin/tryfile
<file>`, `lightcake.py drop <theory> <name>...`), and `drop`
takes either name a theorem goes by.

Whether a name exists is read off the sources: this port's
files that load before the one being written, LightCake's own
blocks that have been taken, and HOL Light's own bindings and
kernel signature.  A proof that uses `Library/rstc.ml`'s
`RTC_INDUCT_L` is left out with that as the reason, because
this port does not load that library.

`tools/lightcake.py` also has `names`, `report` and `deps`,
which say what the two ports share, how many of this port's
cheats LightCake proves, and what a theory of it would need.

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
