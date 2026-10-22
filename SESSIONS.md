# HOL Light tmux sessions of this project

- `hol-base`
  plain HOL Light (made with `repl-new-template base`, which
  uses the `hol.sh` shim in `tools/bin`)

- `hol-template-cakeml`
  clone of `hol-base` with `ml/lib/preamble.ml` loaded, so with
  `Library/words.ml` and the HOL4 compatibility layer
  (`ml/lib/hol4.ml`, `ml/lib/records.ml`, `ml/lib/define.ml`)

- working sessions are clones of `hol-template-cakeml`

The template has only the _hand written_ files of `ml/lib`
(`preamble.ml` loads them); the library theories that the port
translates (`sptree`, `balanced_map`, `regexp_compiler`, ...) are
loaded by the files that need them, so a session that is to try a
definition of one of those has to load its file first.

Rebuild a template after changing `ml/lib/`:

```
. tools/holenv.sh
repl-kill template-cakeml
repl-clone hol-base template-cakeml
repl-step template-cakeml 'loadt "<cakeml>/ml/lib/preamble.ml";;'
```

(`tools/bin/retemplate` does that, and makes `hol-base` again
when it is gone.)

**Always rebuild the template after changing `ml/lib/`**: a
working session is a clone of it, so a session made before the
change has the old library (a run of `tools/bin/checkseq` with an
old template fails on everything that the change adds).

**Never send anything to `hol-seq` while `tools/bin/checkseq` is
running**, and do not clone it either: the command is queued in the
session, eats one of the prompts that `repl-step` waits for, and
the run hangs.  Clone `hol-template-cakeml` instead.

**Do not write into `ml/` while a run is going** either: a file
whose contents change after it was loaded is loaded a second time
by the next file that needs it (HOL Light keeps the digest), and
everything it defines is then "already in use".  A script that
ports a theory to look at what comes out sets
`port.ML` to a scratch directory first.

`tools/bin/trydef <name>...` makes the definitions that the
first pass assumes (`ml/CHEATS.md`) again in a clone of
`hol-seq`, with their constants renamed, and says of each one
whether it was made, how long it took and why it was not: that
is the quick way to try a change to the strategies, because the
ancestors of the definition are loaded already.  With
`PATCH=<file>` the clone loads a changed part of
`ml/lib/define.ml` first (see below).

The hand written files of `ml/lib` (`fastdef.ml`, `hol4.ml`,
`define.ml`, `records.ml`, `words4.ml` and the theories that
`preamble.ml` names) are only loaded by the preamble, which the
template has and a run never loads again, so _those_ may be
written while a run is going; what the run would load a second
time is a _ported_ file.

`cake_debug` writes to one file (`tmp/debug.txt`), so a session
that is given `cake_debug := true` while a run is going writes
into the log of the run.  Its goals are under the name of the
definition that is tried (a test gives it a name of its own), but
a test that does not need the log leaves `cake_debug` alone.

A change to `ml/lib/define.ml` can be tried while a run is going
without writing into `ml/`: everything that file makes is an ML
value (it has no definition of its own at the top level), so a
copy of the part from the changed function to the end of the file
loads over it in a clone of the template and the port's
`cake_define` is then the changed one.  The strategies of
`cake_define_gen` take `TERM_TAC` as it was when they were made,
so the copy has to start at the function that is changed and go
on to the end.

That copy may not make the tables of the session again:
`the_rec_thms` (the recursion theorem of every type that is
loaded) and `the_size_fns` (their size functions) are `ref`s in
the middle of `define.ml`, and a copy that resets them leaves the
session without a recursion theorem and without a size function,
so that every definition by cases and every measure fails.
`tools/tailpatch.py` comments those two lines out; a tail that is
cut by hand (`sed -n '489,$p'`) has to do the same.

Once a run is over, `hol-seq` has the ancestors of every file
loaded, which is what `tools/bin/retry` uses: it loads the phrases
of a file from the one that failed on, in a clone of `hol-seq`
(the session `hol-try`), so that a fix is tried without loading
the ancestors again.

**A clone of `hol-seq` does not survive the retemplate**: it is a
child of the process of `hol-seq`, which is a child of the one of
the template, so `tools/bin/retemplate` takes all three.  So
everything that a session with the port in it is needed for
(`tools/bin/diag`, `tools/bin/trydef`, `tools/bin/retry`) happens
**before** the library layer is made again -- between the reports
of a run and the retemplate of the next cycle.

## Interrupting and killing

A clone is forked from another HOL Light process, so it is not a
child of the tmux pane: a `C-c` in the pane goes to the `socat`
of the session and ends the session, leaving the process (half a
gigabyte) running.  Therefore

- `repl-int` sends the interrupt to the process itself, whose pid
  the clone writes to `bin/socket/hol-<name>.pid`;
- `repl-kill` interrupts the session first (a busy one would not
  read the `exit`), and kills that process if it is still there.

A clone is a child of the process it was forked from, so killing
a session kills the sessions cloned from it as well: `hol-try`,
a clone of `hol-wa`, died with `hol-wa`.  Kill the clone first,
or keep the parent until the clone is no longer needed.

`tools/bin/retemplate` kills the template and makes it again, so
it kills every session that was cloned from it (including
`hol-seq`): a run has to be over before the library layer is
changed, and the sessions that a test needs are made again after
it.

`tools/bin/holclean` kills every session except `hol-base`,
`hol-template-cakeml` and `hol-seq`, the session of a run (which
`FORCE=1 holclean` kills as well).  It killed a run of 65 files
before it spared `hol-seq`.

## Phase three: one frontier, cloned per attempt

What the loading costs, measured:

| | |
|---|---|
| the whole port, in load order | 5,656 s (94 min), 21 s a file |
| the `needs` closure of a file | 485 s on average, 802 s for a proof |
| one closure per file, over the 270 | **36 hours** |
| a clone of a session that is loaded | **1 s** |
| `tools/bin/reload` of the tactics and lemmas | **under a second** |
| `tools/bin/retemplate` | 9 s |

So there is **one frontier session**, `hol-front`, which holds the
files of the load order up to the one being worked on:

```
. tools/holenv.sh
frontier compiler/backend/proofs/bvi_letProof.ml   # extend it
frontier                                           # where is it
frontier -i compiler/backend/proofs/bvi_letProof.ml  # and this one
```

It is **never typed in**: clone it for every attempt (a second), and
throw the clone away when a tactic hangs.  `tmp/frontier.txt` says
what it holds.

**A clone is a fork of the session it comes from, so killing one
kills its clones.**  That is why `hol-front` is a clone of
`hol-base` and loads the preamble itself: a clone of
`hol-template-cakeml` dies every time the template is rebuilt, and
the frontier is the one session that must not (94 minutes).

**A re-port invalidates every session that holds the files it
rewrites.**  `needs` remembers a file by its digest, so after
`portall.py` a loaded session will try to load a changed file
again, and loading a file of the port twice fails (its constants
are already defined) and leaves the session with half a theory --
26 axioms where there should be 6, in the one I ruined that way.
So: re-port **before** building or extending a session, and never
while one is loading.  It is the rule that `CLAUDE.md` already
states for runs, and it holds for the frontier too.

**When a utility function is added**, which file it goes in decides
what it costs:

- a **tactic** goes in `ml/lib/tactics.ml`, a **lemma** that more
  than one proof needs in `ml/lib/lemmas.ml`.  Neither file defines
  anything, so `reload front` (or any session) loads them again in
  under a second and the work goes on.  Load them **whole**, never
  the one function that changed: OCaml binds a name where it
  stands, so a caller keeps the old one.
- a lemma that one proof needs stays **in that proof**, as HOL4's
  sources do it.
- anything that **defines** something -- a constant in
  `ml/lib/hol4.ml`, machinery in `ml/lib/define.ml` -- costs the
  session: 8 minutes for a closure, 94 for the frontier.  So batch
  those, and do them when a file is finished rather than in the
  middle of one.

## The template has to be rebuilt when the library changes

`tools/bin/reload` puts a changed `ml/lib/lemmas.ml` or
`ml/lib/tactics.ml` into a **running** session in a second, and that
is what the work uses; but it does not change
`hol-template-cakeml`, and a clone of the template is then a session
whose library is older than the proofs.  A verification in such a
clone fails with `Unbound value <the new tactic>` part way through
the file, which looks like a broken proof and is not one.

So: after a lemma or a tactic is added, `KEEP=1 retemplate` before
cloning for a verification -- and remember that `retemplate` kills
the old template, which takes **its clones with it** (a clone is a
fork).  `KEEP=1` spares only what hangs off `hol-base`.

## The closure of a single file

For a file in the middle of the order, its `needs` closure is ten
times cheaper than the prefix of the load order (529 s against
4,131 s for `bvi_letProof`), so a one-off visit to a file is a
closure and not a frontier:

Working on the proofs of one file means a session that holds the
**needs closure of that file** and not the whole load order:

```
. tools/holenv.sh
repl-clone hol-template-cakeml pfbase
# the needs lines of the file, in a scratch file of their own
repl-step pfbase '#use "tmp/pfprefix.ml";;'
repl-clone hol-pfbase pf1        # the session to work in
```

For `compiler/backend/proofs/bvi_letProof.ml` that is 529 s
against 4,131 s for the files before it in `tools/load.txt`.
`hol-pfbase` is the template of the file and stays untouched;
`hol-pf1` is cloned from it and is where `g`/`e`/`p` go, and it
is cheap to throw away and clone again when a tactic hangs.

**A change in `ml/lib` costs the closure again**: `retemplate`
rebuilds `hol-template-cakeml` and kills every clone of it, so
batch the library additions that the proofs need.

**Build a test bed out of the closure of the file in the order of
the load order**, which `tools/needsorder.py` writes:

```
python3 -I tools/needsorder.py <path>.ml > tmp/pfprefix.ml
```

Every intermediate language has a `Var`, an `If`, a `Let` and a
`Call`, and the port overloads those names, so the order in which
files load decides what a clause of a later file means: a session
that loads `compiler/backend/bvi.ml` early and `bvi_let.ml` late
reads the `Var` of `bvi_let`'s clauses as **bvl**'s, makes the
definitions clause by clause and reports three proofs `NOT PROVED`
that are right (PORTING-GUIDE.md entry 16).  The check after
building a session is `grep -E 'CHEATED|cake_conj_list'` over its
pane.

A closure that `needs` builds by recursion is **not** in the order
of the load order, and that is not a detail: the recursion takes
the needs of a file in the order they stand in it, so a file of the
order can land after one that stands behind it.  The closure of
`data_to_word_memoryProof` built that way loads
`compiler/backend/semantics/closSem.ml` before
`semantics/evaluate.ml`, five theories have overloaded `evaluate`
by the time `evaluate.ml` defines it, and the file does not load at
all -- `semantics/evaluate.ml` and `dataProps.ml` are then missing
from the session, with no sign of it but one line of its pane.
`tools/needsorder.py` sorts the closure by `tools/load.txt`
instead, which is the order a run has (PORTING-GUIDE.md entry 16).

For a definition file a clone of `hol-template-cakeml` plus
`needs "<the file>"` is enough and takes a minute; for a proof file
`tools/bin/verifyfile <the file>` does all of it, and says what the
file costs in axioms of its own.

**The file to prove about has to be loaded itself**, with its
cheats, and not only its `needs`: the proofs of a proof theory
speak about the relations that the theory defines, and in a session
without it those names are free **variables** (PORTING-GUIDE.md
entry 17).  So the test bed of `bvl_constProof` was

```
repl-clone hol-template-cakeml bp
repl-step bp 'loadt "<...>/ml/compiler/backend/proofs/bvl_constProof.ml";;'
```

-- nine minutes, after which every statement of the file is there
as a cheat and a proof is tried against `concl <the cheat>`.  A
*definition* file wants the overloads of its own point in the load
order, which a session that has loaded its `needs` no longer has
(the files after it overload `Var` again): the clone for
`bvl_const`'s own definitions re-ran `hol4_overload "Var"
"bvl_Var"` and the eight others first.
