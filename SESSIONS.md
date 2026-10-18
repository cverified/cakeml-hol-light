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
