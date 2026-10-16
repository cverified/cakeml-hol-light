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

Once a run is over, `hol-seq` has the ancestors of every file
loaded, which is what `tools/bin/retry` uses: it loads the phrases
of a file from the one that failed on, in a clone of `hol-seq`
(the session `hol-try`), so that a fix is tried without loading
the ancestors again.

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

`tools/bin/holclean` kills every session except `hol-base`,
`hol-template-cakeml` and `hol-seq`, the session of a run (which
`FORCE=1 holclean` kills as well).  It killed a run of 65 files
before it spared `hol-seq`.
