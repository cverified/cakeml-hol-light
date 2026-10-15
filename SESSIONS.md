# HOL Light tmux sessions of this project

- `hol-base`
  plain HOL Light (made with `repl-new-template base`, which
  uses the `hol.sh` shim in `tools/bin`)

- `hol-template-cakeml`
  clone of `hol-base` with `ml/lib/preamble.ml` loaded, so with
  `Library/words.ml` and the HOL4 compatibility layer
  (`ml/lib/hol4.ml`, `ml/lib/records.ml`, `ml/lib/define.ml`)

- working sessions are clones of `hol-template-cakeml`

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

## Interrupting and killing

A clone is forked from another HOL Light process, so it is not a
child of the tmux pane: a `C-c` in the pane goes to the `socat`
of the session and ends the session, leaving the process (half a
gigabyte) running.  Therefore

- `repl-int` sends the interrupt to the process itself, whose pid
  the clone writes to `bin/socket/hol-<name>.pid`;
- `repl-kill` interrupts the session first (a busy one would not
  read the `exit`), and kills that process if it is still there.

`tools/bin/holclean` removes what is left of sessions that are
gone.
