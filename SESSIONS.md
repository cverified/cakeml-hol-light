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
