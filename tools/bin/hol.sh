#!/bin/sh
# hol.sh shim: the tmux server was started with another opam
# switch in its environment, which makes the real hol.sh load
# the wrong findlib (and then fail to find camlp5)
unset OCAMLTOP_INCLUDE_PATH
eval `opam env --switch hol-light --set-switch`
unset OCAMLTOP_INCLUDE_PATH
exec /home/freek/.opam/hol-light/bin/hol.sh "$@"
