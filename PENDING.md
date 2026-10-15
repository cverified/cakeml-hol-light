# Definitions that the port does not have yet

The first pass ports every `Datatype`, `Type`, `Overload` and
`Definition` of the 120 definition theories.  The ones below are
not there yet; each is in its file as a comment that starts with
`PENDING`, and each is listed in `NOT_YET` in
`tools/overrides.py`.

| definition | why |
|---|---|
| `misc$Lnext` | HOL4 proves the termination with the induction principle of `llistTheory`'s `eventually`; the port has `eventually` (in `ml/lib/llist.ml`) but not that induction yet |
| `misc$Lnext_pos` | needs `Lnext` |
| `data_to_word$AnyArith_call_tree` | the value is HOL4 ML code (`^(th_FF |> concl |> rand)`) |
| `infer$start_type_id` | the value is HOL4 ML code (`^(EVAL ... |> rconc)`) |
| `infer$err_var` (a `Type`) | the type is HOL4 ML code (`type_of ``primTypes$prim_tenv.t``) |

The three ML-code ones are definitions whose value HOL4 computes
when the theory is built.  The port will state them as the
expression that HOL4 evaluates (which is provably the value HOL4
gets), with a comment.
