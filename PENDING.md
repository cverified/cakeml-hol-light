# Definitions that the port does not have yet

The first pass ports every `Datatype`, `Type`, `Overload` and
`Definition` of the 120 definition theories: 3153 blocks, of which
3149 are in (see `tools/coverage.py`).  These are the four that are
not, each of them in its file as a comment that starts with
`PENDING` and listed in `NOT_YET` in `tools/overrides.py`.

| definition | why |
|---|---|
| `misc$Lnext` | HOL4 proves the termination with the induction principle of `llistTheory`'s `eventually`; the port has `eventually` and `LDROP` (in `ml/lib/llist.ml`) but not that induction yet |
| `misc$Lnext_pos` | needs `Lnext` |
| `data_to_word$AnyArith_call_tree` | the value is the call graph that HOL4 computes with `EVAL`; the expression it evaluates has a free variable (`data_conf`), so the port has to compute the value as well |

Two definitions whose value HOL4 computes with ML code are in the
port as the expression that HOL4 evaluates, which is provably the
value that HOL4 gets:

| definition | what the port says |
|---|---|
| `infer$start_type_id` | `ITLIST MAX (Tlist_num :: Tbool_num :: prim_type_nums) 0 + 1` |
| `infer$err_var` (a `Type`) | `tenv_abbrev`, the type of the `t` field of a `type_env` |
