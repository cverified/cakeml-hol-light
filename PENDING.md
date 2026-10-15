# Definitions whose form deviates from HOL4's

The first pass ports every `Datatype`, `Type`, `Overload` and
`Definition` of the 120 definition theories: 3153 blocks, and all
3153 of them are in (see `tools/coverage.py`).  There is nothing
pending.

Three of them are definitions whose value HOL4 computes with ML
code (`EVAL` or `type_of`) and states as the value it finds.  The
port states the expression that HOL4 evaluates, which is provably
the same value; `REPLACE` in `tools/overrides.py` has the text.

| definition | what the port says |
|---|---|
| `infer$start_type_id` | `ITLIST MAX (Tlist_num :: Tbool_num :: prim_type_nums) 0 + 1` |
| `infer$err_var` (a `Type`) | `tenv_abbrev`, the type of the `t` field of a `type_env` |
| `data_to_word$AnyArith_call_tree` | `full_call_graph AnyArith_location (fromAList (stubs (:1) ...))`, the call graph of the bignum stubs for a configuration with `call_empty_ffi` and `has_longdiv` false |

In HOL4's `AnyArith_call_tree` the type of the stubs and the other
fields of the configuration are free, and `EVAL` computes a value
that has neither in it, so the value does not depend on them; the
port instantiates the type with `:1` and the configuration with
`ARB`, which is therefore the same call graph.

One definition is proved to exist by hand, because HOL Light
cannot find the termination argument that HOL4 gives:

| definition | how |
|---|---|
| `misc$Lnext` | HOL4 proves the termination with the induction principle of `llistTheory`'s `eventually`; the port proves the existence of the function with `new_specification`, from the number of steps to the first tail that satisfies the predicate (`MINIMAL_SUC`, `eventually_LTL` and `LDROP_SUC` of `ml/lib/llist.ml`) |
