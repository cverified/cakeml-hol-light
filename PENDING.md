# Definitions whose form deviates from HOL4's

The first pass ports every `Datatype`, `Type`, `Overload`,
`Definition` and `Inductive` of the 227 files of the port: 4165
blocks, and all 4165 of them are in (see `tools/coverage.py`).
`tools/fidelity.py` checks that no definition lost a name or a
constructor argument on the way.  There is nothing pending.

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

Five definitions of `compiler` are not ported: the three that
compile Pancake and the two command line drivers that call them
(see `ISSUES.md`).  Pancake is outside the port.

One constant has no value in the port, because HOL4 computes it
with ML code of its own that the port cannot run:

| constant | what HOL4 does |
|---|---|
| `word_bignum$mc_iop_code` | `to_deep` of `word_bignumScript.sml` runs the shallow definitions of the bignum routines through a translator written in ML and states the deep embedding that it finds.  The port declares the constant (`cake_declare`, which adds no axiom) and says nothing about its value |

One definition of the first pass is not ported, because HOL4
makes it from a theorem that the second pass has to prove first
(`new_specification` of a Skolem form):

| definition | what HOL4 does |
|---|---|
| `pegComplete$fFail` (`fFAIL1`, `fFAIL2`) | the Skolem functions of `peg_respects_firstSets`, which say where the parser fails on a token outside the first set.  Only the proofs of `pegComplete` use them |

One definition is proved to exist by hand, because HOL Light
cannot find the termination argument that HOL4 gives:

| definition | how |
|---|---|
| `misc$Lnext` | HOL4 proves the termination with the induction principle of `llistTheory`'s `eventually`; the port proves the existence of the function with `new_specification`, from the number of steps to the first tail that satisfies the predicate (`MINIMAL_SUC`, `eventually_LTL` and `LDROP_SUC` of `ml/lib/llist.ml`) |
