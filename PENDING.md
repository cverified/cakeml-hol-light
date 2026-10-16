# Definitions whose form deviates from HOL4's

The first pass ports every `Datatype`, `Type`, `Overload`,
`Definition` and `Inductive` of the 238 files of the port: 4198
blocks, of which 4182 are in (see `tools/coverage.py`); the
sixteen that are not are the eleven tail recursive definitions
of `unify` and the five Pancake definitions of `compiler`
below.
`tools/fidelity.py` checks that no definition lost a name or a
constructor argument on the way.

Three of them are definitions whose value HOL4 computes with ML
code (`EVAL` or `type_of`) and states as the value it finds.  The
port states the expression that HOL4 evaluates, which is provably
the same value; `REPLACE` in `tools/overrides.py` has the text.
(To compute the value in HOL Light instead, the call by value
machinery of `compute.ml` of the HOL Light distribution, which is
a translation of HOL4's `computeLib`, and the fuller version at
https://github.com/hol-light-family/compute-hol-light are what to
use; nothing of the first pass evaluates anything.)

| definition | what the port says |
|---|---|
| `infer$start_type_id` | `ITLIST MAX (Tlist_num :: Tbool_num :: prim_type_nums) 0 + 1` |
| `infer$err_var` (a `Type`) | `tenv_abbrev`, the type of the `t` field of a `type_env` |
| `mlint$exp_tm` (the value that `num_to_chars` divides by) | `10 EXP exp_for_dec_enc` |
| `data_to_word$AnyArith_call_tree` | `full_call_graph AnyArith_location (fromAList (stubs (:1) ...))`, the call graph of the bignum stubs for a configuration with `call_empty_ffi` and `has_longdiv` false |

In HOL4's `AnyArith_call_tree` the type of the stubs and the other
fields of the configuration are free, and `EVAL` computes a value
that has neither in it, so the value does not depend on them; the
port instantiates the type with `:1` and the configuration with
`ARB`, which is therefore the same call graph.

Five definitions of `compiler` are not ported: the three that
compile Pancake and the two command line drivers that call them
(see `ISSUES.md`).  Pancake is outside the port.

One constant has no value in the port, because HOL4 makes it in
a way that HOL Light has no counterpart for.  The port declares
it (`cake_declare`, which adds no axiom) and says nothing about
its value:

| constant | what HOL4 does |
|---|---|
| `word_bignum$mc_iop_code` | `to_deep` of `word_bignumScript.sml` runs the shallow definitions of the bignum routines through a translator written in ML and states the deep embedding that it finds |

Four constants of the triangular unification algorithm are
defined by the graph of their equation, because HOL4 defines
them with a schema (`xDefineSchema`, for `vwalk` and `walkstar`)
or with `new_specification` out of a theorem about a tail
recursive version (`unify`): the equation holds under the
hypothesis that the substitution is wellfounded (`wfs s`), and
the recursion terminates only then.  The port states the graph
of the equation as an inductive relation and takes a value of
it (`vwalk s v = @r. VWALKR s v r`), which adds no axiom; HOL4's
equation is a theorem of the second pass.  (`unifDef$oc` is a
`Hol_reln` in HOL4 already, and is ported as it stands.)

Eleven definitions of `unify` are not ported: the tail recursive
versions of the unification algorithm, which HOL4 makes with ML
code (`tcallify_th` of `tcallUnifLib` turns the equation of a
function into the step function of a `TAILREC`).  The port cannot
run that code, and nothing outside that part of the file uses
what it makes (`cvwalk_code`, `tcvwalk`, `tcwalk`, `kcocwl_code`,
`tcocwl`, `kcwalkstarwl_code`, `tcwalkstarwl`, `tcwalkstar_p1`,
`tcwalkstar_p2`, `cunify_code` and `tcunify`).

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
