# Porting guide: the HOL4 idioms, and what the port does

_A running record of the HOL4 idioms that cost work to port, and of
how each one was handled.  It is written as the port goes: **an idiom
that took more than ten minutes to get right gets an entry here**, so
that the next file that meets it does not pay for it again.  The
sources use the same two dozen idioms ten thousand times, so an entry
is read far more often than it is written._

_This is not a style guide for the port (`CLAUDE.md`) and not the
plan (`PLAN.md`); it is the part of the work that is knowledge rather
than text: what HOL4 means by a word, why HOL Light does not have it,
and what stands in its place._

## How to add an entry

Six headings, in this order, and the last two are the ones that pay:

- **The idiom** -- the HOL4 line as a source writes it, with the file
  and the line, so it can be looked up.
- **What it means** -- what HOL4's implementation actually does, read
  off HOL4's own sources (`hol4-src/`), not guessed from the name.
- **What resisted** -- why the obvious HOL Light counterpart is not
  one.
- **What the port does** -- the answer, with the tactic or the lemma
  that implements it.
- **Where it lives** -- file and name, so it can be used.
- **Dead ends** -- every version that did not work and why.

An entry is never deleted when a better answer is found: the dead
ends are the part that saves the time.  Give the idiom a number and
add it to the index.

## Index

| # | HOL4 | the port |
|---|---|---|
| 1 | `case x of` in a term, `every_case_tac` | `EVERY_CASE_TAC` |
| 2 | `Cases_on` on a compound term | `CASES_ON_TAC` |
| 3 | `rveq` | `VAR_EQ_TAC` |
| 4 | `imp_res_tac` of a two-part hypothesis | `RES2_TAC` |
| 5 | `recInduct f_ind`, `completeInduct_on` | `num_WF`, by hand |
| 6 | a definition unfolded into a `match` | `MATCH_REDUCE_TAC` |
| 7 | `fs`, `rw`, `simp`, the stateful simpset | written out, always |
| 8 | an `Overload` brought to the front | `front_overloads` |
| 9 | two files that bind the same `foo_def` | `cake_def "<const>"` |
| 10 | a library theorem HOL Light has not | `ml/lib/lemmas.ml` |

## 1. `case x of` in a term, and `every_case_tac`

_The gate of phase three: the 228 CakeML sources use
`every_case_tac`, `CaseEq`, `AllCaseEqs` or a `*CASE_TAC` **7,559
times in 145 of them**, over the 2,809 `case` expressions of their
definitions and statements.  Everything else in this guide is small
beside it._

### The idiom

`bvi_letProofScript.sml:131`:

```
Theorem evaluate_SNOC_Rval:
   evaluate (SNOC x y,env,s) = (Rval a,r) ==> ...
Proof
  fs [evaluate_SNOC] \\ every_case_tac \\ fs []
  \\ imp_res_tac evaluate_SING_IMP \\ rw []
QED
```

`evaluate_SNOC` is an equation whose right hand side is a `case`:

```
evaluate (SNOC x xs,env,s) =
  case evaluate (xs,env,s) of
    (Rval vs,s2) => (case evaluate ([x],env,s2) of
                       (Rval v,s1) => (Rval (vs ++ v),s1)
                     | t => t)
  | t => t
```

After `fs [evaluate_SNOC]` the goal holds a **term** of the shape
`case evaluate (...) of ...`, nested twice.  `every_case_tac` takes
it apart into the four combinations (`Rval`/`Rerr` of each inner
evaluation), and in each of them the `case` disappears and leaves an
ordinary equation between pairs.

The scrutinee is not a variable but `evaluate (xs,env,s)`, an
application of a recursively defined function, so

- it cannot be taken apart by an induction or by naming a variable:
  the case analysis is on a *compound term*, and
- its **identity has to survive** the case analysis, because the
  next line of the proof (`imp_res_tac evaluate_SING_IMP`) is about
  *that* evaluation: it needs the hypothesis `evaluate ([x],env,s2) =
  (Rval v,s1)` to still be there.

A case analysis that only replaced the term by `(Rval v,s1)`
everywhere would satisfy the `case` and lose the proof.

### What it means

`every_case_tac` is `BasicProvers.EVERY_CASE_TAC`
(`hol4-src/src/basicProof/BasicProvers.sml:820`):

```sml
fun EVERY_CASE_TAC goal =
 let val rws = case_rwlist()
     val case_conv = PURE_CASE_SIMP_CONV rws
     val asm_rule = BETA_RULE o Rewrite.REWRITE_RULE rws
     fun tac a = (PURE_FULL_CASE_TAC THEN use_new_assum a THEN
                  RULE_ASSUM_TAC asm_rule THEN
                  CONV_TAC case_conv) a
 in REPEAT tac
 end goal;
```

Four moving parts, and every one of them matters:

1. **`PURE_FULL_CASE_TAC`** (`:694`) looks through the goal *and the
   assumptions* for a subterm that is a fully applied case expression
   whose scrutinee is free in the goal, and does `Cases_on` on that
   scrutinee.  The search is `first_subterm`/`case_find_subterm`
   (`:652`), which goes **innermost first** -- the deepest case, not
   the outermost one.
2. **`Cases_on` on a compound term** ends in `TERM_INTRO_TAC` (`:72`):

   ```sml
   val TERM_INTRO_TAC = STRIP_ALL_THEN
     (fn th => TRY (SUBST_ALL_TAC th) THEN ASSUME_TAC th);
   ```

   It takes the type's `nchotomy` (`!x. (?v. x = Rval v) \/ (?e. x =
   Rerr e)`), instantiates it at the term, splits the disjunction,
   and in each branch **substitutes the equation everywhere and keeps
   it as an assumption**.  That is the answer to the identity problem
   above.  For a scrutinee that *is* a variable, `VAR_INTRO_TAC`
   (`:69`) only substitutes -- the equation would be redundant.
3. **`use_new_assum`** (`:790`) throws away the reflexive assumptions
   the split produced, rewrites with the new assumptions and rewrites
   the old assumptions with them.
4. **`CASE_SIMP_CONV`** (`:731`) rewrites with `case_rwlist()`: the
   **case definition theorems** of every datatype in the TypeBase,
   plus distinctness and injectivity, cached once.

Step 4 is the one with no counterpart in HOL Light, and it is why
HOL4's version is robust.  In HOL4,

```
case x of Rval v => f v | Rerr e => g e
```

is *syntax* for `result_CASE x (\v. f v) (\e. g e)`, where
`result_CASE` is an ordinary constant that the `Datatype` declaration
defines, with ordinary equations:

```
result_CASE (Rval v) f g = f v
result_CASE (Rerr e) f g = g e
```

So a case expression disappears by **rewriting**.  If the scrutinee
is not a constructor application, no equation matches and nothing
happens: no decision, no failure, no garbage.  `Cases_on` makes it a
constructor application, the equation then fires, and `BETA_RULE`
cleans up.

### What resisted

HOL Light has no case constants.  `match x with ...` is syntax for

```
_MATCH x (_SEQPATTERN arm1 (_SEQPATTERN arm2 ...))
```

where an arm is `\u v. ?vs. _UNGUARDED_PATTERN (GEQ pat u) (GEQ body
v)`, and the only way to get rid of one is `MATCH_CONV`
(`hol-light/ind_types.ml:1421`), which is a **decision procedure**:
it tries to decide whether the pattern matches the scrutinee.

| | HOL4 | HOL Light |
|---|---|---|
| a `case` is | an application of `ty_CASE` | `_MATCH x (_SEQPATTERN …)` |
| removing one is | rewriting its equations | deciding a match |
| scrutinee not a constructor | nothing happens | **an epsilon appears** |

`MATCH_CONV` on an undecidable scrutinee does not fail; it returns

```
if ... then @GEN%PVAR%4210. ... else @x. false
```

and the goal is gone.  Worse, once one of those is in the goal, the
next reduction grows it.  So the port's representation of a `case` --
which is faithful to what the source *says*, and phase two's test is
that a source and its port read the same -- is the wrong
representation for *proving*.

Two routes were open:

**Route A -- a case constant per datatype, as HOL4 has.**
`ml/lib/define.ml` would define, for every datatype it makes,

```
let result_CASE = new_recursive_definition result_RECURSION
  `(result_CASE (Rval v) f g = f v) /\
   (result_CASE (Rerr e) f g = g e)`
```

(mechanical: one clause per constructor, straight from the
`RECURSION` theorem the port already has), and `tools/port.py` would
write a `case` of a source as an application of it.  Then the HOL
Light `every_case_tac` is HOL4's, line for line, with `REWRITE_TAC`
where HOL4 has its simpset, and nothing can produce an epsilon
because nothing decides anything.  The cost is a generator change
that touches 2,809 `case`s, a full run to re-read the statements, and
a port whose text drifts from the source: `result_CASE (evaluate (…))
(\vs s2. …) (\t. t)` where the source says `case evaluate (…) of …`.

**Route B -- keep the `match`, fix the tactic.**  Do what HOL4 does,
with `MATCH_CONV` only ever applied where it cannot misfire.  Local,
no re-run, no drift.  **Route B was built, and it works.**

### What the port does

`EVERY_CASE_TAC` (`ml/lib/tactics.ml`).  On the goal of
`evaluate_SNOC_Rval` it does in 8 seconds what HOL4 does:

```
  0 [`evaluate (y,env,s) = Rval a',y'`]
  1 [`evaluate ([x],env,y') = Rval a'',y''`]
`Rval (a' ++ a''),y'' = Rval a,r ==> LENGTH y = LENGTH a`
```

one subgoal, the match gone, both equations kept, the impossible
branches closed.  It took five pieces:

1. the **innermost** scrutinee first (`scruts_of_goal`, sorted by
   depth -- HOL4's `case_find_subterm`);
2. **keep the equation** of a compound scrutinee (`CASES_ON_TAC`,
   entry 2 -- HOL4's `TERM_INTRO_TAC`);
3. **close the impossible branches** right after the split, with the
   distinctness and injectivity of that type (`case_rws` -- HOL4's
   `use_new_assum` and `CASE_SIMP_CONV`).  Without this the goals
   multiply with every split and the tactic disappears into a tree of
   thousands;
4. HOL Light's own **`UNWIND_CONV`**, which clears the guard that
   `MATCH_CONV` leaves for a pattern that binds variables (`if ?vs.
   vs = a' then ...`).  `MATCH_CONV` and `UNWIND_CONV` are defined
   together in `ind_types.ml`; they are meant to be used together;
5. and `VAR_EQ_TAC` (entry 3).

The reduction step is guarded: a `MATCH_CONV` whose result contains
an epsilon term is **rejected**, which is what keeps the undecidable
scrutinee from eating the goal.

```ocaml
let SAFE_MATCH_REDUCE_TAC =
  let bad t = can (find_term is_select) t in
  let conv tm = match tm with
      Comb(Comb(Const("_MATCH",_),_),_) ->
        let th = CHANGED_CONV MATCH_CONV tm in
        if bad (rand(concl th)) then failwith "SAFE_MATCH_REDUCE"
        else th
    | _ -> failwith "SAFE_MATCH_REDUCE" in
  CHANGED_TAC(REPEAT(CONV_TAC(ONCE_DEPTH_CONV (CHANGED_CONV conv))));;
```

and the loop is bounded, because a step that only adds an assumption
is progress that no goal measure sees:

```ocaml
let EVERY_CASE_TAC =
  let step = ((CASE_SPLIT_TAC THEN TRY SAFE_MATCH_REDUCE_TAC) ORELSE
              SAFE_MATCH_REDUCE_TAC) THEN MATCH_TIDY_TAC in
  let rec go k gl = if k <= 0 then ALL_TAC gl
                    else (try (step THEN go (k - 1)) gl
                          with Failure _ -> ALL_TAC gl) in
  go 10;;
```

### Where it lives

`ml/lib/tactics.ml`: `EVERY_CASE_TAC`, and under it
`SAFE_MATCH_REDUCE_TAC`, `CASE_SPLIT_TAC`, `scruts_of_goal`,
`case_rws`, `MATCH_TIDY_TAC`, `is_con_app`, `constructors_of`.
`match_scruts` and `cases_of` are in `ml/lib/define.ml`.

### Dead ends

Four tactics that did not work, in the order they were written:

1. `ONCE_DEPTH_CONV MATCH_REDUCE_CONV` does nothing at all.
   `MATCH_REDUCE_CONV` is a `REPEATC`, which **never fails**, so
   `ONCE_DEPTH_CONV` is satisfied at the top of the term and never
   descends.  (A `REPEATC` of anything is unusable as the argument of
   a `*_DEPTH_CONV`.)
2. `REPEAT (CONV_TAC (ONCE_DEPTH_CONV MATCH_CONV))` spins:
   `MATCH_CONV` can return a **no-change theorem** (`|- t = t`), so
   the `REPEAT` never ends.  Wrap it in `CHANGED_CONV`.
3. The epsilon term above: an unguarded `MATCH_CONV` on an
   undecidable scrutinee silently destroys the goal.  Reject any
   result containing `is_select`.
4. The scrutinee searched **outermost first**.  The outer case is
   then split while the inner scrutinee is still a compound term, and
   the next reduction meets exactly case 3.  HOL4 searches innermost
   first, and so must the port.

And two bugs inside the working version:

- `is_con_app` compared **constants**, so the `CONS` of a `num list`
  was not the polymorphic `CONS` of `constructors_of` and every
  constructor application looked like a splittable scrutinee.
  Compare the **names**.
- the goals multiplied without piece 3 above: eleven splits of a
  four-constructor type is not a proof.

## 2. `Cases_on` on a compound term

### The idiom

`Cases_on \`evaluate (xs,env,s)\`` -- case analysis on something that
is not a variable, used in nearly every semantics proof, and the
inner step of entry 1.

### What it means

`BasicProvers.TERM_INTRO_TAC` (`:72`): instantiate the type's
`nchotomy` at the term, split the disjunction, and in each branch
**substitute the equation everywhere and keep it as an assumption**.
A variable gets `VAR_INTRO_TAC` (`:69`), which only substitutes.

### What resisted

HOL Light's `STRUCT_CASES_TAC` rewrites **the goal only**: the
assumptions keep the old term, so an induction hypothesis or an
`evaluate` equation in the assumptions is left talking about a term
that the goal no longer contains.  `ASM_CASES_TAC`-style splitting
loses the equation instead.  Neither is `Cases_on`.

### What the port does

```ocaml
let CASES_ON_TAC t =
  let th = if prod_type (type_of t) then ISPEC t PAIR_SURJECTIVE
           else ISPEC t (cases_of (type_of t)) in
  let use eq = if is_var t then SUBST_ALL_TAC eq
               else TRY(SUBST_ALL_TAC eq) THEN ASSUME_TAC eq in
  (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN use)) th;;
```

`SUBST_ALL_TAC` is the one that does the assumptions too, which is
why this and not `STRUCT_CASES_TAC`.  A pair needs
`PAIR_SURJECTIVE`, because a product has no `cases_of`.

### Where it lives

`ml/lib/tactics.ml`, `CASES_ON_TAC`.  `LIST_CASES_TAC names` in the
same file is the older, weaker thing (goal only, by variable name);
use `CASES_ON_TAC` whenever the assumptions matter, which for an
induction is always.

### Dead ends

- `LIST_SPLIT_TAC` took **every** list variable of the match apart,
  which loses the list the induction hypothesis is about; naming the
  variables (`LIST_CASES_TAC ["env";"env2"]`) fixed that but not the
  assumptions.
- `SPEC_TAC(\`a:bvlSem_v list\`,\`a:bvlSem_v list\`)` quantified
  **vacuously**, because the variable's type in the statement is a
  type variable and the written type is a different type: the
  resulting `!a. ...` is about a fresh `a`.  Use `GEN_TAC` per
  variable, or find the variable in the goal and `ISPEC` what is
  found (what `LIST_CASES_TAC` does).

## 3. `rveq`

### The idiom

`rveq` (and `var_eq_tac`), on nearly every line after a case split.

### What it means

Use up the assumptions that are equations **between variables**, by
substituting them everywhere, and leave the rest alone.

### What resisted

The HOL Light reflex is `ASM_REWRITE_TAC[]` or
`REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC)`, which uses up *every*
equation -- including `evaluate (xs,env,s) = (Rval vs,s2)`, the one
the proof is about (entry 1).  The remaining goal is then
unprovable: nothing says what the evaluation returned any more.

### What the port does

```ocaml
let VAR_EQ_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if is_var l || is_var r then SUBST_ALL_TAC th
    else failwith "VAR_EQ_TAC"));;
```

### Where it lives

`ml/lib/tactics.ml`, `VAR_EQ_TAC`.

## 4. `imp_res_tac` of a lemma with a two-part hypothesis

### The idiom

`imp_res_tac evaluate_delete_var_Rval` where the lemma is
`A /\ B ==> C` and `A` and `B` are two separate assumptions.

### What it means

HOL4 resolves the lemma against the assumptions, matching the
conjunction against any pair of them.

### What resisted

`FIRST_ASSUM(MATCH_MP_TAC ...)` matches one assumption, not a pair,
and `ASM_MESON_TAC[lemma]` does the job but can take minutes: on the
finishes of this file MESON went `0..0..2..8..…126903` and had to be
interrupted.  A proof that ends in an unbounded search is not a
proof the port can afford 10,332 times.

### What the port does

Resolve the pair explicitly and deterministically:

```ocaml
let RES2_TAC lemma =
  FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
    MP_TAC(MATCH_MP lemma (CONJ th1 th2))));;
```

### Where it lives

`ml/lib/tactics.ml`, `RES2_TAC`.

### Dead ends

`ASM_MESON_TAC` as the general finish.  It is fine on a goal that is
propositional once the equations are in place, and it explodes as
soon as an arithmetic or a list function is in scope.  Prefer an
explicit `MATCH_MP_TAC`/`RES2_TAC`/`VAR_EQ_TAC` finish, and keep the
MESON lemma list short when it is used at all (`CLAUDE.md`).

## 5. `recInduct f_ind` and `completeInduct_on`

### The idiom

`bvi_letProofScript.sml:220`: `completeInduct_on \`list_size
exp_size xs\`` and then eleven `Resume` blocks; elsewhere
`recInduct compile_ind`.

### What it means

HOL4's `Definition` proves termination and **keeps the induction
theorem it used**, as `f_ind`: one antecedent per clause of the
definition, with exactly the induction hypotheses that clause's
recursive calls allow.  `recInduct` applies it.  `completeInduct_on
m` is the same by hand on a measure `m`, through `WF` induction on
`<`.

### What resisted

HOL Light's `define` does not keep an induction theorem, and for a
definition whose termination was *cheated* (phase one) there is
nothing to keep.  So there is no counterpart to `recInduct
compile_ind`, and the eleven clauses have to be reached another way.

### What the port does

Measure induction by hand, in three steps:

1. generalise the measure into a variable, because `num_WF` is about
   a `!n`:

   ```ocaml
   SUBGOAL_THEN
     `!n xs .... list_size bvi_exp_size xs = n /\ ... ==> ...`
     (fun th -> MESON_TAC[th]) THEN
   ```

2. `MATCH_MP_TAC num_WF THEN REPEAT STRIP_TAC`;
3. **use the measure equation right to left before any split**:
   `FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)`, so the induction hypothesis
   is about the size of the list and not about `n`.  Then
   `CASES_ON_TAC` on the list (entry 2), and each constructor case
   discharges its hypothesis with a size inequality.

The cost is real: HOL4 gets the eleven cases from one word, and the
port writes the scaffolding.  It is about ten lines a theorem, and
they are the same ten lines every time.

### Where it lives

No tactic yet -- the scaffolding is written out in each proof (see
`proofs/compiler/backend/proofs/bvi_letProof.prf`,
`evaluate_env_rel` and `compile_code_labels`).  A `MEASURE_INDUCT_TAC`
that takes the measure term and does the three steps is the obvious
next utility; it goes in `ml/lib/tactics.ml` when a second file wants
it.

### Dead ends

- `POP_ASSUM_LIST` and friends to reorder the assumptions before the
  induction: the order is not the problem, the direction of the
  measure equation is.
- `SPEC_TAC` to generalise -- see the vacuous quantification in
  entry 2.

## 6. A definition unfolded into a `match`

### The idiom

`fs [compile_def]`, the first line of a hundred proofs.

### What it means

In HOL4 the clauses of a definition are separate equations, and a
`fs` with them rewrites whichever clause applies.

### What resisted

The port makes a definition by patterns into **one** equation whose
right hand side is a `match`, so unfolding it gives a goal with a
`match` in it, and the clause only appears once the match is reduced
against the right constructor.  So the port's `fs [compile_def]` is
two steps: rewrite, then reduce.

### What the port does

`MATCH_REDUCE_TAC` after the rewrite (and `cake_def "<constant>"`
for the theorem itself, entry 9):

```ocaml
let MATCH_REDUCE_TAC =
  REPEAT(CHANGED_TAC(CONV_TAC(ONCE_DEPTH_CONV MATCH_CONV)));;
```

This is the **unguarded** version and it is kept because nine proofs
of the first file use it, where the scrutinee is a variable that has
just been taken apart and nothing can misfire.  In a proof where the
scrutinee is a compound term, use `EVERY_CASE_TAC` (entry 1), never
this.

### Where it lives

`ml/lib/tactics.ml`: `MATCH_REDUCE_TAC`, and `MATCH_REDUCE_CONV` /
`MATCH_SCRUT_TAC` in `ml/lib/define.ml` from phase two.

## 7. `fs`, `rw`, `simp`, and the stateful simpset

### The idiom

Every second line of every CakeML proof: `fs []`, `rw []`, `simp
[foo]`, `full_simp_tac (srw_ss()) [...]`.

### What it means

Simplification with HOL4's **stateful simpset**: the `[simp]`
theorems of every theory loaded, every datatype's distinctness,
injectivity and case equations from the TypeBase, arithmetic and
list decision procedures, plus the theorems written in the brackets.
`fs` also simplifies the assumptions with each other and the goal
with the assumptions; `rw` strips the goal first.

### What resisted

The port has no simpset and does not replay HOL4's automation
(`CLAUDE.md`: the `[simp]` attributes are kept because the source
says them, but they are not load bearing).  So a one-word `fs []` is
in general *not* one HOL Light tactic, and what it expands to has to
be read off the goal:

- `REWRITE_TAC`/`ASM_REWRITE_TAC` with the theorems named in the
  brackets **plus** the distinctness and injectivity of every type
  the goal splits on (`distinctness "option"`, `injectivity
  "option"`, `PAIR_EQ`, `NOT_CONS_NIL`, `CONS_11`, `NOT_SUC`,
  `SUC_INJ` -- the port's recurring list);
- `ARITH_TAC` where the simplification was arithmetic;
- `ASM_MESON_TAC` with a short list where it was propositional, and
  an explicit finish where it was not (entry 4).

This is where most of the hand work of a proof goes, and it is the
reason phase three is written by hand and not translated.

### What the port does

`MATCH_TIDY_TAC` collects the recurring part of the list:

```ocaml
let MATCH_TIDY_TAC =
  TRY(CONV_TAC(REDEPTH_CONV UNWIND_CONV)) THEN
  TRY(REWRITE_TAC[UNWIND_THM1; UNWIND_THM2; EXISTS_REFL;
                  NOT_CONS_NIL; CONS_11; NOT_SUC; SUC_INJ; PAIR_EQ;
                  distinctness "option"; injectivity "option"]);;
```

and `EVERY_CASE_TAC` runs it after every split, which is what makes
the split survivable.

### Where it lives

`ml/lib/tactics.ml`, `MATCH_TIDY_TAC`, `case_rws`.

## 8. An `Overload` brought to the front

### The idiom

```
Overload compile = “bvi_let$compile”
```

or `bring_to_front_overload "compile" {Thy = "bvi_let", Name =
"compile"}` at the head of a proof script.

### What it means

Several theories define a `compile`; the line says which one this
file's statements mean.  It is **part of what the statements say**,
not a presentation detail.

### What resisted

The generator ignored it at first, and `compile` in `bvi_letProof`
resolved to `clos_mti_compile`.  The statement parsed, the file
loaded, every check passed, and all seventeen theorems were about
another constant.  There is no error message for this; it is found
by reading the statement next to the source.

### What the port does

`tools/port.py` writes the overload (`Porter.front_overloads`), in
16 files.  Five calls of five more go through an ML helper of the
source and get a pointer comment instead.  `tools/nohol4.py` has a
test that a pointer is a real file and line range.

### Where it lives

`tools/port.py`, `front_overloads`.

### Dead ends

Trusting that a file which loads and checks is a file that says what
the source says.  It is not: a wrong overload is invisible to every
mechanical check the port has.  When a proof will not go through and
the statement looks right, **print the constant** (`type_of`, or
`concl` of the theorem) before anything else.

## 9. Two files that bind the same `foo_def`

### The idiom

Each HOL4 `Definition compile_def:` binds `compile_def` **in its own
theory**, and 28 files of the port have one.

### What it means

In HOL4 the name is qualified by the theory
(`bvi_letTheory.compile_def`).

### What resisted

OCaml has one namespace: the port's `compile_def` is whichever file
loaded last, so a proof that writes `compile_def` gets a definition
from another theory, with no error.  Rekeying 355 overrides to
unique names was the obvious fix and the wrong one: it would make
the port's text differ from the source's.

### What the port does

A registry keyed by the **constant**, which is unique:

```ocaml
let cp = cake_def "bvi_let_compile" in ...
```

`cake_note_def` records every definition that `cake_define*`,
`cake_cheat` or `cake_inductive` makes; `cake_def` looks it up.

### Where it lives

`ml/lib/define.ml`: `the_defs`, `cake_note_def`, `cake_def`,
`cake_defs`.

## 10. A HOL4 library theorem HOL Light has not

### The idiom

`fs [EL_DROP]` -- a list lemma of HOL4's `rich_listTheory` that HOL
Light's `lists.ml` does not have.

### What it means

HOL4's library is bigger in the places CakeML uses, and a proof line
that is one rewrite in HOL4 is a lemma to prove in the port.

### What the port does

Prove it once and put it where it costs nothing to reload:

```ocaml
let EL_DROP = prove
 (`!l n k. n + k < LENGTH l ==> EL n (DROP k l) = EL (n + k) l`, ...)
```

The rule for **where** a lemma goes, which is about what a change to
it costs (`SESSIONS.md`):

- used by more than one proof: `ml/lib/lemmas.ml`, which defines
  nothing and so can be `#use`d into a running session in under a
  second (`tools/bin/reload`);
- used by one proof: inside that proof, as a `let` or a
  `SUBGOAL_THEN`;
- a HOL4 *library theory* that CakeML needs a real part of: its own
  file in `ml/lib/` (`ml/lib/finite_map.ml`, `llist.ml`, ...), which
  costs the session when it changes, so those changes are batched
  between files.

### Where it lives

`ml/lib/lemmas.ml`.

---

_Entries are added as the idioms are met.  The ones expected next,
from reading the sources: `CaseEq`/`AllCaseEqs` (the rewriting form
of entry 1, 7,559 uses together with `every_case_tac`), `fix_clock`
and the clock arithmetic of `evaluate`, `qexists_tac`/`qpat_x_assum`
with term quotations whose variables are not the goal's, `Induct_on`
on a mutually recursive datatype, and `metis_tac` with a long list._
