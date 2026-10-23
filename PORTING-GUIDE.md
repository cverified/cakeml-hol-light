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
| 11 | `Parse.hide`, a field name | `cake_hide`, and a clean session |
| 12 | a statement that annotates no type | terms taken from the goal |
| 13 | `evaluate_def` with `fix_clock` removed | `fix_clock_evaluate` |
| 14 | the order of a `case` split | the condition before the hypothesis |
| 15 | a non-empty list written as a `SNOC` | `SNOC_CASES` and four laws |
| 16 | a session loaded out of the port's order | the file's own `needs` |
| 17 | a `Definition` not made | `DEFINE_REL`, two size facts |
| 18 | a relation stated as one `match` | its clauses, by `LAND_CONV` |
| 19 | an argument used only for its length | the type written down |
| 20 | `do_app` as one match over every operation | the clause as a lemma |
| 21 | the arguments of a binary operation | `REVERSE`, so the other way |
| 22 | `MAP_FIRST` over a list of lemmas | the attempts delayed |
| 23 | `INT_ARITH` of a goal with a product | `INT_RING` |
| 24 | `memory_rel` unfolded in every proof | `MEMORY_REL_TAC` |
| 25 | a term of a tactic, typed by the parser | `:num`, or the goal's term |
| 26 | a `case` on the value of a function | `EVERY_CASE_TAC`, before reducing |
| 27 | `+`, `-` and `*` of HOL4 | the associativity written out |
| 28 | a type that nests a list of itself | the store's mutual induction |

## The shape of a transformation proof

_**Fifty-three of the port's sixty-one proof theories have an
`evaluate` and an induction**, and they are all the same proof:
a relation between a source state and a compiled one, a main
theorem that says the compiled code evaluates to what the source
does, an induction, and one case per constructor of the language.
`bvi_letProof` is the smallest of them (23 case splits);
`data_to_word_assignProof` has 350.  So the shape is written out
once here, with the library pieces it is made of, and a new file of
this kind starts by filling it in rather than by inventing it._

### The skeleton

```ocaml
(* the pieces: the definitions this file unfolds, by constant *)
let cp = cake_def "<the compiler's constant>" in
let ev = cake_def "<the semantics' constant>" in
let er = cake_def "<the relation's constant>" in
let fce = <that semantics>_fix_clock_evaluate in      (* entry 13 *)
let sz = size_thms "<the language's type>" in
let res_rws = [PAIR_EQ; distinctness "semanticPrimitives_result";
               injectivity "semanticPrimitives_result"] in

(* HOL4's fs, with this file's rewrites in stages (entry 13) *)
let tidy = FS_TAC [[fce]; [fc]] res_rws in
let tidy2 = tidy THEN ASM_FS_TAC THEN tidy in

(* the size side condition of every use of the hypothesis *)
let size_tac_rws rws =
  RULE_ASSUM_TAC(REWRITE_RULE(rws @ (list_size :: sz))) THEN
  REWRITE_TAC(rws @ (list_size :: sz)) THEN ASM_ARITH_TAC in
let size_tac = size_tac_rws [] in

(* HOL4's drule: EV_PAIR_TAC searches, the file instantiates *)
let use_ih_auto =
  EV_PAIR_TAC "<the semantics' constant>" "<the compiler's>"
    (fun (xs,env1,s) rt cargs env2 -> ... ih_ants ...) in

(* the conditions of the semantics are if-then-else as well as
   case, and the condition goes first (entry 14) *)
let deep_case =
  REPEAT(CHANGED_TAC
    (TRY(CHANGED_TAC use_ih_auto) THEN TRY tidy2 THEN
     (COND_SPLIT_TAC ORELSE CASE_SPLIT_TAC ORELSE
      COND_CASES_TAC) THEN TRY tidy2 THEN
     TRY(CHANGED_TAC use_ih_auto) THEN TRY tidy2 THEN
     TRY(ASM_REWRITE_TAC[]))) THEN ... in

(* one tactic per constructor, in the order of the datatype *)
let sub_cases = [...] in
let single_case =
  NAMED_CASES_TAC `x1:<the type>` [<the names>] THENL sub_cases in

MEASURE_INDUCT_TAC `list_size <the size function>` THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
NAMED_CASES_TAC `xs:<the type> list` [[]; ["x1"; "xr"]] THENL
[nil_case; impossible; nil_case; ALL_TAC] THEN
NAMED_CASES_TAC `xr:<the type> list` [[]; ["x2"; "xr2"]] THENL
[single_case; TRY cons_cons_case]
```

### The library pieces, and which entry each one is

| piece | what it stands for | entry |
|---|---|---|
| `MEASURE_INDUCT_TAC` | `recInduct f_ind`, `completeInduct_on` | 5 |
| `EVERY_CASE_TAC` | `every_case_tac` on a statement | 1 |
| `EVERY_CASE_COND_TAC`, `COND_SPLIT_TAC`, `CASE_SPLIT_TAC` | the same with the condition decided first, which is what a branch that uses the hypothesis needs | 14 |
| `NAMED_CASES_TAC`, `CASES_ON_TAC` | `Cases_on`, with names of the proof's own | 2 |
| `FS_TAC`, `ASM_FS_TAC`, `PRUNE_TAC`, `MATCH_TIDY_TAC` | `fs`, `gvs`, `rw` | 7 |
| `VAR_EQ_TAC` | `rveq` | 3 |
| `EV_PAIR_TAC` | `drule`, `imp_res_tac`, for an evaluation | -- |
| `RES1_THEN`, `RES2_THEN`, `RES2_TAC` | `imp_res_tac` of a lemma with two parts | 4 |
| `MATCH_REDUCE_TAC`, `SAFE_MATCH_REDUCE_TAC` | a definition unfolded into a `match` | 6 |
| `RECORD_CASES_TAC` | a field update whose value is its own field | 13 |
| `SNOC_CASES` and its laws, `EL_LEN_APPEND`, `list_size_SNOC`, `list_size_BUTLAST`, `list_size_LAST`, `oEL_*`, `EL_DROP`, `DROP_0` | the library lemmas HOL4 has and HOL Light does not | 10, 15 |

### The order inside a case, which is the part that bites

1. **Unfold** the clause of the semantics on both sides, and rewrite
   with `fix_clock_evaluate` **before** anything expands `fix_clock`
   (entry 13).
2. **Decide the conditions** of the branch -- `COND_SPLIT_TAC`, which
   looks in the assumptions as well as the goal.
3. **Then** take the cases apart, deepest pattern first.
4. **Then** use the induction hypothesis.

Steps 2 and 4 in the wrong order is the one mistake that produces
goals which are not provable rather than merely hard: in the branch
where a condition holds, the result is already decided, so nothing
is known about what was split under it, and the hypothesis's own
side condition cannot be discharged (entry 14).

### What the recipe cost the second time

_`bvl_constProof` is the same transformation one language up
(bvl_const's own comment says bvi_let is the simpler version of
it), and it is the first file the recipe was used on.  What
transferred and what did not is worth knowing before the third:_

- _the three proofs about `delete_var` transferred **as they
  stand**, with the names changed: the statements are the same
  theorem about another language, and bvi_letProof's tactics
  proved them at the first attempt;_
- _so did `compile_eq`, `compile_length`, `compile_HD_SING` and
  `compile_exp_eq` of the definition file, and the skeleton of
  `evaluate_env_rel` (the measure induction, the nine cases, the
  `deep_case` loop, `EV_PAIR_TAC`, `FS_TAC`) -- the main theorem
  took two hours against the day that bvi_letProof's took;_
- _what cost the time was the part bvi_let has not got: the
  constant folding (`SmartOp`), where the port's `do_app` is one
  match over every operation (entry 20), the arguments of an
  operation are reversed (entry 21) and the arithmetic of one
  branch is a ring identity (entry 23).  Two thirds of the work of
  the file was in one theorem, `SmartOp2_thm`._

_The reading of that: the recipe carries the **shape** of a
transformation proof, and what is left per file is what that
transformation does that others do not.  A file whose pass only
rearranges expressions is a day's work with it; a file whose pass
computes (folds constants, allocates registers, lays out memory)
has one theorem in it that the recipe does not touch._

### Before believing a `NOT PROVED`

A test bed built by hand lies about what is wrong, twice over:

- build the session from **the file's own `needs` lines, in the
  file's order**, or an overloaded constructor resolves to another
  language's (entry 16);
- load the file whose constants the proof mentions, or those names
  are free **variables** and the failure is a kernel error that
  names nothing (entry 17).

`grep -E 'CHEATED|cake_conj_list|NOT PROVED'` over the pane after
building a session takes a second and answers both.  What a file
costs is then its own axioms, which is

```ocaml
let pre p t = is_const t &&
  (let n = fst(dest_const t) in
   String.length n > String.length p &&
   String.sub n 0 (String.length p) = p);;
length (filter (fun th -> can (find_term (pre "<the file's prefix>"))
                            (concl th)) (axioms()));;
```

and has to be 0 when the file is done.

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

`Cases_on `evaluate (xs,env,s)`` -- case analysis on something that
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
- `SPEC_TAC(`a:bvlSem_v list`,`a:bvlSem_v list`)` quantified
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

`bvi_letProofScript.sml:220`: `completeInduct_on `list_size
exp_size xs`` and then eleven `Resume` blocks; elsewhere
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

Measure induction by hand, with the measure **bounded** rather than
equal, so that `INDUCT_TAC` is enough and `num_WF` is not needed:

```ocaml
SUBGOAL_THEN
  `!k n d xs. list_size bvi_exp_size xs <= k ==> <the statement>`
  (fun th -> REPEAT GEN_TAC THEN
     MATCH_MP_TAC(SPEC `list_size bvi_exp_size (xs:bvi_exp list)`
                    th) THEN
     REWRITE_TAC[LE_REFL]) THEN
INDUCT_TAC THENL [base_case; step_case]
```

The induction hypothesis is then at `k` and the goal at `SUC k`, so
a clause's recursive call needs its sub-measure `<= k`, which is
what the size clauses and `ASM_ARITH_TAC` give:

```ocaml
let use_ih t =
  SUBGOAL_THEN (cond t)
    (fun c -> FIRST_ASSUM(fun ih -> REWRITE_TAC[MATCH_MP ih c]))
  THEN TRY size_tac
```

The base case `k = 0` is the one that has to be seen to be
impossible: a list of one or more has size `1 + _ + _`, so
`FIRST_ASSUM MP_TAC THEN REWRITE_TAC[list_size; ARITH_RULE `~(1 + a
+ b <= 0)`]` closes it.

A **mutual** induction theorem (`compile_sing_ind`, over an
expression and over a list of them) is the same with a conjunction
under the `!k`, and the two hypotheses are `CONJUNCT1 ih` and
`CONJUNCT2 ih`:

```ocaml
SUBGOAL_THEN
  `!k. (!n d e. bvi_exp_size e <= k ==> ...) /\
       (!n d es. list_size bvi_exp_size es <= k ==> ...)`
  (fun th -> CONJ_TAC THEN REPEAT GEN_TAC THENL
     [MP_TAC(CONJUNCT1(SPEC `bvi_exp_size (e:bvi_exp)` th)); ...]
     THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL]) THEN
INDUCT_TAC THENL [sing_base; CONJ_TAC THENL [part1; part2]]
```

The cost is real: HOL4 gets the eleven cases from one word, and the
port writes the scaffolding.  It is about ten lines a theorem, and
they are the same ten lines every time.

### Where it lives

No tactic yet -- the scaffolding is written out in each proof (see
`proofs/compiler/backend/proofs/bvi_letProof.prf`,
`evaluate_env_rel` and `compile_code_labels`, and
`proofs/compiler/backend/bvi_let.prf`, `compile_sing` and
`compile_length`).  A `MEASURE_INDUCT_TAC` that takes the measure
term and writes the scaffolding is the obvious next utility; it goes
in `ml/lib/tactics.ml` when a second file wants it.

### Dead ends

- The measure as an **equation** (`list_size f xs = n`) with
  `MATCH_MP_TAC num_WF`.  It works, and it needs the equation used
  right to left before any split
  (`FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)`), or the induction
  hypothesis is about `n` and not about the list.  The bounded form
  above has no such step.
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


## 11. A statement that reads as a variable

### The idiom

Not an idiom of HOL4 at all, but the way HOL4's `Parse.hide` and
its record-field accessors come out in the port, and the one bug
class that no mechanical check of the port can see.

### What it means

HOL4 hides a name from its parser (`Parse.hide "error"`) and names a
record field and another constant alike, so the port reads the
statements of a file with those names taken out of the interface:
`cake_hide` and `cake_hide_consts` (`ml/lib/theorem.ml`), set at the
head of a file and set back to `[]` at its end, and
`cake_hidden_read` and `cake_as_vars` around every statement.

### What resisted

Those two are **global state that a file sets and resets**.  A file
that is loaded again (a re-port, or a library file that failed the
first time and that `needs` therefore retries) and that errors in
the middle never reaches the line that sets the state back, so the
hiding stays on -- and the statements of the files after it are read
with a name of their own taken away.  A name that is not in the
interface is read as a **variable**, which typechecks: the statement
is accepted, it reads exactly as the source does, and it says
nothing.

What it looks like: `compile_CONS` in `bvi_letProof` is
`compile ax d (x :: xs) = compile ax d [x] ++ compile ax d xs` with
`compile` a free variable of invented type, which no tactic can
prove and which the port reports as NOT PROVED.  The statement is
right in a clean session and wrong in a dirty one, so a proof that
works interactively fails in the file -- and a *cheat* of the same
statement passes every check the port has.

### What the port does

`cake_fieldvars ()` lists the theorems whose statement fell back to
the variable reading, and it is the first thing to look at when a
proof that works in a session fails in the file:

```ocaml
cake_fieldvars ();;
(* ["semantics_CURRY_I"; "compile_CONS"; "compile_APPEND";
    "evaluate_env_rel"] *)
```

A theorem of the file under work in that list means the session is
dirty, not that the proof is wrong.  The cure is a session in which
nothing is loaded twice: `retemplate` and a closure built from the
template in one go (`SESSIONS.md`).  `tools/bin/checkseq` and
`runall` load every file once, in order, which is why a run does not
see this.

### Dead ends

Reading the port's text.  The statement reads exactly like the
source -- that is the point of the port -- and the difference is in
the parser's state, not in the file.  Before doubting a proof,
check `cake_fieldvars ()` and `length (axioms ())`.


## 12. A statement whose types are invented

### The idiom

A HOL4 statement annotates nothing and lets the elaborator work:

```
Theorem evaluate_compile_exp:
   evaluate ([d],env,s) = (r,t) /\ r <> Rerr (Rabort Rtype_error) ==>
    evaluate ([bvi_let$compile_exp d],env,s) = (r,t)
```

### What it means

HOL4 fixes the type variables of a theory (`:'ffi`, `:'c`) and its
statements inherit them.  The port parses each statement on its own
with `type_invention_warning := false`, so a variable that nothing
constrains gets a **freshly invented** type variable -- the state of
the theorem above is not `('c,'ffi) bviSem_state` but an invented
pair.

### What resisted

Every term a proof writes by hand is then a different term.
An `ISPECL` of `evaluate_env_rel` at a state written as
`s:('c,'ffi)bviSem_state` produces an instance whose antecedent is
not the assumption, and
`MP`, `MATCH_MP`, `UNDISCH_TAC` and `SUBST_ALL_TAC` all fail with no
hint of why: the two terms print identically.  `term_match` on the
printed forms succeeds, which is what makes it so confusing -- the
mismatch is in a type variable's name, and names are not printed.

The same for a list whose element type nothing fixes: `env_rel` is
polymorphic in the port, so the `env2` of its statement is an
`:?A list`, and an `ARITH_RULE` about
`m < LENGTH (e:bvlSem_v list) - v` will not instantiate against
`m < LENGTH env2 - v`.

### What the port does

Take the terms **out of the goal** instead of writing them:

```ocaml
FIRST_ASSUM(fun ev ->
  let tup = rand(lhs(concl ev)) in
  let env_tm = fst(dest_pair(snd(dest_pair tup))) in
  ...)
```

and state an arithmetic side lemma over `:num` alone, with no list
in it, so that `LENGTH env2` matches as a term of type `:num`
whatever the list's element type is.

A second trap in the same place: a statement of a source may
quantify a variable it does not use (`evaluate_env_rel` has a `ys`),
and `MATCH_MP` then hands back `!ys. <conclusion>`, which
`ACCEPT_TAC` does not take.  `SPEC_ALL` it.

### Dead ends

Annotating harder.  A state written as `s:('c,'ffi)bviSem_state`
has a *different* type from the statement's, however right it
looks; the way out is not to write the type at all.

## 13. `evaluate_def` with `fix_clock` removed

### The idiom

A semantics of CakeML is defined with `fix_clock` around every
recursive call, because that is what makes the definition
terminate, and the file then says

```
(* Finally, we remove fix_clock from the induction and definition
   theorems. *)
Theorem evaluate_def[compute,allow_rebind] =
  REWRITE_RULE [fix_clock_evaluate] evaluate_def;
```

(`bviSemScript.sml:386-393`).  From there on `evaluate_def` is the
name of the *restated* clauses, and every proof of every file above
it rewrites with those.

### What it means

`fix_clock s (res,s1) = (res, s1 with clock := MIN s.clock
s1.clock)`, and `fix_clock_evaluate` says
`fix_clock s (evaluate (xs,env,s)) = evaluate (xs,env,s)` -- true
because `evaluate_clock` says the clock never grows.  So HOL4's
`fs [evaluate_def]` unfolds a clause in which `fix_clock` is simply
not there.

### What resisted

The port binds `evaluate_def` to the clauses **as the definition was
made**, with `fix_clock` in them, because that is the theorem that
`cake_define_list_try_tac` returns.  A proof that unfolds it and
then expands `fix_clock` by its definition is left with

```
state_clock_fupd (K (MIN (state_clock s1) (state_clock as))) as
```

in the middle of every assumption.  Nothing is wrong with it, and it
is unusable: `MIN a a = a` needs a rewrite of its own, the record
update then needs `RECORD_CASES_TAC` and `K_DEF` to collapse (a port
record is a one-constructor datatype, so its laws are stated at the
constructor), the state is no longer the variable the next step
wants to see, and the two sides of the goal get the treatment at
different moments and stop looking alike.

### What the port does

Rewrite with `fix_clock_evaluate` **before** the definition of
`fix_clock` is ever touched, exactly where HOL4 restates the
clauses:

```ocaml
let fce = bviSem_fix_clock_evaluate in
...
let tidy =
  TRY(REWRITE_TAC[fce]) THEN RULE_ASSUM_TRY(REWRITE_RULE[fce]) THEN
  TRY(REWRITE_TAC[fc]) THEN ...
```

The rewrite matches wherever a clause put it, including the
`fix_clock (dec_clock (ticks + 1) s) (evaluate (...,dec_clock
(ticks + 1) s))` of `Call`, because the two state arguments are
syntactically the same term there too.  After it, no proof of the
file contains a record update at all.

`fix_clock_evaluate` is a `CHEAT_TAC` of `bviSem.ml` until that
file's turn comes; depending on it is the same arrangement HOL4 has,
where the restated `evaluate_def` depends on `evaluate_clock`.

### Where it lives

`ml/compiler/backend/semantics/bviSem.ml`, `fix_clock_evaluate`
(and `evaluate_clock` under it).  Used in
`proofs/compiler/backend/proofs/bvi_letProof.prf`, section
`evaluate_env_rel`, as `fce`.

### Dead ends

Expanding `fix_clock` and cleaning up afterwards.  It works for one
clause (`opev` in `evaluate_delete_var_Rval` does it, with
`MIN a a = a` and `RECORD_CASES_TAC`) and it does not scale: the
`Call` clause has two `fix_clock`s at different states and the
assumptions of one branch then disagree with the goal's by a record
update.

## 14. The order of a `case` split

### The idiom

```
\\ gvs [CaseEq"result",CaseEq"option",CaseEq"prod",CaseEq"bool"]
\\ gvs [CaseEq"error_result",CaseEq"exn_or_ret"]
...
\\ res_tac \\ gvs []
```

(`bvi_letProofScript.sml:277-287`.)  HOL4 names the types to split
on, **in an order**, and only then uses the induction hypothesis.

### What it means

`CaseEq"bool"` is the rewrite that splits an `if`; it is in that
list because in HOL4 an `if` is a case on a boolean (entry 1).  The
list is read left to right by the simplifier, so the outer cases of
the clause go first and the hypothesis `res = <the rest>` keeps
relating `res` to what has not been decided yet.

### What resisted

A search that splits the deepest pattern first (which is what entry
1 settled on, and what HOL4's own `every_case_tac` does) reaches the
innermost evaluation of a clause before the conditions above it are
decided.  In the `Call` clause of `bviSem` the conditions above the
handler are `find_code`, and `s.clock < ticks + 1`.  Splitting the
handler first and using the induction hypothesis on it leaves its
antecedent `~(x = Rerr (Rabort Rtype_error))` as a subgoal -- and
when the clock condition is decided *afterwards*, the branch in
which it holds has `res = Rerr (Rabort Rtimeout_error)`, so the
assumptions say nothing about the handler at all and the antecedent
is **not provable**.  Two goals of that shape survived every attempt
to close them, because there was nothing wrong with them except
their existence.

### What the port does

Decide the conditions first, in the loop that drives a deep case:

```ocaml
let deep_case =
  REPEAT(CHANGED_TAC
    (TRY(CHANGED_TAC use_ih_auto) THEN TRY tidy2 THEN
     (COND_SPLIT_TAC ORELSE CASE_SPLIT_TAC ORELSE
      COND_CASES_TAC) THEN TRY tidy2 THEN ...
```

`COND_SPLIT_TAC` (the `if` of entry 1, which looks in the
assumptions as well as the goal) comes before `CASE_SPLIT_TAC`, so
no `case` under an undecided condition is ever taken apart.  That is
the whole difference between a `Call` case with two unprovable side
conditions and a `Call` case that closes.

The rule in one line: **a condition of a branch is decided before
the induction hypothesis is used inside that branch.**

### Where it lives

`deep_case` in the `evaluate_env_rel` section of
`proofs/compiler/backend/proofs/bvi_letProof.prf`;
`COND_SPLIT_TAC`, `CASE_SPLIT_TAC` in `ml/lib/tactics.ml`.

### Dead ends

Leaving the two side conditions to a last-resort split inside the
antecedent's own proof (`ih_ants`).  It splits them, and one branch
of the split is the one that cannot be closed -- the split has to
happen earlier, not harder.  Splitting the negated variable of the
side condition instead (`SPLIT_NEG_VAR`) turned 3 goals into 7.

And **making `EVERY_CASE_TAC` itself decide the condition first**,
which looks like the way to put this lesson in the library once and
for all.  It is not: where no hypothesis is used under the
condition, deciding it only adds a vacuous split (an assumption
`true` and a branch that was already decided), and the two proofs
of this file that take a statement apart with `EVERY_CASE_TAC`
(`evaluate_SNOC_Rval`, `evaluate_delete_var_Rerr`) are written for
the shape the plain one leaves and stop going through.  The
ordering belongs where the hypothesis is used, so it is
`EVERY_CASE_COND_TAC` and the explicit `COND_SPLIT_TAC ORELSE
CASE_SPLIT_TAC` of the induction loop.

## 15. A non-empty list written as a `SNOC`

### The idiom

```
imp_res_tac (METIS_PROVE [SNOC_CASES]
               ``m <> [] ==> ?x y. m = SNOC x y``)
\\ rveq \\ full_simp_tac std_ss
     [FRONT_SNOC,LAST_SNOC,LENGTH_SNOC,ADD1]
```

(`bvi_letProofScript.sml:356-358`.)  A definition that recurses on
`BUTLAST xs` and `LAST xs` is reasoned about by writing the list as
`SNOC x y` and letting `FRONT_SNOC` and `LAST_SNOC` do the rest.

### What it means

`rich_listTheory`/`listTheory` of HOL4 carry `SNOC` with some
seventy lemmas, among them the four that this idiom uses and the
`SNOC_CASES` that justifies the rewriting.

### What resisted

HOL Light has `SNOC` (`ml/lib/hol4.ml` defines it, because a few
sources define functions by recursion on one) and **not one law
about it**.  `BUTLAST` is HOL Light's name for what the sources call
`FRONT`, so `APPEND_BUTLAST_LAST` is there, but nothing connects it
to `SNOC`.

### What the port does

Five one-line inductions, stated where they are used:

```ocaml
let SNOC_APPEND = prove (`!(l:A list) x. SNOC x l = APPEND l [x]`, ...
let NOT_SNOC_NIL = prove (`!(l:A list) x. ~(SNOC x l = [])`, ...
let SNOC_CASES = prove (`!l:A list. ~(l = []) ==> ?x y. l = SNOC x y`, ...
let FRONT_SNOC = prove (`!(l:A list) x. BUTLAST (SNOC x l) = l`, ...
let LAST_SNOC = prove (`!(l:A list) x. LAST (SNOC x l) = x`, ...
let LENGTH_SNOC = prove (`!(l:A list) x. LENGTH (SNOC x l) = LENGTH l + 1`, ...
```

`SNOC_CASES` is proved by `EXISTS_TAC`s of `LAST l` and `BUTLAST l`
and `APPEND_BUTLAST_LAST`; the other four are `LIST_INDUCT_TAC` and
`ASM_REWRITE_TAC`, with `NOT_SNOC_NIL` needed because the clauses of
`BUTLAST` and `LAST` test their tail for `[]`.

A sixth is needed that HOL4 gets from its size simpset, because the
measure of the induction is a `list_size`:
`list_size f (SNOC x l) = list_size f l + (f x + 1)`.

### Where it lives

The `evaluate_env_rel` section of
`proofs/compiler/backend/proofs/bvi_letProof.prf`.  They move to
`ml/lib/lemmas.ml` (entry 10) as soon as a second file wants them.

### Dead ends

Working with `BUTLAST es` and `LAST es` and never naming the two
pieces.  It avoids the five lemmas and it costs more: `evaluate_SNOC`
is stated at a `SNOC`, so the one rewrite that takes the evaluation
of the list apart does not fire, and `~(es = [])` has to be carried
into every arithmetic side condition by hand.

## 16. A session loaded out of the port's order

### The idiom

Not an idiom of HOL4 at all, but the trap that costs the most time
per occurrence: a test bed built by hand.  To try a proof of
`compiler/backend/bvi_let.ml` one wants a session with its
ancestors in it, and the quick way looks like

```
needs "basis/pure/mllist.ml";;
...
needs "compiler/backend/bvi.ml";;      (* instead of bvi_let.ml *)
needs "compiler/backend/semantics/bviProps.ml";;
...
```

and then `loadt "ml/compiler/backend/bvi_let.ml"` on top.

### What it means

Every intermediate language of the compiler has a `Var`, an `If`, a
`Let` and a `Call`, and the port overloads those names: `Var` means
the constructor of whichever language was overloaded last.  The
order in which the files load therefore decides what a clause of a
later file *means*.  In the port's own order `bvi_let.ml` comes
right after `bvi.ml`, so its `Var` is `bvi_exp`'s.  Loaded after
`bvlProps` and `closSem`, the same clause reads `Var` as **bvl**'s.

### What resisted

Nothing says so.  The file loads, the definitions are made, and
every statement of it typechecks -- at the wrong type.  What one
sees is three proofs reporting `NOT PROVED` with messages that
point nowhere (`MATCH_MP_TAC: No match`, `find_term`,
`TAC_PROOF: Unsolved goals`), because the definition theorem that
the proof rewrites with is about another language's constructors
and matches nothing.  Reading the types of the goal makes it look
like entry 12 (an invented type variable), and chasing that is an
hour spent on a statement that was right all along.

### What the port does

Build the test bed out of **the closure of the file in the order of
the load order**, which `tools/needsorder.py` writes:

```
python3 -I tools/needsorder.py \
  compiler/backend/proofs/bvi_letProof.ml > prefix.ml
```

Letting `needs` build the closure by recursion is **not** the same
thing, and the difference bites: the recursion takes the needs of a
file in the order they stand in it, so a file of the load order can
land after one that stands behind it.  In the closure of
`data_to_word_memoryProof` built that way
`compiler/backend/semantics/closSem.ml` comes before
`semantics/evaluate.ml`; five theories have then overloaded
`evaluate`, the clauses of `evaluate.ml` resolve `evaluate` to
`labSem_evaluate` and the file does not load at all.  Its own
`needs` are gone from the session with it (`dataProps.ml`), and the
only sign of it is one line of the pane -- while a run, which loads
the files in the order of `tools/load.txt`, has no trouble with any
of it.

For a definition file, a clone of `hol-template-cakeml` with
`needs "compiler/backend/bvi_let.ml"` is enough and takes a minute:
the file's own needs are its ancestors, in its own order.

### Where it lives

`tmp/pfprefix.ml` is the prefix for `bvi_letProof.ml`, made this
way.  The check that a session is sound is the load log itself:

```
cake_conj_list failed: bvi_let_compile has the types
  ?391533->?391532->(?391534)list->(?391535)list and
  (num)list->num->(bvi_exp)list->(bvl_exp)list
cake_define bvi_let_compile CHEATED (clause by clause)
```

`(bvl_exp)list` in the type of a `bvi_let` constant says it, and so
does an axiom count that is far above what a run reports for the
file (26 against 2).  `grep -E 'CHEATED|cake_conj_list'` over the
pane after building a session is worth the second it takes.

### Dead ends

Reading the types of the goal and concluding that the statement
invents a type variable.  The type variable is real -- in a
mis-ordered session the constant really does come out polymorphic,
because the clause that would have pinned the argument down was
read at another language's type and dropped.  It is a symptom.

## 17. A `Definition` that the machinery will not make

### The idiom

```
Definition compile_def:
  ...
  (compile env d [Let xs x2] =
     ...
     let ys = compile env d xs in
       [Let (MAP delete_var ys)
            (HD (compile (extract_list ys ++ env) d [x2]))])
Termination
  WF_REL_TAC `measure (exp2_size o SND o SND)` \\ ...
End
```

(`bvi_letScript.sml:68-168`.)  The second recursive call is made in
an environment that the **result** of the first one builds, and the
clause also recurses on `BUTLAST xs` and `LAST xs`.

### What it means

HOL4's `TotalDefn` asks only that the measure go down at every
recursive call.  The measure is on the third argument; the inner
call sits in the first, where it changes nothing; and the third
argument of every call (`[x2]`, `xs`, `BUTLAST xs`, `[LAST xs]`) is
smaller.  So it is not a nested recursion as far as the *relation*
is concerned, and HOL Light's `pure_prove_recursive_function_exists`
takes the clauses as they stand and leaves one hypothesis: the
existence of a well-founded relation with those conditions.

### What resisted

Three things at once, and none of them a proof.

1. **The conditions need two size facts** that `cake_term_lemmas`
   has no reason to carry: `list_size f (BUTLAST l) <= list_size f
   l` and `~(l = []) ==> f (LAST l) <= list_size f l`.  Without
   them `discharge_conditions` cannot prove the two `Let` branches.
2. **Eight seconds.**  `cake_cheat_budget` is what a definition gets
   before it is assumed instead, and these two take about twenty
   each.
3. **The relation never gets its turn.**  `cake_define_gen` tries
   eight strategies before the one that uses the relation
   (`prim_rec`, `nested`, `maplist`, `cond_bool`, `sing`, `cases`,
   `match`, `lift_if`), each guarded by `with Failure _ when not
   (declared ())`.  One of them declares the constant and then
   fails, and from there nothing more is tried: `define_single`
   with HOL4's own relation, which makes the definition in a minute
   with no axiom, is never reached.

### What the port does

Three overrides, all keyed on the one definition, so nothing else
of the port can notice:

```python
EXTRA_BEFORE[('bvi_let','compile_def')]   # the two size facts,
                                          # and the budget
EXTRA_AFTER[('bvi_let','compile_sing_def')]   # both taken back
DEFINE_REL = set([('bvi_let','compile_def')])  # the relation
                                               # to define_single
TERMINATION[('bvi_let','compile_sing_def')] = 'TERM_TAC'
```

and `tools/port.py` writes, for a definition in `DEFINE_REL`,

```ocaml
let compile_def =
  let th = end_itlist CONJ (fst (define_single
    [(`MEASURE (list_size bvi_exp_size o SND o SND)`,
      TERM_TAC)]
    (cake_conj_list
  [ ... the clauses ... ]))) in
  (note_dest_fact th; cake_note_def th; th);;
```

`compile_sing` needs no such thing once the facts and the budget
are there -- the chain reaches the relation for it -- so what
stands in its `CHEAT_TAC` slot is `TERM_TAC`: the tactic a leftover
condition would be proved with, which is a no-op when there is
none and an honest failure when there is.

### Where it lives

`tools/overrides.py` (`DEFINE_REL`, `TERMINATION`, `EXTRA_BEFORE`,
`EXTRA_AFTER`) and the `DEFINE_REL` branch of `tools/port.py`.
`compiler/backend/bvi_let.ml` adds **no axiom** with them.

### Dead ends

The one that cost the time, and the lesson of this entry: **a probe
of the definition machinery in a session where the auxiliary
constants are only variables tells you nothing.**  Trying the
clauses by hand in a session that has `bvi.ml` but not `bvi_let.ml`
leaves `delete_var` and `extract_list` as free *variables*, and
`close_clause` then universally quantifies them -- so the clause
says that `compile env d [Let xs x2]` equals something that depends
on a quantified variable its left side does not mention.  HOL Light
fails on that with a kernel `Failure "ABS"`, which names nothing
and points nowhere, and every bisection of the clause set
faithfully reproduces it.  An hour went into the conclusion that
HOL Light cannot do nested recursion, and into permuting the
arguments to get rid of a nesting that was never the problem.  The
session with `bvi_let.ml` loaded answers `ok, hyps 1` to the very
first try.  Entry 16 is the same lesson about the overloads; this
is it about the constants.

Also dead: raising `cake_cheat_budget` alone (the conditions still
fail), adding the size facts alone (the chain still does not reach
the relation), and expanding the `let`s.

---

_Entries are added as the idioms are met.  The ones expected next,
from reading the sources: `CaseEq`/`AllCaseEqs` (the rewriting form
of entry 1, 7,559 uses together with `every_case_tac`),
`qexists_tac`/`qpat_x_assum` with term quotations whose variables are
not the goal's, `Induct_on` on a mutually recursive datatype,
`drule`/`drule_then`/`irule_at` and where they put the antecedents,
and `metis_tac` with a long list._
## 18. A relation that HOL4 states as clauses

### The idiom

```
Definition env_rel_def:
  (env_rel (:'c) (:'ffi) [] e1 e2 = (e1 = e2)) /\
  (env_rel (:'c) (:'ffi) (NONE::rest) (x::e1) (y::e2) <=>
     (x = y) /\ env_rel (:'c) (:'ffi) rest e1 e2) /\
  (env_rel (:'c) (:'ffi) (SOME a::rest) (x::e1) (y::e2) <=> ...) /\
  (env_rel _ _ _ _ _ = F)
End
```

(`bvl_constProofScript.sml:22-29`.)  Every proof of the file then
says `fs [env_rel_def]`, which rewrites with the four clauses.

### What it means

The port states such a definition as **one** equation whose right
side is a `match` on the tuple of the arguments, because that is
what HOL Light's `define` makes of a pattern definition.  A proof
that wants HOL4's clauses takes them off it first:

```ocaml
let erc = map (fun t ->
  prove(t, GEN_REWRITE_TAC LAND_CONV [er] THEN
           MATCH_REDUCE_TAC THEN REWRITE_TAC[]))
 [`env_rel (:'c) (:'ffi) [] e1 e2 <=> (e1 = e2)`;
  `env_rel (:'c) (:'ffi) (CONS NONE rest) (CONS x e1) (CONS y e2)
   <=> (x = y) /\ env_rel (:'c) (:'ffi) rest e1 e2`;
  ...
  `env_rel (:'c) (:'ffi) (CONS h rest) [] e2 <=> F`;
  `env_rel (:'c) (:'ffi) (CONS h rest) (CONS x e1) [] <=> F`];;
```

and `REWRITE_TAC erc` is `fs [env_rel_def]` from then on.  Three
things about that rewrite:

- the clause of a recursive relation has the relation on **both**
  sides, so `REWRITE_TAC [er]` does not terminate and
  `ONCE_REWRITE_TAC [er]` unfolds the occurrence on the right as
  well: the rewrite is `GEN_REWRITE_TAC LAND_CONV [er]`, which is
  the left side of the equation that is being proved;
- where the goal is not an equation (`env_rel (:'c) (:'ffi) []
  env env`, which the main theorem's corollary needs)
  `LAND_CONV` has nothing to take, and `ONCE_REWRITE_TAC [er]` is
  right because there is no other occurrence;
- the clauses that say `F` are worth having: they are what closes
  the branches where one environment is shorter than the other.

The same holds for a relation between values (`v_rel`), and there
the clauses are what a case split on the entry of the environment
needs: the shape that is neither of the two the relation speaks
about makes the relation `F`, which is how the branch closes.

## 19. An argument that a definition uses only for its length

### The idiom

```
Definition extract_def:
  (extract ((Var n):bvl$exp) ys = SOME ((Var (n + LENGTH ys + 1)))) /\
  ...
End
```

(`bvl_constScript.sml:254-260`.)  `ys` is there for `LENGTH ys` and
for nothing else.

### What it means

HOL Light gives the constant the most general type it can, so the
port's `extract` is

```
bvl_exp -> (A)list -> (bvl_exp)option
```

polymorphic in the element type of the second argument.  A term
that a proof writes down without saying what that list is gets a
**fresh type variable**, and the term is then not the one in the
goal, where the type comes from `extract_list` and is `bvl_exp`.
`NAMED_CASES_TAC` on it splits a term that occurs nowhere, the
split says nothing, and the goal does not move.  So a proof of the
port writes the type:

```ocaml
NAMED_CASES_TAC `bvl_const_extract (h:bvl_exp) (t:bvl_exp list)`
  [[]; ["ee"]]
```

`frees` of the term and `type_of` of each of them is what to look
at when a split or a rewrite that should fire does not (entry 12 is
the same mistake made by the port rather than by the proof).

## 20. `do_app`, which is one match over every operation

### The idiom

```
  \ fs [evaluate_def, do_app_def, oneline do_int_app_def, AllCaseEqs()]
```

(`bvl_constProofScript.sml:162`.)  HOL4 unfolds `do_app` and lets
the case splitting sort out which of its hundred clauses applies.

### What it means

The port states `do_app` as one `match` on the pair of the
operation and the values, with some hundred and twenty patterns.
Unfolding it where the operation is a **variable** leaves a match
that cannot be decided, and `MATCH_CONV` then expands it into the
choice term it stands for (`@GEN%PVAR%3850. ...`), which no later
rewrite cleans up again: the proof is stuck with a goal that no
longer looks like a semantics.  So the clause for the operation
that the proof is about is taken off `do_app` as a lemma first:

```ocaml
let da_int = prove
 (`!iop vs (s:('c,'ffi)bvlSem_state).
     do_app (IntOp iop) vs s =
     (match do_int_app iop vs with
        SOME res -> Rval (res,s) | NONE -> Rerr (Rabort Rtype_error))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[da] THEN EVERY_CASE_TAC);;
```

and the proof rewrites with `da_int` and never with `do_app`.  The
same for the two clauses that the constant folding compares
(`El` against `ElemAt`, `Equal` against `EqualConst`): each is a
lemma that says the two agree, proved by a case split on the value
and `EVERY_CASE_TAC` for the lookups inside.

`assign_get_code_label` is the small version of the same trap: the
port's definition is a match with one interesting pattern, and
unfolding it at a variable operation leaves the same choice term.
Four instances of it as rewrites (`IntOp`, `BlockOp`, `MemOp`,
`Label`) are what a proof about code labels wants.

## 21. The arguments of a binary operation, the other way round

### The idiom

```
  (compile env [Op op xs] = [SmartOp op (compile env xs)])
```

with

```
  mk_sub = \x1 x2. ... Op (IntOp Sub) [x11; Op (IntOp (Const (n2 - n12))) []]
```

(`bvl_constScript.sml:106`, `:122`.)  The folding of a subtraction
looks as if it had the two sides swapped.

### What it means

It has.  The semantics of an operation is

```
  evaluate ([Op op xs],env,s) =
    (match fix_clock s (evaluate (xs,env,s)) with
       (Rval vs,s) -> (match do_app op (REVERSE vs) s with ...))
```

-- the list is evaluated **left to right** and `do_app` is given
the `REVERSE` of the values, so `Op Sub [a; b]` is the value of `b`
minus the value of `a`.  A proof that computes with the folding has
to keep that straight; the lemma that does it once is

```ocaml
let ev_pair = prove
 (`!y1 y2 op env (s:('c,'ffi)bvlSem_state).
     evaluate ([Op op [y1; y2]],env,s) =
     (match evaluate ([y1],env,s) with
        (Rval v1,s1) ->
          (match evaluate ([y2],env,s1) with
             (Rval v2,s2) ->
               (match do_app op [HD v2; HD v1] s2 with ...)
           | res -> res)
      | res -> res)`, ...)
```

whose proof is `evaluate_CONS`, a split of the two evaluations, and
`evaluate_SING` to see that each gives one value.  With `ev_pair`
(and `ev_one` for one argument) a branch of the folding is an
equation between two `do_app`s of the same values in some order,
which is where the arithmetic starts.

## 22. `MAP_FIRST` and `FIRST` over a list of lemmas

### The idiom

```
  \ rpt (first_x_assum (fn h => MAP_FIRST (fn th => fn g =>
       mp_tac (MATCH_MP th h) g) (CONJUNCTS do_int_app_eq_some)))
```

(`bvl_constProofScript.sml:186-187`.)  HOL4 tries each conjunct of
a theorem against each assumption and keeps what matches.  Note the
`fn g =>` in it.

### What it means

That `fn g =>` is the whole point, and the port needs it too.
`MAP_FIRST f l` and `FIRST (map f l)` evaluate `f` at **every**
element of the list before any tactic is applied, so a `MATCH_MP`
that fails -- which is exactly what "this conjunct does not apply"
means -- raises there and then and takes the whole search with it.
Written

```ocaml
FIRST (map (fun l gl -> STRIP_ASSUME_TAC(MATCH_MP l th) gl) ths)
```

the `MATCH_MP` happens when the goal arrives, and `FIRST` catches
it.  A search that is silently doing nothing (a `REPEAT` of it
never fires, and nothing fails) is what this looks like from the
outside.

## 23. The arithmetic of a folding is not always linear

### The idiom

```
    intLib.COOPER_TAC ORELSE metis_tac [...]
```

(`bvl_constProofScript.sml:189`.)  HOL4 ends each branch of the
constant folding with a decision procedure for the integers.

### What it means

`ASM_INT_ARITH_TAC` is the port's reading of `COOPER_TAC`, and it
does the branches of `mk_add` and `mk_sub`.  The branch of `mk_mul`
that folds two multiplications,

```
  (q * vb) * (p * va) = (vb * va) * (q * p)
```

is **not** linear, and no amount of assumptions makes
`ASM_INT_ARITH_TAC` do it; `INT_RING` does it at once.  `INT_RING`
ignores the assumptions, so the equations the case split left have
to be put back into the goal first:

```ocaml
let int_ring_fin (asl,w as gl) =
  let eqs = filter (fun (_,th) ->
      try type_of(lhs(concl th)) = `:int` with Failure _ -> false)
      asl in
  (MAP_EVERY (fun (_,th) -> MP_TAC th) eqs THEN
   CONV_TAC INT_RING) gl;;
```

and the finisher of the branch is
`TRY(ASM_INT_ARITH_TAC ORELSE int_ring_fin)`.

A third thing about the arithmetic: `INT_ARITH` reads `&0` as a
**real** unless the type is written down, so

```ocaml
let el_le = INT_ARITH `!i. ~(i < &0) ==> &0 <= i`
```

is a theorem about the reals, and a `MATCH_MP` of it against an
integer assumption says `No match`.  The `i:int` goes in.


## 24. The invariant of the memory, unfolded again and again

### The idiom

A hundred theorems of `data_to_word_memoryProof` are about
`memory_rel`, and almost every one of them starts the same way in
HOL4:

```
fs [memory_rel_def,word_ml_inv_def,abs_ml_inv_def,
    bc_stack_ref_inv_def,v_inv_def] \\ rw []
\\ fs [word_addr_def]
```

### What it means

`memory_rel` is `word_ml_inv` of a heap, which is `abs_ml_inv` of
the values of the stack, whose `bc_stack_ref_inv` relates the
values to a list of **roots** that an existential introduces; the
rules of `v_inv` say what the root of a value is (a `Data` of a
word, a `Data` of a `Loc` or a `Pointer`), and `word_addr` turns a
root into the word that the machine holds.

### What resisted

In HOL Light each of the four steps is a rewrite and each leaves
work that `fs` does silently: the roots have to be split against
the values (a list variable against a cons), the rules of `v_inv`
are a disjunction and a conditional that have to be opened one at a
time, the equation that says what the root is has to be substituted
(and HOL Light's `SUBST_VAR_TAC` as happily substitutes the
variable the statement is about), and the contradictory branches
have to be closed -- of which there are many, because `v_inv` of a
`RefPtr` has three rules and two of them are about a thunk.
`ASM_MESON_TAC[]` closes them, but with twenty assumptions in the
list it takes minutes or goes "Too deep".

### What the port does

`ml/lib/tactics.ml` has the steps:

- `MEMORY_REL_TAC` -- the four definitions and `SPLIT_ROOTS_TAC`
- `SPLIT_ROOTS_TAC` -- the list of roots against the list of values
  (it finds the `ALL2` assumption itself, so no name is written)
- `V_INV_TAC` -- the rules of `v_inv` opened, the roots
  substituted, `word_addr` reduced and the contradictions closed
- `CONTRA_TAC` -- two assumptions that contradict each other
- `OPEN_ASSUM` -- an assumption that is a conditional, a
  disjunction or an existential, opened into the goal
- `USE_CHANGED`, `SUBST_LHS_TAC`, `cake_thm`

With them `memory_rel_Number_IMP_Word` is

```ocaml
MEMORY_REL_TAC THEN V_INV_TAC THEN ASM_MESON_TAC[]
```

and the `ASM_MESON_TAC` at the end has a goal that is one step.

### Dead ends

Writing the type of a variable of the goal in a `ASM_CASES_TAC` or
an `ISPEC`: the statements of this file are polymorphic in the word
and a written type variable is rigid, so the term is about another
variable and the tactic does nothing (entry 12).  `CASES_ON_NAME`,
`SPLIT_ROOTS_TAC` and `SUBST_LHS_TAC` take the term out of the goal
instead.

## 25. The type variables of a statement that the parser invented

### The idiom

A statement of the port is a quotation, and where it does not write
a type itself the parser invents a type variable for it.  HOL Light
names those `?1234`, and a theorem of the file (and so every goal
made from it) carries them:

```
v_inv c v refs (x,f,tf,heap)     x : ((?970900)word_loc)heap_address
```

### What it means

A term that a proof writes down gets type variables of its own, so
`EXISTS_TAC `all_ts refs stack`` or ``ASM_CASES_TAC `!ck. v_inv_ck
ck conf vv refs (y,f,tf,heap)``` is about *other* variables of the
same names and the tactic does nothing (or fails with a type
error).  Three ways out, in this order:

1. write the type the way the statement writes it (`y:(('a
   word_loc)heap_address)`) -- this works when the statement does
   annotate, as the clauses of `v_inv_def` do;
2. take the term out of the goal (`(fun (asl,w) -> ... rand w ...)`
   as a tactic), which is what the proofs of `all_ts` do;
3. state what is needed as a lemma of its own, with `'a` in it, and
   `MATCH_ACCEPT_TAC` it against the goal -- a theorem's type
   variables are instantiated when it is used, so this always
   works.

A name of the port can also be a **constant**: `stack`, `refs` and
`cen` are constants of some theory, so ``stack:(dataSem_v)list``
is an annotation of a constant and fails with "typechecking error
(overload resolution)".  `print_types_of_subterms := 0` makes a
goal with invented type variables readable.

**Arithmetic is where this bites hardest**, because the port
overloads `=`, `+`, `<` and the numerals for words: ``ASM_CASES_TAC
`u = ts``` parses as an equation of two *new* variables of an
invented type, not as the `u` and `ts` of the goal, and
``SPECL [`ts + 1`; ...]`` instantiates with a term of another type
than the goal's.  Nothing complains where the tactic is written:
the case split or the specialisation goes through and the step
after it fails with `tryfind` (`FIRST_ASSUM ACCEPT_TAC` finds no
assumption, `FIRST_X_ASSUM MATCH_MP_TAC` no hypothesis), several
lines away from the cause.  So **every numeral term that a tactic
writes gets `:num`** -- ``ASM_CASES_TAC `(u:num) = ts``` and
``SPECL [`(ts:num) + 1`; ...]`` -- and a quick way to see which
one is wrong is `print_types_of_subterms := 2` on the parsed term,
where the invented one prints as `(ts:?982593)`.  (`aconv` of the
goal's term and the written one is the test; `ACCEPT_TAC` needs
them equal, and `MATCH_ACCEPT_TAC` can fail where `ACCEPT_TAC`
works, so a failing `MATCH_ACCEPT_TAC` is worth retrying as
`ACCEPT_TAC` before looking for a deeper cause.)

## 26. A match whose scrutinee is a call, not a variable

### The idiom

HOL4 writes a definition whose body looks at the value of another
one:

```
xor_bytes (b1::bs1) (b2::bs2) =
  case xor_bytes bs1 bs2 of NONE => NONE
  | SOME rest => SOME (b1 ?? b2 :: rest)
```

### What it means

`MATCH_REDUCE_TAC` reduces a match whose scrutinee is a
constructor.  Where the scrutinee is a call (`xor_bytes bs1 bs2`)
there is nothing to reduce, and what it leaves is the match
expanded into its definition -- an `existsunique` and two `@`
terms, which no later tactic gets anywhere with.  A
`STRUCT_CASES_TAC` on the scrutinee does not help either: the
substitution does not reach the occurrences inside the expanded
match, and the case that the goal keeps is not the case that the
match reduces to.

So the scrutinee is taken apart **before** the match is reduced,
and `EVERY_CASE_TAC` (HOL4's `every_case_tac`, which is
`CASE_SPLIT_TAC` and a reduce, up to ten times) is what does it:
it splits the innermost scrutinee with `CASES_ON_TAC`, which
keeps the equation of the case as an assumption, and reduces the
match in each case.  The idiom is

```
GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [cake_def "xor_bytes"] THEN
EVERY_CASE_TAC THEN ...
```

with **no** `MATCH_REDUCE_TAC` in between: one of those mangles the
goal before the split, and then `EVERY_CASE_TAC` has nothing to
split any more.  Where the scrutinee is a constructor already (the
other clauses of the same definition), `MATCH_REDUCE_TAC` is the
one to use.

## 27. The arithmetic of HOL Light is not HOL4's arithmetic

### The idiom

```
word_bits h l w = word_subword w (l,h + 1 - l)
```

### What it means

HOL4 gives `+` and `-` the same precedence and makes them
associate to the left; HOL Light binds `-` tighter than `+` and
both of them to the right.  So the text above is `(h + 1) - l` in
HOL4 and `h + (1 - l)` in HOL Light -- a different term, and with
truncated subtraction a different value.  The generated files of
the port are safe (the translator builds the term), but a file
that is written by hand is not: `ml/lib/words4.ml` had this in
`word_bits`, in the `><` extract and in `bit_field_insert`, which
made `all_ones_bit` of data_to_word_memoryProof false as stated
(ISSUES.md).  `*` is right-associative as well, so `3 * (a + 1) *
d` is `3 * ((a + 1) * d)` and a rewrite with `MULT_ASSOC` is what
puts it the other way round.

## 28. The induction of a type that nests a list of itself

### The idiom

```
ho_match_mp_tac (theorem "v_all_ts_ind")
```

### What it means

HOL4 keeps an induction theorem for every definition it makes by
well-founded recursion, and a proof about `v_all_vs` or `v_all_ts`
(which recurse into the payload of a `Block`) uses it.  HOL Light
has no such theorem, but `define_datatype` of a type that nests a
list of itself gives a **mutual** induction:

```
|- !P0 P1. (!a. P0 (Number a)) /\ ... /\
           (!a0 a1 a2. P1 a2 ==> P0 (Block a0 a1 a2)) /\ ...
           /\ P1 [] /\ (!a0 a1. P0 a0 /\ P1 a1 ==> P1 (a0 :: a1))
           ==> (!x0. P0 x0) /\ (!x1. P1 x1)
```

so the statement to prove is doubled -- one half about a value, one
about a list of them -- and `MATCH_MP_TAC` of that theorem gives
the seven cases.  `ml/lib/tactics.ml` keeps the clauses of
`v_all_vs` and `v_all_ts` (`v_all_vs_clauses`) and the transitivity
of the values of a value (`v_all_vs_trans_thm`) that the proofs of
the file need before the file itself states them; the induction
theorem is looked up in `the_inductive_types` and not by its name,
because `ml/lib/tactics.ml` is loaded before the type is made.
