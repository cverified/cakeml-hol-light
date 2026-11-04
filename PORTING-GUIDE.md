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
| 9 | two files that bind the same `foo_def` | a binding each, `bindname` |
| 9a | two files that state a theorem of one name | a binding each, the theory in front |
| 10 | a library theorem HOL Light has not | `ml/lib/lemmas.ml` |
| 11 | `Parse.hide`, a field name | `hide_constant`, the type said |
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
| 29 | `drule` with a rewrite in it | `USE_CHANGED`, or a test of the shape |
| 30 | a tactic of several steps | brackets round it, or it is an argument |
| 31 | `SEP_R_TAC`, `SEP_W_TAC`, `AC STAR_ASSOC STAR_COMM` | `read_fun2set`, `write_fun2set`, `STAR_AC` |
| 32 | a family of functions whose clauses overlap | `MATCH_CLAUSES`, a match per function |
| 33 | a statement HOL Light does not read | `unstated.py`, a pointer in its place |

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

### Dead ends

`REPEAT VAR_EQ_TAC` **hangs**: the `REPEAT` is already inside, so
the tactic never fails, and the outer `REPEAT` turns that into a
loop -- the session answers `Stack overflow during evaluation
(looping recursion?)` and nothing says which line it was
(`heap_split_heap_split` paid a quarter of an hour for this).  The
same holds for `REPEAT(VAR_EQ_TAC)` written round any of the
tactics of `ml/lib/tactics.ml` that have a `REPEAT` of their own.

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

OCaml has one namespace.  A port that binds every definition under
the name of its source has 249 names that two or more files bind,
and `compile_def` is then whichever file loaded last: a proof that
writes `compile_def` gets the definition of another theory, with no
error at all.  Of the 976 definition references of the proof store,
32 denoted another constant that way, and the proofs around them
only failed because the rewrite did not fire.

A registry keyed by the constant with a lookup by string
(`cake_def "bvi_let_compile"`) was the port's first answer, and the
wrong one: HOL Light names a definition by its binding, and the
lookup hid which definition a proof meant.

### What the port does

Every definition is a binding of its own, and the binding is
unique: the first file to take a name keeps it and a later one gets
the name of its theory in front (`bvi_let_compile_def`).  That is
`tools/port.py`'s `bindname`, the same function that names a
theorem (entry 9a), because one namespace holds both; the inductive
relations (`cake_inductive`) and the definitions of the monadic
machinery go through it as well, so no two files of the port bind
one name.

`ml/lib/tactics.ml` is the one place that still looks a definition
up by its constant, and it has to: it is part of the library layer
and loads before the files whose definitions its tactics unfold, so
there is no binding to name yet.

```ocaml
let cp = bvi_let_compile_def in ...        (* a proof of the port *)
REWRITE_TAC[cake_def "memory_rel"]         (* ml/lib/tactics.ml *)
```

### Where it lives

`tools/port.py`: `bindname`.  `ml/lib/define.ml`: `the_defs`,
`cake_note_def`, `cake_def`, `cake_defs`.  `tools/bindrefs.py`
rewrites the references of the proof store when a binding changes,
and `tools/bin/dryport` dumps the bindings it needs.

## 9a. Two files that state a theorem of one name

### The idiom

`gen_gcScript.sml` and `gen_gc_partialScript.sml` both state a
`gc_move_list_IMP`, about their own `gc_move_list`; so do a dozen
other pairs of the gc and the semantics files.

### What the port does

Each of them is a binding of its own, the way HOL Light names a
theorem: the first file to state the name takes it
(`gc_move_list_IMP`) and a later one gets the name of its theory
in front (`gen_gc_partial_gc_move_list_IMP`), which is what
`tools/port.py`'s `thmname` does.  A proof names the one it means
and nothing can pick up the other -- which an earlier shape of
the port, where a lookup by the HOL4 name found the one
registered last, could not promise.

The statements of the two print the same way (`gc_move_list conf
state xs = xs',state1`), because the two constants print under the
same overload; the difference is in the type of the head constant
(`gen_gc_partial_gc_move_list` against `gen_gc_gc_move_list`),
which `print_types_of_subterms := 2` or
`fst(dest_const(fst(strip_comb t)))` prints.

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
record field and another constant alike, so a statement of a file
reads a name of the port as a variable of its own.  The port says
the three cases the way HOL Light does: a `Parse.hide` becomes
`do_list hide_constant [...]` at the head of the file and
`do_list unhide_constant [...]` at its end; a variable whose name
is a record accessor says its type in the statement itself
(`tools/fieldvars.py` holds the types); and
a file that needs the accessors of a field and reads the name of
that field as a variable as well takes only those pairs out of the
interface, with `hide_overloads` (`ml/lib/theorem.ml`).

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
- `V_INV_TAC <v_inv_def>` -- the rules of `v_inv` opened, the roots
  substituted, `word_addr` reduced and the contradictions closed
- `CONTRA_TAC` -- two assumptions that contradict each other
- `OPEN_ASSUM` -- an assumption that is a conditional, a
  disjunction or an existential, opened into the goal
- `USE_CHANGED`, `SUBST_LHS_TAC`

With them `memory_rel_Number_IMP_Word` is

```ocaml
MEMORY_REL_TAC THEN V_INV_TAC v_inv_def THEN ASM_MESON_TAC[]
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
   works;
4. when the term is a **theorem of the port** that is to be used on
   the goal, instantiate it *at* the goal:
   `INSTANTIATE (term_match [] (rand (concl th)) w) th` makes its
   type variables the goal's.  Two statements of the port never
   share an invented variable, so `ASM_REWRITE_TAC[]` does not see
   that the conclusion of the one is the goal of the other, and the
   step after it fails on an `X ==> X` that `ACCEPT_TAC` refuses.
   `mutcons_thm` is the example: its `mutcons_thm_alt` has a
   variable of its own for the word *and* one for the data of a
   heap element in each of two `el_length` subterms, so the
   instantiation is taken from the whole conclusion at once and not
   from a subterm.

A name of the port can also be a **constant**: `stack`, `refs`,
`cen` and `be` are constants of some theory (`be` is a field of
`labSem_state`), so ``stack:(dataSem_v)list`` is an annotation of a
constant and fails with "typechecking error (overload
resolution)".  A lemma of a proof therefore calls the endianness
flag something else -- `b2` in `write_bytes_REPLICATE` -- and takes
the goal's own variable with `var_by_name`, which
`ml/lib/tactics.ml` has for exactly this (`CASES_BY_NAME` is the
case split that goes with it, and it splits a pair with
`PAIR_SURJECTIVE`).  `print_types_of_subterms := 0` makes a goal
with invented type variables readable.

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

### The `&` of a quotation is a real unless it is told otherwise

`&` is overloaded for `real` and for `int`, and the parser's
default is `real`.  So `INT_ARITH \`&0 - --(&n) = &n\`` proves a
theorem **about the reals**, which no rewrite of an integer goal
ever fires on, and nothing complains: the tactic runs and leaves
the goal as it stands.  Every quotation of a proof that is about
the integers therefore says so -- ``INT_ARITH `&0 - --(&n) =
&n:int``` -- and the same holds for the `-`, the `<` and the
numerals around it (`word_ml_inv_neg_num` paid twenty minutes for
this).  The other half of the trap is the direction of
`INT_OF_NUM_MUL` (`&(m * n) = &m * &n` is **not** what HOL Light
has: it is `&m * &n = &(m * n)`, so the fold needs it plain and the
split needs the `GSYM`).

### A statement may have two invented type variables, not one

`word_list_AND_word_list_exists_IMP` reads as a statement about a
memory of `'a word` cells holding `'a word_loc` values, and an
`aux` lemma that stands in for it (way 3) was written with one
type variable for both.  `MATCH_ACCEPT_TAC` then failed with
`ACCEPT_TAC`, and `term_match` with `type_match`: the port's
`misc_word_list` is polymorphic in the address **and** in the
contents, nothing in the statement ties them together, and so the
parser invented two.  `print_types_of_subterms := 2` on
`concl <the theorem>` is what shows it; the `aux` then needs
two type variables as well, and the contents one is a bare `M`,
not `(M)word_loc`.

The same holds for `<`, `<=`, `+` and `-`: the port overloads them
for words as well, and a quotation whose variables are free of any
other constraint takes the **word** reading.  `ASM_CASES_TAC `j <
t`` of `shift_shift_lemma` split on an equation between two words
called `j` and `t` that have nothing to do with the goal's numbers,
and the proof then failed in the arithmetic several steps later,
where the printed `ARITH_RULE` showed `j < t` sitting among the
`real_of_int`s, untranslated.  So a comparison of a quotation that
the context does not type says `(j:num) < t`.  The sign that this
is what happened is an `ISPECL` or an `ARITH_RULE` that fails on a
statement that is plainly true, or an assumption of a case split
that nothing ever uses.

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

## 29. A rule inside `FIRST_ASSUM` that never fails

### The idiom

HOL4's `drule`/`imp_res_tac` look for the assumption that a theorem
applies to.  The port writes that as `FIRST_ASSUM(fun th -> ...
th ...)`, and the body is often a rule: `MP_TAC(MATCH_MP lemma th)`
or `MP_TAC(REWRITE_RULE[cases] th)`.

### What it means

`FIRST_ASSUM` is `tryfind` over the assumptions, so it takes the
**first** assumption for which the body does not fail -- and
`REWRITE_RULE` never fails: it gives the theorem back unchanged
when nothing matches.  So
`FIRST_ASSUM(fun r -> MP_TAC(ONCE_REWRITE_RULE[cases] r))` puts the
*first* assumption (the induction hypothesis, as a rule) into the
goal, the rewrite having done nothing, and the proof goes on with a
goal that looks almost right; the failure comes several steps
later, where the disjunction the cases theorem would have given is
missing.  (`MATCH_MP` does fail when it does not apply, so the same
line with `MATCH_MP` is safe.)

Three ways out:

1. `USE_CHANGED ths` of `ml/lib/tactics.ml` -- the assumption that
   the rewrite **changes**, as the antecedent of the goal;
2. the same test by hand when the assumption is to be kept:
   `FIRST_ASSUM(fun r -> let th = REWRITE_RULE ths r in
   if concl th = concl r then fail() else MP_TAC th)`;
3. a check on the shape of the assumption, when several assumptions
   are changed and the one that is wanted is the one *about* a
   constant: `if fst(dest_const(fst(strip_comb(rand(concl th))))) =
   "all_ts" then ... else fail()` (`duplicate_thm` picks the
   `FDOM tf SUBSET all_ts ...` of five SUBSETs that way).

The same trap with the whole continuation inside the `FIRST_ASSUM`
is the cheap fix when the continuation *does* fail on a wrong
choice: `FIRST_ASSUM(fun th -> MATCH_MP_TAC(MATCH_MP lemma th) THEN
REWRITE_TAC[MEM_APPEND; MEM] THEN MESON_TAC[])` lets `tryfind`
backtrack over the assumptions until the MESON closes the goal
(`memory_rel_Block_explode`), at the price of running the MESON
once per wrong assumption.

## 30. A tactic of several steps, where an argument stands

### The idiom

A proof of the store is the third argument of `cake_theorem`, so
the file of the port reads

```
let foo = cake_theorem "foo"
  (fun () -> `...`)
  (DISCH_TAC THEN REWRITE_TAC[...] THEN ARITH_TAC);;
```

### What it means

`THEN` is an infix of OCaml, so without the brackets the line reads
as `(cake_theorem "foo" (fun () -> ...) DISCH_TAC) THEN
REWRITE_TAC[...]`: the theorem gets `DISCH_TAC` as its proof and
the rest of the chain is applied to the **theorem**.  OCaml then
says

```
Error: This expression has type thm = Hol.thm
```

and the file does not load from that line on.  `tmp/sectest.py`
does not catch it, because it binds the body to a name
(`let t = <body>;;`), where a bare chain is fine; the section of
`w2i_i2w_IMP` went through three commits that way.

### What the port does

`tools/prfcheck.py` says `the tactic needs brackets round it` for
a section whose body has a `THEN` or a `THENL` in it and does not
start with `(` and end with `)`; `tmp/mksec.py` puts the brackets
round every body it writes.  A single tactic (`CHEAT_TAC`,
`ARITH_TAC`, `MATCH_ACCEPT_TAC th`) needs none, but brackets round
it do no harm.

### Where it lives

`tools/prfcheck.py` (the check), `tmp/mksec.py` (the writer).

### Dead ends

Running `tools/bin/verifyquick` catches it, but only after the five
minutes it takes to load the file, and only for the file that is
being verified; the check is a second.

## 31. The separation logic of a memory

### The idiom

Every proof of `data_to_word_memoryProof` that touches the memory
goes through HOL4's separation logic:

```
  \\ rpt_drule memory_rel_IMP_word_list_exists
  \\ SEP_R_TAC \\ fs []
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  \\ fs [AC STAR_ASSOC STAR_COMM]
```

### What it means

`fun2set (m,dm)` is the memory `m` restricted to the domain `dm`,
as a set of address-value pairs, and a separation predicate says
what part of that set a piece of the heap takes up.  HOL4's
tactics are a decision procedure over them: `SEP_R_TAC` finds the
cell of an address in an assumption and reads `m a = v` off it,
`SEP_W_TAC` rewrites the assumption for a store at that cell,
`SEP_F_TAC` applies a frame rule and `sep_cond_ss` pulls the
`cond` of a predicate out as an ordinary conjunct.  `AC
STAR_ASSOC STAR_COMM` reorders a product of predicates, which the
sources do on nearly every line.

### What resisted

`ml/lib/set_sep.ml` is a port of HOL4's `set_sepTheory`, but it
had only the unit and associativity laws (a hundred lines), and
none of the tactics exist.  Seventeen cheats of the third file
mention `fun2set`, `word_list_exists` or `STAR`, and none of them
can be touched without the lemmas those tactics are made of.

### What the port does

Ten theorems of `set_sepTheory`, each a transliteration of HOL4's
own proof, now stand in `ml/lib/set_sep.ml`:

- `SEP_EXISTS_THM`, `cond_STAR`, `STAR_cond` -- a predicate taken
  apart at a point;
- `SPLIT_LEMMA`, `one_STAR`, `IN_fun2set` -- the cell of an
  address inside a `fun2set`;
- `read_fun2set` (`(one (a,x) * p) (fun2set (f,d)) ==> f a = x /\
  a IN d`) -- HOL4's `SEP_R_TAC`, applied by hand with
  `FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP read_fun2set th))` after
  the product has been reassociated so that the cell is the left
  factor (`REWRITE_RULE[GSYM STAR_ASSOC]`);
- `write_fun2set` (`... ==> (p * one (a,y)) (fun2set ((a =+ y)
  f,d))`) -- HOL4's `SEP_W_TAC`, the same way, with
  `ISPEC` of the value written (not `SPEC`: the type variable);
- `STAR_AC` -- the commutativity, the associativity and the
  left-commutativity as one permutative rewrite, so that
  `REWRITE_TAC[STAR_AC]` normalises both sides of a goal the way
  HOL4's `AC` does.  Where a specific rearrangement is wanted
  rather than a normal form, a one-line lemma says it
  (`(p * q) * r = (p * r) * q`, proved by `REWRITE_TAC[STAR_AC]`)
  and `ONCE_REWRITE_RULE` applies it to the assumption;
- `STAR_SEP_T` (`(p * SEP_T) s <=> ?u. u SUBSET s /\ p u`) -- what
  a predicate beside `SEP_T` says, which is how a fact about a
  part of the memory is carried to the whole of it.

`APPLY_UPDATE_THM` stands in the same file rather than in
`ml/lib/lemmas.ml`: the load order of a run puts `set_sep.ml`
before the preamble's lemmas, so a lemma it uses has to be there
(`tools/bin/pfbase` reloads the preamble's lemmas into the
template first, for the same reason).

### Where it lives

`ml/lib/set_sep.ml`.  The proofs that use it: `word_list_exists_thm`,
`store_list_thm`, `word_el_IMP_word_list_exists`,
`word_heap_IMP_word_list_exists`,
`word_list_AND_word_list_exists_IMP`.

### Dead ends

A `MESON_TAC` over the unfolded `STAR_def` and `SPLIT_def` solves
the small laws but not a goal with a `word_list_exists` in it: the
existential over the list of words and the `cond` on its length
put it out of reach (`word_list_exists_thm` needs
`STAR_SEP_EXISTS`, `SEP_EXISTS_THM` and `STAR_cond` in that order,
and then a two-line MESON over `LENGTH_EQ_CONS`).

## 32. A family of functions whose clauses overlap

### The idiom

```
Definition do_eq_def:
  do_eq (Litv l1) (Litv l2) = ... ∧
  ...
  do_eq _ _ = Eq_type_error ∧
  do_eq_list [] [] = Eq_val T ∧
  do_eq_list (v1::vs1) (v2::vs2) = ... ∧
  do_eq_list _ _ = Eq_val F
End
```

### What it means

One `Definition` defines two functions, and the clauses of one of
them overlap: the last clause of `do_eq_list` catches the two lists
that the first two have already given a value, and HOL4 takes the
first clause that matches.

### What resisted

The port writes a definition whose clauses overlap as **one** clause
with a `match`, which has HOL4's first match semantics (entry 6).  A
`match` is one clause, so it cannot define a family: the port wrote
both functions as arms of one match, HOL Light's pattern machinery
gave the arms of `do_eq` and of `do_eq_list` the same generated
variable, and the file would not even typecheck:

```
GEN%PVAR%3258 cannot have type semanticPrimitives_v#semanticPrimitives_v
and (_)list#(_)list simultaneously
```

Leaving the clauses as a list of clauses is no answer either: they
contradict each other, and the cheat of the definition's termination
makes them axioms, so the port could prove anything from them.

### What the port does

`overrides.MATCH_CLAUSES` names the constants of the family whose
clauses are to be one clause with a match.  The definition stays a
list of clauses, and the clauses of each named constant are one
entry of that list:

```ocaml
let do_eq_def = cake_define_list_cheat CHEAT_TAC
  [`dataSem_do_eq refs v1 v2 = match (v1,v2) with ...`;
   `dataSem_do_eq_list refs l1 l2 = match (l1,l2) with ...`];;
```

The entry carries the comment that goes over the definition, so a
re-port writes the same file.  The five that need it are the
`do_eq`/`do_eq_list` of `dataSem`, `bvlSem`, `closSem`, `flatSem`
and `semanticPrimitives` (the first two have the overlap in both
functions, the other three in `do_eq_list` alone).

### Where it lives

`tools/overrides.py`: `MATCH_CLAUSES`.  `tools/port.py`:
`clause_form(body, matchcons)` and `match_form(body, only=...)`.

## 33. A statement that HOL Light does not read

### The idiom

Nothing of HOL4: a `Theorem` of a source whose statement HOL4's
parser reads and HOL Light's does not.

```
Theorem SORTED_GENLIST_TIMES:
  0 < n ⇒ SORTED $< (GENLIST (λi. n * i) m)
```

### What it means

HOL4 resolves an overloaded name by the types around it and gives
a variable the type that the clause it stands in asks for.  HOL
Light's parser has less to go on: `SORTED` of the port takes a
relation and a list, and the statement applies it to three
arguments, so the parser says

```
typechecking error (initial type assignment): SORTED has type
(A->A->bool)->(A)list->bool, it cannot be used with type
(B->B->bool)->(B)list->_->bool
```

### What resisted

While a theorem of the port was a statement that `cake_theorem`
registered, a statement like this printed `NOT STATED` and the
file loaded on, so the extent of it was invisible: 688 statements
of one harvest.  A plain `let foo = prove (`...`, tac);;` has no
such slack -- the phrase raises, and `loadt` stops the file, so one
statement that does not read costs every theorem after it.

### What the port does

Where HOL Light does not read the statement the port writes the
comment that points at the source, which is what it does for a
statement its own parser cannot read:

```ocaml
(* HOL4 miscScript.sml:3421-3424: a theorem whose statement HOL
   Light does not read (tools/unstated.py): SORTED_GENLIST_TIMES *)
```

Which statements those are is not something the port can see by
reading the source -- only HOL Light's parser says -- so the names
are harvested:

```
tools/bin/harvestall                      every theorem in a try,
                                          tmp/unstated.txt
python3 -I tools/mkunstated.py > tools/unstated.py
```

`tools/tolerant.py` is what wraps the theorems for that run, and
nothing of it goes into `ml/`.  Every entry of the table is a
statement to win back: a type annotation, an `ARG_TYPES` of the
overrides or a hidden name, and the theorem is stated again.

### Where it lives

`tools/unstated.py` (the table), `tools/mkunstated.py` (writes it),
`tools/tolerant.py` and `tools/bin/harvestall` (the harvest),
`tools/port.py`'s `state` (the pointer in the place of the
theorem).

## 34. A term of a tactic, and the types the goal gave it

### The idiom

Not an idiom of HOL4 but of HOL Light, and the one that cost the
most time in the lemmas about the refs of `v_inv`: a term written
inside a tactic (`SUBGOAL_THEN`, `ASM_CASES_TAC`, `EXISTS_TAC`) is
read by itself, with no goal to constrain it.

### What it means

Each quotation is typechecked on its own.  The statement of a
lemma about the refs of CakeML fixes `refs` to
`((dataSem_v)bvlSem_ref)spt` because `dest_thunk` is in it; a
`SUBGOAL_THEN` of the proof that says

```ocaml
SUBGOAL_THEN
  `lookup ptr refs = NONE \/
   ?a b. lookup ptr refs = SOME (ByteArray a b)`
```

has only `ByteArray` to go on, so its `refs` is `((A)bvlSem_ref)spt`
with a type variable -- a *different* variable of the same name.
The subgoal is then about something else than the goal, and what
fails is not the term but a `MATCH_ACCEPT_TAC` three steps later,
with `Failure "ACCEPT_TAC"`, or an assumption that no `FIRST_ASSUM`
of the rest of the proof finds, with `Failure "tryfind"`.

### What the port does

Either the term is taken from the goal, which is always right:

```ocaml
FIRST_ASSUM(fun h ->
  let d = lhand(concl h) in
  ASM_CASES_TAC d THENL [...])
```

or, where it is written down, it carries the annotation that pins
it:

```ocaml
SUBGOAL_THEN
  `lookup ptr (refs:(dataSem_v bvlSem_ref) spt) = NONE \/ ...`
```

### What else bites in the same place

`THEN` and `THENL` are one precedence level and associate to the
left, so

```ocaml
A THEN (B THENL [b1; b2; b3]) THEN C THENL [c1; c2; c3; c4]
```

without the parentheses around the second group is
`((A THEN B THENL [...]) THEN C) THENL [c1; c2; c3; c4]`: the last
list is applied to the goals of the whole chain, which are three
times four, and what it says is

```
Failure "seqapply: Length mismatch"
```

A tactic with two `THENL`s in sequence brackets each of them.

### Where it lives

The six `v_inv_*_lemma` sections of
`proofs/compiler/backend/proofs/data_to_word_memoryProof.prf`.

## 35. A definition whose induction theorem the port has not got

### The idiom

```
Theorem gc_move_refs_data_refs_split[local]:
  ...
Proof
  recInduct (fetch "gen_gc" "gc_move_refs_ind")
```

and its `ho_match_mp_tac foo_ind` form, which the sources use for
every theorem about a function that HOL4's `Definition` made.

### What it means

HOL4's `Definition` leaves, beside the clauses, an induction
theorem shaped like the recursion: one case per clause, with the
hypothesis at each recursive call.  A proof about the function is
that induction and then the clauses.

### What resisted

HOL Light's `define` leaves no such theorem, and the first pass of
the port assumes the termination (`CLAUDE.md`), so there is not
even the measure theorem to work from.  Worse, the recursion of
the collector is not structural in anything the statement
mentions: `gc_move_refs` consumes `r2` **of the state**, and
`gc_move_data` takes the head of `h2` of the state **after** the
call it makes, which may be longer than the one it started with.

### What the port does

The statement is generalised over what the recursion consumes and
the generalisation is **built from the goal**, never written down
(entry 34: a term of a tactic is read on its own, and the type
variables of a statement are the parser's).  Two shapes:

```ocaml
(* the list that a field of the state is *)
let r2_induct =
  W(fun (asl,w) ->
    let vs,bod = strip_forall w in
    let s = el 1 vs in
    let r2s = find_term
      (fun t -> hd_is "gc_state_r2" t && rand t = s) bod in
    let l = variant (vs @ frees bod) (mk_var("l",type_of r2s)) in
    let gen = list_mk_forall(l :: vs, mk_imp(mk_eq(r2s,l),bod)) in
    SUBGOAL_THEN gen (fun th ->
      MAP_EVERY X_GEN_TAC vs THEN
      ACCEPT_TAC(MP (SPECL (r2s :: vs) th) (REFL r2s))));;
```

and, where no field is taken apart, the measure that the
definition was made with (`MEASURE (\(conf,state). ...)` of the
`cake_define_try_tac`), with `list_mk_icomb` for the constants so
that the types are the goal's:

```ocaml
let meas =
  mk_binop `(-):num->num->num`
    (list_mk_icomb "gen_gc_conf_limit" [cc])
    (list_mk_icomb "heap_length" [list_mk_icomb "gc_state_h1" [s]])
```

`LIST_INDUCT_TAC` or `INDUCT_TAC` then does the induction, and the
step that uses the hypothesis is
`MATCH_MP_TAC(REWRITE_RULE[GSYM IMP_CONJ] ih)` with the witnesses
read off the goal's own equation.  Of a measure the base case is
not a case of the function at all: the branch that recurses is the
one the measure forbids, so it closes by arithmetic
(`SUBGOAL_THEN \`F\` CONTR_TAC THEN ... ASM_ARITH_TAC`).

### Where it lives

`gc_move_refs_data_refs_split` (a list) and
`gc_move_data_data_refs_split` (a measure) of
`proofs/compiler/backend/proofs/data_to_word_memoryProof.prf`, and
`compile_code_labels` of `bvi_letProof` (the first of them).

### Dead ends

- writing the generalised statement down: the type variables of a
  statement are invented by the parser (entry 25), so `SPEC` of it
  fails and `ISPEC` leaves the rest of them to `SPECL`, which
  fails as well;
- `MATCH_MP_TAC` of the generalisation against the goal: the goal
  is the implication of the statement, so the equation has to be a
  **separate** antecedent of the generalisation, and even then the
  match is on a conclusion that the theorem's own bound variables
  stand in -- `MP ... (REFL t)` and `ACCEPT_TAC` is what works;
- `REWRITE_TAC[GSYM imp]` of the equations that a cheated lemma
  about the state gives: with the `IS_PREFIX` and `IS_SUFFIX`
  conjuncts in the set the rewrite does not come back (minutes),
  where `MAP_EVERY (fun e -> SUBST1_TAC (SYM e))` of the equations
  alone is instant.

## 36. Where a tactic broke, without splitting it by hand

`prove` says which exception came out of a tactic and nothing
else: `Failure "tryfind"` for an unguarded `FIRST_ASSUM` that
found nothing, `Failure "ACCEPT_TAC"` for a term whose types are
not the goal's, `seqapply: Length mismatch` for a `THENL` over
more goals than its list has.  None of them says *where*, and the
proof that produced it can be fifty lines, so finding the step
used to mean cutting the proof into a `bsteps` list by hand and
reading the goal state of each step -- a round of the session per
guess.

`tools/bh.ml` now shadows `THEN` and `THENL`:

```ocaml
let b_watch lab (t:tactic) : tactic =
  fun g -> b_note lab g; let r = t g in b_steps := !b_steps + 1; r

let ((THEN):tactic->tactic->tactic) =
  fun t1 t2 -> b_orig_then (b_watch "" t1) (b_watch "" t2)
```

so every step records the goal it is applied to, and `bp`/`bt`
print the record of the step that got **furthest** when the
attempt fails.  Of two records the deeper one is the one to show,
because the failures inside `ORELSE`, `FIRST`, `REPEAT` and `TRY`
are expected and shallow; the chronologically last is printed as
well when it differs.  The kernel's own combinators are untouched,
so only the tactics written after the harness is loaded are
instrumented -- which is exactly the attempt being developed --
and the cost is one `ref` write per step.

A failure that is *not* an exception (`TAC_PROOF: Unsolved
goals`) is the other half: there `b_show` prints the goals that
are left, which is what the attempt has to be read against.  So
the two reports together are what the session used to be needed
for, and a trial is one round of the REPL again.

`bp` is the same attempt against a **term** instead of a theorem
of the file, for the lemmas a proof wants on the way, and it hands
the theorem back (`b_the`) so the next attempt of the round can
use it.

## 37. The direction of APPEND_ASSOC

HOL4's `APPEND_ASSOC` associates to the left
(`(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)`), HOL Light's to the right:

```
APPEND_ASSOC |- !l m n. l ++ m ++ n = (l ++ m) ++ n
```

and `++` prints right-associated, so `A ++ B ++ C` on the page is
`A ++ (B ++ C)`.  `REWRITE_TAC[APPEND_ASSOC]` therefore brings a
term to the **left**-associated form and `GSYM APPEND_ASSOC` to
the right one -- the opposite way round from the HOL4 proof that
is being read.  A rewrite that has to see `(A ++ B) ++ C` (an
update at `LENGTH (A ++ B)`, say) wants the plain theorem, and a
goal whose two sides differ only in the bracketing closes with
`GSYM APPEND_ASSOC` and the clauses of `APPEND` together, which
turn `[x] ++ C` into `x :: C` as well.

## 38. What the parser reads of a term that a tactic writes

Entry 34 is about the types that a term of a tactic invents.  Two
more of its kind, both of which typecheck and so are found only by
the proof going wrong somewhere else:

**`::` binds looser than `++`.**  HOL4 prints `l1 ++ e::rest` for
the list that is `l1 ++ (e :: rest)`, and in HOL Light the same
line reads `(l1 ++ e) :: rest` -- which typechecks, with `e` a
list and `rest` a list of lists, so a lemma written that way is
proved and then never applies.  A cons next to an append is
parenthesised.

**An overloaded token takes the latest overload.**  The port
defines the integer operations of CakeML, so the token `<=` in a
term that a tactic writes is `int_le` unless something forces the
other reading.  `ASM_CASES_TAC \`yp <= xp\`` therefore splits on a
statement about two *integer* variables that the goal has never
heard of, the assumption it adds is useless, and what fails is the
`ASM_ARITH_TAC` three steps later (`linear_ineqs: no
contradiction`, with the conjunct printed untranslated among
`real_of_int` ones -- that is the tell).  A numeral in the term is
enough to force `num` (`4 <= yp` is fine), and otherwise the
variable is annotated: `(yp:num) <= xp`.

Terms built up with `mk_binary "<="` and `mk_small_numeral` are
not affected, because those name the constant rather than the
token -- which is one reason the tactics that read bounds off the
goal (`COPY_BNDS_TAC` of `data_to_word_memoryProof`) build their
terms that way.

**A general `ARITH_RULE` in a rewrite is a schema.**
`REWRITE_TAC[ARITH_RULE \`j + 1 = 1 + j\`]` rewrites `xp + 1` to
`1 + xp` as well, because the rule's variables are generalised; of
the three occurrences in a goal it is the first that it reaches.
Where one specific sum is meant, `SUBGOAL_THEN \`j + 1 = 1 + j\`
SUBST1_TAC THENL [ARITH_TAC; ALL_TAC]` rewrites that term and
nothing else.

## 39. The attempt of a statement that is not proved yet

Phase three replaces a `CHEAT_TAC` with a proof, one statement at a
time, and what stands at a statement nobody has got to yet used to
be the bare cheat.  It is better for the attempt to be there:

```
### <name>
  (* the attempt: the proof of the source names <facts>.  What is
     here rewrites with them and closes by arithmetic or by MESON,
     and the cheat is behind it until the proof is written *)
  (ATTEMPT_TAC 5
    (REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC[<facts>] THEN
     TRY ASM_ARITH_TAC THEN
     TRY(ASM_MESON_TAC[<facts>])))
```

`ATTEMPT_TAC secs tac` of `ml/lib/tactics.ml` gives the attempt
`secs` seconds of processor time and falls back on `CHEAT_TAC` when
it does not close the goal.  It cannot be written as
`FIRST [SOLVED tac; CHEAT_TAC]`, because `Cake_timeout` is not a
`Failure` and `FIRST` would not catch it.

What this buys: the work that is left is in the port and not in a
list beside it, the facts named are the ones the source proof uses
(so the next round starts where the source starts), and
`length (axioms())` still counts exactly the statements that are
not proved -- an attempt that starts to go through takes its own
cheat away.

Two filters are needed when the facts are read off the source
proof.  A fact is only usable if **this file's closure** binds it:
`finalise_cons_def` is of `bvi_tmc`, which
`data_to_word_memoryProof` does not need, and naming it stops the
load.  And a fact that **this file** binds must be bound *before*
the statement, which is what `tools/scope.py` reports: HOL4 names a
theorem `xor_bytes_xor_words` of another theory inside the proof of
its own `xor_bytes_xor_words`, and the port's one stands further
down.

What it costs is the load: an attempt that fails fast costs
nothing, and one that searches costs its budget.  Keep the budget
small (five seconds) and the fact list short (six), or a file of a
hundred attempts adds ten minutes to every load of it.

## 40. The epsilon term that MATCH_CONV leaves

`MATCH_CONV` reduces a match whose scrutinee is a constructor.
Where the scrutinee is a term that a rewrite has just produced --
the `SOME rest` of a recursive call, say -- it does not fail: it
gives the relational form of the match, with the pattern as a
condition and the branch as an epsilon term:

```
(if existsunique p. ?rest. p = SOME (b :: rest) /\ SOME rest = SOME a'
 then @p. ?rest. p = SOME (b :: rest) /\ SOME rest = SOME a'
 else @x. false) = SOME res
```

`safe_match_conv` of `ml/lib/tactics.ml` refuses to make one of
these (that is what it is for), but `MATCH_REDUCE_TAC` makes them,
and a proof that has one in front of it is stuck until it is taken
apart.  Three steps do it, in this order:

```
   REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
   TRY (CONV_TAC(REDEPTH_CONV UNWIND_CONV)) THEN
   REWRITE_TAC[EXISTS_UNIQUE_REFL; SELECT_REFL;
               distinctness "option"; injectivity "option"]
```

The first one makes the condition of the pattern an equation of the
bound variable (`SOME rest = SOME a'` becomes `rest = a'`), which
is what `UNWIND_CONV` asks for; the second one solves the
existential away; and then `EXISTS_UNIQUE_REFL` makes the guard
true and `SELECT_REFL` reads the branch off the epsilon term.  The
order matters: `UNWIND_THM1` as a rewrite does not fire on
`?rest. p = f rest /\ SOME rest = SOME a'`, and `UNWIND_CONV` does
not fire before the `SOME`s are peeled.

## 41. An inner lemma that SPECL has to instantiate

A proof of a statement about `dimindex (:'a)` often proves a
general lemma first and applies it to the statement.  If the
application is by `SPECL`, the lemma has to be stated **with the
type variable of the statement**:

```
   let aux = prove
    (`!ls n m i b (t:'a word) be'. ... `, ...) in
   ...
   MP_TAC (SPECL [ls; n; `0`; i; b; t; be] aux)
```

`SPEC` instantiates the term variables of a theorem and not its
types, so an `aux` about `(N)word` and a goal about `'a word` give
`Failure "SPECL"`.  `ISPECL` instantiates both, and is what to use
for a lemma of the library (`EL_DROP`, `NOT_CONS_NIL`), whose type
variables are its own.  `MATCH_MP_TAC` and `MATCH_ACCEPT_TAC`
instantiate types as well, so a lemma that is applied that way can
be stated with any type variable.

## 42. Three ways a tactic loses what it was given

Each of these took a run to find, and each shows up as
`Failure "tryfind"` or as a goal that has lost an assumption:

- `DISJ_CASES_THEN f th` hands the disjunct to `f` and does **not**
  put it in the assumptions.  A branch that ends in
  `ASM_MESON_TAC[]` has to be written `(fun e -> ... MESON_TAC[e])`
  or start with `ASSUME_TAC e`.
- `STRUCT_CASES_TAC` rewrites the goal and not the assumptions, so
  the induction hypothesis of an induction whose list it takes
  apart is about the old variable and useless.  `CASES_ON_NAME` of
  `ml/lib/tactics.ml` is the one to use there: it substitutes
  everywhere.
- `FIRST_ASSUM`/`FIRST_X_ASSUM` with a test that is too loose picks
  the wrong assumption and the step after it fails somewhere else.
  A test on the head constant of the conclusion is rarely enough in
  a proof about an invariant, where four assumptions are `!`s: the
  test that works is on the shape, as in
  `let bod = snd (strip_forall (concl th)) in
   is_imp bod && hd_is "bc_ref_inv" (rand bod)`.

And one that is not about losing anything but shows up the same
way: the equation `SOME (MutBlock ...) = SOME (Thunk ...)` is not
refuted by `distinctness "bvlSem_ref"` alone.  The rewrite needs
`injectivity "option"` as well, to peel the `SOME` off both sides
first -- without it the disjuncts of `v_inv` that a reference of
another kind would take stay in the goal, and the `THENL` after
them reports `seqapply: Length mismatch`.

## 43. A proof that was fast while the definition was wrong

Two proofs of `data_to_word_memoryProof` went through in a session
in minutes and then cost the file **tens of minutes** when it was
loaded from the start.  The reason is worth knowing before writing
the next one.

### What happened

`vb_eq_size` was assumed as a list of clauses, one per pair of
constructors, with a catch-all clause at the end -- the shape that
entry 42 and `ISSUES.md` say is inconsistent.  A session that had
that list had the clause of each pair as a **rewrite**, so a proof
that takes the two values apart found its case in one step.  With
the definition in the one `match` that HOL4 means (`MATCH_CLAUSES`
of `tools/overrides.py`), the same proof reduces that match again
in each of the twenty-five cases, and `MATCH_CONV` on a match of
five arms with a nested match of four is not cheap.

The same thing in the large: a proof that closes every leaf of the
case tree of `word_eq` with `ASM_ARITH_TAC` pays the linear
arithmetic prover per leaf, with fifteen assumptions each, most of
them not arithmetic at all.

### What to do

- derive the clause of each constructor pair **once**, as a lemma
  of the proof (`prove(\`f (Number n1) (Number n2) = ...\`,
  ONCE_REWRITE_TAC[f_def] THEN MATCH_REDUCE_TAC)`), and rewrite
  with those nine lemmas in the case analysis;
- close the leaves with the cheapest thing that works:
  `ASM_REWRITE_TAC[LE_REFL]` where the equations of `PAIR_EQ` are
  in the assumptions, `EXISTS_TAC` of the witness the assumption
  gives and `ACCEPT_TAC` for an existential goal, and
  `ASM_ARITH_TAC` only where there is real arithmetic;
- never leave `ASM_MESON_TAC[]` at the end of a proof whose
  assumptions include the induction hypothesis of a family: MESON
  takes the `!`s as clauses and searches for minutes.

### How to see it

A `verifyquick` is the only honest measure (the session that wrote
the proof has the file's earlier content in it, and -- as above --
may have other things too).  `tools/bin/verifyquick` prints the
seconds; the file was 743 seconds with ten proofs of this round in
it.  A proof that is written and too slow belongs in the attempt's
comment, with what it needs, until it is made cheap -- which is
where `word_eq_LESS_EQ` and `vb_eq_size_IMP_vb_size` stand.

## 44. The induction of a definition that the port does not have

HOL4's `Definition` gives a `foo_ind` with it, and a proof of the
source starts `ho_match_mp_tac foo_ind`.  The port has no such
theorem: `cake_define_try_tac` makes the constant and its clauses
and nothing else.  Where the recursion is on a measure -- and in
the sources that is where the termination needed a
`WF_REL_TAC 'measure ...'` -- the induction to write by hand is a
complete induction on that measure:

```
let aux = prove
 (`!n v refs ts_opt v' refs' ts'.
     sptree_size refs = n /\ ... ==> ...`,
  MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ...) in
REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_MESON_TAC[aux]
```

The extra variable `n` with `measure x = n` as a conjunct is what
makes the hypothesis usable: it is `!m. m < n ==> !...`, and the
recursive call is reached by `SPEC` of the measure at the smaller
argument, with the decrease discharged from the clause's own
condition.  `MEASURE_INDUCT_TAC` of `ml/lib/tactics.ml` does the
same with `INDUCT_TAC` on a bound, which leaves a base case that
has to be proved as well; `num_WF` has none, so prefer it where
the decrease is strict.

The decrease is a lemma of its own and the one real piece of work:
for `finalise_cons` it is that a delete of a key that is there
makes the tree smaller, which HOL4 gets from `size_delete` of
`sptreeTheory` and `lookup_zero` of `miscTheory`.  Both are proved
by `MATCH_MP_TAC spt_INDUCT`, and the smart constructors need the
size law that `lookup_mk_BN` of `ml/lib/sptree.ml` is the lookup
law of.

**Where such a lemma goes.**  Not in `ml/lib/lemmas.ml`: that file
is loaded from `ml/lib/preamble.ml`, which comes **before**
`ml/lib/sptree.ml` (and before `ml/misc/misc.ml`), so a lemma about
a tree does not even parse there.  Either it stands in the proof
that needs it -- which is what `finalise_cons_none` does -- or it
belongs in `ml/lib/sptree.ml` itself, and then the closure of every
file below has to be built again (`tools/bin/pfbase`, half an
hour).  The first is right while one proof needs it.

## 45. The guard of a pattern has the pattern on the left

`MATCH_CONV` turns an arm whose pattern binds variables into a
guard, and the guard is

```
if ?tag fin l c r. SOME (MutBlock tag fin l c r) = lookup k refs
then ... else ...
```

-- the **pattern** on the left of the equation and the scrutinee on
the right.  So `distinctness "bvlSem_ref"`, whose conjuncts are
`~(ValueArray a = ByteArray b c)` in the declaration's order, does
not fire on it, and neither does `case_rws` of
`ml/lib/tactics.ml`, which is the list that `PRUNE_TAC` and
`EVERY_CASE_TAC` use.  The rewrite set that decides such a guard is

```
let ds = CONJUNCTS (distinctness "bvlSem_ref") in
injectivity "option" :: distinctness "option" ::
injectivity "bvlSem_ref" :: ds @ map GSYM ds
```

with `injectivity "option"` to peel the `SOME` (entry 42) and the
`GSYM`s for the orientation.  Without them the four arms of the
match stay side by side in the assumption and every later step is
applied to a goal that still has all of them.

## 46. Do not open a recursive definition in every assumption

`RULE_ASSUM_TRY (ONCE_REWRITE_RULE[foo_def])` after a case split
looks like the way to reduce the one assumption that says what the
call gives.  It also rewrites the **induction hypothesis**, which
holds a call of `foo` too: the hypothesis becomes the whole body of
the definition under two quantifiers, and the proof dies with
`Stack overflow` several steps later, with nothing in the report to
say why.  Open the one assumption:

```
FIRST_X_ASSUM (fun fc ->
  let c = concl fc in
  if not (is_eq c) ||
     not (hd_is "dataSem_finalise_cons" (lhs c)) then fail() else
  ASSUME_TAC (ONCE_REWRITE_RULE[dataSem_finalise_cons_def] fc))
```

## 47. A name of the file that shadows one of HOL Light

`data_to_word_memoryProof.ml` has

```
let is_cond t = is_forall t && is_eq(snd(strip_forall t));;
```

at line 24033 (a helper of one of its proofs, which the source
writes as an ML value).  From there on `is_cond` is that, and a
session that has the file loaded sees it everywhere -- so a tactic
of a proof **earlier** in the file behaves one way in the file and
another way in the session that is used to write it.  The symptom
is a `Failure "find"` from a `find` over the assumptions that
plainly should have matched one.  Write such a test with `hd_is`:
`hd_is "COND" (lhand c)` rather than `is_cond (lhs c)`.

## 48. A helper of a proof may not be named after a CakeML constant

The `needs` lines of a generated file are not the Ancestors of the
source: `providers` of `tools/db.py` takes every name the generated
text uses and adds the theory that defines it.  So a proof whose
helper is called

```
let CLOSE = TRY (SOLVED (VAR_EQ_TAC THEN ASM_REWRITE_TAC[])) in
let move = prove (...) in
let v_rel = GEN_ALL (...) in
```

gives the file three `needs` it has nothing to do with --
`basis/pure/mlsexp.ml` (which has a `CLOSE`),
`compiler/backend/stackLang.ml` (a `move`) and
`compiler/backend/proofs/bvi_letProof.ml` (a `v_rel`).

That is worse than untidy.  A `needs` that the closure of
`tools/bin/pfbase` was not built with is **loaded** into the clone
that `tools/bin/verifyquick` uses, and a file of the port that is
loaded a second time into a session that already has its constants
dies -- the report is an error deep in another file:

```
Exception: Failure "bvi_let_compile has the types ... and ..."
Error in included file .../ml/compiler/backend/bvi_let.ml
```

So: after `tools/bin/portfile`, look at whether the `needs` lines
changed (`git diff` of the generated file, `grep '^[-+]needs'`).  If
they did and the proof did not mean to use anything new, a helper
has collided with a constant of CakeML; rename it (`CLOSE_ARM`,
`heap_move`, `v_inv_moved`).  The names that are free can be checked
before writing:

```
python3 -I - <<'PY'
import sys; sys.path.insert(0,'tools'); import db
d = db.Db()
for nm in ['CLOSE_ARM','heap_move','v_inv_moved']:
  print(nm, [t for t,_ in d.defs.get(nm,[])])
PY
```

## 49. A lemma that MATCH_MP_TAC can aim, not a term dug out by hand

The proofs of this port grow a tail of `W(fun gl -> ... the_asm
... el 1 (snd (strip_comb ...)) ...)` steps that pick an assumption
out and build a term from its pieces.  Every one of them is a
guess about the goal, and when the guess is wrong the report is a
`Failure "find"` or `"tryfind"` several steps later, in a state
that says nothing about which `the_asm` missed.  `el_thm` cost nine
rounds that way.

The cheap alternative is to state the step as a **lemma with every
variable quantified**, whose conclusion is the goal:

```
let all2_el_cons = prove
 (`!(P:A->B->bool) xs ys i a b st rs.
     EVERY2 P xs ys /\ i < LENGTH xs /\ P a b /\ EVERY2 P st rs
     ==> EVERY2 P (EL i xs :: a :: st) (EL i ys :: b :: rs)`,
  ...)
```

and then the proof is

```
MATCH_MP_TAC all2_el_cons THEN
CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
<the one goal that is not an assumption>
```

-- the conclusion does the matching, HOL Light instantiates every
variable from the goal, and what is left is a list of goals that
`FIRST_ASSUM ACCEPT_TAC` closes one by one.  Nothing can pick the
wrong assumption, and the lemma is reusable and testable on its
own (one `bp` in a batch, seconds of feedback, instead of a
twelve-minute file).

Two things to watch:

- a lemma whose variables are **free** rather than quantified does
  not generalise: `MATCH_MP_TAC` leaves such a variable fixed, so
  the goal it makes is unprovable (`x1` of
  `gc_heap_inline_rel_v_inv`).  `GEN_ALL` first, and then the
  variables that the conclusion does not mention become
  existentials, in `GEN_ALL`'s order -- which is worth printing
  once (`say (String.concat "," (map (fst o dest_var) (fst
  (strip_exists w))))`) rather than guessed;
- a relation applied to a lambda leaves a beta-redex in the goals,
  so `CONV_TAC(TOP_DEPTH_CONV BETA_CONV)` goes before the
  `ACCEPT_TAC`s.

## 50. A test of a section loads what the file loads, and no more

The quick check after `tools/bin/portfile` is to lift the generated
section into a file and `bt` it in the session.  That test is only
worth something if the file it loads has **nothing in it that the
port does not have**.  A test file that begins

```
let SHOW lab = W(fun gl -> b_state lab 0 gl; ALL_TAC);;
```

and a section that still carries a `SHOW` in the last alternative
of a `FIRST` -- a probe left behind from the round that wrote the
proof -- pass the test together and then kill the load of the file
itself:

```
Error: Unbound value SHOW
Error in included file .../data_to_word_memoryProof.ml
```

`verifyquick` reports it as `AXIOMS-ADDED 58` and an error, which
looks like something much worse than a leftover probe.  So: grep the
section for the names of the probes (`SHOW`, `b_state`, `say`,
`b_watch`) before landing it, and keep the harness names out of
`tools/overrides.py` and the `.prf`.

## 51. A GSYM of an injectivity theorem loops the rewriter

Entry 45 gives the rewrite set that decides the guard of a pattern,
and the `GSYM`s in it are of the **distinctness** theorems only.
The temptation is to write

```
let ds = [distinctness "option"; injectivity "option";
          distinctness "bvlSem_ref"; injectivity "bvlSem_ref"] in
REWRITE_TAC (ds @ map GSYM ds)
```

and that is a `Stack overflow`: `injectivity "option"` is
`SOME a = SOME b <=> (a = b)` and its `GSYM` is
`(a = b) <=> SOME a = SOME b`, so the two rewrite each other for
ever.  A distinctness theorem is a negation and has no such
partner, so

```
let ds = [distinctness "option"; distinctness "bvlSem_ref"] in
REWRITE_TAC (injectivity "option" :: ds @ map GSYM ds)
```

is the set to use.  The reduction of a match that the patterns
cannot decide is worth keeping as one tactic (the port has it as
`REDUCE_MATCH_HARD` above `update_ref_thm`): `MATCH_REDUCE_TAC`,
the set above, `UNWIND_CONV`, `SELECT_REFL` and
`EXISTS_UNIQUE_REFL` for the epsilon terms that are left, and
`MATCH_REDUCE_TAC` once more.

## 52. Split the assumptions, then choose, then split again

`SPLIT_ASM_TAC` takes the conjunctions of the assumptions apart and
a `CHOOSE_TAC` pass takes their existentials apart, and the order of
the two is not a matter of taste.  The arm of `bc_ref_inv` for a
`MutBlock` is

```
(!gs. ~(gc_kind conf = Generational gs)) /\
(~fin ==> ~(x IN IMAGE (FAPPLY tf) (FDOM tf))) /\
(?zs. heap_lookup x heap = SOME (BlockRep tg zs) /\ ...)
```

-- an existential **inside** a conjunction.  A pass that chooses
first finds nothing to choose, the split then leaves the
existential standing, and the one arm of four that has this shape
is the one that fails, with the other three closed.  So: split,
choose, split.

## 53. The lists of an invariant and of its arm go the other way

`bc_stack_ref_inv` relates the stack to the roots,

```
EVERY2 (\v x. v_inv conf v refs (x,f,tf,heap)) stack' roots
```

-- the values first -- and the `ValueArray` arm of `bc_ref_inv`
relates the roots to the values,

```
EVERY2 (\z y. v_inv conf y refs (z,f,tf,heap)) zs ys
```

-- the roots first.  So the part of the split of the first that
belongs in the second has to be turned round with `EVERY2_SWAP`
(HOL4 does it with `imp_res_tac EVERY2_SWAP`), and the lambda that
comes out of it is a redex:

```
CONV_RULE(TOP_DEPTH_CONV BETA_CONV) (MATCH_MP EVERY2_SWAP old)
```

Without the `BETA_CONV` the theorem is about
`\y x. (\v x'. v_inv ...) x y` and no `ACCEPT_TAC` of the arm sees
it.  A picker that goes by which list is which (`el 1` against
`el 2` of the `ALL2`) tells the two apart without reading the
lambda.

## 54. Read the definition before resolving against its assumption

`res_tac` of HOL4 resolves an assumption against the others and
says nothing about what it used.  The port does it by hand, and
then the antecedent has to be the one the definition has.  The
invariant of the references of `bc_stack_ref_inv` is

```
!n. reachable_refs stack' refs n /\ n IN FDOM f
    ==> bc_ref_inv conf n refs (f,tf,heap,be')
```

-- a conjunction of two, not the reachability alone.  `MP (SPEC n
inv) reach` is then `MP: theorems do not agree`, which says nothing
about which half is missing; `CONJ reach (the_asm ...)` is the step.
Both halves are among the assumptions when the goal is the same
invariant of the new heap, because stripping its own `!n ... ==>`
puts them there.

## 55. A lemma's free variable may not be the goal's other list

A lemma of a block that several proofs share is applied with
`MATCH_ACCEPT_TAC (MATCH_MP lemma (CONJ ...))`: the hypotheses fix
most of its variables and `MATCH_ACCEPT_TAC` instantiates the rest
from the goal.  That last step fails when a variable it has to
instantiate **has the same name and type as a variable of the
goal that stands for something else**.  The lemma

```
RefBlock_inv heap heap2 /\ lookup ptr refs = SOME (ValueArray as1) /\
v_inv conf v1 refs (v2,f,tf,heap) /\ MEM v1 stack'
==> v_inv conf v1 (insert ptr (ValueArray xs) refs)
      (v2,f,DRESTRICT tf (all_ts (insert ptr (ValueArray xs) refs)
                            stack'),heap2)
```

has `xs` for the array that is written, and no hypothesis mentions
it, so the match has to find it in the goal.  In `update_ref_thm`
the array written *is* the goal's `xs` and the match succeeds; in
`update_ref_thm1` it is `LUPDATE (HD xs) i xs1`, and the goal's
`stack'` is `xs ++ RefPtr b ptr::stack` -- the same `xs`.  An
instantiation `xs := LUPDATE (HD xs) i xs1` would rewrite the
stack as well, so there is none and the step fails with
`Failure "ACCEPT_TAC"`.

The fix is to name the variable of the lemma something the goals do
not use (the block of `update_ref_thm` calls the array that is
written `vls`).  `INST` on the lemma before the `MATCH_MP` does the
same thing by hand, and is what to reach for when the lemma cannot
be renamed.

## 56. A block assembled from scratch files takes the last version

The lemmas of a proof are written in a scratch file each
(`tmp/tryNNN.ml`), and the one that lands in `tools/overrides.py`
is assembled from them.  A picker that is fixed in a later round
sits in two scratch files then, and the assembly has to take it
from the later one.  Taking it from the earlier one gives a block
that the session proves and the file does not:

```
val EVERY2_ARM_GEN_TAC : thm -> goal -> goalstate = <fun>
Exception: Failure "TAC_PROOF: Unsolved goals".
```

-- because the session still has the fixed picker bound from the
round that fixed it, while the file has the stale one.  The same
trap catches the check afterwards: a session that loaded the file
before the fix keeps the file's old binding, so a scratch test of
the regenerated lemma still fails until the fixed picker is loaded
into the session by hand.  So: assemble from the latest scratch
file of each piece, and when a lemma that the session proved fails
in the file, diff the file's text of **every** helper it names
against the scratch file's before looking anywhere else.

## 57. The session to try a proof in is cut at the statement

There are three bases a try can run in, and they are not equally
honest:

- `hol-pfbase` (`tools/bin/pfbase`) holds the **closure** of a
  file -- every file it `needs` and nothing of the file itself.
  Half an hour to build, a second to clone; `verifyquick` clones it
  and loads the whole file on top.
- the session a `verifyquick` leaves (`hol-vq`) holds the **whole
  file**.  It is free, because the verify has to run anyway, and a
  try in it costs one `repl-step` -- which is why the proofs of
  this round were written in it.
- `tools/bin/trybase <file> <statement>` holds the file **up to the
  statement**: a clone of `pfbase` with the prefix loaded.

The second is the fast one and the dangerous one.  It has every
later definition of the file in scope, so a proof can lean on a
name that the file does not have yet (`tools/scope.py` catches
that), and worse, it accumulates **the bindings of the rounds that
wrote the lemmas** -- a fixed picker, a renamed lemma, an older
version of a tactic.  A lemma then proves in the session and fails
when the file loads it, which is entry 56 twice over.  A base cut
at the statement cannot be fooled either way: what comes after is
absent, and a fresh clone has nothing of a scratch round in it.

What it costs is the prefix: `update_mutblock_thm` sits at line
10398 of 29042, so its base is about a third of the file's 753
second load.  That is paid once per statement and cloned per try,
and it buys a try that means what it says.  So: `trybase` for the
statement being proved, and the verify's session only for reading
a goal state when nothing is being landed.

## 58. A helper lemma of a store names its heaps in a hypothesis

A helper lemma of a proof is applied to the assumptions with
`MATCH_MP` and then to the goal with `MATCH_ACCEPT_TAC`, so every
variable of it is fixed from one of the two sides -- and the
matching is _syntactic_.  A variable that stands only in the
conclusion is fixed by the goal, which is fine as long as it is a
variable there too; a variable that stands only in the conclusion
and is a _compound term_ in the goal is not fixed at all, and the
lemma comes out about its own variable.

That is what makes a transfer of a store awkward.  `BA_trans` says
what a store into a byte array does to the invariant:

```
  (!w1 w2. v_inv conf w1 refs (w2,f,tf,ha ++ [Bytes be fl xs ws] ++ hb)
           ==> v_inv conf w1 (insert ptr (ByteArray fl ys) refs)
                 (w2,f,tf,ha ++ [Bytes be fl ys ws] ++ hb))
```

and the proof hands it to `bc_ref_inv_update_other_gen`, which
wants that transfer and the old invariant together: the two have
to be about the _same_ heap, so the heap of the transfer must be
the goal's heap and not the lemma's `ha ++ [Bytes be fl xs ws] ++
hb`.  In `update_byte_ref_thm` the `ws` of the goal is
`REPLICATE (LENGTH xs DIV (dimindex (:'a) DIV 8) + 1) 0w`, not a
variable, so nothing fixed it and the application failed with
`MP: theorems do not agree`.

The cure is to give the lemma a hypothesis that the proof has
anyway and that mentions what the conclusion needs:

```
  heap_lookup p (ha ++ [Bytes be fl xs ws] ++ hb) =
    SOME (Bytes be fl xs ws) /\ LENGTH xs = LENGTH ys
```

-- the lookup of the element fixes `ha`, `hb`, `be`, `fl`, `xs`,
`ws` and `p`, the length equation fixes `ys`, and the rest
(`conf`, `f`, `tf`) are variables of the goal as well.  The
hypothesis is not used in the proof of the lemma at all; it is
there to say which store is meant.  The same shape is what
`heap_lookup_byte_other` and `bc_ref_inv_update_byte_at` take, and
it is why `unused_space_inv_byte_update` of the source reads the
way it does.

So when a helper is written: list the variables of its conclusion,
and for each one name the hypothesis that fixes it.  A lemma with
no hypothesis at all (`isSomeDataElement_byte_update`) cannot be
applied this way and is used the other way round -- the proof
states the instance it wants as a `SUBGOAL_THEN` built from the
goal's own terms and closes it with `MATCH_ACCEPT_TAC`.

## 59. find_term finds the old heap first

A picker that reads a heap off a term with `find_term` gets the
_first_ one in the term order.  In a goal that has both heaps of a
store that is the one written into, not the one written:

```
  !m y. ~(m = heap_length ha) /\ heap_lookup m OLD = SOME y
        ==> heap_lookup m NEW = SOME y
```

so `byte_heap` of that goal is `OLD`, and a proof that wanted the
new element got `el_length u = el_length u` and an `MP` that did
not agree.  The pickers of a store therefore come in pairs:
`byte_heap t` and `byte_heap_not u t`, the second skipping the
append whose element is the one given.

## 60. port.py writes without a preface; portfile is the tool

`python3 -I tools/port.py <theory>` writes into `ml/` directly --
and a plain run of it writes **every** file of the load order,
without the prefaces, because `tools/preface.py` runs after the
port and only `tools/bin/dryport` arranges that.  The result is a
clean `git status` turning into 113 modified files whose prefaces
have been cut back to two lines.

`tools/bin/portfile <theory> ...` is the tool: it ports the whole
load order into `tmp/dry` (50 seconds, prefaces and all) and
copies out only the files asked for.  The recovery, if port.py has
already been run, is `git checkout -- ml/` with the hand-written
files of `ml/lib/` saved first -- they are sources, not output,
and a checkout would take the round's work on them with it.

## 61. The two sides of a lemma may not share a type variable

```ocaml
let el_length_DataElement = prove
 (`el_length (DataElement xs l d) = el_length (DataElement ys l d)`,
  REWRITE_TAC[el_length_def]);;
```

reads as it should and is not what it looks like.  `el_length`
gives a number, so nothing ties the two applications together:
`xs` is `((?1126164)heap_address)list` and `ys` is
`((?1051005)heap_address)list`, two type variables that happen to
print the same way.  `PART_MATCH lhs` against the element of a
goal then fixes the first and leaves the second, and the `INST`
that was to fill it in fails with `vsubst: Bad substitution list`
-- the error says nothing about types, and the terms print
identically, so this costs an hour if the types are not printed.

The cure is to say the type once and quantify:

```ocaml
let el_length_DataElement = prove
 (`!(xs:((A)heap_address)list) (ys:((A)heap_address)list) l (d:B).
     el_length (DataElement xs l d) = el_length (DataElement ys l d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[el_length_def]);;
```

and then to instantiate it with `ISPECL`, which instantiates the
types as well, rather than with `PART_MATCH` and `INST`.  The rule
of thumb: a lemma whose two sides are related only through a
*number* (a length, a count, a size) needs its types said out
loud, and `say ("  X " ^ string_of_term t ^ " : " ^
string_of_type (type_of t))` is what shows it when a match fails
for no visible reason.

## 62. A scratch session has unhidden what the file hides

A proof file of the port hides the names that HOL4 reads as
variables (`vars`, `el`, `not`, `parts`, `sign`, `free`,
`do_partial` for `data_to_word_memoryProof`) at its head and
**unhides them at its end**.  So in a session that has loaded the
file -- which is exactly the session a `verifyquick` leaves, the
cheap place to try a proof -- a quotation of a statement of that
file no longer parses:

```
Exception: Failure "typechecking error (initial type assignment):
  vars has type (?242981)term->num->bool, it cannot be used with
  type (dataSem_v#(_)word_loc)list".
```

A scratch file for such a session therefore begins with the hide
again:

```ocaml
let _ = do_list hide_constant
  ["do_partial"; "el"; "free"; "not"; "parts"; "sign"; "vars"];;
```

(the list is the one at the end of the ported file, which says
what it unhid).  The same holds for a session cut at a statement
with `tools/bin/trybase`: there the hides of the head are still in
force, so nothing is needed -- one more reason the cut base says
what it means (entry 57).

## 63. The two checks take a file or nothing, and said nothing

`tools/lines.py` walks a directory and `tools/scope.py` walks the
files it is given.  So

```
python3 -I tools/lines.py <one file>     # checked nothing: 0
python3 -I tools/scope.py                # checked nothing: 0
```

were both silent for a whole round of proofs, and both reports
were read as clean.  What they were hiding:

- eleven lines of the proof store had gone over 72 characters (the
  `.prf` text is indented by two when it lands in the file, so a
  line of 71 becomes one of 73);
- the block of `IMP_heap_store_unused` rewrote with
  `heap_length_clauses`, which stood in the block of
  `update_byte_ref_thm` eight thousand lines later, so the file did
  not load at all -- and that costs a twelve minute `verifyquick`
  to find out.

Both tools now take either a file or nothing.  The habit to keep:
**run `lines.py` and `scope.py` with no argument after every
`portfile`**, and read the counts, not the silence.  `scope.py`
over the whole port reports thirteen hits, all of them in
definition files where a `let` lower down has the name of a
constant of a statement higher up; the proof files are clean, so
anything new there is real.

The session cannot catch this one: it has the whole file loaded,
so a lemma of a later block is in scope there and the proof goes
through (entry 57 again, from the other side).

## 64. An element's shape lemma carries a type variable of its own

`BlockRep tag xs = DataElement xs (LENGTH xs) (BlockTag tag,[])` and
`ThunkBlock ev x = DataElement [x] 1 (ThunkTag ev,[])` both end in
`[]`, whose element type nothing in the equation fixes.  So
`BlockRep` and `ThunkBlock` have **two** type variables, and a lemma
about them (`el_length_ThunkBlock`, `isRef_BlockRep`,
`samelen_bytes`) carries its own copy of the second one.

`ISPECL [ev; y] el_length_ThunkBlock` therefore gives
`el_length (ThunkBlock ev y) = 2` whose `ThunkBlock` is at the
lemma's type, not at the heap's: it prints exactly like the one of
the goal and matches nothing (entry 61 again).  `MATCH_MP` then says
`No match`, or `term_match` says `safe_insert`.

What works is to build the instance from a term of the goal:

```
let elt = PART_MATCH lhs el_length_ThunkBlock
            (list_mk_icomb "el_length" [el1]) in
```

where `el1` is read off an assumption whose type the heap fixes (the
element of `heap_store_unused a (sp + sp1) el1 heap = (heap2,T)`).
`PART_MATCH` and `MATCH_MP` instantiate types; `ISPECL` and `SPEC`
only instantiate the type of what they specialise.

## 65. GEN fails when a bound name is a free name of an assumption

The transfer that an allocation leaves is built from the predicate
of the old `EVERY2`:

```
let v0,b1 = dest_abs pred in
let x0,bod = dest_abs b1 in
ASSUME_TAC (GENL [v0; x0] (DISCH bod (MATCH_MP step ...)))
```

`dest_abs` renames a bound variable only to avoid capture inside the
term, so of `\v x. v_inv conf v refs (x,f,tf,heap)` it hands back `v`
and `x` -- and `new_thunk_thm` has a value **named `v`** of its own,
which is free in the assumption `ev = Evaluated ==> dest_thunk v
refs = NotThunk` that the step takes.  An assumption of a goal is a
theorem `A |- A`, so that `v` is free in the hypotheses of what is
generalised and `GEN` refuses: `Failure "ABS"`.

So rename the pair before generalising:

```
let v1 = genvar (type_of v0) and x1 = genvar (type_of x0) in
let vtm = vsubst [v1,v0; x1,x0] bod in
ASSUME_TAC (GENL [v1; x1] (DISCH vtm (MATCH_MP step ...)))
```

A genvar cannot be a name of the statement, and the names of the
transfer do not matter to anything that uses it.

## 66. Which disjunct of v_inv a RefPtr has depends on its flag

The `RefPtr b n` clause of `v_inv` is three disjuncts: the plain
pointer, the pointer to a thunk, and a thunk that has been
evaluated away.  The second and the third ask for `~b`, so of a
`RefPtr T ptr` (`new_ref_thm`, `new_byte_alt_thm`) the rewrite with
`v_inv_def` leaves the first disjunct alone and `TRY DISJ1_TAC` is
the whole choice; of a `RefPtr F ptr` (`new_thunk_thm`) all three
stay, and the one that holds is the **second**, because the key does
hold a thunk -- `DISJ1_TAC` there reduces the goal to `false`, which
is what the report shows.

## 67. MATCH_MP_TAC of a statement without quantifiers leaves a free
variable

`MATCH_MP_TAC` existentially quantifies the variables of the
antecedent that the conclusion does not fix -- but only the ones the
theorem quantifies itself.  A lemma of the port is usually written
without them (`cake_as_vars` hands back a term whose names are free),
so of

```
let reach_ref = prove
 (cake_as_vars (fun () ->
    `(!y. MEM y (get_refs v) ==> ref_edge refs ptr y) /\
     reachable_refs (v :: RefPtr b ptr :: stack') refs n
     ==> reachable_refs (RefPtr b ptr :: stack') refs n`), ...)
```

`MATCH_MP_TAC reach_ref` leaves a goal about the lemma's own `v`,
which nothing can close -- the report shows `MEM y (get_refs v)` with
a `v` that is in no assumption.  `MATCH_MP_TAC (GEN_ALL reach_ref)`
gives `?v. ...` instead, and an `EXISTS_TAC` of the value from the
goal follows.  The same holds of `refs_in_block`, `v_inv_SUBMAP` and
`blocks_unique_cons_thm`: where the port writes
`MATCH_MP_TAC (GEN_ALL ...)` it is for this reason.

## 68. STRUCT_CASES_TAC splits the goal, CASES_ON_TAC the assumptions
too

Of a variable `md` of `thunk_mode` in the goal,
`STRUCT_CASES_TAC (ISPEC md (cases "thunk_mode"))` replaces it in the
goal and leaves the assumptions alone -- so an assumption
`lookup ptr refs = SOME (Thunk md vv)` keeps the variable and a lemma
about `Thunk NotEvaluated vv` does not apply to it.  `CASES_ON_TAC md`
(ml/lib/tactics.ml) is `SUBST_ALL_TAC` of each case for a variable, so
the goal *and* the assumptions get the constructor.  Use it whenever
the case is to be used on an assumption, which in a proof about
`bc_ref_inv` or `v_inv` is almost always.

## 69. MATCH_MP of a statement with free variables needs GEN_ALL too

`MATCH_MP` instantiates the leading quantifiers of a theorem, and
nothing else: of

```
gen_gc_data_refs_split:
  !cc roots heap. gen_gc cc (roots,heap) = (roots1,s) /\ ... ==> ...
```

the `roots1` and the `s` are **free**, so `MATCH_MP
gen_gc_data_refs_split eq` asks the equation to have exactly those
two names in it and says `No match` otherwise.  `MATCH_MP (GEN_ALL
gen_gc_data_refs_split) eq` works, and that is why HOL4's proof
writes `old_drule (GEN_ALL gen_gc_data_refs_split)`: HOL4's `drule`
does the `GEN_ALL` itself.  The same holds of `gen_state_ok_reset`
and of any lemma whose statement was written with free names (which
in this port is most of them).

The other side of it: once the hypotheses are supplied, a quantifier
of a variable they do **not** fix is still there, so
`MATCH_MP (GEN_ALL gen_state_ok_reset) ho` has the shape
`!conf. gen_state_ok ...`.  Reading `el 1 (snd (strip_comb (concl
th)))` off that gives the body of the quantifier, not the second
argument -- `Failure "hd"` -- so the `SPEC_ALL` belongs there:

```
let th = SPEC_ALL (MATCH_MP (GEN_ALL gen_state_ok_reset) ho) in
```

## 70. A SUBGOAL_THEN whose rewrite is for the subgoal alone

```
SUBGOAL_THEN tm (fun ir -> STRIP_ASSUME_TAC (MATCH_MP lemma ir)) THEN
REWRITE_TAC[make_gc_conf_def]
```

rewrites the **main** goal as well as the new subgoal, because `THEN`
applies to every goal that is left -- and a rewrite that unfolds a
definition of the statement (here `make_gc_conf`) makes the main goal
unmatchable afterwards.  `THENL [<the subgoal's proof>; ALL_TAC]` is
the form to use whenever the proof of the side condition rewrites
with anything the goal also mentions.

## 71. A definition whose clauses overlap: invert it once

Entry 43 says what a `match` definition costs a proof that takes its
arguments apart: the match is reduced again in each of the cases, and
`vb_eq_size` (five constructors against five, with a nested match on
two lookups) is twenty-five of them.  Entry 43's remedy is the clause
of each pair of constructors as a lemma.  There is a cheaper one when
what the proof needs is not *the value* of the function but *what a
value of it can be*: one inversion lemma per function.

```
let vb_eq_size_cases = prove
 (`!refs v1 v2 n b.
     vb_eq_size refs v1 v2 = SOME (n,b)
     ==> n = 1 \/
         (?ts1 t1 l1 ts2 t2 l2 m.
            v1 = Block ts1 t1 l1 /\ v2 = Block ts2 t2 l2 /\
            vb_eq_size_list refs l1 l2 = SOME (m,b) /\ n = m + 1)`,
  ...)
```

Twenty-five cases are paid **once**, inside the lemma, and the two
theorems about the function are then three lines each: the complete
induction of entry 44, `MATCH_MP` of the inversion lemma on the
assumption, and arithmetic at the leaves.  Measured: the block of six
lemmas is 0.9 seconds and the two theorems 1.6, where the old round's
proofs -- the same statements, reduced per case -- were tens of
minutes.

What the inversion lemma's own proof wants:

- the case split of the two arguments (`CASES_ON_TAC`), the
  definition unfolded in the **antecedent only** (entry 72), the
  conditions decided (`REPEAT COND_CASES_TAC`) and the nested
  matches split (`EVERY_CASE_TAC`);
- `UNWIND_THM1`/`UNWIND_THM2` beside `injectivity`, `distinctness`
  and `PAIR_EQ` in the rewrite list: they are what turns
  `?n. 1 = n /\ P` into `P`, so no branch needs a `MESON_TAC`;
- the witnesses of the one branch that has a conclusion, read off
  the goal's own conjuncts (`conjuncts (snd (strip_exists w))`) and
  the equation the split left among the assumptions;
- a `TRY` around the witness step, because a branch that the split
  settled on its own is already past it.

## 72. Unfolding a definition in the antecedent only

`ONCE_REWRITE_TAC[f_def]` on a goal

```
f refs v1 v2 = SOME (n,b) ==> ... f_list refs l1 l2 = SOME (m,b) ...
```

unfolds **both** occurrences: `ONCE_DEPTH_CONV` takes the topmost
instance of *each* disjoint branch of the term, and the two sides of
an implication are two branches.  The conclusion then holds the whole
case tree of the definition -- which is what the lemma was written to
avoid -- and a goal that was two lines prints as fifty.

```
GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [f_def] THEN
CONV_TAC (LAND_CONV (REDEPTH_CONV safe_match_conv))
```

is the form: the antecedent is unfolded and reduced, the conclusion
is untouched.  `MATCH_REDUCE_TAC` is not the reducer to use here --
it is `MATCH_CONV` under a traversal, and on a match whose scrutinee
the patterns cannot decide `MATCH_CONV` does not fail but returns an
`@x. ...` term, after which the goal is lost (entry 42's epsilon
goals, fifty lines of `GEN%PVAR` in the report).
`safe_match_conv` refuses exactly those.

## 73. The failure report follows the first goal only

`bp`/`bt` of `tools/bh.ml` replay the tactic a step at a time to say
which step broke.  The replay is `e tac`, which applies to the
**first** goal of the stack, so from the first branching step on it is
no longer the proof that ran: a state it prints may be one the real
proof had already closed, and the step it blames may be a step that
in the real proof never saw that goal.  The symptom is a report whose
goal cannot possibly fail (`n = x + 1` with `x + 1 = n` among its
assumptions).

What to do when a report looks impossible: make every step of the
tactic **total** -- a `TRY` around each step that can fail on a
branch it does not belong to -- and run it again.  `prove` then fails
with `TAC_PROOF: Unsolved goals` instead of an exception, and `bp`
prints the goals that are **really** left, with their assumptions
(`b_asm := true`).  That is the state to read.  Once the proof is
right, the `TRY`s that turned out to be needed are the ones that say
where a branch closes early, and the rest come out.

## 74. Do not split every variable of a product type

Opening the case tree of a definition means splitting the scrutinee
of each match and the argument of a constructor that a pattern takes
apart -- the pair under the `SOME` of `SOME (a1,h1)`.  The obvious
way to write the second one,

```
W(fun (asl,w) -> CASES_ON_TAC
  (find_term (fun t -> is_var t && prod_type (type_of t)) w))
```

finds **the records of the arguments** as well: a record of the port
is a product type (`ml/lib/records.ml`), so `c` (a
`data_to_word_config`) and `st` (a `wordSem_state`) are variables of
a product type, and splitting them splits every field, whose own
product fields split again.  The report said *the step that got
furthest broke after 88368 step(s)*, and the attempt spent its whole
processor-time budget there.

`CASE_SPLIT_TAC` of `ml/lib/tactics.ml` is the one to use:
`scruts_of_goal` splits a variable **only where a pattern of a match
looks into it**, so the pair under a `SOME` is split and the record
of an argument is not.  What it does not find is a scrutinee whose
head is a variable (`m a1`, the memory at an address), because its
`ok` asks for a constant head; that one is split by hand.

The same round is where the leaves became cheap, as entry 43 says
they must: `we_tidy` (the constructor rewrites of the goal **and**
the assumptions, then `FIRST_ASSUM CONTR_TAC`) and `we_close`
(`STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL]`) after every split, so
that a branch the split has settled is gone before the next one.

## 75. A theorem between two calls of the same definition: one tree

`word_eq_add_clock` says that a comparison run with a larger clock
returns what it returned:

```
word_eq c st dm m l ck a1 a2 = SOME (res,l',ck1)
==> word_eq c st dm m l (ck + n) a1 a2 = SOME (res,l',ck1 + n)
```

The obvious proof unfolds the definition **on both sides** and
opens the two case trees together.  It does not work: the two
inner comparisons (`word_eq ... (ck - 1) ...` and
`word_eq ... (ck + n - 1) ...`) are different terms, so the splits
multiply, and in a branch where the two trees took different arms
there is nothing in the goal to settle it -- the hypothesis of the
induction is what identifies the two, and by then the branch has
already been split and reduced.  Six rounds went on that.

What works is **one** tree:

- unfold the definition in the **assumption** only (`MP_TAC` of the
  unfolded equation) and leave the goal folded, so every split is
  a split of the assumption;
- in the branch it leaves, collect what the branch knows, then
  apply the hypothesis to each recursive call of the assumption;
- **then** unfold the goal, once, and let `ASM_REWRITE_TAC` and the
  match reduction drive its tree: every condition of it is decided
  by the branch, and every recursive call of it is what the
  hypothesis just gave.

Three details that each cost a round:

- **orient the branch's equations.**  A leaf of the assumption says
  `n2w 0 = res`; used as a rewrite that way it turns every zero of
  the goal's tree into `res` and the conditions stop matching.  One
  that says `SOME (a,h) = word_header ...` reduces no header at
  all.  So `VAR_EQ_TAC` first, and then `SYM` on every equation
  whose right side is a variable of the claim or whose left side is
  a constructor application.
- **only half of De Morgan.**  `~(a1 IN dm \/ ... \/ l = 0 \/
  ck = 0)` has to come apart for `ARITH_ASM_TAC` to see `~(l = 0)`
  (a negated disjunction is not an arithmetic fact and the filter
  drops it), but rewriting with the whole `DE_MORGAN_THM` also
  turns `~(word_bit 0 a1 /\ word_bit 0 a2)` into a disjunction --
  and that negated conjunction is exactly what the goal's own tree
  asks for.  `GEN_ALL (CONJUNCT2 (SPEC_ALL DE_MORGAN_THM))` is the
  rewrite to use.
- **the bound of a recursive call** whose budget came out of an
  inner call (`word_eq_list ... (l'' - 1) ...`) needs the first
  theorem of the pair (`word_eq_LESS_EQ`) to know `l'' <= l - 1`;
  without it the bound is unprovable, the `THENL` that discharges
  it fails, and the whole hypothesis step is skipped by its `TRY`
  with no sign of why.

## 76. One tactic per conjunct, and pickers that discriminate

`gen_gc_partial_thm` unfolds to five named pieces (`roots_ok`,
`heap_ok`, `gc_kind_inv`, `unused_space_inv`, `bc_stack_ref_inv`),
and the first shape of its proof was the one the other collections
use: `REPEAT CONJ_TAC` and then a chain of
`TRY (SOLVED (<the piece>))`.  Three rounds went on that shape and
none of them said anything:

- a piece that fails is **silently skipped**, so the report shows
  the goals that are left and nothing about why;
- a piece that is written for one goal is **tried on the others**,
  so its own error (`rand: Not a combination`) comes from a goal it
  was never meant for -- and in that round the chain had four
  tactics for five goals, so every piece after the third ran on the
  wrong goal;
- the failure report follows the first goal only (entry 73), so the
  state it prints is from yet another branch.

`REPEAT CONJ_TAC THENL [p1; p2; p3; p4; p5]` fixes all three at
once: each piece gets its own goal, a piece that fails says so with
its own exception, and the count is checked (a `Length mismatch` is
the mistake, immediately).

The same round is where the pickers had to learn to discriminate.
`the_asm (hd_is "heap_split")` is not enough when the proof has made
**two** splits of the same heap: pick by an argument --

```
the_asm (fun c -> is_eq c && hd_is "heap_split" (lhand c) &&
           el 0 (snd (strip_comb (lhand c))) = <the point>) gl
```

-- and likewise for the two `EVERY isDataElement` of two pieces, and
for the two conditions of `heap_gen_ok` that differ only in whether
the conclusion is negated.  A picker that takes the first match
silently builds the wrong instance, and what then fails is the
`ACCEPT_TAC` three steps later.

## 77. The word level: what a cell of the memory costs

Thirty-odd theorems of `data_to_word_memoryProof` are about the
memory as a separating conjunction, and HOL4 reads a cell out of one
with `SEP_R_TAC`.  The port needs **no** new infrastructure for
that: `ml/lib/set_sep.ml` already has `read_fun2set`
(`(one (a,x) * p) (fun2set (f,d)) ==> f a = x /\ a IN d`),
`write_fun2set` and `STAR_AC`.  What a proof needs beside them, and
what the block above `word_cmp_loop_thm` holds, is:

- `star_front`: `((p * one c) * f) s ==> (one c * (p * f)) s`, the
  rearrangement that `read_fun2set` asks for.  Its proof is
  `SUBGOAL_THEN <the star equation> (fun e -> REWRITE_TAC[e]) THENL
  [CONV_TAC (AC STAR_AC)]` -- and note the `THENL` takes **one**
  tactic, because rewriting with the equation closes the main goal.
- `word_list_SNOC`: the last cell of a `word_list`, which is where a
  loop over one starts (`word_list a (xs ++ [x]) = word_list a xs *
  one (a + n2w (LENGTH xs) * bytes_in_word,x)`).
- the three word equations of such a loop: the address of the last
  cell (`a + bw * n2w (n + 1) = (a + bw) + n2w n * bw`), the step
  back from it, and the counter (`n2w (n + 1) - n2w 1 = n2w n`).
  Each is `REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE` --
  `WORD_ADD` is the port's `n2w (x + y) = n2w x + n2w y`, and
  without it `WORD_RULE` cannot see that `n2w (n + 1)` is a sum.

Three things that cost a round each in the first such proof:

- **`lhand` is not the function of an application.**  For an
  assumption `(p * q) (fun2set (m,dm))`, the predicate is
  `rator c`, not `lhand c` (which is `q`).  Reading the address and
  the frame out of such an assumption with `lhand` builds the wrong
  instance, and what fails is the `ACCEPT_TAC` or the `SPECL` three
  steps later.
- **a picker's test must not raise.**  `the_asm (fun c -> hd_is ".."
  (rand c) && ..)` dies with `rand: Not a combination` as soon as
  one assumption is `true`; wrap the whole test in
  `try .. with Failure _ -> false`.
- **an equation between the two lengths is a rewrite in one
  direction only.**  `LENGTH y' = LENGTH y` rewrites the
  assumptions into the goal's shape; `LENGTH y = LENGTH y'` (its
  `SYM`) rewrites the goal away from it, and then the hypothesis of
  the induction no longer matches what the branch has.

## 78. The file binds names of HOL Light's own

`data_to_word_memoryProof.ml` has, at line 36808,

```
let is_cond t = is_forall t && is_eq(snd(strip_forall t));;
```

-- a helper of one of its proofs, and from there to the end of the
file `is_cond` is **that** and not HOL Light's test for a
conditional.  A proof written in a scratch session, where the
shadowing is not there, works; the same proof in the file dies with
`Exception: Failure "find_term"` twelve minutes into a verify, and
the report says nothing about why.

So a proof of this file does not use `is_cond`, and in general does
not use a one-word name of HOL Light's that a file of the port may
have taken for a helper of its own.  What a conditional is tested
by instead:

```
let a_cond t =
  try fst (dest_const (fst (strip_comb t))) = "COND"
  with Failure _ -> false in
```

and its condition is `el 0 (snd (strip_comb c))`.  `grep -n "^let
[a-z_]* [a-z]" <the file>` lists the helpers a file binds, and
`is_cond` is the only one of them that collides today.

## 79. The template of a `memory_rel_..._IMP`

Thirty of the theorems of `data_to_word_memoryProof` read a header
or a cell of the heap out of a `memory_rel`, and HOL4 proves each
of them the same way: `fs [memory_rel_def, word_ml_inv_def, ...]`,
then `imp_res_tac get_real_addr_get_addr`, then
`imp_res_tac heap_lookup_SPLIT`, then `fs [word_heap_APPEND,
word_heap_def, word_el_def, word_list_def]` and `SEP_R_TAC`.  The
port's `memory_rel_ValueArray_IMP` is that proof written out, and
it is the template; `memory_rel_Word64_IMP` is the same proof with
`Word64Rep` in place of the `RefBlock`.  The steps, in order:

- `MEMORY_REL_TAC THEN V_INV_TAC v_inv_def` -- the invariant and
  the rule of `v_inv` that the value has, which leaves the heap
  lookup at the pointer as an assumption;
- `EXISTS_TAC` of the pointer (`var_by_name "ptr"`), because what
  the statement says of it is the assumption `Word (get_addr c ptr
  ..) = v` the other way round;
- `heap_in_memory_store_def`, which gives `FLOOKUP st CurrHeap` and
  the bound on `heap_length`;
- `heap_lookup_SPLIT` on the lookup, which splits the heap into
  `ha ++ <the element> :: hb` and makes the pointer `heap_length
  ha`;
- `get_real_addr_get_addr` of those four, with the multiplication
  of the address swapped by `WORD_RULE` into the form the goal has,
  and `EXISTS_TAC` of it;
- `word_heap_APPEND`, `word_heap_def`, the definition of the
  element, `word_el_def`, `word_payload_def`, `word_list_def`, each
  followed by `TOP_DEPTH_CONV let_CONV` -- which leaves one
  separating conjunction of the cells of the element and a `cond`
  of what the header decodes to;
- the `cond` to the front (`sepfront ["cond"]`, which is
  `STAR_AC`), `cond_STAR`, and the facts of it assumed;
- and then every cell read with `read_fun2set`, each time with that
  cell rearranged to the front by `STAR_AC`:

  ```
  DISCH_THEN (fun sep ->
    let p = rator (concl sep) in
    let fs = facs p in
    let st = fst (strip_comb p) in
    let mk a b = mk_comb (mk_comb (st, a), b) in
    let front cell =
      let rest = filter (fun t -> not (t = cell)) fs in
      let target = mk cell (end_itlist mk rest) in
      let eq = prove (mk_eq (p, target), REWRITE_TAC[STAR_AC]) in
      MATCH_MP read_fun2set (REWRITE_RULE[eq] sep) in
    let rds = map front (filter (hd_is "set_sep_one") fs) in
    EXISTS_TAC (rand (rhs (concl (CONJUNCT1 (hd rds))))) THEN
    MAP_EVERY STRIP_ASSUME_TAC rds)
  ```

  (`facs` flattens a `STAR` into its factors, in the order they
  stand, so the first cell is the header.)

The bits of the header come off `make_header_def` with
`BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD`, `NUM_REDUCE_CONV` and the
assumption `len_size + 7 < dimindex`, which is what says that the
length of the header does not reach down to the bits the tag has.

## 80. A term quoted inside a proof and the record fields

The names of the record fields of the sources (`c`, `be`, `ts`,
`m`, `st`, `sp`, `dm`, `refs`, `vars`, ...) are overloaded onto the
accessors, which is why a statement that uses them for variables of
its own goes through `cake_as_vars`.  The same holds for a term
that a _tactic_ quotes: a `SUBGOAL_THEN` of a `memory_rel` with the
variables of the statement in it has to be written

```
SUBGOAL_THEN (cake_as_vars (fun () ->
  `memory_rel c be ts refs sp st m dm [(v1,(w1:'a word_loc))]`))
  ASSUME_TAC
```

Without the wrapper the quotation does not parse, and what comes
out is `Failure "typechecking error (overload resolution)"` -- at
the point where the thunk of the proof is evaluated, so the harness
reports it against whatever step it had reached, which is usually a
step of a lemma of the proof and has nothing to do with it.  A
quotation that names no field (a list of the proof's own variables,
an arithmetic statement) needs no wrapper.

## 81. HOL Light's precedences are not HOL4's

Two of them bite when a lemma of a proof is written to match a
goal:

- `EXP` is _left_ associative, so `d EXP d EXP d` is `(d EXP d) EXP
  d` and not `d EXP (d EXP d)`.  (`MustTerminate_limit` of the port
  therefore has the word size to the square of the word size in it,
  where the source has it to the word size to the word size.
  Either is "a number that's large enough", which is all the source
  asks of it.)
- `-` binds _tighter_ than `+`, so `a + b - c` is `a + (b - c)`.  A
  goal of the shape `(A + B + C) - D` is matched by a lemma whose
  statement has the parentheses written out.

`MATCH_MP_TAC` says `No match` when a lemma is written the other
way, and the term it shows looks the same as the goal.

## 82. `TL` of the port is `hol4_TL`

HOL4's `TL []` is `[]`, HOL Light's `TL` says nothing of the empty
list, so the port has `hol4_TL` (ml/lib/hol4.ml) with both clauses
and overloads `TL` onto it.  A `REWRITE_RULE[TL]` with HOL Light's
theorem therefore leaves the port's `TL (h :: t)` standing: the
rewrite to use is `hol4_TL`.  `MAP_TL` of the source (`MAP f (TL l)
= TL (MAP f l)`) is not in the port; where a proof needs the two
sides to meet, the list is split (`list_CASES` on it) and both are
rewritten with `APPEND; MAP; MAP_APPEND; hol4_TL`.

## 83. A quotation of a proof has type variables of its own

A statement that a tactic writes down (`SUBGOAL_THEN`, the term of
a local lemma) is parsed on its own, so a variable of it that the
quotation does not pin down gets a _fresh_ type -- and the variable
of the goal with the same name is then another variable.  Nothing
says so: `SUBGOAL_THEN` proves the statement that was asked for,
and the `MP` or the `ACCEPT_TAC` that was to use it says
`theorems do not agree` or `ACCEPT_TAC`, with the two terms
printing the same.

The heap of CakeML is where it bites, because the elements of the
port's `BlockRep`, `Bytes` and `ThunkBlock` have a type parameter
of their own (`BlockRep cons_tag [x; y]` is a
`('a word_loc,data_to_word_memoryProof_tag#(?)list)heap_element`,
with `?` free): a quotation about a heap therefore has to carry the
type

```
  (ha:(('a word_loc,data_to_word_memoryProof_tag#('a word_loc)
    list)heap_element) list)
```

on its first heap variable, or the term has to be built from the
goal (`W(fun (asl,gl) -> ... mk_icomb (`heap_length`, hp) ...)`),
which is what the proof of `heap_length_Blocks` does for the heap
it hands to the induction hypothesis.

## 84. Two assumptions that contradict each other cancel

`ASM_REWRITE_TAC[]` with `MEM x t` and `~(MEM x t)` among the
assumptions rewrites the one with the other and leaves the goal
standing (`T ==> ...` and `F ==> ...` both reduce, and which of
them it is depends on the order).  The contradiction has to be
taken by hand:

```
  FIRST_ASSUM (fun m -> USE_THEN "nm" (fun nm ->
    W(fun (asl,gl) -> ACCEPT_TAC (CONTR gl (MP (NOT_ELIM nm) m)))))
```

## 85. `ASM_ARITH_TAC` of the port hands over the arithmetic

The port's `ASM_ARITH_TAC` (ml/lib/tactics.ml) gives `ARITH_TAC`
the assumptions it reads as arithmetic, and an assumption about
`heap_length ha` or `el_length el` is not always one of them.  A
proof that needs such a fact states it:

```
  MP_TAC (MATCH_MP (ARITH_RULE
    `!a b c:num. a + b <= c ==> ~(c < a)`) le) THEN ...
```

and a side condition of a conditional rewrite has to have its
variables in the conclusion -- `SIMP_TAC` cannot use
`0 < b /\ a + b <= c ==> ~(c - a = 0)`, because `b` is nowhere in
`~(c - a = 0)`.

## 86. An assumption cannot be a rewrite across type variables

Entry 83 is about a quotation of a proof; the same fresh type of
the goal makes a _rule of the step_ unusable.  A statement of the
port that does not pin its heap down (the one of
`gc_heap_inline_rel_v_inv_lemma` does not) has a goal whose heap
type is a fresh variable, and the lemmas of the proof have `'a`.
A proved lemma is no trouble -- `MATCH_MP`, `MATCH_ACCEPT_TAC` and
`REWRITE_TAC` instantiate the type variables of a theorem -- but a
theorem that `CHOOSE_THEN` hands over has its own variables among
its _hypotheses_, so they are local constants of the match, and a
type variable in the type of one of them can no longer be
instantiated:

```
  (* `?l d. Bignum i = DataElement [] l d', then *)
  REWRITE_RULE[eq] hl   (* does nothing, and says nothing *)
```

because `d`'s type carries the `'a`.  What works is to prove the
step as a lemma of its own (`heap_lookup ptr heap1 = SOME (Bignum
i) ==> heap_lookup ptr heap2 = SOME (Bignum i)`, with the
existential used inside its proof) and to apply _that_ with
`MATCH_MP`.

The other way to lose a type: a quotation of an overloaded name
alone.  `` `FAPPLY (g:(num,num)fmap)` `` is the map's application,
but `mk_icomb (`FAPPLY`, g)` fails with `type_match`, because
`FAPPLY` on its own does not resolve to `fmap_apply`.  Write the
application in the quotation.

## 87. A hand-written comparison of integers is one of the reals

The port's `&`, `--`, `+`, `<` and `<=` are overloaded over the
numbers, the integers and the reals, and a quotation that pins
none of them down is read as a statement about the _reals_:

```
  is_cond `--(&n) < &0`      (* real_lt, not int_lt *)
```

so a step written like that does not touch what a definition of
the port says.  `Smallnum`'s own condition is `i < &0` with
`int_lt` in it, and the subgoal above neither reduces it nor can
be proved from `0 < n`.  Annotate one side -- `` `(--(&n):int) <
&0` `` -- or let a rule of the integers (`INT_ARITH`,
`INT_OF_NUM_LT`) build the term.

The same trap in the words: a statement whose two words are not
both pinned down,

```
  `!(a:word64) a' p n.
     word_subword a (p,n) = word_subword a' (p,n) ==> ...`
```

has `a'` of a word type of its own, because `word_subword` takes
any width to any width, and an `AP_TERM` of `w2n` over such an
equation then fails with `mk_comb: types do not agree`.  Write the
type of each variable the statement compares.

## 88. The names of HOL Light that this file rebinds

Entry 78 is the list of the names the _port_ rebinds; a file can
rebind one of its own, for the proofs after it.  In
data_to_word_memoryProof the `EXTRA_BEFORE` of `part_to_words_add`
binds `is_cond` to "a statement whose body is an equation", so
every proof after that point has to test for a conditional with
`hd_is "COND"` instead (the file says so where it uses the
rebound one).  A `Failure "tryfind"` out of a `grab_asm` whose
predicate looks right is what this looks like.

Two more of HOL Light's own that cost a round: `BIT_WORD_OR` has
the side condition `i < dimindex (:N)` in it, so rewriting with it
leaves a goal of that -- `BIT_WORD_OR_ALT` is the unconditional
one; and `INT_OF_NUM_EXISTS` is `(?n. x = &n) <=> &0 <= x`, so the
step from a bound to the number needs its `GSYM`.

## 89. A statement with a `let` loses it in an induction

The statement of `memory_rel_do_build` ends in

```
  ?m1. let nf = free + bytes_in_word * n2w (LENGTH ws) in
         memory_rel ... (st |+ (NextFree,Word nf)) m1 ... /\
         store_list free ws m dm = SOME m1
```

and `LIST_INDUCT_TAC` hands the proof an _induction hypothesis
with the `let` reduced_ while the goal keeps it.  A step of the
proof that is stated as a lemma with the hypothesis "the induction
hypothesis" (which is how a long induction keeps its cases apart)
therefore has to state that hypothesis **without** the `let` and
its own conclusion **with** it, or `MATCH_MP` says `No match` and
nothing says why.  Print the two and compare them whenever a match
of a hypothesis that reads the same fails.

And a trap of the harness, not of HOL Light: a case that is
dispatched with `FIRST [SOLVED <the real tactic>; CHEAT_TAC]`
reports `OK` when the real tactic fails, because the cheat closes
the goal.  While a case is being written, dispatch on something
that _fails_ for the other cases (here: the constructor that
`do_part` gives, by `grab_asm`), so that the failure of the case
under work is the failure of the proof.

## 90. The session's scratch layer is not the proof

A long induction is written in a session as two dozen top-level
helpers (`d_open`, `d_step`, `d_fin`, a lemma per case), and what
lands is _one_ term: the tactic of `prove`, with every helper a
`let ... in` of it.  Doing that by hand is where the round loses
its proof, so do it by machine:

- write the helpers into one flat file, in dependency order, with
  each `b_the (bp "x" `...` (fun () -> ...))` turned into a plain
  `prove`, and load that file: it is the proof, still with its own
  names at the top level;
- check that **every** name the file uses is either defined in it
  or stands before the proof in the port -- a name that is only in
  the session is the trap, because the session has it and a fresh
  load does not;
- then turn each top-level `;;` into ` in`, indent the whole by
  three and wrap it in the thunk that `tools/landproof.py` reads.

The check is not optional and a grep for the scratch vocabulary
(`say`, `mk`, `bp`, `b_the`) does not do it: of the helpers of
`memory_rel_do_build` one (`d_open`) was simply not copied into
the flat file, the session's own was used, and the only sign of it
was that the log of the run had the `MARK`s of the session's
version in it -- which the copy no longer has.  List the names,
`grep -c '^let <name> '` each one, and let the list be what says
the file is complete.

## 91. The alignment that HOL4 has and the port does not

`ml/lib/alignment.ml` has the four definitions of HOL4's
alignmentTheory (`align`, `aligned`, `byte_align`, `byte_aligned`)
and not one theorem of it, so a proof that works with the address
of a byte has to prove what it needs.  The two that HOL4 uses are

```
align_add_aligned: aligned p a /\ w2n b < 2 EXP p
                   ==> align p (a + b) = a
aligned_add_pow:   aligned k (w + n2w (n * 2 EXP k)) <=> aligned k w
```

and both come out of one reading of `align`: it is the word
shifted down by `p` and up again (`slice_shl`, which the proof of
`w2n_add_byte_align_lemma` already had), so the value of
`align p w` is `2 EXP p * (val w DIV 2 EXP p)` -- the value with
the lowest `p` bits cleared -- and `aligned p w` is exactly
`val w MOD 2 EXP p = 0`.  From there both are arithmetic over
`VAL_WORD_ADD` and `MOD_MOD_EXP_MIN`, where the one step that
needs care is that a multiple of `2 EXP p` below `2 EXP d` plus a
rest below `2 EXP p` does not wrap (`mult_bound`).

The proof of `heap_in_memory_store_UpdateByte` has all of this as
its own lemmas, with `gd_shift` (the bytes in a word are
`2 EXP LOG2 (dimindex (:'a) DIV 8)`), `heap_addr_aligned`,
`byte_align_add` and `heap_addr_mod` on top of them;
`memory_rel_ByteArray_IMP` and `memory_rel_xor_bytes` want the
same, and copying them is what the port does with a local lemma.

## 92. Four ways a rewrite or an ARITH goes wrong

- `ONCE_REWRITE_TAC[th]` is `ONCE_DEPTH_CONV`, which rewrites the
  topmost instance in **every** branch of the term, not the first
  one in the whole term.  With `th` an equation whose left side is
  a variable (`va = va DIV 2 EXP p * 2 EXP p`) that means every
  occurrence of the variable goes, including the ones inside the
  right side's own shape, and a step that closed the goal while
  there was one occurrence breaks when the goal grows another.
  Rewrite with an explicit path (`GEN_REWRITE_TAC (LAND_CONV o
  LAND_CONV) [th]`) or, better, do not rewrite with such an
  equation at all: `ABBREV_TAC` the quotient and `SUBST_ALL_TAC`
  the variable away.
- a product is **one atom** for `ARITH_TAC`: `LENGTH ys1 * bw` and
  `LENGTH ys1 * (dimindex (:'a) DIV 8)` are two atoms, and an
  assumption `bw = dimindex (:'a) DIV 8` does not bridge them.  A
  lemma whose hypothesis is such a product has to be stated in the
  multiplication order of the place that uses it, with no
  abbreviating variable in between.
- an `ARITH_RULE` whose term holds no numeral gets the default
  type of `<=`, which in the port is not `num`:
  `ARITH_RULE `a <= b ==> n < a ==> n < b`` fails with
  "linear_ineqs: no contradiction" until it says `(a:num)`.
- `btry` gives `TRUTH` when the attempt fails, so a try file that
  takes its statement from `concl <name>` **poisons the session**:
  the next load states `true`, proves it, and the error it reports
  is about a goal that is not the theorem.  After a failed run,
  put the statement back (`mk_thm ([], <the statement>)`) before
  the next one -- or read the failure of a second run with that in
  mind.

## 93. What a proof over the invariant has to keep, and three traps

`MEMORY_REL_TAC` unfolds memory_rel, word_ml_inv, abs_ml_inv and
bc_stack_ref_inv in one go and strips what comes out, which is
what most proofs of data_to_word_memoryProof want.  A proof that
has to **use** one of those folded facts again cannot have it
unfolded:

- `memory_rel_ByteArray_IMP` wants `update_byte_ref_thm`, whose
  hypothesis is an `abs_ml_inv`, so its opening unfolds only
  memory_rel and word_ml_inv, applies that theorem (with the array
  that is written left open -- `DISCH` the two hypotheses it can
  have now and `GEN` the third), and only then unfolds abs_ml_inv
  and bc_stack_ref_inv by hand;
- and it wants `heap_in_memory_store_UpdateByte`, whose hypothesis
  is the folded `heap_in_memory_store`, so the step that unfolds
  that one uses `FIRST_ASSUM`, not `FIRST_X_ASSUM`, and both the
  folded fact and its pieces stay.

Two splits of one heap then come out of two theorems (bc_ref_inv's
`heap_lookup_SPLIT` and update_byte_ref_thm's own), and they are
at one and the same address because the root of the reference
points at both: the equation of the roots gives
`heap_length ha = heap_length h1` through `CONS_11` and the
injectivity of `heap_address`, and that is all the identification
the proof needs -- HOL4 proves `h1 = ha` with `APPEND_EQ_APPEND`
and the port does not have to.

Three traps of the round:

- `MATCH_MP` moves a theorem's **quantified** variables that the
  antecedent does not determine inside the conclusion, but a
  **free** variable of the theorem stays free and uninstantiated.
  A lemma `good_dimindex (:'a) /\ ... ==> ~word_bit 3
  (make_byte_header c fl len)` whose hypotheses say nothing about
  `len` therefore comes back about `len`, and rewriting with it
  does nothing: `INST` the variable from the goal first.
- `ASM_SIMP_TAC` and `SIMP_TAC` simplify the branches of a
  conditional with its condition as context, so a goal that was
  `if dimindex (:'a) = 32 then A else B` comes back with `A` and
  `B` already specialised to the two word sizes.  A lemma that
  states the generic form then needs `COND_CASES_TAC THEN
  ASM_REWRITE_TAC[]` to meet it, not `ACCEPT_TAC`.
- `hd_is` tests the **real** constant name, and the port's
  interface hides two of the ones these proofs grab for:
  `word_bit` is HOL Light's `bit` and `word_list` is
  `misc_word_list`.  A `grab_asm` or a `find_term` that looks for
  the printed name finds nothing.

## 94. A rule over the assumptions may not use an assumption

`RULE_ASSUM_TAC` (and the port's `RULE_ASSUM_TRY`) throws the
assumptions away and assumes what the rule gives back:

```
let RULE_ASSUM_TAC rule (asl,w) =
  (POP_ASSUM_LIST (K ALL_TAC) THEN
   MAP_EVERY (fun th -> ASSUME_TAC (rule th)) (rev asl)) (asl,w);;
```

So a rule that rewrites with a theorem **derived from an
assumption** -- `MATCH_MP lemma (the memory_rel assumption)`, say --
hands back theorems whose hypotheses include that assumption,
which is no longer in the list: the tactic is then *invalid*, and
nothing says so until the end.  Interactively `e` reports
`VALID: Invalid tactic`; inside `prove` the failure comes much
later and reads like something else entirely (`CHOOSE`, with a
goal that has nothing to do with the step).

What to do instead: put the derived theorem into the goal, not
into the assumptions.  `MP_TAC (REWRITE_RULE[derived] assumption)`
keeps the hypotheses where they belong and leaves the goal
`<the rewritten assumption> ==> <the goal>`, which is valid
because the theorem's hypotheses are still assumptions of the
goal.  Rewrite the assumptions with a plain theorem (one with no
hypotheses) and nothing else.

## 95. `INST` rewrites the hypotheses with the rest

`MATCH_MP lemma assumption` gives a theorem whose *hypothesis* is
that assumption, and a hypothesis is a term like any other: an
`INST` on the theorem instantiates the variables of it too.  When
the variable instantiated is one the hypothesis mentions -- and
the names collide easily, because a lemma about a word calls it
`w` and so does the statement -- what comes back is a theorem
whose hypothesis is *not* an assumption of the goal:

```
let lsz = CONJUNCT1 (MATCH_MP mr_len_size mr) in
  (* memory_rel c be ts refs sp st m dm
       ((RefPtr bl i,Word w) :: vars)
     |- data_to_word_config_len_size c + 7 < dimindex (:'a) *)
let dlb = INST [x', `w:'a word`]
            (MATCH_MP decode_length_bound lsz) in
  (* memory_rel c be ts refs sp st m dm
       ((RefPtr bl i,Word x') :: vars) |- ... *)
```

The step goes through and the proof still closes; what fails is
the end of `prove`, with the `CHOOSE` of entry 94, because the
stray hypothesis mentions a variable that `STRIP_ASSUME_TAC`
chose.  Quantify the lemma over what the use site has to fix
(`... ==> !w. ...`) and use `SPEC`, which instantiates the bound
variable and leaves the hypotheses alone.  `SPEC`, `SPECL`,
`ISPEC` and the *minor* premise of `MATCH_MP` are all safe;
`INST` and `INST_TYPE` on a theorem with hypotheses are not.

## 95a. The diagnostics have to come out

A proof that a script assembles out of the files of its
development carries the prints that the development needed
(`ppf`, `mrk`, a `say` of a goal).  They are not defined where
the port loads, so one that is left behind costs a whole verify
to find: the file dies with `Error: Unbound value ppf` and the
twelve minutes with it.  The script that assembles the proof
strips them, and `grep -n 'ppf\|say \|mrk ' <the try file>` is
what says it worked -- before the landing, not after.

## 96. A conditional whose branches are booleans

`COND_CASES_TAC` splits a goal that holds a conditional into the
two cases of its condition -- unless the conditional is a
*boolean* one.  The statement of `memory_rel_Number_cmp` ends in

```
else if word_bit 0 w1 /\ word_bit 0 w2 then (...) else T
```

and on that goal `COND_CASES_TAC` does not leave two goals, so a
`THENL` of two tactics after it fails with `seqapply: Length
mismatch`, which says nothing about where the trouble is.  The
split by hand does work:

```
W(fun (asl,gl) -> ASM_CASES_TAC (fst (dest_cond gl))) THENL
 [FIRST_ASSUM (fun cc -> REWRITE_TAC[cc]) THEN ...;
  FIRST_ASSUM (fun cc -> REWRITE_TAC[cc])]
```

The rewrite that collapses the conditional has to **name the case
assumption**: `ASM_REWRITE_TAC[]` is not enough, because another
assumption may have the condition as its left-hand side (here
`word_bit 0 w1 <=> ~small_int (:'a) i1`), and then the condition
is rewritten into that instead of into `T`.  While on the
subject: `lhand` of a conditional is its *then* branch, so the
condition is `fst (dest_cond t)` and nothing else.

## 97. What a `W` sees

`W(fun (asl,gl) -> ...)` runs its function when the tactic it
builds is applied, so the assumptions it reads are the ones of
that moment.  A `W` whose body is a chain that splits cases
builds the whole chain out of the assumptions of *before* the
split:

```
W(fun (asl,gl) ->
  COND_CASES_TAC THEN
  MAP_EVERY MP_TAC (int_facts asl) THEN INT_ARITH_TAC)
```

never sees what `COND_CASES_TAC` assumed, and the arithmetic is
one fact short.  The facts of a step belong in a `W` of their
own, after it:

```
COND_CASES_TAC THEN
W(fun (asl,gl) -> MAP_EVERY MP_TAC (int_facts asl)) THEN
INT_ARITH_TAC
```

## 98. The name a term is printed with is not its constant

`hd_is` tests the *constant's* name, and three of the names this
file prints are not constant names at all:

| printed      | constant       |
|--------------|----------------|
| `EVERY2`     | `ALL2`         |
| `FAPPLY f x` | `fmap_apply`   |
| `LIST_REL`   | `ALL2`         |

So `hd_is "EVERY2" gl` is false of every goal, and a dispatch
over the parts of an invariant that asks it takes the wrong arm
without a word (the `tryfind` of a `FIRST_ASSUM` at the end of
the chain is all that is seen).  `fst (dest_const (fst (strip_comb
t)))` in the REPL settles what the name is.

The same for a term that is *built*: `` mk_icomb (`FAPPLY`, fm) ``
fails with `type_match`, because a bare `` `FAPPLY` `` is a
constant of another theory (`:'a word -> num -> bool`) and not
the map application at all.  What builds it is
`list_mk_icomb "fmap_apply" [fm; x]`.  `` `FDOM` `` is a constant
of its own name and does work that way.

## 99. Four ways an instantiation of a lemma fails

A proof of this file hands a lemma its hypotheses as a theorem
and takes the conclusion; four things go wrong there, and each
has its own error:

- `Failure "SPEC"` / `"SPECL"`: the lemma's type variables are
  not the goal's.  `SPEC` and `SPECL` do not instantiate a type,
  so a lemma of the file (whose word type is a variable of the
  file) needs `ISPEC` or `ISPECL`.  `ISPECL` reports the failure
  of its own `SPECL`, so the message names `SPECL` either way.
- `Failure "MATCH_MP: No match"` where the two terms *print* the
  same: a type variable that the lemma does not pin down.  Here
  `list_to_BlockReps` has the type `... -> (('a word_loc,tag#'b
  list)heap_element)list`, with `'b` free, so an `ISPECL` of
  `bind_each_isSomeDataElement` leaves `'b` uninstantiated and
  the term it builds has two incompatible element types in it.
  `INST_TYPE (type_match (type_of <the blocks of the instance>)
  (type_of <the blocks of the goal>) [])` puts it right; printing
  with `print_types_of_subterms := 2` is what shows it.
- a `MATCH_MP` whose result is a `!`: `MATCH_MP th1 th2` moves
  the variables of `th1` that its *hypothesis* does not mention
  into the conclusion as `!`s, so `MATCH_MP bind_each_SUBMAP lim`
  is `|- !n k i. tf SUBMAP bind_each tf ts k i n` and does not
  fit the `tf SUBMAP tf1` of `v_inv_SUBMAP`.  `SPEC_ALL` of it
  does, and `MATCH_ACCEPT_TAC` then reads `k`, `i` and `n` off
  the goal.
- a `MATCH_MP_TAC` whose goal is a `?`: the mirror image.  A
  lemma whose hypothesis names what its conclusion does not
  (`unused_nodata_k`, with the start of the space as a variable
  `k`) leaves `?k. ...`, and the step after it is `EXISTS_TAC`.

## 100. A diagnostic run prints the goal, not a cut of it

The harness cuts a goal to one line, which is unreadable for a
goal of this size, and prints every type.  One run of the attempt
with

```
W(fun (asl,gl) ->
  let pt = !print_types_of_subterms in
  print_types_of_subterms := 0;
  say ("\nBL ------\n" ^ string_of_term gl ^ "\n");
  print_types_of_subterms := pt;
  ALL_TAC)
```

in the place of the diagnostic, and a second with the same over
`asl`, gives the goal and its thirty-odd assumptions as a reader
sees them, and after that every grab in the proof can be written
from the text instead of guessed at.  (`let o = ...` does not
parse: `o` is an infix of HOL Light.)

## 101. A binding of the right name and the wrong theorem

`REWRITE_TAC[dest_thunk_def]` is a no-op, and nothing says so: the
name is bound (to a theorem of another theory), the rewrite makes
no change, and `REWRITE_TAC` of a list that changes nothing else
*fails*, so a `TRY` around it swallows the step without a word.
What this file's definition is called is
`dataSem_dest_thunk_def`, and the port's own proofs say so:

```
grep -n 'dest_thunk' ml/compiler/backend/proofs/*.ml | grep REWRITE
```

finds `ONCE_REWRITE_TAC[dataSem_dest_thunk_def]` in three of them.
Before using `foo_def` of a definition of this file, check that the
name is the one the file binds; the printed name of the constant
(entry 98) is not it either.

A definition with a `match` wants `ONCE_REWRITE_TAC` and then
`SAFE_MATCH_REDUCE_TAC`, and the scrutinee has to be in constructor
shape *first*: the branch of a `match` binds its own variables, so
a rewrite with `lookup n refs = SOME (Thunk ev v)` does not reach
the `lookup n refs` inside the branch of an unreduced match.  What
is left after the reduction is a chain of `if`s over
`NONE = SOME ...` and `?v'. SOME (C v') = SOME (C v)`, which
`distinctness`, `injectivity` and `EXISTS_REFL` finish.

## 102. A case split that the goal does not mention

`CASES_ON_TAC` and `NAMED_CASES_TAC` use `SUBST_ALL_TAC`, which
fails with `SUBS_CONV` when the variable does not occur in the
goal.  That is the usual case in a proof of the memory invariant:
the value is in the assumptions and the goal is about the memory.
A local copy of `NAMED_CASES_TAC` whose `use` is

```
let use eq = RULE_ASSUM_TAC (REWRITE_RULE[eq]) THEN
             TRY (SUBST1_TAC eq) in
```

splits it there.  The order of the names is the order of the
constructors in `cases_of` (for `heap_address` that is `Pointer`
then `Data`, for `word_loc` `Word` then `Loc`), and a wrong order
shows up as `Failure "dest_binder"`.

## 103. The lets of word_el, and what MESON must not be given

`word_el a (DataElement ys l (tag,qs)) conf` is a `let (h,ts,c) =
word_payload ... in ...`, a let of *three* variables.  The port's
`PAIRARG_TAC` takes a pair, so on that let it introduces two
variables for three and leaves the let stuck; the way through is
the one the landed proofs use: rewrite `word_payload_def` first,
which makes the bound term a literal triple, and only then
`let_CONV`.  `PAIRARG_TAC` is for the pair of a definition's own
let (`let (sign,payload) = i2mw i in ...` of a bignum), and that
one comes before `word_el_def`.

In the same proofs, `ASM_MESON_TAC[]` over the assumptions of a
memory invariant is a hang, and a plain `MESON_TAC[...; MEM]` is
another: with the clauses of `MEM` in the list and a heap of the
shape `ha ++ x :: hb` in the goal, MESON unfolds the list for as
long as it is allowed to.  Both are to be replaced by the facts
the step needs, two or three of them, named by `grab_asm`.

## 104. A termination that is only short of time

`word_eq`'s cheat was not a missing proof: the fact that HOL4's
`Termination` uses (`imp_res_tac fix_clock_IMP`) is the port's own
`data_to_word_memoryProof_fix_clock_IMP`, and with it among
`cake_term_facts` -- which is how the semantics files register
theirs -- `TERM_TAC` discharges every condition of the measure
that HOL4 gives.  Two things had to be put right at once:

- the fact has to be *pushed*: `cake_term_facts := <the fact> ::
  (!cake_term_facts)` before the definition, which `EXTRA_BEFORE`
  of `tools/overrides.py` writes into the file.  Nothing registers
  a file's own fix_clock_IMP by itself.
- the attempt has a **budget of eight seconds**
  (`cake_cheat_budget`, `with_short_budget`), and this one takes
  four in a warm session and more in the session of a run, so the
  cheat was taken for want of time.  `cake_cheat_budget := 120`
  before the definition and `:= 8` after it (`EXTRA_BEFORE` and
  `EXTRA_AFTER`) is what the file does about it.

So a `cake_define ... CHEATED` line says nothing about whether the
termination is hard.  What tells is `tools/bin/trydef`, with
`S=<session>` to use a session that already holds the file:

```
S=s2 trydef word_eq
```

It makes the definition again with the constants renamed, and the
why column is empty when nothing was cheated.  Two traps: the
renaming turns every *other* head of a clause into a free variable
(`isClos` becomes `isClos_zz`, which is a variable, and the
definition is cheated for that alone), and a second attempt in the
same session fails with `dest_var: not a variable`, because the
first one has declared the renamed constant.  Both are dealt with
by hand: put the names back, and change the suffix for each try.

## 105. A statement about word_heap ties no types

`word_heap` takes an address and a heap of elements, and the two
have type variables of their own: nothing in
`(word_heap curr heap c * frame) (fun2set (m,dm))` says that the
address is of the same word type as the cells of the heap.  A
statement written without annotations is then more general than
it looks, and a `MATCH_MP` of a lemma of the file against it
fails with `type_match`, which says nothing about what did not
match.  So a statement of the port's own about the memory pins
the type by hand:

```
`(word_heap (curr:'a word) (h1 ++ [Bytes be fl2 vals2
    (make_zeros vals2:('a word) list)] ++ h2) c * frame)
  (fun2set (m:'a word->'a word_loc,dm:'a word->bool)) /\ ...`
```

Every place that carries the type variable is annotated once: the
address, the zeros of each array (which is what fixes the element
type), the memory and its domain, and the word that a
`decode_length` gives.  The check is to print `type_of` of the
two sides of the match and look for a `?` in either.

## 106. A rewrite whose left side is a variable does nothing

To put `x` back where a theorem has `make_byte_header c fl1
(LENGTH vals1)`, `REWRITE_TAC[GSYM hdr]` with `hdr :
make_byte_header c fl1 (LENGTH vals1) = x` is no help: the rule's
left side is a variable, so the rewriter drops it -- silently,
because the tactic succeeds and the goal stands.  What works is
to rewrite the theorem with `hdr` and accept that:

```
let nm2 = REWRITE_RULE[hdr] nm in ... ACCEPT_TAC nm2
```

And in a proof about two arrays every `grab_asm` that picks "the"
fact of a shape picks the first of two: the header of the other
array, the length bound of the other array, the `decode_length`
of the other array.  Each of those cost a round of its own.  The
picker has to say which of the two it wants -- `rhs (concl th) =
rand (el 2 gas)` for the header that the goal's length is made
of, or `free_in len1 (concl th)` for the bound of the first
array.

## 107. The same heap, decomposed twice

A proof that writes an array decomposes the memory of the heap
twice: as the heap is, and with the new bytes in it.  The factors
of the two have to come out the same, and three things stand in
the way:

- the address that `word_heap_def` gives the rest of the heap has
  `el_length x` in it, and `bytes_def` has already turned that
  element into a `DataElement` that holds the *bytes*, so the
  addresses after the array are not the same term in the two.
  `el_length_def` in the rewrite list is what makes them one
  (`LENGTH (make_zeros vals) + 1`, which the bytes do not enter).
- the header of a byte array is `make_byte_header c fl (LENGTH
  bs)`, so the new one says `LENGTH res_vals`; rewriting the goal
  with `LENGTH res_vals = LENGTH vals2` (`xor_bytes_length`)
  takes it back to the old one.
- the `cond` factors of `word_el` sit in the frame of the lemma
  that writes the memory, and are out of the frame of the goal,
  where `cond_STAR` has pulled them out as facts.  So the goal is
  accepted not with the lemma's result but with that result with
  its own conds pulled out the same way.

A factor is picked out of a separating conjunction by what its
*list* argument holds (`free_in vals1 (rand t)`), never by what
the whole factor holds: the address of the second array has the
first array's `el_length` in it, so `free_in vals1 t` picks both
and the reordering it asks for cannot be proved.


## 108. The case tree of a definition, as lemmas

`word_eq`'s body is a tree of nine conditions over the headers of
two values, and `word_eq_thm0` has to go down it in each of the
four cases of two values and again in the case of two lists.
Reducing the tree in the goal costs that work four times over and
leaves a goal that no longer says `word_eq`, so five lemmas of the
proof's own say what the comparison gives at each leaf instead:

- `word_eq_refl`: of a root with itself it is one;
- `word_eq_zero`: of two roots that are not one word and whose
  headers say that the two values differ, zero;
- `word_eq_clos`: of two closures, one;
- `word_eq_block`: of two blocks of one header, the comparison of
  the values that they hold;
- `word_eq_loop`: of two values that are compared by their
  contents, the loop over the two payloads.

Each one is `ONCE_REWRITE_TAC[word_eq_def] THEN ASM_REWRITE_TAC[]
THEN TRY SAFE_MATCH_REDUCE_TAC THEN ASM_REWRITE_TAC[]` over a
dozen lines of hypotheses.  A leaf of the main proof then reads

```
MP_TAC (INST [...] (PART_MATCH (fun t -> lhs (snd (dest_imp t)))
                      word_eq_loop (lhs geq))) THEN
ANTS_TAC THENL
 [REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN ...;
  DISCH_THEN (fun th -> REWRITE_TAC[th] THEN ...)]
```

-- `PART_MATCH` of the lemma's own conclusion against the goal's
`word_eq` term fixes every variable of the statement, `INST` fixes
the four that only its hypotheses mention (the two addresses and
the two headers), and what is left per leaf is the semantics:
which value the memory holds, and not the tree.

## 109. A runaway tactic costs the session, not the round

A `MESON_TAC` over the assumptions of a goal of the memory
invariant, on a goal that is not provable (the statement's `n2w 1`
had become `n2w n`, because an assumption `1 = n` was used as a
rewrite left to right), took the heap of the development session
from 1.2 GB to 6.4 GB in ten minutes, filled the swap, and the
kernel killed the session.  `repl-int <session>` stops the tactic
but not the heap: `Gc.compact ()` cannot finish while the swap is
full.  What it cost was the session -- 36 minutes of closure
(`tools/bin/pfbase`) and 14 of file (`tools/bin/trybase`).

Three things follow:

- an assumption `<numeral> = <variable>` is oriented before
  anything rewrites with it: the reduction of a `match` of the
  source leaves `1 = n` and `a = a' <=> b`, and the first of them
  as a rewrite rule puts `n` where the statement says one.  A
  `SUBST_ALL_TAC (SYM th)` over the assumptions whose right side
  is a variable settles both.
- a leaf of a case split is closed with `ASM_REWRITE_TAC[...] THEN
  CONV_TAC TAUT`, not with `MESON_TAC` (entry 103 says the same of
  the lists of a heap).
- a round that takes longer than it should is watched with `top
  -bn1 | grep ocaml`: an RSS that grows past 2 GB is a runaway,
  and the interrupt has to come before the swap fills.

## 110. Five traps of a leaf lemma of a case tree

Entry 108 says what the leaf lemmas of `word_eq`'s tree are.  Each
of the five cost a round of its own, and for five different
reasons:

- **a quotation with no numeral in it is not `num`.**  In a session
  that has the whole port loaded `<` and `<=` are overloaded, so

  ```
  ARITH_RULE `n < l ==> ((l <= n) <=> F)`
  ```

  is read at another type and fails with ``REAL_ARITH `~(n < l /\
  l <= n)`: linear_ineqs: no contradiction``.  One numeral in the
  quotation settles the type of everything in it (`1 <= n <=> ~(n
  = 0)` is read as `num` and goes through), and a statement of
  variables only needs `(n:num)` written out.  The same holds for
  a `!p d l l0.` of an arithmetic lemma: `!(p:num) d l l0.`
- **`ONCE_REWRITE_TAC[<def>]` unfolds the other side as well.**  A
  leaf lemma whose right side names the function again (`word_eq
  ... = word_eq_list ...`) is unfolded on both sides and the two
  do not meet; `GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
  [<def>]` unfolds the left side only.
- **a fact of the first header is not a fact of the second.**  The
  lemma assumes `h1 = h2`, `ASM_REWRITE_TAC` puts `h2` in the goal
  with it, and the test `h2 && n2w 12 = n2w 0` is then settled by
  an assumption that still says `h1`.  `REPEAT SUBST_LHS_TAC`
  before the unfolding makes the assumptions say `h2` too.
- **`COND_ID` is not a basic rewrite.**  Where the facts of the
  leaf do not settle a test of the tree but both of its branches
  give the same answer, the goal is `(if b then x else x) = x` and
  `ASM_REWRITE_TAC[]` leaves it; `ASM_REWRITE_TAC[COND_ID]` closes
  it.
- **`fix_clock` has to be read before the call it wraps is.**  The
  body of `word_eq_list` has `fix_clock (ck - 1) (l - 1) (word_eq
  ... )`, and `fix_clock_word_eq` matches that only while the
  `word_eq` is still there: an `ASM_REWRITE_TAC` that replaces the
  call by its value first leaves a `fix_clock` of a `SOME` that
  the match cannot reduce, and `MATCH_REDUCE_TAC` turns the goal
  into a choice term (`@GEN%PVAR%`).  So the rewrite with
  `fix_clock_word_eq` comes immediately after the unfolding.

## 111. Six traps of a hand written tactic

The proof of `word_eq_thm0` is a thousand lines of tactic that
reads the goal and the assumptions, and six of its rounds went on
one of these:

- **`a + b - c` is `a + (b - c)`.**  HOL Light's `-` binds tighter
  than its `+`, where HOL4's two bind equally and associate to the
  left.  So

  ```
  WORD_RULE `x + bytes_in_word * n2w 2 - bytes_in_word =
             x + bytes_in_word`
  ```

  is a true statement about `x + (bytes_in_word * n2w 2 -
  bytes_in_word)`, its left side is not the term that the goal
  has, and a rewrite with it does nothing at all.  The
  parentheses are written out.
- **a theorem of `WORD_RULE` is not generalised.**  It keeps `x`
  free, so as a rewrite it matches that one variable and not the
  goal's other address; `GEN_ALL` is what makes it a rule about
  both.
- **the name of a constant is not the name it prints.**  `n2w` is
  `word`, `w2n` is `val`, `word_bit` is `bit`, `>>>` is
  `word_ushr`, `lookup` of a sptree is `sptree_lookup`, and
  `isClos` of a dataSem value is `dataSem_isClos` and not
  `bvlSem_isClos`.  A `hd_is` with the printed name picks nothing
  and says nothing, and the `mapfilter` over the assumptions that
  it guards then rewrites with the empty list.
- **a fact rewritten with itself is `T`.**  `RULE_ASSUM_TRY
  (REWRITE_RULE bits)` where `bits` are assumptions of the goal
  turns each of them into `true` and loses it.  The rule has to
  skip the facts it rewrites with (`use_facts` of that proof).
- **`FIRST [tryfind ...; tryfind ...]` raises.**  The list is
  evaluated before `FIRST` sees it, so the first `tryfind` that
  finds nothing takes the whole tactic with it.  Two steps where
  one is the fallback of the other are `try ... with Failure _ ->
  ...` and not `FIRST`.
- **a `prove` inside a tactic may not use an assumption.**  `prove
  (tm, ... ACCEPT_TAC th)` with `th` from the assumption list
  fails with "prove: additional assumptions in result"; what is
  wanted is `MP (prove (mk_imp (concl th,tm), ...)) th`.

## 112. Nine traps of the last two leaves

The last rounds of `word_eq_thm0` went on the two leaves that
were left -- two bignums of one header, and two references of a
kind that is not compared by its contents -- and each of these
cost one of them:

- **a `let` that binds a pair to a conditional does not reduce.**
  What `memory_rel_Number_cmp` says of two bignums of one header
  is

  ```
  let (a1,a2) = (if (x1 && (n2w 16)) = (n2w 0) then (a1,a2)
                 else (a2,a1)) in
    word_cmp_loop (decode_length c x1) (a1 + ...) (a2 + ...) dm m
      = SOME (word_cmp_res i1 i2)
  ```

  and `let_CONV` (so the `TOP_DEPTH_CONV let_CONV` of a
  `RULE_ASSUM_TRY`) cannot take it: the paired beta reduction
  wants a pair, and what stands there is a conditional.  The fact
  goes into the goal (`MP_TAC`), `COND_CASES_TAC` leaves a pair in
  each branch, the reduction takes it, and `DISCH_TAC` puts the
  fact back.
- **`CONTR_TAC` wants `F`, not two assumptions that clash.**  That
  case analysis leaves a branch against a test that the facts have
  settled, so `x1 && (n2w 16) = n2w 0` and its negation stand side
  by side -- and `FIRST_ASSUM CONTR_TAC` does nothing there,
  because `CONTR` asks for a theorem whose conclusion is `F`.  The
  closer is `FIRST_ASSUM (fun n -> FIRST_ASSUM (fun p -> CONTR_TAC
  (MP (NOT_ELIM n) p)))`.
- **and the two may clash only after the substitutions.**  The
  test of the conditional was about the second header and the fact
  about the first, so the clash appears when `REPEAT
  SUBST_LHS_TAC` has made the two headers one word.  A closer that
  stands before the substitutions is applied to a branch that is
  not contradictory yet, and says nothing.
- **a leaf lemma carries what the closer rewrites with.**  The
  kinds a `RefPtr T` can hold gave `~(word_bit 2 x) \/ ~(word_bit
  3 x) /\ word_bit 4 x`, which is what the disjunct of
  `word_eq_zero` asks for -- and the same disjunct asks for
  `~((x && (n2w 12)) = n2w 0)`, which `bit_pattern_1100` turns
  into `~(~(word_bit 2 x) /\ ~(word_bit 3 x))`: that needs the bit
  that is *set*, which the lemma had dropped.  So the lemma says
  `word_bit 3 x /\ ~(word_bit 2 x) \/ word_bit 2 x /\ ~(word_bit 3
  x) /\ word_bit 4 x`.
- **`BOOL_CASES_TAC` substitutes in the goal.**  The flag of a
  `ByteArray` that the case analysis of the kinds introduces
  occurs in the assumptions only, so the case analysis on it gives
  two branches that are the same and the proof does the work twice
  (and still reads the flag as a variable).  What the branch
  needed was the fact itself: `~(?bs. ByteArray T bs = ByteArray b
  bs')` is `~b` after `injectivity "bvlSem_ref"` and `(?z. p /\ z
  = a) <=> p`.
- **the budget of a loop is the word count, not a length that a
  fact names.**  `dlen_tac` and `cmp_arith` read the length out of
  a `decode_length c x = n2w k` fact, which every boxed value of
  the invariant has -- except a byte array, whose
  `memory_rel_ByteArray_IMP` gives the header as
  `make_byte_header c fl (LENGTH bs) = x` and no `decode_length`
  equation at all.  What the two goals of the loop (`w2n
  (decode_length c x) < l` and `l <= l - 1 - w2n (decode_length c
  x) + n * dimword (:'a)`) ask for is `VAL_BOUND` instead: a word
  counts no further than `dimword (:'a)`, and the budget of the
  statement is above that, so
  `ASSUME_TAC (REWRITE_RULE[GSYM dimword] (ISPEC dl VAL_BOUND))`
  and `ARITH_ASM_TAC` close both.
- **`SPEC` does not instantiate types.**  `SPEC `decode_length c
  x` VAL_BOUND` fails with `Failure "SPEC"`, because the bound
  variable of `!w. w2n w < 2 EXP dimindex (:N)` stands at the type
  variable of the library and `SPEC` asks for a term of that same
  type; `ISPEC` matches the types first.  And a step that fails
  inside a `TRY (SOLVED ...)` says nothing at all -- the leaf is
  skipped, the round reports the goal that is left, and the
  failure is found by running the step on that goal by hand.
- **a leaf accepts the orientation that the goal has.**  The case
  analysis on the two headers leaves `~(x' = x)` and the disjunct
  of `word_eq_zero` asks for `~(x = x')`, which `FIRST_ASSUM
  ACCEPT_TAC` does not see.  Before a leaf, both orientations of
  every inequality of the assumptions go in
  (`ONCE_REWRITE_RULE[EQ_SYM_EQ]` of each).
- **`grab_asm` picks the first of two facts of one shape.**
  `memory_rel_RefPtr_IMP_lemma` adds `sptree_lookup p refs = SOME
  res` and the case analysis of the kinds adds `sptree_lookup p
  refs = SOME (ByteArray b bs)`: a search for "the lookup of this
  pointer" finds the first of them, and the lemma that wanted the
  kind gets the variable.  The search is tied to the fact that is
  unique in the branch instead -- here the negation that the arm
  of `vb_eq_size` left, `~(?bs. ByteArray T bs = r)`, whose `r`
  says which lookup is meant.

What the whole thing costs is four minutes of every load of
`data_to_word_memoryProof`: about two and a half of them the
sixty lemmas above the tactic (the `MESON`s of
`word_cmp_loop_bytes` and of `mw_cmp_NONE` are the slow ones) and
the rest the case tree.  A proof of this size has no cheaper
shape -- the alternative is sixty `prove`s at the top of the file
instead of sixty `let`s inside the section, which costs the same
-- so the timing stands in the comment of the section, as entry
109 asks.

And the landing of a section of this size has a bracket of its
own to get right: `tools/mkland.py` strips `\)*;;` from the end
of the attempt and writes `));;` back, and
`tools/landproof.py` takes the text up to the first `);;` and
wraps it in `( )`.  That comes out balanced only when the
attempt's tactic stands in brackets of its own,

```
let _ = bp "nm" stmt (fun () ->
  (<the tactic>));;
```

and without them the section is one `)` over, which
`tools/parens.py` says as `-1 round bracket(s)` and a verify
would say twelve minutes later.

The other one is the order of the helpers inside the section.
`memory_rel_len_size` was proved in the lemma file of an earlier
round, so it stood at the top level of the scratch session, and in
the development file its own `let` came four hundred lines after
the first use of it -- the file loaded all the same, round after
round.  What said so was the verify, fourteen minutes in:

```
Error: Unbound value memory_rel_len_size
```

and the load of the file stopped there (so `AXIOMS-ADDED` came out
as 1, not as the 2 that the state before it had).  The check for
it is `tools/secorder.py`, which costs a second: every outer
`let` of every section against the first line that names it,
comments and quotations taken out.  `tools/scope.py` is the same
check *between* the sections of a file and does not look inside
one, and a session that has been given six scratch files cannot
say which of their bindings the section itself has.
