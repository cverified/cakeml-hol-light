# The `case` idiom, and what it costs the port

_Why the eight proofs that are left in `bvi_letProof` are stuck,
what HOL4's `every_case_tac` actually does, and what the HOL Light
counterpart has to be.  Written to be read before the machinery is
built, because the machinery is the gate of phase three: the 228
CakeML sources use `every_case_tac`, `CaseEq`, `AllCaseEqs` or a
`*CASE_TAC` **7,559 times in 145 of them**, over the 2,809 `case`
expressions of their definitions and statements._

## 1. The idiom

A proof of the CakeML semantics looks like this (HOL4,
`bvi_letProofScript.sml`):

```
Theorem evaluate_SNOC_Rval:
   evaluate (SNOC x y,env,s) = (Rval a,r) ==> ...
Proof
  fs [evaluate_SNOC] \\ every_case_tac \\ fs []
  \\ imp_res_tac evaluate_SING_IMP \\ rw []
  \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
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

So after `fs [evaluate_SNOC]` the goal holds a **term** of the shape
`case evaluate (...) of ...`, nested twice.  `every_case_tac` takes
it apart into the four combinations (`Rval`/`Rerr` for each inner
evaluation), and in each of them the `case` disappears and leaves an
ordinary equation between pairs.  That is the whole trick, and it is
used 7,559 times.

**Your question -- is the bottleneck the `case` or the `evaluate`?**
Both, and the interesting part is the interaction.  The scrutinee is
not a variable: it is `evaluate (xs,env,s)`, an application of a
recursively defined function, so

- it cannot be taken apart by an induction or by naming a variable;
  the case analysis is on a *compound term*, and
- its **identity has to survive** the case analysis, because the next
  lines of the proof (`imp_res_tac evaluate_SING_IMP`) are about
  *that* evaluation: they need the hypothesis
  `evaluate ([x],env,s2) = (Rval v,s1)` to be there afterwards.

A case analysis that only replaces the term by `(Rval v,s1)`
everywhere would satisfy the `case` and lose the proof.

## 2. What HOL4 does

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
   assumptions* for a subterm that is a fully applied case
   expression whose scrutinee is free in the goal, and does
   `Cases_on` on that scrutinee.  The search is
   `first_subterm`/`case_find_subterm` (`:652`), which goes
   **innermost first** -- the deepest case, not the outermost one.
2. **`Cases_on` on a compound term** ends in `TERM_INTRO_TAC`
   (`:72`):

   ```sml
   val TERM_INTRO_TAC = STRIP_ALL_THEN
                          (fn th => TRY (SUBST_ALL_TAC th) THEN ASSUME_TAC th);
   ```

   It takes the type's `nchotomy` (`!x. (?v. x = Rval v) \/ (?e. x =
   Rerr e)`), instantiates it at the term, splits the disjunction,
   and in each branch **substitutes the equation everywhere and
   keeps it as an assumption**.  That is the answer to the identity
   problem above: after the split the goal says `(Rval vs,s2)` and
   the assumptions still say `evaluate (...) = (Rval vs,s2)`.
   (For a scrutinee that *is* a variable, `VAR_INTRO_TAC` only
   substitutes -- the equation would be redundant.)
3. **`use_new_assum`** (`:790`) throws away the reflexive
   assumptions the split produced, rewrites with the new assumptions
   and rewrites the old assumptions with them.
4. **`CASE_SIMP_CONV`** rewrites with `case_rwlist()`: the **case
   definition theorems** of every datatype in the TypeBase, plus
   distinctness and injectivity, cached once.

Step 4 is the one that has no counterpart in HOL Light, and it is
the reason HOL4's version is robust.  In HOL4,

```
case x of Rval v => f v | Rerr e => g e
```

is *syntax* for

```
result_CASE x (\v. f v) (\e. g e)
```

where `result_CASE` is an ordinary constant that the `Datatype`
declaration defines, with ordinary equations:

```
result_CASE (Rval v) f g = f v
result_CASE (Rerr e) f g = g e
```

So a case expression disappears by **rewriting**.  If the scrutinee
is not a constructor application, no equation matches and nothing
happens -- no decision, no failure, no garbage.  `Cases_on` makes it
a constructor application; the equation then fires; `BETA_RULE`
cleans up.

## 3. What HOL Light has instead

HOL Light has no case constants.  `match x with ...` is syntax for

```
_MATCH x (_SEQPATTERN arm1 (_SEQPATTERN arm2 ...))
```

where an arm is `\u v. ?vs. _UNGUARDED_PATTERN (GEQ pat u) (GEQ body v)`,
and the only way to get rid of one is `MATCH_CONV`
(`hol-light/ind_types.ml:1421`), which is a **decision procedure**:
it tries to decide whether the pattern matches the scrutinee.

That difference is the whole problem:

| | HOL4 | HOL Light |
|---|---|---|
| a `case` is | an application of `ty_CASE` | `_MATCH x (_SEQPATTERN …)` |
| removing one is | rewriting with its equations | deciding a match |
| scrutinee not a constructor | nothing happens | **an epsilon term appears** |

`MATCH_CONV` on an undecidable scrutinee does not fail: it returns

```
if ... then @GEN%PVAR%4210. ... else @x. false
```

and the goal is gone.  Worse, once one of those is in the goal, the
next reduction grows it.

So the port's representation of a `case` -- which is faithful to
what the source *says* -- is the wrong representation for *proving*,
and that is what four attempts at a tactic kept running into:

1. `MATCH_REDUCE_CONV` under a traversal does nothing (it is
   `REPEATC …`, which never fails, so `ONCE_DEPTH_CONV` stops at the
   top of the term);
2. `MATCH_CONV` can return a no-change theorem, so a `REPEAT` of it
   spins;
3. an undecidable scrutinee becomes the epsilon term above;
4. and I searched for the scrutinee **outermost first**, where HOL4
   searches innermost first -- so the outer case was split while the
   inner scrutinee was still a compound term, and the next reduction
   met exactly the undecidable case of (3).

## 4. The two routes

**Route A -- a case constant per datatype, as HOL4 has.**
`ml/lib/define.ml` defines, for every datatype it makes, a constant

```
let result_CASE = new_recursive_definition result_RECURSION
  `(result_CASE (Rval v) f g = f v) /\
   (result_CASE (Rerr e) f g = g e)`
```

(mechanical: one clause per constructor, straight from the
`RECURSION` theorem the port already has), and `tools/port.py` writes
a `case` of a source as an application of it instead of a `match`.
Then the HOL Light `every_case_tac` is HOL4's, line for line, with
`REWRITE_TAC` where HOL4 has its simpset, and nothing can produce an
epsilon because nothing decides anything.

Cost: a generator change that touches every `case` of the port
(2,809 of them), a full run to re-read the statements, and the port's
text drifts from the source -- `result_CASE (evaluate (…)) (\vs s2.
…) (\t. t)` where the source says `case evaluate (…) of …`.  That
last point is a real loss: phase two's test is that a source and its
port read the same.

**Route B -- keep the `match`, fix the tactic.**  Do what HOL4 does,
with `MATCH_CONV` only ever applied where it cannot misfire:

1. find the **innermost** match scrutinee that is free in the goal
   (`match_scruts` + an innermost search, as `case_find_subterm`);
2. split it with the type's cases theorem, `TRY (SUBST_ALL_TAC eq)
   THEN ASSUME_TAC eq` for a compound term and `SUBST_ALL_TAC` for a
   variable -- HOL4's `TERM_INTRO_TAC`/`VAR_INTRO_TAC`;
3. reduce **only** matches whose reduction introduces no epsilon;
4. repeat, with the number of `_MATCH` subterms as a progress
   measure, so that a goal the three steps cannot finish fails
   instead of spinning.

Cost: the tactic, and the knowledge that it is subtle.  Nothing in
the port changes, so no re-run and no drift.

**Route B is the one to build first**, because it is local, and
because if it works the 7,559 case splits of the sources are all
reachable.  Route A stays available if B turns out to be unreliable
on the bigger goals -- and A is also what one would do if the port
ever wanted HOL4's `CaseEq`/`AllCaseEqs` idiom, which rewrites with
equations like `(case x of … ) = y <=> ?v. x = Rval v /\ …` and is
used 7,559 times together with `every_case_tac`.

## 5. What this says about the estimate

The nine proofs already written are the ones that do not meet a
`case`: 1-3 lines of HOL4 each, median 25 s.  Every proof that meets
one was blocked, which is why the file stands at 9 of 17 and not at
15 of 17.  Until route B (or A) is in, the measured rate of the easy
band says nothing about the 2,318 proofs of the port that are longer
than 10 lines -- they are nearly all semantics proofs, and nearly all
of them use this idiom.
