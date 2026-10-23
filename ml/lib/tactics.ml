(* ================================================================== *)
(*  The tactics of phase three.                                       *)
(*                                                                    *)
(*  This file holds no definition and no theorem, only tactics, so   *)
(*  it can be loaded again into a running session:                    *)
(*                                                                    *)
(*    tools/bin/reload <session>                                      *)
(*                                                                    *)
(*  A tactic that is added or corrected costs a second that way,      *)
(*  where a change in a file that defines something costs the whole   *)
(*  session again (ml/lib/define.ml and the rest: 8 minutes for the   *)
(*  needs closure of a file, 94 minutes for the whole port).  Load    *)
(*  the file as a whole, not the one tactic that changed: OCaml binds *)
(*  a name where it stands, so a caller keeps the old one.            *)
(*                                                                    *)
(*  What the tactics are for, and what the HOL4 idioms they           *)
(*  stand in for are, is written out in PORTING-GUIDE.md.             *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Two tactics that the proofs of phase three need.                   *)

(* Reduce every match of the goal against the constructors that its
   scrutinee has.  The definitions of the port are matches, so a
   proof that unfolds one has to reduce it.  MATCH_REDUCE_CONV
   cannot be used under a traversal for this: REPEATC never fails,
   so ONCE_DEPTH_CONV stops at the top of the term and changes
   nothing. *)

let MATCH_REDUCE_TAC =
  REPEAT(CHANGED_TAC(CONV_TAC(ONCE_DEPTH_CONV MATCH_CONV)));;

(* Take the named variables of a list type apart.  By name, because
   the type of a variable of a statement is often a type variable
   and an ISPEC of list_CASES cannot then be written down; and only
   the named ones, because LIST_SPLIT_TAC takes every list variable
   of a match apart, which loses the one that the induction
   hypothesis is about (a STRUCT_CASES_TAC rewrites the goal and
   not the assumptions). *)

let LIST_CASES_TAC names (asl,w as gl) =
  MAP_EVERY
    (fun n ->
       let v = find_term (fun t -> is_var t && fst(dest_var t) = n) w in
       STRUCT_CASES_TAC (ISPEC v list_CASES))
    names gl;;

(* ================================================================== *)

(* ---- HOL4's every_case_tac: PORTING-GUIDE.md entry 1 ------------- *)

let prod_type ty =
  try fst(dest_type ty) = "prod" with Failure _ -> false;;

let constructors_of ty =
  map (fun d -> fst(strip_comb(rhs(snd(strip_exists d)))))
      (disjuncts(snd(strip_forall(concl(cases_of ty)))));;

(* the name, not the constant: the cases theorem of a polymorphic
   type gives its constructors at the type of the theorem, and a
   CONS of a num list is not that CONS *)

let is_con_app t =
  try let h = fst(strip_comb t) in
      is_const h &&
      mem (fst(dest_const h))
          (map (fun c -> fst(dest_const c))
               (constructors_of (type_of t)))
  with Failure _ -> false;;

(* RULE_ASSUM_TAC applies its rule to every assumption and fails if
   it fails on one of them, so a pass that is meant to simplify what
   it can is a no-op as soon as one assumption has nothing to
   simplify.  This is the per-assumption version. *)

let RULE_ASSUM_TRY rule =
  RULE_ASSUM_TAC(fun th -> try rule th with Failure _ -> th);;

(* reduce the matches whose reduction says something: MATCH_CONV on
   a scrutinee that the patterns cannot decide does not fail but
   gives an epsilon term, and the goal is lost *)

let safe_match_conv tm =
  match tm with
    Comb(Comb(Const("_MATCH",_),_),_) ->
      let th = CHANGED_CONV MATCH_CONV tm in
      if can (find_term is_select) (rand(concl th))
      then failwith "safe_match_conv" else th
  | _ -> failwith "safe_match_conv";;

let SAFE_MATCH_REDUCE_TAC =
  CHANGED_TAC(CONV_TAC(REDEPTH_CONV safe_match_conv));;

(* and the matches of the assumptions, which is where a rewrite with
   evaluate_CONS puts the other half of the equation.  HOL4 reduces
   them too: the RULE_ASSUM_TAC asm_rule of EVERY_CASE_TAC
   (BasicProvers.sml:820). *)

let SAFE_MATCH_REDUCE_ASM_TAC =
  CHANGED_TAC(RULE_ASSUM_TRY(CONV_RULE(REDEPTH_CONV
                               safe_match_conv)));;

(* case analysis on a scrutinee, as HOL4's Cases_on: a compound term
   keeps its equation, because the lemmas about evaluate are applied
   to it afterwards (TERM_INTRO_TAC, BasicProvers.sml:72); a
   variable does not need one (VAR_INTRO_TAC) *)

let CASES_ON_TAC t =
  let th = if prod_type (type_of t) then ISPEC t PAIR_SURJECTIVE
           else ISPEC t (cases_of (type_of t)) in
  let use eq =
    if is_var t then SUBST_ALL_TAC eq
    else TRY(SUBST_ALL_TAC eq) THEN ASSUME_TAC eq in
  (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN use)) th;;

(* the scrutinees of the matches of the goal and of the assumptions
   that are not in constructor shape yet, the deepest first.  Both,
   because HOL4 searches list_mk_conj (w :: asl) (PURE_FULL_CASE_TAC,
   BasicProvers.sml:694) and a proof of the semantics leaves the
   match a rewrite made in a hypothesis as often as in the goal.
   Deepest first, because that is HOL4's search (case_find_subterm,
   :652): the outermost scrutinee would be split while an inner one
   is still a compound term, and the reduction of that inner match
   then meets the undecidable case above.

   A variable is a scrutinee worth splitting when its type has more
   than one constructor -- or when it is a pair, which has one and
   still has to come apart: a pattern of the source that reads the
   two halves of what find_code returned leaves the pair as a
   variable under a SOME. *)

(* The patterns of a match, which is what says where to split: a
   HOL4 case is nested applications of case constants, one per level
   of the pattern, so its innermost-first search finds each level by
   itself; HOL Light's _MATCH has the whole pattern in one arm, so
   the port has to read the arms. *)

let match_arms tm =
  let rec arms t =
    match t with
      Comb(Comb(Const("_SEQPATTERN",_),a),b) -> a :: arms b
    | _ -> [t] in
  let pat_of arm =
    match snd(strip_exists(snd(strip_abs arm))) with
      Comb(Comb(Const("_UNGUARDED_PATTERN",_),
                Comb(Comb(Const("GEQ",_),p),_)),_) -> p
    | _ -> failwith "match_arms" in
  match tm with
    Comb(Comb(Const("_MATCH",_),sc),a) -> sc,mapfilter pat_of (arms a)
  | _ -> failwith "match_arms";;

let match_pairs tm =
  let rec go t acc =
    let acc = try let sc,pats = match_arms t in
                  itlist (fun p l -> (p,sc) :: l) pats acc
              with Failure _ -> acc in
    match t with
      Comb(a,b) -> go a (go b acc)
    | Abs(_,b) -> go b acc
    | _ -> acc in
  go tm [];;

(* and a split is wanted exactly where a pattern is deeper than the
   term it is matched against: the scrutinee of the match itself
   (the pattern is a constructor, the scrutinee an application), and
   the argument of a constructor that the pattern takes apart (the
   pair under the SOME of SOME (args,exp)).  Where the pattern has a
   variable, as the vs of Rval vs, nothing is wanted. *)

let scruts_of_goal (asl,w) =
  let tms = w :: map (fun (_,th) -> concl th) asl in
  let fvs = itlist (fun t a -> union (frees t) a) tms [] in
  let ok t =
    not (is_con_app t) && not (is_const t) &&
    subtract (frees t) fvs = [] &&
    (is_var t ||
     (is_const (fst(strip_comb t)) &&
      (fst(dest_const(fst(strip_comb t)))).[0] <> '_')) in
  let rec wanted p s =
    if is_var p then []
    else if ok s then [s]
    else
      let hp,ap = strip_comb p and hs,asc = strip_comb s in
      if hp = hs && length ap = length asc then
        itlist2 (fun x y l -> wanted x y @ l) ap asc []
      else [] in
  let rec depth t =
    match t with
      Comb(a,b) -> 1 + max (depth a) (depth b)
    | Abs(_,b) -> 1 + depth b
    | _ -> 0 in
  let cands =
    setify (itlist (fun t a ->
              itlist (fun (p,s) l -> wanted p s @ l)
                     (match_pairs t) a)
            tms []) in
  sort (fun a b -> depth a > depth b) cands;;

(* The same split, but with the existentials of the cases theorem
   named by the proof instead of by HOL Light.  EVERY_CASE_TAC
   leaves goals whose variables it invented (a', y''), which a proof
   cannot then speak about: the witness of an existential goal, or
   the instance of an induction hypothesis, has to be written down.
   So where the proof has something to say after the split, it makes
   the split itself:

     NAMED_CASES_TAC `evaluate ([h],env2,s)` [["hres"; "hs"]]
     NAMED_CASES_TAC `hres:...` [["hv"]; ["he"]]

   one list of names per disjunct of the cases theorem, in its
   order; a product has one disjunct and two names. *)

let NAMED_CASES_TAC t nss =
  let th = if prod_type (type_of t) then ISPEC t PAIR_SURJECTIVE
           else ISPEC t (cases_of (type_of t)) in
  let use eq = if is_var t then SUBST_ALL_TAC eq
               else TRY(SUBST_ALL_TAC eq) THEN ASSUME_TAC eq in
  let rec choose ns th =
    match ns with
      [] -> use th
    | n :: rest ->
        let v,_ = dest_exists (concl th) in
        X_CHOOSE_THEN (mk_var(n,type_of v)) (choose rest) th in
  let rec go nss th =
    if is_disj (concl th) then
      match nss with
        ns :: more -> DISJ_CASES_THEN2 (choose ns) (go more) th
      | [] -> failwith "NAMED_CASES_TAC"
    else match nss with
           [ns] -> choose ns th
         | _ -> failwith "NAMED_CASES_TAC" in
  go nss th;;

(* and the branches that the split makes impossible are closed at
   once, as HOL4 closes them (use_new_assum and the distinctness
   and injectivity theorems of CASE_SIMP_CONV): without that the
   goals multiply with every split *)

let case_rws ty =
  let nm = fst(dest_type ty) in
  PAIR_EQ ::
  (try [distinctness nm] with Failure _ -> []) @
  (try [injectivity nm] with Failure _ -> []);;

let PRUNE_TAC rws =
  RULE_ASSUM_TRY(REWRITE_RULE rws) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  TRY(ASM_REWRITE_TAC rws);;

(* HOL4's fs [] also rewrites the assumptions with one another,
   which HOL Light has no tactic for: ASM_REWRITE_TAC rewrites the
   goal with the assumptions and RULE_ASSUM_TAC rewrites the
   assumptions with theorems.  A split on a condition of a
   definition leaves the condition as one assumption and the
   equation that mentions it as another, and the proof needs the
   second simplified by the first.  One pass, because two
   assumptions that rewrite each other would not terminate. *)

let ASM_FS_TAC (asl,w as gl) =
  let ths = map snd asl in
  RULE_ASSUM_TAC
    (fun th ->
       let others =
         filter (fun t -> not (aconv (concl t) (concl th))) ths in
       try REWRITE_RULE others th with Failure _ -> th) gl;;

(* A conditional is a case expression on a boolean, which is how
   HOL4 sees it: its every_case_tac splits an if of the goal or of
   an assumption like any other case.  So the conditions count as
   candidates too, the outermost first -- an inner conditional is
   under the outer one and cannot be decided before it. *)

let conds_of_goal (asl,w) =
  let tms = w :: map (fun (_,th) -> concl th) asl in
  let fvs = itlist (fun t a -> union (frees t) a) tms [] in
  let cond_of u = rand(rator(rator u)) in
  let ok u = try let c = cond_of u in
                 subtract (frees c) fvs = [] && not (is_const c)
             with Failure _ -> false in
  let cs = filter ok (itlist (fun t a -> find_terms is_cond t @ a)
                             tms []) in
  let rec size t =
    match t with
      Comb(a,b) -> size a + size b
    | Abs(_,b) -> 1 + size b
    | _ -> 1 in
  let rec dedup l =
    match l with
      [] -> []
    | x :: r -> x :: dedup (filter (fun y -> not (y = x)) r) in
  dedup (map cond_of (sort (fun a b -> size a > size b) cs));;

let CASE_SPLIT_TAC gl =
  match scruts_of_goal gl with
    [] -> failwith "CASE_SPLIT_TAC"
  | t :: _ ->
      (CASES_ON_TAC t THEN PRUNE_TAC (case_rws (type_of t))) gl;;

(* the same for a conditional, kept apart from CASE_SPLIT_TAC: a
   proof that wants HOL4's reading of an if as a case says so *)

let COND_SPLIT_TAC gl =
  match conds_of_goal gl with
    [] -> failwith "COND_SPLIT_TAC"
  | c :: _ ->
      (ASM_CASES_TAC c THEN ASM_FS_TAC THEN
       TRY(ASM_REWRITE_TAC[])) gl;;

(* HOL4's every_case_tac: split the innermost scrutinee, reduce what
   can be reduced, and again.  Bounded, because a step that only
   adds an assumption is progress that a goal cannot measure. *)

(* MATCH_CONV leaves the guard of a pattern that binds variables
   (`if ?vs. vs = a then ... `), which is trivially true.  In the
   assumptions as well as in the goal, and there the conjunctions
   that PAIR_EQ makes are taken apart, which is the part of HOL4's
   fs [] that the proof after the split relies on. *)

let SPLIT_ASM_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj (concl th) then CONJUNCTS_THEN ASSUME_TAC th
    else failwith "SPLIT_ASM_TAC"));;

let tidy_rws = [UNWIND_THM1; UNWIND_THM2; EXISTS_REFL;
                FORALL_UNWIND_THM1; FORALL_UNWIND_THM2;
                NOT_CONS_NIL; CONS_11; NOT_SUC; SUC_INJ; PAIR_EQ;
                distinctness "option"; injectivity "option"];;

let MATCH_TIDY_TAC =
  let unwind th = try CONV_RULE(REDEPTH_CONV UNWIND_CONV) th
                  with Failure _ -> th in
  TRY(CONV_TAC(REDEPTH_CONV UNWIND_CONV)) THEN
  RULE_ASSUM_TRY (REWRITE_RULE tidy_rws o unwind) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  SPLIT_ASM_TAC THEN
  TRY(REWRITE_TAC tidy_rws);;

let EVERY_CASE_TAC =
  let reduce =
    (SAFE_MATCH_REDUCE_TAC THEN TRY SAFE_MATCH_REDUCE_ASM_TAC) ORELSE
    SAFE_MATCH_REDUCE_ASM_TAC in
  let step = ((CASE_SPLIT_TAC THEN TRY reduce) ORELSE reduce) THEN
             MATCH_TIDY_TAC in
  let rec go k gl =
    if k <= 0 then ALL_TAC gl
    else (try (step THEN go (k - 1)) gl
          with Failure _ -> ALL_TAC gl) in
  go 10;;

(* and the same with the condition of a branch decided before the
   case under it, which is what a proof that uses an induction
   hypothesis inside a branch needs: a case taken apart while a
   condition above it is still open leaves the hypothesis a side
   condition the branch cannot settle, because in the branch where
   the condition holds the result is already decided and nothing is
   known about what was split (PORTING-GUIDE.md entry 14).  It is a
   tactic of its own and not the behaviour of EVERY_CASE_TAC,
   because deciding a condition that no hypothesis is used under
   only adds a vacuous split, and the proofs that take a statement
   apart with EVERY_CASE_TAC are written for the shape it leaves. *)

let EVERY_CASE_COND_TAC =
  let reduce =
    (SAFE_MATCH_REDUCE_TAC THEN TRY SAFE_MATCH_REDUCE_ASM_TAC) ORELSE
    SAFE_MATCH_REDUCE_ASM_TAC in
  let step = (((COND_SPLIT_TAC ORELSE CASE_SPLIT_TAC) THEN
               TRY reduce) ORELSE reduce) THEN
             MATCH_TIDY_TAC in
  let rec go k gl =
    if k <= 0 then ALL_TAC gl
    else (try (step THEN go (k - 1)) gl
          with Failure _ -> ALL_TAC gl) in
  go 10;;

(* A record of the port is a datatype with one constructor
   (ml/lib/records.ml), and its accessor and update theorems are
   stated at that constructor.  So a field update whose new value is
   the field's own value -- which is what fix_clock s (res,s) leaves
   behind, state_clock_fupd (K (state_clock s)) s -- only reduces
   once the record is taken apart.  HOL4 never meets this: its
   record_fupd simpset has the identity law. *)

let RECORD_CASES_TAC t =
  let nm = fst(dest_type (type_of t)) in
  STRUCT_CASES_TAC (ISPEC t (cases_of (type_of t))) THEN
  REWRITE_TAC (K_DEF :: record_thms nm);;

(* HOL4's rveq (var_eq_tac): use up the equations between variables
   that a case split leaves, and keep the others -- the equations
   that say what a function returned are the ones the proof needs.
   The variable is the side that goes: an equation the other way
   round ([] = a) is used by its SYM, or the goal keeps the variable
   and loses the value. *)

let VAR_EQ_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if is_var l then SUBST_ALL_TAC th
    else if is_var r then SUBST_ALL_TAC(SYM th)
    else failwith "VAR_EQ_TAC"));;

(* resolve a lemma whose hypothesis is a conjunction against the
   assumptions, as HOL4's imp_res_tac does *)

let RES2_TAC lemma =
  FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
    MP_TAC(MATCH_MP lemma (CONJ th1 th2))));;

(* and the same with the rest of the proof inside the search, so
   that the search backtracks when the rest does not go through.
   A lemma about [x] matches more assumptions than the one meant --
   evaluate ([delete_var h],env2,s) as well as evaluate ([h],env2,s)
   -- and FIRST_ASSUM commits as soon as MATCH_MP succeeds, which is
   before the proof that needed the other one fails. *)

let RES1_THEN lemma tac =
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP lemma th) THEN tac);;

let RES2_THEN lemma tac =
  FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
    MP_TAC(MATCH_MP lemma (CONJ th1 th2)) THEN tac));;

(* a tactic that has to close its goal: the branches of a finish
   that is applied to the goals of a case split are tried with
   FIRST, which commits to the first one that succeeds, and a step
   that only rewrites succeeds without finishing *)

let SOLVED tac =
  fun gl -> let (_,gls,_) as gst = tac gl in
            if gls = [] then gst else failwith "SOLVED";;

(* ------------------------------------------------------------------ *)
(* The three steps of a proof about a transformation of the           *)
(* compiler: the induction, the reduction between two steps, and the  *)
(* use of the induction hypothesis.  Fifty-three of the sixty-one     *)
(* proof theories of the port have an evaluate and an induction, so   *)
(* these are written once here and instantiated per file              *)
(* (PORTING-GUIDE.md, "the shape of a transformation proof").         *)
(* ------------------------------------------------------------------ *)

(* HOL4's recInduct f_ind and completeInduct_on: an induction on a
   measure, with the measure bounded rather than equal, so that
   INDUCT_TAC is enough and the hypothesis is about the measure of
   the sub-term and not about the bound (PORTING-GUIDE.md entry 5).
   The argument is the measure as a function; the variable it is
   taken of is the quantified one of its domain type.  Where the
   goal is an implication the bound joins its antecedent, so that
   the hypothesis has one antecedent and not two.  It leaves the
   base case and the step case, as INDUCT_TAC does. *)

let MEASURE_INDUCT_TAC meas (asl,w) =
  let avs0,bod = strip_forall w in
  let dty = fst(dest_fun_ty(type_of meas)) in
  let v = try find (fun x -> type_of x = dty) avs0
          with Failure _ -> failwith "MEASURE_INDUCT_TAC" in
  (* a variable that the statement quantifies and does not use (the
     ys of bvi_letProof's evaluate_env_rel) is left out, so that the
     hypothesis has one quantifier for every argument it is given *)
  let avs = filter (fun x -> x = v || vfree_in x bod) avs0 in
  let kv = variant (avs @ frees bod) (mk_var("k",`:num`)) in
  let m = mk_comb(meas,v) in
  let cnd = mk_binop `(<=):num->num->bool` m kv in
  let sub =
    list_mk_forall(kv :: avs,
      if is_imp bod && not (is_neg bod)
      then mk_imp(mk_conj(cnd,lhand bod),rand bod)
      else mk_imp(cnd,bod)) in
  (SUBGOAL_THEN sub
     (fun th -> REPEAT GEN_TAC THEN TRY STRIP_TAC THEN
        MP_TAC(SPECL (m :: avs) th) THEN
        ASM_REWRITE_TAC[LE_REFL]) THEN
   INDUCT_TAC) (asl,w);;

(* HOL4's fs and gvs: the bundle of reductions that goes between two
   steps of such a proof.  The first argument is the file's own
   rewrites in stages, because one of them has to fire before
   another (bvi_letProof rewrites with fix_clock_evaluate before the
   definition of fix_clock, or it is left with a record update); the
   second is the lemmas that decide an equation between two results,
   which PRUNE_TAC throws the impossible assumptions out with.  The
   goal and the assumptions are reduced alike: one of them with its
   match turned into a guard and the other not is two shapes of the
   same thing. *)

let FS_TAC stages prunes =
  itlist (fun rws t -> TRY(REWRITE_TAC rws) THEN
                       RULE_ASSUM_TRY(REWRITE_RULE rws) THEN t)
         stages
         (TRY SAFE_MATCH_REDUCE_TAC THEN
          TRY SAFE_MATCH_REDUCE_ASM_TAC THEN
          PRUNE_TAC prunes THEN MATCH_TIDY_TAC THEN
          SPLIT_ASM_TAC THEN VAR_EQ_TAC);;

(* HOL4's drule for such a proof, which is the step that made the
   deep cases possible: find an evaluation of the source in the
   assumptions whose compiled twin is somewhere in the goal, and
   hand the two to the instantiation of the hypothesis.  The search
   is the part that is the same in every file; the instantiation is
   not, because it is the statement of that file's theorem, so it is
   the caller's.
     ev is the name of the semantics constant, cp the name of the
   constant that compiles, and use is given the source's list, its
   environment and its state, the pair that it evaluates to, the
   arguments of the compiled call and its environment.  An
   evaluation whose result the assumptions already have is no
   progress, and the search goes on to the next one. *)

let EV_PAIR_TAC ev cp use (asl,w as gl) =
  let named n t =
    try fst(dest_const(fst(strip_comb t))) = n
    with Failure _ -> false in
  let is_ev = named ev and is_cp = named cp in
  let dest_ev t =
    let a,bc = dest_pair (rand t) in
    let b,c = dest_pair bc in a,b,c in
  let where = w :: map (fun (_,th) -> concl th) asl in
  let evs = filter (fun t -> is_ev t && can dest_ev t)
                   (itlist (fun t a -> find_terms is_ev t @ a)
                           where []) in
  let attempt (_,th) =
    let l,rt = dest_eq(concl th) in
    if not (is_ev l) then fail() else
    let xs,env1,s = dest_ev l in
    (* the hypothesis is driven by the source's evaluation, never
       by the compiled one *)
    if is_cp xs then fail() else
    let gt = find (fun g ->
        try let cl,env2,s2 = dest_ev g in
            s2 = s && is_cp cl && mem xs (snd(strip_comb cl))
        with Failure _ -> false) evs in
    let cl,env2,_ = dest_ev gt in
    if exists (fun (_,t) -> aconv (concl t) (mk_eq(gt,rt))) asl
    then fail() else
    use (xs,env1,s) rt (snd(strip_comb cl)) env2 in
  tryfind (fun a -> attempt a gl) asl;;

(* ------------------------------------------------------------------ *)
(* A split by the name of the variable.                               *)
(*                                                                    *)
(* The sources annotate no type where HOL4 can infer one, so a        *)
(* statement of the port often has type variables that the port       *)
(* invented (PORTING-GUIDE.md entry 12), and a term that a proof      *)
(* writes down is then not the term of the goal: the split says       *)
(* nothing and the goal does not move.  These take the variable out   *)
(* of the goal (or of the assumptions) by its name, so that its type  *)
(* is whatever the statement gave it.                                 *)
(* ------------------------------------------------------------------ *)

let var_by_name n (asl,w) =
  let ok t = is_var t && fst(dest_var t) = n in
  tryfind (fun t -> find_term ok t)
          (w :: map (fun (_,th) -> concl th) asl);;

let CASES_BY_NAME n (asl,w as gl) =
  let v = var_by_name n gl in
  (if prod_type (type_of v)
   then STRUCT_CASES_TAC(ISPEC v PAIR_SURJECTIVE)
   else STRUCT_CASES_TAC(ISPEC v (cases_of (type_of v)))) gl;;

(* and the instance of a lemma at such a variable *)

let ISPEC_NAME n th (asl,w as gl) = ISPEC (var_by_name n gl) th;;

let MP_ISPEC_NAME n th (asl,w as gl) =
  MP_TAC(ISPEC_NAME n th gl) gl;;

(* ------------------------------------------------------------------ *)
(* The definition of a constant in its lambda form.                   *)
(*                                                                    *)
(* A HOL4 definition that takes the type itself as an argument has a  *)
(* clause of that one instance ((:'a)), so a statement about the      *)
(* constant at a variable cannot be rewritten with it.  HOL Light's   *)
(* own definition of the constant is generic in that argument, and    *)
(* this is it.                                                        *)
(* ------------------------------------------------------------------ *)

let cake_raw name =
  try find (fun th -> try fst(dest_const(lhs(concl th))) = name
                      with Failure _ -> false)
           (definitions())
  with Failure _ ->
    failwith ("cake_raw: no definition of " ^ name);;

(* ------------------------------------------------------------------ *)
(* The induction hypothesis applied to an assumption: both are found  *)
(* in the assumption list, which is what an induction over a list of  *)
(* a statement with an existential needs.                             *)
(* ------------------------------------------------------------------ *)

let USE_IH =
  FIRST_X_ASSUM(fun ih ->
    FIRST_X_ASSUM(fun a -> MP_TAC(MATCH_MP ih a)));;

(* ------------------------------------------------------------------ *)
(* HOL4's pairarg_tac: a let that takes a pair apart does not reduce  *)
(* while the value it binds is not a pair, so the value is split      *)
(* first.                                                             *)
(* ------------------------------------------------------------------ *)

let PAIRARG_TAC (asl,w as gl) =
  let ok t =
    match t with
      Comb(Comb(Const("LET",_),_),a) ->
        prod_type (type_of a) && not (can dest_pair a)
    | _ -> false in
  let t = find_term ok (list_mk_conj (w :: map (concl o snd) asl)) in
  CASES_ON_TAC (rand t) gl;;

(* and the case split of a named variable that goes into the
   assumptions as well (CASES_ON_TAC's SUBST_ALL_TAC), which is what
   an induction hypothesis about that variable needs *)

let CASES_ON_NAME n (asl,w as gl) = CASES_ON_TAC (var_by_name n gl) gl;;

(* ------------------------------------------------------------------ *)
(* HOL4's asm_exists_tac: the goal is an existential whose body is    *)
(* what an assumption says of other witnesses, and the assumption     *)
(* gives them.  The first conjunct of the body is what is matched,    *)
(* as HOL4 does it.                                                   *)
(* ------------------------------------------------------------------ *)

let ASM_EXISTS_TAC (asl,w as gl) =
  let vs,bod = strip_exists w in
  if vs = [] then failwith "ASM_EXISTS_TAC: no existential" else
  let c = hd (conjuncts bod) in
  let i = tryfind (fun (_,th) -> term_match [] c (concl th)) asl in
  MAP_EVERY EXISTS_TAC (map (instantiate i) vs) gl;;

(* The assumption that a rewrite changes, as the antecedent of the
   goal: a long list of assumptions has one of the shape that a
   definition unfolds, and this picks it out without naming it. *)

let USE_CHANGED ths =
  FIRST_X_ASSUM(fun th ->
    let th' = REWRITE_RULE ths th in
    if concl th' = concl th then fail() else MP_TAC th');;

(* The assumption that gives a variable its value, substituted
   away.  HOL Light's SUBST_VAR_TAC takes the variable on either
   side of the equation, which in a goal of the port is as often
   the variable that the statement is about (the w of
   `word_addr c h = w`) as the one that a case split introduced. *)

let SUBST_LHS_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && is_var(lhs(concl th))
    then SUBST_ALL_TAC th else fail());;

(* Two assumptions that contradict each other close the goal.  A
   case analysis of the relations of the port brings a `~b` against
   a `b` all the time, and MESON over the twenty assumptions that a
   memory_rel goal has is too slow to be the way to use them. *)

let CONTRA_TAC (asl,w as gl) =
  let ths = map snd asl in
  CONTR_TAC
    (tryfind (fun t2 ->
       if is_neg(concl t2)
       then tryfind (fun t1 ->
              if concl t1 = rand(concl t2)
              then MP (NOT_ELIM t2) t1 else fail()) ths
       else fail()) ths) gl;;

(* An assumption that is a conditional, a disjunction or an
   existential, opened into the goal: the body of a relation of the
   port is a disjunction of its rules, and this takes them apart one
   after the other. *)

let OPEN_ASSUM =
  FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_cond t || is_disj t || is_exists t
    then MP_TAC th THEN TRY COND_CASES_TAC THEN STRIP_TAC
    else fail());;

(* A theorem of a file of the port by the name that HOL4 gives it:
   cake_theorem registers every one, so a tactic of the library can
   use a theorem of the file it is applied in (v_inv_def of
   data_to_word_memoryProof) without the file naming it. *)

let cake_thm name =
  try let _,_,th = find (fun (n,_,_) -> n = name) (!the_theorems) in
      th
  with Failure _ -> failwith ("cake_thm: no theorem " ^ name);;

(* The list of roots of an abs_ml_inv, split against the list of
   values: the assumption that relates the two is an ALL2 whose
   first list is a cons and whose second is the variable that the
   existential of word_ml_inv introduced, and the proofs of the
   memory invariant all start by taking that one apart. *)

let SPLIT_ROOTS_TAC (asl,w as gl) =
  let roots = tryfind (fun (_,th) ->
    let c = concl th in
    let f,args = strip_comb c in
    if is_const f && fst(dest_const f) = "ALL2" &&
       length args = 3 && is_var (el 2 args) &&
       not (is_var (el 1 args))
    then el 2 args else fail()) asl in
  (CASES_ON_TAC roots THEN
   RULE_ASSUM_TAC(REWRITE_RULE[MAP; ALL2; FST; SND]) THEN
   TRY(FIRST_X_ASSUM CONTR_TAC) THEN
   REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC))) gl;;

(* The chain of definitions that a goal about the memory invariant
   of data_to_word_memoryProof goes through, with the roots split
   off: memory_rel is word_ml_inv of a heap, which is abs_ml_inv of
   the values of the stack, whose bc_stack_ref_inv relates the
   values to the roots.  The sources unfold the four of them in one
   `fs` and so does this. *)

let MEMORY_REL_TAC gl =
  (REWRITE_TAC[cake_def "memory_rel"; cake_def "word_ml_inv";
               cake_def "abs_ml_inv";
               cake_def "bc_stack_ref_inv"] THEN
   STRIP_TAC THEN SPLIT_ROOTS_TAC) gl;;

(* The clauses of word_addr: the address of a Data of a word is the
   word with its tag bit taken off, the one of a Data of a Loc is
   the Loc and the one of a Pointer is its address. *)

let word_addr_clauses () =
  let cl t =
    prove(t, REPEAT GEN_TAC THEN
             GEN_REWRITE_TAC LAND_CONV [cake_def "word_addr"] THEN
             MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
  [cl `!conf w. word_addr conf (gc_shared_Data (wordLang_Word w)) =
        wordLang_Word (w && word_not (n2w 1))`;
   cl `!conf n w. word_addr conf (gc_shared_Pointer n w) =
        wordLang_Word (get_addr conf n w)`;
   cl `!conf l1 l2.
         word_addr conf (gc_shared_Data (wordLang_Loc l1 l2)) =
         wordLang_Loc l1 0`];;

(* The assumption that says what the root of a value is, taken
   apart: v_inv is a disjunction of the rules of the relation, and
   what each of them leaves is the address of a Data or of a
   Pointer, which word_addr reduces. *)

let V_INV_TAC gl =
  (RULE_ASSUM_TAC(REWRITE_RULE[cake_thm "v_inv_def";
                               injectivity "dataSem_v"]) THEN
   TRY(FIRST_X_ASSUM CONTR_TAC) THEN
   REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
   REPEAT OPEN_ASSUM THEN
   REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
   TRY CONTRA_TAC THEN REPEAT SUBST_LHS_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE(word_addr_clauses () @
     [distinctness "word_loc"; injectivity "word_loc"])) THEN
   TRY(FIRST_X_ASSUM CONTR_TAC) THEN TRY CONTRA_TAC) gl;;

(* A theorem whose hypothesis is a conjunction of two of the
   assumptions, as the antecedent of the goal: the lemmas of the
   port ask for a memory_rel and a good_dimindex all the time, and
   HOL4's `drule` finds the two the same way. *)

let USE2 th =
  FIRST_ASSUM(fun t1 -> FIRST_ASSUM(fun t2 ->
    MP_TAC(MATCH_MP th (CONJ t1 t2))));;

(* The assumption that is a conditional, opened into the goal and
   its condition decided: what a lemma of the form "if the list is
   empty then ... else ..." leaves. *)

let OPEN_COND =
  FIRST_X_ASSUM(fun th ->
    if is_cond (concl th) then MP_TAC th else fail()) THEN
  COND_CASES_TAC THEN STRIP_TAC;;

(* Every instance of a theorem whose hypothesis is a conjunction of
   three of the assumptions, assumed: the lemmas about memory_rel
   ask for the relation, a small_int and a good_dimindex, and a
   proof that needs the instance of two of the values wants both
   instances without naming either. *)

let ALL_INST3 th =
  ASSUM_LIST(fun ths ->
    MAP_EVERY ASSUME_TAC
      (mapfilter (fun (a,bc) -> MATCH_MP th (CONJ a bc))
         (allpairs (fun a bc -> (a,bc)) ths
            (allpairs (fun b c -> CONJ b c) ths ths))));;

(* and the same for a hypothesis of two assumptions *)

let ALL_INST2 th =
  ASSUM_LIST(fun ths ->
    MAP_EVERY ASSUME_TAC
      (mapfilter (fun (a,b) -> MATCH_MP th (CONJ a b))
         (allpairs (fun a b -> (a,b)) ths ths)));;
