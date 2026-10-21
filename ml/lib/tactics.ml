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
