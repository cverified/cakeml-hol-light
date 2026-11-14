(* ================================================================== *)
(*  Case analysis and induction on a term of any inductive type.      *)
(*                                                                    *)
(*  HOL Light knows every datatype it has ever made: for each one     *)
(*  `inductive_type_store` holds the induction theorem, and `cases`   *)
(*  derives the case theorem from it.  What it has not got is a       *)
(*  tactic that looks a type up there.  INDUCT_TAC is the naturals,   *)
(*  LIST_INDUCT_TAC is lists, and anything else means naming the      *)
(*  theorem by hand and putting the goal in the shape MATCH_MP_TAC    *)
(*  wants.  (The ssreflect layer of Formal_ineqs has `case` and       *)
(*  `elim`, but they read a table of five types written out by hand   *)
(*  and `elim` only fires on a goal that is already `!x. P x`.)       *)
(*                                                                    *)
(*  So these take a *term* and work for every type:                   *)
(*                                                                    *)
(*    CASES_ON_TAC  `l:(A)list`   the constructor split               *)
(*    INDUCT_ON_TAC `l:(A)list`   induction, taking along what        *)
(*                                depends on l                        *)
(*                                                                    *)
(*  which is Rocq's `destruct l` and `induction l`, and Isabelle's    *)
(*  `cases l` and `induct l`.                                         *)
(*                                                                    *)
(*  This file is about HOL Light and nothing else.                    *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* The theorems of a type, derived once.                              *)
(* ------------------------------------------------------------------ *)

(* `cases` proves the case theorem from the induction theorem every
   time it is asked; a development that splits on a type a thousand
   times should pay for that once *)

(* The case theorem of a family of types is the conjunction of the
   theorems of its members, so the one of a type is the conjunct
   whose variable has that type at its head.  A pair has no case
   theorem of its own: it has one constructor and the store holds
   the surjective pairing theorem for it. *)

let cases_of,induction_of =
  let cases_cache = ref ([]:(string*thm)list) in
  let cases_of ty =
    let s = fst(dest_type ty) in
    try assoc s (!cases_cache) with Failure _ ->
    let th =
      if s = "prod" then PAIR_SURJECTIVE else
      let ths = CONJUNCTS (cases s) in
      try find (fun th ->
                  fst(dest_type(type_of(fst(dest_forall(concl th)))))
                  = s) ths
      with Failure _ -> hd ths in
    cases_cache := (s,th)::(!cases_cache); th
  and induction_of ty =
    let s = fst(dest_type ty) in
    if s = "num" then num_INDUCTION else
    let _,ith,_ = assoc s (!inductive_type_store) in ith in
  cases_of,induction_of;;

(* ------------------------------------------------------------------ *)
(* The case split.                                                    *)
(* ------------------------------------------------------------------ *)

(* The case theorem of a type says that a term of it is one of the
   constructors applied to something:

     !x. x = [] \/ (?h t. x = CONS h t)

   so the split is: take each disjunct, name what it says exists, and
   use the equation.  For a variable the equation is substituted away
   everywhere, in the goal and in the assumptions both, which is what
   `destruct` does and what a proof about a datatype wants.  For a
   term that is not a variable the substitution may not reach every
   occurrence, so the equation is kept as well: that is Rocq's
   `destruct (f x) eqn:H`, and without it the proof has no way back
   to the term it split. *)

let CASES_ON_TAC t =
  let use eq =
    if is_var t then SUBST_ALL_TAC eq
    else TRY(SUBST_ALL_TAC eq) THEN ASSUME_TAC eq in
  (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN use))
    (ISPEC t (cases_of (type_of t)));;

(* ------------------------------------------------------------------ *)
(* Induction.                                                         *)
(* ------------------------------------------------------------------ *)

(* The induction theorem of a family of datatypes is about all of them
   at once:

     !P0 P1. ... ==> (!x. P0 x) /\ (!y. P1 y)

   which MATCH_MP_TAC cannot aim at a goal about one of them.  Taking
   the others to be trivially true and simplifying leaves the theorem
   for the one type, with the premises that were only about the others
   gone.  For a family of one this is the theorem itself.

   What that costs is the hypotheses about the other types: induction
   on an `exp` whose Call holds an `elist` gives no hypothesis about
   the list, because the predicate on lists was taken to be true.
   That is the weak scheme, and it is what Rocq's `induction` on one
   of a family gives as well; INDUCT_FAMILY_TAC below is the strong
   one, for a goal that says something about every type of the
   family at once. *)

let induction_for_type =
  let t_tm = `T` in
  fun ty ith ->
    let ps,body = strip_forall (concl ith) in
    let concls = conjuncts (rand body) in
    if length concls <= 1 then ith else
    let tyname = fst (dest_type ty) in
    let ours = find (fun c ->
        let v,_ = dest_forall c in
        fst (dest_type (type_of v)) = tyname) concls in
    let p = fst (strip_comb (snd (dest_forall ours))) in
    let triv q =
      if q = p then q
      else mk_abs (genvar (fst (dest_fun_ty (type_of q))), t_tm) in
    GEN p (REWRITE_RULE [] (SPECL (map triv ps) ith));;

(* How the goals of an induction come: one per premise of the scheme,
   each with its constructor's arguments to fix and its induction
   hypotheses to assume.  Counting them off the scheme is what lets
   the split be exact -- REPEAT CONJ_TAC would go on into a goal that
   is itself a conjunction, which is what proving two things by one
   induction looks like. *)

let induction_shape ith =
  map (fun p -> let vs,b = strip_forall p in
                length vs, length (fst (splitlist dest_imp b)))
      (conjuncts (lhand (snd (strip_forall (concl ith)))));;

let INDUCT_ON_TAC : term -> tactic =
  let go t (asl,w as g) =
    let ty = type_of t in
    let ith = induction_for_type ty (induction_of ty) in
    let rec ntac n tac = if n <= 0 then ALL_TAC
                         else tac THEN ntac (n-1) tac in
    let intro (n,m) = ntac n GEN_TAC THEN ntac m STRIP_TAC in
    let rec split = function
        [] -> ALL_TAC
      | [c] -> intro c
      | c::cs -> CONJ_TAC THENL [intro c; split cs] in
    (* the hypotheses that mention the variable go into the goal, or
       the induction hypothesis would be too weak to use them: that
       is what Rocq's `induction x` does with what depends on x *)
    let deps = filter (fun th -> vfree_in t (concl th)) (map snd asl) in
    (MAP_EVERY (fun th -> UNDISCH_TAC (concl th)) deps THEN
     SPEC_TAC (t,t) THEN
     MATCH_MP_TAC ith THEN
     split (induction_shape ith)) g in
  fun t g ->
    if not (is_var t) then
      failwith "INDUCT_ON_TAC: not a variable" else
    (* the variable may still be bound in the goal, as it is in
       `!l. P l` -- Rocq's `induction l` wants it in the context
       and HOL4's `Induct_on` does not care, and neither does this *)
    ((if vfree_in t (snd g) then ALL_TAC else X_GEN_TAC t)
     THEN go t) g;;

(* The strong scheme: a goal that is a conjunction of statements, one
   about each type of a family, is exactly what the family's own
   induction theorem concludes.

     !e. P e /\ (!l. Q l)

   INDUCT_FAMILY_TAC aims the theorem of the family at it and splits
   the premises as INDUCT_ON_TAC does.  This is the induction a proof
   about mutually recursive syntax needs -- Rocq writes the scheme out
   with `Scheme ... with ...` and HOL4 calls it Induct_on with the
   conjunction already there. *)

let INDUCT_FAMILY_TAC : tactic =
  fun (asl,w as g) ->
    let vs = map (fun c -> fst (dest_forall c)) (conjuncts w) in
    let ith = induction_of (type_of (hd vs)) in
    let rec ntac n tac = if n <= 0 then ALL_TAC
                         else tac THEN ntac (n-1) tac in
    let intro (n,m) = ntac n GEN_TAC THEN ntac m STRIP_TAC in
    let rec split = function
        [] -> ALL_TAC
      | [c] -> intro c
      | c::cs -> CONJ_TAC THENL [intro c; split cs] in
    (MATCH_MP_TAC ith THEN split (induction_shape ith)) g;;
