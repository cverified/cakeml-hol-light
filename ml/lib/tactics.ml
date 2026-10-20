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
(*  What the tactics are for is written out in CASE-IDIOM.md.         *)
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

(*  HOL4's every_case_tac for the port: see CASE-IDIOM.md.            *)
(* ---- HOL4's every_case_tac for the port (CASE-IDIOM.md) --------- *)

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

(* reduce the matches whose reduction says something: MATCH_CONV on
   a scrutinee that the patterns cannot decide does not fail but
   gives an epsilon term, and the goal is lost *)

let SAFE_MATCH_REDUCE_TAC =
  let bad t = can (find_term is_select) t in
  let conv tm =
    match tm with
      Comb(Comb(Const("_MATCH",_),_),_) ->
        let th = CHANGED_CONV MATCH_CONV tm in
        if bad (rand(concl th)) then failwith "SAFE_MATCH_REDUCE"
        else th
    | _ -> failwith "SAFE_MATCH_REDUCE" in
  CHANGED_TAC(CONV_TAC(REDEPTH_CONV conv));;

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

(* the scrutinees of the matches of the goal that are not in
   constructor shape yet, the deepest first -- as HOL4 searches them
   (case_find_subterm, BasicProvers.sml:652).  The outermost one
   would be split while an inner scrutinee is still a compound term,
   and the reduction of that inner match then meets the undecidable
   case above. *)

let scruts_of_goal (asl,w) =
  let many t =
    try length (constructors_of (type_of t)) > 1
    with Failure _ -> false in
  let ok t =
    not (is_con_app t) && subtract (frees t) (frees w) = [] &&
    (if is_var t then many t
     else is_const (fst(strip_comb t)) &&
          (fst(dest_const(fst(strip_comb t)))).[0] <> '_' &&
          (prod_type (type_of t) || many t)) in
  let rec cands t =
    if is_pair t then (let a,b = dest_pair t in cands a @ cands b)
    else if ok t then [t] else [] in
  let rec depth t =
    match t with
      Comb(a,b) -> 1 + max (depth a) (depth b)
    | Abs(_,b) -> 1 + depth b
    | _ -> 0 in
  let deep = sort (fun a b -> depth a > depth b)
                  (setify (match_scruts w)) in
  let rec collect l =
    match l with [] -> [] | s :: rest -> cands s @ collect rest in
  collect deep;;

(* and the branches that the split makes impossible are closed at
   once, as HOL4 closes them (use_new_assum and the distinctness
   and injectivity theorems of CASE_SIMP_CONV): without that the
   goals multiply with every split *)

let case_rws ty =
  let nm = fst(dest_type ty) in
  PAIR_EQ ::
  (try [distinctness nm] with Failure _ -> []) @
  (try [injectivity nm] with Failure _ -> []);;

let CASE_SPLIT_TAC gl =
  match scruts_of_goal gl with
    [] -> failwith "CASE_SPLIT_TAC"
  | t :: _ ->
      (CASES_ON_TAC t THEN
       TRY(ASM_REWRITE_TAC (case_rws (type_of t)))) gl;;

(* HOL4's every_case_tac: split the innermost scrutinee, reduce what
   can be reduced, and again.  Bounded, because a step that only
   adds an assumption is progress that a goal cannot measure. *)

(* MATCH_CONV leaves the guard of a pattern that binds variables
   (`if ?vs. vs = a then ... `), which is trivially true *)

let MATCH_TIDY_TAC =
  TRY(CONV_TAC(REDEPTH_CONV UNWIND_CONV)) THEN
  TRY(REWRITE_TAC[UNWIND_THM1; UNWIND_THM2; EXISTS_REFL;
                  NOT_CONS_NIL; CONS_11; NOT_SUC; SUC_INJ; PAIR_EQ;
                  distinctness "option"; injectivity "option"]);;

let EVERY_CASE_TAC =
  let step = ((CASE_SPLIT_TAC THEN TRY SAFE_MATCH_REDUCE_TAC) ORELSE
              SAFE_MATCH_REDUCE_TAC) THEN MATCH_TIDY_TAC in
  let rec go k gl =
    if k <= 0 then ALL_TAC gl
    else (try (step THEN go (k - 1)) gl
          with Failure _ -> ALL_TAC gl) in
  go 10;;

(* HOL4's rveq (var_eq_tac): use up the equations between variables
   that a case split leaves, and keep the others -- the equations
   that say what a function returned are the ones the proof needs *)

let VAR_EQ_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if is_var l || is_var r then SUBST_ALL_TAC th
    else failwith "VAR_EQ_TAC"));;

(* resolve a lemma whose hypothesis is a conjunction against the
   assumptions, as HOL4's imp_res_tac does *)

let RES2_TAC lemma =
  FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
    MP_TAC(MATCH_MP lemma (CONJ th1 th2))));;
