(* ================================================================== *)
(* The induction theorem of a recursive definition.                   *)
(*                                                                    *)
(* HOL4 gives a recursive definition with an induction principle      *)
(* (foo_ind), and its proofs use it (recInduct, ho_match_mp_tac       *)
(* foo_ind); HOL Light's recursion machinery gives the equations and  *)
(* nothing else.  This makes the theorem.                            *)
(*                                                                    *)
(* It is in two halves, and that is the point of it.  The statement   *)
(* is read off the clauses and is proved nothing: one antecedent per  *)
(* clause, with a hypothesis for every recursive call of that clause  *)
(* under the guards that lead to it.  The proof is well-founded       *)
(* induction on the relation the definition was made with.  An        *)
(* abstract that does not check the proofs takes the first half and   *)
(* assumes what the second would have proved, so what it says a file  *)
(* contains cannot drift from what a real load says: the statement    *)
(* comes from one place.                                             *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* The clauses.                                                       *)
(* ------------------------------------------------------------------ *)

(* a definition that HOL4 writes with a match is read as the clauses
   of its arms, which is what its induction theorem is about *)

let dest_match_term tm =
  let hop,margs = strip_comb tm in
  if is_const hop && fst(dest_const hop) = "_MATCH" &&
     length margs = 2
  then hd margs,dest_match_arms (last margs)
  else failwith "dest_match_term";;

let rec strip_pair tm =
  if is_pair tm then let a,b = dest_pair tm in a :: strip_pair b
  else [tm];;

(* the clauses as (variables, head, pattern arguments, right hand
   side).  The head is a variable in a term that is to be defined
   and a constant in a definition that was made; the variables are
   the free variables of the clause, in the order the arguments and
   then the body bring them up, whatever the quantifiers of the
   term look like. *)

let definition_cases tm =
  let cls = conjuncts(snd(strip_forall tm)) in
  let hd_of cl = fst(strip_comb(lhs(snd(strip_forall cl)))) in
  let fs = setify (map hd_of cls) in
  let raw = map (fun cl ->
                   let eq = snd(strip_forall cl) in
                   let l,r = dest_eq eq in
                   let h,args = strip_comb l in
                   h,args,r) cls in
  let rec expand (h,args,r) =
    try let scrut,arms = dest_match_term r in
        let ss = strip_pair scrut in
        itlist (fun (_,pat,bdy) l ->
                  let ps = strip_pair pat in
                  if length ps <> length ss then
                    failwith "expand" else
                  expand (h,map (subst (zip ps ss)) args,bdy) @ l)
               arms []
    with Failure _ -> [h,args,r] in
  let cls = itlist (fun c l -> expand c @ l) raw [] in
  map (fun (h,args,r) ->
         let order = rev_itlist (fun a l -> l @ subtract (frees a) l)
                                (args @ [r]) [] in
         let vs = filter (fun v -> not (mem v fs)) order in
         vs,h,args,r)
      cls;;

(* the recursive calls of a right hand side, each with the guards
   that lead to it, outermost first and in the order they occur *)

let rec calls_of f n gs tm =
  if is_cond tm then
    let c,(a,b) = dest_cond tm in
    calls_of f n gs c @ calls_of f n (c::gs) a @
    calls_of f n (mk_neg c::gs) b
  else if is_abs tm then
    calls_of f n gs (snd(dest_abs tm))
  else if is_comb tm then
    let h,args = strip_comb tm in
    let inner = itlist (fun a l -> calls_of f n gs a @ l) args [] in
    if h = f && length args = n then (rev gs,args) :: inner
    else inner
  else [];;

let definition_arity tm =
  let _,_,args,_ = hd (definition_cases tm) in length args;;

let is_recursive tm =
  let cls = definition_cases tm in
  let _,f,args,_ = hd cls in
  let n = length args in
  exists (fun (_,_,_,r) -> calls_of f n [] r <> []) cls;;

(* ------------------------------------------------------------------ *)
(* The statement, which is proved nothing.                            *)
(* ------------------------------------------------------------------ *)

(* the predicate, the antecedents and the conclusion, with the
   predicate free: the theorem generalizes it at the end, so that
   the proof can name it *)

let induction_parts tm =
  let cls = definition_cases tm in
  let _,f,args0,_ = hd cls in
  let n = length args0 in
  if exists (fun (_,g,a,_) -> g <> f || length a <> n) cls then
    failwith "induction_parts: not one function of one arity" else
  let tys = map type_of args0 in
  let avoid = frees tm in
  let p = variant avoid (mk_var("P",itlist mk_fun_ty tys bool_ty)) in
  let antecedent (vs,_,args,r) =
    let hyps =
      itlist (fun (gs,as_) l ->
                let h = if gs = [] then list_mk_comb(p,as_)
                        else mk_imp(list_mk_conj gs,
                                    list_mk_comb(p,as_)) in
                if exists (aconv h) l then l else h :: l)
             (calls_of f n [] r) [] in
    let conc = list_mk_comb(p,args) in
    list_mk_forall(vs,
      if hyps = [] then conc
      else mk_imp(list_mk_conj hyps,conc)) in
  let xs =
    rev (itlist (fun ty l -> variant (l @ p :: avoid)
                               (mk_var("x",ty)) :: l)
                (rev tys) []) in
  p,map antecedent cls,list_mk_forall(xs,list_mk_comb(p,xs));;

let induction_statement tm =
  let p,ants,conc = induction_parts tm in
  list_mk_forall([p],mk_imp(list_mk_conj ants,conc));;

(* ------------------------------------------------------------------ *)
(* The proof.                                                         *)
(* ------------------------------------------------------------------ *)

let tuple_of args = end_itlist (curry mk_pair) args;;

(* the type of the tuple of the arguments, which is what the
   relation of a definition of HOL Light is on *)

let definition_argtype tm =
  let _,_,args,_ = hd (definition_cases tm) in
  end_itlist (fun ty t -> mk_type("prod",[ty;t])) (map type_of args);;

(* a relation that was written on its own has type variables of its
   own, and the definition is what says what they are.  A redex
   left in it is reduced by the rewriting that the proof does and
   not by the terms the goals are built from, and then the two no
   longer match, so it is reduced here, once. *)

let beta_normalize tm =
  try rhs(concl(DEPTH_CONV BETA_CONV tm)) with Failure _ -> tm;;

let fit_relation rel tm =
  let vty = definition_argtype tm in
  beta_normalize
    (inst (type_match (fst(dest_fun_ty(type_of rel))) vty []) rel);;

(* the termination conditions, as the relation sees them: one for
   every recursive call, under the guards that lead to it.  These
   are the conditions HOL Light's own machinery asks for to make
   the definition, which is why the definition has them in hand. *)

let termination_terms rel tm =
  let cls = definition_cases tm in
  let _,f,args0,_ = hd cls in
  let n = length args0 in
  itlist
    (fun (vs,_,args,r) l ->
       map (fun (gs,as_) ->
              let c = list_mk_comb(rel,[tuple_of as_; tuple_of args]) in
              list_mk_forall(vs,
                if gs = [] then c else mk_imp(list_mk_conj gs,c)))
           (calls_of f n [] r) @ l)
    cls [];;

(* the components of a tuple variable, FST v, FST(SND v), ... *)

let rec tuple_components k t =
  if k <= 1 then [t]
  else mk_icomb(mk_const("FST",[]),t) ::
       tuple_components (k-1) (mk_icomb(mk_const("SND",[]),t));;

(* well-founded induction on the tuple of the arguments, written
   out in the arguments and in the predicate of the statement:
   HOL Light's WF_IND is on one argument, and a function of the
   port takes up to eight *)

let curried_wf_induction wf_th p n =
  let tys = fst(splitlist dest_fun_ty (type_of p)) in
  let vty = end_itlist (fun ty t -> mk_type("prod",[ty;t])) tys in
  let rel = rand(concl wf_th) in
  let wf_th =
    INST_TYPE (type_match (fst(dest_fun_ty(type_of rel))) vty [])
              wf_th in
  let th = REWRITE_RULE[FORALL_PAIR_THM]
             (REWRITE_RULE[WF_IND] wf_th) in
  let pv,_ = dest_forall(concl th) in
  let v = variant [p] (mk_var("v",fst(dest_fun_ty(type_of pv)))) in
  REWRITE_RULE[FST; SND]
    (BETA_RULE (SPEC (mk_abs(v,list_mk_comb(p,tuple_components n v)))
                     th));;

(* the argument of the goal that a clause asks to be taken apart *)

let rec first_split pat arg =
  if is_var pat then None
  else if is_var arg then Some arg
  else
    let hp,ap = strip_comb pat and ha,aa = strip_comb arg in
    if hp <> ha || length ap <> length aa then None
    else first_splits ap aa
and first_splits pats args =
  match pats,args with
    [],[] -> None
  | p::ps,a::as_ ->
      (match first_split p a with
         None -> first_splits ps as_
       | some -> some)
  | _ -> None;;

let rec which_split pats args =
  match pats with
    [] -> None
  | ps::rest ->
      (match first_splits ps args with
         None -> which_split rest args
       | some -> some);;

let rec SPLIT_PATTERNS_TAC pats (asl,w as gl) =
  let c = if is_imp w && not (is_neg w) then snd(dest_imp w) else w in
  match which_split pats (snd(strip_comb c)) with
    None -> ALL_TAC gl
  | Some v ->
      (STRUCT_CASES_TAC (ISPEC v (cases_of (type_of v))) THEN
       SPLIT_PATTERNS_TAC pats) gl;;

(* the theorem, from a relation that is well founded and the
   termination conditions it makes true *)

let prove_induction wf_th tcs tm =
  let p,ants,conc = induction_parts tm in
  let cls = definition_cases tm in
  let n = length (let _,_,a,_ = hd cls in a) in
  let pats = map (fun (_,_,a,_) -> a) cls in
  let wfind = curried_wf_induction wf_th p n in
  (* MATCH_MP_TAC looks at its theorem before it sees the goal, so
     the choice between it and MATCH_ACCEPT_TAC has to wait for
     the goal *)
  let use th g =
    (try MATCH_MP_TAC th with Failure _ -> MATCH_ACCEPT_TAC th) g in
  GEN p
   (prove(mk_imp(list_mk_conj ants,conc),
      DISCH_THEN (fun ath ->
        let aths = CONJUNCTS ath in
        MATCH_MP_TAC wfind THEN
        REPEAT GEN_TAC THEN
        SPLIT_PATTERNS_TAC pats THEN
        DISCH_THEN (fun ih ->
          (* a condition whose conclusion matches but whose guard
             is the other branch's would be taken and then leave
             the goal standing, so every way of going on has to
             close the goal or count as not having worked *)
          let close t = use t THEN ASM_REWRITE_TAC[] THEN NO_TAC in
          let attempt ath =
            use ath THEN
            REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
            MATCH_MP_TAC ih THEN
            FIRST (map close tcs) in
          FIRST (map (fun a -> attempt a THEN NO_TAC) aths)))));;

(* the theorem, from a relation alone: the conditions are proved
   with the tactic that the definition would have used *)

let prove_induction_wf rel tac tm =
  let rel = fit_relation rel tm in
  let wf_th = prove(mk_icomb(mk_const("WF",[]),rel),WF_TAC) in
  let tcs = map (fun t -> prove(t,tac)) (termination_terms rel tm) in
  prove_induction wf_th tcs tm;;
