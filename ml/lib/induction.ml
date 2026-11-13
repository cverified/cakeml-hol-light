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
(*                                                                    *)
(* A family of functions that recurse through one another gets the    *)
(* theorem HOL4 gives it: a predicate for each of them, one           *)
(* antecedent per clause whose hypotheses are the calls to any of     *)
(* them, and a conclusion that is the conjunction of what each        *)
(* predicate says.  The proof is the same well-founded induction, on  *)
(* the sum of the arguments of the members, which is what such a      *)
(* definition is made on.                                            *)
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

(* the functions a definition defines, in the order its clauses
   bring them up, with the arity of each: one for a definition of
   one function and several for a family that recurses through
   itself *)

let definition_functions cls =
  rev (itlist (fun (_,h,args,_) l ->
                 if exists (fun (g,_) -> g = h) l then l
                 else (h,length args) :: l)
              (rev cls) []);;

(* the recursive calls of a right hand side, each with the
   function it calls and the guards that lead to it, outermost
   first and in the order they occur *)

let rec calls_of_any fs gs tm =
  if is_cond tm then
    let c,(a,b) = dest_cond tm in
    calls_of_any fs gs c @ calls_of_any fs (c::gs) a @
    calls_of_any fs (mk_neg c::gs) b
  else if is_abs tm then
    calls_of_any fs gs (snd(dest_abs tm))
  else if is_comb tm then
    let h,args = strip_comb tm in
    let inner = itlist (fun a l -> calls_of_any fs gs a @ l) args [] in
    if (try assoc h fs = length args with Failure _ -> false)
    then (h,rev gs,args) :: inner else inner
  else [];;

let calls_of f n gs tm =
  map (fun (_,gs,args) -> gs,args) (calls_of_any [f,n] gs tm);;

let definition_arity tm =
  let _,_,args,_ = hd (definition_cases tm) in length args;;

let is_recursive tm =
  let cls = definition_cases tm in
  let fs = definition_functions cls in
  exists (fun (_,_,_,r) -> calls_of_any fs [] r <> []) cls;;

(* the types of the arguments a function is applied to *)

let definition_argtys (f,n) =
  let tys,_ = splitlist dest_fun_ty (type_of f) in
  if length tys < n then failwith "definition_argtys"
  else fst (chop_list n tys);;

(* ------------------------------------------------------------------ *)
(* The statement, which is proved nothing.                            *)
(* ------------------------------------------------------------------ *)

(* the predicate of each function, the antecedents and the
   conclusion, with the predicates free: the theorem generalizes
   them at the end, so that the proof can name them.  A
   definition of one function has one predicate, called P as HOL4
   calls it; a family has P0, P1, ... and a conclusion that is
   the conjunction of what each of them says, which is the
   theorem HOL4 gives such a definition. *)

let induction_parts tm =
  let cls = definition_cases tm in
  let fs = definition_functions cls in
  if exists (fun (_,h,a,_) ->
               (try assoc h fs <> length a with Failure _ -> true))
            cls then
    failwith "induction_parts: a function of varying arity" else
  let avoid = frees tm in
  let rec preds i av fs =
    match fs with
      [] -> []
    | fn :: rest ->
        let ty = itlist mk_fun_ty (definition_argtys fn) bool_ty in
        let nm = if i < 0 then "P" else "P" ^ string_of_int i in
        let p = variant av (mk_var(nm,ty)) in
        p :: preds (if i < 0 then i else i + 1) (p :: av) rest in
  let ps = preds (if length fs = 1 then -1 else 0) avoid fs in
  let pred_of h = assoc h (zip (map fst fs) ps) in
  let antecedent (vs,h,args,r) =
    let hyps =
      itlist (fun (g,gs,as_) l ->
                let q = pred_of g in
                let h = if gs = [] then list_mk_comb(q,as_)
                        else mk_imp(list_mk_conj gs,
                                    list_mk_comb(q,as_)) in
                if exists (aconv h) l then l else h :: l)
             (calls_of_any fs [] r) [] in
    let conc = list_mk_comb(pred_of h,args) in
    list_mk_forall(vs,
      if hyps = [] then conc
      else mk_imp(list_mk_conj hyps,conc)) in
  let conclusion fn p =
    let tys = definition_argtys fn in
    let xs =
      rev (itlist (fun ty l -> variant (l @ ps @ avoid)
                                 (mk_var("x",ty)) :: l)
                  (rev tys) []) in
    list_mk_forall(xs,list_mk_comb(p,xs)) in
  ps,map antecedent cls,list_mk_conj (map2 conclusion fs ps);;

let induction_statement tm =
  let ps,ants,conc = induction_parts tm in
  list_mk_forall(ps,mk_imp(list_mk_conj ants,conc));;

(* ------------------------------------------------------------------ *)
(* The proof.                                                         *)
(* ------------------------------------------------------------------ *)

let tuple_of args = end_itlist (curry mk_pair) args;;

(* the tuple type of the arguments of each function, and the sum
   of those, which is what the relation of a definition of HOL
   Light is on: ml/lib/define.ml makes a family one function on
   that sum and the members of it by projection, and the relation
   HOL4 gives such a definition is on it too.  One function alone
   is the tuple of its arguments, which is what the sum of one
   type is. *)

let definition_argtypes tm =
  map (fun fn -> mk_tuple_type (definition_argtys fn))
      (definition_functions (definition_cases tm));;

let definition_argtype tm = mk_sumtype (definition_argtypes tm);;

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
   every recursive call, under the guards that lead to it, with
   the arguments of the call and of the clause in the part of the
   sum of the function they are of.  These are the conditions HOL
   Light's own machinery asks for to make the definition, which is
   why the definition has them in hand. *)

let termination_terms rel tm =
  let cls = definition_cases tm in
  let fs = definition_functions cls in
  let dtys = map (fun fn -> mk_tuple_type (definition_argtys fn)) fs in
  let idx f = index f (map fst fs) in
  itlist
    (fun (vs,h,args,r) l ->
       map (fun (g,gs,as_) ->
              let c = list_mk_comb(rel,
                        [mk_inj dtys (idx g) (tuple_of as_);
                         mk_inj dtys (idx h) (tuple_of args)]) in
              list_mk_forall(vs,
                if gs = [] then c else mk_imp(list_mk_conj gs,c)))
           (calls_of_any fs [] r) @ l)
    cls [];;

(* the components of a tuple variable, FST v, FST(SND v), ... *)

let rec tuple_components k t =
  if k <= 1 then [t]
  else mk_icomb(mk_const("FST",[]),t) ::
       tuple_components (k-1) (mk_icomb(mk_const("SND",[]),t));;

(* what a value of a sum is, which is how the induction below
   takes its predicate apart *)

let FORALL_SUM_THM = prove
 (`!P. (!s:A+B. P s) <=> (!x. P (INL x)) /\ (!y. P (INR y))`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN MATCH_MP_TAC sum_INDUCT THEN ASM_REWRITE_TAC[]]);;

let SUM_DISTINCT = CONJ (distinctness "sum")
  (prove(`!(a:B) (b:A). ~((INR a:A+B) = INL b)`,
         MESON_TAC[distinctness "sum"]));;

(* well-founded induction on the sum of the tuples of the
   arguments, written out in the arguments and in the predicates
   of the statement: HOL Light's WF_IND is on one argument, and a
   definition of the port is of up to eight arguments and of a
   family of functions.  The predicate says, of a value of the
   sum, what the predicate of the function whose part it is says
   of its arguments. *)

let sum_induction wf_th ps ns =
  let dtys =
    map2 (fun p n ->
            mk_tuple_type
              (fst (chop_list n
                      (fst (splitlist dest_fun_ty (type_of p))))))
         ps ns in
  let sty = mk_sumtype dtys in
  let rel = rand(concl wf_th) in
  let wf_th =
    INST_TYPE (type_match (fst(dest_fun_ty(type_of rel))) sty [])
              wf_th in
  let th = REWRITE_RULE[WF_IND] wf_th in
  let v = variant ps (mk_var("v",sty)) in
  let branch i p n =
    let a = variant (v::ps) (mk_var("a",el i dtys)) in
    mk_forall(a,mk_imp(mk_eq(v,mk_inj dtys i a),
                       list_mk_comb(p,tuple_components n a))) in
  let body =
    list_mk_conj (map2 (fun i (p,n) -> branch i p n)
                       (0--(length ps - 1)) (zip ps ns)) in
  (* in two passes: the equation that says which part of the sum
     a value is has to go before the tuple of the arguments is
     taken apart, or it is an equation of two tuples and no
     longer one of a variable *)
  REWRITE_RULE[FORALL_PAIR_THM; FST; SND]
    (REWRITE_RULE
       [FORALL_SUM_THM; injectivity "sum"; SUM_DISTINCT;
        FORALL_UNWIND_THM1; FORALL_UNWIND_THM2]
       (BETA_RULE (SPEC (mk_abs(v,body)) th)));;

(* the argument of the goal that a clause asks to be taken apart.
   A pattern of one function of a family says nothing about the
   arguments of another, so the patterns are looked up by the
   predicate of the goal, and a pattern of another type than the
   argument it stands against is not one that asks for anything. *)

let rec first_split pat arg =
  if is_var pat then None
  else if is_var arg then
    (if type_of pat = type_of arg then Some arg else None)
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
  let h,args = strip_comb c in
  let ps = try assoc h pats with Failure _ -> [] in
  match which_split ps args with
    None -> ALL_TAC gl
  | Some v ->
      (STRUCT_CASES_TAC (ISPEC v (cases_of (type_of v))) THEN
       SPLIT_PATTERNS_TAC pats) gl;;

(* the theorem, from a relation that is well founded and the
   termination conditions it makes true *)

let prove_induction wf_th tcs tm =
  let ps,ants,conc = induction_parts tm in
  let cls = definition_cases tm in
  let fs = definition_functions cls in
  let pats =
    map2 (fun p (f,_) ->
            p,map (fun (_,_,a,_) -> a)
                  (filter (fun (_,h,_,_) -> h = f) cls))
         ps fs in
  let wfind = sum_induction wf_th ps (map snd fs) in
  (* MATCH_MP_TAC looks at its theorem before it sees the goal, so
     the choice between it and MATCH_ACCEPT_TAC has to wait for
     the goal *)
  let use th g =
    (try MATCH_MP_TAC th with Failure _ -> MATCH_ACCEPT_TAC th) g in
  GENL ps
   (prove(mk_imp(list_mk_conj ants,conc),
      DISCH_THEN (fun ath ->
        let aths = CONJUNCTS ath in
        MATCH_MP_TAC wfind THEN
        REPEAT CONJ_TAC THEN
        REPEAT GEN_TAC THEN
        SPLIT_PATTERNS_TAC pats THEN
        DISCH_THEN (fun ih ->
          (* a condition whose conclusion matches but whose guard
             is the other branch's would be taken and then leave
             the goal standing, so every way of going on has to
             close the goal or count as not having worked *)
          let close t = use t THEN ASM_REWRITE_TAC[] THEN NO_TAC in
          let step i = MATCH_MP_TAC i THEN FIRST (map close tcs) in
          let attempt ath =
            use ath THEN
            REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
            FIRST (map step (CONJUNCTS ih)) in
          FIRST (map (fun a -> attempt a THEN NO_TAC) aths)))));;

(* the theorem, from a relation alone: the conditions are proved
   with the tactic that the definition would have used *)

let prove_induction_wf rel tac tm =
  let rel = fit_relation rel tm in
  let wf_th = prove(mk_icomb(mk_const("WF",[]),rel),WF_TAC) in
  let tcs = map (fun t -> prove(t,tac)) (termination_terms rel tm) in
  prove_induction wf_th tcs tm;;
