(* ================================================================== *)
(*  HOL4's Definition for HOL Light.                                  *)
(*                                                                    *)
(*  cake_define handles what HOL4's Define handles, as far as CakeML  *)
(*  needs                                                             *)
(*  it:                                                               *)
(*                                                                    *)
(*    not recursive -> new_definition                                 *)
(*    primitive recursive -> new_recursive_definition                 *)
(*    otherwise recursive -> define                                   *)
(*    mutually recursive -> encoded in a sum type                     *)
(*                                                                    *)
(*  For definitions whose termination HOL Light cannot guess there are*)
(*                                                                    *)
(*    cake_define_wf `relation` `clauses`                             *)
(*    cake_define_tac (`relation`,tactic) `clauses`                   *)
(*                                                                    *)
(*  where the relation is the one of HOL4's WF_REL_TAC. HOL4's        *)
(*  `measure f` is `MEASURE f`, `inv_image R f` is `\x y. R (f x) (f  *)
(*  y)`                                                               *)
(*  and `R1 LEX R2` is `\(x1,y1) (x2,y2). R1 x1 x2 \/ x1 = x2 /\ R2 y1*)
(*  y2`,                                                              *)
(*  which are the HOL Light forms of the same notions (see WF_MEASURE,*)
(*  WF_MEASURE_GEN and WF_LEX). For mutually recursive functions the  *)
(*  relation is one on the sum of the tupled arguments, as in HOL4.   *)
(* ================================================================== *)

(* with cake_debug set, a failing definition is written to
   cakeml/tmp/debug.txt *)

let cake_debug = ref false;;

let cake_log s =
  let ch = open_out_gen [Open_append; Open_creat] 0o644
             "/home/freek/claude/hol-light/cakeml/tmp/debug.txt" in
  output_string ch s; output_string ch "\n"; close_out ch;;

let cake_log_term tm =
  cake_log (string_of_term tm);;

(* ------------------------------------------------------------------ *)
(* Tuples and sums.                                                   *)
(* ------------------------------------------------------------------ *)

let mk_tuple_type tys =
  end_itlist (fun ty1 ty2 -> mk_type("prod",[ty1;ty2])) tys;;

let mk_tuple tms = end_itlist (curry mk_pair) tms;;

let mk_sum_const name ty =
  let c = mk_const(name,[]) in
  inst (type_match (type_of c) ty []) c;;

let rec mk_sumtype tys =
  match tys with
    [ty] -> ty
  | ty::tys -> mk_type("sum",[ty; mk_sumtype tys])
  | [] -> failwith "mk_sumtype";;

(* mk_inj tys i tm : the term tm of type el i tys, in the sum of tys *)

let rec mk_inj tys i tm =
  match tys with
    [_] -> tm
  | ty::tys ->
      let sty = mk_sumtype tys in
      let sumty = mk_type("sum",[ty;sty]) in
      if i = 0 then mk_comb(mk_sum_const "INL" (mk_fun_ty ty sumty),tm)
      else mk_comb(mk_sum_const "INR" (mk_fun_ty sty sumty),
                   mk_inj tys (i-1) tm)
  | [] -> failwith "mk_inj";;

(* mk_proj tys i tm : the el i tys part of tm, which is in the sum *)

let rec mk_proj tys i tm =
  match tys with
    [_] -> tm
  | ty::tys ->
      let sty = mk_sumtype tys in
      let sumty = mk_type("sum",[ty;sty]) in
      if i = 0 then mk_comb(mk_sum_const "OUTL" (mk_fun_ty sumty ty),tm)
      else mk_proj tys (i-1)
             (mk_comb(mk_sum_const "OUTR" (mk_fun_ty sumty sty),tm))
  | [] -> failwith "mk_proj";;

(* ------------------------------------------------------------------ *)
(* The clauses of a definition and the functions it defines.          *)
(* ------------------------------------------------------------------ *)

let definition_clauses tm =
  map (fun cl ->
        let bod = snd(strip_forall cl) in
        let l,r = dest_eq bod in
        let f,args = strip_comb l in
        f,args,r)
      (conjuncts(snd(strip_forall tm)));;

(* the names of the functions that the definition being made
   defines: an auxiliary that a strategy invents may not take one
   of them, not even where the strategy only sees a part of the
   block (presLang's flat_to_display_list is the name that the
   map of flat_to_display would have got) *)

let the_defining = ref ([]:string list);;

let definition_heads tm =
  itlist (fun (f,_,_) l -> if mem f l then l else f::l)
         (definition_clauses tm) [];;

(* universally quantify a clause over its variables *)

let close_clause fs cl =
  let bod = snd(strip_forall cl) in
  list_mk_forall(subtract (frees bod) fs,bod);;

let beta_normalize tm =
  try rhs(concl(TOP_DEPTH_CONV BETA_CONV tm)) with Failure _ -> tm;;

(* ------------------------------------------------------------------ *)
(* Discharging the side conditions of an existence theorem.           *)
(* ------------------------------------------------------------------ *)

(* the tactic that proves that a termination relation is wellfounded *)

let WF_TAC =
  REPEAT(MATCH_MP_TAC WF_inv_image ORELSE MATCH_MP_TAC WF_LEX_ALT ORELSE
         CONJ_TAC) THEN
  REWRITE_TAC[WF_MEASURE; WF_num];;

(* the size functions and lemmas, which the tactic that proves the
   termination conditions uses; they are added by define_size below *)

let the_size_thms = ref ([]:(string * (thm list * thm list)) list);;

let all_size_thms () =
  itlist (fun (_,(a,b)) l -> a @ b @ l) (!the_size_thms) [];;

let all_size_fns () =
  map (fun th -> fst(strip_comb(lhs(snd(strip_forall(concl th))))))
      (itlist (fun (_,(a,_)) l -> a @ l) (!the_size_thms) []);;

(* MEM x l gives f x < list_size f l for the size function of the
   type of x; size_fn_of_type is defined further down, so it is
   reached through a reference *)

let size_fn_of_type_fwd =
  ref ((fun ty -> failwith "size_fn_of_type"):hol_type->term);;

(* The measure that HOL4 gives, with its size functions: HOL4
   numbers the size functions of the types of a family in another
   order than HOL Light does (of closLang's exp, HOL4's exp1_size
   is the one of a (num # exp) list and ours is the one of an exp
   list), so the port leaves such a name a variable rather than
   write down the size function of another type.  The type of the
   variable says which size function it is.  A relation that still
   has a free variable in it is of no use: the goals that it gives
   cannot be proved. *)

let fix_measure rel =
  let fv = frees rel in
  if fv = [] then Some rel else
  try
    let ins =
      map (fun v ->
             let nm = fst(dest_var v) in
             let n = String.length nm in
             if n <= 5 || String.sub nm (n - 5) 5 <> "_size"
             then failwith "fix_measure" else
             let ty,ran = dest_fun_ty(type_of v) in
             (* the relation is parsed on its own, so a type that
                the clauses would fix can still be a variable
                here, and the size function of a type variable
                measures nothing *)
             if ran <> `:num` || tyvars ty <> []
             then failwith "fix_measure" else
             (!size_fn_of_type_fwd) ty,v)
          fv in
    let rel' = vsubst ins rel in
    if frees rel' = [] then Some rel' else None
  with Failure _ -> None;;

(* the members of the front of a list and its last element are
   members of the list: a definition that recurses on BUTLAST and
   LAST (bvi_let$compile_sing) asks for their size *)

let MEM_BUTLAST = prove
 (`!x l. MEM x (BUTLAST l) ==> MEM x l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[BUTLAST; MEM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MEM] THEN
  ASM_MESON_TAC[]);;

let MEM_LAST_NONNIL = prove
 (`!l. ~(l = []) ==> MEM (LAST l) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LAST; MEM; NOT_CONS_NIL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MEM] THEN
  ASM_MESON_TAC[]);;

(* the facts about BUTLAST and LAST that the assumptions of a
   termination goal give, so that MEM_SIZE_TAC can use them *)

let LIST_MEM_TAC (asl,w as gl) =
  let news =
    mapfilter (fun (_,th) ->
                 try MATCH_MP MEM_BUTLAST th
                 with Failure _ -> MATCH_MP MEM_LAST_NONNIL th)
              asl in
  let news = filter (fun th ->
                       not (exists (fun (_,a) -> concl a = concl th)
                                   asl))
                    news in
  (if news = [] then ALL_TAC else MAP_EVERY ASSUME_TAC news) gl;;

(* every bound variable of a termination goal gets a name of its
   own: HOL Light's STRIP_TAC takes an existential assumption
   apart under the name that it has, and the goal of a definition
   by cases has assumptions like (?op xs. Op op xs = expr) whose
   names are the variables of the clause, where CHOOSE fails *)

let FRESH_BOUND_CONV tm =
  (* the variables to keep away from are the free ones and the
     ones that the binders above this place have taken: two
     binders beside each other may have the same name *)
  let rec go avoid t =
    match t with
      Comb(s,u) -> mk_comb(go avoid s,go avoid u)
    | Abs(v,b) ->
        let v1 = variant avoid v in
        mk_abs(v1,go (v1 :: avoid) (vsubst [v1,v] b))
    | _ -> t in
  let tm1 = go (frees tm) tm in
  if tm1 = tm then REFL tm else ALPHA tm tm1;;

let MEM_SIZE_TAC (asl,w as gl) =
  let mems =
    mapfilter (fun (_,th) ->
                 let tm = concl th in
                 if is_comb tm && is_comb(rator tm) &&
                    name_of(rator(rator tm)) = "MEM"
                 then th else fail())
              asl in
  let facts =
    mapfilter
      (fun th ->
         let x = rand(rator(concl th)) in
         SPEC ((!size_fn_of_type_fwd) (type_of x))
              (MATCH_MP MEM_list_size_ALT th))
      mems in
  MAP_EVERY MP_TAC facts gl;;

(* the assumptions that the equations between the assumptions
   give: an assumption i < LENGTH xs and an assumption
   LENGTH xs = LENGTH ys give i < LENGTH ys, which is what the
   fact about the other list asks for *)

let EQ_COPY_TAC (asl,w as gl) =
  let asms = map snd asl in
  let eqs = filter (fun th -> let c = concl th in
                              is_eq c && type_of(lhs c) <> bool_ty)
                   asms in
  let news = ref [] in
  do_list
    (fun e ->
       do_list
         (fun th ->
            (* an equation is not rewritten with another one: the
               copies are for the facts about the sides *)
            if concl th = concl e || is_eq (concl th) ||
               length (!news) > 12 then () else
            let th' = try ONCE_REWRITE_RULE [e] th
                      with Failure _ -> th in
            let c = concl th' in
            if c = concl th || c = `T` ||
               exists (fun t -> concl t = c) asms ||
               exists (fun t -> concl t = c) (!news)
            then () else news := th' :: (!news))
         asms)
    eqs;
  (if !news = [] then ALL_TAC else MAP_EVERY ASSUME_TAC (!news)) gl;;

(* the facts about division and remainder in the goal *)

let DIV_FACTS_TAC (asl,w as gl) =
  let tms =
    find_terms (fun t -> is_comb t && is_comb(rator t) &&
                         is_const(rator(rator t)) &&
                         (name_of(rator(rator t)) = "DIV" ||
                          name_of(rator(rator t)) = "MOD")) w in
  let facts =
    itlist (fun t l ->
              let a = rand(rator t) and k = rand t in
              let op = name_of(rator(rator t)) in
              (if op = "DIV" then
                 [SPECL [a;k] DIV_LE;
                  SPECL [a;k] DIV_LT_SELF]
               else [SPECL [a;k] MOD_LE;
                     SPECL [a;k] MOD_LT_SELF]) @ l)
           (setify tms) [] in
  MAP_EVERY MP_TAC facts gl;;

(* the equations of the pattern that a match provides, as
   substitutions: the goal then talks about the subterms *)

let SUBST_VAR_TAC (asl,w as gl) =
  let eqs =
    mapfilter (fun (_,th) ->
                 let l,r = dest_eq(concl th) in
                 if is_var r && not (vfree_in r l) then SYM th
                 else if is_var l && not (vfree_in l r) then th
                 else fail())
              asl in
  (if eqs = [] then ALL_TAC
   else MAP_EVERY (fun th -> TRY(SUBST_ALL_TAC th)) eqs) gl;;

(* the tactic that is tried on the termination conditions *)

(* the lemmas that the termination proofs may need; a ported file can
   add the ones that its definitions need *)

let cake_term_lemmas =
  ref [list_size; pair_size; option_size; num_size; bool_size;
       DIV2; DIV2_LT; list_size_DROP; list_size_TAKE;
       list_size_APPEND; list_size_REVERSE;
       LENGTH_TAKE_LE; LENGTH_DROP_LE];;

(* the lemmas that state a fact about a subterm of a termination
   goal (and not an equation, so that rewriting cannot use them);
   they are instantiated by matching and added to the assumptions *)

let cake_term_facts =
  ref ([EL_list_size; MEM_ZIP_FST; MEM_ZIP_SND]:thm list);;

let FACTS_TAC (asl,w as gl) =
  let sel bod =
    let c = if is_imp bod then rand bod else bod in
    lhand c in
  let tms =
    itlist (fun t l -> union (find_terms (fun _ -> true) t) l)
           (w :: map (concl o snd) asl) [] in
  (* the constants of the goal and of its assumptions: a fact
     whose own are not among them cannot match anything, and
     there is a fact for every datatype of the port *)
  let gcs = setify (map (fst o dest_const) (filter is_const tms)) in
  let instances th =
    let avs,bod = strip_forall(concl th) in
    let key = sel bod in
    let kcs = map (fst o dest_const)
                  (find_terms is_const key) in
    if not (subset (setify kcs) gcs) then [] else
    let full t =
      try let _,tmin,tyin = term_match [] key t in
          (* the variables of the fact are the ones that the
             types of the match instantiate, and a variable that
             the match leaves as it is does not stand in the
             instantiation at all (it is determined where the
             term has it) *)
          let vs = map (inst tyin) avs in
          forall (fun v -> mem v (map snd tmin) || vfree_in v t)
                 vs
      with Failure _ -> false in
    mapfilter (fun t -> PART_MATCH sel th t) (filter full tms) in
  (* a fact that still has variables of its own gets the
     instance that the goal asks for *)
  let spec th =
    if fst(strip_forall(concl th)) = [] then [th]
    else match instances th with [] -> [th] | l -> l in
  let facts = itlist (fun th l -> instances th @ l)
                     (!cake_term_facts) [] in
  (* the same, for a fact whose antecedent an assumption of the
     goal gives (HOL4's imp_res_tac); the equation of a match is
     the other way round, so it is tried both ways *)
  let facts =
    facts @
    itlist (fun th l ->
              flat (mapfilter (fun (_,a) -> spec (MATCH_MP th a))
                              asl) @
              flat (mapfilter (fun (_,a) -> spec (MATCH_MP th (SYM a)))
                              asl) @ l)
           (!cake_term_facts) [] in
  (* a fact whose antecedent is a conjunction that two of the
     assumptions give *)
  let facts =
    facts @
    itlist (fun th l ->
              let bod = snd(strip_forall(concl th)) in
              if not (is_imp bod && is_conj (lhand bod)) then l else
              itlist (fun (_,a) k ->
                        flat (mapfilter
                                (fun (_,b) ->
                                   spec (MATCH_MP th (CONJ a b)))
                                asl) @ k)
                     asl l)
           (!cake_term_facts) [] in
  (if facts = [] then ALL_TAC else MAP_EVERY MP_TAC facts) gl;;

(* when a termination proof does not close, the goal is logged *)

let LOG_TAC (asl,w) =
  cake_log ("unsolved termination goal of " ^
            (if !the_defining = [] then "?"
             else end_itlist (fun a b -> a ^ ", " ^ b)
                             (!the_defining)) ^ ":");
  cake_log_term w;
  do_list (fun (_,th) -> cake_log ("  asm: " ^ string_of_term(concl
    th)))
          asl;
  failwith "LOG_TAC";;

let rec TERM_TAC g =
  let _,w = g in
  if (try name_of(fst(strip_comb(snd(strip_forall w)))) =
             "admissible"
      with Failure _ -> false)
  then ADMISS_TERM_TAC g else SIZE_TERM_TAC g

and SIZE_TERM_TAC g =
  (* PAIR_EQ takes the equation of the pattern of a match on a
     tuple apart, so that SUBST_VAR_TAC can use it (balanced_map's
     link matches on the pair (l,r), and its condition says
     Bin ...,Bin ... = l,r) *)
  (REWRITE_TAC[MEASURE; LEX; inv_image; FORALL_PAIR_THM; PAIR_EQ;
               o_THM; FST; SND] THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   CONV_TAC FRESH_BOUND_CONV THEN
   REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   REWRITE_TAC(all_size_thms()) THEN
   RULE_ASSUM_TAC(REWRITE_RULE(LENGTH_EQ_NIL::all_size_thms())) THEN
   LIST_MEM_TAC THEN
   EQ_COPY_TAC THEN
   MEM_SIZE_TAC THEN DIV_FACTS_TAC THEN
   (* a fact may make a subterm appear that another fact is about *)
   FACTS_TAC THEN FACTS_TAC THEN
   REWRITE_TAC(I_THM::all_size_thms() @ (!cake_term_lemmas)) THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   (* the facts are assumptions now, and ARITH only sees what the
      size theorems have taken apart *)
   RULE_ASSUM_TAC(REWRITE_RULE(I_THM::all_size_thms() @
                               (!cake_term_lemmas))) THEN
   (ASM_ARITH_TAC ORELSE
    (ASM_SIMP_TAC(all_size_thms() @ (!cake_term_lemmas)) THEN
     ASM_ARITH_TAC) ORELSE
    (if !cake_debug then LOG_TAC else NO_TAC))) g

and ADMISS_TERM_TAC g =
  (PURE_REWRITE_TAC[admissible] THEN
   REWRITE_TAC[FORALL_PAIR_THM] THEN
   CONV_TAC FRESH_BOUND_CONV THEN
   REPEAT GEN_TAC THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   (AGREE_TAC ORELSE (COND_SPLIT_TAC THEN AGREE_TAC))) g

(* the conditions of the conditionals of a goal that no binder
   of it binds: the measure of a recursive call under one of
   them only goes down when the condition says so, and the
   conditional is inside the arm of a match, where
   COND_CASES_TAC cannot lift it out *)

and COND_SPLIT_TAC (asl,w as gl) =
  let conds =
    setify (mapfilter (fun t ->
                         let c,_ = dest_cond t in
                         if subset (frees c) (frees w) then c
                         else fail())
                      (find_terms is_cond w)) in
  let conds = if length conds <= 3 then conds
              else fst(chop_list 3 conds) in
  if conds = [] then failwith "COND_SPLIT_TAC" else
  MAP_EVERY (fun c -> ASM_CASES_TAC c THEN ASM_REWRITE_TAC[])
            conds gl

(* the assumption of an admissibility goal says that the two
   functions agree below the measure; the subterms f x of the goal
   for which that can be shown are rewritten with it *)

and AGREE_TAC (asl,w as gl) =
  let agree =
    mapfilter
      (fun (_,th) ->
         let zs,bod = strip_forall(concl th) in
         let _,con = dest_imp bod in
         let l,r = dest_eq con in
         if zs <> [] && is_comb l && is_comb r &&
            is_var(rator l) && is_var(rator r) &&
            rator l <> rator r then th else fail())
      asl in
  (* the assumption is about a tuple of variables where the
     argument of the function is a tuple, so the instance is
     found by matching *)
  let use th =
    let f = rator(lhs(rand(snd(strip_forall(concl th))))) in
    let args =
      setify(map rand (find_terms (fun t -> is_comb t &&
                                            rator t = f) w)) in
    mapfilter (fun a ->
                 let ith = PART_MATCH (lhs o rand) th (mk_comb(f,a))
                   in
                 (* the assumptions of the goal are what says that
                    the measure goes down (the condition of a
                    conditional that the goal was split on) *)
                 let sub = itlist (fun (_,b) t -> mk_imp(concl b,t))
                                  asl (lhand(concl ith)) in
                 MP ith (rev_itlist (fun (_,b) t -> MP t b) asl
                                    (prove(sub,TERM_TAC))))
              args in
  let eqs = itlist (fun th l -> use th @ l) agree [] in
  if eqs = [] then failwith "AGREE_TAC" else
  (REWRITE_TAC eqs THEN REWRITE_TAC[]) gl;;

(* why the termination conditions could not be discharged: the
   kind of the condition that failed says more than the "tryfind"
   of the strategy that gives up *)

let the_cond_why = ref "";;

(* the strategy that cake_define is in, which a cheat that is a
   timeout reports: the budget ran out in that one *)

let the_strategy = ref "";;

let cond_kind h =
  let b = if is_exists h then snd(dest_exists h) else h in
  let c = if is_conj b then rand b else b in
  try let hd = fst(strip_comb(snd(strip_forall c))) in
      if is_const hd then name_of hd else "measure"
  with Failure _ -> "?";;

let discharge_conditions (rel,tac) th =
  itlist
    (fun h th ->
       let gtac =
         if is_exists h then
           let v,_ = dest_exists h in
           let rel' = inst (type_match (type_of rel) (type_of v) []) rel
             in
           (* the size functions of the relation of HOL4, which
              only its type says *)
           let rel' = match fix_measure rel' with
                        Some r -> r
                      | None -> failwith "free in the relation" in
           EXISTS_TAC rel' THEN CONJ_TAC THENL [WF_TAC; tac]
         else tac in
       let hth =
         try prove(h,gtac)
         with Failure s ->
           (the_cond_why := cond_kind h;
            if !cake_debug then
              (cake_log ("cannot prove the condition of " ^
                         (if !the_defining = [] then "?"
                          else end_itlist (fun a b -> a ^ ", " ^ b)
                                          (!the_defining)) ^
                         " (" ^ s ^ ") with the relation");
               cake_log_term rel;
               cake_log "for the condition:";
               cake_log_term h);
            failwith s) in
       PROVE_HYP hth th)
    (hyp th) th;;

(* ------------------------------------------------------------------ *)
(* Taking paired lambdas apart.                                       *)
(*                                                                    *)
(* HOL Light's machinery for the admissibility of a recursion loses   *)
(* the                                                                *)
(* connection between the pattern of a paired lambda and the argument *)
(* it                                                                 *)
(* is applied to, so that for instance                                *)
(*                                                                    *)
(*   nsMap f (Bind v m) = Bind (MAP (\(n,x). (n,f x)) v)              *)
(*                             (MAP (\(mn,e). (mn,nsMap f e)) m)      *)
(*                                                                    *)
(* gets an unprovable termination condition. Therefore such a         *)
(* definition                                                         *)
(* is made with \p. ... FST p ... SND p ... instead, and the          *)
(* definition as                                                      *)
(* it was given is then derived from it.                              *)
(* ------------------------------------------------------------------ *)

let mk_fst tm =
  match snd(dest_type(type_of tm)) with
    [ty1;ty2] -> mk_comb(mk_const("FST",[ty1,aty; ty2,bty]),tm)
  | _ -> failwith "mk_fst";;

let mk_snd tm =
  match snd(dest_type(type_of tm)) with
    [ty1;ty2] -> mk_comb(mk_const("SND",[ty1,aty; ty2,bty]),tm)
  | _ -> failwith "mk_snd";;

let rec depair tm =
  if is_abs tm then
    let v,b = dest_abs tm in mk_abs(v,depair b)
  else if is_gabs tm then
    let pat,bod = dest_gabs tm in
    let bod = depair bod in
    let p = variant (frees bod) (mk_var("p",type_of pat)) in
    let rec sub pat tm =
      if is_var pat then [tm,pat]
      else let a,b = dest_pair pat in
           sub a (mk_fst tm) @ sub b (mk_snd tm) in
    mk_abs(p,vsubst (sub pat p) bod)
  else
    match tm with
      Comb(s,t) -> mk_comb(depair s,depair t)
    | _ -> tm;;

let DEPAIR_CONV tm =
  let tm' = depair tm in
  if tm' = tm then failwith "DEPAIR_CONV: no change" else
  prove(mk_eq(tm,tm'),
        REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN
        CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
        REWRITE_TAC[FST; SND]);;

let DEPAIR_TAC = CONV_TAC(ONCE_DEPTH_CONV DEPAIR_CONV);;

(* ------------------------------------------------------------------ *)
(* Putting the recursive calls under a MAP.                           *)
(* ------------------------------------------------------------------ *)

let mapify fs tm =
  let itl op b l =
    let v1 = mk_var("b",bool_ty) and v2 = mk_var("a",bool_ty) in
    list_mk_comb(mk_mconst("ITLIST",
      mk_fun_ty (mk_fun_ty bool_ty (mk_fun_ty bool_ty bool_ty))
        (mk_fun_ty (type_of l) (mk_fun_ty bool_ty bool_ty))),
      [mk_abs(v1,mk_abs(v2,mk_binop op v1 v2)); l; b]) in
  let rec go tm =
    match tm with
      Comb(Comb(Const("ALL",_),f),l)
        when exists (fun g -> vfree_in g f) fs ->
          let f = go f and l = go l in
          let mty = mk_fun_ty (type_of f)
                      (mk_fun_ty (type_of l)
                         (mk_type("list",[bool_ty]))) in
          itl `(/\)` `T` (list_mk_comb(mk_mconst("MAP",mty),[f;l]))
    | Comb(Comb(Const("EX",_),f),l)
        when exists (fun g -> vfree_in g f) fs ->
          let f = go f and l = go l in
          let mty = mk_fun_ty (type_of f)
                      (mk_fun_ty (type_of l)
                         (mk_type("list",[bool_ty]))) in
          itl `(\/)` `F` (list_mk_comb(mk_mconst("MAP",mty),[f;l]))
    | Comb(Const("!",_),Abs(v,bod))
        when is_imp bod &&
             (let p = lhand bod in
              is_comb p && is_comb(rator p) &&
              (name_of(rator(rator p)) = "MEM" ||
               (name_of(rator(rator p)) = "IN" &&
                is_comb(rand p) &&
                name_of(rator(rand p)) = "set_of_list"))) &&
             exists (fun g -> vfree_in g (rand bod)) fs ->
          let p = lhand bod in
          let l = if name_of(rator(rator p)) = "MEM" then rand p
                  else rand(rand p) in
          let f = mk_abs(v,go (rand bod)) in
          go (list_mk_comb(mk_mconst("ALL",
                mk_fun_ty (type_of f)
                  (mk_fun_ty (type_of l) bool_ty)),[f;l]))
    | Comb(s,t) -> mk_comb(go s,go t)
    | Abs(v,b) -> mk_abs(v,go b)
    | _ -> tm in
  go tm;;

let MAPIFY_CONV fs tm =
  let tm' = mapify fs tm in
  if tm' = tm then failwith "MAPIFY_CONV: no change" else
  prove(mk_eq(tm,tm'),
        REWRITE_TAC[ALL_MAPIFY; EX_MAPIFY; ALL_MEM;
                    IN_SET_OF_LIST; ETA_AX]);;

(* ------------------------------------------------------------------ *)
(* Definition of one function, with a given termination relation.     *)
(* ------------------------------------------------------------------ *)

let define_single wfs tm =
  let fs = definition_heads tm in
  let f = hd fs in
  let name = fst(dest_var f) in
  let cls = map (close_clause fs) (conjuncts(snd(strip_forall tm))) in
  let existence cls =
    let etm = mk_exists(f,list_mk_conj cls) in
    if wfs = [] then
      (* HOL Light leaves the conditions it cannot prove as
         assumptions, and then this form is not the one to use *)
      let th = prove_general_recursive_function_exists etm in
      if hyp th = [] then th else failwith "existence"
    else
    let th = pure_prove_recursive_function_exists etm in
    if hyp th = [] then th
    else tryfind (fun rt -> discharge_conditions rt th) wfs in
  (* HOL Light's machinery cannot always take the clauses as they
     are: a lambda with a pattern has to be taken apart with FST and
     SND, and where a recursive call is under an ALL or an EX it
     asks for a condition on every element of the type instead of
     on every element of the list, which cannot be proved; the
     clauses rewritten with MAP give the condition it can use.  The
     existence theorem is proved with the first form that works
     (proving it defines nothing yet), and the clauses as they were
     given are derived from the definition that it makes. *)
  let clsd = map depair cls in
  let clsm = map (mapify [f]) clsd in
  let forms = cls :: (if clsd = cls then [] else [clsd]) @
                     (if clsm = clsd then [] else [clsm]) in
  let dth = new_specification [name] (tryfind existence forms) in
  let dths = CONJUNCTS dth in
  let c = mk_mconst(name,type_of f) in
  let norm = [IN_SET_OF_LIST; ALL_MEM; ALL_MAPIFY; EX_MAPIFY;
              ETA_AX; FST; SND] in
  let derive cl =
    prove(vsubst [c,f] cl,
          REPEAT GEN_TAC THEN
          (FIRST (map MATCH_ACCEPT_TAC dths) ORELSE
           (CONV_TAC(ONCE_DEPTH_CONV DEPAIR_CONV) THEN
            REWRITE_TAC norm THEN
            FIRST (map MATCH_ACCEPT_TAC dths)) ORELSE
           (REWRITE_TAC dths THEN
            CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
            REWRITE_TAC norm))) in
  map derive cls,dth;;

(* ------------------------------------------------------------------ *)
(* Definition of a family of mutually recursive functions.            *)
(* ------------------------------------------------------------------ *)

let define_mutual wfs tm =
  let fs = definition_heads tm in
  let cls = definition_clauses tm in
  let arity f =
    let ars = setify (map (fun (_,args,_) -> length args)
                          (filter (fun (g,_,_) -> g = f) cls)) in
    if length ars <> 1
    then failwith ("define_mutual: varying arity for "^fst(dest_var f))
    else hd ars in
  let ars = map arity fs in
  let split f k =
    let tys,ty = splitlist dest_fun_ty (type_of f) in
    let dtys,rtys = chop_list k tys in
    mk_tuple_type dtys,itlist mk_fun_ty rtys ty in
  let dtys = map2 (fun f k -> fst(split f k)) fs ars in
  let rtys = map2 (fun f k -> snd(split f k)) fs ars in
  let sty = mk_sumtype dtys and rty = mk_sumtype rtys in
  let gname = fst(dest_var(hd fs)) ^ "_mutual" in
  let g = mk_var(gname,mk_fun_ty sty rty) in
  (* each f_i becomes \x1 ... xk. OUT_i (g (IN_i (x1,...,xk))) *)
  let repl i f =
    let k = el i ars in
    let tys,_ = splitlist dest_fun_ty (type_of f) in
    let vs = map (fun j -> mk_var("a" ^ string_of_int j,el j tys))
                 (0--(k-1)) in
    list_mk_abs(vs,mk_proj rtys i (mk_comb(g,mk_inj dtys i (mk_tuple
      vs)))),
    f in
  let repls = map2 repl (0--(length fs - 1)) fs in
  let newcl (f,args,r) =
    let i = index f fs in
    mk_eq(mk_comb(g,mk_inj dtys i (mk_tuple args)),
          mk_inj rtys i (beta_normalize(vsubst repls r))) in
  let newcls = map (fun cl -> close_clause [g] (newcl cl)) cls in
  let existence cls =
    let etm = mk_exists(g,list_mk_conj cls) in
    if wfs = [] then
      (* as in define_single: a theorem that still has the
         condition as an assumption is of no use, and giving it
         to new_specification would keep the other form of the
         clauses from being tried *)
      let th = prove_general_recursive_function_exists etm in
      (if hyp th = [] then th else failwith "existence") else
    let th = pure_prove_recursive_function_exists etm in
    if hyp th = [] then th
    else tryfind (fun rt -> discharge_conditions rt th) wfs in
  let eth = try existence newcls
            with Failure _ -> existence (map depair newcls) in
  let gth = new_specification [gname] eth in
  let gc = mk_mconst(gname,type_of g) in
  (* now define the functions themselves *)
  let define_one i f =
    let name = fst(dest_var f) in
    let k = el i ars in
    let tys,_ = splitlist dest_fun_ty (type_of f) in
    let vs = map (fun j -> mk_var("a" ^ string_of_int j,el j tys))
                 (0--(k-1)) in
    new_definition
      (mk_eq(mk_var(name,type_of f),
             list_mk_abs(vs,mk_proj rtys i
               (mk_comb(gc,mk_inj dtys i (mk_tuple vs)))))) in
  let fdefs = map2 define_one (0--(length fs - 1)) fs in
  let fcs = map (fun th -> lhs(concl th)) fdefs in
  (* and derive the clauses as they were given *)
  let derive cl =
    let gcl = close_clause [] (vsubst (zip fcs fs) cl) in
    prove(gcl,
          REPEAT GEN_TAC THEN TRY DEPAIR_TAC THEN REWRITE_TAC fdefs THEN
          GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [gth] THEN
          REWRITE_TAC[OUTL; OUTR]) in
  map derive (conjuncts(snd(strip_forall tm))),gth;;

(* ================================================================== *)

(*  Primitive recursion for a family of functions.                    *)
(*                                                                    *)
(*  HOL Light's new_recursive_definition defines one function at a    *)
(*  time,                                                             *)
(*  but the recursion theorem of a (nested) datatype is about the     *)
(*  whole                                                             *)
(*  family of its types, so it can define a family of functions at    *)
(*  once,                                                             *)
(*  which is what the CakeML definitions over the syntax trees need.  *)
(* ================================================================== *)

(* the recursion theorems of the datatypes, by the name of a type of the
   family that they are about *)

let the_rec_thms = ref ([]:(string * thm) list);;

let rec_thm_of_type ty =
  let s,_ = dest_type ty in
  assoc s (!the_rec_thms);;

let register_rec_thm rth =
  let _,bod = strip_forall(concl rth) in
  let fns,_ = strip_exists bod in
  do_list
    (fun fn ->
       let ty,_ = dest_fun_ty(type_of fn) in
       if is_type ty then
         let s = fst(dest_type ty) in
         if not (can (assoc s) (!the_rec_thms))
         then the_rec_thms := (s,rth)::(!the_rec_thms))
    fns;;

(* the canonical clauses of a recursion theorem *)

let rec_thm_clauses rth =
  let pvars,bod = strip_forall(concl rth) in
  let fns,cjbod = strip_exists bod in
  let cls =
    map (fun c ->
          let eq = snd(strip_forall c) in
          let l,r = dest_eq eq in
          let fn = rator l in
          let con,args = strip_comb(rand l) in
          let fj,rargs = strip_comb r in
          let recvals = filter is_comb rargs in
          fn,con,args,fj,recvals,rargs)
        (conjuncts cjbod) in
  pvars,fns,cls;;

(* the position of the argument on which a function is defined by     *)
(* cases                                                              *)

let pattern_position f cls =
  let mycls = filter (fun (g,_,_) -> g = f) cls in
  let n = itlist (fun (_,args,_) n -> max n (length args)) mycls 0 in
  let ispat i =
    exists (fun (_,args,_) -> not(is_var(el i args))) mycls in
  let ps = filter ispat (0--(n-1)) in
  if length ps = 1 then hd ps
  else failwith "pattern_position: not exactly one pattern argument";;

let define_prim_rec tm =
  let fs = definition_heads tm in
  let cls = definition_clauses tm in
  let arity f =
    itlist (fun (g,args,_) n -> if g = f then max n (length args) else
      n)
           cls 0 in
  let posns = map (fun f -> pattern_position f cls) fs in
  let patty f r =
    let tys,_ = splitlist dest_fun_ty (type_of f) in el r tys in
  let tymatches vty cty = can (type_match vty cty) [] in
  let covers rth =
    let _,fns,_ = rec_thm_clauses rth in
    forall (fun (f,r) ->
              exists (fun fn ->
                        tymatches (fst(dest_fun_ty(type_of fn))) (patty
                          f r))
                     fns)
           (zip fs posns) in
  let rth = find covers
              (mapfilter (fun (f,r) -> rec_thm_of_type (patty f r))
                         (zip fs posns)) in
  let pvars,fns,canon = rec_thm_clauses rth in
  (* the type instantiation of the recursion theorem *)
  let tyins =
    itlist (fun (_,args,_) ins ->
              itlist (fun a ins ->
                        let hop = fst(strip_comb a) in
                        if is_const hop then
                          (try let con' = find
                                 (fun (_,c,_,_,_,_) ->
                                    is_const c &&
                                    fst(dest_const c) = fst(dest_const
                                      hop))
                                 canon in
                               let _,c,_,_,_,_ = con' in
                               type_match (type_of c) (type_of hop) ins
                           with Failure _ -> ins)
                        else ins)
                      args ins)
           cls [] in
  (* which function is defined by which member of the family *)
  let assign =
    map2 (fun f r ->
           let ty = patty f r in
           let fn = find (fun fn -> fst(dest_fun_ty(type_of
                            (inst tyins fn))) = ty) fns in
           fn,(f,r))
         fs posns in
  if length (setify (map fst assign)) <> length assign
  then failwith "define_prim_rec: two functions on the same type" else
  (* the instantiation of the result type variables *)
  let tyins =
    itlist (fun (fn,(f,r)) ins ->
             let tys,ty = splitlist dest_fun_ty (type_of f) in
             let others = filter (fun i -> i <> r) (0--(arity f - 1)) in
             let rty = itlist (fun i ty -> mk_fun_ty (el i tys) ty)
                              others ty in
             let _,resvar = dest_fun_ty(type_of fn) in
             (rty,resvar)::ins)
           assign tyins in
  let tyins =
    itlist (fun fn ins ->
             let _,resvar = dest_fun_ty(type_of fn) in
             if can (rev_assoc resvar) ins then ins
             else (mk_type("1",[]),resvar)::ins)
           fns tyins in
  let fns = map (inst tyins) fns in
  let canon = map (fun (fn,con,args,fj,rvs,rargs) ->
                     inst tyins fn,inst tyins con,map (inst tyins) args,
                     inst tyins fj,map (inst tyins) rvs,
                     map (inst tyins) rargs)
                  canon in
  let assign = map (fun (fn,x) -> inst tyins fn,x) assign in
  (* the witness for each parameter of the recursion theorem *)
  let witness (fn,con,args,fj,recvals,rargs) =
    let rvs = map (fun i -> mk_var("r" ^ string_of_int i,
                                   type_of (el i recvals)))
                  (0--(length recvals - 1)) in
    let absvars =
      map (fun t -> if is_comb t then el (index t recvals) rvs else t)
          rargs in
    let body =
      try
        let f,r = assoc fn assign in
        let n = arity f in
        let others = filter (fun i -> i <> r) (0--(n-1)) in
        let mycls = filter (fun (g,cargs,_) ->
                              g = f && length cargs = n) cls in
        (* the clause of the constructor, or, where it has none,
           the last clause of the function if its pattern is a
           variable: that is what HOL4's first match semantics
           makes of it (bvi_tailrec's has_rec_sing ends with
           has_rec_sing loc x = F) *)
        let cl,catch =
          try find (fun (_,cargs,_) ->
                      fst(strip_comb(el r cargs)) = con) mycls,false
          with Failure _ ->
            (* the failure has to be the one that the ARB case of
               a constructor without a clause catches *)
            if mycls = [] then failwith "find" else
            let lst = last mycls in
            let _,cargs,_ = lst in
            if is_var (el r cargs) then lst,true
            else failwith "find" in
        let _,cargs,rhs = cl in
        let pargs = snd(strip_comb(el r cargs)) in
        (* a pattern argument may itself be a tuple of variables, which
           is then taken apart with FST and SND *)
        let rec patsub a p =
          if is_var p then [a,p]
          else let x,y = dest_pair p in
               patsub (mk_fst a) x @ patsub (mk_snd a) y in
        let rhs =
          if catch
          then vsubst [list_mk_comb(con,args),el r cargs] rhs
          else vsubst (itlist2 (fun a p l -> patsub a p @ l)
                               args pargs []) rhs in
        let ovars = map (fun i -> el i cargs) others in
        let rmap = map2 (fun rv rval -> rator rval,rand rval,rv)
                        rvs recvals in
        let rec fix tm =
          let hop,hargs = strip_comb tm in
          if mem hop fs && length hargs = arity hop then
            let i = index hop fs in
            let fn' = fst(find (fun (_,(g,_)) -> g = hop) assign) in
            let r' = el i posns in
            let ra = el r' hargs in
            try let _,_,rv = find (fun (f1,a1,_) -> f1 = fn' && a1 = ra)
                                  rmap in
                let oth = map (fun j -> fix (el j hargs))
                              (filter (fun j -> j <> r')
                                      (0--(length hargs - 1))) in
                if oth = [] then rv else list_mk_comb(rv,oth)
            with Failure _ ->
              failwith "define_prim_rec: not primitive recursive"
          else
            match tm with
              Comb(s,t) -> mk_comb(fix s,fix t)
            | Abs(v,b) -> mk_abs(v,fix b)
            | _ -> if mem tm fs
                   then failwith "define_prim_rec: partial application"
                   else tm in
        let rhs = fix rhs in
        list_mk_abs(ovars,rhs)
      with Failure s when s = "find" || s = "assoc" ->
        (* a constructor that the definition has no clause for: the
           value is ARB, as a function of the other arguments *)
        (try let f,r = assoc fn assign in
             let tys,ty = splitlist dest_fun_ty (type_of f) in
             let others = filter (fun i -> i <> r)
                                 (0--(arity f - 1)) in
             let ovars = map (fun i -> mk_var("z" ^ string_of_int i,
                                              el i tys))
                             others in
             list_mk_abs(ovars,mk_const("ARB",[ty,aty]))
         with Failure _ -> mk_const("one",[])) in
    list_mk_abs(absvars,body) in
  let wits = map witness canon in
  let wnames = map (fun (_,_,_,fj,_,_) -> fst(dest_var fj)) canon in
  let order_wits =
    map (fun pv -> el (index (fst(dest_var pv)) wnames) wits) pvars in
  let th1 =
    try SPECL order_wits (INST_TYPE tyins rth)
    with Failure _ ->
      (if !cake_debug then
        (print_string "define_prim_rec: SPECL failed\n";
         do_list (fun (p,w) ->
                    print_term p; print_string " : ";
                    print_type (type_of p); print_string
                      "\n  witness : ";
                    print_type (type_of w); print_newline())
                 (zip (fst(strip_forall(concl(INST_TYPE tyins rth))))
                      order_wits));
       failwith "SPECL") in
  let th2 = CONV_RULE (TOP_DEPTH_CONV GEN_BETA_CONV) th1 in
  (* names for the functions of the family; the ones that the
     definition does not name (two of them can be on the same type
     constructor) get a name that is not in use yet *)
  let taken = ref ([]:string list) in
  let names =
    map (fun fn ->
          try let f,r = assoc fn assign in
              if r = 0 then fst(dest_var f) else fst(dest_var f) ^
                "_rec"
          with Failure _ ->
            let s = fst(dest_var(hd fs)) ^ "_aux_" ^
                    fst(dest_type(fst(dest_fun_ty(type_of fn)))) in
            let rec go i =
              let s' = if i = 0 then s else s ^ string_of_int i in
              if can get_const_type s' || mem s' !taken then go (i + 1)
              else (taken := s' :: !taken; s') in
            go 0)
        fns in
  let spec = new_specification names th2 in
  (* the functions that still have to be defined *)
  let fdefs =
    mapfilter
      (fun (fn,(f,r)) ->
         if r = 0 then fail() else
         let name = fst(dest_var f) in
         let fnc = mk_mconst(name ^ "_rec",type_of fn) in
         let tys = fst(splitlist dest_fun_ty (type_of f)) in
         let n = arity f in
         let vs = map (fun i -> mk_var("a" ^ string_of_int i,el i tys))
                      (0--(n-1)) in
         new_definition
           (mk_eq(mk_var(name,type_of f),
                  list_mk_abs(vs,
                    list_mk_comb(fnc,el r vs ::
                      map (fun i -> el i vs)
                          (filter (fun i -> i <> r) (0--(n-1))))))))
      assign in
  let fcs = map (fun f ->
                   let name = fst(dest_var f) in
                   mk_mconst(name,type_of f)) fs in
  let derive cl =
    let gcl = close_clause [] (vsubst (zip fcs fs) cl) in
    try prove(gcl,
              REPEAT GEN_TAC THEN REWRITE_TAC fdefs THEN
              REWRITE_TAC[spec])
    with Failure e ->
      (if !cake_debug then
         (print_string "[prim_rec] cannot derive "; print_term gcl;
          print_newline(); flush stdout);
       failwith e) in
  map derive (conjuncts(snd(strip_forall tm))),spec;;

(* ------------------------------------------------------------------ *)
(* Nested recursion: a recursive call under a MAP, as in              *)
(* real_fringe (Nd n ptl) = FLAT (MAP real_fringe ptl).               *)
(* HOL Light's machinery for such a recursion does not see that the   *)
(* elements of ptl are smaller, so the port defines the function      *)
(* together with the list function it needs (which is how HOL4 defines*)
(* the size functions of a nested datatype as well), and then derives *)
(* the equations as HOL4 states them.                                 *)
(* ------------------------------------------------------------------ *)

let mk_nil ty = mk_mconst("NIL",mk_type("list",[ty]));;

let mk_cons h t =
  list_mk_comb(mk_mconst("CONS",
    mk_fun_ty (type_of h) (mk_fun_ty (type_of t) (type_of t))),[h;t]);;

let NESTED_LEMMAS =
  [IN_SET_OF_LIST; ALL_MEM; ALL_MAPIFY; EX_MAPIFY; ETA_AX];;

(* a name for a list function that is not in use yet *)

let fresh_const_name s =
  if not (can get_const_type s) then s else
  let rec go i =
    let s' = s ^ string_of_int i in
    if can get_const_type s' then go (i + 1) else s' in
  go 1;;

(* a type of pairs, and its two component types *)

let is_prod_type ty =
  is_type ty && fst(dest_type ty) = "prod";;

let dest_prod_type ty =
  match dest_type ty with
    "prod",[ty1;ty2] -> ty1,ty2
  | _ -> failwith "dest_prod_type";;

(* FST and SND of an explicit pair, which is what the body of a
   function on a pair gets when the pattern is substituted in it *)

let rec simp_pair tm =
  match tm with
    Comb(s,t) ->
      let s' = simp_pair s and t' = simp_pair t in
      (match s' with
         Const("FST",_) when is_pair t' -> fst(dest_pair t')
       | Const("SND",_) when is_pair t' -> snd(dest_pair t')
       | _ -> mk_comb(s',t'))
  | Abs(v,b) -> mk_abs(v,simp_pair b)
  | _ -> tm;;

let define_nested tm =
  let fs = definition_heads tm in
  let cls0 = map (close_clause fs) (conjuncts(snd(strip_forall tm))) in
  let cls = map (fun cl -> mapify fs (depair cl)) cls0 in
  (* the arguments of a map of a recursive call, and the map with
     those arguments made canonical, so that clauses that use
     different variable names share one list function *)
  let args h = filter (fun v -> not (mem v fs)) (frees h) in
  let canon h =
    let vs = args h in
    vsubst (map (fun i -> mk_var("v" ^ string_of_int i,
                                 type_of (el i vs)),el i vs)
                (0--(length vs - 1))) h in
  let found = ref [] in
  let rec collect tm =
    match tm with
      Comb(Comb(Const("MAP",_),h),l)
        when exists (fun g -> vfree_in g h) fs ->
          let hk = canon h in
          (if not (exists (fun k -> aconv k hk) !found)
           then found := !found @ [hk]);
          collect h; collect l
    | Comb(s,t) -> (collect s; collect t)
    | Abs(_,b) -> collect b
    | _ -> () in
  do_list collect cls;
  let name0 = fst(dest_var(hd fs)) in
  (* a name for a function of the family that is not in use yet *)
  let used = ref ([]:string list) in
  let new_name s =
    let rec go i =
      let s' = if i = 0 then s else s ^ string_of_int i in
      (* a name that the block itself defines is not free either:
         presLang defines flat_to_display and the
         flat_to_display_list that the map of it would be called *)
      if can get_const_type s' || mem s' !used ||
         mem s' (!the_defining) ||
         exists (fun f -> fst(dest_var f) = s') fs
      then go (i + 1)
      else (used := s' :: !used; s') in
    go 0 in
  let auxs =
    map (fun i ->
          let hk = el i !found in
          let vs = args hk in
          let ty,rty = dest_fun_ty (type_of hk) in
          let name = new_name (name0 ^ "_list") in
          let auxty =
            itlist (fun v t -> mk_fun_ty (type_of v) t) vs
              (mk_fun_ty (mk_type("list",[ty]))
                         (mk_type("list",[rty]))) in
          hk,vs,mk_var(name,auxty))
        (0--(length !found - 1)) in
  let rec repl tm =
    match tm with
      Comb(Comb(Const("MAP",_),h),l)
        when exists (fun g -> vfree_in g h) fs &&
             exists (fun (hk,_,_) -> aconv hk (canon h)) auxs ->
          let _,_,aux = find (fun (hk,_,_) -> aconv hk (canon h)) auxs
            in
          list_mk_comb(aux,args h @ [repl l])
    | Comb(s,t) -> mk_comb(repl s,repl t)
    | Abs(v,b) -> mk_abs(v,repl b)
    | _ -> tm in
  (* the arguments of the recursive calls in a term *)
  let rec call_args tm =
    let hop,hargs = strip_comb tm in
    if mem hop fs && hargs <> [] then
      itlist (fun a l -> union (call_args a) l) hargs hargs
    else
      match tm with
        Comb(s,t) -> union (call_args s) (call_args t)
      | Abs(_,b) -> call_args b
      | _ -> [] in
  (* when the elements of the list are pairs, the recursion theorem
     of the family has a function for every level of the pair that
     the recursion goes through, so the port defines those as well;
     such a function takes the components above its own level that
     its right-hand side needs as extra arguments. (Two element
     types that have a level in common are not supported: the
     family has one function for every type.) *)
  let rec pair_levels vs ty body =
    let ty1,ty2 = dest_prod_type ty in
    let x = variant vs (mk_var("x",ty1)) in
    let y = variant (x :: vs) (mk_var("y",ty2)) in
    let bod = body (mk_pair(x,y)) in
    let ws,rhs,cls2 =
      if is_prod_type ty2 &&
         exists (fun a -> a <> x && a <> y && vfree_in y a)
                (call_args bod)
      then
        let aux2,args2,cls2 =
          pair_levels (vs @ [x]) ty2 (fun t -> body (mk_pair(x,t))) in
        subtract args2 [x],list_mk_comb(aux2,args2 @ [y]),cls2
      else filter (fun v -> vfree_in v bod) vs,bod,[] in
    let aux =
      mk_var(new_name (name0 ^ "_pair"),
             itlist (fun v t -> mk_fun_ty (type_of v) t) ws
                    (mk_fun_ty ty (type_of bod))) in
    aux,ws,
    (mk_eq(list_mk_comb(aux,ws @ [mk_pair(x,y)]),rhs) :: cls2) in
  (* the clauses of the list function of a map, and of the functions
     on the levels of its element type *)
  let auxcls (hk,vs,aux) =
    let ty,rty = dest_fun_ty (type_of hk) in
    let p = variant vs (mk_var("p",ty)) in
    let ps = variant (p :: vs) (mk_var("ps",mk_type("list",[ty]))) in
    let bodyf t = repl(simp_pair(beta_normalize(mk_comb(hk,t)))) in
    let elt,lvls =
      if not (is_prod_type ty) then bodyf p,[]
      else let pf,pargs,lcls = pair_levels vs ty bodyf in
           list_mk_comb(pf,pargs @ [p]),lcls in
    [mk_eq(list_mk_comb(aux,vs @ [mk_nil ty]),mk_nil rty);
     mk_eq(list_mk_comb(aux,vs @ [mk_cons p ps]),
           mk_cons elt (list_mk_comb(aux,vs @ [ps])))] @ lvls in
  (* a call of a function of the block on a mapped list, as in
     has_install_list (MAP SND fns): the port defines the
     composition of the two, with the clauses that the function's
     own clauses give, and derives the call from it.  (Without it
     the definition is not primitive recursive and HOL Light's
     machinery for a wellfounded recursion is far too slow.) *)
  let list_clauses g =
    let cs = map (fun cl ->
                    let l,r = dest_eq(snd(strip_forall cl)) in
                    let f,args = strip_comb l in (f,args,r))
                 cls in
    let cs = filter (fun (f,args,_) -> f = g && length args = 1) cs in
    let isnil (_,args,_) = is_const(hd args) &&
                           fst(dest_const(hd args)) = "NIL" in
    let iscons (_,args,_) =
      is_comb(hd args) && is_comb(rator(hd args)) &&
      is_const(rator(rator(hd args))) &&
      fst(dest_const(rator(rator(hd args)))) = "CONS" in
    let _,_,nilrhs = find isnil cs in
    let _,cargs,consrhs = find iscons cs in
    nilrhs,rand(rator(hd cargs)),rand(hd cargs),consrhs in
  let found2 = ref [] in
  let rec collect2 tm =
    match tm with
      Comb(g,Comb(Comb(Const("MAP",_),h),l))
        when mem g fs && frees h = [] && can list_clauses g ->
          (if not (exists (fun (g',h') -> g' = g && aconv h' h)
                          !found2)
           then found2 := !found2 @ [g,h]);
          collect2 l
    | Comb(s,t) -> (collect2 s; collect2 t)
    | Abs(_,b) -> collect2 b
    | _ -> () in
  do_list collect2 (map repl cls);
  if !found = [] && !found2 = [] then failwith "define_nested" else
  let comps0 =
    map (fun (g,h) ->
          let ty,_ = dest_fun_ty (type_of h) in
          let lty = mk_type("list",[ty]) in
          let _,rty = dest_fun_ty (type_of g) in
          let nilrhs,x,xs,consrhs = list_clauses g in
          let p = variant (frees consrhs) (mk_var("p",ty)) in
          let ps = variant (p :: frees consrhs) (mk_var("ps",lty)) in
          let aux = mk_var(new_name (name0 ^ "_map"),
                           mk_fun_ty lty rty) in
          let mapc = mk_mconst("MAP",
                       mk_fun_ty (type_of h)
                         (mk_fun_ty lty (type_of xs))) in
          let mps = list_mk_comb(mapc,[h; ps]) in
          let bod = vsubst [mk_comb(h,p),x; mps,xs] consrhs in
          let rec tail tm =
            if tm = mk_comb(g,mps) then mk_comb(aux,ps) else
            match tm with
              Comb(s,t) -> mk_comb(tail s,tail t)
            | Abs(v,b) -> mk_abs(v,tail b)
            | _ -> tm in
          let bod = simp_pair(beta_normalize(tail bod)) in
          (* a recursive call on a component of the element needs a
             function on the element type (see pair_levels) *)
          let lvls = ref [] and plems = ref [] in
          let rec fixelem tm =
            let hop,args = strip_comb tm in
            if mem hop fs && args <> [] && last args <> p &&
               vfree_in p (last args) && is_prod_type ty then
              let pf,pargs,cs =
                pair_levels [] ty
                  (fun z -> simp_pair(beta_normalize(vsubst [z,p] tm)))
                in
              (lvls := !lvls @ cs;
               plems := !plems @ [pf,pargs,mk_abs(p,tm)];
               list_mk_comb(pf,pargs @ [p]))
            else
              match tm with
                Comb(s,t) -> mk_comb(fixelem s,fixelem t)
              | Abs(v,b) -> mk_abs(v,fixelem b)
              | _ -> tm in
          let bod = fixelem bod in
          (g,h,aux,!plems),
          [mk_eq(mk_comb(aux,mk_nil ty),nilrhs);
           mk_eq(mk_comb(aux,mk_cons p ps),bod)] @ !lvls)
        !found2 in
  let comps = map fst comps0 and compcls = map snd comps0 in
  let rec repl2 tm =
    match tm with
      Comb(g,Comb(Comb(Const("MAP",_),h),l))
        when exists (fun (g',h',_,_) -> g' = g && aconv h' h) comps ->
          let _,_,aux,_ =
            find (fun (g',h',_,_) -> g' = g && aconv h' h) comps in
          mk_comb(aux,repl2 l)
    | Comb(s,t) -> mk_comb(repl2 s,repl2 t)
    | Abs(v,b) -> mk_abs(v,repl2 b)
    | _ -> tm in
  let auxclss = map auxcls auxs @ compcls in
  let allauxcls = itlist (@) auxclss [] in
  let gs = setify (map (fun cl -> fst(strip_comb(lhs cl))) allauxcls) in
  let newcls = map (close_clause (fs @ gs))
                   (map (fun cl -> repl2 (repl cl)) cls @ allauxcls) in
  let ths,spec = define_prim_rec (list_mk_conj newcls) in
  let fths,auxths = chop_list (length cls) ths in
  let consts = map (fun f -> mk_mconst(fst(dest_var f),type_of f),f)
                   (fs @ gs) in
  (* the theorems of the clauses of each function that was added *)
  let groups =
    rev(snd(itlist (fun cls (ths,l) ->
                      let g,ths' = chop_list (length cls) ths in
                      ths',g :: l)
                   (rev auxclss) (auxths,[]))) in
  (* the lemma that a function on a pair is the function of the map
     itself, from the clauses of the levels of the pair *)
  let pair_lemma lems gths n hk =
    let lvlths = snd(chop_list n gths) in
    if lvlths = [] then [] else
    let ty,_ = dest_fun_ty (type_of hk) in
    let p = variant (frees hk) (mk_var("p",ty)) in
    let pf,pargs = strip_comb(lhs(snd(strip_forall
                     (concl(hd lvlths))))) in
    let pargs = butlast pargs in
    [prove(list_mk_forall(pargs @ [p],
             mk_eq(list_mk_comb(pf,pargs @ [p]),
                   mk_comb(vsubst consts hk,p))),
           REPLICATE_TAC (length pargs) GEN_TAC THEN
           REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
           REWRITE_TAC (lvlths @ lems) THEN REWRITE_TAC[FST; SND])] in
  (* each list function is the map of the function it belongs to *)
  let lemma lems ((hk,vs,aux),gths) =
    let ty,rty = dest_fun_ty (type_of hk) in
    let lty = mk_type("list",[ty]) in
    let l = variant vs (mk_var("l",lty)) in
    let mapc = mk_mconst("MAP",
                 mk_fun_ty (type_of hk)
                   (mk_fun_ty lty (mk_type("list",[rty])))) in
    let pls = pair_lemma lems gths 2 hk in
    lems @ pls @
    [prove(list_mk_forall(vs @ [l],
             mk_eq(list_mk_comb(vsubst consts aux,vs @ [l]),
                   list_mk_comb(mapc,[vsubst consts hk; l]))),
           REPLICATE_TAC (length vs) GEN_TAC THEN LIST_INDUCT_TAC THEN
           ASM_REWRITE_TAC (MAP :: el 0 gths :: el 1 gths :: pls))] in
  let nmaps = length auxs in
  let mapgroups,compgroups = chop_list nmaps groups in
  let lems = itlist (fun a l -> lemma l a)
                    (rev (zip auxs mapgroups)) [] in
  (* and each composition is the function of the mapped list *)
  let comp_lemma lems ((g,h,aux,pfs),gths) =
    let ty,_ = dest_fun_ty (type_of h) in
    let lty = mk_type("list",[ty]) in
    let l = variant [] (mk_var("l",lty)) in
    let ety = mk_type("list",[snd(dest_fun_ty(type_of h))]) in
    let mapc = mk_mconst("MAP",
                 mk_fun_ty (type_of h) (mk_fun_ty lty ety)) in
    let lvlths = snd(chop_list 2 gths) in
    let pls =
      map (fun (pf,pargs,hk) ->
            let p = variant (frees hk) (mk_var("p",ty)) in
            prove(list_mk_forall(pargs @ [p],
                    mk_eq(list_mk_comb(vsubst consts pf,pargs @ [p]),
                          beta_normalize
                            (mk_comb(vsubst consts hk,p)))),
                  REPLICATE_TAC (length pargs) GEN_TAC THEN
                  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
                  REWRITE_TAC (lvlths @ lems) THEN
                  REWRITE_TAC[FST; SND]))
          pfs in
    lems @ pls @
    [prove(mk_forall(l,
             mk_eq(mk_comb(vsubst consts aux,l),
                   mk_comb(vsubst consts g,
                           list_mk_comb(mapc,[h; l])))),
           LIST_INDUCT_TAC THEN
           ASM_REWRITE_TAC (MAP :: (fths @ gths @ pls)))] in
  let lems = itlist (fun a l -> comp_lemma l a)
                    (rev (zip comps compgroups)) lems in
  let derive cl =
    let gcl = vsubst consts cl in
    tryfind (fun tac -> prove(gcl,tac))
      [REPEAT GEN_TAC THEN REWRITE_TAC (fths @ lems) THEN
       REWRITE_TAC NESTED_LEMMAS;
       REPEAT GEN_TAC THEN DEPAIR_TAC THEN
       REWRITE_TAC (fths @ lems) THEN REWRITE_TAC NESTED_LEMMAS;
       REPEAT GEN_TAC THEN DEPAIR_TAC THEN
       REWRITE_TAC NESTED_LEMMAS THEN REWRITE_TAC (map GSYM lems) THEN
       FIRST (map MATCH_ACCEPT_TAC fths)] in
  map derive cls0,spec;;

(* ------------------------------------------------------------------ *)
(* Definitions by nested patterns.  HOL Light's recursion theorem   *)
(* gives a function by cases on one constructor, so a pattern       *)
(* inside a pattern needs a function of its own; the family of the  *)
(* recursion theorem has the types of the arguments of the          *)
(* constructors in it, so those functions can be defined with it.   *)
(* The port compiles the clauses into such functions and derives    *)
(* the clauses as they were given (which only holds when they do    *)
(* not overlap; otherwise the derivation fails and the definition   *)
(* is made in another way).                                         *)
(* ------------------------------------------------------------------ *)

let compile_cases fs cls =
  (* the constructors of a type, with the types of their arguments *)
  let constructors ty =
    if is_prod_type ty then
      (* HOL Light's pair is not a type of define_type *)
      let ty1,ty2 = dest_prod_type ty in
      [mk_mconst(",",mk_fun_ty ty1 (mk_fun_ty ty2 ty)),
       [mk_var("x",ty1); mk_var("y",ty2)]]
    else
    let ths = CONJUNCTS (cases (fst(dest_type ty))) in
    let tyof th = type_of(fst(dest_forall(concl th))) in
    let th = try find (fun th -> tyof th = ty) ths
             with Failure _ ->
               find (fun th -> can (type_match (tyof th) ty) []) ths in
    let th = INST_TYPE (type_match (tyof th) ty []) th in
    let _,bod = dest_forall(concl th) in
    map (fun dj -> let _,eq = strip_exists dj in
                   strip_comb(rhs eq))
        (disjuncts bod) in
  (* the types of the family of the recursion theorem of the
     function, which are the ones a function of its own can be
     defined on *)
  let f0 = hd fs in
  let pos0 =
    let mycls = filter (fun (g,_,_) -> g = f0) cls in
    pattern_position f0 (map (fun (g,args,r) -> g,args,r) mycls) in
  let mainty =
    let tys,_ = splitlist dest_fun_ty (type_of f0) in el pos0 tys in
  let family =
    let _,fns,_ = rec_thm_clauses (rec_thm_of_type mainty) in
    map (fun fn -> fst(dest_fun_ty(type_of fn))) fns in
  let in_family ty =
    exists (fun t -> can (type_match t ty) []) family in
  let name0 = fst(dest_var f0) in
  let used = ref ([]:string list) in
  let new_name () =
    let rec go i =
      let s = name0 ^ "_case" ^ (if i = 0 then "" else string_of_int i)
        in
      if can get_const_type s || mem s !used ||
         mem s (!the_defining) then go (i + 1)
      else (used := s :: !used; s) in
    go 0 in
  let newcls = ref ([]:term list) in
  let auxs = ref ([]:term list) in
  (* the variables of the compiled clauses, which all need a name of
     their own, and one that the clauses do not use (nor a0, a1,
     ..., which define_prim_rec takes from the recursion theorem) *)
  let avoid = itlist (fun (_,args,r) l -> union (freesl (r :: args)) l)
                     cls [] in
  let vcount = ref 0 in
  let rec fresh_var ty =
    (incr vcount;
     let s = "y" ^ string_of_int !vcount in
     if exists (fun w -> fst(dest_var w) = s) avoid then fresh_var ty
     else mk_var(s,ty)) in
  (* the body of a function with these arguments for these clauses:
     a pattern on a type of the family becomes a function of its
     own (the recursion can be under it), a pattern on a pair is
     taken apart with FST and SND, and a pattern on an option
     becomes a conditional *)
  let rec compile_body gargs clauses =
    let pats = filter (fun i -> exists (fun (ps,_) ->
                                          not (is_var (el i ps)))
                                       clauses)
                      (0--(length gargs - 1)) in
    let fampats = filter (fun i -> in_family (type_of (el i gargs)))
                         pats in
    if pats = [] then
      (let ps,r = hd clauses in vsubst (zip gargs ps) r)
    else if fampats <> [] then
      let p = hd fampats in
      let rty = type_of (snd(hd clauses)) in
      let aux = mk_var(new_name (),
                       itlist (fun a t -> mk_fun_ty (type_of a) t)
                              gargs rty) in
      (auxs := !auxs @ [aux];
       do_list (fun (con,cargs) ->
                  let vs = map (fun a -> fresh_var (type_of a)) cargs in
                  let sub = constructor_clauses clauses p con vs in
                  if sub = [] then () else
                  let newargs = fst(chop_list p gargs) @ vs @
                                snd(chop_list (p + 1) gargs) in
                  let gpat = fst(chop_list p gargs) @
                             [list_mk_comb(con,vs)] @
                             snd(chop_list (p + 1) gargs) in
                  newcls := !newcls @
                    [mk_eq(list_mk_comb(aux,gpat),
                           compile_body newargs sub)])
               (constructors (type_of (el p gargs)));
       list_mk_comb(aux,gargs))
    else
      let p = hd pats in
      let ty = type_of (el p gargs) in
      let v = el p gargs in
      if is_prod_type ty then
        (* every clause binds the two components *)
        let vs = [mk_fst v; mk_snd v] in
        let sub = constructor_clauses clauses p
                    (fst(strip_comb(fst(hd(constructors ty))))) vs in
        let sub = if sub = [] then failwith "define_cases" else sub in
        let newargs = fst(chop_list p gargs) @ vs @
                      snd(chop_list (p + 1) gargs) in
        compile_body newargs sub
      else if fst(dest_type ty) = "option" then
        let cons = constructors ty in
        let branch (con,cargs) =
          let vs = map (fun a ->
                          if cargs = [] then a
                          else mk_comb(mk_mconst("THE",
                                 mk_fun_ty ty (type_of a)),v))
                       cargs in
          let sub = constructor_clauses clauses p con vs in
          if sub = [] then None else
          let newargs = fst(chop_list p gargs) @ vs @
                        snd(chop_list (p + 1) gargs) in
          Some (compile_body newargs sub) in
        let nonec = find (fun (c,a) -> a = []) cons in
        let somec = find (fun (c,a) -> a <> []) cons in
        (match branch nonec,branch somec with
           Some a,Some b ->
             mk_cond(mk_eq(v,fst nonec),a,b)
         | Some a,None -> a
         | None,Some b -> b
         | None,None -> failwith "define_cases")
      else failwith "define_cases: cannot take the pattern apart"
  (* the clauses that match a constructor at a position, with the
     arguments of the constructor in its place *)
  and constructor_clauses clauses p con vs =
    mapfilter
      (fun (ps,r) ->
         let q = el p ps in
         if is_var q then
           (fst(chop_list p ps) @ map (fun v -> v) vs @
            snd(chop_list (p + 1) ps)),
           vsubst [list_mk_comb(con,vs),q] r
         else
           let c,qs = strip_comb q in
           if c <> con then fail() else
           (fst(chop_list p ps) @ qs @ snd(chop_list (p + 1) ps)),r)
      clauses in
  (* the clauses of the functions themselves *)
  do_list
    (fun f ->
       let mycls = filter (fun (g,_,_) -> g = f) cls in
       let _,args0,_ = hd mycls in
       let n = length args0 in
       if exists (fun (_,args,_) -> length args <> n) mycls
       then failwith "define_cases: varying arity" else
       let tys,_ = splitlist dest_fun_ty (type_of f) in
       let gargs = map (fun i -> fresh_var (el i tys)) (0--(n-1)) in
       let clauses = map (fun (_,args,r) -> args,r) mycls in
       let p = pattern_position f (map (fun (g,a,r) -> g,a,r) mycls) in
       let ty = el p tys in
       do_list
         (fun (con,cargs) ->
            let vs = map (fun a -> fresh_var (type_of a)) cargs in
            let sub = constructor_clauses clauses p con vs in
            if sub = [] then () else
            let newargs = fst(chop_list p gargs) @ vs @
                          snd(chop_list (p + 1) gargs) in
            let gpat = fst(chop_list p gargs) @
                       [list_mk_comb(con,vs)] @
                       snd(chop_list (p + 1) gargs) in
            newcls := !newcls @
              [mk_eq(list_mk_comb(f,gpat),
                     compile_body newargs sub)])
         (constructors ty))
    fs;
  !newcls,!auxs;;

(* the definition that the compiled clauses make, with the lemmas
   that the derivation of the clauses as they were given needs *)

let define_compiled fs newcls auxs =
  let ths,spec =
    define_prim_rec (list_mk_conj
      (map (close_clause (fs @ auxs)) newcls)) in
  let consts = map (fun f -> mk_mconst(fst(dest_var f),type_of f),f)
                   (fs @ auxs) in
  let rws = ths @ [THE; distinctness "option";
                   injectivity "option"; FST; SND] in
  (* a clause that is more general than the cases of the compiled
     definition (it has a variable where the definition takes the
     constructors apart) needs the case analysis *)
  let case_split v =
    let ty = type_of v in
    if is_prod_type ty then STRUCT_CASES_TAC (ISPEC v PAIR_SURJECTIVE)
    else if fst(dest_type ty) = "num" then failwith "case_split" else
    let cths = CONJUNCTS (cases (fst(dest_type ty))) in
    let tyof th = type_of(fst(dest_forall(concl th))) in
    let th = find (fun th -> can (type_match (tyof th) ty) []) cths in
    STRUCT_CASES_TAC (ISPEC v th) in
  (* the variables of an option or a pair are taken apart, as deep
     as they go (the types get smaller, so this stops) *)
  let rec SPLIT_TAC (asl,w as gl) =
    let vs = filter (fun v ->
                       let ty = type_of v in
                       is_prod_type ty ||
                       (is_type ty && fst(dest_type ty) = "option"))
                    (frees w) in
    if vs = [] then ALL_TAC gl
    else (MAP_EVERY case_split vs THEN SPLIT_TAC) gl in
  spec,consts,rws,SPLIT_TAC,ths;;

(* a definition by clauses with patterns inside patterns *)

let define_cases tm =
  let fs = definition_heads tm in
  let cls = definition_clauses tm in
  let newcls,auxs = compile_cases fs cls in
  if forall (fun cl -> exists (fun cl0 -> aconv cl cl0)
                              (map (snd o strip_forall)
                                   (conjuncts(snd(strip_forall tm)))))
            newcls
  then failwith "define_cases: nothing to compile" else
  let spec,consts,rws,SPLIT_TAC,_ = define_compiled fs newcls auxs in
  let derive cl =
    let gcl = close_clause [] (vsubst consts (snd(strip_forall cl))) in
    try tryfind (fun tac -> prove(gcl,tac))
          [REPEAT GEN_TAC THEN REWRITE_TAC rws;
           REPEAT GEN_TAC THEN SPLIT_TAC THEN REWRITE_TAC rws]
    with Failure e ->
      (if !cake_debug then
         (print_string "[cases] cannot derive "; print_term gcl;
          print_newline(); flush stdout);
       failwith e) in
  map derive (conjuncts(snd(strip_forall tm))),spec;;

(* ------------------------------------------------------------------ *)
(* A definition whose clauses overlap is written with a match (HOL4   *)
(* takes the first clause that matches, and so does HOL Light's       *)
(* match), and then HOL Light's machinery for a recursion does not    *)
(* see the recursive calls that are in it.  The port makes a clause   *)
(* for every constructor of the type that is matched on, defines the  *)
(* function from those, and derives the definition as it was given.   *)
(* ------------------------------------------------------------------ *)

let MATCH_REDUCE_CONV = REPEATC (CHANGED_CONV MATCH_CONV);;

(* the arms of a match of HOL Light, which is
   _MATCH x (_SEQPATTERN arm1 (_SEQPATTERN arm2 ...)) with an arm
   \u v. ?vs. _UNGUARDED_PATTERN (GEQ pat u) (GEQ body v) *)

let dest_match_arms =
  let dest_arm a =
    let _,b1 = dest_abs a in
    let _,b2 = dest_abs b1 in
    let vs,bod = strip_exists b2 in
    if not (is_comb bod && is_comb(rator bod) &&
            is_const(rator(rator bod)) &&
            fst(dest_const(rator(rator bod))) = "_UNGUARDED_PATTERN")
    then failwith "dest_match_arms: a guarded pattern" else
    let p1 = rand(rator bod) and p2 = rand bod in
    vs,rand(rator p1),rand(rator p2) in
  let rec arms tm =
    if is_comb tm && is_comb(rator tm) &&
       is_const(rator(rator tm)) &&
       fst(dest_const(rator(rator tm))) = "_SEQPATTERN"
    then dest_arm (rand(rator tm)) :: arms (rand tm)
    else [dest_arm tm] in
  arms;;

(* A definition with a match: the clauses that its arms give are
   compiled like the clauses of a definition that has patterns
   inside patterns, and the definition as it was given is derived
   from them (HOL Light's match takes the first arm that matches,
   as HOL4's clauses do). *)

let define_match tm =
  let fs = definition_heads tm in
  let cls = definition_clauses tm in
  if length fs <> 1 || length cls <> 1 then failwith "define_match"
  else
  let f,args,bod = hd cls in
  let hop,margs = strip_comb bod in
  if not (is_const hop && fst(dest_const hop) = "_MATCH") ||
     length margs <> 2
  then failwith "define_match" else
  let scrut = hd margs in
  if not (is_var scrut && mem scrut args) then failwith "define_match"
  else
  let p = index scrut args in
  let arms = dest_match_arms (last margs) in
  let clauses =
    map (fun (_,pat,bdy) ->
          (fst(chop_list p args) @ [pat] @
           snd(chop_list (p + 1) args)),bdy)
        arms in
  let newcls,auxs = compile_cases fs (map (fun (ps,r) -> f,ps,r)
                                          clauses) in
  let spec,consts,rws,SPLIT_TAC,_ = define_compiled fs newcls auxs in
  (* the cases theorem of a family is the conjunction of the ones
     of its types *)
  let ty = type_of scrut in
  let casth =
    let ths = CONJUNCTS (cases (fst(dest_type ty))) in
    let th = try find (fun th ->
                         type_of(fst(dest_forall(concl th))) = ty) ths
             with Failure _ -> find (can (ISPEC scrut)) ths in
    ISPEC scrut th in
  let gcl = close_clause [] (vsubst consts (snd(strip_forall
              (hd(conjuncts(snd(strip_forall tm))))))) in
  [prove(gcl,
         REPEAT GEN_TAC THEN STRUCT_CASES_TAC casth THEN
         SPLIT_TAC THEN REWRITE_TAC rws THEN
         CONV_TAC (ONCE_DEPTH_CONV MATCH_REDUCE_CONV) THEN
         REWRITE_TAC rws)],spec;;

(* ------------------------------------------------------------------ *)

(* A name that several theories of the port define is an overloaded
   name in HOL4, which resolves it by the type; HOL Light can do the
   same, so the port gives the constants of such a name different
   names and overloads the name that HOL4 uses with all of them. *)

let hol4_overload name cname =
  (try make_overloadable name `:A` with Failure _ -> ());
  overload_interface(name,mk_mconst(cname,get_const_type cname));;

(* the overload that a file makes for an infix is taken back at
   the end of it, so that the files after it mean what HOL Light
   means: an overload stays in the interface until it is
   overridden, and the ++ of two variables that nothing says the
   type of would then be the choice of a monad that another file
   enabled (semantics' prelude ++ prog) *)

let hol4_only name cname =
  (try make_overloadable name `:A` with Failure _ -> ());
  override_interface(name,mk_mconst(cname,get_const_type cname));;

(* HOL4's Datatype, which also registers the recursion theorem and (as*)
(* HOL4                                                               *)
(* does) defines the size functions of the family.                    *)
(* ------------------------------------------------------------------ *)

(* HOL Light's own parser for the specification of a datatype splits
   the types of the constructor arguments on commas, which goes wrong
   for a type like (num,'a list->bool)fmap.  So the specification is
   parsed here, and the types with HOL Light's type parser. *)

(* HOL Light's type parser turns a type name that it does not know
   into a type variable, which would silently give a wrong type, so
   the names in a datatype specification are checked first *)

let check_type_names news s =
  let letter c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') in
  let idchar c = letter c || (c >= '0' && c <= '9') ||
                 c = '_' || c = '\'' in
  let n = String.length s in
  let i = ref 0 in
  while !i < n do
    if letter s.[!i] then
      (let j = ref !i in
       while !j < n && idchar s.[!j] do incr j done;
       let name = String.sub s !i (!j - !i) in
       if not (!i > 0 && s.[!i - 1] = '\'') &&
          not (mem name news) &&
          not (can get_type_arity name) &&
          not (can (assoc name) (type_abbrevs()))
       then failwith ("unknown type " ^ name);
       i := !j)
    else incr i
  done;;

let parse_datatype_spec s =
  let split c s =
    let out = ref [] and cur = ref [] and depth = ref 0 in
    String.iter
      (fun ch ->
         if ch = '(' || ch = '[' then (incr depth; cur := ch::(!cur))
         else if ch = ')' || ch = ']' then (decr depth; cur :=
           ch::(!cur))
         else if ch = c && !depth = 0 then
           (out := (implode(rev(map (String.make 1) (!cur))))::(!out);
            cur := [])
         else cur := ch::(!cur))
      s;
    rev ((implode(rev(map (String.make 1) (!cur))))::(!out)) in
  let trim s =
    let n = String.length s in
    let i = ref 0 and j = ref n in
    while !i < n && (s.[!i] = ' ' || s.[!i] = '\n' || s.[!i] = '\t')
      do incr i done;
    while !j > !i && (s.[!j-1] = ' ' || s.[!j-1] = '\n' ||
                      s.[!j-1] = '\t') do decr j done;
    String.sub s !i (!j - !i) in
  let args s =
    (* the arguments of a constructor: tokens or parenthesised groups *)
    let out = ref [] and cur = ref [] and depth = ref 0 in
    String.iter
      (fun ch ->
         if ch = '(' then
           (if !depth > 0 then cur := ch::(!cur); incr depth)
         else if ch = ')' then
           (decr depth; if !depth > 0 then cur := ch::(!cur)
            else (out := (implode(rev(map (String.make 1)
              (!cur))))::(!out);
                  cur := []))
         else if !depth = 0 && (ch = ' ' || ch = '\n' || ch = '\t') then
           (if !cur <> [] then
              (out := (implode(rev(map (String.make 1)
                (!cur))))::(!out);
               cur := []))
         else cur := ch::(!cur))
      s;
    if !cur <> [] then
      out := (implode(rev(map (String.make 1) (!cur))))::(!out);
    rev (!out) in
  let parts = split ';' s in
  (* the types that the specification itself defines *)
  let news =
    mapfilter (fun part ->
                 match split '=' part with
                   [l;_] -> trim l
                 | _ -> fail())
              parts in
  map (fun part ->
         match split '=' part with
           [l;r] ->
             let ty = trim l in
             mk_vartype ty,
             map (fun alt ->
                    match args (trim alt) with
                      c::tys ->
                        c,map (fun t -> check_type_names news t;
                                        parse_type t) tys
                    | [] -> failwith "parse_datatype_spec")
                 (split '|' r)
         | _ -> failwith "parse_datatype_spec")
      parts;;

let define_datatype spec =
  let ith,rth = define_type_raw (parse_datatype_spec spec) in
  register_rec_thm rth;
  ith,rth;;

(* the recursion theorems of the types that HOL Light defines itself *)

register_rec_thm list_RECURSION;;
register_rec_thm option_RECURSION;;
register_rec_thm num_RECURSION;;
register_rec_thm sum_RECURSION;;
register_rec_thm char_RECURSION;;
register_rec_thm pair_RECURSION;;

(* ================================================================== *)

(*  Size functions, for the termination of the definitions that are   *)
(*  not                                                               *)
(*  primitive recursive.                                              *)
(*                                                                    *)
(*  define_size "exp" defines exp_size, and exp_size1, exp_size2, ... *)
(*  for                                                               *)
(*  the other types of the family of exp (as HOL4 defines exp1_size,  *)
(*  exp2_size, ...), and identifies the ones on lists with list_size, *)
(*  so                                                                *)
(*  that MEM_list_size gives the facts a termination proof needs.     *)
(* ================================================================== *)

let the_size_fns = ref ([]:(hol_type * term * hol_type list) list);;

(* the types whose size function ml/lib/hol4.ml has, and whose
   size size_fn_of_type writes with it: a size function of our
   own for one of them would be a second constant that no lemma
   is about *)

let builtin_size_types =
  ["list"; "option"; "prod"; "num"; "sum"; "char"; "bool"];;

let define_size tyname =
  if mem tyname builtin_size_types then
    failwith "define_size: the library has the size function" else
  let rth = assoc tyname (!the_rec_thms) in
  let _,fns,canon = rec_thm_clauses rth in
  let numty = mk_type("num",[]) in
  let tyins = map (fun fn -> numty,snd(dest_fun_ty(type_of fn))) fns in
  let ifns = map (inst tyins) fns in
  let canon = map (fun (fn,con,args,fj,rvs,rargs) ->
                     inst tyins fn,inst tyins con,map (inst tyins) args,
                     fj,map (inst tyins) rvs,map (inst tyins) rargs)
                  canon in
  (* the type variables of the family are the parameters: a size
     function for each of them, as HOL4's size functions have *)
  let params =
    itlist (fun fn l ->
              itlist (fun v l -> if mem v l then l else l @ [v])
                     (sort (<) (tyvars(fst(dest_fun_ty(type_of fn)))))
                       l)
           ifns [] in
  let pvars = map (fun ty -> mk_var("size" ^ dest_vartype ty,
                                    mk_fun_ty ty numty))
                  params in
  (* the name of the size function of each type of the family *)
  let k = ref 0 in
  let names =
    map (fun fn ->
          let ty = fst(dest_fun_ty(type_of fn)) in
          (* the name a CakeML theory gives a constant can be the
             one of the size function of its own type (balanced_map
             does that), so the name has to be a free one *)
          if fst(dest_type ty) = tyname
          then fresh_const_name (tyname ^ "_size")
          else (k := !k + 1;
                fresh_const_name (tyname ^ "_size" ^ string_of_int !k)))
        ifns in
  let svars =
    map2 (fun fn nm ->
            mk_var(nm,itlist (fun v ty -> mk_fun_ty (type_of v) ty)
                             pvars (type_of fn)))
         ifns names in
  let svar_of fn =
    list_mk_comb(el (index fn ifns) svars,pvars) in
  let zero = mk_small_numeral 0 and one = mk_small_numeral 1 in
  let clause (fn,con,args,_,rvs,_) =
    let tms =
      mapfilter (fun a ->
                   try mk_comb(svar_of (rator (find (fun rv -> rand rv =
                     a)
                                                    rvs)),a)
                   with Failure _ ->
                     let ty = type_of a in
                     if is_vartype ty && mem ty params
                     then mk_comb(el (index ty params) pvars,a)
                     else fail())
                args in
    let rhs =
      if args = [] then zero
      else if tms = [] then one
      else mk_binop `(+):num->num->num` one
             (end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
                         tms) in
    mk_eq(mk_comb(svar_of fn,list_mk_comb(con,args)),rhs) in
  let cls = map clause canon in
  let ths,_ = define_prim_rec (list_mk_conj cls) in
  let sizedefs = ths in
  (* the size functions on lists are the generic list_size *)
  let listlems =
    mapfilter
      (fun fn ->
         let ty = fst(dest_fun_ty(type_of fn)) in
         if fst(dest_type ty) <> "list" then fail() else
         let ety = hd(snd(dest_type ty)) in
         let efn = find (fun g -> fst(dest_fun_ty(type_of g)) = ety)
                        ifns in
         let sl = list_mk_comb(mk_mconst(el (index fn ifns) names,
                                 type_of(el (index fn ifns)
                                   svars)),pvars)
         and se = list_mk_comb(mk_mconst(el (index efn ifns) names,
                                 type_of(el (index efn ifns) svars)),
                               pvars) in
         let l = mk_var("l",ty) in
         prove(mk_forall(l,list_mk_forall(pvars,
                 mk_eq(mk_comb(sl,l),
                   list_mk_comb(mk_mconst("list_size",
                     mk_fun_ty (type_of se) (mk_fun_ty ty numty)),
                     [se;l])))),
               LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
               ASM_REWRITE_TAC(list_size::sizedefs) THEN
               TRY ARITH_TAC))
      ifns in
  (* the size of what a MAP FST or a MAP SND of a list of pairs
     of the family gives *)
  let pairlems =
    let sfn ty =
      try let g = find (fun g -> fst(dest_fun_ty(type_of g)) = ty)
                       ifns in
          list_mk_comb(mk_mconst(el (index g ifns) names,
                         type_of(el (index g ifns) svars)),pvars)
      with Failure _ -> (!size_fn_of_type_fwd) ty in
    let lsize f t =
      let ety = fst(dest_fun_ty(type_of f)) in
      list_mk_comb(mk_mconst("list_size",
        mk_fun_ty (type_of f)
          (mk_fun_ty (mk_type("list",[ety])) numty)),[f;t]) in
    flat (mapfilter
      (fun fn ->
         let ty = fst(dest_fun_ty(type_of fn)) in
         let n,args = dest_type ty in
         if n <> "prod" then fail() else
         let aty = hd args and bty = hd(tl args) in
         let sp = sfn ty in
         let lty = mk_type("list",[ty]) in
         let l = mk_var("l",lty) in
         let maps nm ety =
           mk_comb(mk_comb(mk_mconst("MAP",
             mk_fun_ty (mk_fun_ty ty ety)
               (mk_fun_ty lty (mk_type("list",[ety])))),
             mk_mconst(nm,mk_fun_ty ty ety)),l) in
         let lemma f t =
           prove(mk_forall(l,list_mk_forall(pvars,
                   mk_binop `(<=):num->num->bool`
                            (lsize f t) (lsize sp l))),
                 MATCH_MP_TAC list_INDUCT THEN
                 REWRITE_TAC[MAP; list_size; FORALL_PAIR_THM] THEN
                 REPEAT GEN_TAC THEN
                 REWRITE_TAC(list_size::sizedefs) THEN ARITH_TAC) in
         [lemma (sfn aty) (maps "FST" aty);
          lemma (sfn bty) (maps "SND" bty)])
      ifns) in
  cake_term_facts := pairlems @ (!cake_term_facts);
  the_size_thms := (tyname,(sizedefs,listlems))::(!the_size_thms);
  do_list
    (fun th ->
       let f = fst(strip_comb(lhs(snd(strip_forall(concl th))))) in
       let ty = el (length pvars) (fst(splitlist dest_fun_ty
                                         (type_of f))) in
       if not (exists (fun (ty0,_,_) -> ty0 = ty) (!the_size_fns))
       then the_size_fns := (ty,f,params)::(!the_size_fns))
    sizedefs;
  sizedefs,listlems;;

let size_thms tyname =
  let a,b = assoc tyname (!the_size_thms) in a @ b;;

(* the size function of a type, which the measures use *)

let rec size_fn_of_type ty =
  try let ty0,f,params = find (fun (ty0,_,_) -> can (type_match ty0 ty)
    [])
                              (!the_size_fns) in
      let ins = type_match ty0 ty [] in
      list_mk_comb(inst ins f,
                   map (fun v -> size_fn_of_type (type_subst ins v))
                       params)
  with Failure _ ->
    if is_vartype ty then mk_abs(mk_var("x",ty),mk_small_numeral 0) else
    let s,args = dest_type ty in
    if s = "num" then mk_abs(mk_var("n",ty),mk_var("n",ty))
    else if s = "list" then
      let f = size_fn_of_type (hd args) in
      list_mk_comb(mk_mconst("list_size",
        mk_fun_ty (type_of f) (mk_fun_ty ty (mk_type("num",[])))),[f])
    else if s = "option" then
      let f = size_fn_of_type (hd args) in
      list_mk_comb(mk_mconst("option_size",
        mk_fun_ty (type_of f) (mk_fun_ty ty (mk_type("num",[])))),[f])
    else if s = "prod" then
      let f = size_fn_of_type (hd args)
      and g = size_fn_of_type (hd(tl args)) in
      list_mk_comb(mk_mconst("pair_size",
        mk_fun_ty (type_of f) (mk_fun_ty (type_of g)
          (mk_fun_ty ty (mk_type("num",[]))))),[f;g])
    else if can (assoc s) (!the_rec_thms) then
     (let _ = define_size s in size_fn_of_type ty)
    else mk_abs(mk_var("x",ty),mk_small_numeral 0);;

(* ------------------------------------------------------------------ *)
(* The measure that HOL4 gives, with its size functions.              *)
(*                                                                    *)
(* HOL4 numbers the size functions of the types of a family in        *)
(* another order than HOL Light does (of closLang's exp, HOL4's       *)
(* exp1_size is the one of a (num # exp) list and ours is the one of  *)
(* an exp list), so the port leaves such a name a variable rather     *)
(* than write down the size function of another type.  The type of    *)
(* the variable says which size function it is.  A relation that      *)
(* still has a free variable in it is of no use: the goals that it    *)
(* gives cannot be proved, and trying it costs a part of the budget.  *)

(* ------------------------------------------------------------------ *)
(* A measure for a definition whose termination HOL Light cannot guess*)
(* and                                                                *)
(* for which HOL4 did not give one either (because HOL4 guessed it).  *)
(* ------------------------------------------------------------------ *)

size_fn_of_type_fwd := size_fn_of_type;;

let measure_of_positions f cls idxs =
  let tys,_ = splitlist dest_fun_ty (type_of f) in
  let mycls = filter (fun (g,_,_) -> g = f) cls in
  let n = itlist (fun (_,args,_) k -> max k (length args)) mycls 0 in
  let tys = fst(chop_list n tys) in
  let vs = map (fun i -> mk_var("x" ^ string_of_int i,el i tys))
               (0--(n-1)) in
  let tms = map (fun i -> mk_comb(size_fn_of_type (el i tys),el i vs))
                idxs in
  let body =
    if tms = [] then mk_small_numeral 0
    else end_itlist (fun a b -> mk_binop `(+):num->num->num` a b) tms in
  if n = 1 then mk_abs(hd vs,body) else mk_gabs(mk_tuple vs,body);;

let pattern_positions f cls =
  let mycls = filter (fun (g,_,_) -> g = f) cls in
  let n = itlist (fun (_,args,_) k -> max k (length args)) mycls 0 in
  filter (fun i -> exists (fun (_,args,_) -> not(is_var(el i args)))
                          mycls)
         (0--(n-1));;

(* the arguments that a match in the right hand side is on: a
   definition that HOL4 writes as one clause with a match has
   variables for patterns, so pattern_positions finds nothing,
   while the recursion goes down on the arguments of the match
   (balanced_map's link matches on the pair (l,r)) *)

let match_positions f cls =
  let mycls = filter (fun (g,_,_) -> g = f) cls in
  itlist
    (fun (_,args,r) l ->
       let hop,margs = strip_comb r in
       if not (is_const hop && fst(dest_const hop) = "_MATCH") ||
          length margs <> 2 then l else
       let vs = striplist dest_pair (hd margs) in
       union (filter (fun i -> mem (el i args) vs)
                     (0--(length args - 1)))
             l)
    mycls [];;

let mk_measure m =
  let dty = fst(dest_fun_ty(type_of m)) in
  list_mk_comb(mk_mconst("MEASURE",
    mk_fun_ty (type_of m) (mk_fun_ty dty (mk_fun_ty dty
      bool_ty))),[m]);;

let arity_in f cls =
  itlist (fun (g,args,_) k ->
            if g = f then max k (length args) else k) cls 0;;

(* the measures to try for a definition whose termination relation
   the HOL4 source does not give: the arguments that are matched on,
   then each argument on its own, then all of them together *)

let candidate_measures tm =
  let fs = definition_heads tm in
  let cls = definition_clauses tm in
  if length fs > 1 then
    let combine ms =
      itlist (fun m1 m2 ->
                list_mk_comb(mk_mconst("sum_measure",
                  mk_fun_ty (type_of m1) (mk_fun_ty (type_of m2)
                    (mk_fun_ty (mk_type("sum",
                       [fst(dest_fun_ty(type_of m1));
                        fst(dest_fun_ty(type_of m2))]))
                     (mk_type("num",[]))))),[m1;m2]))
             (butlast ms) (last ms) in
    let pats = map (fun f ->
                      let p = pattern_positions f cls in
                      measure_of_positions f cls
                        (if p = [] then 0--(arity_in f cls - 1) else p))
                   fs in
    let alls = map (fun f ->
                      measure_of_positions f cls
                        (0--(arity_in f cls - 1)))
                   fs in
    [mk_measure (combine pats); mk_measure (combine alls)]
  else
    let f = hd fs in
    let n = arity_in f cls in
    let pats = pattern_positions f cls in
    let mpos = match_positions f cls in
    let cands =
      (if pats = [] then [] else [pats]) @
      (if mpos = [] then [] else [mpos]) @
      (if mpos = [] || pats = [] then [] else [union pats mpos]) @
      map (fun i -> [i]) (0--(n-1)) @
      [0--(n-1)] in
    (* setify would sort them, and the order is the order in which
       they are tried: the arguments that are matched on first *)
    let rec nub l =
      match l with
        [] -> []
      | h :: t -> h :: nub (filter (fun x -> x <> h) t) in
    let ms = map (fun idxs ->
                    mk_measure (measure_of_positions f cls idxs))
                 (nub cands) in
    (* a measure that does not look at its argument gives the
       goal 0 < 0, so it is only kept where there is nothing
       else; one of another shape is kept, as this only drops
       the ones that are plainly of no use *)
    let looks m =
      try let v,bod = dest_gabs (rand m) in
          (* the size function of a type that has none is \x. 0,
             so the body only says nothing after it is reduced *)
          let bod = beta_normalize bod in
          exists (fun x -> vfree_in x bod) (frees v)
      with Failure _ -> true in
    let good = filter looks ms in
    if good = [] then ms else good;;

let size_thms tyname =
  if not (can (assoc tyname) (!the_size_thms))
  then (try (ignore(define_size tyname) : unit)
        with Failure _ -> ());
  (* a type that the port did not define itself (list) has its size
     function in ml/lib/hol4.ml, and nothing to define here *)
  try let a,b = assoc tyname (!the_size_thms) in a @ b
  with Failure _ -> [];;

(* The definition functions that the port uses.                       *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* The definitions whose proof the port cannot do yet.  In this     *)
(* pass they are assumed: the constants are declared and the        *)
(* clauses are an axiom, so that the files that come after can be   *)
(* loaded.  They are what length(axioms()) counts beyond the three  *)
(* of HOL Light, and cake_cheats() says which ones they are.        *)
(* ------------------------------------------------------------------ *)

let the_cheats = ref ([]:string list);;

let cake_cheats () = rev (!the_cheats);;

(* a constant whose value HOL4 computes with ML code that the port
   cannot run: the constant is declared and nothing is known about
   it (which adds no axiom), and it is recorded as a cheat *)

let cake_declare name ty =
  new_constant(name,ty);
  the_cheats := name :: !the_cheats;
  print_string ("\ncake_declare " ^ name ^ " (no value)\n");
  flush stdout;;

(* the free variables of a definition that are not the functions it
   defines: those are the constants that the port does not have
   yet, and the reason why it cannot make the definition *)

let definition_free tm =
  try itlist
        (fun (_,args,r) l ->
           union (subtract (subtract (frees r) (definition_heads tm))
                           (itlist (fun a l -> union (frees a) l)
                                   args []))
                 l)
        (definition_clauses tm) []
  with Failure _ -> [];;

let the_cheat_free = ref ([]:(string * string list) list);;

let cake_cheat_free () = rev (!the_cheat_free);;

(* and why it is assumed: the message of the strategy that failed
   last, or the timeout *)

let the_cheat_why = ref ([]:(string * string) list);;

let cake_cheat_why () = rev (!the_cheat_why);;

let cheat_why = ref "";;

let note_cheat name tm =
  let free = map (fst o dest_var) (definition_free tm) in
  the_cheat_why := (name,!cheat_why) :: !the_cheat_why;
  if free <> [] then
    (the_cheat_free := (name,free) :: !the_cheat_free;
     print_string ("  (free: " ^
                   end_itlist (fun a b -> a ^ ", " ^ b) free ^ ")\n"));;

let cake_cheat tm =
  let fs = definition_heads tm in
  do_list (fun f ->
             let s,ty = dest_var f in
             if not (can get_const_type s) then new_constant(s,ty))
          fs;
  let consts = map (fun f -> mk_mconst(fst(dest_var f),type_of f),f)
                   fs in
  let cls = map (fun cl -> close_clause []
                             (vsubst consts (snd(strip_forall cl))))
                (conjuncts(snd(strip_forall tm))) in
  let name = fst(dest_var(hd fs)) in
  the_cheats := name :: !the_cheats;
  print_string ("\ncake_define " ^ name ^ " CHEATED\n");
  note_cheat name tm;
  flush stdout;
  new_axiom (list_mk_conj cls);;

(* HOL Light's machinery for a wellfounded recursion takes minutes
   over a definition with many clauses, so it only gets this many
   seconds before the definition is assumed instead (0 is no
   limit) *)

let cake_timeout = ref 30;;

exception Cake_timeout;;

(* the budget is processor time, not real time: a run shares the
   machine with whatever else is going on, and a definition is to
   get the same budget in either case *)

let with_timeout f x =
  if !cake_timeout <= 0 then f x else
  (* the exception is not a Failure, which the machinery of HOL
     Light catches all over the place *)
  (* the alarm itself is a real time one, so it goes off every
     second and looks at the processor time that is left *)
  let deadline = Sys.time() +. float_of_int (!cake_timeout) in
  let handler _ =
    if Sys.time() >= deadline then raise Cake_timeout
    else ignore(Unix.alarm 1) in
  let old = Sys.signal Sys.sigalrm (Sys.Signal_handle handler) in
  let fin () = (ignore(Unix.alarm 0); Sys.set_signal Sys.sigalrm old)
    in
  ignore(Unix.alarm 1);
  try let y = f x in (fin (); y)
  with e -> (fin (); raise e);;
(* ------------------------------------------------------------------ *)
(* A definition over a list whose clauses are [], x::y::xs and the    *)
(* singletons [C ...]: that is how CakeML writes a recursion over an  *)
(* expression and over a list of them as one function (clos_fvs's     *)
(* remove_fvs and twenty others).  HOL Light's machinery for a        *)
(* wellfounded recursion takes minutes over such a definition, so the *)
(* port defines the function on one element with the recursion        *)
(* theorem of the type and this function as its map, and derives the  *)
(* clauses as the source gives them.                                  *)
(* ------------------------------------------------------------------ *)

let is_nil tm = is_const tm && fst(dest_const tm) = "NIL";;

let dest_sing tm =
  let h,t = dest_cons tm in
  if is_nil t then h else failwith "dest_sing";;

let define_sing inner tm =
  let fs = definition_heads tm in
  if length fs <> 1 then failwith "define_sing" else
  let f = hd fs in
  let cls = definition_clauses tm in
  let n = itlist (fun (_,args,_) k -> max k (length args)) cls 0 in
  if n = 0 || exists (fun (_,args,_) -> length args <> n) cls
  then failwith "define_sing" else
  let lastarg (_,args,_) = last args in
  let nils = filter (fun c -> is_nil (lastarg c)) cls in
  let sings = filter (fun c -> can dest_sing (lastarg c)) cls in
  let conses = filter (fun c -> is_cons (lastarg c) &&
                                not (can dest_sing (lastarg c))) cls in
  if length nils <> 1 || length conses <> 1 || sings = []
  then failwith "define_sing" else
  if length (nils @ sings @ conses) <> length cls
  then failwith "define_sing" else
  (* the element type and the type of the elements it gives back *)
  let ty = hd(snd(dest_type(type_of(lastarg (hd sings))))) in
  let _,_,r0 = hd sings in
  let rty = hd(snd(dest_type(type_of r0))) in
  (* a name for the function on one element *)
  let rec new_name s i =
    let s' = if i = 0 then s else s ^ string_of_int i in
    if can get_const_type s' || mem s' (!the_defining) ||
       exists (fun g -> fst(dest_var g) = s') fs
    then new_name s (i + 1) else s' in
  let _,args0,_ = hd conses in
  let vs = butlast args0 in
  let g = mk_var(new_name (fst(dest_var f) ^ "_el") 0,
                 itlist (fun v t -> mk_fun_ty (type_of v) t) vs
                        (mk_fun_ty ty rty)) in
  let mapc t = mk_mconst("MAP",mk_fun_ty (mk_fun_ty ty rty)
                 (mk_fun_ty (mk_type("list",[ty]))
                            (mk_type("list",[rty])))) in
  let rec repl t =
    let h,args = strip_comb t in
    if h = f && length args = n then
      let as_ = map repl (butlast args) and l = last args in
      (try let e = dest_sing l in
           mk_cons (list_mk_comb(g,as_ @ [repl e])) (mk_list([],rty))
       with Failure _ ->
         list_mk_comb(mapc t,[list_mk_comb(g,as_); repl l]))
    else
      match t with
        Comb(s,u) -> mk_comb(repl s,repl u)
      | Abs(v,b) -> mk_abs(v,repl b)
      | _ -> t in
  (* the element that a right hand side of a singleton clause
     gives: the clauses give a list of one element *)
  let rec elem r =
    if is_cond r then
      let c,(a,b) = dest_cond r in mk_cond(c,elem a,elem b)
    else
      let h,args = strip_comb r in
      if is_const h && fst(dest_const h) = "LET" && args <> [] &&
         (let b = snd(strip_abs (hd args)) in
          let h2,a2 = strip_comb b in
          is_const h2 && fst(dest_const h2) = "LET_END" &&
          length a2 = 1)
      then
        let vs,b = strip_abs (hd args) in
        let b' = elem (rand b) in
        let f' = list_mk_abs(vs,
                   mk_comb(mk_mconst("LET_END",
                             mk_fun_ty (type_of b') (type_of b')),
                           b')) in
        let vals = tl args in
        let lty = mk_fun_ty (type_of f')
                    (itlist (fun v t -> mk_fun_ty (type_of v) t)
                            vals (type_of b')) in
        list_mk_comb(mk_mconst("LET",lty),f' :: vals)
      else try dest_sing r with Failure _ ->
        mk_comb(mk_mconst("HD",
                  mk_fun_ty (mk_type("list",[rty])) rty),r) in
  let gcls =
    map (fun (_,args,r) ->
           close_clause [g]
             (mk_eq(list_mk_comb(g,map repl (butlast args) @
                                   [dest_sing (last args)]),
                    elem (repl r))))
        sings in
  let ths,spec = inner (list_mk_conj gcls) in
  (* the function itself is the map of the one on an element *)
  let gc = mk_mconst(fst(dest_var g),type_of g) in
  let l = variant vs (mk_var("l",mk_type("list",[ty]))) in
  let fdef = new_definition
    (mk_eq(list_mk_comb(f,vs @ [l]),
           list_mk_comb(mapc l,[list_mk_comb(gc,vs); l]))) in
  let consts = [mk_mconst(fst(dest_var f),type_of f),f] in
  let derive cl =
    let gcl = close_clause [] (vsubst consts (snd(strip_forall cl))) in
    prove(gcl,
          REPEAT GEN_TAC THEN
          REWRITE_TAC([fdef; MAP; HD; APPEND] @ ths) THEN
          REPEAT (CHANGED_TAC
            (COND_CASES_TAC THEN
             REWRITE_TAC([fdef; MAP; HD; APPEND] @ ths))) THEN
          REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
          CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
          REWRITE_TAC([fdef; MAP; HD; APPEND] @ ths)) in
  map derive (conjuncts(snd(strip_forall tm))),spec;;

(* ------------------------------------------------------------------ *)
(* A block that defines a function on one element and the map of it   *)
(* over a list (CakeML writes the recursions over an expression that  *)
(* way as well: remove_fvs_sing and remove_fvs_list of clos_fvs).     *)
(* The port defines the functions on an element with the recursion    *)
(* theorem of the type, the one over the list as the map of the       *)
(* element it gives, and derives the clauses as they are given.       *)
(* ------------------------------------------------------------------ *)

(* the ways in which the list function of a pair puts the
   elements together: the map of the element function over the
   list (CONS), the conjunction or the disjunction of a predicate
   over the elements, and the concatenation of the lists that the
   element function gives *)

let maplist_kind r nr =
  if is_cons r && is_nil nr then "MAP"
  else if is_conj r && nr = `T` then "ALL"
  else if is_disj r && nr = `F` then "EX"
  else if is_nil nr && is_comb r && is_comb(rator r) &&
          name_of(rator(rator r)) = "APPEND" then "FLAT"
  else failwith "maplist_kind";;

let maplist_parts k r =
  if k = "MAP" then dest_cons r
  else if k = "ALL" then dest_conj r
  else if k = "EX" then dest_disj r
  else lhand r,rand r;;

(* the list function itself, of the function g on an element and
   the list l *)

let maplist_term k g l rty ty =
  let lty = mk_type("list",[ty]) in
  if k = "ALL" || k = "EX" then
    list_mk_comb(mk_mconst(k,
      mk_fun_ty (type_of g) (mk_fun_ty lty bool_ty)),[g;l])
  else
    let m = list_mk_comb(mk_mconst("MAP",
              mk_fun_ty (type_of g)
                (mk_fun_ty lty (mk_type("list",[rty])))),[g;l]) in
    if k = "MAP" then m
    else mk_comb(mk_mconst("FLAT",
           mk_fun_ty (type_of m) rty),m);;

let define_maplist inner tm =
  let fs = definition_heads tm in
  if length fs < 2 then failwith "define_maplist" else
  let cls = definition_clauses tm in
  let allcls = conjuncts(snd(strip_forall tm)) in
  (* the function whose clauses are [] and x::xs, with the cons
     clause giving the element that another function of the block
     gives *)
  let parts f =
    let mycls = filter (fun (g,_,_) -> g = f) cls in
    if length mycls <> 2 then failwith "parts" else
    let _,_,nrhs = find (fun (_,args,_) -> args <> [] &&
                                           is_nil (last args)) mycls in
    let _,cargs,crhs = find (fun (_,args,_) -> args <> [] &&
                                               is_cons (last args))
                            mycls in
    f,(maplist_kind crhs nrhs,cargs,crhs) in
  let fl,(kind,cargs,crhs) =
    try hd (mapfilter parts fs)
    with Failure _ -> failwith "define_maplist" in
  let x,xs = dest_cons (last cargs) in
  let el,rest = maplist_parts kind crhs in
  (* the tail of the right hand side is the function itself on the
     tail of the list, and the head is the element, which is made
     of the head of the list and the other arguments (the pattern
     of the head may be a pair) *)
  if rest <> list_mk_comb(fl,butlast cargs @ [xs]) then
    failwith "define_maplist" else
  let vs = butlast cargs in
  if not (subset (frees el)
            (union (frees x)
               (union fs (itlist (fun v l -> union (frees v) l)
                                 vs [])))) then
    failwith "define_maplist" else
  (* the element may not be the function itself: that would be a
     recursion that this does not take apart *)
  if free_in fl el then failwith "define_maplist" else
  let rty = type_of el and ty = type_of x in
  let n = length cargs in
  let rec repl t =
    let g,args = strip_comb t in
    if g = fl && length args = n then
      let sub = filter (fun (a,b) -> a <> b)
                       (zip (map repl (butlast args)) vs) in
      maplist_term kind (mk_gabs(x,vsubst sub (repl el)))
                   (repl (last args)) rty ty
    else
      match t with
        Comb(s,u) -> mk_comb(repl s,repl u)
      | Abs(v,b) -> mk_abs(v,repl b)
      | _ -> t in
  let others = filter (fun cl ->
                   fst(strip_comb(lhs(snd(strip_forall cl)))) <> fl)
                 allcls in
  if others = [] then failwith "define_maplist" else
  let newcls = map (fun cl ->
                      let l,r = dest_eq(snd(strip_forall cl)) in
                      close_clause fs (mk_eq(l,repl r)))
                   others in
  let ths,spec = inner (list_mk_conj newcls) in
  let consts0 = map (fun f -> mk_mconst(fst(dest_var f),type_of f),f)
                    (filter (fun f -> f <> fl) fs) in
  let l = variant (vs @ frees el) (mk_var("l",mk_type("list",[ty]))) in
  let fldef = new_definition
    (mk_eq(list_mk_comb(fl,vs @ [l]),
           maplist_term kind (mk_gabs(x,vsubst consts0 el)) l
                        rty ty)) in
  let consts = map (fun f -> mk_mconst(fst(dest_var f),type_of f),f)
                   fs in
  let derive cl =
    let gcl = close_clause [] (vsubst consts (snd(strip_forall cl))) in
    prove(gcl,
          REPEAT GEN_TAC THEN
          REWRITE_TAC([fldef; MAP; ALL; EX; FLAT; APPEND] @ ths)
            THEN
          CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
          REWRITE_TAC([fldef; MAP; ALL; EX; FLAT; APPEND] @ ths)
            THEN
          REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
          CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
          REWRITE_TAC([fldef; MAP; ALL; EX; FLAT; APPEND] @ ths)) in
  map derive allcls,spec;;

(* ------------------------------------------------------------------ *)
(* A recursive call inside a conditional that is not the whole right  *)
(* hand side of a clause.  HOL Light's machinery for a wellfounded    *)
(* recursion takes the condition of such a conditional as true, so    *)
(* the termination condition that it asks for is not the one that     *)
(* holds (presLang's num_to_hex calls itself on n DIV 16, which is    *)
(* smaller than n only where 16 <= n).  The port lifts the            *)
(* conditional to the top of the clause, where HOL Light does use     *)
(* the condition, and derives the clause as the source gives it.      *)
(* ------------------------------------------------------------------ *)

let rec lift_conds fs r =
  if is_cond r then
    let c,(a,b) = dest_cond r in
    mk_cond(c,lift_conds fs a,lift_conds fs b)
  else
    let rec look t =
      if is_cond t && exists (fun f -> free_in f t) fs then Some t
      else match t with
        Comb(s,u) -> (match look s with
                        Some x -> Some x | None -> look u)
      | _ -> None in
    match look r with
      None -> r
    | Some t ->
        let c,(a,b) = dest_cond t in
        lift_conds fs (mk_cond(c,subst [a,t] r,subst [b,t] r));;

let define_lift_if inner tm =
  let fs = definition_heads tm in
  let cls = conjuncts(snd(strip_forall tm)) in
  let lift cl =
    let l,r = dest_eq(snd(strip_forall cl)) in
    let r' = lift_conds fs r in
    if r' = r then cl else close_clause fs (mk_eq(l,r')) in
  let newcls = map lift cls in
  if newcls = cls then failwith "define_lift_if" else
  let ths,spec = inner (list_mk_conj (map (close_clause fs) newcls)) in
  let consts = map (fun f -> mk_mconst(fst(dest_var f),type_of f),f)
                   fs in
  let derive cl =
    let gcl = close_clause [] (vsubst consts (snd(strip_forall cl))) in
    prove(gcl,
      REPEAT GEN_TAC THEN
      GEN_REWRITE_TAC LAND_CONV ths THEN
      REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[]) in
  map derive cls,spec;;

(* ------------------------------------------------------------------ *)
(* A list function that folds with a conditional.                     *)
(*                                                                    *)
(* HOL4 writes `if f x then T else g xs` where the definition means   *)
(* `f x \/ g xs` (bvi_tailrec's has_rec_sing), and define_maplist     *)
(* only sees the connective.  The clauses are rewritten with the two  *)
(* tautologies, the definition is made from them, and the clauses as  *)
(* they were given are derived from it.                               *)
(* ------------------------------------------------------------------ *)

let COND_T_OR = TAUT `(if a then T else b) <=> a \/ b`
and COND_F_AND = TAUT `(if a then b else F) <=> a /\ b`;;

let define_cond_bool inner tm =
  let fs = definition_heads tm in
  let cls = conjuncts(snd(strip_forall tm)) in
  let changed = ref false in
  let newcl cl =
    let l,r = dest_eq(snd(strip_forall cl)) in
    let r' = try rand(concl(PURE_REWRITE_CONV[COND_T_OR; COND_F_AND]
                              r))
             with Failure _ -> r in
    if r' <> r then changed := true;
    close_clause fs (mk_eq(l,r')) in
  let newcls = map newcl cls in
  if not (!changed) then failwith "define_cond_bool" else
  (* only where the rewriting makes the shape that define_maplist
     takes: a definition that merely has a conditional in it
     somewhere would otherwise go through all the strategies a
     second time and spend the budget twice *)
  let ths,spec = define_maplist inner (list_mk_conj newcls) in
  let consts = map (fun f -> mk_mconst(fst(dest_var f),type_of f),f)
                   fs in
  let derive cl =
    let gcl = close_clause [] (vsubst consts (snd(strip_forall cl))) in
    prove(gcl,
          REPEAT GEN_TAC THEN
          REWRITE_TAC(COND_T_OR :: COND_F_AND :: ths)) in
  map derive cls,spec;;

let cake_define_gen wf tm =
  the_cond_why := "";
  let fs0 = definition_heads tm in
  the_defining := map (fst o dest_var) fs0;
  (* an attempt that fails after it has made the constant cannot be
     followed by another one *)
  let declared () =
    exists (fun g -> can get_const_type (fst(dest_var g))) fs0 in
  let rec strategies tm =
    let fs = definition_heads tm in
    let cls = definition_clauses tm in
    let recursive =
      exists (fun (_,_,r) -> exists (fun f -> vfree_in f r) fs) cls in
    let attempt wfs =
      if length fs = 1 then define_single wfs tm
      else define_mutual wfs tm in
    if not recursive then
      (if length fs = 1 then
         (if length cls = 1
          then (try [new_definition tm],TRUTH
                with Failure _ -> define_single [] tm)
          else
            (* a definition by cases on one argument is an instance
               of the recursion theorem of the type, which is much
               faster than HOL Light's machinery for patterns *)
            (try define_prim_rec tm
             with Failure _ when not (declared ()) ->
             define_single [] tm))
       else
         itlist
           (fun f (l,th) ->
              let mycls = filter (fun cl ->
                            fst(strip_comb(lhs(snd(strip_forall cl)))) =
                              f)
                            (conjuncts(snd(strip_forall tm))) in
              let ths,th' = define_single [] (list_mk_conj mycls) in
              ths @ l,th')
           fs ([],TRUTH))
    else
      let strat s f = (the_strategy := s; f ()) in
      (try strat "prim_rec" (fun () -> define_prim_rec tm)
       with Failure _ when not (declared ()) ->
       try strat "nested" (fun () -> define_nested tm)
       with Failure _ when not (declared ()) ->
       try strat "maplist" (fun () -> define_maplist strategies tm)
       with Failure _ when not (declared ()) ->
       try strat "cond_bool" (fun () -> define_cond_bool strategies tm)
       with Failure _ when not (declared ()) ->
       try strat "sing" (fun () -> define_sing strategies tm)
       with Failure _ when not (declared ()) ->
       try strat "cases" (fun () -> define_cases tm)
       with Failure _ when not (declared ()) ->
       try strat "match" (fun () -> define_match tm)
       with Failure _ when not (declared ()) ->
       try strat "lift_if" (fun () -> define_lift_if strategies tm)
       with Failure _ when not (declared ()) ->
       let given = match wf with Some rt -> [rt] | None -> [] in
       let cands = given @ map (fun rel -> rel,TERM_TAC)
                               (candidate_measures tm) in
       try strat "measure" (fun () -> attempt cands)
       with Failure _ when not (declared ()) ->
       strat "guess" (fun () -> attempt [])) in
  (* a clause with a free variable that is not one of the
     functions being defined uses a constant that the port does
     not have: no strategy can make such a definition, so it is
     assumed at once *)
  let free = definition_free tm in
  (* every way of making the definition together gets the budget;
     what is left after it is assumed *)
  let ths,_ =
    if free <> [] then
      (cheat_why :=
         "free: " ^ end_itlist (fun a b -> a ^ ", " ^ b)
                               (map (fst o dest_var) free);
       [cake_cheat tm],TRUTH)
    else
    try (the_strategy := ""; with_timeout strategies tm)
    with Cake_timeout ->
           (cheat_why := "timeout in " ^ !the_strategy;
            [cake_cheat tm],TRUTH)
       | Failure e ->
           (* "tryfind" is the strategy that gives up, which says
              nothing; the condition that could not be discharged
              says what the definition asks for *)
           (cheat_why :=
              (if e = "tryfind" && !the_cond_why <> ""
               then "tryfind: " ^ !the_cond_why else e);
            [cake_cheat tm],TRUTH) in
  end_itlist CONJ ths;;

(* with cake_timing set, every definition reports how long it took *)

let cake_timing = ref false;;

(* how long every definition took, which says where the time of
   a run goes *)

let the_times = ref ([]:(string * float) list);;

let cake_times () = rev (!the_times);;

let cake_time f x =
  let t = Sys.time() in
  let y = f x in
  let dt = Sys.time() -. t in
  (try the_times :=
         (fst(dest_var(hd(definition_heads x))),dt) :: !the_times
   with Failure _ -> ());
  if !cake_timing then
    (print_string (Printf.sprintf "[%.2fs] " dt); flush stdout);
  y;;

(* on failure, say which definition failed (and show it when
   cake_debug is set) *)

let cake_report tm s =
  let name =
    try fst(dest_var(hd(definition_heads tm))) with Failure _ -> "?" in
  (* a free variable that is not one of the functions being defined
     is a constant that the port does not have yet *)
  let free =
    try itlist
          (fun (_,args,r) l ->
             union (subtract (subtract (frees r) (definition_heads tm))
                             (itlist (fun a l -> union (frees a) l)
                                     args []))
                   l)
          (definition_clauses tm) []
    with Failure _ -> [] in
  let s = if free = [] then s else
          s ^ " (free: " ^
          end_itlist (fun a b -> a ^ ", " ^ b)
                     (map (fst o dest_var) free) ^ ")" in
  print_string ("\ncake_define " ^ name ^ " failed: " ^ s ^ "\n");
  flush stdout;
  if !cake_debug then
    (cake_log ("cake_define " ^ name ^ " failed: " ^ s);
     cake_log_term tm);
  failwith s;;

let cake_destfacts = ref true;;

(* ------------------------------------------------------------------ *)
(* The size fact of a destructor.                                     *)
(*                                                                    *)
(* A definition of one clause whose body is a match on an argument    *)
(* and whose arms give SOME of the parts of the pattern is a          *)
(* destructor (bvi_tailrec's get_bin_args, bvl_handle's dest_Seq,     *)
(* clos_op's dest_Op, ...).  The termination proof of a definition    *)
(* that uses one asks for the fact that the parts are smaller than    *)
(* what they were taken from, which HOL4 states and proves by hand;   *)
(* here it is made and registered with the definition itself.         *)
(* ------------------------------------------------------------------ *)

let list_type_of ty =
  match dest_type ty with
    "list",[t] -> t
  | _ -> failwith "list_type_of";;

(* a variable of a list type that the goal still matches on *)

(* what the matches of a term look at *)

let match_scruts tm =
  let rec go t acc =
    let acc =
      match t with
        Comb(Comb(Const("_MATCH",_),sc),_) -> insert sc acc
      | _ -> acc in
    match t with
      Comb(a,b) -> go a (go b acc)
    | Abs(_,b) -> go b acc
    | _ -> acc in
  go tm [];;

(* a variable of a list type that the goal still matches on: one
   that the match does not look at is not split, because the
   equation that the arm gives says what it is *)

let LIST_SPLIT_TAC (asl,w as gl) =
  let vs = filter (fun v -> can list_type_of (type_of v))
                  (itlist (fun s l -> union (frees s) l)
                          (match_scruts w) []) in
  if vs = [] then failwith "LIST_SPLIT_TAC" else
  MAP_EVERY (fun v -> STRUCT_CASES_TAC (ISPEC v list_CASES)) vs gl;;

(* the cases theorem of a type of a family of them *)

let cases_of ty =
  let ths = CONJUNCTS (cases (fst(dest_type ty))) in
  try find (fun th -> type_of(fst(dest_forall(concl th))) = ty) ths
  with Failure _ -> hd ths;;

(* the scrutinee of a match of the goal that is not a variable:
   the arm of a destructor may look at the value of another
   function (clos_op's dest_Op), and the match on it only goes
   away when that value is taken apart *)

let MATCH_SCRUT_TAC (asl,w as gl) =
  let scruts tm = filter (fun t -> not (is_var t)) (match_scruts tm) in
  let ok sc =
    can (fun t -> cases_of (type_of t)) sc &&
    not (is_const (fst(strip_comb sc))) in
  let ts = filter ok (scruts w) in
  if ts = [] then failwith "MATCH_SCRUT_TAC" else
  MAP_EVERY (fun t -> STRUCT_CASES_TAC (ISPEC t (cases_of (type_of t))))
            ts gl;;

let dest_size_fact th =
  let tm = snd(strip_forall(concl th)) in
  let l,r = dest_eq tm in
  let f,args = strip_comb l in
  if args = [] || not (is_var (last args)) then
    failwith "dest_size_fact" else
  (* a recursive definition is no destructor, and rewriting with
     one would not stop *)
  if free_in f r then failwith "dest_size_fact" else
  let x = last args in
  let ty = type_of x in
  let tyname = fst(dest_type ty) in
  if not (can (assoc tyname) (!the_rec_thms)) then
    failwith "dest_size_fact" else
  (match dest_type (type_of l) with
     "option",_ -> () | _ -> failwith "dest_size_fact");
  (* the body is a match on the argument: that is a destructor,
     where a definition that looks at the value of another one
     (clos_op's dest_Op_Nil) is not *)
  let hop,margs = strip_comb r in
  if not (is_const hop && fst(dest_const hop) = "_MATCH") ||
     length margs <> 2 || hd margs <> x
  then failwith "dest_size_fact" else
  let pty = hd(snd(dest_type (type_of l))) in
  let rec parts ty =
    if is_vartype ty then [ty] else
    match dest_type ty with
      "prod",[a;b] -> parts a @ parts b
    | _ -> [ty] in
  let ptys = parts pty in
  let vs = map2 (fun t i -> mk_var("a" ^ string_of_int i,t))
                ptys (0--(length ptys - 1)) in
  let tuple = end_itlist (curry mk_pair) vs in
  (* a part of a type that has no size function of its own (a
     number, a word) counts for nothing, and a fact in which no
     part counts says nothing *)
  let sizefn t = try size_fn_of_type t
                 with Failure _ -> mk_abs(mk_var("x",t),`0`) in
  let sizes = map (fun v -> beta_normalize
                              (mk_comb(sizefn (type_of v),v))) vs in
  if not (exists (fun (v,s) -> vfree_in v s) (zip vs sizes)) then
    failwith "dest_size_fact" else
  let sum = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
                       sizes in
  let goal =
    list_mk_forall(args @ vs,
      mk_imp(mk_eq(l,mk_comb(mk_mconst("SOME",
                               mk_fun_ty pty (type_of l)),tuple)),
             mk_binop `(<):num->num->bool` sum
                      (mk_comb(size_fn_of_type ty,x)))) in
  let _ = size_thms tyname in
  let rws () = [distinctness "option"; injectivity "option";
                PAIR_EQ; list_size; th] @ all_size_thms() in
  prove(goal,
        REPEAT GEN_TAC THEN
        STRUCT_CASES_TAC (ISPEC x (cases_of ty)) THEN
        REWRITE_TAC(rws()) THEN
        REPLICATE_TAC 3
          ((* the value that an arm looks at first: the parts
              that the arm gives are only known once the match
              on it is gone *)
           TRY (MATCH_SCRUT_TAC THEN REWRITE_TAC(rws())) THEN
           TRY (LIST_SPLIT_TAC THEN REWRITE_TAC(rws()))) THEN
        (* a pattern that asks for a value that the arm does not
           give (bvl_handle's dest_Seq matches on Var 1) leaves a
           match that the rewriting does not reduce *)
        TRY (CONV_TAC (ONCE_DEPTH_CONV MATCH_CONV)) THEN
        REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC(rws()) THEN
        REPEAT (DISCH_THEN
                  (STRIP_ASSUME_TAC o REWRITE_RULE(rws()))) THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC(rws()) THEN ARITH_TAC);;

(* every definition that is one is registered as a fact; the
   budget is a short one, because most definitions are no
   destructor and the proof is only a help *)

let note_dest_fact th =
  if !cake_destfacts then
    let old = !cake_timeout in
    let fin () = cake_timeout := old in
    (cake_timeout := 10;
     (try cake_term_facts := dest_size_fact th :: (!cake_term_facts)
      with Failure _ -> () | Cake_timeout -> ());
     fin ());;

let cake_define tm =
  try let th = cake_time (cake_define_gen None) tm in
      note_dest_fact th; th
  with Failure s -> cake_report tm s;;

(* the clauses of a definition as separate terms, for a definition
   in which the same variable name has different types in different
   clauses (HOL4 typechecks every clause on its own) *)

(* unification of two types, which HOL Light does not have (it has
   matching, which is not enough here) *)

let rec tyunify ins ty1 ty2 =
  let ty1 = type_subst ins ty1 and ty2 = type_subst ins ty2 in
  if ty1 = ty2 then ins
  else if is_vartype ty1 then
    (if mem ty1 (tyvars ty2) then failwith "tyunify" else
     (ty2,ty1) :: map (fun (t,v) -> type_subst [ty2,ty1] t,v) ins)
  else if is_vartype ty2 then tyunify ins ty2 ty1
  else
    let op1,args1 = dest_type ty1 and op2,args2 = dest_type ty2 in
    if op1 <> op2 || length args1 <> length args2
    then failwith "tyunify"
    else itlist2 (fun a b ins -> tyunify ins a b) args1 args2 ins;;

let cake_conj_list cls =
  (* every clause is typechecked on its own, so the function that
     they define can have a different type in each of them (HOL4
     typechecks them separately as well, but has one constant); the
     types are unified here *)
  let head cl = fst(strip_comb(lhs(snd(strip_forall cl)))) in
  let names = setify (map (fun cl -> fst(dest_var(head cl))) cls) in
  let ins =
    itlist
      (fun nm ins ->
         let tys = map type_of
                       (filter (fun v -> fst(dest_var v) = nm)
                               (itlist (fun cl l -> union (frees cl) l)
                                       cls [])) in
         itlist
           (fun ty ins ->
              try tyunify ins (hd tys) ty
              with Failure _ ->
                failwith (nm ^ " has the types " ^
                          string_of_type (hd tys) ^ " and " ^
                          string_of_type ty))
           (tl tys) ins)
      names [] in
  list_mk_conj (map (inst ins) cls);;

(* when the clauses do not fit together (the types that they get on
   their own cannot be unified), they are assumed one by one, with
   the type of the first clause of a function for its constant *)

let cake_cheat_list cls =
  let head cl = fst(strip_comb(lhs(snd(strip_forall cl)))) in
  let fs = itlist (fun cl l ->
                     let f = head cl in
                     if exists (fun g -> fst(dest_var g) =
                                         fst(dest_var f)) l
                     then l else l @ [f])
                  cls [] in
  do_list (fun f ->
             let s,ty = dest_var f in
             if not (can get_const_type s) then new_constant(s,ty))
          fs;
  let name = fst(dest_var(hd fs)) in
  the_cheats := name :: !the_cheats;
  print_string ("\ncake_define " ^ name ^ " CHEATED (clause by " ^
                "clause)\n");
  note_cheat name (list_mk_conj (map (close_clause []) cls));
  flush stdout;
  (* only the functions that the clauses define become constants; a
     variable whose name is a constant of something else stays a
     variable, which close_clause quantifies *)
  let cheat cl =
    let vs = filter (fun v -> exists (fun g -> fst(dest_var g) =
                                               fst(dest_var v)) fs)
                    (frees cl) in
    let consts = mapfilter
                   (fun v -> mk_mconst(fst(dest_var v),type_of v),v)
                   vs in
    new_axiom (close_clause [] (vsubst consts cl)) in
  let ths = mapfilter cheat cls in
  (* the last resort must not fail: the constants are there, and the
     clauses are recorded as a cheat that gives nothing *)
  if ths = [] then
    (print_string ("\ncake_define " ^ name ^
                   " CHEATED (no clause)\n"); flush stdout; TRUTH)
  else end_itlist CONJ ths;;

let cake_define_list cls =
  (* the clauses are typechecked on their own, so the types that
     they give the functions they define have to be unified first;
     where that fails the clauses are assumed one by one, and the
     reason is reported, as it is a bug of the port *)
  match (try Some(cake_conj_list cls) with Failure s ->
           (print_string ("\ncake_conj_list failed: " ^ s ^ "\n");
            flush stdout; None)) with
    Some tm -> cake_define tm
  | None -> cake_cheat_list cls;;

let cake_define_wf rel tm =
  try cake_time (cake_define_gen (Some(rel,TERM_TAC))) tm
  with Failure s -> cake_report tm s;;

(* HOL4's Inductive: HOL Light's new_inductive_definition takes the
   same shape of rules and gives the rules, the induction principle
   and the cases theorem *)

(* HOL4's Hol_reln quantifies the free variables of a rule itself,
   where HOL Light wants them quantified (parmove's step comes from
   a quotation that HOL4 builds with ML code, and has none) *)

let close_rules tm =
  let rules = conjuncts tm in
  let head r =
    let r = snd(strip_forall r) in
    fst(strip_comb (if is_imp r then rand r else r)) in
  let rels = setify (map head rules) in
  let close r = list_mk_forall(subtract (frees r) rels,r) in
  list_mk_conj (map close rules);;

(* the relations that the rules of an inductive definition
   define: the head of the conclusion of every rule *)

let rule_heads tm =
  itlist
    (fun cl l ->
       let c = snd(strip_forall cl) in
       let c = if is_imp c then rand c else c in
       let f = fst(strip_comb c) in
       if is_var f && not (mem f l) then f :: l else l)
    (conjuncts(snd(strip_forall tm))) [];;

(* an inductive definition that HOL Light does not make: the
   relations are declared and the rules are an axiom.  That is
   weaker than the definition (it does not say that the relation
   is the least one that the rules give), so there is no
   induction theorem, and the second pass has to make the
   definition itself *)

let cake_cheat_rules tm =
  let fs = rule_heads tm in
  do_list (fun f ->
             let s,ty = dest_var f in
             if not (can get_const_type s) then new_constant(s,ty))
          fs;
  let consts = map (fun f -> mk_mconst(fst(dest_var f),type_of f),f)
                   fs in
  let name = fst(dest_var(hd fs)) in
  the_cheats := name :: !the_cheats;
  print_string ("\ncake_inductive " ^ name ^ " CHEATED\n");
  note_cheat name tm;
  flush stdout;
  new_axiom (vsubst consts (snd(strip_forall tm)));;

let cake_inductive tm =
  let rtm = close_rules tm in
  try cake_time new_inductive_definition rtm
  with Failure s ->
    (cheat_why := s;
     print_string ("\ncake_inductive failed: " ^ s ^ "\n");
     flush stdout;
     (cake_cheat_rules rtm,TRUTH,TRUTH));;

let cake_define_list_wf rel cls =
  cake_define_wf rel (cake_conj_list cls);;

(* the same, with the relation of HOL4 in a function, so that a
   relation that does not typecheck is no error of the file: it
   is only the measure that the definition then has to guess *)

let cake_define_list_try f cls =
  match (try Some (f ()) with Failure _ -> None) with
    Some rel -> cake_define_list_wf rel cls
  | None -> cake_define_list cls;;

let cake_define_tac (rel,tac) tm =
  try cake_time (cake_define_gen (Some(rel,tac))) tm
  with Failure s -> cake_report tm s;;

(* ------------------------------------------------------------------ *)
