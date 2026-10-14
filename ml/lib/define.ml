(* ========================================================================= *)
(*  HOL4's Definition for HOL Light.                                        *)
(*                                                                          *)
(*  cake_define handles what HOL4's Define handles, as far as CakeML needs   *)
(*  it:                                                                     *)
(*                                                                          *)
(*    not recursive                   -> new_definition                      *)
(*    primitive recursive             -> new_recursive_definition            *)
(*    otherwise recursive             -> define                             *)
(*    mutually recursive              -> encoded in a sum type              *)
(*                                                                          *)
(*  For definitions whose termination HOL Light cannot guess there are       *)
(*                                                                          *)
(*    cake_define_wf `relation` `clauses`                                    *)
(*    cake_define_tac (`relation`,tactic) `clauses`                          *)
(*                                                                          *)
(*  where the relation is the one of HOL4's WF_REL_TAC.  HOL4's             *)
(*  `measure f` is `MEASURE f`, `inv_image R f` is `\x y. R (f x) (f y)`     *)
(*  and `R1 LEX R2` is `\(x1,y1) (x2,y2). R1 x1 x2 \/ x1 = x2 /\ R2 y1 y2`,  *)
(*  which are the HOL Light forms of the same notions (see WF_MEASURE,       *)
(*  WF_MEASURE_GEN and WF_LEX).  For mutually recursive functions the        *)
(*  relation is one on the sum of the tupled arguments, as in HOL4.          *)
(* ========================================================================= *)

(* with cake_debug set, a failing definition is written to
   cakeml/tmp/debug.txt *)

let cake_debug = ref false;;

let cake_log s =
  let ch = open_out_gen [Open_append; Open_creat] 0o644
             "/home/freek/claude/hol-light/cakeml/tmp/debug.txt" in
  output_string ch s; output_string ch "\n"; close_out ch;;

let cake_log_term tm =
  cake_log (string_of_term tm);;

(* ------------------------------------------------------------------------- *)
(* Tuples and sums.                                                          *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* The clauses of a definition and the functions it defines.                 *)
(* ------------------------------------------------------------------------- *)

let definition_clauses tm =
  map (fun cl ->
        let bod = snd(strip_forall cl) in
        let l,r = dest_eq bod in
        let f,args = strip_comb l in
        f,args,r)
      (conjuncts(snd(strip_forall tm)));;

let definition_heads tm =
  itlist (fun (f,_,_) l -> if mem f l then l else f::l)
         (definition_clauses tm) [];;

(* universally quantify a clause over its variables *)

let close_clause fs cl =
  let bod = snd(strip_forall cl) in
  list_mk_forall(subtract (frees bod) fs,bod);;

let beta_normalize tm =
  try rhs(concl(TOP_DEPTH_CONV BETA_CONV tm)) with Failure _ -> tm;;

(* ------------------------------------------------------------------------- *)
(* Discharging the side conditions of an existence theorem.                  *)
(* ------------------------------------------------------------------------- *)

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
       list_size_APPEND; list_size_REVERSE];;

(* when a termination proof does not close, the goal is logged *)

let LOG_TAC (asl,w) =
  cake_log "unsolved termination goal:";
  cake_log_term w;
  do_list (fun (_,th) -> cake_log ("  asm: " ^ string_of_term(concl th)))
          asl;
  failwith "LOG_TAC";;

let TERM_TAC g =
  (REWRITE_TAC[MEASURE; LEX; inv_image; FORALL_PAIR_THM] THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   REWRITE_TAC(all_size_thms()) THEN
   RULE_ASSUM_TAC(REWRITE_RULE(all_size_thms())) THEN
   MEM_SIZE_TAC THEN DIV_FACTS_TAC THEN
   REWRITE_TAC(I_THM::all_size_thms() @ (!cake_term_lemmas)) THEN
   (ASM_ARITH_TAC ORELSE
    (ASM_SIMP_TAC(all_size_thms() @ (!cake_term_lemmas)) THEN
     ASM_ARITH_TAC) ORELSE
    (if !cake_debug then LOG_TAC else NO_TAC))) g;;

let discharge_conditions (rel,tac) th =
  itlist
    (fun h th ->
       let gtac =
         if is_exists h then
           let v,_ = dest_exists h in
           let rel' = inst (type_match (type_of rel) (type_of v) []) rel in
           EXISTS_TAC rel' THEN CONJ_TAC THENL [WF_TAC; tac]
         else tac in
       let hth =
         try prove(h,gtac)
         with Failure s ->
           (if !cake_debug then
              (cake_log ("cannot prove the condition (" ^ s ^
                         ") with the relation");
               cake_log_term rel;
               cake_log "for the condition:";
               cake_log_term h);
            failwith s) in
       PROVE_HYP hth th)
    (hyp th) th;;

(* ------------------------------------------------------------------------- *)
(* Taking paired lambdas apart.                                              *)
(*                                                                          *)
(* HOL Light's machinery for the admissibility of a recursion loses the      *)
(* connection between the pattern of a paired lambda and the argument it     *)
(* is applied to, so that for instance                                      *)
(*                                                                          *)
(*   nsMap f (Bind v m) = Bind (MAP (\(n,x). (n,f x)) v)                     *)
(*                             (MAP (\(mn,e). (mn,nsMap f e)) m)             *)
(*                                                                          *)
(* gets an unprovable termination condition.  Therefore such a definition    *)
(* is made with \p. ... FST p ... SND p ... instead, and the definition as   *)
(* it was given is then derived from it.                                     *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* Putting the recursive calls under a MAP.                                  *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* Definition of one function, with a given termination relation.            *)
(* ------------------------------------------------------------------------- *)

let define_single wfs tm =
  let fs = definition_heads tm in
  let f = hd fs in
  let name = fst(dest_var f) in
  let cls = map (close_clause fs) (conjuncts(snd(strip_forall tm))) in
  let existence cls =
    let etm = mk_exists(f,list_mk_conj cls) in
    if wfs = [] then prove_general_recursive_function_exists etm else
    let th = pure_prove_recursive_function_exists etm in
    if hyp th = [] then th
    else tryfind (fun rt -> discharge_conditions rt th) wfs in
  try let dth = new_specification [name] (existence cls) in
      CONJUNCTS dth,dth
  with Failure _ ->
    (* the recursive calls may be under a lambda with a pattern, or
       under ALL or EX, which HOL Light's machinery cannot handle *)
    let cls' = map (fun cl -> mapify [f] (depair cl)) cls in
    if cls' = cls then failwith "define_single" else
    let dth = new_specification [name] (existence cls') in
    let c = mk_mconst(name,type_of f) in
    let dths = CONJUNCTS dth in
    let derive cl =
      prove(vsubst [c,f] cl,
            REPEAT GEN_TAC THEN
            CONV_TAC(ONCE_DEPTH_CONV DEPAIR_CONV) THEN
            REWRITE_TAC[IN_SET_OF_LIST; ALL_MEM; ALL_MAPIFY;
                        EX_MAPIFY; ETA_AX] THEN
            FIRST (map MATCH_ACCEPT_TAC dths)) in
    map derive cls,dth;;

(* ------------------------------------------------------------------------- *)
(* Definition of a family of mutually recursive functions.                   *)
(* ------------------------------------------------------------------------- *)

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
    list_mk_abs(vs,mk_proj rtys i (mk_comb(g,mk_inj dtys i (mk_tuple vs)))),
    f in
  let repls = map2 repl (0--(length fs - 1)) fs in
  let newcl (f,args,r) =
    let i = index f fs in
    mk_eq(mk_comb(g,mk_inj dtys i (mk_tuple args)),
          mk_inj rtys i (beta_normalize(vsubst repls r))) in
  let newcls = map (fun cl -> close_clause [g] (newcl cl)) cls in
  let existence cls =
    let etm = mk_exists(g,list_mk_conj cls) in
    if wfs = [] then prove_general_recursive_function_exists etm else
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

(* ========================================================================= *)

(*  Primitive recursion for a family of functions.                          *)
(*                                                                          *)
(*  HOL Light's new_recursive_definition defines one function at a time,     *)
(*  but the recursion theorem of a (nested) datatype is about the whole      *)
(*  family of its types, so it can define a family of functions at once,     *)
(*  which is what the CakeML definitions over the syntax trees need.         *)
(* ========================================================================= *)

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

(* the position of the argument on which a function is defined by cases *)

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
    itlist (fun (g,args,_) n -> if g = f then max n (length args) else n)
           cls 0 in
  let posns = map (fun f -> pattern_position f cls) fs in
  let patty f r =
    let tys,_ = splitlist dest_fun_ty (type_of f) in el r tys in
  let tymatches vty cty = can (type_match vty cty) [] in
  let covers rth =
    let _,fns,_ = rec_thm_clauses rth in
    forall (fun (f,r) ->
              exists (fun fn ->
                        tymatches (fst(dest_fun_ty(type_of fn))) (patty f r))
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
                                    fst(dest_const c) = fst(dest_const hop))
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
             else (mk_type("one",[]),resvar)::ins)
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
        let cl = find (fun (g,cargs,_) ->
                         g = f && length cargs = n &&
                         fst(strip_comb(el r cargs)) = con)
                      cls in
        let _,cargs,rhs = cl in
        let pargs = snd(strip_comb(el r cargs)) in
        (* a pattern argument may itself be a tuple of variables, which
           is then taken apart with FST and SND *)
        let rec patsub a p =
          if is_var p then [a,p]
          else let x,y = dest_pair p in
               patsub (mk_fst a) x @ patsub (mk_snd a) y in
        let rhs = vsubst (itlist2 (fun a p l -> patsub a p @ l)
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
        (try let _ = assoc fn assign in
             let _,ty = splitlist dest_fun_ty
                          (snd(dest_fun_ty(type_of fn))) in
             mk_const("ARB",[ty,aty])
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
                    print_type (type_of p); print_string "\n  witness : ";
                    print_type (type_of w); print_newline())
                 (zip (fst(strip_forall(concl(INST_TYPE tyins rth))))
                      order_wits));
       failwith "SPECL") in
  let th2 = CONV_RULE (TOP_DEPTH_CONV GEN_BETA_CONV) th1 in
  (* names for the functions of the family *)
  let names =
    map (fun fn ->
          try let f,r = assoc fn assign in
              if r = 0 then fst(dest_var f) else fst(dest_var f) ^ "_rec"
          with Failure _ -> fst(dest_var(hd fs)) ^ "_aux_" ^
                            fst(dest_type(fst(dest_fun_ty(type_of fn)))))
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
    prove(gcl,
          REPEAT GEN_TAC THEN REWRITE_TAC fdefs THEN
          REWRITE_TAC[spec]) in
  map derive (conjuncts(snd(strip_forall tm))),spec;;

(* ------------------------------------------------------------------------- *)
(* Nested recursion: a recursive call under a MAP, as in                     *)
(* real_fringe (Nd n ptl) = FLAT (MAP real_fringe ptl).                      *)
(* HOL Light's machinery for such a recursion does not see that the          *)
(* elements of ptl are smaller, so the port defines the function             *)
(* together with the list function it needs (which is how HOL4 defines       *)
(* the size functions of a nested datatype as well), and then derives        *)
(* the equations as HOL4 states them.                                        *)
(* ------------------------------------------------------------------------- *)

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
  if !found = [] then failwith "define_nested" else
  let name0 = fst(dest_var(hd fs)) in
  let auxs =
    map (fun i ->
          let hk = el i !found in
          let vs = args hk in
          let ty,rty = dest_fun_ty (type_of hk) in
          let name = fresh_const_name (name0 ^ "_list" ^
                       (if i = 0 then "" else string_of_int (i+1))) in
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
          let _,_,aux = find (fun (hk,_,_) -> aconv hk (canon h)) auxs in
          list_mk_comb(aux,args h @ [repl l])
    | Comb(s,t) -> mk_comb(repl s,repl t)
    | Abs(v,b) -> mk_abs(v,repl b)
    | _ -> tm in
  let auxcls (hk,vs,aux) =
    let ty,rty = dest_fun_ty (type_of hk) in
    let p = mk_var("p",ty) and ps = mk_var("ps",mk_type("list",[ty])) in
    [mk_eq(list_mk_comb(aux,vs @ [mk_nil ty]),mk_nil rty);
     mk_eq(list_mk_comb(aux,vs @ [mk_cons p ps]),
           mk_cons (repl(beta_normalize(mk_comb(hk,p))))
                   (list_mk_comb(aux,vs @ [ps])))] in
  let gs = map (fun (_,_,aux) -> aux) auxs in
  let newcls = map (close_clause (fs @ gs))
                   (map repl cls @ itlist (fun a l -> auxcls a @ l)
                                          auxs []) in
  let ths,spec = define_prim_rec (list_mk_conj newcls) in
  let fths,auxths = chop_list (length cls) ths in
  let consts = map (fun f -> mk_mconst(fst(dest_var f),type_of f),f)
                   (fs @ gs) in
  (* each list function is the map of the function it belongs to *)
  let lemma i (hk,vs,aux) =
    let ty,rty = dest_fun_ty (type_of hk) in
    let lty = mk_type("list",[ty]) in
    let l = mk_var("l",lty) in
    let mapc = mk_mconst("MAP",
                 mk_fun_ty (type_of hk)
                   (mk_fun_ty lty (mk_type("list",[rty])))) in
    prove(list_mk_forall(vs @ [l],
            mk_eq(list_mk_comb(vsubst consts aux,vs @ [l]),
                  list_mk_comb(mapc,[vsubst consts hk; l]))),
          REPLICATE_TAC (length vs) GEN_TAC THEN LIST_INDUCT_TAC THEN
          ASM_REWRITE_TAC (MAP :: el (2*i) auxths ::
                           [el (2*i+1) auxths])) in
  let lems = map2 lemma (0--(length auxs - 1)) auxs in
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

(* ------------------------------------------------------------------------- *)

(* HOL4's Datatype, which also registers the recursion theorem and (as HOL4  *)
(* does) defines the size functions of the family.                           *)
(* ------------------------------------------------------------------------- *)

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
         else if ch = ')' || ch = ']' then (decr depth; cur := ch::(!cur))
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
            else (out := (implode(rev(map (String.make 1) (!cur))))::(!out);
                  cur := []))
         else if !depth = 0 && (ch = ' ' || ch = '\n' || ch = '\t') then
           (if !cur <> [] then
              (out := (implode(rev(map (String.make 1) (!cur))))::(!out);
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

(* ========================================================================= *)

(*  Size functions, for the termination of the definitions that are not      *)
(*  primitive recursive.                                                     *)
(*                                                                          *)
(*  define_size "exp" defines exp_size, and exp_size1, exp_size2, ... for    *)
(*  the other types of the family of exp (as HOL4 defines exp1_size,         *)
(*  exp2_size, ...), and identifies the ones on lists with list_size, so     *)
(*  that MEM_list_size gives the facts a termination proof needs.            *)
(* ========================================================================= *)

let the_size_fns = ref ([]:(hol_type * term * hol_type list) list);;

let define_size tyname =
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
                     (sort (<) (tyvars(fst(dest_fun_ty(type_of fn))))) l)
           ifns [] in
  let pvars = map (fun ty -> mk_var("size" ^ dest_vartype ty,
                                    mk_fun_ty ty numty))
                  params in
  (* the name of the size function of each type of the family *)
  let k = ref 0 in
  let names =
    map (fun fn ->
          let ty = fst(dest_fun_ty(type_of fn)) in
          if fst(dest_type ty) = tyname then tyname ^ "_size"
          else (k := !k + 1; tyname ^ "_size" ^ string_of_int !k))
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
                   try mk_comb(svar_of (rator (find (fun rv -> rand rv = a)
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
                                 type_of(el (index fn ifns) svars)),pvars)
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
  try let ty0,f,params = find (fun (ty0,_,_) -> can (type_match ty0 ty) [])
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

(* ------------------------------------------------------------------------- *)
(* A measure for a definition whose termination HOL Light cannot guess and   *)
(* for which HOL4 did not give one either (because HOL4 guessed it).         *)
(* ------------------------------------------------------------------------- *)

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

let mk_measure m =
  let dty = fst(dest_fun_ty(type_of m)) in
  list_mk_comb(mk_mconst("MEASURE",
    mk_fun_ty (type_of m) (mk_fun_ty dty (mk_fun_ty dty bool_ty))),[m]);;

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
    let cands =
      (if pats = [] then [] else [pats]) @
      map (fun i -> [i]) (0--(n-1)) @
      [0--(n-1)] in
    map (fun idxs -> mk_measure (measure_of_positions f cls idxs))
        (setify cands);;

let size_thms tyname =
  let a,b = assoc tyname (!the_size_thms) in a @ b;;

(* The definition functions that the port uses.                             *)
(* ------------------------------------------------------------------------- *)

let cake_define_gen wf tm =
  let fs = definition_heads tm in
  let cls = definition_clauses tm in
  let recursive =
    exists (fun (_,_,r) -> exists (fun f -> vfree_in f r) fs) cls in
  let attempt wfs =
    if length fs = 1 then define_single wfs tm else define_mutual wfs tm in
  let ths,_ =
    if not recursive then
      (if length fs = 1 then
         (if length cls = 1
          then (try [new_definition tm],TRUTH
                with Failure _ -> define_single [] tm)
          else define_single [] tm)
       else
         itlist
           (fun f (l,th) ->
              let mycls = filter (fun cl ->
                            fst(strip_comb(lhs(snd(strip_forall cl)))) = f)
                            (conjuncts(snd(strip_forall tm))) in
              let ths,th' = define_single [] (list_mk_conj mycls) in
              ths @ l,th')
           fs ([],TRUTH))
    else
      (try define_prim_rec tm with Failure _ ->
       try define_nested tm with Failure _ ->
       let given = match wf with Some rt -> [rt] | None -> [] in
       let cands = given @ map (fun rel -> rel,TERM_TAC)
                               (candidate_measures tm) in
       try attempt cands with Failure _ -> attempt []) in
  end_itlist CONJ ths;;

(* with cake_timing set, every definition reports how long it took *)

let cake_timing = ref false;;

let cake_time f x =
  if not (!cake_timing) then f x else
  let t = Sys.time() in
  let y = f x in
  (print_string (Printf.sprintf "[%.2fs] " (Sys.time() -. t));
   flush stdout; y);;

(* on failure, say which definition failed (and show it when
   cake_debug is set) *)

let cake_report tm s =
  let name =
    try fst(dest_var(hd(definition_heads tm))) with Failure _ -> "?" in
  print_string ("\ncake_define " ^ name ^ " failed: " ^ s ^ "\n");
  flush stdout;
  if !cake_debug then
    (cake_log ("cake_define " ^ name ^ " failed: " ^ s);
     cake_log_term tm);
  failwith s;;

let cake_define tm =
  try cake_time (cake_define_gen None) tm
  with Failure s -> cake_report tm s;;

let cake_define_wf rel tm =
  try cake_time (cake_define_gen (Some(rel,TERM_TAC))) tm
  with Failure s -> cake_report tm s;;

let cake_define_tac (rel,tac) tm =
  try cake_time (cake_define_gen (Some(rel,tac))) tm
  with Failure s -> cake_report tm s;;

(* ------------------------------------------------------------------------- *)
