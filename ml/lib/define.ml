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

(* the tactic that is tried on the termination condition if none is given *)

let TERM_TAC =
  REWRITE_TAC[MEASURE; FORALL_PAIR_THM; LE_LT] THEN ARITH_TAC;;

let discharge_conditions (rel,tac) th =
  itlist
    (fun h th ->
       let gtac =
         if is_exists h then EXISTS_TAC rel THEN
           REWRITE_TAC[WF_MEASURE; WF_LEX; WF_num] THEN tac
         else tac in
       PROVE_HYP (prove(h,gtac)) th)
    (hyp th) th;;

(* ------------------------------------------------------------------------- *)
(* Definition of one function, with a given termination relation.            *)
(* ------------------------------------------------------------------------- *)

let define_single wf tm =
  let fs = definition_heads tm in
  let f = hd fs in
  let name = fst(dest_var f) in
  let cls = map (close_clause fs) (conjuncts(snd(strip_forall tm))) in
  let etm = mk_exists(f,list_mk_conj cls) in
  let eth =
    match wf with
      None -> prove_general_recursive_function_exists etm
    | Some rt -> discharge_conditions rt
                   (pure_prove_recursive_function_exists etm) in
  let dth = new_specification [name] eth in
  CONJUNCTS dth,dth;;

(* ------------------------------------------------------------------------- *)
(* Definition of a family of mutually recursive functions.                   *)
(* ------------------------------------------------------------------------- *)

let define_mutual wf tm =
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
  let etm = mk_exists(g,list_mk_conj newcls) in
  let eth =
    match wf with
      None -> prove_general_recursive_function_exists etm
    | Some rt -> discharge_conditions rt
                   (pure_prove_recursive_function_exists etm) in
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
          REPEAT GEN_TAC THEN REWRITE_TAC fdefs THEN
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
          let recvals = snd(chop_list (length args) rargs) in
          fn,con,args,fj,recvals)
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
                                 (fun (_,c,_,_,_) ->
                                    is_const c &&
                                    fst(dest_const c) = fst(dest_const hop))
                                 canon in
                               let _,c,_,_,_ = con' in
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
  let canon = map (fun (fn,con,args,fj,rvs) ->
                     inst tyins fn,inst tyins con,map (inst tyins) args,
                     inst tyins fj,map (inst tyins) rvs)
                  canon in
  let assign = map (fun (fn,x) -> inst tyins fn,x) assign in
  (* the witness for each parameter of the recursion theorem *)
  let witness (fn,con,args,fj,recvals) =
    let rvs = map (fun i -> mk_var("r" ^ string_of_int i,
                                   type_of (el i recvals)))
                  (0--(length recvals - 1)) in
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
        let rhs = vsubst (zip args pargs) rhs in
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
    list_mk_abs(args @ rvs,body) in
  let wits = map witness canon in
  let wnames = map (fun (_,_,_,fj,_) -> fst(dest_var fj)) canon in
  let order_wits =
    map (fun pv -> el (index (fst(dest_var pv)) wnames) wits) pvars in
  let th1 = SPECL order_wits (INST_TYPE tyins rth) in
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
(* The definition functions that the port uses.                             *)
(* ------------------------------------------------------------------------- *)

let cake_define_gen wf tm =
  let fs = definition_heads tm in
  let cls = definition_clauses tm in
  let recursive =
    exists (fun (_,_,r) -> exists (fun f -> vfree_in f r) fs) cls in
  let ths,_ =
    if not recursive then
      (if length fs = 1 then
         (if length cls = 1
          then (try [new_definition tm],TRUTH
                with Failure _ -> define_single wf tm)
          else define_single wf tm)
       else
         itlist
           (fun f (l,th) ->
              let mycls = filter (fun cl ->
                            fst(strip_comb(lhs(snd(strip_forall cl)))) = f)
                            (conjuncts(snd(strip_forall tm))) in
              let ths,th' = define_single wf (list_mk_conj mycls) in
              ths @ l,th')
           fs ([],TRUTH))
    else if wf = None then
      (try define_prim_rec tm with Failure _ ->
       if length fs = 1 then define_single wf tm else define_mutual wf tm)
    else
      (if length fs = 1 then define_single wf tm else define_mutual wf tm) in
  end_itlist CONJ ths;;

let cake_define tm = cake_define_gen None tm;;

let cake_define_wf rel tm = cake_define_gen (Some(rel,TERM_TAC)) tm;;

let cake_define_tac (rel,tac) tm = cake_define_gen (Some(rel,tac)) tm;;

(* ------------------------------------------------------------------------- *)
(* HOL4's Datatype, which also registers the recursion theorem and (as HOL4  *)
(* does) defines the size functions of the family.                           *)
(* ------------------------------------------------------------------------- *)

let define_datatype spec =
  let ith,rth = define_type spec in
  register_rec_thm rth;
  ith,rth;;

(* the recursion theorems of the types that HOL Light defines itself *)

register_rec_thm list_RECURSION;;
register_rec_thm option_RECURSION;;
register_rec_thm num_RECURSION;;
register_rec_thm sum_RECURSION;;
register_rec_thm char_RECURSION;;
