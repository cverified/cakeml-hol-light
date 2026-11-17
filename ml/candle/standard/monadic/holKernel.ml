(* ======================================================== *)
(*  holKernel: ported from HOL4's
    candle/standard/monadic/holKernelScript.sml
    A definition theory, with 82 definitions, 3 datatypes and 6
    theorems.  Needed by 19 files of the port.  *)
(* ======================================================== *)

(*
  Define the Candle kernel as shallowly embedded functions in HOL
  using a monadic style in order to conveniently pass around state and
  propagate exceptions.
*)

needs "basis/pure/mllist.ml";;
needs "basis/pure/mlstring.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_call.ml";;
needs "compiler/backend/reg_alloc/linear_scan.ml";;
needs "lib/peg.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "holKernel"
  ["holSyntaxExtra"; "ml_monadBase"; "mllist"; "mlstring"];;

(* we reuse the datatypes of types and terms from the inference system *)

(* HOL4 holKernelScript.sml:21: ML code, not ported *)

(*
  type thm = Sequent of (term list * term)
*)

let thm_INDUCT,thm_RECURSION = define_datatype
  "thm =
     holKernel_Sequent (holSyntax_term list) holSyntax_term";;

(*
  We define a record that holds the state, i.e.

  let the_type_constants = ref ["bool",0; "fun",2]x

  let the_term_constants =
     ref [("=", mk_fun_ty aty (mk_fun_ty aty bool_ty))]

  let the_axioms = ref ([]:thm list)

  The context is the global theory context tracked by the inference system, and
  subsumes the above references. But we use them instead for efficiency (and to
  be close to HOL Light).
*)

let hol_refs_FIELDS = define_record "hol_refs"
  ["the_type_constants","(mlstring#num) list";
   "the_term_constants","(mlstring#type) list";
   "the_axioms","thm list";
   "the_context","holSyntax_update list"];;

(* the state-exception monad *)

let hol_exn_INDUCT,hol_exn_RECURSION = define_datatype
  "hol_exn =
     holKernel_Failure mlstring
   | holKernel_Clash holSyntax_term";;

(* HOL4 holKernelScript.sml:59: the type abbreviation M, which the port
   expands *)

(* deref/ref functions *)

(* HOL4 makes the monadic accessors of hol_refs with ML code
   (define_monad_access_funs of ml_monadBaseLib); these are
   the definitions that it makes *)
let get_the_type_constants_def = new_definition
  `get_the_type_constants = (\state. (M_success (hol_refs_the_type_constants
  state),state))`;;

let set_the_type_constants_def = new_definition
  `set_the_type_constants x =
     (\state. (M_success one,hol_refs_the_type_constants_fupd (K x)
       state))`;;

let get_the_term_constants_def = new_definition
  `get_the_term_constants = (\state. (M_success (hol_refs_the_term_constants
  state),state))`;;

let set_the_term_constants_def = new_definition
  `set_the_term_constants x =
     (\state. (M_success one,hol_refs_the_term_constants_fupd (K x)
       state))`;;

let get_the_axioms_def = new_definition
  `get_the_axioms = (\state. (M_success (hol_refs_the_axioms state),state))`;;

let set_the_axioms_def = new_definition
  `set_the_axioms x =
     (\state. (M_success one,hol_refs_the_axioms_fupd (K x) state))`;;

let get_the_context_def = new_definition
  `get_the_context = (\state. (M_success (hol_refs_the_context
  state),state))`;;

let set_the_context_def = new_definition
  `set_the_context x =
     (\state. (M_success one,hol_refs_the_context_fupd (K x) state))`;;


(* failwith *)

(* HOL4 makes the functions of the exception type hol_exn with ML
   code (define_monad_exception_functions of
   ml_monadBaseLib); these are the definitions that it
   makes *)
let raise_Failure_def = new_definition
  `raise_Failure e1 e2 =
     (\state. (M_failure (holKernel_Failure e1 e2),state))`;;

let raise_Clash_def = new_definition
  `raise_Clash e1 =
     (\state. (M_failure (holKernel_Clash e1),state))`;;

let handle_Failure_def = new_definition
  `handle_Failure x f =
     (\state.
       match x state with (res,state) ->
         match res with M_success y -> (M_success y,state)
         | M_failure e ->
           (match e with holKernel_Failure e1 e2 -> f e1 e2 state |
             holKernel_Clash e1 -> (M_failure (holKernel_Clash e1),state)))`;;

let handle_Clash_def = new_definition
  `handle_Clash x f =
     (\state.
       match x state with (res,state) ->
         match res with M_success y -> (M_success y,state)
         | M_failure e ->
           (match e with holKernel_Failure e1 e2 -> (M_failure
             (holKernel_Failure e1 e2),state) | holKernel_Clash e1 -> f e1
             state))`;;

(* HOL4 holKernelScript.sml:68: the overload failwith, which the port
   expands *)
(* HOL4 holKernelScript.sml:69: the overload raise_clash, which the port
   expands *)
(* HOL4 holKernelScript.sml:70: the overload handle_clash, which the port
   expands *)

(* others *)

let holKernel_try_def = new_definition
  `holKernel_try f x msg = (otherwise (f x) (failwith msg))`;;

(* define failing lookup function *)

let assoc_def,assoc_ind = define_guess
  `assoc s l =
     match l with
       [] -> failwith (implode "not in list")
     | (CONS ((x:'a),(y:'b)) xs) -> if s = x then st_ex_return y else
       assoc s xs`;;

let holKernel_map_def,holKernel_map_ind = define_guess
  `holKernel_map f l =
     match l with
       [] -> st_ex_return []
     | (CONS h t) -> st_ex_bind (f h) (\h. st_ex_bind (holKernel_map f t)
       (\t.
                    st_ex_return (CONS h t)))`;;

(* HOL4 holKernelScript.sml:96-110: code that the source has in a comment *)

let forall_def,forall_ind = define_guess
  `holKernel_forall p l =
     match l with
       [] -> st_ex_return T
     | (CONS h t) -> st_ex_bind (p h) (\ok.
                    if ok then holKernel_forall p t else st_ex_return F)`;;

let subset_def = new_definition
  `subset l1 l2 = ALL (\t. MEM t l2) l1`;;

(*
  let types() = !the_type_constants
*)

let types_def = new_definition
  `types one = get_the_type_constants`;;

(*
  let get_type_arity s = assoc s (!the_type_constants)
*)

let get_type_arity_def = new_definition
  `get_type_arity s =
     st_ex_bind get_the_type_constants (\l. assoc s l)`;;

(*
  let new_type(name,arity) =
    if can get_type_arity name then
      failwith ("new_type: type "^name^" has already been declared")
    else the_type_constants := (name,arity)::(!the_type_constants)
*)

let add_def_def = new_definition
  `add_def d = st_ex_bind get_the_context (\defs.
                  set_the_context (CONS d defs))`;;

let add_type_def = new_definition
  `add_type (name,arity) =
     st_ex_bind (can get_type_arity name) (\ok.
        if ok then failwith (strcat (strcat (implode "new_type: ") name)
          (implode " has already been declared"))
              else st_ex_bind get_the_type_constants (\ts.
                      set_the_type_constants (CONS (name,arity) ts)))`;;

let new_type_def = new_definition
  `new_type (name,arity) =
     st_ex_ignore_bind (add_type (name,arity)) (
        add_def (NewType name arity))`;;

(*
  let mk_type(tyop,args) =
    let arity = try get_type_arity tyop with Failure _ ->
      failwith ("mk_type: type "^tyop^" has not been defined") in
    if arity = length args then
      Tyapp(tyop,args)
    else failwith ("mk_type: wrong number of arguments to "^tyop)
*)

let mk_type_def,mk_type_ind = define_guess
  `mk_type (tyop,args) =
     st_ex_bind (holKernel_try get_type_arity tyop
          (strcat (strcat (implode "mk_type: type ") tyop) (implode
            " has not been defined"))) (\arity.
        if arity = LENGTH args then
          st_ex_return (holSyntax_Tyapp tyop args)
        else failwith (strcat (implode
          "mk_type: wrong number of arguments to ") tyop))`;;

(*
  let mk_vartype v = Tyvar(v)
*)

let mk_vartype_def = new_definition
  `mk_vartype v = holSyntax_Tyvar v`;;

(*
  let dest_type =
    function
        (Tyapp (s,ty)) -> s,ty
      | (Tyvar _) -> failwith "dest_type: type variable not a constructor"
*)

let dest_type_def,dest_type_ind = define_guess
  `dest_type t =
     match t with
       holSyntax_Tyapp s ty -> st_ex_return (s,ty)
     | holSyntax_Tyvar _ -> failwith (implode
       "dest_type: type variable not a constructor")`;;

(*
  let dest_vartype =
    function
        (Tyapp(_,_)) -> failwith "dest_vartype: type constructor not a variable"
      | (Tyvar s) -> s
*)

let dest_vartype_def,dest_vartype_ind = define_guess
  `dest_vartype t =
     match t with
       holSyntax_Tyapp _ _ -> failwith (implode
         "dest_vartype: type constructor not a variable")
     | holSyntax_Tyvar s -> st_ex_return s`;;

(*
  let is_type = can dest_type
*)

let is_type_def = new_definition
  `is_type t = match t with holSyntax_Tyapp s ty -> T | _ -> F`;;

(*
  let is_vartype = can dest_vartype

  We optimise this by making it perform the pattern match directly.
*)

let is_vartype_def = new_definition
  `is_vartype t = match t with holSyntax_Tyvar _ -> T | _ -> F`;;

(*
  let rec tyvars =
      function
          (Tyapp(_,args)) -> itlist (union o tyvars) args []
        | (Tyvar v as tv) -> [tv]
*)

(* the termination relation that HOL4 gives is
     MEASURE (type_size)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 holKernelScript.sml:251-257: the tactic that proves the termination *)
let holKernel_tyvars_def,holKernel_tyvars_ind = define_guess
  `holKernel_tyvars x =
     match x with (holSyntax_Tyapp _ args) -> itlist holSyntaxExtra_union
       (MAP holKernel_tyvars args) []
             | (holSyntax_Tyvar tv) -> [tv]`;;

(*
  let rec type_subst i ty =
    match ty with
      Tyapp(tycon,args) ->
          let args' = qmap (type_subst i) args in
          if args' == args then ty else Tyapp(tycon,args')
      | _ -> rev_assocd ty i ty
*)


let rev_assocd_def,rev_assocd_ind = define_guess
  `rev_assocd a l d =
     match l with
       [] -> d
     | (CONS (x,y) l) -> if y = a then x else rev_assocd a l d`;;

(* the termination relation that HOL4 gives is
     MEASURE (type_size o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 holKernelScript.sml:283-289: the tactic that proves the termination *)
let holKernel_type_subst_def,holKernel_type_subst_ind = define_guess
  `holKernel_type_subst i ty =
     match ty with
       holSyntax_Tyapp tycon args ->
          let args' = MAP (holKernel_type_subst i) args in
          if args' = args then ty else holSyntax_Tyapp tycon args'
     | _ -> rev_assocd ty i ty`;;

(*
  let bool_ty = mk_type("bool",[]);;
  let mk_fun_ty ty1 ty2 = mk_type("fun",[ty1; ty2]);;
  let aty = mk_vartype "A";;
  let bty = mk_vartype "B";;
*)

let bool_ty_def = new_definition
  `bool_ty = holSyntax_Tyapp (implode "bool") []`;;

let mk_fun_ty_def = new_definition
  `mk_fun_ty ty1 ty2 = holSyntax_Tyapp (implode "fun") [ty1; ty2]`;;

let aty_def = new_definition
  `aty = holSyntax_Tyvar (implode "A")`;;

let bty_def = new_definition
  `bty = holSyntax_Tyvar (implode "B")`;;

(*
  let constants() = !the_term_constants
*)

let constants_def = new_definition
  `constants one = get_the_term_constants`;;

(*
  let get_const_type s = assoc s (!the_term_constants)
*)

let get_const_type_def = new_definition
  `get_const_type s =
     st_ex_bind get_the_term_constants (\l. assoc s l)`;;

(*
  let rec type_of tm =
    match tm with
      Var(_,ty) -> ty
    | Const(_,ty) -> ty
    | Comb(s,_) -> hd(tl(snd(dest_type(type_of s))))
    | Abs(Var(_,ty),t) -> mk_fun_ty ty (type_of t)
*)

let type_of_def,type_of_ind = define_guess
  `type_of tm =
     match tm with
       holSyntax_Var _ ty -> st_ex_return ty
     | holSyntax_Const _ ty -> st_ex_return ty
     | holSyntax_Comb s _ -> st_ex_bind (type_of s) (\ty. st_ex_bind
       (dest_type ty) (\x.
                      match x with (_,CONS _ (CONS ty1 _)) -> st_ex_return
                        ty1
                              | _ -> failwith (implode "match")))
     | holSyntax_Abs (holSyntax_Var _ ty) t -> st_ex_bind (type_of t) (\x.
       st_ex_return (mk_fun_ty ty x))
     | _ -> failwith (implode "match")`;;

(*
  let aconv =
    let rec alphavars env tm1 tm2 =
      match env with
        [] -> tm1 = tm2
      | (t1,t2)::oenv ->
            (t1 = tm1 & t2 = tm2) or
            (t1 <> tm1 & t2 <> tm2 & alphavars oenv tm1 tm2) in
    let rec raconv env tm1 tm2 =
      (tm1 == tm2 & env = []) or
      match (tm1,tm2) with
        Var(_,_),Var(_,_) -> alphavars env tm1 tm2
      | Const(_,_),Const(_,_) -> tm1 = tm2
      | Comb(s1,t1),Comb(s2,t2) -> raconv env s1 s2 & raconv env t1 t2
      | Abs(Var(_,ty1) as x1,t1),Abs(Var(_,ty2) as x2,t2) ->
                ty1 = ty2 & raconv ((x1,x2)::env) t1 t2
      | _ -> false in
    fun tm1 tm2 -> raconv [] tm1 tm2
*)

let alphavars_def,alphavars_ind = define_guess
  `alphavars env tm1 tm2 =
     match env with
       [] -> (tm1 = tm2)
     | CONS (t1,t2) oenv ->
       if t1 = tm1 then t2 = tm2
       else if t2 = tm2 then F
       else alphavars oenv tm1 tm2`;;

let raconv_def,raconv_ind = define_guess
  `raconv env tm1 tm2 =
     match (tm1,tm2) with
       (holSyntax_Var _ _,holSyntax_Var _ _) -> alphavars env tm1 tm2
     | (holSyntax_Const _ _,holSyntax_Const _ _) -> (tm1 = tm2)
     | (holSyntax_Comb s1 t1,holSyntax_Comb s2 t2) -> raconv env s1 s2
       /\ raconv env t1 t2
     | (holSyntax_Abs v1 t1,holSyntax_Abs v2 t2) ->
        (match (v1,v2) with
           (holSyntax_Var n1 ty1,holSyntax_Var n2 ty2) -> (ty1 = ty2) /\
                              raconv (CONS (v1,v2) env) t1 t2
         | _ -> F)
     | _ -> F`;;

let aconv_def = new_definition
  `aconv tm1 tm2 = raconv [] tm1 tm2`;;

(*
  let is_var = function (Var(_,_)) -> true | _ -> false
  let is_const = function (Const(_,_)) -> true | _ -> false
  let is_abs = function (Abs(_,_)) -> true | _ -> false
  let is_comb = function (Comb(_,_)) -> true | _ -> false
*)

let is_var_def = new_definition
  `is_var x = match x with (holSyntax_Var _ _) -> T | _ -> F`;;
let holKernel_is_const_def = new_definition
  `holKernel_is_const x = match x with (holSyntax_Const _ _) -> T | _ -> F`;;
let is_abs_def = new_definition
  `is_abs x = match x with (holSyntax_Abs _ _) -> T | _ -> F`;;
let is_comb_def = new_definition
  `is_comb x = match x with (holSyntax_Comb _ _) -> T | _ -> F`;;

(*
  let mk_var(v,ty) = Var(v,ty)
*)

let mk_var_def = new_definition
  `mk_var (v,ty) = holSyntax_Var v ty`;;

(*
  let mk_const(name,theta) =
    let uty = try get_const_type name with Failure _ ->
      failwith "mk_const: not a constant name" in
    Const(name,type_subst theta uty)
*)

let holKernel_mk_const_def = new_definition
  `holKernel_mk_const (name,theta) =
     st_ex_bind (holKernel_try get_const_type name
          (implode "mk_const: not a constant name")) (\uty.
        st_ex_return (holSyntax_Const name (holKernel_type_subst theta
          uty)))`;;

(*
  let mk_abs(bvar,bod) =
    match bvar with
      Var(_,_) -> Abs(bvar,bod)
    | _ -> failwith "mk_abs: not a variable"
*)

let mk_abs_def,mk_abs_ind = define_guess
  `mk_abs (bvar,bod) =
     match bvar with
       holSyntax_Var n ty -> st_ex_return (holSyntax_Abs bvar bod)
     | _ -> failwith (implode "mk_abs: not a variable")`;;

(*
  let mk_comb(f,a) =
    match type_of f with
      Tyapp("fun",[ty;_]) when ty = type_of a -> Comb(f,a)
    | _ -> failwith "mk_comb: types do not agree"
*)

let mk_comb_def,mk_comb_ind = define_guess
  `mk_comb (f,a) =
     st_ex_bind (type_of f) (\tyf. st_ex_bind (type_of a) (\tya.
        match tyf with
          holSyntax_Tyapp (implode "fun") [ty; _] -> if tya = ty then
            st_ex_return (holSyntax_Comb f a) else failwith (implode
            "mk_comb: types do not agree")
        | _ -> failwith (implode "mk_comb: types do not agree")))`;;

(*
  let dest_var =
    function (Var(s,ty)) -> s,ty | _ -> failwith "dest_var: not a variable"

  let dest_const =
    function (Const(s,ty)) -> s,ty | _ -> failwith "dest_const: not a constant"

  let dest_comb =
    function (Comb(f,x)) -> f,x | _ -> failwith "dest_comb: not a combination"

  let dest_abs =
    function (Abs(v,b)) -> v,b | _ -> failwith "dest_abs: not an abstraction"
*)

let holKernel_dest_var_def = new_definition
  `holKernel_dest_var tm = match tm with holSyntax_Var s ty -> st_ex_return
  (s,ty)
                          | _ -> failwith (implode
                            "dest_var: not a variable")`;;

let holKernel_dest_const_def = new_definition
  `holKernel_dest_const tm = match tm with holSyntax_Const s ty -> st_ex_return
  (s,ty)
                            | _ -> failwith (implode
                              "dest_const: not a constant")`;;

let dest_comb_def,dest_comb_ind = define_guess
  `dest_comb tm = match tm with holSyntax_Comb f x -> st_ex_return (f,x)
                           | _ -> failwith (implode
                             "dest_comb: not a combination")`;;

let dest_abs_def,dest_abs_ind = define_guess
  `dest_abs tm = match tm with holSyntax_Abs v b -> st_ex_return (v,b)
                          | _ -> failwith (implode
                            "dest_abs: not an abstraction")`;;

(*
  let rec frees tm =
    match tm with
      Var(_,_) -> [tm]
    | Const(_,_) -> []
    | Abs(bv,bod) -> subtract (frees bod) [bv]
    | Comb(s,t) -> union (frees s) (frees t)
*)

(*
  let freesl tml = itlist (union o frees) tml []
*)

let freesl_def = new_definition
  `freesl tml = itlist (holSyntaxExtra_union o frees) tml []`;;

(*
  let rec freesin acc tm =
    match tm with
      Var(_,_) -> mem tm acc
    | Const(_,_) -> true
    | Abs(bv,bod) -> freesin (bv::acc) bod
    | Comb(s,t) -> freesin acc s & freesin acc t
*)

let freesin_def,freesin_ind = define_guess
  `freesin acc tm =
     match tm with
       holSyntax_Var _ _ -> MEM tm acc
     | holSyntax_Const _ _ -> T
     | holSyntax_Abs bv bod -> freesin (CONS bv acc) bod
     | holSyntax_Comb s t -> freesin acc s /\ freesin acc t`;;

(*
  let rec vfree_in v tm =
    match tm with
      Abs(bv,bod) -> v <> bv & vfree_in v bod
    | Comb(s,t) -> vfree_in v s or vfree_in v t
    | _ -> tm = v
*)

(*
  let rec type_vars_in_term tm =
    match tm with
      Var(_,ty)        -> tyvars ty
    | Const(_,ty)      -> tyvars ty
    | Comb(s,t)        -> union (type_vars_in_term s) (type_vars_in_term t)
    | Abs(Var(_,ty),t) -> union (tyvars ty) (type_vars_in_term t)

  The Abs pmatch is modified slightly.
*)

let type_vars_in_term_def,type_vars_in_term_ind = define_guess
  `type_vars_in_term tm =
     match tm with
       holSyntax_Var _ ty -> holKernel_tyvars ty
     | holSyntax_Const _ ty -> holKernel_tyvars ty
     | holSyntax_Comb s t -> holSyntaxExtra_union (type_vars_in_term s)
       (type_vars_in_term t)
     | holSyntax_Abs v t -> holSyntaxExtra_union (type_vars_in_term v)
       (type_vars_in_term t)`;;

(*
  let rec variant avoid v =
    if not(exists (vfree_in v) avoid) then v else
    match v with
      Var(s,ty) -> variant avoid (Var(s^"'",ty))
    | _ -> failwith "variant: not a variable"

  This function requires a non-trivial terminiation proof. We make
  this a non-failing function to make it pure.
*)

(* [local] *)
let EXISTS_IMP = prove
 (`!xs p. EX p xs ==> (?x. MEM x xs /\ p x)`,
  CHEAT_TAC);;

(* [local] *)
let MEM_subtract = prove
 (`!y z x. MEM x (subtract y z) = (MEM x y /\ ~(MEM x z))`,
  CHEAT_TAC);;

(* [local] *)
let vfree_in_IMP = prove
 (`!(t:holSyntax_term) x v. vfree_in (holSyntax_Var v ty) x ==> MEM
  (holSyntax_Var v ty) (frees x)`,
  CHEAT_TAC);;

(*
  let vsubst =
    let rec vsubst ilist tm =
      match tm with
        Var(_,_) -> rev_assocd tm ilist tm
      | Const(_,_) -> tm
      | Comb(s,t) -> let s' = vsubst ilist s and t' = vsubst ilist t in
                     if s' == s & t' == t then tm else Comb(s',t')
      | Abs(v,s) -> let ilist' = filter (fun (t,x) -> x <> v) ilist in
                    if ilist' = [] then tm else
                    let s' = vsubst ilist' s in
                    if s' == s then tm else
                    if exists (fun (t,x) -> vfree_in v t & vfree_in x s) ilist'
                    then let v' = variant [s'] v in
                         Abs(v',vsubst ((v',v)::ilist') s)
                    else Abs(v,s') in
    fun theta ->
      if theta = [] then (fun tm -> tm) else
      if forall (fun (t,x) -> type_of t = snd(dest_var x)) theta
      then vsubst theta else failwith "vsubst: Bad substitution list"
*)

let vsubst_aux_def,vsubst_aux_ind = define_guess
  `vsubst_aux ilist tm =
     match tm with
       holSyntax_Var _ _ -> rev_assocd tm ilist tm
     | holSyntax_Const _ _ -> tm
     | holSyntax_Comb s t -> let s' = vsubst_aux ilist s in
                   let t' = vsubst_aux ilist t in
                     holSyntax_Comb s' t'
     | holSyntax_Abs v s -> if ~(is_var v) then tm else let ilist' = FILTER
       (\(t,x). ~(x = v)) ilist in
                   if ilist' = [] then tm else let s' = vsubst_aux ilist' s
                     in
                   // if s' = s then tm else --- commented out becuase it doesn't
                   // seem to fit Harrison's formalisation
                   if EX (\(t,x). vfree_in v t /\ vfree_in x s) ilist' then
                     let v' = variant [s'] v in
                          holSyntax_Abs v' (vsubst_aux (CONS (v',v) ilist')
                            s)
                   else holSyntax_Abs v s'`;;

let vsubst_def,vsubst_ind = define_guess
  `vsubst theta tm =
     if theta = [] then st_ex_return tm else st_ex_bind (holKernel_forall
       (\(t,x). st_ex_bind (type_of t) (\ty. st_ex_bind (holKernel_dest_var x)
       (\vty.
                              st_ex_return (ty = SND vty)))) theta) (\ok.
        if ok then st_ex_return (vsubst_aux theta tm)
        else failwith (implode "vsubst: Bad substitution list"))`;;

(*
  let inst =
    let rec inst env tyin tm =
      match tm with
        Var(n,ty)   -> let ty' = type_subst tyin ty in
                       let tm' = if ty' == ty then tm else Var(n,ty') in
                       if rev_assocd tm' env tm = tm then tm'
                       else raise (Clash tm')
      | Const(c,ty) -> let ty' = type_subst tyin ty in
                       if ty' == ty then tm else Const(c,ty')
      | Comb(f,x)   -> let f' = inst env tyin f and x' = inst env tyin x in
                       if f' == f & x' == x then tm else Comb(f',x')
      | Abs(y,t)    -> let y' = inst [] tyin y in
                       let env' = (y,y')::env in
                       try let t' = inst env' tyin t in
                           if y' == y & t' == t then tm else Abs(y',t')
                       with (Clash(w') as ex) ->
                       if w' <> y' then raise ex else
                       let ifrees = map (inst [] tyin) (frees t) in
                       let y'' = variant ifrees y' in
                       let z = Var(fst(dest_var y''),snd(dest_var y)) in
                       inst env tyin (Abs(z,vsubst[z,y] t)) in
      fun tyin -> if tyin = [] then fun tm -> tm else inst [] tyin
*)

let my_term_size_def,my_term_size_ind = define_guess
  `(my_term_size (holSyntax_Var _ _) = (1:num)) /\
   (my_term_size (holSyntax_Const _ _) = ((1):num)) /\
   (my_term_size (holSyntax_Comb s1 s2) = ((1 + my_term_size s1 +
    my_term_size s2):num)) /\
   (my_term_size (holSyntax_Abs s1 s2) = ((1 + my_term_size s1 +
    my_term_size s2):num))`;;

(* [local] *)
let my_term_size_variant = prove
 (`!avoid t. my_term_size (variant avoid t) = my_term_size t`,
  CHEAT_TAC);;

(* [local] *)
let is_var_variant = prove
 (`!avoid t. is_var (variant avoid t) = is_var t`,
  CHEAT_TAC);;

(* HOL4 holKernelScript.sml:713-733: a theorem that HOL4 states as the value
   of an ML expression: my_term_size_vsubst_aux *)

(* [local] *)
let ZERO_LT_term_size = prove
 (`!t. 0 < my_term_size t`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (\(env,tyin,tm). my_term_size tm)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 holKernelScript.sml:771-777: the tactic that proves the termination *)
let inst_aux_def,inst_aux_ind = define_guess
  `(inst_aux (env:(holSyntax_term#holSyntax_term) list) tyin tm) =
     match tm with
       holSyntax_Var n ty -> let ty' = holKernel_type_subst tyin ty in
                     let tm' = (if ty' = ty then tm else holSyntax_Var n
                       ty') in
                     if rev_assocd tm' env tm = tm then st_ex_return tm'
                     else raise_Clash tm'
     | holSyntax_Const c ty -> let ty' = holKernel_type_subst tyin ty in
                     if ty' = ty then st_ex_return tm else st_ex_return
                       (holSyntax_Const c ty')
     | holSyntax_Comb f x -> st_ex_bind (inst_aux env tyin f) (\f'.
       st_ex_bind (inst_aux env tyin x) (\x'.
                        if (f = f') /\ (x = x') then st_ex_return tm
                              else st_ex_return (holSyntax_Comb f' x')))
     | holSyntax_Abs y t -> st_ex_bind (inst_aux [] tyin y)
       (\(y':holSyntax_term). st_ex_bind (st_ex_return (CONS (y,y') env))
       (\env'.
                        handle_Clash
                         (st_ex_bind (inst_aux env' tyin t) (\t'.
                             if (y = y') /\ (t = t') then st_ex_return tm
                              else st_ex_return (holSyntax_Abs y' t')))
                         (\w'.
                          if ~(w' = y') then raise_Clash w' else st_ex_bind
                            (inst_aux [] tyin t) (\temp. st_ex_bind
                            (st_ex_return (variant (frees temp) y')) (\y'.
                            st_ex_bind (holKernel_dest_var y') (\(v1,ty').
                            st_ex_bind (holKernel_dest_var y) (\(v2,ty).
                            st_ex_bind (inst_aux (CONS (holSyntax_Var v1
                            ty,holSyntax_Var v1 ty') env) tyin
                              (vsubst_aux [(holSyntax_Var v1 ty,y)] t))
                                (\t'.
                             st_ex_return (holSyntax_Abs y' t')))))))))`;;

let holKernel_inst_def = new_definition
  `holKernel_inst tyin tm = if tyin = [] then st_ex_return tm else inst_aux
  [] tyin tm`;;

(*
  let rator tm =
    match tm with
      Comb(l,r) -> l
    | _ -> failwith "rator: Not a combination";;

  let rand tm =
    match tm with
      Comb(l,r) -> r
    | _ -> failwith "rand: Not a combination";;
*)

let rator_def,rator_ind = define_guess
  `rator tm =
     match tm with
       holSyntax_Comb l r -> st_ex_return l
     | _ -> failwith (implode "rator: Not a combination")`;;

let rand_def,rand_ind = define_guess
  `rand tm =
     match tm with
       holSyntax_Comb l r -> st_ex_return r
     | _ -> failwith (implode "rand: Not a combination")`;;

(*
  let safe_mk_eq l r =
    let ty = type_of l in
    Comb(Comb(Const("=",Tyapp("fun",[ty;Tyapp("fun",[ty;bool_ty])])),l),r)
*)
let safe_mk_eq_def = new_definition
  `safe_mk_eq l r =
   st_ex_bind (type_of l) (\ty.
     st_ex_return (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
       (implode "=") (holSyntax_Tyapp (implode "fun") [ty; holSyntax_Tyapp
       (implode "fun") [ty; bool_ty]])) l) r))`;;

(*
  let mk_eq =
    let eq = mk_const("=",[]) in
    fun (l,r) ->
      try let ty = type_of l in
          let eq_tm = inst [ty,aty] eq in
          mk_comb(mk_comb(eq_tm,l),r)
      with Failure _ -> failwith "mk_eq";;
*)

let mk_eq_def,mk_eq_ind = define_guess
  `mk_eq (l,r) =
     holKernel_try (\(l,r).
            st_ex_bind (type_of l) (\ty. st_ex_bind (holKernel_mk_const
              ((implode "="),[])) (\eq. st_ex_bind (holKernel_inst [(ty,aty)]
              eq) (\eq_tm. st_ex_bind (mk_comb (eq_tm,l)) (\t. st_ex_bind
              (mk_comb (t,r)) (\t.
               st_ex_return t)))))) (l,r) (implode "mk_eq")`;;

(*
  let dest_eq tm =
    match tm with
      Comb(Comb(Const("=",_),l),r) -> l,r
    | _ -> failwith "dest_eq";;

  let is_eq tm =
    match tm with
      Comb(Comb(Const("=",_),_),_) -> true
    | _ -> false;;
*)

let dest_eq_def,dest_eq_ind = define_guess
  `dest_eq tm =
     match tm with
       holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=") _) l) r
         -> st_ex_return (l,r)
     | _ -> failwith (implode "dest_eq")`;;

let is_eq_def = new_definition
  `is_eq tm =
     match tm with
       holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=") _) l) r
         -> T
     | _ -> F`;;

(*
  let dest_thm (Sequent(asl,c)) = (asl,c)

  let hyp (Sequent(asl,c)) = asl

  let concl (Sequent(asl,c)) = c
*)

let dest_thm_def = new_definition
  `dest_thm (holKernel_Sequent asl c) = (asl,c)`;;
let hyp_def = new_definition
  `hyp (holKernel_Sequent asl c) = asl`;;
let concl_def = new_definition
  `concl (holKernel_Sequent asl c) = c`;;

(*
  let REFL tm =
    Sequent([],safe_mk_eq tm tm)
*)

let REFL_def = new_definition
  `REFL tm = st_ex_bind (safe_mk_eq tm tm) (\eq. st_ex_return
  (holKernel_Sequent [] eq))`;;

(*
  let TRANS (Sequent(asl1,c1)) (Sequent(asl2,c2)) =
    match (c1,c2) with
      Comb((Comb(Const("=",_),_) as eql),m1),Comb(Comb(Const("=",_),m2),r)
        when alphaorder m1 m2 = 0 -> Sequent(term_union asl1 asl2,Comb(eql,r))
    | _ -> failwith "TRANS"
*)

let TRANS_def,TRANS_ind = define_guess
  `TRANS (holKernel_Sequent asl1 c1) (holKernel_Sequent asl2 c2) =
     match (c1,c2) with
       (holSyntax_Comb eql m1,holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "=") _) m2) r) ->
         (match eql with
            (holSyntax_Comb (holSyntax_Const (implode "=") _) l) ->
             if aconv m1 m2 then st_ex_return (holKernel_Sequent (term_union
               asl1 asl2) (holSyntax_Comb eql r))
             else failwith (implode "TRANS")
          | _ -> failwith (implode "TRANS"))
     | _ -> failwith (implode "TRANS")`;;

(* some in-kernel but derivable rules (TRANS is also in this category) *)

let SYM_def,SYM_ind = define_guess
  `SYM (holKernel_Sequent asl eq) =
     match eq with
       holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=") t) l) r
         ->
         st_ex_return (holKernel_Sequent asl (holSyntax_Comb (holSyntax_Comb
           (holSyntax_Const (implode "=") t) r) l))
     | _ -> failwith (implode "SYM")`;;

let PROVE_HYP_def = new_definition
  `PROVE_HYP (holKernel_Sequent asl1 c1) (holKernel_Sequent asl2 c2) =
     st_ex_return (holKernel_Sequent (term_union asl2 (term_remove c2
       asl1)) c1)`;;

let list_to_hypset_def,list_to_hypset_ind = define_guess
  `(list_to_hypset [] a = a) /\
   (list_to_hypset (CONS h hs) a =
       list_to_hypset hs (term_union [h] a))`;;

let ALPHA_THM_def,ALPHA_THM_ind = define_guess
  `ALPHA_THM (holKernel_Sequent h c) (h',c') =
   if aconv c c' then
     let h' = list_to_hypset h' [] in
     if ALL (\x. EX (aconv x) h') h then
       st_ex_bind (holKernel_map type_of h') (\tys.
         if ALL (\ty. ty = bool_ty) tys then
           st_ex_return (holKernel_Sequent h' c')
         else failwith (implode "ALPHA_THM"))
     else failwith (implode "ALPHA_THM")
   else failwith (implode "ALPHA_THM")`;;

(* -- *)

(*
  let MK_COMB(Sequent(asl1,c1),Sequent(asl2,c2)) =
     match (c1,c2) with
       Comb(Comb(Const("=",_),l1),r1),Comb(Comb(Const("=",_),l2),r2) ->
        (match type_of r1 with
           Tyapp("fun",[ty;_]) when compare ty (type_of r2) = 0
             -> Sequent(term_union asl1 asl2,
                        safe_mk_eq (Comb(l1,l2)) (Comb(r1,r2)))
         | _ -> failwith "MK_COMB: types do not agree")
     | _ -> failwith "MK_COMB: not both equations"
*)

let MK_COMB_def,MK_COMB_ind = define_guess
  `MK_COMB (holKernel_Sequent asl1 c1,holKernel_Sequent asl2 c2) =
    match (c1,c2) with
      (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=") _) l1)
        r1,holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=") _) l2)
        r2) ->
        st_ex_bind (type_of r1) (\r1_ty.
           (match r1_ty with
              holSyntax_Tyapp (implode "fun") [ty; _] ->
                st_ex_bind (type_of r2) (\r2_ty.
                  if r2_ty = ty then
                    st_ex_bind (safe_mk_eq (holSyntax_Comb l1 l2)
                      (holSyntax_Comb r1 r2)) (\eq.
                      st_ex_return (holKernel_Sequent (term_union asl1 asl2)
                        eq))
                  else failwith (implode "MK_COMB: types do not agree"))
            | _ -> failwith (implode "MK_COMB: types do not agree")))
    | _ -> failwith (implode "MK_COMB: not both equations")`;;

(*
  let ABS v (Sequent(asl,c)) =
    match (v,c) with
      Var(_,_),Comb(Comb(Const("=",_),l),r) when not(exists (vfree_in v) asl)
         -> Sequent(asl,safe_mk_eq (Abs(v,l)) (Abs(v,r)))
    | _ -> failwith "ABS";;
*)

let ABS_def,ABS_ind = define_guess
  `abs v (holKernel_Sequent asl c) =
     match (v,c) with
       (holSyntax_Var _ _,holSyntax_Comb (holSyntax_Comb (holSyntax_Const
         (implode "=") _) l) r) ->
         (if EX (vfree_in v) asl then failwith (implode
           "ABS: variable is free in assumptions")
         else st_ex_bind (safe_mk_eq (holSyntax_Abs v l) (holSyntax_Abs v
           r)) (\eq.
                 st_ex_return (holKernel_Sequent asl eq)))
     | _ -> failwith (implode "ABS: not an equation")`;;

(*
  let BETA tm =
    match tm with
      Comb(Abs(v,bod),arg) when compare arg v = 0
        -> Sequent([],safe_mk_eq tm bod)
    | _ -> failwith "BETA: not a trivial beta-redex"
*)

let BETA_def,BETA_ind = define_guess
  `BETA tm =
     match tm with
       holSyntax_Comb (holSyntax_Abs v bod) arg ->
         if arg = v then st_ex_bind (safe_mk_eq tm bod) (\eq. st_ex_return
           (holKernel_Sequent [] eq))
         else failwith (implode "BETA: not a trivial beta-redex")
     | _ -> failwith (implode "BETA: not a trivial beta-redex")`;;

(*
  let ASSUME tm =
    if type_of tm = bool_ty then Sequent([tm],tm)
    else failwith "ASSUME: not a proposition"
*)

let ASSUME_def,ASSUME_ind = define_guess
  `ASSUME tm =
     st_ex_bind (type_of tm) (\ty.
        if ty = bool_ty then st_ex_return (holKernel_Sequent [tm] tm)
        else failwith (implode "ASSUME: not a proposition"))`;;

(*
  let EQ_MP (Sequent(asl1,eq)) (Sequent(asl2,c)) =
    match eq with
      Comb(Comb(Const("=",_),l),r) when aconv l c
        -> Sequent(term_union asl1 asl2,r)
    | _ -> failwith "EQ_MP"
*)

let EQ_MP_def,EQ_MP_ind = define_guess
  `EQ_MP (holKernel_Sequent asl1 eq) (holKernel_Sequent asl2 c) =
     match eq with
       holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=") _) l) r
         ->
         if aconv l c then st_ex_return (holKernel_Sequent (term_union asl1
           asl2) r)
                      else failwith (implode "EQ_MP")
     | _ -> failwith (implode "EQ_MP")`;;

(*
  let DEDUCT_ANTISYM_RULE (Sequent(asl1,c1)) (Sequent(asl2,c2)) =
    let asl1' = term_remove c2 asl1 and asl2' = term_remove c1 asl2 in
    Sequent(term_union asl1' asl2',safe_mk_eq c1 c2)
*)

let DEDUCT_ANTISYM_RULE_def = new_definition
  `DEDUCT_ANTISYM_RULE (holKernel_Sequent asl1 c1) (holKernel_Sequent asl2 c2)
  =
     let asl1' = term_remove c2 asl1 in
     let asl2' = term_remove c1 asl2 in
       st_ex_bind (safe_mk_eq c1 c2) (\eq.
          st_ex_return (holKernel_Sequent (term_union asl1' asl2') eq))`;;

let image_def,image_ind = define_guess
  `image f l =
   match l with
     [] -> st_ex_return l
   | (CONS h t) -> st_ex_bind (f h) (\h'. st_ex_bind (image f t) (\t'.
                  st_ex_return (if (h' = h) /\ (t' = t) then l
                           else term_union [h'] t')))`;;

(*
  let INST_TYPE theta (Sequent(asl,c)) =
    let inst_fun = inst theta in
    Sequent(map inst_fun asl,inst_fun c)
*)

let INST_TYPE_def = new_definition
  `INST_TYPE theta (holKernel_Sequent asl c) =
     let inst_fun = holKernel_inst theta in
       st_ex_bind (image inst_fun asl) (\l. st_ex_bind (inst_fun c) (\x.
          st_ex_return (holKernel_Sequent l x)))`;;

(*
  let INST theta (Sequent(asl,c)) =
    let inst_fun = vsubst theta in
    Sequent(map inst_fun asl,inst_fun c)
*)

let holKernel_INST_def = new_definition
  `holKernel_INST theta (holKernel_Sequent asl c) =
     let inst_fun = vsubst theta in
       st_ex_bind (image inst_fun asl) (\l. st_ex_bind (inst_fun c) (\x.
          st_ex_return (holKernel_Sequent l x)))`;;

(*
  let axioms() = !the_axioms
*)

let axioms_def = new_definition
  `axioms one = get_the_axioms`;;

(*
  let new_axiom tm =
    if fst(dest_type(type_of tm)) = "bool" then
      let th = Sequent([],tm) in
       (the_axioms := th::(!the_axioms); th)
    else failwith "new_axiom: Not a proposition"
*)

let new_axiom_def,new_axiom_ind = define_guess
  `new_axiom tm =
     st_ex_bind (type_of tm) (\ty.
        if ty = bool_ty then
          st_ex_bind (st_ex_return (holKernel_Sequent [] tm)) (\th.
            st_ex_bind get_the_axioms (\ax.
             st_ex_ignore_bind (set_the_axioms (CONS th ax)) (
             st_ex_ignore_bind (add_def (NewAxiom tm)) (
             st_ex_return th))))
        else failwith (implode "new_axiom: Not a proposition"))`;;

let first_dup_def,first_dup_ind = define_guess
  `first_dup ls acc =
   match ls with [] -> NONE
   | (CONS h t) ->
     if MEM h acc then SOME h else first_dup t (CONS h acc)`;;

let add_constants_def,add_constants_ind = define_guess
  `add_constants ls =
     st_ex_bind get_the_term_constants (\cs.
        match first_dup (MAP FST ls) (MAP FST cs) with SOME name -> failwith
          (strcat (strcat (implode "add_constants: ") name) (implode
          " appears twice or has already been declared"))
        | NONE -> set_the_term_constants (APPEND ls cs))`;;

let new_specification_def,new_specification_ind = define_guess
  `new_specification (holKernel_Sequent eqs p) =
          st_ex_bind (holKernel_map (\e. st_ex_bind (dest_eq e) (\(l,r).
            st_ex_bind (holKernel_dest_var l) (\(s,ty).
                      if ~(freesin [] r) then
                        failwith (strcat (strcat (implode
                          "new_specification: witness for ") s) (implode
                          " not closed"))
                      else if ~(subset (type_vars_in_term r)
                        (holKernel_tyvars ty)) then
                        failwith (strcat (strcat (implode
                          "new_specification: type variables for ") s) (implode
                          " not contained in the type"))
                      else st_ex_return ((s,ty),r)))) eqs) (\eqs.
        let vars' = MAP FST eqs in
        if ~(freesin (MAP (UNCURRY holSyntax_Var) vars') p) then
          failwith (implode (APPEND
            "new_specification: specification not closed by the"
            " definitions"))
        else st_ex_ignore_bind (add_constants vars') (
          st_ex_ignore_bind (add_def (ConstSpec (MAP (\((s,ty),r). (s,r))
            eqs) p)) (
          let ilist = MAP (\(s,ty). (holSyntax_Const s ty,holSyntax_Var s
            ty)) vars' in
          let p = vsubst_aux ilist p in
          st_ex_return (holKernel_Sequent [] p))))`;;

(*
  let new_constant(name,ty) =
    if can get_const_type name then
      failwith ("new_constant: constant "^name^" has already been declared")
    else the_term_constants := (name,ty)::(!the_term_constants)
*)

let new_constant_def = new_definition
  `new_constant (name,ty) =
     st_ex_ignore_bind (add_constants [(name,ty)]) (
        add_def (NewConst name ty))`;;

let new_basic_definition_def = new_definition
  `new_basic_definition tm = st_ex_bind (ASSUME tm) (\th. new_specification
  th)`;;

(*
  let new_basic_definition tm =
    let l,r = dest_eq tm in
    let cname,ty = dest_var l in
    if not(freesin [] r) then failwith "new_definition: term not closed" else
    if not (subset (type_vars_in_term r) (tyvars ty))
    then failwith "new_definition: Type variables not reflected in constant"
    else
      let c = new_constant(cname,ty); mk_const(cname,[]) in
      Sequent([],mk_eq(c,r))
*)

(* HOL4 holKernelScript.sml:1200-1217: code that the source has in a comment *)

(*
  let new_basic_type_definition tyname (absname,repname) (Sequent(asl,c)) =
    if exists (can get_const_type) [absname; repname] then
      failwith "new_basic_type_definition: Constant(s) already in use" else
    if not (asl = []) then
      failwith "new_basic_type_definition: Assumptions in theorem" else
    let P,x = try dest_comb c
              with Failure _ ->
                failwith "new_basic_type_definition: Not a combination" in
    if not(freesin [] P) then
      failwith "new_basic_type_definition: Predicate is not closed" else
    let tyvars = sort (<=) (type_vars_in_term P) in
    let _ = try new_type(tyname,length tyvars)
            with Failure _ ->
                failwith "new_basic_type_definition: Type already defined" in
    let aty = mk_type(tyname,tyvars)
    and rty = type_of x in
    let abs = new_constant(absname,mk_fun_ty rty aty); mk_const(absname,[])
    and rep = new_constant(repname,mk_fun_ty aty rty); mk_const(repname,[]) in
    let a = mk_var("a",aty) and r = mk_var("r",rty) in
    Sequent([],mk_eq(mk_comb(abs,mk_comb(rep,a)),a)),
    Sequent([],mk_eq(mk_comb(P,r),mk_eq(mk_comb(rep,mk_comb(abs,r)),r)))
*)

let new_basic_type_definition_def,new_basic_type_definition_ind = define_guess
  `new_basic_type_definition (tyname,absname,repname,thm) =
     match thm with (holKernel_Sequent asl c) ->
     st_ex_bind (can get_type_arity tyname) (\ok0. st_ex_bind (can
       get_const_type absname) (\ok1. st_ex_bind (can get_const_type repname)
       (\ok2.
     if ok0 then failwith (implode
       "new_basic_type_definition: Type already defined") else if ok1 \/ ok2
       then failwith (implode (APPEND
       "new_basic_type_definition: Constant(s) already in " "use")) else if
       absname = repname then failwith (implode (APPEND
       "new_basic_type_definition: Constants must be disti" "nct")) else if
       ~(asl = []) then
       failwith (implode
         "new_basic_type_definition: Assumptions in theorem") else st_ex_bind
         (holKernel_try dest_comb c (implode
         "new_basic_type_definition: Not a combination")) (\(P,x).
     if ~(freesin [] P) then
       failwith (implode
         "new_basic_type_definition: Predicate is not closed") else let tyvars'
         = MAP holSyntax_Tyvar (MAP implode (sort string_le (MAP explode
         (type_vars_in_term P)))) in
     st_ex_bind (type_of x) (\rty.
        st_ex_ignore_bind (add_type (tyname,LENGTH tyvars')) (st_ex_bind
          (mk_type (tyname,tyvars')) (\aty'.
        st_ex_ignore_bind (add_constants [(absname,mk_fun_ty rty aty');
          (repname,mk_fun_ty aty' rty)]) (
        st_ex_ignore_bind (add_def (TypeDefn tyname P absname repname))
          (st_ex_bind (holKernel_mk_const (repname,[])) (\rep. st_ex_bind
          (holKernel_mk_const (absname,[])) (\abs'. st_ex_bind (st_ex_return
          (mk_var ((implode "a"),aty'))) (\a. st_ex_bind (st_ex_return (mk_var
          ((implode "r"),rty))) (\r. st_ex_bind (mk_comb (rep,a)) (\x1.
          st_ex_bind (safe_mk_eq (holSyntax_Comb abs' x1) a) (\eq1. st_ex_bind
          (mk_comb (abs',r)) (\y1. st_ex_bind (mk_comb (rep,y1)) (\y2.
          st_ex_bind (safe_mk_eq y2 r) (\eq2. st_ex_bind (safe_mk_eq
          (holSyntax_Comb P r) eq2) (\eq3.
        st_ex_return (holKernel_Sequent [] eq1,holKernel_Sequent []
          eq3))))))))))))))))))))`;;

let context_def = new_definition
  `holKernel_context one = get_the_context`;;

(* and the interface *)
let _ = unhide_overloads ();;
