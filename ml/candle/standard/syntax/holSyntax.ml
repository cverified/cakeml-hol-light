(* ======================================================== *)
(*  holSyntax: ported from HOL4's
    candle/standard/syntax/holSyntaxScript.sml
    A definition theory, with 42 definitions, 3 datatypes and 9
    theorems.  Needed by 29 files of the port.  *)
(* ======================================================== *)

(*
  Defines the HOL inference system.
*)

needs "basis/pure/mlstring.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "lib/sorting.ml";;
needs "lib/ternaryComparisons.ml";;
needs "lib/toto.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "holSyntax"
  ["holSyntaxLib"; "mlstring"];;

let _ = do_list hide_constant ["Fun"];;

(* HOL types *)

let type_INDUCT,type_RECURSION = define_datatype
  "type =
     holSyntax_Tyvar mlstring
   | holSyntax_Tyapp mlstring (type list)";;

(* HOL4 holSyntaxScript.sml:18: the overload Fun, which the port expands *)
(* HOL4 holSyntaxScript.sml:19: the overload Bool, which the port expands *)

let domain_raw = new_definition
  `holSyntax_domain ty = match ty with holSyntax_Tyapp n (CONS x xs) -> x |
  _ -> ty`;;

(* domain_def[compute] *)
let holSyntax_domain_def = prove
 (`!t s. holSyntax_domain ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) s
  t) = s`,
  CHEAT_TAC);;
add_simp holSyntax_domain_def;;

let codomain_raw = new_definition
  `codomain ty = match ty with holSyntax_Tyapp n (CONS y (CONS x xs)) -> x |
  _ -> ty`;;

(* [compute] *)
let codomain_def = prove
 (`!t s. codomain ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) s t) = t`,
  CHEAT_TAC);;
add_simp codomain_def;;

(* HOL4 holSyntaxScript.sml:41-44: a proof *)

(* HOL terms *)

let holSyntax_term_INDUCT,holSyntax_term_RECURSION = define_datatype
  "holSyntax_term =
     holSyntax_Var mlstring type
   | holSyntax_Const mlstring type
   | holSyntax_Comb holSyntax_term holSyntax_term
   | holSyntax_Abs holSyntax_term holSyntax_term";;

(* HOL4 holSyntaxScript.sml:55: the overload Equal, which the port expands *)

let dest_var_def = new_definition
  `holSyntax_dest_var (holSyntax_Var x ty) = (x,ty)`;;
add_simp dest_var_def;;

(* Assignment of types to terms (where possible) *)

let has_type = cake_inductive
  `(has_type (holSyntax_Var n ty) ty) /\
   (has_type (holSyntax_Const n ty) ty) /\
   (
    has_type s ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) dty rty)
      /\ has_type t dty ==> has_type (holSyntax_Comb s t) rty) /\
   (has_type t rty ==> has_type (holSyntax_Abs (holSyntax_Var n dty) t)
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) dty rty))`;;

(* A term is welltyped if it has a type. typeof calculates it. *)

let welltyped_def = new_definition
  `welltyped tm = (?ty. has_type tm ty)`;;

let typeof_def,typeof_ind = define_guess
  `(typeof (holSyntax_Var n ty) = ty) /\
   (typeof (holSyntax_Const n ty) = ty) /\
   (typeof (holSyntax_Comb s t) = codomain (typeof s)) /\
   (typeof (holSyntax_Abs v t) = (\s t. holSyntax_Tyapp (implode "fun")
    [s; t]) (typeof v) (typeof t))`;;
add_simp typeof_def;;

(* Auxiliary relation used to define alpha-equivalence. This relation is
   parameterised by the lists of variables bound above the terms. *)

let RACONV = cake_inductive
  `(
     ALPHAVARS env (holSyntax_Var x1 ty1,holSyntax_Var x2 ty2) ==> RACONV
       env (holSyntax_Var x1 ty1,holSyntax_Var x2 ty2)) /\
   (RACONV env (holSyntax_Const x ty,holSyntax_Const x ty)) /\
   (
     RACONV env (s1,s2) /\ RACONV env (t1,t2) ==> RACONV env (holSyntax_Comb
       s1 t1,holSyntax_Comb s2 t2)) /\
   (
     typeof v1 = typeof v2 /\ RACONV (CONS (v1,v2) env) (t1,t2) ==>
       RACONV env (holSyntax_Abs v1 t1,holSyntax_Abs v2 t2))`;;

(* Alpha-equivalence. *)

let ACONV_def = new_definition
  `ACONV t1 t2 <=> RACONV [] (t1,t2)`;;

(* Term ordering, respecting alpha-equivalence *)
(* TODO: use this in the inference system instead of
   ALPHAVARS, ACONV, TERM_UNION, etc., which don't
   lead to canonical hypothesis sets-as-lists *)

let type_lt = cake_inductive
  `(mlstring_lt x1 x2 ==> type_lt (holSyntax_Tyvar x1) (holSyntax_Tyvar x2)) /\
   (type_lt (holSyntax_Tyvar x1) (holSyntax_Tyapp x2 args2)) /\
   ((mlstring_lt LEX LLEX type_lt) (x1,args1) (x2,args2) ==>
      type_lt (holSyntax_Tyapp x1 args1) (holSyntax_Tyapp x2 args2))`;;

let term_lt = cake_inductive
  `((mlstring_lt LEX type_lt) (x1,ty1) (x2,ty2) ==>
     term_lt (holSyntax_Var x1 ty1) (holSyntax_Var x2 ty2)) /\
   (term_lt (holSyntax_Var x1 ty1) (holSyntax_Const x2 ty2)) /\
   (term_lt (holSyntax_Var x1 ty1) (holSyntax_Comb t1 t2)) /\
   (term_lt (holSyntax_Var x1 ty1) (holSyntax_Abs t1 t2)) /\
   ((mlstring_lt LEX type_lt) (x1,ty1) (x2,ty2) ==>
     term_lt (holSyntax_Const x1 ty1) (holSyntax_Const x2 ty2)) /\
   (term_lt (holSyntax_Const x1 ty1) (holSyntax_Comb t1 t2)) /\
   (term_lt (holSyntax_Const x1 ty1) (holSyntax_Abs t1 t2)) /\
   ((term_lt LEX term_lt) (s1,s2) (t1,t2) ==>
    term_lt (holSyntax_Comb s1 s2) (holSyntax_Comb t1 t2)) /\
   (term_lt (holSyntax_Comb s1 s2) (holSyntax_Abs t1 t2)) /\
   ((term_lt LEX term_lt) (s1,s2) (t1,t2) ==>
    term_lt (holSyntax_Abs s1 s2) (holSyntax_Abs t1 t2))`;;

let term_cmp_def = new_definition
  `term_cmp = TO_of_LinearOrder term_lt`;;

let type_cmp_def = new_definition
  `type_cmp = TO_of_LinearOrder type_lt`;;

let ordav_def,ordav_ind = define_guess
  `(ordav [] x1 x2 = term_cmp x1 x2) /\
   (ordav (CONS (t1,t2) env) x1 x2 =
        (if x1 = t1 then
          if x2 = t2 then EQUAL
          else LESS
        else if x2 = t2 then GREATER
        else ordav env x1 x2))`;;

let orda_def,orda_ind = define_guess
  `orda env t1 t2 =
     if t1 = t2 /\ env = [] then EQUAL else match (t1,t2) with
       (holSyntax_Var _ _,holSyntax_Var _ _) -> ordav env t1 t2
       | (holSyntax_Const _ _,holSyntax_Const _ _) -> term_cmp t1 t2
       | (holSyntax_Comb s1 t1,holSyntax_Comb s2 t2) ->
         (let c = orda env s1 s2 in
            if ~(c = EQUAL) then c else orda env t1 t2)
       | (holSyntax_Abs s1 t1,holSyntax_Abs s2 t2) ->
         (let c = type_cmp (typeof s1) (typeof s2) in
            if ~(c = EQUAL) then c else orda (CONS (s1,s2) env) t1 t2)
       | (holSyntax_Var _ _,_) -> LESS
       | (_,holSyntax_Var _ _) -> GREATER
       | (holSyntax_Const _ _,_) -> LESS
       | (_,holSyntax_Const _ _) -> GREATER
       | (holSyntax_Comb _ _,_) -> LESS
       | (_,holSyntax_Comb _ _) -> GREATER`;;

(*
  let rec term_union l1 l2 =
    match (l1,l2) with
      ([],l2) -> l2
    | (l1,[]) -> l1
    | (h1::t1,h2::t2) -> let c = alphaorder h1 h2 in
                         if c = 0 then h1::(term_union t1 t2)
                         else if c < 0 then h1::(term_union t1 l2)
                         else h2::(term_union l1 t2)
*)
let term_union_def,term_union_ind = define_guess
  `term_union l1 l2 =
     match (l1,l2) with ([],l2) -> l2
     | (l1,[]) -> l1
     | (CONS h1 t1,CONS h2 t2) ->
       let c = orda [] h1 h2 in
       if c = EQUAL then CONS h1 (term_union t1 t2)
       else if c = LESS then CONS h1 (term_union t1 l2)
       else CONS h2 (term_union (CONS h1 t1) t2)`;;

let term_remove_def,term_remove_ind = define_guess
  `term_remove t l =
   match l with [] -> l
   | (CONS s ss) ->
     let c = orda [] t s in
     if c = GREATER then
       let ss' = term_remove t ss in
       if ss' = ss then l else CONS s ss'
     else if c = EQUAL then ss else l`;;

let term_image_def,term_image_ind = define_guess
  `term_image f l =
   match l with [] -> l
   | (CONS h t) ->
     let h' = f h in
     let t' = term_image f t in
     if h' = h /\ t' = t then l
     else term_union [h'] t'`;;

(* Whether a variables (or constant) occurs free in a term. *)

let VFREE_IN_def,VFREE_IN_ind = define_guess
  `(VFREE_IN v (holSyntax_Var x ty) <=> ((holSyntax_Var x
    ty:holSyntax_term) = v)) /\
   (VFREE_IN v (holSyntax_Const x ty) <=> ((holSyntax_Const x
    ty:holSyntax_term) = v)) /\
   (VFREE_IN v (holSyntax_Comb s t) <=> VFREE_IN v s \/ VFREE_IN v t) /\
   (VFREE_IN v (holSyntax_Abs w t) <=> (~(w = v)) /\ VFREE_IN v t)`;;
add_simp VFREE_IN_def;;

(* Closed terms: those with no free variables. *)

let CLOSED_def = new_definition
  `CLOSED tm = (!x ty. ~(VFREE_IN (holSyntax_Var x ty) tm))`;;

(* Producing a variant of a variable, guaranteed
   to not be free in a given term. *)

let VFREE_IN_FINITE = prove
 (`!t. FINITE {x | VFREE_IN x t}`,
  CHEAT_TAC);;

let VFREE_IN_FINITE_ALT = prove
 (`!t ty. FINITE {x | VFREE_IN (holSyntax_Var (implode x) ty) t}`,
  CHEAT_TAC);;

let PRIMED_NAME_EXISTS = prove
 (`?n. ~(VFREE_IN (holSyntax_Var (implode (APPEND x (list_of_seq (K (CHR 39))
  n))) ty) t)`,
  CHEAT_TAC);;

(* [local] *)
let LEAST_EXISTS = prove
 (`(?(n:num). P n) ==> (?k. P k /\ (!m. m < k ==> ~(P m)))`,
  CHEAT_TAC);;

(* HOL4 holSyntaxScript.sml:281-287: ML code, not ported *)

let VARIANT_def = new_definition
  `VARIANT t x ty = implode (APPEND x (list_of_seq (K (CHR 39))
  (VARIANT_PRIMES t x ty)))`;;

let VARIANT_THM = prove
 (`!t x ty. ~(VFREE_IN (holSyntax_Var (VARIANT t x ty) ty) t)`,
  CHEAT_TAC);;

(* Substitution for type variables in a type. *)

(* the clauses in two quotations: ty1 is varN and type, which one quotation
   cannot typecheck *)
(* HOL4 holSyntaxScript.sml:305-307: the tactic that proves the termination *)
let TYPE_SUBST_def,TYPE_SUBST_ind = define_guess_clauses
  [`(TYPE_SUBST i (holSyntax_Tyvar v) = REV_ASSOCD (holSyntax_Tyvar v) i
    (holSyntax_Tyvar v)) /\
    (TYPE_SUBST i (holSyntax_Tyapp v tys) = holSyntax_Tyapp v (MAP
    (TYPE_SUBST i) tys))`;
   `TYPE_SUBST i ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty1 ty2)
    = (\s t. holSyntax_Tyapp (implode "fun") [s; t]) (TYPE_SUBST i ty1)
    (TYPE_SUBST i ty2)`];;
add_simp TYPE_SUBST_def;;
(* HOL4 holSyntaxScript.sml:308: the overload is_instance, which the port
   expands *)

(* Substitution for term variables in a term. *)

let VSUBST_def,VSUBST_ind = define_guess
  `(VSUBST ilist (holSyntax_Var x ty) = REV_ASSOCD (holSyntax_Var x ty)
    ilist (holSyntax_Var x ty)) /\
   (VSUBST ilist (holSyntax_Const x ty) = (holSyntax_Const x
    ty:holSyntax_term)) /\
   (VSUBST ilist (holSyntax_Comb s t) = holSyntax_Comb (VSUBST ilist s)
    (VSUBST ilist t)) /\
   (VSUBST ilist (holSyntax_Abs v t) =
        (let ilist' = FILTER (\(s',s). ~(s = v)) ilist in
        let t' = VSUBST ilist' t in
        if EX (\(s',s). VFREE_IN v s' /\ VFREE_IN s t) ilist' then let
            (x,ty) = holSyntax_dest_var v in
             let z = holSyntax_Var (VARIANT t' (explode x) ty) ty in
             let ilist'' = CONS (z,v) ilist' in
             holSyntax_Abs z (VSUBST ilist'' t)
        else holSyntax_Abs v t'))`;;

(* A measure on terms, used in proving
   termination of type instantiation. *)

let sizeof_def,sizeof_ind = define_guess
  `(sizeof (holSyntax_Var x ty) = 1) /\
   (sizeof (holSyntax_Const x ty) = 1) /\
   (sizeof (holSyntax_Comb s t) = 1 + sizeof s + sizeof t) /\
   (sizeof (holSyntax_Abs v t) = 2 + sizeof t)`;;
add_simp sizeof_def;;

let SIZEOF_VSUBST = prove
 (`!t ilist.
              (!s' s. MEM (s',s) ilist ==> (?x ty. s' = holSyntax_Var x
                ty)) ==> sizeof (VSUBST ilist t) = sizeof t`,
  CHEAT_TAC);;

let sizeof_positive = prove
 (`!t. 0 < sizeof t`,
  CHEAT_TAC);;

(* Instantiation of type variables in terms *)

(* the termination relation that HOL4 gives is
     MEASURE (sizeof o SND o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 holSyntaxScript.sml:388-390: the tactic that proves the termination *)
let INST_CORE_def,INST_CORE_ind = define_guess
  `(INST_CORE env tyin (holSyntax_Var x ty) =
         let tm = (holSyntax_Var x ty:holSyntax_term) in
         let tm' = holSyntax_Var x (TYPE_SUBST tyin ty) in
         if REV_ASSOCD tm' env tm = tm then holSyntaxLib_Result tm'
             else holSyntaxLib_Clash tm') /\
   (INST_CORE env tyin (holSyntax_Const x ty) =
        holSyntaxLib_Result (holSyntax_Const x (TYPE_SUBST tyin ty))) /\
   (INST_CORE env tyin (holSyntax_Comb s t) =
        let sres = INST_CORE env tyin s in
        if IS_CLASH sres then sres else let tres = INST_CORE env tyin t in
        if IS_CLASH tres then tres else let s' = RESULT sres and t' =
            RESULT tres in
        holSyntaxLib_Result (holSyntax_Comb s' t')) /\
   (INST_CORE env tyin (holSyntax_Abs v t) =
        let (x,ty) = holSyntax_dest_var v in
        let ty' = TYPE_SUBST tyin ty in
        let v' = holSyntax_Var x ty' in
        let env' = CONS (v,v') env in
        let tres = INST_CORE env' tyin t in
        if IS_RESULT tres then holSyntaxLib_Result (holSyntax_Abs v'
            (RESULT tres)) else let w = CLASH tres in
        if (~(w = v')) then tres else let x' = VARIANT (RESULT (INST_CORE
            [] tyin t)) (explode x) ty' in
        let t' = VSUBST [holSyntax_Var x' ty,holSyntax_Var x ty] t in
        let ty' = TYPE_SUBST tyin ty in
        let env' = CONS (holSyntax_Var x' ty,holSyntax_Var x' ty') env in
        let tres = INST_CORE env' tyin t' in
        if IS_RESULT tres then holSyntaxLib_Result (holSyntax_Abs
            (holSyntax_Var x' ty') (RESULT tres)) else tres)`;;

let INST_def = new_definition
  `holSyntax_INST tyin tm = RESULT (INST_CORE [] tyin tm)`;;

(* Type variables in a type. *)

(* HOL4 holSyntaxScript.sml:401-403: the tactic that proves the termination *)
let tyvars_def,tyvars_ind = define_guess
  `(holSyntax_tyvars (holSyntax_Tyvar v) = [v]) /\
   (holSyntax_tyvars (holSyntax_Tyapp v tys) = ITLIST (\x y. LIST_UNION
    (holSyntax_tyvars x) y) tys [])`;;

(* Type variables in a term. *)

let tvars_def,tvars_ind = define_guess
  `(tvars (holSyntax_Var n ty) = holSyntax_tyvars ty) /\
   (tvars (holSyntax_Const n ty) = holSyntax_tyvars ty) /\
   (tvars (holSyntax_Comb s t) = LIST_UNION (tvars s) (tvars t)) /\
   (tvars (holSyntax_Abs v t) = LIST_UNION (tvars v) (tvars t))`;;

(* Syntax for equations *)

let equation_def = new_definition
  `((===) s t) = holSyntax_Comb (holSyntax_Comb ((\ty. holSyntax_Const
  (implode "=") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode
  "bool") [])))) (typeof s)) s) t`;;


(* Signature of a theory: indicates the defined type operators, with arities,
   and defined constants, with types. *)

new_type_abbrev("tysig",`:(mlstring,num)fmap`);;
new_type_abbrev("tmsig",`:(mlstring,type)fmap`);;
new_type_abbrev("sig",`:tysig#tmsig`);;
(* HOL4 holSyntaxScript.sml:429: the overload tysof, which the port expands *)
(* HOL4 holSyntaxScript.sml:430: the overload tmsof, which the port expands *)

(* Well-formedness of types/terms with respect to a signature *)

(* HOL4 holSyntaxScript.sml:439-441: the tactic that proves the termination *)
let type_ok_def,type_ok_ind = define_guess
  `(type_ok tysig (holSyntax_Tyvar _) <=> T) /\
   (type_ok tysig (holSyntax_Tyapp name args) <=>
          FLOOKUP tysig name = SOME (LENGTH args) /\
          ALL (type_ok tysig) args)`;;

let holSyntax_term_ok_def,holSyntax_term_ok_ind = define_guess
  `(holSyntax_term_ok sig (holSyntax_Var x ty) <=> type_ok (FST sig) ty) /\
   (holSyntax_term_ok sig (holSyntax_Const name ty) <=>
         (?ty0. FLOOKUP (SND sig) name = SOME ty0 /\
               type_ok (FST sig) ty /\
               (\ty0 ty. ?i. ty = TYPE_SUBST i ty0) ty0 ty)) /\
   (holSyntax_term_ok sig (holSyntax_Comb tm1 tm2) <=>
         holSyntax_term_ok sig tm1 /\
         holSyntax_term_ok sig tm2 /\
         welltyped ((holSyntax_Comb tm1 tm2:holSyntax_term))) /\
   (holSyntax_term_ok sig (holSyntax_Abs v tm) <=>
         (?x ty.
           v = holSyntax_Var x ty /\
           type_ok (FST sig) ty /\
           holSyntax_term_ok sig tm))`;;

(* Well-formed sets of hypotheses, represented as lists,
   are strictly sorted up to alpha-equivalence *)

let alpha_lt_def = new_definition
  `alpha_lt t1 t2 <=> orda [] t1 t2 = LESS`;;

let hypset_ok_def = new_definition
  `hypset_ok ls <=> SORTED alpha_lt ls`;;

(* A theory is a signature together with a set of axioms. It is well-formed if
   the types of the constants are all ok, the axioms are all ok terms of type
   bool, and the signature is standard. *)

new_type_abbrev("thy",`:sig#(holSyntax_term->bool)`);;
(* HOL4 holSyntaxScript.sml:476: the overload sigof, which the port expands *)
(* HOL4 holSyntaxScript.sml:477: the overload axsof, which the port expands *)
(* HOL4 holSyntaxScript.sml:478: the overload tysof, which the port expands *)
(* HOL4 holSyntaxScript.sml:479: the overload tmsof, which the port expands *)

  (* Standard signature includes the minimal type operators and constants *)

let is_std_sig_def = new_definition
  `is_std_sig (sig:(mlstring,num)fmap#(mlstring,type)fmap) <=>
     FLOOKUP (FST sig) (implode "fun") = SOME 2 /\
     FLOOKUP (FST sig) (implode "bool") = SOME 0 /\
     FLOOKUP (SND sig) (implode "=") = SOME ((\s t. holSyntax_Tyapp
       (implode "fun") [s; t]) (holSyntax_Tyvar (implode "A")) ((\s t.
       holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyvar (implode
       "A")) (holSyntax_Tyapp (implode "bool") [])))`;;

let theory_ok_def = new_definition
  `theory_ok
  (thy:((mlstring,num)fmap#(mlstring,type)fmap)#(holSyntax_term->bool)) <=>
     (!ty. ty IN FRANGE (SND (FST thy)) ==> type_ok (FST (FST thy)) ty) /\
     (!p. p IN (SND thy) ==>
       holSyntax_term_ok (FST thy)
       p /\ has_type p (holSyntax_Tyapp (implode "bool") [])) /\
     is_std_sig (FST thy)`;;

(* Sequents provable from a theory *)

let proves = cake_inductive
  `((
      ~(EX (VFREE_IN (holSyntax_Var x ty)) h) /\ type_ok (FST (FST thy)) ty
        /\ (|-) (thy,h) ((===) l r) ==> (|-) (thy,h) ((===) (holSyntax_Abs
        (holSyntax_Var x ty) l) (holSyntax_Abs (holSyntax_Var x ty) r)))) /\
   ((
      theory_ok thy /\ has_type p (holSyntax_Tyapp (implode "bool") [])
        /\ holSyntax_term_ok (FST thy) p ==> (|-) (thy,[p]) p)) /\
   ((
      theory_ok thy /\ type_ok (FST (FST thy)) ty /\ holSyntax_term_ok
        (FST thy) t ==> (|-) (thy,[])
        ((===) (holSyntax_Comb (holSyntax_Abs (holSyntax_Var x ty) t)
        (holSyntax_Var x ty)) t))) /\
   ((
      (|-) (thy,h1) c1 /\ (|-) (thy,h2) c2 ==>
              (|-) (thy,term_union (term_remove c2 h1)
                         (term_remove c1 h2)) ((===) c1 c2))) /\
   ((
      (|-) (thy,h1) ((===) p q) /\ (|-) (thy,h2) p' /\ ACONV p p' ==> (|-)
        (thy,term_union h1 h2) q)) /\
   ((
      (!s s'. MEM (s',s) ilist ==>
                (?x ty. (s = holSyntax_Var x ty) /\ has_type s' ty
                  /\ holSyntax_term_ok (FST thy) s')) /\ (|-) (thy,h)
                  c ==> (|-) (thy,term_image (VSUBST ilist) h) (VSUBST ilist
                  c))) /\
   ((
      (ALL (type_ok (FST (FST thy))) (MAP FST tyin)) /\ (|-) (thy,h) c ==> (|-)
        (thy,term_image (holSyntax_INST tyin) h) (holSyntax_INST tyin c))) /\
   ((
      (|-) (thy,h1) ((===) l1 r1) /\ (|-) (thy,h2) ((===) l2 r2) /\
      welltyped (holSyntax_Comb l1 l2) ==> (|-) (thy,term_union h1 h2)
        ((===) (holSyntax_Comb l1 l2) (holSyntax_Comb r1 r2)))) /\
   ((
      theory_ok thy /\ holSyntax_term_ok (FST thy) t ==> (|-) (thy,[]) ((===) t
        t))) /\
   ((
      theory_ok thy /\ c IN (SND thy) ==> (|-) (thy,[]) c))`;;

(* A context is a sequence of updates *)

let holSyntax_update_INDUCT,holSyntax_update_RECURSION = define_datatype
  "holSyntax_update =
     // Definition of new constants by specification
     // ConstSpec witnesses proposition
     ConstSpec ((mlstring#holSyntax_term) list) holSyntax_term
     // Definition of a new type operator
     // TypeDefn name predicate abs_name rep_name
   | TypeDefn mlstring holSyntax_term mlstring mlstring
     // NewType name arity
   | NewType mlstring num
     // NewConst name type
   | NewConst mlstring type
     // NewAxiom proposition
   | NewAxiom holSyntax_term";;

(* Projecting out pieces of the context *)

  (* Types and constants introduced by an update *)
let types_of_upd_def = define_cases
  `(types_of_upd (ConstSpec _ _) = []) /\
   (types_of_upd (TypeDefn name pred _ _) = [(name,LENGTH (tvars pred))]) /\
   (types_of_upd (NewType name arity) = [(name,arity)]) /\
   (types_of_upd (NewConst _ _) = []) /\
   (types_of_upd (NewAxiom _) = [])`;;
add_simp types_of_upd_def;;

let consts_of_upd_def = define_cases
  `(consts_of_upd (ConstSpec eqs prop) = MAP (\(s,t). (s,typeof t)) eqs) /\
   (consts_of_upd (TypeDefn name pred abs' rep) =
         let rep_type = holSyntax_domain (typeof pred) in
         let abs_type = holSyntax_Tyapp name (MAP holSyntax_Tyvar (MAP
             implode (STRING_SORT (MAP explode (tvars pred))))) in
           [(abs',(\s t. holSyntax_Tyapp (implode "fun") [s; t]) rep_type
               abs_type);
            (rep,(\s t. holSyntax_Tyapp (implode "fun") [s; t])
                abs_type rep_type)]) /\
   (consts_of_upd (NewType _ _) = []) /\
   (consts_of_upd (NewConst name type) = [(name,type)]) /\
   (consts_of_upd (NewAxiom _) = [])`;;
add_simp consts_of_upd_def;;

(* HOL4 holSyntaxScript.sml:594: the overload type_list, which the port
   expands *)
(* HOL4 holSyntaxScript.sml:595: the overload tysof, which the port expands *)
(* HOL4 holSyntaxScript.sml:596: the overload const_list, which the port
   expands *)
(* HOL4 holSyntaxScript.sml:597: the overload tmsof, which the port expands *)

  (* From this we can recover a signature *)
(* HOL4 holSyntaxScript.sml:600: the overload sigof, which the port expands *)

  (* Axioms: we divide them into axiomatic extensions and conservative
     extensions, we will prove that the latter preserve consistency *)
let axexts_of_upd_def = new_definition
  `axexts_of_upd x1 =
   match x1 with
     NewAxiom prop -> [prop]
   | _ -> []`;;
add_simp axexts_of_upd_def;;

let conexts_of_upd_def = new_definition
  `conexts_of_upd x1' =
     match x1' with
       ConstSpec eqs prop ->
       let ilist = MAP (\(s,t). let ty = typeof t in (holSyntax_Const s
         ty,holSyntax_Var s ty)) eqs in
         [VSUBST ilist prop]
     | TypeDefn name pred abs_name rep_name ->
       let abs_type = holSyntax_Tyapp name (MAP holSyntax_Tyvar (MAP implode
         (STRING_SORT (MAP explode (tvars pred))))) in
       let rep_type = holSyntax_domain (typeof pred) in
       let abs' = holSyntax_Const abs_name ((\s t. holSyntax_Tyapp (implode
         "fun") [s; t]) rep_type abs_type) in
       let rep = holSyntax_Const rep_name ((\s t. holSyntax_Tyapp (implode
         "fun") [s; t]) abs_type rep_type) in
       let a = holSyntax_Var (implode "a") abs_type in
       let r = holSyntax_Var (implode "r") rep_type in
         [(===) (holSyntax_Comb abs' (holSyntax_Comb rep a)) a; (===)
           (holSyntax_Comb pred r) ((===) (holSyntax_Comb rep (holSyntax_Comb
           abs' r)) r)]
     | _ -> []`;;

(* HOL4 holSyntaxScript.sml:625: the overload axexts, which the port expands *)
(* HOL4 holSyntaxScript.sml:626: the overload conexts, which the port
   expands *)

(* HOL4 holSyntaxScript.sml:628: the overload axioms_of_upd, which the port
   expands *)
(* HOL4 holSyntaxScript.sml:629: the overload axiom_list, which the port
   expands *)
(* HOL4 holSyntaxScript.sml:630: the overload axsof, which the port expands *)

(* Now we can recover the theory associated with a context *)
(* HOL4 holSyntaxScript.sml:633: the overload thyof, which the port expands *)

(* Principles for extending the context *)

let updates = cake_inductive
  `(
    has_type
    // new_axiom
    prop (holSyntax_Tyapp (implode "bool") []) /\
    holSyntax_term_ok ((\(ctxt:holSyntax_update list). ((\ctxt.
      alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
      alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt)
      prop ==> updates (NewAxiom prop) ctxt) /\
   (
    ~(
    // new_constant
    name IN (FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
      ctxt)) ctxt)) ctxt))) /\
    type_ok ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
      ctxt)) ctxt) ty ==> updates (NewConst name ty) ctxt) /\
   (
    (|-) (
     // new_specification
     (\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list).
       ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
       ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
       ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
       (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) ctxt,MAP
       (\(s,t). (===) (holSyntax_Var s (typeof t)) t) eqs) prop /\
    ALL
      (\t. CLOSED t /\
           (!v. MEM v (tvars t) ==> MEM v (holSyntax_tyvars (typeof t))))
      (MAP SND eqs) /\
    (!x ty. VFREE_IN (holSyntax_Var x ty) prop ==>
              MEM (x,ty) (MAP (\(s,t). (s,typeof t)) eqs)) /\
    (!s. MEM s (MAP FST eqs) ==> ~(s IN (FDOM ((\ctxt. alist_to_fmap
      ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)))) /\
    ALL_DISTINCT (MAP FST eqs) ==> updates (ConstSpec eqs prop) ctxt) /\
   (
    ~(
    // new_type
    name IN (FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd
      ctxt)) ctxt)) ctxt))) ==> updates (NewType name arity) ctxt) /\
   (
    (|-) (
     // new_type_definition
     (\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list).
       ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
       ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
       ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
       (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) ctxt,[])
       (holSyntax_Comb pred witness) /\
    CLOSED pred /\ ~(name IN (FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT
      (MAP types_of_upd ctxt)) ctxt)) ctxt))) /\ ~(abs IN (FDOM ((\ctxt.
      alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)))
      /\ ~(rep IN (FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
      consts_of_upd ctxt)) ctxt)) ctxt))) /\ ~(abs = rep) ==> updates
      (TypeDefn name pred abs rep) ctxt)`;;

let extends_def = new_definition
  `extends <=> RTC (\ctxt2 ctxt1. ?upd. ctxt2 = CONS upd ctxt1 /\ updates
  upd ctxt1)`;;

(* Initial theory context *)

let init_ctxt_def = new_definition
  `init_ctxt = [NewConst (implode "=") ((\s t. holSyntax_Tyapp (implode
  "fun") [s; t]) (holSyntax_Tyvar (implode "A")) ((\s t. holSyntax_Tyapp
  (implode "fun") [s; t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyapp
  (implode "bool") []))); NewType (implode "bool") 0; NewType (implode
  "fun") 2]`;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["Fun"];;

(* and the interface *)
let _ = unhide_overloads ();;
