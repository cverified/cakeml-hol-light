(* ======================================================== *)
(*  holKernelProof: ported from HOL4's
    candle/standard/monadic/holKernelProofScript.sml
    A proof theory about holKernel.ml, with 8 definitions and 178
    theorems.  Needed by 13 files of the port.  *)
(* ======================================================== *)

(*
  Prove correctness of the monadic functions, i.e. prove that they are
  faithful to the inference rules of the Candle logic.
*)

needs "basis/pure/mllist.ml";;
needs "basis/pure/mlstring.ml";;
needs "candle/standard/monadic/holKernel.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "semantics/namespace.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "holKernelProof"
  ["holKernel"; "holSyntax"; "holSyntaxExtra"; "holSyntaxLib";
   "ml_monadBase"; "mllist"; "mlstring"];;

let _ = do_list hide_constant ["Bool"; "const_list"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["name","CommandLineProof_name";
   "vars","vars"];;

(* HOL4 holKernelProofScript.sml:20: the overload failwith, which the port
   expands *)
(* HOL4 holKernelProofScript.sml:21: the overload raise_clash, which the
   port expands *)
(* HOL4 holKernelProofScript.sml:22: the overload handle_clash, which the
   port expands *)

(* HOL4 holKernelProofScript.sml:26: the type abbreviation M, which the port
   expands *)

let rev_assocd_thm = prove
 (`rev_assocd = REV_ASSOCD`,
  CHEAT_TAC);;

(* HOL4 holKernelProofScript.sml:36: ML code, not ported *)

(* [local] *)
let REPLICATE_11 = prove
 (`!m n x. (REPLICATE n x = REPLICATE m x) = (m = n)`,
  CHEAT_TAC);;

(* HOL4 holKernelProofScript.sml:44: the overload impossible_term, which the
   port expands *)

(* ------------------------------------------------------------------------- *)
(* case_eq theorems                                                          *)
(* ------------------------------------------------------------------------- *)

(* HOL4 holKernelProofScript.sml:50-52: ML code, not ported *)

(* ------------------------------------------------------------------------- *)
(* Refinement invariants                                                     *)
(* ------------------------------------------------------------------------- *)

let TYPE_def = new_definition
  `TYPE ctxt ty = type_ok ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
  types_of_upd ctxt)) ctxt)) ctxt) ty`;;

let TERM_def = new_definition
  `TERM ctxt tm = holSyntax_term_ok ((\(ctxt:holSyntax_update list).
  ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
  ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt))
  ctxt)) (ctxt:holSyntax_update list)) tm`;;

let CONTEXT_def = new_definition
  `CONTEXT ctxt = extends ctxt init_ctxt`;;

let THM_def = new_definition
  `THM ctxt (holKernel_Sequent asl c) = ((|-) ((\(ctxt:holSyntax_update
  list). ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt.
  FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
  FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
  ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
  ctxt)) ctxt)) ctxt)) ctxt,asl) c)`;;

let lift_tm_def = new_definition
  `lift_tm c = holKernel_Sequent [] c`;;

let STATE_def = new_definition
  `STATE ctxt state = (
       (ctxt = hol_refs_the_context state) /\ CONTEXT ctxt /\
       (hol_refs_the_type_constants state = (\ctxt. FLAT (MAP types_of_upd
         ctxt)) ctxt) /\
       (hol_refs_the_term_constants state = (\ctxt. FLAT (MAP consts_of_upd
         ctxt)) ctxt) /\
       (hol_refs_the_axioms state = MAP lift_tm ((\ctxt. FLAT (MAP
         axexts_of_upd ctxt)) ctxt)))`;;

(* ------------------------------------------------------------------------- *)
(* impossible term lemmas                                                    *)
(* ------------------------------------------------------------------------- *)

(* [local] *)
let term_ok_impossible_term = prove
 (`~(holSyntax_term_ok defs (holSyntax_Comb (holSyntax_Var (implode "x")
  (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Var (implode "x")
  (holSyntax_Tyapp (implode "bool") []))))`,
  CHEAT_TAC);;

(* [local] *)
let impossible_term_thm = prove
 (`TERM defs tm ==> ~(tm = (holSyntax_Comb (holSyntax_Var (implode "x")
  (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Var (implode "x")
  (holSyntax_Tyapp (implode "bool") []))))`,
  CHEAT_TAC);;

(* [local] *)
let Abs_Var = prove
 (`TERM defs (holSyntax_Abs v tm) ==> (?s ty. v = holSyntax_Var s ty)`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------- *)
(* invariant lemmas                                                          *)
(* ------------------------------------------------------------------------- *)

(* [local] *)
let CONTEXT_ALL_DISTINCT = prove
 (`CONTEXT defs ==> ALL_DISTINCT (MAP FST ((\ctxt. FLAT (MAP types_of_upd
  ctxt)) defs)) /\
                    ALL_DISTINCT (MAP FST ((\ctxt. FLAT (MAP consts_of_upd
                      ctxt)) defs))`,
  CHEAT_TAC);;

(* [local] *)
let STATE_ALL_DISTINCT = prove
 (`STATE defs s ==> ALL_DISTINCT (MAP FST (hol_refs_the_type_constants s)) /\
                    ALL_DISTINCT (MAP FST (hol_refs_the_term_constants s))`,
  CHEAT_TAC);;

(* [local] *)
let TYPE_Tyapp = prove
 (`MEM (tyop,LENGTH args) (hol_refs_the_type_constants r) /\
     STATE defs r /\ ALL (TYPE defs) args ==>
     TYPE defs (holSyntax_Tyapp tyop args)`,
  CHEAT_TAC);;

(* [local] *)
let CONTEXT_std_sig = prove
 (`CONTEXT defs ==> is_std_sig ((\(ctxt:holSyntax_update list). ((\ctxt.
  alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
  alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) defs)`,
  CHEAT_TAC);;

(* [local] *)
let CONTEXT_fun = prove
 (`CONTEXT defs ==>
       (!a. MEM ((implode "fun"),a) ((\ctxt. FLAT (MAP types_of_upd ctxt))
         defs) <=> (a = 2))`,
  CHEAT_TAC);;

let TYPE = prove
 (`(STATE defs state ==> TYPE defs (holSyntax_Tyvar v)) /\
   (TYPE defs (holSyntax_Tyapp op tys) ==> ALL (TYPE defs) tys)`,
  CHEAT_TAC);;

let TERM = prove
 (`(TERM defs (holSyntax_Var n ty) ==> TYPE defs ty) /\
   (TERM defs (holSyntax_Const n ty) ==> TYPE defs ty) /\
   (TERM defs (holSyntax_Abs (holSyntax_Var v ty) x) ==> TERM defs x /\ TYPE
     defs ty) /\
   (TERM defs (holSyntax_Comb x y) ==> TERM defs x /\ TERM defs y)`,
  CHEAT_TAC);;

(* [local] *)
let TYPE_Fun = prove
 (`CONTEXT defs /\ TYPE defs ty1 /\ TYPE defs ty2 ==>
     TYPE defs (holSyntax_Tyapp (implode "fun") [ty1; ty2])`,
  CHEAT_TAC);;

(* [local] *)
let TERM_Var_SIMP = prove
 (`(TERM defs (holSyntax_Var n ty) = TYPE defs ty)`,
  CHEAT_TAC);;

(* [local] *)
let TERM_Var = prove
 (`TYPE defs ty ==> TERM defs (holSyntax_Var n ty)`,
  CHEAT_TAC);;

(* [local] *)
let IMP_TERM_Abs = prove
 (`TERM defs (holSyntax_Var str ty) /\ TERM defs bod ==>
     TERM defs (holSyntax_Abs (holSyntax_Var str ty) bod)`,
  CHEAT_TAC);;

(* [local] *)
let IMP_TERM_Comb = prove
 (`TERM defs f /\
     TERM defs a /\
     (typeof a = ty1) /\
     (typeof f = (\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty1 ty2) ==>
     TERM defs (holSyntax_Comb f a)`,
  CHEAT_TAC);;

(* [local] *)
let TERM_Abs = prove
 (`TERM defs (holSyntax_Abs (holSyntax_Var v ty) tm) <=> TYPE defs ty /\ TERM
  defs tm`,
  CHEAT_TAC);;

(* HOL4 holKernelProofScript.sml:228-230: ML code, not ported *)

(* HOL4 holKernelProofScript.sml:232-256: a theorem that HOL4 states as the
   value of an ML expression: INST_CORE_EMPTY *)

let THM = prove
 (`THM defs (holKernel_Sequent asl c) ==> ALL (TERM defs) asl /\ TERM defs c`,
  CHEAT_TAC);;

(* HOL4 holKernelProofScript.sml:266-270: ML code, not ported *)

(* [local] *)
let type_subst_EMPTY = prove
 (`!ty. holKernel_type_subst [] ty = ty`,
  CHEAT_TAC);;

(* [local] *)
let MAP_EQ_2 = prove
 (`(MAP f l = [x; y]) <=> (?x0 y0. (l = [x0; y0]) /\ (x = f x0) /\ (y = f
  y0))`,
  CHEAT_TAC);;

(* [local] *)
let sequent_has_type_bool = prove
 (`(|-) (d,h) c ==> ALL (\t. has_type t (holSyntax_Tyapp (implode "bool")
  [])) (CONS c h)`,
  CHEAT_TAC);;

(* [local] *)
let THM_term_ok_bool = prove
 (`THM defs (holKernel_Sequent asl p) ==>
     ALL (\t. holSyntax_term_ok ((\(ctxt:holSyntax_update list). ((\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
       ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
       ctxt)) ctxt)) defs) t /\ (typeof t = (holSyntax_Tyapp (implode "bool")
       []))) (CONS p asl)`,
  CHEAT_TAC);;

(* TODO move *)
let ALOOKUP_ALL_DISTINCT_MEM_EXISTS = prove
 (`(?k. MEM (k,v) alist) /\
    ALL_DISTINCT (MAP FST alist) ==>
    (?k. ALOOKUP alist k = SOME v)`,
  CHEAT_TAC);;

let the_term_constants_TYPE = prove
 (`STATE defs refs ==>
   ALL (\(_,ty). TYPE defs ty) (hol_refs_the_term_constants refs)`,
  CHEAT_TAC);;

let the_axioms_THM = prove
 (`STATE defs refs ==>
   ALL (THM defs) (hol_refs_the_axioms refs)`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Verification of type functions                                            *)
(* ------------------------------------------------------------------------- *)
(* [local] *)
let can_thm = prove
 (`can f x s = match f x s with (M_success _,s) -> (M_success T,s) | (_,s) ->
  (M_success F,s)`,
  CHEAT_TAC);;

let assoc_thm = prove
 (`!xs y z s s'.
      (assoc y xs s = (z,s')) ==>
      (s' = s) /\ (!i. (z = M_success i) ==> MEM (y,i) xs) /\
                  (!e. (z = M_failure e) ==> (!i. ~(MEM (y,i) xs)))`,
  CHEAT_TAC);;

(* [local] *)
let get_type_arity_thm = prove
 (`!name s z s'.
       (get_type_arity name s = (z,s')) ==> (s' = s) /\
       (!i. (z = M_success i) ==> MEM (name,i) (hol_refs_the_type_constants
         s)) /\
       (!e. (z = M_failure e) ==> (!i. ~(MEM (name,i)
         (hol_refs_the_type_constants s))))`,
  CHEAT_TAC);;

let mk_vartype_thm = prove
 (`!name s.
      STATE ctxt s ==>
      TYPE ctxt (mk_vartype name)`,
  CHEAT_TAC);;

let mk_type_thm = prove
 (`!tyop args s z s'.
      (mk_type (tyop,args) s = (z,s')) /\
      STATE defs s /\
      ALL (TYPE defs) args ==>
        (s' = s) /\
        ((tyop = (implode "fun")) /\ (LENGTH args = 2) ==> (?i. z =
          M_success i)) /\
        (!i. (z = M_success i) ==> TYPE defs i /\ (i = holSyntax_Tyapp
          tyop args))`,
  CHEAT_TAC);;

(* [local] *)
let mk_type_bool = prove
 (`STATE defs s ==> (mk_type ((implode "bool"),[]) s = (M_success
  (holSyntax_Tyapp (implode "bool") []),s))`,
  CHEAT_TAC);;

let dest_type_thm = prove
 (`!ty s z s'.
      STATE defs s /\
      (dest_type ty s = (z,s')) /\ TYPE defs ty ==> (s' = s) /\
      (!i. (z = M_success i) ==> (?n tys. (ty = holSyntax_Tyapp n tys) /\ (i
        = (n,tys)) /\
                              ALL (TYPE defs) tys))`,
  CHEAT_TAC);;

let dest_vartype_thm = prove
 (`!ty s z s'.
      (dest_vartype ty s = (z,s')) ==> (s' = s) /\
      (!i. (z = M_success i) ==> (ty = holSyntax_Tyvar i))`,
  CHEAT_TAC);;

let is_type_thm = prove
 (`!ty. is_type ty = (?s tys. ty = holSyntax_Tyapp s tys)`,
  CHEAT_TAC);;

let is_vartype_thm = prove
 (`!ty. is_vartype ty = (?s. ty = holSyntax_Tyvar s)`,
  CHEAT_TAC);;

(* [local] *)
let tyvars_thm = prove
 (`!ty s. MEM s (holKernel_tyvars ty) = MEM s (holSyntax_tyvars ty)`,
  CHEAT_TAC);;

(* type_subst *)
let holKernelProof_type_subst = prove
 (`!i ty.
      (holKernel_type_subst i ty = TYPE_SUBST i ty) /\
      (ALL (\(x,y). TYPE s x /\ TYPE s y) i /\ TYPE s ty ==>
       TYPE s (holKernel_type_subst i ty))`,
  CHEAT_TAC);;

let mk_fun_ty_thm = prove
 (`!ty1 ty2.
     CONTEXT defs /\ ALL (TYPE defs) [ty1; ty2] /\
     (mk_fun_ty ty1 ty2 = i) ==>
     (i = (\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty1 ty2) /\ TYPE
       defs i`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Verification of term functions                                            *)
(* ------------------------------------------------------------------------- *)

(* HOL4 holKernelProofScript.sml:512: the overload aty, which the port
   expands *)

(* [local] *)
let get_const_type_thm = prove
 (`!name s z s'.
       (get_const_type name s = (z,s')) ==> (s' = s) /\
       (!i. (z = M_success i) ==> MEM (name,i) (hol_refs_the_term_constants
         s)) /\
       (!e. (z = M_failure e) ==> (!i. ~(MEM (name,i)
         (hol_refs_the_term_constants s))))`,
  CHEAT_TAC);;

let term_type_def,term_type_ind = define_guess
  `term_type tm =
     match tm with
       holSyntax_Var _ ty -> ty
     | holSyntax_Const _ ty -> ty
     | holSyntax_Comb s _ -> (match term_type s with holSyntax_Tyapp
       (implode "fun") (CONS _ (CONS ty1 _)) -> ty1
                              | _ -> holSyntax_Tyvar (implode ""))
     | holSyntax_Abs (holSyntax_Var _ ty) t -> holSyntax_Tyapp (implode
       "fun") [ty; term_type t]
     | _ -> holSyntax_Tyvar (implode "")`;;

let term_type = prove
 (`!defs tm. CONTEXT defs /\ TERM defs tm ==>
     (term_type tm = typeof tm) /\
     TYPE defs (term_type tm)`,
  CHEAT_TAC);;

let type_of_has_type = prove
 (`!tm refs ty refs'.
     STATE defs refs /\
     TERM defs tm /\
     (type_of tm refs = (M_success ty,refs')) ==> has_type tm ty /\
     (typeof tm = ty)`,
  CHEAT_TAC);;

let type_of_thm = prove
 (`!tm. TERM defs tm /\ STATE defs s ==>
        (type_of tm s = (M_success (term_type tm),s))`,
  CHEAT_TAC);;

(* [local] *)
let alphavars_thm = prove
 (`!env.
       STATE defs s /\ TERM defs tm1 /\ TERM defs tm2 /\
       ALL (\(v1,v2). TERM defs v1 /\ TERM defs v2) env ==>
       (alphavars env tm1 tm2 = ALPHAVARS env (tm1,tm2))`,
  CHEAT_TAC);;

(* [local] *)
let raconv_thm = prove
 (`!tm1 tm2 env.
       STATE defs s /\ TERM defs tm1 /\ TERM defs tm2 /\
       ALL (\(v1,v2). TERM defs v1 /\ TERM defs v2) env ==>
       (raconv env tm1 tm2 = RACONV env (tm1,tm2))`,
  CHEAT_TAC);;

let aconv_thm = prove
 (`!tm1 tm2 env.
      STATE defs s /\ TERM defs tm1 /\ TERM defs tm2 ==>
      (aconv tm1 tm2 = ACONV tm1 tm2)`,
  CHEAT_TAC);;

let is_term_thm = prove
 (`(is_var tm = (?n ty. tm = holSyntax_Var n ty)) /\
    (holKernel_is_const tm = (?n ty. tm = holSyntax_Const n ty)) /\
    (is_abs tm = (?v x. tm = holSyntax_Abs v x)) /\
    (is_comb tm = (?x y. tm = holSyntax_Comb x y))`,
  CHEAT_TAC);;

let mk_var_thm = prove
 (`STATE defs s /\ TYPE defs ty ==> TERM defs (mk_var (v,ty))`,
  CHEAT_TAC);;

let mk_abs_thm = prove
 (`!res.
      (mk_abs (bvar,bod) s = (res,s1)) /\
      TERM defs bvar /\
      TERM defs bod ==>
      (s1 = s) /\ (!t. (res = M_success t) ==> TERM defs t /\ (t =
        holSyntax_Abs bvar bod))`,
  CHEAT_TAC);;

let mk_comb_thm = prove
 (`(mk_comb (f,a) s = (res,s1)) /\
   TERM defs f /\
   TERM defs a /\
   STATE defs s ==>
     (s1 = s) /\
     (!t. (res = M_failure t) ==> (!ty. ~(term_type f = (\s t.
       holSyntax_Tyapp (implode "fun") [s; t]) (term_type a) ty))) /\
     (!t. (res = M_success t) ==> TERM defs t /\ (t = holSyntax_Comb f a))`,
  CHEAT_TAC);;

let dest_var_thm = prove
 (`TERM defs v /\ STATE defs s ==>
    (holKernel_dest_var v s = (res,s')) ==>
    (s' = s) /\ (!n ty. (res = M_success (n,ty)) ==> TYPE defs ty)`,
  CHEAT_TAC);;

let dest_const_thm = prove
 (`TERM defs v /\ STATE defs s ==>
    (holKernel_dest_const v s = (res,s')) ==>
    (s' = s) /\ (!n ty. (res = M_success (n,ty)) ==> TYPE defs ty)`,
  CHEAT_TAC);;

let dest_comb_thm = prove
 (`(dest_comb v s = (res,s')) ==>
   TERM defs v /\ STATE defs s ==>
    (s' = s) /\ (!x y. (res = M_success (x,y)) ==> TERM defs x /\ TERM
      defs y)`,
  CHEAT_TAC);;

let dest_abs_thm = prove
 (`TERM defs v /\ STATE defs s ==>
    (dest_abs v s = (res,s')) ==>
    (s' = s) /\ (!x y. (res = M_success (x,y)) ==> TERM defs x /\ TERM
      defs y)`,
  CHEAT_TAC);;

let rator_thm = prove
 (`TERM defs v /\ STATE defs s ==>
    (rator v s = (res,s')) ==>
    (s' = s) /\ (!x. (res = M_success x) ==> TERM defs x)`,
  CHEAT_TAC);;

let rand_thm = prove
 (`TERM defs v /\ STATE defs s ==>
    (rand v s = (res,s')) ==>
    (s' = s) /\ (!x. (res = M_success x) ==> TERM defs x)`,
  CHEAT_TAC);;

(* [local] *)
let type_subst_bool = prove
 (`holKernel_type_subst i (holSyntax_Tyapp (implode "bool") []) =
  (holSyntax_Tyapp (implode "bool") [])`,
  CHEAT_TAC);;

(* [local] *)
let type_subst_fun = prove
 (`holKernel_type_subst i (ast_Fun ty1 ty2) = (\s t. holSyntax_Tyapp (implode
  "fun") [s; t]) (holKernel_type_subst i ty1) (holKernel_type_subst i ty2)`,
  CHEAT_TAC);;

(* [local] *)
let TERM_Const = prove
 (`STATE defs r /\ MEM (name,a) (hol_refs_the_term_constants r) ==>
     TERM defs (holSyntax_Const name a)`,
  CHEAT_TAC);;

(* [local] *)
let TERM_Const_type_subst = prove
 (`ALL (\(x,y). TYPE defs x /\ TYPE defs y) theta /\
     TERM defs (holSyntax_Const name a) ==> TERM defs (holSyntax_Const
       name (holKernel_type_subst theta a))`,
  CHEAT_TAC);;

let mk_const_thm = prove
 (`!name theta s z s'.
      (holKernel_mk_const (name,theta) s = (z,s')) /\
      STATE defs s /\
      ALL (\(x,y). TYPE defs x /\ TYPE defs y) theta ==>
        (s' = s) /\
        (!i. (z = M_success i) ==> TERM defs i)`,
  CHEAT_TAC);;

(* [local] *)
let get_const_type_Equal = prove
 (`STATE defs s ==>
     (get_const_type (implode "=") s = (M_success ((\s t. holSyntax_Tyapp
       (implode "fun") [s; t]) ((holSyntax_Tyvar (implode "A")):type)
       (ast_Fun ((holSyntax_Tyvar (implode "A")):type) (holSyntax_Tyapp
       (implode "bool") []))),s))`,
  CHEAT_TAC);;

(* [local] *)
let mk_const_eq = prove
 (`STATE defs s ==>
     (holKernel_mk_const ((implode "="),[]) s =
      (M_success (holSyntax_Const (implode "=") ((\s t. holSyntax_Tyapp
        (implode "fun") [s; t]) ((holSyntax_Tyvar (implode "A")):type)
        (ast_Fun ((holSyntax_Tyvar (implode "A")):type) (holSyntax_Tyapp
        (implode "bool") [])))),s))`,
  CHEAT_TAC);;

(* [local] *)
let mk_eq_lemma = prove
 (`holKernel_inst [term_type x,((holSyntax_Tyvar (implode "A")):type)]
  (holSyntax_Const (implode "=") ((\s t. holSyntax_Tyapp (implode "fun") [s;
  t]) ((holSyntax_Tyvar (implode "A")):type) (ast_Fun ((holSyntax_Tyvar
  (implode "A")):type) (holSyntax_Tyapp (implode "bool") [])))) s =
     st_ex_return
         (holSyntax_Const (implode "=")
            ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (term_type x)
              (ast_Fun (term_type x) (holSyntax_Tyapp (implode "bool") []))))
              s`,
  CHEAT_TAC);;

let safe_mk_eq_thm = prove
 (`(safe_mk_eq x y s = (res,s')) ==>
   (TERM defs x /\ TERM defs y /\ STATE defs s) ==>
   (typeof x = typeof y) ==>
   (s' = s) /\ (!t. (~(res = M_failure t))) /\
   (!t. (res = M_success t) ==>
        (t = holSyntax_Comb (holSyntax_Comb ((\ty. holSyntax_Const
          (implode "=") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty
          (ast_Fun ty (holSyntax_Tyapp (implode "bool") [])))) (term_type x))
          x) y) /\ TERM defs t)`,
  CHEAT_TAC);;

let mk_eq_thm = prove
 (`(mk_eq (x,y) s = (res,s')) ==>
   TERM defs x /\ TERM defs y /\ STATE defs s ==>
     (s' = s) /\
     (!t. (res = M_failure t) ==> (~((term_type x) = (term_type y)))) /\
     (!t. (res = M_success t) ==>
     (t = holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=") ((\s
       t. holSyntax_Tyapp (implode "fun") [s; t]) (term_type x)
                              (ast_Fun (term_type x) (holSyntax_Tyapp
                                (implode "bool") [])))) x) y) /\
     TERM defs t)`,
  CHEAT_TAC);;

(* [local] *)
let TERM_Eq_x = prove
 (`STATE defs s /\ TERM defs (holSyntax_Comb (holSyntax_Const (implode "=") ty)
  x) ==>
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (typeof x) (ast_Fun
       (typeof x) (holSyntax_Tyapp (implode "bool") [])) = ty)`,
  CHEAT_TAC);;

(* [local] *)
let TERM_Comb = prove
 (`CONTEXT defs ==>
     (TERM defs (holSyntax_Comb f a) <=>
      TERM defs f /\ TERM defs a /\
      (?ty. term_type f = (\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (term_type a) ty))`,
  CHEAT_TAC);;

(* [local] *)
let MAP_EQ_2_SYM = prove
 (`([x; y] = MAP f l) <=> (MAP f l = [x; y])`,
  CHEAT_TAC);;

(* Equal_type[local] *)
let equal_type = prove
 (`STATE defs s /\ TERM defs (holSyntax_Const (implode "=") ty) ==> (?a. ty =
  (\s t. holSyntax_Tyapp (implode "fun") [s; t]) a (ast_Fun a
  (holSyntax_Tyapp (implode "bool") [])))`,
  CHEAT_TAC);;

(* [local] *)
let Equal_type_IMP = prove
 (`STATE defs s /\ TERM defs (holSyntax_Comb (holSyntax_Const (implode "=")
  ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) a' (ast_Fun a'
  (holSyntax_Tyapp (implode "bool") [])))) ll) ==>
     (typeof ll = a')`,
  CHEAT_TAC);;

let dest_eq_thm = prove
 (`(dest_eq tm s = (res,s')) /\
   TERM defs tm /\
   STATE defs s ==>
     (s' = s) /\ (!t1 t2. (res = M_success (t1,t2)) ==> TERM defs t1 /\ TERM
       defs t2 /\
     (tm = holSyntax_Comb (holSyntax_Comb ((\ty. holSyntax_Const (implode
       "=") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty (ast_Fun ty
       (holSyntax_Tyapp (implode "bool") [])))) (typeof t1)) t1) t2))`,
  CHEAT_TAC);;

(* [local] *)
let VFREE_IN_IMP = prove
 (`!y. TERM defs y /\ TYPE defs ty /\ STATE defs s /\
         VFREE_IN (holSyntax_Var name ty) y ==>
         vfree_in (holSyntax_Var name ty) y`,
  CHEAT_TAC);;

(* [local] *)
let SELECT_LEMMA = prove
 (`(@f. !s s'. f (s',s) <=> ~(s = t)) = (\(z,y). ~(y = t))`,
  CHEAT_TAC);;

(* [local] *)
let SELECT_LEMMA2 = prove
 (`(@f.
        !s s''.
          f (s'',s) <=>
          VFREE_IN (holSyntax_Var s' ty) s'' /\ VFREE_IN s tm') =
     (\(x,y). VFREE_IN (holSyntax_Var s' ty) x /\ VFREE_IN y tm')`,
  CHEAT_TAC);;

(* [local] *)
let is_var_thm = prove
 (`!x. is_var x = (?v ty. x = holSyntax_Var v ty)`,
  CHEAT_TAC);;

(* [local] *)
let VSUBST_EMPTY = prove
 (`(!tm. VSUBST [] tm = tm)`,
  CHEAT_TAC);;

(* [local] *)
let VFREE_IN_TYPE = prove
 (`!x. VFREE_IN (holSyntax_Var name oty) x /\ TERM defs x ==>
         (?ty. (oty = ty) /\ TYPE defs ty)`,
  CHEAT_TAC);;

(* [local] *)
let VFREE_IN_IMP_MEM = prove
 (`VFREE_IN (holSyntax_Var name oty) h0 /\ TERM defs h0 /\ STATE defs s ==>
     (?ty1. MEM (holSyntax_Var name ty1) (frees h0) /\ (oty = ty1) /\ TYPE
       defs ty1)`,
  CHEAT_TAC);;

(* [local] *)
let term_type_Var = prove
 (`term_type (holSyntax_Var v ty) = ty`,
  CHEAT_TAC);;

(* [local] *)
let vsubst_aux_thm = prove
 (`!t tm theta. ALL (\(t1,t2). TERM defs t1 /\ TERM defs t2 /\
                      (term_type t1 = term_type t2) /\ is_var t2) theta /\
     TERM defs tm /\ STATE defs s /\
     (vsubst_aux theta tm = t) ==>
     TERM defs t /\
     (t = VSUBST theta tm)`,
  CHEAT_TAC);;

(* [local] *)
let forall_thm = prove
 (`!f s (xs:(holSyntax_term#holSyntax_term) list). (holKernel_forall f xs s =
  (res,s')) ==>
     (!x. ?r. f x s = (r,s)) ==>
     (s' = s) /\ ((res = M_success T) ==> ALL (\x. FST (f x s) = M_success
       T) xs)`,
  CHEAT_TAC);;

(* [local] *)
let assoc_state = prove
 (`!xs x. ?r. assoc x xs s = (r,s)`,
  CHEAT_TAC);;

(* [local] *)
let type_of_state = prove
 (`!tm. ?r. type_of tm s = (r,s)`,
  CHEAT_TAC);;

let variant_thm = prove
 (`!tms tm. ALL (TERM defs) tms /\ TERM defs tm /\ STATE defs s ==>
     TERM defs (variant tms tm)`,
  CHEAT_TAC);;

let vsubst_thm = prove
 (`ALL (\(t1,t2). TERM defs t1 /\ TERM defs t2) theta /\
    TERM defs tm /\ STATE defs s /\
    (vsubst theta tm s = (res,s')) ==>
    (s' = s) /\ (!t. (res = M_success t) ==> TERM defs t /\
    (t = VSUBST theta tm) /\
    (ALL (\(p_1,p_2). ?x ty. (p_2 = holSyntax_Var x ty) /\ has_type (p_1)
      ty) theta))`,
  CHEAT_TAC);;

let inst_aux_Var = prove
 (`inst_aux [] theta (holSyntax_Var v ty) state =
      (M_success (holSyntax_Var v (holKernel_type_subst theta ty)),state)`,
  CHEAT_TAC);;

(* MEM_subtract *)
let holKernelProof_MEM_subtract = prove
 (`!xs ys x. MEM x (subtract xs ys) <=> MEM x xs /\ ~(MEM x ys)`,
  CHEAT_TAC);;

let MEM_frees = prove
 (`!tm y. TERM defs tm /\ MEM y (frees tm) ==>
           (?v ty. (y = holSyntax_Var v ty) /\ TYPE defs ty)`,
  CHEAT_TAC);;

let MEM_freesl = prove
 (`!tms y. ALL (TERM defs) tms /\ MEM y (freesl tms) ==>
   (?v ty. (y = holSyntax_Var v ty) /\ TYPE defs ty)`,
  CHEAT_TAC);;

let inst_aux_thm = prove
 (`!env theta tm s s' res.
      ALL (\(t1,t2). TYPE defs t1 /\ TYPE defs t2) theta /\
      ALL (\(t1,t2). TERM defs t1 /\ TERM defs t2) env /\
      TERM defs tm /\ STATE defs s /\
      (inst_aux env theta tm s = (res,s')) ==>
      (s' = s) /\
      (match res with M_success t -> (INST_CORE env theta tm =
        holSyntaxLib_Result t)
      | M_failure (holKernel_Clash v) -> (INST_CORE env theta tm =
        holKernel_Clash v)
      | _ -> F)`,
  CHEAT_TAC);;

(* inst_lemma[local] *)
let holKernelProof_inst_lemma = prove
 (`ALL (\(t1,t2). TYPE defs t1 /\ TYPE defs t2) theta /\
     TERM defs tm /\ STATE defs s /\
     (holKernel_inst theta tm s = (res,s')) ==>
     (s' = s) /\ (!t. (res = M_success t) ==>
     (t = holSyntax_INST theta (tm)))`,
  CHEAT_TAC);;

let inst_thm = prove
 (`ALL (\(t1,t2). TYPE defs t1 /\ TYPE defs t2) theta /\
    TERM defs tm /\ STATE defs s /\
    (holKernel_inst theta tm s = (res,s')) ==>
    (s' = s) /\ (res = M_success (holSyntax_INST theta tm)) /\ TERM defs
      (holSyntax_INST theta tm)`,
  CHEAT_TAC);;

(* [local] *)
let freesin_IMP = prove
 (`!rhs vars'.
        freesin vars' rhs /\ TERM defs rhs /\ VFREE_IN (holSyntax_Var x ty)
          (rhs) ==>
        MEM (holSyntax_Var x ty) vars'`,
  CHEAT_TAC);;

(* [local] *)
let ALL_DISTINCT_union = prove
 (`!xs. ALL_DISTINCT (holSyntaxExtra_union xs ys) = ALL_DISTINCT ys`,
  CHEAT_TAC);;

(* [local] *)
let ALL_DISTINCT_tyvars_ALT = prove
 (`!h. ALL_DISTINCT (holSyntax_tyvars (h:type))`,
  CHEAT_TAC);;

(* [local] *)
let ALL_DISTINCT_type_vars_in_term = prove
 (`!P. ALL_DISTINCT (type_vars_in_term P)`,
  CHEAT_TAC);;

(* [local] *)
let MEM_type_vars_in_term = prove
 (`!rhs v. TERM defs rhs ==>
             (MEM v (type_vars_in_term rhs) = MEM v (tvars rhs))`,
  CHEAT_TAC);;

(* [local] *)
let sort_type_vars_in_term = prove
 (`TERM defs P ==>
     (sort (<=) (MAP explode (type_vars_in_term P)) = STRING_SORT (MAP
       explode (tvars P)))`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Verification of thm functions                                             *)
(* ------------------------------------------------------------------------- *)

let dest_thm_thm = prove
 (`THM defs th /\ STATE defs s /\ (dest_thm th = (asl,c)) ==>
    ALL (TERM defs) asl /\ TERM defs c`,
  CHEAT_TAC);;

let hyp_thm = prove
 (`THM defs th /\ STATE defs s /\ (hyp th = asl) ==>
    ALL (TERM defs) asl`,
  CHEAT_TAC);;

let concl_thm = prove
 (`THM defs th /\ STATE defs s /\ (concl th = c) ==>
    TERM defs c`,
  CHEAT_TAC);;

let REFL_thm = prove
 (`TERM defs tm /\ STATE defs s /\ (REFL tm s = (res,s')) ==>
    (s' = s) /\ (!th. (res = M_success th) ==> THM defs th)`,
  CHEAT_TAC);;

let TRANS_thm = prove
 (`THM defs th1 /\ THM defs th2 /\ STATE defs s /\
    (TRANS th1 th2 s = (res,s')) ==>
    (s' = s) /\ (!th. (res = M_success th) ==> THM defs th)`,
  CHEAT_TAC);;

let SYM_thm = prove
 (`(SYM th s = (res,s')) /\
   THM defs th /\
   STATE defs s ==>
     (s' = s) /\ (!th. (res = M_success th) ==> THM defs th)`,
  CHEAT_TAC);;

let PROVE_HYP_thm = prove
 (`THM defs th1 /\ THM defs th2 /\ STATE defs s /\
   (PROVE_HYP th1 th2 s = (res,s')) ==>
   (s' = s) /\ (!th. (res = M_success th) ==> THM defs th)`,
  CHEAT_TAC);;

(* [local] *)
let map_type_of = prove
 (`!ls s r s'.
       ALL (TERM defs) ls /\ STATE defs s /\
       (holKernel_map type_of ls s = (M_success r,s')) ==>
       (s' = s) /\
       (r = MAP term_type ls)`,
  CHEAT_TAC);;

(* [local] *)
let map_type_of_state = prove
 (`!ls s r s'.
       (holKernel_map type_of ls s = (r,s')) ==>
       (s' = s)`,
  CHEAT_TAC);;

let hypset_ok_list_to_hypset = prove
 (`!ls a. hypset_ok a ==> hypset_ok (list_to_hypset ls a)`,
  CHEAT_TAC);;
add_simp hypset_ok_list_to_hypset;;

let MEM_list_to_hypset_imp = prove
 (`!ls a. MEM x (list_to_hypset ls a) ==> MEM x ls \/ MEM x a`,
  CHEAT_TAC);;

let ALPHA_THM_thm = prove
 (`THM defs th /\ ALL (TERM defs) h /\ TERM defs c /\ STATE defs s /\
   (ALPHA_THM th (h,c) s = (res,s')) ==>
   (s' = s) /\ (!th. (res = M_success th) ==> THM defs th)`,
  CHEAT_TAC);;

let MK_COMB_thm = prove
 (`THM defs th1 /\ THM defs th2 /\ STATE defs s /\
    (MK_COMB (th1,th2) s = (res,s')) ==>
    (s' = s) /\ (!th. (res = M_success th) ==> THM defs th)`,
  CHEAT_TAC);;

(* [local] *)
let term_type_Const = prove
 (`term_type (holSyntax_Const n ty) = ty`,
  CHEAT_TAC);;

(* [local] *)
let term_type_Comb_Equal = prove
 (`term_type (holSyntax_Comb ((\ty. holSyntax_Const (implode "=") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) ty (ast_Fun ty (holSyntax_Tyapp
  (implode "bool") [])))) ty) ty') = (\s t. holSyntax_Tyapp (implode "fun")
  [s; t]) ty (holSyntax_Tyapp (implode "bool") [])`,
  CHEAT_TAC);;

let ABS_thm = prove
 (`(abs tm th1 s = (res,s')) /\
   TERM defs tm /\
   THM defs th1 /\
   STATE defs s ==>
     (s' = s) /\ (!th. (res = M_success th) ==> THM defs th)`,
  CHEAT_TAC);;

let BETA_thm = prove
 (`(BETA tm s = (res,s')) /\
   TERM defs tm /\
   STATE defs s ==>
     (s' = s) /\ (!th. (res = M_success th) ==> THM defs th)`,
  CHEAT_TAC);;

let ASSUME_thm = prove
 (`(ASSUME tm s = (res,s')) /\
   TERM defs tm /\
   STATE defs s ==>
     (s' = s) /\ (!th. (res = M_success th) ==> THM defs th)`,
  CHEAT_TAC);;

let EQ_MP_thm = prove
 (`THM defs th1 /\ THM defs th2 /\ STATE defs s /\
    (EQ_MP th1 th2 s = (res,s')) ==>
    (s' = s) /\ (!th. (res = M_success th) ==> THM defs th)`,
  CHEAT_TAC);;

let DEDUCT_ANTISYM_RULE_thm = prove
 (`THM defs th1 /\ THM defs th2 /\ STATE defs s /\
    (DEDUCT_ANTISYM_RULE th1 th2 s = (res,s')) ==>
    (s' = s) /\ (!th. (res = M_success th) ==> THM defs th)`,
  CHEAT_TAC);;

(* [local] *)
let image_lemma = prove
 (`!f l s g defs res s'.
       (image f l s = (res,s')) /\ STATE defs s ==>
       ALL (\x. !s. STATE defs s ==>
                      ((f x s = (M_success (g x),s)))) l ==>
       (s' = s) /\ (res = M_success (term_image g l))`,
  CHEAT_TAC);;

let INST_TYPE_thm = prove
 (`ALL (\(t1,t2). TYPE defs t1 /\ TYPE defs t2) theta /\
    THM defs th1 /\ STATE defs s /\
    (INST_TYPE theta th1 s = (res,s')) ==>
    (s' = s) /\ (?th. (res = M_success th) /\ THM defs th)`,
  CHEAT_TAC);;

(* image_lemma[local] *)
let holKernelProof_image_lemma = prove
 (`!f l s g defs res s'.
       (image f l s = (res,s')) /\ STATE defs s ==>
       ALL (\x. !s. STATE defs s ==>
                      (?r s'. ((f x s = (r,s))) /\
                             (!t. (r = M_success t) ==> (t = g x)))) l ==>
       (s' = s) /\ (!ts. (res = M_success ts) ==> (ts = term_image g l))`,
  CHEAT_TAC);;

let INST_thm = prove
 (`(holKernel_INST theta th1 s = (res,s')) /\
   ALL (\(t1,t2). TERM defs t1 /\ TERM defs t2) theta /\
   THM defs th1 /\ STATE defs s ==>
     (s' = s) /\ (!th. (res = M_success th) ==> THM defs th)`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Verification of definition functions                                      *)
(* ------------------------------------------------------------------------- *)

(* TODO move *)
let ALL_DISTINCT_DISJOINT = prove
 (`!xs ys. ALL_DISTINCT (APPEND xs ys) ==> DISJOINT (set_of_list xs)
  (set_of_list ys)`,
  CHEAT_TAC);;

let TYPE_CONS_EXTEND = prove
 (`STATE (CONS d defs) s /\ TYPE defs ty ==> TYPE (CONS d defs) ty`,
  CHEAT_TAC);;

let TYPE_APPEND_EXTEND = prove
 (`STATE (APPEND ds defs) s /\ TYPE defs ty ==> TYPE (APPEND ds defs) ty`,
  CHEAT_TAC);;

let TERM_CONS_EXTEND = prove
 (`STATE (CONS d defs) s /\ TERM defs tm ==> TERM (CONS d defs) tm`,
  CHEAT_TAC);;

let TERM_APPEND_EXTEND = prove
 (`STATE (APPEND ds defs) s /\ TERM defs tm ==> TERM (APPEND ds defs) tm`,
  CHEAT_TAC);;

let STRCAT_SHADOW_def = new_definition
  `STRCAT_SHADOW = APPEND`;;

(* [local] *)
let first_dup_thm = prove
 (`!ls acc. (first_dup ls acc = NONE) ==> ALL_DISTINCT ls /\ (!x. MEM x ls
  ==> ~(MEM x acc))`,
  CHEAT_TAC);;

(* [local] *)
let first_dup_SOME = prove
 (`!ls acc. (first_dup ls acc = SOME x) ==> ~(ALL_DISTINCT (APPEND ls acc))`,
  CHEAT_TAC);;

(* [local] *)
let add_constants_thm = prove
 (`!ls s res s'. (add_constants ls s = (res,s')) ==>
       (!u. (res = M_success u) /\ ALL_DISTINCT (MAP FST
         (hol_refs_the_term_constants s)) ==>
            ALL_DISTINCT (APPEND (MAP FST ls) (MAP FST
              (hol_refs_the_term_constants s))) /\
            (s' = hol_refs_the_term_constants_fupd (K (APPEND ls
              (hol_refs_the_term_constants s))) s)) /\
       (!msg. (res = M_failure msg) ==> (s' = s) /\ (~(ALL_DISTINCT
         (APPEND (MAP FST ls) (MAP FST (hol_refs_the_term_constants s))))))`,
  CHEAT_TAC);;

(* TODO move *)
let tyvars_EQ_thm = prove
 (`holKernel_tyvars = holSyntax_tyvars`,
  CHEAT_TAC);;

(* TODO move, unless it already exists elsewhere *)
let LIST_REL_MAP_EQ = prove
 (`!r l. ALL2 (\x y. x = f y) l r ==> (MAP f r = l)`,
  CHEAT_TAC);;

let new_specification_thm = prove
 (`THM defs th /\ STATE defs s ==>
    (match new_specification th s with (M_failure exn,s') -> (s' = s)
    | (M_success th,s') -> (?d. THM (CONS d defs) th /\
                              STATE (CONS d defs) s' /\
                              (!th. THM defs th ==> THM (CONS d defs)
                                th)))`,
  CHEAT_TAC);;

(* HOL4 holKernelProofScript.sml:2657: ML code, not ported *)

let new_basic_definition_thm = prove
 (`TERM defs tm /\ STATE defs s ==>
    (match new_basic_definition tm s with (M_failure exn,s') -> (s' = s)
    | (M_success th,s') -> (?d. THM (CONS d defs) th /\
                              STATE (CONS d defs) s' /\
                              (!th. THM defs th ==> THM (CONS d defs)
                                th)))`,
  CHEAT_TAC);;

let new_basic_type_definition_thm = prove
 (`THM defs th /\ STATE defs s ==>
    (match new_basic_type_definition (tyname,absname,repname,th) s with
      (M_failure exn,s') -> (s' = s)
    | (M_success (th1,th2),s') ->
      (?ds. THM (APPEND ds defs) th1 /\ THM (APPEND ds defs) th2 /\
            STATE (APPEND ds defs) s' /\
            (!th. THM defs th ==> THM (APPEND ds defs) th)))`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Verification of context extension functions                               *)
(* ------------------------------------------------------------------------- *)

let new_type_thm = prove
 (`STATE defs s ==>
    (match new_type (name,arity) s with (M_failure exn,s') -> (s' = s)
    | (M_success one,s') -> (?d. STATE (CONS d defs) s' /\
                              (!th. THM defs th ==> THM (CONS d defs)
                                th)))`,
  CHEAT_TAC);;

let new_constant_thm = prove
 (`STATE defs s /\ TYPE defs ty ==>
    (match new_constant (name,ty) s with (M_failure exn,s') -> (s' = s)
    | (M_success one,s') -> (?d. STATE (CONS d defs) s' /\
                           (!th. THM defs th ==> THM (CONS d defs) th)))`,
  CHEAT_TAC);;

let new_axiom_thm = prove
 (`STATE defs s /\ TERM defs p ==>
    (match new_axiom p s with (M_failure exn,s') -> (s' = s)
    | (M_success th,s') -> (?d. THM (CONS d defs) th /\ STATE (CONS d defs)
      s' /\
                              (!th. THM defs th ==> THM (CONS d defs)
                                th)))`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Removing clash exceptions                                                 *)
(* ------------------------------------------------------------------------- *)

(* Support theorems *)

let map_not_clash_thm = prove
 (`!f xs s.
   (!x s. ~(f x s = (M_failure (holKernel_Clash tm),refs))) ==>
     ~(holKernel_map f xs s = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;

let forall_clash_thm = prove
 (`!f l s.
    (!x s. ~(f x s = (M_failure (holKernel_Clash tm),refs))) ==>
      ~(holKernel_forall f l s = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;

let image_clash_thm = prove
 (`!f l s.
    (!x s. ~(f x s = (M_failure (holKernel_Clash tm),refs))) ==> ~(image f
      l s = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;

(* Function specific theorems *)

let dest_type_not_clash = prove
 (`~(dest_type x y = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp dest_type_not_clash;;

let type_of_not_clash = prove
 (`!x y. ~(type_of x y = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp type_of_not_clash;;

let mk_abs_not_clash = prove
 (`~(mk_abs x y = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp mk_abs_not_clash;;

let mk_comb_not_clash = prove
 (`~(mk_comb x y = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp mk_comb_not_clash;;

let mk_eq_not_clash = prove
 (`~(mk_eq x y = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp mk_eq_not_clash;;

let mk_type_not_clash = prove
 (`!a b. ~(mk_type a b = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp mk_type_not_clash;;

let safe_mk_eq_not_clash = prove
 (`~(safe_mk_eq x y s = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp safe_mk_eq_not_clash;;

let ABS_not_clash = prove
 (`~(abs x y z = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp ABS_not_clash;;

let MK_COMB_not_clash = prove
 (`~(MK_COMB (a,b) c = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp MK_COMB_not_clash;;

let ASSUME_not_clash = prove
 (`!a b. ~(ASSUME a b = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp ASSUME_not_clash;;

let BETA_not_clash = prove
 (`~(BETA a b = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp BETA_not_clash;;

let mk_const_not_clash = prove
 (`~(holKernel_mk_const (a,b) c = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp mk_const_not_clash;;

let assoc_not_clash = prove
 (`!a b c. ~(assoc a b c = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp assoc_not_clash;;

let get_const_type_not_clash = prove
 (`~(get_const_type a b = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp get_const_type_not_clash;;

let DEDUCT_ANTISYM_RULE_not_clash = prove
 (`~(DEDUCT_ANTISYM_RULE a b c = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp DEDUCT_ANTISYM_RULE_not_clash;;

let SYM_not_clash = prove
 (`~(SYM a b = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp SYM_not_clash;;

let dest_comb_not_clash = prove
 (`~(dest_comb a b = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp dest_comb_not_clash;;

let dest_eq_not_clash = prove
 (`~(dest_eq a b = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp dest_eq_not_clash;;

let EQ_MP_not_clash = prove
 (`~(EQ_MP a b c = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp EQ_MP_not_clash;;

let PROVE_HYP_not_clash = prove
 (`~(PROVE_HYP a b c = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp PROVE_HYP_not_clash;;

let REFL_not_clash = prove
 (`~(REFL a b = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp REFL_not_clash;;

let TRANS_not_clash = prove
 (`~(TRANS a b c = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp TRANS_not_clash;;

let ALPHA_THM_not_clash = prove
 (`!a b c d. ~(ALPHA_THM a (b,c) d = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp ALPHA_THM_not_clash;;

let add_constants_not_clash = prove
 (`~(add_constants a b = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp add_constants_not_clash;;

let add_def_not_clash = prove
 (`~(add_def a b = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp add_def_not_clash;;

let dest_var_not_clash = prove
 (`~(holKernel_dest_var a b = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp dest_var_not_clash;;

let new_specification_not_clash = prove
 (`~(new_specification a b = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp new_specification_not_clash;;

let new_basic_definition_not_clash = prove
 (`~(new_basic_definition a b = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp new_basic_definition_not_clash;;

let add_type_not_clash = prove
 (`~(add_type (a,b) c = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp add_type_not_clash;;

let new_basic_type_definition_not_clash = prove
 (`~(new_basic_type_definition (a,b,c,d) e = (M_failure (holKernel_Clash
  tm),refs))`,
  CHEAT_TAC);;
add_simp new_basic_type_definition_not_clash;;

let vsubst_not_clash = prove
 (`~(vsubst x y s = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp vsubst_not_clash;;

let INST_not_clash = prove
 (`~(holKernel_INST theta x s = (M_failure (holKernel_Clash tm),refs))`,
  CHEAT_TAC);;
add_simp INST_not_clash;;

let new_axiom_not_clash = prove
 (`~(new_axiom ax s = (M_failure (holKernel_Clash tm),t))`,
  CHEAT_TAC);;
add_simp new_axiom_not_clash;;

let new_constant_not_clash = prove
 (`~(new_constant (a,b) s = (M_failure (holKernel_Clash tm),t))`,
  CHEAT_TAC);;
add_simp new_constant_not_clash;;

let new_type_not_clash = prove
 (`~(new_type (a,b) s = (M_failure (holKernel_Clash tm),t))`,
  CHEAT_TAC);;
add_simp new_type_not_clash;;

let dest_abs_not_clash = prove
 (`~(dest_abs x s = (M_failure (holKernel_Clash tm),t))`,
  CHEAT_TAC);;
add_simp dest_abs_not_clash;;


(* TODO Prove for inst_aux *)

(* HOL4 holKernelProofScript.sml:3381-3564: code that the source has in a
   comment *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["Bool";
   "const_list"];;

(* and the interface *)
let _ = unhide_overloads ();;
