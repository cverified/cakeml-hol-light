(* ======================================================== *)
(*  holSyntaxExtra: ported from HOL4's
    candle/standard/syntax/holSyntaxExtraScript.sml
    A definition theory, with 24 definitions, 1 datatype and 239
    theorems.  Needed by 24 files of the port.  *)
(* ======================================================== *)

(*
  Some lemmas about the syntactic functions.
*)

needs "basis/pure/mlstring.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "lib/comparison.ml";;
needs "lib/ternaryComparisons.ml";;
needs "lib/toto.ml";;
needs "misc/misc.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "holSyntaxExtra"
  ["holSyntax"; "holSyntaxLib"; "mlstring"];;

let _ = do_list hide_constant ["Bool"; "Equal"; "Fun"; "concl"; "const_list";
       "subterm"];;

(* HOL4 holSyntaxExtraScript.sml:16-17: ML code, not ported *)

(* HOL4 holSyntaxExtraScript.sml:19-26: a theorem that HOL4 states as the
   value of an ML expression: type_ind *)

(* HOL4 holSyntaxExtraScript.sml:28-32: a theorem whose statement the port
   cannot state yet: type1_size_append *)

let extends_ind = prove
 (`!P. (!upd ctxt. updates upd ctxt /\ P ctxt ==> P (CONS upd ctxt)) ==>
    (!ctxt1 ctxt2. extends ctxt2 ctxt1 ==> P ctxt1 ==> P ctxt2)`,
  CHEAT_TAC);;

(* deconstructing variables *)

let ALOOKUP_MAP_dest_var = prove
 (`!ls f x ty.
      ALL (\s. ?x ty. s = holSyntax_Var x ty) (MAP FST ls) ==>
      ALOOKUP (MAP (holSyntax_dest_var ## f) ls) (x,ty) =
      OPTION_MAP f (ALOOKUP ls (holSyntax_Var x ty))`,
  CHEAT_TAC);;

(* type substitution *)

let TYPE_SUBST_NIL = prove
 (`!ty. TYPE_SUBST [] ty = ty`,
  CHEAT_TAC);;
add_simp TYPE_SUBST_NIL;;

let TYPE_SUBST_Bool = prove
 (`!tyin. TYPE_SUBST tyin (holSyntax_Tyapp (implode "bool") []) =
  (holSyntax_Tyapp (implode "bool") [])`,
  CHEAT_TAC);;

let is_instance_refl = prove
 (`!ty. (\ty0 ty. ?i. ty = TYPE_SUBST i ty0) ty ty`,
  CHEAT_TAC);;
add_simp is_instance_refl;;

let swap_ff = prove
 (`!f g. (\(x,y). (y,x)) o (f ## g) = (g ## f) o (\(x,y). (y,x))`,
  CHEAT_TAC);;

let ff_def = prove
 (`!f g. (f ## g) = (\(x,y). (f x,g y))`,
  CHEAT_TAC);;

let TYPE_SUBST_compose = prove
 (`!tyin1 ty tyin2.
    TYPE_SUBST tyin2 (TYPE_SUBST tyin1 ty) =
    TYPE_SUBST (APPEND (MAP (TYPE_SUBST tyin2 ## I) tyin1) tyin2) ty`,
  CHEAT_TAC);;

let TYPE_SUBST_tyvars = prove
 (`!ty tyin tyin'.
    (TYPE_SUBST tyin ty = TYPE_SUBST tyin' ty) <=>
    (!x. MEM x (holSyntax_tyvars ty) ==>
        REV_ASSOCD (holSyntax_Tyvar x) tyin' (holSyntax_Tyvar x) =
        REV_ASSOCD (holSyntax_Tyvar x) tyin (holSyntax_Tyvar x))`,
  CHEAT_TAC);;

(* Welltyped terms *)

let WELLTYPED_LEMMA = prove
 (`!tm ty. has_type tm ty ==> (typeof tm = ty)`,
  CHEAT_TAC);;

let WELLTYPED = prove
 (`!tm. welltyped tm <=> has_type tm (typeof tm)`,
  CHEAT_TAC);;

let WELLTYPED_CLAUSES = prove
 (`(!n ty. welltyped (holSyntax_Var n ty)) /\
    (!n ty. welltyped (holSyntax_Const n ty)) /\
    (!s t. welltyped (holSyntax_Comb s t) <=>
             welltyped s /\ welltyped t /\
             (?rty. typeof s = (\s t. holSyntax_Tyapp (implode "fun") [s;
               t]) (typeof t) rty)) /\
    (!v t. welltyped (holSyntax_Abs v t) = (?n ty. v = holSyntax_Var n ty
      /\ welltyped t))`,
  CHEAT_TAC);;
add_simp WELLTYPED_CLAUSES;;

(* Alpha-equivalence *)

(* RACONV *)
let holSyntaxExtra_RACONV = prove
 (`(RACONV env (holSyntax_Var x1 ty1,holSyntax_Var x2 ty2) <=>
         ALPHAVARS env ((holSyntax_Var x1 ty1:holSyntax_term),(holSyntax_Var
           x2 ty2:holSyntax_term))) /\
    (RACONV env (holSyntax_Var x1 ty1,holSyntax_Const x2 ty2) <=> F) /\
    (RACONV env (holSyntax_Var x1 ty1,holSyntax_Comb l2 r2) <=> F) /\
    (RACONV env (holSyntax_Var x1 ty1,holSyntax_Abs v2 t2) <=> F) /\
    (RACONV env (holSyntax_Const x1 ty1,holSyntax_Var x2 ty2) <=> F) /\
    (RACONV env (holSyntax_Const x1 ty1,holSyntax_Const x2 ty2) <=> (x1 =
      x2) /\ (ty1 = ty2)) /\
    (RACONV env (holSyntax_Const x1 ty1,holSyntax_Comb l2 r2) <=> F) /\
    (RACONV env (holSyntax_Const x1 ty1,holSyntax_Abs v2 t2) <=> F) /\
    (RACONV env (holSyntax_Comb l1 r1,holSyntax_Var x2 ty2) <=> F) /\
    (RACONV env (holSyntax_Comb l1 r1,holSyntax_Const x2 ty2) <=> F) /\
    (RACONV env (holSyntax_Comb l1 r1,holSyntax_Comb l2 r2) <=>
         RACONV env (l1,l2) /\ RACONV env (r1,r2)) /\
    (RACONV env (holSyntax_Comb l1 r1,holSyntax_Abs v2 t2) <=> F) /\
    (RACONV env (holSyntax_Abs v1 t1,holSyntax_Var x2 ty2) <=> F) /\
    (RACONV env (holSyntax_Abs v1 t1,holSyntax_Const x2 ty2) <=> F) /\
    (RACONV env (holSyntax_Abs v1 t1,holSyntax_Comb l2 r2) <=> F) /\
    (RACONV env (holSyntax_Abs v1 t1,holSyntax_Abs v2 t2) <=>
           typeof v1 = typeof v2 /\
           RACONV (CONS (v1,v2) env) (t1,t2))`,
  CHEAT_TAC);;

let RACONV_REFL = prove
 (`!t env. ALL (UNCURRY (=)) env ==> RACONV env (t,t)`,
  CHEAT_TAC);;

let ACONV_REFL = prove
 (`!t. ACONV t t`,
  CHEAT_TAC);;
add_simp ACONV_REFL;;

let RACONV_TRANS = prove
 (`!env tp. RACONV env tp ==> (!vs t. LENGTH vs = LENGTH env /\ RACONV (ZIP
  (MAP SND env) vs) (SND tp,t) ==> RACONV (ZIP (MAP FST env) vs) (FST tp,t))`,
  CHEAT_TAC);;

let ACONV_TRANS = prove
 (`!t1 t2 t3. ACONV t1 t2 /\ ACONV t2 t3 ==> ACONV t1 t3`,
  CHEAT_TAC);;

let RACONV_SYM = prove
 (`!env tp. RACONV env tp ==> RACONV (MAP (\(x,y). (y,x)) env) (SND tp,FST
  tp)`,
  CHEAT_TAC);;

let ACONV_SYM = prove
 (`!t1 t2. ACONV t1 t2 ==> ACONV t2 t1`,
  CHEAT_TAC);;

let ALPHAVARS_TYPE = prove
 (`!env s t.
              ALPHAVARS env (s,t) /\
              ALL (\(x,y). welltyped x /\
                             welltyped y /\ (typeof x = typeof y)) env /\
              welltyped s /\ welltyped t ==> typeof s = typeof t`,
  CHEAT_TAC);;

let RACONV_TYPE = prove
 (`!env p.
            RACONV env p ==>
              ALL (\(x,y). welltyped x /\
                             welltyped y /\ (typeof x = typeof y)) env /\
              welltyped (FST p) /\ welltyped (SND p) ==> typeof (FST p) =
                typeof (SND p)`,
  CHEAT_TAC);;

let ACONV_TYPE = prove
 (`!s t. ACONV s t ==> welltyped s /\ welltyped t ==> (typeof s = typeof t)`,
  CHEAT_TAC);;

(* subtypes *)

let subtype1 = cake_inductive
  `MEM a args ==> subtype1 a (holSyntax_Tyapp name args)`;;
(* HOL4 holSyntaxExtraScript.sml:265: the overload subtype, which the port
   expands *)

(* HOL4 holSyntaxExtraScript.sml:267-270: a theorem that HOL4 states as the
   value of an ML expression: subtype_Tyvar *)

(* HOL4 holSyntaxExtraScript.sml:272-275: a theorem that HOL4 states as the
   value of an ML expression: subtype_Tyapp *)

let subtype_type_ok = prove
 (`!tysig ty1 ty2. type_ok tysig ty2 /\ RTC subtype1 ty1 ty2 ==> type_ok
  tysig ty1`,
  CHEAT_TAC);;

(* subterms *)

let subterm1 = cake_inductive
  `subterm1 t1 (holSyntax_Comb t1 t2) /\
   subterm1 t2 (holSyntax_Comb t1 t2) /\
   subterm1 tm (holSyntax_Abs v tm) /\
   subterm1 v (holSyntax_Abs v tm)`;;
(* HOL4 holSyntaxExtraScript.sml:303: the overload subterm, which the port
   expands *)
(* HOL4 holSyntaxExtraScript.sml:304-307: a theorem that HOL4 states as the
   value of an ML expression: subterm_Var *)
(* HOL4 holSyntaxExtraScript.sml:308-311: a theorem that HOL4 states as the
   value of an ML expression: subterm_Const *)

(* HOL4 holSyntaxExtraScript.sml:313-316: a theorem that HOL4 states as the
   value of an ML expression: subterm_Comb *)
(* HOL4 holSyntaxExtraScript.sml:317-320: a theorem that HOL4 states as the
   value of an ML expression: subterm_Abs *)

(* [local] *)
let subterm_welltyped_helper = prove
 (`!tm ty. has_type tm ty ==> (!t. RTC subterm1 t tm ==> welltyped t)`,
  CHEAT_TAC);;

let subterm_welltyped = prove
 (`!t tm. welltyped tm /\ RTC subterm1 t tm ==> welltyped t`,
  CHEAT_TAC);;

(* term ordering *)

(* HOL4 holSyntaxExtraScript.sml:336-344: a theorem that HOL4 states as the
   value of an ML expression: type_lt_thm *)

(* HOL4 holSyntaxExtraScript.sml:346-368: a theorem that HOL4 states as the
   value of an ML expression: term_lt_thm *)

let type_cmp_refl = prove
 (`type_cmp t t = EQUAL`,
  CHEAT_TAC);;
add_simp type_cmp_refl;;

let term_cmp_refl = prove
 (`term_cmp t t = EQUAL`,
  CHEAT_TAC);;
add_simp term_cmp_refl;;

(* [local] *)
let irreflexive_type_lt = prove
 (`irreflexive type_lt`,
  CHEAT_TAC);;

(* [local] *)
let trichotomous_type_lt = prove
 (`trichotomous type_lt`,
  CHEAT_TAC);;

(* [local] *)
let transitive_type_lt = prove
 (`!x y. type_lt x y ==> (!z. type_lt y z ==> type_lt x z)`,
  CHEAT_TAC);;

let StrongLinearOrder_type_lt = prove
 (`StrongLinearOrder type_lt`,
  CHEAT_TAC);;

let TotOrd_type_cmp = prove
 (`TotOrd type_cmp`,
  CHEAT_TAC);;

(* [local] *)
let irreflexive_term_lt = prove
 (`irreflexive term_lt`,
  CHEAT_TAC);;

(* [local] *)
let trichotomous_term_lt = prove
 (`trichotomous term_lt`,
  CHEAT_TAC);;

(* [local] *)
let transitive_term_lt = prove
 (`!x y. term_lt x y ==> (!z. term_lt y z ==> term_lt x z)`,
  CHEAT_TAC);;

let StrongLinearOrder_term_lt = prove
 (`StrongLinearOrder term_lt`,
  CHEAT_TAC);;

let TotOrd_term_cmp = prove
 (`TotOrd term_cmp`,
  CHEAT_TAC);;

(* [local] *)
let StrongLinearOrder_irreflexive = prove
 (`StrongLinearOrder R ==> irreflexive R`,
  CHEAT_TAC);;

(* [local] *)
let holSyntaxExtra_irreflexive_mlstring_lt =
  MATCH_MP StrongLinearOrder_irreflexive StrongLinearOrder_mlstring_lt;;

(* [local] *)
let LLEX_irreflexive = prove
 (`!R. irreflexive R ==> irreflexive (LLEX R)`,
  CHEAT_TAC);;

(* [local] *)
let irreflexive_LLEX_type_lt = MATCH_MP LLEX_irreflexive irreflexive_type_lt;;

let type_cmp_thm = prove
 (`!t1 t2. type_cmp t1 t2 =
    match (t1,t2) with (holSyntax_Tyvar x1,holSyntax_Tyvar x2) ->
      mlstring_compare x1 x2
    | (holSyntax_Tyvar _,_) -> LESS
    | (_,holSyntax_Tyvar _) -> GREATER
    | (holSyntax_Tyapp x1 a1,holSyntax_Tyapp x2 a2) ->
      ternaryComparisons_pair_compare mlstring_compare (list_compare
      type_cmp) (x1,a1) (x2,a2)`,
  CHEAT_TAC);;

let type_cmp_ind = prove
 (`!P.
      (!t1 t2.
        (!x1 a1 x2 a2 x y.
          t1 = holSyntax_Tyapp x1 a1 /\
          t2 = holSyntax_Tyapp x2 a2 /\
          MEM x a1 /\ MEM y a2 ==>
          P x y) ==> P t1 t2) ==> (!t1 t2. P t1 t2)`,
  CHEAT_TAC);;

let term_cmp_thm = prove
 (`!t1 t2. term_cmp t1 t2 =
    match (t1,t2) with (holSyntax_Var x1 ty1,holSyntax_Var x2 ty2) ->
      ternaryComparisons_pair_compare mlstring_compare type_cmp (x1,ty1)
      (x2,ty2)
    | (holSyntax_Var _ _,_) -> LESS
    | (_,holSyntax_Var _ _) -> GREATER
    | (holSyntax_Const x1 ty1,holSyntax_Const x2 ty2) ->
      ternaryComparisons_pair_compare mlstring_compare type_cmp (x1,ty1)
      (x2,ty2)
    | (holSyntax_Const _ _,_) -> LESS
    | (_,holSyntax_Const _ _) -> GREATER
    | (holSyntax_Comb s1 t1,holSyntax_Comb s2 t2) ->
      ternaryComparisons_pair_compare term_cmp term_cmp (s1,t1) (s2,t2)
    | (holSyntax_Comb _ _,_) -> LESS
    | (_,holSyntax_Comb _ _) -> GREATER
    | (holSyntax_Abs s1 t1,holSyntax_Abs s2 t2) ->
      ternaryComparisons_pair_compare term_cmp term_cmp (s1,t1) (s2,t2)
    | (holSyntax_Abs _ _,_) -> LESS
    | (_,holSyntax_Abs _ _) -> GREATER`,
  CHEAT_TAC);;

let term_cmp_ind = prove
 (`!P.
      (!t1 t2.
        (!x1 y1 x2 y2.
          t1 = holSyntax_Comb x1 y1 /\ t2 = holSyntax_Comb x2 y2 ==>
            P x1 x2) /\
        (!x1 y1 x2 y2.
          t1 = holSyntax_Comb x1 y1 /\ t2 = holSyntax_Comb x2 y2 ==>
            P y1 y2) /\
        (!x1 y1 x2 y2.
          t1 = holSyntax_Abs x1 y1 /\ t2 = holSyntax_Abs x2 y2 ==>
            P x1 x2) /\
        (!x1 y1 x2 y2.
          t1 = holSyntax_Abs x1 y1 /\ t2 = holSyntax_Abs x2 y2 ==>
            P y1 y2) ==> P t1 t2) ==> (!t1 t2. P t1 t2)`,
  CHEAT_TAC);;

(* alpha ordering *)

(* [local] *)
let ALPHAVARS_ordav = prove
 (`!env tp. ALPHAVARS env tp ==> ordav env (FST tp) (SND tp) = EQUAL`,
  CHEAT_TAC);;

(* [local] *)
let ordav_ALPHAVARS = prove
 (`!env t1 t2. ordav env t1 t2 = EQUAL ==> ALPHAVARS env (t1,t2)`,
  CHEAT_TAC);;

let ALPHAVARS_eq_ordav = prove
 (`!env t1 t2. ALPHAVARS env (t1,t2) <=> ordav env t1 t2 = EQUAL`,
  CHEAT_TAC);;

(* [local] *)
let RACONV_orda = prove
 (`!env tp. RACONV env tp ==> orda env (FST tp) (SND tp) = EQUAL`,
  CHEAT_TAC);;

(* [local] *)
let orda_RACONV = prove
 (`!env t1 t2. orda env t1 t2 = EQUAL ==> RACONV env (t1,t2)`,
  CHEAT_TAC);;

let RACONV_eq_orda = prove
 (`!env t1 t2. RACONV env (t1,t2) <=> orda env t1 t2 = EQUAL`,
  CHEAT_TAC);;

let ACONV_eq_orda = prove
 (`!t1 t2. ACONV t1 t2 = (orda [] t1 t2 = EQUAL)`,
  CHEAT_TAC);;

let ordav_FILTER = prove
 (`!env x y. ordav env x y =
      match FILTER (\(x',y'). x' = x \/ y' = y) env with [] -> term_cmp x y
      | (CONS (x',y') _) -> if x' = x then if y' = y then EQUAL else LESS
        else GREATER`,
  CHEAT_TAC);;

let ordav_sym = prove
 (`!env v1 v2. invert_comparison (ordav env v1 v2) = ordav (MAP (\(x,y).
  (y,x)) env) v2 v1`,
  CHEAT_TAC);;

let orda_sym = prove
 (`!env t1 t2. invert_comparison (orda env t1 t2) = orda (MAP (\(x,y). (y,x))
  env) t2 t1`,
  CHEAT_TAC);;

let antisymmetric_alpha_lt = prove
 (`antisymmetric alpha_lt`,
  CHEAT_TAC);;

(* HOL4 holSyntaxExtraScript.sml:802-810: a theorem whose statement the port
   cannot state yet: orda_thm *)

(* [local] *)
let ordav_lx_trans = prove
 (`!t1 t2 t3 env1 env2.
     ~(ordav env1 t1 t2 = GREATER) /\ ~(ordav env2 t2 t3 = GREATER) /\
     MAP SND env1 = MAP FST env2 ==> ~(ordav (ZIP (MAP FST env1) (MAP SND
       env2)) t1 t3 = GREATER) /\
       (ordav env1 t1 t2 = LESS \/ ordav env2 t2 t3 = LESS ==>
        ordav (ZIP (MAP FST env1) (MAP SND env2)) t1 t3 = LESS)`,
  CHEAT_TAC);;

(* [local] *)
let undo_zip_map_fst = prove
 (`CONS p (ZIP (MAP FST l1) (MAP SND l2)) =
       ZIP (MAP FST (CONS (FST p,v2) l1)) (MAP SND (CONS (v2,SND p) l2))`,
  CHEAT_TAC);;

(* [local] *)
let orda_lx_trans = prove
 (`!env1 t1 t2 env2 t3.
     ~(orda env1 t1 t2 = GREATER) /\ ~(orda env2 t2 t3 = GREATER) /\
     MAP SND env1 = MAP FST env2 ==> ~(orda (ZIP (MAP FST env1) (MAP SND
       env2)) t1 t3 = GREATER) /\
       (orda env1 t1 t2 = LESS \/ orda env2 t2 t3 = LESS ==>
        orda (ZIP (MAP FST env1) (MAP SND env2)) t1 t3 = LESS)`,
  CHEAT_TAC);;

let transitive_alpha_lt = prove
 (`transitive alpha_lt`,
  CHEAT_TAC);;

let alpha_lt_trans_ACONV = prove
 (`!x y z.
    (ACONV x y /\ alpha_lt y z ==> alpha_lt x z) /\
    (alpha_lt x y /\ ACONV y z ==> alpha_lt x z)`,
  CHEAT_TAC);;

let alpha_lt_not_refl = prove
 (`!x. ~(alpha_lt x x)`,
  CHEAT_TAC);;
add_simp alpha_lt_not_refl;;

(* VFREE_IN lemmas *)

let VFREE_IN_RACONV = prove
 (`!env p.
            RACONV env p ==> (!x ty. VFREE_IN (holSyntax_Var x ty) (FST p)
              /\
                     ~(?y. MEM (holSyntax_Var x ty,y) env) <=>
                     VFREE_IN (holSyntax_Var x ty) (SND p) /\
                     ~(?y. MEM (y,holSyntax_Var x ty) env))`,
  CHEAT_TAC);;

let VFREE_IN_ACONV = prove
 (`!s t x ty. ACONV s t ==> (VFREE_IN (holSyntax_Var x ty) s <=> VFREE_IN
  (holSyntax_Var x ty) t)`,
  CHEAT_TAC);;

let VFREE_IN_subterm = prove
 (`!t1 t2. VFREE_IN t1 t2 ==> RTC subterm1 t1 t2`,
  CHEAT_TAC);;

(* hypset_ok *)

let hypset_ok_nil = prove
 (`hypset_ok []`,
  CHEAT_TAC);;
add_simp hypset_ok_nil;;

let hypset_ok_sing = prove
 (`!p. hypset_ok [p]`,
  CHEAT_TAC);;
add_simp hypset_ok_sing;;

let hypset_ok_cons = prove
 (`hypset_ok (CONS h hs) <=>
    ALL (alpha_lt h) hs /\ hypset_ok hs`,
  CHEAT_TAC);;

let hypset_ok_ALL_DISTINCT = prove
 (`!h. hypset_ok h ==> ALL_DISTINCT h`,
  CHEAT_TAC);;

let hypset_ok_eq = prove
 (`!h1 h2. hypset_ok h1 /\ hypset_ok h2 ==>
            ((h1 = h2) <=> (set_of_list h1 = set_of_list h2))`,
  CHEAT_TAC);;

(* HOL4 holSyntaxExtraScript.sml:1035-1037: a theorem that HOL4 states as
   the value of an ML expression: hypset_ok_append *)

(* HOL4 holSyntaxExtraScript.sml:1039-1041: a theorem that HOL4 states as
   the value of an ML expression: hypset_ok_el_less *)

(* term_union lemmas *)

let term_union_idem = prove
 (`!ls. term_union ls ls = ls`,
  CHEAT_TAC);;
add_simp term_union_idem;;

let term_union_thm = prove
 (`(!l2. term_union [] l2 = l2) /\
    (!l1. term_union l1 [] = l1) /\
    (!h1 t1 h2 t2.
          term_union (CONS h1 t1) (CONS h2 t2) =
          (match orda [] h1 h2 with EQUAL -> CONS h1 (term_union t1 t2)
          | LESS -> CONS h1 (term_union t1 (CONS h2 t2))
          | GREATER -> CONS h2 (term_union (CONS h1 t1) t2)))`,
  CHEAT_TAC);;

let MEM_term_union_imp = prove
 (`!l1 l2 x. MEM x (term_union l1 l2) ==> MEM x l1 \/ MEM x l2`,
  CHEAT_TAC);;

let hypset_ok_term_union = prove
 (`!l1 l2. hypset_ok l1 /\ hypset_ok l2 ==>
            hypset_ok (term_union l1 l2)`,
  CHEAT_TAC);;
add_simp hypset_ok_term_union;;

let EVERY_term_union = prove
 (`ALL P l1 /\ ALL P l2 ==> ALL P (term_union l1 l2)`,
  CHEAT_TAC);;

let MEM_term_union = prove
 (`!h1 h2 t. hypset_ok h1 /\ hypset_ok h2 /\ (MEM t h1 \/ MEM t h2) ==>
      (?y. MEM y (term_union h1 h2) /\ ACONV t y)`,
  CHEAT_TAC);;

(* [local] *)
let term_union_sing_lt = prove
 (`!ys x. ALL (\y. alpha_lt x y) ys ==> (term_union [x] ys = CONS x ys)`,
  CHEAT_TAC);;

let term_union_insert = prove
 (`!ys x zs.
    ALL (\y. alpha_lt y x) ys /\
    ALL (\z. alpha_lt x z) zs ==> (term_union [x] (APPEND ys zs) = APPEND
      ys (CONS x zs))`,
  CHEAT_TAC);;

let term_union_replace = prove
 (`!ys x x' zs.
    ALL (\y. alpha_lt y x) ys /\ ACONV x x' /\
    ALL (\z. alpha_lt x z) zs ==>
    term_union [x] (APPEND ys (CONS x' zs)) = APPEND ys (CONS x zs)`,
  CHEAT_TAC);;

let MEM_term_union_first = prove
 (`!h1 h2 t. hypset_ok h1 /\ hypset_ok h2 /\ MEM t h1 ==> MEM t (term_union
  h1 h2)`,
  CHEAT_TAC);;

let term_union_insert_mem = prove
 (`!c h. hypset_ok h /\ MEM c h ==> (term_union [c] h = h)`,
  CHEAT_TAC);;

let term_union_insert_remove = prove
 (`!c h. hypset_ok h /\ MEM c h /\ ACONV c' c ==> (term_union [c]
  (term_remove c' h) = h)`,
  CHEAT_TAC);;

(* term_remove *)

let term_remove_nil = prove
 (`!a. term_remove a [] = []`,
  CHEAT_TAC);;
add_simp term_remove_nil;;

let MEM_term_remove_imp = prove
 (`!ls x t. MEM t (term_remove x ls) ==>
      MEM t ls /\ (hypset_ok ls ==> ~(ACONV x t))`,
  CHEAT_TAC);;

let hypset_ok_term_remove = prove
 (`!ls. hypset_ok ls ==> (!t. hypset_ok (term_remove t ls))`,
  CHEAT_TAC);;
add_simp hypset_ok_term_remove;;

let EVERY_term_remove = prove
 (`ALL P ls ==> ALL P (term_remove t ls)`,
  CHEAT_TAC);;

let MEM_term_remove = prove
 (`!h x t.
    MEM t h /\ ~(ACONV x t) /\ hypset_ok h ==> MEM t (term_remove x h)`,
  CHEAT_TAC);;

let term_remove_exists = prove
 (`!c h. ~(term_remove c h = h) ==> (?c'. MEM c' h /\ ACONV c c')`,
  CHEAT_TAC);;

(* term_image *)

let term_image_nil = prove
 (`term_image f [] = []`,
  CHEAT_TAC);;
add_simp term_image_nil;;

let MEM_term_image_imp = prove
 (`!ls f t. MEM t (term_image f ls) ==> (?x. MEM x ls /\ t = f x)`,
  CHEAT_TAC);;

let hypset_ok_term_image = prove
 (`!ls f. hypset_ok ls ==> hypset_ok (term_image f ls)`,
  CHEAT_TAC);;

let MEM_term_image = prove
 (`!ls f t. MEM t ls /\ hypset_ok ls ==> (?y. MEM y (term_image f ls)
  /\ ACONV (f t) y)`,
  CHEAT_TAC);;

(* VSUBST lemmas *)

let VSUBST_HAS_TYPE = prove
 (`!tm ty ilist.
      has_type tm ty /\
      (!s s'. MEM (s',s) ilist ==> (?x ty. (s = holSyntax_Var x ty)
        /\ has_type s' ty)) ==> has_type (VSUBST ilist tm) ty`,
  CHEAT_TAC);;

let VSUBST_WELLTYPED = prove
 (`!tm ty ilist.
      welltyped tm /\
      (!s s'. MEM (s',s) ilist ==> (?x ty. (s = holSyntax_Var x ty)
        /\ has_type s' ty)) ==> welltyped (VSUBST ilist tm)`,
  CHEAT_TAC);;

let VFREE_IN_VSUBST = prove
 (`!tm u uty ilist.
      welltyped tm ==>
      (VFREE_IN (holSyntax_Var u uty) (VSUBST ilist tm) <=>
       (?y ty. VFREE_IN (holSyntax_Var y ty) tm /\
              VFREE_IN (holSyntax_Var u uty) (REV_ASSOCD (holSyntax_Var y
                ty) ilist (holSyntax_Var y ty))))`,
  CHEAT_TAC);;

let VSUBST_NIL = prove
 (`!tm. VSUBST [] tm = tm`,
  CHEAT_TAC);;
add_simp VSUBST_NIL;;

(* INST lemmas *)

let INST_CORE_HAS_TYPE = prove
 (`!n tm env tyin.
      welltyped tm /\ (sizeof tm = n) /\
      (!s s'. MEM (s,s') env ==>
              (?x ty. (s = holSyntax_Var x ty) /\
                     (s' = holSyntax_Var x (TYPE_SUBST tyin ty)))) ==>
      (?x ty. (INST_CORE env tyin tm = holSyntaxLib_Clash (holSyntax_Var x
        (TYPE_SUBST tyin ty))) /\
                VFREE_IN (holSyntax_Var x ty) tm /\ ~(REV_ASSOCD
                  (holSyntax_Var x (TYPE_SUBST tyin ty))
                  env (holSyntax_Var x ty) = holSyntax_Var x ty)) \/ (!x ty.
                VFREE_IN (holSyntax_Var x ty) tm ==> REV_ASSOCD
                  (holSyntax_Var x (TYPE_SUBST tyin ty))
                    env (holSyntax_Var x ty) = holSyntax_Var x ty) /\
        (?tm'. INST_CORE env tyin tm = holSyntaxLib_Result tm' /\ has_type
          tm' (TYPE_SUBST tyin (typeof tm)) /\
               (!u uty. VFREE_IN (holSyntax_Var u uty) tm' <=>
                        (?oty. VFREE_IN (holSyntax_Var u oty) tm /\
                              uty = TYPE_SUBST tyin oty)))`,
  CHEAT_TAC);;

let INST_CORE_NIL_IS_RESULT = prove
 (`!tyin tm. welltyped tm ==> IS_RESULT (INST_CORE [] tyin tm)`,
  CHEAT_TAC);;

let INST_HAS_TYPE = prove
 (`!tm ty tyin ty'. has_type tm ty /\ ty' = TYPE_SUBST tyin ty ==> has_type
  (holSyntax_INST tyin tm) ty'`,
  CHEAT_TAC);;

let INST_WELLTYPED = prove
 (`!tm tyin. welltyped tm ==> welltyped (holSyntax_INST tyin tm)`,
  CHEAT_TAC);;

let INST_CORE_NIL = prove
 (`!env tyin tm. welltyped tm /\ tyin = [] /\
      (!x ty. VFREE_IN (holSyntax_Var x ty) tm ==> REV_ASSOCD (holSyntax_Var
        x (TYPE_SUBST tyin ty)) env (holSyntax_Var x ty) = holSyntax_Var x ty)
        ==>
      INST_CORE env tyin tm = holSyntaxLib_Result tm`,
  CHEAT_TAC);;

let INST_nil = prove
 (`welltyped tm ==> (holSyntax_INST [] tm = tm)`,
  CHEAT_TAC);;

(* tyvars and tvars *)

let tyvars_ALL_DISTINCT = prove
 (`!ty. ALL_DISTINCT (holSyntax_tyvars ty)`,
  CHEAT_TAC);;
add_simp tyvars_ALL_DISTINCT;;

let tvars_ALL_DISTINCT = prove
 (`!tm. ALL_DISTINCT (tvars tm)`,
  CHEAT_TAC);;
add_simp tvars_ALL_DISTINCT;;

let tyvars_TYPE_SUBST = prove
 (`!ty tyin. set_of_list (holSyntax_tyvars (TYPE_SUBST tyin ty)) =
      {v | ?x. MEM x (holSyntax_tyvars ty) /\ MEM v (holSyntax_tyvars
        (REV_ASSOCD (holSyntax_Tyvar x) tyin (holSyntax_Tyvar x)))}`,
  CHEAT_TAC);;

let tyvars_typeof_subset_tvars = prove
 (`!tm ty. has_type tm ty ==> set_of_list (holSyntax_tyvars ty) SUBSET
  set_of_list (tvars tm)`,
  CHEAT_TAC);;

let tyvars_Tyapp_MAP_Tyvar = prove
 (`!x ls. ALL_DISTINCT ls ==> (holSyntax_tyvars (holSyntax_Tyapp x (MAP
  holSyntax_Tyvar ls)) = LIST_UNION [] ls)`,
  CHEAT_TAC);;

let STRING_SORT_SET_TO_LIST_set_tvars = prove
 (`!tm. STRING_SORT (MAP explode (SET_TO_LIST (set_of_list (tvars tm)))) =
         STRING_SORT (MAP explode (tvars tm))`,
  CHEAT_TAC);;

let mlstring_sort_SET_TO_LIST_set_tvars = prove
 (`mlstring_sort (SET_TO_LIST (set_of_list (tvars tm))) = mlstring_sort
  (tvars tm)`,
  CHEAT_TAC);;

(* Equations *)

let EQUATION_HAS_TYPE_BOOL = prove
 (`!s t.
          has_type ((===) s t) (holSyntax_Tyapp (implode "bool") []) <=>
            welltyped s /\ welltyped t /\ (typeof s = typeof t)`,
  CHEAT_TAC);;

let welltyped_equation = prove
 (`!s t. welltyped ((===) s t) <=> has_type ((===) s t) (holSyntax_Tyapp
  (implode "bool") [])`,
  CHEAT_TAC);;

let typeof_equation = prove
 (`welltyped ((===) l r) ==> (typeof ((===) l r)) = (holSyntax_Tyapp (implode
  "bool") [])`,
  CHEAT_TAC);;

let vfree_in_equation = prove
 (`VFREE_IN v ((===) s t) <=> (v = (\ty. holSyntax_Const (implode "=") ((\s
  t. holSyntax_Tyapp (implode "fun") [s; t]) ty ((\s t. holSyntax_Tyapp
  (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") [])))) (typeof
  s)) \/ VFREE_IN v s \/ VFREE_IN v t`,
  CHEAT_TAC);;

let equation_intro = prove
 (`(ty = typeof p) ==> (holSyntax_Comb (holSyntax_Comb ((\ty. holSyntax_Const
  (implode "=") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode
  "bool") [])))) ty) p) q = (===) p q)`,
  CHEAT_TAC);;

(* type_ok *)

let type_ok_TYPE_SUBST = prove
 (`!s tyin ty.
      type_ok s ty /\
      ALL (type_ok s) (MAP FST tyin) ==> type_ok s (TYPE_SUBST tyin ty)`,
  CHEAT_TAC);;

let type_ok_TYPE_SUBST_imp = prove
 (`!s tyin ty. type_ok s (TYPE_SUBST tyin ty) ==>
                (!x. MEM x (holSyntax_tyvars ty) ==> type_ok s (TYPE_SUBST
                  tyin (holSyntax_Tyvar x)))`,
  CHEAT_TAC);;

(* term_ok *)

let term_ok_welltyped = prove
 (`!sig t. holSyntax_term_ok sig t ==> welltyped t`,
  CHEAT_TAC);;

let term_ok_type_ok = prove
 (`!sig t.
          is_std_sig sig /\ holSyntax_term_ok sig t ==> type_ok (FST sig)
            (typeof t)`,
  CHEAT_TAC);;

let term_ok_equation = prove
 (`is_std_sig sig ==>
      (holSyntax_term_ok sig ((===) s t) <=>
        holSyntax_term_ok sig s /\ holSyntax_term_ok sig t /\
        typeof t = typeof s)`,
  CHEAT_TAC);;

let term_ok_clauses = prove
 (`is_std_sig sig ==>
    (holSyntax_term_ok sig (holSyntax_Var s ty) <=> type_ok ((\ctxt.
      alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) sig) ty) /\
    (type_ok ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
      ctxt)) sig) (holSyntax_Tyvar a) <=> T) /\
    (type_ok ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
      ctxt)) sig) (holSyntax_Tyapp (implode "bool") []) <=> T) /\
    (type_ok ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
      ctxt)) sig) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty1 ty2) <=>
      type_ok ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
      ctxt)) sig) ty1 /\ type_ok ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
      types_of_upd ctxt)) ctxt)) sig) ty2) /\
    (holSyntax_term_ok sig (holSyntax_Comb t1 t2) <=> holSyntax_term_ok sig
      t1 /\ holSyntax_term_ok sig t2 /\ welltyped (holSyntax_Comb t1 t2)) /\
    (holSyntax_term_ok sig ((\ty. holSyntax_Const (implode "=") ((\s t.
      holSyntax_Tyapp (implode "fun") [s; t]) ty ((\s t. holSyntax_Tyapp
      (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") [])))) ty)
      <=> type_ok ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
      ctxt)) sig) ty) /\
    (holSyntax_term_ok sig ((===) t1 t2) <=> holSyntax_term_ok sig t1
      /\ holSyntax_term_ok sig t2 /\ typeof t1 = typeof t2) /\
    (holSyntax_term_ok sig (holSyntax_Abs (holSyntax_Var s ty) t) <=>
      type_ok ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
      ctxt)) sig) ty /\ holSyntax_term_ok sig t)`,
  CHEAT_TAC);;

let term_ok_VSUBST = prove
 (`!sig tm ilist.
    holSyntax_term_ok sig tm /\
    (!s s'. MEM (s',s) ilist ==> (?x ty. s = holSyntax_Var x ty /\ has_type
      s' ty /\ holSyntax_term_ok sig s')) ==>
    holSyntax_term_ok sig (VSUBST ilist tm)`,
  CHEAT_TAC);;

let term_ok_INST_CORE = prove
 (`!sig env tyin tm.
      holSyntax_term_ok sig tm /\
      ALL (type_ok (FST sig)) (MAP FST tyin) /\
      (!s s'. MEM (s,s') env ==> (?x ty. s = holSyntax_Var x ty /\ s' =
        holSyntax_Var x (TYPE_SUBST tyin ty))) /\
      IS_RESULT (INST_CORE env tyin tm) ==>
      holSyntax_term_ok sig (RESULT (INST_CORE env tyin tm))`,
  CHEAT_TAC);;

let term_ok_INST = prove
 (`!sig tyin tm.
    holSyntax_term_ok sig tm /\
    ALL (type_ok (FST sig)) (MAP FST tyin) ==>
    holSyntax_term_ok sig (holSyntax_INST tyin tm)`,
  CHEAT_TAC);;

let term_ok_raconv = prove
 (`!env tp. RACONV env tp ==>
      (!sig.
      ALL (\(s,s'). welltyped s /\ welltyped s' /\ typeof s = typeof s'
        /\ type_ok (FST sig) (typeof s)) env ==>
      holSyntax_term_ok sig (FST tp) /\ welltyped (SND tp) ==>
        holSyntax_term_ok sig (SND tp))`,
  CHEAT_TAC);;

let term_ok_aconv = prove
 (`!sig t1 t2. ACONV t1 t2 /\ holSyntax_term_ok sig t1 /\ welltyped t2 ==>
  holSyntax_term_ok sig t2`,
  CHEAT_TAC);;

let term_ok_VFREE_IN = prove
 (`!sig t x. VFREE_IN x t /\ holSyntax_term_ok sig t ==> holSyntax_term_ok
  sig x`,
  CHEAT_TAC);;

(* de Bruijn terms, for showing alpha-equivalence respect
   by substitution and instantiation *)

let dbterm_INDUCT,dbterm_RECURSION = define_datatype
  "dbterm =
     dbVar mlstring type
   | dbBound num
   | dbConst mlstring type
   | dbComb dbterm dbterm
   | dbAbs type dbterm";;

(* bind a variable above a de Bruijn term *)

let holSyntaxExtra_bind_def,holSyntaxExtra_bind_ind = define_guess
  `(holSyntaxExtra_bind v n (dbVar x ty) = if v = (x,ty) then dbBound n
    else dbVar x ty) /\
   (holSyntaxExtra_bind v n (dbBound m) = dbBound m) /\
   (holSyntaxExtra_bind v n (dbConst x ty) = dbConst x ty) /\
   (holSyntaxExtra_bind v n (dbComb t1 t2) = dbComb (holSyntaxExtra_bind v
    n t1) (holSyntaxExtra_bind v n t2)) /\
   (holSyntaxExtra_bind v n (dbAbs ty tm) = dbAbs ty (holSyntaxExtra_bind
    v (n + 1) tm))`;;
add_simp holSyntaxExtra_bind_def;;

(* conversion into de Bruijn *)

let db_def,db_ind = define_guess
  `(holSyntaxExtra_db (holSyntax_Var x ty) = dbVar x ty) /\
   (holSyntaxExtra_db (holSyntax_Const x ty) = dbConst x ty) /\
   (holSyntaxExtra_db (holSyntax_Comb t1 t2) = dbComb (holSyntaxExtra_db
    t1) (holSyntaxExtra_db t2)) /\
   (holSyntaxExtra_db (holSyntax_Abs v tm) = dbAbs (typeof v)
    (holSyntaxExtra_bind (holSyntax_dest_var v) 0 (holSyntaxExtra_db tm)))`;;
add_simp db_def;;

(* de Bruijn versions of VSUBST and VFREE_IN *)

let dbVSUBST_def,dbVSUBST_ind = define_guess
  `(dbVSUBST ilist (dbVar x ty) = REV_ASSOCD (dbVar x ty) ilist (dbVar x
    ty)) /\
   (dbVSUBST ilist (dbBound m) = dbBound m) /\
   (dbVSUBST ilist (dbConst x ty) = dbConst x ty) /\
   (dbVSUBST ilist (dbComb t1 t2) = dbComb (dbVSUBST ilist t1) (dbVSUBST
    ilist t2)) /\
   (dbVSUBST ilist (dbAbs ty t) = dbAbs ty (dbVSUBST ilist t))`;;
add_simp dbVSUBST_def;;

let dbVFREE_IN_def,dbVFREE_IN_ind = define_guess
  `(dbVFREE_IN v (dbVar x ty) <=> dbVar x ty = v) /\
   (dbVFREE_IN v (dbBound n) <=> F) /\
   (dbVFREE_IN v (dbConst x ty) <=> dbConst x ty = v) /\
   (dbVFREE_IN v (dbComb t1 t2) <=> (dbVFREE_IN v t1 \/ dbVFREE_IN v t2)) /\
   (dbVFREE_IN v (dbAbs ty t) <=> dbVFREE_IN v t)`;;
add_simp dbVFREE_IN_def;;

let bind_not_free = prove
 (`!t n v. ~(dbVFREE_IN (UNCURRY dbVar v) t) ==> holSyntaxExtra_bind v n t =
  t`,
  CHEAT_TAC);;

let bind_dbVSUBST = prove
 (`!tm v n ls.
    ~((UNCURRY dbVar v) IN set_of_list (MAP SND ls)) /\
    (!k. dbVFREE_IN k tm /\ MEM k (MAP SND ls) ==>
        ~(dbVFREE_IN (UNCURRY dbVar v) (REV_ASSOCD k ls k))) ==>
    holSyntaxExtra_bind v n (dbVSUBST ls tm) = dbVSUBST ls
      (holSyntaxExtra_bind v n tm)`,
  CHEAT_TAC);;

let bind_dbVSUBST_cons = prove
 (`!tm z x n ls.
    ~(dbVFREE_IN (UNCURRY dbVar z) (dbVSUBST ls (holSyntaxExtra_bind x n
      tm))) ==>
    holSyntaxExtra_bind z n (dbVSUBST (CONS (UNCURRY dbVar z,UNCURRY dbVar
      x) ls) tm) = dbVSUBST ls (holSyntaxExtra_bind x n tm)`,
  CHEAT_TAC);;

let dbVSUBST_frees = prove
 (`!tm ls ls'.
    (!k. dbVFREE_IN k tm ==> REV_ASSOCD k ls k = REV_ASSOCD k ls' k) ==>
      dbVSUBST ls tm = dbVSUBST ls' tm`,
  CHEAT_TAC);;

let dbVFREE_IN_bind = prove
 (`!tm x v n b. dbVFREE_IN x (holSyntaxExtra_bind v n tm) <=> (~(x = UNCURRY
  dbVar v)) /\ dbVFREE_IN x tm`,
  CHEAT_TAC);;

let dbVFREE_IN_VFREE_IN = prove
 (`!tm x. welltyped tm ==> (dbVFREE_IN (holSyntaxExtra_db x)
  (holSyntaxExtra_db tm) <=> VFREE_IN x tm)`,
  CHEAT_TAC);;

let MAP_db_FILTER_neq = prove
 (`!ls z ty. MAP (\(x,y). (holSyntaxExtra_db x,holSyntaxExtra_db y)) (FILTER
  (\(x,y). ~(y = holSyntax_Var z ty)) ls) = FILTER (\(x,y). ~(y = dbVar z
  ty)) (MAP (\(x,y). (holSyntaxExtra_db x,holSyntaxExtra_db y)) ls)`,
  CHEAT_TAC);;

let REV_ASSOCD_MAP_db = prove
 (`!ls k ky.
    (!k v. MEM (v,k) ls ==> (?x ty. k = holSyntax_Var x ty)) ==>
    REV_ASSOCD (dbVar k ky) (MAP (\(x,y). (holSyntaxExtra_db
      x,holSyntaxExtra_db y)) ls) (dbVar k ky) = holSyntaxExtra_db
      (REV_ASSOCD (holSyntax_Var k ky) ls (holSyntax_Var k ky))`,
  CHEAT_TAC);;

let dbVFREE_IN_dbVSUBST = prove
 (`!tm u uty ilist.
      dbVFREE_IN (dbVar u uty) (dbVSUBST ilist tm) <=>
      (?y ty. dbVFREE_IN (dbVar y ty) tm /\
             dbVFREE_IN (dbVar u uty)
               (REV_ASSOCD (dbVar y ty) ilist (dbVar y ty)))`,
  CHEAT_TAC);;

let VSUBST_dbVSUBST = prove
 (`!tm ilist.
    welltyped tm /\
    (!k v. MEM (v,k) ilist ==> welltyped v /\ (?x ty. k = holSyntax_Var x
      ty)) ==>
    holSyntaxExtra_db (VSUBST ilist tm) = dbVSUBST (MAP (\(x,y).
      (holSyntaxExtra_db x,holSyntaxExtra_db y)) ilist) (holSyntaxExtra_db
      tm)`,
  CHEAT_TAC);;

(* de Bruijn version of INST *)

let dbINST_def,dbINST_ind = define_guess
  `(dbINST tyin (dbVar x ty) = dbVar x (TYPE_SUBST tyin ty)) /\
   (dbINST tyin (dbBound n) = dbBound n) /\
   (dbINST tyin (dbConst x ty) = dbConst x (TYPE_SUBST tyin ty)) /\
   (dbINST tyin (dbComb t1 t2) = dbComb (dbINST tyin t1) (dbINST tyin t2)) /\
   (dbINST tyin (dbAbs ty t) = dbAbs (TYPE_SUBST tyin ty) (dbINST tyin t))`;;
add_simp dbINST_def;;

let dbINST_bind = prove
 (`!tm v n ls.
      (!ty. dbVFREE_IN (dbVar (FST v) ty) tm /\ (TYPE_SUBST ls ty =
        TYPE_SUBST ls (SND v)) ==> ty = SND v) ==> dbINST ls
        (holSyntaxExtra_bind v n tm) = holSyntaxExtra_bind (FST v,TYPE_SUBST
        ls (SND v)) n (dbINST ls tm)`,
  CHEAT_TAC);;

let dbVSUBST_nil = prove
 (`!tm. dbVSUBST [] tm = tm`,
  CHEAT_TAC);;
add_simp dbVSUBST_nil;;

let INST_CORE_dbINST = prove
 (`!tm tyin env tmi.
      welltyped tm /\ (!s s'. MEM (s,s') env ==> (?x ty. s = holSyntax_Var x
        ty /\ s' = holSyntax_Var x (TYPE_SUBST tyin ty))) /\
      INST_CORE env tyin tm = holSyntaxLib_Result tmi ==>
        holSyntaxExtra_db tmi = dbINST tyin (holSyntaxExtra_db tm)`,
  CHEAT_TAC);;

let INST_dbINST = prove
 (`!tm tyin.
      welltyped tm ==>
      holSyntaxExtra_db (holSyntax_INST tyin tm) = dbINST tyin
        (holSyntaxExtra_db tm)`,
  CHEAT_TAC);;

(* conversion into de Bruijn given an environment of already bound variables *)

let dbterm_def,dbterm_ind = define_guess
  `(dbterm env (holSyntax_Var s ty) =
         match find_index (s,ty) env 0 with SOME n -> dbBound n | NONE
             -> dbVar s ty) /\
   (dbterm env (holSyntax_Const s ty) = dbConst s ty) /\
   (dbterm env (holSyntax_Comb t1 t2) = dbComb (dbterm env t1) (dbterm env
    t2)) /\
   (dbterm env (holSyntax_Abs v t) = dbAbs (typeof v) (dbterm (CONS
    (holSyntax_dest_var v) env) t))`;;
add_simp dbterm_def;;

let bind_list_aux_def,bind_list_aux_ind = define_guess
  `(bind_list_aux n [] tm = tm) /\
   (bind_list_aux n (CONS v vs) tm = bind_list_aux (n + 1) vs
    (holSyntaxExtra_bind v n tm))`;;
add_simp bind_list_aux_def;;

let bind_list_aux_clauses = prove
 (`(!env m. bind_list_aux m env (dbBound n) = dbBound n) /\
    (!env m. bind_list_aux m env (dbConst x ty) = dbConst x ty) /\
    (!env m t1 t2. bind_list_aux m env (dbComb t1 t2) = dbComb
      (bind_list_aux m env t1) (bind_list_aux m env t2)) /\
    (!env m ty tm. bind_list_aux m env (dbAbs ty tm) = dbAbs ty
      (bind_list_aux (m + 1) env tm))`,
  CHEAT_TAC);;

let dbterm_bind = prove
 (`!tm env. dbterm env tm = bind_list_aux 0 env (holSyntaxExtra_db tm)`,
  CHEAT_TAC);;

let dbterm_db = prove
 (`!tm. dbterm [] tm = holSyntaxExtra_db tm`,
  CHEAT_TAC);;

(* alpha-equivalence on de Bruijn terms *)

let dbterm_RACONV = prove
 (`!t1 env1 t2 env2. welltyped t1 /\ welltyped t2 /\ dbterm env1 t1 = dbterm
  env2 t2 /\ LENGTH env1 = LENGTH env2 ==>
      RACONV (ZIP (MAP (UNCURRY holSyntax_Var) env1) (MAP (UNCURRY
        holSyntax_Var) env2)) (t1,t2)`,
  CHEAT_TAC);;

let RACONV_dbterm = prove
 (`!env tp. RACONV env tp ==>
    welltyped (FST tp) /\ welltyped (SND tp) /\
    (!vp. MEM vp env ==> (?x ty. (FST vp = holSyntax_Var x ty)) /\ (?x ty.
      (SND vp = holSyntax_Var x ty))) ==> dbterm (MAP (holSyntax_dest_var o
      FST) env) (FST tp) = dbterm (MAP (holSyntax_dest_var o SND) env) (SND
      tp)`,
  CHEAT_TAC);;

let dbterm_ACONV = prove
 (`!t1 t2. welltyped t1 /\ welltyped t2 ==> (ACONV t1 t2 <=> dbterm [] t1 =
  dbterm [] t2)`,
  CHEAT_TAC);;

let ACONV_db = prove
 (`!t1 t2. welltyped t1 /\ welltyped t2 ==> (ACONV t1 t2 <=>
  holSyntaxExtra_db t1 = holSyntaxExtra_db t2)`,
  CHEAT_TAC);;

(* respect of alpha-equivalence by VSUBST and INST follows *)

let ACONV_VSUBST = prove
 (`!t1 t2 ilist.
    welltyped t1 /\ welltyped t2 /\
    (!k v. MEM (v,k) ilist ==> (?x ty. k = holSyntax_Var x ty /\ has_type v
      ty)) /\
    ACONV t1 t2 ==>
    ACONV (VSUBST ilist t1) (VSUBST ilist t2)`,
  CHEAT_TAC);;

let ACONV_INST = prove
 (`!t1 t2 tyin. welltyped t1 /\ welltyped t2 /\ ACONV t1 t2 ==> ACONV
  (holSyntax_INST tyin t1) (holSyntax_INST tyin t2)`,
  CHEAT_TAC);;

(* list of bound variable names in a term *)

let bv_names_def,bv_names_ind = define_guess
  `(bv_names (holSyntax_Var _ _) = []) /\
   (bv_names (holSyntax_Const _ _) = []) /\
   (bv_names (holSyntax_Comb s t) = APPEND (bv_names s) (bv_names t)) /\
   (bv_names (holSyntax_Abs v t) = CONS (FST (holSyntax_dest_var v))
    (bv_names t))`;;
add_simp bv_names_def;;

(* Simpler versions (non-capture-avoiding) of substitution and instantiation.
   We do the semantics proofs on these and then use the fact that it is
   alpha-equivalence respecting, and suitable equivalent term always exists
   (see below). *)

let simple_subst_def,simple_subst_ind = define_guess
  `(simple_subst ilist (holSyntax_Var x ty) = REV_ASSOCD (holSyntax_Var x
    ty) ilist (holSyntax_Var x ty)) /\
   (simple_subst ilist (holSyntax_Const x ty) = (holSyntax_Const x
    ty:holSyntax_term)) /\
   (simple_subst ilist (holSyntax_Comb t1 t2) = holSyntax_Comb
    (simple_subst ilist t1) (simple_subst ilist t2)) /\
   (simple_subst ilist (holSyntax_Abs v tm) =
        holSyntax_Abs v (simple_subst (FILTER (\(s',s). (~(s = v)))
            ilist) tm))`;;
add_simp simple_subst_def;;

let simple_inst_def,simple_inst_ind = define_guess
  `(simple_inst tyin (holSyntax_Var x ty) = holSyntax_Var x (TYPE_SUBST
    tyin ty)) /\
   (simple_inst tyin (holSyntax_Const x ty) = holSyntax_Const x (TYPE_SUBST
    tyin ty)) /\
   (simple_inst tyin (holSyntax_Comb s t) = holSyntax_Comb (simple_inst
    tyin s) (simple_inst tyin t)) /\
   (simple_inst tyin (holSyntax_Abs v t) = holSyntax_Abs (simple_inst tyin
    v) (simple_inst tyin t))`;;
add_simp simple_inst_def;;

let VSUBST_simple_subst = prove
 (`!tm ilist.
               DISJOINT (set_of_list (bv_names tm)) {y | ?ty u. VFREE_IN
                 (holSyntax_Var y ty) u /\ MEM u (MAP FST ilist)} /\
               (!s s'. MEM (s',s) ilist ==> (?x ty. s = holSyntax_Var x ty))
                 /\
               welltyped tm ==> VSUBST ilist tm = simple_subst ilist tm`,
  CHEAT_TAC);;

let INST_CORE_simple_inst = prove
 (`!env tyin tm.
      ALL_DISTINCT (APPEND (bv_names tm) (MAP (FST o holSyntax_dest_var o
        SND) env)) /\
      DISJOINT (set_of_list (bv_names tm)) {x | ?ty. VFREE_IN (holSyntax_Var
        x ty) tm} /\
      (!s s'. MEM (s,s') env ==> (?x ty. s = holSyntax_Var x ty /\ s' =
        holSyntax_Var x (TYPE_SUBST tyin ty))) /\
      (!x ty ty'. VFREE_IN (holSyntax_Var x ty) tm /\ MEM (holSyntax_Var x
        ty') (MAP FST env) ==> ty' = ty) /\
      welltyped tm ==> INST_CORE env tyin tm = holSyntaxLib_Result
        (simple_inst tyin tm)`,
  CHEAT_TAC);;

let INST_simple_inst = prove
 (`!tyin tm.
      ALL_DISTINCT (bv_names tm) /\
      DISJOINT (set_of_list (bv_names tm)) {x | ?ty. VFREE_IN (holSyntax_Var
        x ty) tm} /\
      welltyped tm ==>
      holSyntax_INST tyin tm = simple_inst tyin tm`,
  CHEAT_TAC);;

let simple_subst_has_type = prove
 (`!tm ty. has_type tm ty ==>
      (!subst.
        ALL (\(s',s). has_type s' (typeof s)) subst ==> has_type
          (simple_subst subst tm) ty)`,
  CHEAT_TAC);;

let simple_inst_has_type = prove
 (`!tm tyin. welltyped tm ==> has_type (simple_inst tyin tm) (TYPE_SUBST tyin
  (typeof tm))`,
  CHEAT_TAC);;

(* rename bound variables from a source of names *)

let rename_bvars_def,rename_bvars_ind = define_guess
  `(rename_bvars names env (holSyntax_Var s ty) = (names,holSyntax_Var
    (REV_ASSOCD (s,ty) env s) ty)) /\
   (rename_bvars names env (holSyntax_Const s ty) = (names,(holSyntax_Const
    s ty:holSyntax_term))) /\
   (rename_bvars names env (holSyntax_Comb t1 t2) =
         let (names,t1) = rename_bvars names env t1 in
         let (names,t2) = rename_bvars names env t2 in
         (names,(holSyntax_Comb t1 t2:holSyntax_term))) /\
   (rename_bvars [] env (holSyntax_Abs v tm) =
         let (names,tm) = rename_bvars [] env tm in
         (names,(holSyntax_Abs v tm:holSyntax_term))) /\
   (rename_bvars (CONS s' names) env (holSyntax_Abs v tm) =
         let (names,tm) = rename_bvars names (CONS (s',holSyntax_dest_var
             v) env) tm in
         (names,holSyntax_Abs (holSyntax_Var s' (typeof v)) tm))`;;

let FST_rename_bvars = prove
 (`!names env tm. LENGTH (bv_names tm) <= LENGTH names ==> (FST (rename_bvars
  names env tm) = DROP (LENGTH (bv_names tm)) names)`,
  CHEAT_TAC);;

let rename_bvars_RACONV = prove
 (`!names env tm.
    LENGTH (bv_names tm) <= LENGTH names /\
    DISJOINT (set_of_list (APPEND (MAP FST env) names)) (set_of_list (APPEND
      (MAP (FST o SND) env) (bv_names tm))) /\
    DISJOINT (set_of_list (APPEND (MAP FST env) names)) {x | ?ty. VFREE_IN
      (holSyntax_Var x ty) tm} /\
    ALL_DISTINCT (APPEND (MAP FST env) names) /\
    welltyped tm ==> RACONV (MAP (\(s',(s,ty)). (holSyntax_Var s
      ty,holSyntax_Var s' ty)) env) (tm,SND (rename_bvars names env tm))`,
  CHEAT_TAC);;

let rename_bvars_ACONV = prove
 (`!names tm.
    LENGTH (bv_names tm) <= LENGTH names /\ ALL_DISTINCT names /\
    DISJOINT (set_of_list names) {x | MEM x (bv_names tm) \/ (?ty. VFREE_IN
      (holSyntax_Var x ty) tm)} /\
    welltyped tm ==>
    ACONV tm (SND (rename_bvars names [] tm))`,
  CHEAT_TAC);;

let rename_bvars_has_type = prove
 (`!names env tm ty. has_type tm ty ==> has_type (SND (rename_bvars names env
  tm)) ty`,
  CHEAT_TAC);;

let rename_bvars_welltyped = prove
 (`!names env tm. welltyped tm ==> welltyped (SND (rename_bvars names env
  tm))`,
  CHEAT_TAC);;

(* appropriate fresh term for using the simple functions above *)

(* HOL4 holSyntaxExtraScript.sml:2673-2679: ML code, not ported *)

let fresh_union = prove
 (`FINITE s /\ FINITE t ==> ~(fresh (s UNION t) IN s) /\ ~(fresh (s UNION t)
  IN t)`,
  CHEAT_TAC);;

let fresh_names_exist = prove
 (`!s n. FINITE (s:string->bool) ==> (?names. LENGTH names = n
  /\ ALL_DISTINCT names /\ DISJOINT (set_of_list names) s)`,
  CHEAT_TAC);;

let bv_names_rename_bvars = prove
 (`!names env tm.
    LENGTH (bv_names tm) <= LENGTH names ==>
    bv_names (SND (rename_bvars names env tm)) = TAKE (LENGTH (bv_names
      tm)) names`,
  CHEAT_TAC);;

(* various rewrites for FINITE sets to make this go through *)

let FINITE_VFREE_IN = prove
 (`!tm. FINITE {x | ?ty. VFREE_IN (holSyntax_Var x ty) tm}`,
  CHEAT_TAC);;
add_simp FINITE_VFREE_IN;;

let FINITE_VFREE_IN_2 = prove
 (`!tm. FINITE {(x,ty) | VFREE_IN (holSyntax_Var x ty) tm}`,
  CHEAT_TAC);;
add_simp FINITE_VFREE_IN_2;;

let FINITE_VFREE_IN_list = prove
 (`!ls. FINITE {x | ?ty u. VFREE_IN (holSyntax_Var x ty) u /\ MEM u ls}`,
  CHEAT_TAC);;
add_simp FINITE_VFREE_IN_list;;

let FINITE_MEM_Var = prove
 (`!ls. FINITE {(x,ty) | MEM (holSyntax_Var x ty) ls}`,
  CHEAT_TAC);;
add_simp FINITE_MEM_Var;;

(* HOL4 holSyntaxExtraScript.sml:2787-2809: a proof *)

(* Alternative characterisation of VARIANT, and thereby of VSUBST and INST_CORE.
   Better for evaluation. *)

let vfree_in_def,vfree_in_ind = define_guess
  `vfree_in v tm =
     match tm with
       holSyntax_Abs bv bod -> ~(v = bv) /\ vfree_in v bod
     | holSyntax_Comb s t -> vfree_in v s \/ vfree_in v t
     | _ -> (tm = v)`;;

let vfree_in_thm = prove
 (`!name ty y. (VFREE_IN (holSyntax_Var name ty) y = vfree_in ((holSyntax_Var
  name ty:holSyntax_term)) y)`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (\(avoid,v).
             let n = SUM_SET (UNIONS (set_of_list (MAP (\a. {strlen x + 1 |
               ?ty.
               VFREE_IN (holSyntax_Var x ty) a}) avoid))) in
               n - (match v with holSyntax_Var x ty -> strlen x | _ -> 0))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 holSyntaxExtraScript.sml:2841-2857: the tactic that proves the
   termination *)
let variant_def,variant_ind = define_guess
  `variant avoid v =
     if EX (vfree_in v) avoid then
     match v with
        holSyntax_Var s ty -> variant avoid (holSyntax_Var (strcat s
          (implode "'")) ty)
     | _ -> v else v`;;

(* HOL4 holSyntaxExtraScript.sml:2859-2894: a theorem that HOL4 states as
   the value of an ML expression: variant_vsubst_thm *)

(* HOL4 holSyntaxExtraScript.sml:2896-2897: a theorem that HOL4 states as
   the value of an ML expression: VSUBST_thm *)

let subtract_def = new_definition
  `subtract l1 l2 = FILTER (\t. ~(MEM t l2)) l1`;;

let holSyntaxExtra_insert_def = new_definition
  `holSyntaxExtra_insert x l = if MEM x l then l else CONS x l`;;

let itlist_def,itlist_ind = define_guess
  `itlist f l b =
     match l with
       [] -> b
     | (CONS h t) -> f h (itlist f t b)`;;

let holSyntaxExtra_union_def = new_definition
  `holSyntaxExtra_union l1 l2 = itlist holSyntaxExtra_insert l1 l2`;;

let MEM_union = prove
 (`!xs ys x. MEM x (holSyntaxExtra_union xs ys) <=> MEM x xs \/ MEM x ys`,
  CHEAT_TAC);;

let EXISTS_union = prove
 (`!xs ys. EX P (holSyntaxExtra_union xs ys) <=> EX P xs \/ EX P ys`,
  CHEAT_TAC);;

let frees_def,frees_ind = define_guess
  `frees tm =
     match tm with
       holSyntax_Var _ _ -> [tm]
     | holSyntax_Const _ _ -> []
     | holSyntax_Abs bv bod -> subtract (frees bod) [bv]
     | holSyntax_Comb s t -> holSyntaxExtra_union (frees s) (frees t)`;;

let MEM_frees_EQ = prove
 (`!a x. MEM x (frees a) = (?n ty. (x = holSyntax_Var n ty) /\ MEM
  (holSyntax_Var n ty) (frees a))`,
  CHEAT_TAC);;

(* HOL4 holSyntaxExtraScript.sml:2953-3001: a theorem that HOL4 states as
   the value of an ML expression: variant_inst_thm *)

let INST_CORE_Abs_thm = prove
 (`!v t env tyin. welltyped (holSyntax_Abs v t) ==>
   INST_CORE env tyin (holSyntax_Abs v t) =
   (let (x,ty) = holSyntax_dest_var v in
    let ty' = TYPE_SUBST tyin ty in
    let v' = holSyntax_Var x ty' in
    let env' = CONS (v,v') env in
    let tres = INST_CORE env' tyin t in
      if IS_RESULT tres then holSyntaxLib_Result (holSyntax_Abs v' (RESULT
        tres))
      else (let w = CLASH tres in
           if ~(w = v') then tres
           else (let (x',_) =
               holSyntax_dest_var (variant (frees (RESULT (INST_CORE [] tyin
                 t))) (holSyntax_Var x ty')) in
              let t' = VSUBST [(holSyntax_Var x' ty,holSyntax_Var x ty)] t
                in
              let env'' = CONS (holSyntax_Var x' ty,holSyntax_Var x' ty')
                env in
              let tres' = INST_CORE env'' tyin t' in
                if IS_RESULT tres' then
                  holSyntaxLib_Result (holSyntax_Abs (holSyntax_Var x' ty')
                    (RESULT tres'))
                else tres')))`,
  CHEAT_TAC);;

(* provable terms are ok and of type bool *)

let proves_theory_ok = prove
 (`!thyh c. (|-) thyh c ==> theory_ok (FST thyh)`,
  CHEAT_TAC);;

let theory_ok_sig = prove
 (`!thy. theory_ok thy ==> is_std_sig ((\(ctxt:holSyntax_update list).
  ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
  ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt))
  ctxt)) thy)`,
  CHEAT_TAC);;

let proves_term_ok = prove
 (`!thyh c. (|-) thyh c ==>
      hypset_ok (SND thyh) /\
      ALL (\p. holSyntax_term_ok ((\(ctxt:holSyntax_update list). ((\ctxt.
        alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
        ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
        ctxt)) ctxt)) (FST thyh)) p /\ has_type p (holSyntax_Tyapp (implode
        "bool") [])) (CONS c (SND thyh))`,
  CHEAT_TAC);;

(* some derived rules *)

(* HOL4 holSyntaxExtraScript.sml:3110: ML code, not ported *)
let deductAntisym_equation = el 3 (CONJUNCTS (cake_rules proves));;
let eqMp_equation =
  REWRITE_RULE [GSYM IMP_IMP] (el 4 (CONJUNCTS (cake_rules proves)));;
let refl_equation = el 8 (CONJUNCTS (cake_rules proves));;
let appThm_equation =
  REWRITE_RULE [GSYM IMP_IMP] (el 7 (CONJUNCTS (cake_rules proves)));;

let addAssum = prove
 (`!thy h c a. (|-) (thy,h) c /\ holSyntax_term_ok ((\(ctxt:holSyntax_update
  list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
  ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt))
  ctxt)) thy) a /\ (has_type a (holSyntax_Tyapp (implode "bool") [])) ==>
  (|-) (thy,term_union [a] h) c`,
  CHEAT_TAC);;

(* inference system respects alpha-equivalence *)

(* HOL4 holSyntaxExtraScript.sml:3151-3157: ML code, not ported *)

(* [local] *)
let proves_concl_ACONV = prove
 (`!thyh c c'. (|-) thyh c /\ ACONV c c' /\ welltyped c' ==> (|-) thyh c'`,
  CHEAT_TAC);;

(* [local] *)
let proves_ACONV_lemma = prove
 (`!thy c h' h1 h.
     (|-) (thy,APPEND h1 h) c /\
     hypset_ok (APPEND h1 h') /\
     ALL (\x. EX (ACONV x) h') h /\
     ALL (\x. holSyntax_term_ok ((\(ctxt:holSyntax_update list). ((\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
       ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
       ctxt)) ctxt)) thy) x /\ has_type x (holSyntax_Tyapp (implode "bool")
       [])) h' ==> (|-) (thy,APPEND h1 h') c`,
  CHEAT_TAC);;

let proves_ACONV = prove
 (`!thy h' c' h c.
      (|-) (thy,h) c /\ welltyped c' /\ ACONV c c' /\
      hypset_ok h' /\
      ALL (\x. EX (ACONV x) h') h /\
      ALL (\x. holSyntax_term_ok ((\(ctxt:holSyntax_update list). ((\ctxt.
        alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
        ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
        ctxt)) ctxt)) thy) x /\ has_type x (holSyntax_Tyapp (implode "bool")
        [])) h' ==> (|-) (thy,h') c'`,
  CHEAT_TAC);;

(* more derived rules *)

let sym_equation = prove
 (`!thyh p q. (|-) thyh ((===) p q) ==> (|-) thyh ((===) q p)`,
  CHEAT_TAC);;

(* sym *)
let holSyntaxExtra_sym = prove
 (`!thyh p q ty. (|-) thyh (holSyntax_Comb (holSyntax_Comb ((\ty.
  holSyntax_Const (implode "=") ((\s t. holSyntax_Tyapp (implode "fun") [s;
  t]) ty ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty (holSyntax_Tyapp
  (implode "bool") [])))) ty) p) q) ==> (|-) thyh (holSyntax_Comb
  (holSyntax_Comb ((\ty. holSyntax_Const (implode "=") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) ty ((\s t. holSyntax_Tyapp (implode
  "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") [])))) ty) q) p)`,
  CHEAT_TAC);;

let trans_equation = prove
 (`!thy h1 h2 t1 t2a t2b t3. (|-) (thy,h2) ((===) t2b t3) ==> (|-) (thy,h1)
  ((===) t1 t2a) ==>
      ACONV t2a t2b ==> (|-) (thy,term_union h1 h2) ((===) t1 t3)`,
  CHEAT_TAC);;

let trans = prove
 (`!thy h1 h2 t1 t2a t2b t3 ty. (|-) (thy,h2) (holSyntax_Comb (holSyntax_Comb
  ((\ty. holSyntax_Const (implode "=") ((\s t. holSyntax_Tyapp (implode "fun")
  [s; t]) ty ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty
  (holSyntax_Tyapp (implode "bool") [])))) ty) t2b) t3) ==> (|-) (thy,h1)
  (holSyntax_Comb (holSyntax_Comb ((\ty. holSyntax_Const (implode "=") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) ty ((\s t. holSyntax_Tyapp (implode
  "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") [])))) ty) t1) t2a) ==>
      ACONV t2a t2b ==> (|-) (thy,term_union h1 h2) (holSyntax_Comb
        (holSyntax_Comb ((\ty. holSyntax_Const (implode "=") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) ty ((\s t. holSyntax_Tyapp
        (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") []))))
        ty) t1) t3)`,
  CHEAT_TAC);;

let proveHyp = prove
 (`!thy h1 c1 h2 c2. (|-) (thy,h1) c1 /\ (|-) (thy,h2) c2 ==> (|-)
  (thy,term_union h2 (term_remove c2 h1)) c1`,
  CHEAT_TAC);;

(* extension is transitive *)

let extends_trans = prove
 (`!c1 c2 c3. extends c1 c2 /\ extends c2 c3 ==> extends c1 c3`,
  CHEAT_TAC);;

(* extensions have all distinct names *)

let updates_ALL_DISTINCT = prove
 (`!upd ctxt. updates upd ctxt ==>
      (ALL_DISTINCT (MAP FST ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
        ==>
       ALL_DISTINCT (MAP FST ((\ctxt. FLAT (MAP types_of_upd ctxt)) (CONS
         upd ctxt)))) /\
      (ALL_DISTINCT (MAP FST ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt))
        ==>
       ALL_DISTINCT (MAP FST ((\ctxt. FLAT (MAP consts_of_upd ctxt)) (CONS
         upd ctxt))))`,
  CHEAT_TAC);;

let extends_ALL_DISTINCT = prove
 (`!ctxt1 ctxt2. extends ctxt2 ctxt1 ==>
      (ALL_DISTINCT (MAP FST ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt1))
        ==>
       ALL_DISTINCT (MAP FST ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt2)))
         /\
      (ALL_DISTINCT (MAP FST ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt1))
        ==>
       ALL_DISTINCT (MAP FST ((\ctxt. FLAT (MAP consts_of_upd ctxt))
         ctxt2)))`,
  CHEAT_TAC);;

let init_ALL_DISTINCT = prove
 (`ALL_DISTINCT (MAP FST ((\ctxt. FLAT (MAP consts_of_upd ctxt)) init_ctxt)) /\
    ALL_DISTINCT (MAP FST ((\ctxt. FLAT (MAP types_of_upd ctxt))
      init_ctxt))`,
  CHEAT_TAC);;

let updates_DISJOINT = prove
 (`!upd ctxt. updates upd ctxt ==>
    DISJOINT (FDOM (alist_to_fmap (consts_of_upd upd))) (FDOM ((\ctxt.
      alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) /\
    DISJOINT (FDOM (alist_to_fmap (types_of_upd upd))) (FDOM ((\ctxt.
      alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt))`,
  CHEAT_TAC);;

let updates_upd_ALL_DISTINCT = prove
 (`!upd ctxt. updates upd ctxt ==>
      ALL_DISTINCT (MAP FST (consts_of_upd upd)) /\
      ALL_DISTINCT (MAP FST (types_of_upd upd))`,
  CHEAT_TAC);;

let updates_upd_DISJOINT = prove
 (`!upd ctxt. updates upd ctxt ==>
      DISJOINT (set_of_list (MAP FST (types_of_upd upd))) (set_of_list (MAP
        FST ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))) /\
      DISJOINT (set_of_list (MAP FST (consts_of_upd upd))) (set_of_list
        (MAP FST ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)))`,
  CHEAT_TAC);;

(* signature extensions preserve ok *)

let type_ok_extend = prove
 (`!t tyenv tyenv'.
    tyenv SUBMAP tyenv' /\
    type_ok tyenv t ==>
    type_ok tyenv' t`,
  CHEAT_TAC);;

let term_ok_extend = prove
 (`!t tyenv tmenv tyenv' tmenv'.
    tyenv SUBMAP tyenv' /\ tmenv SUBMAP tmenv' /\
    holSyntax_term_ok (tyenv,tmenv) t ==>
    holSyntax_term_ok (tyenv',tmenv') t`,
  CHEAT_TAC);;

let term_ok_updates = prove
 (`!upd ctxt. updates upd ctxt ==>
      holSyntax_term_ok ((\(ctxt:holSyntax_update list). ((\ctxt.
        alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
        ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
        ctxt)) ctxt)) ((\(ctxt:holSyntax_update list).
        ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
        (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
        FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
        ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
        upd)) ctxt)) ctxt)) ctxt)) ctxt)) tm ==>
      holSyntax_term_ok ((\(ctxt:holSyntax_update list). ((\ctxt.
        alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
        ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
        ctxt)) ctxt)) ((\(ctxt:holSyntax_update list).
        ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
        (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
        FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
        ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
        upd)) ctxt)) ctxt)) ctxt)) (CONS upd ctxt))) tm`,
  CHEAT_TAC);;

let is_std_sig_extend = prove
 (`!tyenv tmenv tyenv' tmenv'.
    is_std_sig (tyenv,tmenv) /\ tyenv SUBMAP tyenv' /\ tmenv SUBMAP tmenv'
      ==>
    is_std_sig (tyenv',tmenv')`,
  CHEAT_TAC);;

(* updates preserve ok *)

let updates_theory_ok = prove
 (`!upd ctxt. updates upd ctxt ==> theory_ok ((\(ctxt:holSyntax_update list).
  ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
  types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
  consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT
  (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt))
  ctxt)) ctxt) ==> theory_ok ((\(ctxt:holSyntax_update list).
  ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
  types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
  consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT
  (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt))
  ctxt)) (CONS upd ctxt))`,
  CHEAT_TAC);;

let extends_theory_ok = prove
 (`!ctxt1 ctxt2. extends ctxt2 ctxt1 ==> theory_ok ((\(ctxt:holSyntax_update
  list). ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt.
  FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
  FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
  ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
  ctxt)) ctxt)) ctxt)) ctxt1) ==> theory_ok ((\(ctxt:holSyntax_update list).
  ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
  types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
  consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT
  (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt))
  ctxt)) ctxt2)`,
  CHEAT_TAC);;

(* init_ctxt ok *)

let init_theory_ok = prove
 (`theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
  list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
  ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt))
  ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
  (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) init_ctxt)`,
  CHEAT_TAC);;

(* is_std_sig is preserved *)

let is_std_sig_extends = prove
 (`!ctxt1 ctxt2. extends ctxt2 ctxt1 ==> is_std_sig ((\(ctxt:holSyntax_update
  list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
  ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt))
  ctxt)) ctxt1) ==> is_std_sig ((\(ctxt:holSyntax_update list). ((\ctxt.
  alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
  alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt2)`,
  CHEAT_TAC);;

(* recover constant definition as a special case of specification *)

(* HOL4 holSyntaxExtraScript.sml:3652: the overload ConstDef, which the port
   expands *)

let ConstDef_updates = prove
 (`!name tm ctxt.
    theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
      list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
      ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
      ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
      (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) ctxt) /\
    holSyntax_term_ok ((\(ctxt:holSyntax_update list). ((\ctxt.
      alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
      alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt)
      tm /\ ~(name IN FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
      consts_of_upd ctxt)) ctxt)) ctxt)) /\
    CLOSED tm /\
    set_of_list (tvars tm) SUBSET set_of_list (holSyntax_tyvars (typeof
      tm)) ==> updates ((\x t. ConstSpec [(x,t)] ((===) (holSyntax_Var x
      (typeof t)) t)) name tm) ctxt`,
  CHEAT_TAC);;

(* lookups in extended contexts *)

let FLOOKUP_tmsof_updates = prove
 (`!upd ctxt. updates upd ctxt ==>
    FLOOKUP ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
      ctxt)) ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list).
      ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
      ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt))
      ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
      (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) ctxt))
      name = SOME ty ==>
    FLOOKUP ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
      ctxt)) ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
      list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
      ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
      ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
      APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
      (CONS upd ctxt))) name = SOME ty`,
  CHEAT_TAC);;

let FLOOKUP_tysof_updates = prove
 (`!upd ctxt. updates upd ctxt ==>
    FLOOKUP ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
      ctxt)) ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list).
      ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
      ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt))
      ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
      (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) ctxt))
      name = SOME a ==>
    FLOOKUP ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
      ctxt)) ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
      list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
      ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
      ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
      APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
      (CONS upd ctxt))) name = SOME a`,
  CHEAT_TAC);;

let FLOOKUP_tysof_extends = prove
 (`!ctxt2 ctxt1. extends ctxt1 ctxt2 ==>
   (FLOOKUP ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
     ctxt)) ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt.
     FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
     FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt2)) k = SOME v) ==>
   (FLOOKUP ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
     ctxt)) ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt.
     FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
     FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt1)) k = SOME v)`,
  CHEAT_TAC);;

let FLOOKUP_tmsof_extends = prove
 (`!ctxt2 ctxt1. extends ctxt1 ctxt2 ==>
   (FLOOKUP ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
     ctxt)) ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt.
     FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
     FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt2)) k = SOME v) ==>
   (FLOOKUP ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
     ctxt)) ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt.
     FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
     FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt1)) k = SOME v)`,
  CHEAT_TAC);;

let extends_sub = prove
 (`!ctxt2 ctxt1. extends ctxt2 ctxt1 ==>
      (\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt))
        ctxt1 SUBMAP (\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt2 /\
      (\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
        ctxt1 SUBMAP (\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd
        ctxt)) ctxt)) ctxt2 /\
      (\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd
        upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt1 SUBSET (\ctxt.
        set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
        (conexts_of_upd upd)) ctxt)) ctxt)) ctxt2`,
  CHEAT_TAC);;

(* proofs still work in extended contexts *)

(* [local] *)
let update_extension = prove
 (`!lhs tm.
       (|-) lhs tm ==>
       (!ctxt tms upd.
         lhs = ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
           list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd
           ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
           consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
           ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
           (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) ctxt,tms) /\ updates
           upd ctxt ==> (|-) ((\(ctxt:holSyntax_update list).
           ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt.
           FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap
           ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt.
           set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
           (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) (CONS upd ctxt),tms)
           tm)`,
  CHEAT_TAC);;

let updates_proves = prove
 (`!upd ctxt. updates upd ctxt ==>
    (!h c. (|-) ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
      list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
      ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
      ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
      APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
      ctxt,h) c ==> (|-) ((\(ctxt:holSyntax_update list).
      ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
      (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
      FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
      ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
      upd)) ctxt)) ctxt)) ctxt)) (CONS upd ctxt),h) c)`,
  CHEAT_TAC);;

let extends_proves = prove
 (`!c2 c1.
     extends c2 c1 ==>
     (!h c. (|-) ((\(ctxt:holSyntax_update list).
       ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
       FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
       ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
       upd)) ctxt)) ctxt)) ctxt)) c1,h) c ==> (|-) ((\(ctxt:holSyntax_update
       list). ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap
       ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt))
       ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
       (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) c2,h)
       c)`,
  CHEAT_TAC);;

(* types occurring in a term *)

let types_in_def,types_in_ind = define_guess
  `(types_in (holSyntax_Var x ty) = {ty}) /\
   (types_in (holSyntax_Const c ty) = {ty}) /\
   (types_in (holSyntax_Comb t1 t2) = types_in t1 UNION types_in t2) /\
   (types_in (holSyntax_Abs v t) = types_in v UNION types_in t)`;;
add_simp types_in_def;;

let type_ok_types_in = prove
 (`!sig. is_std_sig sig ==> (!tm ty. holSyntax_term_ok sig tm /\ ty IN
  types_in tm ==> type_ok ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
  types_of_upd ctxt)) ctxt)) sig) ty)`,
  CHEAT_TAC);;

let VFREE_IN_types_in = prove
 (`!t2 t1. VFREE_IN t1 t2 ==> typeof t1 IN types_in t2`,
  CHEAT_TAC);;

(* Var_subterm_types_in[local] *)
let var_subterm_types_in = prove
 (`!t x ty. RTC subterm1 (holSyntax_Var x ty) t ==> ty IN types_in t`,
  CHEAT_TAC);;

(* Const_subterm_types_in[local] *)
let const_subterm_types_in = prove
 (`!t x ty. RTC subterm1 (holSyntax_Const x ty) t ==> ty IN types_in t`,
  CHEAT_TAC);;

let subterm_typeof_types_in = prove
 (`!t1 t2 name args. RTC subtype1 (holSyntax_Tyapp name args) (typeof t1)
  /\ RTC subterm1 t1 t2 /\ welltyped t2 /\ ~(name = (implode "fun")) ==>
      (?ty2. RTC subtype1 (holSyntax_Tyapp name args) ty2 /\ ty2 IN
        types_in t2)`,
  CHEAT_TAC);;

(* a type matching algorithm, based on the implementation in HOL4 *)

let tymatch_def,tymatch_ind = define_guess
  `tymatch x1 x2 sids =
     match (x1,x2) with
       ([],[]) -> SOME sids
     | ([],_) -> NONE
     | (_,[]) -> NONE
     | (CONS (holSyntax_Tyvar name) ps,CONS ty obs) ->
      (let (s,ids) = sids in
      let v = REV_ASSOCD (holSyntax_Tyvar name) s (holSyntax_Tyvar name) in
      match (if v = holSyntax_Tyvar name then
             if MEM name ids then SOME v else NONE
           else SOME v) with NONE -> if v = ty then tymatch ps obs (s,CONS
             name ids) else tymatch ps obs (CONS (ty,v) s,ids)
       | SOME ty1 -> if ty1 = ty then tymatch ps obs sids else NONE)
     | (CONS (holSyntax_Tyapp c1 a1) ps,CONS (holSyntax_Tyapp c2 a2) obs) ->
      if c1 = c2 then tymatch (APPEND a1 ps) (APPEND a2 obs) sids else NONE
     | (_,_) -> NONE`;;

let arities_match_def,arities_match_ind = define_guess
  `arities_match x1' x2' =
     match (x1',x2') with
       ([],[]) -> T
     | ([],_) -> F
     | (_,[]) -> F
     | (CONS (holSyntax_Tyapp c1 a1) xs,CONS (holSyntax_Tyapp c2 a2) ys) ->
      ((c1 = c2) ==> arities_match a1 a2) /\ arities_match xs ys
     | (CONS _ xs,CONS _ ys) -> arities_match xs ys`;;

let arities_match_length = prove
 (`!l1 l2. arities_match l1 l2 ==> (LENGTH l1 = LENGTH l2)`,
  CHEAT_TAC);;

let arities_match_nil = prove
 (`(arities_match [] ls = (ls = [])) /\
    (arities_match ls [] = (ls = []))`,
  CHEAT_TAC);;
add_simp arities_match_nil;;

let arities_match_Tyvar = prove
 (`arities_match (CONS (holSyntax_Tyvar v) ps) (CONS ty obs) = arities_match
  ps obs`,
  CHEAT_TAC);;
add_simp arities_match_Tyvar;;

let arities_match_append = prove
 (`!l1 l2 l3 l4.
    arities_match l1 l2 /\ arities_match l3 l4 ==>
    arities_match (APPEND l1 l3) (APPEND l2 l4)`,
  CHEAT_TAC);;

let tymatch_SOME = prove
 (`!ps obs sids s' ids'.
     arities_match ps obs /\
      DISJOINT (set_of_list (MAP SND (FST sids))) (set_of_list (MAP
        holSyntax_Tyvar (SND sids))) /\
      (!name. ~(MEM (holSyntax_Tyvar name,holSyntax_Tyvar name) (FST sids)))
        /\
      ALL_DISTINCT (MAP SND (FST sids)) /\
      (tymatch ps obs sids = SOME (s',ids')) ==>
       (?s1 ids1.
         (s' = APPEND s1 (FST sids)) /\ (ids' = APPEND ids1 (SND sids)) /\
         DISJOINT (set_of_list (MAP SND s')) (set_of_list (MAP
           holSyntax_Tyvar ids')) /\
         (!name. ~(MEM (holSyntax_Tyvar name,holSyntax_Tyvar name) s')) /\
         ALL_DISTINCT (MAP SND s') /\
         (MAP (TYPE_SUBST s') ps = obs))`,
  CHEAT_TAC);;

let match_type_def = new_definition
  `match_type ty1 ty2 = OPTION_MAP FST (tymatch [ty1] [ty2] ([],[]))`;;

let type_ok_arities_match = prove
 (`!tys ty1 ty2.
    type_ok tys ty1 /\ type_ok tys ty2 ==> arities_match [ty1] [ty2]`,
  CHEAT_TAC);;

let match_type_SOME = prove
 (`!ty1 ty2 s. arities_match [ty1] [ty2] ==>
    (match_type ty1 ty2 = SOME s) ==>
    (TYPE_SUBST s ty1 = ty2)`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["Bool";
   "Equal";
   "Fun";
   "concl";
   "const_list";
   "subterm"];;

(* and the interface *)
let _ = unhide_overloads ();;
