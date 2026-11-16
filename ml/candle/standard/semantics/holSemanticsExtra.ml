(* ======================================================== *)
(*  holSemanticsExtra: ported from HOL4's
    candle/standard/semantics/holSemanticsExtraScript.sml
    A definition theory, with 1 definition and 45 theorems.  Needed
    by holAxioms.ml, holBool.ml, holConsistency.ml, holExtension.ml,
    holLightConsistency.ml and holSoundness.ml.  *)
(* ======================================================== *)

(*
  Some lemmas about the semantics.
*)

needs "basis/pure/mlstring.ml";;
needs "candle/set-theory/setSpec.ml";;
needs "candle/standard/semantics/holSemantics.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "misc/misc.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "holSemanticsExtra"
  ["holSemantics"; "holSyntax"; "holSyntaxExtra"; "holSyntaxLib"; "setSpec"];;

let _ = do_list hide_constant ["Bool"; "Equal"; "Fun"; "subterm"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["vars","vars"];;

let _ = do_list hide_constant ["mem"];;

(* HOL4 holSemanticsExtraScript.sml:16: the ML values that the definitions
   below antiquote *)

let is_std_interpretation_is_type = prove
 (`(is_std_interpretation0 mem) i ==> (is_std_type_assignment0 mem) (FST i)`,
  CHEAT_TAC);;

(* typesem *)

(* HOL4 holSemanticsExtraScript.sml:26-42: a theorem whose statement the
   port cannot state yet: typesem_inhabited *)

(* HOL4 holSemanticsExtraScript.sml:44-51: a theorem whose statement the
   port cannot state yet: typesem_Fun *)

(* HOL4 holSemanticsExtraScript.sml:53-59: a theorem whose statement the
   port cannot state yet: typesem_Bool *)

(* HOL4 holSemanticsExtraScript.sml:61-69: a theorem whose statement the
   port cannot state yet: typesem_TYPE_SUBST *)

(* HOL4 holSemanticsExtraScript.sml:71-80: a theorem whose statement the
   port cannot state yet: typesem_tyvars *)

(* HOL4 holSemanticsExtraScript.sml:82-98: a theorem whose statement the
   port cannot state yet: typesem_consts *)

(* termsem *)

(* HOL4 holSemanticsExtraScript.sml:102-158: a theorem whose statement the
   port cannot state yet: termsem_typesem *)

(* HOL4 holSemanticsExtraScript.sml:160-170: a theorem whose statement the
   port cannot state yet: termsem_typesem_matchable *)

let termsem_consts = prove
 (`!tmsig i v tm i'.
      welltyped tm /\
      (!name ty. VFREE_IN (holSyntax_Const name ty) tm ==>
                 instance tmsig i' name ty
                   ((FST:(mlstring->'U)#(mlstring#type->'U)->mlstring->'U) v) =
                 instance tmsig i name ty
                   ((FST:(mlstring->'U)#(mlstring#type->'U)->mlstring->'U) v))
                   /\
      (!t. RTC subterm1 t tm ==>
         typesem ((FST:(mlstring->'U list->'U)#(mlstring->'U
           list->'U)->mlstring->'U list->'U) i')
           ((FST:(mlstring->'U)#(mlstring#type->'U)->mlstring->'U) v) (typeof
           t) =
         typesem ((FST:(mlstring->'U list->'U)#(mlstring->'U
           list->'U)->mlstring->'U list->'U) i)
           ((FST:(mlstring->'U)#(mlstring#type->'U)->mlstring->'U) v) (typeof
           t)) ==>
      (termsem0 mem) tmsig i' v tm = (termsem0 mem) tmsig i v tm`,
  CHEAT_TAC);;

(* HOL4 holSemanticsExtraScript.sml:193-197: ML code, not ported *)

(* HOL4 holSemanticsExtraScript.sml:199-224: a theorem whose statement the
   port cannot state yet: termsem_Equal *)

(* equations *)

let termsem_equation = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!sig i v s t tmenv.
    (is_structure0 mem) sig i v /\
    holSyntax_term_ok sig ((===) s t) /\
    tmenv = SND sig ==> (termsem0 mem) tmenv i v ((===) s t) = (boolean mem)
      ((termsem0 mem) tmenv i v s = (termsem0 mem) tmenv i v t))`,
  CHEAT_TAC);;

(* aconv *)

let termsem_raconv = prove
 (`!env tp. RACONV env tp ==>
      (!Gamma i v1 v2.
        (FST v1 = FST v2) /\
        (!x1 ty1 x2 ty2.
          ALPHAVARS env (holSyntax_Var x1 ty1,holSyntax_Var x2 ty2) ==>
            ((termsem0 mem) Gamma i v1 (holSyntax_Var x1 ty1) =
             (termsem0 mem) Gamma i v2 (holSyntax_Var x2 ty2))) /\
        ALL (\(x,y). welltyped x /\ welltyped y /\ typeof x = typeof y) env
          /\
        welltyped (FST tp) /\ welltyped (SND tp) ==>
        (termsem0 mem) Gamma i v1 (FST tp) = (termsem0 mem) Gamma i v2
          (SND tp))`,
  CHEAT_TAC);;

let termsem_aconv = prove
 (`!Gamma i v t1 t2. ACONV t1 t2 /\ welltyped t1 /\ welltyped t2 ==>
  (termsem0 mem) Gamma i v t1 = (termsem0 mem) Gamma i v t2`,
  CHEAT_TAC);;

(* semantics only depends on valuation of free variables *)

let termsem_frees = prove
 (`!Gamma i t v1 v2.
      welltyped t /\ FST v1 = FST v2 /\
      (!x ty. VFREE_IN (holSyntax_Var x ty) t ==> SND v1 (x,ty) = SND v2
        (x,ty)) ==> (termsem0 mem) Gamma i v1 t = (termsem0 mem) Gamma i v2 t`,
  CHEAT_TAC);;

(* HOL4 holSemanticsExtraScript.sml:315-324: a theorem whose statement the
   port cannot state yet: typesem_frees *)

let termsem_tyfrees = prove
 (`!Gamma i t v1 v2 tmenv.
      holSyntax_term_ok Gamma t /\
      SND v1 = SND v2 /\
      (!a. MEM a (tvars t) ==> FST v1 a = FST v2 a) /\
      tmenv = (\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) Gamma ==> (termsem0 mem) tmenv i v1 t = (termsem0 mem)
        tmenv i v2 t`,
  CHEAT_TAC);;

(* semantics of substitution *)

let termsem_simple_subst = prove
 (`!tm ilist.
      welltyped tm /\
      DISJOINT (set_of_list (bv_names tm)) {y | ?ty u. VFREE_IN
        (holSyntax_Var y ty) u /\ MEM u (MAP FST ilist)} /\
      (!s s'. MEM (s',s) ilist ==> (?x ty. s = holSyntax_Var x ty
        /\ has_type s' ty)) ==>
      (!Gamma i v.
        (termsem0 mem) Gamma i v (simple_subst ilist tm) =
        (termsem0 mem) Gamma i
          (FST v,UPDATE_LIST (SND v)
                  (MAP ((holSyntax_dest_var ## (termsem0 mem) Gamma i v) o
                    (\(s',s). (s,s')))
                      (REVERSE ilist)))
          tm)`,
  CHEAT_TAC);;

let termsem_VSUBST = prove
 (`!tm ilist.
     welltyped tm /\
     (!s s'. MEM (s',s) ilist ==> (?x ty. s = holSyntax_Var x ty /\ has_type
       s' ty)) ==>
     (!Gamma i v.
      (termsem0 mem) Gamma i v (VSUBST ilist tm) =
      (termsem0 mem) Gamma i (FST v,UPDATE_LIST (SND v)
                   (MAP ((holSyntax_dest_var ## (termsem0 mem) Gamma i v) o
                     (\(s',s). (s,s')))
                     (REVERSE ilist))) tm)`,
  CHEAT_TAC);;

(* semantics of instantiation *)

let termsem_simple_inst = prove
 (`!Gamma tm tyin tmenv.
      welltyped tm /\ holSyntax_term_ok Gamma tm /\
      ALL_DISTINCT (bv_names tm) /\
      DISJOINT (set_of_list (bv_names tm)) {x | ?ty. VFREE_IN (holSyntax_Var
        x ty) tm} /\
      tmenv = (\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
        ctxt)) Gamma ==>
      (!i v.
        (termsem0 mem) tmenv i v (simple_inst tyin tm) =
        (termsem0 mem) tmenv i
          ((\x. typesem (FST i) (FST v) (TYPE_SUBST tyin (holSyntax_Tyvar
            x))),
           (\(x,ty). SND v (x,TYPE_SUBST tyin ty)))
          tm)`,
  CHEAT_TAC);;

let termsem_INST = prove
 (`!Gamma tm tyin tmenv.
      holSyntax_term_ok Gamma tm /\ tmenv = (\ctxt. alist_to_fmap ((\ctxt.
        FLAT (MAP consts_of_upd ctxt)) ctxt)) Gamma ==>
      (!i v.
        (termsem0 mem) tmenv i v (holSyntax_INST tyin tm) =
        (termsem0 mem) tmenv i
          ((\x. typesem (FST i) (FST v) (TYPE_SUBST tyin (holSyntax_Tyvar
            x))),
           (\(x,ty). SND v (x,TYPE_SUBST tyin ty)))
          tm)`,
  CHEAT_TAC);;

(* extending the context doesn't change the semantics *)

let termsem_extend = prove
 (`!tyenv tmenv tyenv' tmenv' tm.
      tmenv SUBMAP tmenv' /\
      holSyntax_term_ok (tyenv,tmenv) tm ==>
      (!i v. (termsem0 mem) tmenv' i v tm =
            (termsem0 mem) tmenv i v tm)`,
  CHEAT_TAC);;

(* HOL4 holSemanticsExtraScript.sml:569-575: a theorem whose statement the
   port cannot state yet: is_valuation_reduce *)

let satisfies_extend = prove
 (`!tyenv tmenv tyenv' tmenv' tm i h c.
      tmenv SUBMAP tmenv' /\ tyenv SUBMAP tyenv' /\
      ALL (holSyntax_term_ok (tyenv,tmenv)) (CONS c h) /\ satisfies0 mem i
        ((tyenv,tmenv),h,c) ==> satisfies0 mem i ((tyenv',tmenv'),h,c)`,
  CHEAT_TAC);;

(* one interpretation being compatible with another in a signature *)

let equal_on_def = new_definition
  `equal_on (sig:(mlstring,num)fmap#(mlstring,type)fmap) i i' <=>
   (!name. name IN FDOM (FST sig) ==> (FST:(mlstring->'U
     list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i' name =
     (FST:(mlstring->'U list->'U)#(mlstring->'U list->'U)->mlstring->'U
     list->'U) i name) /\
   (!name. name IN FDOM (SND sig) ==> (SND:(mlstring->'U
     list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i' name =
     (SND:(mlstring->'U list->'U)#(mlstring->'U list->'U)->mlstring->'U
     list->'U) i name)`;;

let equal_on_refl = prove
 (`!sig i. equal_on sig i i`,
  CHEAT_TAC);;

let equal_on_sym = prove
 (`!sig i i'. equal_on sig i i' ==> equal_on sig i' i`,
  CHEAT_TAC);;

let equal_on_trans = prove
 (`!sig i1 i2 i3.
    equal_on sig i1 i2 /\ equal_on sig i2 i3 ==> equal_on sig i1 i3`,
  CHEAT_TAC);;

let equal_on_interprets = prove
 (`!sig i1 i2 name args ty m.
      equal_on sig i1 i2 /\
      (SND:(mlstring->'U list->'U)#(mlstring->'U list->'U)->mlstring->'U
        list->'U) i1 (interprets0 mem) name on args as m /\
      (FLOOKUP (SND sig) name = SOME ty) /\
      type_ok (FST sig) ty /\
      (set_of_list (holSyntax_tyvars ty) = set_of_list args) ==>
      (SND:(mlstring->'U list->'U)#(mlstring->'U list->'U)->mlstring->'U
        list->'U) i2 (interprets0 mem) name on args as m`,
  CHEAT_TAC);;

let equal_on_reduce = prove
 (`!ls ctxt i i'.
    equal_on ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap
      ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap
      ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) (APPEND ls ctxt)) i
      i' /\
                 DISJOINT (FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
                   types_of_upd ctxt)) ctxt)) ls)) (FDOM ((\ctxt. alist_to_fmap
                   ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt)) /\
                 DISJOINT (FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
                   consts_of_upd ctxt)) ctxt)) ls)) (FDOM ((\ctxt.
                   alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
                   ctxt)) ctxt)) ==> equal_on ((\(ctxt:holSyntax_update
                   list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
                   types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap
                   ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt))
                   ctxt) i i'`,
  CHEAT_TAC);;

(* semantics only depends on interpretation of things in the term's signature *)

(* HOL4 holSemanticsExtraScript.sml:641-655: a theorem whose statement the
   port cannot state yet: typesem_sig *)

let termsem_sig = prove
 (`!tm Gamma i v i' tmenv.
      is_std_sig Gamma /\ holSyntax_term_ok Gamma tm /\ tmenv = (\ctxt.
        alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) Gamma
        /\ equal_on Gamma i i' ==>
      (termsem0 mem) tmenv i' v tm = (termsem0 mem) tmenv i v tm`,
  CHEAT_TAC);;

let satisfies_sig = prove
 (`!i i' sig h c.
    is_std_sig sig /\
    ALL (holSyntax_term_ok sig) (CONS c h) /\
    equal_on sig i i' /\ satisfies0 mem i (sig,h,c) ==> satisfies0 mem i'
      (sig,h,c)`,
  CHEAT_TAC);;

(* valuations exist *)

(* HOL4 holSemanticsExtraScript.sml:716-724: a theorem whose statement the
   port cannot state yet: term_valuation_exists *)

(* HOL4 holSemanticsExtraScript.sml:726-728: a theorem that HOL4 states as
   the value of an ML expression: is_type_valuation_exists *)

(* HOL4 holSemanticsExtraScript.sml:730-739: a theorem whose statement the
   port cannot state yet: valuation_exists *)

(* HOL4 holSemanticsExtraScript.sml:741-756: a theorem whose statement the
   port cannot state yet: extend_valuation_exists *)

let is_type_valuation_UPDATE_LIST = prove
 (`!t ls. (is_type_valuation0 mem) t /\ ALL ((\s. ?x. (mem:'U->'U->bool) x s) o
  SND) ls ==>
           (is_type_valuation0 mem) (UPDATE_LIST t ls)`,
  CHEAT_TAC);;

(* identity instance *)

let identity_instance = prove
 (`!tmenv (i:(mlstring->'U list->'U)#(mlstring->'U list->'U)) name ty tau.
  FLOOKUP tmenv name = SOME ty ==>
      instance tmenv i name ty = (\tau. (SND:(mlstring->'U
        list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i name (MAP
        tau (MAP implode (STRING_SORT (MAP explode (holSyntax_tyvars ty))))))`,
  CHEAT_TAC);;

(* special cases of interprets *)

(* HOL4 holSemanticsExtraScript.sml:780: the ML values that the definitions
   below antiquote *)
(* HOL4 holSemanticsExtraScript.sml:781-783: a theorem that HOL4 states as
   the value of an ML expression: interprets_nil *)

let interprets_one = prove
 (`i (interprets0 mem) name on [v] as f <=>
    (!x. (\s. ?x. (mem:'U->'U->bool) x s) x ==> (i name [x] = f [x]))`,
  CHEAT_TAC);;

(* for models, reducing the context *)

(* HOL4 holSemanticsExtraScript.sml:800-808: a theorem whose statement the
   port cannot state yet: is_type_assignment_reduce *)

(* HOL4 holSemanticsExtraScript.sml:810-818: a theorem whose statement the
   port cannot state yet: is_term_assignment_reduce *)

let is_interpretation_reduce = prove
 (`!i tyenv tmenv tyenv' tmenv'.
     tyenv SUBMAP tyenv' /\ tmenv SUBMAP tmenv' /\
     (is_interpretation0 mem) (tyenv',tmenv') i ==>
     (is_interpretation0 mem) (tyenv,tmenv) i`,
  CHEAT_TAC);;

let is_valuation_extend_sig = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!tyenv tyenv' tyass v.
    (is_valuation0 mem) tyenv tyass v /\
    (is_type_assignment0 mem) tyenv' tyass /\
    tyenv SUBMAP tyenv' ==>
    (?v'.
      ((FST:(mlstring->'U)#(mlstring#type->'U)->mlstring->'U) v' =
        (FST:(mlstring->'U)#(mlstring#type->'U)->mlstring->'U) v) /\
      (!ty. type_ok tyenv ty ==> (!x.
        (SND:(mlstring->'U)#(mlstring#type->'U)->mlstring#type->'U) v' (x,ty) =
        (SND:(mlstring->'U)#(mlstring#type->'U)->mlstring#type->'U) v (x,ty)))
        /\
      (is_valuation0 mem) tyenv' tyass v'))`,
  CHEAT_TAC);;

let satisfies_reduce = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!i tyenv tmenv tyenv' tmenv' h c.
      is_std_sig (tyenv,tmenv) /\
      tyenv SUBMAP tyenv' /\
      tmenv SUBMAP tmenv' /\
      ALL (holSyntax_term_ok (tyenv,tmenv)) (CONS c h) /\
      (is_type_assignment0 mem) tyenv' ((FST:(mlstring->'U
        list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i)
        /\ satisfies0 mem i ((tyenv',tmenv'),h,c) ==> satisfies0 mem i
        ((tyenv,tmenv),h,c))`,
  CHEAT_TAC);;

let models_reduce = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!i tyenv tmenv axs tyenv' tmenv' axs'.
     is_std_sig (tyenv,tmenv) /\
     tyenv SUBMAP tyenv' /\ tmenv SUBMAP tmenv' /\ (axs SUBSET axs')
       /\ models0 mem i ((tyenv',tmenv'),axs') /\
     (!p. p IN axs ==> (holSyntax_term_ok (tyenv,tmenv)) p) ==> models0
       mem i ((tyenv,tmenv),axs))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["Bool";
   "Equal";
   "Fun";
   "mem";
   "subterm"];;

(* and the interface *)
let _ = unhide_overloads ();;
