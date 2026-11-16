(* ======================================================== *)
(*  holSoundness: ported from HOL4's
    candle/standard/semantics/holSoundnessScript.sml
    A definition theory, with no definitions and 11 theorems.
    Needed by holConsistency.ml, holExtension.ml and
    holLightConsistency.ml.  *)
(* ======================================================== *)

(*
  Proves soundness of the inference system: any provable sequent is valid.
*)

needs "basis/pure/mlstring.ml";;
needs "candle/set-theory/setSpec.ml";;
needs "candle/standard/semantics/holSemantics.ml";;
needs "candle/standard/semantics/holSemanticsExtra.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "holSoundness"
  ["holSemantics"; "holSemanticsExtra"; "holSyntax"; "holSyntaxExtra";
   "holSyntaxLib"; "setSpec"];;

let _ = do_list hide_constant ["Bool"; "True"];;

let _ = do_list hide_constant ["mem"];;

(* HOL4 holSoundnessScript.sml:13: the ML values that the definitions below
   antiquote *)

let binary_inference_rule = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!thy h1 h2 p1 p2 q.
    has_type q (holSyntax_Tyapp (implode "bool") []) /\ holSyntax_term_ok
      (FST thy) q /\
    (!i v. (is_structure0 mem) (FST thy)
      i v /\
           (termsem0 mem) (SND (FST thy)) i v p1 = (setSpec_true mem) /\
           (termsem0 mem) (SND (FST thy)) i v p2 = (setSpec_true mem) ==>
           (termsem0 mem) (SND (FST thy)) i v q = (setSpec_true mem))
             /\ entails0 mem (thy,h1) p1 /\ entails0 mem (thy,h2) p2 ==>
             entails0 mem (thy,term_union h1 h2) q)`,
  CHEAT_TAC);;

let ABS_correct = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!thy x ty h l r.
    ~(EX (VFREE_IN (holSyntax_Var x ty)) h) /\ type_ok (FST (FST thy)) ty
      /\ entails0 mem (thy,h) ((===) l r) ==> entails0 mem (thy,h) ((===)
      (holSyntax_Abs (holSyntax_Var x ty) l) (holSyntax_Abs (holSyntax_Var x
      ty) r)))`,
  CHEAT_TAC);;

let ASSUME_correct = prove
 (`!thy p.
      theory_ok thy /\ has_type p (holSyntax_Tyapp (implode "bool") [])
        /\ holSyntax_term_ok (FST thy) p ==> entails0 mem (thy,[p]) p`,
  CHEAT_TAC);;

let BETA_correct = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!thy x ty t.
      theory_ok thy /\ type_ok (FST (FST thy)) ty /\ holSyntax_term_ok
        (FST thy) t ==> entails0 mem
        (thy,[]) ((===) (holSyntax_Comb (holSyntax_Abs (holSyntax_Var x ty)
        t) (holSyntax_Var x ty)) t))`,
  CHEAT_TAC);;

let DEDUCT_ANTISYM_correct = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!thy h1 p1 h2 p2. entails0 mem (thy,h1) p1 /\ entails0 mem (thy,h2) p2
      ==>
      entails0 mem (thy,
       term_union (term_remove p2 h1)
                  (term_remove p1 h2)) ((===) p1 p2))`,
  CHEAT_TAC);;

let EQ_MP_correct = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!thy h1 h2 p q p'. entails0 mem (thy,h1) ((===) p q) /\ entails0 mem
      (thy,h2) p' /\ ACONV p p' ==> entails0 mem (thy,term_union h1 h2) q)`,
  CHEAT_TAC);;

let INST_correct = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!thy h c.
      (!s s'. MEM (s',s) ilist ==>
              (?x ty. (s = holSyntax_Var x ty) /\ has_type s' ty
                /\ holSyntax_term_ok (FST thy) s')) /\ entails0 mem
                (thy,h) c ==> entails0 mem (thy,term_image (VSUBST ilist) h)
                (VSUBST ilist c))`,
  CHEAT_TAC);;

let INST_TYPE_correct = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!thy h c.
      ALL (type_ok (FST (FST thy))) (MAP FST tyin) /\ entails0 mem (thy,h) c
        ==>
        entails0 mem (thy,term_image (holSyntax_INST tyin) h) (holSyntax_INST
        tyin c))`,
  CHEAT_TAC);;

let MK_COMB_correct = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!thy h1 h2 l1 r1 l2 r2.
      entails0 mem (thy,h1) ((===) l1 r1) /\ entails0 mem (thy,h2) ((===) l2
        r2) /\
      welltyped (holSyntax_Comb l1 l2) ==> entails0 mem (thy,term_union h1
        h2) ((===) (holSyntax_Comb l1 l2) (holSyntax_Comb r1 r2)))`,
  CHEAT_TAC);;

let REFL_correct = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!thy t.
      theory_ok thy /\ holSyntax_term_ok (FST thy) t ==> entails0 mem (thy,[])
        ((===) t t))`,
  CHEAT_TAC);;

let proves_sound = prove
 (`is_set_theory (mem:'U->'U->bool) ==> (!thyh c. (|-) thyh c ==> entails0
  mem thyh c)`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["Bool";
   "True";
   "mem"];;

(* and the interface *)
let _ = unhide_overloads ();;
