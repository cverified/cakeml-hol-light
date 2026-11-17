(* ======================================================== *)
(*  holExtension: ported from HOL4's
    candle/standard/semantics/holExtensionScript.sml
    A definition theory, with 2 definitions and 7 theorems.  Needed
    by holAxioms.ml, holConsistency.ml and holLightConsistency.ml.  *)
(* ======================================================== *)

(*
  Proves soundness of the context extension rules: any model of a context can
  be extended to a model of the context obtained by applying one of the
  non-axiomatic context updates.
*)

needs "basis/pure/mlstring.ml";;
needs "candle/set-theory/setSpec.ml";;
needs "candle/standard/semantics/holSemantics.ml";;
needs "candle/standard/semantics/holSemanticsExtra.ml";;
needs "candle/standard/semantics/holSoundness.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "holExtension"
  ["holSemantics"; "holSemanticsExtra"; "holSoundness"; "holSyntax";
   "holSyntaxExtra"; "holSyntaxLib"; "mlstring"; "setSpec"];;

let _ = do_list hide_constant ["mem"];;

(* HOL4 holExtensionScript.sml:19: the ML values that the definitions below
   antiquote *)

(* HOL4 holExtensionScript.sml:21-26: the definition *)


(* HOL4 holExtensionScript.sml:29: the overload sound_update, which the port
   expands *)

let new_constant_correct = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!ctxt name ty.
     theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
       list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
       ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
       ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
       APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
       ctxt) /\ ~(name IN (FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
       consts_of_upd ctxt)) ctxt)) ctxt))) /\
     type_ok ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
       ctxt)) ctxt) ty ==>
     (sound_update0 mem) ctxt (NewConst name ty))`,
  CHEAT_TAC);;

let new_specification_correct = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!ctxt eqs prop.
     theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
       list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
       ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
       ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
       APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
       ctxt) /\ (|-) ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
       list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
       ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
       ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
       APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
       ctxt,MAP (\(s,t). (===) (holSyntax_Var s (typeof t)) t) eqs) prop /\
     ALL
       (\t. CLOSED t /\
            (!v. MEM v (tvars t) ==> MEM v (holSyntax_tyvars (typeof t))))
       (MAP SND eqs) /\
     (!x ty. VFREE_IN (holSyntax_Var x ty) prop ==>
               MEM (x,ty) (MAP (\(s,t). (s,typeof t)) eqs)) /\
     (!s. MEM s (MAP FST eqs) ==> ~(s IN (FDOM ((\ctxt. alist_to_fmap
       ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)))) /\
     ALL_DISTINCT (MAP FST eqs) ==>
    (sound_update0 mem) ctxt (ConstSpec eqs prop))`,
  CHEAT_TAC);;

let new_definition_correct = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!ctxt name tm.
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
      tm)) ==> (sound_update0 mem) ctxt ((\x t. ConstSpec [(x,t)] ((===)
      (holSyntax_Var x (typeof t)) t)) name tm))`,
  CHEAT_TAC);;

let new_type_correct = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!ctxt name arity.
     theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
       list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
       ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
       ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
       APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
       ctxt) /\ ~(name IN FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
       types_of_upd ctxt)) ctxt)) ctxt)) ==>
     (sound_update0 mem) ctxt (NewType name arity))`,
  CHEAT_TAC);;

let eqsh_def = new_definition
  `eqsh = (=)`;;
let new_type_definition_correct = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!ctxt name pred abs' rep witness. (|-) ((\(ctxt:holSyntax_update list).
      ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
      (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT
      (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt.
      FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt))
      ctxt)) ctxt)) ctxt,[]) (holSyntax_Comb pred witness) /\
    CLOSED pred /\ ~(name IN (FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
      types_of_upd ctxt)) ctxt)) ctxt))) /\ ~(abs' IN (FDOM ((\ctxt.
      alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)))
      /\ ~(rep IN (FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
      ctxt)) ctxt)) ctxt))) /\ ~(abs' = rep) ==>
    (sound_update0 mem) ctxt (TypeDefn name pred abs' rep))`,
  CHEAT_TAC);;
(* HOL4 holExtensionScript.sml:811: ML code, not ported *)

let updates_consistent = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!upd ctxt. updates upd ctxt ==>
      theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
        list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
        ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
        APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
        ctxt) /\ (!p. ~(upd = NewAxiom p)) ==>
      (sound_update0 mem) ctxt upd)`,
  CHEAT_TAC);;

let extends_consistent = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!ctxt1 ctxt2. extends ctxt2 ctxt1 ==>
      (!i.
        theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
          list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
          ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
          ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP
          (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt))
          ctxt)) ctxt1) /\ models0 mem i ((\(ctxt:holSyntax_update list).
          ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
          (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
          FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
          ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
          upd)) ctxt)) ctxt)) ctxt)) ctxt1) /\
          (!p. MEM (NewAxiom p) ctxt2 ==> MEM (NewAxiom p) ctxt1) ==>
        (?i'. equal_on ((\(ctxt:holSyntax_update list). ((\ctxt.
          alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
          ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
          ctxt)) ctxt)) ctxt1) i i' /\ models0 mem i'
          ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list).
          ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
          ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
          ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP
          (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt))
          ctxt)) ctxt)) ctxt2))))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["mem"];;

(* and the interface *)
let _ = unhide_overloads ();;
