(* ======================================================== *)
(*  holConsistency: ported from HOL4's
    candle/standard/semantics/holConsistencyScript.sml
    A definition theory, with 3 definitions and 10 theorems.  Needed
    by holLightConsistency.ml and x64BootstrapProof.ml.  *)
(* ======================================================== *)

(*
  Proves consistency of the inference system: starting from any context with a
  model, any context reached by non-axiomatic extensions has both provable and
  unprovable sequents. And the base case: the HOL contexts (initial context
  with no axioms, with all but infinity axiom, with all three axioms) have
  models (under suitable assumptions).
*)

needs "basis/pure/mlstring.ml";;
needs "candle/set-theory/setSpec.ml";;
needs "candle/standard/semantics/holAxioms.ml";;
needs "candle/standard/semantics/holBool.ml";;
needs "candle/standard/semantics/holExtension.ml";;
needs "candle/standard/semantics/holSemantics.ml";;
needs "candle/standard/semantics/holSemanticsExtra.ml";;
needs "candle/standard/semantics/holSoundness.ml";;
needs "candle/standard/syntax/holAxiomsSyntax.ml";;
needs "candle/standard/syntax/holBoolSyntax.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "holConsistency"
  ["holAxioms"; "holAxiomsSyntax"; "holBool"; "holBoolSyntax";
   "holExtension"; "holSemantics"; "holSemanticsExtra"; "holSoundness";
   "holSyntax"; "holSyntaxExtra"; "holSyntaxLib"; "setSpec"];;

let _ = do_list hide_constant ["mem"];;

(* HOL4 holConsistencyScript.sml:18: the ML values that the definitions
   below antiquote *)

let consistent_theory_def = new_definition
  `consistent_theory thy <=> (|-) (thy,[]) ((===) (holSyntax_Var (implode "x")
  (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Var (implode "x")
  (holSyntax_Tyapp (implode "bool") []))) /\
       ~((|-) (thy,[]) ((===) (holSyntax_Var (implode "x")
         (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Var (implode "y")
         (holSyntax_Tyapp (implode "bool") []))))`;;

let proves_consistent = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!thy. theory_ok thy /\ (?i. models0 mem i thy) ==>
      consistent_theory thy)`,
  CHEAT_TAC);;

let init_ctxt_has_model = prove
 (`is_set_theory (mem:'U->'U->bool) ==> (?i. models0 mem i
  ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list). ((\ctxt.
  alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
  alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt))
  ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd
  upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) init_ctxt))`,
  CHEAT_TAC);;

let min_hol_consistent = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!ctxt. extends ctxt init_ctxt /\ (!p. MEM (NewAxiom p) ctxt ==> MEM
      (NewAxiom p) init_ctxt) ==>
      consistent_theory ((\(ctxt:holSyntax_update list).
        ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
        (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
        FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
        ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
        upd)) ctxt)) ctxt)) ctxt)) ctxt))`,
  CHEAT_TAC);;

let fhol_ctxt_def = new_definition
  `fhol_ctxt = mk_select_ctxt (mk_eta_ctxt (mk_bool_ctxt init_ctxt))`;;

let fhol_extends_bool = prove
 (`extends fhol_ctxt (mk_bool_ctxt init_ctxt)`,
  CHEAT_TAC);;

(* HOL4 holConsistencyScript.sml:113-154: a proof *)

let fhol_has_model = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!ctxt. extends ctxt fhol_ctxt /\
      (!p. MEM (NewAxiom p) ctxt ==> MEM (NewAxiom p) fhol_ctxt) ==>
      theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
        list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
        ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP
        (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt))
        ctxt)) ctxt) /\ (?i. models0 mem i ((\(ctxt:holSyntax_update list).
        ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
        (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
        FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
        ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
        upd)) ctxt)) ctxt)) ctxt)) ctxt)))`,
  CHEAT_TAC);;

let fhol_consistent = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!ctxt. extends ctxt fhol_ctxt /\
      (!p. MEM (NewAxiom p) ctxt ==> MEM (NewAxiom p) fhol_ctxt) ==>
      consistent_theory ((\(ctxt:holSyntax_update list).
        ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
        (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
        FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
        ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
        upd)) ctxt)) ctxt)) ctxt)) ctxt))`,
  CHEAT_TAC);;

let hol_ctxt_def = new_definition
  `hol_ctxt = mk_infinity_ctxt fhol_ctxt`;;

let hol_extends_fhol = prove
 (`extends hol_ctxt fhol_ctxt`,
  CHEAT_TAC);;

let hol_extends_bool = prove
 (`extends hol_ctxt (mk_bool_ctxt init_ctxt)`,
  CHEAT_TAC);;

let hol_has_model = prove
 (`is_set_theory (mem:'U->'U->bool) /\ (?inf'. is_infinite (mem:'U->'U->bool)
  inf') ==>
    (!ctxt. extends ctxt hol_ctxt /\
      (!p. MEM (NewAxiom p) ctxt ==> MEM (NewAxiom p) hol_ctxt) ==>
      theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
        list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
        ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP
        (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt))
        ctxt)) ctxt) /\ (?i. models0 mem i ((\(ctxt:holSyntax_update list).
        ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
        (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
        FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
        ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
        upd)) ctxt)) ctxt)) ctxt)) ctxt)))`,
  CHEAT_TAC);;

let hol_consistent = prove
 (`is_set_theory (mem:'U->'U->bool) /\ (?inf'. is_infinite (mem:'U->'U->bool)
  inf') ==>
    (!ctxt. extends ctxt hol_ctxt /\
      (!p. MEM (NewAxiom p) ctxt ==> MEM (NewAxiom p) hol_ctxt) ==>
      consistent_theory ((\(ctxt:holSyntax_update list).
        ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
        (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
        FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
        ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
        upd)) ctxt)) ctxt)) ctxt)) ctxt))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["mem"];;

(* and the interface *)
let _ = unhide_overloads ();;
