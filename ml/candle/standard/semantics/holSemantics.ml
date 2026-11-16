(* ======================================================== *)
(*  holSemantics: ported from HOL4's
    candle/standard/semantics/holSemanticsScript.sml
    A definition theory, with 15 definitions and no theorems.
    Needed by 7 files of the port.  *)
(* ======================================================== *)

(*
  Define semantics for HOL sequents, in particular the notion of entailment
  i.e. valid sequents, which are those that satisfied by any model of the
  theory context.
*)

needs "basis/pure/mlstring.ml";;
needs "candle/set-theory/setSpec.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "holSemantics"
  ["holSyntax"; "holSyntaxExtra"; "setSpec"];;

let _ = do_list hide_constant ["mem"];;

(* HOL4 holSemanticsScript.sml:14: the ML values that the definitions below
   antiquote *)

(* HOL4 holSemanticsScript.sml:16-19: a proof *)

(* HOL4 holSemanticsScript.sml:21: the overload inhabited, which the port
   expands *)

(* A type assignment is a map from type operator names to semantic functions.
   Each function takes a list of sets representing the meanings of the
   arguments and returns the meaning of the applied operator. The assignment is
   with respect to a type signature, and is only constrained for defined type
   operators applied to the right number of non-empty arguments. *)

(* HOL4 holSemanticsScript.sml:29: the type abbreviation tyass, which the
   port expands *)

let is_type_assignment_def = new_definition
  `is_type_assignment0 (mem':'U->'U->bool) tysig (delta':mlstring->'U list->'U)
  <=>
     FEVERY
       (\(name,arity).
         !ls. LENGTH ls = arity /\ ALL (\s. ?x. mem:'U->'U->bool x s) ls ==>
              (\s. ?x. mem:'U->'U->bool x s) ((delta' name) ls))
       tysig`;;

(* HOL4 holSemanticsScript.sml:40: the overload is_type_assignment, which
   the port expands *)

(* A type valuation is a map from type variable names to non-empty sets. *)

(* HOL4 holSemanticsScript.sml:44: the type abbreviation tyval, which the
   port expands *)

let is_type_valuation_def = new_definition
  `is_type_valuation0 (mem':'U->'U->bool) (tau:mlstring->'U) <=> (!x. (\s.
  ?x. mem:'U->'U->bool x s) (tau x))`;;

(* HOL4 holSemanticsScript.sml:50: the overload is_type_valuation, which the
   port expands *)

(* Semantics of types. Simply applies the valuation and assignment. *)

(* HOL4 holSemanticsScript.sml:58-60: the tactic that proves the termination *)
let typesem_def,typesem_ind = define_guess
  `(typesem delta' (tau:mlstring->'U) (holSyntax_Tyvar s) = tau s) /\
   (typesem delta' (tau:mlstring->'U) (holSyntax_Tyapp name args) =
        (delta' name) (MAP (typesem delta' tau) args))`;;

(* A term assignment is a map from a constant name and a list of values for the
   free type variables to a value for the constant. The assignment is with
   respect to a signature and is only constrained for defined constants. *)

(* HOL4 holSemanticsScript.sml:66: the type abbreviation tmass, which the
   port expands *)

let is_term_assignment_def = new_definition
  `is_term_assignment0 (mem':'U->'U->bool) tmsig delta' (gamma:mlstring->'U
  list->'U) <=>
     FEVERY
       (\(name,ty).
         !tau. (is_type_valuation0 mem) tau ==> mem:'U->'U->bool (gamma name
           (MAP tau (MAP implode (STRING_SORT (MAP explode (holSyntax_tyvars
           ty)))))) (typesem delta' tau ty))
       tmsig`;;

(* HOL4 holSemanticsScript.sml:77: the overload is_term_assignment, which
   the port expands *)

(* A term valuation is a map from a variable to an element of its type. The
   result is not polymorphic: term valuations are specialised for particular
   type valuations. *)

(* HOL4 holSemanticsScript.sml:83: the type abbreviation tmval, which the
   port expands *)

let is_term_valuation_def = new_definition
  `is_term_valuation0 (mem':'U->'U->bool) tysig delta' tau
  (sigma:mlstring#type->'U) <=>
     (!v ty. type_ok tysig ty ==> mem:'U->'U->bool (sigma (v,ty))
       (typesem delta' tau ty))`;;

(* HOL4 holSemanticsScript.sml:90: the overload is_term_valuation, which the
   port expands *)

(* An interpretation is a pair of assignments.
   A valuation is a pair of valuations. *)

(* HOL4 holSemanticsScript.sml:95: the type abbreviation interpretation,
   which the port expands *)
(* HOL4 holSemanticsScript.sml:96: the overload tyaof, which the port
   expands *)
(* HOL4 holSemanticsScript.sml:97: the overload tmaof, which the port
   expands *)
(* HOL4 holSemanticsScript.sml:98: the type abbreviation valuation, which
   the port expands *)
(* HOL4 holSemanticsScript.sml:99: the overload tyvof, which the port
   expands *)
(* HOL4 holSemanticsScript.sml:100: the overload tmvof, which the port
   expands *)

let is_valuation_def = new_definition
  `is_valuation0 (mem':'U->'U->bool) tysig delta' v <=>
     (is_type_valuation0 mem)
       ((FST:(mlstring->'U)#(mlstring#type->'U)->mlstring->'U) v) /\
     (is_term_valuation0 mem) tysig delta'
       ((FST:(mlstring->'U)#(mlstring#type->'U)->mlstring->'U) v)
       ((SND:(mlstring->'U)#(mlstring#type->'U)->mlstring#type->'U) v)`;;

(* HOL4 holSemanticsScript.sml:108: the overload is_valuation, which the
   port expands *)

(* term assignment for instances of constants *)

(* HOL4 holSemanticsScript.sml:112-130: a proof *)

(* Semantics of terms. *)

let termsem_def,termsem_ind = define_guess
  `(termsem0 (mem':'U->'U->bool) (tmsig:(mlstring,type)fmap)
    (i:(mlstring->'U list->'U)#(mlstring->'U list->'U))
    (v:(mlstring->'U)#(mlstring#type->'U)) (holSyntax_Var x ty) =
    (SND:(mlstring->'U)#(mlstring#type->'U)->mlstring#type->'U) v (x,ty)) /\
   (termsem0 (mem':'U->'U->bool) (tmsig:(mlstring,type)fmap)
    (i:(mlstring->'U list->'U)#(mlstring->'U list->'U))
    (v:(mlstring->'U)#(mlstring#type->'U)) (holSyntax_Const name ty) =
    instance tmsig i name ty
    ((FST:(mlstring->'U)#(mlstring#type->'U)->mlstring->'U) v)) /\
   (termsem0 (mem':'U->'U->bool) (tmsig:(mlstring,type)fmap)
    (i:(mlstring->'U list->'U)#(mlstring->'U list->'U))
    (v:(mlstring->'U)#(mlstring#type->'U)) (holSyntax_Comb t1 t2) = apply
    mem (termsem0 (mem':'U->'U->bool) tmsig i v t1) (termsem0
    (mem':'U->'U->bool) tmsig i v t2)) /\
   (termsem0 (mem':'U->'U->bool) (tmsig:(mlstring,type)fmap) (i:(mlstring->'U
    list->'U)#(mlstring->'U list->'U)) (v:(mlstring->'U)#(mlstring#type->'U))
    (holSyntax_Abs (holSyntax_Var x ty) b) =
       (abstract mem) (typesem ((FST:(mlstring->'U list->'U)#(mlstring->'U
           list->'U)->mlstring->'U list->'U) i)
           ((FST:(mlstring->'U)#(mlstring#type->'U)->mlstring->'U) v) ty)
           (typesem ((FST:(mlstring->'U list->'U)#(mlstring->'U
           list->'U)->mlstring->'U list->'U) i)
           ((FST:(mlstring->'U)#(mlstring#type->'U)->mlstring->'U) v) (typeof
           b))
         (\m. termsem0 (mem':'U->'U->bool) tmsig i
             ((FST:(mlstring->'U)#(mlstring#type->'U)->mlstring->'U)
             v,((x,ty) =+ m)
             ((SND:(mlstring->'U)#(mlstring#type->'U)->mlstring#type->'U)
             v)) b))`;;

(* HOL4 holSemanticsScript.sml:144: the overload termsem, which the port
   expands *)

(* Satisfaction of sequents. *)

let satisfies_def = new_definition
  `satisfies0 (mem':'U->'U->bool) i
  ((sig:(mlstring,num)fmap#(mlstring,type)fmap),h,c) <=>
     (!v.
       (is_valuation0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
         types_of_upd ctxt)) ctxt)) sig) ((FST:(mlstring->'U
         list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) v /\
       ALL (\t. (termsem0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
         consts_of_upd ctxt)) ctxt)) sig) i v t = (setSpec_true mem)) h ==>
         (termsem0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
         consts_of_upd ctxt)) ctxt)) sig) i v c = (setSpec_true mem))`;;
(* HOL4 holSemanticsScript.sml:156: the overload satisfies, which the port
   expands *)

(* A interpretation of a theory is a pair of assignments to the constants and
   types in the theory. *)

let is_interpretation_def = new_definition
  `is_interpretation0 (mem':'U->'U->bool)
  (sig:(mlstring,num)fmap#(mlstring,type)fmap) int' <=>
     (is_type_assignment0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
       types_of_upd ctxt)) ctxt)) sig) ((FST:(mlstring->'U
       list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) int') /\
     (is_term_assignment0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
       consts_of_upd ctxt)) ctxt)) sig) ((FST:(mlstring->'U
       list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) int')
       ((SND:(mlstring->'U list->'U)#(mlstring->'U list->'U)->mlstring->'U
       list->'U) int')`;;

(* HOL4 holSemanticsScript.sml:167: the overload is_interpretation, which
   the port expands *)

(* The assignments are standard if they interpret fun, bool, and = according
   to the standard model. *)

let is_std_type_assignment_def = new_definition
  `is_std_type_assignment0 (mem':'U->'U->bool) (delta':mlstring->'U list->'U)
  <=>
     (!dom rng. delta' (implode "fun") [dom; rng] = (funspace mem) dom rng)
       /\
     (delta' (implode "bool") [] = ((two mem)))`;;

(* HOL4 holSemanticsScript.sml:178: the overload is_std_type_assignment,
   which the port expands *)
let interprets_def = new_definition
  `interprets0 (mem':'U->'U->bool) gamma name vs f <=> (!tau.
  (is_type_valuation0 mem) tau ==> gamma name (MAP tau vs) = f (MAP tau vs))`;;

(* HOL4 holSemanticsScript.sml:195: the overload interprets, which the port
   expands *)

(* PORT FAILED: Definition is_std_interpretation_def: unparsed input at 137:
   '\\' *)
(* HOL4 holSemanticsScript.sml:197-203: the definition *)

(* HOL4 holSemanticsScript.sml:205: the overload is_std_interpretation,
   which the port expands *)

(* A model of a theory is a standard interpretation that satisfies all the
   axioms. *)

let models_def = new_definition
  `models0 (mem':'U->'U->bool) i
  (thy:((mlstring,num)fmap#(mlstring,type)fmap)#(holSyntax_term->bool)) <=>
     (is_interpretation0 mem) ((\(ctxt:holSyntax_update list). ((\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) thy)
       i /\
     (is_std_interpretation0 mem) i /\
     (!p. p IN ((\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
       (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) thy) ==>
       satisfies0 mem i ((\(ctxt:holSyntax_update list). ((\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
       ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
       ctxt)) ctxt)) thy,[],p))`;;
(* HOL4 holSemanticsScript.sml:218: the overload models, which the port
   expands *)

(* Validity of sequents. *)

let entails_def = new_definition
  `entails0 (mem':'U->'U->bool) (thy,h) c <=>
     theory_ok thy /\
     ALL (holSyntax_term_ok ((\(ctxt:holSyntax_update list). ((\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt))
       thy)) (CONS c h) /\
     ALL (\p. has_type p (holSyntax_Tyapp (implode "bool") [])) (CONS c h)
       /\
     hypset_ok h /\
     (!i.
         models0 mem i thy ==> satisfies0 mem i ((\(ctxt:holSyntax_update
           list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd
           ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
           consts_of_upd ctxt)) ctxt)) ctxt)) thy,h,c))`;;
(* HOL4 holSemanticsScript.sml:233: the overload |=, which the port expands *)

(* Collect standard signature, standard interpretation and valuation up in one
   predicate *)

let is_structure_def = new_definition
  `is_structure0 (mem':'U->'U->bool) sig int' val' <=>
     is_std_sig sig /\
     (is_std_interpretation0 mem) int' /\
     (is_interpretation0 mem) sig int' /\
     (is_valuation0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
       types_of_upd ctxt)) ctxt)) sig) ((FST:(mlstring->'U
       list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) int') val'`;;

(* HOL4 holSemanticsScript.sml:246: the overload is_structure, which the
   port expands *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["mem"];;

(* and the interface *)
let _ = unhide_overloads ();;
