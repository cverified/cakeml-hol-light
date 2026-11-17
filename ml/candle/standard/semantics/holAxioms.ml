(* ======================================================== *)
(*  holAxioms: ported from HOL4's
    candle/standard/semantics/holAxiomsScript.sml
    A definition theory, with 2 definitions and 6 theorems.  Needed
    by 12 files of the port.  *)
(* ======================================================== *)

(*
  Prove consistency of each of the axioms. (For the axiom of infinity, this
  requires an additional assumption on the set theory.)
*)

needs "basis/pure/mlstring.ml";;
needs "candle/set-theory/setSpec.ml";;
needs "candle/standard/semantics/holBool.ml";;
needs "candle/standard/semantics/holExtension.ml";;
needs "candle/standard/semantics/holSemantics.ml";;
needs "candle/standard/semantics/holSemanticsExtra.ml";;
needs "candle/standard/syntax/holAxiomsSyntax.ml";;
needs "candle/standard/syntax/holBoolSyntax.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "holAxioms"
  ["holAxiomsSyntax"; "holBool"; "holBoolSyntax"; "holExtension";
   "holSemantics"; "holSemanticsExtra"; "holSyntax"; "holSyntaxExtra";
   "holSyntaxLib"; "setSpec"];;

(* HOL4 holAxiomsScript.sml:15: the overload A, which the port expands *)
(* HOL4 holAxiomsScript.sml:16: the overload B, which the port expands *)
(* HOL4 holAxiomsScript.sml:17: the overload x, which the port expands *)
(* HOL4 holAxiomsScript.sml:18: the overload g, which the port expands *)
(* HOL4 holAxiomsScript.sml:19: the overload B, which the port expands *)
(* HOL4 holAxiomsScript.sml:20: the overload EXx, which the port expands *)
(* HOL4 holAxiomsScript.sml:21: the overload x1, which the port expands *)
(* HOL4 holAxiomsScript.sml:22: the overload FAx1, which the port expands *)
(* HOL4 holAxiomsScript.sml:23: the overload x2, which the port expands *)
(* HOL4 holAxiomsScript.sml:24: the overload FAx2, which the port expands *)
(* HOL4 holAxiomsScript.sml:25: the overload y, which the port expands *)
(* HOL4 holAxiomsScript.sml:26: the overload FAy, which the port expands *)

let _ = do_list hide_constant ["mem"];;

(* HOL4 holAxiomsScript.sml:30: the ML values that the definitions below
   antiquote *)

let eta_has_model = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!ctxt. is_std_sig ((\(ctxt:holSyntax_update list). ((\ctxt.
      alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
      alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt)
      ==>
      (!i. models0 mem i ((\(ctxt:holSyntax_update list).
        ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
        (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
        FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
        ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
        upd)) ctxt)) ctxt)) ctxt)) ctxt) ==> models0 mem i
        ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list).
        ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
        ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
        ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
        APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
        (mk_eta_ctxt ctxt))))`,
  CHEAT_TAC);;

let good_select_def = new_definition
  `good_select0 (mem':'U->'U->bool) select = (!ty p x. (mem':'U->'U->bool) x
  ty ==> (mem':'U->'U->bool) (select ty p) ty /\ (p x ==> p (select ty p)))`;;

(* HOL4 holAxiomsScript.sml:75: the overload good_select, which the port
   expands *)

let select_has_model_gen = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!ctxt.
      ~((implode "@") IN FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
        consts_of_upd ctxt)) ctxt)) ctxt)) /\
      is_implies_sig ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt) /\
      theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
        list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
        ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
        APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
        ctxt) ==>
      (!i select.
      models0 mem i ((\(ctxt:holSyntax_update list).
        ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
        (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
        FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
        ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
        upd)) ctxt)) ctxt)) ctxt)) ctxt) /\
        (is_implies_interpretation0 mem) ((SND:(mlstring->'U
          list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) /\
        (good_select0 mem) select ==> (?i'. equal_on
          ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
          (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
          FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt) i i' /\ models0
          mem i' ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
          list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
          ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
          ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP
          (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt))
          ctxt)) (mk_select_ctxt ctxt)) /\
             ((SND:(mlstring->'U list->'U)#(mlstring->'U
               list->'U)->mlstring->'U list->'U) i' (implode "@") =
                (\ls. (abstract mem) ((funspace mem) (HD ls) ((two mem)))
                  (HD ls)
                        (\p. select (HD ls) ((holds mem) p)))))))`,
  CHEAT_TAC);;

let base_select_def = new_definition
  `base_select0 (mem':'U->'U->bool) ty p =
     if (\s. ?x. (mem':'U->'U->bool) x s) ty then
       (match some (\x. (mem':'U->'U->bool) x ty /\ p x) with NONE -> (@x.
         (mem':'U->'U->bool) x ty) | SOME v -> v)
     else ARB`;;

(* HOL4 holAxiomsScript.sml:203: the overload base_select, which the port
   expands *)

let good_select_base_select = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (good_select0 mem) (base_select0 mem)`,
  CHEAT_TAC);;

let select_has_model = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!ctxt.
      ~((implode "@") IN FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
        consts_of_upd ctxt)) ctxt)) ctxt)) /\
      is_implies_sig ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt) /\
      theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
        list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
        ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
        APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
        ctxt) ==>
      (!i.
      models0 mem i ((\(ctxt:holSyntax_update list).
        ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
        (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
        FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
        ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
        upd)) ctxt)) ctxt)) ctxt)) ctxt) /\
        (is_implies_interpretation0 mem) ((SND:(mlstring->'U
          list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) ==>
          (?i'. equal_on ((\(ctxt:holSyntax_update list). ((\ctxt.
          alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
          ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
          ctxt)) ctxt)) ctxt) i i' /\ models0 mem i'
          ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list).
          ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
          ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
          ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP
          (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt))
          ctxt)) ctxt)) (mk_select_ctxt ctxt)))))`,
  CHEAT_TAC);;

(* HOL4 holAxiomsScript.sml:245: the overload h, which the port expands *)
(* HOL4 holAxiomsScript.sml:246: the overload Exh, which the port expands *)

(* HOL4 holAxiomsScript.sml:248-250: the ML values that the definitions
   below antiquote *)

(* HOL4 holAxiomsScript.sml:252-284: a proof *)

let infinity_has_model_gen = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!ctxt.
      theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
        list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
        ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
        APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
        ctxt) /\
      DISJOINT (FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt)) {(implode "ONE_ONE"),(implode "ONTO")}
        /\ ~((implode "ind") IN FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
        types_of_upd ctxt)) ctxt)) ctxt)) /\
      is_implies_sig ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt) /\
      is_and_sig ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt) /\
      is_forall_sig ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt) /\
      is_exists_sig ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt) /\
      is_not_sig ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt) ==>
      (!i inf'.
      models0 mem i ((\(ctxt:holSyntax_update list).
        ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
        (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
        FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
        ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
        upd)) ctxt)) ctxt)) ctxt)) ctxt) /\
          (is_implies_interpretation0 mem) ((SND:(mlstring->'U
            list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) /\
          (is_and_interpretation0 mem) ((SND:(mlstring->'U
            list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) /\
          (is_forall_interpretation0 mem) ((SND:(mlstring->'U
            list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) /\
          (is_exists_interpretation0 mem) ((SND:(mlstring->'U
            list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) /\
          (is_not_interpretation0 mem) ((SND:(mlstring->'U
            list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) /\
          is_infinite (mem:'U->'U->bool) inf' ==> (?i'. equal_on
            ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt.
            FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap
            ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt) i i'
            /\ models0 mem i' ((\(ctxt:holSyntax_update list).
            ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt.
            FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap
            ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt.
            set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
            (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) (mk_infinity_ctxt ctxt))
            /\
             ((FST:(mlstring->'U list->'U)#(mlstring->'U
               list->'U)->mlstring->'U list->'U) i' (implode "ind") [] =
               inf'))))`,
  CHEAT_TAC);;

let infinity_has_model = prove
 (`is_set_theory (mem:'U->'U->bool) /\ (?inf'. is_infinite (mem:'U->'U->bool)
  inf') ==>
    (!ctxt.
      theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
        list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
        ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
        APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
        ctxt) /\
      DISJOINT (FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt)) {(implode "ONE_ONE"),(implode "ONTO")}
        /\ ~((implode "ind") IN FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
        types_of_upd ctxt)) ctxt)) ctxt)) /\
      is_implies_sig ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt) /\
      is_and_sig ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt) /\
      is_forall_sig ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt) /\
      is_exists_sig ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt) /\
      is_not_sig ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt) ==>
      (!i.
      models0 mem i ((\(ctxt:holSyntax_update list).
        ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
        (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
        FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
        ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
        upd)) ctxt)) ctxt)) ctxt)) ctxt) /\ models0 mem i
        ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list).
        ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
        ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
        ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
        (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) ctxt) /\
          (is_implies_interpretation0 mem) ((SND:(mlstring->'U
            list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) /\
          (is_and_interpretation0 mem) ((SND:(mlstring->'U
            list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) /\
          (is_forall_interpretation0 mem) ((SND:(mlstring->'U
            list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) /\
          (is_exists_interpretation0 mem) ((SND:(mlstring->'U
            list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) /\
          (is_not_interpretation0 mem) ((SND:(mlstring->'U
            list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) ==>
            (?i'. equal_on ((\(ctxt:holSyntax_update list). ((\ctxt.
            alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
            ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
            ctxt)) ctxt)) ctxt)) ctxt) i i' /\ models0 mem i'
            ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list).
            ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
            ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
            consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
            ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
            (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) (mk_infinity_ctxt
            ctxt)))))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["mem"];;

(* and the interface *)
let _ = unhide_overloads ();;
