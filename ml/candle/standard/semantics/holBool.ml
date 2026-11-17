(* ======================================================== *)
(*  holBool: ported from HOL4's
    candle/standard/semantics/holBoolScript.sml
    A definition theory, with 10 definitions and 10 theorems.
    Needed by holAxioms.ml, holConsistency.ml and
    holLightConsistency.ml.  *)
(* ======================================================== *)

(*
  Define semantics for the Boolean operations and show the definitions are
  correct.
*)

needs "basis/pure/mlstring.ml";;
needs "candle/set-theory/setSpec.ml";;
needs "candle/standard/semantics/holSemantics.ml";;
needs "candle/standard/semantics/holSemanticsExtra.ml";;
needs "candle/standard/syntax/holBoolSyntax.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "holBool"
  ["holBoolSyntax"; "holSemantics"; "holSemanticsExtra"; "holSyntax";
   "holSyntaxExtra"; "holSyntaxLib"; "setSpec"];;

let _ = do_list hide_constant ["And"; "Bool"; "Fun"; "Not"; "True"];;

let _ = do_list hide_constant ["mem"];;

(* HOL4 holBoolScript.sml:16: the ML values that the definitions below
   antiquote *)

(* HOL4 holBoolScript.sml:18: the overload p, which the port expands *)
(* HOL4 holBoolScript.sml:19: the overload FAp, which the port expands *)
(* HOL4 holBoolScript.sml:20: the overload q, which the port expands *)
(* HOL4 holBoolScript.sml:21: the overload FAq, which the port expands *)
(* HOL4 holBoolScript.sml:22: the overload r, which the port expands *)
(* HOL4 holBoolScript.sml:23: the overload FAr, which the port expands *)
(* HOL4 holBoolScript.sml:24: the overload f, which the port expands *)
(* HOL4 holBoolScript.sml:25: the overload A, which the port expands *)
(* HOL4 holBoolScript.sml:26: the overload P, which the port expands *)
(* HOL4 holBoolScript.sml:27: the overload x, which the port expands *)
(* HOL4 holBoolScript.sml:28: the overload FAx, which the port expands *)

(* HOL4 holBoolScript.sml:30-31: ML code, not ported *)

let bool_sig_instances = prove
 (`is_bool_sig sig ==>
    instance (SND sig) (i:(mlstring->'U list->'U)#(mlstring->'U list->'U))
      (implode
      "T") (holSyntax_Tyapp (implode "bool") []) = (K ((SND:(mlstring->'U
      list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i (implode "T")
      [])) /\
    instance (SND sig) i (implode "F") (holSyntax_Tyapp (implode "bool") []) =
      (K
      ((SND:(mlstring->'U list->'U)#(mlstring->'U list->'U)->mlstring->'U
      list->'U) i (implode "F") [])) /\
    instance (SND sig) i (implode "==>") ((\s t. holSyntax_Tyapp (implode
      "fun") [s;
      t]) (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp
      (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") [])
      (holSyntax_Tyapp (implode "bool") []))) = (K ((SND:(mlstring->'U
      list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i (implode
      "==>") [])) /\
    instance (SND sig) i (implode "/\\") ((\s t. holSyntax_Tyapp (implode
      "fun") [s;
      t]) (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp
      (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") [])
      (holSyntax_Tyapp (implode "bool") []))) = (K ((SND:(mlstring->'U
      list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i (implode
      "/\\") [])) /\
    instance (SND sig) i (implode "\\/") ((\s t. holSyntax_Tyapp (implode
      "fun") [s;
      t]) (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp
      (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") [])
      (holSyntax_Tyapp (implode "bool") []))) = (K ((SND:(mlstring->'U
      list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i (implode
      "\\/") [])) /\
    instance (SND sig) i (implode "~") ((\s t. holSyntax_Tyapp (implode "fun")
      [s;
      t]) (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp (implode
      "bool") [])) = (K ((SND:(mlstring->'U list->'U)#(mlstring->'U
      list->'U)->mlstring->'U list->'U) i (implode "~") [])) /\
    instance (SND sig) i (implode "!") ((\s t. holSyntax_Tyapp (implode "fun")
      [s;
      t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyvar
      (implode "A")) (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Tyapp
      (implode "bool") [])) = (\tau. (SND:(mlstring->'U list->'U)#(mlstring->'U
      list->'U)->mlstring->'U list->'U) i (implode "!") [tau (implode "A")]) /\
    instance (SND sig) i (implode "?") ((\s t. holSyntax_Tyapp (implode
      "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
      (holSyntax_Tyvar (implode "A")) (holSyntax_Tyapp (implode "bool") []))
      (holSyntax_Tyapp (implode "bool") [])) = (\tau. (SND:(mlstring->'U
      list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i (implode
      "?") [tau (implode "A")])`,
  CHEAT_TAC);;

let boolrel_def = new_definition
  `Boolrel0 (mem':'U->'U->bool) R' =
       ((abstract mem') ((two mem')) ((funspace mem') ((two mem')) ((two
         mem')))
            (\(holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool")
              [])). ((abstract mem') ((two mem')) ((two mem'))
               (\(holSyntax_Var (implode "q") (holSyntax_Tyapp (implode
                 "bool") [])). (boolean mem') (R' ((holSyntax_Var (implode
                 "p") (holSyntax_Tyapp (implode "bool") [])) = (setSpec_true
                 mem')) ((holSyntax_Var (implode "q") (holSyntax_Tyapp
                 (implode "bool") [])) = (setSpec_true mem')))))))`;;

(* HOL4 holBoolScript.sml:55: the overload Boolrel, which the port expands *)

let is_true_interpretation_def = new_definition
  `is_true_interpretation0 (mem':'U->'U->bool) gamma <=> (gamma:mlstring->'U
  list->'U) (interprets0 mem') (implode "T") on [] as K (setSpec_true mem')`;;

(* HOL4 holBoolScript.sml:61: the overload is_true_interpretation, which the
   port expands *)

let is_and_interpretation_def = new_definition
  `is_and_interpretation0 (mem':'U->'U->bool) gamma <=> gamma (interprets0
  mem') (implode "/\\") on [] as K ((Boolrel0 mem') (/\))`;;

(* HOL4 holBoolScript.sml:67: the overload is_and_interpretation, which the
   port expands *)

let is_implies_interpretation_def = new_definition
  `is_implies_interpretation0 (mem':'U->'U->bool) gamma <=> gamma
  (interprets0 mem') (implode "==>") on [] as K ((Boolrel0 mem') (==>))`;;

(* HOL4 holBoolScript.sml:73: the overload is_implies_interpretation, which
   the port expands *)

let is_forall_interpretation_def = new_definition
  `is_forall_interpretation0 (mem':'U->'U->bool) gamma <=> gamma
     (interprets0 mem') (implode "!") on [(implode "A")] as
        (\l. (abstract mem') ((funspace mem') (HD l) ((two mem'))) ((two
          mem'))
               (\(holSyntax_Var (implode "P") ((\s t. holSyntax_Tyapp
                 (implode "fun") [s; t]) (holSyntax_Tyvar (implode "A"))
                 (holSyntax_Tyapp (implode "bool") []))). (boolean mem')
                 (!(holSyntax_Var (implode "x") (holSyntax_Tyvar (implode
                 "A"))). (mem':'U->'U->bool) (holSyntax_Var (implode "x")
                 (holSyntax_Tyvar (implode "A"))) (HD l) ==> (holds mem')
                 (holSyntax_Var (implode "P") ((\s t. holSyntax_Tyapp
                 (implode "fun") [s; t]) (holSyntax_Tyvar (implode "A"))
                 (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Var
                 (implode "x") (holSyntax_Tyvar (implode "A"))))))`;;

(* HOL4 holBoolScript.sml:82: the overload is_forall_interpretation, which
   the port expands *)

let is_exists_interpretation_def = new_definition
  `is_exists_interpretation0 (mem':'U->'U->bool) gamma <=> gamma
     (interprets0 mem') (implode "?") on [(implode "A")] as
        (\l. (abstract mem') ((funspace mem') (HD l) ((two mem'))) ((two
          mem'))
               (\(holSyntax_Var (implode "P") ((\s t. holSyntax_Tyapp
                 (implode "fun") [s; t]) (holSyntax_Tyvar (implode "A"))
                 (holSyntax_Tyapp (implode "bool") []))). (boolean mem')
                 (?(holSyntax_Var (implode "x") (holSyntax_Tyvar (implode
                 "A"))). (mem':'U->'U->bool) (holSyntax_Var (implode "x")
                 (holSyntax_Tyvar (implode "A"))) (HD l) /\ (holds mem')
                 (holSyntax_Var (implode "P") ((\s t. holSyntax_Tyapp
                 (implode "fun") [s; t]) (holSyntax_Tyvar (implode "A"))
                 (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Var
                 (implode "x") (holSyntax_Tyvar (implode "A"))))))`;;

(* HOL4 holBoolScript.sml:91: the overload is_exists_interpretation, which
   the port expands *)

let is_or_interpretation_def = new_definition
  `is_or_interpretation0 (mem':'U->'U->bool) gamma <=> gamma (interprets0
  mem') (implode "\\/") on [] as K ((Boolrel0 mem') (\/))`;;

(* HOL4 holBoolScript.sml:97: the overload is_or_interpretation, which the
   port expands *)

let is_false_interpretation_def = new_definition
  `is_false_interpretation0 (mem':'U->'U->bool) gamma <=>
  (gamma:mlstring->'U list->'U) (interprets0 mem') (implode "F") on [] as K
  (setSpec_false mem')`;;

(* HOL4 holBoolScript.sml:103: the overload is_false_interpretation, which
   the port expands *)

let is_not_interpretation_def = new_definition
  `is_not_interpretation0 (mem':'U->'U->bool) gamma <=> gamma (interprets0
  mem') (implode "~") on [] as K ((abstract mem') ((two mem')) ((two mem'))
  (\(holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool") [])).
  (boolean mem') (~((holSyntax_Var (implode "p") (holSyntax_Tyapp (implode
  "bool") [])) = (setSpec_true mem')))))`;;

(* HOL4 holBoolScript.sml:109: the overload is_not_interpretation, which the
   port expands *)

(* HOL4 holBoolScript.sml:111-113: ML code, not ported *)

let is_bool_interpretation_def = new_definition
  `is_bool_interpretation0 (mem':'U->'U->bool) i <=>
     (is_std_interpretation0 mem') i /\
     (is_true_interpretation0 mem') ((SND:(mlstring->'U
       list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) /\
     (is_and_interpretation0 mem') ((SND:(mlstring->'U
       list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) /\
     (is_implies_interpretation0 mem') ((SND:(mlstring->'U
       list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) /\
     (is_forall_interpretation0 mem') ((SND:(mlstring->'U
       list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) /\
     (is_exists_interpretation0 mem') ((SND:(mlstring->'U
       list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) /\
     (is_or_interpretation0 mem') ((SND:(mlstring->'U
       list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) /\
     (is_false_interpretation0 mem') ((SND:(mlstring->'U
       list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) /\
     (is_not_interpretation0 mem') ((SND:(mlstring->'U
       list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i)`;;

(* HOL4 holBoolScript.sml:128: the overload is_bool_interpretation, which
   the port expands *)

let boolrel_in_funspace = prove
 (`is_set_theory (mem:'U->'U->bool) ==> (mem:'U->'U->bool) ((Boolrel0 mem) R)
  ((funspace mem) ((two mem)) ((funspace mem) ((two mem)) ((two mem))))`,
  CHEAT_TAC);;
add_simp boolrel_in_funspace;;

(* HOL4 holBoolScript.sml:137: ML code, not ported *)

(* HOL4 holBoolScript.sml:139-162: a proof *)

(* HOL4 holBoolScript.sml:164-187: a proof *)

let apply_boolrel = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!b1 b2 b3. (mem:'U->'U->bool) b1 ((two mem)) /\ (mem:'U->'U->bool) b2
      ((two mem)) /\ (b3 = (boolean mem) (R (b1 = (setSpec_true mem)) (b2 =
      (setSpec_true mem)))) ==> apply mem (apply mem ((Boolrel0 mem) R) b1)
      b2 = b3)`,
  CHEAT_TAC);;

let bool_has_bool_interpretation = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!ctxt i. theory_ok ((\(ctxt:holSyntax_update list).
      ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
      (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT
      (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt.
      FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt))
      ctxt)) ctxt)) (mk_bool_ctxt ctxt)) /\ models0 mem i
      ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list).
      ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
      ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt))
      ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
      (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
      (mk_bool_ctxt ctxt)) ==>
             (is_bool_interpretation0 mem) i)`,
  CHEAT_TAC);;

let extends_is_bool_interpretation = prove
 (`is_set_theory (mem:'U->'U->bool) /\ extends ctxt2 (mk_bool_ctxt ctxt) /\
    theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
      list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
      ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
      ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
      (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
      (mk_bool_ctxt ctxt)) /\ models0 mem i ((\(ctxt:holSyntax_update list).
      ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
      (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT
      (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt.
      FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt))
      ctxt)) ctxt)) ctxt2) ==>
    (is_bool_interpretation0 mem) i`,
  CHEAT_TAC);;

let termsem_implies = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!s i v p1 p2.
    (is_valuation0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
      types_of_upd ctxt)) ctxt)) s) ((FST:(mlstring->'U list->'U)#(mlstring->'U
      list->'U)->mlstring->'U list->'U) i) v /\
    (is_interpretation0 mem) s i /\
    (is_std_type_assignment0 mem) ((FST:(mlstring->'U
      list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) /\
    holSyntax_term_ok s p1 /\ holSyntax_term_ok s p2 /\
    typeof p1 = (holSyntax_Tyapp (implode "bool") []) /\ typeof p2 =
      (holSyntax_Tyapp (implode "bool") []) /\
    is_implies_sig ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
      ctxt)) ctxt)) s) /\ (is_implies_interpretation0 mem) ((SND:(mlstring->'U
      list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) ==>
    (termsem0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
      ctxt)) ctxt)) s) i v ((\p1 p2. holSyntax_Comb (holSyntax_Comb
      (holSyntax_Const (implode "==>") ((\s t. holSyntax_Tyapp (implode "fun")
      [s; t]) (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp
      (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") [])
      (holSyntax_Tyapp (implode "bool") [])))) p1) p2) p1 p2) =
    (boolean mem) ((termsem0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
      consts_of_upd ctxt)) ctxt)) s) i v p1 = (setSpec_true mem) ==>
             (termsem0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
               consts_of_upd ctxt)) ctxt)) s) i v p2 = (setSpec_true mem)))`,
  CHEAT_TAC);;

let termsem_forall = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!s i v (holSyntax_Var (implode "f") ((\s t. holSyntax_Tyapp (implode
      "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) ((\s t.
      holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool")
      []) (holSyntax_Tyapp (implode "bool") [])))) y b.
    (is_valuation0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
      types_of_upd ctxt)) ctxt)) s) ((FST:(mlstring->'U list->'U)#(mlstring->'U
      list->'U)->mlstring->'U list->'U) i) v /\
    (is_interpretation0 mem) s i /\
    (is_std_interpretation0 mem) i /\
    type_ok ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
      ctxt)) s) y /\ holSyntax_term_ok s b /\ typeof b = (holSyntax_Tyapp
      (implode "bool") []) /\
    is_forall_sig ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
      ctxt)) ctxt)) s) /\ (is_forall_interpretation0 mem) ((SND:(mlstring->'U
      list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) ==>
    (termsem0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
      ctxt)) ctxt)) s) i v ((\(holSyntax_Var (implode "x") (holSyntax_Tyvar
      (implode "A"))) ty (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode
      "bool") [])). holSyntax_Comb (holSyntax_Const (implode "!") ((\s t.
      holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode
      "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Tyapp
      (implode "bool") []))) (holSyntax_Abs (holSyntax_Var (holSyntax_Var
      (implode "x") (holSyntax_Tyvar (implode "A"))) ty) (holSyntax_Var
      (implode "p") (holSyntax_Tyapp (implode "bool") [])))) (holSyntax_Var
      (implode "f") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
      (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp (implode
      "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp
      (implode "bool") [])))) y b) =
    (boolean mem) (!(holSyntax_Var (implode "x") (holSyntax_Tyvar (implode
      "A"))). (mem:'U->'U->bool) (holSyntax_Var (implode "x") (holSyntax_Tyvar
      (implode "A"))) (typesem ((FST:(mlstring->'U list->'U)#(mlstring->'U
      list->'U)->mlstring->'U list->'U) i)
      ((FST:(mlstring->'U)#(mlstring#type->'U)->mlstring->'U) v) y) ==>
                 (termsem0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
                   consts_of_upd ctxt)) ctxt)) s) i
                   ((FST:(mlstring->'U)#(mlstring#type->'U)->mlstring->'U)
                   v,(((holSyntax_Var (implode "f") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool")
                   []) ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp
                   (implode "bool") [])))),y) =+ (holSyntax_Var (implode "x")
                   (holSyntax_Tyvar (implode "A"))))
                   ((SND:(mlstring->'U)#(mlstring#type->'U)->mlstring
                   #type->'U) v)) b = (setSpec_true mem)))`,
  CHEAT_TAC);;

let termsem_exists = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!s i v (holSyntax_Var (implode "f") ((\s t. holSyntax_Tyapp (implode
      "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) ((\s t.
      holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool")
      []) (holSyntax_Tyapp (implode "bool") [])))) y b.
    (is_valuation0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
      types_of_upd ctxt)) ctxt)) s) ((FST:(mlstring->'U list->'U)#(mlstring->'U
      list->'U)->mlstring->'U list->'U) i) v /\
    (is_interpretation0 mem) s i /\
    (is_std_interpretation0 mem) i /\
    type_ok ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
      ctxt)) s) y /\ holSyntax_term_ok s b /\ typeof b = (holSyntax_Tyapp
      (implode "bool") []) /\
    is_exists_sig ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
      ctxt)) ctxt)) s) /\ (is_exists_interpretation0 mem) ((SND:(mlstring->'U
      list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) ==>
    (termsem0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
      ctxt)) ctxt)) s) i v ((\(holSyntax_Var (implode "x") (holSyntax_Tyvar
      (implode "A"))) ty (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode
      "bool") [])). holSyntax_Comb (holSyntax_Const (implode "?") ((\s t.
      holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode
      "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Tyapp
      (implode "bool") []))) (holSyntax_Abs (holSyntax_Var (holSyntax_Var
      (implode "x") (holSyntax_Tyvar (implode "A"))) ty) (holSyntax_Var
      (implode "p") (holSyntax_Tyapp (implode "bool") [])))) (holSyntax_Var
      (implode "f") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
      (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp (implode
      "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp
      (implode "bool") [])))) y b) =
    (boolean mem) (?(holSyntax_Var (implode "x") (holSyntax_Tyvar (implode
      "A"))). (mem:'U->'U->bool) (holSyntax_Var (implode "x") (holSyntax_Tyvar
      (implode "A"))) (typesem ((FST:(mlstring->'U list->'U)#(mlstring->'U
      list->'U)->mlstring->'U list->'U) i)
      ((FST:(mlstring->'U)#(mlstring#type->'U)->mlstring->'U) v) y) /\
                 (termsem0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
                   consts_of_upd ctxt)) ctxt)) s) i
                   ((FST:(mlstring->'U)#(mlstring#type->'U)->mlstring->'U)
                   v,(((holSyntax_Var (implode "f") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool")
                   []) ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp
                   (implode "bool") [])))),y) =+ (holSyntax_Var (implode "x")
                   (holSyntax_Tyvar (implode "A"))))
                   ((SND:(mlstring->'U)#(mlstring#type->'U)->mlstring
                   #type->'U) v)) b = (setSpec_true mem)))`,
  CHEAT_TAC);;

let termsem_and = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!s i v p1 p2.
    (is_valuation0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
      types_of_upd ctxt)) ctxt)) s) ((FST:(mlstring->'U list->'U)#(mlstring->'U
      list->'U)->mlstring->'U list->'U) i) v /\
    (is_interpretation0 mem) s i /\
    (is_std_type_assignment0 mem) ((FST:(mlstring->'U
      list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) /\
    holSyntax_term_ok s p1 /\ holSyntax_term_ok s p2 /\
    typeof p1 = (holSyntax_Tyapp (implode "bool") []) /\ typeof p2 =
      (holSyntax_Tyapp (implode "bool") []) /\
    is_and_sig ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
      ctxt)) ctxt)) s) /\ (is_and_interpretation0 mem) ((SND:(mlstring->'U
      list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) ==>
    (termsem0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
      ctxt)) ctxt)) s) i v ((\p1 p2. holSyntax_Comb (holSyntax_Comb
      (holSyntax_Const (implode "/\\") ((\s t. holSyntax_Tyapp (implode "fun")
      [s; t]) (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp
      (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") [])
      (holSyntax_Tyapp (implode "bool") [])))) p1) p2) p1 p2) =
    (boolean mem) ((termsem0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
      consts_of_upd ctxt)) ctxt)) s) i v p1 = (setSpec_true mem) /\
             (termsem0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
               consts_of_upd ctxt)) ctxt)) s) i v p2 = (setSpec_true mem)))`,
  CHEAT_TAC);;

let termsem_not = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
    (!s i v p1.
    (is_valuation0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
      types_of_upd ctxt)) ctxt)) s) ((FST:(mlstring->'U list->'U)#(mlstring->'U
      list->'U)->mlstring->'U list->'U) i) v /\
    (is_interpretation0 mem) s i /\
    (is_std_type_assignment0 mem) ((FST:(mlstring->'U
      list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) /\
    holSyntax_term_ok s p1 /\
    typeof p1 = (holSyntax_Tyapp (implode "bool") []) /\
    is_not_sig ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
      ctxt)) ctxt)) s) /\ (is_not_interpretation0 mem) ((SND:(mlstring->'U
      list->'U)#(mlstring->'U list->'U)->mlstring->'U list->'U) i) ==>
    (termsem0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
      ctxt)) ctxt)) s) i v ((\(holSyntax_Var (implode "p") (holSyntax_Tyapp
      (implode "bool") [])). holSyntax_Comb (holSyntax_Const (implode "~") ((\s
      t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
      "bool") []) (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Var
      (implode "p") (holSyntax_Tyapp (implode "bool") []))) p1) =
    (boolean mem) (~((termsem0 mem) ((\ctxt. alist_to_fmap ((\ctxt. FLAT
      (MAP consts_of_upd ctxt)) ctxt)) s) i v p1 = (setSpec_true mem))))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["And";
   "Bool";
   "Fun";
   "Not";
   "True";
   "mem"];;

(* and the interface *)
let _ = unhide_overloads ();;
