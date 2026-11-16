(* ======================================================== *)
(*  cfMonad: ported from HOL4's
    translator/monadic/cfMonadScript.sml
    A definition theory, with no definitions and 15 theorems.
    Needed by CommandLineProof.ml.  *)
(* ======================================================== *)

(*
  Proves a connection between the monadic translator's ArrowP
  judgement and CF's app judgement.
*)

needs "basis/pure/mlstring.ml";;
needs "characteristic/cfApp.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "characteristic/cfStore.ml";;
needs "lib/set_sep.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_translator.ml";;
needs "translator/monadic/ml_monad_translator.ml";;
needs "translator/monadic/ml_monad_translatorBase.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "cfMonad"
  ["cfHeapsBase"; "cfStore"; "cfTactics"; "evaluate"; "ml_monad_translator";
   "ml_monad_translatorBase"; "ml_translator"; "semanticPrimitives"];;

let _ = do_list hide_constant ["C"; "fv"];;
(* HOL4 ancestors outside the port: pred_set *)

(* Theorems to convert monadic specifications to cf specifications *)

(* HOL4 cfMonadScript.sml:19: ML code, not ported *)

(*********** Comes from cfLetAutoLib.sml ***********************************************)
(* [dest_pure_fact]
   Deconstruct a pure fact (a heap predicate of the form &P) *)
(* HOL4 cfMonadScript.sml:24-30: the ML values that the definitions below
   antiquote *)
(***************************************************************************************)

(* HOL4 cfMonadScript.sml:33-42: ML code, not ported *)
          (* For some strange reason, AC_CONV doesn't work *)
(* HOL4 cfMonadScript.sml:44-48: ML code, not ported *)

(* HOL4 cfMonadScript.sml:50-54: ML code, not ported *)

(* TODO: use EXTRACT_PURE_FACT_CONV to rewrite EXTRACT_PURE_FACTS_TAC *)
(* HOL4 cfMonadScript.sml:57-65: a proof *)
(***********************************************************************************************)

(* [local] *)
let REFS_PRED_lemma = prove
 (`SPLIT (st2heap (p:('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list) st) (h1,h2) /\ H refs h1 ==> REFS_PRED (H,p) refs st`,
  CHEAT_TAC);;

(* [local] *)
let HPROP_SPLIT3 = prove
 (`(H1 * H2 * H3) h ==> (?h1 h2 h3. SPLIT3 h (h1,h2,h3) /\ H1 h1 /\ H2 h2
  /\ H3 h3)`,
  CHEAT_TAC);;

(* [local] *)
let HPROP_SPLIT3_clock0 = prove
 (`(H1 * H2 * H3) (st2heap p st) ==>
   (?h1 h2 h3. SPLIT3 (st2heap p (semanticPrimitives_state_clock_fupd (K
     0) st)) (h1,h2,h3) /\ H1 h1 /\ H2 h2 /\ H3 h3)`,
  CHEAT_TAC);;

(* [local] *)
let REFS_PRED_from_SPLIT = prove
 (`!state (st:'ffi semanticPrimitives_state) H p h1 h2.
    H state h1 ==>
    SPLIT (st2heap p st) (h1,h2) ==>
    REFS_PRED (H,p) state st`,
  CHEAT_TAC);;

let ArrowP_PURE_to_app = prove
 (`!A B f fv' x1 xv1 xv2 xvl H Q ro state p.
     A x1 xv1 ==>
     (!gv. B (f x1) gv ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) gv
       (CONS xv2 xvl) (H state) (Q state)) ==>
     ArrowP ro (H,p) (PURE A) (PURE B) f fv' ==>
     app p fv' (CONS xv1 (CONS xv2 xvl)) (H state) (Q state)`,
  CHEAT_TAC);;

let ArrowP_MONAD_to_app = prove
 (`!A B C' f fv' H x xv ro refs p.
     A x xv ==>
     ArrowP ro (H,p) (PURE A) (MONAD B C') f fv' ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) fv'
       [xv] (H refs)
     (POSTve
        (\rv. SEP_EXISTS (\refs' r. H refs' *
              &(f x refs = (M_success r,refs')) * &(B r rv)))
        (\ev. SEP_EXISTS (\refs' e. H refs' *
              &(f x refs = (M_failure e,refs')) * &(C' e ev))))`,
  CHEAT_TAC);;

let ArrowP_MONAD_EqSt_to_app = prove
 (`!A B C' f fv' H x xv ro refs p.
     A x xv ==>
     ArrowP ro (H,p) (EqSt (PURE A) refs) (MONAD B C') f fv' ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) fv'
       [xv] (H refs)
     (POSTve
          (\rv. SEP_EXISTS (\refs' r. H refs' *
                &(f x refs = (M_success r,refs')) * &(B r rv)))
          (\ev. SEP_EXISTS (\refs' e. H refs' *
                &(f x refs = (M_failure e,refs')) * &(C' e ev))))`,
  CHEAT_TAC);;

let st2heap_with_clock = prove
 (`// TODO: move
   st2heap p (semanticPrimitives_state_clock_fupd (K c) s) = st2heap p s`,
  CHEAT_TAC);;
add_simp st2heap_with_clock;;

let SPLIT3_IMP_STAR_STAR = prove
 (`// TODO: move
   !x s1 s2 s3 p1 p2 p3.
     p1 s1 /\ p2 s2 /\ p3 s3 /\ SPLIT3 x (s1,s2,s3) ==> (p1 * p2 * p3) x`,
  CHEAT_TAC);;

(* GC_T *)
let cfMonad_GC_T = prove
 (`// TODO: move
   !x. GC x`,
  CHEAT_TAC);;

let st2heap_new_refs_UNION = prove
 (`// TODO: move
   !(st:'ffi semanticPrimitives_state) new_refs p.
       ?x. (st2heap p (semanticPrimitives_state_refs_fupd (K (APPEND
         (semanticPrimitives_state_refs st) new_refs)) st) = st2heap p st UNION
         x) /\
           DISJOINT (st2heap p st) x`,
  CHEAT_TAC);;

(* HOL4 cfMonadScript.sml:258-353: a theorem whose statement the port cannot
   state yet: EvalM_from_app_gen *)

(* HOL4 cfMonadScript.sml:355-373: a theorem whose statement the port cannot
   state yet: EvalM_from_app *)

(* HOL4 cfMonadScript.sml:375-468: a theorem whose statement the port cannot
   state yet: EvalM_from_app_unit_gen *)

(* HOL4 cfMonadScript.sml:470-489: a theorem whose statement the port cannot
   state yet: EvalM_from_app_unit *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["C";
   "fv"];;

(* and the interface *)
let _ = unhide_overloads ();;
