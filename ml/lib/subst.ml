(* ======================================================== *)
(*  subst: ported from HOL4's
    examples/algorithms/unification/triangular/first-order/
      substScript.sml  *)
(* ======================================================== *)

needs "lib/term.ml";;

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: pred_set relation finite_map
   While prim_rec arithmetic bag list *)

let rangevars_def = new_definition
  `rangevars s = BIGUNION (IMAGE vars (FRANGE s))`;;

let substvars_def = new_definition
  `substvars s = FDOM s UNION rangevars s`;;

let vR_def = new_definition
  `vR s y x = (match FLOOKUP s x with SOME t -> y IN vars t | _1 ->
  F)`;;

let wfs_def = new_definition
  `wfs s = WF (vR s)`;;

let subst_APPLY_def,subst_APPLY_ind = define_rec
  [`subst_APPLY s (term_Var v) = (match FLOOKUP s v with NONE ->
  (term_Var v:'a term) | SOME t -> t)`;
   `subst_APPLY s (term_Pair t1 t2) = term_Pair (subst_APPLY s t1)
  (subst_APPLY s t2)`;
   `subst_APPLY s (term_Const c) = (term_Const c:'a term)`];;
