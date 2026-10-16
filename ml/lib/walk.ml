(* ======================================================== *)
(*  walk: ported from HOL4's
    examples/algorithms/unification/triangular/first-order/
      walkScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

needs "lib/subst.ml";;
needs "lib/term.ml";;
(* HOL4 ancestors outside the port: finite_map relation alist
   arithmetic pred_set rich_list list *)

let VWALKR_RULES,VWALKR_INDUCT,VWALKR_CASES =
  new_inductive_definition
  `(!s v. FLOOKUP s v = NONE ==> VWALKR s v (term_Var v)) /\
   (!s v t. FLOOKUP s v = SOME t /\ (!u. ~(t = term_Var u))
      ==> VWALKR s v t) /\
   (!s v u r. FLOOKUP s v = SOME (term_Var u) /\ VWALKR s u r
      ==> VWALKR s v r)`;;

let vwalk_def = new_definition
  `vwalk s v = @r. VWALKR s v r`;;

let walk_def = cake_define
  `walk s t = (match t with term_Var v -> vwalk s v | t -> t)`;;
hol4_overload "walk" "walk";;
