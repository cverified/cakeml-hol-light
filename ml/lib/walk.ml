(* ======================================================== *)
(*  walk: ported from HOL4's
    examples/algorithms/unification/triangular/first-order/
      walkScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 6 files of the port.  *)
(* ======================================================== *)

needs "lib/subst.ml";;
needs "lib/term.ml";;

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
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

let walk_def = new_definition
  `walk s t = (match t with term_Var v -> vwalk s v | t -> t)`;;
