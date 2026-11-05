(* ======================================================== *)
(*  collapse: ported from HOL4's
    examples/algorithms/unification/triangular/first-order/
      collapseScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by unify.ml.  *)
(* ======================================================== *)

needs "lib/subst.ml";;
needs "lib/term.ml";;
needs "lib/walk.ml";;
needs "lib/walkstar.ml";;

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: finite_map pred_set *)

let collapse_def = cake_define
  `collapse s = FUN_FMAP (\v. walkstar s (term_Var v)) (FDOM s)`;;
