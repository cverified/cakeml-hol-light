(* ======================================================== *)
(*  collapse: ported from HOL4's
    examples/algorithms/unification/triangular/first-order/
      collapseScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

needs "lib/subst.ml";;
needs "lib/term.ml";;
needs "lib/walk.ml";;
needs "lib/walkstar.ml";;
(* HOL4 ancestors outside the port: finite_map pred_set *)

let collapse_def = cake_define
  `collapse s = FUN_FMAP (\v. walkstar s (term_Var v)) (FDOM s)`;;
