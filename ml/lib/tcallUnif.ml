(* ======================================================== *)
(*  tcallUnif: ported from HOL4's
    examples/algorithms/unification/triangular/first-order/
      compilation/tcallUnifScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

needs "lib/rmfmap.ml";;
needs "lib/sptree.ml";;
needs "lib/subst.ml";;
needs "lib/unifDef.ml";;
needs "lib/walk.ml";;
needs "lib/walkstar.ml";;
(* HOL4 ancestors outside the port: pair While cps relation pred_set
   finite_map option *)

(* HOL4 tcallUnifScript.sml:270: the overload BAG_OF_LIST, which the
   port expands *)
