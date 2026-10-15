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

cake_declare "vwalk" `:(num,(A)term)fmap->num->(A)term`;;

let walk_def = cake_define
  `walk s t = (match t with term_Var v -> vwalk s v | t -> t)`;;
