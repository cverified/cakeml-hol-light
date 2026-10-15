(* ======================================================== *)
(*  walkstar: ported from HOL4's
    examples/algorithms/unification/triangular/first-order/
      walkstarScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

needs "lib/subst.ml";;
needs "lib/term.ml";;
needs "lib/walk.ml";;
(* HOL4 ancestors outside the port: relation pair bag prim_rec
   finite_map pred_set *)

cake_declare "walkstar" `:(num,(A)term)fmap->(A)term->(A)term`;;

let walkstarR_def = cake_define
  `walkstarR s =
    inv_image ((LEX) (TC (mlt1 (TC (vR s)))) (MEASURE pair_count))
      (\t. (varb t,t))`;;
