(* ======================================================== *)
(*  toto: ported from HOL4's
    src/finite_maps/totoScript.sml  *)
(* ======================================================== *)

needs "lib/ternaryComparisons.ml";;
(* HOL4 ancestors outside the port: pred_set relation pair arithmetic
   numeral string list set_relation *)

let TotOrd = cake_define
  `TotOrd (c:'a->'a->ordering) = (
      (!x y. (c x y = EQUAL) <=> (x = y)) /\
      (!x y. (c x y = GREATER) <=> (c y x = LESS)) /\
      (!x y z. (c x y = LESS) /\ (c y z = LESS) ==> (c x z =
        LESS)))`;;
