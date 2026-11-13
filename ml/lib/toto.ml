(* ======================================================== *)
(*  toto: ported from HOL4's
    src/finite_maps/totoScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 11 files of the port.  *)
(* ======================================================== *)

needs "lib/ternaryComparisons.ml";;

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: pred_set relation pair arithmetic
   numeral string list set_relation *)

let TotOrd = new_definition
  `TotOrd (c:'a->'a->ordering) = (
      (!x y. (c x y = EQUAL) <=> (x = y)) /\
      (!x y. (c x y = GREATER) <=> (c y x = LESS)) /\
      (!x y z. (c x y = LESS) /\ (c y z = LESS) ==> (c x z =
        LESS)))`;;
