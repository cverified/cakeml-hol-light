(* ======================================================== *)
(*  comparison: ported from HOL4's
    src/finite_maps/comparisonScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)
(* HOL4 ancestors outside the port: option pair string list
   arithmetic toto *)
hol4_overload "Less" "LESS";;
hol4_overload "Equal" "EQUAL";;
hol4_overload "Greater" "GREATER";;

hol4_overload "num_cmp" "num_compare";;
