(* ======================================================== *)
(*  comparison: ported from HOL4's
    src/finite_maps/comparisonScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 32 files of the port.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)
(* HOL4 ancestors outside the port: option pair string list
   arithmetic toto *)
hol4_overload "Less" "LESS";;
hol4_overload "Equal" "EQUAL";;
hol4_overload "Greater" "GREATER";;

hol4_overload "num_cmp" "num_compare";;
