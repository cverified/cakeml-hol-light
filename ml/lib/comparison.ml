(* ======================================================== *)
(*  comparison: ported from HOL4's
    src/finite_maps/comparisonScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 32 files of the port.  *)
(* ======================================================== *)

needs "lib/ternaryComparisons.ml";;
needs "lib/toto.ml";;

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: option pair string list
   arithmetic *)
hol4_overload "Less" "LESS";;
hol4_overload "Equal" "EQUAL";;
hol4_overload "Greater" "GREATER";;

let good_cmp_def = new_definition
  `good_cmp cmp <=>
     (!x. cmp x x = EQUAL) /\
     (!x y. cmp x y = EQUAL ==> cmp y x = EQUAL) /\
     (!x y. cmp x y = GREATER <=> cmp y x = LESS) /\
     (!x y z. cmp x y = EQUAL /\ cmp y z = LESS ==> cmp x z = LESS)
       /\
     (!x y z. cmp x y = LESS /\ cmp y z = EQUAL ==> cmp x z = LESS)
       /\
     (!x y z. cmp x y = EQUAL /\ cmp y z = EQUAL ==> cmp x z = EQUAL)
       /\
     (!x y z. cmp x y = LESS /\ cmp y z = LESS ==> cmp x z = LESS)`;;

(* HOL4 comparisonScript.sml:54-56: the overload list_cmp, which the
   port expands *)

(* HOL4 comparisonScript.sml:58: the overload pair_cmp, which the
   port expands *)

hol4_overload "num_cmp" "num_compare";;
