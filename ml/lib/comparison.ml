(* ======================================================== *)
(*  comparison: ported from HOL4's
    src/finite_maps/comparisonScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 8 files of the port.  *)
(* ======================================================== *)

needs "lib/ternaryComparisons.ml";;
needs "lib/toto.ml";;

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: option pair string list
   arithmetic *)
(* HOL4 comparisonScript.sml:13: the overload Less, which the port
   expands *)
(* HOL4 comparisonScript.sml:14: the overload Equal, which the port
   expands *)
(* HOL4 comparisonScript.sml:15: the overload Greater, which the port
   expands *)

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

(* HOL4 comparisonScript.sml:68: the overload num_cmp, which the port
   expands *)
