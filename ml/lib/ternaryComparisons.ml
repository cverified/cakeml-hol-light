(* ======================================================== *)
(*  ternaryComparisons: ported from HOL4's
    src/sort/ternaryComparisonsScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 11 files of the port.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;

let ordering_INDUCT,ordering_RECURSION = define_datatype
  "ordering = LESS | EQUAL | GREATER";;
let pair_compare_def = cake_define
  `pair_compare c1 c2 (a,b) (x,y) =
      (match c1 a x with
         EQUAL -> c2 b y | res -> res)`;;

let num_compare_def = cake_define
  `num_compare n1 n2 =
     (if n1 = n2 then
       EQUAL else if n1 < n2 then
       LESS else
       GREATER)`;;
let list_compare_def = cake_define
  `list_compare cmp l1 l2 =
        match (l1,l2) with
          ([],[]) -> EQUAL
        | ([],l2) -> LESS
        | (l1,[]) -> GREATER
        | ((x :: l1),(y :: l2)) ->
        (match cmp (x:'a) y with
          LESS -> LESS | EQUAL -> list_compare cmp l1 l2 | GREATER
            -> GREATER)`;;

let invert_comparison_def = cake_define_list
  [`invert_comparison GREATER = LESS`;
   `invert_comparison LESS = GREATER`;
   `invert_comparison EQUAL = EQUAL`];;
