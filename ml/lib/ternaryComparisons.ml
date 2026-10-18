(* ======================================================== *)
(*  ternaryComparisons: ported from HOL4's
    src/sort/ternaryComparisonsScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 8 files of the port.  *)
(* ======================================================== *)

let ordering_INDUCT,ordering_RECURSION = define_datatype
  "ordering = LESS | EQUAL | GREATER";;

let num_compare_def = cake_define
  `num_compare n1 n2 =
     (if n1 = n2 then
       EQUAL else if n1 < n2 then
       LESS else
       GREATER)`;;
