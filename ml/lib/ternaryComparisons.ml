(* ======================================================== *)
(*  ternaryComparisons: ported from HOL4's
    src/sort/ternaryComparisonsScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

let ordering_INDUCT,ordering_RECURSION = define_datatype
  "ordering = LESS | EQUAL | GREATER";;
