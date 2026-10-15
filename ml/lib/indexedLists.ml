(* ======================================================== *)
(*  indexedLists[bare]: ported from HOL4's
    src/list/src/indexedListsScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)
(* HOL4 ancestors outside the port: list rich_list *)

let findi_def = cake_define_list
  [`indexedLists_findi x [] = 0`;
   `indexedLists_findi x (h :: t) = (if x = h then 0 else 1 +
  indexedLists_findi x t)`];;
