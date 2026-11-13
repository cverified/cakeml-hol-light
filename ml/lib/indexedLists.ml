(* ======================================================== *)
(*  indexedLists: ported from HOL4's
    src/list/src/indexedListsScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 12 files of the port.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: list rich_list *)

let FOLDRi_def,FOLDRi_ind = define_rec
  [`FOLDRi f a [] = a`;
   `FOLDRi f a (h :: t) = f 0 h (FOLDRi (f o SUC) a t)`];;

let findi_def,findi_ind = define_rec
  [`indexedLists_findi x [] = 0`;
   `indexedLists_findi x (h :: t) = (if x = h then 0 else 1 +
  indexedLists_findi x t)`];;
hol4_overload "findi" "indexedLists_findi";;

let LIST_RELi_rules = cake_inductive
  `LIST_RELi R [] [] /\
   (!h1 h2 l1 l2.
      R (LENGTH l1) h1 h2 /\ LIST_RELi R l1 l2 ==>
      LIST_RELi R (l1 ++ [h1]) (l2 ++ [h2]))`;;
