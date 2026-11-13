(* ======================================================== *)
(*  sorting: ported from HOL4's
    src/sort/sortingScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 22 files of the port.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: rich_list combin pair relation
   list arithmetic pred_set *)

let PERM_DEF = cake_define
  `PERM L1 L2 = (!x. FILTER ((=) x) L1 = FILTER ((=) x) L2)`;;

let SORTED_DEF = cake_define_list
  [`SORTED R [] = T`;
   `SORTED R [x] = T`;
   `SORTED R (x :: y :: rst) <=> R x y /\ SORTED R (y :: rst)`];;

let SORTS_DEF = cake_define
  `SORTS f R <=> (!l. PERM l (f R l) /\ SORTED R (f R l))`;;

let PART_DEF = cake_define_list
  [`PART P [] l1 l2 = (l1,l2)`;
   `PART P (h :: rst) l1 l2 =
              (if P h then PART P rst (h :: l1) l2 else PART P
                rst l1 (h :: l2))`];;

let PARTITION_DEF = cake_define
  `PARTITION P l = PART P l [] []`;;
