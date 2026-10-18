(* ======================================================== *)
(*  sorting: ported from HOL4's
    src/sort/sortingScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 22 files of the port.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)
(* HOL4 ancestors outside the port: rich_list combin pair relation
   list arithmetic pred_set *)

let PERM_DEF = cake_define
  `PERM L1 L2 = (!x. FILTER ((=) x) L1 = FILTER ((=) x) L2)`;;

let SORTED_DEF = cake_define_list
  [`SORTED R [] = T`;
   `SORTED R [x] = T`;
   `SORTED R (x :: y :: rst) <=> R x y /\ SORTED R (y :: rst)`];;

let PART_DEF = cake_define_list
  [`PART P [] l1 l2 = (l1,l2)`;
   `PART P (h :: rst) l1 l2 =
              (if P h then PART P rst (h :: l1) l2 else PART P
                rst l1 (h :: l2))`];;

let PARTITION_DEF = cake_define
  `PARTITION P l = PART P l [] []`;;
