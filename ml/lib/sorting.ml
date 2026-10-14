(* ======================================================== *)
(*  sorting: ported from HOL4's
    src/sort/sortingScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)
(* HOL4 ancestors outside the port: rich_list combin pair relation
   list arithmetic pred_set *)

let PART_DEF = cake_define
  `(PART P [] l1 l2 = (l1,l2)) /\ (PART P (h :: rst) l1 l2 =
       (if P h then PART P rst (h :: l1) l2 else PART P rst l1 (h
         :: l2)))`;;

let PARTITION_DEF = cake_define
  `PARTITION P l = PART P l [] []`;;
