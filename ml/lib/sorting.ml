(* ======================================================== *)
(*  sorting: ported from HOL4's
    src/sort/sortingScript.sml  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: rich_list combin pair relation
   list arithmetic pred_set *)

let PERM_DEF = new_definition
  `PERM L1 L2 = (!x. FILTER ((=) x) L1 = FILTER ((=) x) L2)`;;

let SORTED_DEF,SORTED_DEF_ind = define_guess
  [`SORTED R [] = T`;
   `SORTED R [x] = T`;
   `SORTED R (x :: y :: rst) <=> R x y /\ SORTED R (y :: rst)`];;

let SORTS_DEF = new_definition
  `SORTS f R <=> (!l. PERM l (f R l) /\ SORTED R (f R l))`;;

let PART_DEF,PART_DEF_ind = define_rec
  [`PART P [] l1 l2 = (l1,l2)`;
   `PART P (h :: rst) l1 l2 =
              (if P h then PART P rst (h :: l1) l2 else PART P
                rst l1 (h :: l2))`];;

let PARTITION_DEF = new_definition
  `PARTITION P l = PART P l [] []`;;
