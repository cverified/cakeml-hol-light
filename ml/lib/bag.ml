(* ================================================================== *)
(*  HOL4's bagTheory, of which the port needs the definitions below:  *)
(*  a bag is the function that gives the number of times an element   *)
(*  occurs in it.                                                     *)
(* ================================================================== *)

let EMPTY_BAG = new_definition
  `EMPTY_BAG = (K 0:A->num)`;;

let BAG_INN = new_definition
  `BAG_INN (e:A) n b <=> b e >= n`;;

let SUB_BAG = new_definition
  `SUB_BAG b1 (b2:A->num) <=> !x n. BAG_INN x n b1 ==> BAG_INN x n b2`;;

let BAG_IN = new_definition
  `BAG_IN (e:A) b <=> BAG_INN e 1 b`;;

let BAG_UNION = new_definition
  `BAG_UNION b (c:A->num) = \x. b x + c x`;;

let BAG_DIFF = new_definition
  `BAG_DIFF b1 (b2:A->num) = \x. b1 x - b2 x`;;

let BAG_INSERT = new_definition
  `BAG_INSERT (e:A) b = (\x. if x = e then b e + 1 else b x)`;;

let BAG_INTER = new_definition
  `BAG_INTER b1 (b2:A->num) =
   (\x. if b1 x < b2 x then b1 x else b2 x)`;;

let BAG_MERGE = new_definition
  `BAG_MERGE b1 (b2:A->num) =
   (\x. if b1 x < b2 x then b2 x else b1 x)`;;

let SET_OF_BAG = new_definition
  `SET_OF_BAG (b:A->num) = \x. BAG_IN x b`;;

let BAG_OF_SET = new_definition
  `BAG_OF_SET (P:A->bool) = \x. if x IN P then 1 else 0`;;

let BAG_DISJOINT = new_definition
  `BAG_DISJOINT (b1:A->num) b2 <=>
   DISJOINT (SET_OF_BAG b1) (SET_OF_BAG b2)`;;

let BAG_ALL_DISTINCT = new_definition
  `BAG_ALL_DISTINCT (b:A->num) <=> !e. b e <= 1`;;

let FINITE_BAG = new_definition
  `FINITE_BAG (b:A->num) <=> FINITE (SET_OF_BAG b)`;;

(* the multiset order of HOL4's bagTheory, which the measure of
   the unification algorithm uses *)

let mlt1 = new_definition
  `mlt1 r (b1:A->num) b2 <=>
   FINITE_BAG b1 /\ FINITE_BAG b2 /\
   (?e rep res. b1 = BAG_UNION rep res /\
                b2 = BAG_UNION res (BAG_INSERT e EMPTY_BAG) /\
                (!e'. BAG_IN e' rep ==> r e' e))`;;

(* HOL4 has the multiset order itself as an abbreviation of the
   transitive closure of mlt1 (bagTheory's Overload mlt) *)

let mlt = new_definition
  `mlt (r:A->A->bool) = TC (mlt1 r)`;;

(* HOL4 writes the union of two bags as an infix *)

parse_as_infix("BAG_UNION",(16,"left"));;

(* the bag of the elements of a list, and the image of a bag under
   a function, for which HOL4 needs the size of a bag: it
   specifies that one with a relation and only for a finite bag,
   and the sum over the set of the bag is the same number *)

let LIST_TO_BAG = new_recursive_definition list_RECURSION
  `(LIST_TO_BAG [] = (EMPTY_BAG:A->num)) /\
   (LIST_TO_BAG (CONS (h:A) t) = BAG_INSERT h (LIST_TO_BAG t))`;;

let BAG_FILTER = new_definition
  `BAG_FILTER (P:A->bool) b = (\x. if P x then b x else 0)`;;

let BAG_CARD = new_definition
  `BAG_CARD (b:A->num) = nsum (SET_OF_BAG b) b`;;

let BAG_IMAGE = new_definition
  `BAG_IMAGE (f:A->B) b =
   (\e. let sb = BAG_FILTER (\e0. f e0 = e) b in
        if FINITE_BAG sb then BAG_CARD sb else 1)`;;
