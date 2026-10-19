(* ======================================================== *)
(*  location: ported from HOL4's
    examples/formal-languages/context-free/locationScript.sml  *)
(* ======================================================== *)

let locn_INDUCT,locn_RECURSION = define_datatype
  "locn = UNKNOWNpt | EOFpt | POSN (num) (num)";;

let locnrow_def = cake_define
  `locnrow (POSN r c) = r`;;

let locn_rowupdate_def = cake_define
  `locn_rowupdate f (POSN r c) = POSN (f r) c`;;

let locncol_def = cake_define
  `locncol (POSN r c) = c`;;
let locn_colupdate_def = cake_define
  `locn_colupdate f (POSN r c) = POSN r (f c)`;;

let locs_INDUCT,locs_RECURSION = define_datatype
  "locs = Locs (locn) (locn)";;

(* HOL4 locationScript.sml:35: the overload end_locn, which the port
   expands *)
(* HOL4 locationScript.sml:36: the overload unknown_locn, which the
   port expands *)

let unknown_loc_def = cake_define
  `unknown_loc = Locs UNKNOWNpt UNKNOWNpt`;;

let locnle_def = cake_define
  `locnle l1 l2 <=>
     l1 = l2 \/
     l1 = UNKNOWNpt \/
     l2 = EOFpt \/ ~(l2 = UNKNOWNpt) /\ ~(l1 = EOFpt) /\
     (locnrow l1 < locnrow l2 \/ locnrow l1 = locnrow l2 /\
       locncol l1 < locncol l2)`;;

let locsle_def = cake_define
  `locsle (Locs l1 _1) (Locs l2 _2) <=> locnle l1 l2`;;

let merge_locs_def = cake_define
  `merge_locs (Locs l1 l2) (Locs l3 l4) = Locs l1 l4`;;

let merge_list_locs_def = cake_define
  `merge_list_locs x1 =
        match x1 with
          [] -> unknown_loc
        | (h :: []) -> h
        | (h1 :: h2 :: []) -> merge_locs h1 h2
        | (h1 :: h2 :: t) -> merge_list_locs (h1 :: t)`;;
