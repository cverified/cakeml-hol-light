(* ======================================================== *)
(*  location: ported from HOL4's
    examples/formal-languages/context-free/locationScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 15 files of the port.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;

let locn_INDUCT,locn_RECURSION = define_datatype
  "locn =
     UNKNOWNpt
   | EOFpt
   | POSN num num";;

let locnrow_def = define_general
  [`locnrow (POSN r c) = r`];;

let locn_rowupdate_def = define_general
  [`locn_rowupdate f (POSN r c) = POSN (f r) c`];;

let locncol_def = define_general
  [`locncol (POSN r c) = c`];;
let locn_colupdate_def = define_general
  [`locn_colupdate f (POSN r c) = POSN r (f c)`];;

let locs_INDUCT,locs_RECURSION = define_datatype
  "locs =
     Locs locn locn";;

(* HOL4 locationScript.sml:35: the overload end_locn, which the port
   expands *)
(* HOL4 locationScript.sml:36: the overload unknown_locn, which the
   port expands *)

let unknown_loc_def = new_definition
  `unknown_loc = Locs UNKNOWNpt UNKNOWNpt`;;

let locnle_def = new_definition
  `locnle l1 l2 <=>
     l1 = l2 \/
     // reflexivity, for free
     l1 = UNKNOWNpt \/
     // minimal element
     l2 = EOFpt \/ ~(
     // maximal element
     // otherwise compare row and col lexicographically
     l2 = UNKNOWNpt) /\ ~(l1 = EOFpt) /\
     (locnrow l1 < locnrow l2 \/ locnrow l1 = locnrow l2 /\
       locncol l1 < locncol l2)`;;

let locsle_def = define_general
  [`locsle (Locs l1 _1) (Locs l2 _2) <=> locnle l1 l2`];;
add_simp locsle_def;;

let merge_locs_def = define_general
  [`merge_locs (Locs l1 l2) (Locs l3 l4) = Locs l1 l4`];;

let _ = size_thms "locs";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let merge_list_locs_def,merge_list_locs_ind = define_wf
  `MEASURE (\x0. list_size locs_size x0)`
  [`merge_list_locs x1 =
        match x1 with
          [] -> unknown_loc
        | (CONS h []) -> h
        | (CONS h1 (CONS h2 [])) -> merge_locs h1 h2
        | (CONS h1 (CONS h2 t)) -> merge_list_locs (CONS h1 t)`];;
