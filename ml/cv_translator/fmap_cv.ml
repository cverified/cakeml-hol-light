(* ======================================================== *)
(*  fmap_cv: ported from HOL4's
    cv_translator/fmap_cvScript.sml
    A definition theory, with 4 definitions and 13 theorems.  No
    file of the port needs it.  *)
(* ======================================================== *)

(*
  Set up cv translation of fmaps
*)

needs "basis/pure/mllist.ml";;
needs "candle/prover/compute/compute_exec.ml";;
needs "lib/cv_std.ml";;
needs "lib/cv_type.ml";;
needs "lib/sorting.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "fmap_cv"
  ["mllist"];;
(* HOL4 ancestors outside the port: finite_map list alist string *)

(* -- string as domain -- *)

let from_str_fmap_def = new_definition
  `from_str_fmap (f_a:'a->cv) (m:(string,'a)fmap) =
     from_list (from_pair (from_list from_char) f_a)
       (MAP (\k. (k,FAPPLY m k)) (sort string_le (SET_TO_LIST (FDOM m))))`;;

let to_str_fmap_def = new_definition
  `to_str_fmap (t_a:cv->'a) (v:cv) =
     FEMPTY |++ (to_list (to_pair (to_list to_char) t_a) v)`;;

let from_to_imp = prove
 (`from_to f t ==>
   t (f x) = x`,
  CHEAT_TAC);;

let ALL_DISTINCT_SORT_string_le = prove
 (`FINITE xs ==>
   ALL_DISTINCT (sort string_le (SET_TO_LIST xs))`,
  CHEAT_TAC);;
add_simp ALL_DISTINCT_SORT_string_le;;

let SORT_SORTED_string_le = prove
 (`SORTED string_le (sort string_le xs)`,
  CHEAT_TAC);;
add_simp SORT_SORTED_string_le;;

let fmap_eq_rep = prove
 (`FEMPTY |++ MAP (\k. (k,FAPPLY x k)) (sort string_le (SET_TO_LIST (FDOM
  x))) = x`,
  CHEAT_TAC);;

(* [cv_from_to] *)
let from_to_str_fmap = prove
 (`from_to f_a t_a ==>
   from_to (from_str_fmap (f_a:'a->cv)) (to_str_fmap (t_a:cv->'a))`,
  CHEAT_TAC);;

(* lookup *)

(* [cv_rep] *)
let FLOOKUP_cv_rep = prove
 (`from_option (f_a:'a->cv) (FLOOKUP m k) =
   cv_ALOOKUP (from_str_fmap f_a m) (from_list from_char k)`,
  CHEAT_TAC);;

(* update *)

(* HOL4 fmap_cvScript.sml:99-100: ML code, not ported *)

let str_insert_def,str_insert_ind = define_guess
  `(str_insert [] k v = [(k,v)]) /\
   (str_insert (CONS (a,b) rest) k v =
      if string_lt a k then CONS (a,b) (str_insert rest k v) else if k
          = a then CONS (k,v) rest else CONS (k,v) (CONS (a,b) rest))`;;

(* HOL4 fmap_cvScript.sml:109-110: ML code, not ported *)

let SORTED_string_le_string_lt = prove
 (`SORTED string_le ls /\
   ALL_DISTINCT ls ==>
   SORTED string_lt ls`,
  CHEAT_TAC);;

let SORT_SORTED_string_lt = prove
 (`FINITE s ==>
   SORTED string_lt (sort string_le (SET_TO_LIST s))`,
  CHEAT_TAC);;
add_simp SORT_SORTED_string_lt;;

let MEM_MAP_FST_str_insert = prove
 (`!ls k v.
   MEM x (MAP FST (str_insert ls k v)) <=>
   x = k \/ MEM x (MAP FST ls)`,
  CHEAT_TAC);;

let MEM_str_insert = prove
 (`!ls k v.
   SORTED string_lt (MAP FST ls) ==>
   (MEM (x,y) (str_insert ls k v) <=>
   (if x = k then y = v
   else MEM (x,y) ls))`,
  CHEAT_TAC);;

let str_insert_string_lt = prove
 (`!ls k v.
   SORTED string_lt (MAP FST ls) ==>
   SORTED string_lt (MAP FST (str_insert ls k v))`,
  CHEAT_TAC);;

let SORTED_string_lt_ALL_DISTINCT = prove
 (`SORTED string_lt ls ==>
   ALL_DISTINCT ls`,
  CHEAT_TAC);;

(* [cv_rep] *)
let FUPDATE_cv_rep = prove
 (`from_str_fmap f_a (m |+ (k,(v:'a))) =
   cv_str_insert (from_str_fmap f_a m) (from_list from_char k) (f_a v)`,
  CHEAT_TAC);;

(* test *)

let test_def = new_definition
  `fmap_cv_test m = (FLOOKUP m "hi",m |+ ("ho",(5:num)))`;;

(* HOL4 fmap_cvScript.sml:223-224: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
