(* ======================================================== *)
(*  mlvector: ported from HOL4's
    basis/pure/mlvectorScript.sml  *)
(* ======================================================== *)

(*
  Pure functions for the Vector module.
*)

needs "basis/pure/mllist.ml";;
needs "lib/indexedLists.ml";;
needs "lib/ternaryComparisons.ml";;
needs "misc/misc.ml";;
(* HOL4 ancestors outside the port: regexp_compiler *)

let sub_unsafe_def = cake_define
  `sub_unsafe (Vector l) n = EL n l`;;

let tabulate_def = cake_define
  `mlvector_tabulate n f = Vector (GENLIST f n)`;;
hol4_overload "tabulate" "mlvector_tabulate";;

(* TERMINATION: wf_rel_tac `measure (\(vec, n). length(vec) - n)` *)
let toList_aux_def = cake_define
  `toList_aux vec n =
   (if length (vec) <= n then [] else sub vec n :: toList_aux vec
     (n + 1))`;;

(* HOL4 ML code, not ported:
val toList_aux_ind = theorem"toList_aux_ind";
*)

let toList_def = cake_define
  `mlvector_toList vec = toList_aux vec 0`;;

let update_def = cake_define
  `update vec i x = Vector (LUPDATE x i (mlvector_toList (vec)))`;;


let concat_def = cake_define
  `mlvector_concat l = Vector (FLAT (MAP mlvector_toList l))`;;
hol4_overload "concat" "mlvector_concat";;

let map_def = cake_define
  `mlvector_map vec f = Vector (MAP f (mlvector_toList vec))`;;
hol4_overload "map" "mlvector_map";;

let mapi_def = cake_define
  `mlvector_mapi vec f = Vector (MAPi f (mlvector_toList vec))`;;
hol4_overload "mapi" "mlvector_mapi";;

let foldli_aux_def = cake_define_list
  [`mlvector_foldli_aux f e vec n 0 = e`;
   `mlvector_foldli_aux f e vec n (SUC len) = mlvector_foldli_aux f
  (f n (sub vec n) e) vec (n + 1) len`];;
hol4_overload "foldli_aux" "mlvector_foldli_aux";;

let foldli_def = cake_define
  `mlvector_foldli f e vec = foldli_aux f e vec 0 (length vec)`;;
hol4_overload "foldli" "mlvector_foldli";;

let foldl_aux_def = cake_define_list
  [`foldl_aux f e vec n 0 = e`;
   `foldl_aux f e vec n (SUC len) = foldl_aux f (f e (sub vec n)) vec
  (n + 1) len`];;

let foldl_def = cake_define
  `mlvector_foldl f e vec = foldl_aux f e vec 0 (length vec)`;;
hol4_overload "foldl" "mlvector_foldl";;


let foldri_aux_def = cake_define_list
  [`foldri_aux f e vec 0 = e`;
   `foldri_aux f e vec (SUC len) = foldri_aux f (f len (sub vec len)
  e) vec len`];;

let foldri_def = cake_define
  `foldri f e vec = foldri_aux f e vec (length vec)`;;


let foldr_aux_def = cake_define_list
  [`foldr_aux f e vec 0 = e`;
   `foldr_aux f e vec (SUC len) = foldr_aux f (f (sub vec len) e) vec
  len`];;

let foldr_def = cake_define
  `foldr f e vec = foldr_aux f e vec (length vec)`;;


let findi_aux_def = cake_define_list
  [`findi_aux f vec n 0 = NONE`;
   `findi_aux f vec n (SUC len) =
      (if f n (sub vec n) then SOME (n,(sub vec n)) else
        findi_aux f vec (n + 1) len)`];;

let findi_def = cake_define
  `mlvector_findi f vec = findi_aux f vec 0 (length vec)`;;
hol4_overload "findi" "mlvector_findi";;


let find_aux_def = cake_define_list
  [`find_aux f vec n 0 = NONE`;
   `find_aux f vec n (SUC len) =
      (if f (sub vec n) then SOME (sub vec n) else find_aux f vec
        (n + 1) len)`];;

let find_def = cake_define
  `find f vec = find_aux f vec 0 (length vec)`;;


let exists_aux_def = cake_define_list
  [`exists_aux f vec n 0 = F`;
   `exists_aux f vec n (SUC len) =
        (if f (sub vec n) then T else exists_aux f vec (n + 1)
          len)`];;

let exists_def = cake_define
  `mlvector_exists f vec = exists_aux f vec 0 (length vec)`;;

let all_aux_def = cake_define_list
  [`all_aux f vec n 0 = T`;
   `all_aux f vec n (SUC len) =
        (if f (sub vec n) then all_aux f vec (n + 1) len else F)`];;

let all_def = cake_define
  `all f vec = all_aux f vec 0 (length vec)`;;

let collate_aux_def = cake_define_list
  [`mlvector_collate_aux f vec1 vec2 n ord 0 = ord`;
   `mlvector_collate_aux f vec1 vec2 n ord (SUC len) =
        (if f (sub vec1 n) (sub vec2 n) = EQUAL then
          mlvector_collate_aux f vec1 vec2 (n + 1) ord len else f
          (sub vec1 n) (sub vec2 n))`];;
hol4_overload "collate_aux" "mlvector_collate_aux";;

let collate_def = cake_define
  `mlvector_collate f vec1 vec2 =
   (if (length vec1) < (length vec2) then mlvector_collate_aux f
     vec1 vec2 0 LESS (length vec1) else if (length vec2) < (length
     vec1) then mlvector_collate_aux f vec1 vec2 0 GREATER (length
     vec2) else mlvector_collate_aux f vec1 vec2 0 EQUAL (length
     vec2))`;;
hol4_overload "collate" "mlvector_collate";;
