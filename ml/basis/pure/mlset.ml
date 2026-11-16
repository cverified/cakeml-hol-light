(* ======================================================== *)
(*  mlset: ported from HOL4's
    basis/pure/mlsetScript.sml
    A definition theory, with 18 definitions, 1 datatype and no
    theorems.  Needed by SetProg.ml.  *)
(* ======================================================== *)

(*
  Pure functions for the Set module.
  This file defines a wrapper around the balanced_map type.
*)

needs "lib/balanced_map.ml";;
needs "lib/ternaryComparisons.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "mlset" [];;

(* The type :set would collide with :pred_set$set *)
let mlset_INDUCT,mlset_RECURSION = define_datatype
  "mlset =
     mlset_Set ('a->'a->ordering) (('a,1)balanced_map)";;

let mlset_empty_def = new_definition
  `mlset_empty cmp = mlset_Set cmp balanced_map_empty`;;

let mlset_singleton_def = new_definition
  `mlset_singleton cmp x = mlset_Set cmp (balanced_map_singleton x one)`;;

let mlset_member_def = new_definition
  `mlset_member x (mlset_Set cmp s) = balanced_map_member cmp x s`;;

let mlset_insert_def = new_definition
  `mlset_insert x (mlset_Set cmp s) = mlset_Set cmp (balanced_map_insert cmp
  x one s)`;;

let mlset_delete_def = new_definition
  `mlset_delete x (mlset_Set cmp s) = mlset_Set cmp (balanced_map_delete cmp
  x s)`;;

let mlset_union_def = new_definition
  `mlset_union (mlset_Set cmp s) (mlset_Set _ t) = mlset_Set cmp
  (balanced_map_union cmp s t)`;;

let isSubset_def = new_definition
  `isSubset (mlset_Set cmp s) (mlset_Set _ t) = isSubmapOf cmp s t`;;

let mlset_compare_def = new_definition
  `mlset_compare (mlset_Set cmp s) (mlset_Set _ t) = balanced_map_compare
  cmp (\x y. EQUAL) s t`;;

let mlset_all_def = new_definition
  `mlset_all f (mlset_Set cmp s) = every (\k _. f k) s`;;

let mlset_exists_def = new_definition
  `mlset_exists f (mlset_Set cmp s) = balanced_map_exists (\k _. f k) s`;;

let mlset_translate_def = new_definition
  `mlset_translate f cmp (mlset_Set _ s) =
     mlset_Set cmp (balanced_map_foldrWithKey
               (\k _ t. balanced_map_insert cmp (f k) one t)
               balanced_map_empty s)`;;

let mlset_map_def = new_definition
  `mlset_map f (mlset_Set cmp s) = mlset_translate f cmp (mlset_Set cmp s)`;;

let mlset_filter_def = new_definition
  `mlset_filter f (mlset_Set cmp s) = mlset_Set cmp
  (balanced_map_filterWithKey (\k one. f k) s)`;;

let mlset_fromList_def = new_definition
  `mlset_fromList cmp xs =
     mlset_Set cmp (FOLDL (\t k. balanced_map_insert cmp k one t)
                    balanced_map_empty xs)`;;

let mlset_null_def = new_definition
  `mlset_null (mlset_Set cmp s) = balanced_map_null s`;;

let mlset_size_def = new_definition
  `mlset__size (mlset_Set cmp s) = balanced_map__size s`;;

let mlset_toList_def = new_definition
  `mlset_toList (mlset_Set cmp s) = balanced_map_foldrWithKey (\k _ xs. CONS
  k xs) [] s`;;

let fold_def = new_definition
  `fold f e (mlset_Set cmp s) = balanced_map_foldrWithKey (\k _ t. f k t) e
  s`;;

(* and the interface *)
let _ = unhide_overloads ();;
