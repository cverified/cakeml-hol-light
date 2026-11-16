(* ======================================================== *)
(*  mlmap: ported from HOL4's
    basis/pure/mlmapScript.sml
    A definition theory, with 26 definitions, 1 datatype and 31
    theorems.  Needed by panPtreeConversion.ml and panStatic.ml.  *)
(* ======================================================== *)

(*
  Pure functions for the Map module.
  This file defines a wrapper around the balanced_map type. The new
  type is essentially a pair that carries the compare functions next
  to the tree so that users don't have to provide the compare function
  as an explicit argument everywhere.
*)

needs "lib/balanced_map.ml";;
needs "lib/sorting.ml";;
needs "lib/ternaryComparisons.ml";;
needs "lib/toto.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "mlmap" [];;

let _ = do_list hide_constant ["Less"];;

(* implementation definitions *)

let mlmap_map_INDUCT,mlmap_map_RECURSION = define_datatype
  "mlmap_map =
     Map ('a->'a->ordering) (('a,'b)balanced_map)";;

let mlmap_lookup_def = new_definition
  `mlmap_lookup (Map cmp t) k = balanced_map_lookup cmp k t`;;

let mlmap_insert_def = new_definition
  `mlmap_insert (Map cmp t) k v = Map cmp (balanced_map_insert cmp k v t)`;;

let mlmap_delete_def = new_definition
  `mlmap_delete (Map cmp t) k = Map cmp (balanced_map_delete cmp k t)`;;

let mlmap_null_def = new_definition
  `mlmap_null (Map cmp t) = balanced_map_null t`;;

let mlmap_size_def = new_definition
  `mlmap__size (Map cmp t) = balanced_map__size t`;;

let mlmap_empty_def = new_definition
  `mlmap_empty cmp = Map cmp balanced_map_empty`;;

let mlmap_union_def = new_definition
  `mlmap_union (Map cmp t1) (Map _ t2) = Map cmp (balanced_map_union cmp t1
  t2)`;;

let mlmap_unionWith_def = new_definition
  `mlmap_unionWith f (Map cmp t1) (Map _ t2) =
     Map cmp (balanced_map_unionWith cmp f t1 t2)`;;

let mlmap_unionWithKey_def = new_definition
  `mlmap_unionWithKey f (Map cmp t1) (Map _ t2) =
     Map cmp (balanced_map_unionWithKey cmp f t1 t2)`;;

let mlmap_foldrWithKey_def = new_definition
  `mlmap_foldrWithKey f x (Map cmp t) = balanced_map_foldrWithKey f x t`;;

let mlmap_filter_def = new_definition
  `mlmap_filter p (Map cmp t) = Map cmp (balanced_map_filter p t)`;;

let mlmap_filterWithKey_def = new_definition
  `mlmap_filterWithKey p (Map cmp t) = Map cmp (balanced_map_filterWithKey p
  t)`;;

let mlmap_map_def = new_definition
  `mlmap_map f (Map cmp t) = Map cmp (balanced_map_map f t)`;;

let mlmap_mapWithKey_def = new_definition
  `mlmap_mapWithKey f (Map cmp t) = Map cmp (balanced_map_mapWithKey f t)`;;

let mlmap_toAscList_def = new_definition
  `mlmap_toAscList (Map cmp t) = balanced_map_toAscList t`;;

let mlmap_fromList_def = new_definition
  `mlmap_fromList cmp l = Map cmp (fromList cmp l)`;;

let isSubmapBy_def = new_definition
  `isSubmapBy f (Map cmp t1) (Map _ t2) = isSubmapOfBy cmp f t1 t2`;;

let isSubmap_def = new_definition
  `isSubmap m1 m2 = isSubmapBy (=) m1 m2`;;

let mlmap_all_def = new_definition
  `mlmap_all f (Map cmp t) = every f t`;;

let mlmap_exists_def = new_definition
  `mlmap_exists f (Map cmp t) = balanced_map_exists f t`;;

let mlmap_member_def = new_definition
  `mlmap_member k (Map cmp t) = balanced_map_member cmp k t`;;

let mlmap_singleton_def = new_definition
  `mlmap_singleton cmp k v = Map cmp (balanced_map_singleton k v)`;;

let mlmap_compare_def = new_definition
  `mlmap_compare vcmp (Map cmp m1:('a,'b)mlmap_map) (Map _ m2:('a,'b)mlmap_map)
  =
     balanced_map_compare cmp vcmp m1 m2`;;

(* definitions for proofs *)

let map_ok_def = new_definition
  `map_ok (Map cmp t) <=> balanced_map_invariant cmp t /\ TotOrd cmp`;;

let cmp_of_def = new_definition
  `cmp_of (Map cmp t) = cmp`;;

(* the clauses in two quotations: l is balanced_map and (('a , 'b)
   balanced_map); r is balanced_map and (('a , 'b) balanced_map), which one
   quotation cannot typecheck *)
let mlmap_to_fmap_def,mlmap_to_fmap_ind = define_guess_clauses
  [`mlmap_to_fmap (Map cmp Tip) = FEMPTY`;
   `mlmap_to_fmap (Map cmp (Bin s k v l r)) =
      ((FUNION (mlmap_to_fmap (Map cmp l)) (mlmap_to_fmap (Map cmp
          r))) |+ (k,v))`];;

(* theorems *)

let lookup_insert = prove
 (`map_ok t ==>
   mlmap_lookup (mlmap_insert t k1 v) k2 = (if k1 = k2 then SOME v else
     mlmap_lookup t k2)`,
  CHEAT_TAC);;

let lookup_delete = prove
 (`map_ok t ==>
   mlmap_lookup (mlmap_delete t k1) k2 = (if k1 = k2 then NONE else
     mlmap_lookup t k2)`,
  CHEAT_TAC);;

let cmp_of_insert = prove
 (`cmp_of (mlmap_insert t k v) = cmp_of t`,
  CHEAT_TAC);;
add_simp cmp_of_insert;;

let cmp_of_delete = prove
 (`cmp_of (mlmap_delete t k) = cmp_of t`,
  CHEAT_TAC);;
add_simp cmp_of_delete;;

let cmp_of_empty = prove
 (`cmp_of (mlmap_empty cmp) = cmp`,
  CHEAT_TAC);;
add_simp cmp_of_empty;;

(* [local] *)
let fmap_FLOOKUP_EQ = prove
 (`f1 = f2 <=> FLOOKUP f1 = FLOOKUP f2`,
  CHEAT_TAC);;

let TotOrd_key_set = prove
 (`TotOrd cmp ==> key_set cmp k = {k}`,
  CHEAT_TAC);;
add_simp TotOrd_key_set;;

let to_fmap_thm = prove
 (`!t cmp.
     TotOrd cmp ==>
     mlmap_to_fmap cmp t = MAP_KEYS (\x. {x}) (mlmap_to_fmap (Map cmp t))`,
  CHEAT_TAC);;

let empty_thm = prove
 (`(map_ok (mlmap_empty cmp) = TotOrd cmp) /\ mlmap_to_fmap (mlmap_empty cmp)
  = FEMPTY`,
  CHEAT_TAC);;

let size_thm = prove
 (`map_ok t ==>
     mlmap__size t = FCARD (mlmap_to_fmap t)`,
  CHEAT_TAC);;

let MAP_KEYS_sing_set = prove
 (`MAP_KEYS (\x. {x}) f1 = MAP_KEYS (\x. {x}) f2 <=> (f1 = f2)`,
  CHEAT_TAC);;

let MAP_KEYS_sing_set_UPDATE = prove
 (`MAP_KEYS (\x. {x}) f |+ ({k},v) = MAP_KEYS (\x. {x}) (f |+ (k,v))`,
  CHEAT_TAC);;

let MAP_KEYS_sing_set_DOMSUB = prove
 (`MAP_KEYS (\x. {x}) f \\ {k} = MAP_KEYS (\x. {x}) (f \\ k)`,
  CHEAT_TAC);;

let MAP_KEYS_sing_set_FUNION = prove
 (`FUNION (MAP_KEYS (\x. {x}) f1) (MAP_KEYS (\x. {x}) f2) =
      MAP_KEYS (\x. {x}) (FUNION f1 f2)`,
  CHEAT_TAC);;

let insert_thm = prove
 (`map_ok t ==>
   map_ok (mlmap_insert t k v) /\
   mlmap_to_fmap (mlmap_insert t k v) = (mlmap_to_fmap t |+ (k,v))`,
  CHEAT_TAC);;

let delete_thm = prove
 (`map_ok t ==>
   map_ok (mlmap_delete t k) /\
   mlmap_to_fmap (mlmap_delete t k) = (mlmap_to_fmap t \\ k)`,
  CHEAT_TAC);;

let union_thm = prove
 (`map_ok t1 /\ map_ok t2 /\ cmp_of t1 = cmp_of t2 ==>
   map_ok (mlmap_union t1 t2) /\
   cmp_of (mlmap_union t1 t2) = cmp_of t1 /\
   mlmap_to_fmap (mlmap_union t1 t2) = FUNION (mlmap_to_fmap t1)
     (mlmap_to_fmap t2)`,
  CHEAT_TAC);;

let FMERGE_WITH_KEY_MAP_KEYS = prove
 (`FMERGE_WITH_KEY g (MAP_KEYS (\x. {x}) m1) (MAP_KEYS (\x. {x}) m2) =
   MAP_KEYS (\x. {x}) (FMERGE_WITH_KEY (\k x y. g {k} x y) m1 m2)`,
  CHEAT_TAC);;

let unionWithKey_thm = prove
 (`map_ok t1 /\ map_ok t2 /\ cmp_of t1 = cmp_of t2 ==>
   map_ok (mlmap_unionWithKey f t1 t2) /\
   cmp_of (mlmap_unionWithKey f t1 t2) = cmp_of t1 /\
   mlmap_to_fmap (mlmap_unionWithKey f t1 t2) =
   FMERGE_WITH_KEY f (mlmap_to_fmap t1) (mlmap_to_fmap t2)`,
  CHEAT_TAC);;

let unionWith_lemma = prove
 (`mlmap_unionWith f t1 t2 = mlmap_unionWithKey (\k. f) t1 t2`,
  CHEAT_TAC);;

let unionWith_thm = prove
 (`map_ok t1 /\ map_ok t2 /\ cmp_of t1 = cmp_of t2 ==>
   map_ok (mlmap_unionWith f t1 t2) /\
   cmp_of (mlmap_unionWith f t1 t2) = cmp_of t1 /\
   mlmap_to_fmap (mlmap_unionWith f t1 t2) =
   FMERGE_WITH_KEY (\k x y. f x y) (mlmap_to_fmap t1) (mlmap_to_fmap t2)`,
  CHEAT_TAC);;

(* all_thm *)
let mlmap_all_thm = prove
 (`map_ok t ==>
     (mlmap_all f t <=> (!k v. mlmap_lookup t k = SOME v ==> f k v))`,
  CHEAT_TAC);;

(* exists_thm *)
let mlmap_exists_thm = prove
 (`map_ok t ==>
     (mlmap_exists f t <=> (?k v. mlmap_lookup t k = SOME v /\ f k v))`,
  CHEAT_TAC);;

let FDIFF_MAP_KEYS = prove
 (`(!x. x IN ks ==> SING x) ==>
   FDIFF (MAP_KEYS (\x. {x}) m) ks =
   MAP_KEYS (\x. {x}) (FDIFF m (UNIONS ks))`,
  CHEAT_TAC);;

let filterWithKey_thm = prove
 (`map_ok t ==>
     map_ok (mlmap_filterWithKey f t) /\
     mlmap_to_fmap (mlmap_filterWithKey f t) =
     FDIFF (mlmap_to_fmap t)
           {k | (k,v) | FLOOKUP (mlmap_to_fmap t) k = SOME v /\ ~(f k v)}`,
  CHEAT_TAC);;

let filter_lemma = prove
 (`mlmap_filter f t = mlmap_filterWithKey (\k. f) t`,
  CHEAT_TAC);;

let filter_thm = prove
 (`map_ok t ==>
     map_ok (mlmap_filter f t) /\
     mlmap_to_fmap (mlmap_filter f t) =
     FDIFF (mlmap_to_fmap t) {k | (k,v) | FLOOKUP (mlmap_to_fmap t) k =
       SOME v /\ ~(f v)}`,
  CHEAT_TAC);;

let lookup_thm = prove
 (`map_ok t ==> mlmap_lookup t k = FLOOKUP (mlmap_to_fmap t) k`,
  CHEAT_TAC);;

let filterWithKey_all = prove
 (`map_ok t ==>
     mlmap_all f (mlmap_filterWithKey f t)`,
  CHEAT_TAC);;

let MAP_FST_toAscList = prove
 (`map_ok t ==>
   SORTED (\x y. cmp_of t x y = LESS) (MAP FST (mlmap_toAscList t)) /\
   ALL_DISTINCT (MAP FST (mlmap_toAscList t)) /\
   FDOM (mlmap_to_fmap t) = set_of_list (MAP FST (mlmap_toAscList t))`,
  CHEAT_TAC);;

let MEM_toAscList = prove
 (`map_ok t /\ MEM (k,v) (mlmap_toAscList t) ==> FLOOKUP (mlmap_to_fmap t) k
  = SOME v`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["Less"];;

(* and the interface *)
let _ = unhide_overloads ();;
