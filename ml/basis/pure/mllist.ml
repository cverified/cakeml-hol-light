(* ======================================================== *)
(*  mllist: ported from HOL4's
    basis/pure/mllistScript.sml
    A definition theory, with 26 definitions and 43 theorems.
    Needed by 26 files of the port.  *)
(* ======================================================== *)

(*
  Pure functions for the List module.
*)

needs "lib/indexedLists.ml";;
needs "lib/mergesort.ml";;
needs "lib/sorting.ml";;
needs "lib/ternaryComparisons.ml";;
needs "lib/toto.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "mllist" [];;

let _ = do_list hide_constant ["length"; "negate"];;

let intersperse_def,intersperse_ind = define_guess
  `intersperse sep x2 =
   match x2 with
     [] -> []
   | [x] -> [x]
   | CONS x xs -> CONS x (CONS sep (intersperse sep xs))`;;

(* ===== TODO: TO BE PORTED TO HOL (better theorems for mergesort_tail) ===== *)
let merge_tail_MEM = prove
 (`!negate' R' xs ys acc. MEM x (merge_tail negate' R' xs ys acc) = ((MEM x
  xs) \/ (MEM x ys) \/ (MEM x acc))`,
  CHEAT_TAC);;

let mergesortN_tail_MEM = prove
 (`!negate' R' length' lst. (MEM x (mergesortN_tail negate' R' length' lst)
  <=> MEM x (TAKE length' lst))`,
  CHEAT_TAC);;

let sort3_tail_sort3 = prove
 (`!negate' R' x y z. sort3_tail negate' R' x y z =
     (if negate' then REVERSE (sort3 R' x y z) else sort3 R' x y z)`,
  CHEAT_TAC);;

let sort2_tail_sort2 = prove
 (`!negate' R' x y. sort2_tail negate' R' x y =
     (if negate' then REVERSE (sort2 R' x y) else sort2 R' x y)`,
  CHEAT_TAC);;

let mergetail_merge = prove
 (`!negate' R' xs ys acc.
      merge_tail negate' R' xs ys acc =
      (if negate' then APPEND (REVERSE (mergesort_merge (\x y. ~(R' x y)) xs
        ys)) acc
       else APPEND (REVERSE (mergesort_merge R' xs ys)) acc)`,
  CHEAT_TAC);;

let merge_tail_acc = prove
 (`!negate' R' xs ys acc acc'.
     merge_tail negate' R' xs ys (APPEND acc acc') = APPEND (merge_tail
       negate' R' xs ys acc) acc'`,
  CHEAT_TAC);;

let mergesort_tail_MEM = prove
 (`!R' l. MEM x (mergesort_tail R' l) <=> MEM x l`,
  CHEAT_TAC);;

let merge_tail_PERM = prove
 (`!negate' R' xs ys acc. PERM (APPEND (APPEND xs ys) acc) (merge_tail
  negate' R' xs ys acc)`,
  CHEAT_TAC);;

let sort2_tail_PERM = prove
 (`!neg R' x y. PERM [x; y] (sort2_tail neg R' x y)`,
  CHEAT_TAC);;

let sort3_tail_PERM = prove
 (`!neg R' x y z. PERM [x; y; z] (sort3_tail neg R' x y z)`,
  CHEAT_TAC);;

let mergesortN_tail_PERM = prove
 (`!neg R' len l. PERM (TAKE len l) (mergesortN_tail neg R' len l)`,
  CHEAT_TAC);;
(* ^^^^^ TO BE PORTED TO HOL ^^^^^ *)

let sort_def = new_definition
  `sort = mergesort_tail`;;

let sort_thm = prove
 (`!R' l. sort R' l = mergesort_tail R' l`,
  CHEAT_TAC);;

let sort_SORTED = prove
 (`!R' L. transitive R' /\ total R' ==> SORTED R' (sort R' L)`,
  CHEAT_TAC);;

let sort_MEM = prove
 (`!R' L. MEM x (sort R' L) <=> MEM x L`,
  CHEAT_TAC);;
add_simp sort_MEM;;

let sort_PERM = prove
 (`!R' L. PERM L (sort R' L)`,
  CHEAT_TAC);;

let sort_LENGTH = prove
 (`!R' l. LENGTH (sort R' l) = LENGTH l`,
  CHEAT_TAC);;
add_simp sort_LENGTH;;

let sort_SORTS = prove
 (`!R'. (transitive R' /\ total R') ==> SORTS sort R'`,
  CHEAT_TAC);;

let sort_set = prove
 (`set_of_list (sort R ls) = set_of_list ls`,
  CHEAT_TAC);;
add_simp sort_set;;

let getItem_def = define_cases
  `(getItem [] = NONE) /\
   (getItem (CONS h t) = SOME (h,t))`;;

let nth_def = new_definition
  `mllist_nth l i = EL i l`;;

let take_def = new_definition
  `take l i = TAKE i l`;;

let drop_def = new_definition
  `drop l i = DROP i l`;;

let takeUntil_def,takeUntil_ind = define_rec
  `(takeUntil p [] = []) /\
   (takeUntil p (CONS x xs) = if p x then [] else CONS x (takeUntil p xs))`;;

let dropUntil_def,dropUntil_ind = define_rec
  `(dropUntil p [] = []) /\
   (dropUntil p (CONS x xs) = if p x then CONS x xs else dropUntil p xs)`;;

let mllist_mapi_def,mllist_mapi_ind = define_rec
  `(mllist_mapi f (n:num) [] = []) /\
   (mllist_mapi f (n:num) (CONS h t) = (let y = f n h in (CONS y
    (mllist_mapi f (n + 1) t))))`;;

(* [local] *)
let MAPI_thm_gen = prove
 (`!f l x. MAPi (\a. f (a + x)) l = mllist_mapi f x l`,
  CHEAT_TAC);;

let MAPI_thm = prove
 (`!f l. MAPi f l = mllist_mapi f 0 l`,
  CHEAT_TAC);;

let mapPartial_def,mapPartial_ind = define_rec
  `(mllist_mapPartial f [] = []) /\
   (mllist_mapPartial f (CONS h t) = match (f h) with
        NONE -> mllist_mapPartial f t
        | (SOME x) -> CONS x (mllist_mapPartial f t))`;;

let mapPartial_thm = prove
 (`!f l. mllist_mapPartial f l = MAP THE (FILTER IS_SOME (MAP f l))`,
  CHEAT_TAC);;

let index_find_thm = prove
 (`!x y. OPTION_MAP SND (INDEX_FIND x f l) = OPTION_MAP SND (INDEX_FIND y f
  l)`,
  CHEAT_TAC);;

let FIND_thm = prove
 (`(FIND f [] = NONE) /\
   (!h t. FIND f (CONS h t) = (if f h then SOME h else FIND f t))`,
  CHEAT_TAC);;

let partition_aux_def,partition_aux_ind = define_rec
  `(partition_aux f [] pos neg =
        (REVERSE pos,REVERSE neg)) /\
   (partition_aux f (CONS h t) pos neg = if f h then partition_aux f t (CONS h
    pos) neg
          else partition_aux f t pos (CONS h neg))`;;

let partition_def = new_definition
  `partition (f:'a->bool) l = partition_aux f l [] []`;;

(* [local] *)
let partition_aux_thm = prove
 (`!f l l1 l2.
     partition_aux f l l1 l2 =
     (APPEND (REVERSE l1) (FILTER f l),APPEND (REVERSE l2) (FILTER ((~) o
       f) l))`,
  CHEAT_TAC);;

let partition_pos_thm = prove
 (`!f l. FST (partition f l) = FILTER f l`,
  CHEAT_TAC);;

let partition_neg_thm = prove
 (`!f l. SND (partition f l) = FILTER ((~) o f) l`,
  CHEAT_TAC);;

let foldl_def,foldl_ind = define_rec
  `(mllist_foldl f e [] = e) /\
   (mllist_foldl f e (CONS h t) = mllist_foldl f (f h e) t)`;;

let foldli_aux_def,foldli_aux_ind = define_rec
  `(mllist_foldli_aux f e n [] = e) /\
   (mllist_foldli_aux f e n (CONS h t) = mllist_foldli_aux f (f n h e)
    (SUC n) t)`;;

let foldli_def = new_definition
  `mllist_foldli f e l = mllist_foldli_aux f e 0 l`;;

(* [local] *)
let foldli_aux_thm = prove
 (`!l f e n. mllist_foldli_aux f e n l = FOLDRi (\n'. f ((LENGTH l + n) -
  (SUC n'))) e (REVERSE l)`,
  CHEAT_TAC);;

let foldl_intro = prove
 (`!xs x f. FOLDL f x xs = mllist_foldl (\x acc. f acc x) x xs`,
  CHEAT_TAC);;

let foldli_thm = prove
 (`!f e l. mllist_foldli f e l = FOLDRi (\n. f (LENGTH l - (SUC n))) e
  (REVERSE l)`,
  CHEAT_TAC);;

(* these definitions are in A normal form in
   order to be able to prove CF specs about them
   (in addition to the translator-generated ones)
   (the CF specs allow more general arguments f) *)

(* the termination relation that HOL4 gives is
     MEASURE (\(n,m,_,_). m - n)
   which is not one that HOL Light takes here; the one
   below is what the port found for it *)
let tabulate_aux_def,tabulate_aux_ind = define_wf
  `MEASURE (\(n,m,_1,_2). m - n)`
  `tabulate_aux n m f acc =
     let b = (n >= m) in
     if b then REVERSE acc
     else let v = f n in
       let n = n + 1 in
       let acc = CONS v acc in
       tabulate_aux n m f acc`;;

let tabulate_def = new_definition
  `mllist_tabulate n f = let l = [] in tabulate_aux 0 n f l`;;

let tabulate_aux_GENLIST = prove
 (`!n m f acc. tabulate_aux n m f acc = APPEND (REVERSE acc) (list_of_seq (f
  o ITER n SUC) (m - n))`,
  CHEAT_TAC);;

let tabulate_GENLIST = prove
 (`!n. mllist_tabulate n f = list_of_seq f n`,
  CHEAT_TAC);;

let collate_def,collate_ind = define_guess
  `(mllist_collate f [] [] = EQUAL) /\
   (mllist_collate f [] (CONS h t) = LESS) /\
   (mllist_collate f (CONS h t) [] = GREATER) /\
   (mllist_collate f (CONS h1 t1) (CONS h2 t2) =
        if f h1 h2 = EQUAL then mllist_collate f t1 t2
        else f h1 h2)`;;

let collate_equal_thm = prove
 (`!l. (!x. MEM x l ==> (f x x = EQUAL)) ==> (mllist_collate f l l = EQUAL)`,
  CHEAT_TAC);;

let collate_short_thm = prove
 (`!f l1 l2. (!x. f x x = EQUAL) /\ (~(l1 = l2)) /\ (l1 <<= l2) ==>
        (mllist_collate f l1 l2 = LESS)`,
  CHEAT_TAC);;

let collate_long_thm = prove
 (`!f l1 l2. (!x. f x x = EQUAL) /\ (~(l1 = l2)) /\ (l2 <<= l1) ==>
        (mllist_collate f l1 l2 = GREATER)`,
  CHEAT_TAC);;

let cpn_to_reln_def = new_definition
  `cpn_to_reln f x1 x2 = (f x1 x2 = LESS)`;;

let collate_cpn_reln_thm = prove
 (`!f l1 l2. (!x1 x2. (f x1 x2 = EQUAL) <=>
    (x1 = x2)) ==> (cpn_to_reln (mllist_collate f) l1 l2 = LLEX
      (cpn_to_reln f) l1 l2)`,
  CHEAT_TAC);;

(* from std_preludeLib *)
let LENGTH_AUX_def,LENGTH_AUX_ind = define_rec
  `(LENGTH_AUX [] (n:num) = (n:num)) /\
   (LENGTH_AUX (CONS x xs) (n:num) = ((LENGTH_AUX xs (n + 1)):num))`;;

(* HOL4 mllistScript.sml:572-575: a theorem that HOL4 states as the value of
   an ML expression: LENGTH_AUX_THM *)

let mllist_list_compare_def = list_compare_def;;

(* tail-recursive MAP *)

let map_rev'_def,map_rev'_ind = define_rec
  `(map_rev' f [] acc = acc) /\
   (map_rev' f (CONS x xs) acc = map_rev' f xs (CONS (f x) acc))`;;

let map_rev_def = new_definition
  `map_rev f xs = map_rev' f xs []`;;

(* [local] *)
let map_rev'_lemma = prove
 (`!acc. map_rev' f xs acc = APPEND (map_rev' f xs []) acc`,
  CHEAT_TAC);;

let map_rev_thm = prove
 (`map_rev f xs = REVERSE (MAP f xs)`,
  CHEAT_TAC);;

(* tail-recursive FILTER *)

let filter_rev'_def,filter_rev'_ind = define_rec
  `(filter_rev' P [] acc = acc) /\
   (filter_rev' P (CONS h t) acc = if P h then filter_rev' P t (CONS h
    acc) else filter_rev' P t acc)`;;

let filter_rev_def = new_definition
  `filter_rev P xs = filter_rev' P xs []`;;

(* [local] *)
let filter_rev'_lemma = prove
 (`!acc. filter_rev' P xs acc = APPEND (filter_rev' P xs []) acc`,
  CHEAT_TAC);;

let filter_rev_thm = prove
 (`filter_rev f xs = REVERSE (FILTER f xs)`,
  CHEAT_TAC);;

(* tail-recursive FLAT *)

let flat_rev'_def,flat_rev'_ind = define_rec
  `(flat_rev' [] acc = acc) /\
   (flat_rev' (CONS x xs) acc = flat_rev' xs (REV x acc))`;;

let flat_rev_def = new_definition
  `flat_rev xs = flat_rev' xs []`;;

(* [local] *)
let flat_rev'_lemma = prove
 (`!acc. flat_rev' l acc = APPEND (flat_rev' l []) acc`,
  CHEAT_TAC);;

let flat_rev_thm = prove
 (`flat_rev xs = REVERSE (FLAT xs)`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["length";
   "negate"];;

(* and the interface *)
let _ = unhide_overloads ();;
