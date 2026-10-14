(* ======================================================== *)
(*  mllist: ported from HOL4's
    basis/pure/mllistScript.sml  *)
(* ======================================================== *)

(*
  Pure functions for the List module.
*)

needs "lib/indexedLists.ml";;
needs "lib/mergesort.ml";;
needs "lib/sorting.ml";;
(* HOL4 ancestors outside the port: toto *)

let intersperse_def = cake_define
  `intersperse sep x2 =
      match x2 with
        [] -> []
      | [x] -> [x]
      | (x :: xs) -> x :: sep :: intersperse sep xs`;;

(* ===== TODO: TO BE PORTED TO HOL (better theorems for mergesort_tail)
   ===== *)
(* ^^^^^ TO BE PORTED TO HOL ^^^^^ *)

let sort_def = cake_define
  `sort = mergesort_tail`;;

let getItem_def = cake_define
  `(getItem [] = NONE) /\
   (getItem (h :: t) = SOME (h,t))`;;

let nth_def = cake_define
  `nth l i = EL i l`;;

let take_def = cake_define
  `take l i = TAKE i l`;;

let drop_def = cake_define
  `drop l i = DROP i l`;;

let takeUntil_def = cake_define
  `(takeUntil p [] = []) /\
   (takeUntil p (x :: xs) = (if p x then [] else x :: takeUntil p
     xs))`;;

let dropUntil_def = cake_define
  `(dropUntil p [] = []) /\
   (dropUntil p (x :: xs) = (if p x then x :: xs else dropUntil p
     xs))`;;

let mapi_def = cake_define
  `(mllist_mapi f' (n:num) [] = []) /\
   (mllist_mapi f' n (h :: t) = (let y = f' n h in (y ::
     (mllist_mapi f' (n + 1) t))))`;;

let mapPartial_def = cake_define
  `(mllist_mapPartial f' [] = []) /\
   (mllist_mapPartial f' (h :: t) = (match (f' h) with
     NONE -> mllist_mapPartial f' t | (SOME x) -> x ::
       mllist_mapPartial f' t))`;;

let partition_aux_def = cake_define
  `(partition_aux f' [] pos neg =
     (REVERSE pos,REVERSE neg)) /\
     (partition_aux f' (h :: t) pos neg = (if f' h then
       partition_aux f' t (h :: pos) neg else partition_aux f' t pos
       (h :: neg)))`;;

let partition_def = cake_define
  `partition (f':'a->bool) l = partition_aux f' l [] []`;;

let foldl_def = cake_define
  `(mllist_foldl f' e [] = e) /\
   (mllist_foldl f' e (h :: t) = mllist_foldl f' (f' h e) t)`;;

let foldli_aux_def = cake_define
  `(mllist_foldli_aux f' e n [] = e) /\
   (mllist_foldli_aux f' e n (h :: t) = mllist_foldli_aux f' (f' n
     h e) (SUC n) t)`;;

let foldli_def = cake_define
  `mllist_foldli f' e l = mllist_foldli_aux f' e 0 l`;;

(* these definitions are in A normal form in
   order to be able to prove CF specs about them
   (in addition to the translator-generated ones)
   (the CF specs allow more general arguments f) *)

(* TERMINATION: wf_rel_tac`measure (λ(n,m,_,_). m-n)` *)
let tabulate_aux_def = cake_define
  `tabulate_aux n m f' acc =
     (let b = (n >= m) in
     if b then REVERSE acc else
       let v = f' n in
       let n = n + 1 in
       let acc = v :: acc in
       tabulate_aux n m f' acc)`;;

let tabulate_def = cake_define
  `mllist_tabulate n f' = (let l = [] in tabulate_aux 0 n f' l)`;;

let collate_def = cake_define
  `(mllist_collate f' [] [] = EQUAL) /\
   (mllist_collate f' [] (h :: t) = LESS) /\
   (mllist_collate f' (h :: t) [] = GREATER) /\
   (mllist_collate f' (h1 :: t1) (h2 :: t2) =
     (if f' h1 h2 = EQUAL then mllist_collate f' t1 t2 else f' h1
       h2))`;;

let cpn_to_reln_def = cake_define
  `cpn_to_reln f' x1 x2 = (f' x1 x2 = LESS)`;;

(* from std_preludeLib *)
let LENGTH_AUX_def = cake_define
  `(LENGTH_AUX [] n = (n:num)) /\
   (LENGTH_AUX (x :: xs) n = LENGTH_AUX xs (n + 1))`;;

(* tail-recursive MAP *)

let map_rev'_def = cake_define
  `map_rev' f' [] acc = acc /\
   map_rev' f' (x :: xs) acc = map_rev' f' xs (f' x :: acc)`;;

let map_rev_def = cake_define
  `map_rev f' xs = map_rev' f' xs []`;;

(* tail-recursive FILTER *)

let filter_rev'_def = cake_define
  `filter_rev' P [] acc = acc /\
   filter_rev' P (h :: t) acc = (if P h then filter_rev' P t (h ::
     acc) else filter_rev' P t acc)`;;

let filter_rev_def = cake_define
  `filter_rev P xs = filter_rev' P xs []`;;

(* tail-recursive FLAT *)

let flat_rev'_def = cake_define
  `flat_rev' [] acc = acc /\
   flat_rev' (x :: xs) acc = flat_rev' xs (REV x acc)`;;

let flat_rev_def = cake_define
  `flat_rev xs = flat_rev' xs []`;;
