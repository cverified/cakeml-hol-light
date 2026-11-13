(* ======================================================== *)
(*  mllist: ported from HOL4's
    basis/pure/mllistScript.sml
    A definition theory, with 26 definitions and 43 theorems.
    Needed by 18 files of the port.  *)
(* ======================================================== *)

(*
  Pure functions for the List module.
*)

needs "lib/indexedLists.ml";;
needs "lib/mergesort.ml";;
needs "lib/sorting.ml";;
needs "lib/ternaryComparisons.ml";;
needs "lib/toto.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "mllist" [];;

let _ = do_list hide_constant ["length"; "negate"];;

let intersperse_def,intersperse_ind = define_guess
  [`intersperse sep x2 =
      match x2 with
        [] -> []
      | [x] -> [x]
      | (x :: xs) -> x :: sep :: intersperse sep xs`];;

(* ===== TODO: TO BE PORTED TO HOL (better theorems for mergesort_tail) ===== *)
let merge_tail_MEM = prove
 (`!negate' R xs ys acc. MEM x (merge_tail negate' R xs ys acc) =
  ((MEM x xs) \/ (MEM x ys) \/ (MEM x acc))`,
  CHEAT_TAC);;

let mergesortN_tail_MEM = prove
 (`!negate' R length' lst. (MEM x (mergesortN_tail negate' R length'
  lst) <=> MEM x (TAKE length' lst))`,
  CHEAT_TAC);;

let sort3_tail_sort3 = prove
 (`!negate' R x y z. sort3_tail negate' R x y z =
     (if negate' then REVERSE (sort3 R x y z) else sort3 R x y z)`,
  CHEAT_TAC);;

let sort2_tail_sort2 = prove
 (`!negate' R x y. sort2_tail negate' R x y =
     (if negate' then REVERSE (sort2 R x y) else sort2 R x y)`,
  CHEAT_TAC);;

let mergetail_merge = prove
 (`!negate' R xs ys acc.
      merge_tail negate' R xs ys acc =
      (if negate' then REVERSE (mergesort_merge (\x y. ~(R x y)) xs
        ys) ++ acc else REVERSE (mergesort_merge R xs ys) ++ acc)`,
  CHEAT_TAC);;

let merge_tail_acc = prove
 (`!negate' R xs ys acc acc'.
     merge_tail negate' R xs ys (acc ++ acc') = (merge_tail negate'
       R xs ys acc) ++ acc'`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[mergetail_merge] THEN
    COND_CASES_TAC THEN
   REWRITE_TAC[APPEND_ASSOC]));;

let mergesort_tail_MEM = prove
 (`!R l. MEM x (mergesort_tail R l) <=> MEM x l`,
  CHEAT_TAC);;

let merge_tail_PERM = prove
 (`!negate' R xs ys acc. PERM (xs ++ ys ++ acc) (merge_tail negate' R
  xs ys acc)`,
  CHEAT_TAC);;

let sort2_tail_PERM = prove
 (`!neg R x y. PERM [x; y] (sort2_tail neg R x y)`,
  CHEAT_TAC);;

let sort3_tail_PERM = prove
 (`!neg R x y z. PERM [x; y; z] (sort3_tail neg R x y z)`,
  CHEAT_TAC);;

let mergesortN_tail_PERM = prove
 (`!neg R len l. PERM (TAKE len l) (mergesortN_tail neg R len l)`,
  CHEAT_TAC);;
(* ^^^^^ TO BE PORTED TO HOL ^^^^^ *)

let sort_def = new_definition
  `sort = mergesort_tail`;;

let sort_thm = prove
 (`!R l. sort R l = mergesort_tail R l`,
  (REWRITE_TAC[sort_def]));;

let sort_SORTED = prove
 (`!R L. transitive R /\ total R ==> SORTED R (sort R L)`,
  CHEAT_TAC);;

(* [simp] *)
let sort_MEM = prove
 (`!R L. MEM x (sort R L) <=> MEM x L`,
  (REWRITE_TAC[sort_def; mergesort_tail_MEM]));;

let sort_PERM = prove
 (`!R L. PERM L (sort R L)`,
  CHEAT_TAC);;

(* [simp] *)
let sort_LENGTH = prove
 (`!R l. LENGTH (sort R l) = LENGTH l`,
  CHEAT_TAC);;

let sort_SORTS = prove
 (`!R. (transitive R /\ total R) ==> SORTS sort R`,
  (SIMP_TAC[SORTS_DEF; sort_PERM; sort_SORTED]));;

(* [simp] *)
let sort_set = prove
 (`set_of_list (sort R ls) = set_of_list ls`,
  (REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; sort_MEM]));;

let getItem_def = define_cases
  [`getItem [] = NONE`;
   `getItem (h :: t) = SOME (h,t)`];;

let nth_def = new_definition
  `nth l i = EL i l`;;

let take_def = new_definition
  `take l i = TAKE i l`;;

let drop_def = new_definition
  `drop l i = DROP i l`;;

let takeUntil_def,takeUntil_ind = define_rec
  [`takeUntil p [] = []`;
   `takeUntil p (x :: xs) = (if p x then [] else x :: takeUntil p
  xs)`];;

let dropUntil_def,dropUntil_ind = define_rec
  [`dropUntil p [] = []`;
   `dropUntil p (x :: xs) = (if p x then x :: xs else dropUntil p
  xs)`];;

let mllist_mapi_def,mllist_mapi_ind = define_rec
  [`mllist_mapi f (n:num) [] = []`;
   `mllist_mapi f (n:num) (h :: t) = (let y = f n h in (y ::
  (mllist_mapi f (n + 1) t)))`];;
hol4_overload "mapi" "mllist_mapi";;

(* [local] *)
let MAPI_thm_gen = prove
 (`!f l x. MAPi (\a. f (a + x)) l = mllist_mapi f x l`,
  (GEN_TAC THEN LIST_INDUCT_TAC THEN
   REWRITE_TAC[MAPi_DEF; mllist_mapi_def; LET_DEF; LET_END_DEF;
     ADD_CLAUSES] THEN
   GEN_TAC THEN REWRITE_TAC[CONS_11] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `x + 1`) THEN DISCH_THEN(SUBST1_TAC o
     SYM) THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM]
     THEN
   REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC));;

let MAPI_thm = prove
 (`!f l. MAPi f l = mllist_mapi f 0 l`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MAPI_thm_gen; ADD_CLAUSES;
    ETA_AX]));;

let mapPartial_def,mapPartial_ind = define_rec
  [`mllist_mapPartial f [] = []`;
   `mllist_mapPartial f (h :: t) = (match (f h) with
        NONE -> mllist_mapPartial f t | (SOME x) -> x ::
          mllist_mapPartial f t)`];;
hol4_overload "mapPartial" "mllist_mapPartial";;

let mapPartial_thm = prove
 (`!f l. mllist_mapPartial f l = MAP THE (FILTER IS_SOME (MAP f l))`,
  CHEAT_TAC);;

let index_find_thm = prove
 (`!x y. OPTION_MAP SND (INDEX_FIND x f l) = OPTION_MAP SND
  (INDEX_FIND y f l)`,
  CHEAT_TAC);;

let FIND_thm = prove
 (`(FIND f [] = NONE) /\
   (!h t. FIND f (h :: t) = (if f h then SOME h else FIND f t))`,
  CHEAT_TAC);;

let partition_aux_def,partition_aux_ind = define_rec
  [`partition_aux f [] pos neg =
        (REVERSE pos,REVERSE neg)`;
   `partition_aux f (h :: t) pos neg = (if f h then partition_aux f
  t (h :: pos) neg else partition_aux f t pos (h :: neg))`];;

let partition_def = new_definition
  `partition (f:'a->bool) l = partition_aux f l [] []`;;

(* [local] *)
let partition_aux_thm = prove
 (`!f l l1 l2.
     partition_aux f l l1 l2 =
     (REVERSE l1 ++ (FILTER f l),REVERSE l2 ++ (FILTER ((~) o f)
       l))`,
  (GEN_TAC THEN LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC[partition_aux_def; FILTER; APPEND_NIL; o_THM] THEN
   REPEAT GEN_TAC THEN COND_CASES_TAC THEN
   ASM_REWRITE_TAC[REVERSE; GSYM APPEND_ASSOC; APPEND]));;

let partition_pos_thm = prove
 (`!f l. FST (partition f l) = FILTER f l`,
  (REWRITE_TAC[partition_def; partition_aux_thm; REVERSE; APPEND]));;

let partition_neg_thm = prove
 (`!f l. SND (partition f l) = FILTER ((~) o f) l`,
  (REWRITE_TAC[partition_def; partition_aux_thm; REVERSE; APPEND]));;

let foldl_def,foldl_ind = define_rec
  [`mllist_foldl f e [] = e`;
   `mllist_foldl f e (h :: t) = mllist_foldl f (f h e) t`];;
hol4_overload "foldl" "mllist_foldl";;

let foldli_aux_def,foldli_aux_ind = define_rec
  [`mllist_foldli_aux f e n [] = e`;
   `mllist_foldli_aux f e n (h :: t) = mllist_foldli_aux f (f n h
  e) (SUC n) t`];;
hol4_overload "foldli_aux" "mllist_foldli_aux";;

let foldli_def = new_definition
  `mllist_foldli f e l = mllist_foldli_aux f e 0 l`;;
hol4_overload "foldli" "mllist_foldli";;

(* [local] *)
let foldli_aux_thm = prove
 (`!l f e n. mllist_foldli_aux f e n l = FOLDRi (\n'. f ((LENGTH l +
  n) - (SUC n'))) e (REVERSE l)`,
  CHEAT_TAC);;

let foldl_intro = prove
 (`!xs x f. FOLDL f x xs = mllist_foldl (\x acc. f acc x) x xs`,
  (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FOLDL; foldl_def]));;

let foldli_thm = prove
 (`!f e l. mllist_foldli f e l = FOLDRi (\n. f (LENGTH l - (SUC n))) e
  (REVERSE l)`,
  CHEAT_TAC);;

(* these definitions are in A normal form in
   order to be able to prove CF specs about them
   (in addition to the translator-generated ones)
   (the CF specs allow more general arguments f) *)

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let tabulate_aux_def,tabulate_aux_ind = define_wf
  `MEASURE (\(n,m,_1,_2). m - n)`
  [`tabulate_aux n m f acc =
     (let b = (n >= m) in
     if b then REVERSE acc else
       let v = f n in
       let n = n + 1 in
       let acc = v :: acc in
       tabulate_aux n m f acc)`];;

let tabulate_def = new_definition
  `mllist_tabulate n f = (let l = [] in tabulate_aux 0 n f l)`;;
hol4_overload "tabulate" "mllist_tabulate";;

let tabulate_aux_GENLIST = prove
 (`!n m f acc. tabulate_aux n m f acc = REVERSE acc ++ GENLIST (f o
  FUNPOW SUC n) (m - n)`,
  CHEAT_TAC);;

let tabulate_GENLIST = prove
 (`!n. mllist_tabulate n f = GENLIST f n`,
  (REWRITE_TAC[tabulate_def; tabulate_aux_GENLIST; LET_DEF;
    LET_END_DEF;
               REVERSE; APPEND; FUNPOW_SUC_PLUS; SUB_0] THEN
   GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[FUN_EQ_THM; o_THM; ADD_CLAUSES]));;

let collate_def,collate_ind = define_guess
  [`mllist_collate f [] [] = EQUAL`;
   `mllist_collate f [] (h :: t) = LESS`;
   `mllist_collate f (h :: t) [] = GREATER`;
   `mllist_collate f (h1 :: t1) (h2 :: t2) =
        (if f h1 h2 = EQUAL then mllist_collate f t1 t2 else f
          h1 h2)`];;
hol4_overload "collate" "mllist_collate";;

let collate_equal_thm = prove
 (`!l. (!x. MEM x l ==> (f x x = EQUAL)) ==> (mllist_collate f l l =
  EQUAL)`,
  (LIST_INDUCT_TAC THEN REWRITE_TAC[collate_def; MEM] THEN
   STRIP_TAC THEN ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_MESON_TAC[]));;

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
  [`LENGTH_AUX [] (n:num) = (n:num)`;
   `LENGTH_AUX (x :: xs) (n:num) = ((LENGTH_AUX xs (n + 1)):num)`];;

(* HOL4 mllistScript.sml:572-575: a theorem that HOL4 states as the
   value of an ML expression: LENGTH_AUX_THM *)

(* HOL4 mllistScript.sml:577-578: a theorem that HOL4 states as the
   value of an ML expression: list_compare_def *)

(* tail-recursive MAP *)

let map_rev'_def,map_rev'_ind = define_rec
  [`map_rev' f [] acc = acc`;
   `map_rev' f (x :: xs) acc = map_rev' f xs (f x :: acc)`];;

let map_rev_def = new_definition
  `map_rev f xs = map_rev' f xs []`;;

(* [local] *)
let map_rev'_lemma = prove
 (`!acc. map_rev' f xs acc = (map_rev' f xs []) ++ acc`,
  (SPEC_TAC(`xs:A list`,`xs:A list`) THEN LIST_INDUCT_TAC THEN
   REWRITE_TAC[map_rev'_def; APPEND] THEN GEN_TAC THEN
   FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV)
     [th]) THEN
   FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
   REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]));;

let map_rev_thm = prove
 (`map_rev f xs = REVERSE (MAP f xs)`,
  (REWRITE_TAC[map_rev_def] THEN SPEC_TAC(`xs:A list`,`xs:A list`)
    THEN
   LIST_INDUCT_TAC THEN REWRITE_TAC[map_rev'_def; MAP; REVERSE] THEN
   ONCE_REWRITE_TAC[map_rev'_lemma] THEN ASM_REWRITE_TAC[APPEND]));;

(* tail-recursive FILTER *)

let filter_rev'_def,filter_rev'_ind = define_rec
  [`filter_rev' P [] acc = acc`;
   `filter_rev' P (h :: t) acc = (if P h then filter_rev' P t (h ::
  acc) else filter_rev' P t acc)`];;

let filter_rev_def = new_definition
  `filter_rev P xs = filter_rev' P xs []`;;

(* [local] *)
let filter_rev'_lemma = prove
 (`!acc. filter_rev' P xs acc = (filter_rev' P xs []) ++ acc`,
  (SPEC_TAC(`xs:A list`,`xs:A list`) THEN LIST_INDUCT_TAC THEN
   REWRITE_TAC[filter_rev'_def; APPEND] THEN GEN_TAC THEN
     COND_CASES_TAC THEN
   REWRITE_TAC[] THEN
   FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV)
     [th]) THEN
   FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
   REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]));;

let filter_rev_thm = prove
 (`filter_rev f xs = REVERSE (FILTER f xs)`,
  (REWRITE_TAC[filter_rev_def] THEN SPEC_TAC(`xs:A list`,`xs:A list`)
    THEN
   LIST_INDUCT_TAC THEN REWRITE_TAC[filter_rev'_def; FILTER; REVERSE]
     THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[REVERSE] THEN
   ONCE_REWRITE_TAC[filter_rev'_lemma] THEN ASM_REWRITE_TAC[APPEND;
     APPEND_NIL]));;

(* tail-recursive FLAT *)

let flat_rev'_def,flat_rev'_ind = define_rec
  [`flat_rev' [] acc = acc`;
   `flat_rev' (x :: xs) acc = flat_rev' xs (REV x acc)`];;

let flat_rev_def = new_definition
  `flat_rev xs = flat_rev' xs []`;;

(* [local] *)
let flat_rev'_lemma = prove
 (`!acc. flat_rev' l acc = (flat_rev' l []) ++ acc`,
  CHEAT_TAC);;

let flat_rev_thm = prove
 (`flat_rev xs = REVERSE (FLAT xs)`,
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["length";
   "negate"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
