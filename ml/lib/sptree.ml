(* ======================================================== *)
(*  sptree: ported from HOL4's
    src/finite_maps/sptreeScript.sml  *)
(* ======================================================== *)

(* this file needs nothing of the port *)
(* HOL4 ancestors outside the port: arithmetic logroot list alist
   pred_set rich_list *)

let spt_INDUCT,spt_RECURSION = define_datatype
  "spt = LN | LS ('a) | BN (spt) (spt) | BS (spt) ('a) (spt)";;

(* HOL4 sptreeScript.sml:34: the type abbreviation num_map, which the
   port expands *)
new_type_abbrev("sptree_num_set",`: 1 spt`);;

(* HOL4 sptreeScript.sml:37: the overload isEmpty, which the port
   expands *)

let wf_def = cake_define_list
  [`sptree_wf LN <=> T`;
   `sptree_wf (LS a) <=> T`;
   `sptree_wf (BN t1 t2) <=> sptree_wf t1 /\ sptree_wf t2 /\ ~((\t. t
  = LN) t1 /\ (\t. t = LN) t2)`;
   `sptree_wf (BS t1 a t2) <=> sptree_wf t1 /\ sptree_wf t2 /\
  ~((\t. t = LN) t1 /\ (\t. t = LN) t2)`];;
hol4_overload "wf" "sptree_wf";;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 sptreeScript.sml:46-56: the tactic that proves the
   termination *)
let lookup_def = cake_define_list_try (fun () ->
  `MEASURE FST`)
  [`sptree_lookup k LN = NONE`;
   `sptree_lookup k (LS a) = (if k = 0 then SOME a else NONE)`;
   `sptree_lookup k (BN t1 t2) =
         (if k = 0 then NONE else sptree_lookup ((k - 1) DIV 2)
           (if EVEN k then t1 else t2))`;
   `sptree_lookup k (BS t1 a t2) =
         (if k = 0 then SOME a else sptree_lookup ((k - 1) DIV
           2) (if EVEN k then t1 else t2))`];;
hol4_overload "lookup" "sptree_lookup";;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 sptreeScript.sml:83-85: the tactic that proves the
   termination *)
let insert_def = cake_define_list_try (fun () ->
  `MEASURE FST`)
  [`sptree_insert k a LN = (if k = 0 then LS a else if EVEN k then BN
  (sptree_insert ((k - 1) DIV 2) a LN) LN else BN LN (sptree_insert
  ((k - 1) DIV 2) a LN))`;
   `sptree_insert k a (LS a') =
         (if k = 0 then LS a else if EVEN k then BS
           (sptree_insert ((k - 1) DIV 2) a LN) a' LN else BS LN a'
           (sptree_insert ((k - 1) DIV 2) a LN))`;
   `sptree_insert k a (BN t1 t2) =
         (if k = 0 then BS t1 a t2 else if EVEN k then BN
           (sptree_insert ((k - 1) DIV 2) a t1) t2 else BN t1
           (sptree_insert ((k - 1) DIV 2) a t2))`;
   `sptree_insert k a (BS t1 a' t2) =
         (if k = 0 then BS t1 a t2 else if EVEN k then BS
           (sptree_insert ((k - 1) DIV 2) a t1) a' t2 else BS t1 a'
           (sptree_insert ((k - 1) DIV 2) a t2))`];;
hol4_overload "insert" "sptree_insert";;

let mk_BN_def = cake_define
  `mk_BN t1 t2 =
        match (t1,t2) with
          (LN,LN) -> LN
        | (t1,t2) -> BN t1 t2`;;

let mk_BS_def = cake_define
  `mk_BS t1 x t2 =
        match (t1,t2) with
          (LN,LN) -> LS x
        | (t1,t2) -> BS t1 x t2`;;

let delete_def = cake_define_list
  [`sptree_delete k LN = LN`;
   `sptree_delete k (LS a) = (if k = 0 then LN else LS a)`;
   `sptree_delete k (BN t1 t2) =
         (if k = 0 then BN t1 t2 else if EVEN k then
           mk_BN (sptree_delete ((k - 1) DIV 2) t1) t2 else
           mk_BN t1 (sptree_delete ((k - 1) DIV 2) t2))`;
   `sptree_delete k (BS t1 a t2) =
         (if k = 0 then BN t1 t2 else if EVEN k then
           mk_BS (sptree_delete ((k - 1) DIV 2) t1) a t2 else
           mk_BS t1 a (sptree_delete ((k - 1) DIV 2) t2))`];;
hol4_overload "delete" "sptree_delete";;

let fromList_def = cake_define
  `sptree_fromList l = SND (FOLDL (\(i,t) a. (i + 1,sptree_insert i a
  t)) (0,LN) l)`;;
hol4_overload "fromList" "sptree_fromList";;

let size_def = cake_define_list
  [`sptree_size LN = 0`;
   `sptree_size (LS a) = 1`;
   `sptree_size (BN t1 t2) = sptree_size t1 + sptree_size t2`;
   `sptree_size (BS t1 a t2) = sptree_size t1 + sptree_size t2 + 1`];;
hol4_overload "size" "sptree_size";;

let union_def = cake_define_list
  [`sptree_union LN t = t`;
   `sptree_union (LS a) t =
         (match t with LN -> LS a | LS b -> LS a | BN t1 t2 -> BS
           t1 a t2 | BS t1 _2 t2 -> BS t1 a t2)`;
   `sptree_union (BN t1 t2) t =
         (match t with LN -> BN t1 t2 | LS a -> BS t1 a t2 | BN
           t1' t2' -> BN (sptree_union t1 t1') (sptree_union t2 t2')
           | BS t1' a t2' -> BS (sptree_union t1 t1') a (sptree_union
           t2 t2'))`;
   `sptree_union (BS t1 a t2) t =
         (match t with LN -> BS t1 a t2 | LS a' -> BS t1 a t2 |
           BN t1' t2' -> BS (sptree_union t1 t1') a (sptree_union
           t2 t2') | BS t1' a' t2' -> BS (sptree_union t1 t1') a
           (sptree_union t2 t2'))`];;
hol4_overload "union" "sptree_union";;

let inter_def = cake_define_list
  [`inter LN t = LN`;
   `inter (LS a) t =
         (match t with LN -> LN | LS b -> LS a | BN t1 t2 -> LN |
           BS t1 _4 t2 -> LS a)`;
   `inter (BN t1 t2) t =
         (match t with LN -> LN | LS a -> LN | BN t1' t2' ->
           mk_BN (inter t1 t1') (inter t2 t2') | BS t1' a t2' ->
           mk_BN (inter t1 t1') (inter t2 t2'))`;
   `inter (BS t1 a t2) t =
         (match t with LN -> LN | LS a' -> LS a | BN t1' t2' ->
           mk_BN (inter t1 t1') (inter t2 t2') | BS t1' a' t2' ->
           mk_BS (inter t1 t1') a (inter t2 t2'))`];;

let inter_eq_def = cake_define_list
  [`inter_eq LN t = LN`;
   `inter_eq (LS a) t =
         (match t with LN -> LN | LS b -> (if a = b then LS a
           else LN) | BN t1 t2 -> LN | BS t1 b t2 -> (if a = b then
           LS a else LN))`;
   `inter_eq (BN t1 t2) t =
         (match t with LN -> LN | LS a -> LN | BN t1' t2' ->
           mk_BN (inter_eq t1 t1') (inter_eq t2 t2') | BS t1' a t2'
           -> mk_BN (inter_eq t1 t1') (inter_eq t2 t2'))`;
   `inter_eq (BS t1 a t2) t =
         (match t with LN -> LN | LS a' -> (if a' = a then LS a else
           LN) | BN t1' t2' -> mk_BN (inter_eq t1 t1') (inter_eq t2 t2')
           | BS t1' a' t2' ->
               (if a' = a then
                 mk_BS (inter_eq t1 t1') a (inter_eq t2 t2')
                   else mk_BN (inter_eq t1 t1') (inter_eq t2 t2')))`];;

let difference_def = cake_define_list
  [`difference LN t = LN`;
   `difference (LS a) t =
         (match t with LN -> LS a | LS b -> LN | BN t1 t2 -> LS a
           | BS t1 b t2 -> LN)`;
   `difference (BN t1 t2) t =
         (match t with LN -> BN t1 t2 | LS a -> BN t1 t2 | BN t1'
           t2' -> mk_BN (difference t1 t1') (difference t2 t2') | BS
           t1' a t2' -> mk_BN (difference t1 t1') (difference t2
           t2'))`;
   `difference (BS t1 a t2) t =
         (match t with LN -> BS t1 a t2 | LS a' -> BN t1 t2 |
           BN t1' t2' -> mk_BS (difference t1 t1') a (difference t2
           t2') | BS t1' a' t2' -> mk_BN (difference t1 t1')
           (difference t2 t2'))`];;

(* HOL4 sptreeScript.sml:423-425: the tactic that proves the
   termination *)
let lrnext_def = cake_define_wf
  `MEASURE I`
  `lrnext n = (if n = 0 then 1 else 2 * lrnext ((n - 1) DIV 2))`;;

let domain_def = cake_define_list
  [`domain LN = {}`;
   `domain (LS _5) = {0}`;
   `domain (BN t1 t2) =
       IMAGE (\n. 2 * n + 2) (domain t1) UNION
       IMAGE (\n. 2 * n + 1) (domain t2)`;
   `domain (BS t1 _6 t2) =
       {0} UNION IMAGE (\n. 2 * n + 2) (domain t1) UNION
       IMAGE (\n. 2 * n + 1) (domain t2)`];;

let foldi_def = cake_define_list
  [`foldi f i acc LN = acc`;
   `foldi f i acc (LS a) = f i a acc`;
   `foldi f i acc (BN t1 t2) =
         (let inc = lrnext i in
           foldi f (i + inc) (foldi f (i + 2 * inc) acc t1) t2)`;
   `foldi f i acc (BS t1 a t2) =
         (let inc = lrnext i in
           foldi f (i + inc) (f i a (foldi f (i + 2 * inc) acc
             t1)) t2)`];;

let mapi0_def = cake_define_list
  [`mapi0 f i LN = LN`;
   `mapi0 f i (LS a) = LS (f i a)`;
   `mapi0 f i (BN t1 t2) =
       (let inc = lrnext i in
         mk_BN (mapi0 f (i + 2 * inc) t1) (mapi0 f (i + inc) t2))`;
   `mapi0 f i (BS t1 a t2) =
       (let inc = lrnext i in
         mk_BS (mapi0 f (i + 2 * inc) t1) (f i a) (mapi0 f (i +
           inc) t2))`];;

let mapi_def = cake_define
  `sptree_mapi f pt = mapi0 f 0 pt`;;
hol4_overload "mapi" "sptree_mapi";;

let toAList_def = cake_define
  `toAList = foldi (\k v a. (k,v) :: a) 0 []`;;

let toListA_def = cake_define_list
  [`toListA acc LN = acc`;
   `toListA acc (LS a) = a :: acc`;
   `toListA acc (BN t1 t2) = toListA (toListA acc t2) t1`;
   `toListA acc (BS t1 a t2) = toListA (a :: toListA acc t2) t1`];;

let toList_def = cake_define
  `sptree_toList m = toListA [] m`;;
hol4_overload "toList" "sptree_toList";;

let mk_wf_def = cake_define_list
  [`mk_wf LN = LN`;
   `mk_wf (LS x) = LS x`;
   `mk_wf (BN t1 t2) = mk_BN (mk_wf t1) (mk_wf t2)`;
   `mk_wf (BS t1 x t2) = mk_BS (mk_wf t1) x (mk_wf t2)`];;

let fromAList_def = cake_define_list
  [`fromAList [] = LN`;
   `fromAList ((x,y) :: xs) = sptree_insert x y (fromAList xs)`];;

let map_def = cake_define_list
  [`sptree_map f LN = LN`;
   `sptree_map f (LS a) = (LS (f a))`;
   `sptree_map f (BN t1 t2) = BN (sptree_map f t1) (sptree_map f t2)`;
   `sptree_map f (BS t1 a t2) = BS (sptree_map f t1) (f a)
  (sptree_map f t2)`];;
hol4_overload "map" "sptree_map";;

let spt_left_def = cake_define_list
  [`spt_left LN = LN`;
   `spt_left (LS x) = LN`;
   `spt_left (BN t1 t2) = t1`;
   `spt_left (BS t1 x t2) = t1`];;

let spt_right_def = cake_define_list
  [`spt_right LN = LN`;
   `spt_right (LS x) = LN`;
   `spt_right (BN t1 t2) = t2`;
   `spt_right (BS t1 x t2) = t2`];;

let spt_center_def = cake_define
  `spt_center x1 =
        match x1 with
          LS x -> SOME x
        | (BS t1 x t2) -> SOME x
        | _7 -> NONE`;;

let subspt_eq = cake_define_list
  [`subspt LN t <=> T`;
   `subspt (LS x) t <=> (spt_center t = SOME x)`;
   `subspt (BN t1 t2) t <=>
         subspt t1 (spt_left t) /\ subspt t2 (spt_right t)`;
   `subspt (BS t1 x t2) t <=>
         (spt_center t = SOME x) /\
         subspt t1 (spt_left t) /\ subspt t2 (spt_right t)`];;

let filter_v_def = cake_define_list
  [`filter_v f LN = LN`;
   `filter_v f (LS x) = (if f x then LS x else LN)`;
   `filter_v f (BN l r) = mk_BN (filter_v f l) (filter_v f r)`;
   `filter_v f (BS l x r) =
        (if f x then mk_BS (filter_v f l) x (filter_v f r) else
          mk_BN (filter_v f l) (filter_v f r))`];;

let spt_fold_def = cake_define_list
  [`spt_fold f acc LN = acc`;
   `spt_fold f acc (LS a) = f a acc`;
   `spt_fold f acc (BN t1 t2) = spt_fold f (spt_fold f acc t1) t2`;
   `spt_fold f acc (BS t1 a t2) = spt_fold f (f a (spt_fold f acc
  t1)) t2`];;

let list_to_num_set_def = cake_define_list
  [`list_to_num_set [] = LN`;
   `list_to_num_set (n :: ns) = sptree_insert n one
  (list_to_num_set ns)`];;

let list_insert_def = cake_define_list
  [`list_insert [] t = t`;
   `list_insert (n :: ns) t = list_insert ns (sptree_insert n one
  t)`];;

let alist_insert_def = cake_define
  `alist_insert vs xs t =
      match (vs,xs) with
        ([],xs) -> t
      | (vs,[]) -> t
      | ((v :: vs),(x :: xs)) -> sptree_insert v x (alist_insert
        vs xs t)`;;

let spts_to_alist_add_pause_def = cake_define
  `spts_to_alist_add_pause j q = (match q with [] -> [(j,LN)] |
  ((i,spt) :: q) -> ((i + j,spt) :: q))`;;

(* HOL4 sptreeScript.sml:2378: the overload add_pause, which the port
   expands *)

let spts_to_alist_aux_def = cake_define
  `spts_to_alist_aux i xs acc_cent acc_right acc_left repeat =
     (match xs with [] -> (i,REVERSE acc_right ++ REVERSE
       acc_left,acc_cent,repeat) | (j,spt) :: ys ->
       (if (\t. t = LN) spt then spts_to_alist_aux (i + j) ys
         acc_cent
         (spts_to_alist_add_pause j acc_right)
           (spts_to_alist_add_pause j acc_left)
         repeat else spts_to_alist_aux (i + j) ys
         ((match spt_center spt with NONE -> [] | SOME c -> [(i,c)])
           ++ acc_cent)
         ((j,spt_right spt) :: acc_right) ((j,spt_left spt) ::
           acc_left)
         T))`;;

let _ = size_thms "spt";;
(* HOL4 sptreeScript.sml:2436-2442: the tactic that proves the
   termination *)
let spts_to_alist_def = cake_define_wf
  `MEASURE (\(_8,xs,_9). SUM (MAP (spt_size (K 0) o SND) xs))`
  `spts_to_alist i xs acc_cent =
     (let (i,xs,acc_cent,repeat) =
       spts_to_alist_aux i xs acc_cent [] [] F in
     if repeat then spts_to_alist i xs acc_cent else REVERSE
       acc_cent)`;;

let toSortedAList_def = cake_define
  `toSortedAList spt = spts_to_alist 0 [(1,spt)] []`;;
