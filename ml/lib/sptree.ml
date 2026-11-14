(* ======================================================== *)
(*  sptree: ported from HOL4's
    src/finite_maps/sptreeScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs, and 83 theorems of it from LightCake.  Needed
    by 106 files of the port.  *)
(* ======================================================== *)

needs "lib/indexedLists.ml";;

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: arithmetic logroot list alist
   pred_set rich_list *)

let spt_INDUCT,spt_RECURSION = define_datatype
  "spt = LN | LS ('a) | BN (spt) (spt) | BS (spt) ('a) (spt)";;

(* HOL4 sptreeScript.sml:34: the type abbreviation num_map, which the
   port expands *)
new_type_abbrev("sptree_num_set",`: 1 spt`);;

(* HOL4 sptreeScript.sml:37: the overload isEmpty, which the port
   expands *)

let wf_def,wf_ind = define_rec
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
let lookup_def,lookup_ind = define_wf
  `MEASURE FST`
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
let insert_def,insert_ind = define_wf
  `MEASURE FST`
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

let mk_BN_def = new_definition
  `mk_BN t1 t2 =
        match (t1,t2) with
          (LN,LN) -> LN
        | (t1,t2) -> BN t1 t2`;;

let mk_BS_def = new_definition
  `mk_BS t1 x t2 =
        match (t1,t2) with
          (LN,LN) -> LS x
        | (t1,t2) -> BS t1 x t2`;;

let delete_def,delete_ind = define_rec
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

let fromList_def = new_definition
  `sptree_fromList l = SND (FOLDL (\(i,t) a. (i + 1,sptree_insert i a
  t)) (0,LN) l)`;;
hol4_overload "fromList" "sptree_fromList";;

let size_def,size_ind = define_rec
  [`sptree_size LN = 0`;
   `sptree_size (LS a) = 1`;
   `sptree_size (BN t1 t2) = sptree_size t1 + sptree_size t2`;
   `sptree_size (BS t1 a t2) = sptree_size t1 + sptree_size t2 + 1`];;
hol4_overload "size" "sptree_size";;

let union_def,union_ind = define_rec
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

let inter_def,inter_ind = define_rec
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

let inter_eq_def,inter_eq_ind = define_rec
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

let difference_def,difference_ind = define_rec
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

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 sptreeScript.sml:423-425: the tactic that proves the
   termination *)
let lrnext_def,lrnext_ind = define_wf
  `MEASURE I`
  [`lrnext n = (if n = 0 then 1 else 2 * lrnext ((n - 1) DIV 2))`];;

let _ = size_thms "spt";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let domain_def,domain_ind = define_wf
  `MEASURE (\x0. spt_size (\x. 0) x0)`
  [`domain LN = {}`;
   `domain (LS _5) = {0}`;
   `domain (BN t1 t2) =
       IMAGE (\n. 2 * n + 2) (domain t1) UNION
       IMAGE (\n. 2 * n + 1) (domain t2)`;
   `domain (BS t1 _6 t2) =
       {0} UNION IMAGE (\n. 2 * n + 2) (domain t1) UNION
       IMAGE (\n. 2 * n + 1) (domain t2)`];;

let foldi_def,foldi_ind = define_rec
  [`foldi f i acc LN = acc`;
   `foldi f i acc (LS a) = f i a acc`;
   `foldi f i acc (BN t1 t2) =
         (let inc = lrnext i in
           foldi f (i + inc) (foldi f (i + 2 * inc) acc t1) t2)`;
   `foldi f i acc (BS t1 a t2) =
         (let inc = lrnext i in
           foldi f (i + inc) (f i a (foldi f (i + 2 * inc) acc
             t1)) t2)`];;

let mapi0_def,mapi0_ind = define_rec
  [`mapi0 f i LN = LN`;
   `mapi0 f i (LS a) = LS (f i a)`;
   `mapi0 f i (BN t1 t2) =
       (let inc = lrnext i in
         mk_BN (mapi0 f (i + 2 * inc) t1) (mapi0 f (i + inc) t2))`;
   `mapi0 f i (BS t1 a t2) =
       (let inc = lrnext i in
         mk_BS (mapi0 f (i + 2 * inc) t1) (f i a) (mapi0 f (i +
           inc) t2))`];;

let mapi_def = new_definition
  `sptree_mapi f pt = mapi0 f 0 pt`;;
hol4_overload "mapi" "sptree_mapi";;

let toAList_def = new_definition
  `toAList = foldi (\k v a. CONS (k,v) a) 0 []`;;

let toListA_def,toListA_ind = define_rec
  [`toListA acc LN = acc`;
   `toListA acc (LS a) = CONS a acc`;
   `toListA acc (BN t1 t2) = toListA (toListA acc t2) t1`;
   `toListA acc (BS t1 a t2) = toListA (CONS a (toListA acc t2)) t1`];;

let toList_def = new_definition
  `sptree_toList m = toListA [] m`;;
hol4_overload "toList" "sptree_toList";;

let mk_wf_def,mk_wf_ind = define_rec
  [`mk_wf LN = LN`;
   `mk_wf (LS x) = LS x`;
   `mk_wf (BN t1 t2) = mk_BN (mk_wf t1) (mk_wf t2)`;
   `mk_wf (BS t1 x t2) = mk_BS (mk_wf t1) x (mk_wf t2)`];;

let fromAList_def,fromAList_ind = define_rec
  [`fromAList [] = LN`;
   `fromAList (CONS (x,y) xs) = sptree_insert x y (fromAList xs)`];;

let map_def,map_ind = define_rec
  [`sptree_map f LN = LN`;
   `sptree_map f (LS a) = (LS (f a))`;
   `sptree_map f (BN t1 t2) = BN (sptree_map f t1) (sptree_map f t2)`;
   `sptree_map f (BS t1 a t2) = BS (sptree_map f t1) (f a)
  (sptree_map f t2)`];;
hol4_overload "map" "sptree_map";;

let spt_left_def = define_cases
  [`spt_left LN = LN`;
   `spt_left (LS x) = LN`;
   `spt_left (BN t1 t2) = t1`;
   `spt_left (BS t1 x t2) = t1`];;

let spt_right_def = define_cases
  [`spt_right LN = LN`;
   `spt_right (LS x) = LN`;
   `spt_right (BN t1 t2) = t2`;
   `spt_right (BS t1 x t2) = t2`];;

let spt_center_def = new_definition
  `spt_center x1 =
        match x1 with
          LS x -> SOME x
        | (BS t1 x t2) -> SOME x
        | _7 -> NONE`;;

let subspt_eq,subspt_eq_ind = define_rec
  [`subspt LN t <=> T`;
   `subspt (LS x) t <=> (spt_center t = SOME x)`;
   `subspt (BN t1 t2) t <=>
         subspt t1 (spt_left t) /\ subspt t2 (spt_right t)`;
   `subspt (BS t1 x t2) t <=>
         (spt_center t = SOME x) /\
         subspt t1 (spt_left t) /\ subspt t2 (spt_right t)`];;

let filter_v_def,filter_v_ind = define_rec
  [`filter_v f LN = LN`;
   `filter_v f (LS x) = (if f x then LS x else LN)`;
   `filter_v f (BN l r) = mk_BN (filter_v f l) (filter_v f r)`;
   `filter_v f (BS l x r) =
        (if f x then mk_BS (filter_v f l) x (filter_v f r) else
          mk_BN (filter_v f l) (filter_v f r))`];;

let spt_fold_def,spt_fold_ind = define_rec
  [`spt_fold f acc LN = acc`;
   `spt_fold f acc (LS a) = f a acc`;
   `spt_fold f acc (BN t1 t2) = spt_fold f (spt_fold f acc t1) t2`;
   `spt_fold f acc (BS t1 a t2) = spt_fold f (f a (spt_fold f acc
  t1)) t2`];;

let list_to_num_set_def,list_to_num_set_ind = define_rec
  [`list_to_num_set [] = LN`;
   `list_to_num_set (CONS n ns) = sptree_insert n one
  (list_to_num_set ns)`];;

let list_insert_def,list_insert_ind = define_rec
  [`list_insert [] t = t`;
   `list_insert (CONS n ns) t = list_insert ns (sptree_insert n one
  t)`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let alist_insert_def,alist_insert_ind = define_wf
  `MEASURE (\(x0,x1,x2). list_size (\n. n) x0)`
  [`alist_insert vs xs t =
      match (vs,xs) with
        ([],xs) -> t
      | (vs,[]) -> t
      | ((CONS v vs),(CONS x xs)) -> sptree_insert v x
        (alist_insert vs xs t)`];;

let spts_to_alist_add_pause_def = new_definition
  `spts_to_alist_add_pause j q = (match q with [] -> [(j,LN)] | (CONS
  (i,spt) q) -> (CONS (i + j,spt) q))`;;

(* HOL4 sptreeScript.sml:2378: the overload add_pause, which the port
   expands *)

let spts_to_alist_aux_def,spts_to_alist_aux_ind = define_shaped_rec
  "match"
  [`spts_to_alist_aux i xs acc_cent acc_right acc_left repeat =
     (match xs with [] -> (i,APPEND (REVERSE acc_right) (REVERSE
       acc_left),acc_cent,repeat) | CONS (j,spt) ys ->
       (if (\t. t = LN) spt then spts_to_alist_aux (i + j) ys
         acc_cent
         (spts_to_alist_add_pause j acc_right)
           (spts_to_alist_add_pause j acc_left)
         repeat else spts_to_alist_aux (i + j) ys
         (APPEND (match spt_center spt with NONE -> [] | SOME c ->
           [(i,c)]) acc_cent)
         (CONS (j,spt_right spt) acc_right) (CONS (j,spt_left spt)
           acc_left)
         T))`];;

(* the termination relation that HOL4 gives is
     MEASURE (\(_8,xs,_9). SUM (MAP (spt_size (K 0) o SND) xs))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 sptreeScript.sml:2436-2442: the tactic that proves the
   termination *)
let spts_to_alist_def,spts_to_alist_ind = define_guess
  [`spts_to_alist i xs acc_cent =
     (let (i,xs,acc_cent,repeat) =
       spts_to_alist_aux i xs acc_cent [] [] F in
     if repeat then spts_to_alist i xs acc_cent else REVERSE
       acc_cent)`];;

let toSortedAList_def = new_definition
  `toSortedAList spt = spts_to_alist 0 [(1,spt)] []`;;

(* ================================================================== *)
(*  The theorems of sptreeTheory that a proof of phase three asks     *)
(*  for.  A key is read as a path by its lowest bit (EVEN k) and      *)
(*  (k - 1) DIV 2, so the arithmetic of that encoding comes first:    *)
(*  a key that is not 0 is 2 * ((k - 1) DIV 2) + 2 when it is even    *)
(*  and + 1 when it is odd, which makes the step of a path            *)
(*  injective.                                                        *)
(* ================================================================== *)

let SPT_BIT_DECOMP = prove
 (`!k. ~(k = 0)
       ==> 2 * ((k - 1) DIV 2) + (if EVEN k then 2 else 1) = k`,
  GEN_TAC THEN ASM_CASES_TAC `EVEN k` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `2 * m - 1 = 2 * (m - 1) + 1` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(2 * m + 1) DIV 2 = m`] THEN
    ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o
                  REWRITE_RULE[NOT_EVEN; ODD_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
    DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE `SUC (2 * m) - 1 = 2 * m`;
                ARITH_RULE `(2 * m) DIV 2 = m`] THEN
    ARITH_TAC]);;

let SPT_BIT_EQ = prove
 (`!k1 k2. ~(k1 = 0) /\ ~(k2 = 0) /\
           (k1 - 1) DIV 2 = (k2 - 1) DIV 2 /\ (EVEN k1 <=> EVEN k2)
           ==> k1 = k2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `k1:num` SPT_BIT_DECOMP) THEN
  MP_TAC(SPEC `k2:num` SPT_BIT_DECOMP) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let SPT_BIT_EQ_EQ = prove
 (`!k1 k2. ~(k1 = 0) /\ ~(k2 = 0)
           ==> ((k1 = k2) <=>
                (EVEN k1 <=> EVEN k2) /\
                (k1 - 1) DIV 2 = (k2 - 1) DIV 2)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    STRIP_TAC THEN MATCH_MP_TAC SPT_BIT_EQ THEN ASM_REWRITE_TAC[]]);;

let SPT_DIV2_LT = prove
 (`!k. ~(k = 0) ==> (k - 1) DIV 2 < k`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k - 1`; `2`] DIV_LE) THEN ASM_ARITH_TAC);;

let SPT_BIT_EVEN = prove
 (`!n m. (n = 2 * m + 2) <=>
         ~(n = 0) /\ EVEN n /\ (n - 1) DIV 2 = m`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ARITH_RULE `~(2 * m + 2 = 0)`;
                ARITH_RULE `(2 * m + 2) - 1 = 2 * m + 1`;
                ARITH_RULE `(2 * m + 1) DIV 2 = m`] THEN
    REWRITE_TAC[EVEN_EXISTS] THEN EXISTS_TAC `m + 1` THEN ARITH_TAC;
    STRIP_TAC THEN MP_TAC(SPEC `n:num` SPT_BIT_DECOMP) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let SPT_BIT_ODD = prove
 (`!n m. (n = 2 * m + 1) <=>
         ~(n = 0) /\ ~EVEN n /\ (n - 1) DIV 2 = m`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ARITH_RULE `~(2 * m + 1 = 0)`;
                ARITH_RULE `(2 * m + 1) - 1 = 2 * m`;
                ARITH_RULE `(2 * m) DIV 2 = m`] THEN
    REWRITE_TAC[NOT_EVEN; ODD_EXISTS] THEN EXISTS_TAC `m:num` THEN
    ARITH_TAC;
    STRIP_TAC THEN MP_TAC(SPEC `n:num` SPT_BIT_DECOMP) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* the lookup of an insert, by induction on the key: the insert goes
   down the path of k2 and the lookup down the path of k1, and the
   two paths meet exactly where the keys are equal *)

let lookup_insert = prove
 (`!k2 k1 v (t:(A)spt).
     sptree_lookup k1 (sptree_insert k2 v t) =
     (if k1 = k2 then SOME v else sptree_lookup k1 t)`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `k2:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `k2 = 0` THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(ISPEC `t:(A)spt` (cases_of `:(A)spt`)) THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
      [insert_def] THEN
    REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [lookup_def] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
      [lookup_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!k1 v (t:(A)spt).
       sptree_lookup k1 (sptree_insert ((k2 - 1) DIV 2) v t) =
       (if k1 = (k2 - 1) DIV 2 then SOME v else sptree_lookup k1 t)`
    ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[SPT_DIV2_LT];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(k1 = k2) <=>
                ~(k1 = 0) /\ (EVEN k1 <=> EVEN k2) /\
                (k1 - 1) DIV 2 = (k2 - 1) DIV 2`
    SUBST1_TAC THENL
   [EQ_TAC THENL
     [DISCH_TAC THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN MATCH_MP_TAC SPT_BIT_EQ THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `t:(A)spt` (cases_of `:(A)spt`)) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
    [insert_def] THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [lookup_def] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [lookup_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[CONJUNCT1(lookup_def)]);;

(* and the domain as the keys that the lookup gives a value *)

let domain_lookup = prove
 (`!(t:(A)spt) n. n IN domain t <=> ?v. sptree_lookup n t = SOME v`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[domain_def; lookup_def;
                NOT_IN_EMPTY; distinctness "option"];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[domain_def; lookup_def;
                IN_SING] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
    MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
    REWRITE_TAC[domain_def; IN_UNION; IN_IMAGE] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
      [lookup_def] THEN
    ASM_CASES_TAC `n = 0` THEN
    ASM_REWRITE_TAC[distinctness "option";
                    ARITH_RULE `~(0 = 2 * m + 2)`;
                    ARITH_RULE `~(0 = 2 * m + 1)`] THEN
    TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SPT_BIT_EVEN; SPT_BIT_ODD];
    REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
    REWRITE_TAC[domain_def; IN_UNION; IN_IMAGE; IN_SING] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
      [lookup_def] THEN
    ASM_CASES_TAC `n = 0` THEN
    ASM_REWRITE_TAC[distinctness "option"; injectivity "option";
                    ARITH_RULE `~(0 = 2 * m + 2)`;
                    ARITH_RULE `~(0 = 2 * m + 1)`] THEN
    TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SPT_BIT_EVEN; SPT_BIT_ODD]]);;

(* and HOL4's lookup_NONE_domain *)

let lookup_NONE_domain = prove
 (`!n (t:(A)spt). (sptree_lookup n t = NONE) <=> ~(n IN domain t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[domain_lookup] THEN
  STRUCT_CASES_TAC(ISPEC `sptree_lookup n (t:(A)spt)`
                         (cases_of `:(A)option`)) THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  MESON_TAC[]);;

(* the lookup in the smart constructors, which delete uses: they
   give the LN or the LS where the children are empty, and the
   lookup is the same as in the plain constructor *)

let lookup_mk_BN = prove
 (`!k t1 (t2:(A)spt).
     sptree_lookup k (mk_BN t1 t2) = sptree_lookup k (BN t1 t2)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [mk_BN_def] THEN
  STRUCT_CASES_TAC(ISPEC `t1:(A)spt` (cases_of `:(A)spt`)) THEN
  STRUCT_CASES_TAC(ISPEC `t2:(A)spt` (cases_of `:(A)spt`)) THEN
  MATCH_REDUCE_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[lookup_def; COND_ID] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[lookup_def; COND_ID]);;

let lookup_mk_BS = prove
 (`!k t1 x (t2:(A)spt).
     sptree_lookup k (mk_BS t1 x t2) = sptree_lookup k (BS t1 x t2)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [mk_BS_def] THEN
  STRUCT_CASES_TAC(ISPEC `t1:(A)spt` (cases_of `:(A)spt`)) THEN
  STRUCT_CASES_TAC(ISPEC `t2:(A)spt` (cases_of `:(A)spt`)) THEN
  MATCH_REDUCE_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[lookup_def; COND_ID] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[lookup_def; COND_ID]);;

(* the lookup of a delete: HOL4 sptreeScript.sml:717 *)

let lookup_delete = prove
 (`!(t:(A)spt) k1 k2.
     sptree_lookup k1 (sptree_delete k2 t) =
     (if k1 = k2 then NONE else sptree_lookup k1 t)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[delete_def; lookup_def;
                COND_ID];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[delete_def] THEN
    ASM_CASES_TAC `k2 = 0` THEN ASM_CASES_TAC `k1 = 0` THEN
    ASM_REWRITE_TAC[lookup_def; COND_ID] THEN
    ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC `k2 = 0` THEN ASM_CASES_TAC `k1 = 0` THEN
    ASM_CASES_TAC `EVEN k2` THEN ASM_CASES_TAC `EVEN k1` THEN
    ASM_REWRITE_TAC[delete_def; lookup_mk_BN] THEN
    ASM_REWRITE_TAC[lookup_def] THEN
    ASM_MESON_TAC[SPT_BIT_EQ_EQ];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC `k2 = 0` THEN ASM_CASES_TAC `k1 = 0` THEN
    ASM_CASES_TAC `EVEN k2` THEN ASM_CASES_TAC `EVEN k1` THEN
    ASM_REWRITE_TAC[delete_def; lookup_mk_BS;
                    lookup_mk_BN] THEN
    ASM_REWRITE_TAC[lookup_def] THEN
    ASM_MESON_TAC[SPT_BIT_EQ_EQ]]);;

(* and the lookup of a union, which takes the left value where there
   is one.  HOL4's optcase_lemma, and the same as a conditional,
   which is the form that a rewrite of the port can use: a match on
   a scrutinee that is a variable is not reduced by MATCH_REDUCE_TAC
   but mangled *)

let optcase_lemma = prove
 (`!opt:(A)option.
     (match opt with NONE -> NONE | SOME v -> SOME v) = opt`,
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `opt:(A)option` (cases_of `:(A)option`)) THEN
  MATCH_REDUCE_TAC THEN REWRITE_TAC[]);;

let OPT_MATCH_COND = prove
 (`!(opt:(A)option) y.
     (match opt with NONE -> y | SOME v -> SOME v) =
     (if opt = NONE then y else opt)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `opt:(A)option` (cases_of `:(A)option`)) THEN
  MATCH_REDUCE_TAC THEN
  REWRITE_TAC[distinctness "option"]);;

let optcase_cond = REWRITE_RULE[OPT_MATCH_COND] optcase_lemma;;

let lookup_union = prove
 (`!(m1:(A)spt) m2 k.
     sptree_lookup k (sptree_union m1 m2) =
     (match sptree_lookup k m1 with
        NONE -> sptree_lookup k m2
      | SOME v -> SOME v)`,
  REWRITE_TAC[OPT_MATCH_COND] THEN
  MATCH_MP_TAC spt_INDUCT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[union_def; lookup_def];
    REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(ISPEC `m2:(A)spt` (cases_of `:(A)spt`)) THEN
    REWRITE_TAC[union_def] THEN MATCH_REDUCE_TAC THEN
    ASM_CASES_TAC `k = 0` THEN
    ASM_REWRITE_TAC[lookup_def; optcase_cond;
                    distinctness "option"];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(ISPEC `m2:(A)spt` (cases_of `:(A)spt`)) THEN
    REWRITE_TAC[union_def] THEN MATCH_REDUCE_TAC THEN
    ASM_CASES_TAC `k = 0` THEN ASM_CASES_TAC `EVEN k` THEN
    ASM_REWRITE_TAC[lookup_def; optcase_cond;
                    distinctness "option"];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(ISPEC `m2:(A)spt` (cases_of `:(A)spt`)) THEN
    REWRITE_TAC[union_def] THEN MATCH_REDUCE_TAC THEN
    ASM_CASES_TAC `k = 0` THEN ASM_CASES_TAC `EVEN k` THEN
    ASM_REWRITE_TAC[lookup_def; optcase_cond;
                    distinctness "option"]]);;

(* LightCake's proofs of this theory split on the constructors of a
   term with a tactic of their own, which in HOL Light is the cases
   theorem of the term's type.  tools/lightcake.py takes a proof
   that uses a name of LightCake's only where this port has the
   name, so this is what lets those proofs in *)

let SPTAUX_CASES_TAC (t:term) : tactic =
  STRUCT_CASES_TAC (ISPEC t (cases_of (type_of t)));;

(* ================================================================ *)
(*  The theorems of sptreeTheory that LightCake proves and this   *)
(*  port needs, taken from its hol4/sptree.                       *)
(*                                                                *)
(*  LightCake is the other HOL Light port of CakeML               *)
(*  (hol-light-family/LightCake, BSD 3-Clause); its HOL4 library  *)
(*  layer is proved, and of these theories this port has only     *)
(*  the definitions that CakeML needs.  tools/lightcake.py        *)
(*  writes this file: the statements and the proofs are           *)
(*  LightCake's, with its constants under the names this port     *)
(*  gives them.  What it could not take, and why, is at the end.  *)
(* ================================================================ *)


let spt_distinct = distinctness "spt";;

let spt_inject = injectivity "spt";;

let SPTAUX_DIV2_LT = prove
 (`!k. ~(k = 0) ==> (k - 1) DIV 2 < k`,
  ARITH_TAC);;

let SPTAUX_bit_cases = prove
 (`!n. n = 0 \/ (?m. n = 2 * m + 1) \/ (?m. n = 2 * m + 2)`,
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THENL
   [DISJ1_TAC THEN EXISTS_TAC `0` THEN ARITH_TAC;
    DISJ2_TAC THEN EXISTS_TAC `m:num` THEN ARITH_TAC;
    DISJ1_TAC THEN EXISTS_TAC `m + 1` THEN ARITH_TAC]);;

let SPTAUX_bit_induction = prove
 (`!P. P 0 /\ (!n. P n ==> P (2 * n + 1)) /\ (!n. P n ==> P (2 * n + 2))
       ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num`
    THEN
  REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC `n:num` SPTAUX_bit_cases)
    THEN
  ASM_MESON_TAC[ARITH_RULE `m < 2 * m + 1 /\ m < 2 * m + 2`]);;

let SPTAUX_BIT_RW = prove
 (`(!m. ~(2 * m + 1 = 0)) /\ (!m. ~(2 * m + 2 = 0)) /\
   (!m. ~(0 = 2 * m + 1)) /\ (!m. ~(0 = 2 * m + 2)) /\
   (!m. EVEN (2 * m + 1) <=> F) /\ (!m. EVEN (2 * m + 2) <=> T) /\
   (!m. ODD (2 * m + 1) <=> T) /\ (!m. ODD (2 * m + 2) <=> F) /\
   (!m. ((2 * m + 1) - 1) DIV 2 = m) /\ (!m. ((2 * m + 2) - 1) DIV 2 =
     m) /\
   (!m n. 2 * m + 1 = 2 * n + 1 <=> m = n) /\
   (!m n. 2 * m + 2 = 2 * n + 2 <=> m = n) /\
   (!m n. ~(2 * m + 1 = 2 * n + 2)) /\ (!m n. ~(2 * m + 2 = 2 * n +
     1))`,
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ODD_ADD; ODD_MULT; ARITH] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY ARITH_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH]);;

let lookup_rwts = prove
 (`sptree_lookup k (LN:A spt) = NONE /\
   sptree_lookup 0 (LS (a:A)) = SOME a /\
   sptree_lookup 0 (BN t1 t2) = NONE:A option /\
   sptree_lookup 0 (BS t1 (a:A) t2) = SOME a`,
  REWRITE_TAC[lookup_def]);;

let SPTAUX_lookup_bits = prove
 (`(!m. sptree_lookup (2 * m + 1) (LN:A spt) = NONE) /\
   (!m (a:A). sptree_lookup (2 * m + 1) (LS a) = NONE) /\
   (!m t1 (t2:A spt). sptree_lookup (2 * m + 1) (BN t1 t2) =
     sptree_lookup m t2) /\
   (!m t1 (a:A) t2. sptree_lookup (2 * m + 1) (BS t1 a t2) =
     sptree_lookup m t2) /\
   (!m. sptree_lookup (2 * m + 2) (LN:A spt) = NONE) /\
   (!m (a:A). sptree_lookup (2 * m + 2) (LS a) = NONE) /\
   (!m t1 (t2:A spt). sptree_lookup (2 * m + 2) (BN t1 t2) =
     sptree_lookup m t1) /\
   (!m t1 (a:A) t2. sptree_lookup (2 * m + 2) (BS t1 a t2) =
     sptree_lookup m t1)`,
  REWRITE_TAC[lookup_def; SPTAUX_BIT_RW]);;

let SPTAUX_insert_bits = prove
 (`(!a:A. sptree_insert 0 a LN = LS a) /\
   (!a a':A. sptree_insert 0 a (LS a') = LS a) /\
   (!(a:A) t1 t2. sptree_insert 0 a (BN t1 t2) = BS t1 a t2) /\
   (!(a:A) a' t1 t2. sptree_insert 0 a (BS t1 a' t2) = BS t1 a t2) /\
   (!m (a:A). sptree_insert (2 * m + 1) a LN = BN LN (sptree_insert m a
     LN)) /\
   (!m (a:A) a'. sptree_insert (2 * m + 1) a (LS a') = BS LN a'
     (sptree_insert m a LN)) /\
   (!m (a:A) t1 t2. sptree_insert (2 * m + 1) a (BN t1 t2) = BN t1
     (sptree_insert m a t2)) /\
   (!m (a:A) a' t1 t2.
      sptree_insert (2 * m + 1) a (BS t1 a' t2) = BS t1 a'
        (sptree_insert m a t2)) /\
   (!m (a:A). sptree_insert (2 * m + 2) a LN = BN (sptree_insert m a LN)
     LN) /\
   (!m (a:A) a'. sptree_insert (2 * m + 2) a (LS a') = BS (sptree_insert
     m a LN) a' LN) /\
   (!m (a:A) t1 t2. sptree_insert (2 * m + 2) a (BN t1 t2) = BN
     (sptree_insert m a t1) t2) /\
   (!m (a:A) a' t1 t2.
      sptree_insert (2 * m + 2) a (BS t1 a' t2) = BS (sptree_insert m a
        t1) a' t2)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [insert_def] THEN
    REWRITE_TAC[SPTAUX_BIT_RW]);;

let insert_notEmpty = prove
 (`~(sptree_insert k (a:A) t = LN)`,
  SPTAUX_CASES_TAC `t:A spt` THEN ONCE_REWRITE_TAC[insert_def] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[spt_distinct]);;

let mk_BN_thm = prove
 (`!t1 t2:A spt. mk_BN t1 t2 = if t1 = LN /\ t2 = LN then LN else BN t1
   t2`,
  REPEAT GEN_TAC THEN SPTAUX_CASES_TAC `t1:A spt` THEN
  SPTAUX_CASES_TAC `t2:A spt` THEN REWRITE_TAC[mk_BN_def;
    spt_distinct]);;

let mk_BS_thm = prove
 (`!t1 t2:A spt. mk_BS t1 x t2 = if t1 = LN /\ t2 = LN then LS x else BS
   t1 x t2`,
  REPEAT GEN_TAC THEN SPTAUX_CASES_TAC `t1:A spt` THEN
  SPTAUX_CASES_TAC `t2:A spt` THEN REWRITE_TAC[mk_BS_def;
    spt_distinct]);;

let wf_delete = prove
 (`!t k. sptree_wf (t:A spt) ==> sptree_wf (sptree_delete k t)`,
  MATCH_MP_TAC spt_INDUCT THEN REWRITE_TAC[wf_def; delete_def] THEN
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[wf_def; mk_BN_thm; mk_BS_thm] THEN
  REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[wf_def]);;

let lookup_insert1 = prove
 (`!k (a:A) t. sptree_lookup k (sptree_insert k a t) = SOME a`,
  REWRITE_TAC[lookup_insert]);;

let SPTAUX_wf_mk_BN = prove
 (`!t1 t2:A spt. sptree_wf (mk_BN t1 t2) <=> sptree_wf t1 /\ sptree_wf
   t2`,
  REPEAT GEN_TAC THEN SPTAUX_CASES_TAC `t1:A spt` THEN
  SPTAUX_CASES_TAC `t2:A spt` THEN REWRITE_TAC[mk_BN_def; wf_def;
    spt_distinct]);;

let SPTAUX_wf_mk_BS = prove
 (`!t1 (x:A) t2. sptree_wf (mk_BS t1 x t2) <=> sptree_wf t1 /\ sptree_wf
   t2`,
  REPEAT GEN_TAC THEN SPTAUX_CASES_TAC `t1:A spt` THEN
  SPTAUX_CASES_TAC `t2:A spt` THEN REWRITE_TAC[mk_BS_def; wf_def;
    spt_distinct]);;

let SPTAUX_lookup_mk_BN = prove
 (`sptree_lookup k (mk_BN t1 t2) = sptree_lookup k (BN t1 t2:A spt)`,
  SPTAUX_CASES_TAC `t1:A spt` THEN SPTAUX_CASES_TAC `t2:A spt` THEN
  REWRITE_TAC[mk_BN_def; lookup_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[lookup_def]);;

let SPTAUX_lookup_mk_BS = prove
 (`sptree_lookup k (mk_BS t1 x t2) = sptree_lookup k (BS t1 (x:A) t2)`,
  SPTAUX_CASES_TAC `t1:A spt` THEN SPTAUX_CASES_TAC `t2:A spt` THEN
  REWRITE_TAC[mk_BS_def; lookup_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[lookup_def]);;

let SPTAUX_lookup_cond = prove
 (`!k c (t1:A spt) t2. sptree_lookup k (if c then t1 else t2) =
                       if c then sptree_lookup k t1 else sptree_lookup k
                         t2`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let SPTAUX_domain_bits = prove
 (`(0 IN domain (LN:A spt) <=> F) /\
   (!a:A. 0 IN domain (LS a) <=> T) /\
   (!t1 t2:A spt. 0 IN domain (BN t1 t2) <=> F) /\
   (!t1 (a:A) t2. 0 IN domain (BS t1 a t2) <=> T) /\
   (!m. (2 * m + 1) IN domain (LN:A spt) <=> F) /\
   (!m (a:A). (2 * m + 1) IN domain (LS a) <=> F) /\
   (!m t1 t2:A spt. (2 * m + 1) IN domain (BN t1 t2) <=> m IN domain t2)
     /\
   (!m t1 (a:A) t2. (2 * m + 1) IN domain (BS t1 a t2) <=> m IN domain
     t2) /\
   (!m. (2 * m + 2) IN domain (LN:A spt) <=> F) /\
   (!m (a:A). (2 * m + 2) IN domain (LS a) <=> F) /\
   (!m t1 t2:A spt. (2 * m + 2) IN domain (BN t1 t2) <=> m IN domain t1)
     /\
   (!m t1 (a:A) t2. (2 * m + 2) IN domain (BS t1 a t2) <=> m IN domain
     t1)`,
  REWRITE_TAC[domain_def; IN_UNION; IN_IMAGE; IN_INSERT; NOT_IN_EMPTY]
    THEN
  REWRITE_TAC[SPTAUX_BIT_RW; UNWIND_THM1; UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `2 * m + 1 = 2 * x + 1 <=> x = m`;
              ARITH_RULE `2 * m + 2 = 2 * x + 2 <=> x = m`;
              UNWIND_THM2]);;

let FINITE_domain = prove
 (`FINITE (domain (t:A spt))`,
  SPEC_TAC(`t:A spt`,`t:A spt`) THEN MATCH_MP_TAC spt_INDUCT THEN
  ASM_SIMP_TAC[domain_def; FINITE_UNION; FINITE_IMAGE; FINITE_INSERT;
               FINITE_EMPTY]);;

let size_insert = prove
 (`!k (v:A) m. sptree_size (sptree_insert k v m) =
               if k IN domain m then sptree_size m else sptree_size m +
                 1`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN REPEAT STRIP_TAC THEN
  SPTAUX_CASES_TAC `m:A spt` THEN
  ASM_REWRITE_TAC[SPTAUX_insert_bits; size_def; SPTAUX_domain_bits;
                  CONJUNCT1 domain_def; NOT_IN_EMPTY] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let SPTAUX_lookup_fromList_gen = prove
 (`!l:A list i n t.
     sptree_lookup n (SND (FOLDL (\(i,t) a. (i + 1,sptree_insert i a t))
       (i,t) l)) =
     if n < i then sptree_lookup n t
     else if n < LENGTH l + i then SOME (EL (n - i) l)
     else sptree_lookup n t`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL; LENGTH; ADD_CLAUSES] THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[lookup_insert] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `n:num < i` THENL
   [ASM_SIMP_TAC[ARITH_RULE `n < i ==> n < i + 1 /\ ~(n = i)`]; ALL_TAC]
     THEN
  ASM_CASES_TAC `n:num = i` THENL
   [ASM_REWRITE_TAC[ARITH_RULE `i < i + 1 /\ i < SUC (m + i) /\ i - i =
     0`;
                    EL; HD];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(n < i) /\ ~(n = i) ==> ~(n < i + 1)`;
               ARITH_RULE `n < SUC (m + i) <=> n < m + i + 1`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `n - i = SUC (n - (i + 1))` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[EL; TL]]);;

let lookup_fromList = prove
 (`sptree_lookup n (sptree_fromList l) =
   if n < LENGTH l then SOME (EL n (l:A list)) else NONE`,
  REWRITE_TAC[fromList_def; SPTAUX_lookup_fromList_gen; ADD_CLAUSES; LT;
              SUB_0; lookup_rwts]);;

let SPTAUX_card_images = prove
 (`!s t. FINITE s /\ FINITE t
         ==> CARD (IMAGE (\n. 2 * n + 2) s UNION IMAGE (\n. 2 * n + 1)
           t) =
             CARD s + CARD t /\
             CARD (({0} UNION IMAGE (\n. 2 * n + 2) s) UNION
                   IMAGE (\n. 2 * n + 1) t) =
             CARD s + CARD t + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `CARD (IMAGE (\n. 2 * n + 2) s) = CARD (s:num->bool) /\
                CARD (IMAGE (\n. 2 * n + 1) t) = CARD (t:num->bool)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[]
     THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\n. 2 * n + 2) s INTER IMAGE (\n. 2 * n + 1) t =
    {} /\
                ({0} UNION IMAGE (\n. 2 * n + 2) s) INTER
                IMAGE (\n. 2 * n + 1) t = {} /\
                {0} INTER IMAGE (\n. 2 * n + 2) s = {}`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_IMAGE; IN_INSERT;
                NOT_IN_EMPTY] THEN
    MESON_TAC[SPTAUX_BIT_RW]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_UNION; FINITE_UNION; FINITE_IMAGE; FINITE_INSERT;
               FINITE_EMPTY; CARD_SING] THEN
  ARITH_TAC);;

let domain_delete = prove
 (`domain (sptree_delete k (t:A spt)) = domain t DELETE k`,
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_delete; IN_DELETE] THEN
  MESON_TAC[option_DISTINCT]);;

let SPTAUX_lrnext_bits = prove
 (`lrnext 0 = 1 /\ lrnext 1 = 2 /\ lrnext 2 = 2 /\
   (!m. lrnext (2 * m + 1) = 2 * lrnext m) /\
   (!m. lrnext (2 * m + 2) = 2 * lrnext m)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [lrnext_def] THEN
  REWRITE_TAC[SPTAUX_BIT_RW] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ONCE_REWRITE_TAC[lrnext_def] THEN CONV_TAC NUM_REDUCE_CONV);;

let SPTAUX_lrlemma1 = prove
 (`!i. lrnext (i + lrnext i) = 2 * lrnext i`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN
  REWRITE_TAC[SPTAUX_lrnext_bits; ADD_CLAUSES; ARITH] THEN
  REWRITE_TAC[ARITH_RULE `(2 * m + 1) + 2 * x = 2 * (m + x) + 1 /\
                          (2 * m + 2) + 2 * x = 2 * (m + x) + 2`] THEN
  SIMP_TAC[SPTAUX_lrnext_bits]);;

let SPTAUX_lrlemma2 = prove
 (`!i. lrnext (i + 2 * lrnext i) = 2 * lrnext i`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN
  REWRITE_TAC[SPTAUX_lrnext_bits; ADD_CLAUSES; ARITH] THEN
  REWRITE_TAC[ARITH_RULE `(2 * m + 1) + 2 * 2 * x = 2 * (m + 2 * x) + 1
    /\
                          (2 * m + 2) + 2 * 2 * x = 2 * (m + 2 * x) +
                            2`] THEN
  SIMP_TAC[SPTAUX_lrnext_bits]);;

let SPTAUX_lrnext_pos = prove
 (`!i. ~(lrnext i = 0)`,
  MATCH_MP_TAC SPTAUX_bit_induction THEN
  ASM_REWRITE_TAC[SPTAUX_lrnext_bits; MULT_EQ_0; ARITH]);;

let SPTAUX_foldi_thm = REWRITE_RULE[LET_DEF; LET_END_DEF] foldi_def;;

let SPTAUX_EXISTS_BITS = prove
 (`!P. (?n. P n) <=> P 0 \/ (?m. P (2 * m + 1)) \/ (?m. P (2 * m + 2))`,
  GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
  REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC `n:num` SPTAUX_bit_cases)
    THEN
  MESON_TAC[]);;

let SPTAUX_OFFSET_RW = prove
 (`(!i c. i + c * 0 = i) /\
   (!i c m. i + c * (2 * m + 1) = (i + c) + (2 * c) * m) /\
   (!i c m. i + c * (2 * m + 2) = (i + 2 * c) + (2 * c) * m)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN CONV_TAC NUM_RING);;

let SPTAUX_offset_lookup = prove
 (`(!i c k (v:A). (?n. k = i + c * n /\ sptree_lookup n (LN:A spt) =
   SOME v) <=> F) /\
   (!i c k (v:A) a.
      (?n. k = i + c * n /\ sptree_lookup n (LS a) = SOME v) <=> k = i
        /\ a = v) /\
   (!i c k (v:A) t1 t2.
      (?n. k = i + c * n /\ sptree_lookup n (BN t1 t2) = SOME v) <=>
      (?n. k = (i + 2 * c) + (2 * c) * n /\ sptree_lookup n t1 = SOME v)
        \/
      (?n. k = (i + c) + (2 * c) * n /\ sptree_lookup n t2 = SOME v)) /\
   (!i c k (v:A) a t1 t2.
      (?n. k = i + c * n /\ sptree_lookup n (BS t1 a t2) = SOME v) <=>
      (k = i /\ a = v) \/
      (?n. k = (i + 2 * c) + (2 * c) * n /\ sptree_lookup n t1 = SOME v)
        \/
      (?n. k = (i + c) + (2 * c) * n /\ sptree_lookup n t2 = SOME v))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SPTAUX_EXISTS_BITS] THEN
  REWRITE_TAC[lookup_rwts; SPTAUX_lookup_bits; SPTAUX_OFFSET_RW;
              option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;

let SPTAUX_offset_domain = prove
 (`(!i c. IMAGE (\n. i + c * n) (domain (LN:A spt)) = {}) /\
   (!i c a:A. IMAGE (\n. i + c * n) (domain (LS a)) = {i}) /\
   (!i c t1 t2:A spt.
      IMAGE (\n. i + c * n) (domain (BN t1 t2)) =
      IMAGE (\n. (i + 2 * c) + (2 * c) * n) (domain t1) UNION
      IMAGE (\n. (i + c) + (2 * c) * n) (domain t2)) /\
   (!i c (a:A) t1 t2.
      IMAGE (\n. i + c * n) (domain (BS t1 a t2)) =
      (i INSERT IMAGE (\n. (i + 2 * c) + (2 * c) * n) (domain t1)) UNION
      IMAGE (\n. (i + c) + (2 * c) * n) (domain t2))`,
  REWRITE_TAC[CONJUNCT1 domain_def; IMAGE_CLAUSES] THEN CONJ_TAC THENL
   [REWRITE_TAC[domain_def; IMAGE_CLAUSES; SPTAUX_OFFSET_RW]; ALL_TAC]
     THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNION; IN_INSERT] THEN
  X_GEN_TAC `k:num` THEN
  GEN_REWRITE_TAC LAND_CONV [SPTAUX_EXISTS_BITS] THEN
  REWRITE_TAC[SPTAUX_domain_bits; SPTAUX_OFFSET_RW] THEN
  MESON_TAC[]);;

let SPTAUX_UNION_RW = prove
 (`(!a s1 s2:num->bool. (a UNION s1) UNION s2 = a UNION (s1 UNION s2))
   /\
   (!i a s1 s2:num->bool.
      (i INSERT (a UNION s1)) UNION s2 = a UNION ((i INSERT s1) UNION
        s2)) /\
   (!i a:num->bool. a UNION {i} = i INSERT a)`,
  SET_TAC[]);;

let set_foldi_keys = prove
 (`!t:A spt a i. foldi (\k v a. k INSERT a) i a t =
                 a UNION IMAGE (\n. i + lrnext i * n) (domain t)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[SPTAUX_foldi_thm; SPTAUX_offset_domain;
    SPTAUX_lrlemma1;
                  SPTAUX_lrlemma2; UNION_EMPTY; SPTAUX_UNION_RW]);;

let domain_foldi = prove
 (`domain t = foldi (\k (v:A) a. k INSERT a) 0 {} t`,
  REWRITE_TAC[set_foldi_keys; UNION_EMPTY; SPTAUX_lrnext_bits;
    ADD_CLAUSES;
              MULT_CLAUSES; IMAGE_ID]);;

let SPTAUX_ACC_RW = prove
 (`(!c i. c * 0 + i = i) /\
   (!c i m. c * (2 * m + 1) + i = (2 * c) * m + (i + c)) /\
   (!c i m. c * (2 * m + 2) + i = (2 * c) * m + (i + 2 * c))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN CONV_TAC NUM_RING);;

let domain_empty = prove
 (`!t:A spt. sptree_wf t ==> ((t = LN) <=> (domain t = EMPTY))`,
  MATCH_MP_TAC spt_INDUCT THEN
  REWRITE_TAC[wf_def; domain_def; spt_distinct; NOT_INSERT_EMPTY;
              EMPTY_UNION; IMAGE_EQ_EMPTY] THEN
  MESON_TAC[]);;

let SPTAUX_toListA_APPEND = prove
 (`!t:A spt acc acc'.
     toListA (APPEND acc acc') t = APPEND (toListA acc t) acc'`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[toListA_def; APPEND] THEN
  ASM_REWRITE_TAC[GSYM(CONJUNCT2 APPEND)]);;

let toListA_append = prove
 (`!t:A spt acc. toListA acc t = APPEND (toListA [] t) acc`,
  REWRITE_TAC[GSYM SPTAUX_toListA_APPEND; APPEND]);;

let SPTAUX_LENGTH_toListA = prove
 (`!t:A spt acc. LENGTH (toListA acc t) = sptree_size t + LENGTH acc`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[toListA_def; size_def; LENGTH] THEN ARITH_TAC);;

let size_zero_empty = prove
 (`!x:A spt. sptree_size x = 0 <=> domain x = EMPTY`,
  MATCH_MP_TAC spt_INDUCT THEN
  ASM_REWRITE_TAC[size_def; domain_def; ADD_EQ_0; ARITH;
                  NOT_INSERT_EMPTY; EMPTY_UNION; IMAGE_EQ_EMPTY] THEN
  MESON_TAC[]);;

let isEmpty_toListA = prove
 (`!t:A spt acc. sptree_wf t ==> ((t = LN) <=> (toListA acc t = acc))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[toListA_def]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `LENGTH:A list->num`) THEN
  REWRITE_TAC[SPTAUX_LENGTH_toListA; ARITH_RULE `a + b = b <=> a = 0`]
    THEN
  ASM_SIMP_TAC[size_zero_empty; domain_empty]);;

let isEmpty_toList = prove
 (`!t:A spt. sptree_wf t ==> ((t = LN) <=> (sptree_toList t = []))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[toList_def] THEN
  MATCH_MP_TAC isEmpty_toListA THEN ASM_REWRITE_TAC[]);;

let SPTAUX_EXISTS_lookup = prove
 (`(!x:A. (?k. sptree_lookup k (LN:A spt) = SOME x) <=> F) /\
   (!(x:A) a. (?k. sptree_lookup k (LS a) = SOME x) <=> a = x) /\
   (!(x:A) t1 t2. (?k. sptree_lookup k (BN t1 t2) = SOME x) <=>
                  (?k. sptree_lookup k t1 = SOME x) \/ (?k.
                    sptree_lookup k t2 = SOME x)) /\
   (!(x:A) a t1 t2. (?k. sptree_lookup k (BS t1 a t2) = SOME x) <=>
                  a = x \/ (?k. sptree_lookup k t1 = SOME x) \/
                  (?k. sptree_lookup k t2 = SOME x))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SPTAUX_EXISTS_BITS] THEN
  REWRITE_TAC[lookup_rwts; SPTAUX_lookup_bits; option_DISTINCT;
    option_INJ] THEN
  MESON_TAC[]);;

let SPTAUX_MEM_toListA = prove
 (`!t:A spt acc x. MEM x (toListA acc t) <=>
                   (MEM x acc \/ ?k. sptree_lookup k t = SOME x)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[toListA_def; MEM; SPTAUX_EXISTS_lookup] THEN
  MESON_TAC[]);;

let MEM_toList = prove
 (`!x (t:A spt). MEM x (sptree_toList t) <=> ?k. sptree_lookup k t =
   SOME x`,
  REWRITE_TAC[toList_def; SPTAUX_MEM_toListA; MEM]);;

let SPTAUX_FORALL_BITS = prove
 (`!P. (!n. P n) <=> P 0 /\ (!m. P (2 * m + 1)) /\ (!m. P (2 * m + 2))`,
  GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN X_GEN_TAC `n:num` THEN
  REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC `n:num` SPTAUX_bit_cases)
    THEN
  ASM_REWRITE_TAC[]);;

let SPTAUX_lookup_NONE_LN = prove
 (`!t:A spt. sptree_wf t ==> (((!n. sptree_lookup n t = NONE) <=> t =
   LN) /\
                      ((!n. NONE = sptree_lookup n t) <=> t = LN))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[domain_empty] THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; GSYM lookup_NONE_domain] THEN
  MESON_TAC[]);;

let wf_mk_wf = prove
 (`!t:A spt. sptree_wf (mk_wf t)`,
  MATCH_MP_TAC spt_INDUCT THEN
  ASM_SIMP_TAC[wf_def; mk_wf_def; SPTAUX_wf_mk_BS; SPTAUX_wf_mk_BN]);;

let wf_mk_id = prove
 (`!t:A spt. sptree_wf t ==> (mk_wf t = t)`,
  MATCH_MP_TAC spt_INDUCT THEN REWRITE_TAC[wf_def; mk_wf_def] THEN
  SIMP_TAC[mk_BS_thm; mk_BN_thm]);;

let SPTAUX_toListA_map = prove
 (`!s:A spt acc. toListA (MAP (f:A->B) acc) (sptree_map f s) = MAP f
   (toListA acc s)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[map_def; toListA_def; MAP] THEN
  ASM_REWRITE_TAC[GSYM(CONJUNCT2 MAP)]);;

let toList_map = prove
 (`!s:A spt. sptree_toList (sptree_map (f:A->B) s) = MAP f
   (sptree_toList s)`,
  REWRITE_TAC[toList_def; GSYM SPTAUX_toListA_map; MAP]);;

let domain_map = prove
 (`!s:A spt. domain (sptree_map (f:A->B) s) = domain s`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[map_def; domain_def]);;

let map_LN = prove
 (`!t:A spt. (sptree_map (f:A->B) t = LN) <=> (t = LN)`,
  GEN_TAC THEN SPTAUX_CASES_TAC `t:A spt` THEN
  REWRITE_TAC[map_def; spt_distinct]);;

let wf_map = prove
 (`!t:A spt (f:A->B). sptree_wf (sptree_map f t) = sptree_wf t`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[map_def; wf_def; map_LN]);;

let map_map_o = prove
 (`!t:A spt (f:B->C) (g:A->B). sptree_map f (sptree_map g t) =
   sptree_map (f o g) t`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[map_def; o_THM]);;

let map_insert = prove
 (`!(f:A->B) x y z. sptree_map f (sptree_insert x y z) = sptree_insert x
   (f y) (sptree_map f z)`,
  GEN_TAC THEN MATCH_MP_TAC SPTAUX_bit_induction THEN REPEAT STRIP_TAC
    THEN
  SPTAUX_CASES_TAC `z:A spt` THEN
  ASM_REWRITE_TAC[SPTAUX_insert_bits; map_def]);;

let lookup_0_spt_center = prove
 (`!spt:A spt. sptree_lookup 0 spt = spt_center spt`,
  GEN_TAC THEN SPTAUX_CASES_TAC `spt:A spt` THEN
  REWRITE_TAC[lookup_rwts; spt_center_def]);;

let SPTAUX_lookup_gen_bits = prove
 (`(!t:A spt. sptree_lookup 0 t = spt_center t) /\
   (!m t:A spt. sptree_lookup (2 * m + 1) t = sptree_lookup m (spt_right
     t)) /\
   (!m t:A spt. sptree_lookup (2 * m + 2) t = sptree_lookup m (spt_left
     t))`,
  REWRITE_TAC[lookup_0_spt_center] THEN CONJ_TAC THEN REPEAT GEN_TAC
    THEN
  SPTAUX_CASES_TAC `t:A spt` THEN
  REWRITE_TAC[SPTAUX_lookup_bits; spt_right_def; spt_left_def;
    lookup_rwts]);;

let lookup_spt_right = prove
 (`sptree_lookup i (spt_right spt) = sptree_lookup ((i * 2) + 1) (spt:A
   spt)`,
  REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] SPTAUX_lookup_gen_bits]);;

let lookup_spt_left = prove
 (`sptree_lookup i (spt_left spt) = sptree_lookup ((i * 2) + 2) (spt:A
   spt)`,
  REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] SPTAUX_lookup_gen_bits]);;

let subspt_lookup = prove
 (`!t1 t2:A spt.
     subspt t1 t2 <=>
     !x y. (sptree_lookup x t1 = SOME y) ==> (sptree_lookup x t2 = SOME
       y)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[subspt_eq] THEN ONCE_REWRITE_TAC[SPTAUX_FORALL_BITS] THEN
  ASM_REWRITE_TAC[lookup_rwts; SPTAUX_lookup_bits;
    SPTAUX_lookup_gen_bits;
                  option_DISTINCT; option_INJ; spt_center_def;
                  FORALL_UNWIND_THM1; FORALL_UNWIND_THM2] THEN
  MESON_TAC[]);;

let subspt_domain = prove
 (`!t1 (t2:1 spt). subspt t1 t2 <=> domain t1 SUBSET domain t2`,
  REWRITE_TAC[subspt_lookup; domain_lookup; SUBSET; FORALL_ONE_THM;
              EXISTS_ONE_THM] THEN
  MESON_TAC[]);;

let subspt_def = prove
 (`!sp1 sp2:A spt.
     subspt sp1 sp2 <=>
     !k. k IN domain sp1 ==> k IN domain sp2 /\
         (sptree_lookup k sp2 = sptree_lookup k sp1)`,
  REWRITE_TAC[subspt_lookup; domain_lookup] THEN
  MESON_TAC[option_INJ]);;

let subspt_refl = prove
 (`subspt sp (sp:A spt)`,
  REWRITE_TAC[subspt_lookup]);;

let subspt_trans = prove
 (`subspt sp1 sp2 /\ subspt sp2 sp3 ==> subspt sp1 (sp3:A spt)`,
  REWRITE_TAC[subspt_lookup] THEN MESON_TAC[]);;

let subspt_LN = prove
 (`(subspt LN (sp:A spt) <=> T) /\ (subspt sp (LN:A spt) <=> (domain sp
   = {}))`,
  REWRITE_TAC[subspt_def; EXTENSION; domain_def; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let domain_eq = prove
 (`!t1:A spt t2:B spt.
     (domain t1 = domain t2) <=>
     !k. (sptree_lookup k t1 = NONE) <=> (sptree_lookup k t2 = NONE)`,
  REWRITE_TAC[EXTENSION; lookup_NONE_domain] THEN MESON_TAC[]);;

let wf_filter_v = prove
 (`!t:A spt f. sptree_wf t ==> sptree_wf (filter_v f t)`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wf_def]) THEN
  REWRITE_TAC[filter_v_def] THEN REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[wf_def; SPTAUX_wf_mk_BN; SPTAUX_wf_mk_BS]);;

let wf_mk_BN = prove
 (`sptree_wf t1 /\ sptree_wf t2 ==> sptree_wf (mk_BN t1 (t2:A spt))`,
  REWRITE_TAC[SPTAUX_wf_mk_BN]);;

let wf_mk_BS = prove
 (`sptree_wf t1 /\ sptree_wf t2 ==> sptree_wf (mk_BS t1 (a:A) t2)`,
  REWRITE_TAC[SPTAUX_wf_mk_BS]);;

let wf_mapi = prove
 (`sptree_wf (sptree_mapi (f:num->A->B) pt)`,
  REWRITE_TAC[mapi_def] THEN
  SUBGOAL_THEN `!pt:A spt n. sptree_wf (mapi0 (f:num->A->B) n pt)`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC spt_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[mapi0_def; LET_DEF; LET_END_DEF; wf_def;
    SPTAUX_wf_mk_BN;
                  SPTAUX_wf_mk_BS]);;

let lookup_fromList_outside = prove
 (`!k. LENGTH args <= k ==> (sptree_lookup k (sptree_fromList (args:A
   list)) = NONE)`,
  SIMP_TAC[lookup_fromList; GSYM NOT_LT]);;

let domain_FOLDR_delete = prove
 (`!ls live:A spt.
     domain (ITLIST sptree_delete ls live) = (domain live) DIFF
       (set_of_list ls)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITLIST; set_of_list; DIFF_EMPTY; domain_delete] THEN
  SET_TAC[]);;

let lookup_list_to_num_set = prove
 (`!xs. sptree_lookup x (list_to_num_set xs) = if MEM x xs then SOME one
   else NONE`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_to_num_set_def; lookup_rwts; MEM; lookup_insert]
    THEN
  MESON_TAC[]);;

let wf_LN = prove
 (`sptree_wf (LN:A spt)`,
  REWRITE_TAC[wf_def]);;

let SPTAUX_LENGTH_MAPi = prove
 (`!(f:num->A->B) l. LENGTH (MAPi f l) = LENGTH l`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAPi_DEF; LENGTH]);;

let SPTAUX_EL_MAPi = prove
 (`!l (f:num->A->B) n. n < LENGTH l ==> EL n (MAPi f l) = f n (EL n l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[MAPi_DEF; EL; HD; TL; LT_SUC] THEN
  ASM_SIMP_TAC[o_THM]);;

let SPTAUX_delete_mk_BN = prove
 (`(!t1 t2:A spt. sptree_delete 0 (mk_BN t1 t2) = mk_BN t1 t2) /\
   (!m t1 t2:A spt. sptree_delete (2 * m + 1) (mk_BN t1 t2) = mk_BN t1
     (sptree_delete m t2)) /\
   (!m t1 t2:A spt. sptree_delete (2 * m + 2) (mk_BN t1 t2) = mk_BN
     (sptree_delete m t1) t2)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  SPTAUX_CASES_TAC `t1:A spt` THEN SPTAUX_CASES_TAC `t2:A spt` THEN
  REWRITE_TAC[mk_BN_def; delete_def; SPTAUX_BIT_RW]);;

let SPTAUX_delete_mk_BS = prove
 (`(!t1 (s:A) t2. sptree_delete 0 (mk_BS t1 s t2) = mk_BN t1 t2) /\
   (!m t1 (s:A) t2.
      sptree_delete (2 * m + 1) (mk_BS t1 s t2) = mk_BS t1 s
        (sptree_delete m t2)) /\
   (!m t1 (s:A) t2.
      sptree_delete (2 * m + 2) (mk_BS t1 s t2) = mk_BS (sptree_delete m
        t1) s t2)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  SPTAUX_CASES_TAC `t1:A spt` THEN SPTAUX_CASES_TAC `t2:A spt` THEN
  REWRITE_TAC[mk_BS_def; mk_BN_def; delete_def; SPTAUX_BIT_RW]);;

let SPTAUX_BIT_LT = prove
 (`(!p q. 2 * p + 1 < 2 * q + 1 <=> p < q) /\
   (!p q. 2 * p + 2 < 2 * q + 2 <=> p < q)`,
  ARITH_TAC);;

let SPTAUX_EXISTS_lookup_P = prove
 (`(!P. (?k v. sptree_lookup k (LN:A spt) = SOME v /\ P v) <=> F) /\
   (!P (a:A). (?k v. sptree_lookup k (LS a) = SOME v /\ P v) <=> P a) /\
   (!P t1 t2:A spt. (?k v. sptree_lookup k (BN t1 t2) = SOME v /\ P v)
     <=>
                    (?k v. sptree_lookup k t1 = SOME v /\ P v) \/
                    (?k v. sptree_lookup k t2 = SOME v /\ P v)) /\
   (!P (a:A) t1 t2. (?k v. sptree_lookup k (BS t1 a t2) = SOME v /\ P v)
     <=>
                    P a \/ (?k v. sptree_lookup k t1 = SOME v /\ P v) \/
                    (?k v. sptree_lookup k t2 = SOME v /\ P v))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SPTAUX_EXISTS_BITS] THEN
  REWRITE_TAC[lookup_rwts; SPTAUX_lookup_bits; option_DISTINCT;
    option_INJ;
              UNWIND_THM1; UNWIND_THM2] THEN
  MESON_TAC[]);;

let SPTAUX_FORALL_lookup_P = prove
 (`(!P. (!k v. sptree_lookup k (LN:A spt) = SOME v ==> P v) <=> T) /\
   (!P (a:A). (!k v. sptree_lookup k (LS a) = SOME v ==> P v) <=> P a)
     /\
   (!P t1 t2:A spt. (!k v. sptree_lookup k (BN t1 t2) = SOME v ==> P v)
     <=>
                    (!k v. sptree_lookup k t1 = SOME v ==> P v) /\
                    (!k v. sptree_lookup k t2 = SOME v ==> P v)) /\
   (!P (a:A) t1 t2. (!k v. sptree_lookup k (BS t1 a t2) = SOME v ==> P
     v) <=>
                    P a /\ (!k v. sptree_lookup k t1 = SOME v ==> P v)
                      /\
                    (!k v. sptree_lookup k t2 = SOME v ==> P v))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SPTAUX_FORALL_BITS] THEN
  REWRITE_TAC[lookup_rwts; SPTAUX_lookup_bits; option_DISTINCT;
    option_INJ;
              FORALL_UNWIND_THM1; FORALL_UNWIND_THM2] THEN
  MESON_TAC[]);;

(* What this port cannot take from LightCake's sptree
   yet, with the names of its own that each proof
   uses:

     spt_CASE                         case_def
     spt_case_eq                      case_eq
     spt_size_def                     size_def
     SPTAUX_TC_TAC                    WF_REL_THMS
     SPTAUX_BITS_TAC                  term
     SPTAUX_CASES_TAC                 CASES_ON term
     wf_insert                        -- Exception: Failure "TAC_PROOF:
                                      Unsolved goals".
     isEmpty_union                    spt_CASE
     wf_union                         isEmpty_union spt_CASE
     SPTAUX_optcase_lemma             option_CASE
     wf_inter                         spt_CASE
     SPTAUX_optcase_NONE              option_CASE
     lookup_inter                     SPTAUX_BITS_TAC
                                      SPTAUX_optcase_NONE option_CASE
                                      spt_CASE
     lookup_inter_eq                  SPTAUX_BITS_TAC
                                      SPTAUX_optcase_NONE inter_eq
                                      option_CASE spt_CASE
     lookup_inter_EQ                  lookup_inter option_CASE
     lookup_inter_assoc               lookup_inter option_CASE
     lookup_difference                SPTAUX_BITS_TAC spt_CASE
     set_domain_list                  domain_list_def
     IN_domain                        SPTAUX_BITS_TAC
     lookup_inter_alt                 lookup_inter option_CASE
     domain_union                     option_CASE
     domain_inter                     lookup_inter option_CASE
     domain_insert                    v
     domain_difference                lookup_difference
     domain_sing                      domain_insert v
     domain_fromList                  count_DEF
     size_domain                      -- Exception:
     spt_acc_thm                      spt_acc_def
     spt_acc_eqn                      spt_acc_def spt_acc_thm
     spt_acc_0                        spt_acc_eqn
     lookup_mapi0                     SPTAUX_BITS_TAC option_CASE
                                      spt_acc_eqn
     lookup_mapi                      OPTION_MAP_DEF lookup_mapi0
                                      option_CASE spt_acc_0
     SPTAUX_MEM_foldi                 CONS
     MEM_toAList                      SPTAUX_MEM_foldi v
     SPTAUX_ALOOKUP_MEM               ALOOKUP_DEF v
     SPTAUX_ALOOKUP_FAILS             ALOOKUP_DEF
     ALOOKUP_toAList                  MEM_toAList SPTAUX_ALOOKUP_FAILS
                                      SPTAUX_ALOOKUP_MEM
     insert_union                     spt_CASE
     SPTAUX_LENGTH_foldi              CONS
     LENGTH_toAList                   SPTAUX_LENGTH_foldi
     SPTAUX_ALL_DISTINCT_CARD         -- Exception: Failure "find_term".
     set_MAP_FST_toAList_domain       MEM_toAList
     ALL_DISTINCT_MAP_FST_toAList     LENGTH_toAList
                                      SPTAUX_ALL_DISTINCT_CARD
                                      set_MAP_FST_toAList_domain
                                      size_domain
     SPTAUX_ITLIST_UNCURRY            CONS UNCURRY
     SPTAUX_foldi_FOLDR_toAList_lemma CONS SPTAUX_ITLIST_UNCURRY UNCURRY
     foldi_FOLDR_toAList              SPTAUX_foldi_FOLDR_toAList_lemma
                                      UNCURRY
     spt_eq_thm                       -- Error in included file the
                                      block
     lookup_mk_wf                     SPTAUX_BITS_TAC
     domain_mk_wf                     lookup_mk_wf
     mk_wf_eq                         lookup_mk_wf spt_eq_thm
     inter_eq                         spt_eq_thm wf_inter
     union_mk_wf                      lookup_mk_wf mk_wf_eq wf_union
     inter_mk_wf                      lookup_inter lookup_mk_wf mk_wf_eq
                                      wf_inter
     insert_mk_wf                     lookup_mk_wf mk_wf_eq wf_insert
     delete_mk_wf                     lookup_mk_wf mk_wf_eq
     union_LN                         spt_CASE
     inter_LN                         spt_CASE
     union_assoc                      spt_CASE
     inter_assoc                      inter_eq lookup_inter option_CASE
     lookup_fromAList                 ALOOKUP_DEF ALOOKUP_THM
     domain_fromAList                 domain_insert
     lookup_fromAList_toAList         ALOOKUP_toAList lookup_fromAList
     wf_fromAList                     -- Error: Unbound value wf_insert
     fromAList_toAList                lookup_fromAList_toAList
                                      spt_eq_thm wf_fromAList
     union_insert_LN                  insert_union
     fromAList_append                 insert_union union_LN union_assoc
                                      union_insert_LN
     lookup_map                       OPTION_MAP_DEF SPTAUX_BITS_TAC
     map_fromAList                    map_insert
     insert_insert                    SPTAUX_BITS_TAC
     insert_shadow                    insert_insert
     subspt_union                     option_CASE
     subspt_FOLDL_union               subspt_union
     domain_mapi                      OPTION_MAP_DEF lookup_mapi
     lookup_FOLDL_union               OPTION_CHOICE_DEF option_CASE
     map_union                        spt_CASE
     lookup_filter_v                  SPTAUX_BITS_TAC option_CASE
     SPTAUX_ALOOKUP_MAP_lemma         ALOOKUP_DEF OPTION_MAP_DEF
     MAP_foldi                        CONS
     mapi_Alist                       ALOOKUP_toAList
                                      SPTAUX_ALOOKUP_MAP_lemma
                                      lookup_fromAList lookup_mapi
                                      spt_eq_thm wf_fromAList
     num_set_domain_eq                -- Error: Unbound value spt_eq_thm
     union_num_set_sym                spt_CASE
     union_disjoint_sym               option_CASE spt_eq_thm wf_union
     difference_sub                   domain_difference
     wf_difference                    spt_CASE
     delete_fail                      -- Error: Unbound value spt_eq_thm
     size_delete                      -- Error: Unbound value
                                      size_domain
     IMP_size_LESS_size               -- Error: Unbound value
                                      size_domain
     size_diff_less                   IMP_size_LESS_size
                                      domain_difference
                                      lookup_difference
     inter_eq_LN                      domain_inter wf_inter
     domain_list_to_num_set           domain_insert
     domain_list_insert               domain_insert
     list_to_num_set_append           insert_union union_LN union_assoc
                                      union_insert_LN
     map_map_K                        K_THM
     lookup_map_K                     K_THM OPTION_MAP_DEF lookup_map
     lookup_alist_insert              ALOOKUP_DEF option_CASE
     domain_alist_insert              domain_insert
     alist_insert_append              -- no answer
     wf_fromList                      -- Error: Unbound value wf_insert
     wf_list_to_num_set               -- Error: Unbound value wf_insert
     size_list_to_num_set             domain_list_to_num_set nub_DEF
     mapi_fromList                    OPTION_MAP_DEF lookup_mapi
                                      spt_eq_thm wf_fromList
     SPTAUX_DROP_0                    DROP_DEF
     SPTAUX_TAKE_DROP_UPDATE          DROP_DEF SPTAUX_DROP_0 TAKE_DEF v
     insert_fromList_IN_domain        SPTAUX_TAKE_DROP_UPDATE spt_eq_thm
                                      wf_fromList wf_insert
     insert_swap                      insert_insert
     alist_insert_pull_insert         insert_swap
     alist_insert_REVERSE             alist_insert_append
                                      alist_insert_pull_insert
     insert_unchanged                 -- Exception: Failure "TAC_PROOF:
                                      Unsolved goals".
     SPTAUX_delete_delete_same        SPTAUX_BITS_TAC
     SPTAUX_delete_delete_lt          SPTAUX_BITS_TAC
     delete_delete                    SPTAUX_delete_delete_lt
                                      SPTAUX_delete_delete_same
     size_map                         -- Error: Unbound value
                                      size_domain
     size_mapi                        domain_mapi size_domain
     SUM_MAP_same_LE                  SUM
     SUM_MAP_same_LESS                SUM SUM_MAP_same_LE
     size_fromList                    count_DEF domain_fromList
                                      size_domain
     SPTAUX_spts_to_alist_aux_thm     CONS list_CASE option_CASE
                                      pair_CASE
     SPTAUX_SUM_add_pause             SUM list_CASE pair_CASE
                                      spt_size_def
     SPTAUX_SUM_MAP_APPEND            SUM
     SPTAUX_SUM_MAP_REVERSE           SPTAUX_SUM_MAP_APPEND SUM
     SPTAUX_spt_size_left_right       K_THM spt_size_def
     spts_to_alist_aux_size           RVEQ_TAC SPTAUX_SUM_MAP_APPEND
                                      SPTAUX_SUM_MAP_REVERSE
                                      SPTAUX_SUM_add_pause
                                      SPTAUX_spt_size_left_right
                                      SPTAUX_spts_to_alist_aux_thm SUM
                                      spt_size_def
     SPTAUX_LENGTH_COUNT_LIST         COUNT_LIST_DEF
     SPTAUX_ALOOKUP_ZIP_MAP_SUC       ALOOKUP_DEF
     SPTAUX_ALOOKUP_ZIP_COUNT_LIST    ALOOKUP_DEF COUNT_LIST_DEF
                                      SPTAUX_ALOOKUP_ZIP_MAP_SUC
                                      SPTAUX_LENGTH_COUNT_LIST
     fromList_fromAList               SPTAUX_ALOOKUP_ZIP_COUNT_LIST
                                      lookup_fromAList spt_eq_thm
                                      wf_fromAList wf_fromList
     domain_spt_fold_union            domain_union
     SPTAUX_closure_spt_size          domain_spt_fold_union domain_union
                                      lookup_inter_EQ size_diff_less
     closure_spt_ind                  RVEQ_TAC SPTAUX_closure_spt_size
     num_set_tree_union_empty         num_set_tree_union_def spt_CASE
     wf_num_set_tree_union            num_set_tree_union_def
                                      num_set_tree_union_empty spt_CASE
     domain_num_set_tree_union        num_set_tree_union_def spt_CASE
     num_set_tree_union_sym           num_set_tree_union_def spt_CASE
                                      union_num_set_sym
     lookup_num_set_tree_union        SPTAUX_BITS_TAC
                                      SPTAUX_optcase_lemma
                                      num_set_tree_union_def option_CASE
                                      spt_CASE
     wf_spt_fold_union                wf_union
     wf_closure_spt                   closure_spt_def closure_spt_ind
                                      lookup_inter_EQ wf_spt_fold_union
                                      wf_union
     adjacent_domain                  is_adjacent_def
     reachable_domain                 RTC_INDUCT_L adjacent_domain
                                      is_reachable_def
     reachable_LHS_NOTIN              RTC_CASES_R adjacent_domain
                                      is_reachable_def
     rtc_is_adjacent                  -- Error: Unbound value
                                      RTC_INDUCT_L
     is_adjacent_num_set_tree_union   is_adjacent_def
                                      lookup_num_set_tree_union
                                      option_CASE
     is_reachable_num_set_tree_union  RTC_MONO
                                      is_adjacent_num_set_tree_union
                                      is_reachable_def
     closure_spt_lemma                RTC_TRANS_L closure_spt_def
                                      closure_spt_ind
                                      domain_spt_fold_union domain_union
                                      is_adjacent_def is_reachable_def
                                      lookup_inter_alt rtc_is_adjacent
     closure_spt_thm                  RTC_REFL closure_spt_lemma
                                      is_reachable_def
     _                                LENGTH_toAList cake_add_simps
                                      delete_mk_wf domain_difference
                                      domain_insert domain_inter
                                      domain_mapi domain_mk_wf
                                      domain_union insert_mk_wf inter_LN
                                      inter_eq inter_mk_wf isEmpty_def
                                      isEmpty_union lookup_mk_wf
                                      map_map_K mk_wf_eq size_fromList
                                      size_map size_mapi subspt_union
                                      union_LN union_mk_wf wf_fromList
                                      wf_inter wf_list_to_num_set

*)
