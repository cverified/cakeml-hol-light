(* ======================================================== *)
(*  sptree: ported from HOL4's
    src/finite_maps/sptreeScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 106 files of the port.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

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
  `toAList = foldi (\k v a. (k,v) :: a) 0 []`;;

let toListA_def,toListA_ind = define_rec
  [`toListA acc LN = acc`;
   `toListA acc (LS a) = a :: acc`;
   `toListA acc (BN t1 t2) = toListA (toListA acc t2) t1`;
   `toListA acc (BS t1 a t2) = toListA (a :: toListA acc t2) t1`];;

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
   `fromAList ((x,y) :: xs) = sptree_insert x y (fromAList xs)`];;

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
   `list_to_num_set (n :: ns) = sptree_insert n one
  (list_to_num_set ns)`];;

let list_insert_def,list_insert_ind = define_rec
  [`list_insert [] t = t`;
   `list_insert (n :: ns) t = list_insert ns (sptree_insert n one
  t)`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let alist_insert_def,alist_insert_ind = define_wf
  `MEASURE (\(x0,x1,x2). list_size (\n. n) x0)`
  [`alist_insert vs xs t =
      match (vs,xs) with
        ([],xs) -> t
      | (vs,[]) -> t
      | ((v :: vs),(x :: xs)) -> sptree_insert v x (alist_insert
        vs xs t)`];;

let spts_to_alist_add_pause_def = new_definition
  `spts_to_alist_add_pause j q = (match q with [] -> [(j,LN)] |
  ((i,spt) :: q) -> ((i + j,spt) :: q))`;;

(* HOL4 sptreeScript.sml:2378: the overload add_pause, which the port
   expands *)

let spts_to_alist_aux_def,spts_to_alist_aux_ind = define_shaped_rec
  "match"
  [`spts_to_alist_aux i xs acc_cent acc_right acc_left repeat =
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
