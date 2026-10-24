(* ======================================================== *)
(*  balanced_map: ported from HOL4's
    examples/data-structures/balanced_bst/balanced_mapScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 7 files of the port.  *)
(* ======================================================== *)

needs "lib/comparison.ml";;
needs "lib/sorting.ml";;
needs "lib/ternaryComparisons.ml";;
(* HOL4 ancestors outside the port: option pair string arithmetic
   pred_set list finite_map alist *)

let key_set_def = cake_define
  `key_set cmp k = {k' | cmp k k' = EQUAL}`;;

let balanced_map_INDUCT,balanced_map_RECURSION = define_datatype
  "balanced_map = Tip | Bin (num) ('k) ('v) (balanced_map) \
   (balanced_map)";;

let ratio_def = cake_define
  `ratio = (2:num)`;;

let delta_def = cake_define
  `delta = (3:num)`;;

let balanced_map_size_def = cake_define_list
  [`balanced_map_size Tip = 0`;
   `balanced_map_size (Bin s k v l r) = s`];;
hol4_overload "size" "balanced_map_size";;

let bin_def = cake_define
  `bin k x l r = Bin (balanced_map_size l + balanced_map_size r + 1)
  k x l r`;;

let balanced_map_lookup_def = cake_define_list
  [`balanced_map_lookup cmp k Tip = NONE`;
   `balanced_map_lookup cmp k (Bin s k' v l r) =
      (match cmp k k' with LESS -> balanced_map_lookup cmp k l
        | GREATER -> balanced_map_lookup cmp k r | EQUAL -> SOME v)`];;
hol4_overload "lookup" "balanced_map_lookup";;

let empty_def = cake_define
  `balanced_map_empty = Tip`;;
hol4_overload "empty" "balanced_map_empty";;

let singleton_def = cake_define
  `singleton k x = Bin 1 k x Tip Tip`;;

let balanceL_def = cake_define
  `balanceL k x x3 x4 =
        match (x3,x4) with
          (Tip,Tip) ->
     Bin 1 k x Tip Tip
        | ((Bin s' k' v' Tip Tip),Tip) ->
     Bin 2 k x (Bin s' k' v' Tip Tip) Tip
        | ((Bin _7 lk lx Tip (Bin _8 lrk lrx _9 _10)),Tip) ->
     Bin 3 lrk lrx (Bin 1 lk lx Tip Tip) (Bin 1 k x Tip Tip)
        | ((Bin _11 lk lx (Bin s' k' v' l' r') Tip),Tip) ->
     Bin 3 lk lx (Bin s' k' v' l' r') (Bin 1 k x Tip Tip)
        | ((Bin ls lk lx (Bin lls k' v' l' r') (Bin lrs lrk lrx lrl
          lrr)),Tip) ->
     (if lrs < ratio * lls then
       Bin (1 + ls) lk lx (Bin lls k' v' l' r')
                        (Bin (1 + lrs) k x (Bin lrs lrk lrx lrl lrr)
                          Tip) else
       Bin (1 + ls) lrk lrx (Bin (1 + lls + balanced_map_size lrl) lk
         lx (Bin lls k' v' l' r') lrl)
                          (Bin (1 + balanced_map_size lrr) k x lrr
                            Tip))
        | (Tip,(Bin rs k' v' l' r')) ->
     Bin (1 + rs) k x Tip (Bin rs k' v' l' r')
        | ((Bin ls lk lx ll lr),(Bin rs k' v' l' r')) ->
     (if ls > delta * rs then
       match (ll,lr) with (Bin lls _12 _13 _14 _15,Bin lrs lrk lrx
         lrl lrr) ->
              (if lrs < ratio * lls then
                Bin (1 + ls + rs) lk lx ll (Bin (1 + rs + lrs) k x lr
                  (Bin rs k' v' l' r')) else
                Bin (1 + ls + rs) lrk lrx (Bin (1 + lls +
                  balanced_map_size lrl) lk lx ll lrl)
                              (Bin (1 + rs + balanced_map_size lrr) k
                                x lrr (Bin rs k' v' l' r'))) | (_16,_17)
                                -> Tip else
       // error "Failure in Data.Map.balanceL"
       Bin (1 + ls + rs) k x (Bin ls lk lx ll lr) (Bin rs k' v' l'
         r'))`;;

let balanceR_def = cake_define
  `balanceR k x x3 x4 =
        match (x3,x4) with
          (Tip,Tip) ->
     Bin 1 k x Tip Tip
        | (Tip,(Bin s' k' v' Tip Tip)) ->
     Bin 2 k x Tip (Bin s' k' v' Tip Tip)
        | (Tip,(Bin _24 rk rx Tip (Bin s' k' v' l' r'))) ->
     Bin 3 rk rx (Bin 1 k x Tip Tip) (Bin s' k' v' l' r')
        | (Tip,(Bin _25 rk rx (Bin _26 rlk rlx _27 _28) Tip)) ->
     Bin 3 rlk rlx (Bin 1 k x Tip Tip) (Bin 1 rk rx Tip Tip)
        | (Tip,(Bin rs rk rx (Bin rls rlk rlx rll rlr) (Bin rrs k' v'
          l' r'))) ->
     (if rls < ratio * rrs then
       Bin (1 + rs) rk rx (Bin (1 + rls) k x Tip (Bin rls rlk rlx rll
         rlr)) (Bin rrs k' v' l' r') else
       Bin (1 + rs) rlk rlx (Bin (1 + balanced_map_size rll) k x Tip
         rll)
                          (Bin (1 + rrs + balanced_map_size rlr) rk
                            rx rlr (Bin rrs k' v' l' r')))
        | ((Bin ls k' v' l' r'),Tip) ->
     Bin (1 + ls) k x (Bin ls k' v' l' r') Tip
        | ((Bin ls k' v' l' r'),(Bin rs rk rx rl rr)) ->
     (if rs > delta * ls then
       match (rl,rr) with (Bin rls rlk rlx rll rlr,Bin rrs _29 _30
         _31 _32) ->
              (if rls < ratio * rrs then
                Bin (1 + ls + rs) rk rx (Bin (1 + ls + rls) k x (Bin
                  ls k' v' l' r') rl) rr else
                Bin (1 + ls + rs) rlk rlx (Bin (1 + ls +
                  balanced_map_size rll) k x (Bin ls k' v' l' r') rll)
                              (Bin (1 + rrs + balanced_map_size rlr)
                                rk rx rlr rr)) | (_33,_34) -> Tip else
       // error "Failure in Data.Map.balanceR"
       Bin (1 + ls + rs) k x (Bin ls k' v' l' r') (Bin rs rk rx rl
         rr))`;;

let balanced_map_insert_def = cake_define_list
  [`balanced_map_insert cmp k v Tip = singleton k v`;
   `balanced_map_insert cmp k v (Bin s k' v' l r) =
      (match cmp k k' with LESS -> balanceL k' v'
        (balanced_map_insert cmp k v l) r | GREATER -> balanceR k'
        v' l (balanced_map_insert cmp k v r) | EQUAL -> Bin s k v l
        r)`];;
hol4_overload "insert" "balanced_map_insert";;

let insertR_def = cake_define_list
  [`insertR cmp k v Tip = singleton k v`;
   `insertR cmp k v (Bin s k' v' l r) =
      (match cmp k k' with LESS -> balanceL k' v' (insertR cmp
        k v l) r | GREATER -> balanceR k' v' l (insertR cmp k v r)
        | EQUAL -> Bin s k' v' l r)`];;

let insertMax_def = cake_define_list
  [`insertMax k v Tip = singleton k v`;
   `insertMax k v (Bin s k' v' l r) = balanceR k' v' l (insertMax k
  v r)`];;

let insertMin_def = cake_define_list
  [`insertMin k v Tip = singleton k v`;
   `insertMin k v (Bin s k' v' l r) = balanceL k' v' (insertMin k v
  l) r`];;

let deleteFindMax_def = cake_define
  `deleteFindMax x1 =
        match x1 with
          Bin s k x l Tip -> ((k,x),l)
        | (Bin s k x l r) ->
     (let (km,r') = deleteFindMax r in
       (km,balanceL k x l r'))
        | Tip ->
     (ARB,Tip)`;;

let deleteFindMin_def = cake_define
  `deleteFindMin x1 =
        match x1 with
          Bin s k x Tip r -> ((k,x),r)
        | (Bin s k x l r) ->
     (let (km,l') = deleteFindMin l in
       (km,balanceR k x l' r))
        | Tip ->
     (ARB,Tip)`;;

let glue_def = cake_define
  `glue l r =
        match (l,r) with
          (Tip,r) -> r
        | (l,Tip) -> l
        | (l,r) ->
     (if balanced_map_size l > balanced_map_size r then
       let ((km,m),l') = deleteFindMax l in
         balanceR km m l' r else
       let ((km,m),r') = deleteFindMin r in
         balanceL km m l r')`;;

let balanced_map_delete_def = cake_define_list
  [`balanced_map_delete cmp k Tip = Tip`;
   `balanced_map_delete cmp k (Bin s k' v l r) =
      (match cmp k k' with LESS -> balanceR k' v
        (balanced_map_delete cmp k l) r | GREATER -> balanceL k' v
        l (balanced_map_delete cmp k r) | Eq' -> glue l r)`];;
hol4_overload "delete" "balanced_map_delete";;

let trim_help_greater_def = cake_define_list
  [`trim_help_greater cmp lo (Bin s' k v' l' r) =
      (if cmp k lo = LESS \/ cmp k lo = EQUAL then
        trim_help_greater cmp lo r else
        Bin s' k v' l' r)`;
   `trim_help_greater cmp lo Tip = Tip`];;

let trim_help_lesser_def = cake_define_list
  [`trim_help_lesser cmp hi (Bin s' k v' l r') =
      (if cmp k hi = GREATER \/ cmp k hi = EQUAL then
        trim_help_lesser cmp hi l else
        Bin s' k v' l r')`;
   `trim_help_lesser cmp lo Tip = Tip`];;

let trim_help_middle_def = cake_define_list
  [`trim_help_middle cmp lo hi (Bin s' k v' l r) =
      (if cmp k lo = LESS \/ cmp k lo = EQUAL then
        trim_help_middle cmp lo hi r else if cmp k hi = GREATER \/
          cmp k hi = EQUAL then
        trim_help_middle cmp lo hi l else
        Bin s' k v' l r)`;
   `trim_help_middle lo cmp hi Tip = Tip`];;

let trim_def = cake_define
  `trim cmp x2 x3 t =
        match (x2,x3) with
          (NONE,NONE) -> t
        | ((SOME lk),NONE) -> trim_help_greater cmp lk t
        | (NONE,(SOME hk)) -> trim_help_lesser cmp hk t
        | ((SOME lk),(SOME hk)) -> trim_help_middle cmp lk hk t`;;

let link_def = cake_define
  `link k v l r =
        match (l,r) with
          (Tip,r) -> insertMin k v r
        | (l,Tip) -> insertMax k v l
        | ((Bin sizeL ky y ly ry),(Bin sizeR kz z lz rz)) ->
     (if delta * sizeL < sizeR then
       balanceL kz z (link k v (Bin sizeL ky y ly ry) lz) rz else if
         delta * sizeR < sizeL then
       balanceR ky y ly (link k v ry (Bin sizeR kz z lz rz)) else
       bin k v (Bin sizeL ky y ly ry) (Bin sizeR kz z lz rz))`;;

let filterLt_help_def = cake_define_list
  [`filterLt_help cmp b Tip = Tip`;
   `filterLt_help cmp b' (Bin s kx x l r) =
      (match cmp kx b' with LESS -> link kx x l (filterLt_help
        cmp b' r) | EQUAL -> l | GREATER -> filterLt_help cmp b' l)`];;

let filterLt_def = cake_define_list
  [`filterLt cmp NONE t = t`;
   `filterLt cmp (SOME b) t = filterLt_help cmp b t`];;

let filterGt_help_def = cake_define_list
  [`filterGt_help cmp b Tip = Tip`;
   `filterGt_help cmp b' (Bin s kx x l r) =
      (match cmp b' kx with LESS -> link kx x (filterGt_help
        cmp b' l) r | EQUAL -> r | GREATER -> filterGt_help cmp b'
        r)`];;

let filterGt_def = cake_define_list
  [`filterGt cmp NONE t = t`;
   `filterGt cmp (SOME b) t = filterGt_help cmp b t`];;

let hedgeUnion_def = cake_define
  `hedgeUnion cmp blo bhi t1 t2 =
        match (t1,t2) with
          (t1,Tip) -> t1
        | (Tip,(Bin _35 kx x l r)) ->
     link kx x (filterGt cmp blo l) (filterLt cmp bhi r)
        | (t1,(Bin _36 kx x Tip Tip)) -> insertR cmp kx x t1
        | ((Bin s kx x l r),t2) ->
     link kx x (hedgeUnion cmp blo (SOME kx) l (trim cmp blo (SOME
       kx) t2))
               (hedgeUnion cmp (SOME kx) bhi r (trim cmp (SOME kx)
                 bhi t2))`;;

let balanced_map_union_def = cake_define
  `balanced_map_union cmp t1 t2 =
        match (t1,t2) with
          (Tip,t2) -> t2
        | (t1,Tip) -> t1
        | (t1,t2) -> hedgeUnion cmp NONE NONE t1 t2`;;
hol4_overload "union" "balanced_map_union";;

let foldrWithKey_def = cake_define_list
  [`foldrWithKey f z' Tip = z'`;
   `foldrWithKey f z' (Bin _37 kx x l r) =
      foldrWithKey f (f kx x (foldrWithKey f z' r)) l`];;

let toAscList_def = cake_define
  `toAscList t = foldrWithKey (\k x xs. (k,x) :: xs) [] t`;;

let compare_def = cake_define
  `balanced_map_compare cmp1 cmp2 t1 t2 = list_compare (pair_compare
  cmp1 cmp2) (toAscList t1) (toAscList t2)`;;
hol4_overload "compare" "balanced_map_compare";;

let mapWithKey_def = cake_define_list
  [`mapWithKey f Tip = Tip`;
   `mapWithKey f (Bin sx kx x l r) =
         Bin sx kx (f kx x) (mapWithKey f l) (mapWithKey f r)`];;

let balanced_map_map_def = cake_define
  `balanced_map_map f t = mapWithKey (\k x. f x) t`;;
hol4_overload "map" "balanced_map_map";;

let to_fmap_def = cake_define_list
  [`to_fmap cmp Tip = FEMPTY`;
   `to_fmap cmp (Bin s k v l r) =
      (FUNION (to_fmap cmp l) (to_fmap cmp r)) |+ (key_set cmp
        k,v)`];;

let balanced_def = cake_define
  `balanced l r <=> l + r <= 1 \/ MAX l r <= delta * MIN l r`;;

let structure_size_def = cake_define_list
  [`structure_size Tip = 0`;
   `structure_size (Bin n k v l r) = 1 + structure_size l +
  structure_size r`];;

let key_ordered_def = cake_define_list
  [`key_ordered cmp k Tip res <=> T`;
   `key_ordered cmp k (Bin n k' v l r) res <=>
      cmp k k' = res /\
      key_ordered cmp k l res /\
      key_ordered cmp k r res`];;

let invariant_def = cake_define_list
  [`balanced_map_invariant cmp Tip <=> T`;
   `balanced_map_invariant cmp (Bin s k v l r) <=>
      s = 1 + structure_size l + structure_size r /\
      key_ordered cmp k l GREATER /\
      key_ordered cmp k r LESS /\
      balanced (balanced_map_size l) (balanced_map_size r) /\
      balanced_map_invariant cmp l /\
      balanced_map_invariant cmp r`];;
hol4_overload "invariant" "balanced_map_invariant";;

let exists_def = cake_define_list
  [`balanced_map_exists f Tip = F`;
   `balanced_map_exists f (Bin _38 kx x l r) =
      (if f kx x then
        T else if balanced_map_exists f l then
        T else if balanced_map_exists f r then
        T else
        F)`];;
