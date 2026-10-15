(* ======================================================== *)
(*  reg_alloc: ported from HOL4's
    compiler/backend/reg_alloc/reg_allocScript.sml  *)
(* ======================================================== *)

(*
  A monadic graph-coloring register allocator
*)

needs "basis/pure/mllist.ml";;
needs "lib/sorting.ml";;
needs "lib/sptree.ml";;
needs "lib/state_transformer.ml";;
needs "misc/misc.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(*
  The graph-coloring register allocator

  It currently uses several ``secret'' invariants that are important for
  performance but are not verified.

  This is an attempt at listing them:

  1) In ra_state.coalesced, coalesced[x] = x iff x is not coalesced.
     For non-Fixed pairs, coalesces happen ``downwards'' (smaller index
     survives). For Fixed-Atemp pairs, the Fixed node survives
       regardless
     of index, so coalesce_parent checks is_Fixed before the <= test.

  2) adjacency lists are ALWAYS sorted
*)

(*
  The tag datatype representing the state of nodes:

  Fixed n : means it is fixed to color n
  Atemp   : means that the node is allowed to be allocated to any
    register or stack pos
  Stemp   : only allowed to be mapped to k, k+1, ... (stack positions)
*)
let reg_alloc_tag_INDUCT,reg_alloc_tag_RECURSION = define_datatype
  "reg_alloc_tag = Fixed (num) | Atemp | Stemp";;

(*
  Inputs are tagged with Fixed, Atemp , Stemp

  At all times, maintain invariant that adjacent nodes cannot be both
    Fixed
  to the same number

  First pass changes all Atemps to either Fixed or Stemp
  - Proofs: Fixed/Stemp stays unchanged

  Second pass changes all Stemps to Fixed with argument ≥ k
  - Proof: No remaining Stemp, every input node is mapped to Fixed
*)

(* Coloring state
  - Invariant: all the arrays have dimension = dim
*)
let ra_state_FIELDS = define_record "ra_state"
  ["adj_ls","(num list) list";
   "node_tag","reg_alloc_tag list";
   "degrees","num list";
   "dim","num";
   "simp_wl","num list";
   "spill_wl","num list";
   "freeze_wl","num list";
   "avail_moves_wl","(num#num#num) list";
   "unavail_moves_wl","(num#num#num) list";
   "coalesced","num list";
   "move_related","bool list";
   "stack","num list"];;

(* HOL4 ML code, not ported:
val accessors = define_monad_access_funs ``:ra_state``;
*)

(* HOL4 ML code, not ported:
val adj_ls_accessors = el 1 accessors;
val (adj_ls,get_adj_ls_def,set_adj_ls_def) = adj_ls_accessors;
*)

(* HOL4 ML code, not ported:
val node_tag_accessors = el 2 accessors;
val (node_tag,get_node_tag_def,set_node_tag_def) = node_tag_accessors;
*)

(* HOL4 ML code, not ported:
val degrees_accessors = el 3 accessors;
val (degrees,get_degrees_def,set_degrees_def) = degrees_accessors;
*)

(* HOL4 ML code, not ported:
val coalesced_accessors = el 10 accessors;
val (coalesced, get_coalesced_def, set_coalesced_def) =
  coalesced_accessors;
*)

(* HOL4 ML code, not ported:
val move_related_accessors = el 11 accessors;
val (move_related, get_move_related_def, set_move_related_def) =
  move_related_accessors;
*)

(* Data type for the exceptions *)
let state_exn_INDUCT,state_exn_RECURSION = define_datatype
  "state_exn = reg_alloc_Fail (string) | reg_alloc_Subscript";;
hol4_overload "Fail" "reg_alloc_Fail";;
hol4_overload "Subscript" "reg_alloc_Subscript";;

(* Monadic functions to handle the exceptions *)
(* HOL4 ML code, not ported:
val exn_functions = define_monad_exception_functions ``:state_exn``
  ``:ra_state``;
*)
(* HOL4 overload (expanded in the port):
     failwith = raise_Fail *)

(* HOL4 ML code, not ported:
val sub_exn = ``Subscript``;
val update_exn = ``Subscript``;
*)

(* Fixed-size array manipulators *)
(* HOL4 ML code, not ported:
val arr_manip = define_MFarray_manip_funs
  [adj_ls_accessors,node_tag_accessors,degrees_accessors,
   coalesced_accessors, move_related_accessors] sub_exn update_exn;
*)

(* HOL4 ML code, not ported:
fun accessor_thm (a,b,c,d,e,f) = LIST_CONJ [b,c,d,e,f]
*)

(* HOL4 ML code, not ported:
val adj_ls_manip = el 1 arr_manip;
val node_tag_manip = el 2 arr_manip;
val degrees_manip = el 3 arr_manip;
val coalesced_manip = el 4 arr_manip;
val move_related_manip = el 5 arr_manip;
*)

(* Helper functions for defining the allocator *)

(* Monadic list functions -- doesn't care about order *)
let st_ex_FOREACH_def = cake_define
  `(st_ex_FOREACH [] a = return one) /\
   (st_ex_FOREACH (x :: xs) a =
   monad_ignore_bind
     (a x) (
     st_ex_FOREACH xs a))`;;

let st_ex_MAP_def = cake_define
  `(st_ex_MAP f [] = return []) /\
   (st_ex_MAP f (x :: xs) =
   monad_bind (f x) (\
     fx. monad_bind (st_ex_MAP f xs) (\
     fxs.
     return (fx :: fxs))))`;;

let st_ex_PARTITION_def = cake_define
  `(st_ex_PARTITION P [] tt ff = return (tt,ff)) /\
   (st_ex_PARTITION P (x :: xs) tt ff =
   monad_bind (P x) (\
     Px.
     if Px then
       st_ex_PARTITION P xs (x :: tt) ff else
       st_ex_PARTITION P xs tt (x :: ff)))`;;

let st_ex_FILTER_def = cake_define
  `(st_ex_FILTER P [] acc = return acc) /\
   (st_ex_FILTER P (x :: xs) acc =
   monad_bind (P x) (\
     Px.
     if Px then
       st_ex_FILTER P xs (x :: acc) else
       st_ex_FILTER P xs acc))`;;

(* Keep adjacency lists sorted by > *)

(* Insert an undirect edge into the adj list representation *)
let sorted_insert_def = cake_define
  `(sorted_insert (x:num) acc [] = REVERSE (x :: acc)) /\
   (sorted_insert x acc (y :: ys) =
     (if x = y then REVERSE acc ++ (y :: ys) else if x > y then
       REVERSE acc ++ (x :: y :: ys) else sorted_insert x (y :: acc)
       ys))`;;

let sorted_mem_def = cake_define
  `(sorted_mem (x:num) [] = F) /\
   (sorted_mem x (y :: ys) =
     (if x = y then T else if x > y then F else sorted_mem x ys))`;;

let insert_edge_def = cake_define
  `insert_edge x y =
   monad_bind (adj_ls_sub x) (\
     adjx. monad_bind (adj_ls_sub y) (\
     adjy.
     monad_ignore_bind
       (update_adj_ls x (sorted_insert y [] adjx)) (
       update_adj_ls y (sorted_insert x [] adjy))))`;;

(* insert a list of edges all adjacent to one node *)
let list_insert_edge_def = cake_define
  `(list_insert_edge x [] = return one) /\
   (list_insert_edge x (y :: ys) =
     monad_ignore_bind
       (insert_edge x y) (
       list_insert_edge x ys))`;;

let clique_insert_edge_def = cake_define
  `(clique_insert_edge [] = return one) /\
   (clique_insert_edge (x :: xs) =
   monad_ignore_bind
     (list_insert_edge x xs) (
     clique_insert_edge xs))`;;

(* assuming vertices in cli already forms a clique,
   extend it with new members
*)
let extend_clique_def = cake_define
  `(extend_clique [] cli = return cli) /\
   (extend_clique (x :: xs) cli =
     (if MEM x cli then
       extend_clique xs cli else
     monad_ignore_bind
       (list_insert_edge x cli) (
       extend_clique xs (x :: cli))))`;;

(* The allocator heuristics, designed to minimize proof at the
   cost of some extra computation *)

(* (Safely) decrement the degree of all vertices adjacent to n by 1 *)
let dec_deg_def = cake_define
  `dec_deg n =
   monad_bind (degrees_sub n) (\
     cd.
     update_degrees n (cd - 1))`;;

let dec_degree_def = cake_define
  `dec_degree n =
   monad_bind get_dim (\
     d.
     if n < d then
     monad_bind (adj_ls_sub n) (\
       adjs.
       st_ex_FOREACH adjs dec_deg) else
       return one)`;;

let add_simp_wl_def = cake_define
  `add_simp_wl ls =
   monad_bind get_simp_wl (\
     swl.
     set_simp_wl (ls ++ swl))`;;

let add_spill_wl_def = cake_define
  `add_spill_wl ls =
   monad_bind get_spill_wl (\
     swl.
     set_spill_wl (ls ++ swl))`;;

let add_freeze_wl_def = cake_define
  `add_freeze_wl ls =
   monad_bind get_freeze_wl (\
     fwl.
     set_freeze_wl (ls ++ fwl))`;;

(* push x onto the stack, deleting it from "existence" *)
let push_stack_def = cake_define
  `push_stack x =
   monad_bind get_stack (\
     swl. monad_ignore_bind
     (update_degrees x 0) (monad_ignore_bind
     (update_move_related x F) (
     set_stack (x :: swl))))`;;

let add_unavail_moves_wl_def = cake_define
  `add_unavail_moves_wl ls =
   monad_bind get_unavail_moves_wl (\
     swl.
     set_unavail_moves_wl (ls ++ swl))`;;

(* unspill:
   Move any vertices in the spill list that has
   degree < k into the simplify or freeze worklist
   Revive all neighboring moves of these nodes
*)
let is_not_coalesced_def = cake_define
  `is_not_coalesced d =
   monad_bind (coalesced_sub d) (\
     dt.
     return (d = dt))`;;

let split_degree_def = cake_define
  `split_degree d k v =
   (if v < d then
   monad_bind (degrees_sub v) (\
     vd. monad_bind (is_not_coalesced v) (\
     b.
     return (vd < k /\ b))) else
     return T)`;;

(* sort moves by priority *)
let sort_moves_def = cake_define
  `reg_alloc_sort_moves ls =
     sort (\((p:num),x,p',x'). p > p') ls`;;
hol4_overload "sort_moves" "reg_alloc_sort_moves";;

(* merge two sorted lists *)
let smerge_def = cake_define
  `smerge xs ys =
        match (xs,ys) with
          ([],ys) -> ys
        | (xs,[]) -> xs
        | ((((p:num),m) :: xs),((p',m') :: ys)) ->
       if p >= p' then
         (p,m) :: smerge xs ((p',m') :: ys) else
         (p',m') :: smerge ((p,m) :: xs) ys`;;

(*
  revive the unavailable moves that touch each neighbor
*)
let revive_moves_def = cake_define
  `revive_moves vs =
   monad_bind (st_ex_MAP adj_ls_sub vs) (\
     nbs. monad_bind get_unavail_moves_wl (\
     uam. monad_bind get_avail_moves_wl (\
     am.
     let (rev,unavail) = PARTITION
       (\(_1,(x,y)). EXISTS (sorted_mem x) nbs \/ EXISTS (sorted_mem
         y) nbs) uam in
     let sorted = smerge (sort_moves rev) am in
     monad_ignore_bind
       (set_avail_moves_wl sorted) (
       set_unavail_moves_wl unavail))))`;;

let unspill_def = cake_define
  `unspill (k:num) =
   monad_bind get_dim (\
     d. monad_bind get_spill_wl (\
     swl. monad_bind (st_ex_PARTITION (split_degree d k) swl [] [])
       (\
     (ltk,gtk). monad_ignore_bind
     (revive_moves ltk) (monad_bind (st_ex_PARTITION
       (move_related_sub) ltk [] []) (\
     (ltkfreeze,ltksimp). monad_ignore_bind
     (set_spill_wl gtk) (monad_ignore_bind
     (add_simp_wl ltksimp) (
     add_freeze_wl ltkfreeze)))))))`;;

(* simplify:
  Directly simplifies the entire list
  instead of doing it 1-by-1
  T = successful simplification
  F = no simplification
*)
let do_simplify_def = cake_define
  `do_simplify k =
   monad_bind get_simp_wl (\
     simps.
     if NULL simps then
       return F else
     monad_ignore_bind
       (st_ex_FOREACH simps dec_degree) (monad_ignore_bind
       (st_ex_FOREACH simps push_stack) (monad_ignore_bind
       (set_simp_wl []) (monad_ignore_bind
       (unspill k) (
       return T)))))`;;

(* increment degree of n by d *)
let inc_deg_def = cake_define
  `inc_deg n d =
   monad_bind (degrees_sub n) (\
     cd.
     update_degrees n (cd + d))`;;

(*
  Within the allocator, we will assume that all moves
  have the form:

  1) x:=y where x is Fixed (<k) or Atemp, and y is Atemp
  2) x < y
*)

(*
  do coalesce for real :
  perform a coalesce of (x,y) by merging y into x
  - this assumes y is Atemp
  - we only "pretend" to delete y from the graph
  Case 1:
  x -> v <- y, then the degree of v is reduced by 1
  Case 2:
  x -/-> v <- y, then the degree of x is increased by 1
  Case 3:
  x -> v <-/- y, no change
  In both cases, we leave the v-y edge dangling
*)

(* An actual register *)
let is_Fixed_def = cake_define
  `is_Fixed x =
   monad_bind (node_tag_sub x) (\
     xt.
     return (match xt with Fixed n -> T | _2 -> F))`;;

let do_coalesce_real_def = cake_define
  `do_coalesce_real x y case1 case2 =
   monad_ignore_bind
     (update_coalesced y x) (monad_bind (is_Fixed x) (\
     bx. monad_ignore_bind
     (if bx then return one else inc_deg x (LENGTH case2))
       (monad_ignore_bind
     (list_insert_edge x case2) (monad_ignore_bind
     (st_ex_FOREACH case1 dec_deg) (
     push_stack y)))))`;;

(* The coalesceable criterion, Briggs and George *)

(*
  Briggs:
  the result of combining x,y should have fewer than k neighbors
  of significant degree (i.e. degree ≥ k)

  George:
  assume that x is a high degree node (typically a "Fixed" node)
  then coalescing y into x is allowed if every neighbor of y not already
  a neighbor of x (i.e. case 2) has degree < k

  TODO: The implementation here isn't super great,
  because the George check is only
  really efficient if one has a true adjacency matrix representation
*)
let is_Atemp_def = cake_define
  `is_Atemp d =
   monad_bind (node_tag_sub d) (\
     dt.
     return (dt = Atemp))`;;

let is_Fixed_k_def = cake_define
  `is_Fixed_k k x =
   monad_bind (node_tag_sub x) (\
     xt.
     return (match xt with Fixed n -> n < k | _3 -> F))`;;

let considered_var_def = cake_define
  `considered_var k x =
   monad_bind (is_Atemp x) (\
     bx. monad_bind (is_Fixed_k k x) (\
     fx.
     return (bx \/ fx)))`;;

(* Fixed vars are treated as having infinite degree *)
let deg_or_inf_def = cake_define
  `deg_or_inf k x =
   monad_bind (is_Fixed_k k x) (\
     bx.
     if bx then return k else degrees_sub x)`;;

let bg_ok_def = cake_define
  `bg_ok k x y =
   monad_bind (adj_ls_sub x) (\
     adjx. monad_bind (adj_ls_sub y) (\
     adjy.
     let (case1,case2) = PARTITION (\v. sorted_mem v adjx) adjy in
     monad_bind (st_ex_FILTER (considered_var k) case1 []) (\
       case1. monad_bind (st_ex_FILTER (considered_var k) case2 [])
         (\
       case2. monad_bind (st_ex_MAP (deg_or_inf k) case2) (\
       case2degs.
       let c2len = LENGTH (FILTER (\x. x >= k) case2degs) in
       if c2len = 0 then return (SOME (case1,case2)) else
       let case3 = FILTER (\v. ~sorted_mem v adjy) adjx in
       monad_bind (st_ex_FILTER (considered_var k) case3 []) (\
         case3. monad_bind (st_ex_MAP (deg_or_inf (k + 1)) case1) (\
         case1degs. monad_bind (st_ex_MAP (deg_or_inf k) case3) (\
         case3degs. monad_bind (return (LENGTH (FILTER (\x. x - 1 >=
           k) case1degs))) (\
         c1len. monad_bind (return (LENGTH (FILTER (\x. x >= k)
           case3degs))) (\
         c3len.
         if c1len + c2len + c3len < k then
           return (SOME (case1,case2)) else
           return NONE))))))))))`;;

(*
  Consistency check for moves
  Any moves failing this check can be directly discarded
  1) x ≠ y
  2) x,y must not already clash

  3) x,y either fixed or atemps and not both fixed
*)

let consistency_ok_def = cake_define
  `consistency_ok x y =
   (if x = y then
     return F else
   monad_bind (adj_ls_sub y) (\
     adjy.
     if sorted_mem x adjy then return F else
     monad_bind (is_Fixed x) (\
       bx. monad_bind (is_Fixed y) (\
       by. monad_bind (move_related_sub x) (\
       movrelx. monad_bind (move_related_sub y) (\
       movrely.
       return ((bx \/ movrelx) /\ (by \/ movrely) /\ ~(bx /\
         by))))))))`;;

(*
  find the ancestor
  and collapse along the way

*)
let coalesce_parent_def = cake_define
  `coalesce_parent x =
   monad_bind (coalesced_sub x) (\
     xt. monad_bind (is_Fixed xt) (\
     bx.
     if bx then
       return xt else
       if x <= xt then
         return x else
       monad_bind (coalesce_parent xt) (\
         anc. monad_ignore_bind
         (update_coalesced x anc) (
         return anc))))`;;

let canonize_move_def = cake_define
  `canonize_move x y =
   monad_bind (is_Fixed x) (\
     bx. monad_bind (is_Fixed y) (\
     by.
     if by then return (y,x) else if bx then return (x,y) else
       if x < y then return (x,y) else return (y,x)))`;;

(*
  Picks apart the available moves worklist
  1) If we find any inconsistent ones -> throw them away
  not necessary? -- 2) canonize the move to put fixed register in front
  3) returns the first bg_ok move that is also consistent
*)
let st_ex_FIRST_def = cake_define
  `(st_ex_FIRST P Q [] unavail = return (NONE,unavail)) /\
   (st_ex_FIRST P Q (m :: ms) unavail =
     (let (p,(x,y)) = m in
     monad_bind (coalesce_parent x) (\
       x. monad_bind (coalesce_parent y) (\
       y. monad_bind (P x y) (\
       b1.
       if ~b1 then
         st_ex_FIRST P Q ms unavail else
       monad_bind (canonize_move x y) (\
         (x,y). monad_bind (Q x y) (\
         optb2.
         match optb2 with
           NONE -> st_ex_FIRST P Q ms ((p,(x,y)) :: unavail) | SOME
             pr ->
           return (SOME ((x,y),pr,ms),unavail))))))))`;;

let respill_def = cake_define
  `respill k x =
   monad_bind (degrees_sub x) (\
     xd.
     if xd < k then return one else
     monad_bind get_freeze_wl (\
       freeze.
       if MEM x freeze then
       monad_ignore_bind
         (add_spill_wl [x]) (
         set_freeze_wl (FILTER (\y. ~(y = x)) freeze)) else return
           one))`;;

let do_coalesce_def = cake_define
  `do_coalesce k =
   monad_bind get_avail_moves_wl (\
     am. monad_bind (st_ex_FIRST consistency_ok (bg_ok k) am []) (\
     (ores,unavail). monad_ignore_bind
     (add_unavail_moves_wl unavail) (
     match ores with
       NONE ->
         monad_ignore_bind
           (set_avail_moves_wl []) (
           return F) | SOME ((x,y),(case1,case2),ms) ->
     monad_ignore_bind
       (set_avail_moves_wl ms) (monad_ignore_bind
       (do_coalesce_real x y case1 case2) (monad_ignore_bind
       (unspill k) (monad_ignore_bind
       (respill k x) (
       return T)))))))`;;

(*
  prefreeze: make the freeze and spill worklists consistent.

  If this makes a node simplifiable, then we skip freezing

  If we got here, it means coalescing failed, i.e. everything is
  an "unavailable" move now

  Here, we cleanup any potential mess in the coalescing phase
  1) Filter out all nodes y that have been coalesced
  2) delete any moves in the unavailable list, that are actually invalid
  3) mark only nodes involved in the remaining moves as "move related"
  4) simplify any resulting non-move-related nodes

*)

let reset_move_related_def = cake_define
  `reset_move_related ls =
   monad_bind get_dim (\
     d. monad_ignore_bind
     (st_ex_FOREACH (COUNT_LIST d) (\x. update_move_related x F)) (
     st_ex_FOREACH ls (\(_4,(x,y)).
         monad_bind (is_Fixed x) (\
           bx. monad_bind (is_Fixed y) (\
           by. monad_ignore_bind
           (update_move_related x (~bx)) (
           update_move_related y (~by)))))))`;;

let do_prefreeze_def = cake_define
  `do_prefreeze k =
   monad_bind get_freeze_wl (\
     fwl_pre. monad_bind (st_ex_FILTER is_not_coalesced fwl_pre [])
       (\
     fwl. monad_bind get_spill_wl (\
     swl_pre. monad_bind (st_ex_FILTER is_not_coalesced swl_pre [])
       (\
     swl. monad_ignore_bind
     (set_spill_wl swl) (monad_bind get_unavail_moves_wl (\
     uam_pre. monad_bind (st_ex_FILTER (\(_5,(x,y)). consistency_ok x
       y) uam_pre []) (\
     uam. monad_ignore_bind
     (reset_move_related uam) (monad_bind (set_unavail_moves_wl uam)
       (\
     uam. monad_bind (st_ex_PARTITION (move_related_sub) fwl [] [])
       (\
     (ltkfreeze,ltksimp). monad_ignore_bind
     (add_simp_wl ltksimp) (monad_ignore_bind
     (set_freeze_wl ltkfreeze) (
     do_simplify k))))))))))))`;;

(* if prefreeze failed, then just freeze *)

let do_freeze_def = cake_define
  `do_freeze k =
   monad_bind get_freeze_wl (\
     freeze.
     match freeze with
       [] -> return F | x :: xs ->
       monad_ignore_bind
         (dec_degree x) (monad_ignore_bind
         (push_stack x) (monad_ignore_bind
         (set_freeze_wl xs) (monad_ignore_bind
         (unspill k) (
         return T)))))`;;

(* spill:
  If given a spill cost,
    picks the cheapest node in the spill worklist,
    based on spill cost / degree
  Otherwise,
    picks highest degree node
*)
let safe_div_def = cake_define
  `safe_div x v = (if v = 0 then 0 else x DIV v)`;;

let st_ex_list_MIN_cost_def = cake_define
  `(st_ex_list_MIN_cost scost [] d k v acc = return (k,acc)) /\
   (st_ex_list_MIN_cost scost (x :: xs) d k v acc =
   (if x < d then
     monad_bind (degrees_sub x) (\
       xv. monad_bind (return (safe_div (lookup_any x scost 0) xv))
         (\
       cost.
       if v > cost then
         st_ex_list_MIN_cost scost xs d x cost (k :: acc) else
         st_ex_list_MIN_cost scost xs d k v (x :: acc))) else
     st_ex_list_MIN_cost scost xs d k v acc))`;;

let st_ex_list_MAX_deg_def = cake_define
  `(st_ex_list_MAX_deg [] d k v acc = return (k,acc)) /\
   (st_ex_list_MAX_deg (x :: xs) d k v acc =
   (if x < d then
     monad_bind (degrees_sub x) (\
       xv.
       if v < xv then
         st_ex_list_MAX_deg xs d x xv (k :: acc) else
         st_ex_list_MAX_deg xs d k v (x :: acc)) else
   st_ex_list_MAX_deg xs d k v acc))`;;

let do_spill_def = cake_define
  `do_spill scostopt k =
   monad_bind get_spill_wl (\
     spills. monad_bind get_dim (\
     d.
     match spills with
       [] -> return F | (x :: xs) ->
       monad_bind (degrees_sub x) (\
         xv. monad_bind (match scostopt with
               NONE -> st_ex_list_MAX_deg xs d x xv [] | SOME scost
                 -> st_ex_list_MIN_cost scost xs d x (safe_div
                 (lookup_any x scost 0) xv) []) (\
         (y,ys). monad_ignore_bind
         (dec_degree y) (monad_ignore_bind
         (push_stack y) (monad_ignore_bind
         (set_spill_wl ys) (monad_ignore_bind
         (unspill k) (
         return T))))))))`;;

let do_step_def = cake_define
  `do_step scost k =
   monad_bind (do_simplify k) (\
     b.
     if b then return b else
     monad_bind (do_coalesce k) (\
       b.
       if b then return b else
       monad_bind (do_prefreeze k) (\
         b.
         if b then return b else
         monad_bind (do_freeze k) (\
           b.
           if b then
             return b else
             monad_bind (do_spill scost k) (\
               b.
               return b)))))`;;

let rpt_do_step_def = cake_define
  `(rpt_do_step scost k 0 = return one) /\
   (rpt_do_step scost k (SUC c) =
   monad_bind (do_step scost k) (\
     b.
     if b then rpt_do_step scost k c else return one))`;;

(*
  The coloring functions
*)

(* Removing adjacent colours from ks *)
let remove_colours_def = cake_define
  `remove_colours x1 ks =
        match (x1,ks) with
          ((ls:num list),[]) -> return []
        | ([],(ks:num list)) -> return ks
        | ((x :: xs),ks) ->
       monad_bind (node_tag_sub x) (\
         cx. monad_bind
         (match cx with
           Fixed c ->
             remove_colours xs (FILTER (\x. ~(x = c)) ks) | _6 ->
             remove_colours xs ks) (\
         r.
         return r))`;;

(* First colouring -- turns all Atemps into Fixeds or Stemps drawing
   from colors in ks *)
(* Assign a tag to an Atemp node, skipping if it is not actually an
   Atemp *)

let assign_Atemp_tag_def = cake_define
  `assign_Atemp_tag ks prefs n =
   monad_bind (node_tag_sub n) (\
     ntag.
     match ntag with
       Atemp ->
       monad_bind (adj_ls_sub n) (\
         adjs. monad_bind (remove_colours adjs ks) (\
         ks.
         match ks with
           [] -> update_node_tag n Stemp | (x :: _7) ->
           monad_bind (prefs n ks) (\
             c.
             match c with
               NONE ->
               update_node_tag n (Fixed x) | SOME y ->
               update_node_tag n (Fixed y)))) | _8 -> return one)`;;

(* The first allocation step *)
(* k = num registers, ls = heuristic list, prefs = coloring preference
   *)
let assign_Atemps_def = cake_define
  `assign_Atemps k ls prefs =
   monad_bind get_dim (\
     d. monad_bind (return (FILTER (\n. n < d) ls)) (\
     ls. monad_bind (return (GENLIST (\x. x) k)) (\
     ks. monad_bind (return (GENLIST (\x. x) d)) (\
     cs. monad_ignore_bind
     (st_ex_FOREACH ls (assign_Atemp_tag ks prefs)) (
     st_ex_FOREACH cs (assign_Atemp_tag ks prefs))))))`;;

(* Default makes it easier to translate, doesn't matter for our purposes
   what
   the default is *)
let tag_col_def = cake_define
  `tag_col x1 =
        match x1 with
          (Fixed n) -> n
        | _9 -> 0`;;

(* Find the first available in k,k+1,...
   assuming input is sorted
*)
let unbound_colour_def = cake_define
  `(unbound_colour col [] = col) /\
   (unbound_colour col ((x:num) :: xs) =
     (if col < x then
       col else if x = col then
       unbound_colour (col + 1) xs else
       unbound_colour col xs))`;;

(* Second colouring -- turns all Stemps into Fixed ≥ k *)
let assign_Stemp_tag_def = cake_define
  `assign_Stemp_tag k prefs n =
   monad_bind (node_tag_sub n) (\
     ntag.
     match ntag with
       Stemp ->
       monad_bind (adj_ls_sub n) (\
         adjs. monad_bind (st_ex_MAP node_tag_sub adjs) (\
         tags.
         let bads = sort (\x y. x <= y) (MAP tag_col tags) in
         monad_bind (prefs n bads) (\
           c.
           match c with
             NONE ->
               update_node_tag n (Fixed (unbound_colour k bads)) |
                 SOME y ->
               update_node_tag n (Fixed y)))) | _10 -> return one)`;;


(* The second allocation step *)
let assign_Stemps_def = cake_define
  `assign_Stemps k prefs =
   monad_bind get_dim (\
     d. monad_bind (return (GENLIST (\x. x) d)) (\
     cs.
     st_ex_FOREACH cs (assign_Stemp_tag k prefs)))`;;

(* Monadic biased selection oracle, finds the first matching color *)
let first_match_col_def = cake_define
  `(first_match_col ks [] = return NONE) /\
   (first_match_col ks (x :: xs) =
     monad_bind (node_tag_sub x) (\
       c.
       match c with
         Fixed m ->
           (if MEM m ks then return (SOME m) else first_match_col
             ks xs) | _12 -> first_match_col ks xs))`;;

(* Clash tree representation of a program -- this is designed as an
   interface:
  wordLang program -> clash tree -> reg alloc

  It only represents wordLang programs, which do not have back-edges
  The allocator itself is more general, and supports arbitrary graphs
  It serves two purposes:
  1) slightly more efficient checking of coloring oracles
  2) it gets compiled in to the clash graphs for the allocator

  TODO: probably want to move the clash tree representation up and
    separate it
  from the allocator
*)

let clash_tree_INDUCT,clash_tree_RECURSION = define_datatype
  "clash_tree = reg_alloc_Delta (num list) (num list) | reg_alloc_Set \
   (one spt) | reg_alloc_Branch ((one spt) option) (clash_tree) \
   (clash_tree) | reg_alloc_Seq (clash_tree) (clash_tree)";;
hol4_overload "Delta" "reg_alloc_Delta";;
hol4_overload "Set" "reg_alloc_Set";;
hol4_overload "Branch" "reg_alloc_Branch";;
hol4_overload "Seq" "reg_alloc_Seq";;

(* --- clash_tree oracle checks --- *)
let numset_list_delete_def = cake_define
  `(numset_list_delete [] (t:'a spt) = t) /\
   (numset_list_delete (x :: xs) t = numset_list_delete xs (delete
     x t))`;;

(*Check that a numset is injective over the clash sets in an interpreted
   tree*)
let check_col_def = cake_define
  `check_col f t =
     (let names = MAP (f o FST) (toAList t) in
     if ALL_DISTINCT names then
       SOME (t,fromAList (MAP (\x. (x,one)) names)) else NONE)`;;

let check_partial_col_def = cake_define
  `(check_partial_col f [] t ft = SOME (t,ft)) /\
   (check_partial_col f (x :: xs) t ft =
     (match lookup x t with
       SOME one -> check_partial_col f xs t ft | NONE ->
     (match lookup (f x) ft with
       NONE -> check_partial_col f xs (insert x one t) (insert (f
         x) one ft) | SOME one -> NONE)))`;;

(* The checking function, used by oracle, and also used as part of the
   correctness proof *)
(* live = the liveset, flive = the liveset with f applied over it*)
let check_clash_tree_def = cake_define
  `(check_clash_tree f (Delta w r) live flive =
     (match check_partial_col f w live flive with
       NONE -> NONE | SOME _14 ->
     (let del_w = (numset_list_delete w live) in
     let fdel_w = (numset_list_delete (MAP f w) flive) in
     check_partial_col f r del_w fdel_w))) /\
   (check_clash_tree f (Set t) live flive = check_col f t) /\
   (check_clash_tree f (Branch topt t1 t2) live flive =
     (match check_clash_tree f t1 live flive with
       NONE -> NONE | SOME (t1_out,ft1_out) ->
     (match check_clash_tree f t2 live flive with
       NONE -> NONE | SOME (t2_out,ft2_out) ->
     (match topt with
       NONE ->
         check_partial_col f (MAP FST (toAList (difference t2_out
           t1_out))) t1_out ft1_out | SOME t -> check_col f t)))) /\
   (check_clash_tree f (Seq t1 t2) live flive =
     (match check_clash_tree f t2 live flive with
       NONE -> NONE | SOME (t2_out,ft2_out) ->
       check_clash_tree f t1 t2_out ft2_out))`;;

(* --
compile clash_trees into a register allocator state
This produces two sptrees that re-map clash_tree variables
into the register allocator state, and vice versa
The second remap is probably not necessary?
-- *)

(* Map clash tree variables into allocator nodes, also computes the
  size of the array required
  ta = to allocator
  fa = from allocator
  nv = next fresh name
*)
let list_remap_def = cake_define
  `(list_remap [] (ta,fa,nv) = (ta,fa,nv)) /\
   (list_remap (x :: xs) (ta,fa,nv) =
     (match lookup x ta with
       SOME v -> list_remap xs (ta,fa,nv) | NONE ->
       list_remap xs (insert x nv ta,insert nv x fa,nv + 1)))`;;

let mk_bij_aux_def = cake_define
  `(mk_bij_aux (Delta writes reads) tfn =
     list_remap writes (list_remap reads tfn)) /\
   (mk_bij_aux (Set t) tfn =
     list_remap (MAP FST (toAList t)) tfn) /\
   (mk_bij_aux (Branch topt t1 t2) tfn =
      (let tfn' = mk_bij_aux t2 (mk_bij_aux t1 tfn) in
      match topt with
        NONE -> tfn' | SOME ts -> list_remap (MAP FST (toAList ts))
          tfn')) /\
   (mk_bij_aux (Seq t1 t2) tfn =
     mk_bij_aux t1 (mk_bij_aux t2 tfn))`;;

let mk_bij_def = cake_define
  `mk_bij t =
     (let (ta,fa,n) = mk_bij_aux t (LN,LN,0) in
     (ta,fa,n))`;;
    (* Hide the sptree impl
    ((λi. lookup_any i ta 0),(λi. lookup_any i fa 0), n)` *)

(*Distinguish 3 kinds of variables:
  Evens are physical registers
  4n+1 are allocatable registers
  4n+3 are stack registers*)

let is_stack_var_def = cake_define
  `is_stack_var (n:num) = (n MOD 4 = 3)`;;
let is_phy_var_def = cake_define
  `is_phy_var (n:num) = (n MOD 2 = 0)`;;
let is_alloc_var_def = cake_define
  `is_alloc_var (n:num) = (n MOD 4 = 1)`;;

(* Set the tags according to wordLang conventions *)
let mk_tags_def = cake_define
  `mk_tags n fs fa =
   monad_bind (return (GENLIST (\x. x) n)) (\
     inds.
     st_ex_FOREACH inds
     (\i.
       let v = fa i in
       let remainder = v MOD 4 in
       if remainder = 1 then
         (match lookup v fs with
           NONE -> update_node_tag i Atemp | SOME one ->
             update_node_tag i Stemp) else if remainder = 3 then
         update_node_tag i Stemp else
         update_node_tag i (Fixed (v DIV 2))))`;;

(* Initializes the clash_graph using a clash_tree and a remapping
   bijection *)
let mk_graph_def = cake_define
  `(mk_graph ta (Delta w r) liveout =
     monad_bind (return (MAP ta w)) (\
       wta. monad_bind (return (MAP ta r)) (\
       rta. monad_bind (extend_clique wta liveout) (\
       live. monad_bind (return (FILTER (\x. ~MEM x wta) live)) (\
       live. monad_bind (extend_clique rta live) (\
       livein.
       return livein)))))) /\
   (mk_graph ta (Set t) liveout =
     monad_bind (return (MAP ta (MAP FST (toAList t)))) (\
       live. monad_ignore_bind
       (clique_insert_edge live) (
       return live))) /\
   (mk_graph ta (Branch topt t1 t2) liveout =
     monad_bind (mk_graph ta t1 liveout) (\
       t1_live. monad_bind (mk_graph ta t2 liveout) (\
       t2_live.
       (match topt with
         NONE ->
         monad_bind (extend_clique t1_live t2_live) (\
           livein.
           return livein) | SOME t ->
         monad_bind (return (MAP ta (MAP FST (toAList t)))) (\
           clashes. monad_ignore_bind
           (clique_insert_edge clashes) (
           return clashes)))))) /\
   (mk_graph ta (Seq t1 t2) liveout =
     monad_bind (mk_graph ta t2 liveout) (\
       live.
       mk_graph ta t1 live))`;;

let sp_default_def = cake_define
  `sp_default t i =
   (match lookup i t with NONE -> (if is_phy_var i then i DIV 2
     else 0) | SOME x -> x)`;;

let extend_graph_def = cake_define
  `(extend_graph ta [] = return one) /\
   (extend_graph ta ((x,y) :: xs) =
   monad_ignore_bind
     (insert_edge (ta x) (ta y)) (
     extend_graph ta xs))`;;

(* sets up the register allocator init state with the clash_tree input
  TODO: should the sptrees be hidden right away?
  It might be easier to transfer an sptree directly for the oracle
    register
  allocator

  ct = clash_tree
  forced = forced edges -- will need new proof that all forced edges are
    in the tree
*)
let init_ra_state_def = cake_define
  `init_ra_state ct forced fs (ta,fa,n) =
   monad_ignore_bind
     (mk_graph (sp_default ta) ct []) (monad_ignore_bind
     (extend_graph (sp_default ta) forced) (
     mk_tags n fs (sp_default fa)))`;;

(* work around translator bug *)
let do_upd_coalesce_def = cake_define
  `do_upd_coalesce i =
   update_coalesced i (0 + i)`;;

(* Initializer for the first allocation step *)
let init_alloc1_heu_def = cake_define
  `init_alloc1_heu moves d k =
   monad_bind (return (COUNT_LIST d)) (\
     ds. monad_bind (st_ex_FILTER is_Atemp ds []) (\
     allocs. monad_ignore_bind
     (st_ex_FOREACH ds
       (\i.
       monad_bind (adj_ls_sub i) (\
         adjls. monad_bind (st_ex_FILTER (\v. considered_var k v)
           adjls []) (\
         fills.
         update_degrees i (LENGTH fills))))) (monad_ignore_bind
     (st_ex_FOREACH ds do_upd_coalesce) (monad_ignore_bind
     (set_avail_moves_wl (sort_moves moves)) (monad_ignore_bind
     (reset_move_related moves) (monad_bind (st_ex_PARTITION
       (split_degree d k) allocs [] []) (\
     (ltk,gtk). monad_bind (st_ex_PARTITION (move_related_sub) ltk []
       []) (\
     (ltkfreeze,ltksimp). monad_ignore_bind
     (set_spill_wl gtk) (monad_ignore_bind
     (set_simp_wl ltksimp) (monad_ignore_bind
     (set_freeze_wl ltkfreeze) (
     return (LENGTH allocs))))))))))))`;;

let do_alloc1_def = cake_define
  `do_alloc1 moves scost k =
   monad_bind get_dim (\
     d. monad_bind (init_alloc1_heu moves d k) (\
     l. monad_ignore_bind
     (rpt_do_step scost k l) (monad_bind get_stack (\
     st.
     return st))))`;;

let extract_tag_def = cake_define
  `((extract_tag t = (match t with
     Fixed m -> m | _15 -> 0))
   End'
   Definition extract_color_def:extract_color ta) =
   monad_bind (return (toAList ta)) (\
     taa. monad_bind (st_ex_MAP (\(k,v).
       monad_bind (node_tag_sub v) (\
         t.
         return (k,extract_tag t))) taa) (\
     itags.
     return (fromAList itags)))`;;

let pri_move_insert_def = cake_define
  `pri_move_insert p x y acc =
   (match lookup x acc with
     NONE ->
       insert x [(p,y)] acc | SOME ls ->
       insert x ((p,y) :: ls) acc)`;;

let undir_move_insert_def = cake_define
  `undir_move_insert p x y acc =
     pri_move_insert p x y (pri_move_insert p y x acc)`;;

let moves_to_sp_def = cake_define
  `(moves_to_sp [] acc = acc) /\
   (moves_to_sp (move' :: xs) acc =
     (let (p,x,y) = move' in
     moves_to_sp xs (undir_move_insert p x y acc)))`;;

(*Do a consistency sort after setting up the sptree of moves*)
let resort_moves_def = cake_define
  `resort_moves acc =
   map (\ls. MAP SND (sort_moves ls)) acc`;;

let algorithm_INDUCT,algorithm_RECURSION = define_datatype
  "algorithm = reg_alloc_Simple | reg_alloc_IRC";;
hol4_overload "Simple" "reg_alloc_Simple";;
hol4_overload "IRC" "reg_alloc_IRC";;

(* Read-only version of coalesce_parent: follows the coalesce chain
   to the root without path compression. Safe for use in biased_pref
   where state must not be modified. *)
let coalesce_root_def = cake_define
  `coalesce_root x =
   monad_bind (coalesced_sub x) (\
     xt. monad_bind (is_Fixed xt) (\
     bx.
     if bx then
       return xt else
       if x <= xt then
         return x else
         coalesce_root xt))`;;

(* mtable is an sptree lookup for the moves *)
let biased_pref_def = cake_define
  `biased_pref mtable n ks =
   monad_bind get_dim (\
     d.
     if n < d then
     monad_bind (coalesce_root n) (\
       v.
       let vs = match lookup n mtable with NONE -> [] | SOME vs -> vs
         in
       handle_Subscript (first_match_col ks (v :: vs)) (return NONE))
         else
       return NONE)`;;

(* very similar to consistency_ok, but for initializing *)
let full_consistency_ok_def = cake_define
  `full_consistency_ok k x y =
   (if x = y then
     return F else
   monad_bind get_dim (\
     d.
     if x >= d \/ y >= d then return F else
     monad_bind (adj_ls_sub y) (\
       adjy.
       if sorted_mem x adjy then return F else
       monad_bind (is_Fixed_k k x) (\
         bx. monad_bind (is_Fixed_k k y) (\
         by. monad_bind (is_Atemp x) (\
         ax. monad_bind (is_Atemp y) (\
         ay.
         return ((bx \/ ax) /\ (by \/ ay) /\ ~(bx /\ by)))))))))`;;

let update_move_def = cake_define
  `update_move spta ((p:num),((x:num),(y:num))) =
   (let spx:num = spta x in
   let spy:num = spta y in
   if spx <= spy then
     (p,(spx,spy)) else
     (p,(spy,spx)))`;;

(* These behave in reverse to their other versions *)
let neg_first_match_col_def = cake_define
  `(neg_first_match_col k bads [] = return NONE) /\
   (neg_first_match_col k bads (x :: xs) =
     monad_bind (node_tag_sub x) (\
       c.
       match c with
         Fixed m ->
           (if MEM m bads \/ m < k then neg_first_match_col k bads
             xs else return (SOME m)) | _17 -> neg_first_match_col k
             bads xs))`;;

let neg_biased_pref_def = cake_define
  `neg_biased_pref k mtable n bads =
   monad_bind get_dim (\
     d.
     if n < d then
       let vs = match lookup n mtable with NONE -> [] | SOME vs -> vs
         in
       handle_Subscript (neg_first_match_col k bads vs) (return NONE)
         else
       return NONE)`;;

(* Putting everything together in one call *)
let do_reg_alloc_def = cake_define
  `do_reg_alloc alg scost k moves ct forced fs (ta,fa,n) =
   monad_ignore_bind
     (init_ra_state ct forced fs (ta,fa,n)) (monad_bind (return (MAP
       (update_move (sp_default ta)) moves)) (\
     moves0. monad_bind (st_ex_FILTER (\(_18,(x,y)).
       full_consistency_ok k x y) moves0 []) (\
     moves. monad_bind (do_alloc1 (if alg = Simple then [] else
       moves) scost k) (\
     ls. monad_bind (return (resort_moves (moves_to_sp moves0 LN)))
       (\
     mvs. monad_ignore_bind
     (assign_Atemps k ls (biased_pref mvs)) (monad_ignore_bind
     (assign_Stemps k (neg_biased_pref k mvs)) (monad_bind
       (extract_color ta) (\
     spcol.
     return spcol))))))))`;;

(* As we are using fixed-size array, we need to define a different
   record type for the initialization *)
(* HOL4 ML code, not ported:
val array_fields_names = ["adj_ls", "node_tag",
  "degrees","coalesced","move_related"];
val run_ira_state_def = define_run ``:ra_state``
                                       array_fields_names
                                      "ira_state";
*)

(* The top-level (non-monadic) reg_alloc call which should be modified
   to fit
   the translator's requirements *)

let reg_alloc_aux_def = cake_define
  `reg_alloc_aux alg scost k moves ct forced fs (ta,fa,n) =
     run_ira_state (do_reg_alloc alg scost k moves ct forced fs
       (ta,fa,n))
                       (mk_ra_state (n,[]) (n,Atemp) (n,0) n [] []
                         [] [] [] (n,0) (n,F) [])`;;

let reg_alloc_def = cake_define
  `reg_alloc alg scost k moves ct forced fs =
     reg_alloc_aux alg scost k moves ct forced fs (mk_bij ct)`;;
