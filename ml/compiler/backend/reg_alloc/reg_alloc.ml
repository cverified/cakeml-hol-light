(* ======================================================== *)
(*  reg_alloc: ported from HOL4's
    compiler/backend/reg_alloc/reg_allocScript.sml
    A definition theory, with 88 definitions, 5 datatypes and 6
    theorems.  Needed by 12 files of the port.  *)
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

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "reg_alloc"
  ["ml_monadBase"; "mllist"];;


hol4_overload "++" "otherwise";;

(*
  The graph-coloring register allocator

  It currently uses several ``secret'' invariants that are important for
  performance but are not verified.

  This is an attempt at listing them:

  1) In ra_state.coalesced, coalesced[x] = x iff x is not coalesced.
     For non-Fixed pairs, coalesces happen ``downwards'' (smaller index
     survives). For Fixed-Atemp pairs, the Fixed node survives regardless
     of index, so coalesce_parent checks is_Fixed before the <= test.

  2) adjacency lists are ALWAYS sorted
*)

(*
  The tag datatype representing the state of nodes:

  Fixed n : means it is fixed to color n
  Atemp   : means that the node is allowed to be allocated to any register or stack pos
  Stemp   : only allowed to be mapped to k, k+1, ... (stack positions)
*)
let reg_alloc_tag_INDUCT,reg_alloc_tag_RECURSION = define_datatype
  "reg_alloc_tag = Fixed (num) | Atemp | Stemp";;

(*
  Inputs are tagged with Fixed, Atemp , Stemp

  At all times, maintain invariant that adjacent nodes cannot be both Fixed
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
  [(* Info about the graph *)
   "adj_ls","(num list) list";
   (* adjacency list -- arr of lists *)
   "node_tag","reg_alloc_tag list";
   (* tags for each node -- arr *)
   "degrees","num list";
   (* degrees for each node -- arr *)
   "dim","num";
   (* num vertices in the graph *)
   (* worklists *)
   "simp_wl","num list";
   (* simp worklist -- list, non-move related deg < k *)
   "spill_wl","num list";
   (* spill worklist -- list, deg >= k *)
   "freeze_wl","num list";
   (* freeze worklist -- list, move related deg < k *)
   "avail_moves_wl","(num#num#num) list";
   (* active moves -- list, sorted by pri *)
   "unavail_moves_wl","(num#num#num) list";
   (* inactive moves -- list *)
   (* book keeping *)
   "coalesced","num list";
   (* keep track of coalesce target for each node -- arr *)
   "move_related","bool list";
   (* fast check if a node is still move related -- arr *)
   "stack","num list"];;
hol4_field_overload "stack" "ra_state_stack";;
hol4_field_overload "stack_fupd" "ra_state_stack_fupd";;

(* HOL4 makes the monadic accessors of ra_state with ML code
   (define_monad_access_funs of ml_monadBaseLib); these are
   the definitions that it makes *)
let get_adj_ls_def = new_definition
  `get_adj_ls = (\state. (M_success (ra_state_adj_ls state),state))`;;

let set_adj_ls_def = new_definition
  `set_adj_ls x =
     (\state. (M_success one,ra_state_adj_ls_fupd (K x) state))`;;

let get_node_tag_def = new_definition
  `get_node_tag = (\state. (M_success (ra_state_node_tag
  state),state))`;;

let set_node_tag_def = new_definition
  `set_node_tag x =
     (\state. (M_success one,ra_state_node_tag_fupd (K x) state))`;;

let get_degrees_def = new_definition
  `get_degrees = (\state. (M_success (ra_state_degrees state),state))`;;

let set_degrees_def = new_definition
  `set_degrees x =
     (\state. (M_success one,ra_state_degrees_fupd (K x) state))`;;

let get_dim_def = new_definition
  `get_dim = (\state. (M_success (ra_state_dim state),state))`;;

let set_dim_def = new_definition
  `set_dim x =
     (\state. (M_success one,ra_state_dim_fupd (K x) state))`;;

let get_simp_wl_def = new_definition
  `get_simp_wl = (\state. (M_success (ra_state_simp_wl state),state))`;;

let set_simp_wl_def = new_definition
  `set_simp_wl x =
     (\state. (M_success one,ra_state_simp_wl_fupd (K x) state))`;;

let get_spill_wl_def = new_definition
  `get_spill_wl = (\state. (M_success (ra_state_spill_wl
  state),state))`;;

let set_spill_wl_def = new_definition
  `set_spill_wl x =
     (\state. (M_success one,ra_state_spill_wl_fupd (K x) state))`;;

let get_freeze_wl_def = new_definition
  `get_freeze_wl = (\state. (M_success (ra_state_freeze_wl
  state),state))`;;

let set_freeze_wl_def = new_definition
  `set_freeze_wl x =
     (\state. (M_success one,ra_state_freeze_wl_fupd (K x) state))`;;

let get_avail_moves_wl_def = new_definition
  `get_avail_moves_wl = (\state. (M_success (ra_state_avail_moves_wl
  state),state))`;;

let set_avail_moves_wl_def = new_definition
  `set_avail_moves_wl x =
     (\state. (M_success one,ra_state_avail_moves_wl_fupd (K x)
       state))`;;

let get_unavail_moves_wl_def = new_definition
  `get_unavail_moves_wl = (\state. (M_success
  (ra_state_unavail_moves_wl state),state))`;;

let set_unavail_moves_wl_def = new_definition
  `set_unavail_moves_wl x =
     (\state. (M_success one,ra_state_unavail_moves_wl_fupd (K x)
       state))`;;

let get_coalesced_def = new_definition
  `get_coalesced = (\state. (M_success (ra_state_coalesced
  state),state))`;;

let set_coalesced_def = new_definition
  `set_coalesced x =
     (\state. (M_success one,ra_state_coalesced_fupd (K x) state))`;;

let get_move_related_def = new_definition
  `get_move_related = (\state. (M_success (ra_state_move_related
  state),state))`;;

let set_move_related_def = new_definition
  `set_move_related x =
     (\state. (M_success one,ra_state_move_related_fupd (K x)
       state))`;;

let get_stack_def = new_definition
  `reg_alloc_get_stack = (\state. (M_success (ra_state_stack
  state),state))`;;

let set_stack_def = new_definition
  `set_stack x =
     (\state. (M_success one,ra_state_stack_fupd (K x) state))`;;


(* HOL4 reg_allocScript.sml:85-86: ML code, not ported *)

(* HOL4 reg_allocScript.sml:88-89: ML code, not ported *)

(* HOL4 reg_allocScript.sml:91-92: ML code, not ported *)

(* HOL4 reg_allocScript.sml:94-95: ML code, not ported *)

(* HOL4 reg_allocScript.sml:97-98: ML code, not ported *)

(* Data type for the exceptions *)
let state_exn_INDUCT,state_exn_RECURSION = define_datatype
  "state_exn = reg_alloc_Fail (string) | reg_alloc_Subscript";;
hol4_overload "Fail" "reg_alloc_Fail";;
hol4_overload "Subscript" "reg_alloc_Subscript";;

(* Monadic functions to handle the exceptions *)
(* HOL4 makes the functions of the exception type state_exn with ML
   code (define_monad_exception_functions of
   ml_monadBaseLib); these are the definitions that it
   makes *)
let raise_Fail_def = new_definition
  `raise_Fail e1 =
     (\state. (M_failure (Fail e1),state))`;;

let raise_Subscript_def = new_definition
  `raise_Subscript =
     (\state. (M_failure reg_alloc_Subscript,state))`;;

let handle_Fail_def = new_definition
  `handle_Fail x f =
     (\state.
       match x state with (res,state) ->
         match res with M_success y -> (M_success y,state)
         | M_failure e ->
           (match e with Fail e1 -> f e1 state |
             reg_alloc_Subscript -> (M_failure
             reg_alloc_Subscript,state)))`;;

let handle_Subscript_def = new_definition
  `handle_Subscript x f =
     (\state.
       match x state with (res,state) ->
         match res with M_success y -> (M_success y,state)
         | M_failure e ->
           (match e with Fail e1 -> (M_failure (Fail e1),state) |
             reg_alloc_Subscript -> f state))`;;

hol4_overload "failwith" "raise_Fail";;

(* HOL4 reg_allocScript.sml:109-110: the ML values that the
   definitions below antiquote *)

(* Fixed-size array manipulators *)
(* HOL4 makes the manipulators of the fixed size arrays with
   ML code (define_MFarray_manip_funs of ml_monadBaseLib);
   these are the definitions that it makes *)
let adj_ls_length_def = new_definition
  `adj_ls_length = Marray_length (\state. ra_state_adj_ls state)`;;

let adj_ls_sub_def = new_definition
  `adj_ls_sub = Marray_sub (\state. ra_state_adj_ls state)
  reg_alloc_Subscript`;;

let update_adj_ls_def = new_definition
  `update_adj_ls =
     Marray_update (\state. ra_state_adj_ls state)
       (\x state. ra_state_adj_ls_fupd (K x) state)
         reg_alloc_Subscript`;;

let node_tag_length_def = new_definition
  `node_tag_length = Marray_length (\state. ra_state_node_tag state)`;;

let node_tag_sub_def = new_definition
  `node_tag_sub = Marray_sub (\state. ra_state_node_tag state)
  reg_alloc_Subscript`;;

let update_node_tag_def = new_definition
  `update_node_tag =
     Marray_update (\state. ra_state_node_tag state)
       (\x state. ra_state_node_tag_fupd (K x) state)
         reg_alloc_Subscript`;;

let degrees_length_def = new_definition
  `degrees_length = Marray_length (\state. ra_state_degrees state)`;;

let degrees_sub_def = new_definition
  `degrees_sub = Marray_sub (\state. ra_state_degrees state)
  reg_alloc_Subscript`;;

let update_degrees_def = new_definition
  `update_degrees =
     Marray_update (\state. ra_state_degrees state)
       (\x state. ra_state_degrees_fupd (K x) state)
         reg_alloc_Subscript`;;

let coalesced_length_def = new_definition
  `coalesced_length = Marray_length (\state. ra_state_coalesced
  state)`;;

let coalesced_sub_def = new_definition
  `coalesced_sub = Marray_sub (\state. ra_state_coalesced state)
  reg_alloc_Subscript`;;

let update_coalesced_def = new_definition
  `update_coalesced =
     Marray_update (\state. ra_state_coalesced state)
       (\x state. ra_state_coalesced_fupd (K x) state)
         reg_alloc_Subscript`;;

let move_related_length_def = new_definition
  `move_related_length = Marray_length (\state. ra_state_move_related
  state)`;;

let move_related_sub_def = new_definition
  `move_related_sub = Marray_sub (\state. ra_state_move_related
  state) reg_alloc_Subscript`;;

let update_move_related_def = new_definition
  `update_move_related =
     Marray_update (\state. ra_state_move_related state)
       (\x state. ra_state_move_related_fupd (K x) state)
         reg_alloc_Subscript`;;


(* HOL4 reg_allocScript.sml:117: ML code, not ported *)

(* HOL4 reg_allocScript.sml:119-123: ML code, not ported *)

(* HOL4 reg_allocScript.sml:125-126: a theorem that HOL4 states as
   the value of an ML expression: adj_ls_accessor *)
(* HOL4 reg_allocScript.sml:127-128: a theorem that HOL4 states as
   the value of an ML expression: node_tag_accessor *)
(* HOL4 reg_allocScript.sml:129-130: a theorem that HOL4 states as
   the value of an ML expression: degrees_accessor *)
(* HOL4 reg_allocScript.sml:131-132: a theorem that HOL4 states as
   the value of an ML expression: coalesced_accessor *)
(* HOL4 reg_allocScript.sml:133-134: a theorem that HOL4 states as
   the value of an ML expression: move_related_accessor *)

(* Helper functions for defining the allocator *)

(* Monadic list functions -- doesn't care about order *)
let st_ex_FOREACH_def,st_ex_FOREACH_ind = define_guess
  [`st_ex_FOREACH [] a = st_ex_return one`;
   `st_ex_FOREACH (x :: xs) a =
      st_ex_ignore_bind
        (a x) (
        st_ex_FOREACH xs a)`];;

(* HOL4 reg_allocScript.sml: the case constant that its Datatype
   makes for the tag of a register *)

let reg_alloc_tag_CASE =
  new_recursive_definition reg_alloc_tag_RECURSION
  `(reg_alloc_tag_CASE (Fixed n) ff af sf = ff n) /\
   (reg_alloc_tag_CASE Atemp ff af sf = af) /\
   (reg_alloc_tag_CASE Stemp ff af sf = sf)`;;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let st_ex_MAP_def,st_ex_MAP_ind = define_rec
  [`st_ex_MAP f [] = st_ex_return []`;
   `st_ex_MAP f (x :: xs) =
      st_ex_bind (f x) (\
        fx. st_ex_bind (st_ex_MAP f xs) (\
        fxs.
        st_ex_return (fx :: fxs)))`];;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let st_ex_PARTITION_def,st_ex_PARTITION_ind = define_rec
  [`st_ex_PARTITION P [] tt ff = st_ex_return (tt,ff)`;
   `st_ex_PARTITION P (x :: xs) tt ff =
      st_ex_bind (P x) (\
        Px.
        if Px then
          st_ex_PARTITION P xs (x :: tt) ff else
          st_ex_PARTITION P xs tt (x :: ff))`];;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let st_ex_FILTER_def,st_ex_FILTER_ind = define_rec
  [`st_ex_FILTER P [] acc = st_ex_return acc`;
   `st_ex_FILTER P (x :: xs) acc =
      st_ex_bind (P x) (\
        Px.
        if Px then
          st_ex_FILTER P xs (x :: acc) else
          st_ex_FILTER P xs acc)`];;

(* Keep adjacency lists sorted by > *)

(* Insert an undirect edge into the adj list representation *)
let sorted_insert_def,sorted_insert_ind = define_rec
  [`sorted_insert (x:num) acc [] = REVERSE (x :: acc)`;
   `sorted_insert (x:num) acc (y :: ys) =
        (if x = y then REVERSE acc ++ (y :: ys) else if x > y
          then REVERSE acc ++ (x :: y :: ys) else sorted_insert x
          (y :: acc) ys)`];;

let sorted_mem_def,sorted_mem_ind = define_rec
  [`sorted_mem (x:num) [] = F`;
   `sorted_mem (x:num) (y :: ys) =
        (if x = y then T else if x > y then F else sorted_mem x
          ys)`];;

let insert_edge_def = new_definition
  `insert_edge x y =
   st_ex_bind (adj_ls_sub x) (\
     adjx. st_ex_bind (adj_ls_sub y) (\
     adjy.
     st_ex_ignore_bind
       (update_adj_ls x (sorted_insert y [] adjx)) (
       update_adj_ls y (sorted_insert x [] adjy))))`;;

(* insert a list of edges all adjacent to one node *)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let list_insert_edge_def,list_insert_edge_ind = define_wf
  `MEASURE (\(x0,x1). list_size (\n. n) x1)`
  [`list_insert_edge x [] = st_ex_return one`;
   `list_insert_edge x (y :: ys) =
        st_ex_ignore_bind
          (insert_edge x y) (
          list_insert_edge x ys)`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let clique_insert_edge_def,clique_insert_edge_ind = define_wf
  `MEASURE (\x0. list_size (\n. n) x0)`
  [`clique_insert_edge [] = st_ex_return one`;
   `clique_insert_edge (x :: xs) =
      st_ex_ignore_bind
        (list_insert_edge x xs) (
        clique_insert_edge xs)`];;

(* assuming vertices in cli already forms a clique,
   extend it with new members
*)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let extend_clique_def,extend_clique_ind = define_wf
  `MEASURE (\(x0,x1). list_size (\n. n) x0)`
  [`extend_clique [] cli = st_ex_return cli`;
   `extend_clique (x :: xs) cli =
        (if MEM x cli then
          extend_clique xs cli else
        st_ex_ignore_bind
          (list_insert_edge x cli) (
          extend_clique xs (x :: cli)))`];;

(* The allocator heuristics, designed to minimize proof at the
   cost of some extra computation *)

(* (Safely) decrement the degree of all vertices adjacent to n by 1 *)
let dec_deg_def = new_definition
  `dec_deg n =
   st_ex_bind (degrees_sub n) (\
     cd.
     update_degrees n (cd - 1))`;;

let dec_degree_def = new_definition
  `dec_degree n =
   st_ex_bind get_dim (\
     d.
     // TODO: check unnecessary
     if n < d then
     st_ex_bind (adj_ls_sub n) (\
       adjs.
       st_ex_FOREACH adjs dec_deg) else
       st_ex_return one)`;;

let add_simp_wl_def = new_definition
  `add_simp_wl ls =
   st_ex_bind get_simp_wl (\
     swl.
     set_simp_wl (ls ++ swl))`;;

let add_spill_wl_def = new_definition
  `add_spill_wl ls =
   st_ex_bind get_spill_wl (\
     swl.
     set_spill_wl (ls ++ swl))`;;

let add_freeze_wl_def = new_definition
  `add_freeze_wl ls =
   st_ex_bind get_freeze_wl (\
     fwl.
     set_freeze_wl (ls ++ fwl))`;;

(* push x onto the stack, deleting it from "existence" *)
let push_stack_def = new_definition
  `push_stack x =
   st_ex_bind reg_alloc_get_stack (\
     swl. st_ex_ignore_bind
     (update_degrees x 0) (st_ex_ignore_bind
     (update_move_related x F) (
     set_stack (x :: swl))))`;;

let add_unavail_moves_wl_def = new_definition
  `add_unavail_moves_wl ls =
   st_ex_bind get_unavail_moves_wl (\
     swl.
     set_unavail_moves_wl (ls ++ swl))`;;

(* unspill:
   Move any vertices in the spill list that has
   degree < k into the simplify or freeze worklist
   Revive all neighboring moves of these nodes
*)
let is_not_coalesced_def = new_definition
  `is_not_coalesced d =
   st_ex_bind (coalesced_sub d) (\
     dt.
     st_ex_return (d = dt))`;;

let split_degree_def = new_definition
  `split_degree d k v =
   (if v < d then
   // TODO: unnecessary
   st_ex_bind (degrees_sub v) (\
     vd. st_ex_bind (is_not_coalesced v) (\
     b.
     st_ex_return (vd < k /\ b))) else
     st_ex_return T)`;;

(* sort moves by priority *)
let sort_moves_def = new_definition
  `reg_alloc_sort_moves ls =
     sort (\((p:num),x) (p',x'). p > p') ls`;;
hol4_overload "sort_moves" "reg_alloc_sort_moves";;

(* merge two sorted lists *)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let smerge_def,smerge_ind = define_wf
  `MEASURE (\(x0,x1).      list_size (pair_size (\n. n) (\x. 0)) x0 +
     list_size (pair_size (\n. n) (\x. 0)) x1)`
  [`smerge xs ys =
        match (xs,ys) with
          ([],ys) -> ys
        | (xs,[]) -> xs
        | ((((p:num),m) :: xs),((p',m') :: ys)) ->
       (if p >= p' then
         (p,m) :: smerge xs ((p',m') :: ys) else
         (p',m') :: smerge ((p,m) :: xs) ys)`];;

(*
  revive the unavailable moves that touch each neighbor
*)
let revive_moves_def = new_definition
  `revive_moves vs =
   st_ex_bind (st_ex_MAP adj_ls_sub vs) (\
     nbs. st_ex_bind get_unavail_moves_wl (\
     uam. st_ex_bind get_avail_moves_wl (\
     am.
     let (rev,unavail) = PARTITION
       (\(_1,(x,y)). EXISTS (sorted_mem x) nbs \/ EXISTS (sorted_mem
         y) nbs) uam in
     let sorted = smerge (reg_alloc_sort_moves rev) am in
     st_ex_ignore_bind
       (set_avail_moves_wl sorted) (
       set_unavail_moves_wl unavail))))`;;

let unspill_def = new_definition
  `unspill (k:num) =
   st_ex_bind get_dim (\
     d. st_ex_bind get_spill_wl (\
     swl. st_ex_bind (st_ex_PARTITION (split_degree d k) swl [] [])
       (\
     (ltk,gtk). st_ex_ignore_bind
     // The nodes in ltk have turned into low degree nodes
     (revive_moves ltk) (st_ex_bind (st_ex_PARTITION
       (move_related_sub) ltk [] []) (\
     (ltkfreeze,ltksimp). st_ex_ignore_bind
     (set_spill_wl gtk) (st_ex_ignore_bind
     (add_simp_wl ltksimp) (
     add_freeze_wl ltkfreeze)))))))`;;

(* simplify:
  Directly simplifies the entire list
  instead of doing it 1-by-1
  T = successful simplification
  F = no simplification
*)
let do_simplify_def = new_definition
  `do_simplify k =
   st_ex_bind get_simp_wl (\
     simps.
     if NULL simps then
       st_ex_return F else
     st_ex_ignore_bind
       (st_ex_FOREACH simps dec_degree) (st_ex_ignore_bind
       (st_ex_FOREACH simps push_stack) (st_ex_ignore_bind
       (set_simp_wl []) (st_ex_ignore_bind
       (unspill k) (
       st_ex_return T)))))`;;

(* increment degree of n by d *)
let inc_deg_def = new_definition
  `inc_deg n d =
   st_ex_bind (degrees_sub n) (\
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
let is_Fixed_def = new_definition
  `is_Fixed x =
   st_ex_bind (node_tag_sub x) (\
     xt.
     st_ex_return (match xt with Fixed n -> T | _2 -> F))`;;

let do_coalesce_real_def = new_definition
  `do_coalesce_real x y case1 case2 =
   st_ex_ignore_bind
     // mark y as coalesced to x
     (update_coalesced y x) (st_ex_bind (is_Fixed x) (\
     // increment degree of x by new vertices
     bx. st_ex_ignore_bind
     (if bx then st_ex_return one else inc_deg x (LENGTH case2))
       (st_ex_ignore_bind
     // add corresponding edges
     (list_insert_edge x case2) (st_ex_ignore_bind
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
let is_Atemp_def = new_definition
  `is_Atemp d =
   st_ex_bind (node_tag_sub d) (\
     dt.
     st_ex_return (dt = Atemp))`;;

let is_Fixed_k_def = new_definition
  `is_Fixed_k k x =
   st_ex_bind (node_tag_sub x) (\
     xt.
     st_ex_return (match xt with Fixed n -> n < k | _3 -> F))`;;

let considered_var_def = new_definition
  `considered_var k x =
   st_ex_bind (is_Atemp x) (\
     bx. st_ex_bind (is_Fixed_k k x) (\
     fx.
     st_ex_return (bx \/ fx)))`;;

(* Fixed vars are treated as having infinite degree *)
let deg_or_inf_def = new_definition
  `deg_or_inf k x =
   st_ex_bind (is_Fixed_k k x) (\
     bx.
     if bx then st_ex_return k else degrees_sub x)`;;

let bg_ok_def = new_definition
  `bg_ok k x y =
   st_ex_bind (adj_ls_sub x) (\
     adjx. st_ex_bind (adj_ls_sub y) (\
     adjy.
     // see do_coalesce_real for the cases
     let (case1,case2) = PARTITION (\v. sorted_mem v adjx) adjy in
     st_ex_bind (st_ex_FILTER (considered_var k) case1 []) (\
       // the "true" case1 and 2s
       case1. st_ex_bind (st_ex_FILTER (considered_var k) case2 [])
         (\
       case2. st_ex_bind (st_ex_MAP (deg_or_inf k) case2) (\
       // Check the George criterion
       case2degs.
       let c2len = LENGTH (FILTER (\x. x >= k) case2degs) in
       if c2len = 0 then st_ex_return (SOME (case1,case2)) else
       // george criterion
       let case3 = FILTER (\v. ~(sorted_mem v adjy)) adjx in
       st_ex_bind (st_ex_FILTER (considered_var k) case3 []) (\
         case3. st_ex_bind (st_ex_MAP (deg_or_inf (k + 1)) case1) (\
         case1degs. st_ex_bind (st_ex_MAP (deg_or_inf k) case3) (\
         // k+1 is infinity here..
         case3degs. st_ex_bind (st_ex_return (LENGTH (FILTER (\x. x -
           1 >= k) case1degs))) (\
         c1len. st_ex_bind (st_ex_return (LENGTH (FILTER (\x. x >= k)
           case3degs))) (\
         c3len.
         if c1len + c2len + c3len < k then
           st_ex_return (SOME (case1,case2)) else
           st_ex_return NONE))))))))))`;;

(*
  Consistency check for moves
  Any moves failing this check can be directly discarded
  1) x ≠ y
  2) x,y must not already clash

  3) x,y either fixed or atemps and not both fixed
*)

let consistency_ok_def = new_definition
  `consistency_ok x y =
   (if x = y then
     st_ex_return F else
   // check 1
   st_ex_bind (adj_ls_sub y) (\
     adjy.
     // check 2
     if sorted_mem x adjy then st_ex_return F else
     st_ex_bind (is_Fixed x) (\
       bx. st_ex_bind (is_Fixed y) (\
       by. st_ex_bind (move_related_sub x) (\
       movrelx. st_ex_bind (move_related_sub y) (\
       movrely.
       st_ex_return ((bx \/ movrelx) /\ (by \/ movrely) /\ ~(bx /\
         by))))))))`;;

(*
  find the ancestor
  and collapse along the way

*)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let coalesce_parent_def,coalesce_parent_ind = define_wf
  `MEASURE (\x0. (\n. n) x0)`
  [`coalesce_parent x =
   st_ex_bind (coalesced_sub x) (\
     xt. st_ex_bind (is_Fixed xt) (\
     bx.
     // Special case where x is coalesced to a fixed color already
     if bx then
       st_ex_return xt else
       if x <= xt then
         st_ex_return x else
       st_ex_bind (coalesce_parent xt) (\
         anc. st_ex_ignore_bind
         (update_coalesced x anc) (
         st_ex_return anc))))`];;

let canonize_move_def = new_definition
  `canonize_move x y =
   st_ex_bind (is_Fixed x) (\
     bx. st_ex_bind (is_Fixed y) (\
     by.
     if by then st_ex_return (y,x) else if bx then st_ex_return (x,y)
       else
       if x < y then st_ex_return (x,y) else st_ex_return (y,x)))`;;

(*
  Picks apart the available moves worklist
  1) If we find any inconsistent ones -> throw them away
  not necessary? -- 2) canonize the move to put fixed register in front
  3) returns the first bg_ok move that is also consistent
*)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let st_ex_FIRST_def,st_ex_FIRST_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3).      list_size (pair_size (\x. 0)
  (pair_size (\n. n) (\n. n))) x2)`
  [`st_ex_FIRST P Q [] unavail = st_ex_return (NONE,unavail)`;
   `st_ex_FIRST P Q (m :: ms) unavail =
        (let (p,(x,y)) = m in
        st_ex_bind (coalesce_parent x) (\
          x. st_ex_bind (coalesce_parent y) (\
          y. st_ex_bind (P x y) (\
          b1.
          if ~b1 then
            st_ex_FIRST P Q ms unavail else
          st_ex_bind (canonize_move x y) (\
            (x,y). st_ex_bind (Q x y) (\
            optb2.
            match optb2 with
              NONE -> st_ex_FIRST P Q ms ((p,(x,y)) :: unavail) |
                SOME pr ->
              st_ex_return (SOME ((x,y),pr,ms),unavail)))))))`];;

let respill_def = new_definition
  `respill k x =
   st_ex_bind (degrees_sub x) (\
     xd.
     if xd < k then st_ex_return one else
     st_ex_bind get_freeze_wl (\
       freeze.
       if MEM x freeze then
       st_ex_ignore_bind
         (add_spill_wl [x]) (
         set_freeze_wl (FILTER (\y. ~(y = x)) freeze)) else
           st_ex_return one))`;;

let do_coalesce_def = new_definition
  `do_coalesce k =
   st_ex_bind get_avail_moves_wl (\
     am. st_ex_bind (st_ex_FIRST consistency_ok (bg_ok k) am []) (\
     (ores,unavail). st_ex_ignore_bind
     (add_unavail_moves_wl unavail) (
     match ores with
       NONE ->
         st_ex_ignore_bind
           (set_avail_moves_wl []) (
           st_ex_return F) | SOME ((x,y),(case1,case2),ms) ->
     st_ex_ignore_bind
       (set_avail_moves_wl ms) (st_ex_ignore_bind
       // coalesce y into x
       (do_coalesce_real x y case1 case2) (st_ex_ignore_bind
       (unspill k) (st_ex_ignore_bind
       (respill k x) (
       st_ex_return T)))))))`;;

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

let reset_move_related_def = new_definition
  `reset_move_related ls =
   st_ex_bind get_dim (\
     d. st_ex_ignore_bind
     // zero out move_related
     (st_ex_FOREACH (COUNT_LIST d) (\x. update_move_related x F)) (
     // reset to correct values
     st_ex_FOREACH ls (\(_4,(x,y)).
         st_ex_bind (is_Fixed x) (\
           // make sure fixed are kept as NOT move_related
           bx. st_ex_bind (is_Fixed y) (\
           by. st_ex_ignore_bind
           (update_move_related x (~bx)) (
           update_move_related y (~by)))))))`;;

let do_prefreeze_def = new_definition
  `do_prefreeze k =
   st_ex_bind get_freeze_wl (\
     fwl_pre. st_ex_bind (st_ex_FILTER is_not_coalesced fwl_pre [])
       (\
     fwl. st_ex_bind get_spill_wl (\
     swl_pre. st_ex_bind (st_ex_FILTER is_not_coalesced swl_pre [])
       (\
     swl. st_ex_ignore_bind
     (set_spill_wl swl) (st_ex_bind get_unavail_moves_wl (\
     uam_pre. st_ex_bind (st_ex_FILTER (\(_5,(x,y)). consistency_ok x
       y) uam_pre []) (\
     uam. st_ex_ignore_bind
     (reset_move_related uam) (st_ex_bind (set_unavail_moves_wl uam)
       (\
     uam. st_ex_bind (st_ex_PARTITION (move_related_sub) fwl [] [])
       (\
     (ltkfreeze,ltksimp). st_ex_ignore_bind
     (add_simp_wl ltksimp) (st_ex_ignore_bind
     (set_freeze_wl ltkfreeze) (
     do_simplify k))))))))))))`;;

(* if prefreeze failed, then just freeze *)

let do_freeze_def = new_definition
  `do_freeze k =
   st_ex_bind get_freeze_wl (\
     freeze.
     match freeze with
       [] -> st_ex_return F | x :: xs ->
       st_ex_ignore_bind
         (dec_degree x) (st_ex_ignore_bind
         (push_stack x) (st_ex_ignore_bind
         (set_freeze_wl xs) (st_ex_ignore_bind
         (unspill k) (
         st_ex_return T)))))`;;

(* spill:
  If given a spill cost,
    picks the cheapest node in the spill worklist,
    based on spill cost / degree
  Otherwise,
    picks highest degree node
*)
let safe_div_def = new_definition
  `safe_div x v = (if v = 0 then 0 else x DIV v)`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let st_ex_list_MIN_cost_def,st_ex_list_MIN_cost_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3,x4,x5). list_size (\n. n) x1)`
  [`st_ex_list_MIN_cost scost [] d k v acc = st_ex_return (k,acc)`;
   `st_ex_list_MIN_cost scost (x :: xs) d k v acc =
      (if x < d then
        st_ex_bind (degrees_sub x) (\
          xv. st_ex_bind (st_ex_return (safe_div (lookup_any x scost
            0) xv)) (\
          cost.
          if v > cost then
            st_ex_list_MIN_cost scost xs d x cost (k :: acc) else
            st_ex_list_MIN_cost scost xs d k v (x :: acc))) else
        st_ex_list_MIN_cost scost xs d k v acc)`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let st_ex_list_MAX_deg_def,st_ex_list_MAX_deg_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3,x4). list_size (\n. n) x0)`
  [`st_ex_list_MAX_deg [] d k v acc = st_ex_return (k,acc)`;
   `st_ex_list_MAX_deg (x :: xs) d k v acc =
      (if x < d then
        st_ex_bind (degrees_sub x) (\
          xv.
          if v < xv then
            st_ex_list_MAX_deg xs d x xv (k :: acc) else
            st_ex_list_MAX_deg xs d k v (x :: acc)) else
      st_ex_list_MAX_deg xs d k v acc)`];;

let do_spill_def = new_definition
  `do_spill scostopt k =
   st_ex_bind get_spill_wl (\
     spills. st_ex_bind get_dim (\
     d.
     match spills with
       [] -> st_ex_return F | (x :: xs) ->
       st_ex_bind (degrees_sub x) (\
         xv. st_ex_bind (match scostopt with
               NONE -> st_ex_list_MAX_deg xs d x xv [] | SOME scost
                 -> st_ex_list_MIN_cost scost xs d x (safe_div
                 (lookup_any x scost 0) xv) []) (\
         (y,ys). st_ex_ignore_bind
         (dec_degree y) (st_ex_ignore_bind
         (push_stack y) (st_ex_ignore_bind
         (set_spill_wl ys) (st_ex_ignore_bind
         (unspill k) (
         st_ex_return T))))))))`;;

let do_step_def = new_definition
  `do_step scost k =
   st_ex_bind (do_simplify k) (\
     b.
     if b then st_ex_return b else
     st_ex_bind (do_coalesce k) (\
       b.
       if b then st_ex_return b else
       st_ex_bind (do_prefreeze k) (\
         b.
         if b then st_ex_return b else
         st_ex_bind (do_freeze k) (\
           b.
           if b then
             st_ex_return b else
             st_ex_bind (do_spill scost k) (\
               b.
               st_ex_return b)))))`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let rpt_do_step_def,rpt_do_step_ind = define_wf
  `MEASURE (\(x0,x1,x2). (\n. n) x2)`
  [`rpt_do_step scost k 0 = st_ex_return one`;
   `rpt_do_step scost k (SUC c) =
      st_ex_bind (do_step scost k) (\
        b.
        if b then rpt_do_step scost k c else st_ex_return one)`];;

(*
  The coloring functions
*)

(* Removing adjacent colours from ks *)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let remove_colours_def,remove_colours_ind = define_wf
  `MEASURE (\(x0,x1). list_size (\n. n) x0)`
  [`remove_colours x1 ks =
        match (x1,ks) with
          // No more available colours
        ((ls:num list),[]) -> st_ex_return []
        // Some available colour after checking
        | ([],(ks:num list)) -> st_ex_return ks
        // Do the check for vertex x
        | ((x :: xs),ks) ->
       st_ex_bind (node_tag_sub x) (\
         cx. st_ex_bind
         (match cx with
           Fixed c ->
             remove_colours xs (FILTER (\x. ~(x = c)) ks) | _6 ->
             remove_colours xs ks) (\
         r.
         st_ex_return r))`];;

(* First colouring -- turns all Atemps into Fixeds or Stemps drawing from colors in ks *)
(* Assign a tag to an Atemp node, skipping if it is not actually an Atemp *)

let assign_Atemp_tag_def = new_definition
  `assign_Atemp_tag ks prefs n =
   st_ex_bind (node_tag_sub n) (\
     ntag.
     match ntag with
       Atemp ->
       st_ex_bind (adj_ls_sub n) (\
         adjs. st_ex_bind (remove_colours adjs ks) (\
         ks.
         match ks with
           [] -> update_node_tag n Stemp | (x :: _7) ->
           st_ex_bind (prefs n ks) (\
             c.
             // Apply monadic preference oracle
             match c with
               NONE ->
               update_node_tag n (Fixed x) | SOME y ->
               update_node_tag n (Fixed y)))) | _8 -> st_ex_return
                 one)`;;

(* The first allocation step *)
(* k = num registers, ls = heuristic list, prefs = coloring preference *)
let assign_Atemps_def = new_definition
  `assign_Atemps k ls prefs =
   st_ex_bind get_dim (\
     d. st_ex_bind (st_ex_return (FILTER (\n. n < d) ls)) (\
     ls. st_ex_bind (st_ex_return (GENLIST (\x. x) k)) (\
     ks. st_ex_bind (st_ex_return (GENLIST (\x. x) d)) (\
     cs. st_ex_ignore_bind
     // actually, only need to do those not already in ls
     // Assign all the ones that the ls tells us to
     (st_ex_FOREACH ls (assign_Atemp_tag ks prefs)) (
     // actually, assign_Atemp_tag already filters for Atemps, so just pass it all the nodes
     st_ex_FOREACH cs (assign_Atemp_tag ks prefs))))))`;;

(* Default makes it easier to translate, doesn't matter for our purposes what
   the default is *)
let tag_col_def = new_definition
  `tag_col x1 =
        match x1 with
          Fixed n -> n
        | _9 -> 0`;;

(* Find the first available in k,k+1,...
   assuming input is sorted
*)
let unbound_colour_def,unbound_colour_ind = define_rec
  [`unbound_colour col [] = col`;
   `unbound_colour col ((x:num) :: xs) =
        (if col < x then
          col else if x = col then
          unbound_colour (col + 1) xs else
          unbound_colour col xs)`];;

(* Second colouring -- turns all Stemps into Fixed ≥ k *)
let assign_Stemp_tag_def = new_definition
  `assign_Stemp_tag k prefs n =
   st_ex_bind (node_tag_sub n) (\
     ntag.
     match ntag with
       Stemp ->
       st_ex_bind (adj_ls_sub n) (\
         adjs. st_ex_bind (st_ex_MAP node_tag_sub adjs) (\
         tags.
         let bads = sort (\x y. x <= y) (MAP tag_col tags) in
         st_ex_bind (prefs n bads) (\
           c.
           match c with
             NONE ->
               update_node_tag n (Fixed (unbound_colour k bads)) |
                 SOME y ->
               update_node_tag n (Fixed y)))) | _10 ->
                 st_ex_return one)`;;


(* The second allocation step *)
let assign_Stemps_def = new_definition
  `assign_Stemps k prefs =
   st_ex_bind get_dim (\
     d. st_ex_bind (st_ex_return (GENLIST (\x. x) d)) (\
     cs.
     st_ex_FOREACH cs (assign_Stemp_tag k prefs)))`;;

(* Monadic biased selection oracle, finds the first matching color *)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let first_match_col_def,first_match_col_ind = define_wf
  `MEASURE (\(x0,x1). list_size (\n. n) x1)`
  [`first_match_col ks [] = st_ex_return NONE`;
   `first_match_col ks (x :: xs) =
        st_ex_bind (node_tag_sub x) (\
          c.
          match c with
            Fixed m ->
              (if MEM m ks then st_ex_return (SOME m) else
                first_match_col ks xs) | _12 -> first_match_col ks
                xs)`];;

(* Clash tree representation of a program -- this is designed as an interface:
  wordLang program -> clash tree -> reg alloc

  It only represents wordLang programs, which do not have back-edges
  The allocator itself is more general, and supports arbitrary graphs
  It serves two purposes:
  1) slightly more efficient checking of coloring oracles
  2) it gets compiled in to the clash graphs for the allocator

  TODO: probably want to move the clash tree representation up and separate it
  from the allocator
*)

let clash_tree_INDUCT,clash_tree_RECURSION = define_datatype
  "clash_tree = reg_alloc_Delta (num list) (num list) \
   // (Writes list, Reads list)\n\
   | reg_alloc_Set (1 spt) \
   // Fixed set\n\
   | reg_alloc_Branch ((1 spt) option) (clash_tree) (clash_tree) | \
   reg_alloc_Seq (clash_tree) (clash_tree) \
   // Binary branch, with an optional liveset at the head";;
hol4_overload "Delta" "reg_alloc_Delta";;
hol4_overload "Set" "reg_alloc_Set";;
hol4_overload "Branch" "reg_alloc_Branch";;
hol4_overload "Seq" "reg_alloc_Seq";;

(* --- clash_tree oracle checks --- *)
let numset_list_delete_def,numset_list_delete_ind = define_rec
  [`numset_list_delete [] (t:'a spt) = t`;
   `numset_list_delete (x :: xs) (t:'a spt) = numset_list_delete xs
  (sptree_delete x t)`];;

(*Check that a numset is injective over the clash sets in an interpreted tree*)
let check_col_def = new_definition
  `check_col f t =
     (let names = MAP (f o FST) (toAList t) in
     if ALL_DISTINCT names then
       SOME (t,fromAList (MAP (\x. (x,one)) names)) else NONE)`;;

let check_partial_col_def,check_partial_col_ind = define_rec
  [`check_partial_col f [] t ft = SOME (t,ft)`;
   `check_partial_col f (x :: xs) t ft =
        (match sptree_lookup x t with
          SOME one -> check_partial_col f xs t ft | NONE ->
        (match sptree_lookup (f x) ft with
          NONE -> check_partial_col f xs (sptree_insert x one
            t) (sptree_insert (f x) one ft) | SOME one -> NONE))`];;

(* The checking function, used by oracle, and also used as part of the correctness proof *)
(* live = the liveset, flive = the liveset with f applied over it*)
let check_clash_tree_def,check_clash_tree_ind = define_rec
  [`check_clash_tree f (reg_alloc_Delta w r) live flive =
        (match check_partial_col f w live flive with
          NONE -> NONE | SOME _14 ->
        (let del_w = (numset_list_delete w live) in
        let fdel_w = (numset_list_delete (MAP f w) flive) in
        check_partial_col f r del_w fdel_w))`;
   `check_clash_tree f (reg_alloc_Set t:clash_tree) live flive =
  check_col f t`;
   `check_clash_tree f (reg_alloc_Branch topt t1 t2:clash_tree) live
  flive =
        (match check_clash_tree f t1 live flive with
          NONE -> NONE | SOME (t1_out,ft1_out) ->
        (match check_clash_tree f t2 live flive with
          NONE -> NONE | SOME (t2_out,ft2_out) ->
        (match topt with
          NONE ->
            // This check can be done in either direction
            check_partial_col f (MAP FST (toAList (difference
              t2_out t1_out))) t1_out ft1_out | SOME t -> check_col f
              t)))`;
   `check_clash_tree f (reg_alloc_Seq t1 t2:clash_tree) live flive =
        (match check_clash_tree f t2 live flive with
          NONE -> NONE | SOME (t2_out,ft2_out) ->
          check_clash_tree f t1 t2_out ft2_out)`];;

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
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let list_remap_def,list_remap_ind = define_wf
  `MEASURE (\(x0,x1). list_size (\n. n) x0)`
  [`list_remap [] (ta,fa,nv) = (ta,fa,nv)`;
   `list_remap (x :: xs) (ta,fa,nv) =
        (match sptree_lookup x ta with
          SOME v -> list_remap xs (ta,fa,nv) | NONE ->
          list_remap xs (sptree_insert x nv ta,sptree_insert nv
            x fa,nv + 1))`];;

let mk_bij_aux_def,mk_bij_aux_ind = define_rec
  [`mk_bij_aux (reg_alloc_Delta writes reads) tfn =
        list_remap writes (list_remap reads tfn)`;
   `mk_bij_aux (reg_alloc_Set t:clash_tree) tfn =
        list_remap (MAP FST (toAList t)) tfn`;
   `mk_bij_aux (reg_alloc_Branch topt t1 t2:clash_tree) tfn =
         (let tfn' = mk_bij_aux t2 (mk_bij_aux t1 tfn) in
         match topt with
           NONE -> tfn' | SOME ts -> list_remap (MAP FST (toAList
             ts)) tfn')`;
   `mk_bij_aux (reg_alloc_Seq t1 t2:clash_tree) tfn =
        mk_bij_aux t1 (mk_bij_aux t2 tfn)`];;

let mk_bij_def = new_definition
  `mk_bij t =
     (let (ta,fa,n) = mk_bij_aux t (LN,LN,0) in
     (ta,fa,n))`;;
    (* Hide the sptree impl
    ((λi. lookup_any i ta 0),(λi. lookup_any i fa 0), n)` *)

(*Distinguish 3 kinds of variables:
  Evens are physical registers
  4n+1 are allocatable registers
  4n+3 are stack registers*)

let is_stack_var_def = new_definition
  `is_stack_var (n:num) = (n MOD 4 = 3)`;;
let is_phy_var_def = new_definition
  `is_phy_var (n:num) = (n MOD 2 = 0)`;;
let is_alloc_var_def = new_definition
  `is_alloc_var (n:num) = (n MOD 4 = 1)`;;

let convention_partitions = prove
 (`!n. (is_stack_var n <=> (~(is_phy_var n)) /\ ~(is_alloc_var n)) /\
     (is_phy_var n <=> (~(is_stack_var n)) /\ ~(is_alloc_var n)) /\
     (is_alloc_var n <=> (~(is_phy_var n)) /\ ~(is_stack_var n))`,
  CHEAT_TAC);;

(* Set the tags according to wordLang conventions *)
let mk_tags_def = new_definition
  `mk_tags n fs fa =
   st_ex_bind (st_ex_return (GENLIST (\x. x) n)) (\
     inds.
     st_ex_FOREACH inds
     (\i.
       let v = fa i in
       let remainder = v MOD 4 in
       if remainder = 1 then
         (match sptree_lookup v fs with
           NONE -> update_node_tag i Atemp | SOME one ->
             update_node_tag i Stemp) else if remainder = 3 then
         update_node_tag i Stemp else
         update_node_tag i (Fixed (v DIV 2))))`;;

(* Initializes the clash_graph using a clash_tree and a remapping bijection *)
let _ = size_thms "clash_tree";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let mk_graph_def,mk_graph_ind = define_wf
  `MEASURE (\(x0,x1,x2). clash_tree_size x1)`
  [`mk_graph ta (reg_alloc_Delta w r) liveout =
        st_ex_bind (st_ex_return (MAP ta w)) (\
          wta. st_ex_bind (st_ex_return (MAP ta r)) (\
          rta. st_ex_bind (extend_clique wta liveout) (\
          live. st_ex_bind (st_ex_return (FILTER (\x. ~(MEM x wta))
            live)) (\
          live. st_ex_bind (extend_clique rta live) (\
          livein.
          st_ex_return livein)))))`;
   `mk_graph ta (reg_alloc_Set t:clash_tree) liveout =
        st_ex_bind (st_ex_return (MAP ta (MAP FST (toAList t)))) (\
          live. st_ex_ignore_bind
          (clique_insert_edge live) (
          st_ex_return live))`;
   `mk_graph ta (reg_alloc_Branch topt t1 t2:clash_tree) liveout =
        st_ex_bind (mk_graph ta t1 liveout) (\
          t1_live. st_ex_bind (mk_graph ta t2 liveout) (\
          t2_live.
          (match topt with
            NONE ->
            st_ex_bind (extend_clique t1_live t2_live) (\
              livein.
              st_ex_return livein) | SOME t ->
            st_ex_bind (st_ex_return (MAP ta (MAP FST (toAList t))))
              (\
              clashes. st_ex_ignore_bind
              (clique_insert_edge clashes) (
              st_ex_return clashes)))))`;
   `mk_graph ta (reg_alloc_Seq t1 t2:clash_tree) liveout =
        st_ex_bind (mk_graph ta t2 liveout) (\
          live.
          mk_graph ta t1 live)`];;

let sp_default_def = new_definition
  `sp_default t i =
   (match sptree_lookup i t with NONE -> (if is_phy_var i then i
     DIV 2 else 0) | SOME x -> x)`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let extend_graph_def,extend_graph_ind = define_wf
  `MEASURE (\(x0,x1). list_size (pair_size (\x. 0) (\x. 0)) x1)`
  [`extend_graph ta [] = st_ex_return one`;
   `extend_graph ta ((x,y) :: xs) =
      st_ex_ignore_bind
        (insert_edge (ta x) (ta y)) (
        extend_graph ta xs)`];;

(* sets up the register allocator init state with the clash_tree input
  TODO: should the sptrees be hidden right away?
  It might be easier to transfer an sptree directly for the oracle register
  allocator

  ct = clash_tree
  forced = forced edges -- will need new proof that all forced edges are in the tree
*)
let init_ra_state_def = new_definition
  `init_ra_state ct forced fs (ta,fa,n) =
   st_ex_ignore_bind
     (mk_graph (sp_default ta) ct []) (st_ex_ignore_bind
     // Put in the usual edges
     (extend_graph (sp_default ta) forced) (
     mk_tags n fs (sp_default fa)))`;;

(* work around translator bug *)
let do_upd_coalesce_def = new_definition
  `do_upd_coalesce i =
   update_coalesced i (0 + i)`;;

(* Initializer for the first allocation step *)
let init_alloc1_heu_def = new_definition
  `init_alloc1_heu moves d k =
   st_ex_bind (st_ex_return (COUNT_LIST d)) (\
     ds. st_ex_bind (st_ex_FILTER is_Atemp ds []) (\
     // make sure move_related is correct
     allocs. st_ex_ignore_bind
     // only need to allocate Atemps
     (st_ex_FOREACH ds
       (
        // Set the degree for each node
        \i.
       st_ex_bind (adj_ls_sub i) (\
         adjls. st_ex_bind (st_ex_FILTER (\v. considered_var k v)
           adjls []) (\
         fills.
         update_degrees i (LENGTH fills))))) (st_ex_ignore_bind
     (st_ex_FOREACH ds do_upd_coalesce) (st_ex_ignore_bind
     (set_avail_moves_wl (reg_alloc_sort_moves moves))
       (st_ex_ignore_bind
     (reset_move_related moves) (st_ex_bind (st_ex_PARTITION
       (split_degree d k) allocs [] []) (\
     (ltk,gtk). st_ex_bind (st_ex_PARTITION (move_related_sub) ltk []
       []) (\
     (ltkfreeze,ltksimp). st_ex_ignore_bind
     (set_spill_wl gtk) (st_ex_ignore_bind
     (set_simp_wl ltksimp) (st_ex_ignore_bind
     (set_freeze_wl ltkfreeze) (
     st_ex_return (LENGTH allocs))))))))))))`;;

let do_alloc1_def = new_definition
  `do_alloc1 moves scost k =
   st_ex_bind get_dim (\
     d. st_ex_bind (init_alloc1_heu moves d k) (\
     l. st_ex_ignore_bind
     (rpt_do_step scost k l) (st_ex_bind reg_alloc_get_stack (\
     st.
     st_ex_return st))))`;;

let extract_tag_def = new_definition
  `(extract_tag t = (match t with
     Fixed m -> m | _15 -> 0))`;;
(* never happens*)

(* return the final coloring as an sptree *)
let extract_color_def = new_definition
  `extract_color ta =
   st_ex_bind (st_ex_return (toAList ta)) (\
     taa. st_ex_bind (st_ex_MAP (\(k,v).
       st_ex_bind (node_tag_sub v) (\
         t.
         st_ex_return (k,extract_tag t))) taa) (\
     itags.
     // can make the sptree directly
     st_ex_return (fromAList itags)))`;;

let pri_move_insert_def = new_definition
  `pri_move_insert p x y acc =
   (match sptree_lookup x acc with
     NONE ->
       sptree_insert x [(p,y)] acc | SOME ls ->
       sptree_insert x ((p,y) :: ls) acc)`;;

let undir_move_insert_def = new_definition
  `undir_move_insert p x y acc =
     pri_move_insert p x y (pri_move_insert p y x acc)`;;

let moves_to_sp_def,moves_to_sp_ind = define_rec
  [`moves_to_sp [] acc = acc`;
   `moves_to_sp (move' :: xs) acc =
        (let (p,x,y) = move' in
        moves_to_sp xs (undir_move_insert p x y acc))`];;

(*Do a consistency sort after setting up the sptree of moves*)
let resort_moves_def = new_definition
  `resort_moves acc =
   sptree_map (\ls. MAP SND (reg_alloc_sort_moves ls)) acc`;;

let algorithm_INDUCT,algorithm_RECURSION = define_datatype
  "algorithm = reg_alloc_Simple | reg_alloc_IRC";;
hol4_overload "Simple" "reg_alloc_Simple";;
hol4_overload "IRC" "reg_alloc_IRC";;

(* Read-only version of coalesce_parent: follows the coalesce chain
   to the root without path compression. Safe for use in biased_pref
   where state must not be modified. *)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let coalesce_root_def,coalesce_root_ind = define_wf
  `MEASURE (\x0. (\n. n) x0)`
  [`coalesce_root x =
   st_ex_bind (coalesced_sub x) (\
     xt. st_ex_bind (is_Fixed xt) (\
     bx.
     if bx then
       st_ex_return xt else
       if x <= xt then
         st_ex_return x else
         coalesce_root xt))`];;

(* mtable is an sptree lookup for the moves *)
let biased_pref_def = new_definition
  `biased_pref mtable n ks =
   st_ex_bind get_dim (\
     d.
     if n < d then
     st_ex_bind (coalesce_root n) (\
       v.
       let vs = (match sptree_lookup n mtable with NONE -> [] | SOME
         vs -> vs) in
       handle_Subscript (first_match_col ks (v :: vs)) (st_ex_return
         NONE)) else
       st_ex_return NONE)`;;

(* very similar to consistency_ok, but for initializing *)
let full_consistency_ok_def = new_definition
  `full_consistency_ok k x y =
   (if x = y then
     st_ex_return F else
   // check 1
   st_ex_bind get_dim (\
     d.
     if x >= d \/ y >= d then st_ex_return F else
     st_ex_bind (adj_ls_sub y) (\
       adjy.
       // check 2
       if sorted_mem x adjy then st_ex_return F else
       st_ex_bind (is_Fixed_k k x) (\
         bx. st_ex_bind (is_Fixed_k k y) (\
         by. st_ex_bind (is_Atemp x) (\
         ax. st_ex_bind (is_Atemp y) (\
         ay.
         st_ex_return ((bx \/ ax) /\ (by \/ ay) /\ ~(bx /\
           by)))))))))`;;

let update_move_def = new_definition
  `update_move spta ((p:num),(x:num),(y:num)) =
   (let spx:num = spta x in
   let spy:num = spta y in
   if spx <= spy then
     (p,(spx,spy)) else
     (p,(spy,spx)))`;;

(* These behave in reverse to their other versions *)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let neg_first_match_col_def,neg_first_match_col_ind = define_wf
  `MEASURE (\(x0,x1,x2). list_size (\n. n) x2)`
  [`neg_first_match_col k bads [] = st_ex_return NONE`;
   `neg_first_match_col k bads (x :: xs) =
        st_ex_bind (node_tag_sub x) (\
          c.
          match c with
            Fixed m ->
              (if MEM m bads \/ m < k then neg_first_match_col
                k bads xs else st_ex_return (SOME m)) | _17 ->
                neg_first_match_col k bads xs)`];;

let neg_biased_pref_def = new_definition
  `neg_biased_pref k mtable n bads =
   st_ex_bind get_dim (\
     d.
     if n < d then
       let vs = (match sptree_lookup n mtable with NONE -> [] | SOME
         vs -> vs) in
       handle_Subscript (neg_first_match_col k bads vs) (st_ex_return
         NONE) else
       st_ex_return NONE)`;;

(* Putting everything together in one call *)
let do_reg_alloc_def = new_definition
  `do_reg_alloc alg scost k moves ct forced fs (ta,fa,n) =
   st_ex_ignore_bind
     (init_ra_state ct forced fs (ta,fa,n)) (st_ex_bind (st_ex_return
       (MAP (update_move (sp_default ta)) moves)) (\
     moves0. st_ex_bind (st_ex_FILTER (\(_18,(x,y)).
       full_consistency_ok k x y) moves0 []) (\
     moves. st_ex_bind (do_alloc1 (if alg = Simple then [] else
       moves) scost k) (\
     ls. st_ex_bind (st_ex_return (resort_moves (moves_to_sp moves0
       LN))) (\
     mvs. st_ex_ignore_bind
     (assign_Atemps k ls (biased_pref mvs)) (st_ex_ignore_bind
     (assign_Stemps k (neg_biased_pref k mvs)) (st_ex_bind
       (extract_color ta) (\
     spcol.
     st_ex_return spcol))))))))
   // return the composed from wordLang into the graph + the allocation`;;

(* As we are using fixed-size array, we need to define a different record type for the initialization *)
(* HOL4 makes the record of an initial state of ra_state and the
   run function with ML code (define_run of
   ml_monadBaseLib); an array field of it is the length and
   the initial value of the array *)
let ira_state_FIELDS = define_record "ira_state"
  ["adj_ls","num#num list";
   "node_tag","num#reg_alloc_tag";
   "degrees","num#num";
   "dim","num";
   "simp_wl","num list";
   "spill_wl","num list";
   "freeze_wl","num list";
   "avail_moves_wl","(num#num#num) list";
   "unavail_moves_wl","(num#num#num) list";
   "coalesced","num#num";
   "move_related","num#bool";
   "stack","num list"];;
let run_ira_state_def = new_definition
  `run_ira_state x state =
     run x (mk_ra_state (REPLICATE (FST (ira_state_adj_ls state))
       (SND (ira_state_adj_ls state))) (REPLICATE (FST
       (ira_state_node_tag state)) (SND (ira_state_node_tag state)))
       (REPLICATE (FST (ira_state_degrees state)) (SND
       (ira_state_degrees state))) (ira_state_dim state)
       (ira_state_simp_wl state) (ira_state_spill_wl state)
       (ira_state_freeze_wl state) (ira_state_avail_moves_wl state)
       (ira_state_unavail_moves_wl state) (REPLICATE (FST
       (ira_state_coalesced state)) (SND (ira_state_coalesced
       state))) (REPLICATE (FST (ira_state_move_related state)) (SND
       (ira_state_move_related state))) (ira_state_stack state))`;;


(* The top-level (non-monadic) reg_alloc call which should be modified to fit
   the translator's requirements *)

let reg_alloc_aux_def = new_definition
  `reg_alloc_aux alg scost k moves ct forced fs (ta,fa,n) =
     run_ira_state (do_reg_alloc alg scost k moves ct forced fs
       (ta,fa,n))
                       (mk_ira_state (n,[]) (n,Atemp) (n,0) n []
                         [] [] [] [] (n,0) (n,F) [])`;;

let reg_alloc_def = new_definition
  `reg_alloc alg scost k moves ct forced fs =
     reg_alloc_aux alg scost k moves ct forced fs (mk_bij ct)`;;

hol4_only "++" "APPEND";;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
