(* ======================================================== *)
(*  reg_allocProof: ported from HOL4's
    compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml
    A proof theory about reg_alloc.ml, with 12 definitions and 119
    theorems.  Needed by linear_scanProof.ml and word_allocProof.ml.  *)
(* ======================================================== *)

(*
  Proves correctness of the graph-colouring register allocator.
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "lib/sorting.ml";;
needs "lib/sptree.ml";;
needs "lib/state_transformer.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

cake_hide_consts
  ["return","errorMonad_return"];;

hol4_overload "++" "otherwise";;

(* Edge from node x to node y, in terms of an adjacency list *)
let has_edge_def = cake_define
  `has_edge adjls x y <=>
   x < LENGTH adjls /\
   y < LENGTH adjls /\
   MEM y (EL x adjls)`;;

let undirected_def = cake_define
  `undirected adjls <=>
   (!x y.
     has_edge adjls x y ==>
     has_edge adjls y x)`;;

(* ---
  some well-formedness properties on the state.
  this basically says that all of the arrays have the right dimensions,
  and that the worklists always contain legal nodes
  --- *)

let good_ra_state_def = cake_define
  `good_ra_state s <=>
   LENGTH (ra_state_adj_ls s) = ra_state_dim s /\
   LENGTH (ra_state_node_tag s) = ra_state_dim s /\
   LENGTH (ra_state_degrees s) = ra_state_dim s /\
   LENGTH (ra_state_coalesced s) = ra_state_dim s /\
   LENGTH (ra_state_move_related s) = ra_state_dim s /\
   EVERY (\v. v < ra_state_dim s) (ra_state_coalesced s) /\
   EVERY (\ls. EVERY (\v. v < ra_state_dim s) ls) (ra_state_adj_ls s)
     /\
   EVERY (\ls. SORTED (>) ls) (ra_state_adj_ls s) /\
   EVERY (\v. v < ra_state_dim s) (ra_state_simp_wl s) /\
   EVERY (\v. v < ra_state_dim s) (ra_state_spill_wl s) /\
   EVERY (\v. v < ra_state_dim s) (ra_state_freeze_wl s) /\
   EVERY (\((p:num),x,y). x < ra_state_dim s /\ y < ra_state_dim s)
     (ra_state_avail_moves_wl s) /\
   EVERY (\((p:num),x,y). x < ra_state_dim s /\ y < ra_state_dim s)
     (ra_state_unavail_moves_wl s) /\
   undirected (ra_state_adj_ls s)`;;

(* --- invariant: no two adjacent nodes have the same colour --- *)
let no_clash_def = cake_define
  `no_clash adj_ls node_tag <=>
   (!x y.
     has_edge adj_ls x y ==>
     (match (EL x node_tag,EL y node_tag) with
       (Fixed n,Fixed m) ->
         n = m ==> x = y | _1 -> T))`;;

(*
  Good preference oracle may only inspect, but not touch the state
  Moreover, it must always select a member of the input list
*)
let good_pref_def = cake_define
  `good_pref pref <=>
   (!n ks s.
     good_ra_state s ==>
     (?res.
     pref n ks s = (M_success res,s) /\
     (match res with
       NONE -> T | SOME k -> MEM k ks)))`;;

(* HOL4 reg_allocProofScript.sml:84: ML code, not ported *)

(* HOL4 reg_allocProofScript.sml:86: ML code, not ported *)

(* HOL4 reg_allocProofScript.sml:88: ML code, not ported *)

(* HOL4 reg_allocProofScript.sml:90: ML code, not ported *)

(* HOL4 reg_allocProofScript.sml:92: ML code, not ported *)

(* M_success conditions *)
(* HOL4 reg_allocProofScript.sml:95-98: a theorem that HOL4 states as
   the value of an ML expression: case_eq_thms *)

let tag_case_st = cake_theorem "tag_case_st"
  (fun () ->
    `!t.
     (reg_alloc_tag_CASE t a b c) f = (reg_alloc_tag_CASE t (\n.
       a n f) (b f) (c f))`)
  CHEAT_TAC;;

let list_case_st = cake_theorem "list_case_st"
  (fun () ->
    `!t.
     (list_CASE t a b) f = (list_CASE t (a f) (\x y. b x y f))`)
  CHEAT_TAC;;

(* ---
  TODO: These lemmas should be automatically generated for each array used!

  Note that they can be stated independently of the precise state invariants
  (as shown below)

  The array components we have are:
    adj_ls, node_tag, degrees, coalesced, move_related
  ---*)

(* Rewriting lemmas for array "sub" *)
let msub_eqn = cake_theorem "Msub_eqn[simp]"
  (fun () ->
    `!e n ls v.
     Msub e n ls =
     (if n < LENGTH ls then M_success (EL n ls) else M_failure e)`)
  CHEAT_TAC;;

let adj_ls_sub_eqn = cake_theorem "adj_ls_sub_eqn[simp]"
  (fun () ->
    `adj_ls_sub n s =
     (if n < LENGTH (ra_state_adj_ls s) then
     (M_success (EL n (ra_state_adj_ls s)),s) else
     (M_failure (reg_alloc_Subscript),s))`)
  CHEAT_TAC;;

let node_tag_sub_eqn = cake_theorem "node_tag_sub_eqn[simp]"
  (fun () ->
    `node_tag_sub n s =
     (if n < LENGTH (ra_state_node_tag s) then
     (M_success (EL n (ra_state_node_tag s)),s) else
     (M_failure (reg_alloc_Subscript),s))`)
  CHEAT_TAC;;

let degrees_sub_eqn = cake_theorem "degrees_sub_eqn[simp]"
  (fun () ->
    `degrees_sub n s =
     (if n < LENGTH (ra_state_degrees s) then
     (M_success (EL n (ra_state_degrees s)),s) else
     (M_failure (reg_alloc_Subscript),s))`)
  CHEAT_TAC;;

let coalesced_sub = cake_theorem "coalesced_sub[simp]"
  (fun () ->
    `coalesced_sub n s =
     (if n < LENGTH (ra_state_coalesced s) then
     (M_success (EL n (ra_state_coalesced s)),s) else
     (M_failure reg_alloc_Subscript,s))`)
  CHEAT_TAC;;

let move_related_sub = cake_theorem "move_related_sub[simp]"
  (fun () ->
    `move_related_sub n s =
     (if n < LENGTH (ra_state_move_related s) then
     (M_success (EL n (ra_state_move_related s)),s) else
     (M_failure reg_alloc_Subscript,s))`)
  CHEAT_TAC;;

(* Rewriting lemmas for array "update" *)
let mupdate_eqn = cake_theorem "Mupdate_eqn[simp]"
  (fun () ->
    `!e x n ls.
     Mupdate e x n ls =
     (if n < LENGTH ls then
     M_success (LUPDATE x n ls) else
     M_failure e)`)
  CHEAT_TAC;;

let update_adj_ls_eqn = cake_theorem "update_adj_ls_eqn[simp]"
  (fun () ->
    `update_adj_ls n t s =
     (if n < LENGTH (ra_state_adj_ls s) then
      (M_success one,ra_state_adj_ls_fupd (K (LUPDATE t n
        (ra_state_adj_ls s))) s) else
      (M_failure (reg_alloc_Subscript),s))`)
  CHEAT_TAC;;

let update_node_tag_eqn = cake_theorem "update_node_tag_eqn[simp]"
  (fun () ->
    `update_node_tag n t s =
     (if n < LENGTH (ra_state_node_tag s) then
      (M_success one,ra_state_node_tag_fupd (K (LUPDATE t n
        (ra_state_node_tag s))) s) else
      (M_failure (reg_alloc_Subscript),s))`)
  CHEAT_TAC;;

let update_degrees_eqn = cake_theorem "update_degrees_eqn[simp]"
  (fun () ->
    `update_degrees n t s =
     (if n < LENGTH (ra_state_degrees s) then
      (M_success one,ra_state_degrees_fupd (K (LUPDATE t n
        (ra_state_degrees s))) s) else
      (M_failure (reg_alloc_Subscript),s))`)
  CHEAT_TAC;;

let update_coalesced_eqn = cake_theorem "update_coalesced_eqn[simp]"
  (fun () ->
    `update_coalesced n t s =
     (if n < LENGTH (ra_state_coalesced s) then
      (M_success one,ra_state_coalesced_fupd (K (LUPDATE t n
        (ra_state_coalesced s))) s) else
      (M_failure (reg_alloc_Subscript),s))`)
  CHEAT_TAC;;

let update_move_related_eqn =
  cake_theorem "update_move_related_eqn[simp]"
  (fun () ->
    `update_move_related n t s =
     (if n < LENGTH (ra_state_move_related s) then
      (M_success one,ra_state_move_related_fupd (K (LUPDATE t n
        (ra_state_move_related s))) s) else
      (M_failure (reg_alloc_Subscript),s))`)
  CHEAT_TAC;;

(* --- *)

(* The following are also routine theorems, but slightly more complicated.
  TODO: can they be stated generically? *)

(* This asserts, e.g. that the monadic map of (\i.node_tag_sub i) returns
   success if the input list were all within range *)
let st_ex_MAP_node_tag_sub = cake_theorem "st_ex_MAP_node_tag_sub"
  (fun () ->
    `!ls s.
     EVERY (\v. v < LENGTH (ra_state_node_tag s)) ls ==>
     st_ex_MAP node_tag_sub ls s = (M_success (MAP (\i. EL i
       (ra_state_node_tag s)) ls),s)`)
  CHEAT_TAC;;

let st_ex_MAP_adj_ls_sub = cake_theorem "st_ex_MAP_adj_ls_sub"
  (fun () ->
    `!ls s.
     EVERY (\v. v < LENGTH (ra_state_adj_ls s)) ls ==>
     st_ex_MAP adj_ls_sub ls s = (M_success (MAP (\i. EL i
       (ra_state_adj_ls s)) ls),s)`)
  CHEAT_TAC;;

let st_ex_MAP_degrees_sub = cake_theorem "st_ex_MAP_degrees_sub"
  (fun () ->
    `!ls s.
     EVERY (\v. v < LENGTH (ra_state_degrees s)) ls ==>
     st_ex_MAP degrees_sub ls s = (M_success (MAP (\i. EL i
       (ra_state_degrees s)) ls),s)`)
  CHEAT_TAC;;
(* --- *)

(* --- the main (core) correctness proofs start here --- *)
let remove_colours_frame = cake_theorem "remove_colours_frame"
  (fun () ->
    `!adjs ks s res s'.
     remove_colours adjs ks s = (res,s') ==>
     s = s'`)
  CHEAT_TAC;;

let remove_colours_success = cake_theorem "remove_colours_success"
  (fun () ->
    `!adjs ks s ls s'.
     remove_colours adjs ks s = (M_success ls,s') ==>
     Abbrev (set_of_list ls SUBSET set_of_list ks /\
     (!n. MEM n adjs /\ n < LENGTH (ra_state_node_tag s') ==>
     (match EL n (ra_state_node_tag s) with
       Fixed c -> ~(MEM c ls) | _2 -> T)))`)
  CHEAT_TAC;;

let no_clash_LUPDATE_Stemp =
  cake_theorem "no_clash_LUPDATE_Stemp[local]"
  (fun () ->
    `no_clash adjls tags ==>
     no_clash adjls (LUPDATE Stemp n tags)`)
  CHEAT_TAC;;

let no_clash_LUPDATE_Fixed =
  cake_theorem "no_clash_LUPDATE_Fixed[local]"
  (fun () ->
    `undirected adjls /\
     EVERY (\ls. EVERY (\v. v < LENGTH tags) ls) adjls /\
     n < LENGTH adjls /\
     (!m. MEM m (EL n adjls) /\ m < LENGTH tags ==> ~(EL m tags =
       Fixed x)) /\
     no_clash adjls tags ==>
     no_clash adjls (LUPDATE (Fixed x) n tags)`)
  CHEAT_TAC;;

let remove_colours_succeeds =
  cake_theorem "remove_colours_succeeds[local]"
  (fun () ->
    `!adj ks s s.
     EVERY (\v. v < LENGTH (ra_state_node_tag s)) adj ==>
     (?ls. remove_colours adj ks s = (M_success ls,s))`)
  CHEAT_TAC;;

let assign_Atemp_tag_correct = cake_theorem "assign_Atemp_tag_correct"
  (fun () ->
    `good_ra_state s /\
     no_clash (ra_state_adj_ls s) (ra_state_node_tag s) /\
     good_pref pref /\
     n < ra_state_dim s ==>
     (?s'.
     assign_Atemp_tag ks pref n s = (M_success one,s') /\
     (!m.
     if n = m /\ EL n (ra_state_node_tag s) = Atemp then ~(EL n
       (ra_state_node_tag s') = Atemp) else EL m (ra_state_node_tag s')
       = EL m (ra_state_node_tag s)) /\
     no_clash (ra_state_adj_ls s') (ra_state_node_tag s') /\
     good_ra_state s' /\
     s' = ra_state_node_tag_fupd (K (ra_state_node_tag s')) s)`)
  CHEAT_TAC;;

let assign_Atemps_FOREACH_lem =
  cake_theorem "assign_Atemps_FOREACH_lem[local]"
  (fun () ->
    `!ls s ks prefs.
     good_ra_state s /\
     no_clash (ra_state_adj_ls s) (ra_state_node_tag s) /\
     good_pref prefs /\
     EVERY (\v. v < ra_state_dim s) ls ==>
     (?s'.
       st_ex_FOREACH ls (assign_Atemp_tag ks prefs) s = (M_success
         one,s') /\
       no_clash (ra_state_adj_ls s') (ra_state_node_tag s') /\
       good_ra_state s' /\
       s' = ra_state_node_tag_fupd (K (ra_state_node_tag s')) s /\
       (!m.
         if MEM m ls /\ EL m (ra_state_node_tag s) = Atemp then
           ~(EL m (ra_state_node_tag s') = Atemp) else EL m
           (ra_state_node_tag s') = EL m (ra_state_node_tag s)))`)
  CHEAT_TAC;;

let assign_Atemps_correct = cake_theorem "assign_Atemps_correct"
  (fun () ->
    `!k ls prefs s.
     good_ra_state s /\
     good_pref prefs /\
     no_clash (ra_state_adj_ls s) (ra_state_node_tag s) ==>
     (?s'.
     assign_Atemps k ls prefs s = (M_success one,s') /\
     no_clash (ra_state_adj_ls s') (ra_state_node_tag s') /\
     good_ra_state s' /\
     s' = ra_state_node_tag_fupd (K (ra_state_node_tag s')) s /\
     EVERY (\n. ~(n = Atemp)) (ra_state_node_tag s') /\
     (!m.
     m < LENGTH (ra_state_node_tag s) /\ ~(EL m (ra_state_node_tag
       s) = Atemp) ==>
     EL m (ra_state_node_tag s') = EL m (ra_state_node_tag s)))`)
  CHEAT_TAC;;

let SORTED_HEAD_LT = cake_theorem "SORTED_HEAD_LT[local]"
  (fun () ->
    `!ls.
     (col:num) < h /\ SORTED (\x y. x <= y) (h :: ls) ==>
     ~(MEM col ls)`)
  CHEAT_TAC;;

(* Correctness for the second step *)
let unbound_colour_correct = cake_theorem "unbound_colour_correct"
  (fun () ->
    `!ls k k'.
     SORTED (\x y. x <= y) ls ==>
     k <= unbound_colour k ls /\
     ~(MEM (unbound_colour k ls) ls)`)
  CHEAT_TAC;;

(*
  Good negated preference oracle may only inspect, but not touch the state
  Moreover, it must always select an element ≥ k not in the input list
*)
let good_neg_pref_def = cake_define
  `good_neg_pref (k:num) pref <=>
   (!n bads s.
     good_ra_state s ==>
     (?res.
     pref n bads s = (M_success res,s) /\
     (match res with
       NONE -> T | SOME c -> ~(MEM c bads) /\ k <= c)))`;;

let assign_Stemp_tag_correct = cake_theorem "assign_Stemp_tag_correct"
  (fun () ->
    `good_ra_state s /\
     no_clash (ra_state_adj_ls s) (ra_state_node_tag s) /\
     n < ra_state_dim s /\
     good_neg_pref k prefs ==>
     (?s'.
     assign_Stemp_tag k prefs n s = (M_success one,s') /\
     (!m.
       if n = m /\ EL n (ra_state_node_tag s) = Stemp then ?k'. EL
         n (ra_state_node_tag s') = Fixed k' /\ k <= k' else EL m
         (ra_state_node_tag s') = EL m (ra_state_node_tag s)) /\
     no_clash (ra_state_adj_ls s') (ra_state_node_tag s') /\
     good_ra_state s' /\
     s' = ra_state_node_tag_fupd (K (ra_state_node_tag s')) s)`)
  CHEAT_TAC;;

(* Almost exactly the same as the FOREACH for Atemps *)
let assign_Stemps_FOREACH_lem =
  cake_theorem "assign_Stemps_FOREACH_lem[local]"
  (fun () ->
    `!ls s k.
     good_ra_state s /\
     no_clash (ra_state_adj_ls s) (ra_state_node_tag s) /\
     EVERY (\v. v < ra_state_dim s) ls /\
     good_neg_pref k prefs ==>
     (?s'.
       st_ex_FOREACH ls (assign_Stemp_tag k prefs) s = (M_success
         one,s') /\
       no_clash (ra_state_adj_ls s') (ra_state_node_tag s') /\
       good_ra_state s' /\
       (!m.
         if MEM m ls /\ EL m (ra_state_node_tag s) = Stemp then
           ?k'. EL m (ra_state_node_tag s') = Fixed k' /\ k <= k' else
           EL m (ra_state_node_tag s') = EL m (ra_state_node_tag s)) /\
       s' = ra_state_node_tag_fupd (K (ra_state_node_tag s')) s)`)
  CHEAT_TAC;;

let assign_Stemps_correct = cake_theorem "assign_Stemps_correct"
  (fun () ->
    `good_ra_state s /\
     no_clash (ra_state_adj_ls s) (ra_state_node_tag s) /\
     good_neg_pref k prefs ==>
     (?s'.
       assign_Stemps k prefs s = (M_success one,s') /\
       no_clash (ra_state_adj_ls s') (ra_state_node_tag s') /\
       good_ra_state s' /\
       s' = ra_state_node_tag_fupd (K (ra_state_node_tag s')) s /\
       (!m.
         m < LENGTH (ra_state_node_tag s) ==>
         (if EL m (ra_state_node_tag s) = Stemp then
           ?k'. EL m (ra_state_node_tag s') = Fixed k' /\ k <= k'
             else
         EL m (ra_state_node_tag s') = EL m (ra_state_node_tag
           s))))`)
  CHEAT_TAC;;

(* --  Random sanity checks that will be needed at some point -- *)

(* Checking that biased_pref satisfies good_pref *)
let first_match_col_correct =
  cake_theorem "first_match_col_correct[local]"
  (fun () ->
    `!x ks s.
     ?res. first_match_col ks x s = (res,s) /\
     (match res with
       M_failure v -> v = reg_alloc_Subscript | M_success (SOME
         k) -> MEM k ks | _3 -> T)`)
  CHEAT_TAC;;

let coalesce_root_success = cake_theorem "coalesce_root_success"
  (fun () ->
    `!n s. good_ra_state s /\ n < ra_state_dim s ==>
     (?v. coalesce_root n s = (M_success v,s))`)
  CHEAT_TAC;;

let good_pref_biased_pref = cake_theorem "good_pref_biased_pref"
  (fun () ->
    `!t. good_pref (biased_pref t)`)
  CHEAT_TAC;;

(* Checking that the bijection produced is correct *)

let in_clash_tree_def = cake_define_list
  [`in_clash_tree (reg_alloc_Delta w r) x <=> MEM x w \/ MEM x r`;
   `in_clash_tree (reg_alloc_Set names:clash_tree) x <=> x IN domain
  names`;
   `in_clash_tree (reg_alloc_Branch name_opt t1 t2:clash_tree) x <=>
        in_clash_tree t1 x \/
        in_clash_tree t2 x \/
        (match name_opt with
          SOME names -> x IN domain names | NONE -> F)`;
   `in_clash_tree (reg_alloc_Seq t t':clash_tree) x <=>
  in_clash_tree t x \/ in_clash_tree t' x`];;

(*g inverts f as an sptree *)
let sp_inverts_def = cake_define
  `sp_inverts f g <=>
   (!m fm.
     sptree_lookup m f = SOME fm ==>
     sptree_lookup fm g = SOME m)`;;

let sp_inverts_insert = cake_theorem "sp_inverts_insert"
  (fun () ->
    `sp_inverts f g /\ ~(x IN domain f) /\ ~(y IN domain g) ==>
     sp_inverts (sptree_insert x y f) (sptree_insert y x g)`)
  CHEAT_TAC;;

let list_remap_domain = cake_theorem "list_remap_domain[local]"
  (fun () ->
    `!ls ta fa n ta' fa' n'.
     list_remap ls (ta,fa,n) = (ta',fa',n') ==>
     domain ta' = domain ta UNION set_of_list ls`)
  CHEAT_TAC;;

(* HOL4 reg_allocProofScript.sml:814-835: a theorem that HOL4 states
   as the value of an ML expression: list_remap_bij *)

let mk_bij_aux_domain = cake_theorem "mk_bij_aux_domain[local]"
  (fun () ->
    `!ct ta fa n ta' fa' n'.
     mk_bij_aux ct (ta,fa,n) = (ta',fa',n') ==>
     domain ta' = domain ta UNION {x | in_clash_tree ct x}`)
  CHEAT_TAC;;

(* HOL4 reg_allocProofScript.sml:879-919: a theorem that HOL4 states
   as the value of an ML expression: mk_bij_aux_bij *)

let list_remap_wf = cake_theorem "list_remap_wf[local]"
  (fun () ->
    `!l ta fa n ta' fa' n'.
     list_remap l (ta,fa,n) = (ta',fa',n') /\
     sptree_wf ta /\ sptree_wf fa ==>
     sptree_wf ta' /\ sptree_wf fa'`)
  CHEAT_TAC;;

let mk_bij_aux_wf = cake_theorem "mk_bij_aux_wf"
  (fun () ->
    `!ct ta fa n ta' fa' n'.
     mk_bij_aux ct (ta,fa,n) = (ta',fa',n') /\
     sptree_wf ta /\ sptree_wf fa ==>
     Abbrev (sptree_wf ta' /\ sptree_wf fa')`)
  CHEAT_TAC;;

(* Properties of the graph manipulating functions
   All of these simultaneously prove success
   together with the correctness properties.

   One could also imagine proving the success separately from
   the correctness
*)
(* the list represents a clique *)
let is_clique_def = cake_define
  `is_clique ls adjls <=>
   (!x y. MEM x ls /\ MEM y ls /\ ~(x = y) ==>
     has_edge adjls x y)`;;

let is_subgraph_def = cake_define
  `is_subgraph g h <=>
   (!x y.
     has_edge g x y ==> has_edge h x y)`;;

let is_subgraph_refl = cake_theorem "is_subgraph_refl"
  (fun () ->
    `is_subgraph s s`)
  CHEAT_TAC;;

let is_subgraph_trans = cake_theorem "is_subgraph_trans"
  (fun () ->
    `is_subgraph s s' /\
     is_subgraph s' s'' ==>
     is_subgraph s s''`)
  CHEAT_TAC;;

(* TODO quick sanity check: move to proof file when done *)
let hide_def = cake_define
  `reg_allocProof_hide x = x`;;
hol4_overload "hide" "reg_allocProof_hide";;

let GT_TRANS = cake_theorem "GT_TRANS[local]"
  (fun () ->
    `(a:num) > b /\ b > c ==> a > c`)
  CHEAT_TAC;;

let GT_sorted_eq = cake_theorem "GT_sorted_eq[local]"
  (fun () ->
    `SORTED (>) ((x:num) :: L) <=> SORTED (>) L /\ (!y. MEM y L ==> x
  > y)`)
  CHEAT_TAC;;

let sorted_insert_correct_lem =
  cake_theorem "sorted_insert_correct_lem[local]"
  (fun () ->
    `!ls acc.
     SORTED (>) ls /\
     SORTED (>) (REVERSE acc) /\
     SORTED (>) (REVERSE acc ++ ls) /\
     EVERY (\y. y > x) acc ==>
     reg_allocProof_hide (
       SORTED (>) (sorted_insert x acc ls) /\
       (!z.
       MEM z (sorted_insert x acc ls) <=>
       x = z \/ MEM z ls \/ MEM z acc))`)
  CHEAT_TAC;;

let sorted_insert_correct = cake_theorem "sorted_insert_correct"
  (fun () ->
    `!ls.
     SORTED (>) ls ==>
     SORTED (>) (sorted_insert x [] ls) /\
     (!z.
     MEM z (sorted_insert x [] ls) <=> x = z \/ MEM z ls)`)
  CHEAT_TAC;;

let sorted_mem_correct = cake_theorem "sorted_mem_correct"
  (fun () ->
    `!ls.
     SORTED (>) ls ==>
     (sorted_mem x ls <=> MEM x ls)`)
  CHEAT_TAC;;

let insert_edge_succeeds = cake_theorem "insert_edge_succeeds"
  (fun () ->
    `good_ra_state s /\
     y < ra_state_dim s /\
     x < ra_state_dim s ==>
     (?s'. insert_edge x y s = (M_success one,s') /\
     good_ra_state s' /\
     s' = ra_state_adj_ls_fupd (K (ra_state_adj_ls s')) s /\
     (!a b.
     (has_edge (ra_state_adj_ls s') a b <=>
     (a = x /\ b = y) \/ (a = y /\ b = x) \/ (has_edge
       (ra_state_adj_ls s) a b))))`)
  CHEAT_TAC;;

let list_insert_edge_succeeds = cake_theorem "list_insert_edge_succeeds"
  (fun () ->
    `!ys x s.
     good_ra_state s /\
     x < ra_state_dim s /\
     EVERY (\y. y < ra_state_dim s) ys ==>
     (?s'. list_insert_edge x ys s = (M_success one,s') /\
     good_ra_state s' /\
     s' = ra_state_adj_ls_fupd (K (ra_state_adj_ls s')) s /\
     (!a b.
     (has_edge (ra_state_adj_ls s') a b <=>
     (a = x /\ MEM b ys) \/
     (b = x /\ MEM a ys) \/
     (has_edge (ra_state_adj_ls s) a b))))`)
  CHEAT_TAC;;

(* From here onwards we stop characterizing s'.adj_ls exactly
   although it could be done
 *)
let clique_insert_edge_succeeds =
  cake_theorem "clique_insert_edge_succeeds"
  (fun () ->
    `!ls s.
     good_ra_state s /\
     EVERY (\y. y < ra_state_dim s) ls ==>
     (?s'. clique_insert_edge ls s = (M_success one,s') /\
     good_ra_state s' /\
     s' = ra_state_adj_ls_fupd (K (ra_state_adj_ls s')) s /\
     is_clique ls (ra_state_adj_ls s') /\
     is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s'))`)
  CHEAT_TAC;;

let extend_clique_succeeds = cake_theorem "extend_clique_succeeds"
  (fun () ->
    `!ls cli s.
     good_ra_state s /\
     is_clique cli (ra_state_adj_ls s) /\
     EVERY (\y. y < ra_state_dim s) ls /\
     ALL_DISTINCT cli /\
     EVERY (\y. y < ra_state_dim s) cli ==>
     (?cli' s'. extend_clique ls cli s = (M_success cli',s') /\
     good_ra_state s' /\
     ALL_DISTINCT cli' /\
     s' = ra_state_adj_ls_fupd (K (ra_state_adj_ls s')) s /\
     set_of_list cli' = set_of_list (cli ++ ls) /\
     is_clique cli' (ra_state_adj_ls s') /\
     is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s'))`)
  CHEAT_TAC;;

(* The col needed to get colouring satisfactory can be generated
   from the node tags
   The correctness should be a consequence of no_clash *)
let colouring_satisfactory_def = cake_define
  `colouring_satisfactory col adjls =
   (!x. x < LENGTH adjls ==>
    (!y. y < LENGTH adjls /\ MEM y (EL x adjls) ==>
    col x = col y ==> x = y))`;;

(*TODO: this is in word_allocProof*)
let INJ_less = cake_theorem "INJ_less[local]"
  (fun () ->
    `!f s' t s.
     INJ f s' t /\ s SUBSET s' ==>
     INJ f s t`)
  CHEAT_TAC;;

let check_partial_col_success = cake_theorem "check_partial_col_success"
  (fun () ->
    `!ls live flive col.
     domain flive = IMAGE col (domain live) /\
     INJ col (set_of_list ls UNION domain live) UNIV ==>
     (?livein flivein.
     check_partial_col col ls live flive = SOME (livein,flivein) /\
     domain flivein = IMAGE col (domain livein))`)
  CHEAT_TAC;;

let INJ_COMPOSE_IMAGE = cake_theorem "INJ_COMPOSE_IMAGE"
  (fun () ->
    `!a b u.
     INJ f a b /\
     INJ g (IMAGE f a) u ==>
     INJ (g o f) a u`)
  CHEAT_TAC;;

let colouring_satisfactory_cliques =
  cake_theorem "colouring_satisfactory_cliques"
  (fun () ->
    `!ls g (f:num->num).
     ALL_DISTINCT ls /\
     EVERY (\x. x < LENGTH g) ls /\
     colouring_satisfactory f g /\ is_clique ls g ==>
     ALL_DISTINCT (MAP f ls)`)
  CHEAT_TAC;;

let domain_eq_IMAGE = cake_theorem "domain_eq_IMAGE[local]"
  (fun () ->
    `domain s = IMAGE FST (set_of_list (toAList s))`)
  CHEAT_TAC;;

let is_clique_FILTER = cake_theorem "is_clique_FILTER[local]"
  (fun () ->
    `!ls.
     is_clique ls G ==>
     is_clique (FILTER P ls) G`)
  CHEAT_TAC;;

let is_clique_subgraph = cake_theorem "is_clique_subgraph[local]"
  (fun () ->
    `is_clique ls s /\
     is_subgraph s s' ==>
     is_clique ls s'`)
  CHEAT_TAC;;

let domain_numset_list_delete = cake_theorem "domain_numset_list_delete"
  (fun () ->
    `!l live.
     domain (numset_list_delete l live) =
     domain live DIFF set_of_list l`)
  CHEAT_TAC;;

(* The success theorem is separated here *)
let mk_graph_succeeds = cake_theorem "mk_graph_succeeds"
  (fun () ->
    `!ct ta liveout s.
     good_ra_state s /\
     (!x. in_clash_tree ct x ==> ta x < ra_state_dim s) /\
     INJ ta ({x | in_clash_tree ct x}) (count (LENGTH
       (ra_state_adj_ls s))) /\
     (is_clique liveout (ra_state_adj_ls s)) /\
     ALL_DISTINCT liveout /\
     (EVERY (\y. y < ra_state_dim s) liveout) ==>
     (?livein s'. mk_graph ta ct liveout s = (M_success livein,s')
       /\
     good_ra_state s' /\
     is_clique livein (ra_state_adj_ls s') /\
     s' = ra_state_adj_ls_fupd (K (ra_state_adj_ls s')) s /\
     (EVERY (\y. y < ra_state_dim s) livein) /\
     ALL_DISTINCT livein /\
     set_of_list livein SUBSET set_of_list liveout UNION IMAGE ta
       {x | in_clash_tree ct x} /\
     is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s'))`)
  CHEAT_TAC;;

let colouring_satisfactory_subgraph =
  cake_theorem "colouring_satisfactory_subgraph"
  (fun () ->
    `colouring_satisfactory f h /\
     is_subgraph g h ==>
     colouring_satisfactory f g`)
  CHEAT_TAC;;

let ALL_DISTINCT_set_INJ = cake_theorem "ALL_DISTINCT_set_INJ[local]"
  (fun () ->
    `!ls col.
     ALL_DISTINCT (MAP col ls) ==>
     INJ col (set_of_list ls) UNIV`)
  CHEAT_TAC;;

let IMAGE_DIFF = cake_theorem "IMAGE_DIFF[local]"
  (fun () ->
    `INJ f (s UNION t) UNIV ==>
     IMAGE f (s DIFF t) =
     (IMAGE f s DIFF IMAGE f t)`)
  CHEAT_TAC;;

let set_FILTER = cake_theorem "set_FILTER[local]"
  (fun () ->
    `set_of_list (FILTER P live) =
     set_of_list live DIFF (\x. ~(P x))`)
  CHEAT_TAC;;

let MEM_MAP_IMAGE = cake_theorem "MEM_MAP_IMAGE[local]"
  (fun () ->
    `(\x. MEM x (MAP f l)) = IMAGE f (set_of_list l)`)
  CHEAT_TAC;;

let domain_difference = cake_theorem "domain_difference[local]"
  (fun () ->
    `domain (difference s t) = domain s DIFF domain t`)
  CHEAT_TAC;;

let UNION_DIFF_3 = cake_theorem "UNION_DIFF_3[local]"
  (fun () ->
    `s DIFF t UNION t = s UNION t`)
  CHEAT_TAC;;

let check_partial_col_domain = cake_theorem "check_partial_col_domain"
  (fun () ->
    `!ls f live flive v.
     check_partial_col f ls live flive = SOME v ==>
     domain (FST v) = set_of_list ls UNION domain live`)
  CHEAT_TAC;;

let check_clash_tree_domain = cake_theorem "check_clash_tree_domain"
  (fun () ->
    `!ct f live flive live' flive'.
     check_clash_tree f ct live flive = SOME (live',flive') ==>
     domain live' SUBSET domain live UNION {x | in_clash_tree ct
       x}`)
  CHEAT_TAC;;

(* the correctness theorem for mk_graph *)
let mk_graph_check_clash_tree = cake_theorem "mk_graph_check_clash_tree"
  (fun () ->
    `!ct ta livelist s livelist' s' col live flive.
     mk_graph ta ct livelist s = (M_success livelist',s') /\
     colouring_satisfactory col (ra_state_adj_ls s') /\
     INJ ta ({x | in_clash_tree ct x} UNION domain live) (count
       (LENGTH (ra_state_adj_ls s))) /\
     IMAGE ta (domain live) = set_of_list livelist /\
     ALL_DISTINCT livelist /\
     EVERY (\y. y < ra_state_dim s) livelist /\
     is_clique livelist (ra_state_adj_ls s) /\
     good_ra_state s /\
     domain flive = IMAGE (col o ta) (domain live) ==>
     (?livein flivein.
     check_clash_tree (col o ta) ct live flive = SOME
       (livein,flivein) /\
     IMAGE ta (domain livein) = set_of_list livelist' /\
     domain flivein = IMAGE (col o ta) (domain livein))`)
  CHEAT_TAC;;

(* This precise characterization is needed to show that the forced edges
   correctly force any two to be distinct *)
let extend_graph_succeeds = cake_theorem "extend_graph_succeeds"
  (fun () ->
    `!(forced:(num#num) list) f s.
     good_ra_state s /\
     EVERY (\(x,y). f x < ra_state_dim s /\ f y < ra_state_dim s)
       forced ==>
     (?s'.
     extend_graph f forced s = (M_success one,s') /\
     good_ra_state s' /\
     s' = ra_state_adj_ls_fupd (K (ra_state_adj_ls s')) s /\
     (!a b.
     (has_edge (ra_state_adj_ls s') a b <=>
     (?x y. f x = a /\ f y = b /\ MEM (y,x) forced) \/
     (?x y. f x = a /\ f y = b /\ MEM (x,y) forced) \/ (has_edge
       (ra_state_adj_ls s) a b))))`)
  CHEAT_TAC;;

(* Again, this characterization is only needed for the conventions,
   but not for the correctness theorem *)
let mk_tags_st_ex_FOREACH_lem =
  cake_theorem "mk_tags_st_ex_FOREACH_lem[local]"
  (fun () ->
    `!ls s fa.
     good_ra_state s /\
     EVERY (\v. v < ra_state_dim s) ls ==>
     (?s'.
       st_ex_FOREACH ls
          (\i.
          if fa i MOD 4 = 1 then
           (match sptree_lookup (fa i) fs with NONE ->
             update_node_tag i Atemp | SOME one -> update_node_tag i
             Stemp) else if fa i MOD 4 = 3 then update_node_tag i Stemp
             else update_node_tag i (Fixed (fa i DIV 2))) s = (M_success
             one,s') /\
       good_ra_state s' /\
       s' = ra_state_node_tag_fupd (K (ra_state_node_tag s')) s /\
       (!x.
       x < ra_state_dim s ==>
       (if MEM x ls then
         (if is_phy_var (fa x) then EL x (ra_state_node_tag s') =
           Fixed ((fa x) DIV 2) else if is_stack_var (fa x) then EL x
           (ra_state_node_tag s') = Stemp else EL x (ra_state_node_tag
           s') = Atemp \/ EL x (ra_state_node_tag s') = Stemp) else
          EL x (ra_state_node_tag s') = EL x (ra_state_node_tag
            s))))`)
  CHEAT_TAC;;

let mk_tags_succeeds = cake_theorem "mk_tags_succeeds"
  (fun () ->
    `good_ra_state s /\
     n = ra_state_dim s ==>
     (?s'.
       mk_tags n fs fa s = (M_success one,s') /\
       good_ra_state s' /\
       s' = ra_state_node_tag_fupd (K (ra_state_node_tag s')) s /\
       (!x y.
       x < n /\ y = fa x ==>
       (if is_phy_var y then EL x (ra_state_node_tag s') = Fixed
         (y DIV 2) else if is_stack_var y then EL x (ra_state_node_tag
         s') = Stemp else EL x (ra_state_node_tag s') = Atemp \/ EL x
         (ra_state_node_tag s') = Stemp)))`)
  CHEAT_TAC;;

(* copied from word-to-stack proof*)
let reg_allocProof_TWOxDIV2 = cake_theorem "TWOxDIV2"
  (fun () ->
    `(
        2 * x) DIV 2 = x`)
  CHEAT_TAC;;

let extract_color_st_ex_MAP_lem =
  cake_theorem "extract_color_st_ex_MAP_lem[local]"
  (fun () ->
    `!ls s.
     EVERY (\(k,v). v < LENGTH (ra_state_node_tag s)) ls ==>
     st_ex_MAP (\(k,v). st_ex_bind (node_tag_sub v) (\t.
       st_ex_return (k,extract_tag t))) ls s =
     (M_success (MAP (\(k,v). (k,extract_tag (EL v
       (ra_state_node_tag s)))) ls),s)`)
  CHEAT_TAC;;

let extract_color_succeeds = cake_theorem "extract_color_succeeds"
  (fun () ->
    `good_ra_state s /\
     (!x y. sptree_lookup x ta = SOME y ==> y < ra_state_dim s) /\
     sptree_wf ta ==>
     extract_color ta s =
     (M_success (sptree_map (\v. extract_tag (EL v
       (ra_state_node_tag s))) ta),s)`)
  CHEAT_TAC;;

(* Here are the proofs about the "heuristic steps" *)

(* st_ex_PARTITION is similar to st_ex_MAP in that there ought to be
   some generic way to state the following lemmas
*)

(* is_not_coalesced succeeds and preserves state *)
let is_not_coalesced_succeeds =
  cake_theorem "is_not_coalesced_succeeds[local]"
  (fun () ->
    `good_ra_state s /\ n < ra_state_dim s ==>
     (?b. is_not_coalesced n s = (M_success b,s))`)
  CHEAT_TAC;;

(* As an example, we don't bother fully characterizing
   st_ex_PARTITION, but merely that show it succeeds *)
let st_ex_PARTITION_split_degree =
  cake_theorem "st_ex_PARTITION_split_degree[local]"
  (fun () ->
    `!atemps k lss lss' s.
     good_ra_state s ==>
     (?ts fs. st_ex_PARTITION (split_degree (ra_state_dim s) k)
       atemps lss lss' s =
       (M_success (ts,fs),s) /\
     EVERY (\x. MEM x (lss) \/ MEM x atemps) ts /\
     EVERY (\x. MEM x (lss') \/ MEM x atemps) fs)`)
  CHEAT_TAC;;

let st_ex_PARTITION_move_related_sub =
  cake_theorem "st_ex_PARTITION_move_related_sub[local]"
  (fun () ->
    `!atemps lss lss' s.
     EVERY (\x. x < LENGTH (ra_state_move_related s)) atemps ==>
     (?ts fs. st_ex_PARTITION move_related_sub atemps lss lss' s =
       (M_success (ts,fs),s) /\
     EVERY (\x. MEM x lss \/ MEM x atemps) ts /\
     EVERY (\x. MEM x lss' \/ MEM x atemps) fs)`)
  CHEAT_TAC;;

(* This is currently more general than necessary because it doesn't
   do any coalescing (yet) *)
let dec_deg_success = cake_theorem "dec_deg_success[local]"
  (fun () ->
    `!ls s.
     EVERY (\v. v < ra_state_dim s) ls /\
     good_ra_state s ==>
     (?d. st_ex_FOREACH ls dec_deg s = (M_success
       one,ra_state_degrees_fupd (K d) s) /\
     LENGTH d = LENGTH (ra_state_degrees s))`)
  CHEAT_TAC;;

let dec_degree_success = cake_theorem "dec_degree_success[local]"
  (fun () ->
    `!ls s.
     good_ra_state s ==>
     (?d.
     st_ex_FOREACH ls dec_degree s = (M_success
       one,ra_state_degrees_fupd (K d) s) /\
     LENGTH d = LENGTH (ra_state_degrees s))`)
  CHEAT_TAC;;

let MEM_smerge = cake_theorem "MEM_smerge[local]"
  (fun () ->
    `!xs ys.
     MEM x (smerge xs ys) <=>
     MEM x xs \/ MEM x ys`)
  CHEAT_TAC;;

let revive_moves_success = cake_theorem "revive_moves_success[local]"
  (fun () ->
    `EVERY (\x. x < LENGTH (ra_state_adj_ls s)) ls ==>
     (?s'.
     revive_moves ls s = (M_success one,s') /\
     s' = ra_state_unavail_moves_wl_fupd (K
       (ra_state_unavail_moves_wl s')) (ra_state_avail_moves_wl_fupd (K
       (ra_state_avail_moves_wl s')) s) /\
     EVERY (\x. MEM x (ra_state_avail_moves_wl s ++
       ra_state_unavail_moves_wl s)) (ra_state_avail_moves_wl s') /\
     EVERY (\x. MEM x (ra_state_avail_moves_wl s ++
       ra_state_unavail_moves_wl s)) (ra_state_unavail_moves_wl s'))`)
  CHEAT_TAC;;

let unspill_success = cake_theorem "unspill_success[local]"
  (fun () ->
    `!k s.
     good_ra_state s ==>
     (?s' b.
     unspill k s = (M_success one,s') /\
     good_ra_state s' /\
     is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s') /\
       ra_state_dim
     s = ra_state_dim s' /\ ra_state_node_tag
     s = ra_state_node_tag s')`)
  CHEAT_TAC;;

let push_stack_success = cake_theorem "push_stack_success[local]"
  (fun () ->
    `!ls s.
     EVERY (\x. x < ra_state_dim s) ls /\
     good_ra_state s ==>
     (?d mr st.
     st_ex_FOREACH ls push_stack s = (M_success
       one,ra_state_stack_fupd (K st) (ra_state_move_related_fupd (K mr)
       (ra_state_degrees_fupd (K d)
       s))) /\
     LENGTH d = LENGTH (ra_state_degrees s) /\
     LENGTH mr = LENGTH (ra_state_move_related s))`)
  CHEAT_TAC;;

let do_simplify_success = cake_theorem "do_simplify_success[local]"
  (fun () ->
    `!s.
     good_ra_state s ==>
     (?s' b.
     do_simplify k s = (M_success b,s') /\
     good_ra_state s' /\
     is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s') /\
       ra_state_dim
     s = ra_state_dim s' /\ ra_state_node_tag
     s = ra_state_node_tag s')`)
  CHEAT_TAC;;

(* This basically says nothing at the moment *)
let st_ex_FILTER_is_not_coalesced =
  cake_theorem "st_ex_FILTER_is_not_coalesced[local]"
  (fun () ->
    `!ls acc s.
     EVERY (\x. x < LENGTH (ra_state_coalesced s)) ls /\
     EVERY (\x. x < LENGTH (ra_state_coalesced s)) acc ==>
     (?ts fs. st_ex_FILTER is_not_coalesced ls acc s =
       (M_success ts,s) /\
     EVERY (\x. x < LENGTH (ra_state_coalesced s)) ts)`)
  CHEAT_TAC;;

let consistency_ok_success =
  cake_theorem "consistency_ok_success[local]"
  (fun () ->
    `!x y s.
     good_ra_state s /\
     x < ra_state_dim s /\
     y < ra_state_dim s ==>
     (?b.
     consistency_ok x y s = (M_success b,s) /\
     (b ==> x < ra_state_dim s /\ y < ra_state_dim s))`)
  CHEAT_TAC;;

let st_ex_FILTER_consistency_ok =
  cake_theorem "st_ex_FILTER_consistency_ok[local]"
  (fun () ->
    `!ls acc s.
     good_ra_state s /\
     EVERY (\((p:num),x,y). x < ra_state_dim s /\ y < ra_state_dim
       s) ls ==>
     (?ts. st_ex_FILTER (\(_4,x,y). consistency_ok x y) ls acc s =
       (M_success ts,s) /\
     EVERY (\(p,(x,y)). x < ra_state_dim s /\ y < ra_state_dim s
       \/ MEM (p,(x,y)) acc) ts)`)
  CHEAT_TAC;;

(* do_coalesce *)
let st_ex_FILTER_considered_var =
  cake_theorem "st_ex_FILTER_considered_var[local]"
  (fun () ->
    `!ls acc s.
     EVERY (\x. x < LENGTH (ra_state_node_tag s)) ls /\
     EVERY (\x. x < LENGTH (ra_state_node_tag s)) acc ==>
     (?ts fs. st_ex_FILTER (considered_var k) ls acc s =
       (M_success ts,s) /\
     EVERY (\x. x < LENGTH (ra_state_node_tag s)) ts)`)
  CHEAT_TAC;;

(* HOL4 reg_allocProofScript.sml:2364-2382: a theorem that HOL4
   states as the value of an ML expression: st_ex_MAP_deg_or_inf *)

let bg_ok_success = cake_theorem "bg_ok_success[local]"
  (fun () ->
    `good_ra_state s /\
     x < ra_state_dim s /\ y < ra_state_dim s ==>
     (?opt.
     bg_ok k x y s = (M_success opt,s) /\
     (match opt with
      NONE -> T | SOME (case1,case2) ->
       EVERY (\v. v < ra_state_dim s) case1 /\ EVERY (\v. v <
         ra_state_dim s) case2))`)
  CHEAT_TAC;;

let coalesce_parent_success =
  cake_theorem "coalesce_parent_success[local]"
  (fun () ->
    `!x s.
     x < ra_state_dim s /\
     good_ra_state s ==>
     (?y s' coal.
     coalesce_parent x s = (M_success y,s') /\
     y < ra_state_dim s /\
     good_ra_state s' /\
     s' = ra_state_coalesced_fupd (K coal) s)`)
  CHEAT_TAC;;

let canonize_move_success = cake_theorem "canonize_move_success[local]"
  (fun () ->
    `x < ra_state_dim s /\ y < ra_state_dim s /\ good_ra_state s ==>
     (?x2 y2.
     canonize_move x y s = (M_success (x2,y2),s) /\
     x2 < ra_state_dim s /\ y2 < ra_state_dim s)`)
  CHEAT_TAC;;

let st_ex_FIRST_consistency_ok_bg_ok =
  cake_theorem "st_ex_FIRST_consistency_ok_bg_ok[local]"
  (fun () ->
    `!ls acc s.
     good_ra_state s /\
     EVERY (\((p:num),x,y). x < ra_state_dim s /\ y < ra_state_dim
       s) ls /\
     EVERY (\((p:num),x,y). x < ra_state_dim s /\ y < ra_state_dim
       s) acc ==>
     (?ores ys s' coal.
     st_ex_FIRST consistency_ok (bg_ok k) ls acc s = (M_success
       (ores,ys),s') /\
     good_ra_state s' /\
     s' = ra_state_coalesced_fupd (K coal) s /\
     EVERY (\((p:num),x,y). x < ra_state_dim s /\ y < ra_state_dim
       s) ys /\
     (match ores with
       SOME ((x,y),(case1,case2),rest) ->
       x < ra_state_dim s /\ y < ra_state_dim s /\
       EVERY (\v. v < ra_state_dim s) case1 /\
       EVERY (\v. v < ra_state_dim s) case2 /\
       EVERY (\((p:num),x,y). x < ra_state_dim s /\ y <
         ra_state_dim s) rest | _5 -> T))`)
  CHEAT_TAC;;

let do_coalesce_real_success =
  cake_theorem "do_coalesce_real_success[local]"
  (fun () ->
    `!x y case1 case2 s.
     y < ra_state_dim s /\
     x < ra_state_dim s /\
     EVERY (\v. v < ra_state_dim s) case1 /\
     EVERY (\v. v < ra_state_dim s) case2 /\
     good_ra_state s ==>
     (?s'.
     do_coalesce_real x y case1 case2 s = (M_success one,s') /\
     good_ra_state s' /\
     is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s') /\
       ra_state_dim
     s = ra_state_dim s' /\ ra_state_node_tag
     s = ra_state_node_tag s')`)
  CHEAT_TAC;;

let do_coalesce_success = cake_theorem "do_coalesce_success[local]"
  (fun () ->
    `!s.
       good_ra_state s ==>
       (?s' b.
        do_coalesce k s = (M_success b,s') /\
        good_ra_state s' /\
        is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s') /\
          ra_state_dim
        s = ra_state_dim s' /\ ra_state_node_tag
        s = ra_state_node_tag s')`)
  CHEAT_TAC;;

let st_ex_FOREACH_update_move_related =
  cake_theorem "st_ex_FOREACH_update_move_related[local]"
  (fun () ->
    `!ls s b.
     EVERY (\v. v < LENGTH (ra_state_move_related s)) ls ==>
     (?lss.
     st_ex_FOREACH ls (\x. update_move_related x b) s = (M_success
       one,ra_state_move_related_fupd (K lss) s) /\
     LENGTH lss = LENGTH (ra_state_move_related s))`)
  CHEAT_TAC;;

let reset_move_related_success =
  cake_theorem "reset_move_related_success[local]"
  (fun () ->
    `!ls s.
     good_ra_state s /\
     EVERY (\(p,(x,y)). x < ra_state_dim s /\ y < ra_state_dim s)
       ls ==>
     (?mv.
     reset_move_related ls s = (M_success
       one,ra_state_move_related_fupd (K mv) s) /\
     LENGTH mv = ra_state_dim s)`)
  CHEAT_TAC;;

let do_prefreeze_success = cake_theorem "do_prefreeze_success[local]"
  (fun () ->
    `!s.
     good_ra_state s ==>
     (?s' b.
     do_prefreeze k s = (M_success b,s') /\
     good_ra_state s' /\
     is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s') /\
       ra_state_dim
     s = ra_state_dim s' /\ ra_state_node_tag
     s = ra_state_node_tag s')`)
  CHEAT_TAC;;

(* do freeze *)
let do_freeze_success = cake_theorem "do_freeze_success[local]"
  (fun () ->
    `!s.
     good_ra_state s ==>
     (?s' b.
     do_freeze k s = (M_success b,s') /\
     good_ra_state s' /\
     is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s') /\
       ra_state_dim
     s = ra_state_dim s' /\ ra_state_node_tag
     s = ra_state_node_tag s')`)
  CHEAT_TAC;;

(* do spill *)
let st_ex_list_MIN_cost_success =
  cake_theorem "st_ex_list_MIN_cost_success[local]"
  (fun () ->
    `!ls s k v acc.
     good_ra_state s /\
     EVERY (\v. v < ra_state_dim s) acc /\
     k < ra_state_dim s ==>
     (?x y.
     st_ex_list_MIN_cost scost ls (ra_state_dim s) k v acc s =
       (M_success (x,y),s) /\
     x < ra_state_dim s /\
     EVERY (\v. v < ra_state_dim s) y)`)
  CHEAT_TAC;;

let st_ex_list_MAX_deg_success =
  cake_theorem "st_ex_list_MAX_deg_success[local]"
  (fun () ->
    `!ls s k v acc.
     good_ra_state s /\
     EVERY (\v. v < ra_state_dim s) acc /\
     k < ra_state_dim s ==>
     (?x y.
     st_ex_list_MAX_deg ls (ra_state_dim s) k v acc s = (M_success
       (x,y),s) /\
     x < ra_state_dim s /\
     EVERY (\v. v < ra_state_dim s) y)`)
  CHEAT_TAC;;

let do_spill_success = cake_theorem "do_spill_success[local]"
  (fun () ->
    `!s.
       good_ra_state s ==>
       (?s' b.
         do_spill scost k s = (M_success b,s') /\
         good_ra_state s' /\
         is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s') /\
           ra_state_dim
         s = ra_state_dim s' /\ ra_state_node_tag
         s = ra_state_node_tag s')`)
  CHEAT_TAC;;

let do_step_success = cake_theorem "do_step_success[local]"
  (fun () ->
    `!scost k s.
       good_ra_state s ==>
       (?b s'.
         do_step scost k s = (M_success b,s') /\
         good_ra_state s' /\
         is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s') /\
           ra_state_dim
         s = ra_state_dim s' /\ ra_state_node_tag
         s = ra_state_node_tag s')`)
  CHEAT_TAC;;

(* HOL4 reg_allocProofScript.sml:2862: ML code, not ported *)
let rpt_do_step_success = cake_theorem "rpt_do_step_success[local]"
  (fun () ->
    `!n s k sc.
       good_ra_state s ==>
       (?s'.
         rpt_do_step scost k n s = (M_success one,s') /\
         good_ra_state s' /\
         is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s') /\
           ra_state_dim
         s = ra_state_dim s' /\ ra_state_node_tag
         s = ra_state_node_tag s')`)
  CHEAT_TAC;;

let full_consistency_ok_success =
  cake_theorem "full_consistency_ok_success[local]"
  (fun () ->
    `!x y s.
     good_ra_state s ==>
     (?b.
     full_consistency_ok k x y s = (M_success b,s) /\
     (b ==> x < ra_state_dim s /\ y < ra_state_dim s))`)
  CHEAT_TAC;;

let st_ex_FILTER_full_consistency_ok =
  cake_theorem "st_ex_FILTER_full_consistency_ok[local]"
  (fun () ->
    `!ls acc s.
     good_ra_state s ==>
     (?ts. st_ex_FILTER (\(_6,x,y). full_consistency_ok k x y) ls
       acc s =
       (M_success ts,s) /\
     EVERY (\(p,(x,y)). x < ra_state_dim s /\ y < ra_state_dim s
       \/ MEM (p,(x,y)) acc) ts)`)
  CHEAT_TAC;;

let do_alloc1_success = cake_theorem "do_alloc1_success[local]"
  (fun () ->
    `good_ra_state s /\
     EVERY (\((p:num),x,y). x < ra_state_dim s /\ y < ra_state_dim
       s) moves ==>
     (?ls s'.
     do_alloc1 moves scost k s = (M_success ls,s') /\
     good_ra_state s' /\
     is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s') /\
       ra_state_dim
     s' = ra_state_dim s /\ ra_state_node_tag
     s' = ra_state_node_tag s)`)
  CHEAT_TAC;;

let no_clash_colouring_satisfactory =
  cake_theorem "no_clash_colouring_satisfactory"
  (fun () ->
    `no_clash adjls node_tag /\
     LENGTH adjls = LENGTH node_tag /\
     EVERY (\n. ~(n = Stemp) /\ ~(n = Atemp)) node_tag ==>
     colouring_satisfactory
     (\f. if f < LENGTH node_tag then extract_tag (EL f node_tag)
       else 0) adjls`)
  CHEAT_TAC;;

let check_partial_col_same_dom =
  cake_theorem "check_partial_col_same_dom"
  (fun () ->
    `!ls f g t ft.
     (!x. MEM x ls ==> f x = g x) ==>
     check_partial_col f ls t ft = check_partial_col g ls t ft`)
  CHEAT_TAC;;

let check_clash_tree_same_dom = cake_theorem "check_clash_tree_same_dom"
  (fun () ->
    `!ct f g live flive.
     (!x. in_clash_tree ct x \/ x IN domain live ==> f x = g x) ==>
     check_clash_tree f ct live flive =
     check_clash_tree g ct live flive`)
  CHEAT_TAC;;

let opt_split = cake_theorem "opt_split[local]"
  (fun () ->
    `~(a = NONE) <=> a = SOME one`)
  CHEAT_TAC;;

let INJ_IMG_lookup = cake_theorem "INJ_IMG_lookup"
  (fun () ->
    `!x. INJ g UNIV UNIV /\
     domain (gt:1 spt) = IMAGE g (domain ft) ==>
     sptree_lookup (g x) gt = sptree_lookup x ft`)
  CHEAT_TAC;;

let check_partial_col_INJ = cake_theorem "check_partial_col_INJ"
  (fun () ->
    `!ls t ft gt.
     INJ g UNIV UNIV /\
     domain gt = IMAGE g (domain ft) ==>
     (match check_partial_col f ls t ft with
     NONE -> check_partial_col (g o f) ls t gt = NONE | SOME
       (tt,ftt) ->
     (?gtt. check_partial_col (g o f) ls t gt = SOME (tt,gtt) /\
     domain gtt = IMAGE g (domain ftt)))`)
  CHEAT_TAC;;

let check_col_INJ = cake_theorem "check_col_INJ"
  (fun () ->
    `INJ g UNIV UNIV ==>
     (match check_col f (s:1 spt) with
     NONE -> check_col (g o f) s = NONE | SOME (t,ft) ->
     (?gt. check_col (g o f) s = SOME (t,gt) /\
     domain gt = IMAGE g (domain ft)))`)
  CHEAT_TAC;;

let check_clash_tree_INJ = cake_theorem "check_clash_tree_INJ"
  (fun () ->
    `!ct f g live flive glive.
     INJ g UNIV UNIV /\
     domain glive = IMAGE g (domain flive) ==>
     (match check_clash_tree f ct live flive with
     NONE -> check_clash_tree (g o f) ct live glive = NONE | SOME
       (liveout,fliveout) ->
     (?gliveout.
     check_clash_tree (g o f) ct live glive = SOME
       (liveout,gliveout) /\
     domain gliveout = IMAGE g (domain fliveout)))`)
  CHEAT_TAC;;

let neg_first_match_col_correct =
  cake_theorem "neg_first_match_col_correct[local]"
  (fun () ->
    `!x ks s.
     ?res. neg_first_match_col k ks x s = (res,s) /\
     (match res with
       M_failure v -> v = reg_alloc_Subscript | M_success (SOME
         c) -> ~(MEM c ks) /\ k <= c | _7 -> T)`)
  CHEAT_TAC;;

let good_neg_pref_neg_biased_pref =
  cake_theorem "good_neg_pref_neg_biased_pref"
  (fun () ->
    `good_neg_pref k (neg_biased_pref k t)`)
  CHEAT_TAC;;

(* The top-most correctness theorem *)
let do_reg_alloc_correct = cake_theorem "do_reg_alloc_correct"
  (fun () ->
    `!alg scost k moves ct forced fs st ta fa n.
     mk_bij ct = (ta,fa,n) ==> ra_state_adj_ls
     st = REPLICATE n [] ==> ra_state_node_tag
     st = REPLICATE n Atemp ==> ra_state_degrees
     st = REPLICATE n 0 ==> ra_state_dim
     st = n ==> ra_state_simp_wl
     st = [] ==> ra_state_spill_wl
     st = [] ==> ra_state_freeze_wl
     st = [] ==> ra_state_avail_moves_wl
     st = [] ==> ra_state_unavail_moves_wl
     st = [] ==> ra_state_coalesced
     st = REPLICATE n 0 ==> ra_state_move_related
     st = REPLICATE n F ==>
     EVERY (\(x,y). in_clash_tree ct x /\ in_clash_tree ct y)
       forced ==>
     (?spcol st' livein flivein.
       do_reg_alloc alg scost k moves ct forced fs (ta,fa,n) st =
         (M_success spcol,st') /\
       check_clash_tree (sp_default spcol) ct LN LN = SOME
         (livein,flivein) /\
       (!x. in_clash_tree ct x ==>
       x IN domain spcol /\
       (if is_phy_var x then
         sp_default spcol x = x DIV 2 else if is_stack_var x then
         k <= (sp_default spcol x) else
         T)) /\
       (!x. x IN domain spcol ==> in_clash_tree ct x) /\
       EVERY (\(x,y). (sp_default spcol) x = (sp_default spcol) y
         ==> x = y) forced)`)
  CHEAT_TAC;;

(* HOL4 reg_allocProofScript.sml:3455-3457: a proof *)

(* The top-most correctness theorem *)
let reg_alloc_correct = cake_theorem "reg_alloc_correct"
  (fun () ->
    `!alg scost k moves ct forced fs.
     EVERY (\(x,y). in_clash_tree ct x /\ in_clash_tree ct y)
       forced ==>
     (?spcol livein flivein.
       reg_alloc alg scost k moves ct forced fs = M_success spcol
         /\
       check_clash_tree (sp_default spcol) ct LN LN = SOME
         (livein,flivein) /\
       (!x. in_clash_tree ct x ==>
       x IN domain spcol /\
       (if is_phy_var x then
         sp_default spcol x = x DIV 2 else if is_stack_var x then
         k <= (sp_default spcol x) else
         T)) /\
       (!x. x IN domain spcol ==> in_clash_tree ct x) /\
       EVERY (\(x,y). (sp_default spcol) x = (sp_default spcol) y
         ==> x = y) forced)`)
  CHEAT_TAC;;
(* --- --- *)

hol4_only "++" "APPEND";;

cake_hide_consts [];;
