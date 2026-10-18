(* ======================================================== *)
(*  reg_allocProof: ported from HOL4's
    compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml  *)
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

(* ---
  TODO: These lemmas should be automatically generated for each array
    used!

  Note that they can be stated independently of the precise state
    invariants
  (as shown below)

  The array components we have are:
    adj_ls, node_tag, degrees, coalesced, move_related
  ---*)

(* Rewriting lemmas for array "sub" *)

(* Rewriting lemmas for array "update" *)

(* --- *)

(* The following are also routine theorems, but slightly more
   complicated.
  TODO: can they be stated generically? *)

(* This asserts, e.g. that the monadic map of (\i.node_tag_sub i)
   returns
   success if the input list were all within range *)
(* --- *)

(* --- the main (core) correctness proofs start here --- *)

(* Correctness for the second step *)

(*
  Good negated preference oracle may only inspect, but not touch the
    state
  Moreover, it must always select an element ≥ k not in the input list
*)
let good_neg_pref_def = cake_define
  `good_neg_pref (k:num) pref <=>
   (!n bads s.
     good_ra_state s ==>
     (?res.
     pref n bads s = (M_success res,s) /\
     (match res with
       NONE -> T | SOME c -> ~MEM c bads /\ k <= c)))`;;

(* Almost exactly the same as the FOREACH for Atemps *)

(* --  Random sanity checks that will be needed at some point -- *)

(* Checking that biased_pref satisfies good_pref *)

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

(* HOL4 reg_allocProofScript.sml:814-835: a proof *)

(* HOL4 reg_allocProofScript.sml:879-919: a proof *)

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

(* TODO quick sanity check: move to proof file when done *)
let hide_def = cake_define
  `reg_allocProof_hide x = x`;;
hol4_overload "hide" "reg_allocProof_hide";;

(* From here onwards we stop characterizing s'.adj_ls exactly
   although it could be done
 *)

(* The col needed to get colouring satisfactory can be generated
   from the node tags
   The correctness should be a consequence of no_clash *)
let colouring_satisfactory_def = cake_define
  `colouring_satisfactory col adjls =
   (!x. x < LENGTH adjls ==>
    (!y. y < LENGTH adjls /\ MEM y (EL x adjls) ==>
    col x = col y ==> x = y))`;;

(*TODO: this is in word_allocProof*)

(* The success theorem is separated here *)

(* the correctness theorem for mk_graph *)

(* This precise characterization is needed to show that the forced edges
   correctly force any two to be distinct *)

(* Again, this characterization is only needed for the conventions,
   but not for the correctness theorem *)

(* copied from word-to-stack proof*)

(* Here are the proofs about the "heuristic steps" *)

(* st_ex_PARTITION is similar to st_ex_MAP in that there ought to be
   some generic way to state the following lemmas
*)

(* is_not_coalesced succeeds and preserves state *)

(* As an example, we don't bother fully characterizing
   st_ex_PARTITION, but merely that show it succeeds *)

(* This is currently more general than necessary because it doesn't
   do any coalescing (yet) *)

(* This basically says nothing at the moment *)

(* do_coalesce *)

(* HOL4 reg_allocProofScript.sml:2364-2382: a proof *)

(* do freeze *)

(* do spill *)

(* HOL4 reg_allocProofScript.sml:2862: ML code, not ported *)

(* The top-most correctness theorem *)

(* HOL4 reg_allocProofScript.sml:3455-3457: a proof *)

(* The top-most correctness theorem *)
(* --- --- *)

hol4_only "++" "APPEND";;
