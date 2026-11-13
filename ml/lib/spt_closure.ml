(* ======================================================== *)
(*  spt_closure: ported from HOL4's
    examples/algorithms/spt_closureScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by flat_elim.ml, flat_elimProof.ml,
    word_elim.ml and word_elimProof.ml.  *)
(* ======================================================== *)

needs "lib/sptree.ml";;

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: pred_set arithmetic relation *)

let num_set_tree_union_def,num_set_tree_union_ind = define_rec
  [`num_set_tree_union LN (t2:(1 spt) spt) = (t2:(1 spt) spt)`;
   `num_set_tree_union (LS a) t =
       ((match t with LN -> LS a | LS b -> LS (sptree_union a b)
         | BN t1 t2 -> BS t1 a t2 | BS t1 b t2 -> BS t1 (sptree_union
         a b) t2):(1 spt) spt)`;
   `num_set_tree_union (BN t1 t2) t =
         ((match t with LN -> BN t1 t2 | LS a -> BS t1 a t2 | BN t1'
           t2' ->
                BN (num_set_tree_union t1 t1') (num_set_tree_union
                  t2 t2') | BS t1' a t2' ->
            BS (num_set_tree_union t1 t1') a (num_set_tree_union
              t2 t2')):(1 spt) spt)`;
   `num_set_tree_union (BS t1 a t2) t =
         ((match t with LN -> BS t1 a t2 | LS b -> BS t1
           (sptree_union a b) t2 | BN t1' t2' ->
                BS (num_set_tree_union t1 t1') a (num_set_tree_union
                  t2 t2') | BS t1' b t2' ->
                BS (num_set_tree_union t1 t1') (sptree_union a b)
                    (num_set_tree_union t2 t2')):(1 spt) spt)`];;

let _ = size_thms "spt";;
(* the termination relation that HOL4 gives is
     MEASURE (\(r,t). sptree_size (difference (spt_fold sptree_union LN
       t) r))
   which is not one that HOL Light takes here; the one
   below is what the port found for it *)
(* HOL4 spt_closureScript.sml:90-99: the tactic that proves the
   termination *)
let closure_spt_def,closure_spt_ind = define_wf
  `MEASURE (\(x0,x1). spt_size (spt_size (\x. 0)) x1)`
  [`closure_spt (reachable:1 spt) tree =
     (let sets = inter tree reachable in
     let nodes = spt_fold sptree_union LN sets in
     if subspt nodes reachable then reachable else closure_spt
       (sptree_union reachable nodes) tree)`];;

let is_adjacent_def = new_definition
  `is_adjacent tree x y =
   (?aSetx.
       (sptree_lookup x tree = SOME aSetx) /\ (sptree_lookup y
         aSetx = SOME one))`;;

let is_reachable_def = new_definition
  `is_reachable tree = RTC (is_adjacent tree)`;;
