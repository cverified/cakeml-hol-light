(* ======================================================== *)
(*  spt_closure: ported from HOL4's
    examples/algorithms/spt_closureScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

needs "lib/sptree.ml";;
(* HOL4 ancestors outside the port: pred_set arithmetic relation *)

let num_set_tree_union_def = cake_define_list
  [`num_set_tree_union LN t2 = (t2:(1 spt) spt)`;
   `num_set_tree_union (LS a) t =
       (match t with LN -> LS a | LS b -> LS (union a b) | BN t1
         t2 -> BS t1 a t2 | BS t1 b t2 -> BS t1 (union a b) t2)`;
   `num_set_tree_union (BN t1 t2) t =
         (match t with LN -> BN t1 t2 | LS a -> BS t1 a t2 | BN t1'
           t2' ->
                BN (num_set_tree_union t1 t1') (num_set_tree_union
                  t2 t2') | BS t1' a t2' ->
            BS (num_set_tree_union t1 t1') a (num_set_tree_union
              t2 t2'))`;
   `num_set_tree_union (BS t1 a t2) t =
         (match t with LN -> BS t1 a t2 | LS b -> BS t1 (union a b)
           t2 | BN t1' t2' ->
                BS (num_set_tree_union t1 t1') a (num_set_tree_union
                  t2 t2') | BS t1' b t2' ->
                BS (num_set_tree_union t1 t1') (union a b)
                    (num_set_tree_union t2 t2'))`];;

(* HOL4 termination: >> rw[] >> gvs[subspt_domain, SUBSET_DEF] >>
   irule size_diff_less >> gvs[domain_union, domain_spt_fold_union,
   lookup_inter] >> EVERY_CASE_TAC >> gvs[] >> simp[PULL_EXISTS, GSYM
   CONJ_ASSOC] >> goal_assum drule >> goal_assum drule >> simp[] >>
   goal_assum (drule_at Any) >> qexists_tac `k` >> simp[] *)
let closure_spt_def = cake_define_wf
  `MEASURE (\(r,t). size (difference (spt_fold union LN t) r))`
  `closure_spt (reachable:1 spt) tree =
     (let sets = inter tree reachable in
     let nodes = spt_fold union LN sets in
     if subspt nodes reachable then reachable else closure_spt
       (union reachable nodes) tree)`;;
