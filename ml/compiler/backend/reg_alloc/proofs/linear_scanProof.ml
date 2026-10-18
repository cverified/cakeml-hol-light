(* ======================================================== *)
(*  linear_scanProof: ported from HOL4's
    compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml
    A proof theory about linear_scan.ml, with 15 definitions and 188
    theorems.  Needed by word_allocProof.ml.  *)
(* ======================================================== *)

(*
  Proves correctness of the linear-scan register allocator.
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/reg_alloc/linear_scan.ml";;
needs "compiler/backend/reg_alloc/proofs/reg_allocProof.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "lib/sorting.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* HOL4 linear_scanProofScript.sml:12-13: ML code, not ported *)

hol4_overload "++" "otherwise";;

(* TODO: clean up this file: e.g., move things upstream *)

let set_MAP_FST_toAList_eq_domain =
  cake_theorem "set_MAP_FST_toAList_eq_domain"
  (fun () ->
    `!s. set_of_list (MAP FST' (toAList s)) = domain s`)
  CHEAT_TAC;;

let numset_list_insert_FOLDL = cake_theorem "numset_list_insert_FOLDL"
  (fun () ->
    `!l live. linear_scan_numset_list_insert l live = FOLDL (\live x.
  sptree_insert x one live) live l`)
  CHEAT_TAC;;

let numset_list_insert_nottailrec_FOLDR =
  cake_theorem "numset_list_insert_nottailrec_FOLDR"
  (fun () ->
    `!l live. numset_list_insert_nottailrec l live = ITLIST (\x live.
  sptree_insert x one live) l live`)
  CHEAT_TAC;;

let both_numset_list_insert_equal =
  cake_theorem "both_numset_list_insert_equal"
  (fun () ->
    `!l live.
     linear_scan_numset_list_insert l live =
       numset_list_insert_nottailrec (REVERSE l) live`)
  CHEAT_TAC;;

let domain_numset_list_insert = cake_theorem "domain_numset_list_insert"
  (fun () ->
    `!l s. domain (linear_scan_numset_list_insert l s) = set_of_list l
  UNION domain s`)
  CHEAT_TAC;;

(* why breaking encapsulation like this? To get rid of the assumption `wf s` *)
let lookup_insert_id = cake_theorem "lookup_insert_id"
  (fun () ->
    `!x (y:1) s. sptree_lookup x s = SOME one ==> s = sptree_insert x
  one s`)
  CHEAT_TAC;;

let numset_list_insert_FILTER = cake_theorem "numset_list_insert_FILTER"
  (fun () ->
    `!l live.
     linear_scan_numset_list_insert (FILTER (\x. sptree_lookup x
       live = NONE) l) live =
     linear_scan_numset_list_insert l live`)
  CHEAT_TAC;;

let linear_scanProof_domain_numset_list_delete =
  cake_theorem "domain_numset_list_delete"
  (fun () ->
    `!l s. domain (numset_list_delete l s) = (domain s) DIFF
  (set_of_list l)`)
  CHEAT_TAC;;

let check_partial_col_success_INJ_lemma =
  cake_theorem "check_partial_col_success_INJ_lemma"
  (fun () ->
    `!l live flive f.
     domain flive = IMAGE f (domain live) /\
     INJ f (domain live) UNIV /\
     check_partial_col f l live flive = SOME (live',flive') ==>
     INJ f (set_of_list l UNION domain live) UNIV`)
  CHEAT_TAC;;

let check_partial_col_success_INJ =
  cake_theorem "check_partial_col_success_INJ"
  (fun () ->
    `!l live flive f.
     domain flive = IMAGE f (domain live) /\
     INJ f (domain live) UNIV /\
     check_partial_col f l live flive = SOME (live',flive') ==>
     INJ f (set_of_list l UNION domain live) UNIV /\
     INJ f (domain live') UNIV`)
  CHEAT_TAC;;

let check_partial_col_input_monotone =
  cake_theorem "check_partial_col_input_monotone"
  (fun () ->
    `!f live1 flive1 live2 flive2 l v.
     IMAGE f (domain live1) = domain flive1 /\ IMAGE f (domain
       live2) = domain flive2 ==>
     domain live1 SUBSET domain live2 ==>
     INJ f (domain live2) UNIV ==>
     check_partial_col f l live2 flive2 = SOME v ==>
     (?livein1 flivein1. check_partial_col f l live1 flive1 =
       SOME (livein1,flivein1))`)
  CHEAT_TAC;;

let numset_list_delete_IMAGE = cake_theorem "numset_list_delete_IMAGE"
  (fun () ->
    `!f l live flive v.
     domain flive = IMAGE f (domain live) ==>
     INJ f (domain live) UNIV ==>
     check_partial_col f l live flive = SOME v ==>
     domain (numset_list_delete (MAP f l) flive) = IMAGE f
       (domain (numset_list_delete l live))`)
  CHEAT_TAC;;

let check_partial_col_IMAGE = cake_theorem "check_partial_col_IMAGE"
  (fun () ->
    `!f l live flive live' flive'.
     (domain flive) = IMAGE f (domain live) ==>
     check_partial_col f l live flive = SOME (live',flive') ==>
     (domain flive') = IMAGE f (domain live')`)
  CHEAT_TAC;;

let branch_domain = cake_theorem "branch_domain"
  (fun () ->
    `!(live1:1 spt) (live2:1 spt).
     set_of_list (MAP FST (toAList (difference live2 live1)))
       UNION domain live1 = domain live1 UNION domain live2`)
  CHEAT_TAC;;

let check_partial_col_branch_domain =
  cake_theorem "check_partial_col_branch_domain"
  (fun () ->
    `!(live1:1 spt) (live2:1 spt) flive1 liveout fliveout.
     check_partial_col f (MAP FST (toAList (difference live2
       live1))) live1 flive1 = SOME (liveout,fliveout) ==>
     domain liveout = domain live1 UNION domain live2`)
  CHEAT_TAC;;


let check_partial_col_branch_comm =
  cake_theorem "check_partial_col_branch_comm"
  (fun () ->
    `!f live1 flive1 live2 flive2 a b.
     INJ f (domain live1) UNIV ==>
     domain flive1 = IMAGE f (domain live1) /\ domain flive2 =
       IMAGE f (domain live2) ==>
     check_partial_col f (MAP FST (toAList (difference live2
       live1))) live1 flive1 = SOME (a,b) ==>
     (?c d. check_partial_col f (MAP FST (toAList (difference
       live1 live2))) live2 flive2 = SOME (c,d))`)
  CHEAT_TAC;;

let check_partial_col_list_monotone =
  cake_theorem "check_partial_col_list_monotone"
  (fun () ->
    `!f live flive (s1:1 spt) (s2:1 spt) a b.
     domain flive = IMAGE f (domain live) ==>
     INJ f (domain live) UNIV ==>
     domain s1 SUBSET domain s2 ==>
     check_partial_col f (MAP FST (toAList s2)) live flive = SOME
       (a,b) ==>
     (?c d. check_partial_col f (MAP FST (toAList s1)) live flive
       = SOME (c,d))`)
  CHEAT_TAC;;

let check_live_tree_success = cake_theorem "check_live_tree_success"
  (fun () ->
    `!lt live flive live' flive' f.
     domain flive = IMAGE f (domain live) /\
     INJ f (domain live) UNIV /\
     check_live_tree f lt live flive = SOME (live',flive') ==>
     domain flive' = IMAGE f (domain live') /\
     INJ f (domain live') UNIV`)
  CHEAT_TAC;;

let ALL_DISTINCT_INJ_MAP = cake_theorem "ALL_DISTINCT_INJ_MAP"
  (fun () ->
    `!f l. ALL_DISTINCT (MAP f l) ==> INJ f (set_of_list l) UNIV`)
  CHEAT_TAC;;

let check_col_output = cake_theorem "check_col_output"
  (fun () ->
    `!f live live' flive'.
     check_col f live = SOME (live',flive') ==>
     domain flive' = IMAGE f (domain live') /\
     INJ f (domain live') UNIV`)
  CHEAT_TAC;;

let check_col_success = cake_theorem "check_col_success"
  (fun () ->
    `!f live.
     INJ f (domain live) UNIV ==>
     (?flive. check_col f live = SOME (live,flive))`)
  CHEAT_TAC;;

let check_clash_tree_output = cake_theorem "check_clash_tree_output"
  (fun () ->
    `!f ct live flive livein flivein.
     domain flive = IMAGE f (domain live) /\
     INJ f (domain live) UNIV /\
     check_clash_tree f ct live flive = SOME (livein,flivein) ==>
     domain flivein = IMAGE f (domain livein) /\
     INJ f (domain livein) UNIV`)
  CHEAT_TAC;;

let get_live_tree_correct_lemma =
  cake_theorem "get_live_tree_correct_lemma"
  (fun () ->
    `!f live flive live' flive' ct livein' flivein'.
     IMAGE f (domain live) = domain flive /\ IMAGE f (domain live')
       = domain flive' ==>
     INJ f (domain live') UNIV ==>
     domain live SUBSET domain live' ==>
     check_live_tree f (get_live_tree ct) live' flive' = SOME
       (livein',flivein') ==>
     (?livein flivein. check_clash_tree f ct live flive = SOME
       (livein,flivein) /\
     domain livein SUBSET domain livein')`)
  CHEAT_TAC;;

let get_live_tree_correct = cake_theorem "get_live_tree_correct"
  (fun () ->
    `!f live flive ct livein flivein.
     IMAGE f (domain live) = domain flive ==>
     INJ f (domain live) UNIV ==>
     check_live_tree f (get_live_tree ct) live flive = SOME
       (livein,flivein) ==>
     (?livein' flivein'. check_clash_tree f ct live flive = SOME
       (livein',flivein'))`)
  CHEAT_TAC;;

let get_live_tree_correct_LN = cake_theorem "get_live_tree_correct_LN"
  (fun () ->
    `!f ct livein flivein.
     check_live_tree f (get_live_tree ct) LN LN = SOME
       (livein,flivein) ==>
     (?livein' flivein'. check_clash_tree f ct LN LN = SOME
       (livein',flivein'))`)
  CHEAT_TAC;;

let check_partial_col_numset_list_insert =
  cake_theorem "check_partial_col_numset_list_insert"
  (fun () ->
    `!f l live flive liveout fliveout.
     check_partial_col f l live flive = SOME (liveout,fliveout) ==>
     liveout = linear_scan_numset_list_insert l live`)
  CHEAT_TAC;;

let check_live_tree_eq_get_live_backward =
  cake_theorem "check_live_tree_eq_get_live_backward"
  (fun () ->
    `!f lt live flive liveout fliveout.
     check_live_tree f lt live flive = SOME (liveout,fliveout) ==>
     liveout = get_live_backward lt live`)
  CHEAT_TAC;;

let fix_domination_fixes_domination =
  cake_theorem "fix_domination_fixes_domination"
  (fun () ->
    `!lt. domain (get_live_backward (fix_domination lt) LN) = EMPTY`)
  CHEAT_TAC;;

let fix_domination_check_live_tree =
  cake_theorem "fix_domination_check_live_tree"
  (fun () ->
    `!f lt liveout fliveout.
     check_live_tree f (fix_domination lt) LN LN = SOME
       (liveout,fliveout) ==>
     (?liveout' fliveout'. check_live_tree f lt LN LN = SOME
       (liveout',fliveout'))`)
  CHEAT_TAC;;

let size_of_live_tree_positive =
  cake_theorem "size_of_live_tree_positive"
  (fun () ->
    `!lt. 0 <= size_of_live_tree lt`)
  CHEAT_TAC;;

let check_number_property_strong_monotone_weak =
  cake_theorem "check_number_property_strong_monotone_weak"
  (fun () ->
    `!P Q lt n live.
     (!n' live'. P n' live' ==> Q n' live') /\
     check_number_property_strong P lt n live ==>
     check_number_property_strong Q lt n live`)
  CHEAT_TAC;;


let check_number_property_strong_monotone =
  cake_theorem "check_number_property_strong_monotone"
  (fun () ->
    `!P Q lt n live.
     (!n' live'. (n - size_of_live_tree lt) <= n' /\ P n' live' ==>
       Q n' live') /\
     check_number_property_strong P lt n live ==>
     check_number_property_strong Q lt n live`)
  CHEAT_TAC;;

let check_number_property_strong_end =
  cake_theorem "check_number_property_strong_end"
  (fun () ->
    `!P lt n live.
     check_number_property_strong P lt n live ==>
     P (n - size_of_live_tree lt) (get_live_backward lt live)`)
  CHEAT_TAC;;

let check_number_property_monotone_weak =
  cake_theorem "check_number_property_monotone_weak"
  (fun () ->
    `!P Q lt n live.
     (!n' live'. P n' live' ==> Q n' live') /\
     check_number_property P lt n live ==>
     check_number_property Q lt n live`)
  CHEAT_TAC;;


let lookup_numset_list_add_if = cake_theorem "lookup_numset_list_add_if"
  (fun () ->
    `!r l v s.
     sptree_lookup r (numset_list_add_if l v s P) =
        (if MEM r l then
          match sptree_lookup r s with (SOME vr) ->
            (if P v vr then SOME v else SOME vr) | NONE ->
            SOME v else
          sptree_lookup r s)`)
  CHEAT_TAC;;


let lookup_numset_list_add_if_lt =
  cake_theorem "lookup_numset_list_add_if_lt"
  (fun () ->
    `!r l v s.
     sptree_lookup r (numset_list_add_if_lt l v s) =
        (if MEM r l then
          match sptree_lookup r s with (SOME vr) ->
            (if v <= vr then SOME v else SOME vr) | NONE ->
            SOME v else
          sptree_lookup r s)`)
  CHEAT_TAC;;

let lookup_numset_list_add_if_gt =
  cake_theorem "lookup_numset_list_add_if_gt"
  (fun () ->
    `!r l v s.
     sptree_lookup r (numset_list_add_if_gt l v s) =
        (if MEM r l then
          match sptree_lookup r s with (SOME vr) ->
            (if vr <= v then SOME v else SOME vr) | NONE ->
            SOME v else
          sptree_lookup r s)`)
  CHEAT_TAC;;

let domain_numset_list_add_if = cake_theorem "domain_numset_list_add_if"
  (fun () ->
    `!l v s P. domain (numset_list_add_if l v s P) = set_of_list l
  UNION domain s`)
  CHEAT_TAC;;

let domain_numset_list_add_if_lt =
  cake_theorem "domain_numset_list_add_if_lt"
  (fun () ->
    `!l v s. domain (numset_list_add_if_lt l v s) = set_of_list l
  UNION domain s`)
  CHEAT_TAC;;

let domain_numset_list_add_if_gt =
  cake_theorem "domain_numset_list_add_if_gt"
  (fun () ->
    `!l v s. domain (numset_list_add_if_gt l v s) = set_of_list l
  UNION domain s`)
  CHEAT_TAC;;

let lookup_numset_list_delete = cake_theorem "lookup_numset_list_delete"
  (fun () ->
    `!l s x. sptree_lookup x (numset_list_delete l s) = (if MEM x l
  then NONE else sptree_lookup x s)`)
  CHEAT_TAC;;

let get_intervals_nout = cake_theorem "get_intervals_nout"
  (fun () ->
    `!lt n_in beg_in end_in n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals lt n_in beg_in end_in
       ==>
     n_out = n_in - (size_of_live_tree lt)`)
  CHEAT_TAC;;

let get_intervals_withlive_nout =
  cake_theorem "get_intervals_withlive_nout"
  (fun () ->
    `!lt n_in beg_in end_in n_out beg_out end_out live.
     (n_out,beg_out,end_out) = get_intervals_withlive lt n_in
       beg_in end_in live ==>
     n_out = n_in - (size_of_live_tree lt)`)
  CHEAT_TAC;;


let get_intervals_intend_augment =
  cake_theorem "get_intervals_intend_augment"
  (fun () ->
    `!lt n_in beg_in end_in n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals lt n_in beg_in end_in
       ==>
     (!r v. sptree_lookup r end_in = SOME v ==> (?v'.
       sptree_lookup r end_out = SOME v' /\ v <= v'))`)
  CHEAT_TAC;;

let check_number_property_intend =
  cake_theorem "check_number_property_intend"
  (fun () ->
    `!end_out lt n_in live_in.
     check_number_property (\n (live:1 spt). !r. r IN domain live
       ==> (?v. sptree_lookup r end_out = SOME v /\ n + 1 <= v)) lt n_in
       live_in ==>
     (!r. r IN domain (get_live_backward lt live_in) ==> (?v.
       sptree_lookup r end_out = SOME v /\ n_in - (size_of_live_tree
       lt) <= v))`)
  CHEAT_TAC;;

let get_intervals_live_less_end =
  cake_theorem "get_intervals_live_less_end"
  (fun () ->
    `!lt n_in beg_in end_in live_in n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals lt n_in beg_in end_in
       /\
     (!r. r IN domain live_in ==> (?v. sptree_lookup r end_in =
       SOME v /\ n_in <= v)) ==>
     check_number_property (\n (live:1 spt). !r. r IN domain live
       ==> (?v. sptree_lookup r end_out = SOME v /\ n + 1 <= v)) lt
       n_in live_in`)
  CHEAT_TAC;;

let get_intervals_withlive_intbeg_reduce =
  cake_theorem "get_intervals_withlive_intbeg_reduce"
  (fun () ->
    `!lt n_in beg_in end_in n_out beg_out end_out live.
     (n_out,beg_out,end_out) = get_intervals_withlive lt n_in
       beg_in end_in live /\
     (!r v. sptree_lookup r beg_in = SOME v ==> n_in <= v) ==>
     (!r. option_CASE (sptree_lookup r beg_out) n_out (\x. x) <=
       option_CASE (sptree_lookup r beg_in) n_in (\x. x)) /\
     (!r v. sptree_lookup r beg_out = SOME v ==> n_out <= v)`)
  CHEAT_TAC;;

let get_intervals_withlive_intbeg_nout =
  cake_theorem "get_intervals_withlive_intbeg_nout"
  (fun () ->
    `!lt n_in beg_in end_in n_out beg_out end_out live.
     (n_out,beg_out,end_out) = get_intervals_withlive lt n_in
       beg_in end_in live /\
     (!r v. sptree_lookup r beg_in = SOME v ==> n_in <= v) ==>
     (!r v. sptree_lookup r beg_out = SOME v ==> n_out <= v)`)
  CHEAT_TAC;;

let get_intervals_intbeg_nout = cake_theorem "get_intervals_intbeg_nout"
  (fun () ->
    `!lt n_in beg_in end_in n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals lt n_in beg_in end_in
       /\
     (!r v. sptree_lookup r beg_in = SOME v ==> n_in <= v) ==>
     (!r v. sptree_lookup r beg_out = SOME v ==> n_out <= v)`)
  CHEAT_TAC;;


let get_intervals_withlive_live_intbeg =
  cake_theorem "get_intervals_withlive_live_intbeg"
  (fun () ->
    `!lt n_in beg_in end_in live n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals_withlive lt n_in
       beg_in end_in live /\
     (!r. r IN domain live ==> ~(r IN domain beg_in)) ==>
     (!r. r IN domain (get_live_backward lt live) ==> ~(r IN
       domain beg_out))`)
  CHEAT_TAC;;

let get_intervals_withlive_beg_less_live =
  cake_theorem "get_intervals_withlive_beg_less_live"
  (fun () ->
    `!lt n_in beg_in end_in live_in n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals_withlive lt n_in
       beg_in end_in live_in /\
     (!r v. sptree_lookup r beg_in = SOME v ==> n_in <= v) /\
     (!r. r IN domain live_in ==> ~(r IN domain beg_in)) ==>
     check_number_property_strong (\n (live:1 spt). !r. r IN
       domain live ==> option_CASE (sptree_lookup r beg_out) n_out
       (\x. x) <= n) lt n_in live_in`)
  CHEAT_TAC;;

let get_intervals_withlive_n_eq_get_intervals_n =
  cake_theorem "get_intervals_withlive_n_eq_get_intervals_n"
  (fun () ->
    `!lt n beg end beg' end' n1 beg1 end1 n2 beg2 end2 live.
     (n1,beg1,end1) = get_intervals lt n beg end /\
     (n2,beg2,end2) = get_intervals_withlive lt n beg' end' live
       ==>
     n1 = n2`)
  CHEAT_TAC;;

let get_intervals_withlive_end_eq_get_intervals_end =
  cake_theorem "get_intervals_withlive_end_eq_get_intervals_end"
  (fun () ->
    `!lt n beg beg' end n1 beg1 end1 n2 beg2 end2 live.
     (n1,beg1,end1) = get_intervals lt n beg end /\
     (n2,beg2,end2) = get_intervals_withlive lt n beg' end live ==>
     end1 = end2`)
  CHEAT_TAC;;

let get_intervals_withlive_beg_eq_get_intervals_beg_when_some =
  cake_theorem
    "get_intervals_withlive_beg_eq_get_intervals_beg_when_some"
  (fun () ->
    `!lt n beg beg' end n1 beg1 end1 n2 beg2 end2 live.
     (n1,beg1,end1) = get_intervals lt n beg end /\
     (n2,beg2,end2) = get_intervals_withlive lt n beg' end live /\
     (!r v. sptree_lookup r beg = SOME v ==> n <= v) /\
     (!r v. sptree_lookup r beg' = SOME v ==> n <= v) /\
     (!r v1 v2. sptree_lookup r beg = SOME v1 /\ sptree_lookup r
       beg' = SOME v2 ==> v1 = v2) ==>
     (!r v1 v2. sptree_lookup r beg1 = SOME v1 /\ sptree_lookup r
       beg2 = SOME v2 ==> v1 = v2)`)
  CHEAT_TAC;;

let get_intervals_withlive_beg_subset_get_intervals_beg =
  cake_theorem "get_intervals_withlive_beg_subset_get_intervals_beg"
  (fun () ->
    `!lt n beg_in1 beg_in2 end n1 beg_out1 end1 n2 beg_out2 end2 live.
     (n1,beg_out1,end1) = get_intervals_withlive lt n beg_in1 end
       live /\
     (n2,beg_out2,end2) = get_intervals lt n beg_in2 end /\
     domain beg_in1 SUBSET domain beg_in2 ==>
     domain beg_out1 SUBSET domain beg_out2`)
  CHEAT_TAC;;

let get_intervals_beg_subset_registers =
  cake_theorem "get_intervals_beg_subset_registers"
  (fun () ->
    `!lt n_in beg_in end_in n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals lt n_in beg_in end_in
       ==>
     domain beg_out SUBSET (domain beg_in UNION
       (live_tree_registers lt))`)
  CHEAT_TAC;;

(* This theorem looks like lipschitz continuity: it says something like f(x+y) <= f(x)+y *)
let get_intervals_withlive_beg_lipschitz =
  cake_theorem "get_intervals_withlive_beg_lipschitz"
  (fun () ->
    `!lt n1 beg1 end1 live n2 beg2 end2 (s:int spt) nout1 begout1
  endout1 nout2 begout2 endout2.
     (nout1,begout1,endout1) = get_intervals_withlive lt n1 beg1
       end1 live /\
     (nout2,begout2,endout2) = get_intervals_withlive lt n2 beg2
       end2 live /\
     domain beg2 SUBSET domain beg1 UNION domain s ==>
     domain begout2 SUBSET domain begout1 UNION domain s`)
  CHEAT_TAC;;

let get_intervals_withlive_registers_subset_beg =
  cake_theorem "get_intervals_withlive_registers_subset_beg"
  (fun () ->
    `!lt n_in beg_in end_in n_out beg_out end_out live_in.
     domain end_in SUBSET domain beg_in UNION domain live_in /\
     (n_out,beg_out,end_out) = get_intervals_withlive lt n_in
       beg_in end_in live_in ==>
     domain end_out SUBSET domain beg_out UNION domain
       (get_live_backward lt live_in)`)
  CHEAT_TAC;;

let get_intervals_withlive_live_tree_registers_subset_endout =
  cake_theorem
    "get_intervals_withlive_live_tree_registers_subset_endout"
  (fun () ->
    `!lt n_in beg_in end_in live_in n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals_withlive lt n_in
       beg_in end_in live_in ==>
     domain end_in UNION live_tree_registers lt SUBSET domain
       end_out`)
  CHEAT_TAC;;

let get_intervals_domain_eq_live_tree_registers =
  cake_theorem "get_intervals_domain_eq_live_tree_registers"
  (fun () ->
    `!lt n beg end.
     (n,beg,end) = get_intervals (fix_domination lt) 0 LN LN ==>
     domain beg = live_tree_registers (fix_domination lt) /\
     domain end = live_tree_registers (fix_domination lt)`)
  CHEAT_TAC;;

let get_intervals_withlive_domain_eq_live_tree_registers =
  cake_theorem "get_intervals_withlive_domain_eq_live_tree_registers"
  (fun () ->
    `!lt n beg end.
     (n,beg,end) = get_intervals_withlive (fix_domination lt) 0 LN
       LN LN ==>
     domain beg = live_tree_registers (fix_domination lt) /\
     domain end = live_tree_registers (fix_domination lt)`)
  CHEAT_TAC;;

let get_intervals_withlive_beg_eq_get_intervals_beg =
  cake_theorem "get_intervals_withlive_beg_eq_get_intervals_beg"
  (fun () ->
    `!lt n beg end n' beg' end'.
     (n,beg,end) = get_intervals_withlive (fix_domination lt) 0 LN
       LN LN /\
     (n',beg',end') = get_intervals (fix_domination lt) 0 LN LN ==>
     (!(r:num). sptree_lookup r beg = sptree_lookup r beg')`)
  CHEAT_TAC;;

let get_intervals_end_increase =
  cake_theorem "get_intervals_end_increase"
  (fun () ->
    `!lt n_in beg_in end_in n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals lt n_in beg_in end_in
       ==>
     domain end_in SUBSET domain end_out`)
  CHEAT_TAC;;

let check_number_property_subset_endout =
  cake_theorem "check_number_property_subset_endout"
  (fun () ->
    `!lt n_in beg_in end_in live_in n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals lt n_in beg_in end_in
       /\
     domain live_in SUBSET domain end_in ==>
     check_number_property_strong (\n (live:1 spt). domain live
       SUBSET domain end_out) lt n_in live_in`)
  CHEAT_TAC;;

let get_intervals_beg_less_live =
  cake_theorem "get_intervals_beg_less_live"
  (fun () ->
    `!lt live_in n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals (fix_domination lt) 0
       LN LN ==>
     check_number_property_strong (\n (live:1 spt). !r. r IN
       domain live ==> option_CASE (sptree_lookup r beg_out) n_out
       (\x. x) <= n) (fix_domination lt) 0 LN`)
  CHEAT_TAC;;

let get_intervals_intbeg_reduce =
  cake_theorem "get_intervals_intbeg_reduce"
  (fun () ->
    `!lt n_in beg_in end_in n_out beg_out end_out live.
     (n_out,beg_out,end_out) = get_intervals lt n_in beg_in end_in
       /\
     (!r v. sptree_lookup r beg_in = SOME v ==> n_in <= v) ==>
     (!r. option_CASE (sptree_lookup r beg_out) n_out (\x. x) <=
       option_CASE (sptree_lookup r beg_in) n_in (\x. x)) /\
     (!r v. sptree_lookup r beg_out = SOME v ==> n_out <= v)`)
  CHEAT_TAC;;

let check_startlive_prop_monotone =
  cake_theorem "check_startlive_prop_monotone"
  (fun () ->
    `!lt beg ndef end beg' ndef' end' n_in.
     (!r. option_CASE (sptree_lookup r beg') ndef' (\x. x) <=
       option_CASE (sptree_lookup r beg) ndef (\x. x)) /\
     (!r v. sptree_lookup r end = SOME v ==> (?v'. sptree_lookup r
       end' = SOME v' /\ v <= v')) /\
     check_startlive_prop lt n_in beg end ndef ==>
     check_startlive_prop lt n_in beg' end' ndef'`)
  CHEAT_TAC;;

let check_startlive_prop_augment_ndef =
  cake_theorem "check_startlive_prop_augment_ndef"
  (fun () ->
    `!lt n_in beg_out end_out ndef.
     check_startlive_prop lt n_in beg_out end_out ndef /\
     ndef <= ndef' /\
     ndef' <= n_in - size_of_live_tree lt ==>
     check_startlive_prop lt n_in beg_out end_out ndef'`)
  CHEAT_TAC;;

let get_intervals_check_startlive_prop =
  cake_theorem "get_intervals_check_startlive_prop"
  (fun () ->
    `!lt n_in beg_in end_in n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals lt n_in beg_in end_in
       /\
     (!r v. sptree_lookup r beg_in = SOME v ==> n_in <= v) ==>
     check_startlive_prop lt n_in beg_out end_out n_out`)
  CHEAT_TAC;;

let exists_point_inside_interval_interval_intersect =
  cake_theorem "exists_point_inside_interval_interval_intersect"
  (fun () ->
    `!l1 r1 l2 r2 v.
     point_inside_interval (l1,r1) v /\ point_inside_interval
       (l2,r2) v ==>
     interval_intersect (l1,r1) (l2,r2)`)
  CHEAT_TAC;;

let check_intervals_check_live_tree_lemma =
  cake_theorem "check_intervals_check_live_tree_lemma"
  (fun () ->
    `!lt n_in beg_out end_out f live flive.
     check_startlive_prop lt n_in beg_out end_out (n_in -
       size_of_live_tree lt) /\
     check_number_property_strong (\n (live':1 spt). !r. r IN
       domain live' ==> option_CASE (sptree_lookup r beg_out) n_out (\x.
       x) <= n) lt n_in live /\
     check_number_property (\n (live':1 spt). !r. r IN domain live'
       ==> (?v. sptree_lookup r end_out = SOME v /\ n + 1 <= v)) lt n_in
       live /\
     check_number_property_strong (\n (live':1 spt). domain live'
       SUBSET domain end_out) lt n_in live /\
     domain beg_out = domain end_out /\
     live_tree_registers lt SUBSET domain end_out /\
     check_intervals f beg_out end_out /\
     domain flive = IMAGE f (domain live) /\
     INJ f (domain live) UNIV ==>
     (?liveout fliveout. check_live_tree f lt live flive = SOME
       (liveout,fliveout))`)
  CHEAT_TAC;;

let check_intervals_check_live_tree =
  cake_theorem "check_intervals_check_live_tree"
  (fun () ->
    `!lt n_out beg_out end_out f.
     (n_out,beg_out,end_out) = get_intervals (fix_domination lt) 0
       LN LN /\
     check_intervals f beg_out end_out ==>
     (?liveout fliveout. check_live_tree f (fix_domination lt) LN
       LN = SOME (liveout,fliveout))`)
  CHEAT_TAC;;

let get_intervals_ct_aux_live = cake_theorem "get_intervals_ct_aux_live"
  (fun () ->
    `!ct n_in beg_in end_in live_in live_in' n_out beg_out end_out
  live_out.
     domain live_in = domain live_in' /\
     (n_out,beg_out,end_out,live_out) = get_intervals_ct_aux ct
       n_in beg_in end_in live_in ==>
     domain live_out = domain (get_live_backward (get_live_tree
       ct) live_in')`)
  CHEAT_TAC;;

let get_intervals_ct_aux_int = cake_theorem "get_intervals_ct_aux_int"
  (fun () ->
    `!ct n_in beg_in end_in live_in n_out beg_out end_out live_out.
     (n_out,beg_out,end_out,live_out) = get_intervals_ct_aux ct
       n_in beg_in end_in live_in ==>
     (n_out,beg_out,end_out) = get_intervals (get_live_tree ct)
       n_in beg_in end_in`)
  CHEAT_TAC;;

let get_intervals_ct_eq = cake_theorem "get_intervals_ct_eq"
  (fun () ->
    `!ct int_beg1 int_beg2 int_end1 int_end2 n1 n2.
     (n1,int_beg1,int_end1) = get_intervals_ct ct /\
     (n2,int_beg2,int_end2) = get_intervals (fix_domination
       (get_live_tree ct)) 0 LN LN ==>
     (!r. sptree_lookup r int_beg1 = sptree_lookup r int_beg2) /\
     (!r. sptree_lookup r int_end1 = sptree_lookup r int_end2)`)
  CHEAT_TAC;;

let colors_sub_eqn = cake_theorem "colors_sub_eqn[simp]"
  (fun () ->
    `colors_sub n s =
     (if n < LENGTH (linear_scan_hidden_state_colors s) then
     (M_success (EL n (linear_scan_hidden_state_colors s)),s) else
     (M_failure (reg_alloc_Subscript),s))`)
  CHEAT_TAC;;

let update_colors_eqn = cake_theorem "update_colors_eqn[simp]"
  (fun () ->
    `update_colors n t s =
     (if n < LENGTH (linear_scan_hidden_state_colors s) then
      (M_success one,linear_scan_hidden_state_colors_fupd (K
        (LUPDATE t n (linear_scan_hidden_state_colors s))) s) else
      (M_failure (reg_alloc_Subscript),s))`)
  CHEAT_TAC;;

let int_beg_sub_eqn = cake_theorem "int_beg_sub_eqn[simp]"
  (fun () ->
    `int_beg_sub n s =
     (if n < LENGTH (linear_scan_hidden_state_int_beg s) then
      (M_success (EL n (linear_scan_hidden_state_int_beg s)),s)
        else
      (M_failure (reg_alloc_Subscript),s))`)
  CHEAT_TAC;;

let update_int_beg_eqn = cake_theorem "update_int_beg_eqn[simp]"
  (fun () ->
    `update_int_beg n t s =
     (if n < LENGTH (linear_scan_hidden_state_int_beg s) then
       (M_success one,linear_scan_hidden_state_int_beg_fupd (K
         (LUPDATE t n (linear_scan_hidden_state_int_beg s))) s) else
       (M_failure (reg_alloc_Subscript),s))`)
  CHEAT_TAC;;

let int_end_sub_eqn = cake_theorem "int_end_sub_eqn[simp]"
  (fun () ->
    `int_end_sub n s =
     (if n < LENGTH (linear_scan_hidden_state_int_end s) then
      (M_success (EL n (linear_scan_hidden_state_int_end s)),s)
        else
      (M_failure (reg_alloc_Subscript),s))`)
  CHEAT_TAC;;

let update_int_end_eqn = cake_theorem "update_int_end_eqn[simp]"
  (fun () ->
    `update_int_end n t s =
     (if n < LENGTH (linear_scan_hidden_state_int_end s) then
       (M_success one,linear_scan_hidden_state_int_end_fupd (K
         (LUPDATE t n (linear_scan_hidden_state_int_end s))) s) else
       (M_failure (reg_alloc_Subscript),s))`)
  CHEAT_TAC;;

let sorted_regs_sub_eqn = cake_theorem "sorted_regs_sub_eqn[simp]"
  (fun () ->
    `sorted_regs_sub n s =
     (if n < LENGTH (linear_scan_hidden_state_sorted_regs s) then
      (M_success (EL n (linear_scan_hidden_state_sorted_regs s)),s)
        else
      (M_failure (reg_alloc_Subscript),s))`)
  CHEAT_TAC;;

let update_sorted_regs_eqn = cake_theorem "update_sorted_regs_eqn[simp]"
  (fun () ->
    `update_sorted_regs n t s =
     (if n < LENGTH (linear_scan_hidden_state_sorted_regs s) then
       (M_success one,linear_scan_hidden_state_sorted_regs_fupd (K
         (LUPDATE t n (linear_scan_hidden_state_sorted_regs s))) s) else
       (M_failure (reg_alloc_Subscript),s))`)
  CHEAT_TAC;;

let sorted_moves_sub_eqn = cake_theorem "sorted_moves_sub_eqn[simp]"
  (fun () ->
    `sorted_moves_sub n s =
     (if n < LENGTH (linear_scan_hidden_state_sorted_moves s) then
      (M_success (EL n (linear_scan_hidden_state_sorted_moves
        s)),s) else
      (M_failure (reg_alloc_Subscript),s))`)
  CHEAT_TAC;;

let update_sorted_moves_eqn =
  cake_theorem "update_sorted_moves_eqn[simp]"
  (fun () ->
    `update_sorted_moves n t s =
     (if n < LENGTH (linear_scan_hidden_state_sorted_moves s) then
       (M_success one,linear_scan_hidden_state_sorted_moves_fupd (K
         (LUPDATE t n (linear_scan_hidden_state_sorted_moves s))) s)
         else
       (M_failure (reg_alloc_Subscript),s))`)
  CHEAT_TAC;;

(* HOL4 linear_scanProofScript.sml:2130: ML code, not ported *)

let lookup_default_id_def = cake_define
  `lookup_default_id s x = option_CASE (sptree_lookup x s) x (\x. x)`;;

let find_reg_exchange_step_def = cake_define
  `find_reg_exchange_step colors r (exch,invexch) =
       (let col1 = EL r colors in
       let fcol1 = r DIV 2 in
       let col2 = lookup_default_id invexch fcol1 in
       let fcol2 = lookup_default_id exch col1 in
       (sptree_insert col1 fcol1 (sptree_insert col2 fcol2
         exch),sptree_insert fcol1 col1 (sptree_insert fcol2 col2
         invexch)))`;;

let find_reg_exchange_FOLDL = cake_theorem "find_reg_exchange_FOLDL"
  (fun () ->
    `!l colors exch invexch sth.
     (!r. MEM r l ==> r < LENGTH (linear_scan_hidden_state_colors
       sth)) ==>
     find_reg_exchange l exch invexch sth = (M_success (FOLDL (\a
       b. find_reg_exchange_step (linear_scan_hidden_state_colors sth)
       b a) (exch,invexch) l),sth)`)
  CHEAT_TAC;;

let lookup_default_id_insert = cake_theorem "lookup_default_id_insert"
  (fun () ->
    `!s k1 k2 v.
     lookup_default_id (sptree_insert k2 v s) k1 = (if k1 = k2
       then v else lookup_default_id s k1)`)
  CHEAT_TAC;;

let id_def = cake_define
  `linear_scanProof_id x = x`;;
hol4_overload "id" "linear_scanProof_id";;

let find_reg_exchange_FOLDR_correct =
  cake_theorem "find_reg_exchange_FOLDR_correct"
  (fun () ->
    `!l colors exch invexch k.
     ALL_DISTINCT (MAP (\r. EL r colors) l) /\
     (!r. MEM r l ==> is_phy_var r) /\
     (exch,invexch) = ITLIST (\a b. find_reg_exchange_step colors a
       b) l (LN,LN) ==>
     ((lookup_default_id exch) o (lookup_default_id invexch) = (\x.
       x) /\ (lookup_default_id invexch) o (lookup_default_id exch) =
       (\x. x)) /\
     (!r. MEM r l ==> lookup_default_id exch (EL r colors) = r DIV
       2) /\
     ((!r. MEM r l ==> (k <= EL r colors <=> k <= r DIV 2)) ==>
      (!c. linear_scanProof_id (k <= c <=> k <= lookup_default_id
        exch c))) /\
     ((!r. MEM r l ==> r DIV 2 < k) ==>
      (!c. k <= c /\ (!r. MEM r l ==> ~(c = EL r colors)) ==> k <=
        lookup_default_id exch c)) /\
     ((!r. MEM r l ==> (k <= EL r colors /\ k <= r DIV 2)) ==>
      (!c. c < k ==> lookup_default_id exch c = c))`)
  CHEAT_TAC;;

let find_reg_exchange_correct = cake_theorem "find_reg_exchange_correct"
  (fun () ->
    `!l sth k.
     ALL_DISTINCT (MAP (\r. EL r (linear_scan_hidden_state_colors
       sth)) l) /\
     (!r. MEM r l ==> is_phy_var r) /\
     (!r. MEM r l ==> r < LENGTH (linear_scan_hidden_state_colors
       sth)) ==>
     (?exch invexch. find_reg_exchange l LN LN sth = (M_success
       (exch,invexch),sth) /\
     ((lookup_default_id exch) o (lookup_default_id invexch) = (\x.
       x) /\ (lookup_default_id invexch) o (lookup_default_id exch) =
       (\x. x)) /\
     (!r. MEM r l ==> lookup_default_id exch (EL r
       (linear_scan_hidden_state_colors sth)) = r DIV 2) /\
     ((!r. MEM r l ==> (k <= EL r (linear_scan_hidden_state_colors
       sth) <=> k <= r DIV 2)) ==>
      (!c. linear_scanProof_id (k <= c <=> k <= lookup_default_id
        exch c))) /\
     ((!r. MEM r l ==> r DIV 2 < k) ==>
      (!c. k <= c /\ (!r. MEM r l ==> ~(c = EL r
        (linear_scan_hidden_state_colors sth))) ==> k <=
        lookup_default_id exch c)) /\
     ((!r. MEM r l ==> (k <= EL r (linear_scan_hidden_state_colors
       sth) /\ k <= r DIV 2)) ==>
      (!c. c < k ==> lookup_default_id exch c = c)))`)
  CHEAT_TAC;;

let MAP_colors_eq_lemma = cake_theorem "MAP_colors_eq_lemma"
  (fun () ->
    `!sth n f.
     n <= LENGTH (linear_scan_hidden_state_colors sth) ==>
     (?sthout. (M_success one,sthout) = MAP_colors f n sth /\
     LENGTH (linear_scan_hidden_state_colors sth) = LENGTH
       (linear_scan_hidden_state_colors sthout) /\
       linear_scan_hidden_state_int_beg
     sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout =
       linear_scan_hidden_state_int_end sth /\
     (!n'. n' < n ==> EL n' (linear_scan_hidden_state_colors
       sthout) = f (EL n' (linear_scan_hidden_state_colors sth))) /\
     (!n'. n <= n' ==> EL n' (linear_scan_hidden_state_colors
       sthout) = EL n' (linear_scan_hidden_state_colors sth)))`)
  CHEAT_TAC;;

let MAP_colors_eq = cake_theorem "MAP_colors_eq"
  (fun () ->
    `!sth f.
     ?sthout. (M_success one,sthout) = MAP_colors f (LENGTH
       (linear_scan_hidden_state_colors sth)) sth /\
     (!n. n < LENGTH (linear_scan_hidden_state_colors sth) ==> EL n
       (linear_scan_hidden_state_colors sthout) = f (EL n
       (linear_scan_hidden_state_colors sth))) /\
     LENGTH (linear_scan_hidden_state_colors sth) = LENGTH
       (linear_scan_hidden_state_colors sthout) /\
       linear_scan_hidden_state_int_beg
     sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout =
       linear_scan_hidden_state_int_end sth`)
  CHEAT_TAC;;

let apply_reg_exchange_correct =
  cake_theorem "apply_reg_exchange_correct"
  (fun () ->
    `!l sth k.
     ALL_DISTINCT (MAP (\r. EL r (linear_scan_hidden_state_colors
       sth)) l) /\
     (!r. MEM r l ==> is_phy_var r) /\
     (!r. MEM r l ==> r < LENGTH (linear_scan_hidden_state_colors
       sth)) ==>
     (?sthout. (M_success one,sthout) = apply_reg_exchange l sth /\
     LENGTH (linear_scan_hidden_state_colors sthout) = LENGTH
       (linear_scan_hidden_state_colors sth) /\
       linear_scan_hidden_state_int_beg
     sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout =
       linear_scan_hidden_state_int_end sth /\
     (!r1 r2. r1 < LENGTH (linear_scan_hidden_state_colors sth) /\
       r2 < LENGTH (linear_scan_hidden_state_colors sth) ==> EL r1
       (linear_scan_hidden_state_colors sthout) = EL r2
       (linear_scan_hidden_state_colors sthout) ==> EL r1
       (linear_scan_hidden_state_colors sth) = EL r2
       (linear_scan_hidden_state_colors sth)) /\
     (!r. MEM r l ==> EL r (linear_scan_hidden_state_colors sthout)
       = r DIV 2) /\
     ((!r. MEM r l ==> (k <= EL r (linear_scan_hidden_state_colors
       sth) <=> k <= r DIV 2)) ==>
      (!r. r < LENGTH (linear_scan_hidden_state_colors sth) ==> (k
        <= EL r (linear_scan_hidden_state_colors sth) <=> k <= EL r
        (linear_scan_hidden_state_colors sthout)))) /\
     ((!r. MEM r l ==> r DIV 2 < k) ==>
      (!r. r < LENGTH (linear_scan_hidden_state_colors sth) /\ k <=
        EL r (linear_scan_hidden_state_colors sth) /\ (!r'. MEM r' l ==>
        ~(EL r (linear_scan_hidden_state_colors sth) = EL r'
        (linear_scan_hidden_state_colors sth))) ==> k <= EL r
        (linear_scan_hidden_state_colors sthout))) /\
     ((!r. MEM r l ==> (k <= EL r (linear_scan_hidden_state_colors
       sth) /\ k <= r DIV 2)) ==>
      (!r. r < LENGTH (linear_scan_hidden_state_colors sth) /\ EL
        r (linear_scan_hidden_state_colors sth) < k ==> EL r
        (linear_scan_hidden_state_colors sthout) = EL r
        (linear_scan_hidden_state_colors sth))))`)
  CHEAT_TAC;;

let less_FST_def = cake_define
  `less_FST (x:int#num) y = (FST x <= FST y)`;;

let transitive_less_FST = cake_theorem "transitive_less_FST"
  (fun () ->
    `transitive less_FST`)
  CHEAT_TAC;;

let good_linear_scan_state_def = cake_define
  `good_linear_scan_state st sth l (pos:int) forced mincol = (
       LENGTH (linear_scan_hidden_state_int_beg sth) = LENGTH
         (linear_scan_hidden_state_colors sth) /\ LENGTH
         (linear_scan_hidden_state_int_end sth) = LENGTH
         (linear_scan_hidden_state_colors sth) /\
       ALL_DISTINCT (linear_scan_state_colorpool st ++ MAP (\(e,r).
         EL r (linear_scan_hidden_state_colors sth))
         (linear_scan_state_active st)) /\
       EVERY (\r. r < LENGTH (linear_scan_hidden_state_colors sth)) l
         /\
       EVERY (\r. EL r (linear_scan_hidden_state_colors sth) <
         linear_scan_state_stacknum st) l /\
       domain (linear_scan_state_phyregs st) = {EL r
         (linear_scan_hidden_state_colors sth) | r | MEM r l /\
         is_phy_var r /\ EL r (linear_scan_hidden_state_colors sth) <
         linear_scan_state_colormax st} /\
       ALL_DISTINCT (MAP (\r. EL r (linear_scan_hidden_state_colors
         sth)) (FILTER is_phy_var l)) /\
       EVERY (\c. c < linear_scan_state_colornum st)
         (linear_scan_state_colorpool st) /\
       EVERY (\(e,r). EL r (linear_scan_hidden_state_colors sth) <
         linear_scan_state_colornum st) (linear_scan_state_active st) /\
         linear_scan_state_colornum
       st <= linear_scan_state_colormax st /\
         linear_scan_state_colormax
       st <= linear_scan_state_stacknum st /\
       EVERY (\r. EL r (linear_scan_hidden_state_colors sth) <
         linear_scan_state_colormax st ==> EL r
         (linear_scan_hidden_state_colors sth) <
         linear_scan_state_colornum st) l /\
       EVERY (\r. EL r (linear_scan_hidden_state_int_beg sth) <= pos)
         l /\
       EVERY (\r. ((pos <= EL r (linear_scan_hidden_state_int_end
         sth) /\ EL r (linear_scan_hidden_state_colors sth) <
         linear_scan_state_colormax st) ==> (MEM (EL r
         (linear_scan_hidden_state_int_end sth),r)
         (linear_scan_state_active st)))) l /\
       EVERY (\r. ((MEM (EL r (linear_scan_hidden_state_int_end
         sth),r) (linear_scan_state_active st)) ==> (pos <= (&1) + EL r
         (linear_scan_hidden_state_int_end sth)))) l /\
       (!r1 r2. MEM r1 l /\ MEM r2 l /\
           interval_intersect (EL r1
             (linear_scan_hidden_state_int_beg sth),EL r1
             (linear_scan_hidden_state_int_end sth)) (EL r2
             (linear_scan_hidden_state_int_beg sth),EL r2
             (linear_scan_hidden_state_int_end sth)) /\
           EL r1 (linear_scan_hidden_state_colors sth) = EL r2
             (linear_scan_hidden_state_colors sth) ==> r1 = r2) /\
       SORTED less_FST (linear_scan_state_active st) /\
       EVERY (\(e,r). e = EL r (linear_scan_hidden_state_int_end
         sth)) (linear_scan_state_active st) /\
       EVERY (\(e,r). MEM r l) (linear_scan_state_active st) /\
       EVERY (\(r1,r2). MEM r1 l /\ MEM r2 l /\ EL r1
         (linear_scan_hidden_state_colors sth) = EL r2
         (linear_scan_hidden_state_colors sth) ==> r1 = r2) forced /\
       mincol <= linear_scan_state_colornum st /\
       EVERY (\c. mincol <= c) (linear_scan_state_colorpool st ++
         MAP (\r. EL r (linear_scan_hidden_state_colors sth)) l))`;;

(* HOL4 linear_scanProofScript.sml:2444-2451: a proof *)

let remove_inactive_intervals_invariants =
  cake_theorem "remove_inactive_intervals_invariants"
  (fun () ->
    `!beg st sth l pos forced mincol.
     good_linear_scan_state st sth l pos forced mincol /\
     pos <= beg ==>
     (?stout. (M_success stout,sth) = remove_inactive_intervals beg
       st sth /\
     good_linear_scan_state stout sth l beg forced mincol /\
       linear_scan_state_colormax
     stout = linear_scan_state_colormax st)`)
  CHEAT_TAC;;

let add_active_interval_output =
  cake_theorem "add_active_interval_output"
  (fun () ->
    `!lin x lout.
     SORTED less_FST lin /\
     lout = add_active_interval (e,r) lin ==>
     SORTED less_FST lout /\
     (?l1 l2. lin = l1 ++ l2 /\ lout = l1 ++ ((e,r) :: l2))`)
  CHEAT_TAC;;

let find_color_in_list_output = cake_theorem "find_color_in_list_output"
  (fun () ->
    `!forbidden col l rest.
     find_color_in_list l forbidden = SOME (col,rest) ==>
     MEM col l /\ ~(col IN domain forbidden) /\
     (?l1 l2. rest = l1 ++ l2 /\ l = l1 ++ (col :: l2))`)
  CHEAT_TAC;;

let find_color_in_colornum_invariants =
  cake_theorem "find_color_in_colornum_invariants"
  (fun () ->
    `!st forbidden sth l pos forced mincol.
     good_linear_scan_state st sth l pos forced mincol /\
     domain forbidden SUBSET {EL r (linear_scan_hidden_state_colors
       sth) | r | MEM r l} /\
     find_color_in_colornum st forbidden = (stout,SOME col) ==>
     good_linear_scan_state (linear_scan_state_colorpool_fupd (\l.
       col :: l) stout) sth l pos forced mincol /\
       linear_scan_state_colornum
     st <= col /\ col < linear_scan_state_colornum stout /\
       linear_scan_state_colornum
     st <= linear_scan_state_colornum stout /\ ~(
     col IN domain forbidden) /\
     st = linear_scan_state_colornum_fupd (K
       (linear_scan_state_colornum st))
       (linear_scan_state_colorpool_fupd (K
       (linear_scan_state_colorpool st)) stout)`)
  CHEAT_TAC;;

let find_color_invariants = cake_theorem "find_color_invariants"
  (fun () ->
    `!st forbidden stout col sth l pos forced mincol.
     good_linear_scan_state st sth l pos forced mincol /\
     domain forbidden SUBSET {EL r (linear_scan_hidden_state_colors
       sth) | r | MEM r l} /\
     find_color st forbidden = (stout,SOME col) ==>
     good_linear_scan_state (linear_scan_state_colorpool_fupd (\l.
       col :: l) stout) sth l pos forced mincol /\
     col < linear_scan_state_colornum stout /\ ~(
     col IN domain forbidden) /\
     st = linear_scan_state_colornum_fupd (K
       (linear_scan_state_colornum st))
       (linear_scan_state_colorpool_fupd (K
       (linear_scan_state_colorpool st)) stout)`)
  CHEAT_TAC;;

let update_color_active_colors_same =
  cake_theorem "update_color_active_colors_same"
  (fun () ->
    `!e reg active regcol colors.
     MAP (\(e,r). EL r (LUPDATE regcol reg colors)) (FILTER
       (\(e,r). ~(r = reg)) active) = MAP (\(e,r). EL r colors)
       (FILTER (\(e,r). ~(r = reg)) active)`)
  CHEAT_TAC;;

let forced_update_stack_color_lemma =
  cake_theorem "forced_update_stack_color_lemma"
  (fun () ->
    `!(colors:num list) (stacknum:num) l r2 r1.
     EVERY (\r. EL r colors < stacknum) l /\
     MEM r2 l /\
     r1 < LENGTH colors /\
     EL r1 (LUPDATE stacknum r1 colors) = EL r2 (LUPDATE stacknum
       r1 colors) ==>
     r1 = r2`)
  CHEAT_TAC;;

(* TODO: this should be part of the standard library, but I couldn't find it *)
let IS_SPARSE_SUBLIST_def = cake_define_list
  [`IS_SPARSE_SUBLIST [] l2 = T`;
   `IS_SPARSE_SUBLIST (x :: xs) [] = F`;
   `IS_SPARSE_SUBLIST (x :: xs) (y :: ys) =
      ((x = y /\ IS_SPARSE_SUBLIST xs ys) \/ IS_SPARSE_SUBLIST
        (x :: xs) ys)`];;

let FILTER_IS_SPARSE_SUBLIST = cake_theorem "FILTER_IS_SPARSE_SUBLIST"
  (fun () ->
    `!l. IS_SPARSE_SUBLIST (FILTER P l) l`)
  CHEAT_TAC;;

let MEM_SPARSE_SUBLIST = cake_theorem "MEM_SPARSE_SUBLIST"
  (fun () ->
    `!l1 l2 x. IS_SPARSE_SUBLIST l1 l2 /\ MEM x l1 ==> MEM x l2`)
  CHEAT_TAC;;

let IS_SPARSE_SUBLIST_APPEND_LEFT =
  cake_theorem "IS_SPARSE_SUBLIST_APPEND_LEFT"
  (fun () ->
    `!l1 l2 l. IS_SPARSE_SUBLIST l1 l2 ==> IS_SPARSE_SUBLIST (l ++ l1)
  (l ++ l2)`)
  CHEAT_TAC;;

let IS_SPARSE_SUBLIST_APPEND_RIGHT =
  cake_theorem "IS_SPARSE_SUBLIST_APPEND_RIGHT"
  (fun () ->
    `!l1 l2 l. IS_SPARSE_SUBLIST l1 l2 ==> IS_SPARSE_SUBLIST (l1 ++ l)
  (l2 ++ l)`)
  CHEAT_TAC;;

let MAP_IS_SPARSE_SUBLIST = cake_theorem "MAP_IS_SPARSE_SUBLIST"
  (fun () ->
    `!l1 l2. IS_SPARSE_SUBLIST l1 l2 ==> IS_SPARSE_SUBLIST (MAP f l1)
  (MAP f l2)`)
  CHEAT_TAC;;

let ALL_DISTINCT_IS_SPARSE_SUBLIST =
  cake_theorem "ALL_DISTINCT_IS_SPARSE_SUBLIST"
  (fun () ->
    `!l1 l2. ALL_DISTINCT l2 /\ IS_SPARSE_SUBLIST l1 l2 ==>
  ALL_DISTINCT l1`)
  CHEAT_TAC;;

let spill_register_FILTER_invariants_hidden =
  cake_theorem "spill_register_FILTER_invariants_hidden"
  (fun () ->
    `!st sth l pos forced reg mincol.
     linear_scanProof_id (~(is_phy_var reg) \/ ~(MEM reg l)) /\
     good_linear_scan_state st sth l pos forced mincol /\
     reg < LENGTH (linear_scan_hidden_state_colors sth) /\
     EL reg (linear_scan_hidden_state_int_beg sth) <= pos ==>
     (?stout sthout. (M_success stout,sthout) = spill_register
       (linear_scan_state_active_fupd (K (FILTER (\(e,r). ~(r = reg))
       (linear_scan_state_active st))) st) reg sth /\
     good_linear_scan_state stout sthout (reg :: l) pos forced
       mincol /\
     LENGTH (linear_scan_hidden_state_colors sthout) = LENGTH
       (linear_scan_hidden_state_colors sth) /\
     (!r. ~(r = reg) ==> EL r (linear_scan_hidden_state_colors sth)
       = EL r (linear_scan_hidden_state_colors sthout)) /\
       linear_scan_state_colormax
     stout = linear_scan_state_colormax st /\
       linear_scan_hidden_state_int_beg
     sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout =
       linear_scan_hidden_state_int_end sth /\
       linear_scan_state_colormax
     st <= EL reg (linear_scan_hidden_state_colors sthout))`)
  CHEAT_TAC;;

(* HOL4 linear_scanProofScript.sml:2914-2916: a theorem that HOL4
   states as the value of an ML expression *)

let FILTER_MEM_active = cake_theorem "FILTER_MEM_active"
  (fun () ->
    `!(reg:num) l. (!(e:int). ~(MEM (e,reg) l)) ==> FILTER (\(e,r).
  ~(r = reg)) l = l`)
  CHEAT_TAC;;

let spill_register_invariants = cake_theorem "spill_register_invariants"
  (fun () ->
    `!st sth l pos forced reg mincol.
     (!e. ~(MEM (e,reg) (linear_scan_state_active st))) /\
     (~(is_phy_var reg) \/ ~(MEM reg l)) /\
     good_linear_scan_state st sth l pos forced mincol /\
     reg < LENGTH (linear_scan_hidden_state_colors sth) /\
     EL reg (linear_scan_hidden_state_int_beg sth) <= pos ==>
     (?stout sthout. (M_success stout,sthout) = spill_register st
       reg sth /\
     good_linear_scan_state stout sthout (reg :: l) pos forced
       mincol /\
     LENGTH (linear_scan_hidden_state_colors sthout) = LENGTH
       (linear_scan_hidden_state_colors sth) /\
       linear_scan_hidden_state_int_beg
     sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout =
       linear_scan_hidden_state_int_end sth /\
     (!r. ~(r = reg) ==> EL r (linear_scan_hidden_state_colors sth)
       = EL r (linear_scan_hidden_state_colors sthout)) /\
       linear_scan_state_colormax
     stout = linear_scan_state_colormax st /\
       linear_scan_state_colormax
     st <= EL reg (linear_scan_hidden_state_colors sthout))`)
  CHEAT_TAC;;

let edges_to_adjlist_step_def = cake_define
  `edges_to_adjlist_step sth (a,b) acc =
     (if a = b then
       acc else if ((<) LEX (<=)) (EL a
         (linear_scan_hidden_state_int_beg sth),a) (EL b
         (linear_scan_hidden_state_int_beg sth),b) then
       sptree_insert b (a :: (the [] (sptree_lookup b acc))) acc else
       sptree_insert a (b :: (the [] (sptree_lookup a acc))) acc)`;;

let edges_to_adjlist_FOLDL = cake_theorem "edges_to_adjlist_FOLDL"
  (fun () ->
    `!forced sth acc.
     EVERY (\(r1,r2). r1 < LENGTH (linear_scan_hidden_state_int_beg
       sth) /\ r2 < LENGTH (linear_scan_hidden_state_int_beg sth))
       forced ==>
     edges_to_adjlist forced acc sth = (M_success (FOLDL (\acc
       pair. edges_to_adjlist_step sth pair acc) acc forced),sth)`)
  CHEAT_TAC;;

let forbidden_is_from_forced_def = cake_define
  `forbidden_is_from_forced forced (int_beg:int list) reg forbidden =
       (!reg2. (~(reg = reg2) /\ (MEM (reg2,reg) forced \/ MEM
         (reg,reg2) forced) /\
       ((<) LEX (<=)) (EL reg2 int_beg,reg2) (EL reg int_beg,reg))
         <=> MEM reg2 forbidden)`;;

let forbidden_is_from_forced_sublist_def = cake_define
  `forbidden_is_from_forced_sublist l forced (int_beg:int list) reg
  forbidden =
       (!reg2. (~(reg = reg2) /\ (MEM (reg2,reg) forced \/ MEM
         (reg,reg2) forced) /\
       ((<) LEX (<=)) (EL reg2 int_beg,reg2) (EL reg int_beg,reg))
         <=> (MEM reg2 forbidden /\ MEM reg l))`;;

let forbidden_is_from_forced_list_def = cake_define
  `forbidden_is_from_forced_list forced l reg forbidden =
       (!reg2. MEM reg2 l /\
              (MEM (reg2,reg) forced \/ MEM (reg,reg2) forced) ==>
              MEM reg2 forbidden)`;;

let forbidden_is_from_map_color_forced_def = cake_define
  `forbidden_is_from_map_color_forced forced l colors reg (forbidden:1
  spt) =
       (!reg2. MEM reg2 l /\
              (MEM (reg2,reg) forced \/ MEM (reg,reg2) forced) ==>
              EL reg2 colors IN domain forbidden)`;;

let edges_to_adjlist_FOLDR_output =
  cake_theorem "edges_to_adjlist_FOLDR_output"
  (fun () ->
    `!forced sth.
     !reg. forbidden_is_from_forced forced
       (linear_scan_hidden_state_int_beg sth) reg (the []
       (sptree_lookup reg (ITLIST (\pair acc. edges_to_adjlist_step
       sth pair acc) forced LN)))`)
  CHEAT_TAC;;

let edges_to_adjlist_output = cake_theorem "edges_to_adjlist_output"
  (fun () ->
    `!forced sth.
     EVERY (\(r1,r2). r1 < LENGTH (linear_scan_hidden_state_int_beg
       sth) /\ r2 < LENGTH (linear_scan_hidden_state_int_beg sth))
       forced ==>
     (?adjlist. edges_to_adjlist forced LN sth = (M_success
       adjlist,sth) /\
     (!reg. forbidden_is_from_forced forced
       (linear_scan_hidden_state_int_beg sth) reg (the []
       (sptree_lookup reg adjlist))))`)
  CHEAT_TAC;;

let state_invariants_remove_head =
  cake_theorem "state_invariants_remove_head"
  (fun () ->
    `!st sth reg l pos forced mincol.
     MEM reg l /\
     good_linear_scan_state st sth (reg :: l) pos forced mincol ==>
     good_linear_scan_state st sth l pos forced mincol`)
  CHEAT_TAC;;

let find_last_stealable_success =
  cake_theorem "find_last_stealable_success"
  (fun () ->
    `!forbidden sth active.
     EVERY (\(e,r). r < LENGTH (linear_scan_hidden_state_colors
       sth)) active ==>
     (?optout. find_last_stealable active forbidden sth =
       (M_success optout,sth))`)
  CHEAT_TAC;;

let find_last_stealable_output =
  cake_theorem "find_last_stealable_output"
  (fun () ->
    `!forbidden sth active steal rest.
     find_last_stealable active forbidden sth = (M_success (SOME
       (steal,rest)),sth) ==>
     ~is_phy_var (SND steal) /\ sptree_lookup (EL (SND steal)
       (linear_scan_hidden_state_colors sth)) forbidden = NONE /\
     (?l1 l2. rest = l1 ++ l2 /\ active = l1 ++ (steal :: l2))`)
  CHEAT_TAC;;

let good_linear_scan_state_active_length_colors =
  cake_theorem "good_linear_scan_state_active_length_colors"
  (fun () ->
    `!st sth l pos forced mincol.
     good_linear_scan_state st sth l pos forced mincol ==>
     EVERY (\(e,r). r < LENGTH (linear_scan_hidden_state_colors
       sth)) (linear_scan_state_active st)`)
  CHEAT_TAC;;

let color_register_eq = cake_theorem "color_register_eq"
  (fun () ->
    `!st reg col rend.
     color_register st reg col rend =
      st_ex_ignore_bind
        (update_colors reg col) (
        st_ex_return (linear_scan_state_phyregs_fupd (K (if
          is_phy_var reg then (sptree_insert col one)
          (linear_scan_state_phyregs st) else linear_scan_state_phyregs
          st)) (linear_scan_state_active_fupd (add_active_interval
          (rend,reg))
          st)))`)
  CHEAT_TAC;;

let color_register_invariants = cake_theorem "color_register_invariants"
  (fun () ->
    `!st sth l pos forced reg col forbidden mincol.
     good_linear_scan_state st sth l pos forced mincol /\
     forbidden_is_from_map_color_forced forced l
       (linear_scan_hidden_state_colors sth) reg forbidden /\ ~(
     col IN domain forbidden) /\
     (is_phy_var reg ==> domain (linear_scan_state_phyregs st)
       SUBSET domain forbidden) /\
     ~MEM col (linear_scan_state_colorpool st ++ MAP (\(e,r). EL r
       (linear_scan_hidden_state_colors sth)) (linear_scan_state_active
       st)) /\
     EL reg (linear_scan_hidden_state_int_beg sth) = pos /\
     EL reg (linear_scan_hidden_state_int_beg sth) <= EL reg
       (linear_scan_hidden_state_int_end sth) /\
     col < linear_scan_state_colornum st /\
     mincol <= col /\
     reg < LENGTH (linear_scan_hidden_state_colors sth) /\
     ~MEM reg l ==>
     (?stout sthout. (M_success stout,sthout) = color_register st
       reg col (EL reg (linear_scan_hidden_state_int_end sth)) sth /\
     good_linear_scan_state stout sthout (reg :: l) pos forced
       mincol /\
     LENGTH (linear_scan_hidden_state_colors sthout) = LENGTH
       (linear_scan_hidden_state_colors sth) /\
       linear_scan_hidden_state_int_beg
     sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout =
       linear_scan_hidden_state_int_end sth /\
     (!r. ~(r = reg) ==> EL r (linear_scan_hidden_state_colors sth)
       = EL r (linear_scan_hidden_state_colors sthout)) /\
       linear_scan_state_colormax
     stout = linear_scan_state_colormax st)`)
  CHEAT_TAC;;

let find_spill_invariants = cake_theorem "find_spill_invariants"
  (fun () ->
    `!st sth l forbidden forced reg force mincol.
     ~MEM reg l /\
     good_linear_scan_state st sth l (EL reg
       (linear_scan_hidden_state_int_beg sth)) forced mincol /\
     reg < LENGTH (linear_scan_hidden_state_colors sth) /\
     forbidden_is_from_map_color_forced forced l
       (linear_scan_hidden_state_colors sth) reg forbidden /\
     (is_phy_var reg ==> domain (linear_scan_state_phyregs st)
       SUBSET domain forbidden) /\
     EL reg (linear_scan_hidden_state_int_beg sth) <= EL reg
       (linear_scan_hidden_state_int_end sth) ==>
     (?stout sthout. (M_success stout,sthout) = find_spill st
       forbidden reg (EL reg (linear_scan_hidden_state_int_end sth))
       force sth /\
     good_linear_scan_state stout sthout (reg :: l) (EL reg
       (linear_scan_hidden_state_int_beg sth)) forced mincol /\
     LENGTH (linear_scan_hidden_state_colors sthout) = LENGTH
       (linear_scan_hidden_state_colors sth) /\
       linear_scan_hidden_state_int_beg
     sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout =
       linear_scan_hidden_state_int_end sth /\
     (!r. ~MEM r (reg :: l) ==> EL r
       (linear_scan_hidden_state_colors sthout) = EL r
       (linear_scan_hidden_state_colors sth)) /\
     (!r. MEM r l /\ is_phy_var r ==> EL r
       (linear_scan_hidden_state_colors sthout) = EL r
       (linear_scan_hidden_state_colors sth)) /\
       linear_scan_state_colormax
     stout = linear_scan_state_colormax st)`)
  CHEAT_TAC;;

let linear_reg_alloc_step_aux_invariants =
  cake_theorem "linear_reg_alloc_step_aux_invariants"
  (fun () ->
    `!st sth l preferred (forbidden:1 spt) forced reg force mincol.
     ~MEM reg l /\
     good_linear_scan_state st sth l (EL reg
       (linear_scan_hidden_state_int_beg sth)) forced mincol /\
     reg < LENGTH (linear_scan_hidden_state_colors sth) /\
     forbidden_is_from_map_color_forced forced l
       (linear_scan_hidden_state_colors sth) reg forbidden /\
     (is_phy_var reg ==> domain (linear_scan_state_phyregs st)
       SUBSET domain forbidden) /\
     domain forbidden SUBSET {EL r (linear_scan_hidden_state_colors
       sth) | r | MEM r l} /\
     EL reg (linear_scan_hidden_state_int_beg sth) <= EL reg
       (linear_scan_hidden_state_int_end sth) ==>
     (?stout sthout. (M_success stout,sthout) =
       linear_reg_alloc_step_aux st forbidden preferred reg (EL reg
       (linear_scan_hidden_state_int_end sth)) force sth /\
     good_linear_scan_state stout sthout (reg :: l) (EL reg
       (linear_scan_hidden_state_int_beg sth)) forced mincol /\
     LENGTH (linear_scan_hidden_state_colors sthout) = LENGTH
       (linear_scan_hidden_state_colors sth) /\
       linear_scan_hidden_state_int_beg
     sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout =
       linear_scan_hidden_state_int_end sth /\
     (!r. ~MEM r (reg :: l) ==> EL r
       (linear_scan_hidden_state_colors sthout) = EL r
       (linear_scan_hidden_state_colors sth)) /\
     (!r. MEM r l /\ is_phy_var r ==> EL r
       (linear_scan_hidden_state_colors sthout) = EL r
       (linear_scan_hidden_state_colors sth)) /\
       linear_scan_state_colormax
     stout = linear_scan_state_colormax st)`)
  CHEAT_TAC;;

let st_ex_MAP_colors_sub = cake_theorem "st_ex_MAP_colors_sub"
  (fun () ->
    `!l sth.
     EVERY (\r. r < LENGTH (linear_scan_hidden_state_colors sth)) l
       ==>
     st_ex_MAP colors_sub l sth = (M_success (MAP (\r. EL r
       (linear_scan_hidden_state_colors sth)) l),sth)`)
  CHEAT_TAC;;

let phystack_on_stack_def = cake_define
  `phystack_on_stack l st sth =
     (!r. MEM r l /\ is_phy_var r /\ 2 *
       linear_scan_state_colormax st <= r ==>
       linear_scan_state_colormax st <= EL r
       (linear_scan_hidden_state_colors sth))`;;

let linear_reg_alloc_step_pass1_invariants =
  cake_theorem "linear_reg_alloc_step_pass1_invariants"
  (fun () ->
    `!st sth l moves forced_adj forced reg pos mincol.
     ~MEM reg l /\
     good_linear_scan_state st sth l pos forced mincol /\
     pos <= (EL reg (linear_scan_hidden_state_int_beg sth)) /\
     reg < LENGTH (linear_scan_hidden_state_colors sth) /\
     forbidden_is_from_forced_list forced l reg (the []
       (sptree_lookup reg forced_adj)) /\
     EVERY (\r. MEM r l) (the [] (sptree_lookup reg forced_adj)) /\
     EVERY (\r. r < LENGTH (linear_scan_hidden_state_colors sth))
       (the [] (sptree_lookup reg forced_adj)) /\
     EVERY (\r. r < LENGTH (linear_scan_hidden_state_colors sth))
       (the [] (sptree_lookup reg moves)) /\
     EL reg (linear_scan_hidden_state_int_beg sth) <= EL reg
       (linear_scan_hidden_state_int_end sth) ==>
     (?stout sthout. (M_success stout,sthout) =
       linear_reg_alloc_step_pass1 forced_adj moves st reg sth /\
     good_linear_scan_state stout sthout (reg :: l) (EL reg
       (linear_scan_hidden_state_int_beg sth)) forced mincol /\
     LENGTH (linear_scan_hidden_state_colors sthout) = LENGTH
       (linear_scan_hidden_state_colors sth) /\
       linear_scan_hidden_state_int_beg
     sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout =
       linear_scan_hidden_state_int_end sth /\
     (!r. ~MEM r (reg :: l) ==> EL r
       (linear_scan_hidden_state_colors sthout) = EL r
       (linear_scan_hidden_state_colors sth)) /\
     (!r. MEM r l /\ is_phy_var r ==> EL r
       (linear_scan_hidden_state_colors sthout) = EL r
       (linear_scan_hidden_state_colors sth)) /\
     (phystack_on_stack l st sth ==> phystack_on_stack (reg :: l)
       stout sthout) /\ linear_scan_state_colormax
     stout = linear_scan_state_colormax st)`)
  CHEAT_TAC;;

let linear_reg_alloc_step_pass2_invariants =
  cake_theorem "linear_reg_alloc_step_pass2_invariants"
  (fun () ->
    `!st sth l moves forced_adj forced reg pos mincol.
     ~MEM reg l /\
     good_linear_scan_state st sth l pos forced mincol /\
     pos <= (EL reg (linear_scan_hidden_state_int_beg sth)) /\
     reg < LENGTH (linear_scan_hidden_state_colors sth) /\
     forbidden_is_from_forced_list forced l reg (the []
       (sptree_lookup reg forced_adj)) /\
     EVERY (\r. MEM r l) (the [] (sptree_lookup reg forced_adj)) /\
     EVERY (\r. r < LENGTH (linear_scan_hidden_state_colors sth))
       (the [] (sptree_lookup reg forced_adj)) /\
     EVERY (\r. r < LENGTH (linear_scan_hidden_state_colors sth))
       (the [] (sptree_lookup reg moves)) /\
     EL reg (linear_scan_hidden_state_int_beg sth) <= EL reg
       (linear_scan_hidden_state_int_end sth) ==>
     (?stout sthout. (M_success stout,sthout) =
       linear_reg_alloc_step_pass2 forced_adj moves st reg sth /\
     good_linear_scan_state stout sthout (reg :: l) (EL reg
       (linear_scan_hidden_state_int_beg sth)) forced mincol /\
     LENGTH (linear_scan_hidden_state_colors sthout) = LENGTH
       (linear_scan_hidden_state_colors sth) /\
       linear_scan_hidden_state_int_beg
     sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout =
       linear_scan_hidden_state_int_end sth /\
     (!r. ~MEM r (reg :: l) ==> EL r
       (linear_scan_hidden_state_colors sthout) = EL r
       (linear_scan_hidden_state_colors sth)) /\
     (!r. MEM r l /\ is_phy_var r ==> EL r
       (linear_scan_hidden_state_colors sthout) = EL r
       (linear_scan_hidden_state_colors sth)) /\
       linear_scan_state_colormax
     stout = linear_scan_state_colormax st)`)
  CHEAT_TAC;;

(* TODO: move *)
let intbeg_less_def = cake_define
  `intbeg_less (int_beg:int list) r1 r2 = ((<) LEX (<=)) (EL r1
  int_beg,r1) (EL r2 int_beg,r2)`;;

let intbeg_less_transitive = cake_theorem "intbeg_less_transitive"
  (fun () ->
    `!int_beg. transitive (intbeg_less int_beg)`)
  CHEAT_TAC;;

let intbeg_less_total = cake_theorem "intbeg_less_total"
  (fun () ->
    `!int_beg. total (intbeg_less int_beg)`)
  CHEAT_TAC;;

let st_ex_FOLDL_linear_reg_alloc_step_passn_invariants_lemma =
  cake_theorem
    "st_ex_FOLDL_linear_reg_alloc_step_passn_invariants_lemma"
  (fun () ->
    `!regl st sth l pos b moves forced_adj forced mincol.
     SORTED (intbeg_less (linear_scan_hidden_state_int_beg sth))
       regl /\
     (!r1 r2. MEM r1 l /\ MEM r2 regl ==> intbeg_less
       (linear_scan_hidden_state_int_beg sth) r1 r2) /\
     ALL_DISTINCT regl /\
     EVERY (\r. ~MEM r regl) l /\
     good_linear_scan_state st sth l pos forced mincol /\
     EVERY (\r. pos <= (EL r (linear_scan_hidden_state_int_beg
       sth))) regl /\
     EVERY (\r. r < LENGTH (linear_scan_hidden_state_colors sth))
       regl /\
     (!r. forbidden_is_from_forced_sublist (l ++ regl) forced
       (linear_scan_hidden_state_int_beg sth) r (the [] (sptree_lookup r
       forced_adj))) /\
     EVERY (\(r1,r2). MEM r1 (l ++ regl) /\ MEM r2 (l ++ regl))
       forced /\
     (!r1. EVERY (\r2. r2 < LENGTH (linear_scan_hidden_state_colors
       sth)) (the [] (sptree_lookup r1 forced_adj))) /\
     (!r1. EVERY (\r2. r2 < LENGTH (linear_scan_hidden_state_colors
       sth)) (the [] (sptree_lookup r1 moves))) /\
     EVERY (\r. EL r (linear_scan_hidden_state_int_beg sth) <= EL r
       (linear_scan_hidden_state_int_end sth)) regl ==>
     (?stout sthout posout. (M_success stout,sthout) = st_ex_FOLDL
       ((if b then linear_reg_alloc_step_pass1 else
       linear_reg_alloc_step_pass2) forced_adj moves) st regl sth /\
     good_linear_scan_state stout sthout ((REVERSE regl) ++ l)
       (posout) forced mincol /\
     LENGTH (linear_scan_hidden_state_colors sthout) = LENGTH
       (linear_scan_hidden_state_colors sth) /\
       linear_scan_hidden_state_int_beg
     sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout =
       linear_scan_hidden_state_int_end sth /\
     (!r. ~MEM r (l ++ regl) ==> EL r
       (linear_scan_hidden_state_colors sthout) = EL r
       (linear_scan_hidden_state_colors sth)) /\
     (b ==> (phystack_on_stack l st sth ==> phystack_on_stack
       ((REVERSE regl) ++ l) stout sthout)) /\
       linear_scan_state_colormax
     stout = linear_scan_state_colormax st)`)
  CHEAT_TAC;;

let st_ex_FOLDL_linear_reg_alloc_step_passn_invariants =
  cake_theorem "st_ex_FOLDL_linear_reg_alloc_step_passn_invariants"
  (fun () ->
    `!regl st sth pos b moves forced_adj forced mincol.
     SORTED (intbeg_less (linear_scan_hidden_state_int_beg sth))
       regl /\
     ALL_DISTINCT regl /\
     good_linear_scan_state st sth [] pos forced mincol /\
     EVERY (\r. pos <= (EL r (linear_scan_hidden_state_int_beg
       sth))) regl /\
     EVERY (\r. r < LENGTH (linear_scan_hidden_state_colors sth))
       regl /\
     (!r. forbidden_is_from_forced_sublist regl forced
       (linear_scan_hidden_state_int_beg sth) r (the [] (sptree_lookup r
       forced_adj))) /\
     EVERY (\(r1,r2). MEM r1 regl /\ MEM r2 regl) forced /\
     (!r1. EVERY (\r2. r2 < LENGTH (linear_scan_hidden_state_colors
       sth)) (the [] (sptree_lookup r1 forced_adj))) /\
     (!r1. EVERY (\r2. r2 < LENGTH (linear_scan_hidden_state_colors
       sth)) (the [] (sptree_lookup r1 moves))) /\
     EVERY (\r. EL r (linear_scan_hidden_state_int_beg sth) <= EL r
       (linear_scan_hidden_state_int_end sth)) regl ==>
     (?stout sthout posout. (M_success stout,sthout) = st_ex_FOLDL
       ((if b then linear_reg_alloc_step_pass1 else
       linear_reg_alloc_step_pass2) forced_adj moves) st regl sth /\
     good_linear_scan_state stout sthout (REVERSE regl) (posout)
       forced mincol /\
     LENGTH (linear_scan_hidden_state_colors sthout) = LENGTH
       (linear_scan_hidden_state_colors sth) /\
       linear_scan_hidden_state_int_beg
     sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout =
       linear_scan_hidden_state_int_end sth /\
     (!r. ~MEM r regl ==> EL r (linear_scan_hidden_state_colors
       sthout) = EL r (linear_scan_hidden_state_colors sth)) /\
     (b ==> phystack_on_stack (REVERSE regl) stout sthout) /\
       linear_scan_state_colormax
     stout = linear_scan_state_colormax st)`)
  CHEAT_TAC;;

let swap_regs_eq = cake_theorem "swap_regs_eq"
  (fun () ->
    `!sth i1 i2.
     i1 < LENGTH (linear_scan_hidden_state_sorted_regs sth) /\ i2 <
       LENGTH (linear_scan_hidden_state_sorted_regs sth) ==>
     (?sthout. swap_regs i1 i2 sth = (M_success one,sthout) /\
     sthout = linear_scan_hidden_state_sorted_regs_fupd (K
       (LUPDATE (EL i1 (linear_scan_hidden_state_sorted_regs sth)) i2
       (LUPDATE (EL i2 (linear_scan_hidden_state_sorted_regs sth)) i1
       (linear_scan_hidden_state_sorted_regs sth)))) sth)`)
  CHEAT_TAC;;

(* TODO: move *)
let if_thm = cake_theorem "if_thm"
  (fun () ->
    `!b x y z. (if b then x else y) = z <=> ((b /\ x = z) \/ (~b /\ y
  = z))`)
  CHEAT_TAC;;

let split_at_indice_sing = cake_theorem "split_at_indice_sing"
  (fun () ->
    `!l i.
     i < LENGTH l ==>
     (?l1 x l2. l = l1 ++ [x] ++ l2 /\ LENGTH l1 = i)`)
  CHEAT_TAC;;

let split_at_indice = cake_theorem "split_at_indice"
  (fun () ->
    `!l i.
     i <= LENGTH l ==>
     (?l1 l2. l = l1 ++ l2 /\ LENGTH l1 = i)`)
  CHEAT_TAC;;

let swap_perm_lemma = cake_theorem "swap_perm_lemma"
  (fun () ->
    `!l i1 i2.
     i1 < LENGTH l /\
     i2 < LENGTH l ==>
     PERM l (LUPDATE (EL i1 l) i2 (LUPDATE (EL i2 l) i1 l))`)
  CHEAT_TAC;;

let LUPDATE_TAKE = cake_theorem "LUPDATE_TAKE"
  (fun () ->
    `!n x y l. x < n /\ n <= LENGTH l ==> TAKE n (LUPDATE y x l) =
  LUPDATE y x (TAKE n l)`)
  CHEAT_TAC;;

let swap_regs_perm = cake_theorem "swap_regs_perm"
  (fun () ->
    `!sth i1 i2 sthout.
     swap_regs i1 i2 sth = (M_success one,sthout) ==>
     (!n. i1 < n /\ i2 < n /\ n <= LENGTH
       (linear_scan_hidden_state_sorted_regs sth) ==> PERM (TAKE n
       (linear_scan_hidden_state_sorted_regs sth)) (TAKE n
       (linear_scan_hidden_state_sorted_regs sthout)))`)
  CHEAT_TAC;;

let partition_regs_correct = cake_theorem "partition_regs_correct"
  (fun () ->
    `!l rpiv begrpiv r sth.
     (!i. l <= i /\ i < r ==> EL i
       (linear_scan_hidden_state_sorted_regs sth) < LENGTH
       (linear_scan_hidden_state_int_beg sth)) /\
     l <= LENGTH (linear_scan_hidden_state_sorted_regs sth) /\
     r <= LENGTH (linear_scan_hidden_state_sorted_regs sth) ==>
     (?mid sthout. partition_regs l rpiv begrpiv r sth = (M_success
       mid,sthout) /\
     sthout = linear_scan_hidden_state_sorted_regs_fupd (K
       (linear_scan_hidden_state_sorted_regs sthout)) sth /\
     LENGTH (linear_scan_hidden_state_sorted_regs sthout) = LENGTH
       (linear_scan_hidden_state_sorted_regs sth) /\
     (l <= r ==> l <= mid /\ mid <= r) /\
     (!n. l <= n /\ r <= n /\ n <= LENGTH
       (linear_scan_hidden_state_sorted_regs sth) ==> PERM (TAKE n
       (linear_scan_hidden_state_sorted_regs sth)) (TAKE n
       (linear_scan_hidden_state_sorted_regs sthout))) /\
     (!ind'. ind' < l \/ r <= ind' ==> EL ind'
       (linear_scan_hidden_state_sorted_regs sthout) = EL ind'
       (linear_scan_hidden_state_sorted_regs sth)) /\
     (!ind'. l <= ind' /\ ind' < mid ==>
        (let reg = EL ind' (linear_scan_hidden_state_sorted_regs
          sthout) in
        ((<) LEX (<=)) (EL reg (linear_scan_hidden_state_int_beg
          sth),reg) (begrpiv,rpiv))) /\
     (!ind'. mid <= ind' /\ ind' < r ==>
        (let reg = EL ind' (linear_scan_hidden_state_sorted_regs
          sthout) in
        ((<) LEX (<=)) (begrpiv,rpiv) (EL reg
          (linear_scan_hidden_state_int_beg sth),reg))))`)
  CHEAT_TAC;;

let PERM_EVERY_EQ = cake_theorem "PERM_EVERY_EQ"
  (fun () ->
    `!P l1 l2.
     PERM l1 l2 ==>
     (EVERY P l1 <=> EVERY P l2)`)
  CHEAT_TAC;;

let sort_regs_prop_lemma = cake_theorem "sort_regs_prop_lemma"
  (fun () ->
    `!(P:num->bool) l1 l2 l r.
     l <= LENGTH l1 /\
     r <= LENGTH l1 /\
     (!ind'. ind' < l \/ r <= ind' ==> EL ind' l2 = EL ind' l1) /\
     (!ind'. l <= ind' /\ ind' < r ==> P (EL ind' l1)) /\
     PERM l1 l2 ==>
     (!ind'. l <= ind' /\ ind' < r ==> P (EL ind' l2))`)
  CHEAT_TAC;;

let sort_regs_correct = cake_theorem "sort_regs_correct"
  (fun () ->
    `!l r sth.
     (!i. l <= i /\ i < r ==> EL i
       (linear_scan_hidden_state_sorted_regs sth) < LENGTH
       (linear_scan_hidden_state_int_beg sth)) /\
     l <= LENGTH (linear_scan_hidden_state_sorted_regs sth) /\
     r <= LENGTH (linear_scan_hidden_state_sorted_regs sth) ==>
     (?sthout. sort_regs l r sth = (M_success one,sthout) /\
     sthout = linear_scan_hidden_state_sorted_regs_fupd (K
       (linear_scan_hidden_state_sorted_regs sthout)) sth /\
     LENGTH (linear_scan_hidden_state_sorted_regs sthout) = LENGTH
       (linear_scan_hidden_state_sorted_regs sth) /\
     (!n. l <= n /\ r <= n /\ n <= LENGTH
       (linear_scan_hidden_state_sorted_regs sth) ==> PERM (TAKE n
       (linear_scan_hidden_state_sorted_regs sth)) (TAKE n
       (linear_scan_hidden_state_sorted_regs sthout))) /\
     (!ind'. ind' < l \/ r <= ind' ==> EL ind'
       (linear_scan_hidden_state_sorted_regs sthout) = EL ind'
       (linear_scan_hidden_state_sorted_regs sth)) /\
     (!i1 i2. l <= i1 /\ i1 <= i2 /\ i2 < r ==>
      (let reg1 = EL i1 (linear_scan_hidden_state_sorted_regs
        sthout) in
      let reg2 = EL i2 (linear_scan_hidden_state_sorted_regs
        sthout) in
        ((<) LEX (<=)) (EL reg1 (linear_scan_hidden_state_int_beg
          sth),reg1) (EL reg2 (linear_scan_hidden_state_int_beg
          sth),reg2))))`)
  CHEAT_TAC;;

let swap_moves_eq = cake_theorem "swap_moves_eq"
  (fun () ->
    `!sth i1 i2.
     i1 < LENGTH (linear_scan_hidden_state_sorted_moves sth) /\ i2
       < LENGTH (linear_scan_hidden_state_sorted_moves sth) ==>
     (?sthout. swap_moves i1 i2 sth = (M_success one,sthout) /\
     sthout = linear_scan_hidden_state_sorted_moves_fupd (K
       (LUPDATE (EL i1 (linear_scan_hidden_state_sorted_moves sth)) i2
       (LUPDATE (EL i2 (linear_scan_hidden_state_sorted_moves sth)) i1
       (linear_scan_hidden_state_sorted_moves sth)))) sth)`)
  CHEAT_TAC;;

let swap_moves_correct = cake_theorem "swap_moves_correct"
  (fun () ->
    `!sth i1 i2.
     i1 < LENGTH (linear_scan_hidden_state_sorted_moves sth) /\ i2
       < LENGTH (linear_scan_hidden_state_sorted_moves sth) ==>
     (?sthout. swap_moves i1 i2 sth = (M_success one,sthout) /\
     sthout = linear_scan_hidden_state_sorted_moves_fupd (K
       (linear_scan_hidden_state_sorted_moves sthout)) sth /\
     LENGTH (linear_scan_hidden_state_sorted_moves sthout) = LENGTH
       (linear_scan_hidden_state_sorted_moves sth) /\
     (!n. i1 < n /\ i2 < n /\ n <= LENGTH
       (linear_scan_hidden_state_sorted_moves sth) ==> PERM (TAKE n
       (linear_scan_hidden_state_sorted_moves sth)) (TAKE n
       (linear_scan_hidden_state_sorted_moves sthout))))`)
  CHEAT_TAC;;

let partition_moves_correct = cake_theorem "partition_moves_correct"
  (fun () ->
    `!l ppiv r sth.
     l <= LENGTH (linear_scan_hidden_state_sorted_moves sth) /\
     r <= LENGTH (linear_scan_hidden_state_sorted_moves sth) ==>
     (?mid sthout. partition_moves l ppiv r sth = (M_success
       mid,sthout) /\
     (l <= r ==> l <= mid /\ mid <= r) /\
     sthout = linear_scan_hidden_state_sorted_moves_fupd (K
       (linear_scan_hidden_state_sorted_moves sthout)) sth /\
     LENGTH (linear_scan_hidden_state_sorted_moves sthout) = LENGTH
       (linear_scan_hidden_state_sorted_moves sth) /\
     (!n. l <= n /\ r <= n /\ n <= LENGTH
       (linear_scan_hidden_state_sorted_moves sth) ==> PERM (TAKE n
       (linear_scan_hidden_state_sorted_moves sth)) (TAKE n
       (linear_scan_hidden_state_sorted_moves sthout))))`)
  CHEAT_TAC;;

let sort_moves_correct = cake_theorem "sort_moves_correct"
  (fun () ->
    `!l r sth.
     l <= LENGTH (linear_scan_hidden_state_sorted_moves sth) /\
     r <= LENGTH (linear_scan_hidden_state_sorted_moves sth) ==>
     (?sthout. sort_moves l r sth = (M_success one,sthout) /\
     sthout = linear_scan_hidden_state_sorted_moves_fupd (K
       (linear_scan_hidden_state_sorted_moves sthout)) sth /\
     LENGTH (linear_scan_hidden_state_sorted_moves sthout) = LENGTH
       (linear_scan_hidden_state_sorted_moves sth) /\
     (!n. l <= n /\ r <= n /\ n <= LENGTH
       (linear_scan_hidden_state_sorted_moves sth) ==> PERM (TAKE n
       (linear_scan_hidden_state_sorted_moves sth)) (TAKE n
       (linear_scan_hidden_state_sorted_moves sthout))))`)
  CHEAT_TAC;;


let list_minimum = cake_theorem "list_minimum"
  (fun () ->
    `!f (l:num list). ?(x:int). EVERY (\y. x <= f y) l`)
  CHEAT_TAC;;

let linear_reg_alloc_pass1_initial_state_invariants =
  cake_theorem "linear_reg_alloc_pass1_initial_state_invariants"
  (fun () ->
    `!sth reglist forced k st.
     LENGTH (linear_scan_hidden_state_int_beg sth) = LENGTH
       (linear_scan_hidden_state_colors sth) /\ LENGTH
       (linear_scan_hidden_state_int_end sth) = LENGTH
       (linear_scan_hidden_state_colors sth) ==>
     (?pos.
     good_linear_scan_state (linear_reg_alloc_pass1_initial_state
       k) sth [] pos forced 0 /\
     EVERY (\r. pos <= EL r (linear_scan_hidden_state_int_beg
       sth)) reglist)`)
  CHEAT_TAC;;

let linear_reg_alloc_pass2_initial_state_invariants =
  cake_theorem "linear_reg_alloc_pass2_initial_state_invariants"
  (fun () ->
    `!sth reglist forced k nreg st.
     LENGTH (linear_scan_hidden_state_int_beg sth) = LENGTH
       (linear_scan_hidden_state_colors sth) /\ LENGTH
       (linear_scan_hidden_state_int_end sth) = LENGTH
       (linear_scan_hidden_state_colors sth) ==>
     (?pos.
     good_linear_scan_state (linear_reg_alloc_pass2_initial_state k
       nreg) sth [] pos forced k /\
     EVERY (\r. pos <= EL r (linear_scan_hidden_state_int_beg
       sth)) reglist)`)
  CHEAT_TAC;;

let st_ex_FILTER_good_stack = cake_theorem "st_ex_FILTER_good_stack"
  (fun () ->
    `!reglist sth k.
     EVERY (\r. r < LENGTH (linear_scan_hidden_state_colors sth))
       reglist ==>
     st_ex_FILTER_good (\r.
      st_ex_bind (colors_sub r) (\
        col.
        st_ex_return (is_stack_var r \/ k <= col))) reglist sth =
     (M_success (FILTER (\r. is_stack_var r \/ k <= EL r
       (linear_scan_hidden_state_colors sth)) reglist),sth)`)
  CHEAT_TAC;;

let lookup_fromAList_MAP_not_NONE =
  cake_theorem "lookup_fromAList_MAP_not_NONE"
  (fun () ->
    `!r l. ~(sptree_lookup r (fromAList (MAP (\r. (r,one)) l)) = NONE)
  <=> MEM r l`)
  CHEAT_TAC;;

let linear_scanProof_PERM_PARTITION = cake_theorem "PERM_PARTITION"
  (fun () ->
    `!P l. PERM l ((FILTER (\x. P x) l) ++ (FILTER (\x. ~P x) l))`)
  CHEAT_TAC;;

let forbidden_is_from_forced_take_sublist =
  cake_theorem "forbidden_is_from_forced_take_sublist"
  (fun () ->
    `EVERY (\(r1,r2). MEM r1 l /\ MEM r2 l) forced /\
     (!r. forbidden_is_from_forced forced int_beg r (the []
       (sptree_lookup r forced_adj))) ==>
     (!r. forbidden_is_from_forced_sublist l forced int_beg r
       (the [] (sptree_lookup r forced_adj)))`)
  CHEAT_TAC;;

let good_linear_scan_state_REVERSE =
  cake_theorem "good_linear_scan_state_REVERSE"
  (fun () ->
    `!st sth l pos forced mincol.
     good_linear_scan_state st sth (REVERSE l) pos forced mincol
       <=>
     good_linear_scan_state st sth l pos forced mincol`)
  CHEAT_TAC;;

let phystack_on_stack_REVERSE = cake_theorem "phystack_on_stack_REVERSE"
  (fun () ->
    `!l st sth. phystack_on_stack (REVERSE l) st sth <=>
  phystack_on_stack l st sth`)
  CHEAT_TAC;;

let FILTER_remove_MEM_l = cake_theorem "FILTER_remove_MEM_l"
  (fun () ->
    `!P l. FILTER (\x. P x /\ MEM x l) l = FILTER (\x. P x) l`)
  CHEAT_TAC;;

let le_div_2 = cake_theorem "le_div_2"
  (fun () ->
    `!k r. k <= r DIV 2 <=> 2 * k <= r`)
  CHEAT_TAC;;

let lt_div_2 = cake_theorem "lt_div_2"
  (fun () ->
    `!k r. r DIV 2 < k <=> r < 2 * k`)
  CHEAT_TAC;;

let list_to_sorted_regs_correct =
  cake_theorem "list_to_sorted_regs_correct"
  (fun () ->
    `!l n sth.
     n + LENGTH l <= LENGTH (linear_scan_hidden_state_sorted_regs
       sth) ==>
     (?sthout. (M_success one,sthout) = list_to_sorted_regs l n sth
       /\
     LENGTH (linear_scan_hidden_state_sorted_regs sthout) = LENGTH
       (linear_scan_hidden_state_sorted_regs sth) /\
     sthout = linear_scan_hidden_state_sorted_regs_fupd (K
       (linear_scan_hidden_state_sorted_regs sthout)) sth /\
     TAKE n (linear_scan_hidden_state_sorted_regs sthout) = TAKE n
       (linear_scan_hidden_state_sorted_regs sth) /\
     TAKE (LENGTH l) (DROP n
       (linear_scan_hidden_state_sorted_regs sthout)) = l)`)
  CHEAT_TAC;;

let sorted_regs_to_list_correct =
  cake_theorem "sorted_regs_to_list_correct"
  (fun () ->
    `!n last sth.
     last <= LENGTH (linear_scan_hidden_state_sorted_regs sth) ==>
     sorted_regs_to_list n last sth = (M_success (TAKE (last - n)
       (DROP n (linear_scan_hidden_state_sorted_regs sth))),sth)`)
  CHEAT_TAC;;

let list_to_sorted_moves_correct =
  cake_theorem "list_to_sorted_moves_correct"
  (fun () ->
    `!l n sth.
     n + LENGTH l <= LENGTH (linear_scan_hidden_state_sorted_moves
       sth) ==>
     (?sthout. (M_success one,sthout) = list_to_sorted_moves l n
       sth /\
     LENGTH (linear_scan_hidden_state_sorted_moves sthout) = LENGTH
       (linear_scan_hidden_state_sorted_moves sth) /\
     sthout = linear_scan_hidden_state_sorted_moves_fupd (K
       (linear_scan_hidden_state_sorted_moves sthout)) sth /\
     TAKE n (linear_scan_hidden_state_sorted_moves sthout) = TAKE n
       (linear_scan_hidden_state_sorted_moves sth) /\
     TAKE (LENGTH l) (DROP n
       (linear_scan_hidden_state_sorted_moves sthout)) = l)`)
  CHEAT_TAC;;

let sorted_moves_to_list_correct =
  cake_theorem "sorted_moves_to_list_correct"
  (fun () ->
    `!n last sth.
     last <= LENGTH (linear_scan_hidden_state_sorted_moves sth) ==>
     sorted_moves_to_list n last sth = (M_success (TAKE (last -
       n) (DROP n (linear_scan_hidden_state_sorted_moves sth))),sth)`)
  CHEAT_TAC;;

let linear_reg_alloc_intervals_correct =
  cake_theorem "linear_reg_alloc_intervals_correct"
  (fun () ->
    `!k forced moves reglist_unsorted sth.
     EVERY (\(r1,r2). MEM r1 reglist_unsorted /\ MEM r2
       reglist_unsorted) forced /\
     EVERY (\(r1,r2). r1 < LENGTH (linear_scan_hidden_state_colors
       sth) /\ r2 < LENGTH (linear_scan_hidden_state_colors sth)) (MAP
       SND moves) /\
     EVERY (\r. r < LENGTH (linear_scan_hidden_state_colors sth))
       reglist_unsorted /\
     EVERY (\r. EL r (linear_scan_hidden_state_int_beg sth) <= EL r
       (linear_scan_hidden_state_int_end sth)) reglist_unsorted /\
     ALL_DISTINCT reglist_unsorted /\
     EVERY (\r. r < LENGTH (linear_scan_hidden_state_int_beg sth))
       reglist_unsorted /\
     LENGTH (linear_scan_hidden_state_colors sth) = LENGTH
       (linear_scan_hidden_state_int_beg sth) /\
     LENGTH (linear_scan_hidden_state_int_end sth) = LENGTH
       (linear_scan_hidden_state_int_beg sth) /\
     LENGTH reglist_unsorted <= LENGTH
       (linear_scan_hidden_state_sorted_regs sth) /\
     LENGTH moves <= LENGTH (linear_scan_hidden_state_sorted_moves
       sth) ==>
     (?sthout. linear_reg_alloc_intervals k forced moves
       reglist_unsorted sth = (M_success one,sthout) /\
     (!r1 r2. MEM r1 reglist_unsorted /\ MEM r2 reglist_unsorted /\
        interval_intersect (EL r1 (linear_scan_hidden_state_int_beg
          sth),EL r1 (linear_scan_hidden_state_int_end sth)) (EL r2
          (linear_scan_hidden_state_int_beg sth),EL r2
          (linear_scan_hidden_state_int_end sth)) /\
        EL r1 (linear_scan_hidden_state_colors sthout) = EL r2
          (linear_scan_hidden_state_colors sthout) ==>
        r1 = r2) /\
     EVERY (\r.
      if is_phy_var r then
        EL r (linear_scan_hidden_state_colors sthout) = r DIV 2
          else if is_stack_var r then
        k <= EL r (linear_scan_hidden_state_colors sthout) else
        T) reglist_unsorted /\
     EVERY (\(r1,r2). EL r1 (linear_scan_hidden_state_colors
       sthout) = EL r2 (linear_scan_hidden_state_colors sthout) ==> r1 =
       r2) forced /\
     LENGTH (linear_scan_hidden_state_colors sthout) = LENGTH
       (linear_scan_hidden_state_colors sth))`)
  CHEAT_TAC;;

let good_bijection_state_def = cake_define
  `good_bijection_state st regset = (
       regset = domain (bijection_state_bij st) /\
       (
         sp_inverts (bijection_state_bij st) (bijection_state_invbij
           st) /\
         sp_inverts (bijection_state_invbij st) (bijection_state_bij
           st)) /\ (
         (!r. r IN regset ==> (is_stack_var r <=> is_stack_var (the 0
           (sptree_lookup r (bijection_state_bij st))))) /\
         (!r. r IN regset ==> (is_alloc_var r <=> is_alloc_var (the 0
           (sptree_lookup r (bijection_state_bij st))))) /\
         (!r. r IN regset /\ is_phy_var r ==> r = (the 0
           (sptree_lookup r (bijection_state_bij st))))) /\
       (!r. r IN domain (bijection_state_invbij st) /\ is_stack_var r
         ==> r < bijection_state_nstack st) /\
       (!r. r IN domain (bijection_state_invbij st) /\ is_alloc_var r
         ==> r < bijection_state_nalloc st) /\
       (
         is_stack_var (bijection_state_nstack st) /\
         is_alloc_var (bijection_state_nalloc st)) /\
       (!r. the 0 (sptree_lookup r (bijection_state_bij st)) <=
         bijection_state_nmax st))`;;

let convention_partitions_or = cake_theorem "convention_partitions_or"
  (fun () ->
    `!r. (is_phy_var r /\ ~is_stack_var r /\ ~is_alloc_var r) \/
         (~is_phy_var r /\ is_stack_var r /\ ~is_alloc_var r) \/
         (~is_phy_var r /\ ~is_stack_var r /\ is_alloc_var r)`)
  CHEAT_TAC;;

let find_bijection_invariants = cake_theorem "find_bijection_invariants"
  (fun () ->
    `!st r regset.
     good_bijection_state st regset ==>
     good_bijection_state (find_bijection_step st r) (r INSERT
       regset)`)
  CHEAT_TAC;;

let FOLDL_find_bijection_invariants =
  cake_theorem "FOLDL_find_bijection_invariants"
  (fun () ->
    `!st l regset.
     good_bijection_state st regset ==>
     good_bijection_state (FOLDL find_bijection_step st l)
       (set_of_list l UNION regset)`)
  CHEAT_TAC;;

let foldi_find_bijection_invariants =
  cake_theorem "foldi_find_bijection_invariants"
  (fun () ->
    `!st s regset.
     good_bijection_state st regset ==>
     good_bijection_state (foldi (\r v acc. find_bijection_step
       acc r) 0 st s) (domain s UNION regset)`)
  CHEAT_TAC;;

let in_clash_tree_set_eq = cake_theorem "in_clash_tree_set_eq"
  (fun () ->
    `(!w r. in_clash_tree (reg_alloc_Delta w r) = set_of_list w UNION
  set_of_list r) /\
     (!names. in_clash_tree (reg_alloc_Set names) = domain names)
       /\
     (!name_opt t1 t2.
      in_clash_tree (Branch name_opt t1 t2) =
      (match name_opt with SOME names -> domain names UNION
        in_clash_tree t1 UNION in_clash_tree t2 | NONE -> in_clash_tree
        t1 UNION in_clash_tree t2)) /\
     (!t1 t2. in_clash_tree (Seq t1 t2) = in_clash_tree t1 UNION
       in_clash_tree t2)`)
  CHEAT_TAC;;

let find_bijection_clash_tree_invariants =
  cake_theorem "find_bijection_clash_tree_invariants"
  (fun () ->
    `!st ct regset.
     good_bijection_state st regset ==>
     good_bijection_state (find_bijection_clash_tree st ct)
       (in_clash_tree ct UNION regset)`)
  CHEAT_TAC;;

let find_bijection_init_invariants =
  cake_theorem "find_bijection_init_invariants"
  (fun () ->
    `good_bijection_state find_bijection_init EMPTY`)
  CHEAT_TAC;;

let sptree_eq_list_def = cake_define
  `sptree_eq_list (s:int spt) l = (!i.
     i < LENGTH l ==>
     ((&0) < EL i l <=> sptree_lookup i s = NONE) /\
     (EL i l <= (&0) <=> sptree_lookup i s = SOME (EL i l)))`;;

let numset_list_add_if_lt_monad_correct =
  cake_theorem "numset_list_add_if_lt_monad_correct"
  (fun () ->
    `!int_beg sth l v.
     v <= 0 /\
     sptree_eq_list int_beg (linear_scan_hidden_state_int_beg sth)
       /\
     EVERY (\r. r < LENGTH (linear_scan_hidden_state_int_beg sth))
       l ==>
     (?sthout. numset_list_add_if_lt_monad l v sth = (M_success
       one,sthout) /\
     sptree_eq_list (numset_list_add_if_lt l v int_beg)
       (linear_scan_hidden_state_int_beg sthout) /\
     sthout = linear_scan_hidden_state_int_beg_fupd (K
       (linear_scan_hidden_state_int_beg sthout)) sth /\
     LENGTH (linear_scan_hidden_state_int_beg sthout) = LENGTH
       (linear_scan_hidden_state_int_beg sth))`)
  CHEAT_TAC;;

let numset_list_add_if_gt_monad_correct =
  cake_theorem "numset_list_add_if_gt_monad_correct"
  (fun () ->
    `!int_end sth l v.
     v <= 0 /\
     sptree_eq_list int_end (linear_scan_hidden_state_int_end sth)
       /\
     EVERY (\r. r < LENGTH (linear_scan_hidden_state_int_end sth))
       l ==>
     (?sthout. numset_list_add_if_gt_monad l v sth = (M_success
       one,sthout) /\
     sptree_eq_list (numset_list_add_if_gt l v int_end)
       (linear_scan_hidden_state_int_end sthout) /\
     sthout = linear_scan_hidden_state_int_end_fupd (K
       (linear_scan_hidden_state_int_end sthout)) sth /\
     LENGTH (linear_scan_hidden_state_int_end sthout) = LENGTH
       (linear_scan_hidden_state_int_end sth))`)
  CHEAT_TAC;;

let get_intervals_ct_monad_aux_correct =
  cake_theorem "get_intervals_ct_monad_aux_correct"
  (fun () ->
    `!ct sth live n int_beg int_end nout int_begout int_endout liveout.
     n <= 0 /\
     sptree_eq_list int_beg (linear_scan_hidden_state_int_beg sth)
       /\
     sptree_eq_list int_end (linear_scan_hidden_state_int_end sth)
       /\
     get_intervals_ct_aux ct n int_beg int_end live =
       (nout,int_begout,int_endout,liveout) /\
     LENGTH (linear_scan_hidden_state_int_end sth) = LENGTH
       (linear_scan_hidden_state_int_beg sth) /\
     (!r. in_clash_tree ct r ==> r < LENGTH
       (linear_scan_hidden_state_int_beg sth)) /\
     (!r. r IN domain live ==> r < LENGTH
       (linear_scan_hidden_state_int_beg sth)) ==>
     (?sthout. get_intervals_ct_monad_aux ct n live sth =
       (M_success (nout,liveout),sthout) /\
     sptree_eq_list int_begout (linear_scan_hidden_state_int_beg
       sthout) /\
     sptree_eq_list int_endout (linear_scan_hidden_state_int_end
       sthout) /\
     LENGTH (linear_scan_hidden_state_int_beg sthout) = LENGTH
       (linear_scan_hidden_state_int_beg sth) /\
     LENGTH (linear_scan_hidden_state_int_end sthout) = LENGTH
       (linear_scan_hidden_state_int_end sth) /\
     (!r. r IN domain liveout ==> r < LENGTH
       (linear_scan_hidden_state_int_beg sth)) /\
     sthout = linear_scan_hidden_state_int_end_fupd (K
       (linear_scan_hidden_state_int_end sthout))
       (linear_scan_hidden_state_int_beg_fupd (K
       (linear_scan_hidden_state_int_beg sthout)) sth) /\
     nout <= 0)`)
  CHEAT_TAC;;

let get_intervals_ct_monad_correct =
  cake_theorem "get_intervals_ct_monad_correct"
  (fun () ->
    `!ct sth n int_beg int_end.
     (!i. i < LENGTH (linear_scan_hidden_state_int_beg sth) ==> 0 <
       EL i (linear_scan_hidden_state_int_beg sth)) /\
     (!i. i < LENGTH (linear_scan_hidden_state_int_end sth) ==> 0 <
       EL i (linear_scan_hidden_state_int_end sth)) /\
     get_intervals_ct ct = (n,int_beg,int_end) /\
     LENGTH (linear_scan_hidden_state_int_end sth) = LENGTH
       (linear_scan_hidden_state_int_beg sth) /\
     (!r. in_clash_tree ct r ==> r < LENGTH
       (linear_scan_hidden_state_int_beg sth)) ==>
     (?sthout. get_intervals_ct_monad ct sth = (M_success n,sthout)
       /\
     sptree_eq_list int_beg (linear_scan_hidden_state_int_beg
       sthout) /\
     sptree_eq_list int_end (linear_scan_hidden_state_int_end
       sthout) /\
     LENGTH (linear_scan_hidden_state_int_beg sthout) = LENGTH
       (linear_scan_hidden_state_int_beg sth) /\
     LENGTH (linear_scan_hidden_state_int_end sthout) = LENGTH
       (linear_scan_hidden_state_int_end sth) /\
     sthout = linear_scan_hidden_state_int_end_fupd (K
       (linear_scan_hidden_state_int_end sthout))
       (linear_scan_hidden_state_int_beg_fupd (K
       (linear_scan_hidden_state_int_beg sthout)) sth))`)
  CHEAT_TAC;;

let in_clash_tree_eq_live_tree_registers =
  cake_theorem "in_clash_tree_eq_live_tree_registers"
  (fun () ->
    `!ct r. in_clash_tree ct r <=> r IN (live_tree_registers
  (get_live_tree ct))`)
  CHEAT_TAC;;

let get_live_backward_in_live_tree_registers =
  cake_theorem "get_live_backward_in_live_tree_registers"
  (fun () ->
    `!lt live. domain (get_live_backward lt live) SUBSET domain live
  UNION live_tree_registers lt`)
  CHEAT_TAC;;

let fix_domination_live_tree_registers =
  cake_theorem "fix_domination_live_tree_registers"
  (fun () ->
    `!lt. live_tree_registers (fix_domination lt) =
  live_tree_registers lt`)
  CHEAT_TAC;;

let get_intervals_beg_less_end =
  cake_theorem "get_intervals_beg_less_end"
  (fun () ->
    `!lt n_in beg_in end_in n_out beg_out end_out.
     (!r. r IN domain beg_in ==> the 0 (sptree_lookup r beg_in) <=
       the 0 (sptree_lookup r end_in)) /\
     domain beg_in SUBSET domain end_in /\
     (n_out,beg_out,end_out) = get_intervals lt n_in beg_in end_in
       ==>
     (!r. r IN domain beg_out ==> the 0 (sptree_lookup r beg_out)
       <= the 0 (sptree_lookup r end_out)) /\
     domain beg_out SUBSET domain end_out`)
  CHEAT_TAC;;

let linear_reg_alloc_without_renaming_correct =
  cake_theorem "linear_reg_alloc_without_renaming_correct"
  (fun () ->
    `!k moves ct forced.
     (!i. i < LENGTH (linear_scan_hidden_state_int_beg sth) ==> 0 <
       EL i (linear_scan_hidden_state_int_beg sth)) /\
     (!i. i < LENGTH (linear_scan_hidden_state_int_end sth) ==> 0 <
       EL i (linear_scan_hidden_state_int_end sth)) /\
     LENGTH (linear_scan_hidden_state_int_end sth) = LENGTH
       (linear_scan_hidden_state_int_beg sth) /\
     (!r. MEM r reglist_unsorted <=> in_clash_tree ct r) /\
     (!r. in_clash_tree ct r ==> r < LENGTH
       (linear_scan_hidden_state_int_beg sth)) /\
     EVERY (\(r1,r2). in_clash_tree ct r1 /\ in_clash_tree ct r2)
       forced /\
     EVERY (\(r1,r2). r1 < LENGTH (linear_scan_hidden_state_colors
       sth) /\ r2 < LENGTH (linear_scan_hidden_state_colors sth)) (MAP
       SND moves) /\
     LENGTH reglist_unsorted <= LENGTH
       (linear_scan_hidden_state_sorted_regs sth) /\
     LENGTH moves <= LENGTH (linear_scan_hidden_state_sorted_moves
       sth) /\
     LENGTH (linear_scan_hidden_state_colors sth) = LENGTH
       (linear_scan_hidden_state_int_beg sth) /\
     LENGTH (linear_scan_hidden_state_int_end sth) = LENGTH
       (linear_scan_hidden_state_int_beg sth) /\
     ALL_DISTINCT reglist_unsorted ==>
     (?sthout livein flivein.
     st_ex_ignore_bind
      (get_intervals_ct_monad ct) (
      linear_reg_alloc_intervals k forced moves reglist_unsorted)
        sth = (M_success one,sthout) /\
     check_clash_tree (\r. EL r (linear_scan_hidden_state_colors
       sthout)) ct LN LN = SOME (livein,flivein) /\
     (!r. in_clash_tree ct r ==>
      (if is_phy_var r then
        EL r (linear_scan_hidden_state_colors sthout) = r DIV 2
          else if is_stack_var r then
        k <= EL r (linear_scan_hidden_state_colors sthout) else
        T)) /\
     EVERY (\(r1,r2). EL r1 (linear_scan_hidden_state_colors
       sthout) = EL r2 (linear_scan_hidden_state_colors sthout) ==> r1 =
       r2) forced /\
     LENGTH (linear_scan_hidden_state_colors sthout) = LENGTH
       (linear_scan_hidden_state_colors sth))`)
  CHEAT_TAC;;

let check_col_apply_bijection = cake_theorem "check_col_apply_bijection"
  (fun () ->
    `!(cutset:1 spt) livein flivein f.
     (!r. r IN bijdom ==> (appbij r) IN bijcodom /\ appinvbij
       (appbij r) = r) /\
     (!r. r IN bijcodom ==> (appinvbij r) IN bijdom /\ appbij
       (appinvbij r) = r) /\
     domain cutset SUBSET bijdom /\
     check_col f (foldi (\r _1 acc. sptree_insert (appbij r) one
       acc) 0 LN cutset) = SOME (livein,flivein) ==>
     (?livein' flivein'. check_col (\r. f (appbij r)) cutset = SOME
       (livein',flivein') /\
     domain livein' = IMAGE appinvbij (domain livein))`)
  CHEAT_TAC;;


let check_partial_col_apply_bijection =
  cake_theorem "check_partial_col_apply_bijection"
  (fun () ->
    `!l live flive live' flive' livein flivein.
     (!r. r IN bijdom ==> (appbij r) IN bijcodom /\ appinvbij
       (appbij r) = r) /\
     (!r. r IN bijcodom ==> (appinvbij r) IN bijdom /\ appbij
       (appinvbij r) = r) /\
     (set_of_list l) SUBSET bijdom /\
     (domain live) SUBSET bijcodom /\
     domain flive = IMAGE f (domain live) /\
     domain flive' = IMAGE (f o appbij) (domain live') /\
     domain live' = IMAGE appinvbij (domain live) /\
     INJ f (domain live) UNIV /\
     check_partial_col f (MAP appbij l) live flive = SOME
       (livein,flivein) ==>
     (?livein' flivein'. check_partial_col (\r. f (appbij r)) l
       live' flive' = SOME (livein',flivein') /\
     domain livein' = IMAGE appinvbij (domain livein))`)
  CHEAT_TAC;;

let check_clash_tree_output_subset =
  cake_theorem "check_clash_tree_output_subset"
  (fun () ->
    `!ct live flive livein flivein.
     check_clash_tree f ct live flive = SOME (livein,flivein) ==>
     domain livein SUBSET domain live UNION in_clash_tree ct`)
  CHEAT_TAC;;

let domain_apply_bij_set = cake_theorem "domain_apply_bij_set"
  (fun () ->
    `!s bij. domain (foldi (\r _2 acc. sptree_insert (the 0
  (sptree_lookup r bij)) one acc) 0 LN s) = IMAGE (\r. the 0
  (sptree_lookup r bij)) (domain s)`)
  CHEAT_TAC;;

let in_clash_tree_apply_bij = cake_theorem "in_clash_tree_apply_bij"
  (fun () ->
    `!bij ct.
     in_clash_tree ct SUBSET domain bij ==>
     in_clash_tree (apply_bij_on_clash_tree ct bij) = IMAGE (\r.
       the 0 (sptree_lookup r bij)) (in_clash_tree ct)`)
  CHEAT_TAC;;

let check_clash_tree_apply_bijection =
  cake_theorem "check_clash_tree_apply_bijection"
  (fun () ->
    `!bij invbij f ct live flive live' flive' livein flivein.
     sp_inverts bij invbij /\
     sp_inverts invbij bij /\
     in_clash_tree ct SUBSET domain bij /\
     domain live SUBSET domain invbij /\
     domain flive = IMAGE f (domain live) /\
     domain flive' = IMAGE (\r. f (the 0 (sptree_lookup r bij)))
       (domain live') /\
     domain live' = IMAGE (\r. the 0 (sptree_lookup r invbij))
       (domain live) /\
     INJ f (domain live) UNIV /\
     check_clash_tree f (apply_bij_on_clash_tree ct bij) live flive
       = SOME (livein,flivein) ==>
     (?livein' flivein'. check_clash_tree (\r. f (the 0
       (sptree_lookup r bij))) ct live' flive' = SOME (livein',flivein')
       /\
     domain livein' = IMAGE (\r. the 0 (sptree_lookup r invbij))
       (domain livein))`)
  CHEAT_TAC;;

let extract_coloration_output = cake_theorem "extract_coloration_output"
  (fun () ->
    `!bij invbij sth l acc.
     sp_inverts bij invbij /\
     sp_inverts invbij bij /\
     EVERY (\r. r IN domain invbij) l /\
     EVERY (\r. r < LENGTH (linear_scan_hidden_state_colors sth)) l
       ==>
     (?col. extract_coloration invbij l acc sth = (M_success
       col,sth) /\
     (!r. r IN domain bij ==>
      (if MEM (the 0 (sptree_lookup r bij)) l then
        sptree_lookup r col = SOME (EL (the 0 (sptree_lookup r
          bij)) (linear_scan_hidden_state_colors sth)) else
        sptree_lookup r col = sptree_lookup r acc)) /\
     domain col SUBSET domain bij UNION domain acc)`)
  CHEAT_TAC;;

(* TODO: move *)
let LENGTH_toAList = cake_theorem "LENGTH_toAList"
  (fun () ->
    `!s. LENGTH (toAList s) = sptree_size s`)
  CHEAT_TAC;;

let check_col_equal_col = cake_theorem "check_col_equal_col"
  (fun () ->
    `!s f1 f2.
       (!r. r IN domain s ==> f1 r = f2 r) ==>
       check_col f1 s = check_col f2 s`)
  CHEAT_TAC;;

let check_partial_col_equal_col =
  cake_theorem "check_partial_col_equal_col"
  (fun () ->
    `!l live flive f1 f2.
     (!r. MEM r l ==> f1 r = f2 r) ==>
     check_partial_col f1 l live flive = check_partial_col f2 l
       live flive`)
  CHEAT_TAC;;

let check_clash_tree_equal_col =
  cake_theorem "check_clash_tree_equal_col"
  (fun () ->
    `!f1 f2 ct live flive.
     (!r. r IN in_clash_tree ct ==> f1 r = f2 r) /\
     (!r. r IN domain live ==> f1 r = f2 r) ==>
     check_clash_tree f1 ct live flive = check_clash_tree f2 ct
       live flive`)
  CHEAT_TAC;;

let linear_scan_reg_alloc_correct =
  cake_theorem "linear_scan_reg_alloc_correct"
  (fun () ->
    `!k moves ct forced.
       EVERY (\(r1,r2). in_clash_tree ct r1 /\ in_clash_tree ct r2)
         forced ==>
       (?col livein flivein.
       linear_scan_reg_alloc k moves ct forced = M_success col /\
       check_clash_tree (sp_default col) ct LN LN = SOME
         (livein,flivein) /\
       (!r. in_clash_tree ct r ==>
         r IN domain col /\
         (if is_phy_var r then
           sp_default col r = r DIV 2 else if is_stack_var r then
           k <= (sp_default col r) else
           T)) /\
       (!r. r IN domain col ==> in_clash_tree ct r) /\
       EVERY (\(r1,r2). (sp_default col) r1 = (sp_default col) r2
         ==> r1 = r2) forced)`)
  CHEAT_TAC;;

hol4_only "++" "APPEND";;
