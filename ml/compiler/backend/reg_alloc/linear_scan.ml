(* ======================================================== *)
(*  linear_scan: ported from HOL4's
    compiler/backend/reg_alloc/linear_scanScript.sml
    A definition theory, with 67 definitions, 4 datatypes and 5
    theorems.  Needed by 6 files of the port.  *)
(* ======================================================== *)

(*
  A linear-scan register allocator.
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "lib/sptree.ml";;
needs "lib/state_transformer.ml";;
needs "misc/misc.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "linear_scan"
  ["ml_monadBase"; "mllist"; "reg_alloc"];;

let live_tree_INDUCT,live_tree_RECURSION = define_datatype
  "live_tree = linear_scan_Writes (num list) | linear_scan_Reads (num \
   list) | linear_scan_Branch (live_tree) (live_tree) | \
   linear_scan_Seq (live_tree) (live_tree)";;


let numset_list_insert_def,numset_list_insert_ind = define_rec
  [`linear_scan_numset_list_insert [] t = t`;
   `linear_scan_numset_list_insert (CONS x xs) t =
  linear_scan_numset_list_insert xs (sptree_insert x one t)`];;

let numset_list_insert_nottailrec_def,
    numset_list_insert_nottailrec_ind =
  define_rec
  [`numset_list_insert_nottailrec [] t = t`;
   `numset_list_insert_nottailrec (CONS x xs) t = sptree_insert x
  one (numset_list_insert_nottailrec xs t)`];;

let get_live_tree_def,get_live_tree_ind = define_rec
  [`get_live_tree (reg_alloc_Delta wr rd) =
      linear_scan_Seq (linear_scan_Reads rd) (linear_scan_Writes
        wr)`;
   `get_live_tree (reg_alloc_Set cutset) =
      (let cutlist = MAP FST (toAList cutset) in
      linear_scan_Reads cutlist)`;
   `get_live_tree (reg_alloc_Branch optcutset ct1 ct2) =
      (let lt1 = get_live_tree ct1 in
      let lt2 = get_live_tree ct2 in
      match optcutset with SOME cutset ->
          (let cutlist = MAP FST (toAList cutset) in
          linear_scan_Seq (linear_scan_Reads cutlist)
            (linear_scan_Branch lt1 lt2)) | NONE ->
            (linear_scan_Branch lt1 lt2))`;
   `get_live_tree (reg_alloc_Seq ct1 ct2) =
      (let lt2 = get_live_tree ct2 in
      let lt1 = get_live_tree ct1 in
      linear_scan_Seq lt1 lt2)`];;

let check_live_tree_def,check_live_tree_ind = define_rec
  [`check_live_tree f (linear_scan_Writes l) live flive =
      (match check_partial_col f l live flive with NONE -> NONE |
        SOME _2 ->
      (let livein = numset_list_delete l live in
      let flivein = numset_list_delete (MAP f l) flive in
      SOME (livein,flivein)))`;
   `check_live_tree f (linear_scan_Reads l) live flive =
      check_partial_col f l live flive`;
   `check_live_tree f (linear_scan_Branch lt1 lt2:live_tree) live flive
  =
      (match check_live_tree f lt1 live flive with NONE -> NONE |
        SOME (livein1,flivein1) ->
      (match check_live_tree f lt2 live flive with NONE -> NONE |
        SOME (livein2,flivein2) ->
      check_partial_col f (MAP FST (toAList (difference livein2
        livein1))) livein1 flivein1))`;
   `check_live_tree f (linear_scan_Seq lt1 lt2:live_tree) live flive =
      (match check_live_tree f lt2 live flive with NONE -> NONE |
        SOME (livein2,flivein2) ->
        check_live_tree f lt1 livein2 flivein2)`];;

let get_live_backward_def,get_live_backward_ind = define_rec
  [`get_live_backward (linear_scan_Writes l) live =
      numset_list_delete l live`;
   `get_live_backward (linear_scan_Reads l) live =
      linear_scan_numset_list_insert l live`;
   `get_live_backward (linear_scan_Branch lt1 lt2:live_tree) live =
      (let live1 = get_live_backward lt1 live in
      let live2 = get_live_backward lt2 live in
      linear_scan_numset_list_insert (MAP FST (toAList
        (difference live2 live1))) live1)`;
   `get_live_backward (linear_scan_Seq lt1 lt2:live_tree) live =
      get_live_backward lt1 (get_live_backward lt2 live)`];;

let fix_domination_def = new_definition
  `fix_domination lt =
       (let live = get_live_backward lt LN in
       if live = LN then lt else linear_scan_Seq
         (linear_scan_Writes (MAP FST (toAList live))) lt)`;;

let numset_list_add_if_def,numset_list_add_if_ind = define_rec
  [`numset_list_add_if [] (v:int) s P = s`;
   `numset_list_add_if (CONS x xs) (v:int) s P =
      (match sptree_lookup x s with (SOME v') ->
          (if P v v' then numset_list_add_if xs v (sptree_insert x v
            s) P else numset_list_add_if xs v s P) | NONE ->
          numset_list_add_if xs v (sptree_insert x v s) P)`];;

let numset_list_add_if_lt_def = new_definition
  `numset_list_add_if_lt l (v:int) s = numset_list_add_if l v s (<=)`;;

let numset_list_add_if_gt_def = new_definition
  `numset_list_add_if_gt l (v:int) s = numset_list_add_if l v s (\a
  b. b <= a)`;;

let size_of_live_tree_def,size_of_live_tree_ind = define_rec
  [`(
     size_of_live_tree (linear_scan_Writes l) =
       ((&1):int)) /\ (
     size_of_live_tree (linear_scan_Reads l) =
       ((&1):int)) /\ (
     size_of_live_tree (linear_scan_Branch lt1 lt2) =
       size_of_live_tree lt1 + size_of_live_tree lt2) /\ (
     size_of_live_tree (linear_scan_Seq lt1 lt2) =
       size_of_live_tree lt1 + size_of_live_tree lt2)`];;

let get_intervals_def,get_intervals_ind = define_rec
  [`get_intervals (linear_scan_Writes l) (n:int) int_beg int_end =
      (n - (&1),numset_list_add_if_lt l n
        int_beg,numset_list_add_if_gt l n int_end)`;
   `get_intervals (linear_scan_Reads l) (n:int) int_beg int_end =
      (n - (&1),int_beg,numset_list_add_if_gt l n int_end)`;
   `get_intervals (linear_scan_Branch lt1 lt2:live_tree) (n:int) int_beg
  int_end =
      (let (n2,int_beg2,int_end2) = get_intervals lt2 n int_beg
        int_end in
      get_intervals lt1 n2 int_beg2 int_end2)`;
   `get_intervals (linear_scan_Seq lt1 lt2:live_tree) (n:int) int_beg
  int_end =
      (let (n2,int_beg2,int_end2) = get_intervals lt2 n int_beg
        int_end in
      get_intervals lt1 n2 int_beg2 int_end2)`];;

(* compute the same thing as `get_intervals` (as says the `get_intervals_withlive_beg_eq_get_intervals_beg` theorem),
 * but has the following invariant: !r. r IN domain live ==> r NOTIN domain beg_in (as stated by the `get_intervals_withlive_live_intbeg` theorem *)
let get_intervals_withlive_def,get_intervals_withlive_ind = define_rec
  [`get_intervals_withlive (linear_scan_Writes l) (n:int) int_beg
  int_end live =
      (n - (&1),numset_list_add_if_lt l n
        int_beg,numset_list_add_if_gt l n int_end)`;
   `get_intervals_withlive (linear_scan_Reads l) (n:int) int_beg int_end
  live =
      (n - (&1),numset_list_delete l
        int_beg,numset_list_add_if_gt l n int_end)`;
   `get_intervals_withlive (linear_scan_Branch lt1 lt2:live_tree)
  (n:int) int_beg int_end live =
      (let (n2,int_beg2,int_end2) = get_intervals_withlive lt2 n
        int_beg int_end live in
      let (n1,int_beg1,int_end1) = get_intervals_withlive lt1 n2
        (difference int_beg2 live) int_end2 live in
      (n1,difference int_beg1 (sptree_union (get_live_backward
        lt1 live) (get_live_backward lt2 live)),int_end1))`;
   `get_intervals_withlive (linear_scan_Seq lt1 lt2:live_tree) (n:int)
  int_beg int_end live =
      (let (n2,int_beg2,int_end2) = get_intervals_withlive lt2 n
        int_beg int_end live in
      let (n1,int_beg1,int_end1) = get_intervals_withlive lt1 n2
        int_beg2 int_end2 (get_live_backward lt2 live) in
      (n1,int_beg1,int_end1))`];;

let check_number_property_def,check_number_property_ind = define_rec
  [`check_number_property (P:int->1 spt->bool) (linear_scan_Writes l)
  (n:int) live =
        (let n_out = n - (&1) in
        let live_out = numset_list_delete l live in
        P n_out live_out)`;
   `check_number_property (P:int->1 spt->bool) (linear_scan_Reads l)
  (n:int) live =
        (let n_out = n - (&1) in
        let live_out = linear_scan_numset_list_insert l live in
        P n_out live_out)`;
   `check_number_property (P:int->1 spt->bool) (linear_scan_Branch lt1
  lt2:live_tree) (n:int) live =
        (let r2 = check_number_property P lt2 n live in
        let r1 = check_number_property P lt1 (n - (size_of_live_tree
          lt2)) live in
        r1 /\ r2)`;
   `check_number_property (P:int->1 spt->bool) (linear_scan_Seq lt1
  lt2:live_tree) (n:int) live =
        (let r2 = check_number_property P lt2 n live in
        let r1 = check_number_property P lt1 (n - size_of_live_tree
          lt2) (get_live_backward lt2 live) in
        r1 /\ r2)`];;

let check_number_property_strong_def,check_number_property_strong_ind =
  define_rec
  [`check_number_property_strong (P:int->1 spt->bool)
  (linear_scan_Writes l) (n:int) live =
        (let n_out = n - (&1) in
        let live_out = numset_list_delete l live in
        P n_out live_out)`;
   `check_number_property_strong (P:int->1 spt->bool) (linear_scan_Reads
  l) (n:int) live =
        (let n_out = n - (&1) in
        let live_out = linear_scan_numset_list_insert l live in
        P n_out live_out)`;
   `check_number_property_strong (P:int->1 spt->bool)
  (linear_scan_Branch lt1 lt2:live_tree) (n:int) live =
        (let r2 = check_number_property_strong P lt2 n live in
        let r1 = check_number_property_strong P lt1 (n -
          (size_of_live_tree lt2)) live in
        r1 /\ r2 /\ P (n - (size_of_live_tree (linear_scan_Branch
          lt1 lt2))) (get_live_backward (linear_scan_Branch lt1 lt2)
          live))`;
   `check_number_property_strong (P:int->1 spt->bool) (linear_scan_Seq
  lt1 lt2:live_tree) (n:int) live =
        (let r2 = check_number_property_strong P lt2 n live in
        let r1 = check_number_property_strong P lt1 (n -
          size_of_live_tree lt2) (get_live_backward lt2 live) in
        r1 /\ r2)`];;

let check_startlive_prop_def,check_startlive_prop_ind = define_rec
  [`(
     check_startlive_prop (linear_scan_Writes l) n beg end ndef =
         (!r. MEM r l ==> (option_CASE (sptree_lookup r beg) ndef
           (\x. x) <= n /\
                         (?v. sptree_lookup r end = SOME v /\ n <=
                           v)))) /\ (
     check_startlive_prop (linear_scan_Reads l) n beg end ndef =
         T) /\ (
     check_startlive_prop (linear_scan_Branch lt1 lt2) n beg end
       ndef =
         (let r2 = check_startlive_prop lt2 n beg end ndef in
         let r1 = check_startlive_prop lt1 (n - (size_of_live_tree
           lt2)) beg end ndef in
         r1 /\ r2)) /\ (
     check_startlive_prop (linear_scan_Seq lt1 lt2) n beg end ndef =
         (let r2 = check_startlive_prop lt2 n beg end ndef in
         let r1 = check_startlive_prop lt1 (n - size_of_live_tree
           lt2) beg end ndef in
         r1 /\ r2))`];;

let _ = size_thms "live_tree";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let live_tree_registers_def,live_tree_registers_ind = define_wf
  `MEASURE (\x0. live_tree_size x0)`
  [`live_tree_registers (linear_scan_Writes l) = set_of_list l`;
   `live_tree_registers (linear_scan_Reads l) = set_of_list l`;
   `live_tree_registers (linear_scan_Branch lt1 lt2:live_tree) =
  live_tree_registers lt1 UNION live_tree_registers lt2`;
   `live_tree_registers (linear_scan_Seq lt1 lt2:live_tree) =
  live_tree_registers lt1 UNION live_tree_registers lt2`];;

let interval_intersect_def = new_definition
  `interval_intersect ((l1:int),(r1:int)) (l2,r2) = (l1 <= r2 /\ l2
  <= r1)`;;

let point_inside_interval_def = new_definition
  `point_inside_interval ((l:int),(r:int)) n = (l <= n /\ n <= r)`;;

let check_intervals_def = new_definition
  `check_intervals f int_beg int_end = (!r1 r2.
     r1 IN domain int_beg /\ r2 IN domain int_beg /\
     interval_intersect (THE (sptree_lookup r1 int_beg),THE
       (sptree_lookup r1 int_end)) (THE (sptree_lookup r2 int_beg),THE
       (sptree_lookup r2 int_end)) /\
     f r1 = f r2 ==>
     r1 = r2)`;;

let get_intervals_ct_aux_def,get_intervals_ct_aux_ind = define_rec
  [`get_intervals_ct_aux (reg_alloc_Delta wr rd) (n:int) int_beg int_end
  live =
      (n - (&2),numset_list_add_if_lt wr n
        int_beg,numset_list_add_if_gt rd (n - (&1))
        (numset_list_add_if_gt wr n
        int_end),linear_scan_numset_list_insert rd
        (numset_list_delete wr live))`;
   `get_intervals_ct_aux (reg_alloc_Set cutset) (n:int) int_beg int_end
  live =
      (n - (&1),int_beg,numset_list_add_if_gt (MAP FST (toAList
        cutset)) n int_end,sptree_union cutset live)`;
   `get_intervals_ct_aux (reg_alloc_Branch optcutset ct1 ct2) (n:int)
  int_beg int_end live =
      (let (n2,int_beg2,int_end2,live2) = get_intervals_ct_aux ct2 n
        int_beg int_end live in
      let (n1,int_beg1,int_end1,live1) = get_intervals_ct_aux ct1 n2
        int_beg2 int_end2 live in
      match optcutset with NONE ->
        (n1,int_beg1,int_end1,sptree_union live1 live2) | SOME cutset
        -> (n1 - (&1),int_beg1,numset_list_add_if_gt (MAP FST
        (toAList cutset)) n1 int_end1,sptree_union cutset
        (sptree_union live1 live2)))`;
   `get_intervals_ct_aux (reg_alloc_Seq ct1 ct2) (n:int) int_beg int_end
  live =
      (let (n2,int_beg2,int_end2,live2) = get_intervals_ct_aux ct2 n
        int_beg int_end live in
      get_intervals_ct_aux ct1 n2 int_beg2 int_end2 live2)`];;

let get_intervals_ct_def = new_definition
  `get_intervals_ct ct =
       (let (n,int_beg,int_end,live) = get_intervals_ct_aux ct (&0)
         LN LN LN in
       let listlive = MAP FST (toAList live) in
       (n - (&1),numset_list_add_if_lt listlive n
         int_beg,numset_list_add_if_gt listlive n int_end))`;;

let linear_scan_state_FIELDS = define_record "linear_scan_state"
  ["active","(int#num) list";
   (* interval end # reg *)
   "colorpool","num list";
   "phyregs","1 spt";
   "colornum","num";
   "colormax","num";
   "stacknum","num"];;

let linear_scan_hidden_state_FIELDS =
  define_record "linear_scan_hidden_state"
  ["colors","num list";
   "int_beg","int list";
   "int_end","int list";
   "sorted_regs","num list";
   "sorted_moves","(num#num#num) list"];;

(* HOL4 makes the monadic accessors of linear_scan_hidden_state with ML
   code
   (define_monad_access_funs of ml_monadBaseLib); these are
   the definitions that it makes *)
let get_colors_def = new_definition
  `get_colors = (\state. (M_success (linear_scan_hidden_state_colors
  state),state))`;;

let set_colors_def = new_definition
  `set_colors x =
     (\state. (M_success one,linear_scan_hidden_state_colors_fupd
       (K x) state))`;;

let get_int_beg_def = new_definition
  `get_int_beg = (\state. (M_success
  (linear_scan_hidden_state_int_beg state),state))`;;

let set_int_beg_def = new_definition
  `set_int_beg x =
     (\state. (M_success one,linear_scan_hidden_state_int_beg_fupd
       (K x) state))`;;

let get_int_end_def = new_definition
  `get_int_end = (\state. (M_success
  (linear_scan_hidden_state_int_end state),state))`;;

let set_int_end_def = new_definition
  `set_int_end x =
     (\state. (M_success one,linear_scan_hidden_state_int_end_fupd
       (K x) state))`;;

let get_sorted_regs_def = new_definition
  `get_sorted_regs = (\state. (M_success
  (linear_scan_hidden_state_sorted_regs state),state))`;;

let set_sorted_regs_def = new_definition
  `set_sorted_regs x =
     (\state. (M_success
       one,linear_scan_hidden_state_sorted_regs_fupd (K x) state))`;;

let get_sorted_moves_def = new_definition
  `get_sorted_moves = (\state. (M_success
  (linear_scan_hidden_state_sorted_moves state),state))`;;

let set_sorted_moves_def = new_definition
  `set_sorted_moves x =
     (\state. (M_success
       one,linear_scan_hidden_state_sorted_moves_fupd (K x) state))`;;


(* HOL4 linear_scanScript.sml:337-341: ML code, not ported *)

(* HOL4 linear_scanScript.sml:343-347: ML code, not ported *)

(* HOL4 linear_scanScript.sml:349-353: code that the source has in a
   comment *)

(* HOL4 makes the functions of the exception type state_exn a
   second time here (define_monad_exception_functions of
   ml_monadBaseLib); they are the same as the ones that
   reg_alloc makes, which the port uses *)
(* HOL4 linear_scanScript.sml:356: the overload failwith, which the
   port expands *)

(* HOL4 linear_scanScript.sml:358-359: the ML values that the
   definitions below antiquote *)

(* HOL4 makes the manipulators of the fixed size arrays with
   ML code (define_MFarray_manip_funs of ml_monadBaseLib);
   these are the definitions that it makes *)
let colors_length_def = new_definition
  `colors_length = Marray_length (\state.
  linear_scan_hidden_state_colors state)`;;

let colors_sub_def = new_definition
  `colors_sub = Marray_sub (\state. linear_scan_hidden_state_colors
  state) reg_alloc_Subscript`;;

let update_colors_def = new_definition
  `update_colors =
     Marray_update (\state. linear_scan_hidden_state_colors state)
       (\x state. linear_scan_hidden_state_colors_fupd (K x)
         state) reg_alloc_Subscript`;;

let int_beg_length_def = new_definition
  `int_beg_length = Marray_length (\state.
  linear_scan_hidden_state_int_beg state)`;;

let int_beg_sub_def = new_definition
  `int_beg_sub = Marray_sub (\state. linear_scan_hidden_state_int_beg
  state) reg_alloc_Subscript`;;

let update_int_beg_def = new_definition
  `update_int_beg =
     Marray_update (\state. linear_scan_hidden_state_int_beg state)
       (\x state. linear_scan_hidden_state_int_beg_fupd (K x)
         state) reg_alloc_Subscript`;;

let int_end_length_def = new_definition
  `int_end_length = Marray_length (\state.
  linear_scan_hidden_state_int_end state)`;;

let int_end_sub_def = new_definition
  `int_end_sub = Marray_sub (\state. linear_scan_hidden_state_int_end
  state) reg_alloc_Subscript`;;

let update_int_end_def = new_definition
  `update_int_end =
     Marray_update (\state. linear_scan_hidden_state_int_end state)
       (\x state. linear_scan_hidden_state_int_end_fupd (K x)
         state) reg_alloc_Subscript`;;

let sorted_regs_length_def = new_definition
  `sorted_regs_length = Marray_length (\state.
  linear_scan_hidden_state_sorted_regs state)`;;

let sorted_regs_sub_def = new_definition
  `sorted_regs_sub = Marray_sub (\state.
  linear_scan_hidden_state_sorted_regs state) reg_alloc_Subscript`;;

let update_sorted_regs_def = new_definition
  `update_sorted_regs =
     Marray_update (\state. linear_scan_hidden_state_sorted_regs
       state)
       (\x state. linear_scan_hidden_state_sorted_regs_fupd (K x)
         state) reg_alloc_Subscript`;;

let sorted_moves_length_def = new_definition
  `sorted_moves_length = Marray_length (\state.
  linear_scan_hidden_state_sorted_moves state)`;;

let sorted_moves_sub_def = new_definition
  `sorted_moves_sub = Marray_sub (\state.
  linear_scan_hidden_state_sorted_moves state) reg_alloc_Subscript`;;

let update_sorted_moves_def = new_definition
  `update_sorted_moves =
     Marray_update (\state. linear_scan_hidden_state_sorted_moves
       state)
       (\x state. linear_scan_hidden_state_sorted_moves_fupd (K x)
         state) reg_alloc_Subscript`;;


(* HOL4 linear_scanScript.sml:363: ML code, not ported *)

(* HOL4 linear_scanScript.sml:365-369: ML code, not ported *)

(* HOL4 linear_scanScript.sml:371-372: a theorem that HOL4 states as
   the value of an ML expression: colors_accessor *)
(* HOL4 linear_scanScript.sml:373-374: a theorem that HOL4 states as
   the value of an ML expression: int_beg_accessor *)
(* HOL4 linear_scanScript.sml:375-376: a theorem that HOL4 states as
   the value of an ML expression: int_end_accessor *)
(* HOL4 linear_scanScript.sml:377-378: a theorem that HOL4 states as
   the value of an ML expression: sorted_regs_accessor *)
(* HOL4 linear_scanScript.sml:379-380: a theorem that HOL4 states as
   the value of an ML expression: sorted_moves_accessor *)

(* HOL4 linear_scanScript.sml:382-384: ML code, not ported *)

(* HOL4 linear_scanScript.sml:386-388: ML code, not ported *)

(* HOL4 linear_scanScript.sml:390-392: ML code, not ported *)

(* HOL4 linear_scanScript.sml:394-396: ML code, not ported *)

(* HOL4 linear_scanScript.sml:398-400: ML code, not ported *)

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let numset_list_add_if_lt_monad_def,numset_list_add_if_lt_monad_ind =
  define_wf
  `MEASURE (\(x0,x1). list_size (\n. n) x0)`
  [`numset_list_add_if_lt_monad [] (v:int) =
      st_ex_return one`;
   `numset_list_add_if_lt_monad (CONS r rs) (v:int) =
      st_ex_bind (int_beg_sub r) (\
        begr.
        if (&0) < begr then
          st_ex_ignore_bind
            (update_int_beg r v) (
            numset_list_add_if_lt_monad rs v) else if v <= begr then
          st_ex_ignore_bind
            (update_int_beg r v) (
            numset_list_add_if_lt_monad rs v) else
          numset_list_add_if_lt_monad rs v)`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let numset_list_add_if_gt_monad_def,numset_list_add_if_gt_monad_ind =
  define_wf
  `MEASURE (\(x0,x1). list_size (\n. n) x0)`
  [`numset_list_add_if_gt_monad [] (v:int) =
      st_ex_return one`;
   `numset_list_add_if_gt_monad (CONS r rs) (v:int) =
      st_ex_bind (int_end_sub r) (\
        begr.
        if (&0) < begr then
          st_ex_ignore_bind
            (update_int_end r v) (
            numset_list_add_if_gt_monad rs v) else if begr <= v then
          st_ex_ignore_bind
            (update_int_end r v) (
            numset_list_add_if_gt_monad rs v) else
          numset_list_add_if_gt_monad rs v)`];;

let _ = size_thms "clash_tree";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let get_intervals_ct_monad_aux_def,get_intervals_ct_monad_aux_ind =
  define_wf
  `MEASURE (\(x0,x1,x2). clash_tree_size x0)`
  [`get_intervals_ct_monad_aux (reg_alloc_Delta wr rd) (n:int) live =
      st_ex_ignore_bind
        (numset_list_add_if_lt_monad wr n) (st_ex_ignore_bind
        (numset_list_add_if_gt_monad wr n) (st_ex_ignore_bind
        (numset_list_add_if_gt_monad rd (n - (&1))) (
        st_ex_return (n - (&2),linear_scan_numset_list_insert rd
          (numset_list_delete wr live)))))`;
   `get_intervals_ct_monad_aux (reg_alloc_Set cutset) (n:int) live =
      st_ex_ignore_bind
        (numset_list_add_if_gt_monad (MAP FST (toAList cutset)) n) (
        st_ex_return (n - (&1),sptree_union cutset live))`;
   `get_intervals_ct_monad_aux (reg_alloc_Branch optcutset ct1 ct2)
  (n:int) live =
      st_ex_bind (get_intervals_ct_monad_aux ct2 n live) (\
        (n2,live2). st_ex_bind (get_intervals_ct_monad_aux ct1 n2
          live) (\
        (n1,live1).
        match optcutset with NONE -> st_ex_return (n1,sptree_union
          live1 live2) | SOME cutset ->
          st_ex_ignore_bind
            (numset_list_add_if_gt_monad (MAP FST (toAList cutset))
              n1) (
            st_ex_return (n1 - (&1),sptree_union cutset
              (sptree_union live1 live2)))))`;
   `get_intervals_ct_monad_aux (reg_alloc_Seq ct1 ct2) (n:int) live =
      st_ex_bind (get_intervals_ct_monad_aux ct2 n live) (\
        (n2,live2).
        get_intervals_ct_monad_aux ct1 n2 live2)`];;

let get_intervals_ct_monad_def = new_definition
  `get_intervals_ct_monad ct =
     st_ex_bind (get_intervals_ct_monad_aux ct (&0) LN) (\
       (n,live). st_ex_ignore_bind
       (numset_list_add_if_lt_monad (MAP FST (toAList live)) n)
         (st_ex_ignore_bind
       (numset_list_add_if_gt_monad (MAP FST (toAList live)) n) (
       st_ex_return (n - (&1)))))`;;

(* the termination relation that HOL4 gives is
     MEASURE (\(_3,st). LENGTH (linear_scan_state_active st))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 linear_scanScript.sml:514-517: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let remove_inactive_intervals_def,remove_inactive_intervals_ind =
  define_guess_cheat
  [`remove_inactive_intervals beg st =
     (match linear_scan_state_active st with [] -> st_ex_return st |
       CONS (e,r) activetail -> (
       if e < beg then
         st_ex_bind (colors_sub r) (\
           col.
           let st' = linear_scan_state_colorpool_fupd (\l. CONS col
             l) (linear_scan_state_active_fupd (K activetail) st) in
           remove_inactive_intervals beg st') else
         st_ex_return st))`];;

let add_active_interval_def,add_active_interval_ind = define_rec
  [`add_active_interval v [] = [v]`;
   `add_active_interval (v1:int#num) (CONS v2 tail) =
        (if FST v1 <= FST v2 then CONS v1 (CONS v2 tail) else
          CONS v2 (add_active_interval v1 tail))`];;

let find_color_in_list_def,find_color_in_list_ind = define_rec
  [`find_color_in_list [] (forbidden:1 spt) = NONE`;
   `find_color_in_list (CONS r rs) (forbidden:1 spt) =
        (if sptree_lookup r forbidden = NONE then
          SOME (r,rs) else
          match find_color_in_list rs forbidden with NONE ->
            NONE | SOME (col,rest) -> SOME (col,CONS r rest))`];;

let find_color_in_colornum_def = new_definition
  `find_color_in_colornum st (forbidden:1 spt) =
       (if linear_scan_state_colormax st <=
         linear_scan_state_colornum st then
         (st,NONE) else
         (linear_scan_state_colornum_fupd ((+) 1) st,SOME
           (linear_scan_state_colornum st)))`;;

let find_color_def = new_definition
  `find_color st (forbidden:1 spt) =
       (match find_color_in_list (linear_scan_state_colorpool st)
         forbidden with SOME (col,rest) ->
         (linear_scan_state_colorpool_fupd (K rest) st,SOME col) |
         NONE -> find_color_in_colornum st forbidden)`;;

let spill_register_def = new_definition
  `spill_register st reg =
     st_ex_ignore_bind
       (update_colors reg (linear_scan_state_stacknum st)) (
       st_ex_return (linear_scan_state_stacknum_fupd ((+) 1) st))`;;

let color_register_def = new_definition
  `color_register st reg col rend =
     st_ex_ignore_bind
       (update_colors reg col) (
       if is_phy_var reg then
         st_ex_return (linear_scan_state_phyregs_fupd (sptree_insert
           col one) (linear_scan_state_active_fupd (add_active_interval
           (rend,reg))
           st)) else
         st_ex_return (linear_scan_state_active_fupd
           (add_active_interval (rend,reg)) st))`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let find_last_stealable_def,find_last_stealable_ind = define_wf
  `MEASURE (\(x0,x1). list_size (pair_size (\x. 0) (\n. n)) x0)`
  [`find_last_stealable [] (forbidden:1 spt) =
        st_ex_return NONE`;
   `find_last_stealable (CONS x xs) (forbidden:1 spt) =
      st_ex_bind (find_last_stealable xs forbidden) (\
        recursion.
        match recursion with SOME (steal,rest) -> st_ex_return (SOME
          (steal,CONS x rest)) | NONE -> (
            st_ex_bind (colors_sub (SND x)) (\
              xcol.
              if ~(is_phy_var (SND x)) /\ (sptree_lookup xcol
                forbidden = NONE) then
                st_ex_return (SOME (x,xs)) else
                st_ex_return NONE)))`];;

let find_spill_def = new_definition
  `find_spill st (forbidden:1 spt) reg rend force =
     st_ex_bind (find_last_stealable (linear_scan_state_active st)
       forbidden) (\
       stealable.
       match stealable with NONE -> spill_register st reg | SOME
         ((stealend,stealreg),newactive) ->
         (if force \/ rend < stealend then
           st_ex_bind (colors_sub stealreg) (\
             stealcolor. st_ex_bind (spill_register
               (linear_scan_state_active_fupd (K newactive) st)
               stealreg) (\
             st'.
             color_register st' reg stealcolor rend)) else
           spill_register st reg))`;;

let linear_reg_alloc_step_aux_def = new_definition
  `linear_reg_alloc_step_aux st (forbidden:1 spt) preferred reg rend
  force =
     // TODO: this might be slow
     (let preferred_filtered = FILTER (\c. MEM c
       (linear_scan_state_colorpool st)) preferred in
     match find_color_in_list preferred_filtered forbidden with SOME
       (col,_4) -> color_register (linear_scan_state_colorpool_fupd
       (FILTER ((\x y. ~(x = y)) col)) st) reg col rend | NONE -> (
       match find_color st forbidden with (st',SOME col) ->
         color_register st' reg col rend | (st',NONE) -> find_spill
         st' forbidden reg rend force))`;;

let linear_reg_alloc_step_pass1_def = new_definition
  `linear_reg_alloc_step_pass1 forced moves st reg =
     st_ex_bind (int_beg_sub reg) (\
       rbeg. st_ex_bind (int_end_sub reg) (\
       rend. st_ex_bind (remove_inactive_intervals rbeg st) (\
       st'.
       if is_stack_var reg then
         spill_register st' reg else
         st_ex_bind (st_ex_MAP colors_sub (the [] (sptree_lookup reg
           forced))) (\
           forced_forbidden_list.
           let forced_forbidden = fromAList (MAP (\c. (c,one))
             forced_forbidden_list) in
           if is_phy_var reg then
             if reg < 2 * (linear_scan_state_colormax st') then
               let forbidden = sptree_union
                 (linear_scan_state_phyregs st') forced_forbidden in
               linear_reg_alloc_step_aux st' forbidden [] reg rend T
                 else
               spill_register st' reg else
             st_ex_bind (st_ex_MAP colors_sub (the [] (sptree_lookup
               reg moves))) (\
               moves_preferred.
               linear_reg_alloc_step_aux st' forced_forbidden
                 moves_preferred reg rend F)))))`;;

let linear_reg_alloc_step_pass2_def = new_definition
  `linear_reg_alloc_step_pass2 forced moves st reg =
     st_ex_bind (int_beg_sub reg) (\
       rbeg. st_ex_bind (int_end_sub reg) (\
       rend. st_ex_bind (remove_inactive_intervals rbeg st) (\
       st'. st_ex_bind (st_ex_MAP colors_sub (the [] (sptree_lookup
         reg forced))) (\
       forced_forbidden_list. st_ex_bind (st_ex_return (fromAList
         (MAP (\c. (c,one)) forced_forbidden_list))) (\
       forced_forbidden. st_ex_bind (st_ex_MAP colors_sub (the []
         (sptree_lookup reg moves))) (\
       moves_preferred.
       if is_phy_var reg then
         let forbidden = sptree_union (linear_scan_state_phyregs st')
           forced_forbidden in
           linear_reg_alloc_step_aux st' forbidden [] reg rend F else
         linear_reg_alloc_step_aux st' forced_forbidden
           moves_preferred reg rend F))))))`;;


let linear_reg_alloc_pass1_initial_state_def = new_definition
  `linear_reg_alloc_pass1_initial_state k =
     mk_linear_scan_state [] [] LN 0 k k`;;

let linear_reg_alloc_pass2_initial_state_def = new_definition
  `linear_reg_alloc_pass2_initial_state k nreg =
     mk_linear_scan_state [] [] LN k (k + nreg) (k + nreg)`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let find_reg_exchange_def,find_reg_exchange_ind = define_wf
  `MEASURE (\(x0,x1,x2). list_size (\n. n) x0)`
  [`find_reg_exchange [] exch invexch = st_ex_return (exch,invexch)`;
   `find_reg_exchange (CONS r rs) exch invexch =
      st_ex_bind (colors_sub r) (\
        col1.
        let fcol1 = r DIV 2 in
        let col2 = option_CASE (sptree_lookup fcol1 invexch) fcol1
          (\x. x) in
        let fcol2 = option_CASE (sptree_lookup col1 exch) col1 (\x.
          x) in
        find_reg_exchange rs (sptree_insert col1 fcol1
          (sptree_insert col2 fcol2 exch)) (sptree_insert fcol1
          col1 (sptree_insert fcol2 col2 invexch)))`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let MAP_colors_def,MAP_colors_ind = define_wf
  `MEASURE (\(x0,x1). (\n. n) x1)`
  [`MAP_colors f 0 = st_ex_return one`;
   `MAP_colors f (SUC n) =
      st_ex_bind (colors_sub n) (\
        col. st_ex_ignore_bind
        (update_colors n (f col)) (
        MAP_colors f n))`];;

let apply_reg_exchange_def = new_definition
  `apply_reg_exchange phyregs =
     st_ex_bind (find_reg_exchange phyregs LN LN) (\
       (exch,invexch). st_ex_bind colors_length (\
       col_size.
       MAP_colors (\c. option_CASE (sptree_lookup c exch) c (\x.
         x)) col_size))`;;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let st_ex_FOLDL_def,st_ex_FOLDL_ind = define_guess_cheat
  [`st_ex_FOLDL f e [] = st_ex_return e`;
   `st_ex_FOLDL f e (CONS x xs) =
      st_ex_bind (f e x) (\
        e'.
        st_ex_FOLDL f e' xs)`];;

(* like st_ex_FILTER, but preserve the order *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let st_ex_FILTER_good_def,st_ex_FILTER_good_ind = define_guess_cheat
  [`st_ex_FILTER_good P [] = st_ex_return []`;
   `st_ex_FILTER_good P (CONS x xs) =
      st_ex_bind (P x) (\
        Px.
        if Px then
          st_ex_bind (st_ex_FILTER_good P xs) (\
            filter_xs.
            st_ex_return (CONS x filter_xs)) else
          st_ex_FILTER_good P xs)`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let edges_to_adjlist_def,edges_to_adjlist_ind = define_wf
  `MEASURE (\(x0,x1). list_size (pair_size (\n. n) (\n. n)) x0)`
  [`edges_to_adjlist [] acc = st_ex_return acc`;
   `edges_to_adjlist (CONS (a,b) abs') acc =
      (if a = b then
        edges_to_adjlist abs' acc else
        st_ex_bind (int_beg_sub a) (\
          bega. st_ex_bind (int_beg_sub b) (\
          begb.
          if bega < begb \/ (bega = begb /\ a <= b) then
            edges_to_adjlist abs' (sptree_insert b (CONS a (the []
              (sptree_lookup b acc))) acc) else
            edges_to_adjlist abs' (sptree_insert a (CONS b (the
              [] (sptree_lookup a acc))) acc))))`];;

let sort_moves_rev_def = new_definition
  `sort_moves_rev ls =
     sort (\((p:num),x) (p',x'). p < p') ls`;;

let swap_regs_def = new_definition
  `swap_regs i1 i2 =
     st_ex_bind (sorted_regs_sub i1) (\
       r1. st_ex_bind (sorted_regs_sub i2) (\
       r2. st_ex_ignore_bind
       (update_sorted_regs i1 r2) (
       update_sorted_regs i2 r1)))`;;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let partition_regs_def,partition_regs_ind = define_wf
  `MEASURE (\(l,rpiv,begrpiv,r). r - l)`
  [`partition_regs l rpiv begrpiv r =
     (if r <= l then
       st_ex_return l else
       st_ex_bind (sorted_regs_sub l) (\
         reg. st_ex_bind (int_beg_sub reg) (\
         begreg.
         if begreg < begrpiv \/ (begreg = begrpiv /\ reg <= rpiv)
           then
             partition_regs (l + 1) rpiv begrpiv r else
           st_ex_ignore_bind
             (swap_regs l (r - 1)) (
             partition_regs l rpiv begrpiv (r - 1)))))`];;

(* the termination relation that HOL4 gives is
     MEASURE (\(l,r). r - l)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let sort_regs_def,sort_regs_ind = define_guess_cheat
  [`sort_regs l r =
     (if r <= l + 1 then
       st_ex_return one else
       st_ex_bind (sorted_regs_sub l) (\
         rpiv. st_ex_bind (int_beg_sub rpiv) (\
         begrpiv. st_ex_bind (partition_regs (l + 1) rpiv begrpiv r)
           (\
         m. st_ex_ignore_bind
         (swap_regs l (m - 1)) (
         // TODO: this condition is necessary for the termination argument, but useless in practice
         if m <= l \/ r < m then
           st_ex_return one else
           st_ex_ignore_bind
             (sort_regs l (m - 1)) (
             sort_regs m r))))))`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let list_to_sorted_regs_def,list_to_sorted_regs_ind = define_wf
  `MEASURE (\(x0,x1). list_size (\n. n) x0)`
  [`list_to_sorted_regs [] n =
        st_ex_return one`;
   `list_to_sorted_regs (CONS r rs) n =
      st_ex_ignore_bind
        (update_sorted_regs n r) (
        list_to_sorted_regs rs (n + 1))`];;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let sorted_regs_to_list_def,sorted_regs_to_list_ind = define_wf
  `MEASURE (\(n,last). last - n)`
  [`sorted_regs_to_list n last =
     (if last <= n then
       st_ex_return [] else
       st_ex_bind (sorted_regs_sub n) (\
         r. st_ex_bind (sorted_regs_to_list (n + 1) last) (\
         l.
         st_ex_return (CONS r l))))`];;

let swap_moves_def = new_definition
  `swap_moves i1 i2 =
     st_ex_bind (sorted_moves_sub i1) (\
       r1. st_ex_bind (sorted_moves_sub i2) (\
       r2. st_ex_ignore_bind
       (update_sorted_moves i1 r2) (
       update_sorted_moves i2 r1)))`;;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let partition_moves_def,partition_moves_ind = define_wf
  `MEASURE (\(l,piv,r). r - l)`
  [`partition_moves l ppiv r =
     (if r <= l then
       st_ex_return l else
       st_ex_bind (sorted_moves_sub l) (\
         move'.
         if FST move' < ppiv then
           partition_moves (l + 1) ppiv r else
           st_ex_ignore_bind
             (swap_moves l (r - 1)) (
             partition_moves l ppiv (r - 1))))`];;

(* the termination relation that HOL4 gives is
     MEASURE (\(l,r). r - l)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let linear_scan_sort_moves_def,linear_scan_sort_moves_ind =
  define_guess_cheat
  [`linear_scan_sort_moves l r =
     (if r <= l + 1 then
       st_ex_return one else
       st_ex_bind (sorted_moves_sub l) (\
         piv. st_ex_bind (partition_moves (l + 1) (FST piv) r) (\
         m. st_ex_ignore_bind
         (swap_moves l (m - 1)) (
         // TODO: this condition is necessary for the termination argument, but useless in practice
         if m <= l \/ r < m then
           st_ex_return one else
           st_ex_ignore_bind
             (linear_scan_sort_moves l (m - 1)) (
             linear_scan_sort_moves m r)))))`];;


(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let list_to_sorted_moves_def,list_to_sorted_moves_ind = define_wf
  `MEASURE (\(x0,x1). list_size (pair_size (\n. n) (pair_size (\n. n)
  (\n. n))) x0)`
  [`list_to_sorted_moves [] n =
        st_ex_return one`;
   `list_to_sorted_moves (CONS r rs) n =
      st_ex_ignore_bind
        (update_sorted_moves n r) (
        list_to_sorted_moves rs (n + 1))`];;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let sorted_moves_to_list_def,sorted_moves_to_list_ind = define_wf
  `MEASURE (\(n,len). len - n)`
  [`sorted_moves_to_list n len =
     (if len <= n then
       st_ex_return [] else
       st_ex_bind (sorted_moves_sub n) (\
         r. st_ex_bind (sorted_moves_to_list (n + 1) len) (\
         l.
         st_ex_return (CONS r l))))`];;

let linear_reg_alloc_intervals_def = new_definition
  `linear_reg_alloc_intervals k forced moves reglist_unsorted =
       (let lenreg = LENGTH reglist_unsorted in
       let lenmoves = LENGTH moves in
       let st_init_pass1 = linear_reg_alloc_pass1_initial_state k in
       st_ex_ignore_bind
         (list_to_sorted_regs reglist_unsorted 0) (st_ex_ignore_bind
         (sort_regs 0 lenreg) (st_ex_bind (sorted_regs_to_list 0
           lenreg) (\
         reglist. st_ex_bind (st_ex_return (FILTER is_phy_var
           reglist)) (\
         phyregs. st_ex_bind (st_ex_return (FILTER (\r. r < 2 * k)
           phyregs)) (\
         phyphyregs. st_ex_bind (st_ex_return (FILTER (\r. 2 * k <=
           r) phyregs)) (\
         stackphyregs. st_ex_ignore_bind
         (list_to_sorted_moves moves 0) (st_ex_ignore_bind
         (linear_scan_sort_moves 0 lenmoves) (st_ex_bind
           (sorted_moves_to_list 0 lenmoves) (\
         smoves. st_ex_bind (edges_to_adjlist (MAP SND smoves) LN) (\
         moves_adjlist. st_ex_bind (edges_to_adjlist forced LN) (\
         forced_adjlist. st_ex_bind (st_ex_FOLDL
           (linear_reg_alloc_step_pass1 forced_adjlist moves_adjlist)
           st_init_pass1 reglist) (\
         st_end_pass1. st_ex_ignore_bind
         (apply_reg_exchange phyphyregs) (st_ex_bind
           (st_ex_FILTER_good (\r.
           st_ex_bind (colors_sub r) (\
             col.
             st_ex_return (is_stack_var r \/ k <= col))) reglist) (\
         stacklist. st_ex_bind (st_ex_return
           (linear_reg_alloc_pass2_initial_state k (LENGTH stacklist)))
           (\
         st_init_pass2. st_ex_bind (st_ex_return (fromAList (MAP (\r.
           (r,one)) stacklist))) (\
         stackset. st_ex_bind (st_ex_return (sptree_map (FILTER (\r.
           ~(sptree_lookup r stackset = NONE))) forced_adjlist)) (\
         forced_adjlist'. st_ex_bind (st_ex_return (sptree_map
           (FILTER (\r. ~(sptree_lookup r stackset = NONE)))
           moves_adjlist)) (\
         moves_adjlist'. st_ex_bind (st_ex_FOLDL
           (linear_reg_alloc_step_pass2 forced_adjlist' moves_adjlist')
           st_init_pass2 stacklist) (\
         st_end_pass2.
         apply_reg_exchange stackphyregs))))))))))))))))))))`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let extract_coloration_def,extract_coloration_ind = define_wf
  `MEASURE (\(x0,x1,x2). list_size (\n. n) x1)`
  [`extract_coloration invbij [] acc = st_ex_return acc`;
   `extract_coloration invbij (CONS r rs) acc =
      st_ex_bind (colors_sub r) (\
        col.
        extract_coloration invbij rs (sptree_insert (the 0
          (sptree_lookup r invbij)) col acc))`];;

let bijection_state_FIELDS = define_record "bijection_state"
  ["bij","num spt";
   "invbij","num spt";
   "nmax","num";
   "nstack","num";
   "nalloc","num"];;

let find_bijection_init_def = new_definition
  `find_bijection_init =
       mk_bijection_state LN LN 0 3 1`;;

let find_bijection_step_def = new_definition
  `find_bijection_step state r =
     (if ~(sptree_lookup r (bijection_state_bij state) = NONE) then
       state else if is_phy_var r then bijection_state_nmax_fupd (K
         (MAX r (bijection_state_nmax state)))
         (bijection_state_invbij_fupd (K (sptree_insert r r
         (bijection_state_invbij state))) (bijection_state_bij_fupd (K
         (sptree_insert r r (bijection_state_bij state)))
       state)) else if is_stack_var r then
         bijection_state_nstack_fupd (K (bijection_state_nstack state +
         4)) (bijection_state_nmax_fupd (K (MAX (bijection_state_nstack
         state) (bijection_state_nmax state)))
         (bijection_state_invbij_fupd (K (sptree_insert
         (bijection_state_nstack state) r (bijection_state_invbij
         state))) (bijection_state_bij_fupd (K (sptree_insert r
         (bijection_state_nstack state) (bijection_state_bij state)))
       state))) else bijection_state_nalloc_fupd (K
         (bijection_state_nalloc state + 4)) (bijection_state_nmax_fupd
         (K (MAX (bijection_state_nalloc state) (bijection_state_nmax
         state))) (bijection_state_invbij_fupd (K (sptree_insert
         (bijection_state_nalloc state) r (bijection_state_invbij
         state))) (bijection_state_bij_fupd (K (sptree_insert r
         (bijection_state_nalloc state) (bijection_state_bij state)))
       state))))`;;

let find_bijection_clash_tree_def,find_bijection_clash_tree_ind =
  define_rec
  [`find_bijection_clash_tree state (reg_alloc_Delta wr rd) =
      FOLDL find_bijection_step (FOLDL find_bijection_step state
        rd) wr`;
   `find_bijection_clash_tree state (reg_alloc_Set cutset:clash_tree) =
      foldi (\r v acc. find_bijection_step acc r) 0 state cutset`;
   `find_bijection_clash_tree state (linear_scan_Branch optcutset ct1
  ct2:clash_tree) =
      (let state1 = find_bijection_clash_tree state ct1 in
      let state2 = find_bijection_clash_tree state1 ct2 in
        match optcutset with NONE -> state2 | SOME cutset ->
          foldi (\r v acc. find_bijection_step acc r) 0 state2
            cutset)`;
   `find_bijection_clash_tree state (linear_scan_Seq ct1 ct2:clash_tree)
  =
      (let state1 = find_bijection_clash_tree state ct1 in
      find_bijection_clash_tree state1 ct2)`];;

let apply_bijection_def = new_definition
  `apply_bijection bij (interval:int spt) =
       foldi (\r i acc. sptree_insert (the 0 (sptree_lookup r
         bij)) i acc) 0 LN interval`;;

(* HOL4 makes the record of an initial state of linear_scan_hidden_state
   and the
   run function with ML code (define_run of
   ml_monadBaseLib); an array field of it is the length and
   the initial value of the array *)
let i_linear_scan_hidden_state_FIELDS =
  define_record "i_linear_scan_hidden_state"
  ["colors","num#num";
   "int_beg","num#int";
   "int_end","num#int";
   "sorted_regs","num#num";
   "sorted_moves","num#num#num#num"];;
let run_i_linear_scan_hidden_state_def = new_definition
  `run_i_linear_scan_hidden_state x state =
     run x (mk_linear_scan_hidden_state (REPLICATE (FST
       (i_linear_scan_hidden_state_colors state)) (SND
       (i_linear_scan_hidden_state_colors state))) (REPLICATE (FST
       (i_linear_scan_hidden_state_int_beg state)) (SND
       (i_linear_scan_hidden_state_int_beg state))) (REPLICATE (FST
       (i_linear_scan_hidden_state_int_end state)) (SND
       (i_linear_scan_hidden_state_int_end state))) (REPLICATE (FST
       (i_linear_scan_hidden_state_sorted_regs state)) (SND
       (i_linear_scan_hidden_state_sorted_regs state))) (REPLICATE
       (FST (i_linear_scan_hidden_state_sorted_moves state)) (SND
       (i_linear_scan_hidden_state_sorted_moves state))))`;;


let linear_reg_alloc_and_extract_coloration_def = new_definition
  `linear_reg_alloc_and_extract_coloration ct k forced moves
  reglist_unsorted invbij nmax =
     st_ex_ignore_bind
       (get_intervals_ct_monad ct) (st_ex_ignore_bind
       (linear_reg_alloc_intervals k forced moves reglist_unsorted) (
       extract_coloration invbij reglist_unsorted LN))`;;

let size_of_clash_tree_def,size_of_clash_tree_ind = define_rec
  [`size_of_clash_tree (reg_alloc_Delta wr rd) =
      ((&2:int):int)`;
   `size_of_clash_tree (reg_alloc_Set cutset:clash_tree) =
      ((&1:int):int)`;
   `size_of_clash_tree (linear_scan_Branch optcutset ct1 ct2:clash_tree)
  = ((
      (if IS_SOME optcutset then (&1) else (&0)) +
        size_of_clash_tree ct1 + size_of_clash_tree ct2):int)`;
   `size_of_clash_tree (linear_scan_Seq ct1 ct2:clash_tree) = ((
      size_of_clash_tree ct1 + size_of_clash_tree ct2):int)`];;

let run_linear_reg_alloc_intervals_def = new_definition
  `run_linear_reg_alloc_intervals ct k forced moves
     reglist_unsorted invbij nmax =
     run_i_linear_scan_hidden_state
       (linear_reg_alloc_and_extract_coloration ct k forced moves
         reglist_unsorted invbij nmax)
       (mk_i_linear_scan_hidden_state (nmax + 1,0)
         ((nmax + 1,&1):num#int) ((nmax + 1,&1):num#int)
         (nmax + 1,0) (LENGTH moves,(0,(0,0))))`;;

let apply_bij_on_clash_tree_def,apply_bij_on_clash_tree_ind = define_rec
  [`apply_bij_on_clash_tree (reg_alloc_Delta wr rd) bij =
      reg_alloc_Delta (MAP (\r. the 0 (sptree_lookup r bij)) wr)
        (MAP (\r. the 0 (sptree_lookup r bij)) rd)`;
   `apply_bij_on_clash_tree (reg_alloc_Set cutset:clash_tree) bij =
      reg_alloc_Set (foldi (\r _18 acc. sptree_insert (the 0
        (sptree_lookup r bij)) one acc) 0 LN cutset)`;
   `apply_bij_on_clash_tree (linear_scan_Branch optcutset ct1
  ct2:clash_tree) bij =
      reg_alloc_Branch (OPTION_MAP (foldi (\r _34 acc.
        sptree_insert (the 0 (sptree_lookup r bij)) one acc) 0 LN)
        optcutset) (apply_bij_on_clash_tree ct1 bij)
        (apply_bij_on_clash_tree ct2 bij)`;
   `apply_bij_on_clash_tree (linear_scan_Seq ct1 ct2:clash_tree) bij =
      reg_alloc_Seq (apply_bij_on_clash_tree ct1 bij)
        (apply_bij_on_clash_tree ct2 bij)`];;


let linear_scan_reg_alloc_def = new_definition
  `linear_scan_reg_alloc k moves ct forced =
       (let bijstate = find_bijection_clash_tree find_bijection_init
         ct in
       let ct' = apply_bij_on_clash_tree ct (bijection_state_bij
         bijstate) in
       let forced' = MAP (\(r1,r2). (the 0 (sptree_lookup r1
         (bijection_state_bij bijstate)),the 0 (sptree_lookup r2
         (bijection_state_bij bijstate)))) forced in
       let moves' = MAP (\(p,(r1,r2)). (p,(the 0 (sptree_lookup r1
         (bijection_state_bij bijstate)),the 0 (sptree_lookup r2
         (bijection_state_bij bijstate))))) moves in
       let reglist_unsorted = (MAP SND (toAList (bijection_state_bij
         bijstate))) in
       run_linear_reg_alloc_intervals ct' k forced' moves'
         reglist_unsorted (bijection_state_invbij bijstate)
         (bijection_state_nmax bijstate))
   // (0i-((size_of_clash_tree ct') + 1))`;;

(* HOL4 linear_scanScript.sml:1148-1328: code that the source has in
   a comment *)

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
