(* ======================================================== *)
(*  linear_scan: ported from HOL4's
    compiler/backend/reg_alloc/linear_scanScript.sml  *)
(* ======================================================== *)

(*
  A linear-scan register allocator.
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/stackLang.ml";;
needs "lib/sptree.ml";;
needs "lib/state_transformer.ml";;
needs "misc/misc.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

let live_tree_INDUCT,live_tree_RECURSION = define_datatype
  "live_tree = linear_scan_Writes (num list) | linear_scan_Reads (num \
   list) | linear_scan_Branch (live_tree) (live_tree) | \
   linear_scan_Seq (live_tree) (live_tree)";;
hol4_overload "Branch" "linear_scan_Branch";;
hol4_overload "Seq" "linear_scan_Seq";;


let numset_list_insert_def = cake_define
  `(linear_scan_numset_list_insert [] t = t) /\
   (linear_scan_numset_list_insert (x :: xs) t =
     linear_scan_numset_list_insert xs (insert x one t))`;;
hol4_overload "numset_list_insert" "linear_scan_numset_list_insert";;

let numset_list_insert_nottailrec_def = cake_define
  `(numset_list_insert_nottailrec [] t = t) /\
   (numset_list_insert_nottailrec (x :: xs) t = insert x one
     (numset_list_insert_nottailrec xs t))`;;

let get_live_tree_def = cake_define
  `(
     get_live_tree (reg_alloc_Delta wr rd) =
       Seq (linear_scan_Reads rd) (linear_scan_Writes wr)) /\ (
     get_live_tree (reg_alloc_Set cutset) =
       (let cutlist = MAP FST (toAList cutset) in
       linear_scan_Reads cutlist)) /\ (
     get_live_tree (reg_alloc_Branch optcutset ct1 ct2) =
       (let lt1 = get_live_tree ct1 in
       let lt2 = get_live_tree ct2 in
       match optcutset with SOME cutset ->
           (let cutlist = MAP FST (toAList cutset) in
           Seq (linear_scan_Reads cutlist) (Branch lt1 lt2)) | NONE
             -> (Branch lt1 lt2))) /\ (
     get_live_tree (reg_alloc_Seq ct1 ct2) =
       (let lt2 = get_live_tree ct2 in
       let lt1 = get_live_tree ct1 in
       Seq lt1 lt2))`;;

let check_live_tree_def = cake_define
  `(
     check_live_tree f (linear_scan_Writes l) live flive =
       (match check_partial_col f l live flive with NONE -> NONE |
         SOME _2 ->
       (let livein = numset_list_delete l live in
       let flivein = numset_list_delete (MAP f l) flive in
       SOME (livein,flivein)))) /\ (
     check_live_tree f (linear_scan_Reads l) live flive =
       check_partial_col f l live flive) /\ (
     check_live_tree f (Branch lt1 lt2) live flive =
       (match check_live_tree f lt1 live flive with NONE -> NONE |
         SOME (livein1,flivein1) ->
       (match check_live_tree f lt2 live flive with NONE -> NONE |
         SOME (livein2,flivein2) ->
       check_partial_col f (MAP FST (toAList (difference livein2
         livein1))) livein1 flivein1))) /\ (
     check_live_tree f (Seq lt1 lt2) live flive =
       (match check_live_tree f lt2 live flive with NONE -> NONE |
         SOME (livein2,flivein2) ->
         check_live_tree f lt1 livein2 flivein2))`;;

let get_live_backward_def = cake_define
  `(
     get_live_backward (linear_scan_Writes l) live =
       numset_list_delete l live) /\ (
     get_live_backward (linear_scan_Reads l) live =
       numset_list_insert l live) /\ (
     get_live_backward (Branch lt1 lt2) live =
       (let live1 = get_live_backward lt1 live in
       let live2 = get_live_backward lt2 live in
       numset_list_insert (MAP FST (toAList (difference live2
         live1))) live1)) /\ (
     get_live_backward (Seq lt1 lt2) live =
       get_live_backward lt1 (get_live_backward lt2 live))`;;

let fix_domination_def = cake_define
  `fix_domination lt =
       (let live = get_live_backward lt LN in
       if live = LN then lt else Seq (linear_scan_Writes (MAP FST
         (toAList live))) lt)`;;

let numset_list_add_if_def = cake_define
  `(
     numset_list_add_if [] (v:int) s P = s) /\ (
     numset_list_add_if (x :: xs) v s P =
       (match lookup x s with (SOME v') ->
           (if P v v' then numset_list_add_if xs v (insert x v s) P
             else numset_list_add_if xs v s P) | NONE ->
           numset_list_add_if xs v (insert x v s) P))`;;

let numset_list_add_if_lt_def = cake_define
  `numset_list_add_if_lt l (v:int) s = numset_list_add_if l v s (<=)`;;

let numset_list_add_if_gt_def = cake_define
  `numset_list_add_if_gt l (v:int) s = numset_list_add_if l v s (\a
  b. b <= a)`;;

let size_of_live_tree_def = cake_define
  `(
     size_of_live_tree (linear_scan_Writes l) =
       (1:int)) /\ (
     size_of_live_tree (linear_scan_Reads l) =
       (1:int)) /\ (
     size_of_live_tree (Branch lt1 lt2) =
       size_of_live_tree lt1 + size_of_live_tree lt2) /\ (
     size_of_live_tree (Seq lt1 lt2) =
       size_of_live_tree lt1 + size_of_live_tree lt2)`;;

let get_intervals_def = cake_define
  `(
     get_intervals (linear_scan_Writes l) (n:int) int_beg int_end =
       (n - 1,numset_list_add_if_lt l n int_beg,numset_list_add_if_gt
         l n int_end)) /\ (
     get_intervals (linear_scan_Reads l) (n:int) int_beg int_end =
       (n - 1,int_beg,numset_list_add_if_gt l n int_end)) /\ (
     get_intervals (Branch lt1 lt2) (n:int) int_beg int_end =
       (let (n2,int_beg2,int_end2) = get_intervals lt2 n int_beg
         int_end in
       get_intervals lt1 n2 int_beg2 int_end2)) /\ (
     get_intervals (Seq lt1 lt2) (n:int) int_beg int_end =
       (let (n2,int_beg2,int_end2) = get_intervals lt2 n int_beg
         int_end in
       get_intervals lt1 n2 int_beg2 int_end2))`;;

(* compute the same thing as `get_intervals` (as says the
   `get_intervals_withlive_beg_eq_get_intervals_beg` theorem),
 * but has the following invariant: !r. r IN domain live ==> r NOTIN
   domain beg_in (as stated by the `get_intervals_withlive_live_intbeg`
   theorem *)
let get_intervals_withlive_def = cake_define
  `(
     get_intervals_withlive (linear_scan_Writes l) (n:int) int_beg
       int_end live =
       (n - 1,numset_list_add_if_lt l n int_beg,numset_list_add_if_gt
         l n int_end)) /\ (
     get_intervals_withlive (linear_scan_Reads l) (n:int) int_beg
       int_end live =
       (n - 1,numset_list_delete l int_beg,numset_list_add_if_gt l n
         int_end)) /\ (
     get_intervals_withlive (Branch lt1 lt2) (n:int) int_beg int_end
       live =
       (let (n2,int_beg2,int_end2) = get_intervals_withlive lt2 n
         int_beg int_end live in
       let (n1,int_beg1,int_end1) = get_intervals_withlive lt1 n2
         (difference int_beg2 live) int_end2 live in
       (n1,difference int_beg1 (union (get_live_backward lt1 live)
         (get_live_backward lt2 live)),int_end1))) /\ (
     get_intervals_withlive (Seq lt1 lt2) (n:int) int_beg int_end
       live =
       (let (n2,int_beg2,int_end2) = get_intervals_withlive lt2 n
         int_beg int_end live in
       let (n1,int_beg1,int_end1) = get_intervals_withlive lt1 n2
         int_beg2 int_end2 (get_live_backward lt2 live) in
       (n1,int_beg1,int_end1)))`;;

let check_number_property_def = cake_define
  `(
     check_number_property (P:int->one spt->bool) (linear_scan_Writes
       l) n live =
         (let n_out = n - 1 in
         let live_out = numset_list_delete l live in
         P n_out live_out)) /\ (
     check_number_property P (linear_scan_Reads l) n live =
         (let n_out = n - 1 in
         let live_out = numset_list_insert l live in
         P n_out live_out)) /\ (
     check_number_property P (Branch lt1 lt2) n live =
         (let r2 = check_number_property P lt2 n live in
         let r1 = check_number_property P lt1 (n - (size_of_live_tree
           lt2)) live in
         r1 /\ r2)) /\ (
     check_number_property P (Seq lt1 lt2) n live =
         (let r2 = check_number_property P lt2 n live in
         let r1 = check_number_property P lt1 (n - size_of_live_tree
           lt2) (get_live_backward lt2 live) in
         r1 /\ r2))`;;

let check_number_property_strong_def = cake_define
  `(
     check_number_property_strong (P:int->one spt->bool)
       (linear_scan_Writes l) n live =
         (let n_out = n - 1 in
         let live_out = numset_list_delete l live in
         P n_out live_out)) /\ (
     check_number_property_strong P (linear_scan_Reads l) n live =
         (let n_out = n - 1 in
         let live_out = numset_list_insert l live in
         P n_out live_out)) /\ (
     check_number_property_strong P (Branch lt1 lt2) n live =
         (let r2 = check_number_property_strong P lt2 n live in
         let r1 = check_number_property_strong P lt1 (n -
           (size_of_live_tree lt2)) live in
         r1 /\ r2 /\ P (n - (size_of_live_tree (Branch lt1 lt2)))
           (get_live_backward (Branch lt1 lt2) live))) /\ (
     check_number_property_strong P (Seq lt1 lt2) n live =
         (let r2 = check_number_property_strong P lt2 n live in
         let r1 = check_number_property_strong P lt1 (n -
           size_of_live_tree lt2) (get_live_backward lt2 live) in
         r1 /\ r2))`;;

let check_startlive_prop_def = cake_define
  `(
     check_startlive_prop (linear_scan_Writes l) n beg end ndef =
         (!r. MEM r l ==> (option_CASE (lookup r beg) ndef (\x. x) <=
           n /\
                         (?v. lookup r end = SOME v /\ n <= v)))) /\
                           (
     check_startlive_prop (linear_scan_Reads l) n beg end ndef =
         T) /\ (
     check_startlive_prop (Branch lt1 lt2) n beg end ndef =
         (let r2 = check_startlive_prop lt2 n beg end ndef in
         let r1 = check_startlive_prop lt1 (n - (size_of_live_tree
           lt2)) beg end ndef in
         r1 /\ r2)) /\ (
     check_startlive_prop (Seq lt1 lt2) n beg end ndef =
         (let r2 = check_startlive_prop lt2 n beg end ndef in
         let r1 = check_startlive_prop lt1 (n - size_of_live_tree
           lt2) beg end ndef in
         r1 /\ r2))`;;

let live_tree_registers_def = cake_define
  `(live_tree_registers (linear_scan_Writes l) = set_of_list l) /\
   (live_tree_registers (linear_scan_Reads l) = set_of_list l) /\
   (live_tree_registers (Branch lt1 lt2) = live_tree_registers lt1
     UNION live_tree_registers lt2) /\
   (live_tree_registers (Seq lt1 lt2) = live_tree_registers lt1
     UNION live_tree_registers lt2)`;;

let interval_intersect_def = cake_define
  `interval_intersect ((l1:int),(r1:int)) (l2,r2) = (l1 <= r2 /\ l2
  <= r1)`;;

let point_inside_interval_def = cake_define
  `point_inside_interval ((l:int),(r:int)) n = (l <= n /\ n <= r)`;;

let check_intervals_def = cake_define
  `check_intervals f int_beg int_end = (!r1 r2.
     r1 IN domain int_beg /\ r2 IN domain int_beg /\
     interval_intersect (THE (lookup r1 int_beg),THE (lookup r1
       int_end)) (THE (lookup r2 int_beg),THE (lookup r2 int_end)) /\
     f r1 = f r2 ==>
     r1 = r2)`;;

let get_intervals_ct_aux_def = cake_define
  `(
     get_intervals_ct_aux (reg_alloc_Delta wr rd) (n:int) int_beg
       int_end live =
       (n - 2,numset_list_add_if_lt wr n
         int_beg,numset_list_add_if_gt rd (n - 1) (numset_list_add_if_gt
         wr n int_end),numset_list_insert rd (numset_list_delete wr
         live))) /\ (
     get_intervals_ct_aux (reg_alloc_Set cutset) (n:int) int_beg
       int_end live =
       (n - 1,int_beg,numset_list_add_if_gt (MAP FST (toAList
         cutset)) n int_end,union cutset live)) /\ (
     get_intervals_ct_aux (reg_alloc_Branch optcutset ct1 ct2)
       (n:int) int_beg int_end live =
       (let (n2,int_beg2,int_end2,live2) = get_intervals_ct_aux ct2 n
         int_beg int_end live in
       let (n1,int_beg1,int_end1,live1) = get_intervals_ct_aux ct1 n2
         int_beg2 int_end2 live in
       match optcutset with NONE -> (n1,int_beg1,int_end1,union live1
         live2) | SOME cutset -> (n1 - 1,int_beg1,numset_list_add_if_gt
         (MAP FST (toAList cutset)) n1 int_end1,union cutset (union
         live1 live2)))) /\ (
     get_intervals_ct_aux (reg_alloc_Seq ct1 ct2) (n:int) int_beg
       int_end live =
       (let (n2,int_beg2,int_end2,live2) = get_intervals_ct_aux ct2 n
         int_beg int_end live in
       get_intervals_ct_aux ct1 n2 int_beg2 int_end2 live2))`;;

let get_intervals_ct_def = cake_define
  `get_intervals_ct ct =
       (let (n,int_beg,int_end,live) = get_intervals_ct_aux ct 0 LN
         LN LN in
       let listlive = MAP FST (toAList live) in
       (n - 1,numset_list_add_if_lt listlive n
         int_beg,numset_list_add_if_gt listlive n int_end))`;;

let linear_scan_state_FIELDS = define_record "linear_scan_state"
  ["active","(int#num) list";
   "colorpool","num list";
   "phyregs","one spt";
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

(* HOL4 ML code, not ported:
val accessors = define_monad_access_funs ``:linear_scan_hidden_state``;
*)

(* HOL4 ML code, not ported:
val colors_accessors = el 1 accessors;
val int_beg_accessors = el 2 accessors;
val int_end_accessors = el 3 accessors;
val sorted_regs_accessors = el 4 accessors;
val sorted_moves_accessors = el 5 accessors;
*)

(* HOL4 ML code, not ported:
val (colors,get_colors_def,set_colors_def) = colors_accessors;
val (int_beg,get_int_beg_def,set_int_beg_def) = int_beg_accessors;
val (int_end,get_int_end_def,set_int_end_def) = int_end_accessors;
val (sorted_regs,get_sorted_regs_def,set_sorted_regs_def) =
  sorted_regs_accessors;
val (sorted_moves,get_sorted_moves_def,set_sorted_moves_def) =
  sorted_moves_accessors;
*)

(*
Datatype:
  state_exn = Fail string | Subscript
End
*)

(* HOL4 ML code, not ported:
val exn_functions = define_monad_exception_functions ``:state_exn``
  ``:linear_scan_hidden_state``;
*)
(* HOL4 overload (expanded in the port):
     failwith = raise_Fail *)

(* HOL4 ML code, not ported:
val sub_exn = ``Subscript``;
val update_exn = ``Subscript``;
*)

(* HOL4 ML code, not ported:
val arr_manip = define_MFarray_manip_funs [colors_accessors,
  int_beg_accessors, int_end_accessors, sorted_regs_accessors,
  sorted_moves_accessors] sub_exn update_exn;
*)

(* HOL4 ML code, not ported:
fun accessor_thm (a,b,c,d,e,f) = LIST_CONJ [b,c,d,e,f]
*)

(* HOL4 ML code, not ported:
val colors_manip = el 1 arr_manip;
val int_beg_manip = el 2 arr_manip;
val int_end_manip = el 3 arr_manip;
val sorted_regs_manip = el 4 arr_manip;
val sorted_moves_manip = el 5 arr_manip;
*)

(* HOL4 ML code, not ported:
val colors_length_def = fetch "-" "colors_length_def";
val colors_sub_def    = fetch "-" "colors_sub_def";
val update_colors_def = fetch "-" "update_colors_def";
*)

(* HOL4 ML code, not ported:
val int_beg_length_def = fetch "-" "int_beg_length_def";
val int_beg_sub_def    = fetch "-" "int_beg_sub_def";
val update_int_beg_def = fetch "-" "update_int_beg_def";
*)

(* HOL4 ML code, not ported:
val int_end_length_def = fetch "-" "int_end_length_def";
val int_end_sub_def    = fetch "-" "int_end_sub_def";
val update_int_end_def = fetch "-" "update_int_end_def";
*)

(* HOL4 ML code, not ported:
val sorted_regs_length_def = fetch "-" "sorted_regs_length_def";
val sorted_regs_sub_def    = fetch "-" "sorted_regs_sub_def";
val update_sorted_regs_def = fetch "-" "update_sorted_regs_def";
*)

(* HOL4 ML code, not ported:
val sorted_moves_length_def = fetch "-" "sorted_moves_length_def";
val sorted_moves_sub_def    = fetch "-" "sorted_moves_sub_def";
val update_sorted_moves_def = fetch "-" "update_sorted_moves_def";
*)

let numset_list_add_if_lt_monad_def = cake_define
  `(
     numset_list_add_if_lt_monad [] v =
       return one) /\ (
     numset_list_add_if_lt_monad (r :: rs) v =
       monad_bind (int_beg_sub r) (\
         begr.
         if 0 < begr then
           monad_ignore_bind
             (update_int_beg r v) (
             numset_list_add_if_lt_monad rs v) else if v <= begr then
           monad_ignore_bind
             (update_int_beg r v) (
             numset_list_add_if_lt_monad rs v) else
           numset_list_add_if_lt_monad rs v))`;;

let numset_list_add_if_gt_monad_def = cake_define
  `(
     numset_list_add_if_gt_monad [] v =
       return one) /\ (
     numset_list_add_if_gt_monad (r :: rs) v =
       monad_bind (int_end_sub r) (\
         begr.
         if 0 < begr then
           monad_ignore_bind
             (update_int_end r v) (
             numset_list_add_if_gt_monad rs v) else if begr <= v then
           monad_ignore_bind
             (update_int_end r v) (
             numset_list_add_if_gt_monad rs v) else
           numset_list_add_if_gt_monad rs v))`;;

let get_intervals_ct_monad_aux_def = cake_define
  `(
     get_intervals_ct_monad_aux (reg_alloc_Delta wr rd) (n:int) live
       =
       monad_ignore_bind
         (numset_list_add_if_lt_monad wr n) (monad_ignore_bind
         (numset_list_add_if_gt_monad wr n) (monad_ignore_bind
         (numset_list_add_if_gt_monad rd (n - 1)) (
         return (n - 2,numset_list_insert rd (numset_list_delete wr
           live)))))) /\ (
     get_intervals_ct_monad_aux (reg_alloc_Set cutset) (n:int) live =
       monad_ignore_bind
         (numset_list_add_if_gt_monad (MAP FST (toAList cutset)) n) (
         return (n - 1,union cutset live))) /\ (
     get_intervals_ct_monad_aux (reg_alloc_Branch optcutset ct1 ct2)
       (n:int) live =
       monad_bind (get_intervals_ct_monad_aux ct2 n live) (\
         (n2,live2). monad_bind (get_intervals_ct_monad_aux ct1 n2
           live) (\
         (n1,live1).
         match optcutset with NONE -> return (n1,union live1 live2) |
           SOME cutset ->
           monad_ignore_bind
             (numset_list_add_if_gt_monad (MAP FST (toAList cutset))
               n1) (
             return (n1 - 1,union cutset (union live1 live2)))))) /\
               (
     get_intervals_ct_monad_aux (reg_alloc_Seq ct1 ct2) (n:int) live
       =
       monad_bind (get_intervals_ct_monad_aux ct2 n live) (\
         (n2,live2).
         get_intervals_ct_monad_aux ct1 n2 live2))`;;

let get_intervals_ct_monad_def = cake_define
  `get_intervals_ct_monad ct =
     monad_bind (get_intervals_ct_monad_aux ct 0 LN) (\
       (n,live). monad_ignore_bind
       (numset_list_add_if_lt_monad (MAP FST (toAList live)) n)
         (monad_ignore_bind
       (numset_list_add_if_gt_monad (MAP FST (toAList live)) n) (
       return (n - 1))))`;;

(* HOL4 termination: >> rw [] *)
let remove_inactive_intervals_def = cake_define_wf
  `MEASURE (\(_3,st). LENGTH (linear_scan_state_active st))`
  `remove_inactive_intervals beg st =
     (match linear_scan_state_active st with [] -> return st | (e,r)
       :: activetail -> (
       if e < beg then
         monad_bind (colors_sub r) (\
           col.
           let st' = linear_scan_state_colorpool_fupd (\l. col :: l)
             (linear_scan_state_active_fupd (K activetail) st) in
           remove_inactive_intervals beg st') else
         return st))`;;

let add_active_interval_def = cake_define
  `(
     add_active_interval v [] = [v]) /\ (
     add_active_interval (v1:int#num) (v2 :: tail) =
         (if FST v1 <= FST v2 then
             v1 :: v2 :: tail else
             v2 :: (add_active_interval v1 tail)))`;;

let find_color_in_list_def = cake_define
  `(
     find_color_in_list [] (forbidden:one spt) = NONE) /\ (
     find_color_in_list (r :: rs) forbidden =
         (if lookup r forbidden = NONE then
           SOME (r,rs) else
           match find_color_in_list rs forbidden with NONE -> NONE
             | SOME (col,rest) -> SOME (col,r :: rest)))`;;

let find_color_in_colornum_def = cake_define
  `find_color_in_colornum st (forbidden:one spt) =
       (if linear_scan_state_colormax st <=
         linear_scan_state_colornum st then
         (st,NONE) else
         (linear_scan_state_colornum_fupd ((+) 1) st,SOME
           (linear_scan_state_colornum st)))`;;

let find_color_def = cake_define
  `find_color st (forbidden:one spt) =
       (match find_color_in_list (linear_scan_state_colorpool st)
         forbidden with SOME (col,rest) ->
         (linear_scan_state_colorpool_fupd (K rest) st,SOME col) |
         NONE -> find_color_in_colornum st forbidden)`;;

let spill_register_def = cake_define
  `spill_register st reg =
     monad_ignore_bind
       (update_colors reg (linear_scan_state_stacknum st)) (
       return (linear_scan_state_stacknum_fupd ((+) 1) st))`;;

let color_register_def = cake_define
  `color_register st reg col rend =
     monad_ignore_bind
       (update_colors reg col) (
       if is_phy_var reg then
         return (linear_scan_state_phyregs_fupd (insert col one)
           (linear_scan_state_active_fupd (add_active_interval
           (rend,reg))
           st)) else
         return (linear_scan_state_active_fupd
           (add_active_interval (rend,reg)) st))`;;

let find_last_stealable_def = cake_define
  `(
     find_last_stealable [] (forbidden:one spt) =
         return NONE) /\ (
     find_last_stealable (x :: xs) forbidden =
       monad_bind (find_last_stealable xs forbidden) (\
         recursion.
         match recursion with SOME (steal,rest) -> return (SOME
           (steal,x :: rest)) | NONE -> (
             monad_bind (colors_sub (SND x)) (\
               xcol.
               if ~(is_phy_var (SND x)) /\ (lookup xcol forbidden =
                 NONE) then
                 return (SOME (x,xs)) else
                 return NONE))))`;;

let find_spill_def = cake_define
  `find_spill st (forbidden:one spt) reg rend force =
     monad_bind (find_last_stealable (linear_scan_state_active st)
       forbidden) (\
       stealable.
       match stealable with NONE -> spill_register st reg | SOME
         ((stealend,stealreg),newactive) ->
         (if force \/ rend < stealend then
           monad_bind (colors_sub stealreg) (\
             stealcolor. monad_bind (spill_register
               (linear_scan_state_active_fupd (K newactive) st)
               stealreg) (\
             st'.
             color_register st' reg stealcolor rend)) else
           spill_register st reg))`;;

let linear_reg_alloc_step_aux_def = cake_define
  `linear_reg_alloc_step_aux st (forbidden:one spt) preferred reg rend
  force =
     (let preferred_filtered = FILTER (\c. MEM c
       (linear_scan_state_colorpool st)) preferred in
     match find_color_in_list preferred_filtered forbidden with SOME
       (col,_4) -> color_register (linear_scan_state_colorpool_fupd
       (FILTER ((<>) col)) st) reg col rend | NONE -> (
       match find_color st forbidden with (st',SOME col) ->
         color_register st' reg col rend | (st',NONE) -> find_spill
         st' forbidden reg rend force))`;;

let linear_reg_alloc_step_pass1_def = cake_define
  `linear_reg_alloc_step_pass1 forced moves st reg =
     monad_bind (int_beg_sub reg) (\
       rbeg. monad_bind (int_end_sub reg) (\
       rend. monad_bind (remove_inactive_intervals rbeg st) (\
       st'.
       if is_stack_var reg then
         spill_register st' reg else
         monad_bind (st_ex_MAP colors_sub (the [] (lookup reg
           forced))) (\
           forced_forbidden_list.
           let forced_forbidden = fromAList (MAP (\c. (c,one))
             forced_forbidden_list) in
           if is_phy_var reg then
             if reg < 2 * (linear_scan_state_colormax st') then
               let forbidden = union (linear_scan_state_phyregs st')
                 forced_forbidden in
               linear_reg_alloc_step_aux st' forbidden [] reg rend T
                 else
               spill_register st' reg else
             monad_bind (st_ex_MAP colors_sub (the [] (lookup reg
               moves))) (\
               moves_preferred.
               linear_reg_alloc_step_aux st' forced_forbidden
                 moves_preferred reg rend F)))))`;;

let linear_reg_alloc_step_pass2_def = cake_define
  `linear_reg_alloc_step_pass2 forced moves st reg =
     monad_bind (int_beg_sub reg) (\
       rbeg. monad_bind (int_end_sub reg) (\
       rend. monad_bind (remove_inactive_intervals rbeg st) (\
       st'. monad_bind (st_ex_MAP colors_sub (the [] (lookup reg
         forced))) (\
       forced_forbidden_list. monad_bind (return (fromAList (MAP (\c.
         (c,one)) forced_forbidden_list))) (\
       forced_forbidden. monad_bind (st_ex_MAP colors_sub (the []
         (lookup reg moves))) (\
       moves_preferred.
       if is_phy_var reg then
         let forbidden = union (linear_scan_state_phyregs st')
           forced_forbidden in
           linear_reg_alloc_step_aux st' forbidden [] reg rend F else
         linear_reg_alloc_step_aux st' forced_forbidden
           moves_preferred reg rend F))))))`;;


let linear_reg_alloc_pass1_initial_state_def = cake_define
  `linear_reg_alloc_pass1_initial_state k =
     mk_linear_scan_state [] [] LN 0 k k`;;

let linear_reg_alloc_pass2_initial_state_def = cake_define
  `linear_reg_alloc_pass2_initial_state k nreg =
     mk_linear_scan_state [] [] LN k (k + nreg) (k + nreg)`;;

let find_reg_exchange_def = cake_define
  `(
     find_reg_exchange [] exch invexch = return (exch,invexch)) /\ (
     find_reg_exchange (r :: rs) exch invexch =
       monad_bind (colors_sub r) (\
         col1.
         let fcol1 = r DIV 2 in
         let col2 = option_CASE (lookup fcol1 invexch) fcol1 (\x. x)
           in
         let fcol2 = option_CASE (lookup col1 exch) col1 (\x. x) in
         find_reg_exchange rs (insert col1 fcol1 (insert col2
           fcol2 exch)) (insert fcol1 col1 (insert fcol2 col2
           invexch))))`;;

let MAP_colors_def = cake_define
  `(
     MAP_colors f 0 = return one) /\ (
     MAP_colors f (SUC n) =
       monad_bind (colors_sub n) (\
         col. monad_ignore_bind
         (update_colors n (f col)) (
         MAP_colors f n)))`;;

let apply_reg_exchange_def = cake_define
  `apply_reg_exchange phyregs =
     monad_bind (find_reg_exchange phyregs LN LN) (\
       (exch,invexch). monad_bind colors_length (\
       col_size.
       MAP_colors (\c. option_CASE (lookup c exch) c (\x. x))
         col_size))`;;

let st_ex_FOLDL_def = cake_define
  `(
     st_ex_FOLDL f e [] = return e) /\ (
     st_ex_FOLDL f e (x :: xs) =
       monad_bind (f e x) (\
         e'.
         st_ex_FOLDL f e' xs))`;;

(* like st_ex_FILTER, but preserve the order *)
let st_ex_FILTER_good_def = cake_define
  `(
     st_ex_FILTER_good P [] = return []) /\ (
     st_ex_FILTER_good P (x :: xs) =
       monad_bind (P x) (\
         Px.
         if Px then
           monad_bind (st_ex_FILTER_good P xs) (\
             filter_xs.
             return (x :: filter_xs)) else
           st_ex_FILTER_good P xs))`;;

let edges_to_adjlist_def = cake_define
  `(
     edges_to_adjlist [] acc = return acc) /\ (
     edges_to_adjlist ((a,b) :: abs) acc =
       (if a = b then
         edges_to_adjlist abs acc else
         monad_bind (int_beg_sub a) (\
           bega. monad_bind (int_beg_sub b) (\
           begb.
           if bega < begb \/ (bega = begb /\ a <= b) then
             edges_to_adjlist abs (insert b (a :: (the [] (lookup b
               acc))) acc) else
             edges_to_adjlist abs (insert a (b :: (the [] (lookup
               a acc))) acc)))))`;;

let sort_moves_rev_def = cake_define
  `sort_moves_rev ls =
     sort (\((p:num),x,p',x'). p < p') ls`;;

let swap_regs_def = cake_define
  `swap_regs i1 i2 =
     monad_bind (sorted_regs_sub i1) (\
       r1. monad_bind (sorted_regs_sub i2) (\
       r2. monad_ignore_bind
       (update_sorted_regs i1 r2) (
       update_sorted_regs i2 r1)))`;;

(* HOL4 termination: *)
let partition_regs_def = cake_define_wf
  `MEASURE (\(l,rpiv,begrpiv,r). r - l)`
  `partition_regs l rpiv begrpiv r =
     (if r <= l then
       return l else
       monad_bind (sorted_regs_sub l) (\
         reg. monad_bind (int_beg_sub reg) (\
         begreg.
         if begreg < begrpiv \/ (begreg = begrpiv /\ reg <= rpiv)
           then
             partition_regs (l + 1) rpiv begrpiv r else
           monad_ignore_bind
             (swap_regs l (r - 1)) (
             partition_regs l rpiv begrpiv (r - 1)))))`;;

(* HOL4 termination: *)
let sort_regs_def = cake_define_wf
  `MEASURE (\(l,r). r - l)`
  `sort_regs l r =
     (if r <= l + 1 then
       return one else
       monad_bind (sorted_regs_sub l) (\
         rpiv. monad_bind (int_beg_sub rpiv) (\
         begrpiv. monad_bind (partition_regs (l + 1) rpiv begrpiv r)
           (\
         m. monad_ignore_bind
         (swap_regs l (m - 1)) (
         if m <= l \/ r < m then
           return one else
           monad_ignore_bind
             (sort_regs l (m - 1)) (
             sort_regs m r))))))`;;

let list_to_sorted_regs_def = cake_define
  `(
     list_to_sorted_regs [] n =
         return one) /\ (
     list_to_sorted_regs (r :: rs) n =
       monad_ignore_bind
         (update_sorted_regs n r) (
         list_to_sorted_regs rs (n + 1)))`;;

(* HOL4 termination: *)
let sorted_regs_to_list_def = cake_define_wf
  `MEASURE (\(n,last). last - n)`
  `sorted_regs_to_list n last =
     (if last <= n then
       return [] else
       monad_bind (sorted_regs_sub n) (\
         r. monad_bind (sorted_regs_to_list (n + 1) last) (\
         l.
         return (r :: l))))`;;

let swap_moves_def = cake_define
  `swap_moves i1 i2 =
     monad_bind (sorted_moves_sub i1) (\
       r1. monad_bind (sorted_moves_sub i2) (\
       r2. monad_ignore_bind
       (update_sorted_moves i1 r2) (
       update_sorted_moves i2 r1)))`;;

(* HOL4 termination: *)
let partition_moves_def = cake_define_wf
  `MEASURE (\(l,piv,r). r - l)`
  `partition_moves l ppiv r =
     (if r <= l then
       return l else
       monad_bind (sorted_moves_sub l) (\
         move.
         if FST move < ppiv then
           partition_moves (l + 1) ppiv r else
           monad_ignore_bind
             (swap_moves l (r - 1)) (
             partition_moves l ppiv (r - 1))))`;;

(* HOL4 termination: *)
let sort_moves_def = cake_define_wf
  `MEASURE (\(l,r). r - l)`
  `linear_scan_sort_moves l r =
     (if r <= l + 1 then
       return one else
       monad_bind (sorted_moves_sub l) (\
         piv. monad_bind (partition_moves (l + 1) (FST piv) r) (\
         m. monad_ignore_bind
         (swap_moves l (m - 1)) (
         if m <= l \/ r < m then
           return one else
           monad_ignore_bind
             (linear_scan_sort_moves l (m - 1)) (
             linear_scan_sort_moves m r)))))`;;
hol4_overload "sort_moves" "linear_scan_sort_moves";;


let list_to_sorted_moves_def = cake_define
  `(
     list_to_sorted_moves [] n =
         return one) /\ (
     list_to_sorted_moves (r :: rs) n =
       monad_ignore_bind
         (update_sorted_moves n r) (
         list_to_sorted_moves rs (n + 1)))`;;

(* HOL4 termination: *)
let sorted_moves_to_list_def = cake_define_wf
  `MEASURE (\(n,len). len - n)`
  `sorted_moves_to_list n len =
     (if len <= n then
       return [] else
       monad_bind (sorted_moves_sub n) (\
         r. monad_bind (sorted_moves_to_list (n + 1) len) (\
         l.
         return (r :: l))))`;;

let linear_reg_alloc_intervals_def = cake_define
  `linear_reg_alloc_intervals k forced moves reglist_unsorted =
       (let lenreg = LENGTH reglist_unsorted in
       let lenmoves = LENGTH moves in
       let st_init_pass1 = linear_reg_alloc_pass1_initial_state k in
       monad_ignore_bind
         (list_to_sorted_regs reglist_unsorted 0) (monad_ignore_bind
         (sort_regs 0 lenreg) (monad_bind (sorted_regs_to_list 0
           lenreg) (\
         reglist. monad_bind (return (FILTER is_phy_var reglist)) (\
         phyregs. monad_bind (return (FILTER (\r. r < 2 * k)
           phyregs)) (\
         phyphyregs. monad_bind (return (FILTER (\r. 2 * k <= r)
           phyregs)) (\
         stackphyregs. monad_ignore_bind
         (list_to_sorted_moves moves 0) (monad_ignore_bind
         (sort_moves 0 lenmoves) (monad_bind (sorted_moves_to_list 0
           lenmoves) (\
         smoves. monad_bind (edges_to_adjlist (MAP SND smoves) LN) (\
         moves_adjlist. monad_bind (edges_to_adjlist forced LN) (\
         forced_adjlist. monad_bind (st_ex_FOLDL
           (linear_reg_alloc_step_pass1 forced_adjlist moves_adjlist)
           st_init_pass1 reglist) (\
         st_end_pass1. monad_ignore_bind
         (apply_reg_exchange phyphyregs) (monad_bind
           (st_ex_FILTER_good (\r.
           monad_bind (colors_sub r) (\
             col.
             return (is_stack_var r \/ k <= col))) reglist) (\
         stacklist. monad_bind (return
           (linear_reg_alloc_pass2_initial_state k (LENGTH stacklist)))
           (\
         st_init_pass2. monad_bind (return (fromAList (MAP (\r.
           (r,one)) stacklist))) (\
         stackset. monad_bind (return (map (FILTER (\r. ~(lookup r
           stackset = NONE))) forced_adjlist)) (\
         forced_adjlist'. monad_bind (return (map (FILTER (\r.
           ~(lookup r stackset = NONE))) moves_adjlist)) (\
         moves_adjlist'. monad_bind (st_ex_FOLDL
           (linear_reg_alloc_step_pass2 forced_adjlist' moves_adjlist')
           st_init_pass2 stacklist) (\
         st_end_pass2.
         apply_reg_exchange stackphyregs))))))))))))))))))))`;;

let extract_coloration_def = cake_define
  `(
     extract_coloration invbij [] acc = return acc) /\ (
     extract_coloration invbij (r :: rs) acc =
       monad_bind (colors_sub r) (\
         col.
         extract_coloration invbij rs (insert (the 0 (lookup r
           invbij)) col acc)))`;;

let bijection_state_FIELDS = define_record "bijection_state"
  ["bij","num spt";
   "invbij","num spt";
   "nmax","num";
   "nstack","num";
   "nalloc","num"];;

let find_bijection_init_def = cake_define
  `find_bijection_init =
       mk_bijection_state LN LN 0 3 1`;;

let find_bijection_step_def = cake_define
  `find_bijection_step state r =
     (if ~(lookup r (bijection_state_bij state) = NONE) then
       state else if is_phy_var r then bijection_state_nmax_fupd (K
         (MAX r (bijection_state_nmax state)))
         (bijection_state_invbij_fupd (K (insert r r
         (bijection_state_invbij state))) (bijection_state_bij_fupd (K
         (insert r r (bijection_state_bij state)))
       state)) else if is_stack_var r then
         bijection_state_nstack_fupd (K (bijection_state_nstack state +
         4)) (bijection_state_nmax_fupd (K (MAX (bijection_state_nstack
         state) (bijection_state_nmax state)))
         (bijection_state_invbij_fupd (K (insert (bijection_state_nstack
         state) r (bijection_state_invbij state)))
         (bijection_state_bij_fupd (K (insert r (bijection_state_nstack
         state) (bijection_state_bij state)))
       state))) else bijection_state_nalloc_fupd (K
         (bijection_state_nalloc state + 4)) (bijection_state_nmax_fupd
         (K (MAX (bijection_state_nalloc state) (bijection_state_nmax
         state))) (bijection_state_invbij_fupd (K (insert
         (bijection_state_nalloc state) r (bijection_state_invbij
         state))) (bijection_state_bij_fupd (K (insert r
         (bijection_state_nalloc state) (bijection_state_bij state)))
       state))))`;;

let find_bijection_clash_tree_def = cake_define
  `(
     find_bijection_clash_tree state (reg_alloc_Delta wr rd) =
       FOLDL find_bijection_step (FOLDL find_bijection_step state rd)
         wr) /\ (
     find_bijection_clash_tree state (Set cutset) =
       foldi (\r v acc. find_bijection_step acc r) 0 state cutset) /\
         (
     find_bijection_clash_tree state (Branch optcutset ct1 ct2) =
       (let state1 = find_bijection_clash_tree state ct1 in
       let state2 = find_bijection_clash_tree state1 ct2 in
         match optcutset with NONE -> state2 | SOME cutset ->
           foldi (\r v acc. find_bijection_step acc r) 0 state2
             cutset)) /\ (
     find_bijection_clash_tree state (Seq ct1 ct2) =
       (let state1 = find_bijection_clash_tree state ct1 in
       find_bijection_clash_tree state1 ct2))`;;

let apply_bijection_def = cake_define
  `apply_bijection bij (interval:int spt) =
       foldi (\r i acc. insert (the 0 (lookup r bij)) i acc) 0 LN
         interval`;;

(* HOL4 ML code, not ported:
val array_fields_names = ["colors", "int_beg", "int_end", "sorted_regs",
  "sorted_moves"];
val run_i_linear_scan_hidden_state_def =
  define_run ``:linear_scan_hidden_state``
  array_fields_names
  "i_linear_scan_hidden_state";
*)

let linear_reg_alloc_and_extract_coloration_def = cake_define
  `linear_reg_alloc_and_extract_coloration ct k forced moves
  reglist_unsorted invbij nmax =
     monad_ignore_bind
       (get_intervals_ct_monad ct) (monad_ignore_bind
       (linear_reg_alloc_intervals k forced moves reglist_unsorted) (
       extract_coloration invbij reglist_unsorted LN))`;;

let size_of_clash_tree_def = cake_define
  `(
     size_of_clash_tree (reg_alloc_Delta wr rd) =
       (&2)) /\ (
     size_of_clash_tree (Set cutset) =
       (&1)) /\ (
     size_of_clash_tree (Branch optcutset ct1 ct2) =
       (if IS_SOME optcutset then 1 else 0) + size_of_clash_tree ct1
         + size_of_clash_tree ct2) /\ (
     size_of_clash_tree (Seq ct1 ct2) =
       size_of_clash_tree ct1 + size_of_clash_tree ct2)`;;

let run_linear_reg_alloc_intervals_def = cake_define
  `run_linear_reg_alloc_intervals ct k forced moves reglist_unsorted
  invbij nmax =
       run_i_linear_scan_hidden_state
         (linear_reg_alloc_and_extract_coloration ct k forced moves
           reglist_unsorted invbij nmax)
         (mk_linear_scan_hidden_state (nmax + 1,0) (nmax + 1,1)
           (nmax + 1,1) (nmax + 1,0) (LENGTH moves,(0,(0,0))))`;;

let apply_bij_on_clash_tree_def = cake_define
  `(
     apply_bij_on_clash_tree (reg_alloc_Delta wr rd) bij =
       reg_alloc_Delta (MAP (\r. the 0 (lookup r bij)) wr) (MAP (\r.
         the 0 (lookup r bij)) rd)) /\ (
     apply_bij_on_clash_tree (Set cutset) bij =
       Set (foldi (\r _7 acc. insert (the 0 (lookup r bij)) one acc)
         0 LN cutset)) /\ (
     apply_bij_on_clash_tree (Branch optcutset ct1 ct2) bij =
       Branch (OPTION_MAP (foldi (\r _8 acc. insert (the 0 (lookup r
         bij)) one acc) 0 LN) optcutset) (apply_bij_on_clash_tree ct1
         bij) (apply_bij_on_clash_tree ct2 bij)) /\ (
     apply_bij_on_clash_tree (Seq ct1 ct2) bij =
       Seq (apply_bij_on_clash_tree ct1 bij)
         (apply_bij_on_clash_tree ct2 bij))`;;


let linear_scan_reg_alloc_def = cake_define
  `linear_scan_reg_alloc k moves ct forced =
       (let bijstate = find_bijection_clash_tree find_bijection_init
         ct in
       let ct' = apply_bij_on_clash_tree ct (bijection_state_bij
         bijstate) in
       let forced' = MAP (\(r1,r2). (the 0 (lookup r1
         (bijection_state_bij bijstate)),the 0 (lookup r2
         (bijection_state_bij bijstate)))) forced in
       let moves' = MAP (\(p,(r1,r2)). (p,(the 0 (lookup r1
         (bijection_state_bij bijstate)),the 0 (lookup r2
         (bijection_state_bij bijstate))))) moves in
       let reglist_unsorted = (MAP SND (toAList (bijection_state_bij
         bijstate))) in
       run_linear_reg_alloc_intervals ct' k forced' moves'
         reglist_unsorted (bijection_state_invbij bijstate)
         (bijection_state_nmax bijstate))`;;

(*
(* === translation (TODO: move to bootstrap translation) === *)

(* TODO: remove when moved to bootstrap *)
val _ = register_type ``:'a num_map``;
val _ = register_type ``:'a list``;

(*
 *  Set up the monadic translator
 *)

(* The record types used for the monadic state and exceptions *)
val state_type = ``:linear_scan_hidden_state``
val exn_type   = ``:state_exn``;
val _          = register_exn_type exn_type;

val STATE_EXN_TYPE_def = theorem "REG_ALLOC_STATE_EXN_TYPE_def"
val exn_ri_def         = STATE_EXN_TYPE_def;
val store_hprop_name   = "LINEAR_SCAN_HIDDEN_STATE";

(* Accessor functions are defined (and used) previously together
   with exceptions, etc. *)

val exn_functions = [
    (raise_Fail_def, handle_Fail_def),
    (raise_Subscript_def, handle_Subscript_def)
];

val refs_manip_list = [] : (string * thm * thm) list;
val rarrays_manip_list = [] : (string * thm * thm * thm * thm * thm *
  thm) list;
val farrays_manip_list = [
    ("colors", get_colors_def, set_colors_def, colors_length_def,
      colors_sub_def, update_colors_def),
    ("int_beg", get_int_beg_def, set_int_beg_def, int_beg_length_def,
      int_beg_sub_def, update_int_beg_def),
    ("int_end", get_int_end_def, set_int_end_def, int_end_length_def,
      int_end_sub_def, update_int_end_def),
    ("sorted_regs", get_sorted_regs_def, set_sorted_regs_def,
      sorted_regs_length_def, sorted_regs_sub_def,
      update_sorted_regs_def),
    ("sorted_moves", get_sorted_moves_def, set_sorted_moves_def,
      sorted_moves_length_def, sorted_moves_sub_def,
      update_sorted_moves_def)
];

val add_type_theories  = ([] : string list);
val store_pinv_def_opt = NONE : thm option;

(* Initialization *)

val _ = start_dynamic_init_fixed_store_translation
            refs_manip_list
            rarrays_manip_list
            farrays_manip_list
            store_hprop_name
            state_type
            exn_ri_def
            [] (* exn_functions *)
            add_type_theories
            store_pinv_def_opt

(* Translate basics -- TODO: remove in bootstrap *)

val res = translate NULL
val res = translate LENGTH
val res = translate MAP
val res = translate FILTER
val res = translate EVEN
val res = translate FST
val res = translate SND
val res = translate HD;
val res = translate TL;
val res = translate K_DEF;
val res = translate LAST_DEF;
val res = translate FRONT_DEF;
val res = translate the_def;
val res = translate MEMBER_def;

val hd_side = prove(
  ``hd_side x <=> x <> []``,
  Cases_on `x` \\ fs [fetch "-" "hd_side_def"])
  |> update_precondition;

val tl_side = prove(
  ``tl_side x <=> x <> []``,
  Cases_on `x` \\ fs [fetch "-" "tl_side_def"])
  |> update_precondition;

val last_side = prove(
  ``!x. last_side x <=> x <> []``,
  Induct \\ simp [Once (fetch "-" "last_side_def")])
  |> update_precondition;

val front_side = prove(
  ``!x. front_side x <=> x <> []``,
  Induct \\ simp [Once (fetch "-" "front_side_def")])
  |> update_precondition;

val res = translate mk_BN_def;
val res = translate mk_BS_def;
val res = translate delete_def;
val res = translate numset_list_delete_def;
val res = translate lookup_def
val res = translate insert_def
val res = translate union_def
val res = translate map_def
val res = translate difference_def;
val res = translate is_stack_var_def
val res = translate is_phy_var_def
val res = translate fromAList_def;
val res = translate sortingTheory.PART_DEF
val res = translate sortingTheory.PARTITION_DEF
val res = translate sortingTheory.QSORT_DEF

val res = translate pairTheory.LEX_DEF
val res = translate lrnext_def
val res = translate foldi_def
val res = translate toAList_def
val res = translate MAX_DEF;
val res = translate FOLDL;

(* Translate linear scan register allocator *)

Definition map_colors_sub_def:
  (map_colors_sub [] = return []) ∧
  (map_colors_sub (x::xs) =
     do fx <- colors_sub x; fxs <- map_colors_sub xs; return (fx::fxs)
       od)
End

Theorem map_colors_sub_eq:
   map_colors_sub = st_ex_MAP colors_sub
Proof
  once_rewrite_tac [FUN_EQ_THM]
  \\ Induct \\ fs [map_colors_sub_def,st_ex_MAP_def]
QED

val res = m_translate spill_register_def;
val res = m_translate MAP_colors_def;
val res = m_translate st_ex_FOLDL_def;
val res = m_translate map_colors_sub_def;
val res = m_translate remove_inactive_intervals_def;

val res = translate linear_reg_alloc_pass1_initial_state_def
val res = translate linear_reg_alloc_pass2_initial_state_def
val res = translate add_active_interval_def
val res = translate find_color_in_list_def
val res = translate find_color_in_colornum_def
val res = translate find_color_def
val res = m_translate color_register_def
val res = m_translate find_last_stealable_def;
val res = m_translate find_spill_def;
val res = m_translate (linear_reg_alloc_step_aux_def
                       |> REWRITE_RULE [MEMBER_INTRO]);
val res = m_translate (linear_reg_alloc_step_pass1_def
                       |> REWRITE_RULE [GSYM map_colors_sub_eq]);
val res = m_translate (linear_reg_alloc_step_pass2_def
                       |> REWRITE_RULE [GSYM map_colors_sub_eq]);

val res = m_translate find_reg_exchange_def
val res = m_translate apply_reg_exchange_def
val res = translate edges_to_adjlist_impl_def
val res = m_translate st_ex_FILTER_good_def;

val res = translate sort_moves_def;

val res = m_translate (linear_reg_alloc_intervals_def
                       |> REWRITE_RULE [edges_to_adjlist_impl_thm]);

val res = m_translate extract_coloration_def;
val res = translate find_bijection_init_def;
val res = translate find_bijection_step_def;
val res = translate find_bijection_def;
val res = translate apply_bijection_def;

val res = m_translate
  linear_reg_alloc_intervals_and_extract_coloration_def;
val res = m_translate_run run_linear_reg_alloc_intervals_def;

val res = translate get_live_tree_def;
val res = translate numset_list_insert_def;
val res = translate get_live_backward_def;
val res = translate fix_domination_def;
val res = translate numset_list_add_if_def;
val res = translate numset_list_add_if_lt_def;
val res = translate numset_list_add_if_gt_def;
val res = translate get_intervals_def;
val res = translate linear_scan_reg_alloc_def;

*)
