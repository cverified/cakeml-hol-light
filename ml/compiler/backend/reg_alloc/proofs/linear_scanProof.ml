(* ======================================================== *)
(*  linear_scanProof: ported from HOL4's
    compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml  *)
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

(* HOL4 ML code, not ported:
val _ = disable_tyabbrev_printing "type_ident"
val _ = disable_tyabbrev_printing "alist"
*)

(* TODO: clean up this file: e.g., move things upstream *)

(* why breaking encapsulation like this? To get rid of the assumption
   `wf s` *)

(* This theorem looks like lipschitz continuity: it says something like
   f(x+y) <= f(x)+y *)

(* HOL4 ML code, not ported:
val msimps = [st_ex_bind_def,st_ex_ignore_bind_def,st_ex_return_def];
*)

let lookup_default_id_def = cake_define
  `lookup_default_id s x = option_CASE (lookup x s) x (\x. x)`;;

let find_reg_exchange_step_def = cake_define
  `find_reg_exchange_step colors r (exch,invexch) =
       (let col1 = EL r colors in
       let fcol1 = r DIV 2 in
       let col2 = lookup_default_id invexch fcol1 in
       let fcol2 = lookup_default_id exch col1 in
       (insert col1 fcol1 (insert col2 fcol2 exch),insert fcol1
         col1 (insert fcol2 col2 invexch)))`;;

let id_def = cake_define
  `linear_scanProof_id x = x`;;
hol4_overload "id" "linear_scanProof_id";;

let less_FST_def = cake_define
  `less_FST (x:int#num) y = (FST x <= FST y)`;;

let good_linear_scan_state_def = cake_define
  `good_linear_scan_state st sth l (pos:int) forced mincol = (
       LENGTH (linear_scan_hidden_state_int_beg sth) = LENGTH
         (linear_scan_hidden_state_colors sth) /\ LENGTH
         (linear_scan_hidden_state_int_end sth) = LENGTH
         (linear_scan_hidden_state_colors sth) /\
       ALL_DISTINCT (linear_scan_state_colorpool st ++ MAP (\(e,r).
         EL' r (linear_scan_hidden_state_colors sth))
         (linear_scan_state_active st)) /\
       EVERY (\r. r < LENGTH (linear_scan_hidden_state_colors sth)) l
         /\
       EVERY (\r. EL' r (linear_scan_hidden_state_colors sth) <
         linear_scan_state_stacknum st) l /\
       domain (linear_scan_state_phyregs st) = {EL' r
         (linear_scan_hidden_state_colors sth) | r | MEM r l /\
         is_phy_var r /\ EL' r (linear_scan_hidden_state_colors sth) <
         linear_scan_state_colormax st} /\
       ALL_DISTINCT (MAP (\r. EL' r (linear_scan_hidden_state_colors
         sth)) (FILTER is_phy_var l)) /\
       EVERY (\c. c < linear_scan_state_colornum st)
         (linear_scan_state_colorpool st) /\
       EVERY (\(e,r). EL' r (linear_scan_hidden_state_colors sth) <
         linear_scan_state_colornum st) (linear_scan_state_active st) /\
         linear_scan_state_colornum
       st <= linear_scan_state_colormax st /\
         linear_scan_state_colormax
       st <= linear_scan_state_stacknum st /\
       EVERY (\r. EL' r (linear_scan_hidden_state_colors sth) <
         linear_scan_state_colormax st ==> EL' r
         (linear_scan_hidden_state_colors sth) <
         linear_scan_state_colornum st) l /\
       EVERY (\r. EL' r (linear_scan_hidden_state_int_beg sth) <=
         pos) l /\
       EVERY (\r. ((pos <= EL' r (linear_scan_hidden_state_int_end
         sth) /\ EL' r (linear_scan_hidden_state_colors sth) <
         linear_scan_state_colormax st) ==> (MEM (EL' r
         (linear_scan_hidden_state_int_end sth),r)
         (linear_scan_state_active st)))) l /\
       EVERY (\r. ((MEM (EL' r (linear_scan_hidden_state_int_end
         sth),r) (linear_scan_state_active st)) ==> (pos <= 1 + EL' r
         (linear_scan_hidden_state_int_end sth)))) l /\
       (!r1 r2. MEM r1 l /\ MEM r2 l /\
           interval_intersect (EL' r1
             (linear_scan_hidden_state_int_beg sth),EL' r1
             (linear_scan_hidden_state_int_end sth)) (EL' r2
             (linear_scan_hidden_state_int_beg sth),EL' r2
             (linear_scan_hidden_state_int_end sth)) /\
           EL' r1 (linear_scan_hidden_state_colors sth) = EL' r2
             (linear_scan_hidden_state_colors sth) ==> r1 = r2) /\
       SORTED less_FST (linear_scan_state_active st) /\
       EVERY (\(e,r). e = EL' r (linear_scan_hidden_state_int_end
         sth)) (linear_scan_state_active st) /\
       EVERY (\(e,r). MEM r l) (linear_scan_state_active st) /\
       EVERY (\(r1,r2). MEM r1 l /\ MEM r2 l /\ EL' r1
         (linear_scan_hidden_state_colors sth) = EL' r2
         (linear_scan_hidden_state_colors sth) ==> r1 = r2) forced /\
       mincol <= linear_scan_state_colornum st /\
       EVERY (\c. mincol <= c) (linear_scan_state_colorpool st ++
         MAP (\r. EL' r (linear_scan_hidden_state_colors sth)) l))`;;

(* HOL4 ML code, not ported:
val good_linear_scan_state_def' = let
  val inj_rwt = Q.prove(‘(f x = f y ==> x = y) ⇔ (f x = f y ⇔ x = y)’,
                        metis_tac[])
in
  good_linear_scan_state_def
    |> SIMP_RULE bool_ss [GSYM AND_IMP_INTRO, inj_rwt]
    |> SIMP_RULE bool_ss [AND_IMP_INTRO]
end
*)

(* TODO: this should be part of the standard library, but I couldn't
   find it *)
let IS_SPARSE_SUBLIST_def = cake_define
  `(
     IS_SPARSE_SUBLIST [] l2 = T) /\ (
     IS_SPARSE_SUBLIST (x :: xs) [] = F) /\ (
     IS_SPARSE_SUBLIST (x :: xs) (y :: ys) =
       ((x = y /\ IS_SPARSE_SUBLIST xs ys) \/ IS_SPARSE_SUBLIST (x
         :: xs) ys))`;;

let edges_to_adjlist_step_def = cake_define
  `edges_to_adjlist_step sth (a,b) acc =
     (if a = b then
       acc else if ((<) LEX (<=)) (EL a
         (linear_scan_hidden_state_int_beg sth),a) (EL b
         (linear_scan_hidden_state_int_beg sth),b) then
       insert b (a :: (the [] (lookup b acc))) acc else
       insert a (b :: (the [] (lookup a acc))) acc)`;;

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

let phystack_on_stack_def = cake_define
  `phystack_on_stack l st sth =
     (!r. MEM r l /\ is_phy_var r /\ 2 *
       linear_scan_state_colormax st <= r ==>
       linear_scan_state_colormax st <= EL r
       (linear_scan_hidden_state_colors sth))`;;

(* TODO: move *)
let intbeg_less_def = cake_define
  `intbeg_less (int_beg:int list) r1 r2 = ((<) LEX (<=)) (EL r1
  int_beg,r1) (EL r2 int_beg,r2)`;;

(* TODO: move *)

let good_bijection_state_def = cake_define
  `good_bijection_state st regset = (
       regset = domain (bijection_state_bij st) /\
       (
         sp_inverts (bijection_state_bij st) (bijection_state_invbij
           st) /\
         sp_inverts (bijection_state_invbij st) (bijection_state_bij
           st)) /\ (
         (!r. r IN regset ==> (is_stack_var r <=> is_stack_var (the 0
           (lookup r (bijection_state_bij st))))) /\
         (!r. r IN regset ==> (is_alloc_var r <=> is_alloc_var (the 0
           (lookup r (bijection_state_bij st))))) /\
         (!r. r IN regset /\ is_phy_var r ==> r = (the 0 (lookup r
           (bijection_state_bij st))))) /\
       (!r. r IN domain (bijection_state_invbij st) /\ is_stack_var r
         ==> r < bijection_state_nstack st) /\
       (!r. r IN domain (bijection_state_invbij st) /\ is_alloc_var r
         ==> r < bijection_state_nalloc st) /\
       (
         is_stack_var (bijection_state_nstack st) /\
         is_alloc_var (bijection_state_nalloc st)) /\
       (!r. the 0 (lookup r (bijection_state_bij st)) <=
         bijection_state_nmax st))`;;

let sptree_eq_list_def = cake_define
  `sptree_eq_list (s:int spt) l = (!i.
     i < LENGTH l ==>
     (0 < EL i l <=> lookup i s = NONE) /\
     (EL i l <= 0 <=> lookup i s = SOME (EL i l)))`;;

(* TODO: move *)
