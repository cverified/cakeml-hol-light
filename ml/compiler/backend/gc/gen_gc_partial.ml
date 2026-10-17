(* ======================================================== *)
(*  gen_gc_partial: ported from HOL4's
    compiler/backend/gc/gen_gc_partialScript.sml  *)
(* ======================================================== *)

(*
  The minor collection of the generational copying garbage collector.
*)

needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "lib/integer_word.ml";;
(* HOL4 ancestors outside the port: words *)

(* HOL4 ML code, not ported:
val gc_state_component_equality = DB.fetch "gc_shared"
  "gc_state_component_equality";
*)

let gen_gc_partial_conf_FIELDS = define_record "gen_gc_partial_conf"
  ["limit","num";
   "isRef","'a->bool";
   "gen_start","num";
   "refs_start","num"];;
hol4_overload "limit" "gen_gc_partial_conf_limit";;
hol4_overload "limit_fupd" "gen_gc_partial_conf_limit_fupd";;
hol4_overload "isRef" "gen_gc_partial_conf_isRef";;
hol4_overload "isRef_fupd" "gen_gc_partial_conf_isRef_fupd";;

let gc_move_def = cake_define_list
  [`gen_gc_partial_gc_move conf state (gc_shared_Data d) =
  ((gc_shared_Data d:'a heap_address),state)`;
   `gen_gc_partial_gc_move conf state (gc_shared_Pointer ptr d) =
         (let ok = (gc_state_ok state /\ (ptr < heap_length
           (gc_state_heap state))) in
         (if ptr < gen_gc_partial_conf_gen_start conf \/
           gen_gc_partial_conf_refs_start conf <= ptr then
            (gc_shared_Pointer ptr d,gc_state_ok_fupd (K ok) state)
              else
          match heap_lookup ptr (gc_state_heap state) with SOME
            (DataElement xs l dd) ->
              (let ok = (ok /\ l + 1 <= gc_state_n state /\ ~(isRef
                conf dd)) in
               let n = gc_state_n state - (l + 1) in
               let h2 = gc_state_h2 state ++ [DataElement xs l dd]
                 in
               let (heap,ok) = gc_forward_ptr ptr (gc_state_heap
                 state) (gc_state_a state) d ok in
               let a = gc_state_a state + l + 1 in
                 (
                 gc_shared_Pointer (gc_state_a state)
                   d,gc_state_ok_fupd (K ok) (gc_state_heap_fupd (K
                   heap) (gc_state_a_fupd (K a) (gc_state_n_fupd (K
                   n) (gc_state_h2_fupd (K h2) state)))))) | SOME
                   (ForwardPointer ptr _3 l) -> (gc_shared_Pointer
                   ptr d,state) | _4 -> (gc_shared_Pointer ptr
                   d,gc_state_ok_fupd (K F) state)))`];;
hol4_overload "gc_move" "gen_gc_partial_gc_move";;

let gc_move_list_def = cake_define_list
  [`gen_gc_partial_gc_move_list conf state [] = ([],state)`;
   `gen_gc_partial_gc_move_list conf state (x :: xs) =
        (let (x,state) = gc_move conf state x in
        let (xs,state) = gen_gc_partial_gc_move_list conf state xs
          in
          (x :: xs,state))`];;
hol4_overload "gc_move_list" "gen_gc_partial_gc_move_list";;

(* HOL4 termination: \\ rw [heap_length_def,el_length_def,SUM_APPEND]
   \\ imp_res_tac (GSYM gc_move_list_IMP) \\ fs [] \\ decide_tac *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let gc_move_data_def = cake_define_try_tac (fun () ->
  `MEASURE (\(conf,state). limit conf - heap_length (gc_state_h1
  state))`)
  CHEAT_TAC
  `(gen_gc_partial_gc_move_data conf state =
     (match gc_state_h2 state with [] -> state | h :: h2 ->
       (if limit conf < heap_length (gc_state_h1 state ++ (h :: h2))
         then gc_state_ok_fupd (K F) state else
        match h with DataElement xs l d ->
          (let (xs,state) = gc_move_list conf state xs in
          let h1 = gc_state_h1 state ++ [DataElement xs l d] in
          let h2 = TL (gc_state_h2 state) in
          let ok = (gc_state_ok state /\ ~(gc_state_h2 state = []) /\
            (HD (gc_state_h2 state) = h)) in
            gen_gc_partial_gc_move_data conf (gc_state_ok_fupd (K
              ok) (gc_state_h2_fupd (K h2) (gc_state_h1_fupd (K h1)
              state)))) | _5 -> gc_state_ok_fupd (K F) state)))`;;
hol4_overload "gc_move_data" "gen_gc_partial_gc_move_data";;

let gc_move_ref_list_def = cake_define
  `gc_move_ref_list conf state x3 =
        match x3 with
          [] -> ([],state)
        | (DataElement ptrs l d :: xs) ->
       (let (ptrs',state) = gc_move_list conf state ptrs in
       let (xs,state) = gc_move_ref_list conf state xs in
         (DataElement ptrs' l d :: xs,state))
        | (x :: xs) -> (x :: xs,gc_state_ok_fupd (K F) state)`;;

let partial_gc_def = cake_define
  `partial_gc conf (roots,heap) =
     (match heap_segment (gen_gc_partial_conf_gen_start
       conf,gen_gc_partial_conf_refs_start conf) heap with NONE ->
       (roots,gc_state_ok_fupd (K F) empty_state) | SOME
       (old,current,refs) ->
       (let n = heap_length current in
       let state =
           gc_state_n_fupd (K n) (gc_state_a_fupd (K
             (gen_gc_partial_conf_gen_start conf)) (gc_state_r2_fupd (K
             refs) (gc_state_old_fupd (K old) (gc_state_heap_fupd (K
             heap) empty_state)))) in
       let (roots,state) = gc_move_list conf state roots in
       let (refs',state) = gc_move_ref_list conf state refs in
       let state = gc_move_data conf (gc_state_r2_fupd (K [])
         (gc_state_r1_fupd (K refs') state)) in
         (roots,state)))`;;

(* Pointers between current and old generations are correct *)
let heap_gen_ok_def = cake_define
  `heap_gen_ok heap conf <=>
     (?old current refs. gen_gc_partial_conf_gen_start
       conf <= gen_gc_partial_conf_refs_start conf /\
         gen_gc_partial_conf_refs_start conf <= limit conf /\
       EVERY isDataElement old /\
       EVERY isDataElement refs /\
       (SOME (old,current,refs) = heap_segment
         (gen_gc_partial_conf_gen_start
         conf,gen_gc_partial_conf_refs_start conf) heap) /\
       (!ptr xs l d u. MEM (DataElement xs l d) old /\ MEM
         (gc_shared_Pointer ptr u) xs ==>
         (ptr < gen_gc_partial_conf_gen_start conf \/
           gen_gc_partial_conf_refs_start conf <= ptr)) /\
       (!xs l d. MEM (DataElement xs l d) old ==> ~(isRef conf d)) /\
       (!xs l d. MEM (DataElement xs l d) current ==> ~(isRef conf
         d)) /\
       (!xs l d. MEM (DataElement xs l d) refs ==> isRef conf d))`;;

let data_sort_INDUCT,data_sort_RECURSION = define_datatype
  "data_sort = Protected ('a) | Real ('b)";;

let to_gen_heap_address_def = cake_define_list
  [`to_gen_heap_address conf (gc_shared_Data a) = gc_shared_Data
  (Real a)`;
   `to_gen_heap_address conf (gc_shared_Pointer ptr a) =
        (if ptr < gen_gc_partial_conf_gen_start conf then
          gc_shared_Data (Protected (gc_shared_Pointer ptr a)) else
            if gen_gc_partial_conf_refs_start conf <= ptr then
          gc_shared_Data (Protected (gc_shared_Pointer ptr a)) else
          gc_shared_Pointer (ptr -
            gen_gc_partial_conf_gen_start conf) (Real a))`];;

let to_gen_conf_def = cake_define
  `to_gen_conf (conf:'a gen_gc_partial_conf) =
     (mk_gen_gc_conf (limit conf - gen_gc_partial_conf_gen_start
       conf - (limit conf - gen_gc_partial_conf_refs_start conf))
       (isRef conf):'a gen_gc_conf)`;;

let to_gen_heap_element_def = cake_define_list
  [`to_gen_heap_element conf (Unused n) = Unused n`;
   `to_gen_heap_element conf (ForwardPointer ptr a l) =
        ForwardPointer (ptr - gen_gc_partial_conf_gen_start conf)
          (Real a) l`;
   `to_gen_heap_element conf (DataElement ptrs l d) =
        DataElement (MAP (to_gen_heap_address conf) ptrs) l d`];;

let to_gen_heap_list_def = cake_define
  `to_gen_heap_list conf heap =
     MAP (to_gen_heap_element conf) heap`;;

let to_gen_heap_def = cake_define
  `to_gen_heap conf heap =
     to_gen_heap_list conf
         (heap_restrict (gen_gc_partial_conf_gen_start conf)
           (gen_gc_partial_conf_refs_start conf) heap)`;;

let to_gen_state_def = cake_define
  `to_gen_state conf state = gc_state_heap0_fupd (K (to_gen_heap conf
  (gc_state_heap0 state))) (gc_state_heap_fupd (K (to_gen_heap conf
  (gc_state_heap state))) (gc_state_ok_fupd (K (gc_state_ok state))
  (gc_state_n_fupd (K (gc_state_n state)) (gc_state_a_fupd (K
  (gc_state_a state - gen_gc_partial_conf_gen_start conf))
  (gc_state_r1_fupd (K []) (gc_state_r2_fupd (K []) (gc_state_r3_fupd (K
  []) (gc_state_r4_fupd (K []) (gc_state_h2_fupd (K (to_gen_heap_list
  conf (gc_state_h2 state))) (gc_state_h1_fupd (K (to_gen_heap_list conf
  (gc_state_h1 state)))
     empty_state))))))))))`;;

let to_gen_roots_def = cake_define
  `to_gen_roots conf roots =
     MAP (to_gen_heap_address conf) roots`;;

let refs_to_roots_def = cake_define
  `refs_to_roots conf x2 =
        match x2 with
          [] -> []
        | (DataElement ptrs _6 _7 :: refs) ->
       MAP (to_gen_heap_address conf) ptrs ++ refs_to_roots conf refs
        | (_8 :: refs) -> refs_to_roots conf refs`;;

let RootsRefs = cake_inductive
  `(RootsRefs [] []) /\
   (!ptrs m b refs roots ptr a.
      RootsRefs (DataElement ptrs m b :: refs) roots ==>
      RootsRefs (DataElement (gc_shared_Pointer ptr a :: ptrs) m b ::
        refs) (gc_shared_Pointer ptr a :: roots)) /\
   (!ptrs m b refs roots a.
      RootsRefs (DataElement ptrs m b :: refs) roots ==>
      RootsRefs (DataElement (gc_shared_Data a :: ptrs) m b :: refs)
        (gc_shared_Data a :: roots)) /\
   (!refs roots m b.
      RootsRefs refs roots ==>
      RootsRefs (DataElement [] m b :: refs) roots) /\
   (!refs roots n.
      RootsRefs refs roots ==>
      RootsRefs (Unused n :: refs) roots) /\
   (!refs roots.
      RootsRefs refs roots ==>
      RootsRefs (ForwardPointer _9 _10 _11 :: refs) roots)`;;

(* HOL4 ML code, not ported:
val RootsRefs_def = RootsRefs_rules;
*)

(*

     GenGC     GC
inp    o ----> o
       |       |
       |       |
       v       v
out    o ----> o

last step: need a relation <---
 *)

let heap_element_is_ref_def = cake_define
  `heap_element_is_ref conf x2 =
        match x2 with
          DataElement xs l d -> isRef conf d
        | _12 -> F`;;

let gen_inv_def = cake_define
  `gen_inv (conf:'b gen_gc_partial_conf) heap =
  (gen_gc_partial_conf_gen_start
     conf <= gen_gc_partial_conf_refs_start conf /\
       gen_gc_partial_conf_refs_start
     conf <= limit conf /\
     (?heap_old heap_current heap_refs.
       (heap_segment (gen_gc_partial_conf_gen_start
         conf,gen_gc_partial_conf_refs_start conf) heap =
         SOME (heap_old,heap_current,heap_refs)) /\
       EVERY (\e. ~heap_element_is_ref conf e) heap_old /\
       EVERY (\e. ~heap_element_is_ref conf e) heap_current /\
       EVERY isDataElement heap_refs /\
       (!n a d.
          MEM (ForwardPointer n a d) heap ==>
            gen_gc_partial_conf_gen_start
          conf <= n /\ n < gen_gc_partial_conf_refs_start conf) /\
       EVERY isDataElement heap_old /\
       (!xs l d ptr u.
         MEM (DataElement xs l d) heap_old /\ MEM (gc_shared_Pointer
           ptr u) xs ==>
         ptr < gen_gc_partial_conf_gen_start conf \/
           gen_gc_partial_conf_refs_start conf <= ptr)))`;;

let has_old_ptr_def = cake_define
  `has_old_ptr conf hs ptr <=>
     (?xs l d u.
       MEM (DataElement xs l d) hs /\ MEM (gc_shared_Pointer ptr u)
         xs /\
       (ptr < gen_gc_partial_conf_gen_start conf \/
         gen_gc_partial_conf_refs_start conf <= ptr))`;;

(* HOL4 ML code, not ported:
val has_old_ptr_CONS =
  has_old_ptr_APPEND |> Q.SPEC `[x]` |> SIMP_RULE std_ss [APPEND]
*)

let all_old_ptrs_def = cake_define
  `all_old_ptrs conf xs ptr <=>
     (?u. MEM (gc_shared_Pointer ptr u) xs /\
         (ptr < gen_gc_partial_conf_gen_start conf \/
           gen_gc_partial_conf_refs_start conf <= ptr))`;;

let sim_inv_def = cake_define
  `sim_inv conf (heap0:(('a,'b)heap_element) list)
  (state:('a,'b)gc_state) <=>
     gen_inv conf (gc_state_heap state) /\
       gen_gc_partial_conf_gen_start
     conf <= gc_state_a state /\ gc_state_a
     state + gc_state_n state <= gen_gc_partial_conf_refs_start conf
       /\
     (gen_gc_partial_conf_gen_start conf + heap_length (gc_state_h1
       state ++ gc_state_h2 state) + gc_state_n state =
       gen_gc_partial_conf_refs_start conf) /\
     (gen_gc_partial_conf_refs_start conf <=
       gen_gc_partial_conf_gen_start conf ==> (gc_state_h1 state = [])
       /\ (gc_state_h2 state = [])) /\
     has_old_ptr conf (gc_state_heap state ++ gc_state_h1 state ++
       gc_state_h2 state ++ gc_state_r1 state) SUBSET has_old_ptr
       conf heap0`;;

let f_old_ptrs_def = cake_define
  `f_old_ptrs conf heap =
     {a |
          isSomeDataElement (heap_lookup a heap) /\ (a <
            gen_gc_partial_conf_gen_start conf \/
            gen_gc_partial_conf_refs_start conf <= a)}`;;

let new_f_def = cake_define
  `new_f f conf heap =
     FUNION (FUN_FMAP I (f_old_ptrs conf heap))
            (FUN_FMAP (\a. gen_gc_partial_conf_gen_start conf +
              FAPPLY f (a - gen_gc_partial_conf_gen_start conf))
                      (IMAGE ((+) (gen_gc_partial_conf_gen_start
                        conf)) (FDOM f)))`;;

(* HOL4 ML code, not ported:
val heap_lookup_heap_expand = isSomeDataElement_heap_lookup_heap_expand
  |> SIMP_RULE std_ss [isSomeDataElement_def];
*)

let similar_ptr_def = cake_define
  `similar_ptr conf x1 x2 =
        match (x1,x2) with
          (gc_shared_Pointer p1 d1,gc_shared_Pointer p2 d2) -> (d2 =
            d1)
        | (x1,x2) -> (x1 = x2)`;;

let similar_data_def = cake_define
  `similar_data conf x y =
        match (x,y) with
          (DataElement xs1 l1 d1,DataElement xs2 l2 d2) ->
       (l2 = l1) /\ (d2 = d1) /\ LIST_REL (similar_ptr conf) xs1 xs2
        | (x,y) -> (x = y)`;;

let has_bad_ref_def = cake_define
  `has_bad_ref c s <=>
     (?xs l d. MEM (DataElement xs l d) (gc_state_h1 s ++ gc_state_h2
       s) /\ isRef c d) \/
     (?xs l d n. gen_gc_partial_conf_gen_start
       c <= n /\ n < gen_gc_partial_conf_refs_start c /\
       (heap_lookup n (gc_state_heap s) = SOME (DataElement xs l
         d)) /\ isRef c d)`;;

let balanced_state_def = cake_define
  `balanced_state c s <=>
     (
      heap_length (FILTER isForwardPointer (gc_state_heap s)) =
        heap_length (gc_state_h1 s) + heap_length (gc_state_h2 s)) /\
     (match heap_segment (gen_gc_partial_conf_gen_start
       c,gen_gc_partial_conf_refs_start c) (gc_state_heap s) with NONE
       -> F | SOME (old,curr,refs) ->
         heap_length (FILTER isDataElement (gc_state_r1 s)) +
         heap_length (FILTER isDataElement (gc_state_r2 s)) +
         heap_length (FILTER isDataElement (gc_state_old s)) <=
         heap_length (FILTER isDataElement old) +
         heap_length (FILTER isDataElement refs))`;;

let simple_rel_def = cake_define
  `simple_rel c s1 s2 <=>
     (gc_state_old s2 = gc_state_old s1) /\
     (heap_length (gc_state_h1 s2 ++ gc_state_h2 s2 ++ heap_expand
       (gc_state_n s2)) =
      heap_length (gc_state_h1 s1 ++ gc_state_h2 s1 ++ heap_expand
        (gc_state_n s1))) /\
     ((gc_state_a s1 = gen_gc_partial_conf_gen_start c + heap_length
       (gc_state_h1 s1) + heap_length (gc_state_h2 s1)) ==>
      (gc_state_a s2 = gen_gc_partial_conf_gen_start c + heap_length
        (gc_state_h1 s2) + heap_length (gc_state_h2 s2))) /\
     (EVERY isDataElement (gc_state_h1 s1) ==> EVERY isDataElement
       (gc_state_h1 s2)) /\
     (heap_length (FILTER isDataElement (gc_state_heap s1) ++
       gc_state_h1 s1 ++ gc_state_h2 s1) =
      heap_length (FILTER isDataElement (gc_state_heap s2) ++
        gc_state_h1 s2 ++ gc_state_h2 s2)) /\
     (heap_length (FILTER isForwardPointer (gc_state_heap s1)) +
      heap_length (FILTER isDataElement (gc_state_heap s1)) =
      heap_length (FILTER isForwardPointer (gc_state_heap s2)) +
      heap_length (FILTER isDataElement (gc_state_heap s2))) /\
     (balanced_state c s1 ==> balanced_state c s2) /\
     (has_bad_ref c s2 ==> has_bad_ref c s1)`;;
