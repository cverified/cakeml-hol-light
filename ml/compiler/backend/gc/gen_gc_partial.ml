(* ======================================================== *)
(*  gen_gc_partial: ported from HOL4's
    compiler/backend/gc/gen_gc_partialScript.sml
    A definition theory, with 27 definitions, 2 datatypes and 110
    theorems.  Needed by 6 files of the port.  *)
(* ======================================================== *)

(*
  The minor collection of the generational copying garbage collector.
*)

needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "lib/integer_word.ml";;
(* HOL4 ancestors outside the port: words *)

(* HOL4 gen_gc_partialScript.sml:14: ML code, not ported *)

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

let gen_gc_partial_gc_move_IMP = cake_theorem "gc_move_IMP"
  (fun () ->
    `!x x' state state1.
      (gc_move conf state x = (x',state1)) ==>
      (gc_state_old state1 = gc_state_old state) /\
      (gc_state_h1 state1 = gc_state_h1 state) /\
      (gc_state_r4 state1 = gc_state_r4 state) /\
      (gc_state_r3 state1 = gc_state_r3 state) /\
      (gc_state_r2 state1 = gc_state_r2 state) /\
      (gc_state_r1 state1 = gc_state_r1 state)`)
  CHEAT_TAC;;

let gc_move_list_def = cake_define_list
  [`gen_gc_partial_gc_move_list conf state [] = ([],state)`;
   `gen_gc_partial_gc_move_list conf state (x :: xs) =
        (let (x,state) = gc_move conf state x in
        let (xs,state) = gen_gc_partial_gc_move_list conf state xs
          in
          (x :: xs,state))`];;
hol4_overload "gc_move_list" "gen_gc_partial_gc_move_list";;

let gen_gc_partial_gc_move_list_IMP = cake_theorem "gc_move_list_IMP"
  (fun () ->
    `!xs xs' state state1.
      (gc_move_list conf state xs = (xs',state1)) ==>
      (LENGTH xs = LENGTH xs') /\
      (gc_state_old state1 = gc_state_old state) /\
      (gc_state_h1 state1 = gc_state_h1 state) /\
      (gc_state_r4 state1 = gc_state_r4 state) /\
      (gc_state_r3 state1 = gc_state_r3 state) /\
      (gc_state_r2 state1 = gc_state_r2 state) /\
      (gc_state_r1 state1 = gc_state_r1 state)`)
  CHEAT_TAC;;

(* HOL4 gen_gc_partialScript.sml:113-119: the tactic that proves the
   termination *)
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

let gc_move_data_IMP = cake_theorem "gc_move_data_IMP"
  (fun () ->
    `!conf state state1.
      (gc_move_data conf state = state1) ==>
      (gc_state_old state1 = gc_state_old state) /\
      (gc_state_r1 state1 = gc_state_r1 state) /\
      (gc_state_r2 state1 = gc_state_r2 state) /\
      (gc_state_r3 state1 = gc_state_r3 state) /\
      (gc_state_r4 state1 = gc_state_r4 state)`)
  CHEAT_TAC;;

let gc_move_ref_list_def = cake_define
  `gc_move_ref_list conf state x3 =
        match x3 with
          [] -> ([],state)
        | (DataElement ptrs l d :: xs) ->
       (let (ptrs',state) = gc_move_list conf state ptrs in
       let (xs,state) = gc_move_ref_list conf state xs in
         (DataElement ptrs' l d :: xs,state))
        | (x :: xs) -> (x :: xs,gc_state_ok_fupd (K F) state)`;;

let gc_move_ref_list_IMP = cake_theorem "gc_move_ref_list_IMP[local]"
  (fun () ->
    `!conf state refs state1 refs1.
     (gc_move_ref_list conf state refs = (refs1,state1)) ==>
     (gc_state_old state1 = gc_state_old state) /\
     (gc_state_r1 state1 = gc_state_r1 state) /\
     (gc_state_r2 state1 = gc_state_r2 state) /\
     (heap_length refs = heap_length refs1) /\
     (!ptr.
        isSomeDataElement (heap_lookup ptr refs) ==>
        isSomeDataElement (heap_lookup ptr refs1))`)
  CHEAT_TAC;;

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

let partial_gc_IMP = cake_theorem "partial_gc_IMP[local]"
  (fun () ->
    `!roots heap roots1 state1 heap_old heap_current heap_refs.
     (partial_gc conf (roots,heap) = (roots1,state1)) /\
     (heap_segment (gen_gc_partial_conf_gen_start
       conf,gen_gc_partial_conf_refs_start conf) heap =
       SOME (heap_old,heap_current,heap_refs)) ==>
     (gc_state_old state1 = heap_old) /\
     (heap_length (gc_state_r1 state1) = heap_length heap_refs) /\
     (LENGTH roots = LENGTH roots1) /\
     (!ptr.
        isSomeDataElement (heap_lookup ptr heap_refs) ==>
        isSomeDataElement (heap_lookup ptr (gc_state_r1 state1)))`)
  CHEAT_TAC;;

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

let to_gen_heap_list_heap_length =
  cake_theorem "to_gen_heap_list_heap_length[local]"
  (fun () ->
    `!xs.
     heap_length (to_gen_heap_list conf xs) = heap_length xs`)
  CHEAT_TAC;;

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

(* HOL4 gen_gc_partialScript.sml:346: ML code, not ported *)

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

let has_old_ptr_APPEND = cake_theorem "has_old_ptr_APPEND[local]"
  (fun () ->
    `!xs ys. has_old_ptr conf (xs ++ ys) =
             has_old_ptr conf xs UNION has_old_ptr conf ys`)
  CHEAT_TAC;;

(* HOL4 gen_gc_partialScript.sml:399-400: ML code, not ported *)

let all_old_ptrs_def = cake_define
  `all_old_ptrs conf xs ptr <=>
     (?u. MEM (gc_shared_Pointer ptr u) xs /\
         (ptr < gen_gc_partial_conf_gen_start conf \/
           gen_gc_partial_conf_refs_start conf <= ptr))`;;

let has_old_ptr_simp = cake_theorem "has_old_ptr_simp[simp]"
  (fun () ->
    `has_old_ptr conf [DataElement xs x1 x2] = all_old_ptrs conf xs`)
  CHEAT_TAC;;

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

let heap_length_to_gen_heap_list =
  cake_theorem "heap_length_to_gen_heap_list[simp]"
  (fun () ->
    `!h2. heap_length (to_gen_heap_list conf h2) = heap_length h2`)
  CHEAT_TAC;;

let el_length_not_zero = cake_theorem "el_length_not_zero[simp]"
  (fun () ->
    `!x. ~(el_length x = 0)`)
  CHEAT_TAC;;

let heap_split_length = cake_theorem "heap_split_length"
  (fun () ->
    `!h1 h2. heap_split (heap_length h1) (h1 ++ h2) = SOME (h1,h2)`)
  CHEAT_TAC;;

let heap_segment_length = cake_theorem "heap_segment_length[local]"
  (fun () ->
    `heap_segment (heap_length h1,heap_length h1 + heap_length h2) (h1
  ++ h2 ++ h3) = SOME (h1,h2,h3)`)
  CHEAT_TAC;;

let gc_move_simulation = cake_theorem "gc_move_simulation[local]"
  (fun () ->
    `!ptr ptr' state state' ptr1' state1'.
       (gc_move conf state ptr = (ptr',state')) /\
       (!ptr' u. (ptr = gc_shared_Pointer ptr' u) ==> ptr' <
         heap_length (gc_state_heap state)) /\
       (heap_length (gc_state_heap state) = limit conf) /\
       sim_inv conf heap0 state /\
       (gen_gc_gc_move
          (to_gen_conf conf)
          (to_gen_state conf state)
          (to_gen_heap_address conf ptr) = (ptr1',state1')) /\
            gc_state_ok state1' ==>
       sim_inv conf heap0 state' /\
       (
        (ptr1',state1') = (to_gen_heap_address conf
          ptr',to_gen_state conf state')) /\
       all_old_ptrs conf [ptr'] SUBSET all_old_ptrs conf [ptr]`)
  CHEAT_TAC;;

let gc_forward_ptr_heap_length =
  cake_theorem "gc_forward_ptr_heap_length"
  (fun () ->
    `!n h m a ok h' ok'. (gc_forward_ptr n h m a ok = (h',ok')) ==>
  (heap_length h = heap_length h')`)
  CHEAT_TAC;;

let gc_move_heap_length = cake_theorem "gc_move_heap_length"
  (fun () ->
    `(gc_move conf state h = (x,state')) ==> (heap_length
  (gc_state_heap state) = heap_length (gc_state_heap state'))`)
  CHEAT_TAC;;

let gen_gc_partial_gc_move_list_heap_length =
  cake_theorem "gc_move_list_heap_length"
  (fun () ->
    `!h x state state'. (gc_move_list conf state h = (x,state')) ==>
  (heap_length (gc_state_heap state) = heap_length (gc_state_heap
  state'))`)
  CHEAT_TAC;;

let gc_move_ref_list_heap_length =
  cake_theorem "gc_move_ref_list_heap_length"
  (fun () ->
    `!h x state state'.
     (gc_move_ref_list conf state h = (x,state')) ==>
       (heap_length (gc_state_heap state) = heap_length (gc_state_heap
       state'))`)
  CHEAT_TAC;;

let gc_move_ok' = cake_theorem "gc_move_ok'"
  (fun () ->
    `(gc_move conf state x = (x',state')) /\ gc_state_ok state' ==>
  gc_state_ok state`)
  CHEAT_TAC;;

let gen_gc_partial_gc_move_ok = cake_theorem "gc_move_ok"
  (fun () ->
    `(gc_move conf state x = (x',state')) /\ gc_state_ok state' /\
  (!ptr' u. (x = gc_shared_Pointer ptr' u) ==> ptr' < heap_length
  (gc_state_heap state)) ==> gc_state_ok state`)
  CHEAT_TAC;;

let gc_move_list_ok' = cake_theorem "gc_move_list_ok'"
  (fun () ->
    `!xs xs' state state'.
      (gc_move_list conf state xs = (xs',state')) /\ gc_state_ok
        state' ==> gc_state_ok
        state`)
  CHEAT_TAC;;

let gen_gc_partial_gc_move_list_ok = cake_theorem "gc_move_list_ok"
  (fun () ->
    `!xs xs' state state'.
      (gc_move_list conf state xs = (xs',state')) /\
        gc_state_ok state' /\ (!ptr' u. MEM (gc_shared_Pointer ptr'
          u) xs ==> ptr' < heap_length (gc_state_heap state)) ==>
          gc_state_ok
        state`)
  CHEAT_TAC;;

let gc_move_ref_list_ok' = cake_theorem "gc_move_ref_list_ok'"
  (fun () ->
    `!xs xs' state state'.
      (gc_move_ref_list conf state xs = (xs',state')) /\
        gc_state_ok state' ==> gc_state_ok
        state`)
  CHEAT_TAC;;

let gc_move_data_ok' = cake_theorem "gc_move_data_ok'"
  (fun () ->
    `!conf state state'.
       (gc_move_data conf state = state') /\ gc_state_ok state' ==>
         gc_state_ok
         state`)
  CHEAT_TAC;;

let gc_move_list_simulation =
  cake_theorem "gc_move_list_simulation[local]"
  (fun () ->
    `!ptr ptr' state state' ptr1' state1'.
       (gc_move_list conf state ptr = (ptr',state')) /\
       sim_inv conf heap0 state /\
       (!ptr' u. MEM (gc_shared_Pointer ptr' u) ptr ==> ptr' <
         heap_length (gc_state_heap state)) /\
       (heap_length (gc_state_heap state) = limit conf) /\
       (gen_gc_gc_move_list
          (to_gen_conf conf)
          (to_gen_state conf state)
          (MAP (to_gen_heap_address conf) ptr) = (ptr1',state1'))
            /\ gc_state_ok state1' ==>
       sim_inv conf heap0 state' /\
       (
        (ptr1',state1') = (MAP (to_gen_heap_address conf)
          ptr',to_gen_state conf state')) /\
       all_old_ptrs conf ptr' SUBSET all_old_ptrs conf ptr`)
  CHEAT_TAC;;

let gc_move_list_APPEND = cake_theorem "gc_move_list_APPEND[local]"
  (fun () ->
    `!conf state0 xs ys roots' state'.
       (gen_gc_gc_move_list conf state0 (xs ++ ys) =
         (roots',state')) ==>
       (?roots1 roots2 state1.
         (gen_gc_gc_move_list conf state0 xs = (roots1,state1)) /\
         (gen_gc_gc_move_list conf state1 ys = (roots2,state')) /\
         (roots' = roots1 ++ roots2))`)
  CHEAT_TAC;;

let heap_restrict_NIL = cake_theorem "heap_restrict_NIL[simp]"
  (fun () ->
    `heap_restrict gen_start refs_start [] = []`)
  CHEAT_TAC;;

let to_gen_heap_NIL = cake_theorem "to_gen_heap_NIL[simp]"
  (fun () ->
    `to_gen_heap conf [] = []`)
  CHEAT_TAC;;

let to_gen_heap_list_NIL = cake_theorem "to_gen_heap_list_NIL[simp]"
  (fun () ->
    `to_gen_heap_list conf [] = []`)
  CHEAT_TAC;;

let gc_move_data_r1 = cake_theorem "gc_move_data_r1[local]"
  (fun () ->
    `!refs state conf. gc_state_r1
       (gc_move_data conf (gc_state_r1_fupd (K refs) state)) =
         refs`)
  CHEAT_TAC;;

let gc_move_ref_list_simulation =
  cake_theorem "gc_move_ref_list_simulation[local]"
  (fun () ->
    `!conf state refs0 heap0 state1 state1' refs1 refs1'.
     (
       gc_move_ref_list conf (state:('b,'a)gc_state)
         (refs0:(('b,'a)heap_element) list) = (refs1,state1)) /\
     (
       gc_move_list (to_gen_conf conf)
                   (to_gen_state conf state)
                   (refs_to_roots conf refs0) = (refs1',state1'))
                     /\ gc_state_ok state1' /\
     sim_inv conf heap0 state /\
     (!ptrs l d ptr' u. MEM (gc_shared_Pointer ptr' u) ptrs /\ MEM
       (DataElement ptrs l d) refs0 ==> ptr' < heap_length
       (gc_state_heap state)) /\
     (heap_length (gc_state_heap state) = limit conf) /\
     EVERY isDataElement refs0 ==>
     sim_inv conf heap0 state1 /\
     (refs1' = refs_to_roots conf refs1) /\
     (state1' = to_gen_state conf state1) /\
     has_old_ptr conf refs1 SUBSET has_old_ptr conf refs0`)
  CHEAT_TAC;;

let gc_move_list_r1 = cake_theorem "gc_move_list_r1[local]"
  (fun () ->
    `!s0 xs ys s1. (gc_move_list conf s0 xs = (ys,s1)) ==>
  (gc_state_r1 s1 = gc_state_r1 s0)`)
  CHEAT_TAC;;

let gen_gc_partial_gc_move_data_r1 =
  cake_theorem "gc_move_data_r1[local]"
  (fun () ->
    `(gc_move_data conf (gc_state_r1_fupd (K refs') state') = state1)
  ==>
     (gc_state_r1 state1 = refs')`)
  CHEAT_TAC;;

let el_length_to_gen_heap_element =
  cake_theorem "el_length_to_gen_heap_element[local]"
  (fun () ->
    `!h. el_length (to_gen_heap_element conf h) = el_length h`)
  CHEAT_TAC;;

let to_gen_heap_address_11 =
  cake_theorem "to_gen_heap_address_11[local]"
  (fun () ->
    `!x y.
       (to_gen_heap_address conf x = to_gen_heap_address conf y)
         ==> (x = y)`)
  CHEAT_TAC;;

let MAP_to_gen_heap_address_11 =
  cake_theorem "MAP_to_gen_heap_address_11[local]"
  (fun () ->
    `!x y.
       (MAP (to_gen_heap_address conf) x = MAP
         (to_gen_heap_address conf) y) <=> (x = y)`)
  CHEAT_TAC;;

let gc_forward_ptr_data_pres =
  cake_theorem "gc_forward_ptr_data_pres[local]"
  (fun () ->
    `!x a ptr d ok x' ok'.
      (gc_forward_ptr a x ptr d ok = (x',ok')) ==> (
           MEM (DataElement xs l dd) x = (MEM (DataElement xs l
             dd) x' \/ (heap_lookup a x = SOME (DataElement xs l
             dd))))`)
  CHEAT_TAC;;

let gc_move_data_pres = cake_theorem "gc_move_data_pres[local]"
  (fun () ->
    `(gc_move conf state x = (x1,state1)) ==> (
           MEM (DataElement xs l dd) (gc_state_heap state1 ++
             gc_state_h2 state1) = MEM (DataElement xs l dd)
             (gc_state_heap state ++ gc_state_h2 state))`)
  CHEAT_TAC;;

let gc_move_list_data_pres =
  cake_theorem "gc_move_list_data_pres[local]"
  (fun () ->
    `!x conf state x1 state1 xs l dd.
      (gc_move_list conf state x = (x1,state1)) ==> (
           MEM (DataElement xs l dd) (gc_state_heap state1 ++
             gc_state_h2 state1) = MEM (DataElement xs l dd)
             (gc_state_heap state ++ gc_state_h2 state))`)
  CHEAT_TAC;;

let gc_move_ref_list_data_pres =
  cake_theorem "gc_move_ref_list_data_pres[local]"
  (fun () ->
    `!x conf state x1 state1 xs l dd.
      (gc_move_ref_list conf state x = (x1,state1)) ==> (
           MEM (DataElement xs l dd) (gc_state_heap state1 ++
             gc_state_h2 state1) = MEM (DataElement xs l dd)
             (gc_state_heap state ++ gc_state_h2 state))`)
  CHEAT_TAC;;

let gc_move_data_simulation =
  cake_theorem "gc_move_data_simulation[local]"
  (fun () ->
    `!conf state heap0 state' ptr1' state1'.
       (gc_move_data conf state = state') /\
       sim_inv conf heap0 state /\
       (!ptrs l d ptr' u. MEM (gc_shared_Pointer ptr' u) ptrs /\
         MEM (DataElement ptrs l d) (gc_state_h2 state ++ gc_state_heap
         state) ==> ptr' < heap_length (gc_state_heap state)) /\
       (heap_length (gc_state_heap state) = limit conf) /\
       (gen_gc_gc_move_data
          (to_gen_conf conf)
          (to_gen_state conf state) = state1') /\ gc_state_ok
            state1' ==>
       sim_inv conf heap0 state' /\
       (state1' = to_gen_state conf state')`)
  CHEAT_TAC;;

let gc_move_with_refs = cake_theorem "gc_move_with_refs[local]"
  (fun () ->
    `!l. (gc_move conf (gc_state_r1_fupd (K refs) state) l =
          (let (xs,s) = gc_move conf state l in
            (xs,gc_state_r1_fupd (K refs) s)))`)
  CHEAT_TAC;;

let gc_move_with_refs' = cake_theorem "gc_move_with_refs'[local]"
  (fun () ->
    `!l. (gc_move conf (gc_state_r1_fupd (K refs) (gc_state_r2_fupd (K
  []) state)) l =
          (let (xs,s) = gc_move conf state l in
            (xs,gc_state_r1_fupd (K refs) (gc_state_r2_fupd (K [])
            s))))`)
  CHEAT_TAC;;

let gc_move_list_with_refs =
  cake_theorem "gc_move_list_with_refs[local]"
  (fun () ->
    `!l state.
       (gc_move_list conf (gc_state_r1_fupd (K refs) state) l =
       (let (xs,s) = gc_move_list conf state l in
         (xs,gc_state_r1_fupd (K refs) s)))`)
  CHEAT_TAC;;

let gc_move_list_with_refs' =
  cake_theorem "gc_move_list_with_refs'[local]"
  (fun () ->
    `!l state.
       (gc_move_list conf (gc_state_r1_fupd (K refs)
         (gc_state_r2_fupd (K []) state)) l =
        (let (xs,s) = gc_move_list conf state l in
          (xs,gc_state_r1_fupd (K refs) (gc_state_r2_fupd (K []) s))))`)
  CHEAT_TAC;;

let gc_move_data_with_refs =
  cake_theorem "gc_move_data_with_refs[local]"
  (fun () ->
    `!conf state refs.
       (gc_move_data conf (gc_state_r1_fupd (K refs) state) =
         gc_state_r1_fupd (K refs)
       (gc_move_data conf state))`)
  CHEAT_TAC;;

let gc_move_data_with_refs' =
  cake_theorem "gc_move_data_with_refs'[local]"
  (fun () ->
    `!conf state refs.
      (gc_move_data conf (gc_state_r1_fupd (K refs)
        (gc_state_r2_fupd (K []) state)) = gc_state_r1_fupd (K refs)
        (gc_state_r2_fupd (K [])
      (gc_move_data conf state)))`)
  CHEAT_TAC;;

let gen_gc_partial_gc_move_data_h2 =
  cake_theorem "gc_move_data_h2[local]"
  (fun () ->
    `!conf state. gc_state_ok
       (gc_move_data conf state) ==>
       (gc_state_h2 (gc_move_data conf state) = [])`)
  CHEAT_TAC;;

let gen_gc_partial_gc_move_ref_list_heap_length =
  cake_theorem "gc_move_ref_list_heap_length[local]"
  (fun () ->
    `!h x state state'. (gc_move_ref_list conf state h = (x,state'))
  ==> (heap_length (gc_state_heap state) = heap_length (gc_state_heap
  state'))`)
  CHEAT_TAC;;

let gen_gc_partial_gc_move_data_r1 =
  cake_theorem "gc_move_data_r1[local]"
  (fun () ->
    `gc_state_r1
       (gc_move_data conf state) = gc_state_r1 state`)
  CHEAT_TAC;;

let partial_gc_simulation = cake_theorem "partial_gc_simulation[local]"
  (fun () ->
    `!conf roots heap0 roots1 state1 heap0_old heap0_current heap0_refs
      new_roots new_state.
       (partial_gc conf (roots,heap0) = (roots1,state1)) /\
       heap_gen_ok heap0 conf /\ gen_gc_partial_conf_gen_start
       conf <= gen_gc_partial_conf_refs_start conf /\
         gen_gc_partial_conf_refs_start conf <= limit conf /\
       (
         heap_segment (gen_gc_partial_conf_gen_start
           conf,gen_gc_partial_conf_refs_start conf) heap0 = SOME
           (heap0_old,heap0_current,heap0_refs)) /\
       EVERY (\e. ~(heap_element_is_ref conf e)) (heap0_old ++
         heap0_current) /\
       EVERY isDataElement heap0_refs /\
       roots_ok roots heap0 /\
       (gen_gc (to_gen_conf conf)
         (to_gen_roots conf roots ++ refs_to_roots conf heap0_refs,
          to_gen_heap_list conf heap0_current) =
            (new_roots,new_state)) /\
       heap_ok heap0 (limit conf) /\ gc_state_ok new_state ==>
       (new_roots = to_gen_roots conf roots1 ++ refs_to_roots conf
         (gc_state_r1 state1)) /\
       (new_state = to_gen_state conf state1) /\
       sim_inv conf heap0 state1 /\ (gc_state_h2 state1 = []) /\
         gc_state_ok state1`)
  CHEAT_TAC;;

let f_old_ptrs_def = cake_define
  `f_old_ptrs conf heap =
     {a |
          isSomeDataElement (heap_lookup a heap) /\ (a <
            gen_gc_partial_conf_gen_start conf \/
            gen_gc_partial_conf_refs_start conf <= a)}`;;

let f_old_ptrs_finite = cake_theorem "f_old_ptrs_finite[simp]"
  (fun () ->
    `!heap conf.
      FINITE (f_old_ptrs conf heap)`)
  CHEAT_TAC;;

(* HOL4 gen_gc_partialScript.sml:1315-1316: a theorem that HOL4
   states as the value of an ML expression *)

let new_f_def = cake_define
  `new_f f conf heap =
     FUNION (FUN_FMAP I (f_old_ptrs conf heap))
            (FUN_FMAP (\a. gen_gc_partial_conf_gen_start conf +
              FAPPLY f (a - gen_gc_partial_conf_gen_start conf))
                      (IMAGE ((+) (gen_gc_partial_conf_gen_start
                        conf)) (FDOM f)))`;;

let APPEND_LENGTH_IMP = cake_theorem "APPEND_LENGTH_IMP[local]"
  (fun () ->
    `!a c b d.
     ((a ++ b) = (c ++ d)) /\ (LENGTH a = LENGTH c) ==>
     (a = c) /\ (b = d)`)
  CHEAT_TAC;;

let roots_ok_APPEND = cake_theorem "roots_ok_APPEND[local]"
  (fun () ->
    `!left right heap.
     roots_ok (left ++ right) heap ==>
     roots_ok left heap /\
     roots_ok right heap`)
  CHEAT_TAC;;

let roots_ok_CONS = cake_theorem "roots_ok_CONS[local]"
  (fun () ->
    `!h t.
     roots_ok (h :: t) heap ==>
     roots_ok t heap`)
  CHEAT_TAC;;

let isSomeDataElement_to_gen_heap_list =
  cake_theorem "isSomeDataElement_to_gen_heap_list[simp]"
  (fun () ->
    `!n heap.
      isSomeDataElement (heap_lookup n (to_gen_heap_list conf
        heap)) = isSomeDataElement (heap_lookup n heap)`)
  CHEAT_TAC;;

(* HOL4 gen_gc_partialScript.sml:1371-1372: a theorem that HOL4
   states as the value of an ML expression *)

let MEM_refs_to_roots_IMP_MEM =
  cake_theorem "MEM_refs_to_roots_IMP_MEM[local]"
  (fun () ->
    `!heap_refs.
     MEM (gc_shared_Pointer ptr u) (refs_to_roots conf heap_refs)
       ==>
     (?xs l d ptr' u'.
     MEM (DataElement xs l d) heap_refs /\
     MEM (gc_shared_Pointer ptr' u') xs /\
     (ptr = ptr' - gen_gc_partial_conf_gen_start conf) /\
     (u = Real u') /\
     (gen_gc_partial_conf_gen_start conf <= ptr') /\
     (ptr' < gen_gc_partial_conf_refs_start conf))`)
  CHEAT_TAC;;

let MEM_to_gen_roots_IMP_MEM =
  cake_theorem "MEM_to_gen_roots_IMP_MEM[local]"
  (fun () ->
    `!roots.
     MEM (gc_shared_Pointer ptr u) (to_gen_roots conf roots) ==>
     (?ptr' u'.
     MEM (gc_shared_Pointer ptr' u') roots /\
     (ptr = ptr' - gen_gc_partial_conf_gen_start conf) /\
     (u = Real u') /\
     (gen_gc_partial_conf_gen_start conf <= ptr') /\
     (ptr' < gen_gc_partial_conf_refs_start conf))`)
  CHEAT_TAC;;

let roots_ok_simulation = cake_theorem "roots_ok_simulation[local]"
  (fun () ->
    `!roots heap heap_old heap_current heap_refs (conf:'b
  gen_gc_partial_conf).
     roots_ok roots (heap:(('a,'b)heap_element) list) /\
     heap_ok heap (limit conf) /\
     (heap_segment (gen_gc_partial_conf_gen_start
       conf,gen_gc_partial_conf_refs_start conf) heap = SOME
       (heap_old,heap_current,heap_refs)) /\
     (gen_gc_partial_conf_gen_start conf <=
       gen_gc_partial_conf_refs_start conf) ==>
     roots_ok
       (to_gen_roots conf roots ++ refs_to_roots conf heap_refs)
       (MAP (to_gen_heap_element conf) heap_current)`)
  CHEAT_TAC;;

(* HOL4 gen_gc_partialScript.sml:1459-1460: a theorem that HOL4
   states as the value of an ML expression *)

let MEM_to_gen_heap_IMP_MEM =
  cake_theorem "MEM_to_gen_heap_IMP_MEM[local]"
  (fun () ->
    `!heap_current xs l d ptr u.
     MEM (DataElement xs l d) (MAP (to_gen_heap_element conf)
       heap_current) /\
     MEM (gc_shared_Pointer ptr u) xs ==>
     (?xs' u' ptr'.
     MEM (DataElement xs' l d) heap_current /\
     MEM (gc_shared_Pointer ptr' u') xs' /\
     (xs = MAP (to_gen_heap_address conf) xs') /\
     (ptr = ptr' - gen_gc_partial_conf_gen_start conf) /\
     (u = Real u') /\
     (ptr' < gen_gc_partial_conf_refs_start conf) /\
     (gen_gc_partial_conf_gen_start conf <= ptr'))`)
  CHEAT_TAC;;

let heap_ok_simulation = cake_theorem "heap_ok_simulation[local]"
  (fun () ->
    `!heap heap_old heap_current heap_refs (conf:'b
  gen_gc_partial_conf).
     heap_ok (heap:(('a,'b)heap_element) list) (limit conf) /\
     (heap_segment (gen_gc_partial_conf_gen_start
       conf,gen_gc_partial_conf_refs_start conf) heap = SOME
       (heap_old,heap_current,heap_refs)) /\
     (gen_gc_partial_conf_gen_start conf <=
       gen_gc_partial_conf_refs_start conf) /\
     (gen_gc_partial_conf_refs_start conf <= limit conf) ==>
     heap_ok
       (MAP (to_gen_heap_element conf) heap_current) (limit
       (to_gen_conf conf))`)
  CHEAT_TAC;;

let new_f_FDOM = cake_theorem "new_f_FDOM[local]"
  (fun () ->
    `(!i. i IN FDOM f ==> isSomeDataElement (heap_lookup (i +
  gen_gc_partial_conf_gen_start conf) heap)) ==>
     ((x IN FDOM (new_f f conf heap)) =
     (if x < gen_gc_partial_conf_gen_start conf \/
       gen_gc_partial_conf_refs_start conf <= x then
     isSomeDataElement (heap_lookup x heap) else
     x IN (IMAGE ((+) (gen_gc_partial_conf_gen_start conf)) (FDOM
       f))))`)
  CHEAT_TAC;;

let new_f_FAPPLY = cake_theorem "new_f_FAPPLY[local]"
  (fun () ->
    `(x IN FDOM (new_f f conf heap)) /\
     (!i. i IN FDOM f ==> isSomeDataElement (heap_lookup (i +
       gen_gc_partial_conf_gen_start conf) heap)) ==>
     (FAPPLY (new_f f conf heap) x =
     (if x < gen_gc_partial_conf_gen_start conf \/
       gen_gc_partial_conf_refs_start conf <= x then
     x else gen_gc_partial_conf_gen_start
     conf + FAPPLY f (x - gen_gc_partial_conf_gen_start conf)))`)
  CHEAT_TAC;;

let isSomeDataElement_heap_lookup_heap_expand =
  cake_theorem "isSomeDataElement_heap_lookup_heap_expand[simp]"
  (fun () ->
    `~isSomeDataElement (heap_lookup x (heap_expand n))`)
  CHEAT_TAC;;

(* HOL4 gen_gc_partialScript.sml:1581-1582: ML code, not ported *)

let heap_lookup_old_IMP = cake_theorem "heap_lookup_old_IMP[local]"
  (fun () ->
    `!i ys.
     (partial_gc conf (roots,heap) = (roots1,state1)) /\
     gen_inv conf heap /\
     (heap_lookup i heap = SOME (DataElement xs l d)) /\
     (i < gen_gc_partial_conf_gen_start conf) ==>
     (heap_lookup i (gc_state_old state1 ++ ys) = SOME
       (DataElement xs l d))`)
  CHEAT_TAC;;

let heap_lookup_old_IMP_ALT =
  cake_theorem "heap_lookup_old_IMP_ALT[local]"
  (fun () ->
    `!ys.
     (partial_gc conf (roots,heap) = (roots1,state1)) /\
     gen_inv conf heap /\
     isSomeDataElement (heap_lookup x heap) /\
     (x < gen_gc_partial_conf_gen_start conf) ==>
     isSomeDataElement (heap_lookup x (gc_state_old state1 ++
       ys))`)
  CHEAT_TAC;;

let heap_lookup_refs_IMP = cake_theorem "heap_lookup_refs_IMP[local]"
  (fun () ->
    `!x.
     (partial_gc conf (roots,heap) = (roots1,state1)) /\
     gen_inv conf heap /\
     (heap_lookup x heap = SOME (DataElement xs l d)) /\
     (heap_length (gc_state_old state1 ++ gc_state_h1 state1 ++
       heap_expand (gc_state_n state1)) = gen_gc_partial_conf_refs_start
       conf) /\
     (gen_gc_partial_conf_refs_start conf <= x) ==>
     (?xs1.
     (heap_lookup x (gc_state_old state1 ++ gc_state_h1 state1 ++
       heap_expand (gc_state_n state1) ++ gc_state_r1 state1) =
       SOME (DataElement xs1 l d)))`)
  CHEAT_TAC;;

let heap_lookup_refs_IMP_ALT =
  cake_theorem "heap_lookup_refs_IMP_ALT[local]"
  (fun () ->
    `(partial_gc conf (roots,heap) = (roots1,state1)) /\
     gen_inv conf heap /\
     isSomeDataElement (heap_lookup x heap) /\
     (heap_length (gc_state_old state1 ++ gc_state_h1 state1 ++
       heap_expand (gc_state_n state1)) = gen_gc_partial_conf_refs_start
       conf) /\
     (gen_gc_partial_conf_refs_start conf <= x) ==>
     isSomeDataElement (heap_lookup x (gc_state_old state1 ++
       gc_state_h1 state1 ++ heap_expand (gc_state_n state1) ++
       gc_state_r1 state1))`)
  CHEAT_TAC;;

let ADDR_MAP_ID = cake_theorem "ADDR_MAP_ID[local]"
  (fun () ->
    `(!x u. MEM (gc_shared_Pointer x u) xs ==> (x = f x)) ==> (xs =
  ADDR_MAP f xs)`)
  CHEAT_TAC;;

let MEM_heap_old = cake_theorem "MEM_heap_old[local]"
  (fun () ->
    `!n m i x.
     (heap_segment (n,m) heap = SOME
       (heap_old,heap_current,heap_refs)) /\
     (n <= m) /\
     i < n /\
     (heap_lookup i heap = SOME x) ==>
     MEM x heap_old`)
  CHEAT_TAC;;

let FILTER_isForward_to_gen =
  cake_theorem "FILTER_isForward_to_gen[local]"
  (fun () ->
    `!xs.
     (FILTER isForwardPointer (to_gen_heap_list conf xs) = []) ==>
     (FILTER isForwardPointer xs = [])`)
  CHEAT_TAC;;

let isSomeData_to_gen_heap_IMP =
  cake_theorem "isSomeData_to_gen_heap_IMP[local]"
  (fun () ->
    `!xs ptr conf ys l d.
     (heap_lookup ptr (to_gen_heap_list conf xs) = SOME
       (DataElement ys l d)) ==>
     isSomeDataElement (heap_lookup ptr xs)`)
  CHEAT_TAC;;

let refs_to_roots_APPEND = cake_theorem "refs_to_roots_APPEND[local]"
  (fun () ->
    `!xs ys.
     refs_to_roots conf (xs ++ ys) = refs_to_roots conf xs ++
       refs_to_roots conf ys`)
  CHEAT_TAC;;

let gc_move_refs_isForwardPointer =
  cake_theorem "gc_move_refs_isForwardPointer[local]"
  (fun () ->
    `!refs refs1 state1 state.
     (gc_move_ref_list conf state refs = (refs1,state1)) /\
     (FILTER isForwardPointer refs = []) ==>
     (FILTER isForwardPointer refs1 = [])`)
  CHEAT_TAC;;

let gen_gc_partial_el_length_to_gen_heap_element =
  cake_theorem "el_length_to_gen_heap_element[simp]"
  (fun () ->
    `el_length (to_gen_heap_element conf h) = el_length h`)
  CHEAT_TAC;;

let to_gen_heap_element_isSomeData =
  cake_theorem "to_gen_heap_element_isSomeData[local]"
  (fun () ->
    `!xs n.
     isSomeDataElement (heap_lookup n (MAP (to_gen_heap_element
       (conf:'b gen_gc_partial_conf)) (xs:(('a,'b)heap_element) list)))
       ==>
     isSomeDataElement (heap_lookup n xs)`)
  CHEAT_TAC;;

let heap_lookup_GT_FALSE = cake_theorem "heap_lookup_GT_FALSE[local]"
  (fun () ->
    `!xs n.
     ~(n < heap_length xs) ==>
     ~(isSomeDataElement (heap_lookup n xs))`)
  CHEAT_TAC;;

let heap_lookup_to_gen_heap_element =
  cake_theorem "heap_lookup_to_gen_heap_element[local]"
  (fun () ->
    `!heap_current i.
       isSomeDataElement (heap_lookup i (MAP (to_gen_heap_element
         conf) heap_current)) =
       isSomeDataElement (heap_lookup i heap_current)`)
  CHEAT_TAC;;

let partial_gc_heap_length_lemma =
  cake_theorem "partial_gc_heap_length_lemma[local]"
  (fun () ->
    `!roots'.
     (partial_gc conf (roots,heap) = (roots1,state1)) /\
     (gen_gc (to_gen_conf conf) (gen_roots,gen_heap) =
       (roots',to_gen_state conf state1)) /\
     (heap_segment (gen_gc_partial_conf_gen_start
       conf,gen_gc_partial_conf_refs_start conf) heap = SOME
       (heap_old,heap_current,heap_refs)) /\
     (gen_gc_partial_conf_gen_start conf <=
       gen_gc_partial_conf_refs_start conf) /\
     (gen_gc_partial_conf_refs_start conf <= limit conf) /\
     roots_ok gen_roots gen_heap /\
     heap_ok gen_heap (limit (to_gen_conf conf)) ==>
     (heap_length (gc_state_old state1 ++ gc_state_h1 state1 ++
       heap_expand (gc_state_n state1)) =
       gen_gc_partial_conf_refs_start conf)`)
  CHEAT_TAC;;

let gc_move_ref_list_isSomeDataElement =
  cake_theorem "gc_move_ref_list_isSomeDataElement[local]"
  (fun () ->
    `!refs ptr state state1 refs1.
     (gc_move_ref_list conf state refs = (refs1,state1)) /\
     isSomeDataElement (heap_lookup ptr refs) ==>
     isSomeDataElement (heap_lookup ptr refs1)`)
  CHEAT_TAC;;

let ptr_Real_lemma = cake_theorem "ptr_Real_lemma[local]"
  (fun () ->
    `!ys ptr.
     MEM (gc_shared_Pointer ptr u) ys /\
     (gen_gc_partial_conf_gen_start conf <= ptr) /\
     (ptr < gen_gc_partial_conf_refs_start conf) ==>
     MEM (gc_shared_Pointer (ptr - gen_gc_partial_conf_gen_start
       conf) (Real u)) (MAP (to_gen_heap_address conf) ys)`)
  CHEAT_TAC;;

let partial_gc_refs_isSomeDataElement_isSomeDataElement =
  cake_theorem
    "partial_gc_refs_isSomeDataElement_isSomeDataElement[local]"
  (fun () ->
    `!ptr heap state1 heap_current heap_refs.
     (
      partial_gc conf (roots,heap) = (roots1,state1)) /\
     (heap_segment (gen_gc_partial_conf_gen_start
       conf,gen_gc_partial_conf_refs_start conf) heap = SOME
       (gc_state_old state1,heap_current,heap_refs)) /\
     isSomeDataElement (heap_lookup ptr heap_refs) ==>
     isSomeDataElement (heap_lookup ptr (gc_state_r1 state1))`)
  CHEAT_TAC;;

let isSomeData_to_gen_heap_IMP_isSomeData =
  cake_theorem "isSomeData_to_gen_heap_IMP_isSomeData[local]"
  (fun () ->
    `!heap ptr.
     isSomeDataElement (heap_lookup ptr (to_gen_heap_list conf heap
       ++ heap_expand (gc_state_n state1))) ==>
     isSomeDataElement (heap_lookup ptr (heap ++ heap_expand
       (gc_state_n state1)))`)
  CHEAT_TAC;;

let refs_root_IMP_isSomeData =
  cake_theorem "refs_root_IMP_isSomeData[local]"
  (fun () ->
    `!(state1:('a,'b)gc_state) (conf:'b gen_gc_partial_conf) refs.
     MEM (DataElement xs l d) refs /\
     MEM (gc_shared_Pointer ptr u) xs /\
     roots_ok (refs_to_roots conf refs)
       (to_gen_heap_list conf (gc_state_h1 state1) ++ heap_expand
         (gc_state_n state1)) /\
     (ptr < gen_gc_partial_conf_refs_start conf) /\
     ~(ptr < gen_gc_partial_conf_gen_start conf) ==>
     isSomeDataElement (heap_lookup (ptr -
       gen_gc_partial_conf_gen_start conf) (gc_state_h1 state1 ++
       heap_expand (gc_state_n state1)))`)
  CHEAT_TAC;;

let ADDR_MAP_APPEND_LENGTH_IMP =
  cake_theorem "ADDR_MAP_APPEND_LENGTH_IMP[local]"
  (fun () ->
    `!(roots:('a heap_address) list) (heap_refs:(('a,'b)heap_element)
  list) (f:(num,num)fmap) roots1 (r1:(('a,'b)heap_element) list)
  (conf:'b gen_gc_partial_conf).
     (ADDR_MAP ((FAPPLY) f) (to_gen_roots conf roots ++
       refs_to_roots conf heap_refs) =
        to_gen_roots conf roots1 ++ refs_to_roots conf r1) /\
     (LENGTH roots = LENGTH roots1) ==>
     (ADDR_MAP ((FAPPLY) f) (to_gen_roots conf roots) =
       to_gen_roots conf roots1) /\
     (ADDR_MAP ((FAPPLY) f) (refs_to_roots conf heap_refs) =
       refs_to_roots conf r1)`)
  CHEAT_TAC;;

let heap_lookup_by_f_isSomeData_lemma =
  cake_theorem "heap_lookup_by_f_isSomeData_lemma[local]"
  (fun () ->
    `!h1 x xs (state1:('a,'b)gc_state) (heap:(('a,'b)heap_element) list)
  conf.
     (heap_lookup x
       (MAP (to_gen_heap_element conf) h1 ++ heap_expand
         (gc_state_n state1)) =
       SOME (DataElement (ADDR_MAP ((FAPPLY) f) (MAP
         (to_gen_heap_address conf) xs)) l d)) /\
     (!u ptr.
        MEM (gc_shared_Pointer ptr u) xs ==>
        isSomeDataElement (heap_lookup ptr heap)) /\
     (!ptr u.
        MEM (gc_shared_Pointer ptr u) (MAP (to_gen_heap_address
          conf) xs) ==>
        ptr IN FDOM f) ==>
     (heap_lookup x (h1 ++ heap_expand (gc_state_n state1) ++
       gc_state_r1 state1) =
       SOME (DataElement (ADDR_MAP ((FAPPLY) (new_f f conf heap))
         xs) l d))`)
  CHEAT_TAC;;

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

let LENGTH_ADDR_MAP = cake_theorem "LENGTH_ADDR_MAP[local]"
  (fun () ->
    `!xs. LENGTH (ADDR_MAP f xs) = LENGTH xs`)
  CHEAT_TAC;;

let heap_lookup_similar_data_IMP =
  cake_theorem "heap_lookup_similar_data_IMP[local]"
  (fun () ->
    `!h1 h2 n.
       LIST_REL (similar_data conf) h1 h2 /\
       (heap_lookup n h1 = SOME (DataElement xs1 l d)) /\
       (ADDR_MAP (FAPPLY f) (refs_to_roots conf h1) = refs_to_roots
         conf h2) ==>
       (?xs2. (heap_lookup n h2 = SOME (DataElement xs2 l d)) /\
             (ADDR_MAP ((FAPPLY) f) (MAP (to_gen_heap_address conf)
               xs1) =
                MAP (to_gen_heap_address conf) xs2))`)
  CHEAT_TAC;;

let new_f_old_parts = cake_theorem "new_f_old_parts[local]"
  (fun () ->
    `n IN FDOM (new_f f conf heap) /\
     (!i. i IN FDOM f ==>
          isSomeDataElement (heap_lookup (i +
            gen_gc_partial_conf_gen_start conf) heap)) /\
     (n < gen_gc_partial_conf_gen_start conf \/
       gen_gc_partial_conf_refs_start conf <= n) ==>
     (FAPPLY (new_f f conf heap) n = n)`)
  CHEAT_TAC;;

let gc_move_list_similar = cake_theorem "gc_move_list_similar[local]"
  (fun () ->
    `!xs state1 ys state2.
       (gc_move_list conf state1 xs = (ys,state2)) ==>
       LIST_REL (similar_ptr conf) xs ys`)
  CHEAT_TAC;;

let gc_move_ref_list_similar =
  cake_theorem "gc_move_ref_list_similar[local]"
  (fun () ->
    `!heap_refs state refs' state' conf.
       (gc_move_ref_list conf state heap_refs = (refs',state')) ==>
       LIST_REL (similar_data conf) heap_refs refs'`)
  CHEAT_TAC;;

let IMP_gen_inv = cake_theorem "IMP_gen_inv[local]"
  (fun () ->
    `heap_ok (heap:(('a,'b)heap_element) list) (limit conf) /\
     heap_gen_ok heap conf ==>
     gen_inv conf heap`)
  CHEAT_TAC;;

let partial_gc_related = cake_theorem "partial_gc_related"
  (fun () ->
    `roots_ok roots heap /\
      heap_ok (heap:(('a,'b)heap_element) list) (limit conf) /\
      heap_gen_ok heap conf ==>
      (?state f.
        (partial_gc conf ((roots:('a heap_address) list),heap) =
           (ADDR_MAP (FAPPLY f) roots,state)) /\
        (!ptr u. MEM (gc_shared_Pointer ptr u) roots ==> ptr IN
          FDOM f) /\
        (heap_ok
          (gc_state_old state ++ gc_state_h1 state ++ heap_expand
            (gc_state_n state) ++ gc_state_r1 state) (limit conf)) /\
        gc_related f heap (gc_state_old state ++ gc_state_h1 state
          ++ heap_expand (gc_state_n state) ++ gc_state_r1 state) /\
          gc_state_ok
        state)`)
  CHEAT_TAC;;

let gen_gc_partial_gc_move_list_length =
  cake_theorem "gc_move_list_length"
  (fun () ->
    `!xs xs' state state'.
        (gc_move_list conf state xs = (xs',state')) ==>
        (LENGTH xs' = LENGTH xs)`)
  CHEAT_TAC;;

let gc_move_ref_list_length = cake_theorem "gc_move_ref_list_length"
  (fun () ->
    `!xs xs' state state'.
        (gc_move_ref_list conf state xs = (xs',state')) ==>
        (LENGTH xs' = LENGTH xs)`)
  CHEAT_TAC;;

let gc_move_ref_list_heap_length' =
  cake_theorem "gc_move_ref_list_heap_length'"
  (fun () ->
    `!xs xs' state state'.
        (gc_move_ref_list conf state xs = (xs',state')) ==>
        (heap_length xs' = heap_length xs)`)
  CHEAT_TAC;;

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

let simple_rel_refl = cake_theorem "simple_rel_refl[local]"
  (fun () ->
    `simple_rel c x x`)
  CHEAT_TAC;;

let simple_rel_trans = cake_theorem "simple_rel_trans[local]"
  (fun () ->
    `simple_rel c x1 x2 /\ simple_rel c x2 x3 ==> simple_rel c x1 x3`)
  CHEAT_TAC;;

let gc_forward_ptr_lookup_DataElement =
  cake_theorem "gc_forward_ptr_lookup_DataElement[local]"
  (fun () ->
    `!hs n x a heap n1.
       (gc_forward_ptr n hs x a T = (heap,T)) /\
       (heap_lookup n1 heap = SOME (DataElement xs l' d)) ==>
       (heap_lookup n1 hs = SOME (DataElement xs l' d))`)
  CHEAT_TAC;;

let gc_forward_ptr_APPEND = cake_theorem "gc_forward_ptr_APPEND[local]"
  (fun () ->
    `!x0 n a1 a x1 heap1.
       (gc_forward_ptr n (x0 ++ x1) a1 a T = (heap1,T)) ==>
       (if n < heap_length x0 then
         ?y0. (gc_forward_ptr n x0 a1 a T = (y0,T)) /\
              (heap1 = y0 ++ x1) else
         ?y1. (gc_forward_ptr (n - heap_length x0) x1 a1 a T =
           (y1,T)) /\
              (heap1 = x0 ++ y1))`)
  CHEAT_TAC;;

let gc_forward_ptr_APPEND_APPEND =
  cake_theorem "gc_forward_ptr_APPEND_APPEND[local]"
  (fun () ->
    `(gc_forward_ptr n (x0 ++ x1 ++ x2) a1 a T = (heap1,T)) /\
     heap_length x0 <= n /\ n < heap_length (x0 ++ x1) ==>
     (?y. (heap1 = x0 ++ y ++ x2) /\ (heap_length y = heap_length
       x1))`)
  CHEAT_TAC;;

let heap_segment_gc_forward_ptr =
  cake_theorem "heap_segment_gc_forward_ptr[local]"
  (fun () ->
    `(heap_segment (k,l) heap = SOME (x0,x1,x2)) /\
     (gc_forward_ptr n heap a1 a T = (heap1,T)) /\
     k <= n /\ n < l ==>
     (?y. (heap_segment (k,l) heap1 = SOME (x0,y,x2)))`)
  CHEAT_TAC;;

let gc_move_inv = cake_theorem "gc_move_inv"
  (fun () ->
    `!xs xs' s1 s2.
        (gc_move c s1 xs = (xs',s2)) /\ gc_state_ok s2 ==>
        simple_rel c s1 s2`)
  CHEAT_TAC;;

let gc_move_list_inv = cake_theorem "gc_move_list_inv"
  (fun () ->
    `!xs xs' s1 s2.
        (gc_move_list c s1 xs = (xs',s2)) /\ gc_state_ok s2 ==>
        simple_rel c s1 s2`)
  CHEAT_TAC;;

let gc_move_ref_list_inv = cake_theorem "gc_move_ref_list_inv"
  (fun () ->
    `!xs xs' s1 s2.
        (gc_move_ref_list c s1 xs = (xs',s2)) /\ gc_state_ok s2 ==>
        simple_rel c s1 s2`)
  CHEAT_TAC;;

let gc_move_data_inv = cake_theorem "gc_move_data_inv"
  (fun () ->
    `!c s1 s2.
        (gen_gc_partial_gc_move_data c s1 = s2) /\ gc_state_ok s2
          ==>
        simple_rel c s1 s2`)
  CHEAT_TAC;;

let LIST_REL_similar_data_IMP = cake_theorem "LIST_REL_similar_data_IMP"
  (fun () ->
    `!xs ys. LIST_REL (similar_data cc) xs ys ==>
              (heap_length xs = heap_length ys) /\
              (heap_length (FILTER isDataElement xs) =
               heap_length (FILTER isDataElement ys))`)
  CHEAT_TAC;;

let gen_gc_partial_partial_gc_IMP = cake_theorem "partial_gc_IMP"
  (fun () ->
    `(partial_gc c (roots,heap) = (roots1,state1)) /\ gc_state_ok state1
  ==>
      (gc_state_a state1 = gen_gc_partial_conf_gen_start c +
        heap_length (gc_state_h1 state1)) /\
      (LENGTH roots1 = LENGTH roots) /\
      (heap_length (gc_state_old state1) =
        gen_gc_partial_conf_gen_start c) /\
      (heap_length (gc_state_old state1 ++ gc_state_h1 state1 ++
        heap_expand (gc_state_n state1)) =
        gen_gc_partial_conf_refs_start
       c) /\
      ((FILTER isForwardPointer heap = []) ==>
       heap_length (FILTER isDataElement (gc_state_old state1 ++
         gc_state_h1 state1 ++ gc_state_r1 state1)) <=
       heap_length (FILTER isDataElement heap)) /\
      EVERY isDataElement (gc_state_h1 state1) /\
      (?curr refs. (heap_segment (gen_gc_partial_conf_gen_start
        c,gen_gc_partial_conf_refs_start c) heap =
                     SOME (gc_state_old state1,curr,refs)) /\
                  EVERY2 (similar_data c) refs (gc_state_r1 state1)
                    /\
                  (!xs l d. MEM (DataElement xs l d) (gc_state_h1
                    state1) /\ isRef
                            c d ==>
                            (?xs l d. MEM (DataElement xs l d)
                              curr /\ isRef c d)))`)
  CHEAT_TAC;;
