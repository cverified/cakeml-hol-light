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

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "gen_gc_partial"
  ["gc_shared"; "gen_gc"];;
(* HOL4 ancestors outside the port: words *)

(* HOL4 gen_gc_partialScript.sml:14: ML code, not ported *)

let gen_gc_partial_conf_FIELDS = define_record "gen_gc_partial_conf"
  ["limit","num";
   (* size of heap *)
   "isRef","'a->bool";
   "gen_start","num";
   (* start of generation *)
   "refs_start","num"
   (* start of references *)
  ];;

let gen_gc_partial_gc_move_def = define_cases
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
              (let ok = (ok /\ l + 1 <= gc_state_n state /\
                ~(gen_gc_partial_conf_isRef conf dd)) in
               let n = gc_state_n state - (l + 1) in
               let h2 = APPEND (gc_state_h2 state) [DataElement xs l
                 dd] in
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

(* gc_move_IMP *)
let gen_gc_partial_gc_move_IMP = prove
 (`!x x' state state1.
    (gen_gc_partial_gc_move conf state x = (x',state1)) ==>
    (gc_state_old state1 = gc_state_old state) /\
    (gc_state_h1 state1 = gc_state_h1 state) /\
    (gc_state_r4 state1 = gc_state_r4 state) /\
    (gc_state_r3 state1 = gc_state_r3 state) /\
    (gc_state_r2 state1 = gc_state_r2 state) /\
    (gc_state_r1 state1 = gc_state_r1 state)`,
  CHEAT_TAC);;

let gen_gc_partial_gc_move_list_def,gen_gc_partial_gc_move_list_ind =
  define_rec
  [`gen_gc_partial_gc_move_list conf state [] = ([],state)`;
   `gen_gc_partial_gc_move_list conf state (CONS x xs) =
        (let (x,state) = gen_gc_partial_gc_move conf state x in
        let (xs,state) = gen_gc_partial_gc_move_list conf state xs
          in
          (CONS x xs,state))`];;

(* gc_move_list_IMP *)
let gen_gc_partial_gc_move_list_IMP = prove
 (`!xs xs' state state1.
    (gen_gc_partial_gc_move_list conf state xs = (xs',state1)) ==>
    (LENGTH xs = LENGTH xs') /\
    (gc_state_old state1 = gc_state_old state) /\
    (gc_state_h1 state1 = gc_state_h1 state) /\
    (gc_state_r4 state1 = gc_state_r4 state) /\
    (gc_state_r3 state1 = gc_state_r3 state) /\
    (gc_state_r2 state1 = gc_state_r2 state) /\
    (gc_state_r1 state1 = gc_state_r1 state)`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (\(conf,state). gen_gc_partial_conf_limit conf - heap_length
       (gc_state_h1 state))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 gen_gc_partialScript.sml:113-119: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let gen_gc_partial_gc_move_data_def,gen_gc_partial_gc_move_data_ind =
  define_guess_cheat
  [`(gen_gc_partial_gc_move_data conf state =
     (match gc_state_h2 state with [] -> state | CONS h h2 ->
       (if gen_gc_partial_conf_limit conf < heap_length (APPEND
         (gc_state_h1 state) (CONS h h2)) then gc_state_ok_fupd (K F)
         state else
        match h with DataElement xs l d ->
          (let (xs,state) = gen_gc_partial_gc_move_list conf state
            xs in
          let h1 = APPEND (gc_state_h1 state) [DataElement xs l d]
            in
          let h2 = TL (gc_state_h2 state) in
          let ok = (gc_state_ok state /\ ~(gc_state_h2 state = [])
            /\ (HD (gc_state_h2 state) = h)) in
            gen_gc_partial_gc_move_data conf (gc_state_ok_fupd
              (K ok) (gc_state_h2_fupd (K h2) (gc_state_h1_fupd (K
              h1) state)))) | _5 -> gc_state_ok_fupd (K F) state)))`];;

let gc_move_data_IMP = prove
 (`!conf state state1.
    (gen_gc_partial_gc_move_data conf state = state1) ==>
    (gc_state_old state1 = gc_state_old state) /\
    (gc_state_r1 state1 = gc_state_r1 state) /\
    (gc_state_r2 state1 = gc_state_r2 state) /\
    (gc_state_r3 state1 = gc_state_r3 state) /\
    (gc_state_r4 state1 = gc_state_r4 state)`,
  CHEAT_TAC);;

let _ = size_thms "heap_element";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let gc_move_ref_list_def,gc_move_ref_list_ind = define_wf
  `MEASURE (\(x0,x1,x2). list_size (heap_element_size (\x. 0) (\x. 0))
  x2)`
  [`gc_move_ref_list conf state x3 =
        match x3 with
          [] -> ([],state)
        | CONS (DataElement ptrs l d) xs ->
       (let (ptrs',state) = gen_gc_partial_gc_move_list conf state
         ptrs in
       let (xs,state) = gc_move_ref_list conf state xs in
         (CONS (DataElement ptrs' l d) xs,state))
        | (CONS x xs) -> (CONS x xs,gc_state_ok_fupd (K F)
          state)`];;

(* [local] *)
let gc_move_ref_list_IMP = prove
 (`!conf state refs state1 refs1.
   (gc_move_ref_list conf state refs = (refs1,state1)) ==>
   (gc_state_old state1 = gc_state_old state) /\
   (gc_state_r1 state1 = gc_state_r1 state) /\
   (gc_state_r2 state1 = gc_state_r2 state) /\
   (heap_length refs = heap_length refs1) /\
   (!ptr.
      isSomeDataElement (heap_lookup ptr refs) ==>
      isSomeDataElement (heap_lookup ptr refs1))`,
  CHEAT_TAC);;

let partial_gc_def = new_definition
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
       // process roots:
       let (roots,state) = gen_gc_partial_gc_move_list conf state
         roots in
       // process references:
       let (refs',state) = gc_move_ref_list conf state refs in
       // process rest:
       let state = gen_gc_partial_gc_move_data conf (gc_state_r2_fupd
         (K []) (gc_state_r1_fupd (K refs') state)) in
         (roots,state)))`;;

(* [local] *)
let partial_gc_IMP = prove
 (`!roots heap roots1 state1 heap_old heap_current heap_refs.
   (partial_gc conf (roots,heap) = (roots1,state1)) /\
   (heap_segment (gen_gc_partial_conf_gen_start
     conf,gen_gc_partial_conf_refs_start conf) heap =
     SOME (heap_old,heap_current,heap_refs)) ==>
   (gc_state_old state1 = heap_old) /\
   (heap_length (gc_state_r1 state1) = heap_length heap_refs) /\
   (LENGTH roots = LENGTH roots1) /\
   (!ptr.
      isSomeDataElement (heap_lookup ptr heap_refs) ==>
      isSomeDataElement (heap_lookup ptr (gc_state_r1 state1)))`,
  CHEAT_TAC);;

(* Pointers between current and old generations are correct *)
let heap_gen_ok_def = new_definition
  `heap_gen_ok heap conf <=>
     (?old current refs. gen_gc_partial_conf_gen_start
       conf <= gen_gc_partial_conf_refs_start conf /\
         gen_gc_partial_conf_refs_start conf <=
         gen_gc_partial_conf_limit conf /\
       ALL isDataElement old /\
       ALL isDataElement refs /\
       (SOME (old,current,refs) = heap_segment
         (gen_gc_partial_conf_gen_start
         conf,gen_gc_partial_conf_refs_start conf) heap) /\
       (
        // old points only to itself and references
        !ptr xs l d u. MEM (DataElement xs l d) old /\ MEM
          (gc_shared_Pointer ptr u) xs ==>
         (ptr < gen_gc_partial_conf_gen_start conf \/
           gen_gc_partial_conf_refs_start conf <= ptr)) /\
       (
        // old contains no references
        !xs l d. MEM (DataElement xs l d) old ==>
          ~(gen_gc_partial_conf_isRef conf d)) /\
       (
        // old contains no references
        !xs l d. MEM (DataElement xs l d) current ==>
          ~(gen_gc_partial_conf_isRef conf d)) /\
       (
        // refs only contains references
        !xs l d. MEM (DataElement xs l d) refs ==>
          gen_gc_partial_conf_isRef conf d))`;;

let data_sort_INDUCT,data_sort_RECURSION = define_datatype
  "data_sort = Protected ('a) \
   // pointer to old generations\n\
   | Real ('b) \
   // data or pointer to current generation";;

let to_gen_heap_address_def = define_cases
  [`to_gen_heap_address conf (gc_shared_Data a) = gc_shared_Data
  (Real a)`;
   `to_gen_heap_address conf (gc_shared_Pointer ptr a) =
        (if ptr < gen_gc_partial_conf_gen_start conf then
          gc_shared_Data (Protected (gc_shared_Pointer ptr a)) else
            if gen_gc_partial_conf_refs_start conf <= ptr then
          gc_shared_Data (Protected (gc_shared_Pointer ptr a)) else
          gc_shared_Pointer (ptr -
            gen_gc_partial_conf_gen_start conf) (Real a))`];;

let to_gen_conf_def = new_definition
  `to_gen_conf (conf:'a gen_gc_partial_conf) =
     (mk_gen_gc_conf (gen_gc_partial_conf_limit conf -
       gen_gc_partial_conf_gen_start conf -
       (gen_gc_partial_conf_limit conf -
       gen_gc_partial_conf_refs_start conf))
       (gen_gc_partial_conf_isRef conf):'a gen_gc_conf)`;;

let to_gen_heap_element_def = define_cases
  [`to_gen_heap_element conf (Unused n) = Unused n`;
   `to_gen_heap_element conf (ForwardPointer ptr a l) =
        ForwardPointer (ptr - gen_gc_partial_conf_gen_start conf)
          (Real a) l`;
   `to_gen_heap_element conf (DataElement ptrs l d) =
        DataElement (MAP (to_gen_heap_address conf) ptrs) l d`];;

let to_gen_heap_list_def = new_definition
  `to_gen_heap_list conf heap =
     MAP (to_gen_heap_element conf) heap`;;

(* [local] *)
let to_gen_heap_list_heap_length = prove
 (`!xs.
   heap_length (to_gen_heap_list conf xs) = heap_length xs`,
  CHEAT_TAC);;

let to_gen_heap_def = new_definition
  `to_gen_heap conf heap =
     to_gen_heap_list conf
         (heap_restrict (gen_gc_partial_conf_gen_start conf)
           (gen_gc_partial_conf_refs_start conf) heap)`;;

let to_gen_state_def = new_definition
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

let to_gen_roots_def = new_definition
  `to_gen_roots conf roots =
     MAP (to_gen_heap_address conf) roots`;;

let _ = size_thms "heap_element";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let refs_to_roots_def,refs_to_roots_ind = define_wf
  `MEASURE (\(x0,x1). list_size (heap_element_size (\x. 0) (\x. 0)) x1)`
  [`refs_to_roots conf x2 =
        match x2 with
          [] -> []
        | CONS (DataElement ptrs _6 _7) refs -> APPEND (MAP
          (to_gen_heap_address conf) ptrs) (refs_to_roots conf refs)
        | (CONS _8 refs) -> refs_to_roots conf refs`];;

let RootsRefs = cake_inductive
  `(RootsRefs [] []) /\
   (!ptrs m b refs roots ptr a.
      RootsRefs (CONS (DataElement ptrs m b) refs) roots ==>
      RootsRefs (CONS (DataElement (CONS (gc_shared_Pointer ptr a)
        ptrs) m b) refs) (CONS (gc_shared_Pointer ptr a) roots)) /\
   (!ptrs m b refs roots a.
      RootsRefs (CONS (DataElement ptrs m b) refs) roots ==>
      RootsRefs (CONS (DataElement (CONS (gc_shared_Data a) ptrs) m
        b) refs) (CONS (gc_shared_Data a) roots)) /\
   (!refs roots m b.
      RootsRefs refs roots ==>
      RootsRefs (CONS (DataElement [] m b) refs) roots) /\
   (!refs roots n.
      RootsRefs refs roots ==>
      RootsRefs (CONS (Unused n) refs) roots) /\
   (!refs roots.
      RootsRefs refs roots ==>
      RootsRefs (CONS (ForwardPointer _9 _10 _11) refs) roots)`;;

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

let heap_element_is_ref_def = new_definition
  `heap_element_is_ref conf x2 =
        match x2 with
          DataElement xs l d -> gen_gc_partial_conf_isRef conf d
        | _12 -> F`;;

let gen_inv_def = new_definition
  `gen_inv (conf:'b gen_gc_partial_conf) heap =
  (gen_gc_partial_conf_gen_start
     conf <= gen_gc_partial_conf_refs_start conf /\
       gen_gc_partial_conf_refs_start
     conf <= gen_gc_partial_conf_limit conf /\
     (?heap_old heap_current heap_refs.
       (heap_segment (gen_gc_partial_conf_gen_start
         conf,gen_gc_partial_conf_refs_start conf) heap =
         SOME (heap_old,heap_current,heap_refs)) /\
       ALL (\e. ~(heap_element_is_ref conf e)) heap_old /\
       ALL (\e. ~(heap_element_is_ref conf e)) heap_current /\
       ALL isDataElement heap_refs /\
       (!n a d.
          MEM (ForwardPointer n a d) heap ==>
            gen_gc_partial_conf_gen_start
          conf <= n /\ n < gen_gc_partial_conf_refs_start conf) /\
       ALL isDataElement heap_old /\
       (!xs l d ptr u.
         MEM (DataElement xs l d) heap_old /\ MEM (gc_shared_Pointer
           ptr u) xs ==>
         ptr < gen_gc_partial_conf_gen_start conf \/
           gen_gc_partial_conf_refs_start conf <= ptr)))`;;

let has_old_ptr_def = new_definition
  `has_old_ptr conf hs ptr <=>
     (?xs l d u.
       MEM (DataElement xs l d) hs /\ MEM (gc_shared_Pointer ptr u)
         xs /\
       (ptr < gen_gc_partial_conf_gen_start conf \/
         gen_gc_partial_conf_refs_start conf <= ptr))`;;

(* [local] *)
let has_old_ptr_APPEND = prove
 (`!xs ys. has_old_ptr conf (APPEND xs ys) =
           has_old_ptr conf xs UNION has_old_ptr conf ys`,
  (REWRITE_TAC[EXTENSION; IN_UNION] THEN REWRITE_TAC[IN;
    has_old_ptr_def; MEM_APPEND] THEN
   MESON_TAC[]));;

(* HOL4 gen_gc_partialScript.sml:399-400: ML code, not ported *)

let all_old_ptrs_def = new_definition
  `all_old_ptrs conf xs ptr <=>
     (?u. MEM (gc_shared_Pointer ptr u) xs /\
         (ptr < gen_gc_partial_conf_gen_start conf \/
           gen_gc_partial_conf_refs_start conf <= ptr))`;;

(* [simp] *)
let has_old_ptr_simp = prove
 (`has_old_ptr conf [DataElement xs x1 x2] = all_old_ptrs conf xs`,
  CHEAT_TAC);;

let sim_inv_def = new_definition
  `sim_inv conf (heap0:(('a,'b)heap_element) list)
  (state:('a,'b)gc_state) <=>
     gen_inv conf (gc_state_heap state) /\
       gen_gc_partial_conf_gen_start
     conf <= gc_state_a state /\ gc_state_a
     state + gc_state_n state <= gen_gc_partial_conf_refs_start conf
       /\
     (gen_gc_partial_conf_gen_start conf + heap_length (APPEND
       (gc_state_h1 state) (gc_state_h2 state)) + gc_state_n state =
       gen_gc_partial_conf_refs_start conf) /\
     (gen_gc_partial_conf_refs_start conf <=
       gen_gc_partial_conf_gen_start conf ==> (gc_state_h1 state = [])
       /\ (gc_state_h2 state = [])) /\
     has_old_ptr conf (APPEND (APPEND (APPEND (gc_state_heap
       state) (gc_state_h1 state)) (gc_state_h2 state)) (gc_state_r1
       state)) SUBSET has_old_ptr conf heap0`;;

(* [simp] *)
let heap_length_to_gen_heap_list = prove
 (`!h2. heap_length (to_gen_heap_list conf h2) = heap_length h2`,
  CHEAT_TAC);;

(* [simp] *)
let el_length_not_zero = prove
 (`!x. ~(el_length x = 0)`,
  (REWRITE_TAC[el_length_NOT_0]));;

let heap_split_length = prove
 (`!h1 h2. heap_split (heap_length h1) (APPEND h1 h2) = SOME (h1,h2)`,
  CHEAT_TAC);;

(* [local] *)
let heap_segment_length = prove
 (`heap_segment (heap_length h1,heap_length h1 + heap_length h2)
  (APPEND (APPEND h1 h2) h3) = SOME (h1,h2,h3)`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_simulation = prove
 (`!ptr ptr' state state' ptr1' state1'.
     (gen_gc_partial_gc_move conf state ptr = (ptr',state')) /\
     (!ptr' u. (ptr = gc_shared_Pointer ptr' u) ==> ptr' <
       heap_length (gc_state_heap state)) /\
     (heap_length (gc_state_heap state) = gen_gc_partial_conf_limit
       conf) /\
     sim_inv conf heap0 state /\
     (gen_gc_gc_move
        (to_gen_conf conf)
        (to_gen_state conf state)
        (to_gen_heap_address conf ptr) = (ptr1',state1')) /\
          gc_state_ok state1' ==>
     sim_inv conf heap0 state' /\
     (
      (ptr1',state1') = (to_gen_heap_address conf ptr',to_gen_state
        conf state')) /\
     all_old_ptrs conf [ptr'] SUBSET all_old_ptrs conf [ptr]`,
  CHEAT_TAC);;

let gc_forward_ptr_heap_length = prove
 (`!n h m a ok h' ok'. (gc_forward_ptr n h m a ok = (h',ok')) ==>
  (heap_length h = heap_length h')`,
  CHEAT_TAC);;

let gc_move_heap_length = prove
 (`(gen_gc_partial_gc_move conf state h = (x,state')) ==> (heap_length
  (gc_state_heap state) = heap_length (gc_state_heap state'))`,
  CHEAT_TAC);;

(* gc_move_list_heap_length *)
let gen_gc_partial_gc_move_list_heap_length = prove
 (`!h x state state'. (gen_gc_partial_gc_move_list conf state h =
  (x,state')) ==> (heap_length (gc_state_heap state) = heap_length
  (gc_state_heap state'))`,
  CHEAT_TAC);;

let gc_move_ref_list_heap_length = prove
 (`!h x state state'.
   (gc_move_ref_list conf state h = (x,state')) ==> (heap_length
     (gc_state_heap state) = heap_length (gc_state_heap state'))`,
  CHEAT_TAC);;

let gc_move_ok' = prove
 (`(gen_gc_partial_gc_move conf state x = (x',state')) /\ gc_state_ok
  state' ==> gc_state_ok state`,
  CHEAT_TAC);;

(* gc_move_ok *)
let gen_gc_partial_gc_move_ok = prove
 (`(gen_gc_partial_gc_move conf state x = (x',state')) /\ gc_state_ok
  state' /\ (!ptr' u. (x = gc_shared_Pointer ptr' u) ==> ptr' <
  heap_length (gc_state_heap state)) ==> gc_state_ok state`,
  CHEAT_TAC);;

let gc_move_list_ok' = prove
 (`!xs xs' state state'.
    (gen_gc_partial_gc_move_list conf state xs = (xs',state')) /\
      gc_state_ok state' ==> gc_state_ok
      state`,
  (LIST_INDUCT_TAC THEN REWRITE_TAC[gen_gc_partial_gc_move_list_def;
    PAIR_EQ] THENL
    [REPEAT STRIP_TAC THEN (REPEAT VAR_EQ_TAC) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REPEAT GEN_TAC THEN PAIRARG_TAC THEN PAIRARG_TAC THEN
     REWRITE_TAC[PAIR_EQ] THEN
   STRIP_TAC THEN (REPEAT VAR_EQ_TAC) THEN MATCH_MP_TAC gc_move_ok'
     THEN
   MAP_EVERY EXISTS_TAC [`conf:B gen_gc_partial_conf`; `h:A
     heap_address`; `x':A heap_address`;
                         `state'':(A,B)gc_state`] THEN
   ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(fun mv -> MATCH_MP_TAC
     (MATCH_MP
     (REWRITE_RULE[IMP_CONJ] ih) mv))) THEN
   ASM_REWRITE_TAC[]));;

(* gc_move_list_ok *)
let gen_gc_partial_gc_move_list_ok = prove
 (`!xs xs' state state'.
    (gen_gc_partial_gc_move_list conf state xs = (xs',state')) /\
      gc_state_ok state' /\ (!ptr' u. MEM (gc_shared_Pointer ptr' u)
        xs ==> ptr' < heap_length (gc_state_heap state)) ==> gc_state_ok
      state`,
  CHEAT_TAC);;

let gc_move_ref_list_ok' = prove
 (`!xs xs' state state'.
    (gc_move_ref_list conf state xs = (xs',state')) /\ gc_state_ok
      state' ==> gc_state_ok
      state`,
  CHEAT_TAC);;

let gc_move_data_ok' = prove
 (`!conf state state'.
     (gen_gc_partial_gc_move_data conf state = state') /\ gc_state_ok
       state' ==> gc_state_ok
       state`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_list_simulation = prove
 (`!ptr ptr' state state' ptr1' state1'.
     (gen_gc_partial_gc_move_list conf state ptr = (ptr',state')) /\
     sim_inv conf heap0 state /\
     (!ptr' u. MEM (gc_shared_Pointer ptr' u) ptr ==> ptr' <
       heap_length (gc_state_heap state)) /\
     (heap_length (gc_state_heap state) = gen_gc_partial_conf_limit
       conf) /\
     (gen_gc_gc_move_list
        (to_gen_conf conf)
        (to_gen_state conf state)
        (MAP (to_gen_heap_address conf) ptr) = (ptr1',state1')) /\
          gc_state_ok state1' ==>
     sim_inv conf heap0 state' /\
     (
      (ptr1',state1') = (MAP (to_gen_heap_address conf)
        ptr',to_gen_state conf state')) /\
     all_old_ptrs conf ptr' SUBSET all_old_ptrs conf ptr`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_list_APPEND = prove
 (`!conf state0 xs ys roots' state'.
     (gen_gc_gc_move_list conf state0 (APPEND xs ys) =
       (roots',state')) ==>
     (?roots1 roots2 state1.
       (gen_gc_gc_move_list conf state0 xs = (roots1,state1)) /\
       (gen_gc_gc_move_list conf state1 ys = (roots2,state')) /\
       (roots' = APPEND roots1 roots2))`,
  CHEAT_TAC);;

(* [simp] *)
let heap_restrict_NIL = prove
 (`heap_restrict gen_start refs_start [] = []`,
  CHEAT_TAC);;

(* [simp] *)
let to_gen_heap_NIL = prove
 (`to_gen_heap conf [] = []`,
  (REWRITE_TAC[to_gen_heap_def; heap_restrict_NIL;
    to_gen_heap_list_def; MAP]));;

(* [simp] *)
let to_gen_heap_list_NIL = prove
 (`to_gen_heap_list conf [] = []`,
  (REWRITE_TAC[to_gen_heap_list_def; MAP]));;

(* [local] *)
let gc_move_data_r1 = prove
 (`!refs state conf. gc_state_r1
     (gen_gc_partial_gc_move_data conf (gc_state_r1_fupd (K refs)
       state)) = refs`,
  (MESON_TAC[gc_move_data_IMP]));;

(* [local] *)
let gc_move_ref_list_simulation = prove
 (`!conf state refs0 heap0 state1 state1' refs1 refs1'.
   (
     gc_move_ref_list conf (state:('b,'a)gc_state)
       (refs0:(('b,'a)heap_element) list) = (refs1,state1)) /\
   (
     gen_gc_partial_gc_move_list (to_gen_conf conf)
                 (to_gen_state conf state)
                 (refs_to_roots conf refs0) = (refs1',state1')) /\
                   gc_state_ok state1' /\
   sim_inv conf heap0 state /\
   (!ptrs l d ptr' u. MEM (gc_shared_Pointer ptr' u) ptrs /\ MEM
     (DataElement ptrs l d) refs0 ==> ptr' < heap_length (gc_state_heap
     state)) /\
   (heap_length (gc_state_heap state) = gen_gc_partial_conf_limit
     conf) /\
   ALL isDataElement refs0 ==>
   sim_inv conf heap0 state1 /\
   (refs1' = refs_to_roots conf refs1) /\
   (state1' = to_gen_state conf state1) /\
   has_old_ptr conf refs1 SUBSET has_old_ptr conf refs0`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_list_r1 = prove
 (`!s0 xs ys s1. (gen_gc_partial_gc_move_list conf s0 xs = (ys,s1))
  ==> (gc_state_r1 s1 = gc_state_r1 s0)`,
  (MESON_TAC[gen_gc_partial_gc_move_list_IMP]));;

(* gc_move_data_r1[local] *)
let gen_gc_partial_gc_move_data_r1 = prove
 (`(gen_gc_partial_gc_move_data conf (gc_state_r1_fupd (K refs') state')
  = state1) ==>
   (gc_state_r1 state1 = refs')`,
  CHEAT_TAC);;

(* [local] *)
let el_length_to_gen_heap_element = prove
 (`!h. el_length (to_gen_heap_element conf h) = el_length h`,
  CHEAT_TAC);;

(* [local] *)
let to_gen_heap_address_11 = prove
 (`!x y.
     (to_gen_heap_address conf x = to_gen_heap_address conf y) ==>
       (x = y)`,
  CHEAT_TAC);;

(* [local] *)
let MAP_to_gen_heap_address_11 = prove
 (`!x y.
     (MAP (to_gen_heap_address conf) x = MAP (to_gen_heap_address
       conf) y) <=> (x = y)`,
  (LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
   REWRITE_TAC[MAP; NOT_CONS_NIL; GSYM NOT_CONS_NIL; CONS_11] THEN
   ASM_MESON_TAC[to_gen_heap_address_11]));;

(* [local] *)
let gc_forward_ptr_data_pres = prove
 (`!x a ptr d ok x' ok'.
    (gc_forward_ptr a x ptr d ok = (x',ok')) ==> (
         MEM (DataElement xs l dd) x = (MEM (DataElement xs l dd)
           x' \/ (heap_lookup a x = SOME (DataElement xs l dd))))`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_data_pres = prove
 (`(gen_gc_partial_gc_move conf state x = (x1,state1)) ==> (
         MEM (DataElement xs l dd) (APPEND (gc_state_heap state1)
           (gc_state_h2 state1)) = MEM (DataElement xs l dd) (APPEND
           (gc_state_heap state) (gc_state_h2 state)))`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_list_data_pres = prove
 (`!x conf state x1 state1 xs l dd.
    (gen_gc_partial_gc_move_list conf state x = (x1,state1)) ==> (
         MEM (DataElement xs l dd) (APPEND (gc_state_heap state1)
           (gc_state_h2 state1)) = MEM (DataElement xs l dd) (APPEND
           (gc_state_heap state) (gc_state_h2 state)))`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_ref_list_data_pres = prove
 (`!x conf state x1 state1 xs l dd.
    (gc_move_ref_list conf state x = (x1,state1)) ==> (
         MEM (DataElement xs l dd) (APPEND (gc_state_heap state1)
           (gc_state_h2 state1)) = MEM (DataElement xs l dd) (APPEND
           (gc_state_heap state) (gc_state_h2 state)))`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_data_simulation = prove
 (`!conf state heap0 state' ptr1' state1'.
     (gen_gc_partial_gc_move_data conf state = state') /\
     sim_inv conf heap0 state /\
     (!ptrs l d ptr' u. MEM (gc_shared_Pointer ptr' u) ptrs /\ MEM
       (DataElement ptrs l d) (APPEND (gc_state_h2 state) (gc_state_heap
       state)) ==> ptr' < heap_length (gc_state_heap state)) /\
     (heap_length (gc_state_heap state) = gen_gc_partial_conf_limit
       conf) /\
     (gen_gc_gc_move_data
        (to_gen_conf conf)
        (to_gen_state conf state) = state1') /\ gc_state_ok state1'
          ==>
     sim_inv conf heap0 state' /\
     (state1' = to_gen_state conf state')`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_with_refs = prove
 (`!l. (gen_gc_partial_gc_move conf (gc_state_r1_fupd (K refs) state) l
  =
        (let (xs,s) = gen_gc_partial_gc_move conf state l in
          (xs,gc_state_r1_fupd (K refs) s)))`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_with_refs' = prove
 (`!l. (gen_gc_partial_gc_move conf (gc_state_r1_fupd (K refs)
  (gc_state_r2_fupd (K []) state)) l =
        (let (xs,s) = gen_gc_partial_gc_move conf state l in
          (xs,gc_state_r1_fupd (K refs) (gc_state_r2_fupd (K []) s))))`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_list_with_refs = prove
 (`!l state.
     (gen_gc_partial_gc_move_list conf (gc_state_r1_fupd (K refs)
       state) l =
     (let (xs,s) = gen_gc_partial_gc_move_list conf state l in
       (xs,gc_state_r1_fupd (K refs) s)))`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_list_with_refs' = prove
 (`!l state.
     (gen_gc_partial_gc_move_list conf (gc_state_r1_fupd (K refs)
       (gc_state_r2_fupd (K []) state)) l =
      (let (xs,s) = gen_gc_partial_gc_move_list conf state l in
        (xs,gc_state_r1_fupd (K refs) (gc_state_r2_fupd (K []) s))))`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_data_with_refs = prove
 (`!conf state refs.
     (gen_gc_partial_gc_move_data conf (gc_state_r1_fupd (K refs)
       state) = gc_state_r1_fupd (K refs)
     (gen_gc_partial_gc_move_data conf state))`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_data_with_refs' = prove
 (`!conf state refs.
    (gen_gc_partial_gc_move_data conf (gc_state_r1_fupd (K refs)
      (gc_state_r2_fupd (K []) state)) = gc_state_r1_fupd (K refs)
      (gc_state_r2_fupd (K [])
    (gen_gc_partial_gc_move_data conf state)))`,
  CHEAT_TAC);;

(* gc_move_data_h2[local] *)
let gen_gc_partial_gc_move_data_h2 = prove
 (`!conf state. gc_state_ok
     (gen_gc_partial_gc_move_data conf state) ==>
     (gc_state_h2 (gen_gc_partial_gc_move_data conf state) = [])`,
  CHEAT_TAC);;

(* gc_move_ref_list_heap_length[local] *)
let gen_gc_partial_gc_move_ref_list_heap_length = prove
 (`!h x state state'. (gc_move_ref_list conf state h = (x,state')) ==>
  (heap_length (gc_state_heap state) = heap_length (gc_state_heap
  state'))`,
  CHEAT_TAC);;

(* gc_move_data_r1[local] *)
let gen_gc_partial_gc_move_data_r1 = prove
 (`gc_state_r1
     (gen_gc_partial_gc_move_data conf state) = gc_state_r1 state`,
  CHEAT_TAC);;

(* [local] *)
let partial_gc_simulation = prove
 (`!conf roots heap0 roots1 state1 heap0_old heap0_current heap0_refs
    new_roots new_state.
     (partial_gc conf (roots,heap0) = (roots1,state1)) /\
     heap_gen_ok heap0 conf /\ gen_gc_partial_conf_gen_start
     conf <= gen_gc_partial_conf_refs_start conf /\
       gen_gc_partial_conf_refs_start conf <= gen_gc_partial_conf_limit
       conf /\
     (
       heap_segment (gen_gc_partial_conf_gen_start
         conf,gen_gc_partial_conf_refs_start conf) heap0 = SOME
         (heap0_old,heap0_current,heap0_refs)) /\
     ALL (\e. ~(heap_element_is_ref conf e)) (APPEND heap0_old
       heap0_current) /\
     ALL isDataElement heap0_refs /\
     roots_ok roots heap0 /\
     (gen_gc (to_gen_conf conf)
       (APPEND (to_gen_roots conf roots) (refs_to_roots conf
         heap0_refs),
        to_gen_heap_list conf heap0_current) = (new_roots,new_state))
          /\
     heap_ok heap0 (gen_gc_partial_conf_limit conf) /\ gc_state_ok
       new_state ==>
     (new_roots = APPEND (to_gen_roots conf roots1) (refs_to_roots
       conf (gc_state_r1 state1))) /\
     (new_state = to_gen_state conf state1) /\
     sim_inv conf heap0 state1 /\ (gc_state_h2 state1 = []) /\
       gc_state_ok state1`,
  CHEAT_TAC);;

let f_old_ptrs_def = new_definition
  `f_old_ptrs conf heap =
     {a |
          isSomeDataElement (heap_lookup a heap) /\ (a <
            gen_gc_partial_conf_gen_start conf \/
            gen_gc_partial_conf_refs_start conf <= a)}`;;

(* [simp] *)
let f_old_ptrs_finite = prove
 (`!heap conf.
    FINITE (f_old_ptrs conf heap)`,
  (REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
   EXISTS_TAC `{a:num | a < heap_length
     (heap:((A,B)heap_element)list)}` THEN
   REWRITE_TAC[FINITE_NUMSEG_LT; f_old_ptrs_def; SUBSET; IN_ELIM_THM;
               isSomeDataElement_def] THEN
   MESON_TAC[heap_lookup_LESS]));;

(* HOL4 gen_gc_partialScript.sml:1315-1316: a theorem that HOL4
   states as the value of an ML expression: f_old_ptrs_finite_open *)

let new_f_def = new_definition
  `new_f f conf heap =
     FUNION (FUN_FMAP I (f_old_ptrs conf heap))
            (FUN_FMAP (\a. gen_gc_partial_conf_gen_start conf +
              FAPPLY f (a - gen_gc_partial_conf_gen_start conf))
                      (IMAGE ((+) (gen_gc_partial_conf_gen_start
                        conf)) (FDOM f)))`;;

(* [local] *)
let APPEND_LENGTH_IMP = prove
 (`!a c b d.
   ((APPEND a b) = (APPEND c d)) /\ (LENGTH a = LENGTH c) ==>
   (a = c) /\ (b = d)`,
  (LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
   REWRITE_TAC[APPEND; LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ;
     CONS_11] THEN
   ASM_MESON_TAC[]));;

(* [local] *)
let roots_ok_APPEND = prove
 (`!left right heap.
   roots_ok (APPEND left right) heap ==>
   roots_ok left heap /\
   roots_ok right heap`,
  (REWRITE_TAC[roots_ok_def; MEM_APPEND] THEN MESON_TAC[]));;

(* [local] *)
let roots_ok_CONS = prove
 (`!h t.
   roots_ok (CONS h t) heap ==>
   roots_ok t heap`,
  (REWRITE_TAC[roots_ok_def; MEM] THEN MESON_TAC[]));;

(* [simp] *)
let isSomeDataElement_to_gen_heap_list = prove
 (`!n heap.
    isSomeDataElement (heap_lookup n (to_gen_heap_list conf heap))
      = isSomeDataElement (heap_lookup n heap)`,
  CHEAT_TAC);;

(* HOL4 gen_gc_partialScript.sml:1371-1372: a theorem that HOL4
   states as the value of an ML expression:
   isSomeDataElement_to_gen_heap_element *)

(* [local] *)
let MEM_refs_to_roots_IMP_MEM = prove
 (`!heap_refs.
   MEM (gc_shared_Pointer ptr u) (refs_to_roots conf heap_refs) ==>
   (?xs l d ptr' u'.
   MEM (DataElement xs l d) heap_refs /\
   MEM (gc_shared_Pointer ptr' u') xs /\
   (ptr = ptr' - gen_gc_partial_conf_gen_start conf) /\
   (u = Real u') /\
   (gen_gc_partial_conf_gen_start conf <= ptr') /\
   (ptr' < gen_gc_partial_conf_refs_start conf))`,
  CHEAT_TAC);;

(* [local] *)
let MEM_to_gen_roots_IMP_MEM = prove
 (`!roots.
   MEM (gc_shared_Pointer ptr u) (to_gen_roots conf roots) ==>
   (?ptr' u'.
   MEM (gc_shared_Pointer ptr' u') roots /\
   (ptr = ptr' - gen_gc_partial_conf_gen_start conf) /\
   (u = Real u') /\
   (gen_gc_partial_conf_gen_start conf <= ptr') /\
   (ptr' < gen_gc_partial_conf_refs_start conf))`,
  CHEAT_TAC);;

(* [local] *)
let roots_ok_simulation = prove
 (`!roots heap heap_old heap_current heap_refs (conf:'b
  gen_gc_partial_conf).
   roots_ok roots (heap:(('a,'b)heap_element) list) /\
   heap_ok heap (gen_gc_partial_conf_limit conf) /\
   (heap_segment (gen_gc_partial_conf_gen_start
     conf,gen_gc_partial_conf_refs_start conf) heap = SOME
     (heap_old,heap_current,heap_refs)) /\
   (gen_gc_partial_conf_gen_start conf <=
     gen_gc_partial_conf_refs_start conf) ==>
   roots_ok
     (APPEND (to_gen_roots conf roots) (refs_to_roots conf
       heap_refs))
     (MAP (to_gen_heap_element conf) heap_current)`,
  CHEAT_TAC);;

(* HOL4 gen_gc_partialScript.sml:1459-1460: a theorem that HOL4
   states as the value of an ML expression:
   heap_length_to_gen_heap_element *)

(* [local] *)
let MEM_to_gen_heap_IMP_MEM = prove
 (`!heap_current xs l d ptr u.
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
   (gen_gc_partial_conf_gen_start conf <= ptr'))`,
  CHEAT_TAC);;

(* [local] *)
let heap_ok_simulation = prove
 (`!heap heap_old heap_current heap_refs (conf:'b gen_gc_partial_conf).
   heap_ok (heap:(('a,'b)heap_element) list)
     (gen_gc_partial_conf_limit conf) /\
   (heap_segment (gen_gc_partial_conf_gen_start
     conf,gen_gc_partial_conf_refs_start conf) heap = SOME
     (heap_old,heap_current,heap_refs)) /\
   (gen_gc_partial_conf_gen_start conf <=
     gen_gc_partial_conf_refs_start conf) /\
   (gen_gc_partial_conf_refs_start conf <= gen_gc_partial_conf_limit
     conf) ==>
   heap_ok
     (MAP (to_gen_heap_element conf) heap_current)
       (gen_gc_partial_conf_limit
     (to_gen_conf conf))`,
  CHEAT_TAC);;

(* [local] *)
let new_f_FDOM = prove
 (`(!i. i IN FDOM f ==> isSomeDataElement (heap_lookup (i +
  gen_gc_partial_conf_gen_start conf) heap)) ==>
   ((x IN FDOM (new_f f conf heap)) =
   (if x < gen_gc_partial_conf_gen_start conf \/
     gen_gc_partial_conf_refs_start conf <= x then
   isSomeDataElement (heap_lookup x heap) else
   x IN (IMAGE ((+) (gen_gc_partial_conf_gen_start conf)) (FDOM
     f))))`,
  CHEAT_TAC);;

(* [local] *)
let new_f_FAPPLY = prove
 (`(x IN FDOM (new_f f conf heap)) /\
   (!i. i IN FDOM f ==> isSomeDataElement (heap_lookup (i +
     gen_gc_partial_conf_gen_start conf) heap)) ==>
   (FAPPLY (new_f f conf heap) x =
   (if x < gen_gc_partial_conf_gen_start conf \/
     gen_gc_partial_conf_refs_start conf <= x then
   x else gen_gc_partial_conf_gen_start
   conf + FAPPLY f (x - gen_gc_partial_conf_gen_start conf)))`,
  CHEAT_TAC);;

(* [simp] *)
let isSomeDataElement_heap_lookup_heap_expand = prove
 (`~(isSomeDataElement (heap_lookup x (heap_expand n)))`,
  CHEAT_TAC);;

(* HOL4 gen_gc_partialScript.sml:1581-1582: ML code, not ported *)

(* [local] *)
let heap_lookup_old_IMP = prove
 (`!i ys.
   (partial_gc conf (roots,heap) = (roots1,state1)) /\
   gen_inv conf heap /\
   (heap_lookup i heap = SOME (DataElement xs l d)) /\
   (i < gen_gc_partial_conf_gen_start conf) ==>
   (heap_lookup i (APPEND (gc_state_old state1) ys) = SOME
     (DataElement xs l d))`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[gen_inv_def] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pg") (CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
       (X_CHOOSE_THEN `ho:((A,B)heap_element)list` (X_CHOOSE_THEN
         `hc:((A,B)heap_element)list`
         (X_CHOOSE_THEN `hr:((A,B)heap_element)list`
           (CONJUNCTS_THEN2 (LABEL_TAC "seg") (K ALL_TAC)))))))
     (CONJUNCTS_THEN2 (LABEL_TAC "lk") (LABEL_TAC "lt")))) THEN
   USE_THEN "pg" (fun pg -> USE_THEN "seg" (fun sg ->
     REWRITE_TAC[CONJUNCT1 (MATCH_MP gen_gc_partial_partial_gc_IMP
       (CONJ pg sg))])) THEN
   USE_THEN "seg" (fun th -> let cs = CONJUNCTS (MATCH_MP
     heap_segment_IMP th) in
     LABEL_TAC "happ" (el 0 cs) THEN LABEL_TAC "hlo" (el 1 cs)) THEN
   SUBGOAL_THEN `i < heap_length (ho:((A,B)heap_element)list)`
     ASSUME_TAC THENL
    [USE_THEN "hlo" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "lt"
      ACCEPT_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[LESS_IMP_heap_lookup] THEN
   USE_THEN "lk" MP_TAC THEN
   USE_THEN "happ" (fun th -> REWRITE_TAC[GSYM th; GSYM
     APPEND_ASSOC]) THEN
   ASM_SIMP_TAC[LESS_IMP_heap_lookup]));;

(* [local] *)
let heap_lookup_old_IMP_ALT = prove
 (`!ys.
   (partial_gc conf (roots,heap) = (roots1,state1)) /\
   gen_inv conf heap /\
   isSomeDataElement (heap_lookup x heap) /\
   (x < gen_gc_partial_conf_gen_start conf) ==>
   isSomeDataElement (heap_lookup x (APPEND (gc_state_old state1)
     ys))`,
  (REWRITE_TAC[isSomeDataElement_def] THEN
    MESON_TAC[heap_lookup_old_IMP]));;

(* [local] *)
let heap_lookup_refs_IMP = prove
 (`!x.
   (partial_gc conf (roots,heap) = (roots1,state1)) /\
   gen_inv conf heap /\
   (heap_lookup x heap = SOME (DataElement xs l d)) /\
   (heap_length (APPEND (APPEND (gc_state_old state1) (gc_state_h1
     state1)) (heap_expand (gc_state_n state1))) =
     gen_gc_partial_conf_refs_start conf) /\
   (gen_gc_partial_conf_refs_start conf <= x) ==>
   (?xs1.
   (heap_lookup x (APPEND (APPEND (APPEND (gc_state_old state1)
     (gc_state_h1 state1)) (heap_expand (gc_state_n state1)))
     (gc_state_r1 state1)) =
     SOME (DataElement xs1 l d)))`,
  CHEAT_TAC);;

(* [local] *)
let heap_lookup_refs_IMP_ALT = prove
 (`(partial_gc conf (roots,heap) = (roots1,state1)) /\
   gen_inv conf heap /\
   isSomeDataElement (heap_lookup x heap) /\
   (heap_length (APPEND (APPEND (gc_state_old state1) (gc_state_h1
     state1)) (heap_expand (gc_state_n state1))) =
     gen_gc_partial_conf_refs_start conf) /\
   (gen_gc_partial_conf_refs_start conf <= x) ==>
   isSomeDataElement (heap_lookup x (APPEND (APPEND (APPEND
     (gc_state_old state1) (gc_state_h1 state1)) (heap_expand
     (gc_state_n state1))) (gc_state_r1 state1)))`,
  (REWRITE_TAC[isSomeDataElement_def] THEN
    MESON_TAC[heap_lookup_refs_IMP]));;

(* [local] *)
let ADDR_MAP_ID = prove
 (`(!x u. MEM (gc_shared_Pointer x u) xs ==> (x = f x)) ==> (xs =
  ADDR_MAP f xs)`,
  CHEAT_TAC);;

(* [local] *)
let MEM_heap_old = prove
 (`!n m i x.
   (heap_segment (n,m) heap = SOME (heap_old,heap_current,heap_refs))
     /\
   (n <= m) /\
   i < n /\
   (heap_lookup i heap = SOME x) ==>
   MEM x heap_old`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP heap_segment_IMP) THEN STRIP_TAC
     THEN
   MATCH_MP_TAC heap_lookup_IMP_MEM THEN EXISTS_TAC `i:num` THEN
   UNDISCH_TAC `heap_lookup i heap = SOME (x:(A,B)heap_element)` THEN
   EXPAND_TAC "heap" THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
   SUBGOAL_THEN `i < heap_length (heap_old:((A,B)heap_element)list)`
     ASSUME_TAC THENL
    [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_SIMP_TAC[LESS_IMP_heap_lookup]));;

(* [local] *)
let FILTER_isForward_to_gen = prove
 (`!xs.
   (FILTER isForwardPointer (to_gen_heap_list conf xs) = []) ==>
   (FILTER isForwardPointer xs = [])`,
  CHEAT_TAC);;

(* [local] *)
let isSomeData_to_gen_heap_IMP = prove
 (`!xs ptr conf ys l d.
   (heap_lookup ptr (to_gen_heap_list conf xs) = SOME (DataElement ys
     l d)) ==>
   isSomeDataElement (heap_lookup ptr xs)`,
  (MESON_TAC[isSomeDataElement_to_gen_heap_list;
    isSomeDataElement_def]));;

(* [local] *)
let refs_to_roots_APPEND = prove
 (`!xs ys.
   refs_to_roots conf (APPEND xs ys) = APPEND (refs_to_roots conf
     xs) (refs_to_roots conf ys)`,
  (LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; refs_to_roots_def] THEN
   STRUCT_CASES_TAC (ISPEC `h:(A,B)heap_element` (cases
     "heap_element")) THEN
   ASM_REWRITE_TAC[APPEND; refs_to_roots_def; APPEND_ASSOC]));;

(* [local] *)
let gc_move_refs_isForwardPointer = prove
 (`!refs refs1 state1 state.
   (gc_move_ref_list conf state refs = (refs1,state1)) /\
   (FILTER isForwardPointer refs = []) ==>
   (FILTER isForwardPointer refs1 = [])`,
  CHEAT_TAC);;

(* el_length_to_gen_heap_element[simp] *)
let gen_gc_partial_el_length_to_gen_heap_element = prove
 (`el_length (to_gen_heap_element conf h) = el_length h`,
  CHEAT_TAC);;

(* [local] *)
let to_gen_heap_element_isSomeData = prove
 (`!xs n.
   isSomeDataElement (heap_lookup n (MAP (to_gen_heap_element
     (conf:'b gen_gc_partial_conf)) (xs:(('a,'b)heap_element) list)))
     ==>
   isSomeDataElement (heap_lookup n xs)`,
  CHEAT_TAC);;

(* [local] *)
let heap_lookup_GT_FALSE = prove
 (`!xs n.
   ~(n < heap_length xs) ==>
   ~(isSomeDataElement (heap_lookup n xs))`,
  (MESON_TAC[isSomeDataElement_def; heap_lookup_LESS]));;

(* [local] *)
let heap_lookup_to_gen_heap_element = prove
 (`!heap_current i.
     isSomeDataElement (heap_lookup i (MAP (to_gen_heap_element conf)
       heap_current)) =
     isSomeDataElement (heap_lookup i heap_current)`,
  CHEAT_TAC);;

(* [local] *)
let partial_gc_heap_length_lemma = prove
 (`!roots'.
   (partial_gc conf (roots,heap) = (roots1,state1)) /\
   (gen_gc (to_gen_conf conf) (gen_roots,gen_heap) =
     (roots',to_gen_state conf state1)) /\
   (heap_segment (gen_gc_partial_conf_gen_start
     conf,gen_gc_partial_conf_refs_start conf) heap = SOME
     (heap_old,heap_current,heap_refs)) /\
   (gen_gc_partial_conf_gen_start conf <=
     gen_gc_partial_conf_refs_start conf) /\
   (gen_gc_partial_conf_refs_start conf <= gen_gc_partial_conf_limit
     conf) /\
   roots_ok gen_roots gen_heap /\
   heap_ok gen_heap (gen_gc_partial_conf_limit (to_gen_conf conf))
     ==>
   (heap_length (APPEND (APPEND (gc_state_old state1) (gc_state_h1
     state1)) (heap_expand (gc_state_n state1))) =
     gen_gc_partial_conf_refs_start conf)`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_ref_list_isSomeDataElement = prove
 (`!refs ptr state state1 refs1.
   (gc_move_ref_list conf state refs = (refs1,state1)) /\
   isSomeDataElement (heap_lookup ptr refs) ==>
   isSomeDataElement (heap_lookup ptr refs1)`,
  CHEAT_TAC);;

(* [local] *)
let ptr_Real_lemma = prove
 (`!ys ptr.
   MEM (gc_shared_Pointer ptr u) ys /\
   (gen_gc_partial_conf_gen_start conf <= ptr) /\
   (ptr < gen_gc_partial_conf_refs_start conf) ==>
   MEM (gc_shared_Pointer (ptr - gen_gc_partial_conf_gen_start
     conf) (Real u)) (MAP (to_gen_heap_address conf) ys)`,
  (REWRITE_TAC[MEM_MAP] THEN REPEAT STRIP_TAC THEN
   EXISTS_TAC `gc_shared_Pointer ptr (u:A)` THEN
     ASM_REWRITE_TAC[to_gen_heap_address_def] THEN
   ASM_SIMP_TAC[ARITH_RULE `a <= p ==> ~(p < a)`; ARITH_RULE `p < b
     ==> ~(b <= p)`]));;

(* [local] *)
let partial_gc_refs_isSomeDataElement_isSomeDataElement = prove
 (`!ptr heap state1 heap_current heap_refs.
   (
    partial_gc conf (roots,heap) = (roots1,state1)) /\
   (heap_segment (gen_gc_partial_conf_gen_start
     conf,gen_gc_partial_conf_refs_start conf) heap = SOME (gc_state_old
     state1,heap_current,heap_refs)) /\
   isSomeDataElement (heap_lookup ptr heap_refs) ==>
   isSomeDataElement (heap_lookup ptr (gc_state_r1 state1))`,
  (REPEAT STRIP_TAC THEN
   FIRST_ASSUM(fun pg -> FIRST_ASSUM(fun sg ->
     MATCH_MP_TAC (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (MATCH_MP
       partial_gc_IMP (CONJ pg sg))))))) THEN
   ASM_REWRITE_TAC[]));;

(* [local] *)
let isSomeData_to_gen_heap_IMP_isSomeData = prove
 (`!heap ptr.
   isSomeDataElement (heap_lookup ptr (APPEND (to_gen_heap_list conf
     heap) (heap_expand (gc_state_n state1)))) ==>
   isSomeDataElement (heap_lookup ptr (APPEND heap (heap_expand
     (gc_state_n state1))))`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[heap_lookup_APPEND;
    heap_length_to_gen_heap_list] THEN
   COND_CASES_TAC THEN
   REWRITE_TAC[isSomeDataElement_to_gen_heap_list;
     isSomeDataElement_heap_lookup_heap_expand]));;

(* [local] *)
let refs_root_IMP_isSomeData = prove
 (`!(state1:('a,'b)gc_state) (conf:'b gen_gc_partial_conf) refs.
   MEM (DataElement xs l d) refs /\
   MEM (gc_shared_Pointer ptr u) xs /\
   roots_ok (refs_to_roots conf refs)
     (APPEND (to_gen_heap_list conf (gc_state_h1 state1))
       (heap_expand (gc_state_n state1))) /\
   (ptr < gen_gc_partial_conf_refs_start conf) /\
   ~(ptr < gen_gc_partial_conf_gen_start conf) ==>
   isSomeDataElement (heap_lookup (ptr -
     gen_gc_partial_conf_gen_start conf) (APPEND (gc_state_h1 state1)
     (heap_expand (gc_state_n state1))))`,
  CHEAT_TAC);;

(* [local] *)
let ADDR_MAP_APPEND_LENGTH_IMP = prove
 (`!(roots:('a heap_address) list) (heap_refs:(('a,'b)heap_element)
  list) (f:(num,num)fmap) roots1 (r1:(('a,'b)heap_element) list)
  (conf:'b gen_gc_partial_conf).
   (ADDR_MAP (FAPPLY f) (APPEND (to_gen_roots conf roots)
     (refs_to_roots conf heap_refs)) = APPEND (to_gen_roots conf roots1)
     (refs_to_roots conf r1)) /\
   (LENGTH roots = LENGTH roots1) ==>
   (ADDR_MAP (FAPPLY f) (to_gen_roots conf roots) = to_gen_roots conf
     roots1) /\
   (ADDR_MAP (FAPPLY f) (refs_to_roots conf heap_refs) =
     refs_to_roots conf r1)`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[ADDR_MAP_APPEND] THEN STRIP_TAC
    THEN
   MATCH_MP_TAC APPEND_LENGTH_IMP THEN
   CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[GSYM ADDR_MAP_LENGTH; to_gen_roots_def;
     LENGTH_MAP]));;

(* [local] *)
let heap_lookup_by_f_isSomeData_lemma = prove
 (`!h1 x xs (state1:('a,'b)gc_state) (heap:(('a,'b)heap_element) list)
  conf.
   (heap_lookup x
     (APPEND (MAP (to_gen_heap_element conf) h1) (heap_expand
       (gc_state_n state1))) =
     SOME (DataElement (ADDR_MAP (FAPPLY f) (MAP (to_gen_heap_address
       conf) xs)) l d)) /\
   (!u ptr.
      MEM (gc_shared_Pointer ptr u) xs ==>
      isSomeDataElement (heap_lookup ptr heap)) /\
   (!ptr u.
      MEM (gc_shared_Pointer ptr u) (MAP (to_gen_heap_address conf)
        xs) ==>
      ptr IN FDOM f) ==>
   (heap_lookup x (APPEND (APPEND h1 (heap_expand (gc_state_n
     state1))) (gc_state_r1 state1)) =
     SOME (DataElement (ADDR_MAP (FAPPLY (new_f f conf heap)) xs) l
       d))`,
  CHEAT_TAC);;

let similar_ptr_def = new_definition
  `similar_ptr conf x1 x2 =
        match (x1,x2) with
          (gc_shared_Pointer p1 d1,gc_shared_Pointer p2 d2) -> (d2 =
            d1)
        | (x1,x2) -> (x1 = x2)`;;

let similar_data_def = new_definition
  `similar_data conf x y =
        match (x,y) with
          (DataElement xs1 l1 d1,DataElement xs2 l2 d2) ->
       (l2 = l1) /\ (d2 = d1) /\ ALL2 (similar_ptr conf) xs1 xs2
        | (x,y) -> (x = y)`;;

(* [local] *)
let LENGTH_ADDR_MAP = prove
 (`!xs. LENGTH (ADDR_MAP f xs) = LENGTH xs`,
  (REWRITE_TAC[GSYM ADDR_MAP_LENGTH]));;

(* [local] *)
let heap_lookup_similar_data_IMP = prove
 (`!h1 h2 n.
     ALL2 (similar_data conf) h1 h2 /\
     (heap_lookup n h1 = SOME (DataElement xs1 l d)) /\
     (ADDR_MAP (FAPPLY f) (refs_to_roots conf h1) = refs_to_roots
       conf h2) ==>
     (?xs2. (heap_lookup n h2 = SOME (DataElement xs2 l d)) /\
           (ADDR_MAP (FAPPLY f) (MAP (to_gen_heap_address conf) xs1)
             =
              MAP (to_gen_heap_address conf) xs2))`,
  CHEAT_TAC);;

(* [local] *)
let new_f_old_parts = prove
 (`n IN FDOM (new_f f conf heap) /\
   (!i. i IN FDOM f ==>
        isSomeDataElement (heap_lookup (i +
          gen_gc_partial_conf_gen_start conf) heap)) /\
   (n < gen_gc_partial_conf_gen_start conf \/
     gen_gc_partial_conf_refs_start conf <= n) ==>
   (FAPPLY (new_f f conf heap) n = n)`,
  (REPEAT STRIP_TAC THEN ASM_SIMP_TAC[new_f_FAPPLY]));;

(* [local] *)
let gc_move_list_similar = prove
 (`!xs state1 ys state2.
     (gen_gc_partial_gc_move_list conf state1 xs = (ys,state2)) ==>
     ALL2 (similar_ptr conf) xs ys`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_ref_list_similar = prove
 (`!heap_refs state refs' state' conf.
     (gc_move_ref_list conf state heap_refs = (refs',state')) ==>
     ALL2 (similar_data conf) heap_refs refs'`,
  CHEAT_TAC);;

(* [local] *)
let IMP_gen_inv = prove
 (`heap_ok (heap:(('a,'b)heap_element) list) (gen_gc_partial_conf_limit
  conf) /\
   heap_gen_ok heap conf ==>
   gen_inv conf heap`,
  CHEAT_TAC);;

let partial_gc_related = prove
 (`roots_ok roots heap /\
    heap_ok (heap:(('a,'b)heap_element) list)
      (gen_gc_partial_conf_limit conf) /\
    heap_gen_ok heap conf ==>
    (?state f.
      (partial_gc conf ((roots:('a heap_address) list),heap) =
         (ADDR_MAP (FAPPLY f) roots,state)) /\
      (!ptr u. MEM (gc_shared_Pointer ptr u) roots ==> ptr IN FDOM f)
        /\
      (heap_ok
        (APPEND (APPEND (APPEND (gc_state_old state) (gc_state_h1
          state)) (heap_expand (gc_state_n state))) (gc_state_r1 state))
          (gen_gc_partial_conf_limit conf)) /\
      gc_related f heap (APPEND (APPEND (APPEND (gc_state_old state)
        (gc_state_h1 state)) (heap_expand (gc_state_n state)))
        (gc_state_r1 state)) /\ gc_state_ok
      state)`,
  CHEAT_TAC);;

(* gc_move_list_length *)
let gen_gc_partial_gc_move_list_length = prove
 (`!xs xs' state state'.
      (gen_gc_partial_gc_move_list conf state xs = (xs',state')) ==>
      (LENGTH xs' = LENGTH xs)`,
  CHEAT_TAC);;

let gc_move_ref_list_length = prove
 (`!xs xs' state state'.
      (gc_move_ref_list conf state xs = (xs',state')) ==>
      (LENGTH xs' = LENGTH xs)`,
  CHEAT_TAC);;

let gc_move_ref_list_heap_length' = prove
 (`!xs xs' state state'.
      (gc_move_ref_list conf state xs = (xs',state')) ==>
      (heap_length xs' = heap_length xs)`,
  (MESON_TAC[gc_move_ref_list_IMP]));;

let has_bad_ref_def = new_definition
  `has_bad_ref c s <=>
     (?xs l d. MEM (DataElement xs l d) (APPEND (gc_state_h1 s)
       (gc_state_h2 s)) /\ gen_gc_partial_conf_isRef c d) \/
     (?xs l d n. gen_gc_partial_conf_gen_start
       c <= n /\ n < gen_gc_partial_conf_refs_start c /\
       (heap_lookup n (gc_state_heap s) = SOME (DataElement xs l
         d)) /\ gen_gc_partial_conf_isRef c d)`;;

let balanced_state_def = new_definition
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

let simple_rel_def = new_definition
  `simple_rel c s1 s2 <=>
     (gc_state_old s2 = gc_state_old s1) /\
     (heap_length (APPEND (APPEND (gc_state_h1 s2) (gc_state_h2 s2))
       (heap_expand (gc_state_n s2))) =
      heap_length (APPEND (APPEND (gc_state_h1 s1) (gc_state_h2 s1))
        (heap_expand (gc_state_n s1)))) /\
     ((gc_state_a s1 = gen_gc_partial_conf_gen_start c + heap_length
       (gc_state_h1 s1) + heap_length (gc_state_h2 s1)) ==>
      (gc_state_a s2 = gen_gc_partial_conf_gen_start c + heap_length
        (gc_state_h1 s2) + heap_length (gc_state_h2 s2))) /\
     (ALL isDataElement (gc_state_h1 s1) ==> ALL isDataElement
       (gc_state_h1 s2)) /\
     (heap_length (APPEND (APPEND (FILTER isDataElement
       (gc_state_heap s1)) (gc_state_h1 s1)) (gc_state_h2 s1)) =
      heap_length (APPEND (APPEND (FILTER isDataElement
        (gc_state_heap s2)) (gc_state_h1 s2)) (gc_state_h2 s2))) /\
     (heap_length (FILTER isForwardPointer (gc_state_heap s1)) +
      heap_length (FILTER isDataElement (gc_state_heap s1)) =
      heap_length (FILTER isForwardPointer (gc_state_heap s2)) +
      heap_length (FILTER isDataElement (gc_state_heap s2))) /\
     (balanced_state c s1 ==> balanced_state c s2) /\
     (has_bad_ref c s2 ==> has_bad_ref c s1)`;;

(* [local] *)
let simple_rel_refl = prove
 (`simple_rel c x x`,
  (REWRITE_TAC[simple_rel_def]));;

(* [local] *)
let simple_rel_trans = prove
 (`simple_rel c x1 x2 /\ simple_rel c x2 x3 ==> simple_rel c x1 x3`,
  (REWRITE_TAC[simple_rel_def] THEN REPEAT GEN_TAC THEN STRIP_TAC
    THEN
   ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]));;

(* [local] *)
let gc_forward_ptr_lookup_DataElement = prove
 (`!hs n x a heap n1.
     (gc_forward_ptr n hs x a T = (heap,T)) /\
     (heap_lookup n1 heap = SOME (DataElement xs l' d)) ==>
     (heap_lookup n1 hs = SOME (DataElement xs l' d))`,
  CHEAT_TAC);;

(* [local] *)
let gc_forward_ptr_APPEND = prove
 (`!x0 n a1 a x1 heap1.
     (gc_forward_ptr n (APPEND x0 x1) a1 a T = (heap1,T)) ==>
     (if n < heap_length x0 then
       ?y0. (gc_forward_ptr n x0 a1 a T = (y0,T)) /\
            (heap1 = APPEND y0 x1) else
       ?y1. (gc_forward_ptr (n - heap_length x0) x1 a1 a T = (y1,T))
         /\
            (heap1 = APPEND x0 y1))`,
  CHEAT_TAC);;

(* [local] *)
let gc_forward_ptr_APPEND_APPEND = prove
 (`(gc_forward_ptr n (APPEND (APPEND x0 x1) x2) a1 a T = (heap1,T)) /\
   heap_length x0 <= n /\ n < heap_length (APPEND x0 x1) ==>
   (?y. (heap1 = APPEND (APPEND x0 y) x2) /\ (heap_length y =
     heap_length x1))`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `~(n < heap_length (x0:((A,B)heap_element)list))`
     ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP gc_forward_ptr_APPEND) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `y0:((A,B)heap_element)list`
     (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN
   DISCH_THEN(MP_TAC o MATCH_MP gc_forward_ptr_APPEND) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `y1:((A,B)heap_element)list`
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
   EXISTS_TAC `y1:((A,B)heap_element)list` THEN REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP gc_forward_ptr_heap_length) THEN
   MESON_TAC[]));;

(* [local] *)
let heap_segment_gc_forward_ptr = prove
 (`(heap_segment (k,l) heap = SOME (x0,x1,x2)) /\
   (gc_forward_ptr n heap a1 a T = (heap1,T)) /\
   k <= n /\ n < l ==>
   (?y. (heap_segment (k,l) heap1 = SOME (x0,y,x2)))`,
  CHEAT_TAC);;

let gc_move_inv = prove
 (`!xs xs' s1 s2.
      (gen_gc_partial_gc_move c s1 xs = (xs',s2)) /\ gc_state_ok s2
        ==>
      simple_rel c s1 s2`,
  CHEAT_TAC);;

let gc_move_list_inv = prove
 (`!xs xs' s1 s2.
      (gen_gc_partial_gc_move_list c s1 xs = (xs',s2)) /\ gc_state_ok
        s2 ==>
      simple_rel c s1 s2`,
  CHEAT_TAC);;

let gc_move_ref_list_inv = prove
 (`!xs xs' s1 s2.
      (gc_move_ref_list c s1 xs = (xs',s2)) /\ gc_state_ok s2 ==>
      simple_rel c s1 s2`,
  CHEAT_TAC);;

let gc_move_data_inv = prove
 (`!c s1 s2.
      (gen_gc_partial_gc_move_data c s1 = s2) /\ gc_state_ok s2 ==>
      simple_rel c s1 s2`,
  CHEAT_TAC);;

let LIST_REL_similar_data_IMP = prove
 (`!xs ys. ALL2 (similar_data cc) xs ys ==>
            (heap_length xs = heap_length ys) /\
            (heap_length (FILTER isDataElement xs) =
             heap_length (FILTER isDataElement ys))`,
  CHEAT_TAC);;

(* partial_gc_IMP *)
let gen_gc_partial_partial_gc_IMP = prove
 (`(partial_gc c (roots,heap) = (roots1,state1)) /\ gc_state_ok state1
  ==>
    (gc_state_a state1 = gen_gc_partial_conf_gen_start c +
      heap_length (gc_state_h1 state1)) /\
    (LENGTH roots1 = LENGTH roots) /\
    (heap_length (gc_state_old state1) =
      gen_gc_partial_conf_gen_start c) /\
    (heap_length (APPEND (APPEND (gc_state_old state1) (gc_state_h1
      state1)) (heap_expand (gc_state_n state1))) =
      gen_gc_partial_conf_refs_start
     c) /\
    ((FILTER isForwardPointer heap = []) ==>
     heap_length (FILTER isDataElement (APPEND (APPEND (gc_state_old
       state1) (gc_state_h1 state1)) (gc_state_r1 state1))) <=
     heap_length (FILTER isDataElement heap)) /\
    ALL isDataElement (gc_state_h1 state1) /\
    (?curr refs. (heap_segment (gen_gc_partial_conf_gen_start
      c,gen_gc_partial_conf_refs_start c) heap =
                   SOME (gc_state_old state1,curr,refs)) /\
                ALL2 (similar_data c) refs (gc_state_r1 state1) /\
                (!xs l d. MEM (DataElement xs l d) (gc_state_h1
                  state1) /\ gen_gc_partial_conf_isRef
                          c d ==>
                          (?xs l d. MEM (DataElement xs l d) curr
                            /\ gen_gc_partial_conf_isRef c d)))`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
