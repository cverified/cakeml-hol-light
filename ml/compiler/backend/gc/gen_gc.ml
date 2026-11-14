(* ======================================================== *)
(*  gen_gc: ported from HOL4's
    compiler/backend/gc/gen_gcScript.sml
    A definition theory, with 8 definitions, 1 datatype and 61
    theorems.  Needed by 7 files of the port.  *)
(* ======================================================== *)

(*
  The major collection of the generational copying garbage collector.
*)

needs "compiler/backend/gc/gc_shared.ml";;
needs "lib/integer_word.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "gen_gc"
  ["gc_shared"];;
(* HOL4 ancestors outside the port: words *)

(* HOL4 gen_gcScript.sml:16: ML code, not ported *)

(* Copying GC which moves references to the end of the heap. This
   implementation is a pre-stage to the generational GC. *)

let gen_gc_conf_FIELDS = define_record "gen_gc_conf"
  ["limit","num";
   "isRef","'a->bool"];;
hol4_field_overload "limit" "gen_gc_conf_limit";;
hol4_field_overload "limit_fupd" "gen_gc_conf_limit_fupd";;
hol4_field_overload "isRef" "gen_gc_conf_isRef";;
hol4_field_overload "isRef_fupd" "gen_gc_conf_isRef_fupd";;

let gen_gc_gc_move_def = define_cases
  [`gen_gc_gc_move conf state (gc_shared_Data d) = ((gc_shared_Data
  d:'a heap_address),state)`;
   `gen_gc_gc_move conf state (gc_shared_Pointer ptr d) =
         (match heap_lookup ptr (gc_state_heap state) with SOME
           (ForwardPointer ptr _3 l) -> (gc_shared_Pointer ptr d,state)
           | SOME (DataElement xs l dd) ->
           (let ok = (gc_state_ok state /\ l + 1 <= gc_state_n
             state) in
           let n = gc_state_n state - (l + 1) in
            if gen_gc_conf_isRef conf dd then
              // put refs in r4
              let r4 = CONS (DataElement xs l dd) (gc_state_r4
                state) in
              let (heap,ok) = gc_forward_ptr ptr (gc_state_heap
                state) (gc_state_a state + n) d ok in
                (
                gc_shared_Pointer (gc_state_a state + n)
                  d,gc_state_ok_fupd (K ok) (gc_state_heap_fupd (K heap)
                  (gc_state_n_fupd (K n) (gc_state_r4_fupd (K r4)
                  state)))) else
              // put data in h2
              let h2 = APPEND (gc_state_h2 state) [DataElement xs l
                dd] in
              let (heap,ok) = gc_forward_ptr ptr (gc_state_heap
                state) (gc_state_a state) d ok in
              let a = gc_state_a state + l + 1 in
                (
                gc_shared_Pointer (gc_state_a state)
                  d,gc_state_ok_fupd (K ok) (gc_state_heap_fupd (K
                  heap) (gc_state_a_fupd (K a) (gc_state_n_fupd (K
                  n) (gc_state_h2_fupd (K h2) state)))))) | _4 ->
                  (gc_shared_Pointer ptr d,gc_state_ok_fupd (K F)
                  state))`];;


(* [local] *)
let gc_move_IMP = prove
 (`!x x' state state'.
   (gen_gc_gc_move conf state x = (x',state')) ==>
   (gc_state_h1 state = gc_state_h1 state') /\
   (gc_state_r3 state = gc_state_r3 state') /\
   (gc_state_r2 state = gc_state_r2 state') /\
   (gc_state_r1 state = gc_state_r1 state') /\
   (IS_PREFIX (gc_state_h2 state') (gc_state_h2 state)) /\
   (IS_SUFFIX (gc_state_r4 state') (gc_state_r4 state))`,
  CHEAT_TAC);;

let gen_gc_gc_move_list_def,gen_gc_gc_move_list_ind = define_rec
  [`gen_gc_gc_move_list conf state [] = ([],state)`;
   `gen_gc_gc_move_list conf state (CONS x xs) =
        (let (x,state) = gen_gc_gc_move conf state x in
        let (xs,state) = gen_gc_gc_move_list conf state xs in
          (CONS x xs,state))`];;

let gc_move_list_IMP = prove
 (`!xs xs' state state'.
    (gen_gc_gc_move_list conf state xs = (xs',state')) ==>
    (gc_state_h1 state = gc_state_h1 state') /\
    (gc_state_r3 state = gc_state_r3 state') /\
    (gc_state_r2 state = gc_state_r2 state') /\
    (gc_state_r1 state = gc_state_r1 state') /\
    (IS_PREFIX (gc_state_h2 state') (gc_state_h2 state)) /\
    (IS_SUFFIX (gc_state_r4 state') (gc_state_r4 state))`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (\(conf,state). gen_gc_conf_limit conf - heap_length
       (gc_state_h1 state))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 gen_gcScript.sml:123-129: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let gc_move_data_def,gc_move_data_ind = define_guess_cheat
  [`(gen_gc_gc_move_data conf state =
     (match gc_state_h2 state with [] -> state | CONS h h2 ->
       (if gen_gc_conf_limit conf < heap_length (APPEND (gc_state_h1
         state) (CONS h h2)) then gc_state_ok_fupd (K F) state else
        match h with DataElement xs l d ->
          (let (xs,state) = gen_gc_gc_move_list conf state xs in
          let h1 = APPEND (gc_state_h1 state) [DataElement xs l d]
            in
          let h2 = TL (gc_state_h2 state) in
          let ok = (gc_state_ok state /\ ~(gc_state_h2 state = [])
            /\ (HD (gc_state_h2 state) = h)) in
            gen_gc_gc_move_data conf (gc_state_ok_fupd (K ok)
              (gc_state_h2_fupd (K h2) (gc_state_h1_fupd (K h1)
              state)))) | _5 -> gc_state_ok_fupd (K F) state)))`];;

(* the termination relation that HOL4 gives is
     MEASURE (\(conf,state). heap_length (gc_state_r2 state))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 gen_gcScript.sml:143-147: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let gc_move_refs_def,gc_move_refs_ind = define_guess_cheat
  [`// maybe more refs (r4 could have more)
   gc_move_refs conf state =
     (match gc_state_r2 state with [] -> gc_state_r1_fupd (K (APPEND
       (gc_state_r3 state) (gc_state_r1 state))) (gc_state_r3_fupd (K
       []) state) | CONS ref r2 ->
       (match ref with DataElement xs l d ->
         (let (xs,state) = gen_gc_gc_move_list conf state xs in
         let r3 = APPEND (gc_state_r3 state) [DataElement xs l d] in
           gc_move_refs conf (gc_state_r3_fupd (K r3)
             (gc_state_r2_fupd (K r2) state))) | _6 ->
             gc_state_ok_fupd (K F) state))`];;

(* The main gc loop *)
(* Runs a clock to simplify the termination argument *)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let gen_gc_gc_move_loop_def,gen_gc_gc_move_loop_ind = define_wf
  `MEASURE (\(x0,x1,x2). (\n. n) x2)`
  [`gen_gc_gc_move_loop conf state (clock:num) =
     (match gc_state_r4 state with [] ->
       (match gc_state_h2 state with [] -> state | (CONS h h2) ->
          (let state = gen_gc_gc_move_data conf state in
          if clock = 0 then gc_state_ok_fupd (K F) state else
            gen_gc_gc_move_loop conf state (clock - 1))) | (CONS h r4)
            ->
       (let state = gc_move_refs conf (gc_state_r4_fupd (K [])
         (gc_state_r2_fupd (K (gc_state_r4 state)) state)) in
       if clock = 0 then gc_state_ok_fupd (K F) state else
         gen_gc_gc_move_loop conf state (clock - 1)))`];;

let gen_gc_def = new_definition
  `gen_gc conf (roots,heap) =
     (let state =
         gc_state_ok_fupd (K (heap_length heap = gen_gc_conf_limit
           conf)) (gc_state_n_fupd (K (gen_gc_conf_limit conf))
           (gc_state_heap_fupd (K heap) empty_state)) in
     let (roots,state) = gen_gc_gc_move_list conf state roots in
     let state = gen_gc_gc_move_loop conf state (gen_gc_conf_limit
       conf) in
       (roots,state))`;;

(* Do we point to something that is fully processed? I.e. all children
are also copied. *)
let is_final_def = new_definition
  `is_final conf state ptr =
     (let h1end = heap_length (gc_state_h1 state) in
     let r3start = gc_state_a state + gc_state_n state + heap_length
       (gc_state_r4 state) in
     let r3end = r3start + heap_length (gc_state_r3 state) in
     let r1start = r3end + heap_length (gc_state_r2 state) in
     ptr < h1end \/
     r1start <= ptr \/
     (r3start <= ptr /\ ptr < r3end))`;;

let gen_gc_gc_inv_def = new_definition
  `gen_gc_gc_inv conf state (heap0:(('a,'b)heap_element) list)
  (roots0:('a heap_address) list) =
     (let heap' = APPEND (APPEND (APPEND (APPEND (APPEND (APPEND
       (gc_state_h1 state) (gc_state_h2 state))
                 (heap_expand (gc_state_n state))) (gc_state_r4
                 state)) (gc_state_r3 state)) (gc_state_r2 state))
                   (gc_state_r1 state) in
     (
      // lengths
      heap_length (APPEND (gc_state_h1 state) (gc_state_h2 state)) =
        gc_state_a state) /\
     (gc_state_a state + gc_state_n state + heap_length (APPEND
       (APPEND (APPEND (gc_state_r4 state) (gc_state_r3 state))
       (gc_state_r2 state)) (gc_state_r1 state)) = gen_gc_conf_limit
       conf) /\
     (heap_length (FILTER (\h. ~(isForwardPointer h)) (gc_state_heap
       state)) = gc_state_n state) /\
     ((heap_length (gc_state_heap state)) = gen_gc_conf_limit conf)
       /\ gc_state_ok
     // ----
     state /\
     heap_ok heap0 (gen_gc_conf_limit conf) /\
     heaps_similar heap0 (gc_state_heap state) /\
     // ----
     ALL isDataElement (gc_state_h1 state) /\ ALL isDataElement
       (gc_state_h2 state) /\
     ALL isDataElement (gc_state_r1 state) /\ ALL isDataElement
       (gc_state_r2 state) /\
     ALL isDataElement (gc_state_r3 state) /\ ALL isDataElement
       (gc_state_r4 state) /\
     (
      // ----
      !x l d. MEM (DataElement x l d) (APPEND (APPEND (APPEND
        (gc_state_r4 state) (gc_state_r3 state)) (gc_state_r2 state))
        (gc_state_r1 state)) ==> gen_gc_conf_isRef
           conf d) /\
     // ----
     BIJ (heap_map1 (gc_state_heap state)) (FDOM (heap_map 0
       (gc_state_heap state)))
         (heap_addresses 0 (APPEND (gc_state_h1 state) (gc_state_h2
           state)) UNION
          heap_addresses (gc_state_a state + gc_state_n state)
            (APPEND (APPEND (APPEND (gc_state_r4 state) (gc_state_r3
              state)) (gc_state_r2 state)) (gc_state_r1 state))) /\
     // ----
     (!i j.
       (FLOOKUP (heap_map 0 (gc_state_heap state)) i = SOME j) ==>
       (?xs l d.
         (heap_lookup i heap0 = SOME (DataElement xs l d)) /\
         (heap_lookup j heap' =
           SOME (DataElement
                  (if is_final conf state j then ADDR_MAP (heap_map1
                    (gc_state_heap state)) xs else xs)
                  l d)) /\
         reachable_addresses roots0 heap0 i /\
         (!ptr d.
           MEM (gc_shared_Pointer ptr d) xs /\ is_final conf state j
             ==>
           ptr IN FDOM (heap_map 0 (gc_state_heap state))))))`;;

(* HOL4 gen_gcScript.sml:235: ML code, not ported *)

(* [local] *)
let heap_map_ForwardPointer_lemma = prove
 (`!ptr.
     heap_map 0 (APPEND ha (CONS (ForwardPointer ptr a l) hb)) =
     heap_map 0 (APPEND ha (CONS (DataElement ys l d) hb)) |+
       (heap_length ha,ptr)`,
  CHEAT_TAC);;

(* isSomeDataOrForward_lemma[local] *)
let gen_gc_isSomeDataOrForward_lemma = prove
 (`!ha ptr.
     isSomeDataOrForward (heap_lookup ptr (APPEND ha (CONS
       (DataElement ys l d) hb))) <=>
     isSomeDataOrForward (heap_lookup ptr (APPEND ha (CONS
       (ForwardPointer a u l) hb)))`,
  CHEAT_TAC);;

(* HOL4 gen_gcScript.sml:264-266: ML code, not ported *)

(* [local] *)
let NOT_IN_heap_addresses = prove
 (`!xs n. ~(n + heap_length xs IN heap_addresses n xs)`,
  CHEAT_TAC);;

(* HOL4 gen_gcScript.sml:277: code that the source has in a comment *)
(*   NOT_IN_heap_addresses_general |> Q.SPECL [`xs`,`0`] |> SIMP_RULE std_ss []; *)

(* [local] *)
let NOT_IN_heap_addresses_less = prove
 (`!xs m n. (m < n) ==> ~(m IN heap_addresses n xs)`,
  (MESON_TAC[heap_addresses_LESS; NOT_LE]));;

(* [local] *)
let NOT_IN_heap_addresses_gt = prove
 (`!xs m n p.
   (heap_length xs + p <= m) ==>
   ~(m IN heap_addresses p xs)`,
  (MESON_TAC[heap_addresses_LESS_heap_length; ADD_SYM; NOT_LE]));;

(* [local] *)
let heap_length_CONS = prove
 (`!x xs. heap_length (CONS x xs) = el_length x + heap_length xs`,
  CHEAT_TAC);;

let heap_lookup_LENGTH = prove
 (`!xs x ys l. (heap_length xs = l) ==> (heap_lookup l (APPEND xs
  (CONS x ys)) = SOME x)`,
  (MESON_TAC[heap_lookup_PREFIX]));;

let heap_lookup_APPEND = prove
 (`!j xs ys.
    heap_lookup j (APPEND xs ys) =
      (if j < heap_length xs then heap_lookup j xs else heap_lookup
        (j - heap_length xs) ys)`,
  CHEAT_TAC);;

(* [local] *)
let IMP_if_equal = prove
 (`!b1 b2 x1 x2 y1 y2.
   (b1 = b2) /\ (b1 ==> (x1 = x2)) /\ (~b1 ==> (y1 = y2)) ==>
   ((if b1 then x1 else y1) = (if b2 then x2 else y2))`,
  (REPEAT GEN_TAC THEN BOOL_CASES_TAC `b1:bool` THEN REWRITE_TAC[]
    THEN MESON_TAC[]));;

(* heap_length_heap_expand[local] *)
let gen_gc_heap_length_heap_expand = prove
 (`!l. heap_length (heap_expand l) = l`,
  CHEAT_TAC);;

(* ADDR_MAP_EQ[local] *)
let gen_gc_ADDR_MAP_EQ = prove
 (`!xs. (!p d. MEM (gc_shared_Pointer p d) xs ==> (f p = g p)) ==>
        (ADDR_MAP f xs = ADDR_MAP g xs)`,
  CHEAT_TAC);;

(* heaps_similar_lemma[local] *)
let gen_gc_heaps_similar_lemma = prove
 (`!ha heap0 hb ptr ys l d a l.
     heaps_similar heap0 (APPEND (APPEND ha [DataElement ys l d]) hb)
       ==>
     heaps_similar heap0 (APPEND (APPEND ha [ForwardPointer ptr a
       l]) hb)`,
  CHEAT_TAC);;

(* gc_move_thm *)
let gen_gc_gc_move_thm = prove
 (`!x state.
       gen_gc_gc_inv conf state heap0 roots0 /\
       (!ptr u. (x = gc_shared_Pointer ptr u) ==>
                isSomeDataOrForward (heap_lookup ptr (gc_state_heap
                  state)) /\
                reachable_addresses roots0 heap0 ptr) ==>
       (?state'.
         (gen_gc_gc_move conf state x =
         (ADDR_APPLY (heap_map1 (gc_state_heap state')) x,state')) /\
         (!ptr u. (x = gc_shared_Pointer ptr u) ==> ptr IN FDOM
           (heap_map 0 (gc_state_heap state'))) /\
         (!ptr. isSomeDataOrForward (heap_lookup ptr (gc_state_heap
           state)) =
                isSomeDataOrForward (heap_lookup ptr (gc_state_heap
                  state'))) /\
         ((heap_map 0 (gc_state_heap state)) SUBMAP (heap_map 0
           (gc_state_heap state'))) /\
         gen_gc_gc_inv conf state' heap0 roots0)`,
  CHEAT_TAC);;

(* gc_move_ALT *)
let gen_gc_gc_move_ALT = prove
 (`gen_gc_gc_move conf state y =
     (let (y',state') = gen_gc_gc_move conf (gc_state_r4_fupd (K [])
       (gc_state_h2_fupd (K []) state)) y in
       (y',gc_state_r4_fupd (K (APPEND (gc_state_r4 state')
         (gc_state_r4 state))) (gc_state_h2_fupd (K (APPEND
         (gc_state_h2 state) (gc_state_h2 state'))) state')))`,
  CHEAT_TAC);;

(* gc_move_list_thm[local] *)
let gen_gc_gc_move_list_thm = prove
 (`!xs state.
   gen_gc_gc_inv conf state heap0 roots0 /\
   (!ptr u. MEM (gc_shared_Pointer ptr u) (xs:('a heap_address) list)
     ==>
            isSomeDataOrForward (heap_lookup ptr (gc_state_heap
              state)) /\
            reachable_addresses roots0 heap0 ptr) ==>
   (?state'.
     (gen_gc_gc_move_list conf state xs =
       (ADDR_MAP (heap_map1 (gc_state_heap state')) xs,state')) /\
     (!ptr u. MEM (gc_shared_Pointer ptr u) xs ==> ptr IN FDOM
       (heap_map 0 (gc_state_heap state'))) /\
     (!ptr. isSomeDataOrForward (heap_lookup ptr (gc_state_heap
       state)) =
            isSomeDataOrForward (heap_lookup ptr (gc_state_heap
              state'))) /\
     ((heap_map 0 (gc_state_heap state)) SUBMAP (heap_map 0
       (gc_state_heap state'))) /\
     gen_gc_gc_inv conf state' heap0 roots0)`,
  CHEAT_TAC);;

(* gc_move_list_ALT *)
let gen_gc_gc_move_list_ALT = prove
 (`!ys state.
      gen_gc_gc_move_list conf state ys =
        (let (ys',state') = gen_gc_gc_move_list conf
          (gc_state_r4_fupd (K []) (gc_state_h2_fupd (K []) state)) ys
          in
        (ys',gc_state_r4_fupd (K (APPEND (gc_state_r4 state')
          (gc_state_r4 state))) (gc_state_h2_fupd (K (APPEND
          (gc_state_h2 state) (gc_state_h2 state'))) state')))`,
  CHEAT_TAC);;

(* gc_move_list_APPEND_lemma[local] *)
let gen_gc_gc_move_list_APPEND_lemma = prove
 (`!ys state.
     (gen_gc_gc_move_list conf state ys = (ys',state')) ==>
       (?h2' r4'. (gc_state_h2 state' = APPEND (gc_state_h2 state)
         h2') /\ (gc_state_r4 state' = APPEND r4' (gc_state_r4
         state)))`,
  CHEAT_TAC);;

(* heap_addresses_APPEND[local] *)
let gen_gc_heap_addresses_APPEND = prove
 (`!xs ys n. heap_addresses n (APPEND xs ys) =
             heap_addresses n xs UNION heap_addresses (n +
               heap_length xs) ys`,
  CHEAT_TAC);;

(* [local] *)
let heap_addresses_APPEND_IN = prove
 (`!xs ys n j.
     j IN heap_addresses n (APPEND xs ys) ==>
     j IN heap_addresses n xs \/ j IN heap_addresses (n +
       heap_length xs) ys`,
  (REWRITE_TAC[gen_gc_heap_addresses_APPEND; IN_UNION]));;

(* [local] *)
let GREATER_IMP_heap_lookup = prove
 (`!ys xs j.
   (heap_length (APPEND xs ys) <= j + heap_length ys) ==>
   (heap_lookup j (APPEND xs ys) = heap_lookup (j - heap_length xs)
     ys)`,
  (REWRITE_TAC[heap_length_APPEND] THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC NOT_LESS_IMP_heap_lookup THEN ASM_ARITH_TAC));;

let heap_lookup_IMP_MEM = prove
 (`!x n y. (heap_lookup n x = SOME y) ==> MEM y x`,
  (MESON_TAC[heap_lookup_MEM]));;

(* heaps_similar_lemma *)
let gen_gc_heaps_similar_lemma = prove
 (`!h1 h2 ptr.
      heaps_similar h1 h2 /\ isSomeDataElement (heap_lookup ptr h1)
        ==>
      isSomeDataOrForward (heap_lookup ptr h2)`,
  CHEAT_TAC);;

let BIJ_IMP_FLOOKUP_SOME = prove
 (`!s h j.
      BIJ (heap_map1 h) (FDOM (heap_map 0 h)) s /\ j IN s ==>
      (?i. FLOOKUP (heap_map 0 h) i = SOME j)`,
  CHEAT_TAC);;

(* [local] *)
let heap_lookup_IMP_heap_addresses_GEN = prove
 (`!xs n x j. (heap_lookup j xs = SOME x) ==> n + j IN heap_addresses
  n xs`,
  CHEAT_TAC);;

(* in gc_inv or prove lemma here *)
(* [local] *)
let pointers_ok = prove
 (`!state xs l d ptr u.
     gen_gc_gc_inv conf state heap0 roots0 /\
     (MEM (DataElement xs l d) (gc_state_h2 state) \/ MEM
       (DataElement xs l d) (gc_state_r2 state)) /\
     MEM (gc_shared_Pointer ptr u) xs ==>
     isSomeDataOrForward (heap_lookup ptr (gc_state_heap state))`,
  CHEAT_TAC);;

let IMP_reachable_addresses = prove
 (`!i ptr u xs l d.
      reachable_addresses roots0 heap0 i /\ MEM (gc_shared_Pointer
        ptr u) xs /\
      (heap_lookup i heap0 = SOME (DataElement xs l d)) ==>
      reachable_addresses roots0 heap0 ptr`,
  CHEAT_TAC);;

let gc_move_data_thm = prove
 (`!conf state.
      gen_gc_gc_inv conf state heap0 roots0 /\
      (gc_state_r3 state = []) /\ (gc_state_r2 state = []) ==>
      (?state'.
        (gen_gc_gc_move_data conf state = state') /\
        ((heap_map 0 (gc_state_heap state)) SUBMAP (heap_map 0
          (gc_state_heap state'))) /\
        gen_gc_gc_inv conf state' heap0 roots0 /\
        (gc_state_h2 state' = []) /\ (gc_state_r3 state' = []) /\
          (gc_state_r2 state' = []))`,
  CHEAT_TAC);;

let gc_move_refs_lemma = prove
 (`!state l n b xs' t state'.
      gen_gc_gc_inv conf state heap0 roots0 /\
      (gc_state_r2 state = CONS (DataElement l n b) t) /\
      (gen_gc_gc_move_list conf state l = (xs',state')) /\
      (!ptr u. MEM (gc_shared_Pointer ptr u) l ==>
        isSomeDataOrForward (heap_lookup ptr (gc_state_heap state))
          /\
        reachable_addresses roots0 heap0 ptr) ==>
      gen_gc_gc_inv conf
        (gc_state_r2_fupd (K t) (gc_state_r3_fupd (K (APPEND
          (gc_state_r3 state') [DataElement xs' n b])) state'))
        heap0 roots0`,
  CHEAT_TAC);;

let gc_move_refs_thm = prove
 (`!conf state.
      gen_gc_gc_inv conf state heap0 roots0 ==>
      (?state'.
        (gc_move_refs conf state = state') /\
        ((heap_map 0 (gc_state_heap state)) SUBMAP (heap_map 0
          (gc_state_heap state'))) /\
        gen_gc_gc_inv conf state' heap0 roots0 /\
        (gc_state_r3 state' = []) /\ (gc_state_r2 state' = []) /\
        (0 < heap_length (gc_state_r3 state) ==> heap_length
          (gc_state_r1 state) < heap_length (gc_state_r1 state')))`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_list_heap_length = prove
 (`!conf state state' xs ys.
     (gen_gc_gc_move_list conf state xs = (ys,state')) ==>
     (heap_length (gc_state_h1 state) <= heap_length (gc_state_h1
       state')) /\
     (heap_length (gc_state_r1 state) <= heap_length (gc_state_r1
       state'))`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_data_heap_length = prove
 (`!conf state state'.
     Abbrev (state' = gen_gc_gc_move_data conf state) ==>
     heap_length (gc_state_h1 state) <= heap_length (gc_state_h1
       state') /\
     heap_length (gc_state_r1 state) <= heap_length (gc_state_r1
       state')`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_refs_heap_length = prove
 (`!conf state state'.
     (gc_move_refs conf state = state') ==>
     heap_length (gc_state_h1 state) <= heap_length (gc_state_h1
       state') /\
     heap_length (gc_state_r1 state) <= heap_length (gc_state_r1
       state')`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_loop_gc_inv = prove
 (`!conf state h t.
     gen_gc_gc_inv conf state heap0 roots0 /\ (gc_state_r2 state =
       []) /\ (gc_state_r4 state = CONS h t) /\
     (gc_state_r3 state = []) ==>
     gen_gc_gc_inv conf (gc_state_r4_fupd (K []) (gc_state_r2_fupd
       (K (CONS h t)) state)) heap0 roots0`,
  CHEAT_TAC);;

(* [local] *)
let reachable_addresses_gc_inv_r4 = prove
 (`gen_gc_gc_inv conf state heap roots0 /\
   (gc_state_r4 state = CONS (DataElement l n b) t) /\ MEM
     (gc_shared_Pointer ptr u) l ==>
   reachable_addresses roots0 heap ptr`,
  CHEAT_TAC);;

(* gc_move_loop_thm *)
let gen_gc_gc_move_loop_thm = prove
 (`!conf state clock. gen_gc_conf_limit
      conf <= clock + heap_length (gc_state_h1 state) + heap_length
        (gc_state_r1 state) /\
      (gc_state_r2 state = []) /\ (gc_state_r3 state = []) /\
      gen_gc_gc_inv conf state heap roots0 ==>
        (?state'.
          (gen_gc_gc_move_loop conf state clock = state') /\
          ((heap_map 0 (gc_state_heap state)) SUBMAP (heap_map 0
            (gc_state_heap state'))) /\
          gen_gc_gc_inv conf state' heap roots0 /\
          (gc_state_h2 state' = []) /\
          (gc_state_r4 state' = []) /\
          (gc_state_r3 state' = []) /\
          (gc_state_r2 state' = []))`,
  CHEAT_TAC);;

(* gc_inv_init *)
let gen_gc_gc_inv_init = prove
 (`heap_ok heap (gen_gc_conf_limit conf) ==>
    gen_gc_gc_inv conf (gc_state_ok_fupd (K (heap_length heap =
      gen_gc_conf_limit conf)) (gc_state_n_fupd (K (gen_gc_conf_limit
      conf)) (gc_state_heap_fupd (K heap) empty_state))) heap roots`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let gen_gc_thm = prove
 (cake_as_vars (fun () ->
    `!conf roots heap.
      roots_ok roots heap /\ heap_ok heap (gen_gc_conf_limit conf)
        ==>
      (?state.
        (gen_gc conf (roots,heap) =
        (ADDR_MAP (heap_map1 (gc_state_heap state)) roots,state))
          /\
        (!ptr u. MEM (gc_shared_Pointer ptr u) roots ==> ptr IN
          FDOM (heap_map 0 (gc_state_heap state))) /\
        gen_gc_gc_inv conf state heap roots /\
        (gc_state_h2 state = []) /\
        (gc_state_r4 state = []) /\
        (gc_state_r3 state = []) /\
        (gc_state_r2 state = []))`),
  CHEAT_TAC);;

(* LESS_IMP_heap_lookup *)
let gen_gc_LESS_IMP_heap_lookup = prove
 (`!xs j ys. j < heap_length xs ==> (heap_lookup j (APPEND xs ys) =
  heap_lookup j xs)`,
  CHEAT_TAC);;

(* HOL4 gen_gcScript.sml:1619-1623: a theorem that HOL4 states as the
   value of an ML expression: heap_lookup_IMP_heap_addresses *)

(* [local] *)
let heap_lookup_AND_APPEND_IMP = prove
 (`!xs n ys d d1.
     (heap_lookup n xs = SOME d) /\
     (heap_lookup n (APPEND xs ys) = SOME d1) ==> (d1 = d)`,
  (MESON_TAC[gen_gc_heap_lookup_EXTEND; option_INJ]));;

(* [local] *)
let heap_lookup_AND_PREPEND_IMP = prove
 (`!n xs ys d d1.
     (heap_lookup n ys = SOME d) /\
     (heap_lookup (heap_length xs + n) (APPEND xs ys) = SOME d1) ==>
     (d1 = d)`,
  CHEAT_TAC);;

(* [local] *)
let MEM_heap_expand_FALSE = prove
 (`!n. ~(MEM (DataElement xs l d) (heap_expand n))`,
  CHEAT_TAC);;

(* [local] *)
let FILTER_isForward_heap_expand_lemma = prove
 (`!n. FILTER isForwardPointer (heap_expand n) = []`,
  (GEN_TAC THEN REWRITE_TAC[heap_expand_def] THEN COND_CASES_TAC THEN
   REWRITE_TAC[FILTER; isForwardPointer_def]));;

(* [local] *)
let heap_lookup_CONS_IMP = prove
 (`(heap_lookup j ys = SOME z) ==>
   (heap_lookup (j + heap_length [x]) (CONS x ys) = SOME z)`,
  CHEAT_TAC);;

(* [local] *)
let heap_lookup_PREPEND_EXTEND = prove
 (`!xs j ys z.
   (heap_lookup j ys = SOME z) ==>
   (heap_lookup (heap_length xs + j) (APPEND xs ys) = SOME z)`,
  CHEAT_TAC);;

let gen_gc_ok = prove
 (`!conf roots heap.
    roots_ok roots heap /\ heap_ok (heap:(('a,'b)heap_element) list)
      (gen_gc_conf_limit conf) ==>
    (?state roots' heap'.
      (heap' = APPEND (APPEND (gc_state_h1 state) (heap_expand
        (gc_state_n state))) (gc_state_r1 state)) /\
      (gen_gc conf ((roots:('a heap_address) list),heap) =
        (roots',state)) /\ gc_state_ok
      state /\
      (gc_state_a state = heap_length (gc_state_h1 state)) /\
      roots_ok roots' heap' /\
      heap_ok heap' (gen_gc_conf_limit conf))`,
  CHEAT_TAC);;

(* [local] *)
let IN_heap_addresses_LESS = prove
 (`!heap n k. n IN heap_addresses k heap ==> k <= n /\ n < k +
  heap_length heap`,
  (MESON_TAC[heap_addresses_LESS; heap_addresses_LESS_heap_length]));;

(* heap_lookup_EXTEND *)
let gen_gc_heap_lookup_EXTEND = prove
 (`!xs n ys x. (heap_lookup n xs = SOME x) ==>
                (heap_lookup n (APPEND xs ys) = SOME x)`,
  CHEAT_TAC);;

let gen_gc_related = prove
 (`!conf roots heap.
    roots_ok roots heap /\ heap_ok (heap:(('a,'b)heap_element) list)
      (gen_gc_conf_limit conf) ==>
    (?state f.
      (gen_gc conf ((roots:('a heap_address) list),heap) =
         (ADDR_MAP (FAPPLY f) roots,state)) /\
      (FDOM f = reachable_addresses roots heap) /\
      (FRANGE f = {a | isSomeDataElement (heap_lookup a (APPEND
        (APPEND (gc_state_h1 state) (heap_expand (gc_state_n state)))
        (gc_state_r1 state)))}) /\
      (heap_length (APPEND (gc_state_h1 state) (gc_state_r1 state)) =
       heap_length (heap_filter (FDOM f) heap)) /\
      gc_related f heap (APPEND (APPEND (gc_state_h1 state)
        (heap_expand (gc_state_n state))) (gc_state_r1 state)) /\
      ALL isDataElement (APPEND (gc_state_h1 state) (gc_state_r1
        state)))`,
  CHEAT_TAC);;

(* gc_forward_ptr_ok *)
let gen_gc_gc_forward_ptr_ok = prove
 (`!heap n a d c x. (gc_forward_ptr n heap a d c = (x,T)) ==> c`,
  CHEAT_TAC);;

(* gc_move_ok *)
let gen_gc_gc_move_ok = prove
 (`(gen_gc_gc_move conf state x = (x',state')) /\ gc_state_ok state'
  ==> gc_state_ok state`,
  CHEAT_TAC);;

(* gc_move_list_ok *)
let gen_gc_gc_move_list_ok = prove
 (`!xs xs' state state'.
      (gen_gc_gc_move_list conf state xs = (xs',state')) /\
        gc_state_ok state' ==> gc_state_ok
      state`,
  CHEAT_TAC);;

let gc_move_data_ok = prove
 (`!conf s. gc_state_ok (gen_gc_gc_move_data conf s) ==> gc_state_ok s`,
  CHEAT_TAC);;

let gc_move_data_h2 = prove
 (`!conf s. gc_state_ok (gen_gc_gc_move_data conf s) ==>
             (gc_state_h2 (gen_gc_gc_move_data conf s) = [])`,
  CHEAT_TAC);;

let gc_move_refs_ok = prove
 (`!conf s. gc_state_ok (gc_move_refs conf s) ==> gc_state_ok s`,
  CHEAT_TAC);;

let gc_move_loop_ok = prove
 (`!conf s c. gc_state_ok (gen_gc_gc_move_loop conf s c) ==>
  gc_state_ok s`,
  CHEAT_TAC);;

let gc_move_list_length = prove
 (`!xs xs' state state'.
      (gen_gc_gc_move_list conf state xs = (xs',state')) ==>
      (LENGTH xs' = LENGTH xs)`,
  CHEAT_TAC);;

let gen_gc_LENGTH = prove
 (`(gen_gc c (xs,heap) = (ys,s)) ==> (LENGTH ys = LENGTH xs)`,
  CHEAT_TAC);;

let gen_gc_a = prove
 (`(gen_gc c (xs,heap) = (ys,s1)) /\ gc_state_ok s1 /\
    roots_ok xs heap /\ heap_ok heap (gen_gc_conf_limit c) ==>
    (gc_state_a s1 = heap_length (gc_state_h1 s1))`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
