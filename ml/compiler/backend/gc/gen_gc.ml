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

let gc_move_def = cake_define_list
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
              let r4 = (DataElement xs l dd) :: gc_state_r4 state in
              let (heap,ok) = gc_forward_ptr ptr (gc_state_heap
                state) (gc_state_a state + n) d ok in
                (
                gc_shared_Pointer (gc_state_a state + n)
                  d,gc_state_ok_fupd (K ok) (gc_state_heap_fupd (K heap)
                  (gc_state_n_fupd (K n) (gc_state_r4_fupd (K r4)
                  state)))) else
              let h2 = gc_state_h2 state ++ [DataElement xs l dd] in
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
hol4_overload "gc_move" "gen_gc_gc_move";;


let gc_move_IMP = cake_theorem "gc_move_IMP[local]"
  (fun () ->
    `!x x' state state'.
     (gen_gc_gc_move conf state x = (x',state')) ==>
     (gc_state_h1 state = gc_state_h1 state') /\
     (gc_state_r3 state = gc_state_r3 state') /\
     (gc_state_r2 state = gc_state_r2 state') /\
     (gc_state_r1 state = gc_state_r1 state') /\
     (IS_PREFIX (gc_state_h2 state') (gc_state_h2 state)) /\
     (IS_SUFFIX (gc_state_r4 state') (gc_state_r4 state))`)
  CHEAT_TAC;;

let gc_move_list_def = cake_define_list
  [`gen_gc_gc_move_list conf state [] = ([],state)`;
   `gen_gc_gc_move_list conf state (x :: xs) =
        (let (x,state) = gen_gc_gc_move conf state x in
        let (xs,state) = gen_gc_gc_move_list conf state xs in
          (x :: xs,state))`];;
hol4_overload "gc_move_list" "gen_gc_gc_move_list";;

let gc_move_list_IMP = cake_theorem "gc_move_list_IMP"
  (fun () ->
    `!xs xs' state state'.
      (gen_gc_gc_move_list conf state xs = (xs',state')) ==>
      (gc_state_h1 state = gc_state_h1 state') /\
      (gc_state_r3 state = gc_state_r3 state') /\
      (gc_state_r2 state = gc_state_r2 state') /\
      (gc_state_r1 state = gc_state_r1 state') /\
      (IS_PREFIX (gc_state_h2 state') (gc_state_h2 state)) /\
      (IS_SUFFIX (gc_state_r4 state') (gc_state_r4 state))`)
  CHEAT_TAC;;

(* HOL4 gen_gcScript.sml:123-129: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let gc_move_data_def = cake_define_try_tac (fun () ->
  `MEASURE (\(conf,state). gen_gc_conf_limit conf - heap_length
  (gc_state_h1 state))`)
  CHEAT_TAC
  `(gen_gc_gc_move_data conf state =
     (match gc_state_h2 state with [] -> state | h :: h2 ->
       (if gen_gc_conf_limit conf < heap_length (gc_state_h1 state ++
         (h :: h2)) then gc_state_ok_fupd (K F) state else
        match h with DataElement xs l d ->
          (let (xs,state) = gen_gc_gc_move_list conf state xs in
          let h1 = gc_state_h1 state ++ [DataElement xs l d] in
          let h2 = TL (gc_state_h2 state) in
          let ok = (gc_state_ok state /\ ~(gc_state_h2 state = []) /\
            (HD (gc_state_h2 state) = h)) in
            gen_gc_gc_move_data conf (gc_state_ok_fupd (K ok)
              (gc_state_h2_fupd (K h2) (gc_state_h1_fupd (K h1)
              state)))) | _5 -> gc_state_ok_fupd (K F) state)))`;;
hol4_overload "gc_move_data" "gen_gc_gc_move_data";;

(* HOL4 gen_gcScript.sml:143-147: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let gc_move_refs_def = cake_define_try_tac (fun () ->
  `MEASURE (\(conf,state). heap_length (gc_state_r2 state))`)
  CHEAT_TAC
  `gc_move_refs conf state =
     (match gc_state_r2 state with [] -> gc_state_r1_fupd (K
       (gc_state_r3 state ++ gc_state_r1 state)) (gc_state_r3_fupd (K
       []) state) | ref :: r2 ->
       (match ref with DataElement xs l d ->
         (let (xs,state) = gen_gc_gc_move_list conf state xs in
         let r3 = gc_state_r3 state ++ [DataElement xs l d] in
           gc_move_refs conf (gc_state_r3_fupd (K r3)
             (gc_state_r2_fupd (K r2) state))) | _6 ->
             gc_state_ok_fupd (K F) state))`;;

(* The main gc loop *)
(* Runs a clock to simplify the termination argument *)
let gc_move_loop_def = cake_define
  `gen_gc_gc_move_loop conf state (clock:num) =
     (match gc_state_r4 state with [] ->
       (match gc_state_h2 state with [] -> state | (h :: h2) ->
          (let state = gen_gc_gc_move_data conf state in
          if clock = 0 then gc_state_ok_fupd (K F) state else
            gen_gc_gc_move_loop conf state (clock - 1))) | (h :: r4) ->
       (let state = gc_move_refs conf (gc_state_r4_fupd (K [])
         (gc_state_r2_fupd (K (gc_state_r4 state)) state)) in
       if clock = 0 then gc_state_ok_fupd (K F) state else
         gen_gc_gc_move_loop conf state (clock - 1)))`;;
hol4_overload "gc_move_loop" "gen_gc_gc_move_loop";;

let gen_gc_def = cake_define
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
let is_final_def = cake_define
  `is_final conf state ptr =
     (let h1end = heap_length (gc_state_h1 state) in
     let r3start = gc_state_a state + gc_state_n state + heap_length
       (gc_state_r4 state) in
     let r3end = r3start + heap_length (gc_state_r3 state) in
     let r1start = r3end + heap_length (gc_state_r2 state) in
     ptr < h1end \/
     r1start <= ptr \/
     (r3start <= ptr /\ ptr < r3end))`;;

let gc_inv_def = cake_define
  `gen_gc_gc_inv conf state (heap0:(('a,'b)heap_element) list)
  (roots0:('a heap_address) list) =
     (let heap' = gc_state_h1 state ++ gc_state_h2 state ++
                 heap_expand (gc_state_n state) ++ gc_state_r4
                 state ++ gc_state_r3 state ++ gc_state_r2 state ++
                   gc_state_r1 state in
     (heap_length (gc_state_h1 state ++ gc_state_h2 state) =
       gc_state_a state) /\
     (gc_state_a state + gc_state_n state + heap_length (gc_state_r4
       state ++ gc_state_r3 state ++ gc_state_r2 state ++ gc_state_r1
       state) = gen_gc_conf_limit conf) /\
     (heap_length (FILTER (\h. ~(isForwardPointer h)) (gc_state_heap
       state)) = gc_state_n state) /\
     ((heap_length (gc_state_heap state)) = gen_gc_conf_limit conf)
       /\ gc_state_ok
     state /\
     heap_ok heap0 (gen_gc_conf_limit conf) /\
     heaps_similar heap0 (gc_state_heap state) /\
     EVERY isDataElement (gc_state_h1 state) /\ EVERY isDataElement
       (gc_state_h2 state) /\
     EVERY isDataElement (gc_state_r1 state) /\ EVERY isDataElement
       (gc_state_r2 state) /\
     EVERY isDataElement (gc_state_r3 state) /\ EVERY isDataElement
       (gc_state_r4 state) /\
     (!x l d. MEM (DataElement x l d) (gc_state_r4 state ++
       gc_state_r3 state ++ gc_state_r2 state ++ gc_state_r1 state) ==>
       gen_gc_conf_isRef
           conf d) /\
     BIJ (heap_map1 (gc_state_heap state)) (FDOM (heap_map 0
       (gc_state_heap state)))
         (heap_addresses 0 (gc_state_h1 state ++ gc_state_h2 state)
           UNION
          heap_addresses (gc_state_a state + gc_state_n state)
            (gc_state_r4 state ++ gc_state_r3 state ++ gc_state_r2
              state ++ gc_state_r1 state)) /\
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
hol4_overload "gc_inv" "gen_gc_gc_inv";;

(* HOL4 gen_gcScript.sml:235: ML code, not ported *)

let heap_map_ForwardPointer_lemma =
  cake_theorem "heap_map_ForwardPointer_lemma[local]"
  (fun () ->
    `!ptr.
       heap_map 0 (ha ++ (ForwardPointer ptr a l :: hb)) =
       heap_map 0 (ha ++ (DataElement ys l d :: hb)) |+
         (heap_length ha,ptr)`)
  CHEAT_TAC;;

let gen_gc_isSomeDataOrForward_lemma =
  cake_theorem "isSomeDataOrForward_lemma[local]"
  (fun () ->
    `!ha ptr.
       isSomeDataOrForward (heap_lookup ptr (ha ++ (DataElement ys
         l d :: hb))) <=>
       isSomeDataOrForward (heap_lookup ptr (ha ++
         (ForwardPointer a u l :: hb)))`)
  CHEAT_TAC;;

(* HOL4 gen_gcScript.sml:264-266: ML code, not ported *)

let NOT_IN_heap_addresses = cake_theorem "NOT_IN_heap_addresses[local]"
  (fun () ->
    `!xs n. ~(n + heap_length xs IN heap_addresses n xs)`)
  CHEAT_TAC;;

(* HOL4 gen_gcScript.sml:277: code that the source has in a comment *)
(*   NOT_IN_heap_addresses_general |> Q.SPECL [`xs`,`0`] |> SIMP_RULE std_ss []; *)

let NOT_IN_heap_addresses_less =
  cake_theorem "NOT_IN_heap_addresses_less[local]"
  (fun () ->
    `!xs m n. (m < n) ==> ~(m IN heap_addresses n xs)`)
  CHEAT_TAC;;

let NOT_IN_heap_addresses_gt =
  cake_theorem "NOT_IN_heap_addresses_gt[local]"
  (fun () ->
    `!xs m n p.
     (heap_length xs + p <= m) ==>
     ~(m IN heap_addresses p xs)`)
  CHEAT_TAC;;

let heap_length_CONS = cake_theorem "heap_length_CONS[local]"
  (fun () ->
    `!x xs. heap_length (x :: xs) = el_length x + heap_length xs`)
  CHEAT_TAC;;

let heap_lookup_LENGTH = cake_theorem "heap_lookup_LENGTH"
  (fun () ->
    `!xs x ys l. (heap_length xs = l) ==> (heap_lookup l (xs ++ (x ::
  ys)) = SOME x)`)
  CHEAT_TAC;;

let heap_lookup_APPEND = cake_theorem "heap_lookup_APPEND"
  (fun () ->
    `!j xs ys.
      heap_lookup j (xs ++ ys) =
        (if j < heap_length xs then heap_lookup j xs else
          heap_lookup (j - heap_length xs) ys)`)
  CHEAT_TAC;;

let IMP_if_equal = cake_theorem "IMP_if_equal[local]"
  (fun () ->
    `!b1 b2 x1 x2 y1 y2.
     (b1 = b2) /\ (b1 ==> (x1 = x2)) /\ (~b1 ==> (y1 = y2)) ==>
     ((if b1 then x1 else y1) = (if b2 then x2 else y2))`)
  CHEAT_TAC;;

let gen_gc_heap_length_heap_expand =
  cake_theorem "heap_length_heap_expand[local]"
  (fun () ->
    `!l. heap_length (heap_expand l) = l`)
  CHEAT_TAC;;

let gen_gc_ADDR_MAP_EQ = cake_theorem "ADDR_MAP_EQ[local]"
  (fun () ->
    `!xs. (!p d. MEM (gc_shared_Pointer p d) xs ==> (f p = g p)) ==>
          (ADDR_MAP f xs = ADDR_MAP g xs)`)
  CHEAT_TAC;;

let gen_gc_heaps_similar_lemma =
  cake_theorem "heaps_similar_lemma[local]"
  (fun () ->
    `!ha heap0 hb ptr ys l d a l.
       heaps_similar heap0 (ha ++ [DataElement ys l d] ++ hb) ==>
       heaps_similar heap0 (ha ++ [ForwardPointer ptr a l] ++ hb)`)
  CHEAT_TAC;;

let gen_gc_gc_move_thm = cake_theorem "gc_move_thm"
  (fun () ->
    `!x state.
         gen_gc_gc_inv conf state heap0 roots0 /\
         (!ptr u. (x = gc_shared_Pointer ptr u) ==>
                  isSomeDataOrForward (heap_lookup ptr
                    (gc_state_heap state)) /\
                  reachable_addresses roots0 heap0 ptr) ==>
         (?state'.
           (gen_gc_gc_move conf state x =
           (ADDR_APPLY (heap_map1 (gc_state_heap state'))
             x,state')) /\
           (!ptr u. (x = gc_shared_Pointer ptr u) ==> ptr IN FDOM
             (heap_map 0 (gc_state_heap state'))) /\
           (!ptr. isSomeDataOrForward (heap_lookup ptr
             (gc_state_heap state)) =
                  isSomeDataOrForward (heap_lookup ptr
                    (gc_state_heap state'))) /\
           ((heap_map 0 (gc_state_heap state)) SUBMAP (heap_map 0
             (gc_state_heap state'))) /\
           gen_gc_gc_inv conf state' heap0 roots0)`)
  CHEAT_TAC;;

let gen_gc_gc_move_ALT = cake_theorem "gc_move_ALT"
  (fun () ->
    `gen_gc_gc_move conf state y =
       (let (y',state') = gen_gc_gc_move conf (gc_state_r4_fupd (K
         []) (gc_state_h2_fupd (K []) state)) y in
         (y',gc_state_r4_fupd (K (gc_state_r4 state' ++
           gc_state_r4 state)) (gc_state_h2_fupd (K (gc_state_h2 state
           ++ gc_state_h2 state')) state')))`)
  CHEAT_TAC;;

let gen_gc_gc_move_list_thm = cake_theorem "gc_move_list_thm[local]"
  (fun () ->
    `!xs state.
     gen_gc_gc_inv conf state heap0 roots0 /\
     (!ptr u. MEM (gc_shared_Pointer ptr u) (xs:('a heap_address)
       list) ==>
              isSomeDataOrForward (heap_lookup ptr (gc_state_heap
                state)) /\
              reachable_addresses roots0 heap0 ptr) ==>
     (?state'.
       (gen_gc_gc_move_list conf state xs =
         (ADDR_MAP (heap_map1 (gc_state_heap state')) xs,state'))
           /\
       (!ptr u. MEM (gc_shared_Pointer ptr u) xs ==> ptr IN FDOM
         (heap_map 0 (gc_state_heap state'))) /\
       (!ptr. isSomeDataOrForward (heap_lookup ptr (gc_state_heap
         state)) =
              isSomeDataOrForward (heap_lookup ptr (gc_state_heap
                state'))) /\
       ((heap_map 0 (gc_state_heap state)) SUBMAP (heap_map 0
         (gc_state_heap state'))) /\
       gen_gc_gc_inv conf state' heap0 roots0)`)
  CHEAT_TAC;;

let gen_gc_gc_move_list_ALT = cake_theorem "gc_move_list_ALT"
  (fun () ->
    `!ys state.
        gen_gc_gc_move_list conf state ys =
          (let (ys',state') = gen_gc_gc_move_list conf
            (gc_state_r4_fupd (K []) (gc_state_h2_fupd (K []) state)) ys
            in
          (ys',gc_state_r4_fupd (K (gc_state_r4 state' ++
            gc_state_r4 state)) (gc_state_h2_fupd (K (gc_state_h2
            state ++ gc_state_h2 state')) state')))`)
  CHEAT_TAC;;

let gen_gc_gc_move_list_APPEND_lemma =
  cake_theorem "gc_move_list_APPEND_lemma[local]"
  (fun () ->
    `!ys state.
       (gen_gc_gc_move_list conf state ys = (ys',state')) ==>
         (?h2' r4'. (gc_state_h2 state' = gc_state_h2 state ++
           h2') /\ (gc_state_r4 state' = r4' ++ gc_state_r4 state))`)
  CHEAT_TAC;;

let gen_gc_heap_addresses_APPEND =
  cake_theorem "heap_addresses_APPEND[local]"
  (fun () ->
    `!xs ys n. heap_addresses n (xs ++ ys) =
               heap_addresses n xs UNION heap_addresses (n +
                 heap_length xs) ys`)
  CHEAT_TAC;;

let heap_addresses_APPEND_IN =
  cake_theorem "heap_addresses_APPEND_IN[local]"
  (fun () ->
    `!xs ys n j.
       j IN heap_addresses n (xs ++ ys) ==>
       j IN heap_addresses n xs \/ j IN heap_addresses (n +
         heap_length xs) ys`)
  CHEAT_TAC;;

let GREATER_IMP_heap_lookup =
  cake_theorem "GREATER_IMP_heap_lookup[local]"
  (fun () ->
    `!ys xs j.
     (heap_length (xs ++ ys) <= j + heap_length ys) ==>
     (heap_lookup j (xs ++ ys) = heap_lookup (j - heap_length xs)
       ys)`)
  CHEAT_TAC;;

let heap_lookup_IMP_MEM = cake_theorem "heap_lookup_IMP_MEM"
  (fun () ->
    `!x n y. (heap_lookup n x = SOME y) ==> MEM y x`)
  CHEAT_TAC;;

let gen_gc_heaps_similar_lemma = cake_theorem "heaps_similar_lemma"
  (fun () ->
    `!h1 h2 ptr.
        heaps_similar h1 h2 /\ isSomeDataElement (heap_lookup ptr
          h1) ==>
        isSomeDataOrForward (heap_lookup ptr h2)`)
  CHEAT_TAC;;

let BIJ_IMP_FLOOKUP_SOME = cake_theorem "BIJ_IMP_FLOOKUP_SOME"
  (fun () ->
    `!s h j.
        BIJ (heap_map1 h) (FDOM (heap_map 0 h)) s /\ j IN s ==>
        (?i. FLOOKUP (heap_map 0 h) i = SOME j)`)
  CHEAT_TAC;;

let heap_lookup_IMP_heap_addresses_GEN =
  cake_theorem "heap_lookup_IMP_heap_addresses_GEN[local]"
  (fun () ->
    `!xs n x j. (heap_lookup j xs = SOME x) ==> n + j IN
  heap_addresses n xs`)
  CHEAT_TAC;;

(* in gc_inv or prove lemma here *)
let pointers_ok = cake_theorem "pointers_ok[local]"
  (fun () ->
    `!state xs l d ptr u.
       gen_gc_gc_inv conf state heap0 roots0 /\
       (MEM (DataElement xs l d) (gc_state_h2 state) \/ MEM
         (DataElement xs l d) (gc_state_r2 state)) /\
       MEM (gc_shared_Pointer ptr u) xs ==>
       isSomeDataOrForward (heap_lookup ptr (gc_state_heap
         state))`)
  CHEAT_TAC;;

let IMP_reachable_addresses = cake_theorem "IMP_reachable_addresses"
  (fun () ->
    `!i ptr u xs l d.
        reachable_addresses roots0 heap0 i /\ MEM
          (gc_shared_Pointer ptr u) xs /\
        (heap_lookup i heap0 = SOME (DataElement xs l d)) ==>
        reachable_addresses roots0 heap0 ptr`)
  CHEAT_TAC;;

let gc_move_data_thm = cake_theorem "gc_move_data_thm"
  (fun () ->
    `!conf state.
        gen_gc_gc_inv conf state heap0 roots0 /\
        (gc_state_r3 state = []) /\ (gc_state_r2 state = []) ==>
        (?state'.
          (gen_gc_gc_move_data conf state = state') /\
          ((heap_map 0 (gc_state_heap state)) SUBMAP (heap_map 0
            (gc_state_heap state'))) /\
          gen_gc_gc_inv conf state' heap0 roots0 /\
          (gc_state_h2 state' = []) /\ (gc_state_r3 state' = [])
            /\ (gc_state_r2 state' = []))`)
  CHEAT_TAC;;

let gc_move_refs_lemma = cake_theorem "gc_move_refs_lemma"
  (fun () ->
    `!state l n b xs' t state'.
        gen_gc_gc_inv conf state heap0 roots0 /\
        (gc_state_r2 state = DataElement l n b :: t) /\
        (gen_gc_gc_move_list conf state l = (xs',state')) /\
        (!ptr u. MEM (gc_shared_Pointer ptr u) l ==>
          isSomeDataOrForward (heap_lookup ptr (gc_state_heap
            state)) /\
          reachable_addresses roots0 heap0 ptr) ==>
        gen_gc_gc_inv conf
          (gc_state_r2_fupd (K t) (gc_state_r3_fupd (K (gc_state_r3
            state' ++ [DataElement xs' n b])) state'))
          heap0 roots0`)
  CHEAT_TAC;;

let gc_move_refs_thm = cake_theorem "gc_move_refs_thm"
  (fun () ->
    `!conf state.
        gen_gc_gc_inv conf state heap0 roots0 ==>
        (?state'.
          (gc_move_refs conf state = state') /\
          ((heap_map 0 (gc_state_heap state)) SUBMAP (heap_map 0
            (gc_state_heap state'))) /\
          gen_gc_gc_inv conf state' heap0 roots0 /\
          (gc_state_r3 state' = []) /\ (gc_state_r2 state' = []) /\
          (0 < heap_length (gc_state_r3 state) ==> heap_length
            (gc_state_r1 state) < heap_length (gc_state_r1 state')))`)
  CHEAT_TAC;;

let gc_move_list_heap_length =
  cake_theorem "gc_move_list_heap_length[local]"
  (fun () ->
    `!conf state state' xs ys.
       (gen_gc_gc_move_list conf state xs = (ys,state')) ==>
       (heap_length (gc_state_h1 state) <= heap_length (gc_state_h1
         state')) /\
       (heap_length (gc_state_r1 state) <= heap_length
         (gc_state_r1 state'))`)
  CHEAT_TAC;;

let gc_move_data_heap_length =
  cake_theorem "gc_move_data_heap_length[local]"
  (fun () ->
    `!conf state state'.
       Abbrev (state' = gen_gc_gc_move_data conf state) ==>
       heap_length (gc_state_h1 state) <= heap_length (gc_state_h1
         state') /\
       heap_length (gc_state_r1 state) <= heap_length
         (gc_state_r1 state')`)
  CHEAT_TAC;;

let gc_move_refs_heap_length =
  cake_theorem "gc_move_refs_heap_length[local]"
  (fun () ->
    `!conf state state'.
       (gc_move_refs conf state = state') ==>
       heap_length (gc_state_h1 state) <= heap_length (gc_state_h1
         state') /\
       heap_length (gc_state_r1 state) <= heap_length
         (gc_state_r1 state')`)
  CHEAT_TAC;;

let gc_move_loop_gc_inv = cake_theorem "gc_move_loop_gc_inv[local]"
  (fun () ->
    `!conf state h t.
       gen_gc_gc_inv conf state heap0 roots0 /\ (gc_state_r2 state
         = []) /\ (gc_state_r4 state = h :: t) /\
       (gc_state_r3 state = []) ==>
       gen_gc_gc_inv conf (gc_state_r4_fupd (K [])
         (gc_state_r2_fupd (K (h :: t)) state)) heap0 roots0`)
  CHEAT_TAC;;

let reachable_addresses_gc_inv_r4 =
  cake_theorem "reachable_addresses_gc_inv_r4[local]"
  (fun () ->
    `gen_gc_gc_inv conf state heap roots0 /\
     (gc_state_r4 state = DataElement l n b :: t) /\ MEM
       (gc_shared_Pointer ptr u) l ==>
     reachable_addresses roots0 heap ptr`)
  CHEAT_TAC;;

let gen_gc_gc_move_loop_thm = cake_theorem "gc_move_loop_thm"
  (fun () ->
    `!conf state clock. gen_gc_conf_limit
        conf <= clock + heap_length (gc_state_h1 state) +
          heap_length (gc_state_r1 state) /\
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
            (gc_state_r2 state' = []))`)
  CHEAT_TAC;;

let gen_gc_gc_inv_init = cake_theorem "gc_inv_init"
  (fun () ->
    `heap_ok heap (gen_gc_conf_limit conf) ==>
      gen_gc_gc_inv conf (gc_state_ok_fupd (K (heap_length heap =
        gen_gc_conf_limit conf)) (gc_state_n_fupd (K
        (gen_gc_conf_limit conf)) (gc_state_heap_fupd (K heap)
        empty_state))) heap roots`)
  CHEAT_TAC;;

let gen_gc_thm = cake_theorem "gen_gc_thm"
  (fun () ->
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
        (gc_state_r2 state = []))`)
  CHEAT_TAC;;

let gen_gc_LESS_IMP_heap_lookup = cake_theorem "LESS_IMP_heap_lookup"
  (fun () ->
    `!xs j ys. j < heap_length xs ==> (heap_lookup j (xs ++ ys) =
  heap_lookup j xs)`)
  CHEAT_TAC;;

(* HOL4 gen_gcScript.sml:1619-1623: a theorem that HOL4 states as the
   value of an ML expression *)

let heap_lookup_AND_APPEND_IMP =
  cake_theorem "heap_lookup_AND_APPEND_IMP[local]"
  (fun () ->
    `!xs n ys d d1.
       (heap_lookup n xs = SOME d) /\
       (heap_lookup n (xs ++ ys) = SOME d1) ==> (d1 = d)`)
  CHEAT_TAC;;

let heap_lookup_AND_PREPEND_IMP =
  cake_theorem "heap_lookup_AND_PREPEND_IMP[local]"
  (fun () ->
    `!n xs ys d d1.
       (heap_lookup n ys = SOME d) /\
       (heap_lookup (heap_length xs + n) (xs ++ ys) = SOME d1) ==>
       (d1 = d)`)
  CHEAT_TAC;;

let MEM_heap_expand_FALSE = cake_theorem "MEM_heap_expand_FALSE[local]"
  (fun () ->
    `!n. ~(MEM (DataElement xs l d) (heap_expand n))`)
  CHEAT_TAC;;

let FILTER_isForward_heap_expand_lemma =
  cake_theorem "FILTER_isForward_heap_expand_lemma[local]"
  (fun () ->
    `!n. FILTER isForwardPointer' (heap_expand n) = []`)
  CHEAT_TAC;;

let heap_lookup_CONS_IMP = cake_theorem "heap_lookup_CONS_IMP[local]"
  (fun () ->
    `(heap_lookup j ys = SOME z) ==>
     (heap_lookup (j + heap_length [x]) (x :: ys) = SOME z)`)
  CHEAT_TAC;;

let heap_lookup_PREPEND_EXTEND =
  cake_theorem "heap_lookup_PREPEND_EXTEND[local]"
  (fun () ->
    `!xs j ys z.
     (heap_lookup j ys = SOME z) ==>
     (heap_lookup (heap_length xs + j) (xs ++ ys) = SOME z)`)
  CHEAT_TAC;;

let gen_gc_ok = cake_theorem "gen_gc_ok"
  (fun () ->
    `!conf roots heap.
      roots_ok roots heap /\ heap_ok (heap:(('a,'b)heap_element)
        list) (gen_gc_conf_limit conf) ==>
      (?state roots' heap'.
        (heap' = gc_state_h1 state ++ heap_expand (gc_state_n
          state) ++ gc_state_r1 state) /\
        (gen_gc conf ((roots:('a heap_address) list),heap) =
          (roots',state)) /\ gc_state_ok
        state /\
        (gc_state_a state = heap_length (gc_state_h1 state)) /\
        roots_ok roots' heap' /\
        heap_ok heap' (gen_gc_conf_limit conf))`)
  CHEAT_TAC;;

let IN_heap_addresses_LESS =
  cake_theorem "IN_heap_addresses_LESS[local]"
  (fun () ->
    `!heap n k. n IN heap_addresses k heap ==> k <= n /\ n < k +
  heap_length heap`)
  CHEAT_TAC;;

let gen_gc_heap_lookup_EXTEND = cake_theorem "heap_lookup_EXTEND"
  (fun () ->
    `!xs n ys x. (heap_lookup n xs = SOME x) ==>
                  (heap_lookup n (xs ++ ys) = SOME x)`)
  CHEAT_TAC;;

let gen_gc_related = cake_theorem "gen_gc_related"
  (fun () ->
    `!conf roots heap.
      roots_ok roots heap /\ heap_ok (heap:(('a,'b)heap_element)
        list) (gen_gc_conf_limit conf) ==>
      (?state f.
        (gen_gc conf ((roots:('a heap_address) list),heap) =
           (ADDR_MAP (FAPPLY f) roots,state)) /\
        (FDOM f = reachable_addresses roots heap) /\
        (FRANGE f = {a | isSomeDataElement (heap_lookup a
          (gc_state_h1 state ++ heap_expand (gc_state_n state) ++
          gc_state_r1 state))}) /\
        (heap_length (gc_state_h1 state ++ gc_state_r1 state) =
         heap_length (heap_filter (FDOM f) heap)) /\
        gc_related f heap (gc_state_h1 state ++ heap_expand
          (gc_state_n state) ++ gc_state_r1 state) /\
        EVERY isDataElement (gc_state_h1 state ++ gc_state_r1
          state))`)
  CHEAT_TAC;;

let gen_gc_gc_forward_ptr_ok = cake_theorem "gc_forward_ptr_ok"
  (fun () ->
    `!heap n a d c x. (gc_forward_ptr n heap a d c = (x,T)) ==> c`)
  CHEAT_TAC;;

let gen_gc_gc_move_ok = cake_theorem "gc_move_ok"
  (fun () ->
    `(gen_gc_gc_move conf state x = (x',state')) /\ gc_state_ok state'
  ==> gc_state_ok state`)
  CHEAT_TAC;;

let gen_gc_gc_move_list_ok = cake_theorem "gc_move_list_ok"
  (fun () ->
    `!xs xs' state state'.
        (gen_gc_gc_move_list conf state xs = (xs',state')) /\
          gc_state_ok state' ==> gc_state_ok
        state`)
  CHEAT_TAC;;

let gc_move_data_ok = cake_theorem "gc_move_data_ok"
  (fun () ->
    `!conf s. gc_state_ok (gen_gc_gc_move_data conf s) ==> gc_state_ok
  s`)
  CHEAT_TAC;;

let gc_move_data_h2 = cake_theorem "gc_move_data_h2"
  (fun () ->
    `!conf s. gc_state_ok (gen_gc_gc_move_data conf s) ==>
               (gc_state_h2 (gen_gc_gc_move_data conf s) = [])`)
  CHEAT_TAC;;

let gc_move_refs_ok = cake_theorem "gc_move_refs_ok"
  (fun () ->
    `!conf s. gc_state_ok (gc_move_refs conf s) ==> gc_state_ok s`)
  CHEAT_TAC;;

let gc_move_loop_ok = cake_theorem "gc_move_loop_ok"
  (fun () ->
    `!conf s c. gc_state_ok (gen_gc_gc_move_loop conf s c) ==>
  gc_state_ok s`)
  CHEAT_TAC;;

let gc_move_list_length = cake_theorem "gc_move_list_length"
  (fun () ->
    `!xs xs' state state'.
        (gen_gc_gc_move_list conf state xs = (xs',state')) ==>
        (LENGTH xs' = LENGTH xs)`)
  CHEAT_TAC;;

let gen_gc_LENGTH = cake_theorem "gen_gc_LENGTH"
  (fun () ->
    `(gen_gc c (xs,heap) = (ys,s)) ==> (LENGTH ys = LENGTH xs)`)
  CHEAT_TAC;;

let gen_gc_a = cake_theorem "gen_gc_a"
  (fun () ->
    `(gen_gc c (xs,heap) = (ys,s1)) /\ gc_state_ok s1 /\
      roots_ok xs heap /\ heap_ok heap (gen_gc_conf_limit c) ==>
      (gc_state_a s1 = heap_length (gc_state_h1 s1))`)
  CHEAT_TAC;;
