(* ======================================================== *)
(*  gen_gc: ported from HOL4's
    compiler/backend/gc/gen_gcScript.sml  *)
(* ======================================================== *)

(*
  The major collection of the generational copying garbage collector.
*)

needs "compiler/backend/gc/gc_shared.ml";;
needs "lib/integer_word.ml";;
(* HOL4 ancestors outside the port: words *)

(* HOL4 ML code, not ported:
val gc_state_component_equality = DB.fetch "gc_shared"
  "gc_state_component_equality";
*)

(* Copying GC which moves references to the end of the heap. This
   implementation is a pre-stage to the generational GC. *)

let gen_gc_conf_FIELDS = define_record "gen_gc_conf"
  ["limit","num";
   "isRef","'a->bool"];;
hol4_overload "limit" "gen_gc_conf_limit";;
hol4_overload "limit_fupd" "gen_gc_conf_limit_fupd";;
hol4_overload "isRef" "gen_gc_conf_isRef";;
hol4_overload "isRef_fupd" "gen_gc_conf_isRef_fupd";;

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

let gc_move_list_def = cake_define_list
  [`gen_gc_gc_move_list conf state [] = ([],state)`;
   `gen_gc_gc_move_list conf state (x :: xs) =
        (let (x,state) = gen_gc_gc_move conf state x in
        let (xs,state) = gen_gc_gc_move_list conf state xs in
          (x :: xs,state))`];;
hol4_overload "gc_move_list" "gen_gc_gc_move_list";;

(* HOL4 termination: \\ rw [heap_length_def,el_length_def,SUM_APPEND]
   \\ imp_res_tac (GSYM gc_move_list_IMP) \\ fs [] \\ decide_tac *)
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

(* HOL4 termination: \\ rw [heap_length_def,el_length_def,SUM_APPEND]
   \\ decide_tac *)
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

(* HOL4 ML code, not ported:
val full_simp = full_simp_tac std_ss
*)

(* HOL4 ML code, not ported:
val isSomeDataOrForward_lemma_expanded =
  isSomeDataOrForward_lemma
  |> SIMP_RULE std_ss
    [isSomeDataOrForward_def,isSomeDataElement_def
    ,isSomeForwardPointer_def];
*)

(* val NOT_IN_heap_addresses = *)
(*   NOT_IN_heap_addresses_general |> Q.SPECL [`xs`,`0`] |> SIMP_RULE
   std_ss []; *)

(* in gc_inv or prove lemma here *)
