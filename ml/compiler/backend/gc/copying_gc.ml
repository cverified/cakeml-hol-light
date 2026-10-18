(* ======================================================== *)
(*  copying_gc: ported from HOL4's
    compiler/backend/gc/copying_gcScript.sml  *)
(* ======================================================== *)

(*
  The straightforward non-generational copying garbage collector.
*)

needs "compiler/backend/gc/gc_shared.ml";;
needs "lib/integer_word.ml";;
(* HOL4 ancestors outside the port: words *)

(* The GC is a copying collector which moves elements *)

let gc_move_def = cake_define_list
  [`copying_gc_gc_move (gc_shared_Data d,h2,a,n,heap,c,limit') =
  ((gc_shared_Data d:'a heap_address),h2,a,n,heap,c)`;
   `copying_gc_gc_move (gc_shared_Pointer ptr d,h2,a,n,heap,c,limit') =
         (match heap_lookup ptr heap with SOME (DataElement xs l dd)
           ->
             (let c = (c /\ l + 1 <= n /\ (a + n = limit')) in
             let n = n - (l + 1) in
             let h2 = h2 ++ [DataElement xs l dd] in
             let (heap,c) = gc_forward_ptr ptr heap a d c in
               (gc_shared_Pointer a d,h2,a + (l + 1),n,heap,c))
                 | SOME (ForwardPointer ptr _3 l) ->
                 (gc_shared_Pointer ptr d,h2,a,n,heap,c) | _4 ->
                 (ARB,h2,a,n,heap,F))`];;
hol4_overload "gc_move" "copying_gc_gc_move";;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let gc_move_list_def = cake_define_list_cheat CHEAT_TAC
  [`copying_gc_gc_move_list ([],h2,a,n,heap,c,limit') =
  ([],h2,a,n,heap,c)`;
   `copying_gc_gc_move_list (x :: xs,h2,a,n,heap,c,limit') =
         (let (x,h2,a,n,heap,c) = copying_gc_gc_move
           (x,h2,a,n,heap,c,limit') in
         let (xs,h2,a,n,heap,c) = copying_gc_gc_move_list
           (xs,h2,a,n,heap,c,limit') in
           (x :: xs,h2,a,n,heap,c))`];;
hol4_overload "gc_move_list" "copying_gc_gc_move_list";;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 copying_gcScript.sml:50-53: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let gc_move_loop_def = cake_define_list_try_tac (fun () ->
  `MEASURE (\(h1,h2,a,n,heap,c,limit'). limit' - heap_length h1)`)
  CHEAT_TAC
  [`copying_gc_gc_move_loop (h1,[],a,n,heap,c,limit') =
  (h1,a,n,heap,c)`;
   `copying_gc_gc_move_loop (h1,h :: h2,a,n,heap,c,limit') =
         (if limit' < heap_length (h1 ++ (h :: h2)) then
           (h1,a,n,heap,F) else
           match h with DataElement xs l d ->
              (let (xs,h2,a,n,heap,c) = copying_gc_gc_move_list
                (xs,h :: h2,a,n,heap,c,limit') in
              let c = (c /\ ~(h2 = []) /\ (HD h2 = h)) in
              let h2 = TL h2 in
              let h1 = h1 ++ [DataElement xs l d] in
                copying_gc_gc_move_loop
                  (h1,h2,a,n,heap,c,limit')) | _6 ->
                  (h1,a,n,heap,F))`];;
hol4_overload "gc_move_loop" "copying_gc_gc_move_loop";;

let full_gc_def = cake_define
  `full_gc (roots,heap,limit') =
     (let c0 = (heap_length heap = limit') in
     let (roots,h2,a,n,heap,c) = copying_gc_gc_move_list
       (roots,[],0,limit',heap,T,limit') in
     let (heap,a,n,temp,c) = copying_gc_gc_move_loop
       ([],h2,a,n,heap,c,limit') in
     let c = (c /\ (a = heap_length heap) /\ (heap_length temp =
       limit') /\
              c0 /\ (n = limit' - a) /\ a <= limit') in
       (roots,heap,a,c))`;;

(* Invariant *)

(* HOL4 copying_gcScript.sml:67: ML code, not ported *)

let gc_inv_def = cake_define
  `copying_gc_gc_inv (h1,h2,a,n,heap,c,limit')
  (heap0:(('a,'b)heap_element) list) (roots0:('a heap_address) list) = (
     (a + n = limit') /\
     (a = heap_length (h1 ++ h2)) /\
     (n = heap_length (FILTER (\h. ~(isForwardPointer h)) heap)) /\ c
       /\
     (heap_length heap = limit') /\
     heap_ok heap0 limit' /\
     heaps_similar heap0 heap /\
     EVERY isDataElement h1 /\ EVERY isDataElement h2 /\
     BIJ (heap_map1 heap) (FDOM (heap_map 0 heap)) (heap_addresses 0
       (h1 ++ h2)) /\
     (!i j. (FLOOKUP (heap_map 0 heap) i = SOME j) ==>
           (?xs l d. (heap_lookup i heap0 = SOME (DataElement xs l
             d)) /\
                    (heap_lookup j (h1 ++ h2) =
                      SOME (DataElement (if j < heap_length h1 then
                              ADDR_MAP (heap_map1 heap) xs else xs) l
                                d)) /\
                    reachable_addresses roots0 heap0 i /\
                    (!ptr d. MEM (gc_shared_Pointer ptr d) xs /\ j <
                      heap_length h1 ==>
                            ptr IN FDOM (heap_map 0 heap)))))`;;
hol4_overload "gc_inv" "copying_gc_gc_inv";;

(* Invariant maintained *)

(* HOL4 copying_gcScript.sml:126-132: a proof *)

(* HOL4 copying_gcScript.sml:247: the ML values that the definitions
   below antiquote *)

(* HOL4 copying_gcScript.sml:411-417: a proof *)

(* Lemmas about ok and a *)

(* HOL4 copying_gcScript.sml:598-602: ML code, not ported *)

(* HOL4 copying_gcScript.sml:604-617: a proof *)

(* HOL4 copying_gcScript.sml:619-620: ML code, not ported *)
