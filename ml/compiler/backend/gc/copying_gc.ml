(* ======================================================== *)
(*  copying_gc: ported from HOL4's
    compiler/backend/gc/copying_gcScript.sml  *)
(* ======================================================== *)

(*
  The straightforward non-generational copying garbage collector.
*)

needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "lib/integer_word.ml";;
(* HOL4 ancestors outside the port: words *)

(* The GC is a copying collector which moves elements *)

let gc_move_def = cake_define_list
  [`copying_gc_gc_move (Data d,h2,a,n,heap,c,limit) = (Data
  d,h2,a,n,heap,c)`;
   `copying_gc_gc_move (Pointer ptr d,h2,a,n,heap,c,limit) =
         (match heap_lookup ptr heap with SOME (DataElement xs l dd)
           ->
             (let c = c /\ l + 1 <= n /\ (a + n = limit) in
             let n = n - (l + 1) in
             let h2 = h2 ++ [DataElement xs l dd] in
             let (heap,c) = gc_forward_ptr ptr heap a d c in
               (Pointer a d,h2,a + (l + 1),n,heap,c)) | SOME
                 (ForwardPointer ptr _3 l) -> (Pointer ptr
                 d,h2,a,n,heap,c) | _4 -> (ARB,h2,a,n,heap,F))`];;
hol4_overload "gc_move" "copying_gc_gc_move";;

let gc_move_list_def = cake_define_list
  [`copying_gc_gc_move_list ([],h2,a,n,heap,c,limit) =
  ([],h2,a,n,heap,c)`;
   `copying_gc_gc_move_list (x :: xs,h2,a,n,heap,c,limit) =
         (let (x,h2,a,n,heap,c) = gc_move (x,h2,a,n,heap,c,limit) in
         let (xs,h2,a,n,heap,c) = copying_gc_gc_move_list
           (xs,h2,a,n,heap,c,limit) in
           (x :: xs,h2,a,n,heap,c))`];;
hol4_overload "gc_move_list" "copying_gc_gc_move_list";;

let gc_move_loop_def = cake_define_list
  [`copying_gc_gc_move_loop (h1,[],a,n,heap,c,limit) =
  (h1,a,n,heap,c)`;
   `copying_gc_gc_move_loop (h1,h :: h2,a,n,heap,c,limit) =
         (if limit < heap_length (h1 ++ (h :: h2)) then
           (h1,a,n,heap,F) else
           match h with DataElement xs l d ->
              (let (xs,h2,a,n,heap,c) = gc_move_list (xs,h ::
                h2,a,n,heap,c,limit) in
              let c = c /\ ~(h2 = []) /\ (HD h2 = h) in
              let h2 = TL h2 in
              let h1 = h1 ++ [DataElement xs l d] in
                copying_gc_gc_move_loop (h1,h2,a,n,heap,c,limit))
                  | _6 -> (h1,a,n,heap,F))`];;
hol4_overload "gc_move_loop" "copying_gc_gc_move_loop";;

let full_gc_def = cake_define
  `full_gc (roots,heap,limit) =
     (let c0 = (heap_length heap = limit) in
     let (roots,h2,a,n,heap,c) = gc_move_list
       (roots,[],0,limit,heap,T,limit) in
     let (heap,a,n,temp,c) = gc_move_loop ([],h2,a,n,heap,c,limit) in
     let c = (c /\ (a = heap_length heap) /\ (heap_length temp =
       limit) /\
              c0 /\ (n = limit - a) /\ a <= limit) in
       (roots,heap,a,c))`;;

(* Invariant *)

(* HOL4 ML code, not ported:
val _ = augment_srw_ss [rewrites [LIST_REL_def]];
*)

let gc_inv_def = cake_define
  `copying_gc_gc_inv (h1,h2,a,n,heap,c,limit)
  (heap0:(('a,'b)heap_element) list) (roots0:('a heap_address) list) = (
     (a + n = limit) /\
     (a = heap_length (h1 ++ h2)) /\
     (n = heap_length (FILTER (\h. ~(isForwardPointer h)) heap)) /\ c
       /\
     (heap_length heap = limit) /\
     heap_ok heap0 limit /\
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
                    (!ptr d. MEM (Pointer ptr d) xs /\ j <
                      heap_length h1 ==>
                            ptr IN FDOM (heap_map 0 heap)))))`;;
hol4_overload "gc_inv" "copying_gc_gc_inv";;

(* Invariant maintained *)

(* HOL4 ML code, not ported:
val NOT_IN_heap_addresses = Q.prove(
  `!xs n. ~(n + heap_length xs IN heap_addresses n xs)`,
  Induct \\ full_simp_tac (srw_ss())
    [heap_addresses_def,APPEND,heap_length_def]
  \\ full_simp_tac (srw_ss()) [EXTENSION] \\ rpt strip_tac
  \\ full_simp_tac std_ss [ADD_ASSOC]
  THEN1 (Cases_on `h` \\ EVAL_TAC \\ decide_tac) \\ metis_tac [])
  |> Q.SPECL [`xs`,`0`] |> SIMP_RULE std_ss [];
*)

(* HOL4 ML code, not ported:
val APPEND_NIL_LEMMA = METIS_PROVE [APPEND_NIL] ``?xs1. xs = xs ++
  xs1:'a list``
*)

(* HOL4 ML code, not ported:
val heap_lookup_IMP_heap_addresses = Q.prove(
  `!xs n x j. (heap_lookup j xs = SOME x) ==> n + j IN heap_addresses n
    xs`,
  Induct \\ full_simp_tac std_ss
    [MEM,heap_lookup_def,heap_addresses_def]
  \\ SRW_TAC [] [] \\ res_tac
  \\ pop_assum (mp_tac o Q.SPEC `n + el_length h`)
  \\ `n + el_length h + (j - el_length h) = n + j` by decide_tac
  \\ metis_tac []) |> Q.SPECL [`xs`,`0`] |> SIMP_RULE std_ss [] |>
    GEN_ALL;
*)

(* Lemmas about ok and a *)

(* HOL4 ML code, not ported:
val th =
  fetch "-" "gc_move_loop_ind" |> Q.SPEC `(\(h1,h2,a,n,heap,c,limit).
     !xs' h1' a' n' heap' c'.
       (gc_move_loop (h1,h2,a,n,heap,c,limit) = (h1',a',n',heap',T)) ==>
       c)`
*)

(* HOL4 ML code, not ported:
val lemma = prove(th |> concl |> dest_imp |> fst,
  rpt strip_tac \\ simp_tac std_ss [gc_move_loop_def]
  \\ rpt strip_tac \\ pop_assum mp_tac
  \\ Cases_on `limit < heap_length (h1 ++ h::h2)`
  \\ asm_rewrite_tac [] \\ simp_tac std_ss []
  \\ Cases_on `h` \\ simp_tac (srw_ss()) []
  \\ `?x1 x2 x3 x4 x5 x6.
        gc_move_list (l,DataElement l n'' b::h2,a,n,heap,c,limit) =
          (x1,x2,x3,x4,x5,x6)` by metis_tac [PAIR]
  \\ asm_rewrite_tac [] \\ simp_tac std_ss [LET_DEF]
  \\ qpat_x_assum `!xs.bbb` mp_tac
  \\ CONV_TAC (RATOR_CONV (SIMP_CONV (srw_ss()) []))
  \\ asm_rewrite_tac [] \\ simp_tac std_ss [LET_DEF] \\ rpt strip_tac
  \\ res_tac \\ full_simp_tac std_ss [] \\ imp_res_tac gc_move_list_ok)
*)

(* HOL4 ML code, not ported:
val th = MP th lemma |> SIMP_RULE std_ss []
         |> Q.SPECL
           [`h1`,`h2`,`a`,`n`,`heap`,`c`,`limit`,`h1'`,`a'`,`n'`
           ,`heap'`]
*)
