(* ======================================================== *)
(*  gc_shared: ported from HOL4's
    compiler/backend/gc/gc_sharedScript.sml  *)
(* ======================================================== *)

(*
  Types, functions and lemmas that are shared between GC definitions
*)

needs "compiler/backend/backend_passes.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "lib/integer_word.ml";;
needs "semantics/typeSystem.ml";;
(* HOL4 ancestors outside the port: finite_map words *)

(* The ML heap is represented as a list of heap_elements. *)

let heap_address_INDUCT,heap_address_RECURSION = define_datatype
  "heap_address = gc_shared_Pointer (num) ('a) | gc_shared_Data ('a)";;
hol4_overload "Data" "gc_shared_Data";;

let heap_element_INDUCT,heap_element_RECURSION = define_datatype
  "heap_element = Unused (num) | ForwardPointer (num) ('a) (num) | \
   DataElement (('a heap_address) list) (num) ('b)";;


let gc_state_FIELDS = define_record "gc_state"
  ["old","(('a,'b)heap_element) list";
   "h1","(('a,'b)heap_element) list";
   "h2","(('a,'b)heap_element) list";
   "r4","(('a,'b)heap_element) list";
   "r3","(('a,'b)heap_element) list";
   "r2","(('a,'b)heap_element) list";
   "r1","(('a,'b)heap_element) list";
   "a","num";
   "n","num";
   "ok","bool";
   "heap","(('a,'b)heap_element) list";
   "heap0","(('a,'b)heap_element) list"];;

let empty_state_def = cake_define
  `empty_state =
     mk_gc_state [] [] [] [] [] [] [] 0 0 T [] []`;;

(* The heap is accessed using the following lookup function. *)

let el_length_def = cake_define
  `(el_length (Unused l) = l + 1) /\
   (el_length (ForwardPointer n d l) = l + 1) /\
   (el_length (DataElement xs l data) = l + 1)`;;

let heap_length_def = cake_define
  `heap_length heap = SUM (MAP el_length heap)`;;

let heap_lookup_def = cake_define
  `(heap_lookup a [] = NONE) /\
   (heap_lookup a (x :: xs) =
      (if a = 0 then SOME x else
      if a < el_length x then NONE else heap_lookup (a - el_length
        x) xs))`;;

let heap_split_def = cake_define
  `(heap_split a [] = (if a = 0 then SOME ([],[]) else NONE)) /\
   (heap_split a (el :: heap) =
     (if a = 0 then SOME ([],el :: heap) else
     if a < el_length el then NONE else
     match heap_split (a - el_length el) heap with NONE -> NONE |
       SOME (h1,h2) ->
       SOME (el :: h1,h2)))`;;

let heap_drop_def = cake_define
  `heap_drop n (heap:(('a,'b)heap_element) list) =
     (match heap_split n heap with NONE -> ARB | SOME (h1,h2) ->
       h2)`;;

let heap_take_def = cake_define
  `heap_take n (heap:(('a,'b)heap_element) list) =
     (match heap_split n heap with NONE -> ARB | SOME (h1,h2) ->
       h1)`;;

let heap_segment_def = cake_define
  `heap_segment (a,b) heap =
     (match heap_split a heap with NONE -> NONE | SOME (h1,heap') ->
       (if b < a then NONE else
       match heap_split (b - heap_length h1) heap' with NONE ->
         NONE | SOME (h2,h3) -> SOME (h1,h2,h3)))`;;

let heap_restrict_def = cake_define
  `heap_restrict start end (heap:(('a,'b)heap_element) list) =
      (match heap_segment (start,end) heap with NONE -> [] | SOME
        (h1,h2,h3) -> h2)`;;

(* The heap is well-formed if heap_ok *)

let isDataElement_def = cake_define
  `isDataElement x = (?ys l d. x = DataElement ys l d)`;;

let isSomeDataElement_def = cake_define
  `isSomeDataElement x = (?ys l d. x = SOME (DataElement ys l d))`;;

let isSomeForwardPointer_def = cake_define
  `isSomeForwardPointer x = (?ptr d l. x = SOME (ForwardPointer ptr d
  l))`;;

let isSomeDataOrForward_def = cake_define
  `isSomeDataOrForward x = (isSomeForwardPointer x \/
  isSomeDataElement x)`;;

let roots_ok_def = cake_define
  `roots_ok roots heap =
     (!ptr u. MEM (gc_shared_Pointer ptr u) roots ==>
       isSomeDataElement (heap_lookup ptr heap))`;;

let isForwardPointer_def = cake_define
  `isForwardPointer x1 =
        match x1 with
          (ForwardPointer n d l) -> T
        | _1 -> F`;;

let heap_ok_def = cake_define
  `heap_ok heap limit = (
     (heap_length heap = limit) /\
     (FILTER isForwardPointer heap = []) /\
     (!xs l d ptr u. MEM (DataElement xs l d) heap /\ MEM
       (gc_shared_Pointer ptr u) xs ==>
                     isSomeDataElement (heap_lookup ptr heap)))`;;

let gc_forward_ptr_def = cake_define
  `(gc_forward_ptr a [] ptr d ok = ([],F)) /\
   (gc_forward_ptr a (x :: xs) ptr d ok =
      (if a = 0 then
        (ForwardPointer ptr d ((el_length x) - 1) ::
          xs,(isDataElement x /\ ok)) else
      if a < el_length x then (x :: xs,F) else
        let (xs,ok) = gc_forward_ptr (a - el_length x) xs ptr d ok in
          (x :: xs,ok)))`;;

(*Theorem gc_forward_ptr_ok:
   !heap n a ok x. (gc_forward_ptr n heap a d ok = (x,T)) ==> ok
Proof
  Induct
  >- simp [gc_forward_ptr_def]
  \\ once_rewrite_tac [gc_forward_ptr_def]
  \\ ntac 5 strip_tac
  \\ IF_CASES_TAC
  >- (once_rewrite_tac [PAIR_EQ] \\ strip_tac \\ fs [])
  \\ IF_CASES_TAC
  >- metis_tac [PAIR_EQ]
  \\ rewrite_tac [LET_THM]
  \\ pairarg_tac
  \\ asm_rewrite_tac []
  \\ DISCH_TAC
  \\ fs []
  \\ qpat_x_assum `!n a ok x. _` (qspecl_then [`n - el_length
    h`,`a`,`ok`,`xs`] assume_tac)
  \\ fs []
QED*)

let heap_expand_def = cake_define
  `heap_expand n = (if n = 0 then [] else [Unused (n - 1)])`;;

let heap_map_def = cake_define
  `heap_map a x2 =
        match x2 with
          [] -> FEMPTY
        | (ForwardPointer ptr d l :: xs) ->
        heap_map (a + l + 1) xs |+ (a,ptr)
        | (x :: xs) -> heap_map (a + el_length x) xs`;;

let heap_map1_def = cake_define
  `heap_map1 heap = (\a. FAPPLY (heap_map 0 heap) a)`;;

let heap_addresses_def = cake_define
  `(heap_addresses a [] = {}) /\
   (heap_addresses a (x :: xs) = a INSERT heap_addresses (a +
     el_length x) xs)`;;

let ADDR_MAP_def = cake_define
  `(ADDR_MAP f [] = []) /\
   (ADDR_MAP f (Data x :: xs) = Data x :: ADDR_MAP f xs) /\
   (ADDR_MAP f (gc_shared_Pointer a d :: xs) = gc_shared_Pointer
     (f a) d :: ADDR_MAP f xs)`;;

let ADDR_APPLY_def = cake_define
  `(ADDR_APPLY f (gc_shared_Pointer x d) = gc_shared_Pointer (f x) d) /\
   (ADDR_APPLY f (Data y) = Data y)`;;

(* HOL4 ML code, not ported:
val _ = augment_srw_ss [rewrites [LIST_REL_def]];
*)

let heaps_similar_def = cake_define
  `heaps_similar heap0 heap =
     EVERY2 (\h0 h. if isForwardPointer h then
                      (el_length h = el_length h0) /\
                        isDataElement h0 else (h = h0)) heap0 heap`;;

(* --- *)

let gc_related_def = cake_define
  `gc_related (f:(num,num)fmap) heap1 heap2 = (
     INJ (FAPPLY f) (FDOM f) {a | isSomeDataElement (heap_lookup a
       heap2)} /\
     (!i. i IN FDOM f ==> isSomeDataElement (heap_lookup i heap1)) /\
     (!i xs l d.
       i IN FDOM f /\ (heap_lookup i heap1 = SOME (DataElement xs l
         d)) ==>
       (heap_lookup (FAPPLY f i) heap2 = SOME (DataElement (ADDR_MAP
         (FAPPLY f) xs) l d)) /\
       (!ptr u. MEM (gc_shared_Pointer ptr u) xs ==> ptr IN FDOM
         f)))`;;

(* an edge in the heap *)

let gc_edge_def = cake_define
  `gc_edge heap x y <=>
     (?xs l d t. (heap_lookup x heap = SOME (DataElement xs l d)) /\
                MEM (gc_shared_Pointer y t) xs)`;;

let reachable_addresses_def = cake_define
  `reachable_addresses roots heap y =
     (?t x. MEM (gc_shared_Pointer x t) roots /\ RTC (gc_edge
       heap) x y)`;;

let heap_filter_aux_def = cake_define
  `(heap_filter_aux n P [] = []) /\
   (heap_filter_aux n P (x :: xs) =
      (if n IN P then [x] else []) ++ heap_filter_aux (n +
        el_length x) P xs)`;;

let heap_filter_def = cake_define
  `heap_filter = heap_filter_aux 0`;;

(* HOL4 ML code, not ported:
val heap_filter_aux_ADD_SING = prove(
  ``!k n e heap.
      heap_filter_aux (k+n) {e+n} heap = heap_filter_aux k {e} heap``,
  Induct_on `heap`
  \\ fs [heap_filter_aux_def] \\ rw []
  \\ first_x_assum (qspecl_then [`k+el_length h`,`n`,`e`] mp_tac)
  \\ fs []) |> Q.SPEC `0` |> SIMP_RULE std_ss [];
*)
