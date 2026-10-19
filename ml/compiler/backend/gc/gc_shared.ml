(* ======================================================== *)
(*  gc_shared: ported from HOL4's
    compiler/backend/gc/gc_sharedScript.sml
    A definition theory, with 29 definitions, 3 datatypes and 53
    theorems.  Needed by 10 files of the port.  *)
(* ======================================================== *)

(*
  Types, functions and lemmas that are shared between GC definitions
*)

needs "lib/integer_word.ml";;
(* HOL4 ancestors outside the port: finite_map words *)

(* The ML heap is represented as a list of heap_elements. *)

let heap_address_INDUCT,heap_address_RECURSION = define_datatype
  "heap_address = gc_shared_Pointer (num) ('a) | gc_shared_Data ('a)";;
hol4_overload "Pointer" "gc_shared_Pointer";;
hol4_overload "Data" "gc_shared_Data";;

let heap_element_INDUCT,heap_element_RECURSION = define_datatype
  "heap_element = Unused (num) | ForwardPointer (num) ('a) (num) | \
   DataElement (('a heap_address) list) (num) ('b)";;


let gc_state_FIELDS = define_record "gc_state"
  ["old","(('a,'b)heap_element) list";
   (* old generations *)
   "h1","(('a,'b)heap_element) list";
   (* final left heap *)
   "h2","(('a,'b)heap_element) list";
   (* not updated left heap *)
   "r4","(('a,'b)heap_element) list";
   (* not updated right heap *)
   "r3","(('a,'b)heap_element) list";
   (* temp. final right heap *)
   "r2","(('a,'b)heap_element) list";
   (* temp. not updated right heap *)
   "r1","(('a,'b)heap_element) list";
   (* final right heap *)
   "a","num";
   (* gen_start + heap_length (h1 ++ h2) *)
   "n","num";
   (* unused heap space *)
   "ok","bool";
   (* OK *)
   "heap","(('a,'b)heap_element) list";
   (* old heap (w/ fwd pointers) *)
   "heap0","(('a,'b)heap_element) list"
   (* old heap *)
  ];;

let empty_state_def = cake_define
  `empty_state =
     mk_gc_state [] [] [] [] [] [] [] 0 0 T [] []`;;

(* The heap is accessed using the following lookup function. *)

let el_length_def = cake_define_list
  [`el_length (Unused l) = l + 1`;
   `el_length (ForwardPointer n d l) = l + 1`;
   `el_length (DataElement xs l data) = l + 1`];;

let el_length_NOT_0 = cake_theorem "el_length_NOT_0"
  (fun () ->
    `!el. ~(el_length el = 0)`)
  CHEAT_TAC;;

let el_length_GT_0 = cake_theorem "el_length_GT_0"
  (fun () ->
    `!el. 1 <= el_length el`)
  CHEAT_TAC;;

let heap_length_def = cake_define
  `heap_length heap = SUM (MAP el_length heap)`;;

let heap_length_NIL = cake_theorem "heap_length_NIL[simp]"
  (fun () ->
    `heap_length [] = 0`)
  CHEAT_TAC;;

let heap_length_GTE = cake_theorem "heap_length_GTE"
  (fun () ->
    `!heap. 0 <= heap_length heap`)
  CHEAT_TAC;;

let heap_length_APPEND = cake_theorem "heap_length_APPEND"
  (fun () ->
    `heap_length (xs ++ ys) = heap_length xs + heap_length ys`)
  CHEAT_TAC;;

let heap_lookup_def = cake_define_list
  [`heap_lookup a [] = NONE`;
   `heap_lookup a (x :: xs) =
         (if a = 0 then SOME x else
         if a < el_length x then NONE else heap_lookup (a -
           el_length x) xs)`];;

let heap_lookup_MEM = cake_theorem "heap_lookup_MEM"
  (fun () ->
    `!heap n x. (heap_lookup n heap = SOME x) ==> MEM x heap`)
  CHEAT_TAC;;

let MEM_IMP_heap_lookup = cake_theorem "MEM_IMP_heap_lookup"
  (fun () ->
    `!xs x. MEM x xs ==> (?j. (heap_lookup j xs = SOME x))`)
  CHEAT_TAC;;

let heap_lookup_LESS = cake_theorem "heap_lookup_LESS"
  (fun () ->
    `!xs n. (heap_lookup n xs = SOME x) ==> n < heap_length xs`)
  CHEAT_TAC;;

let heap_split_def = cake_define_list
  [`heap_split a [] = (if a = 0 then SOME ([],[]) else NONE)`;
   `heap_split a (el :: heap) =
        (if a = 0 then SOME ([],el :: heap) else
        if a < el_length el then NONE else
        match heap_split (a - el_length el) heap with NONE -> NONE |
          SOME (h1,h2) ->
          SOME (el :: h1,h2))`];;

let heap_lookup_SPLIT = cake_theorem "heap_lookup_SPLIT"
  (fun () ->
    `!heap n x. (heap_lookup n heap = SOME x) ==>
                 (?ha hb. (heap = ha ++ (x :: hb)) /\ (n =
                   heap_length ha))`)
  CHEAT_TAC;;

let heap_drop_def = cake_define
  `heap_drop n (heap:(('a,'b)heap_element) list) =
     (match heap_split n heap with NONE -> ARB | SOME (h1,h2) ->
       h2)`;;

let heap_take_def = cake_define
  `heap_take n (heap:(('a,'b)heap_element) list) =
     (match heap_split n heap with NONE -> ARB | SOME (h1,h2) ->
       h1)`;;

let heap_split_heap_length = cake_theorem "heap_split_heap_length"
  (fun () ->
    `!heap h1 h2 a.
      (heap_split a heap = SOME (h1,h2)) ==>
      (heap_length h1 = a) /\
      (heap_length (h1 ++ h2) = heap_length heap) /\
      (h1 ++ h2 = heap)`)
  CHEAT_TAC;;

let heap_segment_def = cake_define
  `heap_segment (a,b) heap =
     (match heap_split a heap with NONE -> NONE | SOME (h1,heap') ->
       (if b < a then NONE else
       match heap_split (b - heap_length h1) heap' with NONE ->
         NONE | SOME (h2,h3) -> SOME (h1,h2,h3)))`;;

let heap_segment_IMP = cake_theorem "heap_segment_IMP"
  (fun () ->
    `!heap a b h1 h2 h3.
      (heap_segment (a,b) heap = SOME (h1,h2,h3)) ==>
      (h1 ++ h2 ++ h3 = heap) /\
      (heap_length h1 = a) /\
      (heap_length (h1 ++ h2) = b) /\
      (heap_length h3 = (heap_length heap - b))`)
  CHEAT_TAC;;

let heap_restrict_def = cake_define
  `heap_restrict start' end (heap:(('a,'b)heap_element) list) =
      (match heap_segment (start',end) heap with NONE -> [] | SOME
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
          ForwardPointer n d l -> T
        | _1 -> F`;;

let heap_ok_def = cake_define
  `heap_ok heap limit' = (
     (heap_length heap = limit') /\
     (
      // no forward pointers
      FILTER isForwardPointer heap = []) /\
     (
      // all pointers in DataElements point to some DataElement
      !xs l d ptr u. MEM (DataElement xs l d) heap /\ MEM
        (gc_shared_Pointer ptr u) xs ==>
                     isSomeDataElement (heap_lookup ptr heap)))`;;

let gc_forward_ptr_def = cake_define_list
  [`// replace cell at a with a forwardpointer to ptr
    gc_forward_ptr a [] ptr d ok = ([],F)`;
   `gc_forward_ptr a (x :: xs) ptr d ok =
         (if a = 0 then
           (ForwardPointer ptr d ((el_length x) - 1) ::
             xs,(isDataElement x /\ ok)) else
         if a < el_length x then (x :: xs,F) else
           let (xs,ok) = gc_forward_ptr (a - el_length x) xs ptr d
             ok in
             (x :: xs,ok))`];;

let gc_forward_ptr_ok = cake_theorem "gc_forward_ptr_ok"
  (fun () ->
    `!heap n a c x. (gc_forward_ptr n heap a d c = (x,T)) ==> c`)
  CHEAT_TAC;;

let gc_forward_ptr_thm = cake_theorem "gc_forward_ptr_thm"
  (fun () ->
    `!ha. gc_forward_ptr (heap_length ha) (ha ++ (DataElement ys l d ::
  hb)) a u c =
           (ha ++ (ForwardPointer a u l :: hb),c)`)
  CHEAT_TAC;;

(* HOL4 gc_sharedScript.sml:309-327: code that the source has in a
   comment *)

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

let heap_addresses_def = cake_define_list
  [`heap_addresses a [] = {}`;
   `heap_addresses a (x :: xs) = a INSERT heap_addresses (a +
  el_length x) xs`];;

let ADDR_MAP_def = cake_define_list
  [`ADDR_MAP f [] = []`;
   `ADDR_MAP f (gc_shared_Data x :: xs) = (gc_shared_Data x:'a
  heap_address) :: ADDR_MAP f xs`;
   `ADDR_MAP f (gc_shared_Pointer a d :: xs) = gc_shared_Pointer (f
  a) d :: ADDR_MAP f xs`];;

let ADDR_MAP_EQ = cake_theorem "ADDR_MAP_EQ"
  (fun () ->
    `!xs. (!p d. MEM (gc_shared_Pointer p d) xs ==> (f p = g p)) ==>
           (ADDR_MAP f xs = ADDR_MAP g xs)`)
  CHEAT_TAC;;

let ADDR_MAP_LENGTH = cake_theorem "ADDR_MAP_LENGTH"
  (fun () ->
    `!xs f. LENGTH xs = LENGTH (ADDR_MAP f xs)`)
  CHEAT_TAC;;

let ADDR_MAP_APPEND = cake_theorem "ADDR_MAP_APPEND"
  (fun () ->
    `!h1 h2 f.
      ADDR_MAP f (h1 ++ h2) = ADDR_MAP f h1 ++ ADDR_MAP f h2`)
  CHEAT_TAC;;

let ADDR_APPLY_def = cake_define_list
  [`ADDR_APPLY f (gc_shared_Pointer x d) = gc_shared_Pointer (f x) d`;
   `ADDR_APPLY f (gc_shared_Data y) = (gc_shared_Data y:'a
  heap_address)`];;

(* HOL4 gc_sharedScript.sml:383-395: a theorem that HOL4 states as
   the value of an ML expression: heap_lookup_FLOOKUP *)

(* HOL4 gc_sharedScript.sml:397: ML code, not ported *)

let heaps_similar_def = cake_define
  `heaps_similar heap0 heap =
     EVERY2 (\h0 h. if isForwardPointer h then
                      (el_length h = el_length h0) /\
                        isDataElement h0 else (h = h0)) heap0 heap`;;

let IN_heap_map_IMP = cake_theorem "IN_heap_map_IMP"
  (fun () ->
    `!heap n k. n IN FDOM (heap_map k heap) ==> k <= n`)
  CHEAT_TAC;;

(* HOL4 gc_sharedScript.sml:414-423: a theorem that HOL4 states as
   the value of an ML expression: NOT_IN_heap_map *)

let isSomeDataOrForward_lemma = cake_theorem "isSomeDataOrForward_lemma"
  (fun () ->
    `!ha ptr.
        isSomeDataOrForward (heap_lookup ptr (ha ++ (DataElement ys
          l d :: hb))) <=>
        isSomeDataOrForward (heap_lookup ptr (ha ++
          [ForwardPointer a u l] ++ hb))`)
  CHEAT_TAC;;

let heaps_similar_IMP_heap_length =
  cake_theorem "heaps_similar_IMP_heap_length"
  (fun () ->
    `!xs ys. heaps_similar xs ys ==> (heap_length xs = heap_length ys)`)
  CHEAT_TAC;;

let heap_similar_Data_IMP = cake_theorem "heap_similar_Data_IMP"
  (fun () ->
    `heaps_similar heap0 (ha ++ (DataElement ys l d :: hb)) ==>
      (?ha0 hb0. (heap0 = ha0 ++ (DataElement ys l d :: hb0)) /\
                (heap_length ha = heap_length ha0))`)
  CHEAT_TAC;;

let heaps_similar_lemma = cake_theorem "heaps_similar_lemma"
  (fun () ->
    `!ha heap0.
        heaps_similar heap0 (ha ++ (DataElement ys l d :: hb)) ==>
        heaps_similar heap0 (ha ++ [ForwardPointer (heap_length
          (h1 ++ h2)) u l] ++ hb)`)
  CHEAT_TAC;;

let heap_lookup_PREFIX = cake_theorem "heap_lookup_PREFIX"
  (fun () ->
    `!xs. (heap_lookup (heap_length xs) (xs ++ (x :: ys)) = SOME x)`)
  CHEAT_TAC;;

let heap_lookup_EXTEND = cake_theorem "heap_lookup_EXTEND"
  (fun () ->
    `!xs n ys x. (heap_lookup n xs = SOME x) ==>
                  (heap_lookup n (xs ++ ys) = SOME x)`)
  CHEAT_TAC;;

let heap_map_APPEND = cake_theorem "heap_map_APPEND"
  (fun () ->
    `!xs n ys. (heap_map n (xs ++ ys)) =
                FUNION (heap_map n xs) (heap_map (n + heap_length
                  xs) ys)`)
  CHEAT_TAC;;

(* HOL4 gc_sharedScript.sml:493-500: a theorem that HOL4 states as
   the value of an ML expression: FDOM_heap_map *)

let heap_addresses_APPEND = cake_theorem "heap_addresses_APPEND"
  (fun () ->
    `!xs ys n. heap_addresses n (xs ++ ys) =
                heap_addresses n xs UNION heap_addresses (n +
                  heap_length xs) ys`)
  CHEAT_TAC;;

let LESS_IMP_heap_lookup = cake_theorem "LESS_IMP_heap_lookup"
  (fun () ->
    `!xs j ys. j < heap_length xs ==> (heap_lookup j (xs ++ ys) =
  heap_lookup j xs)`)
  CHEAT_TAC;;

let NOT_LESS_IMP_heap_lookup = cake_theorem "NOT_LESS_IMP_heap_lookup"
  (fun () ->
    `!xs j ys. ~(j < heap_length xs) ==>
                (heap_lookup j (xs ++ ys) = heap_lookup (j -
                  heap_length xs) ys)`)
  CHEAT_TAC;;

let heap_similar_Data_IMP_DataOrForward =
  cake_theorem "heap_similar_Data_IMP_DataOrForward"
  (fun () ->
    `!heap0 heap1 ptr.
        heaps_similar heap0 heap1 /\ isSomeDataElement (heap_lookup
          ptr heap0) ==>
        isSomeDataOrForward (heap_lookup ptr heap1)`)
  CHEAT_TAC;;

let FILTER_LEMMA = cake_theorem "FILTER_LEMMA"
  (fun () ->
    `!heap. (FILTER isForwardPointer heap = []) ==>
             (FILTER (\h. ~(isForwardPointer h)) heap = heap)`)
  CHEAT_TAC;;

let heaps_similar_REFL = cake_theorem "heaps_similar_REFL"
  (fun () ->
    `!xs. (FILTER isForwardPointer xs = []) ==> heaps_similar xs xs`)
  CHEAT_TAC;;

let heap_map_EMPTY = cake_theorem "heap_map_EMPTY"
  (fun () ->
    `!xs n. (FILTER isForwardPointer xs = []) ==> (FDOM (heap_map n
  xs) = {})`)
  CHEAT_TAC;;

let MEM_ADDR_MAP = cake_theorem "MEM_ADDR_MAP"
  (fun () ->
    `!xs f ptr u. MEM (gc_shared_Pointer ptr u) (ADDR_MAP f xs) ==>
                   (?y. MEM (gc_shared_Pointer y u) xs /\ (f y =
                     ptr))`)
  CHEAT_TAC;;

let heap_length_heap_expand = cake_theorem "heap_length_heap_expand"
  (fun () ->
    `!n. heap_length (heap_expand n) = n`)
  CHEAT_TAC;;

let EVERY_isDataElement_IMP_LEMMA =
  cake_theorem "EVERY_isDataElement_IMP_LEMMA"
  (fun () ->
    `!heap2. EVERY isDataElement heap2 ==> (FILTER isForwardPointer
  heap2 = [])`)
  CHEAT_TAC;;

let isSome_heap_looukp_IMP_APPEND =
  cake_theorem "isSome_heap_looukp_IMP_APPEND"
  (fun () ->
    `!xs ptr. isSomeDataElement (heap_lookup ptr xs) ==>
               isSomeDataElement (heap_lookup ptr (xs ++ ys))`)
  CHEAT_TAC;;

let heap_split_APPEND_if = cake_theorem "heap_split_APPEND_if"
  (fun () ->
    `!h1 n h2. heap_split n (h1 ++ h2) =
     (if n < heap_length h1 then
      match heap_split n h1 with
          NONE -> NONE | SOME (h1',h2') -> SOME (h1',h2' ++ h2)
            else
      match heap_split (n - heap_length h1) h2 with
          NONE -> NONE | SOME (h1',h2') -> SOME (h1 ++ h1',h2'))`)
  CHEAT_TAC;;

let heap_split_0 = cake_theorem "heap_split_0[simp]"
  (fun () ->
    `heap_split 0 h = SOME ([],h)`)
  CHEAT_TAC;;

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

let heap_addresses_LESS_heap_length =
  cake_theorem "heap_addresses_LESS_heap_length"
  (fun () ->
    `!heap n k. k IN heap_addresses n heap ==> k < n + heap_length
  heap`)
  CHEAT_TAC;;

let heap_addresses_LESS = cake_theorem "heap_addresses_LESS"
  (fun () ->
    `!heap n k. k IN heap_addresses n heap ==> n <= k`)
  CHEAT_TAC;;

let FINITE_heap_addresses = cake_theorem "FINITE_heap_addresses"
  (fun () ->
    `!xs n. FINITE (heap_addresses n xs)`)
  CHEAT_TAC;;

let CARD_heap_addresses = cake_theorem "CARD_heap_addresses"
  (fun () ->
    `!xs n. CARD (heap_addresses n xs) = LENGTH xs`)
  CHEAT_TAC;;

let heap_filter_aux_def = cake_define_list
  [`heap_filter_aux n P [] = []`;
   `heap_filter_aux n P (x :: xs) =
         (if n IN P then [x] else []) ++ heap_filter_aux (n +
           el_length x) P xs`];;

let heap_filter_def = cake_define
  `heap_filter = heap_filter_aux 0`;;

let heap_filter_EMPTY = cake_theorem "heap_filter_EMPTY"
  (fun () ->
    `!heap. heap_filter {} heap = []`)
  CHEAT_TAC;;

let heap_length_heap_filter_INSERT =
  cake_theorem "heap_length_heap_filter_INSERT[local]"
  (fun () ->
    `!heap.
       ~(e IN s) ==>
       (heap_length (heap_filter (e INSERT s) heap) =
        heap_length (heap_filter {e} heap) + heap_length
          (heap_filter s heap))`)
  CHEAT_TAC;;

(* HOL4 gc_sharedScript.sml:706-712: a theorem that HOL4 states as
   the value of an ML expression: heap_filter_aux_ADD_SING *)

let heap_filter_aux_SING_ZERO =
  cake_theorem "heap_filter_aux_SING_ZERO[local]"
  (fun () ->
    `!heap n. 0 < n ==> (heap_filter_aux n {0} heap = [])`)
  CHEAT_TAC;;

let heap_lookup_IMP_heap_filter =
  cake_theorem "heap_lookup_IMP_heap_filter[local]"
  (fun () ->
    `!heap e x. (heap_lookup e heap = SOME x) ==> (heap_filter {e}
  heap = [x])`)
  CHEAT_TAC;;

let heap_length_heap_filter_eq =
  cake_theorem "heap_length_heap_filter_eq"
  (fun () ->
    `!s t f heap heap2.
        BIJ f s t /\ FINITE s /\ FINITE t /\
        (!i. i IN s ==>
             (?xs xs2 l d d.
               (heap_lookup i heap = SOME (DataElement xs l d)) /\
               (heap_lookup (f i) heap2 = SOME (DataElement xs2 l
                 d)))) ==>
        (heap_length (heap_filter t heap2) = heap_length
          (heap_filter s heap))`)
  CHEAT_TAC;;

let heap_length_heap_filter_aux =
  cake_theorem "heap_length_heap_filter_aux[local]"
  (fun () ->
    `!n heap x.
        heap_length (heap_filter_aux n (x UNION heap_addresses n
          heap) heap) =
        heap_length heap`)
  CHEAT_TAC;;

let heap_length_heap_filter = cake_theorem "heap_length_heap_filter"
  (fun () ->
    `!heap.
        heap_length (heap_filter (heap_addresses 0 heap) heap) =
        heap_length heap`)
  CHEAT_TAC;;

let heap_filter_aux_APPEND = cake_theorem "heap_filter_aux_APPEND"
  (fun () ->
    `!xs ys n s.
        heap_filter_aux n s (xs ++ ys) =
        heap_filter_aux n s xs ++ heap_filter_aux (n +
          heap_length xs) s ys`)
  CHEAT_TAC;;

let heap_filter_aux_heap_addresses_UNION =
  cake_theorem "heap_filter_aux_heap_addresses_UNION"
  (fun () ->
    `!xs n s. heap_filter_aux n (heap_addresses n xs UNION s) xs = xs`)
  CHEAT_TAC;;
