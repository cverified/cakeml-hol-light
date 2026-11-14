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

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "gc_shared" [];;
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

let empty_state_def = new_definition
  `empty_state =
     mk_gc_state [] [] [] [] [] [] [] 0 0 T [] []
   // ; r := 0`;;

(* The heap is accessed using the following lookup function. *)

let el_length_def = define_cases
  [`el_length (Unused l) = l + 1`;
   `el_length (ForwardPointer n d l) = l + 1`;
   `el_length (DataElement xs l data) = l + 1`];;

let el_length_NOT_0 = prove
 (`!el. ~(el_length el = 0)`,
  CHEAT_TAC);;

let el_length_GT_0 = prove
 (`!el. 1 <= el_length el`,
  CHEAT_TAC);;

let heap_length_def = new_definition
  `heap_length heap = SUM (MAP el_length heap)`;;

(* [simp] *)
let heap_length_NIL = prove
 (`heap_length [] = 0`,
  CHEAT_TAC);;

let heap_length_GTE = prove
 (`!heap. 0 <= heap_length heap`,
  CHEAT_TAC);;

let heap_length_APPEND = prove
 (`heap_length (APPEND xs ys) = heap_length xs + heap_length ys`,
  CHEAT_TAC);;

let heap_lookup_def,heap_lookup_ind = define_rec
  [`heap_lookup a [] = NONE`;
   `heap_lookup a (CONS x xs) =
         (if a = 0 then SOME x else
         if a < el_length x then NONE else heap_lookup (a -
           el_length x) xs)`];;

let heap_lookup_MEM = prove
 (`!heap n x. (heap_lookup n heap = SOME x) ==> MEM x heap`,
  CHEAT_TAC);;

let MEM_IMP_heap_lookup = prove
 (`!xs x. MEM x xs ==> (?j. (heap_lookup j xs = SOME x))`,
  CHEAT_TAC);;

let heap_lookup_LESS = prove
 (`!xs n. (heap_lookup n xs = SOME x) ==> n < heap_length xs`,
  CHEAT_TAC);;

let heap_split_def,heap_split_ind = define_rec
  [`heap_split a [] = (if a = 0 then SOME ([],[]) else NONE)`;
   `heap_split a (CONS el heap) =
        (if a = 0 then SOME ([],CONS el heap) else
        if a < el_length el then NONE else
        match heap_split (a - el_length el) heap with NONE -> NONE |
          SOME (h1,h2) ->
          SOME (CONS el h1,h2))`];;

let heap_lookup_SPLIT = prove
 (`!heap n x. (heap_lookup n heap = SOME x) ==>
               (?ha hb. (heap = APPEND ha (CONS x hb)) /\ (n =
                 heap_length ha))`,
  CHEAT_TAC);;

let heap_drop_def = new_definition
  `heap_drop n (heap:(('a,'b)heap_element) list) =
     (match heap_split n heap with NONE -> ARB | SOME (h1,h2) ->
       h2)`;;

let heap_take_def = new_definition
  `heap_take n (heap:(('a,'b)heap_element) list) =
     (match heap_split n heap with NONE -> ARB | SOME (h1,h2) ->
       h1)`;;

let heap_split_heap_length = prove
 (`!heap h1 h2 a.
    (heap_split a heap = SOME (h1,h2)) ==>
    (heap_length h1 = a) /\
    (heap_length (APPEND h1 h2) = heap_length heap) /\
    (APPEND h1 h2 = heap)`,
  CHEAT_TAC);;

let heap_segment_def = new_definition
  `heap_segment (a,b) heap =
     (match heap_split a heap with NONE -> NONE | SOME (h1,heap') ->
       (if b < a then NONE else
       match heap_split (b - heap_length h1) heap' with NONE ->
         NONE | SOME (h2,h3) -> SOME (h1,h2,h3)))`;;

let heap_segment_IMP = prove
 (`!heap a b h1 h2 h3.
    (heap_segment (a,b) heap = SOME (h1,h2,h3)) ==>
    (APPEND (APPEND h1 h2) h3 = heap) /\
    (heap_length h1 = a) /\
    (heap_length (APPEND h1 h2) = b) /\
    (heap_length h3 = (heap_length heap - b))`,
  CHEAT_TAC);;

let heap_restrict_def = new_definition
  `heap_restrict start' end (heap:(('a,'b)heap_element) list) =
      (match heap_segment (start',end) heap with NONE -> [] | SOME
        (h1,h2,h3) -> h2)`;;

(* The heap is well-formed if heap_ok *)

let isDataElement_def = new_definition
  `isDataElement x = (?ys l d. x = DataElement ys l d)`;;

let isSomeDataElement_def = new_definition
  `isSomeDataElement x = (?ys l d. x = SOME (DataElement ys l d))`;;

let isSomeForwardPointer_def = new_definition
  `isSomeForwardPointer x = (?ptr d l. x = SOME (ForwardPointer ptr d
  l))`;;

let isSomeDataOrForward_def = new_definition
  `isSomeDataOrForward x = (isSomeForwardPointer x \/
  isSomeDataElement x)`;;

let roots_ok_def = new_definition
  `roots_ok roots heap =
     (!ptr u. MEM (gc_shared_Pointer ptr u) roots ==>
       isSomeDataElement (heap_lookup ptr heap))`;;

let isForwardPointer_def = new_definition
  `isForwardPointer x1 =
        match x1 with
          ForwardPointer n d l -> T
        | _1 -> F`;;

let heap_ok_def = new_definition
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

let gc_forward_ptr_def,gc_forward_ptr_ind = define_rec
  [`// replace cell at a with a forwardpointer to ptr
    gc_forward_ptr a [] ptr d ok = ([],F)`;
   `gc_forward_ptr a (CONS x xs) ptr d ok =
         (if a = 0 then
           (CONS (ForwardPointer ptr d ((el_length x) - 1))
             xs,(isDataElement x /\ ok)) else
         if a < el_length x then (CONS x xs,F) else
           let (xs,ok) = gc_forward_ptr (a - el_length x) xs ptr d
             ok in
             (CONS x xs,ok))`];;

let gc_forward_ptr_ok = prove
 (`!heap n a c x. (gc_forward_ptr n heap a d c = (x,T)) ==> c`,
  CHEAT_TAC);;

let gc_forward_ptr_thm = prove
 (`!ha. gc_forward_ptr (heap_length ha) (APPEND ha (CONS (DataElement ys
  l d) hb)) a u c =
         (APPEND ha (CONS (ForwardPointer a u l) hb),c)`,
  CHEAT_TAC);;

(* HOL4 gc_sharedScript.sml:309-327: code that the source has in a
   comment *)

let heap_expand_def = new_definition
  `heap_expand n = (if n = 0 then [] else [Unused (n - 1)])`;;

let _ = size_thms "heap_element";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let heap_map_def,heap_map_ind = define_wf
  `MEASURE (\(x0,x1). list_size (heap_element_size (\x. 0) (\x. 0)) x1)`
  [`heap_map a x2 =
        match x2 with
          [] -> FEMPTY
        | CONS (ForwardPointer ptr d l) xs ->
        heap_map (a + l + 1) xs |+ (a,ptr)
        | (CONS x xs) -> heap_map (a + el_length x) xs`];;

let heap_map1_def = new_definition
  `heap_map1 heap = (\a. FAPPLY (heap_map 0 heap) a)`;;

let _ = size_thms "heap_element";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let heap_addresses_def,heap_addresses_ind = define_wf
  `MEASURE (\(x0,x1). list_size (heap_element_size (\x. 0) (\x. 0)) x1)`
  [`heap_addresses a [] = {}`;
   `heap_addresses a (CONS x xs) = a INSERT heap_addresses (a +
  el_length x) xs`];;

let _ = size_thms "heap_address";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let ADDR_MAP_def,ADDR_MAP_ind = define_wf
  `MEASURE (\(x0,x1). list_size (heap_address_size (\x. 0)) x1)`
  [`ADDR_MAP f [] = []`;
   `ADDR_MAP f (CONS (gc_shared_Data x) xs) = CONS (gc_shared_Data
  x:'a heap_address) (ADDR_MAP f xs)`;
   `ADDR_MAP f (CONS (gc_shared_Pointer a d) xs) = CONS
  (gc_shared_Pointer (f a) d) (ADDR_MAP f xs)`];;

let ADDR_MAP_EQ = prove
 (`!xs. (!p d. MEM (gc_shared_Pointer p d) xs ==> (f p = g p)) ==>
         (ADDR_MAP f xs = ADDR_MAP g xs)`,
  CHEAT_TAC);;

let ADDR_MAP_LENGTH = prove
 (`!xs f. LENGTH xs = LENGTH (ADDR_MAP f xs)`,
  (LIST_INDUCT_TAC THEN TRY (CASES_ON_TAC `h:A heap_address`) THEN
   REWRITE_TAC[ADDR_MAP_def; LENGTH; SUC_INJ] THEN ASM_MESON_TAC[]));;

let ADDR_MAP_APPEND = prove
 (`!h1 h2 f.
    ADDR_MAP f (APPEND h1 h2) = APPEND (ADDR_MAP f h1) (ADDR_MAP f
      h2)`,
  (LIST_INDUCT_TAC THEN TRY (CASES_ON_TAC `h:A heap_address`) THEN
   ASM_REWRITE_TAC[ADDR_MAP_def; APPEND]));;

let ADDR_APPLY_def = define_cases
  [`ADDR_APPLY f (gc_shared_Pointer x d) = gc_shared_Pointer (f x) d`;
   `ADDR_APPLY f (gc_shared_Data y) = (gc_shared_Data y:'a
  heap_address)`];;

(* HOL4 gc_sharedScript.sml:383-395: a theorem that HOL4 states as
   the value of an ML expression: heap_lookup_FLOOKUP *)

(* HOL4 gc_sharedScript.sml:397: ML code, not ported *)

let heaps_similar_def = new_definition
  `heaps_similar heap0 heap =
     ALL2 (\h0 h. if isForwardPointer h then
                      (el_length h = el_length h0) /\
                        isDataElement h0 else (h = h0)) heap0 heap`;;

let IN_heap_map_IMP = prove
 (`!heap n k. n IN FDOM (heap_map k heap) ==> k <= n`,
  CHEAT_TAC);;

(* HOL4 gc_sharedScript.sml:414-423: a theorem that HOL4 states as
   the value of an ML expression: NOT_IN_heap_map *)

let isSomeDataOrForward_lemma = prove
 (`!ha ptr.
      isSomeDataOrForward (heap_lookup ptr (APPEND ha (CONS
        (DataElement ys l d) hb))) <=>
      isSomeDataOrForward (heap_lookup ptr (APPEND (APPEND ha
        [ForwardPointer a u l]) hb))`,
  CHEAT_TAC);;

let heaps_similar_IMP_heap_length = prove
 (`!xs ys. heaps_similar xs ys ==> (heap_length xs = heap_length ys)`,
  CHEAT_TAC);;

let heap_similar_Data_IMP = prove
 (`heaps_similar heap0 (APPEND ha (CONS (DataElement ys l d) hb)) ==>
    (?ha0 hb0. (heap0 = APPEND ha0 (CONS (DataElement ys l d) hb0))
      /\
              (heap_length ha = heap_length ha0))`,
  CHEAT_TAC);;

let heaps_similar_lemma = prove
 (`!ha heap0.
      heaps_similar heap0 (APPEND ha (CONS (DataElement ys l d) hb))
        ==>
      heaps_similar heap0 (APPEND (APPEND ha [ForwardPointer
        (heap_length (APPEND h1 h2)) u l]) hb)`,
  CHEAT_TAC);;

let heap_lookup_PREFIX = prove
 (`!xs. (heap_lookup (heap_length xs) (APPEND xs (CONS x ys)) = SOME
  x)`,
  CHEAT_TAC);;

let heap_lookup_EXTEND = prove
 (`!xs n ys x. (heap_lookup n xs = SOME x) ==>
                (heap_lookup n (APPEND xs ys) = SOME x)`,
  (LIST_INDUCT_TAC THEN REWRITE_TAC[heap_lookup_def; APPEND;
    option_DISTINCT] THEN
   REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
   REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[]));;

let heap_map_APPEND = prove
 (`!xs n ys. (heap_map n (APPEND xs ys)) =
              FUNION (heap_map n xs) (heap_map (n + heap_length xs)
                ys)`,
  CHEAT_TAC);;

(* HOL4 gc_sharedScript.sml:493-500: a theorem that HOL4 states as
   the value of an ML expression: FDOM_heap_map *)

let heap_addresses_APPEND = prove
 (`!xs ys n. heap_addresses n (APPEND xs ys) =
              heap_addresses n xs UNION heap_addresses (n +
                heap_length xs) ys`,
  CHEAT_TAC);;

let LESS_IMP_heap_lookup = prove
 (`!xs j ys. j < heap_length xs ==> (heap_lookup j (APPEND xs ys) =
  heap_lookup j xs)`,
  CHEAT_TAC);;

let NOT_LESS_IMP_heap_lookup = prove
 (`!xs j ys. ~(j < heap_length xs) ==>
              (heap_lookup j (APPEND xs ys) = heap_lookup (j -
                heap_length xs) ys)`,
  CHEAT_TAC);;

let heap_similar_Data_IMP_DataOrForward = prove
 (`!heap0 heap1 ptr.
      heaps_similar heap0 heap1 /\ isSomeDataElement (heap_lookup ptr
        heap0) ==>
      isSomeDataOrForward (heap_lookup ptr heap1)`,
  CHEAT_TAC);;

let FILTER_LEMMA = prove
 (`!heap. (FILTER isForwardPointer heap = []) ==>
           (FILTER (\h. ~(isForwardPointer h)) heap = heap)`,
  (LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER] THEN COND_CASES_TAC THEN
   ASM_REWRITE_TAC[NOT_CONS_NIL; CONS_11]));;

let heaps_similar_REFL = prove
 (`!xs. (FILTER isForwardPointer xs = []) ==> heaps_similar xs xs`,
  (REWRITE_TAC[heaps_similar_def] THEN LIST_INDUCT_TAC THEN
   REWRITE_TAC[FILTER; ALL2] THEN COND_CASES_TAC THEN
   ASM_REWRITE_TAC[NOT_CONS_NIL]));;

let heap_map_EMPTY = prove
 (`!xs n. (FILTER isForwardPointer xs = []) ==> (FDOM (heap_map n xs)
  = {})`,
  CHEAT_TAC);;

let MEM_ADDR_MAP = prove
 (`!xs f ptr u. MEM (gc_shared_Pointer ptr u) (ADDR_MAP f xs) ==>
                 (?y. MEM (gc_shared_Pointer y u) xs /\ (f y =
                   ptr))`,
  (LIST_INDUCT_TAC THEN TRY (CASES_ON_TAC `h:A heap_address`) THEN
   REWRITE_TAC[ADDR_MAP_def; MEM; injectivity "heap_address";
               distinctness "heap_address"] THEN
   ASM_MESON_TAC[]));;

let heap_length_heap_expand = prove
 (`!n. heap_length (heap_expand n) = n`,
  CHEAT_TAC);;

let EVERY_isDataElement_IMP_LEMMA = prove
 (`!heap2. ALL isDataElement heap2 ==> (FILTER isForwardPointer heap2
  = [])`,
  (LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; FILTER; isDataElement_def]
    THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[isForwardPointer_def] THEN
     ASM_MESON_TAC[]));;

let isSome_heap_looukp_IMP_APPEND = prove
 (`!xs ptr. isSomeDataElement (heap_lookup ptr xs) ==>
             isSomeDataElement (heap_lookup ptr (APPEND xs ys))`,
  (REWRITE_TAC[isSomeDataElement_def] THEN
   MESON_TAC[heap_lookup_EXTEND]));;

let heap_split_APPEND_if = prove
 (`!h1 n h2. heap_split n (APPEND h1 h2) =
   (if n < heap_length h1 then
    match heap_split n h1 with
        NONE -> NONE | SOME (h1',h2') -> SOME (h1',APPEND h2' h2)
          else
    match heap_split (n - heap_length h1) h2 with
        NONE -> NONE | SOME (h1',h2') -> SOME (APPEND h1 h1',h2'))`,
  CHEAT_TAC);;

(* [simp] *)
let heap_split_0 = prove
 (`heap_split 0 h = SOME ([],h)`,
  (GEN_TAC THEN CASES_ON_TAC `h:((A,B)heap_element)list` THEN
   REWRITE_TAC[heap_split_def]));;

(* --- *)

let gc_related_def = new_definition
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

let gc_edge_def = new_definition
  `gc_edge heap x y <=>
     (?xs l d t. (heap_lookup x heap = SOME (DataElement xs l d)) /\
                MEM (gc_shared_Pointer y t) xs)`;;

let reachable_addresses_def = new_definition
  `reachable_addresses roots heap y =
     (?t x. MEM (gc_shared_Pointer x t) roots /\ RTC (gc_edge
       heap) x y)`;;

let heap_addresses_LESS_heap_length = prove
 (`!heap n k. k IN heap_addresses n heap ==> k < n + heap_length heap`,
  CHEAT_TAC);;

let heap_addresses_LESS = prove
 (`!heap n k. k IN heap_addresses n heap ==> n <= k`,
  CHEAT_TAC);;

let FINITE_heap_addresses = prove
 (`!xs n. FINITE (heap_addresses n xs)`,
  (LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC[heap_addresses_def; FINITE_EMPTY; FINITE_INSERT]));;

let CARD_heap_addresses = prove
 (`!xs n. CARD (heap_addresses n xs) = LENGTH xs`,
  CHEAT_TAC);;

let heap_filter_aux_def,heap_filter_aux_ind = define_rec
  [`heap_filter_aux n P [] = []`;
   `heap_filter_aux n P (CONS x xs) = APPEND (if n IN P then [x]
  else []) (heap_filter_aux (n + el_length x) P xs)`];;

let heap_filter_def = new_definition
  `heap_filter = heap_filter_aux 0`;;

let heap_filter_EMPTY = prove
 (`!heap. heap_filter {} heap = []`,
  CHEAT_TAC);;

(* [local] *)
let heap_length_heap_filter_INSERT = prove
 (`!heap.
     ~(e IN s) ==>
     (heap_length (heap_filter (e INSERT s) heap) =
      heap_length (heap_filter {e} heap) + heap_length (heap_filter
        s heap))`,
  CHEAT_TAC);;

(* HOL4 gc_sharedScript.sml:706-712: a theorem that HOL4 states as
   the value of an ML expression: heap_filter_aux_ADD_SING *)

(* [local] *)
let heap_filter_aux_SING_ZERO = prove
 (`!heap n. 0 < n ==> (heap_filter_aux n {0} heap = [])`,
  (LIST_INDUCT_TAC THEN REWRITE_TAC[heap_filter_aux_def; IN_SING]
    THEN
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)
     /\ 0 < n + m`; APPEND]));;

(* [local] *)
let heap_lookup_IMP_heap_filter = prove
 (`!heap e x. (heap_lookup e heap = SOME x) ==> (heap_filter {e} heap
  = [x])`,
  CHEAT_TAC);;

let heap_length_heap_filter_eq = prove
 (`!s t f heap heap2.
      BIJ f s t /\ FINITE s /\ FINITE t /\
      (!i. i IN s ==>
           (?xs xs2 l d d.
             (heap_lookup i heap = SOME (DataElement xs l d)) /\
             (heap_lookup (f i) heap2 = SOME (DataElement xs2 l d))))
               ==>
      (heap_length (heap_filter t heap2) = heap_length (heap_filter
        s heap))`,
  CHEAT_TAC);;

(* [local] *)
let heap_length_heap_filter_aux = prove
 (`!n heap x.
      heap_length (heap_filter_aux n (x UNION heap_addresses n heap)
        heap) =
      heap_length heap`,
  CHEAT_TAC);;

let heap_length_heap_filter = prove
 (`!heap.
      heap_length (heap_filter (heap_addresses 0 heap) heap) =
      heap_length heap`,
  (REWRITE_TAC[heap_filter_def] THEN
   MESON_TAC[heap_length_heap_filter_aux; UNION_EMPTY]));;

let heap_filter_aux_APPEND = prove
 (`!xs ys n s.
      heap_filter_aux n s (APPEND xs ys) = APPEND (heap_filter_aux
        n s xs) (heap_filter_aux (n + heap_length xs) s ys)`,
  CHEAT_TAC);;

let heap_filter_aux_heap_addresses_UNION = prove
 (`!xs n s. heap_filter_aux n (heap_addresses n xs UNION s) xs = xs`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
