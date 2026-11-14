(* ======================================================== *)
(*  copying_gc: ported from HOL4's
    compiler/backend/gc/copying_gcScript.sml
    A definition theory, with 5 definitions and 23 theorems.  Needed
    by 6 files of the port.  *)
(* ======================================================== *)

(*
  The straightforward non-generational copying garbage collector.
*)

needs "compiler/backend/gc/gc_shared.ml";;
needs "lib/integer_word.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "copying_gc"
  ["gc_shared"];;
(* HOL4 ancestors outside the port: words *)

(* The GC is a copying collector which moves elements *)

let gc_move_def = define_general
  [`copying_gc_gc_move (gc_shared_Data d,h2,a,n,heap,c,limit') =
  ((gc_shared_Data d:'a heap_address),h2,a,n,heap,c)`;
   `copying_gc_gc_move (gc_shared_Pointer ptr d,h2,a,n,heap,c,limit') =
         (match heap_lookup ptr heap with SOME (DataElement xs l dd)
           ->
             (let c = (c /\ l + 1 <= n /\ (a + n = limit')) in
             let n = n - (l + 1) in
             let h2 = APPEND h2 [DataElement xs l dd] in
             let (heap,c) = gc_forward_ptr ptr heap a d c in
               (gc_shared_Pointer a d,h2,a + (l + 1),n,heap,c))
                 | SOME (ForwardPointer ptr _3 l) ->
                 (gc_shared_Pointer ptr d,h2,a,n,heap,c) | _4 ->
                 (ARB,h2,a,n,heap,F))`];;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let gc_move_list_def,gc_move_list_ind = define_guess_cheat
  [`copying_gc_gc_move_list ([],h2,a,n,heap,c,limit') =
  ([],h2,a,n,heap,c)`;
   `copying_gc_gc_move_list (CONS x xs,h2,a,n,heap,c,limit') =
         (let (x,h2,a,n,heap,c) = copying_gc_gc_move
           (x,h2,a,n,heap,c,limit') in
         let (xs,h2,a,n,heap,c) = copying_gc_gc_move_list
           (xs,h2,a,n,heap,c,limit') in
           (CONS x xs,h2,a,n,heap,c))`];;

(* the termination relation that HOL4 gives is
     MEASURE (\(h1,h2,a,n,heap,c,limit'). limit' - heap_length h1)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 copying_gcScript.sml:50-53: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let gc_move_loop_def,gc_move_loop_ind = define_guess_cheat
  [`copying_gc_gc_move_loop (h1,[],a,n,heap,c,limit') =
  (h1,a,n,heap,c)`;
   `copying_gc_gc_move_loop (h1,CONS h h2,a,n,heap,c,limit') =
         (if limit' < heap_length (APPEND h1 (CONS h h2)) then
           (h1,a,n,heap,F) else
           match h with DataElement xs l d ->
              (let (xs,h2,a,n,heap,c) = copying_gc_gc_move_list
                (xs,CONS h h2,a,n,heap,c,limit') in
              let c = (c /\ ~(h2 = []) /\ (HD h2 = h)) in
              let h2 = TL h2 in
              let h1 = APPEND h1 [DataElement xs l d] in
                copying_gc_gc_move_loop
                  (h1,h2,a,n,heap,c,limit')) | _6 ->
                  (h1,a,n,heap,F))`];;

let full_gc_def = new_definition
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

let gc_inv_def = new_definition
  `copying_gc_gc_inv (h1,h2,a,n,heap,c,limit')
  (heap0:(('a,'b)heap_element) list) (roots0:('a heap_address) list) = (
     (a + n = limit') /\
     (a = heap_length (APPEND h1 h2)) /\
     (n = heap_length (FILTER (\h. ~(isForwardPointer h)) heap)) /\ c
       /\
     (heap_length heap = limit') /\
     // the initial heap is well-formed
     heap_ok heap0 limit' /\
     // the initial heap is related to the current heap
     heaps_similar heap0 heap /\
     // the new heap consists of only DataElements
     ALL isDataElement h1 /\ ALL isDataElement h2 /\
     // the forward pointers consitute a bijection into the new heap
     BIJ (heap_map1 heap) (FDOM (heap_map 0 heap)) (heap_addresses 0
       (APPEND h1 h2)) /\
     (!i j. (FLOOKUP (heap_map 0 heap) i = SOME j) ==>
           (?xs l d. (heap_lookup i heap0 = SOME (DataElement xs l
             d)) /\
                    (heap_lookup j (APPEND h1 h2) =
                      SOME (DataElement (if j < heap_length h1 then
                              ADDR_MAP (heap_map1 heap) xs else xs) l
                                d)) /\
                    reachable_addresses roots0 heap0 i /\
                    (!ptr d. MEM (gc_shared_Pointer ptr d) xs /\ j <
                      heap_length h1 ==>
                            ptr IN FDOM (heap_map 0 heap)))))`;;

(* Invariant maintained *)

(* [local] *)
let DRESTRICT_heap_map = prove
 (`!heap k. n < k ==> (DRESTRICT (heap_map k heap) (COMPL {n}) =
  heap_map k heap)`,
  CHEAT_TAC);;

(* [local] *)
let IN_FRANGE = prove
 (`!heap n. MEM (ForwardPointer ptr d l) heap ==> ptr IN FRANGE
  (heap_map n heap)`,
  CHEAT_TAC);;

(* [local] *)
let heap_addresses_SNOC = prove
 (`!xs n x.
       heap_addresses n (APPEND xs [x]) =
       heap_addresses n xs UNION {heap_length xs + n}`,
  CHEAT_TAC);;

(* HOL4 copying_gcScript.sml:126-132: a theorem that HOL4 states as
   the value of an ML expression: NOT_IN_heap_addresses *)

(* [local] *)
let gc_move_thm = prove
 (`copying_gc_gc_inv (h1,h2,a,n,(heap:(('a,'b)heap_element)
  list),c,limit) heap0 roots0 /\
     (!ptr u. (x = gc_shared_Pointer ptr u) ==> isSomeDataOrForward
       (heap_lookup ptr heap) /\
                              reachable_addresses roots0 heap0 ptr)
                                ==>
     (?x3 h23 a3 n3 heap3 c3.
       (copying_gc_gc_move ((x:'a heap_address),h2,a,n,heap,c,limit)
         = (ADDR_APPLY (heap_map1 heap3) x,h23,a3,n3,heap3,c3)) /\
       (!ptr u. (x = gc_shared_Pointer ptr u) ==> ptr IN FDOM
         (heap_map 0 heap3)) /\
       (!ptr. isSomeDataOrForward (heap_lookup ptr heap) =
              isSomeDataOrForward (heap_lookup ptr heap3)) /\
       ((heap_map 0 heap) SUBMAP (heap_map 0 heap3)) /\
       copying_gc_gc_inv (h1,h23,a3,n3,heap3,c3,limit) heap0
         roots0)`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_list_thm = prove
 (`!xs h2 a n heap c.
     copying_gc_gc_inv (h1,h2,a,n,(heap:(('a,'b)heap_element)
       list),c,limit) heap0 roots0 /\
     (!ptr u. MEM (gc_shared_Pointer ptr u) (xs:('a heap_address)
       list) ==>
              isSomeDataOrForward (heap_lookup ptr heap) /\
              reachable_addresses roots0 heap0 ptr) ==>
     (?h23 a3 n3 heap3 c3.
       (copying_gc_gc_move_list (xs,h2,a,n,heap,c,limit) = (ADDR_MAP
         (heap_map1 heap3) xs,h23,a3,n3,heap3,c3)) /\
       (!ptr u. MEM (gc_shared_Pointer ptr u) xs ==> ptr IN FDOM
         (heap_map 0 heap3)) /\
       (!ptr. isSomeDataOrForward (heap_lookup ptr heap) =
              isSomeDataOrForward (heap_lookup ptr heap3)) /\
       ((heap_map 0 heap) SUBMAP (heap_map 0 heap3)) /\
       copying_gc_gc_inv (h1,h23,a3,n3,heap3,c3,limit) heap0
         roots0)`,
  CHEAT_TAC);;

(* HOL4 copying_gcScript.sml:247: the ML values that the definitions
   below antiquote *)

let gc_move_ALT = prove
 (`copying_gc_gc_move (ys,xs,a,n,heap,c,limit) =
      (let (ys,xs1,x) = copying_gc_gc_move (ys,[],a,n,heap,c,limit)
        in
        (ys,APPEND xs xs1,x))`,
  CHEAT_TAC);;

let gc_move_list_ALT = prove
 (`!ys xs a n heap c limit' ys3 xs3 a3 n3 heap3 c3.
      copying_gc_gc_move_list (ys,xs,a,n,heap,c,limit') =
        (let (ys,xs1,x) = copying_gc_gc_move_list
          (ys,[],a,n,heap,c,limit') in
          (ys,APPEND xs xs1,x))`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_list_APPEND_lemma = prove
 (`!ys xs a n heap c limit' ys3 xs3 a3 n3 heap3 c3.
       (copying_gc_gc_move_list (ys,xs,a,n,heap,c,limit') =
         (ys3,xs3,a3,n3,heap3,c3)) ==>
       (?xs1. xs3 = APPEND xs xs1)`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_loop_thm = prove
 (`!h1 h2 a n heap c.
       copying_gc_gc_inv (h1,h2,a,n,(heap:(('a,'b)heap_element)
         list),c,limit) heap0 roots0 ==>
       (?h13 a3 n3 heap3 c3.
         (copying_gc_gc_move_loop (h1,h2,a,n,heap,c,limit) =
           (h13,a3,n3,heap3,c3)) /\
       ((heap_map 0 heap) SUBMAP (heap_map 0 heap3)) /\
       copying_gc_gc_inv (h13,[],a3,n3,heap3,c3,limit) heap0
         roots0)`,
  CHEAT_TAC);;

(* [local] *)
let gc_inv_init = prove
 (`copying_gc_gc_inv ([],[],0,limit,heap,T,limit) heap roots = heap_ok
  heap limit`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let full_gc_thm = prove
 (cake_as_vars (fun () ->
    `roots_ok roots heap /\ heap_ok (heap:(('a,'b)heap_element) list)
  limit ==>
      (?heap2 a2 heap3.
        (full_gc ((roots:('a heap_address) list),heap,limit) =
           (ADDR_MAP (heap_map1 heap3) roots,heap2,a2,T)) /\
        (!ptr u. MEM (gc_shared_Pointer ptr u) roots ==> ptr IN
          FDOM (heap_map 0 heap3)) /\
        copying_gc_gc_inv (heap2,[],a2,limit - a2,heap3,T,limit)
          heap roots)`),
  CHEAT_TAC);;

(* HOL4 copying_gcScript.sml:411-417: a theorem that HOL4 states as
   the value of an ML expression: heap_lookup_IMP_heap_addresses *)

let full_gc_LENGTH = prove
 (`roots_ok roots heap /\ heap_ok (heap:(('a,'b)heap_element) list)
  limit ==>
    (?roots2 heap2 a2.
      (full_gc ((roots:('a heap_address) list),heap,limit) =
      (roots2,heap2,heap_length heap2,T)))`,
  CHEAT_TAC);;

let full_gc_ok = prove
 (`roots_ok roots heap /\ heap_ok (heap:(('a,'b)heap_element) list)
  limit ==>
    (?roots2 heap2 a2.
      (full_gc ((roots:('a heap_address) list),heap,limit) =
        (roots2,heap2,a2,T)) /\
      a2 <= limit /\ roots_ok roots2 (APPEND heap2 (heap_expand
        (limit - a2))) /\
      heap_ok (APPEND heap2 (heap_expand (limit - a2))) limit)`,
  CHEAT_TAC);;

let full_gc_related = prove
 (`roots_ok roots heap /\ heap_ok (heap:(('a,'b)heap_element) list)
  limit ==>
    (?heap2 a2 f.
      (full_gc ((roots:('a heap_address) list),heap,limit) =
         (ADDR_MAP (FAPPLY f) roots,heap2,a2,T)) /\
      (FDOM f = reachable_addresses roots heap) /\
      (FRANGE f = {a | isSomeDataElement (heap_lookup a heap2)}) /\
      (heap_length heap2 = heap_length (heap_filter (FDOM f) heap))
        /\
      gc_related f heap (APPEND heap2 (heap_expand (limit - a2))) /\
      ALL isDataElement heap2)`,
  CHEAT_TAC);;

(* Lemmas about ok and a *)

let gc_move_ok = prove
 (`(copying_gc_gc_move (x,h2,a,n,heap,c,limit) = (x',h2',a',n',heap',T))
  ==>
    c /\
    ((a = b + heap_length h2) ==> (a' = b + heap_length h2'))`,
  CHEAT_TAC);;

let gc_move_list_ok = prove
 (`!xs h2 a n heap c limit' xs' h2' a' n' heap' c'.
      (copying_gc_gc_move_list (xs,h2,a,n,heap,c,limit') =
        (xs',h2',a',n',heap',T)) ==>
      c /\
      ((a = b + heap_length h2) ==> (a' = b + heap_length h2'))`,
  CHEAT_TAC);;

(* HOL4 copying_gcScript.sml:598-602: ML code, not ported *)

(* HOL4 copying_gcScript.sml:604-617: a proof *)

(* HOL4 copying_gcScript.sml:619-620: ML code, not ported *)

(* HOL4 copying_gcScript.sml:622-623: a theorem that HOL4 states as
   the value of an ML expression: gc_move_loop_ok *)

let gc_move_list_IMP_LENGTH = prove
 (`!l5 h a n heap c k xs ys a1 xs1 heap1 c1.
      (copying_gc_gc_move_list (l5,h,a,n,heap,c,k) =
        (xs,ys,a1,xs1,heap1,c1)) ==> (LENGTH xs = LENGTH l5)`,
  CHEAT_TAC);;

let full_gc_IMP_LENGTH = prove
 (`(full_gc (xs,heap,limit) = (roots2,heap2,h,T)) ==>
    (LENGTH roots2 = LENGTH xs)`,
  CHEAT_TAC);;

let gc_move_IMP_isDataElement = prove
 (`!l5 h a n heap c k xs ys a1 xs1 heap1 c1.
      ALL isDataElement h /\
      (copying_gc_gc_move (l5,h,a,n,heap,c,k) =
        (xs,ys,a1,xs1,heap1,c1)) ==>
      ALL isDataElement ys`,
  CHEAT_TAC);;

let gc_move_list_IMP_isDataElement = prove
 (`!l5 h a n heap c k xs ys a1 xs1 heap1 c1.
      ALL isDataElement h /\
      (copying_gc_gc_move_list (l5,h,a,n,heap,c,k) =
        (xs,ys,a1,xs1,heap1,c1)) ==>
      ALL isDataElement ys`,
  CHEAT_TAC);;

let gc_move_loop_IMP_isDataElement = prove
 (`!h1 h2 a n heap c limit' h1' a' n' heap' c'.
      ALL isDataElement h1 /\
      ALL isDataElement h2 /\
      (copying_gc_gc_move_loop (h1,h2,a,n,heap,c,limit') =
        (h1',a',n',heap',T)) ==>
      ALL isDataElement h1'`,
  CHEAT_TAC);;

let full_gc_IMP_isDataElement = prove
 (`(full_gc (roots,heap,limit) = (roots1,heap1,a,T)) ==>
    ALL isDataElement heap1`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
