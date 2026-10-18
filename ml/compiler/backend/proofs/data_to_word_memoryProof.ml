(* ======================================================== *)
(*  data_to_word_memoryProof: ported from HOL4's
    compiler/backend/proofs/data_to_word_memoryProofScript.sml
    A proof theory, with 119 definitions, 1 datatype and 632
    theorems.  Needed by 4 files of the port.  *)
(* ======================================================== *)

(*
  Part of the correctness proof for data_to_word
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/data_space.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/gc/copying_gc.ml";;
needs "compiler/backend/gc/gc_combined.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "compiler/backend/gc/gen_gc_partial.ml";;
needs "compiler/backend/labLang.ml";;
needs "compiler/backend/proofs/word_gcFunctions.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/labSem.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/alignment.ml";;
needs "lib/balanced_map.ml";;
needs "lib/byte.ml";;
needs "lib/comparison.ml";;
needs "lib/integer_word.ml";;
needs "lib/multiword.ml";;
needs "lib/set_sep.ml";;
needs "lib/sorting.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

cake_hide ["do_partial"; "parts"; "vars"];;
(* HOL4 ancestors outside the port: int_bitwise While *)


(* HOL4 data_to_word_memoryProofScript.sml:13-14: ML code, not ported *)

(* TODO: move? *)
(* HOL4 data_to_word_memoryProofScript.sml:21-22: a proof *)

(* HOL4 data_to_word_memoryProofScript.sml:24: ML code, not ported *)
(* HOL4 data_to_word_memoryProofScript.sml:28: the overload
   good_dimindex, which the port expands *)

(* HOL4 data_to_word_memoryProofScript.sml:30-32: the ML values that
   the definitions below antiquote *)

let word_eq = cake_theorem "word_eq"
  (fun () ->
    `!w v. w = v <=> (!n. word_bit n w = word_bit n v)`)
  CHEAT_TAC;;

let ZIP_REPLICATE = cake_theorem "ZIP_REPLICATE"
  (fun () ->
    `!n. ZIP (REPLICATE n x) (REPLICATE n y) = REPLICATE n (x,y)`)
  CHEAT_TAC;;

(* MutBlock payloads have the shape l ++ [c] ++ r, which simplifiers split
   into three membership tests; this puts EL_MEM into the same split form *)
let MEM_EL_APPEND_MID = cake_theorem "MEM_EL_APPEND_MID"
  (fun () ->
    `!n l c r.
       n < LENGTH l + (LENGTH r + 1) ==>
       MEM (EL n (l ++ [c] ++ r)) l \/ EL n (l ++ [c] ++ r) = c \/
       MEM (EL n (l ++ [c] ++ r)) r`)
  CHEAT_TAC;;

let MAX_LIST_sum_bound = cake_theorem "MAX_LIST_sum_bound"
  (fun () ->
    `SUM ls <= MAX_LIST ls * LENGTH ls`)
  CHEAT_TAC;;

let MAX_LIST_bounded_elements = cake_theorem "MAX_LIST_bounded_elements"
  (fun () ->
    `!l1 l2. LIST_REL (<=) l1 l2 ==> MAX_LIST l1 <= MAX_LIST l2`)
  CHEAT_TAC;;

let MAX_LIST_MAP = cake_theorem "MAX_LIST_MAP"
  (fun () ->
    `!f l. (!x y. x < y ==> f x < f y) ==> MAX_LIST (MAP f l) = (if
  NULL l then 0 else f (MAX_LIST l))`)
  CHEAT_TAC;;

let w2i_i2w_IMP = cake_theorem "w2i_i2w_IMP"
  (fun () ->
    `(w2i ((i2w i):'a word)) = i ==> INT_MIN (:'a) <= i /\ i <=
  INT_MAX (:'a)`)
  CHEAT_TAC;;

let word_i2w_sub = cake_theorem "word_i2w_sub"
  (fun () ->
    `!a b. i2w a - i2w b = i2w (a - b)`)
  CHEAT_TAC;;

(* -- *)

let data_to_word_memoryProof_tag_INDUCT,
    data_to_word_memoryProof_tag_RECURSION =
  define_datatype
  "data_to_word_memoryProof_tag = BlockTag (num) | RefTag | BytesTag \
   (bool) (num) | ThunkTag (thunk_mode) | NumTag (bool) | Word64Tag";;

let BlockRep_def = cake_define
  `BlockRep tag xs = DataElement xs (LENGTH xs) (BlockTag tag,[])`;;

(* HOL4 data_to_word_memoryProofScript.sml:139: the type abbreviation
   ml_el, which the port expands *)
(* HOL4 data_to_word_memoryProofScript.sml:140: the type abbreviation
   ml_heap, which the port expands *)

let bytes_def = cake_define
  `((Bytes is_bigendian cmp_by_contents (bs:word8 list) (ws:('a word)
  list)):('a word_loc,data_to_word_memoryProof_tag#('a word_loc)
  list)heap_element) =
     (let ws = write_bytes bs ws is_bigendian in
       DataElement [] (LENGTH ws) (BytesTag cmp_by_contents
         (LENGTH bs),MAP wordLang_Word ws))`;;

let bignum_def = cake_define
  `Bignum i =
     (let (sign,(payload:('a word) list)) = i2mw i in
       DataElement [] (LENGTH payload) (NumTag sign,MAP
         wordLang_Word payload))`;;

let BlockNil_def = cake_define
  `BlockNil n = n2w n << 4 + (n2w 2)`;;

let Word64Rep_def = cake_define
  `Word64Rep (:'a) (w:word64) =
     (if dimindex (:'a) < 64 then
       DataElement [] 2 (Word64Tag,[wordLang_Word ((63 >< 32) w);
         wordLang_Word ((31 >< 0) w)]) else
       DataElement [] 1 (Word64Tag,[wordLang_Word (((63 >< 0)
         w):'a word)]))`;;

let Word64Rep_DataElement = cake_theorem "Word64Rep_DataElement"
  (fun () ->
    `!a w. ?ws. (Word64Rep a w:('a
  word_loc,data_to_word_memoryProof_tag#('a word_loc)
  list)heap_element) = DataElement [] (LENGTH ws) (Word64Tag,ws)`)
  CHEAT_TAC;;

let ThunkBlock_def = cake_define
  `ThunkBlock ev x = DataElement [x] 1 (ThunkTag ev,[])`;;

(* HOL4 data_to_word_memoryProofScript.sml:176-181: a theorem whose
   statement the port cannot state yet: v_size_LEMMA *)

(* v_inv conf v refs (x,f,tf,heap)
   v    : the dataSem value
   x    : the abstract gc value
   f    : reference values in dataLang to gc address (sort of like the content of the pointer)
   tf   : time-stamps in dataLang to gc addresses
   heap : is the gc abstract heap
 *)

(* The word annotation carried by a pointer to a ref. It is 0 for ordinary
   refs, but a MutBlock must carry exactly the annotation its finalised Block
   carries, since FinaliseCons is a no-op at word level. *)
let ref_ptr_annot_def = cake_define
  `ref_ptr_annot conf x2 =
      match x2 with
        SOME (bvlSem_MutBlock tg fin l c r) ->
     (wordLang_Word (ptr_bits conf tg (LENGTH l + 1 + LENGTH r)):'a
       word_loc)
      | _1 -> wordLang_Word (n2w 0)`;;

let v_inv_ck = cake_inductive
  `(small_int (:'a) i ==>
       v_inv_ck ck conf (Number i) (refs:(dataSem_v bvlSem_ref) spt)
                  (gc_shared_Data (wordLang_Word (Smallnum
                    i)),f,tf,(heap:(('a
                    word_loc,data_to_word_memoryProof_tag#('a word_loc)
                    list)heap_element) list))) /\
   (~(small_int (:'a) i) /\
     heap_lookup ptr heap = SOME (Bignum i) ==>
       v_inv_ck ck conf (Number i) refs (gc_shared_Pointer ptr
         (wordLang_Word (n2w 0)),f,tf,(heap:(('a
         word_loc,data_to_word_memoryProof_tag#('a word_loc)
         list)heap_element) list))) /\
   (heap_lookup ptr heap = SOME (Word64Rep (:'a) w) ==>
       v_inv_ck ck conf (Word64 w) refs (gc_shared_Pointer ptr
         (wordLang_Word (n2w 0)),f,tf,(heap:(('a
         word_loc,data_to_word_memoryProof_tag#('a word_loc)
         list)heap_element) list))) /\
   (v_inv_ck ck conf (CodePtr n) refs (gc_shared_Data (Loc n
     0),f,tf,(heap:(('a word_loc,data_to_word_memoryProof_tag#('a
     word_loc) list)heap_element) list))) /\
   (n IN FDOM f /\
     (!ev v. ~(lookup n refs = SOME (Thunk ev v))) /\
     (!tg fin l c r. lookup n refs = SOME (bvlSem_MutBlock tg fin l c
       r) ==> ~b) ==>
       v_inv_ck ck conf (RefPtr b n) refs
                  (gc_shared_Pointer (FAPPLY f n) (ref_ptr_annot conf
                    (lookup n refs)),
                   f,tf,(heap:(('a
                     word_loc,data_to_word_memoryProof_tag#('a word_loc)
                     list)heap_element) list))) /\
   (lookup n refs = SOME (Thunk ev v) /\
     (ev = Evaluated ==> dest_thunk v refs = NotThunk) /\
     n IN FDOM f /\
     heap_lookup (FAPPLY f n) heap = SOME (ThunkBlock ev x) /\
     (~(ck = (0:num)) ==> v_inv_ck (ck - 1) conf v refs
       (x,f,tf,heap)) ==>
       v_inv_ck ck conf (RefPtr F n) refs
                  (gc_shared_Pointer (FAPPLY f n) (wordLang_Word (n2w
                    0)),f,tf,(heap:(('a
                    word_loc,data_to_word_memoryProof_tag#('a word_loc)
                    list)heap_element) list))) /\
   (lookup n refs = SOME (Thunk Evaluated v) /\
     dest_thunk v refs = NotThunk /\
     (~(ck = 0) ==> v_inv_ck (ck - 1) conf v refs (x,f,tf,heap)) ==>
       v_inv_ck ck conf (RefPtr F n) refs (x,f,tf,(heap:(('a
         word_loc,data_to_word_memoryProof_tag#('a word_loc)
         list)heap_element) list))) /\
   (vs = [] /\
     n < dimword (:'a) DIV 16 /\
     ts = 0 ==>
       v_inv_ck ck conf (Block ts n vs) refs
                  (gc_shared_Data (wordLang_Word (BlockNil
                    n)),f,tf,(heap:(('a
                    word_loc,data_to_word_memoryProof_tag#('a word_loc)
                    list)heap_element) list))) /\
   (~(vs = []) /\
     (~(ck = 0) ==> EVERY2 (\v x. v_inv_ck (ck - 1) conf v refs
       (x,f,tf,heap)) vs xs) /\
     FLOOKUP tf ts = SOME ptr /\
     heap_lookup ptr heap = SOME (BlockRep n xs) ==>
       v_inv_ck ck conf (Block ts n vs) refs
                  (gc_shared_Pointer ptr (wordLang_Word (ptr_bits
                    conf n (LENGTH xs))),
                   f,tf,(heap:(('a
                     word_loc,data_to_word_memoryProof_tag#('a
                     word_loc) list)heap_element) list)))`;;

let v_inv_eq = cake_define
  `v_inv conf v refs (x,f,tf,heap) =
     (!ck. v_inv_ck ck conf v refs (x,f,tf,heap))`;;

let ThunkBlock_11 = cake_theorem "ThunkBlock_11[simp]"
  (fun () ->
    `ThunkBlock ev1 x1 = ThunkBlock ev2 x2 <=>
       ev1 = ev2 /\ x1 = x2`)
  CHEAT_TAC;;

let v_inv_ck_mono = cake_theorem "v_inv_ck_mono"
  (fun () ->
    `!ck conf v refs x f tf heap.
       v_inv_ck ck conf v refs (x,f,tf,heap) ==>
         (!ck'. ck' <= ck ==> v_inv_ck ck' conf v refs
           (x,f,tf,heap))`)
  CHEAT_TAC;;

let v_inv_def = cake_theorem "v_inv_def"
  (fun () ->
    `(v_inv conf (Number i:dataSem_v) (refs:(dataSem_v bvlSem_ref) spt)
  (x,f,tf,(heap:(('a word_loc,data_to_word_memoryProof_tag#('a word_loc)
  list)heap_element) list)) <=>
        (if small_int (:'a) i then (x = gc_shared_Data
          (wordLang_Word (Smallnum i))) else
          ?ptr. (x = gc_shared_Pointer ptr (wordLang_Word (n2w 0)))
            /\
                (heap_lookup ptr heap = SOME (Bignum i)))) /\
     (v_inv conf (Word64 w) refs (x,f,tf,heap) <=>
       (?ptr. (x = gc_shared_Pointer ptr (wordLang_Word (n2w 0)))
         /\
             (heap_lookup ptr heap = SOME (Word64Rep (:'a) w)))) /\
     (v_inv conf (CodePtr n) refs (x,f,tf,heap) <=>
        (x = gc_shared_Data (Loc n 0))) /\
     (v_inv conf (RefPtr b n) refs (x,f,tf,heap) <=>
        (n IN FDOM f /\
         (!ev v. ~(lookup n refs = SOME (Thunk ev v))) /\
         (!tg fin l c r. lookup n refs = SOME (bvlSem_MutBlock tg
           fin l c r) ==> ~b) /\
         x = gc_shared_Pointer (FAPPLY f n) (ref_ptr_annot conf
           (lookup n refs))) \/
        (?ev v y.
            lookup n refs = SOME (Thunk ev v) /\
            (ev = Evaluated ==> dest_thunk v refs = NotThunk) /\
            n IN FDOM f /\
            heap_lookup (FAPPLY f n) heap = SOME (ThunkBlock ev y)
              /\
            v_inv conf v refs (y,f,tf,heap) /\
            ~b /\
            x = gc_shared_Pointer (FAPPLY f n) (wordLang_Word (n2w
              0))) \/
        (?v.
            lookup n refs = SOME (Thunk Evaluated v) /\
            dest_thunk v refs = NotThunk /\
            ~b /\
            v_inv conf v refs (x,f,tf,heap))) /\
     (v_inv conf (Block ts n vs) refs (x,f,tf,heap) <=>
        (if vs = [] then (x = gc_shared_Data (wordLang_Word
          (BlockNil n))) /\
             n < dimword (:'a) DIV 16 /\
             ts = 0 else
          ?ptr xs.
            EVERY2 (\v x. v_inv conf v refs (x,f,tf,heap)) vs xs /\
            FLOOKUP tf ts = SOME ptr /\
            (x = gc_shared_Pointer ptr (wordLang_Word (ptr_bits
              conf n (LENGTH xs)))) /\
            (heap_lookup ptr heap = SOME (BlockRep n xs))))`)
  CHEAT_TAC;;

(* a compare-by-pointer RefPtr never points at a thunk or a MutBlock, so its
   pointer annotation is always 0 *)
let v_inv_RefPtr_T = cake_theorem "v_inv_RefPtr_T"
  (fun () ->
    `v_inv conf (RefPtr T n:dataSem_v) (refs:(dataSem_v bvlSem_ref) spt)
  (x,f,tf,(heap:(('a word_loc,data_to_word_memoryProof_tag#('a word_loc)
  list)heap_element) list)) <=>
       n IN FDOM f /\
       (!ev v. ~(lookup n refs = SOME (Thunk ev v))) /\
       (!tg fin l c r. ~(lookup n refs = SOME (bvlSem_MutBlock tg
         fin l c r))) /\
       x = gc_shared_Pointer (FAPPLY f n) (wordLang_Word (n2w 0))`)
  CHEAT_TAC;;


let MEM_IMP_v_size = cake_theorem "MEM_IMP_v_size[local]"
  (fun () ->
    `!l a. MEM a l ==> dataSem_v_size a < 1 + list_size dataSem_v_size
  l`)
  CHEAT_TAC;;

let _ = size_thms "dataSem_v";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 data_to_word_memoryProofScript.sml:389-392: the tactic that
   proves the termination *)
let get_refs_def = cake_define_list_try (fun () ->
  `MEASURE (dataSem_v_size)`)
  [`get_refs (Number _3:dataSem_v) = []`;
   `get_refs (Word64 _5:dataSem_v) = []`;
   `get_refs (CodePtr _7:dataSem_v) = []`;
   `get_refs (RefPtr _9 p:dataSem_v) = [p]`;
   `get_refs (Block _12 _13 vs:dataSem_v) = FLAT (MAP get_refs vs)`];;

let ref_edge_def = cake_define
  `ref_edge refs x res =
     (match lookup x refs with SOME (ValueArray ys) -> MEM res
       (get_refs (Block 0 ARB ys)) | SOME (Thunk _14 v) -> MEM res
       (get_refs (Block 0 ARB [v])) | SOME (bvlSem_MutBlock _15 _16 l
       c r) -> MEM res (get_refs (Block 0 ARB (l ++ [c] ++ r))) | _17
       -> F)`;;

let reachable_refs_def = cake_define
  `reachable_refs roots refs t =
     (?x r. MEM x roots /\ MEM r (get_refs x) /\ RTC (ref_edge
       refs) r t)`;;

let RefBlock_def = cake_define
  `RefBlock xs = DataElement xs (LENGTH xs) (RefTag,[])`;;

let dest_evaluated_thunk_rel = cake_inductive
  `!x. dest_evaluated_thunk_rel (ThunkBlock Evaluated x) x`;;

let bc_ref_inv_def = cake_define
  `bc_ref_inv conf n refs (f,tf,heap,be') =
     (match (FLOOKUP f n,lookup n refs) with (SOME x,SOME (ValueArray
       ys)) ->
         (?zs. heap_lookup x heap = SOME (RefBlock zs) /\
               EVERY2 (\z y. v_inv conf y refs (z,f,tf,heap)) zs ys)
                 | (SOME x,SOME (ByteArray flag bs)) ->
         (let ws = LENGTH bs DIV (dimindex (:'a) DIV 8) + 1 in
           (heap_lookup x heap = SOME (Bytes be' flag bs (REPLICATE
             ws ((n2w 0):'a word))))) | (SOME x,SOME (Thunk ev v)) ->
         (?(z:('a word_loc) heap_address).
            heap_lookup x heap = SOME (ThunkBlock ev z) /\
            (ev = Evaluated ==> dest_thunk v refs = NotThunk) /\
            v_inv conf v refs (z,f,tf,heap)) | (SOME x,SOME
              (bvlSem_MutBlock tg fin l c r)) ->
         (!gs. ~(data_to_word_config_gc_kind conf =
           data_to_word_Generational gs)) /\
         (~fin ==> ~(x IN IMAGE (FAPPLY tf) (FDOM tf))) /\
         (?zs. heap_lookup x heap = SOME (BlockRep tg zs) /\
               EVERY2 (\z y. v_inv conf y refs (z,f,tf,heap)) zs
                 (l ++ [c] ++ r)) | _18 -> F)`;;

(* TODO: MOVE *)
let _ = size_thms "dataSem_v";;
(* HOL4 data_to_word_memoryProofScript.sml:451-454: the tactic that
   proves the termination *)
let v_all_ts_def = cake_define_wf
  `MEASURE (dataSem_v_size)`
  `v_all_ts x1 =
      match x1 with
        (Block ts _20 xs:dataSem_v) -> ts :: FLAT (MAP v_all_ts xs)
      | _21 -> []`;;

let find_ref_def = cake_define
  `find_ref x1 x =
      match x1 with
        bvlSem_ValueArray l -> MEM x l
      | (Thunk m v) -> (v = x)
      | (bvlSem_MutBlock tg fin l c r) -> MEM x (l ++ [c] ++ r)
      | _22 -> F`;;

(* TODO: MOVE *)
let all_ts_def = cake_define
  `all_ts refs stack' =
     (let refs_v = {x | ?n r. sptree_lookup n refs = SOME r /\
       find_ref r x} in {ts | ?x. (x IN refs_v \/ MEM x stack') /\
       MEM ts (v_all_ts x)})`;;

let be_ok_def = cake_define
  `be_ok b1 b2 <=> b1 = b2`;;

let v_all_vs_def = cake_define
  `v_all_vs x1 =
      match x1 with
        ((Block ts tag l:dataSem_v) :: xs) -> (Block ts tag l ::
          v_all_vs l) ++ v_all_vs xs
      | (x :: xs) -> x :: v_all_vs xs
      | [] -> []`;;

let all_vs_def = cake_define
  `all_vs refs stack' =
     {v | ?(n:num) l. lookup n refs = SOME (ValueArray l) /\ MEM v
       (v_all_vs l)} UNION
     {v | ?n ev x. lookup n refs = SOME (Thunk ev x) /\ MEM v
       (v_all_vs [x])} UNION
     {v | ?n tg fin l c r. lookup n refs = SOME (bvlSem_MutBlock tg
       fin l c r) /\
                            MEM v (v_all_vs (l ++ [c] ++ r))} UNION
     {v | MEM v (v_all_vs stack')}`;;

let blocks_unique_def = cake_define
  `blocks_unique ts vs =
     (!t a1 xs1 a2 xs2.
       Block t a1 xs1 IN vs /\ ~(xs1 = []) /\
       Block t a2 xs2 IN vs /\ ~(xs2 = []) ==>
       a1 = a2 /\ xs1 = xs2 /\ t < ts)`;;

(* THIS IS IMPORTANT *)
let bc_stack_ref_inv_def = cake_define
  `bc_stack_ref_inv conf ts stack' refs (roots,heap,be') =
     (?f tf.
       INJ (FAPPLY f) (FDOM f) {a | isSomeDataElement (heap_lookup a
         heap)} /\
       FDOM f SUBSET (domain refs) /\
       INJ (FAPPLY tf) (FDOM tf) {a | isSomeDataElement (heap_lookup
         a heap)} /\
       FDOM tf SUBSET (all_ts refs stack') /\
       FDOM tf SUBSET {n | n < ts} /\ be_ok (be conf) be' /\
       blocks_unique ts (all_vs refs stack') /\
       EVERY2 (\v x. v_inv conf v refs (x,f,tf,heap)) stack' roots /\
       (!n.
         reachable_refs stack' refs n /\
         n IN FDOM f ==>
           bc_ref_inv conf n refs (f,tf,heap,be')))`;;

let data_up_to_def = cake_define
  `data_up_to a heap =
     (?h1 h2. heap_split a heap = SOME (h1,h2) /\ EVERY
       isDataElement h1)`;;

let unused_space_inv_def = cake_define
  `unused_space_inv ptr l heap <=>
     (~(l = 0) ==> (heap_lookup ptr heap = SOME (Unused (l - 1)))) /\
     ptr + l <= heap_length heap /\
     data_up_to ptr heap`;;

let isMutTag_def = cake_define
  `isMutTag t <=> t = RefTag \/ (?ev. t = ThunkTag ev)`;;

let isRef_def = cake_define
  `data_to_word_memoryProof_isRef x1 =
      match x1 with
        DataElement ys l (tag,qs) -> isMutTag tag
      | _23 -> F`;;
hol4_overload "isRef" "data_to_word_memoryProof_isRef";;

let gen_start_ok_def = cake_define
  `gen_start_ok heap refs_start gen_start =
     (?h1 h2.
       heap_split gen_start heap = SOME (h1,h2) /\
       (!xs l d p e.
         MEM (DataElement xs l d) h1 /\ MEM (gc_shared_Pointer p e)
           xs ==>
         p < gen_start \/ refs_start <= p))`;;

let gen_state_ok_def = cake_define
  `gen_state_ok a refs_start heap (GenState _24 starts) <=>
     EVERY (\s. s <= a) starts /\
     EVERY (gen_start_ok heap refs_start) starts`;;

let gc_kind_inv_def = cake_define
  `gc_kind_inv c a sp sp1 (gens:gen_state) heap <=>
     (match data_to_word_config_gc_kind c with None -> (sp1 = 0) |
       Simple -> (sp1 = 0) | data_to_word_Generational sizes ->
         gen_state_ok a (a + sp + sp1) heap gens /\
         (?h1 h2. (heap_split (a + sp + sp1) heap = SOME (h1,h2)) /\
                 EVERY (\x. ~(data_to_word_memoryProof_isRef x))
                   h1 /\ EVERY data_to_word_memoryProof_isRef h2))`;;

let abs_ml_inv_def = cake_define
  `abs_ml_inv conf stack' refs (roots,heap,be',a,sp,sp1,gens) limit' ts
  <=>
     roots_ok roots heap /\ heap_ok heap limit' /\
     gc_kind_inv conf a sp sp1 gens heap /\
     unused_space_inv a (sp + sp1) heap /\
     bc_stack_ref_inv conf ts stack' refs (roots,heap,be')`;;

(* --- *)

(* TODO: move/reorganise various things in this file *)

let word_list_limit = cake_theorem "word_list_limit"
  (fun () ->
    `EVERY isWord ws /\ ALL_DISTINCT ws ==>
      LENGTH (ws:('a word_loc) list) <= dimword (:'a)`)
  CHEAT_TAC;;

let MOD_EQ_0_0 = cake_theorem "MOD_EQ_0_0"
  (fun () ->
    `!n b. 0 < b ==> (n MOD b = 0) ==> n < b ==> (n = 0)`)
  CHEAT_TAC;;

let EVERY2_IMP_EVERY = cake_theorem "EVERY2_IMP_EVERY"
  (fun () ->
    `!xs ys. EVERY2 P xs ys ==> EVERY (\(x,y). P y x) (ZIP ys xs)`)
  CHEAT_TAC;;

let EVERY2_IMP_EVERY2 = cake_theorem "EVERY2_IMP_EVERY2"
  (fun () ->
    `!xs ys P1 P2.
        (!x y. MEM x xs /\ MEM y ys /\ P1 x y ==> P2 x y) ==>
        EVERY2 P1 xs ys ==> EVERY2 P2 xs ys`)
  CHEAT_TAC;;

let MEM_EVERY2_IMP = cake_theorem "MEM_EVERY2_IMP"
  (fun () ->
    `!l x zs P. MEM x l /\ EVERY2 P zs l ==> (?z. MEM z zs /\ P z x)`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:621-622: ML code, not
   ported *)

let EVERY2_APPEND_CONS = cake_theorem "EVERY2_APPEND_CONS"
  (fun () ->
    `!xs y ys zs P. EVERY2 P (xs ++ (y :: ys)) zs ==>
                     (?t1 t t2. (zs = t1 ++ (t :: t2)) /\ (LENGTH
                       t1 = LENGTH xs) /\
                              EVERY2 P xs t1 /\ P y t /\ EVERY2 P
                                ys t2)`)
  CHEAT_TAC;;

let EVERY2_SWAP = cake_theorem "EVERY2_SWAP"
  (fun () ->
    `!xs ys. EVERY2 P xs ys ==> EVERY2 (\y x. P x y) ys xs`)
  CHEAT_TAC;;

let EVERY2_APPEND_IMP_APPEND = cake_theorem "EVERY2_APPEND_IMP_APPEND"
  (fun () ->
    `!xs1 xs2 ys P.
        EVERY2 P (xs1 ++ xs2) ys ==>
        (?ys1 ys2. (ys = ys1 ++ ys2) /\ EVERY2 P xs1 ys1 /\
          EVERY2 P xs2 ys2)`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:654-655: ML code, not
   ported *)

(* HOL4 data_to_word_memoryProofScript.sml:657: ML code, not ported *)

(* HOL4 data_to_word_memoryProofScript.sml:659-660: ML code, not
   ported *)

let EVERY2_MAP_FST_SND = cake_theorem "EVERY2_MAP_FST_SND[local]"
  (fun () ->
    `!xs. EVERY2 P (MAP FST xs) (MAP SND xs) = EVERY (\(x,y). P x y)
  xs`)
  CHEAT_TAC;;

let fapply_fupdate_update = cake_theorem "fapply_fupdate_update"
  (fun () ->
    `(FAPPLY) (f |+ p) = (FST p =+ SND p) ((FAPPLY) f)`)
  CHEAT_TAC;;

let heap_lookup_APPEND1 = cake_theorem "heap_lookup_APPEND1[local]"
  (fun () ->
    `!h1 z h2.
       heap_length h1 <= z ==>
       (heap_lookup z (h1 ++ h2) = heap_lookup (z - heap_length
         h1) h2)`)
  CHEAT_TAC;;

let heap_lookup_APPEND2 = cake_theorem "heap_lookup_APPEND2[local]"
  (fun () ->
    `!h1 z h2.
       z < heap_length h1 ==>
       (heap_lookup z (h1 ++ h2) = heap_lookup z h1)`)
  CHEAT_TAC;;

let data_to_word_memoryProof_heap_lookup_APPEND =
  cake_theorem "heap_lookup_APPEND"
  (fun () ->
    `heap_lookup a (h1 ++ h2) =
      (if a < heap_length h1 then
      heap_lookup a h1 else
      heap_lookup (a - heap_length h1) h2)`)
  CHEAT_TAC;;

(* Prove refinement is maintained past GC calls *)

let data_to_word_memoryProof_LENGTH_ADDR_MAP =
  cake_theorem "LENGTH_ADDR_MAP[local]"
  (fun () ->
    `!xs f. LENGTH (ADDR_MAP f xs) = LENGTH xs`)
  CHEAT_TAC;;

let EL_ADDR_MAP = cake_theorem "EL_ADDR_MAP[local]"
  (fun () ->
    `!xs n f.
         n < LENGTH xs ==> (EL n (ADDR_MAP f xs) = ADDR_APPLY f
           (EL n xs))`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:719: ML code, not ported *)

let evaluated_thunk_ptr_def = cake_define
  `evaluated_thunk_ptr refs n <=> (?v. lookup n refs = SOME (Thunk
  Evaluated v))`;;

(* HOL4 data_to_word_memoryProofScript.sml:725-730: ML code, not
   ported *)

let v_inv_related_lemma = cake_theorem "v_inv_related_lemma[local]"
  (fun () ->
    `!ck w refs x f tf heap1.
       v_inv conf w refs (x,f,tf,heap1) /\
       gc_related g heap1 (heap2:(('a
         word_loc,data_to_word_memoryProof_tag#('a word_loc)
         list)heap_element) list) /\
       (!ptr u. (x = gc_shared_Pointer ptr u) ==> ptr IN FDOM g)
         ==>
         v_inv_ck ck conf w refs (ADDR_APPLY (FAPPLY g) x,g f_o_f
           f,g f_o_f tf,heap2) /\
         EVERY (\n. ~(n IN evaluated_thunk_ptr refs) ==> FAPPLY f
           n IN FDOM g) (get_refs w)`)
  CHEAT_TAC;;

let v_inv_related = cake_theorem "v_inv_related[local]"
  (fun () ->
    `!w x f tf.
       gc_related g heap1 (heap2:(('a
         word_loc,data_to_word_memoryProof_tag#('a word_loc)
         list)heap_element) list) /\
       (!ptr u. (x = gc_shared_Pointer ptr u) ==> ptr IN FDOM g) /\
       v_inv conf w refs (x,f,tf,heap1) ==>
       v_inv conf w refs (ADDR_APPLY (FAPPLY g) x,g f_o_f f,g f_o_f
         tf,heap2) /\
       EVERY (\n. ~(n IN evaluated_thunk_ptr refs) ==> FAPPLY f n
         IN FDOM g)
             (get_refs w)`)
  CHEAT_TAC;;

let EVERY2_ADDR_MAP = cake_theorem "EVERY2_ADDR_MAP[local]"
  (fun () ->
    `!zs l. EVERY2 P (ADDR_MAP g zs) l <=>
              EVERY2 (\x y. P (ADDR_APPLY g x) y) zs l`)
  CHEAT_TAC;;

let bc_ref_inv_related = cake_theorem "bc_ref_inv_related[local]"
  (fun () ->
    `gc_related g heap1 heap2 /\
       bc_ref_inv conf n refs (f,tf,heap1,be) /\ (FAPPLY f n) IN
         FDOM g ==>
       bc_ref_inv conf n refs (g f_o_f f,g f_o_f tf,heap2,be)`)
  CHEAT_TAC;;

let gc_inline_rel = cake_inductive
  `(gc_inline_rel inline h1 x x) /\
   (heap_lookup p h1 = SOME block /\
     inline block x ==>
       gc_inline_rel inline h1 (gc_shared_Pointer p u) x)`;;

let gc_heap_inline_rel = cake_inductive
  `(gc_heap_inline_rel inline h1 x x) /\
   (LIST_REL (gc_inline_rel inline h1) xs ys ==>
       gc_heap_inline_rel inline h1 (DataElement xs n d)
         (DataElement ys n d))`;;

let gc_inline_def = cake_define
  `gc_inline inline (r1,h1) (r2,h2) <=>
     LIST_REL (gc_inline_rel inline h1) r1 r2 /\
     LIST_REL (gc_heap_inline_rel inline h1) h1 h2`;;

let gc_related_roots_heap_def = cake_define
  `gc_related_roots_heap f (r1,h1) (r2,h2) <=>
     gc_related f h1 h2 /\
     r2 = ADDR_MAP ((FAPPLY) f) r1 /\
     (!ptr u. MEM (gc_shared_Pointer ptr u) r1 ==> ptr IN FDOM f)`;;

let gc_inline_related_def = cake_define
  `gc_inline_related inline f (r1,h1) (r2,h2) =
     (?ri hi. gc_inline inline (r1,h1) (ri,hi) /\
             gc_related_roots_heap f (ri,hi) (r2,h2))`;;

let gc_heap_inline_rel_heap_lookup =
  cake_theorem "gc_heap_inline_rel_heap_lookup[local]"
  (fun () ->
    `!heap1 heap2.
       LIST_REL (gc_heap_inline_rel dest_evaluated_thunk_rel heap)
         heap1 heap2 ==>
         (!a. isSomeDataElement (heap_lookup a heap1) <=>
             isSomeDataElement (heap_lookup a heap2))`)
  CHEAT_TAC;;

let ThunkBlock_not_EQ = cake_theorem "ThunkBlock_not_EQ[local]"
  (fun () ->
    `~(ThunkBlock ev x = Bignum i) /\ ~(ThunkBlock ev x = Word64Rep
  (:'a) w) /\ ~(ThunkBlock ev x = BlockRep n xs) /\ ~(ThunkBlock ev x
  = RefBlock zs) /\ ~(ThunkBlock ev x = Bytes be flag bs ys)`)
  CHEAT_TAC;;

let LIST_REL_gc_heap_inline_DataElement =
  cake_theorem "LIST_REL_gc_heap_inline_DataElement[local]"
  (fun () ->
    `!heap1 heap2.
       LIST_REL (gc_heap_inline_rel dest_evaluated_thunk_rel base)
         heap1 heap2 ==>
         (!ptr.
           heap_lookup ptr heap1 = SOME (DataElement xs n d) ==>
           (?ys.
             heap_lookup ptr heap2 = SOME (DataElement ys n d) /\
             LIST_REL (gc_inline_rel dest_evaluated_thunk_rel
               base) xs ys))`)
  CHEAT_TAC;;

let gc_heap_inline_rel_v_inv_lemma =
  cake_theorem "gc_heap_inline_rel_v_inv_lemma[local]"
  (fun () ->
    `!ck v refs x1 x2 f tf heap1 heap2.
       v_inv conf v refs (x1,f,tf,heap1) ==>
         LIST_REL (gc_heap_inline_rel dest_evaluated_thunk_rel
           heap1) heap1 heap2 /\
         (!n.
           n IN FDOM f /\
           reachable_refs [v] refs n ==>
             bc_ref_inv conf n refs (f,tf,heap1,be)) /\
         gc_inline_rel dest_evaluated_thunk_rel heap1 x1 x2 ==>
           v_inv_ck ck conf v refs (x2,f,tf,heap2)`)
  CHEAT_TAC;;

let gc_heap_inline_rel_v_inv =
  cake_theorem "gc_heap_inline_rel_v_inv[local]"
  (fun () ->
    `LIST_REL (gc_heap_inline_rel dest_evaluated_thunk_rel heap1) heap1
  heap2 /\
     (!n.
       n IN FDOM f /\
       reachable_refs [v] refs n ==>
         bc_ref_inv conf n refs (f,tf,heap1,be)) /\
     v_inv conf v refs (x1,f,tf,heap1) /\
     gc_inline_rel dest_evaluated_thunk_rel heap1 x1 x2 ==>
       v_inv conf v refs (x2,f,tf,heap2)`)
  CHEAT_TAC;;

let bc_stack_ref_inv_gc_inline =
  cake_theorem "bc_stack_ref_inv_gc_inline[local]"
  (fun () ->
    `gc_inline dest_evaluated_thunk_rel (roots1,heap1) (roots2,heap2) /\
     bc_stack_ref_inv conf ts stack refs (roots1,heap1,be) ==>
       bc_stack_ref_inv conf ts stack refs (roots2,heap2,be)`)
  CHEAT_TAC;;

let bc_stack_ref_inv_gc_related_roots_heap =
  cake_theorem "bc_stack_ref_inv_gc_related_roots_heap[local]"
  (fun () ->
    `gc_related_roots_heap g (roots1,heap1) (roots2,heap2) /\
     bc_stack_ref_inv conf ts stack refs (roots1,heap1,be) ==>
       bc_stack_ref_inv conf ts stack refs (roots2,heap2,be)`)
  CHEAT_TAC;;

let bc_stack_ref_inv_related =
  cake_theorem "bc_stack_ref_inv_related[local]"
  (fun () ->
    `gc_inline_related dest_evaluated_thunk_rel g (roots1,heap1)
  (roots2,heap2) /\
     bc_stack_ref_inv conf ts stack refs (roots1,heap1,be) ==>
       bc_stack_ref_inv conf ts stack refs (roots2,heap2,be)`)
  CHEAT_TAC;;

let data_up_to_APPEND = cake_theorem "data_up_to_APPEND[simp]"
  (fun () ->
    `data_up_to (heap_length xs) (xs ++ ys) <=> EVERY isDataElement xs`)
  CHEAT_TAC;;

let all_reachable_from_roots_def = cake_define
  `all_reachable_from_roots roots heap <=>
     (!p xs l d.
        heap_lookup p heap = SOME (DataElement xs l d) ==>
        p IN reachable_addresses roots heap)`;;

(* HOL4 data_to_word_memoryProofScript.sml:1196-1198: a theorem that
   HOL4 states as the value of an ML expression:
   IN_reachable_addresses *)

let reachable_addresses_related =
  cake_theorem "reachable_addresses_related"
  (fun () ->
    `k IN reachable_addresses roots heap /\ gc_related f heap heap2 /\
     reachable_addresses roots heap SUBSET FDOM f ==> FAPPLY
     f k IN reachable_addresses (ADDR_MAP ((FAPPLY) f) roots)
       heap2`)
  CHEAT_TAC;;

let IMP_all_reachable_from_roots =
  cake_theorem "IMP_all_reachable_from_roots"
  (fun () ->
    `FDOM f = reachable_addresses roots heap /\
     FRANGE f = {a | isSomeDataElement (heap_lookup a heap2)} /\
     gc_related f heap heap2 ==>
     all_reachable_from_roots (ADDR_MAP ((FAPPLY) f) roots) heap2`)
  CHEAT_TAC;;

let heap_lookup_expand_eq_SOME =
  cake_theorem "heap_lookup_expand_eq_SOME"
  (fun () ->
    `heap_lookup a (heap ++ heap_expand n) = SOME (DataElement ys l d)
  <=>
     heap_lookup a heap = SOME (DataElement ys l d)`)
  CHEAT_TAC;;

let isSomeDataElement_heap_lookup =
  cake_theorem "isSomeDataElement_heap_lookup"
  (fun () ->
    `isSomeDataElement (heap_lookup a (heap ++ heap_expand n)) =
     isSomeDataElement (heap_lookup a heap)`)
  CHEAT_TAC;;

let gc_related_APPEND_heap_expand =
  cake_theorem "gc_related_APPEND_heap_expand"
  (fun () ->
    `gc_related f heap (heap2 ++ heap_expand n) = gc_related f heap
  heap2`)
  CHEAT_TAC;;

let data_to_word_memoryProof_full_gc_thm = cake_theorem "full_gc_thm"
  (fun () ->
    `abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts
  /\ data_to_word_config_gc_kind
     conf = Simple ==>
      (?roots2 heap2 a2.
        (full_gc (roots,heap,limit) = (roots2,heap2,a2,T)) /\
         abs_ml_inv conf stack refs
          (roots2,heap2 ++ heap_expand (limit - a2),be,
           a2,limit - a2,0,gens) limit ts /\
        (heap_length heap2 = a2) /\
        (heap_length (heap_filter (reachable_addresses roots heap)
          heap) =
         heap_length heap2) /\
        all_reachable_from_roots roots2 (heap2 ++ heap_expand
          (limit - a2)) /\
        EVERY isDataElement heap2)`)
  CHEAT_TAC;;

let make_gc_conf_def = cake_define
  `make_gc_conf limit' =
     (mk_gen_gc_conf limit' (isMutTag o
       FST):(data_to_word_memoryProof_tag#'a) gen_gc_conf)`;;

let gc_move_data_refs_split =
  cake_theorem "gc_move_data_refs_split[local]"
  (fun () ->
    `(gen_gc_gc_move cc s x = (x1,s1)) /\ (!t r. isRef cc (t,r) <=>
  isMutTag t) /\
      EVERY isDataElement (gc_state_h2 s) /\ EVERY (\x.
        ~(data_to_word_memoryProof_isRef x)) (gc_state_h2 s) /\ EVERY
        data_to_word_memoryProof_isRef (gc_state_r4 s) ==>
      EVERY isDataElement (gc_state_h2 s1) /\
      (EVERY (\x. ~(data_to_word_memoryProof_isRef x)))
        (gc_state_h2 s1) /\ EVERY data_to_word_memoryProof_isRef
        (gc_state_r4 s1)`)
  CHEAT_TAC;;

let gc_move_list_data_refs_split =
  cake_theorem "gc_move_list_data_refs_split[local]"
  (fun () ->
    `!x x1 s s1.
     (gen_gc_gc_move_list cc s x = (x1,s1)) /\
      (!t r. (isRef cc (t,r) <=> isMutTag t)) /\ EVERY
        isDataElement (gc_state_h2 s) /\ (EVERY (\x.
        ~(data_to_word_memoryProof_isRef x))) (gc_state_h2 s) /\ EVERY
        data_to_word_memoryProof_isRef (gc_state_r4 s) ==>
      EVERY isDataElement (gc_state_h2 s1) /\ (EVERY (\x.
        ~(data_to_word_memoryProof_isRef x))) (gc_state_h2 s1) /\
        EVERY data_to_word_memoryProof_isRef (gc_state_r4 s1)`)
  CHEAT_TAC;;

let gc_move_refs_data_refs_split =
  cake_theorem "gc_move_refs_data_refs_split[local]"
  (fun () ->
    `!cc s s1.
     (gc_move_refs cc s = s1) /\
      (!t r. (isRef cc (t,r) <=> isMutTag t)) /\ EVERY
        isDataElement (gc_state_h1 s ++ gc_state_h2 s) /\ (EVERY (\x.
        ~(data_to_word_memoryProof_isRef x))) (gc_state_h1 s ++
        gc_state_h2 s) /\
      EVERY data_to_word_memoryProof_isRef (gc_state_r1 s ++
        gc_state_r2 s ++ gc_state_r3 s ++ gc_state_r4 s) ==>
      EVERY isDataElement (gc_state_h1 s1 ++ gc_state_h2 s1) /\
      (EVERY (\x. ~(data_to_word_memoryProof_isRef x)))
        (gc_state_h1 s1 ++ gc_state_h2 s1) /\
      EVERY data_to_word_memoryProof_isRef (gc_state_r1 s1 ++
        gc_state_r2 s1 ++ gc_state_r3 s1 ++ gc_state_r4 s1)`)
  CHEAT_TAC;;

let gc_move_data_data_refs_split =
  cake_theorem "gc_move_data_data_refs_split[local]"
  (fun () ->
    `!cc s s1.
     (gen_gc_gc_move_data cc s = s1) /\
      (!t r. (isRef cc (t,r) <=> isMutTag t)) /\ (EVERY (\x.
        ~(data_to_word_memoryProof_isRef x))) (gc_state_h1 s ++
        gc_state_h2 s) /\
      EVERY isDataElement (gc_state_h1 s ++ gc_state_h2 s) /\
      EVERY data_to_word_memoryProof_isRef (gc_state_r1 s ++
        gc_state_r2 s ++ gc_state_r3 s ++ gc_state_r4 s) ==>
      EVERY isDataElement (gc_state_h1 s1 ++ gc_state_h2 s1) /\
      (EVERY (\x. ~(data_to_word_memoryProof_isRef x)))
        (gc_state_h1 s1 ++ gc_state_h2 s1) /\
      EVERY data_to_word_memoryProof_isRef (gc_state_r1 s1 ++
        gc_state_r2 s1 ++ gc_state_r3 s1 ++ gc_state_r4 s1)`)
  CHEAT_TAC;;

let gc_move_loop_data_refs_split =
  cake_theorem "gc_move_loop_data_refs_split[local]"
  (fun () ->
    `!clock cc s s1.
     (gen_gc_gc_move_loop cc s clock = s1) /\
     (!t r. (isRef cc (t,r) <=> isMutTag t)) /\
     EVERY isDataElement (gc_state_h1 s ++ gc_state_h2 s) /\
     (EVERY (\x. ~(data_to_word_memoryProof_isRef x))) (gc_state_h1
       s ++ gc_state_h2 s) /\
     EVERY data_to_word_memoryProof_isRef (gc_state_r1 s ++
       gc_state_r2 s ++ gc_state_r3 s ++ gc_state_r4 s) ==>
     EVERY isDataElement (gc_state_h1 s1 ++ gc_state_h2 s1) /\
     (EVERY (\x. ~(data_to_word_memoryProof_isRef x))) (gc_state_h1
       s1 ++ gc_state_h2 s1) /\
     EVERY data_to_word_memoryProof_isRef (gc_state_r1 s1 ++
       gc_state_r2 s1 ++ gc_state_r3 s1 ++ gc_state_r4 s1)`)
  CHEAT_TAC;;

let gen_gc_data_refs_split =
  cake_theorem "gen_gc_data_refs_split[local]"
  (fun () ->
    `!cc roots heap.
     (gen_gc cc (roots,heap) = (roots1,s)) /\
     (!t r. (isRef cc (t,r) <=> isMutTag t)) ==>
     (EVERY (\x. ~(data_to_word_memoryProof_isRef x))) (gc_state_h1
       s ++ gc_state_h2 s) /\
     EVERY isDataElement (gc_state_h1 s ++ gc_state_h2 s) /\
     EVERY data_to_word_memoryProof_isRef (gc_state_r1 s ++
       gc_state_r2 s ++ gc_state_r3 s ++ gc_state_r4 s)`)
  CHEAT_TAC;;

let heap_expand_not_isRef = cake_theorem "heap_expand_not_isRef"
  (fun () ->
    `EVERY (\x. ~(data_to_word_memoryProof_isRef x)) (heap_expand n)`)
  CHEAT_TAC;;

let reset_gens_def = cake_define
  `reset_gens conf a =
     (match data_to_word_config_gc_kind conf with
       data_to_word_Generational sizes -> GenState 0 (MAP (K a)
       sizes) | _25 -> GenState 0 [])`;;

let gen_state_ok_reset = cake_theorem "gen_state_ok_reset"
  (fun () ->
    `heap_ok (h ++ heap_expand n ++ r) l ==>
      gen_state_ok (heap_length h) (n + heap_length h)
        (h ++ heap_expand n ++ r) (reset_gens conf (heap_length
          h))`)
  CHEAT_TAC;;

let data_to_word_memoryProof_gen_gc_thm = cake_theorem "gen_gc_thm"
  (fun () ->
    `abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts
  ==>
      (?roots2 state2.
        (gen_gc (make_gc_conf limit) (roots,heap) =
          (roots2,state2)) /\
        abs_ml_inv conf stack refs
          (roots2,gc_state_h1 state2 ++ heap_expand (gc_state_n
            state2) ++ gc_state_r1 state2,be,gc_state_a
           state2,gc_state_n state2,0,reset_gens conf (gc_state_a
             state2)) limit ts /\ gc_state_ok state2 /\
        (heap_length (gc_state_h1 state2 ++ gc_state_r1 state2) =
         heap_length (heap_filter (reachable_addresses roots heap)
           heap)) /\
        EVERY isDataElement (gc_state_h1 state2) /\
        EVERY isDataElement (gc_state_r1 state2) /\
        all_reachable_from_roots roots2
          (gc_state_h1 state2 ++ heap_expand (gc_state_n state2)
            ++ gc_state_r1 state2))`)
  CHEAT_TAC;;

let has_gen_def = cake_define
  `has_gen (GenState _26 xs) <=> ~(xs = [])`;;

let heap_split_heap_split = cake_theorem "heap_split_heap_split"
  (fun () ->
    `!heap n1 n2 h1 h2 h3 h4.
        heap_split n2 heap = SOME (h3,h4) /\
        heap_split n1 heap = SOME (h1,h2) /\ n1 <= n2 ==>
        (?m.
          h2 = m ++ h4 /\ h3 = h1 ++ m /\ heap = h1 ++ m ++ h4 /\
          heap_split (n2 - heap_length h1) h2 = SOME (m,h4))`)
  CHEAT_TAC;;

let heap_split_LESS_EQ = cake_theorem "heap_split_LESS_EQ"
  (fun () ->
    `!heap n x. heap_split n heap = SOME x ==> n <= heap_length heap`)
  CHEAT_TAC;;

let isRef_heap_expand = cake_theorem "isRef_heap_expand[local]"
  (fun () ->
    `!x. EVERY (\x. ~(data_to_word_memoryProof_isRef x)) (heap_expand
  x)`)
  CHEAT_TAC;;

let gen_gc_partial_thm = cake_theorem "gen_gc_partial_thm"
  (fun () ->
    `abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts
  /\
     has_gen gens /\ data_to_word_config_gc_kind conf =
       data_to_word_Generational xs ==>
      (?roots2 state2.
        partial_gc
          (make_partial_conf (make_gc_conf limit) gens (a + (sp +
            sp1)))
          (roots,heap) = (roots2,state2) /\
        abs_ml_inv conf stack refs
          (roots2,gc_state_old state2 ++ gc_state_h1 state2 ++
            heap_expand (gc_state_n state2) ++ gc_state_r1
            state2,be,gc_state_a
           state2,gc_state_n state2,0,reset_gens conf (gc_state_a
             state2)) limit ts /\ gc_state_ok state2)`)
  CHEAT_TAC;;

let data_pointers_def = cake_define
  `data_pointers x1 =
        match x1 with
          [] -> []
        | (DataElement x y z :: rest) ->
        0 :: MAP (\n. n + el_length (DataElement x y z))
          (data_pointers rest)
        | (x :: rest) ->
        MAP (\n. n + el_length x) (data_pointers rest)`;;

let lookup_len_def = cake_define
  `lookup_len heap p =
     (match heap_lookup p heap with NONE -> 0 | SOME x ->
       el_length x)`;;

let data_length_def = cake_define
  `data_length heap =
     SUM (MAP (lookup_len heap) (data_pointers heap))`;;

let data_pointers_heap_expand = cake_theorem "data_pointers_heap_expand"
  (fun () ->
    `data_pointers (heap ++ heap_expand n) = data_pointers heap`)
  CHEAT_TAC;;

let data_length_APPEND_heap_expand =
  cake_theorem "data_length_APPEND_heap_expand"
  (fun () ->
    `data_length (heap ++ heap_expand n) = data_length heap`)
  CHEAT_TAC;;

let data_length_heap_length = cake_theorem "data_length_heap_length"
  (fun () ->
    `EVERY isDataElement heap ==>
     data_length heap = heap_length heap`)
  CHEAT_TAC;;

let data_length_CONS = cake_theorem "data_length_CONS"
  (fun () ->
    `!x xs. data_length (x :: xs) = data_length [x] + data_length xs`)
  CHEAT_TAC;;

let data_length_APPEND = cake_theorem "data_length_APPEND"
  (fun () ->
    `!xs ys. data_length (xs ++ ys) = data_length xs + data_length ys`)
  CHEAT_TAC;;

let data_length_heap_expand = cake_theorem "data_length_heap_expand"
  (fun () ->
    `data_length (heap_expand n) = 0`)
  CHEAT_TAC;;

let gc_combined_thm = cake_theorem "gc_combined_thm"
  (fun () ->
    `abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts
  /\
     (do_partial ==> has_gen gens) ==>
      (?roots2 heap2 gens2 n2 a2.
        (gc_combined (make_gc_conf limit)
          (data_to_word_config_gc_kind conf)
              (roots,heap,gens,a + sp + sp1,do_partial) =
           (roots2,heap2,a2,n2,gens2,T)) /\
        abs_ml_inv conf stack refs (roots2,heap2,be,a2,n2,0,gens2)
          limit ts /\
        (~(data_to_word_config_gc_kind conf = None) /\
          (~(data_to_word_config_gc_kind conf = Simple) ==> ~do_partial)
          ==>
         all_reachable_from_roots roots2 heap2 /\
         heap_length heap2 = data_length heap2 + n2))`)
  CHEAT_TAC;;

(* Write to unused heap space is fine, e.g. cons *)

let heap_store_def = cake_define_list
  [`heap_store a y [] = ([],F)`;
   `heap_store a y (x :: xs) =
        (if a = 0 then (y ++ xs,(el_length x = heap_length y)) else
        if a < el_length x then (x :: xs,F) else
          let (xs,c) = heap_store (a - el_length x) y xs in
            (x :: xs,c))`];;

let isUnused_def = cake_define
  `isUnused x = (?k. x = Unused k)`;;

let isSomeUnused_def = cake_define
  `isSomeUnused x = (?k. x = SOME (Unused k))`;;

let heap_store_unused_def = cake_define
  `heap_store_unused a sp x xs =
     (if (heap_lookup a xs = SOME (Unused (sp - 1))) /\ el_length x
       <= sp then
       heap_store a (heap_expand (sp - el_length x) ++ [x]) xs
         else (xs,F))`;;

let heap_store_unused_alt_def = cake_define
  `heap_store_unused_alt a sp x xs =
     (if (heap_lookup a xs = SOME (Unused (sp - 1))) /\ el_length x
       <= sp then
       heap_store a ([x] ++ heap_expand (sp - el_length x)) xs
         else (xs,F))`;;

let heap_store_lemma = cake_theorem "heap_store_lemma"
  (fun () ->
    `!xs y x ys.
        heap_store (heap_length xs) y (xs ++ (x :: ys)) =
        (xs ++ y ++ ys,(heap_length y = el_length x))`)
  CHEAT_TAC;;

let heap_store_rel_def = cake_define
  `heap_store_rel heap heap2 <=>
     (!ptr. isSomeDataElement (heap_lookup ptr heap) ==>
            (heap_lookup ptr heap2 = heap_lookup ptr heap))`;;

let isSomeDataElement_heap_lookup_lemma1 =
  cake_theorem "isSomeDataElement_heap_lookup_lemma1[local]"
  (fun () ->
    `isSomeDataElement (heap_lookup n (Unused k :: xs)) <=>
       k < n /\ isSomeDataElement (heap_lookup (n - (k + 1)) xs)`)
  CHEAT_TAC;;

let isSomeDataElement_heap_lookup_lemma2 =
  cake_theorem "isSomeDataElement_heap_lookup_lemma2[local]"
  (fun () ->
    `isSomeDataElement (heap_lookup n (heap_expand k ++ xs)) <=>
       k <= n /\ isSomeDataElement (heap_lookup (n - k) xs)`)
  CHEAT_TAC;;

let isSomeDataElement_heap_lookup_lemma3 =
  cake_theorem "isSomeDataElement_heap_lookup_lemma3[local]"
  (fun () ->
    `~(n = 0) ==>
         (isSomeDataElement (heap_lookup n (x :: xs)) <=>
          el_length x <= n /\ isSomeDataElement (heap_lookup (n -
            el_length x) xs))`)
  CHEAT_TAC;;

let IMP_heap_store_unused = cake_theorem "IMP_heap_store_unused[local]"
  (fun () ->
    `unused_space_inv a sp (heap:(('a,'b)heap_element) list) /\
       el_length x <= sp ==>
       (?heap2. (heap_store_unused a sp x heap = (heap2,T)) /\
               unused_space_inv a (sp - el_length x) heap2 /\
               (heap_lookup ((a + sp) - el_length x) heap2 = SOME
                 x) /\
               ~(isSomeDataElement (heap_lookup ((a + sp) -
                 el_length x) heap)) /\
               (heap_length heap2 = heap_length heap) /\
               (~(isForwardPointer x) ==>
                (FILTER isForwardPointer heap2 = FILTER
                  isForwardPointer heap)) /\
               (!xs l d.
                  MEM (DataElement xs l d) heap2 <=>
                    (x = DataElement xs l d) \/
                    MEM (DataElement xs l d) heap) /\
               (isDataElement x ==>
                ({a | isSomeDataElement (heap_lookup a heap2)} =
                    ((
                  a + sp) - el_length x) INSERT {a |
                    isSomeDataElement (heap_lookup a heap)})) /\
               heap_store_rel heap heap2)`)
  CHEAT_TAC;;

let IMP_heap_store_unused_alt =
  cake_theorem "IMP_heap_store_unused_alt[local]"
  (fun () ->
    `unused_space_inv a sp (heap:(('a,'b)heap_element) list) /\
       el_length x <= sp ==>
       (?heap2. (heap_store_unused_alt a sp x heap = (heap2,T)) /\
               (isDataElement x ==>
                  unused_space_inv (a + el_length x) (sp -
                    el_length x) heap2) /\
               (heap_lookup a heap2 = SOME x) /\
               ~(isSomeDataElement (heap_lookup a heap)) /\
               (heap_length heap2 = heap_length heap) /\
               (~(isForwardPointer x) ==>
                (FILTER isForwardPointer heap2 = FILTER
                  isForwardPointer heap)) /\
               (!xs l d.
                  MEM (DataElement xs l d) heap2 <=>
                    (x = DataElement xs l d) \/
                    MEM (DataElement xs l d) heap) /\
               (isDataElement x ==>
                ({a | isSomeDataElement (heap_lookup a heap2)} =
                  a INSERT {a | isSomeDataElement (heap_lookup a
                    heap)})) /\
               heap_store_rel heap heap2)`)
  CHEAT_TAC;;

let heap_store_rel_lemma = cake_theorem "heap_store_rel_lemma[local]"
  (fun () ->
    `heap_store_rel h1 h2 /\ (heap_lookup n h1 = SOME (DataElement ys l
  d)) ==>
       (heap_lookup n h2 = SOME (DataElement ys l d))`)
  CHEAT_TAC;;

(* cons *)

let v_inv_SUBMAP_lemma = cake_theorem "v_inv_SUBMAP_lemma[local]"
  (fun () ->
    `!ck w refs x f tf heap.
       v_inv conf w refs (x,f,tf,heap) ==>
         f SUBMAP f1 /\
         tf SUBMAP tf1 /\
         heap_store_rel heap heap1 ==>
           v_inv_ck ck conf w refs (x,f1,tf1,heap1)`)
  CHEAT_TAC;;

let v_inv_SUBMAP = cake_theorem "v_inv_SUBMAP[local]"
  (fun () ->
    `!w x.
         f SUBMAP f1 /\ tf SUBMAP tf1 /\
         heap_store_rel heap heap1 /\
         v_inv conf w refs (x,f,tf,heap) ==>
         v_inv conf w refs (x,f1,tf1,heap1)`)
  CHEAT_TAC;;

let heap_store_rel_v_inv = cake_theorem "heap_store_rel_v_inv"
  (fun () ->
    `!w x.
         heap_store_rel heap heap1 /\
         v_inv conf w refs (x,f,tf,heap) ==>
         v_inv conf w refs (x,f,tf,heap1)`)
  CHEAT_TAC;;

let heap_store_unused_alt_thm =
  cake_theorem "heap_store_unused_alt_thm[local]"
  (fun () ->
    `!a n heap h1 h2 heap2 x.
       heap_split (a + n) heap = SOME (h1,h2) /\
       heap_store_unused_alt a n x heap = (heap2,T) /\
       unused_space_inv (a + el_length x) (n - el_length x) heap2
         ==>
       (?h0. h1 = h0 ++ [Unused (n - 1)] /\
            heap = h1 ++ h2 /\ heap_length h0 = a /\
            heap2 = h0 ++ [x] ++ heap_expand (n - el_length x) ++
              h2)`)
  CHEAT_TAC;;

let heap_store_unused_alt_heap_lookup =
  cake_theorem "heap_store_unused_alt_heap_lookup"
  (fun () ->
    `!heap heap2 a k x n.
        heap_store_unused_alt a k x heap = (heap2,T) /\ n < a ==>
        heap_lookup n heap = heap_lookup n heap2`)
  CHEAT_TAC;;

let heap_split_heap_store = cake_theorem "heap_split_heap_store[local]"
  (fun () ->
    `!heap e h1 h2 a y heap2.
       heap_split e heap = SOME (h1,h2) /\
       heap_store a y heap = (heap2,T) /\ e <= a ==>
       (?h3. heap_split e heap2 = SOME (h1,h3))`)
  CHEAT_TAC;;

let heap_store_unused_alt_gen_state_ok =
  cake_theorem "heap_store_unused_alt_gen_state_ok[local]"
  (fun () ->
    `heap_store_unused_alt a k x heap = (heap2,T) /\
     gen_state_ok a (a + k) heap gens ==>
     gen_state_ok (a + el_length x) (a + k) heap2 gens`)
  CHEAT_TAC;;

let isDataElement_lemmas = cake_theorem "isDataElement_lemmas[simp]"
  (fun () ->
    `isDataElement (DataElement x1 x2 x3) /\
      isDataElement (BlockRep tag ys1) /\
      isDataElement (Word64Rep (:'a) w) /\
      isDataElement (RefBlock ws) /\
      isDataElement (Bytes y1 y2 y3 y4) /\
      isDataElement (ThunkBlock ev v) /\
      isDataElement (Bignum i)`)
  CHEAT_TAC;;

(* --- Allocating multiple cons-elements in one go --- *)

let list_to_BlockReps_def = cake_define_list
  [`list_to_BlockReps conf t a [] = ARB`;
   `list_to_BlockReps conf t a (h :: l) =
      (match l with
        [] -> [BlockRep cons_tag [h; t]] | _28 ->
          BlockRep cons_tag
            [h; gc_shared_Pointer (a + 3) (wordLang_Word (ptr_bits
              conf cons_tag 2))] ::
              list_to_BlockReps conf t (a + 3) l)`];;

let list_to_BlockReps_heap_length =
  cake_theorem "list_to_BlockReps_heap_length"
  (fun () ->
    `!xs len.
       ~(xs = []) ==>
       heap_length (list_to_BlockReps conf x len xs) =
        3 * LENGTH xs`)
  CHEAT_TAC;;

let heap_lookup_heap_length = cake_theorem "heap_lookup_heap_length"
  (fun () ->
    `heap_lookup (heap_length h1) (h1 ++ h2) = heap_lookup 0 h2`)
  CHEAT_TAC;;

let list_to_BlockReps_heap_lookup_0 =
  cake_theorem "list_to_BlockReps_heap_lookup_0"
  (fun () ->
    `~(xs = []) ==>
     isSomeDataElement (heap_lookup 0 (list_to_BlockReps conf x
       len xs))`)
  CHEAT_TAC;;

let list_to_BlockReps_isDataElement =
  cake_theorem "list_to_BlockReps_isDataElement"
  (fun () ->
    `!xs x len.
       ~(xs = []) ==>
       EVERY isDataElement (list_to_BlockReps conf x len xs)`)
  CHEAT_TAC;;

let list_to_BlockReps_data_up_to_lem =
  cake_theorem "list_to_BlockReps_data_up_to_lem[local]"
  (fun () ->
    `~(xs = []) /\
        h1 = list_to_BlockReps conf x len xs ==>
        data_up_to (heap_length h1) (h1 ++ h2)`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:2360-2363: a theorem that
   HOL4 states as the value of an ML expression:
   list_to_BlockReps_data_up_to *)

let list_to_BlockReps_ForwardPointer =
  cake_theorem "list_to_BlockReps_ForwardPointer"
  (fun () ->
    `~(xs = []) ==> FILTER isForwardPointer (list_to_BlockReps conf x
  len xs) = []`)
  CHEAT_TAC;;

let list_to_BlockReps_Ref = cake_theorem "list_to_BlockReps_Ref"
  (fun () ->
    `!xs len x conf. ~(xs = []) ==> EVERY (\v.
  ~(data_to_word_memoryProof_isRef v)) (list_to_BlockReps conf x len
  xs)`)
  CHEAT_TAC;;

let list_to_BlockReps_NULL = cake_theorem "list_to_BlockReps_NULL"
  (fun () ->
    `~(xs = []) ==> ~(list_to_BlockReps conf x len xs = [])`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:2388-2390: a proof *)

let list_to_BlockReps_MEM = cake_theorem "list_to_BlockReps_MEM"
  (fun () ->
    `MEM v (list_to_BlockReps conf x len (h :: t)) ==>
       MEM v (list_to_BlockReps conf x (len + 3) t) \/
       v = BlockRep cons_tag
             [h; gc_shared_Pointer (len + 3) (wordLang_Word
               (ptr_bits conf cons_tag 2))] \/
       v = BlockRep cons_tag [h; x]`)
  CHEAT_TAC;;

let list_to_BlockReps_Pointer_lem =
  cake_theorem "list_to_BlockReps_Pointer_lem[local]"
  (fun () ->
    `!xs len ys l d ptr u.
        let allocd = list_to_BlockReps conf x len xs in ~(xs = [])
          /\
          MEM (DataElement ys l d) allocd /\
          MEM (gc_shared_Pointer ptr u) ys ==>
            gc_shared_Pointer ptr u = x \/
            MEM (gc_shared_Pointer ptr u) xs \/
            (ptr < len + heap_length allocd /\
             ptr > len /\
             isSomeDataElement
               (heap_lookup (ptr - len) allocd))`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:2435-2437: a theorem that
   HOL4 states as the value of an ML expression:
   list_to_BlockReps_Pointer *)

let list_to_v_get_refs = cake_theorem "list_to_v_get_refs"
  (fun () ->
    `!xs t r ts.
       MEM r (get_refs (list_to_v ts t xs)) ==>
         (?x. (MEM x xs \/ x = t) /\ MEM r (get_refs x))`)
  CHEAT_TAC;;

let v_inv_lemma = cake_theorem "v_inv_lemma"
  (fun () ->
    `!ck v refs y x f tf.
       v_inv conf v refs (x,f,tf,ha ++ heap_expand sp ++ hb) ==>
         0 < heap_length hs /\
         heap_length hs <= sp ==>
           v_inv_ck ck conf v refs (x,f,tf,
                              ha ++ hs ++ heap_expand (sp -
                                heap_length hs) ++ hb)`)
  CHEAT_TAC;;

let data_to_word_memoryProof_v_inv_lemma =
  cake_theorem "v_inv_lemma[allow_rebind]"
  (fun () ->
    `!conf v refs x f tf hs ha hb sp.
      0 < heap_length hs /\
      heap_length hs <= sp /\
      v_inv conf v refs (x,f,tf,ha ++ heap_expand sp ++ hb) ==>
      v_inv conf v refs (x,f,tf,ha ++ hs ++ heap_expand (sp -
        heap_length hs) ++ hb)`)
  CHEAT_TAC;;

let v_inv_LIST_REL = cake_theorem "v_inv_LIST_REL"
  (fun () ->
    `!l1 l2.
       0 < heap_length hs /\
       heap_length hs <= sp /\
       LIST_REL (\z y. v_inv conf y refs
         (z,f,tf,ha ++ heap_expand sp ++ hb)) l1 l2 ==>
       LIST_REL (\z y. v_inv conf y refs
         (z,f,tf,ha ++ hs ++ heap_expand (sp - heap_length hs) ++
           hb)) l1 l2`)
  CHEAT_TAC;;

let bind_each_def = cake_define_list
  [`bind_each tf ts (k:num) i 0 = tf`;
   `bind_each tf ts (k:num) i (SUC n) = bind_each tf (ts + 1) (k +
  i) i n |+ (ts,k)`];;

let bind_each_MONO = cake_theorem "bind_each_MONO"
  (fun () ->
    `!n t1 t2 tf k i.
      t1 < t2 /\ (!t. t IN FDOM tf ==> t < t1) ==> ~(t1 IN FDOM
        (bind_each tf t2 k i n))`)
  CHEAT_TAC;;

let bind_each_SUBMAP = cake_theorem "bind_each_SUBMAP"
  (fun () ->
    `!n tf ts k i.
      (!t. t IN FDOM tf ==> t < ts) ==> tf SUBMAP bind_each tf ts
        k i n`)
  CHEAT_TAC;;

let v_inv_list_to_v_lem = cake_theorem "v_inv_list_to_v_lem"
  (fun () ->
    `!rs xs t rt ha hb sp ts.
       let hm = list_to_BlockReps conf rt (heap_length ha) rs in
         ~(rs = []) /\
         v_inv conf t refs (rt,f,tf,ha ++ heap_expand sp ++ hb) /\
         LIST_REL (\v x. v_inv conf v refs (x,f,tf,ha ++
           heap_expand sp ++ hb)) xs rs /\
         heap_length hm <= sp /\ (!t. t IN FDOM tf ==> t < ts) ==>
         v_inv conf (list_to_v ts t xs) refs
           (gc_shared_Pointer (heap_length ha) (wordLang_Word
             (ptr_bits conf cons_tag 2)),
            f,bind_each tf ts (heap_length ha) 3 (LENGTH xs),
            ha ++ hm ++ heap_expand (sp - heap_length hm) ++ hb)`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:2670-2671: a theorem that
   HOL4 states as the value of an ML expression: v_inv_list_to_v *)

(* A timestamp that is not in the  *)

let all_ts_cons = cake_theorem "all_ts_cons"
  (fun () ->
    `!refs stack' ts tag xs.
       all_ts refs ((Block ts tag xs:dataSem_v) :: stack') = ts
         INSERT all_ts refs (xs ++ stack')`)
  CHEAT_TAC;;

let all_ts_cons_no_block = cake_theorem "all_ts_cons_no_block"
  (fun () ->
    `!refs stack' v.
       (!ts tag xs. ~(v = Block ts tag xs)) ==> all_ts refs (v ::
         stack') = all_ts refs stack'`)
  CHEAT_TAC;;

(* NOT USED *)
let all_ts_in_no_block = cake_theorem "all_ts_in_no_block"
  (fun () ->
    `!refs stack' v t.
       (!ts tag xs. ~(v = Block ts tag xs)) /\
       t IN all_ts refs (v :: stack') ==> t IN all_ts refs stack'`)
  CHEAT_TAC;;

let all_ts_append = cake_theorem "all_ts_append"
  (fun () ->
    `!refs x y. all_ts refs (x ++ y) = all_ts refs x UNION all_ts refs
  y`)
  CHEAT_TAC;;

let all_ts_head = cake_theorem "all_ts_head"
  (fun () ->
    `!refs x xs. all_ts refs (x :: xs) = all_ts refs [x] UNION all_ts
  refs xs`)
  CHEAT_TAC;;

let v_all_vs_MEM = cake_theorem "v_all_vs_MEM"
  (fun () ->
    `!l ts tag xs.
       MEM (Block ts tag xs) (v_all_vs l) ==> (?x y. v_all_vs l =
         x ++ (Block ts tag xs :: v_all_vs xs) ++ y)`)
  CHEAT_TAC;;

let v_in_all_vs = cake_theorem "v_in_all_vs"
  (fun () ->
    `!x y stack' refs.
       x IN all_vs refs stack' /\ MEM y (v_all_vs [x]) ==> y IN
         all_vs refs stack'`)
  CHEAT_TAC;;

let v_all_vs_MEM2 = cake_theorem "v_all_vs_MEM2"
  (fun () ->
    `!l ts tag xs.
       MEM (Block ts tag xs) (v_all_vs l) ==> (?x. MEM x l /\ MEM
         (Block ts tag xs) (v_all_vs [x]))`)
  CHEAT_TAC;;

let v_all_vs_ts = cake_theorem "v_all_vs_ts"
  (fun () ->
    `!x ts tag xs. MEM (Block ts tag xs) (v_all_vs [x]) ==> MEM ts
  (v_all_ts x)`)
  CHEAT_TAC;;

let MEM_v_all_vs = cake_theorem "MEM_v_all_vs"
  (fun () ->
    `!l v. MEM v l ==> MEM v (v_all_vs l)`)
  CHEAT_TAC;;

let MEM_stack_all_vs = cake_theorem "MEM_stack_all_vs"
  (fun () ->
    `!v stack' refs. MEM v stack' ==> v IN all_vs refs stack'`)
  CHEAT_TAC;;

let v_all_vs_ts_MEM = cake_theorem "v_all_vs_ts_MEM"
  (fun () ->
    `!x y ts. MEM ts (v_all_ts x) /\ MEM x (v_all_vs [y]) ==> MEM ts
  (v_all_ts y)`)
  CHEAT_TAC;;

let v_all_vs_trans = cake_theorem "v_all_vs_trans"
  (fun () ->
    `!x y z. MEM y (v_all_vs x) /\ MEM z (v_all_vs [y]) ==> MEM z
  (v_all_vs x)`)
  CHEAT_TAC;;

let MEM_in_all_ts = cake_theorem "MEM_in_all_ts"
  (fun () ->
    `!x ts stack' refs.
       x IN all_vs refs stack' /\ MEM ts (v_all_ts x) ==> ts IN
         all_ts refs stack'`)
  CHEAT_TAC;;

let MEM_in_all_vs = cake_theorem "MEM_in_all_vs"
  (fun () ->
    `!x y refs stack'. x IN all_vs refs stack' /\ MEM y (v_all_vs [x])
  ==> y IN all_vs refs stack'`)
  CHEAT_TAC;;

(* NOT USED *)
let v_all_vs_ts_list = cake_theorem "v_all_vs_ts_list"
  (fun () ->
    `!x y ts. MEM x (v_all_vs y) /\ MEM ts (v_all_ts x) ==> MEM ts
  (FLAT (MAP v_all_ts y))`)
  CHEAT_TAC;;

let v_inv_tf_update_thm_lemma = cake_theorem "v_inv_tf_update_thm_lemma"
  (fun () ->
    `!ck v refs y f tf heap ts' a.
       v_inv conf v refs (y,f,tf,heap) /\ ~(ts' IN FDOM tf) ==>
         v_inv_ck ck conf v refs (y,f,tf |+ (ts',a),heap)`)
  CHEAT_TAC;;

let v_inv_tf_update_thm = cake_theorem "v_inv_tf_update_thm"
  (fun () ->
    `!conf v refs y f tf heap ts' a.
       v_inv conf v refs (y,f,tf,heap) /\ ~(ts' IN FDOM tf) ==>
       v_inv conf v refs (y,f,tf |+ (ts',a),heap)`)
  CHEAT_TAC;;

let v_inv_tf_update_thm_alt_lemma =
  cake_theorem "v_inv_tf_update_thm_alt_lemma"
  (fun () ->
    `!ck v refs y f tf heap ts' a.
       v_inv conf v refs (y,f,tf,heap) /\ ~(ts' IN (all_ts refs
         stack)) /\ ~(ts' IN set_of_list (v_all_ts v)) ==>
           v_inv_ck ck conf v refs (y,f,tf |+ (ts',a),heap)`)
  CHEAT_TAC;;

let v_inv_tf_update_thm_alt = cake_theorem "v_inv_tf_update_thm_alt"
  (fun () ->
    `!conf v refs y f tf heap ts' a stack'.
       v_inv conf v refs (y,f,tf,heap) /\ ~(ts' IN (all_ts refs
         stack')) /\ ~(ts' IN set_of_list (v_all_ts v)) ==>
       v_inv conf v refs (y,f,tf |+ (ts',a),heap)`)
  CHEAT_TAC;;

let v_inv_tf_update_lemma = cake_theorem "v_inv_tf_update_lemma"
  (fun () ->
    `!ck v1 refs v2.
       v_inv conf v1 refs v2 ==>
         (!ts tag xs y f tf heap.
           v1 = (Block ts tag xs) /\
           v2 = (y,f,tf,heap) /\
           v1 IN (all_vs refs stack) /\ ~(ts' IN all_ts refs stack)
             ==>
             v_inv_ck ck conf v1 refs (y,f,tf |+ (ts',a),heap))`)
  CHEAT_TAC;;

let v_inv_tf_update = cake_theorem "v_inv_tf_update"
  (fun () ->
    `!conf refs y f tf heap heap1 a stack' ts ts' tag xs.
        (Block ts tag xs) IN (all_vs refs stack') /\ ~(ts' IN
          all_ts refs stack') /\
        v_inv conf (Block ts tag xs) refs (y,f,tf,heap) ==> v_inv
          conf ((Block ts tag xs)) refs (y,f,tf |+ (ts',a),heap)`)
  CHEAT_TAC;;

let v_inv_tf_restrict_lemma = cake_theorem "v_inv_tf_restrict_lemma"
  (fun () ->
    `!ck v1 refs y f tf heap.
       v_inv conf v1 refs (y,f,tf,heap) ==>
           (!x. MEM x (v_all_ts v1) ==> x IN P) /\
           (!x. x IN (all_ts refs stack) ==> x IN P) ==>
             v_inv_ck ck conf v1 refs (y,f,DRESTRICT tf P,heap)`)
  CHEAT_TAC;;

let v_inv_tf_restrict = cake_theorem "v_inv_tf_restrict"
  (fun () ->
    `!conf v refs stack' y f tf heap P.
        v_inv conf v refs (y,f,tf,heap) /\
        (!x. MEM x (v_all_ts v) ==> x IN P) /\
        (!x. x IN (all_ts refs stack') ==> x IN P) ==>
          v_inv conf v refs (y,f,DRESTRICT tf P,heap)`)
  CHEAT_TAC;;

let v_all_vs_append = cake_theorem "v_all_vs_append"
  (fun () ->
    `!x y. v_all_vs (x ++ y) = v_all_vs x ++ v_all_vs y`)
  CHEAT_TAC;;

let MEM_v_all_vs_split = cake_theorem "MEM_v_all_vs_split"
  (fun () ->
    `!x v xs. MEM x (v_all_vs (v :: xs)) ==> MEM x (v_all_vs [v]) \/
  MEM x (v_all_vs xs)`)
  CHEAT_TAC;;

let MEM_v_all_vs_split2 = cake_theorem "MEM_v_all_vs_split2"
  (fun () ->
    `MEM x (v_all_vs (v :: y :: xs)) ==>
       MEM x (v_all_vs (v :: xs)) \/ MEM x (v_all_vs [y])`)
  CHEAT_TAC;;

let MEM_v_all_vs_extend_tl = cake_theorem "MEM_v_all_vs_extend_tl"
  (fun () ->
    `!x v xs. MEM x (v_all_vs [v]) ==> MEM x (v_all_vs (v :: xs))`)
  CHEAT_TAC;;

let MEM_v_all_vs_extend_hd = cake_theorem "MEM_v_all_vs_extend_hd"
  (fun () ->
    `!x v xs. MEM x (v_all_vs xs) ==> MEM x (v_all_vs (v :: xs))`)
  CHEAT_TAC;;

let MEM_v_all_vs_extend_append =
  cake_theorem "MEM_v_all_vs_extend_append"
  (fun () ->
    `MEM x (v_all_vs xs) ==> MEM x (v_all_vs (xs ++ ys))`)
  CHEAT_TAC;;

let MEM_v_all_vs_EL = cake_theorem "MEM_v_all_vs_EL"
  (fun () ->
    `!xs i x.
       i < LENGTH xs /\
       MEM x (v_all_vs [EL i xs]) ==>
         MEM x (v_all_vs xs)`)
  CHEAT_TAC;;

let MEM_v_all_vs_LUPDATE = cake_theorem "MEM_v_all_vs_LUPDATE"
  (fun () ->
    `!xs i v x.
       MEM x (v_all_vs (LUPDATE v i xs)) ==>
         MEM x (v_all_vs [v]) \/ MEM x (v_all_vs xs)`)
  CHEAT_TAC;;

let all_vs_Block = cake_theorem "all_vs_Block"
  (fun () ->
    `all_vs refs ((Block t tag xs:dataSem_v) :: ys) =
     Block t tag xs INSERT all_vs refs (xs ++ ys)`)
  CHEAT_TAC;;

let blocks_unique_cons_thm = cake_theorem "blocks_unique_cons_thm"
  (fun () ->
    `blocks_unique ts s ==>
     blocks_unique (ts + 1) (Block ts tag xs INSERT s)`)
  CHEAT_TAC;;

let cons_thm_alt = cake_theorem "cons_thm_alt"
  (fun () ->
    `abs_ml_inv conf (xs ++ stack) refs (roots,heap,be,a,sp,sp1,gens)
  limit ts /\
      LENGTH xs < sp /\ ~(xs = []) ==>
      (?rs roots2 heap2.
        (roots = rs ++ roots2) /\ (LENGTH rs = LENGTH xs) /\
        (heap_store_unused_alt a (sp + sp1) (BlockRep tag rs) heap
          = (heap2,T)) /\
        abs_ml_inv conf
          ((Block ts tag xs) :: stack) refs
          (gc_shared_Pointer a (wordLang_Word (ptr_bits conf tag
            (LENGTH xs))) :: roots2,
           heap2,be,a + el_length (BlockRep tag rs),
           sp - el_length (BlockRep tag rs),sp1,gens) limit (ts +
             1))`)
  CHEAT_TAC;;

let cons_thm_EMPTY = cake_theorem "cons_thm_EMPTY"
  (fun () ->
    `abs_ml_inv conf stack refs (roots,(heap:(('a
  word_loc,data_to_word_memoryProof_tag#('a word_loc) list)heap_element)
  list),be,a,sp,sp1,gens) limit ts /\
      tag < dimword (:'a) DIV 16 ==>
      abs_ml_inv conf ((Block 0 tag []) :: stack) refs
        (gc_shared_Data (wordLang_Word (BlockNil tag)) ::
          roots,heap,be,a,sp,sp1,gens) limit ts`)
  CHEAT_TAC;;

(* word64 *)

let blocks_unique_Word64 = cake_theorem "blocks_unique_Word64"
  (fun () ->
    `blocks_unique ts (all_vs refs (ws ++ stack)) ==>
       blocks_unique ts (all_vs refs (Word64 w64 :: stack))`)
  CHEAT_TAC;;

let word64_alt_thm = cake_theorem "word64_alt_thm"
  (fun () ->
    `abs_ml_inv conf (ws ++ stack) refs (rs ++
  roots,heap,be,a,sp,sp1,gens) limit ts /\
     LENGTH ws = LENGTH rs /\
     (Word64Rep (:'a) w64:('a
       word_loc,data_to_word_memoryProof_tag#('a word_loc)
       list)heap_element) = DataElement [] len (Word64Tag,xs) /\
      LENGTH xs < sp ==>
     (?heap2.
       heap_store_unused_alt a (sp + sp1) (Word64Rep (:'a) w64)
         heap = (heap2,T) /\
       abs_ml_inv conf (Word64 w64 :: stack) refs
         (gc_shared_Pointer a (wordLang_Word (n2w 0)) ::
           roots,heap2,
          be,a + len + 1,sp - len - 1,sp1,gens) limit ts)`)
  CHEAT_TAC;;

(* bignum *)

let blocks_unique_Number = cake_theorem "blocks_unique_Number"
  (fun () ->
    `blocks_unique ts (all_vs refs (ws ++ stack)) ==>
       blocks_unique ts (all_vs refs (Number i :: stack))`)
  CHEAT_TAC;;

let bignum_alt_thm = cake_theorem "bignum_alt_thm"
  (fun () ->
    `abs_ml_inv conf (ws ++ stack) refs (rs ++
  roots,heap,be,a,sp,sp1,gens) limit ts /\
     LENGTH ws = LENGTH rs /\ ~(small_int (:'a) i) /\
     (Bignum i:('a word_loc,data_to_word_memoryProof_tag#('a
       word_loc) list)heap_element) = DataElement [] len (tag,xs) /\
     LENGTH xs < sp ==>
     (?heap2.
       heap_store_unused_alt a (sp + sp1) (Bignum i) heap =
         (heap2,T) /\
       abs_ml_inv conf (Number i :: stack) refs
         (gc_shared_Pointer a (wordLang_Word ((n2w 0):'a word))
           :: roots,heap2,be,a + len + 1,sp - len - 1,sp1,gens) limit
           ts)`)
  CHEAT_TAC;;

(* update ref *)

let ref_edge_ValueArray = cake_theorem "ref_edge_ValueArray[local]"
  (fun () ->
    `ref_edge (insert ptr (ValueArray xs) refs) x y =
       (if x = ptr then MEM y (get_refs (Block 0 ARB xs)) else
         ref_edge refs x y)`)
  CHEAT_TAC;;

let ref_edge_Thunk = cake_theorem "ref_edge_Thunk[local]"
  (fun () ->
    `ref_edge (insert ptr (Thunk ev v) refs) x y =
       (if x = ptr then MEM y (get_refs (Block 0 ARB [v])) else
         ref_edge refs x y)`)
  CHEAT_TAC;;

let reachable_refs_UPDATE = cake_theorem "reachable_refs_UPDATE[local]"
  (fun () ->
    `reachable_refs (xs ++ (RefPtr b ptr :: stack)) (insert ptr
  (ValueArray xs) refs) n ==>
       reachable_refs (xs ++ (RefPtr b ptr :: stack)) refs n`)
  CHEAT_TAC;;

let reachable_refs_Thunk_UPDATE =
  cake_theorem "reachable_refs_Thunk_UPDATE[local]"
  (fun () ->
    `reachable_refs (v :: RefPtr b ptr :: stack) (insert ptr (Thunk ev
  v) refs) n ==>
       reachable_refs (v :: RefPtr b ptr :: stack) refs n`)
  CHEAT_TAC;;

let reachable_refs_UPDATE1 =
  cake_theorem "reachable_refs_UPDATE1[local]"
  (fun () ->
    `reachable_refs (xs ++ (RefPtr b ptr :: stack)) (insert ptr
  (ValueArray xs1) refs) n ==>
       (!v. MEM v xs1 ==> ~(MEM v xs) ==> (?xs2. (lookup ptr refs =
         SOME (ValueArray xs2)) /\ MEM v xs2)) ==>
       reachable_refs (xs ++ (RefPtr b ptr :: stack)) refs n`)
  CHEAT_TAC;;

let v_inv_ByteArray_insert_lemma =
  cake_theorem "v_inv_ByteArray_insert_lemma"
  (fun () ->
    `!ck v1 refs y f tf heap.
       v_inv conf v1 refs (y,f,tf,heap) /\
         (ptr IN domain refs ==> (?a b. lookup ptr refs = SOME
           (ByteArray a b))) ==>
           v_inv_ck ck conf v1 (insert ptr (ByteArray fl xs)
             refs) (y,f,tf,heap)`)
  CHEAT_TAC;;

let v_inv_ByteArray_insert = cake_theorem "v_inv_ByteArray_insert"
  (fun () ->
    `!conf v1 refs v2 f tf heap ptr fl xs.
       v_inv conf v1 refs (v2,f,tf,heap) /\
       (ptr IN domain refs ==> (?a b. lookup ptr refs = SOME
         (ByteArray a b))) ==>
         v_inv conf v1 (insert ptr (ByteArray fl xs) refs)
           (v2,f,tf,heap)`)
  CHEAT_TAC;;

let isRefBlock_def = cake_define
  `isRefBlock x = (?p. x = RefBlock p)`;;

let RefBlock_inv_def = cake_define
  `RefBlock_inv heap heap2 <=>
     (!n x. (heap_lookup n heap = SOME x) /\ ~(isRefBlock x) ==>
            (heap_lookup n heap2 = SOME x)) /\
     (!n x. (heap_lookup n heap2 = SOME x) /\ ~(isRefBlock x) ==>
            (heap_lookup n heap = SOME x))`;;

let heap_store_RefBlock_thm = cake_theorem "heap_store_RefBlock_thm"
  (fun () ->
    `!ha. (LENGTH x = LENGTH y) ==>
           (heap_store (heap_length ha) [RefBlock x] (ha ++
             (RefBlock y :: hb)) =
             (ha ++ (RefBlock x :: hb),T))`)
  CHEAT_TAC;;

let heap_lookup_RefBlock_lemma =
  cake_theorem "heap_lookup_RefBlock_lemma[local]"
  (fun () ->
    `(heap_lookup n (ha ++ (RefBlock y :: hb)) = SOME x) =
         (if n < heap_length ha then
           (heap_lookup n ha = SOME x) else if n = heap_length ha
             then
           (x = RefBlock y) else if heap_length ha + (LENGTH y + 1)
             <= n then
           (heap_lookup (n - heap_length ha - (LENGTH y + 1)) hb
             = SOME x) else F)`)
  CHEAT_TAC;;

let heap_store_RefBlock = cake_theorem "heap_store_RefBlock[local]"
  (fun () ->
    `(LENGTH y = LENGTH h) /\
       (heap_lookup n heap = SOME (RefBlock y)) ==>
       (?heap2. (heap_store n [RefBlock h] heap = (heap2,T)) /\
               RefBlock_inv heap heap2 /\
               (heap_lookup n heap2 = SOME (RefBlock h)) /\
               (heap_length heap2 = heap_length heap) /\
               (FILTER isForwardPointer heap2 = FILTER
                 isForwardPointer heap) /\
               (!xs l d.
                  MEM (DataElement xs l d) heap2 ==> (DataElement
                    xs l d = RefBlock h) \/
                              MEM (DataElement xs l d) heap) /\
               (!a. isSomeDataElement (heap_lookup a heap2) =
                    isSomeDataElement (heap_lookup a heap)) /\
               (!m x. ~(m = n) /\ (heap_lookup m heap = SOME x) ==>
                     (heap_lookup m heap2 = SOME x)))`)
  CHEAT_TAC;;

let NOT_isRefBlock = cake_theorem "NOT_isRefBlock[local]"
  (fun () ->
    `~(isRefBlock (Bignum x)) /\
       ~(isRefBlock (Word64Rep a w)) /\
       ~(isRefBlock (DataElement xs (LENGTH xs) (BlockTag n,[])))`)
  CHEAT_TAC;;

let v_inv_Ref_lemma = cake_theorem "v_inv_Ref_lemma[local]"
  (fun () ->
    `!ck w refs x f tf heap.
       v_inv conf w refs (x,f,tf,heap) /\
       RefBlock_inv heap heap2 ==>
         v_inv_ck ck conf w refs (x,f,tf,heap) = v_inv_ck ck conf
           w refs (x,f,tf,heap2)`)
  CHEAT_TAC;;

let v_inv_Ref = cake_theorem "v_inv_Ref[local]"
  (fun () ->
    `RefBlock_inv heap heap2 ==>
       (!x h f tf. (v_inv conf x refs (h,f,tf,heap2) =
                   v_inv conf x refs (h,f,tf,heap)))`)
  CHEAT_TAC;;

let v_inv_ValueArray_insert_lemma =
  cake_theorem "v_inv_ValueArray_insert_lemma"
  (fun () ->
    `!ck v1 refs y f tf heap.
       v_inv conf v1 refs (y,f,tf,heap) /\
         RefBlock_inv heap heap2 /\
         (ptr IN domain refs ==> (?as. lookup ptr refs = SOME
           (ValueArray as))) ==>
           v_inv_ck ck conf v1 (insert ptr (ValueArray xs) refs)
             (y,f,tf,heap)`)
  CHEAT_TAC;;

let v_inv_ValueArray_insert = cake_theorem "v_inv_ValueArray_insert"
  (fun () ->
    `!conf v1 refs v2 f tf heap ptr xs heap2.
       RefBlock_inv heap heap2 /\
       v_inv conf v1 refs (v2,f,tf,heap) /\
       (ptr IN domain refs ==> (?as. lookup ptr refs = SOME
         (ValueArray as))) ==>
         v_inv conf v1 (insert ptr (ValueArray xs) refs)
           (v2,f,tf,heap2)`)
  CHEAT_TAC;;

(* inserting a *fresh* MutBlock ref cannot disturb any existing v_inv: the only
   way v_inv inspects refs is through a RefPtr, and those are confined to
   FDOM f, which sits inside domain refs *)
let v_inv_MutBlock_insert_lemma =
  cake_theorem "v_inv_MutBlock_insert_lemma"
  (fun () ->
    `!ck v1 refs y f tf heap.
       v_inv conf v1 refs (y,f,tf,heap) /\
       ~(ptr IN domain refs) /\ FDOM f SUBSET domain refs ==>
         v_inv_ck ck conf v1 (insert ptr (bvlSem_MutBlock tag fin
           l cv r) refs) (y,f,tf,heap)`)
  CHEAT_TAC;;

let v_inv_MutBlock_insert = cake_theorem "v_inv_MutBlock_insert"
  (fun () ->
    `!conf v1 refs v2 f tf heap ptr tag fin l cv r.
       v_inv conf v1 refs (v2,f,tf,heap) /\
       ~(ptr IN domain refs) /\ FDOM f SUBSET domain refs ==>
         v_inv conf v1 (insert ptr (bvlSem_MutBlock tag fin l cv
           r) refs) (v2,f,tf,heap)`)
  CHEAT_TAC;;

(* v_inv cannot see a MutBlock's finalised flag: ref_ptr_annot ignores it and
   dest_thunk sends every MutBlock to NotThunk.  Flipping the flag therefore
   preserves v_inv -- this is what makes FinaliseCons a no-op at word level. *)
let v_inv_MutBlock_fin_lemma =
  cake_theorem "v_inv_MutBlock_fin_lemma[local]"
  (fun () ->
    `!ck v1 refs y f tf heap.
       v_inv conf v1 refs (y,f,tf,heap) /\
       lookup ptr refs = SOME (bvlSem_MutBlock tag fin1 ll cv rr)
         ==>
         v_inv_ck ck conf v1 (insert ptr (bvlSem_MutBlock tag fin2
           ll cv rr) refs)
           (y,f,tf,heap)`)
  CHEAT_TAC;;

(* bound variables deliberately avoid the names used at the use sites, so that
   irule/MATCH_MP_TAC does not fail on a free/bound name clash *)
let v_inv_MutBlock_fin = cake_theorem "v_inv_MutBlock_fin"
  (fun () ->
    `!cnf vv rfs yy ff tff hp pp tg b1 b2 l1 c1 r1.
       v_inv cnf vv rfs (yy,ff,tff,hp) /\
       lookup pp rfs = SOME (bvlSem_MutBlock tg b1 l1 c1 r1) ==>
         v_inv cnf vv (insert pp (bvlSem_MutBlock tg b2 l1 c1 r1)
           rfs) (yy,ff,tff,hp)`)
  CHEAT_TAC;;

(* ---- MutCons: the Cons allocation, but the value handed back is a fresh ref *)

let all_ts_SUBSET_gen = cake_theorem "all_ts_SUBSET_gen[local]"
  (fun () ->
    `(!x. ((?n r'. lookup n refs1 = SOME r' /\ find_ref r' x) \/ MEM x
  stack1) ==>
          ((?n r'. lookup n refs2 = SOME r' /\ find_ref r' x) \/
            MEM x stack2)) ==>
     all_ts refs1 stack1 SUBSET all_ts refs2 stack2`)
  CHEAT_TAC;;

(* like all_ts_SUBSET_gen, but the witness on the right may be a different
   value, as long as it carries the timestamp -- needed when a value only
   survives inside a newly built Block *)
let all_ts_SUBSET_ts = cake_theorem "all_ts_SUBSET_ts[local]"
  (fun () ->
    `(!x t. (((?n r'. lookup n refs1 = SOME r' /\ find_ref r' x) \/ MEM
  x stack1) /\
             MEM t (v_all_ts x)) ==>
            (?x'. ((?n r'. lookup n refs2 = SOME r' /\ find_ref r'
              x') \/
                  MEM x' stack2) /\ MEM t (v_all_ts x'))) ==>
     all_ts refs1 stack1 SUBSET all_ts refs2 stack2`)
  CHEAT_TAC;;

let all_ts_mutcons = cake_theorem "all_ts_mutcons[local]"
  (fun () ->
    `~(ptr IN domain refs) ==>
       all_ts refs ((l ++ [c] ++ r) ++ stack) SUBSET
       all_ts (insert ptr (bvlSem_MutBlock tag F l c r) refs)
         (RefPtr F ptr :: stack)`)
  CHEAT_TAC;;

let blocks_unique_mutcons = cake_theorem "blocks_unique_mutcons[local]"
  (fun () ->
    `blocks_unique ts (all_vs refs ((l ++ [c] ++ r) ++ stack)) ==>
     blocks_unique ts
       (all_vs (insert ptr (bvlSem_MutBlock tag F l c r) refs)
         (RefPtr F ptr :: stack))`)
  CHEAT_TAC;;

let ref_edge_MutBlock = cake_theorem "ref_edge_MutBlock[local]"
  (fun () ->
    `ref_edge (insert ptr (bvlSem_MutBlock tag fin l c r) refs) x y =
       (if x = ptr then MEM y (get_refs (Block 0 ARB (l ++ [c] ++
         r))) else ref_edge refs x y)`)
  CHEAT_TAC;;

(* the only new edge leaves ptr and lands inside the payload, which is exactly
   what used to sit on the stack *)
let reachable_refs_MutCons_lemma =
  cake_theorem "reachable_refs_MutCons_lemma[local]"
  (fun () ->
    `!r1 n.
       RTC (ref_edge (insert ptr (bvlSem_MutBlock tag F l c r)
         refs)) r1 n ==> ~(n = ptr) ==>
       RTC (ref_edge refs) r1 n \/
       (?s. MEM s (get_refs (Block 0 ARB (l ++ [c] ++ r))) /\ RTC
         (ref_edge refs) s n)`)
  CHEAT_TAC;;

let reachable_refs_MutCons =
  cake_theorem "reachable_refs_MutCons[local]"
  (fun () ->
    `reachable_refs (RefPtr F ptr :: stack)
       (insert ptr (bvlSem_MutBlock tag F l c r) refs) n /\ ~(n =
         ptr) /\ ~(ptr IN domain refs) ==>
     reachable_refs ((l ++ [c] ++ r) ++ stack) refs n`)
  CHEAT_TAC;;

(* lifting a v_inv across the MutCons allocation: refs gains a fresh ref and f
   gains its binding, and the heap only grew *)
let v_inv_MutCons_step = cake_theorem "v_inv_MutCons_step[local]"
  (fun () ->
    `v_inv conf v refs (y,f,tf,heap) /\ ~(ptr IN domain refs) /\
     FDOM f SUBSET domain refs /\ heap_store_rel heap heap2 ==>
       v_inv conf v (insert ptr (bvlSem_MutBlock tag F l c r) refs)
         (y,f |+ (ptr,a),tf,heap2)`)
  CHEAT_TAC;;

let take_el_drop = cake_theorem "take_el_drop[local]"
  (fun () ->
    `!index vals. index < LENGTH vals ==>
       TAKE index vals ++ [EL index vals] ++ DROP (index + 1)
         vals = vals`)
  CHEAT_TAC;;

(* a value that is not a thunk cannot become one by adding a fresh ref *)
let dest_thunk_insert_fresh =
  cake_theorem "dest_thunk_insert_fresh[local]"
  (fun () ->
    `~(ptr IN domain refs) /\ dest_thunk v refs = NotThunk ==>
       dest_thunk v (insert ptr x refs) = NotThunk`)
  CHEAT_TAC;;

(* mirrors cons_thm_alt: the allocation is the Cons allocation, but the value
   handed back is a RefPtr into refs, so f (not tf) gains a binding and no
   timestamp is consumed *)
let mutcons_thm_alt = cake_theorem "mutcons_thm_alt[local]"
  (fun () ->
    `abs_ml_inv conf (l ++ [c] ++ r ++ stack) refs
                (roots,heap,be,a,sp,sp1,gens) limit ts /\
     LENGTH (l ++ [c] ++ r) < sp /\ ~(ptr IN domain refs) /\
     (!gs. ~(data_to_word_config_gc_kind conf =
       data_to_word_Generational gs)) ==>
     (?rs roots2 heap2.
       (roots = rs ++ roots2) /\ (LENGTH rs = LENGTH (l ++ [c] ++
         r)) /\
       (heap_store_unused_alt a (sp + sp1) (BlockRep tag rs) heap =
         (heap2,T)) /\
       abs_ml_inv conf (RefPtr F ptr :: stack)
         (insert ptr (bvlSem_MutBlock tag F l c r) refs)
         (gc_shared_Pointer a (wordLang_Word (ptr_bits conf tag
           (LENGTH (l ++ [c] ++ r)))) :: roots2,
          heap2,be,a + el_length (BlockRep tag rs),
          sp - el_length (BlockRep tag rs),sp1,gens) limit ts)`)
  CHEAT_TAC;;

let mutcons_thm = cake_theorem "mutcons_thm[local]"
  (fun () ->
    `abs_ml_inv conf (xs ++ stack) refs (roots,heap,be,a,sp,sp1,gens)
  limit ts /\
     LENGTH xs < sp /\ index < LENGTH xs /\ ~(ptr IN domain refs)
       /\
     (!gs. ~(data_to_word_config_gc_kind conf =
       data_to_word_Generational gs)) ==>
     (?rs roots2 heap2.
       (roots = rs ++ roots2) /\ (LENGTH rs = LENGTH xs) /\
       (heap_store_unused_alt a (sp + sp1) (BlockRep tag rs) heap =
         (heap2,T)) /\
       abs_ml_inv conf (RefPtr F ptr :: stack)
         (insert ptr (bvlSem_MutBlock tag F (TAKE index xs) (EL
           index xs)
                              (DROP (index + 1) xs)) refs)
         (gc_shared_Pointer a (wordLang_Word (ptr_bits conf tag
           (LENGTH xs))) :: roots2,
          heap2,be,a + el_length (BlockRep tag rs),
          sp - el_length (BlockRep tag rs),sp1,gens) limit ts)`)
  CHEAT_TAC;;

let heap_store_ThunkBlock_thm = cake_theorem "heap_store_ThunkBlock_thm"
  (fun () ->
    `!ha.
       (heap_store (heap_length ha) [ThunkBlock ev1 v1] (ha ++
         (ThunkBlock ev2 v2 :: hb)) =
       (ha ++ (ThunkBlock ev1 v1 :: hb),T))`)
  CHEAT_TAC;;

let heap_lookup_ThunkBlock_lemma =
  cake_theorem "heap_lookup_ThunkBlock_lemma[local]"
  (fun () ->
    `(heap_lookup n (ha ++ (ThunkBlock ev v :: hb)) = SOME x) =
         (if n < heap_length ha then
           (heap_lookup n ha = SOME x) else if n = heap_length ha
             then
           (x = ThunkBlock ev v) else if heap_length ha + 2 <= n
             then
           (heap_lookup (n - heap_length ha - 2) hb = SOME x)
             else F)`)
  CHEAT_TAC;;

let heap_store_ThunkBlock = cake_theorem "heap_store_ThunkBlock[local]"
  (fun () ->
    `(heap_lookup n heap = SOME (ThunkBlock NotEvaluated y)) ==>
     (?heap2.
       heap_store n [ThunkBlock ev h] heap = (heap2,T) /\
       (heap_lookup n heap2 = SOME (ThunkBlock ev h)) /\
       (heap_length heap2 = heap_length heap) /\
       (FILTER isForwardPointer heap2 = FILTER isForwardPointer
         heap) /\
       (!xs l d.
          MEM (DataElement xs l d) heap2 ==>
            (DataElement xs l d = ThunkBlock ev h) \/
            MEM (DataElement xs l d) heap) /\
       (!a. isSomeDataElement (heap_lookup a heap2) =
            isSomeDataElement (heap_lookup a heap)) /\
       (!m x. ~(m = n) /\ (heap_lookup m heap = SOME x) ==>
             (heap_lookup m heap2 = SOME x)))`)
  CHEAT_TAC;;

let INJ_NEQ = cake_theorem "INJ_NEQ"
  (fun () ->
    `INJ (FAPPLY f) (FDOM f) {a | isSomeDataElement (heap_lookup a
  heap)} /\
     n IN FDOM f /\
     ptr IN FDOM f /\ ~(n = ptr) ==> ~((FAPPLY f n) = (FAPPLY f
       ptr))`)
  CHEAT_TAC;;

let v_inv_Thunk_insert_lemma =
  cake_theorem "v_inv_Thunk_insert_lemma[local]"
  (fun () ->
    `!ck v1 refs x f tf heap ptr v y q.
       v_inv conf v1 refs (x,f,tf,heap) /\
       INJ (FAPPLY f) (FDOM f) {a | isSomeDataElement (heap_lookup
         a heap)} /\
       ptr IN FDOM f /\
       lookup ptr refs = SOME (Thunk NotEvaluated v) /\
       heap_lookup (FAPPLY f ptr) heap = SOME (ThunkBlock
         NotEvaluated y) /\
       v_inv conf v refs (y,f,tf,heap) /\
       (ev = Evaluated ==> dest_thunk h refs = NotThunk) /\
       heap_store (FAPPLY f ptr) [ThunkBlock ev q] heap = (heap2,T)
         /\
       heap_lookup (FAPPLY f ptr) heap2 = SOME (ThunkBlock ev q) /\
       (!m x. ~(m = FAPPLY f ptr) /\ heap_lookup m heap = SOME x
         ==>
          heap_lookup m heap2 = SOME x) /\
       v_inv conf h refs (q,f,tf,heap) ==>
         v_inv_ck ck conf v1 (insert ptr (Thunk ev h) refs)
           (x,f,tf,heap2)`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:4636-4640: a theorem that
   HOL4 states as the value of an ML expression: v_inv_Thunk_insert *)

let heap_lookup_heap_split =
  cake_theorem "heap_lookup_heap_split[local]"
  (fun () ->
    `!heap a b h1 h2 x.
       heap_split a heap = SOME (h1,h2) /\
       heap_lookup b heap = SOME x ==>
       (if b < a then MEM x h1 else MEM x h2)`)
  CHEAT_TAC;;

let heap_store_heap_lookup = cake_theorem "heap_store_heap_lookup"
  (fun () ->
    `!heap heap2 a x n.
        heap_store a x heap = (heap2,T) /\ n < a ==>
        heap_lookup n heap = heap_lookup n heap2`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:4680-4689: a theorem that
   HOL4 states as the value of an ML expression:
   update_ref_gen_state_ok *)

let data_up_to_alt = cake_theorem "data_up_to_alt[local]"
  (fun () ->
    `(data_up_to n [] <=> (n = 0)) /\
     (data_up_to n (x :: xs) <=>
        (if n = 0 then T else
        if n < el_length x \/ ~(isDataElement x) then F else
          data_up_to (n - el_length x) xs))`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:4704-4713: a theorem that
   HOL4 states as the value of an ML expression:
   update_thunk_gen_state_ok *)

let data_up_to_heap_store = cake_theorem "data_up_to_heap_store"
  (fun () ->
    `!heap a b heap2 y.
        data_up_to a heap /\ heap_store b [y] heap = (heap2,T) /\
        isDataElement y ==> data_up_to a heap2`)
  CHEAT_TAC;;

let blocks_unique_update_ref = cake_theorem "blocks_unique_update_ref"
  (fun () ->
    `blocks_unique ts (all_vs refs (xs ++ (RefPtr b ptr :: stack))) ==>
       blocks_unique ts
         (all_vs (insert ptr (ValueArray xs) refs)
            (xs ++ (RefPtr b ptr :: stack)))`)
  CHEAT_TAC;;

let update_ref_thm = cake_theorem "update_ref_thm"
  (fun () ->
    `abs_ml_inv conf (xs ++ ((RefPtr b ptr) :: stack)) refs
      (roots,heap,be,a,sp,sp1,gens) limit ts /\
      (lookup ptr refs = SOME (ValueArray xs1)) /\ (LENGTH xs =
        LENGTH xs1) ==>
      (?p rs roots2 heap2 u.
        (roots = rs ++ (gc_shared_Pointer p u :: roots2)) /\
        (heap_store p [RefBlock rs] heap = (heap2,T)) /\
        abs_ml_inv conf (xs ++ ((RefPtr b ptr) :: stack)) (insert
          ptr (ValueArray xs) refs)
          (roots,heap2,be,a,sp,sp1,gens) limit ts)`)
  CHEAT_TAC;;

let blocks_unique_update_ref1 = cake_theorem "blocks_unique_update_ref1"
  (fun () ->
    `0 < LENGTH xs /\
     lookup ptr refs = SOME (ValueArray xs1) /\
     blocks_unique ts (all_vs refs (xs ++ (RefPtr b ptr :: stack)))
       ==>
       blocks_unique ts
         (all_vs (insert ptr (ValueArray (LUPDATE (HD xs) i xs1))
           refs)
            (xs ++ (RefPtr b ptr :: stack)))`)
  CHEAT_TAC;;

let heap_deref_def = cake_define
  `(heap_deref a heap =
     (match heap_lookup a heap with SOME (DataElement xs l
       (RefTag,[])) -> SOME xs | _29 -> NONE))`;;

let update_ref_thm1 = cake_theorem "update_ref_thm1"
  (fun () ->
    `abs_ml_inv conf (xs ++ (RefPtr b ptr :: stack)) refs
      (roots,heap,be,a,sp,sp1,gens) limit ts /\
      (lookup ptr refs = SOME (ValueArray xs1)) /\ i < LENGTH xs1
        /\ 0 < LENGTH xs ==>
      (?p rs roots2 vs1 heap2 u.
        (roots = rs ++ (gc_shared_Pointer p u :: roots2)) /\
          (LENGTH rs = LENGTH xs) /\
        (heap_deref p heap = SOME vs1) /\ LENGTH vs1 = LENGTH xs1
          /\
        (heap_store p [RefBlock (LUPDATE (HD rs) i vs1)] heap =
          (heap2,T)) /\
        abs_ml_inv conf (xs ++ ((RefPtr b ptr) :: stack))
          (insert ptr (ValueArray (LUPDATE (HD xs) i xs1)) refs)
          (roots,heap2,be,a,sp,sp1,gens) limit ts)`)
  CHEAT_TAC;;

let blocks_unique_update_thunk =
  cake_theorem "blocks_unique_update_thunk"
  (fun () ->
    `blocks_unique ts (all_vs refs (h :: RefPtr F ptr :: stack)) ==>
       blocks_unique ts
         (all_vs (insert ptr (Thunk ev h) refs) (h :: RefPtr F
           ptr :: stack))`)
  CHEAT_TAC;;

let thunk_deref_def = cake_define
  `(thunk_deref a heap =
     (match heap_lookup a heap with SOME (DataElement xs l
       (ThunkTag NotEvaluated,[])) -> SOME xs | _30 -> NONE))`;;

let update_thunk_thm = cake_theorem "update_thunk_thm"
  (fun () ->
    `abs_ml_inv conf (h :: RefPtr F ptr :: stack) refs
                (roots,heap,be,a,sp,sp1,gens) limit ts /\
     (lookup ptr refs = SOME (Thunk NotEvaluated v)) /\
     (ev = Evaluated ==> dest_thunk h refs = NotThunk) ==>
       (?p r roots2 v1 heap2 u.
         (roots = r :: gc_shared_Pointer p u :: roots2) /\
         (thunk_deref p heap = SOME v1) /\
         (heap_store p [ThunkBlock ev r] heap = (heap2,T)) /\
         abs_ml_inv conf (h :: (RefPtr F ptr) :: stack)
           (insert ptr (Thunk ev h) refs)
           (roots,heap2,be,a,sp,sp1,gens) limit ts)`)
  CHEAT_TAC;;

(* ---- UpdateCons: writing the hole of an unfinalised MutBlock.  The cell is
   laid out as a BlockRep, so the heap-level machinery is the RefBlock/
   ThunkBlock machinery transposed to BlockRep.  What is new is that v_inv can
   read BlockRep cells, so rewriting one is only safe because no timestamp
   points at an unfinalised MutBlock -- exactly what bc_ref_inv records. *)

let heap_store_BlockRep_thm =
  cake_theorem "heap_store_BlockRep_thm[local]"
  (fun () ->
    `!ha. (LENGTH x = LENGTH y) ==>
          (heap_store (heap_length ha) [BlockRep tag x] (ha ++
            (BlockRep tag y :: hb)) =
            (ha ++ (BlockRep tag x :: hb),T))`)
  CHEAT_TAC;;

let heap_lookup_BlockRep_lemma =
  cake_theorem "heap_lookup_BlockRep_lemma[local]"
  (fun () ->
    `(heap_lookup n (ha ++ (BlockRep tag y :: hb)) = SOME x) =
         (if n < heap_length ha then
           (heap_lookup n ha = SOME x) else if n = heap_length ha
             then
           (x = BlockRep tag y) else if heap_length ha + (LENGTH y
             + 1) <= n then
           (heap_lookup (n - heap_length ha - (LENGTH y + 1)) hb
             = SOME x) else F)`)
  CHEAT_TAC;;

let heap_store_BlockRep = cake_theorem "heap_store_BlockRep[local]"
  (fun () ->
    `(LENGTH y = LENGTH h) /\
     (heap_lookup n heap = SOME (BlockRep tag y)) ==>
     (?heap2. (heap_store n [BlockRep tag h] heap = (heap2,T)) /\
             (heap_lookup n heap2 = SOME (BlockRep tag h)) /\
             (heap_length heap2 = heap_length heap) /\
             (FILTER isForwardPointer heap2 = FILTER
               isForwardPointer heap) /\
             (!xs l d.
                MEM (DataElement xs l d) heap2 ==>
                  (DataElement xs l d = BlockRep tag h) \/
                  MEM (DataElement xs l d) heap) /\
             (!a. isSomeDataElement (heap_lookup a heap2) =
                  isSomeDataElement (heap_lookup a heap)) /\
             (!m x. ~(m = n) /\ (heap_lookup m heap = SOME x) ==>
                   (heap_lookup m heap2 = SOME x)))`)
  CHEAT_TAC;;

(* v_inv survives an in-place rewrite of a BlockRep cell that no timestamp
   points at: Bignum/Word64Rep/ThunkBlock cells cannot be that cell because
   their tags differ, and a Block's cell is in the range of tf *)
let v_inv_BlockRep_upd_lemma =
  cake_theorem "v_inv_BlockRep_upd_lemma[local]"
  (fun () ->
    `!ck conf v1 refs x f tf heap heap2 p tag zs.
       v_inv conf v1 refs (x,f,tf,heap) /\
       heap_lookup p heap = SOME (BlockRep tag zs) /\
       (!t. t IN FDOM tf ==> ~(FAPPLY tf t = p)) /\
       (!m y. ~(m = p) /\ heap_lookup m heap = SOME y ==>
         heap_lookup m heap2 = SOME y) ==>
         v_inv_ck ck conf v1 refs (x,f,tf,heap2)`)
  CHEAT_TAC;;

(* the binders are renamed apart from the names used at the application sites,
   so that qexists can name the witnesses *)
(* HOL4 data_to_word_memoryProofScript.sml:5514-5518: a theorem that
   HOL4 states as the value of an ML expression: v_inv_BlockRep_upd *)

(* v_inv cannot see what sits in a MutBlock's hole, only how long the two
   sides of it are *)
let v_inv_MutBlock_hole_lemma =
  cake_theorem "v_inv_MutBlock_hole_lemma[local]"
  (fun () ->
    `!ck v1 refs y f tf heap.
       v_inv conf v1 refs (y,f,tf,heap) /\
       lookup ptr refs = SOME (bvlSem_MutBlock tag fin1 ll cv1 rr)
         ==>
         v_inv_ck ck conf v1 (insert ptr (bvlSem_MutBlock tag fin2
           ll cv2 rr) refs)
           (y,f,tf,heap)`)
  CHEAT_TAC;;

let v_inv_MutBlock_hole = cake_theorem "v_inv_MutBlock_hole[local]"
  (fun () ->
    `!cnf vv rfs yy ff tff hp pp tg b1 b2 l1 c1 c2 r1.
       v_inv cnf vv rfs (yy,ff,tff,hp) /\
       lookup pp rfs = SOME (bvlSem_MutBlock tg b1 l1 c1 r1) ==>
         v_inv cnf vv (insert pp (bvlSem_MutBlock tg b2 l1 c2 r1)
           rfs) (yy,ff,tff,hp)`)
  CHEAT_TAC;;

let blocks_unique_update_mutblock =
  cake_theorem "blocks_unique_update_mutblock[local]"
  (fun () ->
    `lookup ptr refs = SOME (bvlSem_MutBlock tag fin l cv r) /\
     blocks_unique ts (all_vs refs (h :: RefPtr F ptr :: stack))
       ==>
       blocks_unique ts
         (all_vs (insert ptr (bvlSem_MutBlock tag fin l h r) refs)
                 (h :: RefPtr F ptr :: stack))`)
  CHEAT_TAC;;

let ref_edge_MutBlock_UPDATE =
  cake_theorem "ref_edge_MutBlock_UPDATE[local]"
  (fun () ->
    `lookup ptr refs = SOME (bvlSem_MutBlock tg fin ll cc rr) /\
     ref_edge (insert ptr (bvlSem_MutBlock tg fin ll h rr) refs) r1
       z /\
     ~(MEM z (get_refs h)) ==> ref_edge refs r1 z`)
  CHEAT_TAC;;

(* the only new edges out of ptr land in the value that was written, which is
   itself on the stack *)
let reachable_refs_MutBlock_UPDATE =
  cake_theorem "reachable_refs_MutBlock_UPDATE[local]"
  (fun () ->
    `lookup ptr refs = SOME (bvlSem_MutBlock tg fin ll cc rr) /\
     reachable_refs (h :: RefPtr b ptr :: stack)
                    (insert ptr (bvlSem_MutBlock tg fin ll h rr)
                      refs) n ==>
       reachable_refs (h :: RefPtr b ptr :: stack) refs n`)
  CHEAT_TAC;;

(* mirrors update_thunk_thm: the hole is rewritten in place, so f and the heap
   layout are untouched and only tf shrinks *)
let update_mutblock_thm = cake_theorem "update_mutblock_thm[local]"
  (fun () ->
    `abs_ml_inv conf (h :: RefPtr F ptr :: stack) refs
                (roots,heap,be,a,sp,sp1,gens) limit ts /\
     (lookup ptr refs = SOME (bvlSem_MutBlock tag F l cv r)) ==>
       (?p rr roots2 vs1 heap2 u.
         (roots = rr :: gc_shared_Pointer p u :: roots2) /\
         (heap_lookup p heap = SOME (BlockRep tag vs1)) /\
         (LENGTH vs1 = LENGTH l + 1 + LENGTH r) /\
         (heap_store p [BlockRep tag (LUPDATE rr (LENGTH l) vs1)]
           heap = (heap2,T)) /\
         abs_ml_inv conf (h :: RefPtr F ptr :: stack)
           (insert ptr (bvlSem_MutBlock tag F l h r) refs)
           (roots,heap2,be,a,sp,sp1,gens) limit ts)`)
  CHEAT_TAC;;

(* update byte ref *)

let LENGTH_write_bytes = cake_theorem "LENGTH_write_bytes[simp]"
  (fun () ->
    `!ws bs be'. LENGTH (write_bytes bs ws be') = LENGTH ws`)
  CHEAT_TAC;;

let LIST_REL_IMP_LIST_REL = cake_theorem "LIST_REL_IMP_LIST_REL[local]"
  (fun () ->
    `!xs ys.
         (!x y. MEM x xs ==> P x y ==> Q x y) ==>
         LIST_REL P xs ys ==> LIST_REL Q xs ys`)
  CHEAT_TAC;;

let v_size_LESS_EQ = cake_theorem "v_size_LESS_EQ[local]"
  (fun () ->
    `!l x. MEM x l ==> dataSem_v_size x <= list_size dataSem_v_size l`)
  CHEAT_TAC;;

let v_inv_IMP_lemma = cake_theorem "v_inv_IMP_lemma[local]"
  (fun () ->
    `!ck w refs x f tf.
       v_inv conf w refs (x,f,tf,ha ++ [Bytes be fl xs ws] ++ hb)
         ==>
         v_inv_ck ck conf w refs (x,f,tf,ha ++ [Bytes be fl ys
           ws] ++ hb)`)
  CHEAT_TAC;;

let v_inv_IMP = cake_theorem "v_inv_IMP[local]"
  (fun () ->
    `!y x f tf ha.
         v_inv conf y refs (x,f,tf,ha ++ [Bytes be fl xs ws] ++ hb)
           ==>
         v_inv conf y refs (x,f,tf,ha ++ [Bytes be fl ys ws] ++
           hb)`)
  CHEAT_TAC;;

let gen_state_ok_update_byte =
  cake_theorem "gen_state_ok_update_byte[local]"
  (fun () ->
    `gen_state_ok a k (ha ++ [Bytes be fl xs ws] ++ hb) gens ==>
     gen_state_ok a k (ha ++ [Bytes be fl ys ws] ++ hb) gens`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:5900-5902: a theorem that
   HOL4 states as the value of an ML expression: heap_length_Bytes *)

let unused_space_inv_byte_update =
  cake_theorem "unused_space_inv_byte_update[local]"
  (fun () ->
    `unused_space_inv a (sp + sp1)
         (ha ++ [Bytes be fl xs (REPLICATE ws (n2w 0))] ++ hb) ==>
     unused_space_inv a (sp + sp1)
         (ha ++ [Bytes be fl ys (REPLICATE ws (n2w 0))] ++ hb)`)
  CHEAT_TAC;;

let blocks_unique_insert_ByteArray =
  cake_theorem "blocks_unique_insert_ByteArray"
  (fun () ->
    `blocks_unique ts (all_vs refs (RefPtr b ptr :: stack)) ==>
       blocks_unique ts
         (all_vs (insert ptr (ByteArray fl ys) refs) (RefPtr b
           ptr :: stack))`)
  CHEAT_TAC;;

let update_byte_ref_thm = cake_theorem "update_byte_ref_thm"
  (fun () ->
    `abs_ml_inv conf ((RefPtr b ptr) :: stack) refs
  (roots,heap,be,a,sp,sp1,gens) limit ts /\
      (lookup ptr refs = SOME (ByteArray fl xs)) /\ (LENGTH xs =
        LENGTH ys) ==>
      (?roots2 h1 h2 ws.
        (roots = gc_shared_Pointer (heap_length h1) ((wordLang_Word
          (n2w 0)):'a word_loc) :: roots2) /\
        heap = h1 ++ [Bytes be fl xs ws] ++ h2 /\
        LENGTH ws = LENGTH xs DIV (dimindex (:'a) DIV 8) + 1 /\
        abs_ml_inv conf ((RefPtr b ptr) :: stack) (insert ptr
          (ByteArray fl ys) refs)
          (roots,h1 ++ [Bytes be fl ys ws] ++
            h2,be,a,sp,sp1,gens) limit ts)`)
  CHEAT_TAC;;

let heap_store_unused_thm = cake_theorem "heap_store_unused_thm[local]"
  (fun () ->
    `!a n heap h1 h2 heap2 x.
       heap_split (a + n) heap = SOME (h1,h2) /\
       heap_store_unused a n x heap = (heap2,T) /\
       unused_space_inv a (n - el_length x) heap2 ==>
       (?h0. h1 = h0 ++ [Unused (n - 1)] /\
            heap = h1 ++ h2 /\ heap_length h0 = a /\
            heap2 = h0 ++ heap_expand (n - el_length x) ++ [x] ++
              h2)`)
  CHEAT_TAC;;

let heap_store_unused_heap_lookup =
  cake_theorem "heap_store_unused_heap_lookup"
  (fun () ->
    `!heap heap2 a k x n.
        heap_store_unused a k x heap = (heap2,T) /\ n < a ==>
        heap_lookup n heap = heap_lookup n heap2`)
  CHEAT_TAC;;

let heap_store_unused_gen_state_ok =
  cake_theorem "heap_store_unused_gen_state_ok[local]"
  (fun () ->
    `heap_store_unused a k x heap = (heap2,T) /\
     gen_state_ok a (a + k) heap gens ==>
     gen_state_ok a ((a + k) - el_length x) heap2 gens`)
  CHEAT_TAC;;

(* new ref *)

let blocks_unique_new_ref = cake_theorem "blocks_unique_new_ref"
  (fun () ->
    `blocks_unique ts (all_vs refs (xs ++ stack)) ==>
       blocks_unique ts
         (all_vs (insert ptr (ValueArray xs) refs)
            (xs ++ (RefPtr T ptr :: stack)))`)
  CHEAT_TAC;;

let new_ref_thm = cake_theorem "new_ref_thm"
  (fun () ->
    `abs_ml_inv conf (xs ++ stack) refs (roots,heap,be,a,sp,sp1,gens)
  limit ts /\
      ~(ptr IN (domain refs)) /\ LENGTH xs + 1 <= sp ==>
      (?p rs roots2 heap2.
        (roots = rs ++ roots2) /\ LENGTH rs = LENGTH xs /\
        (heap_store_unused a (sp + sp1) (RefBlock rs) heap =
          (heap2,T)) /\
        abs_ml_inv conf (xs ++ ((RefPtr T ptr) :: stack)) (insert
          ptr (ValueArray xs) refs)
                   (rs ++ (gc_shared_Pointer ((a + sp + sp1) -
                     (LENGTH xs + 1)) (wordLang_Word (n2w 0)) ::
                     roots2),heap2,be,a,
                    sp - (LENGTH xs + 1),sp1,gens) limit ts)`)
  CHEAT_TAC;;

let v_inv_new_Thunk_insert_lemma =
  cake_theorem "v_inv_new_Thunk_insert_lemma[local]"
  (fun () ->
    `!ck v refs x f tf heap ptr.
       v_inv conf v refs (x,f,tf,heap) /\ ~(ptr IN FDOM f) /\ ~(ptr
         IN domain refs) /\
       (ev = Evaluated ==> dest_thunk h refs = NotThunk) ==>
         v_inv_ck ck conf v (insert ptr (Thunk ev h) refs)
           (x,f,tf,heap)`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:6472-6476: a theorem that
   HOL4 states as the value of an ML expression:
   v_inv_new_Thunk_insert *)

let blocks_unique_new_thunk = cake_theorem "blocks_unique_new_thunk"
  (fun () ->
    `blocks_unique ts (all_vs refs (v :: stack)) ==>
       blocks_unique ts
         (all_vs (insert ptr (Thunk ev v) refs) (v :: RefPtr F
           ptr :: stack))`)
  CHEAT_TAC;;

let new_thunk_thm = cake_theorem "new_thunk_thm"
  (fun () ->
    `abs_ml_inv conf (v :: stack) refs (roots,heap,be,a,sp,sp1,gens)
  limit ts /\
      ~(ptr IN (domain refs)) /\ 2 <= sp /\
      (ev = Evaluated ==> dest_thunk v refs = NotThunk) ==>
      (?p r roots2 heap2.
        (roots = r :: roots2) /\
        (heap_store_unused a (sp + sp1) (ThunkBlock ev r) heap =
          (heap2,T)) /\
        abs_ml_inv conf (v :: (RefPtr F ptr) :: stack) (insert ptr
          (Thunk ev v) refs)
                   (r :: gc_shared_Pointer ((a + sp + sp1) - 2)
                     (wordLang_Word (n2w 0)) :: roots2,heap2,be,a,
                    sp - 2,sp1,gens) limit ts)`)
  CHEAT_TAC;;

(* deref *)

let heap_el_def = cake_define
  `heap_el x1 n heap =
        match x1 with
          gc_shared_Pointer a u ->
       (match heap_lookup a heap with SOME (DataElement xs l d) ->
           (if n < LENGTH xs then (EL n xs,T) else (ARB,F)) | _31 ->
             (ARB,F))
        | _32 -> (ARB,F)`;;

let blocks_unique_deref1 = cake_theorem "blocks_unique_deref1"
  (fun () ->
    `lookup ptr refs = SOME (Thunk NotEvaluated a') /\
     blocks_unique ts (all_vs refs (RefPtr F ptr :: stack)) ==>
       blocks_unique ts (all_vs refs (a' :: RefPtr F ptr ::
         stack))`)
  CHEAT_TAC;;

let blocks_unique_deref2 = cake_theorem "blocks_unique_deref2"
  (fun () ->
    `n < LENGTH l /\
     lookup ptr refs = SOME (ValueArray l) /\
     blocks_unique ts (all_vs refs (RefPtr b ptr :: stack)) ==>
       blocks_unique ts (all_vs refs (EL n l :: RefPtr b ptr ::
         stack))`)
  CHEAT_TAC;;

let deref_thm = cake_theorem "deref_thm"
  (fun () ->
    `abs_ml_inv conf (RefPtr b ptr :: stack) refs
  (roots,heap,be,a,sp,sp1,gens) limit ts ==>
      (?r roots2.
        (roots = r :: roots2) /\ ptr IN (domain refs) /\
        (match THE (lookup ptr refs) with ByteArray _33 _34 -> T |
          bvlSem_MutBlock _35 _36 _37 _38 _39 -> T | ValueArray vs ->
        (!n. n < LENGTH vs ==>
            (?y. (heap_el r n heap = (y,T)) /\
                  abs_ml_inv conf (EL n vs :: RefPtr b ptr ::
                    stack) refs
                    (y :: roots,heap,be,a,sp,sp1,gens) limit ts)) |
                      Thunk Evaluated v -> T | Thunk NotEvaluated v ->
        (?y. (heap_el r 0 heap = (y,T)) /\
              abs_ml_inv conf (v :: RefPtr b ptr :: stack) refs
                (y :: roots,heap,be,a,sp,sp1,gens) limit ts)))`)
  CHEAT_TAC;;

(* el *)

let blocks_unique_el = cake_theorem "blocks_unique_el"
  (fun () ->
    `i < LENGTH xs /\
     blocks_unique ts (all_vs refs (Block t0 n xs :: stack)) ==>
       blocks_unique ts (all_vs refs (EL i xs :: Block t0 n xs ::
         stack))`)
  CHEAT_TAC;;

let el_thm = cake_theorem "el_thm"
  (fun () ->
    `abs_ml_inv conf (Block t0 n xs :: stack) refs
  (roots,heap,be,a,sp,sp1,gens) limit ts /\
      i < LENGTH xs ==>
      (?r roots2 y.
        (roots = r :: roots2) /\ (heap_el r i heap = (y,T)) /\
        abs_ml_inv conf (EL i xs :: Block t0 n xs :: stack) refs
                        (y :: roots,heap,be,a,sp,sp1,gens) limit
                          ts)`)
  CHEAT_TAC;;

(* new byte array *)

let blocks_unique_new_byte_alt =
  cake_theorem "blocks_unique_new_byte_alt"
  (fun () ->
    `blocks_unique ts (all_vs refs stack) ==>
       blocks_unique ts
         (all_vs (insert ptr (ByteArray fl bs) refs) (RefPtr b
           ptr :: stack))`)
  CHEAT_TAC;;

let new_byte_alt_thm = cake_theorem "new_byte_alt_thm"
  (fun () ->
    `abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts
  /\
     Abbrev (ws = LENGTH bs DIV (dimindex (:'a) DIV 8) + 1) /\
     ~(ptr IN (domain refs)) /\ ws + 1 <= sp ==>
     (?heap2.
       (heap_store_unused_alt a (sp + sp1)
         (Bytes be fl bs (REPLICATE ws ((n2w 0):'a word))) heap =
           (heap2,T)) /\
       abs_ml_inv conf ((RefPtr b ptr) :: stack) (insert ptr
         (ByteArray fl bs) refs)
                  (gc_shared_Pointer a (wordLang_Word (n2w 0)) ::
                    roots,heap2,be,a + ws + 1,
                   sp - (ws + 1),sp1,gens) limit ts)`)
  CHEAT_TAC;;

(* equality *)

let ref_eq_thm = cake_theorem "ref_eq_thm"
  (fun () ->
    `abs_ml_inv conf (RefPtr T p1 :: RefPtr T p2 :: stack) refs
        (r1 :: r2 :: roots,heap,be,a,sp,sp1,gens) limit ts ==>
      ((p1 = p2) <=> (r1 = r2)) /\
      (?p1 p2. r1 = gc_shared_Pointer p1 (wordLang_Word (n2w 0))
        /\ r2 = gc_shared_Pointer p2 (wordLang_Word (n2w 0)))`)
  CHEAT_TAC;;

let num_eq_thm = cake_theorem "num_eq_thm"
  (fun () ->
    `abs_ml_inv conf (Number i1 :: Number i2 :: stack) refs
       (r1 :: r2 :: roots,heap,be,a,sp,sp1,gens) limit ts /\
     small_int (:'a) i1 /\
     small_int (:'a) i2 ==>
     ((i1 = i2) <=> (r1 = r2)) /\
     r1 = gc_shared_Data (wordLang_Word (Smallnum i1:'a word)) /\
     r2 = gc_shared_Data (wordLang_Word (Smallnum i2))`)
  CHEAT_TAC;;

let smallnum_i2w = cake_theorem "Smallnum_i2w"
  (fun () ->
    `Smallnum i = i2w ((&4) * i)`)
  CHEAT_TAC;;

let small_int_IMP_MIN_MAX = cake_theorem "small_int_IMP_MIN_MAX"
  (fun () ->
    `good_dimindex (:'a) /\ small_int (:'a) i ==>
      INT_MIN (:'a) <= (&4) * i /\ (&4) * i <= INT_MAX (:'a)`)
  CHEAT_TAC;;

let num_less_thm = cake_theorem "num_less_thm"
  (fun () ->
    `good_dimindex (:'a) /\ small_int (:'a) i1 /\ small_int (:'a) i2 ==>
      ((i1 < i2) <=> (Smallnum i1 < (Smallnum i2:'a word)))`)
  CHEAT_TAC;;

(* permute stack *)

let all_ts_permute = cake_theorem "all_ts_permute"
  (fun () ->
    `!(refs:(dataSem_v bvlSem_ref) spt) stack' stack'.
       PERM stack' stack' ==> all_ts refs stack' = all_ts refs
         stack'`)
  CHEAT_TAC;;

let reachable_refs_stack_subset =
  cake_theorem "reachable_refs_stack_subset"
  (fun () ->
    `!x y refs n. reachable_refs y refs n /\ set_of_list y SUBSET
  set_of_list x ==> reachable_refs x refs n`)
  CHEAT_TAC;;

let MEM_v_all_vs_FST = cake_theorem "MEM_v_all_vs_FST"
  (fun () ->
    `!xs h0 h1 x.
     MEM (h0,h1) xs /\
     MEM x (v_all_vs [h0]) ==>
       MEM x (v_all_vs (MAP FST xs))`)
  CHEAT_TAC;;

let MEM_v_all_vs_SUBSET = cake_theorem "MEM_v_all_vs_SUBSET"
  (fun () ->
    `!ys xs x.
       set_of_list ys SUBSET set_of_list xs /\
       MEM x (v_all_vs (MAP FST ys)) ==>
         MEM x (v_all_vs (MAP FST xs))`)
  CHEAT_TAC;;

let blocks_unique_stack_permute =
  cake_theorem "blocks_unique_stack_permute"
  (fun () ->
    `set_of_list ys SUBSET set_of_list xs /\
     blocks_unique ts (all_vs refs (MAP FST xs ++ stack)) ==>
       blocks_unique ts (all_vs refs (MAP FST ys ++ stack))`)
  CHEAT_TAC;;

let abs_ml_inv_stack_permute = cake_theorem "abs_ml_inv_stack_permute"
  (fun () ->
    `!xs ys.
         abs_ml_inv conf (MAP FST xs ++ stack) refs
           (MAP SND xs ++ roots,heap,be,a,sp,sp1,gens) limit ts /\
         set_of_list ys SUBSET set_of_list xs ==>
         abs_ml_inv conf (MAP FST ys ++ stack) refs
           (MAP SND ys ++ roots,heap,be,a,sp,sp1,gens) limit ts`)
  CHEAT_TAC;;

(* pop *)

let pop_thm = cake_theorem "pop_thm"
  (fun () ->
    `abs_ml_inv conf (xs ++ stack) refs (rs ++
  roots,heap,be,a,sp,sp1,gens) limit ts /\
      (LENGTH xs = LENGTH rs) ==>
      abs_ml_inv conf (stack) refs (roots,heap,be,a,sp,sp1,gens)
        limit ts`)
  CHEAT_TAC;;

(* duplicate *)

let blocks_unique_duplicate = cake_theorem "blocks_unique_duplicate"
  (fun () ->
    `blocks_unique ts (all_vs refs (xs ++ stack)) ==>
       blocks_unique ts (all_vs refs (xs ++ xs ++ stack))`)
  CHEAT_TAC;;

let duplicate_thm = cake_theorem "duplicate_thm"
  (fun () ->
    `abs_ml_inv conf (xs ++ stack) refs (rs ++
  roots,heap,be,a,sp,sp1,gens) limit ts /\
     (LENGTH xs = LENGTH rs) ==>
     abs_ml_inv conf (xs ++ xs ++ stack) refs (rs ++ rs ++
       roots,heap,be,a,sp,sp1,gens) limit ts`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:7427-7429: a theorem that
   HOL4 states as the value of an ML expression: duplicate1_thm *)

(* move *)

let blocks_unique_move = cake_theorem "blocks_unique_move"
  (fun () ->
    `blocks_unique ts (all_vs refs (xs1 ++ xs2 ++ xs3 ++ stack)) ==>
       blocks_unique ts (all_vs refs (xs1 ++ xs3 ++ xs2 ++
         stack))`)
  CHEAT_TAC;;

let move_thm = cake_theorem "move_thm"
  (fun () ->
    `!xs1 rs1 xs2 rs2 xs3 rs3.
        abs_ml_inv conf (xs1 ++ xs2 ++ xs3 ++ stack) refs
                        (rs1 ++ rs2 ++ rs3 ++
                          roots,heap,be,a,sp,sp1,gens) limit ts /\
        (LENGTH xs1 = LENGTH rs1) /\
        (LENGTH xs2 = LENGTH rs2) /\
        (LENGTH xs3 = LENGTH rs3) ==>
        abs_ml_inv conf (xs1 ++ xs3 ++ xs2 ++ stack) refs
                        (rs1 ++ rs3 ++ rs2 ++
                          roots,heap,be,a,sp,sp1,gens) limit ts`)
  CHEAT_TAC;;

(* splits *)

let split1_thm = cake_theorem "split1_thm"
  (fun () ->
    `abs_ml_inv conf (xs1 ++ stack) refs (roots,heap,be,a,sp,sp1,gens)
  limit ts ==>
      (?rs1 roots1. (roots = rs1 ++ roots1) /\ (LENGTH rs1 =
        LENGTH xs1))`)
  CHEAT_TAC;;

let split2_thm = cake_theorem "split2_thm"
  (fun () ->
    `abs_ml_inv conf (xs1 ++ xs2 ++ stack) refs
  (roots,heap,be,a,sp,sp1,gens) limit ts ==>
      (?rs1 rs2 roots1. (roots = rs1 ++ rs2 ++ roots1) /\
        (LENGTH rs1 = LENGTH xs1) /\ (LENGTH rs2 = LENGTH xs2))`)
  CHEAT_TAC;;

let split3_thm = cake_theorem "split3_thm"
  (fun () ->
    `abs_ml_inv conf (xs1 ++ xs2 ++ xs3 ++ stack) refs
  (roots,heap,be,a,sp,sp1,gens) limit ts ==>
      (?rs1 rs2 rs3 roots1. (roots = rs1 ++ rs2 ++ rs3 ++ roots1)
        /\
        (LENGTH rs1 = LENGTH xs1) /\ (LENGTH rs2 = LENGTH xs2) /\
        (LENGTH rs3 = LENGTH xs3))`)
  CHEAT_TAC;;

let abs_ml_inv_Num = cake_theorem "abs_ml_inv_Num"
  (fun () ->
    `abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts
  /\ small_int (:'a) i ==>
      abs_ml_inv conf (Number i :: stack) refs
        (gc_shared_Data (wordLang_Word ((Smallnum i):'a word)) ::
          roots,heap,be,a,sp,sp1,gens) limit ts`)
  CHEAT_TAC;;

let heap_store_unused_IMP_length =
  cake_theorem "heap_store_unused_IMP_length"
  (fun () ->
    `heap_store_unused a sp' x heap = (heap2,T) ==>
       heap_length heap2 = heap_length heap`)
  CHEAT_TAC;;

let heap_store_unused_alt_IMP_length =
  cake_theorem "heap_store_unused_alt_IMP_length"
  (fun () ->
    `heap_store_unused_alt a sp' x heap = (heap2,T) ==>
      heap_length heap2 = heap_length heap`)
  CHEAT_TAC;;


(* -------------------------------------------------------
    representation in memory
   ------------------------------------------------------- *)

let pointer_bits_def = cake_define
  `pointer_bits conf abs_heap n =
     (match heap_lookup n abs_heap with SOME (DataElement xs l
       (BlockTag tag,[])) ->
         maxout_bits (LENGTH xs) (data_to_word_config_len_bits conf)
           (data_to_word_config_tag_bits conf + 2) ||
         maxout_bits tag (data_to_word_config_tag_bits conf) 2 ||
           (n2w 1) | _40 -> all_ones (data_to_word_config_len_bits
           conf + data_to_word_config_tag_bits conf + 1) 0)`;;

let is_all_ones_def = cake_define
  `is_all_ones m n w = ((all_ones m n && w) = all_ones m n)`;;

let decode_maxout_def = cake_define
  `decode_maxout l n w =
     (if is_all_ones (n + l) n w then NONE else SOME ((word_bits
       (n + l) n) w >> n))`;;

let decode_addr_def = cake_define
  `decode_addr conf w =
     (decode_maxout (data_to_word_config_len_bits conf)
       (data_to_word_config_tag_bits conf + 2) w,
      decode_maxout (data_to_word_config_tag_bits conf) 2 w)`;;

let get_addr_def = cake_define
  `get_addr conf n w =
     ((n2w n << shift_length conf) || get_lowerbits conf w)`;;

let word_addr_def = cake_define
  `word_addr conf x2 =
        match x2 with
          gc_shared_Data (Loc l1 l2) -> Loc l1 0
        | (gc_shared_Data (wordLang_Word v)) -> wordLang_Word (v &&
          (word_not (n2w 1)))
        | (gc_shared_Pointer n w) -> wordLang_Word (get_addr conf
          n w)`;;

let b2w_def = cake_theorem "b2w_def"
  (fun () ->
    `(b2w T = (n2w 1)) /\ (b2w F = (n2w 0))`)
  CHEAT_TAC;;

let thunk_tag_to_bits_def = cake_define_list
  [`thunk_tag_to_bits Evaluated = (n2w 1)`;
   `thunk_tag_to_bits NotEvaluated = (n2w 0)`];;

let word_payload_def = cake_define_list
  [`word_payload ys l (BlockTag n) qs conf =
         (make_header conf (n2w n << 2) (LENGTH ys),
          MAP (word_addr conf) ys,(
          (qs = []) /\ (LENGTH ys = l) /\
          encode_header conf (n * 4) (LENGTH ys) =
            SOME (make_header conf (n2w n << 2) (LENGTH ys):'a
              word)))`;
   `word_payload ys l RefTag qs conf =
         (make_header conf (n2w 2) (LENGTH ys),
          MAP (word_addr conf) ys,(
          (qs = []) /\ (LENGTH ys = l)))`;
   `word_payload ys l (ThunkTag e) qs conf =
         (make_header conf (thunk_tag_to_bits e << 3 || (n2w 6))
           (LENGTH ys),
          MAP (word_addr conf) ys,(
          (qs = []) /\ (LENGTH ys = 1) /\ l = 1))`;
   `word_payload ys l Word64Tag qs conf =
         (make_header conf (n2w 3) l,
          qs,((ys = []) /\ (LENGTH qs = l) /\
              IS_SOME ((encode_header conf 3 l):('a word)
                option)))`;
   `word_payload ys l (NumTag b) qs conf =
         (make_header conf (b2w b << 2 || ((n2w 3):'a word)) (LENGTH
           qs),
          qs,((ys = []) /\ (LENGTH qs = l) /\
              IS_SOME ((encode_header conf (w2n (b2w b << 2 || ((n2w
                3):'a word)))
                          (LENGTH qs)):('a word) option)))`;
   `word_payload ys l (BytesTag fl n) qs conf =
         (((make_byte_header conf fl n):'a word),
          qs,((ys = []) /\ (LENGTH qs = l) /\
              (let k = (if dimindex (:'a) = 32 then 2 else 3) in
              n + 2 EXP k < 2 EXP (data_to_word_config_len_size
                conf + k))))`];;

let word_payload_T_IMP = cake_theorem "word_payload_T_IMP"
  (fun () ->
    `word_payload l5 n5 tag r conf = ((h:'a word),ts,T) /\
      good_dimindex (:'a) /\ data_to_word_config_len_size conf + 2
        < dimindex (:'a) ==>
      n5 = LENGTH ts /\
      (if word_bit 2 h then l5 = [] else ts = MAP (word_addr
        conf) l5)`)
  CHEAT_TAC;;

let word_el_def = cake_define_list
  [`word_el (a:'a word) (Unused l) conf = word_list_exists (a:'a
  word) (l + 1)`;
   `word_el (a:'a word) (ForwardPointer n d l) conf =
         set_sep_one (a,wordLang_Word (n2w n << 2)) *
         word_list_exists (a + bytes_in_word) l`;
   `word_el (a:'a word) (DataElement ys l (tag,qs)) conf =
         (let (h,ts,c) = word_payload ys l tag qs conf in
           misc_word_list a (wordLang_Word h :: ts) *
           cond (LENGTH ts < 2 EXP (dimindex (:'a) - 4) /\
                 decode_length conf h = n2w (LENGTH ts) /\ c))`];;

let word_heap_def = cake_define_list
  [`word_heap a ([]:(('a word_loc,data_to_word_memoryProof_tag#('a
  word_loc) list)heap_element) list) conf = emp`;
   `word_heap a (x :: xs) conf =
         word_el a x conf *
         word_heap (a + bytes_in_word * n2w (el_length x)) xs
           conf`];;

let gen_starts_in_store_def = cake_define
  `gen_starts_in_store c x2 x3 =
      match (x2,x3) with
        (GenState _41 gen_starts,SOME (wordLang_Word w)) ->
     (!gen_sizes. data_to_word_config_gc_kind
        c = data_to_word_Generational gen_sizes ==>
        LENGTH gen_starts = LENGTH gen_sizes /\
        (!x xs. gen_starts = x :: xs ==>
               w = (bytes_in_word * n2w x)))
      | (_42,_43) -> F`;;

let gen_starts_in_store_IMP = cake_theorem "gen_starts_in_store_IMP"
  (fun () ->
    `gen_starts_in_store c gens x ==> (?w. x = SOME (wordLang_Word w))`)
  CHEAT_TAC;;

let glob_real_inv_def = cake_define
  `glob_real_inv c (curr:'a word) globals globreal <=>
     (?w. globals = SOME (wordLang_Word w) /\
         globreal = SOME (wordLang_Word (curr + (w >>>
           (shift_length c) << backend_common_word_shift (:'a)))))`;;

let heap_in_memory_store_def = cake_define
  `heap_in_memory_store heap a sp sp1 gens c s m dm limit' <=>
     heap_length heap <= dimword (:'a) DIV 2 EXP shift_length c /\
     (heap_length heap + 3) * (dimindex (:'a) DIV 8) < dimword (:'a)
       /\
     backend_common_word_shift (:'a) <= shift_length c /\
       ~(data_to_word_config_len_size c = 0) /\
       data_to_word_config_len_size
     c + 7 < dimindex (:'a) /\
     shift_length c < dimindex (:'a) /\ Globals IN FDOM s /\
     (?curr other.
       byte_aligned curr /\ byte_aligned other /\
       (FLOOKUP s CurrHeap = SOME (wordLang_Word (curr:'a word))) /\
       (FLOOKUP s OtherHeap = SOME (wordLang_Word other)) /\
       (FLOOKUP s NextFree = SOME (wordLang_Word (curr +
         bytes_in_word * n2w a))) /\
       (FLOOKUP s TriggerGC = SOME (wordLang_Word (curr +
         bytes_in_word * n2w (a + sp)))) /\
       (FLOOKUP s EndOfHeap = SOME (wordLang_Word (curr +
         bytes_in_word * n2w (a + sp + sp1)))) /\
       (FLOOKUP s HeapLength = SOME (wordLang_Word (bytes_in_word *
         n2w limit'))) /\
       glob_real_inv c curr (FLOOKUP s Globals) (FLOOKUP s GlobReal)
         /\
       gen_starts_in_store c gens (FLOOKUP s GenStart) /\
       (word_heap curr heap c *
        word_heap other (heap_expand limit') c) (fun2set (m,dm)))`;;

let word_ml_inv_def = cake_define
  `word_ml_inv (heap,be',a,sp,sp1,gens) limit' ts c refs stack' <=>
     (?hs. abs_ml_inv c (MAP FST stack') refs
       (hs,heap,be',a,sp,sp1,gens) limit' ts /\
          EVERY2 (\v w. word_addr c v = w) hs (MAP SND stack'))`;;

let IMP_THE_EQ = cake_theorem "IMP_THE_EQ"
  (fun () ->
    `x = SOME w ==> THE x = w`)
  CHEAT_TAC;;

let memory_rel_def = cake_define
  `memory_rel c be' ts refs space' st (m:'a word->'a word_loc) dm vars'
  <=>
     (?heap limit' a sp sp1 gens.
        heap_in_memory_store heap a sp sp1 gens c st m dm limit' /\
        word_ml_inv (heap,be',a,sp,sp1,gens) limit' ts c refs vars'
          /\
        (limit' + 3) * (dimindex (:'a) DIV 8) + 1 < dimword (:'a)
          /\ space' <= sp)`;;

let EVERY2_MAP_MAP = cake_theorem "EVERY2_MAP_MAP"
  (fun () ->
    `!xs. EVERY2 P (MAP f xs) (MAP g xs) = EVERY (\x. P (f x) (g x))
  xs`)
  CHEAT_TAC;;

let MEM_FIRST_EL = cake_theorem "MEM_FIRST_EL"
  (fun () ->
    `!xs x.
        MEM x xs <=>
        (?n. n < LENGTH xs /\ (EL n xs = x) /\
            (!m. m < n ==> (~(EL m xs = EL n xs))))`)
  CHEAT_TAC;;

let ALOOKUP_ZIP_EL = cake_theorem "ALOOKUP_ZIP_EL"
  (fun () ->
    `!xs hs n.
        n < LENGTH xs /\ LENGTH hs = LENGTH xs /\
        (!m. m < n ==> ~(EL m xs = EL n xs)) ==>
        ALOOKUP (ZIP xs hs) (EL n xs) = SOME (EL n hs)`)
  CHEAT_TAC;;

let word_ml_inv_rearrange = cake_theorem "word_ml_inv_rearrange"
  (fun () ->
    `(!x. MEM x ys ==> MEM x xs) ==>
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs xs ==>
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs ys`)
  CHEAT_TAC;;

let memory_rel_rearrange = cake_theorem "memory_rel_rearrange"
  (fun () ->
    `(!x. MEM x ys ==> MEM x xs) ==>
     memory_rel c be ts refs sp st m dm xs ==>
     memory_rel c be ts refs sp st m dm ys`)
  CHEAT_TAC;;

let memory_rel_tl = cake_theorem "memory_rel_tl"
  (fun () ->
    `memory_rel c be ts refs sp st m dm (x :: xs) ==>
     memory_rel c be ts refs sp st m dm xs`)
  CHEAT_TAC;;

let word_ml_inv_Unit = cake_theorem "word_ml_inv_Unit"
  (fun () ->
    `word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs ws /\
      good_dimindex (:'a) ==>
      word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
        ((Unit,wordLang_Word ((n2w 2):'a word)) :: ws)`)
  CHEAT_TAC;;

let memory_rel_Unit = cake_theorem "memory_rel_Unit"
  (fun () ->
    `memory_rel c be ts refs sp st m dm xs /\ good_dimindex (:'a) ==>
     memory_rel c be ts refs sp st m dm ((Unit,wordLang_Word
       ((n2w 2):'a word)) :: xs)`)
  CHEAT_TAC;;

let get_lowerbits_LSL_shift_length =
  cake_theorem "get_lowerbits_LSL_shift_length"
  (fun () ->
    `get_lowerbits conf a >>> shift_length conf = (n2w 0)`)
  CHEAT_TAC;;

let get_real_addr_def = cake_define
  `get_real_addr conf st (w:'a word) =
     (let k = backend_common_word_shift (:'a) in
       match FLOOKUP st CurrHeap with SOME (wordLang_Word curr) ->
           (if k = shift_length conf /\ data_to_word_config_len_bits
             conf = 0 /\ data_to_word_config_tag_bits conf = 0 then SOME
             ((curr + w) - (n2w 1)) else
             if k <= data_to_word_config_pad_bits conf + 1 then
               SOME (curr + (w >>> (shift_length conf - k))) else
               SOME (curr + (w >>> (shift_length conf) << k))) | _44
               -> NONE)`;;

let get_real_offset_def = cake_define
  `get_real_offset (w:'a word) =
     (if dimindex (:'a) = 32 then SOME (w + bytes_in_word) else
       SOME (w << 1 + bytes_in_word))`;;

let get_real_simple_addr_def = cake_define
  `get_real_simple_addr conf st (w:'a word) =
     (match FLOOKUP st CurrHeap with SOME (wordLang_Word curr) ->
       SOME (curr + w >>> shift_length conf <<
       backend_common_word_shift (:'a)) | _45 -> NONE)`;;

let or_1 = cake_theorem "or_1[local]"
  (fun () ->
    `!w. (word_bits 0 0) w || (n2w 1) = ((n2w 1):'a word)`)
  CHEAT_TAC;;

let get_real_addr_get_addr = cake_theorem "get_real_addr_get_addr"
  (fun () ->
    `heap_length heap <= dimword (:'a) DIV 2 EXP shift_length c /\
      heap_lookup n heap = SOME anything /\
      FLOOKUP st CurrHeap = SOME (wordLang_Word (curr:'a word)) /\
      good_dimindex (:'a) ==>
      get_real_simple_addr c st (get_addr c n w) = SOME (curr + n2w
        n * bytes_in_word) /\
      get_real_addr c st (get_addr c n w) = SOME (curr + n2w n *
        bytes_in_word)`)
  CHEAT_TAC;;

let get_real_offset_thm = cake_theorem "get_real_offset_thm"
  (fun () ->
    `good_dimindex (:'a) ==>
      get_real_offset (n2w (4 * index)) =
        SOME (bytes_in_word + n2w index * (bytes_in_word:'a
          word))`)
  CHEAT_TAC;;

let word_heap_APPEND = cake_theorem "word_heap_APPEND"
  (fun () ->
    `!xs ys a.
        word_heap a (xs ++ ys) conf =
        word_heap a xs conf *
        word_heap (a + bytes_in_word * n2w (heap_length xs)) ys
          conf`)
  CHEAT_TAC;;

let FORALL_WORD = cake_theorem "FORALL_WORD"
  (fun () ->
    `(!(v:'a word). P v) <=> (!n. n < dimword (:'a) ==> P (n2w n))`)
  CHEAT_TAC;;

let BlockNil_and_lemma = cake_theorem "BlockNil_and_lemma"
  (fun () ->
    `good_dimindex (:'a) ==>
      (--(n2w 2) && (n2w 16) * tag + (n2w 2)) = (n2w 16) * tag +
        ((n2w 2):'a word)`)
  CHEAT_TAC;;

let word_ml_inv_num_lemma = cake_theorem "word_ml_inv_num_lemma"
  (fun () ->
    `good_dimindex (:'a) ==> (--(n2w 2) && (n2w 4) * v) = (n2w 4) *
  (v:'a word)`)
  CHEAT_TAC;;

let word_ml_inv_num = cake_theorem "word_ml_inv_num"
  (fun () ->
    `word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c (state_refs s) ws /\
      good_dimindex (:'a) /\
      small_enough_int (&n) ==>
      word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c (state_refs s)
        ((Number (&n),wordLang_Word (n2w (4 * n):'a word)) :: ws)`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:8032-8033: a theorem that
   HOL4 states as the value of an ML expression: word_ml_inv_zero *)

let word_ml_inv_neg_num_lemma = cake_theorem "word_ml_inv_neg_num_lemma"
  (fun () ->
    `good_dimindex (:'a) ==> (--(n2w 2) && --(n2w 4) * v) = --(n2w 4)
  * (v:'a word)`)
  CHEAT_TAC;;

let word_ml_inv_neg_num = cake_theorem "word_ml_inv_neg_num"
  (fun () ->
    `word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c (state_refs s) ws /\
      good_dimindex (:'a) /\
      small_enough_int (--(&n)) /\ ~(n = 0) ==>
      word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c (state_refs s)
        ((Number (--(&n)),wordLang_Word (--(n2w (4 * n):'a
          word))) :: ws)`)
  CHEAT_TAC;;

let word_list_APPEND = cake_theorem "word_list_APPEND"
  (fun () ->
    `!xs ys a. misc_word_list a (xs ++ ys) =
                misc_word_list a xs * misc_word_list (a + n2w
                  (LENGTH xs) * bytes_in_word) ys`)
  CHEAT_TAC;;

let all_ts_head_eq = cake_theorem "all_ts_head_eq"
  (fun () ->
    `!v refs stack' ts.
      v IN all_vs refs stack' ==> all_ts refs stack' = all_ts
        refs (v :: stack')`)
  CHEAT_TAC;;

let memory_rel_El' = cake_theorem "memory_rel_El'"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
       ((Block ts' tag vals,ptr) :: vars) /\
      good_dimindex (:'a) /\
      index < LENGTH vals ==>
      (?ptr_w i_w (x:'a word).
        ptr = wordLang_Word ptr_w /\
        get_real_addr c st ptr_w = SOME x /\
        (x + bytes_in_word + bytes_in_word * n2w index) IN dm /\
        memory_rel c be ts refs sp st m dm
          ((EL index vals,m (x + bytes_in_word + bytes_in_word *
            n2w index)) ::
           (Block ts' tag vals,ptr) :: vars))`)
  CHEAT_TAC;;

let memory_rel_El = cake_theorem "memory_rel_El"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
       ((Block ts' tag vals,ptr) :: (Number (&index),i) :: vars) /\
      good_dimindex (:'a) /\
      index < LENGTH vals ==>
      (?ptr_w i_w x (y:'a word).
        ptr = wordLang_Word ptr_w /\ i = wordLang_Word i_w /\
        get_real_addr c st ptr_w = SOME x /\
        get_real_offset i_w = SOME y /\
        (x + y) IN dm /\
        memory_rel c be ts refs sp st m dm
          ((EL index vals,m (x + y)) ::
           (Block ts' tag vals,ptr) :: (Number (&index),i) ::
             vars))`)
  CHEAT_TAC;;

let memory_rel_swap = cake_theorem "memory_rel_swap"
  (fun () ->
    `memory_rel c be ts refs sp st m dm (x :: y :: z) ==>
     memory_rel c be ts refs sp st m dm (y :: x :: z)`)
  CHEAT_TAC;;

let memory_rel_Deref' = cake_theorem "memory_rel_Deref'"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((RefPtr bl nn,ptr) :: vars) /\
      lookup nn refs = SOME (ValueArray vals) /\
      good_dimindex (:'a) /\
      index < LENGTH vals ==>
      (?ptr_w (x:'a word).
        ptr = wordLang_Word ptr_w /\
        get_real_addr c st ptr_w = SOME x /\
        (x + bytes_in_word + bytes_in_word * n2w index) IN dm /\
        memory_rel c be ts refs sp st m dm
          ((EL index vals,m (x + bytes_in_word + bytes_in_word *
            n2w index)) ::
           (RefPtr bl nn,ptr) :: vars))`)
  CHEAT_TAC;;

let memory_rel_Deref = cake_theorem "memory_rel_Deref"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
       ((RefPtr bl nn,ptr) :: (Number (&index),i) :: vars) /\
      lookup nn refs = SOME (ValueArray vals) /\
      good_dimindex (:'a) /\
      index < LENGTH vals ==>
      (?ptr_w i_w x (y:'a word).
        ptr = wordLang_Word ptr_w /\ i = wordLang_Word i_w /\
        get_real_addr c st ptr_w = SOME x /\
        get_real_offset i_w = SOME y /\
        (x + y) IN dm /\
        memory_rel c be ts refs sp st m dm
          ((EL index vals,m (x + y)) ::
           (RefPtr bl nn,ptr) :: (Number (&index),i) :: vars))`)
  CHEAT_TAC;;

let LENGTH_EQ_1 = cake_theorem "LENGTH_EQ_1"
  (fun () ->
    `(LENGTH xs = 1 <=> (?a1. xs = [a1])) /\
      (1 = LENGTH xs <=> (?a1. xs = [a1]))`)
  CHEAT_TAC;;

let LENGTH_EQ_2 = cake_theorem "LENGTH_EQ_2"
  (fun () ->
    `(LENGTH xs = 2 <=> (?a1 a2. xs = [a1; a2])) /\
      (2 = LENGTH xs <=> (?a1 a2. xs = [a1; a2]))`)
  CHEAT_TAC;;

let LENGTH_EQ_3 = cake_theorem "LENGTH_EQ_3"
  (fun () ->
    `(LENGTH xs = 3 <=> (?a1 a2 a3. xs = [a1; a2; a3])) /\
      (3 = LENGTH xs <=> (?a1 a2 a3. xs = [a1; a2; a3]))`)
  CHEAT_TAC;;

let heap_split_SOME_APPEND = cake_theorem "heap_split_SOME_APPEND"
  (fun () ->
    `!xs ys a h1 h2.
        heap_split a (xs ++ ys) = SOME (h1,h2) <=>
        (if a < heap_length xs then
          ?ha hb. heap_split a xs = SOME (ha,hb) /\
                  h1 = ha /\ h2 = hb ++ ys else
          ?ha hb. heap_split (a - heap_length xs) ys = SOME (ha,hb)
            /\
                  h1 = xs ++ ha /\ h2 = hb)`)
  CHEAT_TAC;;

let gc_kind_update_Ref = cake_theorem "gc_kind_update_Ref[local]"
  (fun () ->
    `gc_kind_inv c a sp sp1 gens
         (ha ++ (DataElement (ys1 ++ (y :: ys2)) l (RefTag,[]) ::
           hb)) ==>
     gc_kind_inv c a sp sp1 gens
         (ha ++ (DataElement (ys1 ++ (z :: ys2)) l (RefTag,[]) ::
           hb))`)
  CHEAT_TAC;;

let memory_rel_Update' = cake_theorem "memory_rel_Update'"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
       ((h,w) :: (RefPtr bl nn,ptr) :: vars) /\
      lookup nn refs = SOME (ValueArray vals) /\
      good_dimindex (:'a) /\
      index < LENGTH vals ==>
      (?ptr_w (x:'a word).
        ptr = wordLang_Word ptr_w /\
        get_real_addr c st ptr_w = SOME x /\
        (x + bytes_in_word + bytes_in_word * n2w index) IN dm /\
        memory_rel c be ts (insert nn (ValueArray (LUPDATE h index
          vals)) refs) sp st
          (((x + bytes_in_word + bytes_in_word * n2w index) =+ w)
            m) dm
          ((h,w) :: (RefPtr bl nn,ptr) :: vars))`)
  CHEAT_TAC;;

let memory_rel_Update = cake_theorem "memory_rel_Update"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
       ((h,w) :: (RefPtr bl nn,ptr) :: (Number (&index),i) :: vars)
         /\
      lookup nn refs = SOME (ValueArray vals) /\
      good_dimindex (:'a) /\
      index < LENGTH vals ==>
      (?ptr_w i_w x (y:'a word).
        ptr = wordLang_Word ptr_w /\ i = wordLang_Word i_w /\
        get_real_addr c st ptr_w = SOME x /\
        get_real_offset i_w = SOME y /\
        (x + y) IN dm /\
        memory_rel c be ts (insert nn (ValueArray (LUPDATE h index
          vals)) refs) sp st
          (((x + y) =+ w) m) dm
          ((h,w) :: (RefPtr bl nn,ptr) :: (Number (&index),i) ::
            vars))`)
  CHEAT_TAC;;

(* mirrors memory_rel_Update: writing the hole of an unfinalised MutBlock is
   the same single memory write as updating a reference's payload *)
let memory_rel_UpdateCons = cake_theorem "memory_rel_UpdateCons"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
       ((h,w) :: (RefPtr bl nn,ptr) :: (Number (&index),i) :: vars)
         /\
      lookup nn refs = SOME (bvlSem_MutBlock tag F l cv r) /\
      good_dimindex (:'a) /\
      index = LENGTH l ==>
      (?ptr_w i_w x (y:'a word).
        ptr = wordLang_Word ptr_w /\ i = wordLang_Word i_w /\
        get_real_addr c st ptr_w = SOME x /\
        get_real_offset i_w = SOME y /\
        (x + y) IN dm /\
        memory_rel c be ts (insert nn (bvlSem_MutBlock tag F l h r)
          refs) sp st
          (((x + y) =+ w) m) dm
          ((h,w) :: (RefPtr bl nn,ptr) :: (Number (&index),i) ::
            vars))`)
  CHEAT_TAC;;

let store_list_def = cake_define_list
  [`data_to_word_memoryProof_store_list a [] (m:'a word->'a word_loc)
  dm = SOME m`;
   `data_to_word_memoryProof_store_list a (w :: ws) (m:'a word->'a
  word_loc) dm =
         (if a IN dm then
           data_to_word_memoryProof_store_list (a +
             bytes_in_word) ws ((a =+ w) m) dm else NONE)`];;
hol4_overload "store_list" "data_to_word_memoryProof_store_list";;

let store_list_append = cake_theorem "store_list_append"
  (fun () ->
    `!xs ys a dm m m1.
       data_to_word_memoryProof_store_list a (xs ++ ys) m dm = SOME
         m1 <=>
       (?m0. data_to_word_memoryProof_store_list a xs m dm = SOME
         m0 /\
            data_to_word_memoryProof_store_list (a +
              bytes_in_word * n2w (LENGTH xs)) ys m0 dm = SOME m1)`)
  CHEAT_TAC;;

let minus_lemma = cake_theorem "minus_lemma[local]"
  (fun () ->
    `--(n2w 1) * (bytes_in_word * w) = bytes_in_word * --w`)
  CHEAT_TAC;;

let n2w_lsr_eq_0 = cake_theorem "n2w_lsr_eq_0"
  (fun () ->
    `n DIV 2 EXP k = 0 /\ n < dimword (:'a) ==> n2w n >>> k = ((n2w
  0):'a word)`)
  CHEAT_TAC;;

let LESS_EXO_SUB = cake_theorem "LESS_EXO_SUB[local]"
  (fun () ->
    `n < 2 EXP (k - m) ==> n < 2 EXP k`)
  CHEAT_TAC;;

let LESS_EXO_SUB_ALT = cake_theorem "LESS_EXO_SUB_ALT[local]"
  (fun () ->
    `m <= k ==> n < 2 EXP (k - m) ==> n * 2 EXP m < 2 EXP k`)
  CHEAT_TAC;;

let less_pow_dimindex_sub_imp =
  cake_theorem "less_pow_dimindex_sub_imp[local]"
  (fun () ->
    `n < 2 EXP (dimindex (:'a) - k) ==> n < dimword (:'a)`)
  CHEAT_TAC;;

let encode_header_NEQ_0 = cake_theorem "encode_header_NEQ_0"
  (fun () ->
    `encode_header c n k = SOME w ==> ~(w = (n2w 0))`)
  CHEAT_TAC;;

let encode_header_IMP = cake_theorem "encode_header_IMP[local]"
  (fun () ->
    `encode_header c tag len = SOME (hd:'a word) /\
  data_to_word_config_len_size
       c + 5 < dimindex (:'a) /\ good_dimindex (:'a) ==>
       len < 2 EXP (dimindex (:'a) - 4) /\
       decode_length c hd = n2w len`)
  CHEAT_TAC;;

let memory_rel_UpdateThunk_NotEvaluated =
  cake_theorem "memory_rel_UpdateThunk_NotEvaluated"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
       ((h,w) :: (RefPtr F nn,ptr) :: vars) /\
      lookup nn refs = SOME (Thunk NotEvaluated v) /\
      good_dimindex (:'a) ==>
      (?ptr_w (x:'a word).
        ptr = wordLang_Word ptr_w /\
        get_real_addr c st ptr_w = SOME x /\
        (x + bytes_in_word) IN dm /\
        memory_rel c be ts (insert nn (Thunk NotEvaluated h) refs)
          sp st
          (((x + bytes_in_word) =+ w) m) dm
          ((h,w) :: (RefPtr F nn,ptr) :: vars))`)
  CHEAT_TAC;;

let thunk_tag_bits_lemma = cake_theorem "thunk_tag_bits_lemma[local]"
  (fun () ->
    `(thunk_tag_to_bits Evaluated << 3 || (n2w 6)) = ((n2w 14):'a
  word)`)
  CHEAT_TAC;;

let memory_rel_UpdateThunk_Evaluated =
  cake_theorem "memory_rel_UpdateThunk_Evaluated"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
       ((h,w) :: (RefPtr F nn,ptr) :: vars) /\
      lookup nn refs = SOME (Thunk NotEvaluated v) /\
      encode_header c (8 + 6) 1 = SOME hdr /\
      dest_thunk h refs = NotThunk /\
      good_dimindex (:'a) ==>
      (?ptr_w (x:'a word).
        ptr = wordLang_Word ptr_w /\
        get_real_addr c st ptr_w = SOME x /\
        x IN dm /\ (x + bytes_in_word) IN dm /\
        memory_rel c be ts (insert nn (Thunk Evaluated h) refs) sp
          st
          (UPDATE_LIST m [x,wordLang_Word hdr; x +
            bytes_in_word,w]) dm
          ((h,w) :: (RefPtr F nn,ptr) :: vars))`)
  CHEAT_TAC;;

let word_list_exists_thm = cake_theorem "word_list_exists_thm"
  (fun () ->
    `(word_list_exists a 0 = emp) /\
      (word_list_exists a (SUC n) =
       SEP_EXISTS (\w. set_sep_one (a,w) * word_list_exists (a +
         bytes_in_word) n))`)
  CHEAT_TAC;;

let word_list_exists_ADD = cake_theorem "word_list_exists_ADD"
  (fun () ->
    `!m n a.
        word_list_exists a (m + n) =
        word_list_exists a m *
        word_list_exists (a + bytes_in_word * n2w m) n`)
  CHEAT_TAC;;

let store_list_thm = cake_theorem "store_list_thm"
  (fun () ->
    `!xs a frame m dm.
        (word_list_exists a (LENGTH xs) * frame) (fun2set (m,dm))
          ==>
        (?m1.
          data_to_word_memoryProof_store_list a xs m dm = SOME m1
            /\
          (misc_word_list a xs * frame) (fun2set (m1,dm)))`)
  CHEAT_TAC;;

let store_list_domain = cake_theorem "store_list_domain"
  (fun () ->
    `!a xs m dm m1.
     data_to_word_memoryProof_store_list a xs m dm = SOME m1 ==>
     (!n. n < LENGTH xs ==> a + n2w n * bytes_in_word IN dm)`)
  CHEAT_TAC;;

let store_list_append_imp = cake_theorem "store_list_append_imp"
  (fun () ->
    `!w1 a m dm m' w2.
     data_to_word_memoryProof_store_list a (w1 ++ w2) m dm = SOME
       m' ==>
     (?m''. data_to_word_memoryProof_store_list a w1 m dm = SOME
       m'' /\
           data_to_word_memoryProof_store_list (a + n2w (LENGTH
             w1) * bytes_in_word) w2 m'' dm = SOME m')`)
  CHEAT_TAC;;

let store_list_update_m_outside =
  cake_theorem "store_list_update_m_outside"
  (fun () ->
    `!ws a m dm m'.
     data_to_word_memoryProof_store_list a ws m dm = SOME m' /\
     (!i. i < LENGTH ws ==> ~(a + n2w i * bytes_in_word = a')) ==>
     data_to_word_memoryProof_store_list a ws ((a' =+ v) m) dm =
       SOME ((a' =+ v) m')`)
  CHEAT_TAC;;

let word_payload_IMP = cake_theorem "word_payload_IMP"
  (fun () ->
    `word_payload addrs ll tags tt1 conf = (h,ts,T) ==> LENGTH ts = ll`)
  CHEAT_TAC;;

let word_el_IMP_word_list_exists =
  cake_theorem "word_el_IMP_word_list_exists"
  (fun () ->
    `!temp p curr.
        (p * word_el curr temp conf) s ==>
        (p * word_list_exists curr (el_length temp)) s`)
  CHEAT_TAC;;

let word_heap_IMP_word_list_exists =
  cake_theorem "word_heap_IMP_word_list_exists"
  (fun () ->
    `!temp p curr.
        (p * word_heap curr temp conf) s ==>
        (p * word_list_exists curr (heap_length temp)) s`)
  CHEAT_TAC;;

let EVERY2_f_EQ = cake_theorem "EVERY2_f_EQ[local]"
  (fun () ->
    `!rs ws f. EVERY2 (\v w. f v = w) rs ws <=> MAP f rs = ws`)
  CHEAT_TAC;;

let word_heap_heap_expand = cake_theorem "word_heap_heap_expand"
  (fun () ->
    `word_heap a (heap_expand n) conf = word_list_exists a n`)
  CHEAT_TAC;;

let get_lowerbits_or_1 = cake_theorem "get_lowerbits_or_1[local]"
  (fun () ->
    `get_lowerbits c v = (get_lowerbits c v || (n2w 1))`)
  CHEAT_TAC;;

let memory_rel_Word64_alt = cake_theorem "memory_rel_Word64_alt"
  (fun () ->
    `memory_rel c be ts refs sp st m dm (vs ++ vars) /\ good_dimindex
  (:'a) /\
     (Word64Rep (:'a) w64:('a
       word_loc,data_to_word_memoryProof_tag#('a word_loc)
       list)heap_element) = DataElement [] (LENGTH ws) (Word64Tag,ws) /\
     LENGTH ws < sp /\
     encode_header c 3 (LENGTH ws) = SOME hd ==>
     (?ne curr m1.
       FLOOKUP st NextFree = SOME (wordLang_Word ne) /\
       FLOOKUP st CurrHeap = SOME (wordLang_Word curr) /\
       data_to_word_memoryProof_store_list ne (wordLang_Word hd ::
         ws) m dm = SOME m1 /\
       memory_rel c be ts refs (sp - (LENGTH ws + 1))
          (st |+ (NextFree,wordLang_Word (ne + bytes_in_word * n2w
            (LENGTH ws + 1)))) m1 dm
          ((Word64 w64,make_ptr c (ne - curr) ((n2w 0):'a word)
            (LENGTH ws)) :: vars))`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:9026-9028: a theorem that
   HOL4 states as the value of an ML expression:
   memory_rel_WordOp64_alt *)

let IMP_memory_rel_bignum_alt =
  cake_theorem "IMP_memory_rel_bignum_alt[local]"
  (fun () ->
    `memory_rel c be ts refs sp st m dm (vs ++ vars) /\
      good_dimindex (:'a) /\ ~(small_int (:'a) i) /\
      (Bignum i:('a word_loc,data_to_word_memoryProof_tag#('a
        word_loc) list)heap_element) = DataElement [] (LENGTH ws)
        (NumTag is_neg,MAP wordLang_Word ws) /\
      LENGTH ws < sp /\
      encode_header c (w2n ((b2w is_neg << 2 || (n2w 3)):'a word))
        (LENGTH ws) =
        SOME (hd:'a word) ==>
      (?next' curr m1.
        FLOOKUP st NextFree = SOME (wordLang_Word next') /\
        FLOOKUP st CurrHeap = SOME (wordLang_Word curr) /\
        (data_to_word_memoryProof_store_list next' (MAP
          wordLang_Word (hd :: ws)) m dm = SOME m1 /\
         memory_rel c be ts refs (sp - (LENGTH ws + 1))
           (st |+ (NextFree,wordLang_Word (next' + bytes_in_word *
             n2w (LENGTH ws + 1))))
           m1 dm ((Number i,make_ptr c (next' - curr) ((n2w 0):'a
             word) (LENGTH ws)) :: vars)))`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:9113-9114: a theorem that
   HOL4 states as the value of an ML expression:
   IMP_memory_rel_bignum_alt *)

let memory_rel_Cons1 = cake_theorem "memory_rel_Cons1"
  (fun () ->
    `memory_rel c be ts refs sp st m dm (ZIP vals ws ++ vars) /\
      LENGTH vals = LENGTH (ws:('a word_loc) list) /\ ~(vals = [])
        /\
      encode_header c (4 * tag) (LENGTH ws) = SOME hd /\
      LENGTH ws < sp /\ good_dimindex (:'a) ==>
      (?free' (curr:'a word) m1.
        FLOOKUP st NextFree = SOME (wordLang_Word free') /\
        FLOOKUP st CurrHeap = SOME (wordLang_Word curr) /\
        (let w = free' + bytes_in_word * n2w (LENGTH ws + 1) in
          data_to_word_memoryProof_store_list free' (wordLang_Word
            hd :: ws) m dm = SOME m1 /\
          memory_rel c be (ts + 1) refs (sp - (LENGTH ws + 1))
            (st |+ (NextFree,wordLang_Word w)) m1 dm
            ((Block ts tag vals,make_cons_ptr c (free' - curr)
              tag (LENGTH ws)) :: vars)))`)
  CHEAT_TAC;;

(* mirrors memory_rel_Cons1: a MutBlock is laid out exactly like the Block it
   finalises to, so the allocation is the Cons allocation; what differs is that
   the abstract value handed back is a RefPtr into refs rather than a Block,
   and no timestamp is consumed *)
let memory_rel_MutCons = cake_theorem "memory_rel_MutCons"
  (fun () ->
    `memory_rel c be ts refs sp st m dm (ZIP vals ws ++ vars) /\
      LENGTH vals = LENGTH (ws:('a word_loc) list) /\ ~(vals = [])
        /\
      encode_header c (4 * tag) (LENGTH ws) = SOME hd /\
      LENGTH ws < sp /\ good_dimindex (:'a) /\
      index < LENGTH vals /\ ~(ptr IN domain refs) /\
      (!gs. ~(data_to_word_config_gc_kind c =
        data_to_word_Generational gs)) ==>
      (?free' (curr:'a word) m1.
        FLOOKUP st NextFree = SOME (wordLang_Word free') /\
        FLOOKUP st CurrHeap = SOME (wordLang_Word curr) /\
        (let w = free' + bytes_in_word * n2w (LENGTH ws + 1) in
          data_to_word_memoryProof_store_list free' (wordLang_Word
            hd :: ws) m dm = SOME m1 /\
          memory_rel c be ts
            (insert ptr (bvlSem_MutBlock tag F (TAKE index vals)
              (EL index vals)
                              (DROP (index + 1) vals)) refs)
            (sp - (LENGTH ws + 1))
            (st |+ (NextFree,wordLang_Word w)) m1 dm
            ((RefPtr F ptr,make_cons_ptr c (free' - curr) tag
              (LENGTH ws)) :: vars)))`)
  CHEAT_TAC;;

let INJ_FUPDATE = cake_theorem "INJ_FUPDATE"
  (fun () ->
    `INJ (FAPPLY tf) (FDOM tf) s /\ ~(ts2 IN FDOM tf) /\ ~(x IN FRANGE
  tf) /\ x IN s ==>
     INJ (FAPPLY (tf |+ (ts2,x))) (FDOM (tf |+ (ts2,x))) s`)
  CHEAT_TAC;;

let finalise_cons_none = cake_theorem "finalise_cons_none[local]"
  (fun () ->
    `!v refs ts_opt v' refs' ts'.
       dataSem_finalise_cons v refs ts_opt = SOME (v',refs',ts') /\
       lookup ptr refs = NONE ==>
       lookup ptr refs' = NONE`)
  CHEAT_TAC;;

let v_inv_swap_refs = cake_theorem "v_inv_swap_refs"
  (fun () ->
    `!c v refs1 x f tf heap refs.
       v_inv c v refs1 (x,f,tf,heap) /\
       (!n. sptree_lookup n refs = lookup n refs1) ==>
       v_inv c v refs (x,f,tf,heap)`)
  CHEAT_TAC;;

let bc_stack_ref_inv_swap_refs =
  cake_theorem "bc_stack_ref_inv_swap_refs"
  (fun () ->
    `bc_stack_ref_inv c ts vars refs (xs,heap,be) /\
     (!n. sptree_lookup n refs = lookup n refs1) ==>
     bc_stack_ref_inv c ts vars refs1 (xs,heap,be)`)
  CHEAT_TAC;;

(* ---- FinaliseCons: the MutBlock at ptr keeps its payload and only flips its
   fin flag, and the value handed back is the Block that payload denotes.
   Neither all_ts, all_vs, ref_edge nor dest_thunk can observe fin, so the
   only real work is relocating the payload from the ref into the new Block. *)

let blocks_unique_SUBSET = cake_theorem "blocks_unique_SUBSET[local]"
  (fun () ->
    `blocks_unique ts vs2 /\ vs1 SUBSET vs2 ==> blocks_unique ts vs1`)
  CHEAT_TAC;;

let blocks_unique_INSERT = cake_theorem "blocks_unique_INSERT[local]"
  (fun () ->
    `blocks_unique ts vs ==> blocks_unique (SUC ts) (Block ts tag l
  INSERT vs)`)
  CHEAT_TAC;;

let all_ts_CONS_SUBSET = cake_theorem "all_ts_CONS_SUBSET[local]"
  (fun () ->
    `all_ts refs stack SUBSET all_ts refs (x :: stack)`)
  CHEAT_TAC;;

let in_all_vs_stack = cake_theorem "in_all_vs_stack[local]"
  (fun () ->
    `MEM v (v_all_vs stack) ==> v IN all_vs refs stack`)
  CHEAT_TAC;;

let in_all_vs_MutBlock = cake_theorem "in_all_vs_MutBlock[local]"
  (fun () ->
    `lookup n refs = SOME (bvlSem_MutBlock tg fin l c r) /\
     MEM v (v_all_vs (l ++ [c] ++ r)) ==>
     v IN all_vs refs stack`)
  CHEAT_TAC;;

let all_vs_CONS_SUBSET = cake_theorem "all_vs_CONS_SUBSET[local]"
  (fun () ->
    `x IN all_vs refs stack ==> all_vs refs (x :: stack) SUBSET all_vs
  refs stack`)
  CHEAT_TAC;;

let all_vs_MutBlock_centre =
  cake_theorem "all_vs_MutBlock_centre[local]"
  (fun () ->
    `lookup ptr refs = SOME (bvlSem_MutBlock tag fin left cen right) ==>
     all_vs refs (cen :: stack) SUBSET all_vs refs stack`)
  CHEAT_TAC;;

(* every value reachable after finalisation was reachable before, except the
   new Block itself *)
let all_vs_MutBlock_T = cake_theorem "all_vs_MutBlock_T[local]"
  (fun () ->
    `lookup ptr refs = SOME (bvlSem_MutBlock tag F left cen right) ==>
     all_vs (insert ptr (bvlSem_MutBlock tag T left cen right)
       refs)
            (Block ts2 tag (left ++ [res] ++ right) :: vars) SUBSET
     Block ts2 tag (left ++ [res] ++ right) INSERT
     all_vs refs (res :: RefPtr b ptr :: vars)`)
  CHEAT_TAC;;

(* the hole of a MutBlock is reachable from the pointer to it *)
let reachable_refs_MutBlock_centre =
  cake_theorem "reachable_refs_MutBlock_centre[local]"
  (fun () ->
    `lookup ptr refs = SOME (bvlSem_MutBlock tag fin left cen right) /\
     reachable_refs (cen :: RefPtr b ptr :: vars) refs n ==>
     reachable_refs (RefPtr b ptr :: vars) refs n`)
  CHEAT_TAC;;

let ref_edge_insert_MutBlock =
  cake_theorem "ref_edge_insert_MutBlock[local]"
  (fun () ->
    `lookup ptr refs = SOME (bvlSem_MutBlock tg fin1 l c r) ==>
     ref_edge (insert ptr (bvlSem_MutBlock tg fin2 l c r) refs) =
       ref_edge refs`)
  CHEAT_TAC;;

(* the payload of the finalised cell moves into the new Block, so the refs it
   reaches are the ones the pointer used to reach *)
let reachable_refs_MutBlock_T =
  cake_theorem "reachable_refs_MutBlock_T[local]"
  (fun () ->
    `lookup ptr refs = SOME (bvlSem_MutBlock tag F left cen right) /\
     reachable_refs (Block ts2 tag (left ++ [res] ++ right) ::
       vars)
                    (insert ptr (bvlSem_MutBlock tag T left cen
                      right) refs) n ==>
     reachable_refs (res :: RefPtr b ptr :: vars) refs n`)
  CHEAT_TAC;;

let dest_thunk_insert_MutBlock =
  cake_theorem "dest_thunk_insert_MutBlock[local]"
  (fun () ->
    `lookup ptr refs = SOME (bvlSem_MutBlock tg fin1 l c r) ==>
     dest_thunk v (insert ptr (bvlSem_MutBlock tg fin2 l c r)
       refs) = dest_thunk v refs`)
  CHEAT_TAC;;

let bc_stack_ref_inv_MutBlock_centre =
  cake_theorem "bc_stack_ref_inv_MutBlock_centre"
  (fun () ->
    `bc_stack_ref_inv c ts (RefPtr b ptr :: vars) refs (x :: xs,heap,be)
  /\
     lookup ptr refs = SOME (bvlSem_MutBlock tag F left cen right)
       ==>
     (?ptr_n zs.
       x = gc_shared_Pointer ptr_n (ref_ptr_annot c (lookup ptr
         refs)) /\
       heap_lookup ptr_n heap = SOME (BlockRep tag zs) /\
       LENGTH zs = LENGTH left + 1 + LENGTH right /\
       bc_stack_ref_inv c ts (cen :: RefPtr b ptr :: vars) refs
                             (EL (LENGTH left) zs :: x ::
                               xs,heap,be))`)
  CHEAT_TAC;;

let bc_stack_ref_inv_union_del_ins_lemma =
  cake_theorem "bc_stack_ref_inv_union_del_ins_lemma[local]"
  (fun () ->
    `bc_stack_ref_inv c ts vars (union refs frame) (xs,heap,be) /\
     lookup ptr refs = SOME x ==>
     bc_stack_ref_inv c ts vars (union (delete ptr refs) (insert
       ptr x frame)) (xs,heap,be)`)
  CHEAT_TAC;;

let bc_stack_ref_inv_MutBlock_F =
  cake_theorem "bc_stack_ref_inv_MutBlock_F"
  (fun () ->
    `bc_stack_ref_inv c ts2
       (res :: RefPtr b ptr :: vars) refs
       (EL (LENGTH left) zs :: gc_shared_Pointer ptr_n
          (wordLang_Word (ptr_bits c tag (LENGTH left + (LENGTH
            right + 1)))) :: xs,heap,be) /\
     heap_lookup ptr_n heap = SOME (BlockRep tag zs) /\
     lookup ptr refs = SOME (bvlSem_MutBlock tag F left cen right)
       ==>
     bc_stack_ref_inv c (SUC ts2)
       (Block ts2 tag (left ++ [res] ++ right) :: vars)
       (insert ptr (bvlSem_MutBlock tag T left cen right) refs)
       (gc_shared_Pointer ptr_n
          (wordLang_Word (ptr_bits c tag (LENGTH left + (LENGTH
            right + 1)))) :: xs,heap,be)`)
  CHEAT_TAC;;

let bc_stack_ref_inv_FinaliseCons_lemma =
  cake_theorem "bc_stack_ref_inv_FinaliseCons_lemma[local]"
  (fun () ->
    `!v refs ts_opt v' refs' ts' ts vars' w frame x xs.
       dataSem_finalise_cons v refs ts_opt = SOME (v',refs',ts') /\
         ts_opt = SOME ts /\
       bc_stack_ref_inv c ts (v :: vars') (union refs frame) (x ::
         xs,heap,be) ==>
       IS_SOME ts' /\
       bc_stack_ref_inv c (THE ts') (v' :: vars') (union refs'
         frame) (x :: xs,heap,be)`)
  CHEAT_TAC;;

let memory_rel_FinaliseCons = cake_theorem "memory_rel_FinaliseCons"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((v,w) :: vars) /\
      dataSem_finalise_cons v refs (SOME ts) = SOME (v',refs',ts')
        ==>
      IS_SOME ts' /\
      memory_rel c be (THE ts') refs' sp st m dm ((v',w) :: vars)`)
  CHEAT_TAC;;

let memory_rel_Cons_empty = cake_theorem "memory_rel_Cons_empty"
  (fun () ->
    `memory_rel c be ts refs sp st m (dm:'a word->bool) vars /\
      tag < dimword (:'a) DIV 16 /\ good_dimindex (:'a) ==>
      memory_rel c be ts refs sp st m dm
        ((Block 0 tag [],wordLang_Word (BlockNil tag)) :: vars)`)
  CHEAT_TAC;;

let memory_rel_Ref = cake_theorem "memory_rel_Ref"
  (fun () ->
    `memory_rel c be ts refs sp st m dm (ZIP vals ws ++ vars) /\
      LENGTH vals = LENGTH (ws:('a word_loc) list) /\
      encode_header c 2 (LENGTH ws) = SOME hd /\ ~(new IN (domain
        refs)) /\
      LENGTH ws < sp /\ good_dimindex (:'a) ==>
      (?eoh (curr:'a word) trig m1.
        FLOOKUP st EndOfHeap = SOME (wordLang_Word eoh) /\
        FLOOKUP st TriggerGC = SOME (wordLang_Word trig) /\
        FLOOKUP st CurrHeap = SOME (wordLang_Word curr) /\
        (let w = eoh - bytes_in_word * n2w (LENGTH ws + 1) in
        let w1 = trig - bytes_in_word * n2w (LENGTH ws + 1) in
          data_to_word_memoryProof_store_list w (wordLang_Word hd
            :: ws) m dm = SOME m1 /\
          memory_rel c be ts (insert new (ValueArray vals) refs)
            (sp - (LENGTH ws + 1))
            (st |+ (EndOfHeap,wordLang_Word w) |+
              (TriggerGC,wordLang_Word w1)) m1 dm
            ((RefPtr T new,make_ptr c (w - curr) (n2w 0) (LENGTH
              ws)) :: vars)))`)
  CHEAT_TAC;;

let memory_rel_AllocThunk = cake_theorem "memory_rel_AllocThunk"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((v,w) :: vars) /\
     encode_header c (match ev with Evaluated -> 14 | NotEvaluated
       -> 6) 1 = SOME hd /\
      ~(new IN (domain refs)) /\
      (ev = Evaluated ==> dest_thunk v refs = NotThunk) /\
      2 <= sp /\ good_dimindex (:'a) ==>
      (?eoh (curr:'a word) trig m1.
        FLOOKUP st EndOfHeap = SOME (wordLang_Word eoh) /\
        FLOOKUP st TriggerGC = SOME (wordLang_Word trig) /\
        FLOOKUP st CurrHeap = SOME (wordLang_Word curr) /\
        (let w' = eoh - bytes_in_word * (n2w 2) in
        let w1 = trig - bytes_in_word * (n2w 2) in
          data_to_word_memoryProof_store_list w' [wordLang_Word hd;
            w] m dm = SOME m1 /\
          memory_rel c be ts (insert new (Thunk ev v) refs) (sp -
            2)
            (st |+ (EndOfHeap,wordLang_Word w') |+
              (TriggerGC,wordLang_Word w1)) m1 dm
            ((RefPtr F new,make_ptr c (w' - curr) (n2w 0) 1) ::
              vars)))`)
  CHEAT_TAC;;

let memory_rel_write = cake_theorem "memory_rel_write"
  (fun () ->
    `memory_rel c be ts refs sp st m dm vars ==>
      (?(free':'a word).
        FLOOKUP st NextFree = SOME (wordLang_Word free') /\
        (!n.
          n < sp ==>
          (let a = free' + bytes_in_word * n2w n in
            a IN dm /\ memory_rel c be ts refs sp st ((a =+ w) m)
              dm vars)))`)
  CHEAT_TAC;;

let word_list_AND_word_list_exists_IMP =
  cake_theorem "word_list_AND_word_list_exists_IMP"
  (fun () ->
    `!ws aa frame n.
        (misc_word_list aa ws * SEP_T) (fun2set (m,dm)) /\
        (word_list_exists aa n * frame) (fun2set (m,dm)) /\
        LENGTH ws <= n ==>
        (misc_word_list aa ws *
         word_list_exists (aa + bytes_in_word * n2w (LENGTH ws)) (n
           - LENGTH ws) *
         frame) (fun2set (m,dm))`)
  CHEAT_TAC;;

let memory_rel_Cons_alt = cake_theorem "memory_rel_Cons_alt"
  (fun () ->
    `memory_rel c be ts refs sp st m dm (ZIP vals ws ++ vars) /\
      LENGTH vals = LENGTH (ws:('a word_loc) list) /\ ~(vals = [])
        /\
      encode_header c (4 * tag) (LENGTH ws) = SOME hd /\
      LENGTH ws < sp /\ good_dimindex (:'a) ==>
      (?free' (curr:'a word) m1.
        FLOOKUP st NextFree = SOME (wordLang_Word free') /\
        FLOOKUP st CurrHeap = SOME (wordLang_Word curr) /\
        ((misc_word_list free' (wordLang_Word hd :: ws) * SEP_T)
          (fun2set (m,dm)) ==>
         memory_rel c be (ts + 1) refs (sp - (LENGTH ws + 1))
           (st |+ (NextFree,wordLang_Word (free' + bytes_in_word *
             n2w (LENGTH ws + 1)))) m dm
           ((Block ts tag vals,make_cons_ptr c (free' - curr) tag
             (LENGTH ws)) :: vars)))`)
  CHEAT_TAC;;

let memory_rel_REPLICATE = cake_theorem "memory_rel_REPLICATE"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((v,w) :: vars) ==>
      memory_rel c be ts refs sp st m dm (REPLICATE n (v,w) ++
        vars)`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:10078-10084: a theorem
   that HOL4 states as the value of an ML expression:
   memory_rel_RefArray *)

let word_of_byte_def = cake_define
  `word_of_byte (w:'a word) =
     (let w = (w << 8 || w) in
     let w = (w << 16 || w) in
       if dimindex (:'a) = 32 then w else w << 32 || w)`;;

(* HOL4 data_to_word_memoryProofScript.sml:10093-10096: a theorem
   that HOL4 states as the value of an ML expression: ADD_DIV_EQ *)

let set_byte_word_of_byte = cake_theorem "set_byte_word_of_byte[local]"
  (fun () ->
    `good_dimindex (:'a) ==>
       set_byte a w (word_of_byte ((w2w w):'a word)) be =
         word_of_byte (w2w w)`)
  CHEAT_TAC;;

let w2w_word_of_byte_w2w = cake_theorem "w2w_word_of_byte_w2w"
  (fun () ->
    `good_dimindex (:'a) ==>
     (w2w (word_of_byte (w2w w:'a word)):word8) = w`)
  CHEAT_TAC;;

let write_bytes_REPLICATE = cake_theorem "write_bytes_REPLICATE[local]"
  (fun () ->
    `!n m.
         good_dimindex (:'a) ==>
         write_bytes (REPLICATE m w) (REPLICATE n (word_of_byte
           (w2w w))) be =
         REPLICATE n (word_of_byte ((w2w w):'a word))`)
  CHEAT_TAC;;

let IMP_EXP_LESS = cake_theorem "IMP_EXP_LESS"
  (fun () ->
    `m <= l ==> 2 EXP m <= 2 EXP l`)
  CHEAT_TAC;;

let shift_shift_lemma = cake_theorem "shift_shift_lemma[local]"
  (fun () ->
    `l = k + backend_common_word_shift (:'a) /\ t < k /\ n DIV i < 2 EXP
  t /\ l = dimindex (:'a) /\
       i = 2 EXP backend_common_word_shift (:'a) /\ n < dimword
         (:'a) ==>
       n2w n << (k - t) >>> (l - t) = ((n2w (n DIV i)):'a word)`)
  CHEAT_TAC;;

let write_bytes_APPEND = cake_theorem "write_bytes_APPEND"
  (fun () ->
    `!xs ys vals be'.
        write_bytes vals (xs ++ (ys:('a word) list)) be' =
        write_bytes vals xs be' ++
        write_bytes (DROP ((dimindex (:'a) DIV 8) * LENGTH xs)
          vals) ys be'`)
  CHEAT_TAC;;

let set_byte_sort = cake_theorem "set_byte_sort"
  (fun () ->
    `!n1 n2.
        set_byte (n2w n1) b1 (set_byte (n2w n2:'a word) b2 w be) be
          =
        (if n1 = n2 then set_byte (n2w n1) b1 w be else
        if n1 < dimindex (:'a) DIV 8 /\ n2 < dimindex (:'a) DIV 8
          /\
           good_dimindex (:'a) /\ ~(n2 = n1) then
          set_byte (n2w n2) b2 (set_byte (n2w n1) b1 w be) be else
          set_byte (n2w n1) b1 (set_byte (n2w n2) b2 w be) be)`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:10203-10213: ML code, not
   ported *)

let set_byte_eq_ARB = cake_theorem "set_byte_eq_ARB"
  (fun () ->
    `good_dimindex (:'a) ==>
      (!x h h'.
        (set_byte (n2w 0) x h be = set_byte (n2w 0) x (h':'a word)
          be <=>
         set_byte (n2w 0) ARB h be = set_byte (n2w 0) ARB h' be) /\
        (set_byte (n2w 1) x h be = set_byte (n2w 1) x (h':'a word)
          be <=>
         set_byte (n2w 1) ARB h be = set_byte (n2w 1) ARB h' be) /\
        (set_byte (n2w 2) x h be = set_byte (n2w 2) x (h':'a word)
          be <=>
         set_byte (n2w 2) ARB h be = set_byte (n2w 2) ARB h' be) /\
        (set_byte (n2w 3) x h be = set_byte (n2w 3) x (h':'a word)
          be <=>
         set_byte (n2w 3) ARB h be = set_byte (n2w 3) ARB h' be) /\
        (set_byte (n2w 4) x h be = set_byte (n2w 4) x (h':'a word)
          be <=>
         set_byte (n2w 4) ARB h be = set_byte (n2w 4) ARB h' be) /\
        (set_byte (n2w 5) x h be = set_byte (n2w 5) x (h':'a word)
          be <=>
         set_byte (n2w 5) ARB h be = set_byte (n2w 5) ARB h' be) /\
        (set_byte (n2w 6) x h be = set_byte (n2w 6) x (h':'a word)
          be <=>
         set_byte (n2w 6) ARB h be = set_byte (n2w 6) ARB h' be) /\
        (set_byte (n2w 7) x h be = set_byte (n2w 7) x (h':'a word)
          be <=>
         set_byte (n2w 7) ARB h be = set_byte (n2w 7) ARB h' be))`)
  CHEAT_TAC;;

let bytes_to_word_eq_lemma = cake_theorem "bytes_to_word_eq_lemma"
  (fun () ->
    `good_dimindex (:'a) /\ LENGTH bs' = LENGTH bs /\
      bytes_to_word (dimindex (:'a) DIV 8) (n2w 0) bs (h:'a word)
        be =
      bytes_to_word (dimindex (:'a) DIV 8) (n2w 0) bs h' be ==>
      bytes_to_word (dimindex (:'a) DIV 8) (n2w 0) bs' h be =
      bytes_to_word (dimindex (:'a) DIV 8) (n2w 0) bs' h' be`)
  CHEAT_TAC;;

let write_bytes_inj_lemma = cake_theorem "write_bytes_inj_lemma"
  (fun () ->
    `good_dimindex (:'a) ==>
     (!w1 w2 bs bs'.
     write_bytes bs w1 be = write_bytes bs (w2:('a word) list) be
       /\
     LENGTH w1 = LENGTH w2 /\
     LENGTH bs' = LENGTH bs ==>
     write_bytes bs' w1 be = write_bytes bs' w2 be)`)
  CHEAT_TAC;;

(* slow *)
let set_byte_all_64 = cake_theorem "set_byte_all_64"
  (fun () ->
    `dimindex (:'a) = 64 ==>
     set_byte ((n2w 0):'a word) b1
       (set_byte (n2w 1) b2
         (set_byte (n2w 2) b3
           (set_byte (n2w 3) b4
             (set_byte (n2w 4) b5
               (set_byte (n2w 5) b6
                 (set_byte (n2w 6) b7
                   (set_byte (n2w 7) b8 x be) be) be) be) be) be)
                     be) be =
     set_byte (n2w 0) b1
       (set_byte (n2w 1) b2
         (set_byte (n2w 2) b3
           (set_byte (n2w 3) b4
             (set_byte (n2w 4) b5
               (set_byte (n2w 5) b6
                 (set_byte (n2w 6) b7
                   (set_byte (n2w 7) b8 y be) be) be) be) be) be)
                     be) be`)
  CHEAT_TAC;;

let set_byte_all_32 = cake_theorem "set_byte_all_32"
  (fun () ->
    `dimindex (:'a) = 32 ==>
     set_byte ((n2w 0):'a word) b1
       (set_byte (n2w 1) b2
         (set_byte (n2w 2) b3
                   (set_byte (n2w 3) b8 x be) be) be) be =
     set_byte (n2w 0) b1
       (set_byte (n2w 1) b2
         (set_byte (n2w 2) b3
                   (set_byte (n2w 3) b8 y be) be) be) be`)
  CHEAT_TAC;;

(* slow *)
let word_of_byte_set_byte_64 = cake_theorem "word_of_byte_set_byte_64"
  (fun () ->
    `dimindex (:'a) = 64 ==>
     word_of_byte (w2w w) =
     set_byte (n2w 0) w
       (set_byte (n2w 1) w
         (set_byte (n2w 2) w
           (set_byte (n2w 3) w
             (set_byte (n2w 4) w
               (set_byte (n2w 5) w
                 (set_byte (n2w 6) w
                   (set_byte (n2w 7) w (x:'a word) be) be) be)
                     be) be) be) be) be`)
  CHEAT_TAC;;

let word_of_byte_set_byte_32 = cake_theorem "word_of_byte_set_byte_32"
  (fun () ->
    `dimindex (:'a) = 32 ==>
     word_of_byte (w2w w) =
     set_byte (n2w 0) w
       (set_byte (n2w 1) w
         (set_byte (n2w 2) w
                   (set_byte (n2w 3) w (x:'a word) be) be) be) be`)
  CHEAT_TAC;;

let write_bytes_change_extra = cake_theorem "write_bytes_change_extra"
  (fun () ->
    `!ws bs be' ws'.
       good_dimindex (:'a) /\
       LENGTH ws = LENGTH ws' /\
       LENGTH ws < byte_len (:'a) (LENGTH bs) ==>
       write_bytes bs (ws:('a word) list) be' = write_bytes bs
         ws' be'`)
  CHEAT_TAC;;

let last_bytes_def = cake_define
  `last_bytes k b a w be' =
     (if k = 0 then w else
       set_byte a b (last_bytes (k - 1) b (a + (n2w 1)) w be')
         be')`;;

(* HOL4 data_to_word_memoryProofScript.sml:10399-10403: a theorem
   that HOL4 states as the value of an ML expression: last_bytes_simp *)

let last_bytes_bytes_to_word_REPLICATE =
  cake_theorem "last_bytes_bytes_to_word_REPLICATE"
  (fun () ->
    `!n1 n k a (w:'a word).
     n <= k /\ b1 = b2 /\ n1 = n ==>
     bytes_to_word k a (REPLICATE n b2) w be =
     last_bytes n1 b1 a w be`)
  CHEAT_TAC;;

let decode_length_make_byte_header =
  cake_theorem "decode_length_make_byte_header"
  (fun () ->
    `good_dimindex (:'a) /\ data_to_word_config_len_size c + 7 <
  dimindex (:'a) /\
     len + (2 EXP backend_common_word_shift (:'a)) < 2 EXP
       (data_to_word_config_len_size c + backend_common_word_shift
       (:'a)) ==>
     len <= w2n ((decode_length c (make_byte_header c fl len)):'a
       word) *
         (dimindex (:'a) DIV 8) /\
     w2n ((decode_length c (make_byte_header c fl len)):'a word) <=
         len DIV (dimindex (:'a) DIV 8) + 1`)
  CHEAT_TAC;;

let memory_rel_RefByte_content =
  cake_theorem "memory_rel_RefByte_content"
  (fun () ->
    `memory_rel c be ts refs sp st m dm vars /\ ~(new IN (domain refs))
  /\ byte_len (:'a) n < sp /\
     byte_len (:'a) n < 2 EXP (dimindex (:'a) - 4) /\
     byte_len (:'a) n < 2 EXP data_to_word_config_len_size c /\ n =
       LENGTH bytes /\
     good_dimindex (:'a) ==>
     (?free' curr m1.
       FLOOKUP st NextFree = SOME (wordLang_Word free') /\
       FLOOKUP st CurrHeap = SOME (wordLang_Word curr) /\
       (let w' = bytes_in_word * ((n2w (byte_len (:'a) n + 1)):'a
         word) in
        let ws = REPLICATE (byte_len (:'a) n) (n2w 0) in
        let ws = write_bytes bytes ws be in
          data_to_word_memoryProof_store_list free' (wordLang_Word
            (make_byte_header c fl n) :: MAP wordLang_Word ws) m dm =
            SOME m1 /\
          memory_rel c be ts (insert new (ByteArray fl bytes) refs)
            (sp - (byte_len (:'a) n + 1)) (st |+
              (NextFree,wordLang_Word (free' + w'))) m1 dm
            ((RefPtr T new,make_ptr c (free' - curr) ((n2w 0):'a
              word) (byte_len (:'a) n)) :: vars)))`)
  CHEAT_TAC;;

let memory_rel_RefByte_alt = cake_theorem "memory_rel_RefByte_alt"
  (fun () ->
    `memory_rel c be ts refs sp st m dm vars /\ ~(new IN (domain refs))
  /\ byte_len (:'a) n < sp /\
      byte_len (:'a) n < 2 EXP (dimindex (:'a) - 4) /\
      byte_len (:'a) n < 2 EXP data_to_word_config_len_size c /\
      good_dimindex (:'a) ==>
      (?free' curr m1.
        FLOOKUP st NextFree = SOME (wordLang_Word free') /\
        FLOOKUP st CurrHeap = SOME (wordLang_Word curr) /\
        (let w' = bytes_in_word * ((n2w (byte_len (:'a) n + 1)):'a
          word) in
         let ws = REPLICATE (byte_len (:'a) n) (wordLang_Word
           (word_of_byte (w2w w))) in
         let nb = (n MOD (dimindex (:'a) DIV 8)) in
         let ws = LUPDATE (wordLang_Word (last_bytes nb w (n2w 0)
           (n2w 0) be)) (byte_len (:'a) n - 1) ws in
           data_to_word_memoryProof_store_list free' (wordLang_Word
             (make_byte_header c fl n) :: ws) m dm = SOME m1 /\
           memory_rel c be ts (insert new (ByteArray fl (REPLICATE
             n w)) refs)
             (sp - (byte_len (:'a) n + 1)) (st |+
               (NextFree,wordLang_Word (free' + w'))) m1 dm
             ((RefPtr T new,make_ptr c (free' - curr) (n2w 0)
               (byte_len (:'a) n)) :: vars)))`)
  CHEAT_TAC;;

let memory_rel_tail = cake_theorem "memory_rel_tail"
  (fun () ->
    `memory_rel c be ts refs sp st m dm (v :: vars) ==>
      memory_rel c be ts refs sp st m dm vars`)
  CHEAT_TAC;;

let memory_rel_drop = cake_theorem "memory_rel_drop"
  (fun () ->
    `memory_rel c be ts refs sp st m dm (vs ++ vars) ==>
      memory_rel c be ts refs sp st m dm vars`)
  CHEAT_TAC;;

let memory_rel_IMP_word_list_exists =
  cake_theorem "memory_rel_IMP_word_list_exists"
  (fun () ->
    `memory_rel c be ts refs sp st m dm vars /\ n <= sp /\
      FLOOKUP st NextFree = SOME (wordLang_Word f) ==>
      (word_list_exists f n * SEP_T) (fun2set (m,dm))`)
  CHEAT_TAC;;

let get_addr_0 = cake_theorem "get_addr_0"
  (fun () ->
    `FAPPLY
        (get_addr c n u) 0`)
  CHEAT_TAC;;

let word_addr_eq_Loc = cake_theorem "word_addr_eq_Loc"
  (fun () ->
    `word_addr c v = Loc l1 l2 <=> l2 = 0 /\ (?l2. v = gc_shared_Data
  (Loc l1 l2))`)
  CHEAT_TAC;;

let blocks_unique_CodePtr = cake_theorem "blocks_unique_CodePtr"
  (fun () ->
    `blocks_unique ts (all_vs refs (MAP FST vars)) ==>
       blocks_unique ts (all_vs refs (CodePtr lab :: MAP FST
         vars))`)
  CHEAT_TAC;;

let memory_rel_CodePtr = cake_theorem "memory_rel_CodePtr"
  (fun () ->
    `memory_rel c be ts refs sp st m dm vars ==>
      memory_rel c be ts refs sp st m dm ((CodePtr lab,Loc lab 0)
        :: vars)`)
  CHEAT_TAC;;

let memory_rel_Block_IMP = cake_theorem "memory_rel_Block_IMP"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Block ts' tag vals,(v:'a
  word_loc)) :: vars) /\
      good_dimindex (:'a) ==>
      (?w. v = wordLang_Word w /\
          (if vals = [] then
            w = n2w tag * (n2w 16) + (n2w 2) /\ ~(FAPPLY w 0) /\
            tag < dimword (:'a) DIV 16 /\ ts' = 0 else
            ?a x. FAPPLY
              w 0 /\ ~(word_bit 3 x) /\ ~(word_bit 2 x) /\
              get_real_addr c st w = SOME a /\ m a = wordLang_Word
                x /\ a IN dm /\
              decode_length c x = n2w (LENGTH vals) /\
              LENGTH vals < 2 EXP (dimindex (:'a) - 4) /\
              encode_header c (4 * tag) (LENGTH vals) = SOME x /\
              ts' < ts))`)
  CHEAT_TAC;;

let IMP_memory_rel_Number = cake_theorem "IMP_memory_rel_Number"
  (fun () ->
    `good_dimindex (:'a) /\ small_int (:'a) i /\
      memory_rel c be ts refs sp st m dm vars ==>
      memory_rel c be ts refs sp st m dm
       ((Number i,(wordLang_Word (Smallnum i):'a word_loc)) ::
         vars)`)
  CHEAT_TAC;;

let memory_rel_El_any = cake_theorem "memory_rel_El_any"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Block ts' tag vals,(ptr:'a
  word_loc)) :: vars) /\
      good_dimindex (:'a) /\
      index < LENGTH vals ==>
      (?ptr_w x (y:'a word).
        ptr = wordLang_Word ptr_w /\
        get_real_addr c st ptr_w = SOME x /\
        (x + bytes_in_word + bytes_in_word * n2w index) IN dm /\
        memory_rel c be ts refs sp st m dm
          ((EL index vals,m (x + bytes_in_word + bytes_in_word *
            n2w index)) ::
           (Block ts' tag vals,ptr) :: vars))`)
  CHEAT_TAC;;

let copy_list_def = cake_define
  `copy_list c' st k (a,x,(b:'a word),(m:'a word->'a word_loc),dm) =
     (let c = (b IN dm) in
     let m = (b =+ x) m in
     let b = b + bytes_in_word in
       if k = 0 then (if c then SOME (b,m) else NONE) else
         match a with Loc _46 _47 -> NONE | wordLang_Word a ->
         (match get_real_addr c' st a with NONE -> NONE | SOME a ->
           (let c = (c /\ a + (n2w 2) * bytes_in_word IN dm /\ a +
             bytes_in_word IN dm) in
           let x = m (a + bytes_in_word) in
           let a = m (a + (n2w 2) * bytes_in_word) in
             if c then copy_list c' st (k - 1) (a,x,b,m,dm) else
               NONE)))`;;

(* HOL4 data_to_word_memoryProofScript.sml:10872-10965: a theorem
   that HOL4 states as the value of an ML expression: copy_list_thm *)

let memory_rel_FromList = cake_theorem "memory_rel_FromList"
  (fun () ->
    `v_to_list v = SOME vs /\ ~(vs = []) /\
      memory_rel c be ts refs sp st m dm ((v,(a:'a word_loc)) ::
        vars) /\
      encode_header c (4 * tag) (LENGTH vs) = SOME hd /\ LENGTH vs
        < sp /\
      good_dimindex (:'a) ==>
      (?free' curr m1 f1 xs.
        FLOOKUP st NextFree = SOME (wordLang_Word free') /\
        FLOOKUP st CurrHeap = SOME (wordLang_Word curr) /\
        copy_list c st (LENGTH vs) (a,wordLang_Word hd,free',m,dm)
          = SOME (f1,m1) /\
        memory_rel c be (ts + 1) refs (sp - (LENGTH vs + 1)) (st |+
          (NextFree,wordLang_Word f1)) m1 dm
          ((Block ts tag vs,
            make_cons_ptr c (free' - curr) tag (LENGTH vs)) ::
              vars))`)
  CHEAT_TAC;;

let make_header_tag_mask = cake_theorem "make_header_tag_mask[local]"
  (fun () ->
    `k < 2 EXP (dimindex (:'a) - (data_to_word_config_len_size c + 2))
  ==>
       (tag_mask c && make_header c ((n2w k):'a word) n) = n2w (4
         * k)`)
  CHEAT_TAC;;

let make_header_and_2 = cake_theorem "make_header_and_2[local]"
  (fun () ->
    `((n2w 2) && make_header c w n) = (n2w 2)`)
  CHEAT_TAC;;

let encode_header_tag_mask = cake_theorem "encode_header_tag_mask"
  (fun () ->
    `encode_header c (4 * tag) n = SOME (w:'a word) /\ good_dimindex
  (:'a) ==>
      tag < dimword (:'a) DIV 16 /\
      (w && (tag_mask c || (n2w 2))) = n2w (16 * tag + 2)`)
  CHEAT_TAC;;

let memory_rel_tag_limit = cake_theorem "memory_rel_tag_limit"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Block ts' tag l,(w:'a
  word_loc)) :: rest) /\
      good_dimindex (:'a) ==>
      tag < dimword (:'a) DIV 16`)
  CHEAT_TAC;;

let LESS_DIV_16_IMP = cake_theorem "LESS_DIV_16_IMP[local]"
  (fun () ->
    `n < k DIV 16 ==> 16 * n + 2 < (k:num)`)
  CHEAT_TAC;;

let MULT_BIT0 = cake_theorem "MULT_BIT0[local]"
  (fun () ->
    `BIT 0 (m * n) <=> BIT 0 m /\ BIT 0 n`)
  CHEAT_TAC;;

let memory_rel_test_nil_eq = cake_theorem "memory_rel_test_nil_eq"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Block ts' tag l,(w:'a
  word_loc)) :: rest) /\
      n < dimword (:'a) DIV 16 /\ good_dimindex (:'a) ==>
      (?v. w = wordLang_Word v /\ (v = n2w (16 * n + 2) <=> tag =
        n /\ l = []))`)
  CHEAT_TAC;;

let memory_rel_test_none_eq = cake_theorem "memory_rel_test_none_eq"
  (fun () ->
    `encode_header c (4 * n) len = (NONE:('a word) option) /\
      memory_rel c be ts refs sp st m dm ((Block ts' tag l,(w:'a
        word_loc)) :: rest) /\ ~(len = 0) /\ good_dimindex (:'a) ==>
      ~(tag = n /\ LENGTH l = len)`)
  CHEAT_TAC;;

let not_bit_lt_2exp = cake_theorem "not_bit_lt_2exp[local]"
  (fun () ->
    `!p x n. n < 2 EXP (p + 1) ==> ~(BIT (p + (x + 1)) n)`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:11090: ML code, not ported *)

let encode_header_EQ = cake_theorem "encode_header_EQ"
  (fun () ->
    `encode_header c t1 l1 = SOME (w1:'a word) /\
      encode_header c t2 l2 = SOME (w2:'a word) /\
        data_to_word_config_len_size
      c + 2 < dimindex (:'a) ==>
      (w1 = w2 <=> t1 = t2 /\ l1 = l2)`)
  CHEAT_TAC;;

let memory_rel_ValueArray_IMP = cake_theorem "memory_rel_ValueArray_IMP"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((RefPtr bl p,(v:'a word_loc))
  :: vars) /\
      lookup p refs = SOME (ValueArray vals) /\ good_dimindex (:'a)
        ==>
      (?w a x.
        v = wordLang_Word w /\ FAPPLY w 0 /\ word_bit 3 x /\
          ~(word_bit 2 x) /\ ~(word_bit 4 x) /\
        get_real_simple_addr c st w = SOME a /\
        get_real_addr c st w = SOME a /\
        m a = wordLang_Word x /\ a IN dm /\
        decode_length c x = n2w (LENGTH vals) /\
        LENGTH vals < 2 EXP (dimindex (:'a) - 4))`)
  CHEAT_TAC;;

let blocks_unique_Thunk = cake_theorem "blocks_unique_Thunk"
  (fun () ->
    `lookup p refs = SOME (Thunk ev x) /\
     blocks_unique ts (all_vs refs (RefPtr bl p :: MAP FST vars))
       ==>
       blocks_unique ts (all_vs refs (x :: MAP FST vars))`)
  CHEAT_TAC;;

let blocks_unique_Thunk2 = cake_theorem "blocks_unique_Thunk2"
  (fun () ->
    `lookup p refs = SOME (Thunk ev v') /\
     blocks_unique ts (all_vs refs (RefPtr F p :: MAP FST vars))
       ==>
       blocks_unique ts (all_vs refs (v' :: RefPtr F p :: MAP FST
         vars))`)
  CHEAT_TAC;;

let memory_rel_Thunk_IMP = cake_theorem "memory_rel_Thunk_IMP"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((RefPtr bl p,(v:'a word_loc))
  :: vars) /\
     lookup p refs = SOME (Thunk ev z) /\
     good_dimindex (:'a) ==>
       (~bl /\
        ev = Evaluated /\
        (!w. v = wordLang_Word w /\ FAPPLY w 0 ==>
           memory_rel c be ts refs sp st m dm ((z,v) :: vars) /\
           (?a x. get_real_addr c st w = SOME a /\
                 m a = wordLang_Word x /\ a IN dm /\ ~((x && (n2w
                   0b111100)) = n2w ((0 + 6) * 4)) /\ ~((x && (n2w
                   0b111100)) = n2w ((8 + 6) * 4))))) \/
       (?w a x.
         v = wordLang_Word w /\ FAPPLY w 0 /\ word_bit 3 x /\
           ~(word_bit 2 x) /\ word_bit 4 x /\
         get_real_simple_addr c st w = SOME a /\
         get_real_addr c st w = SOME a /\
         m a = wordLang_Word x /\ a IN dm /\
         (a + bytes_in_word) IN dm /\
         decode_length c x = (n2w 1) /\
         (word_bit 5 x <=> ev = Evaluated) /\
         memory_rel c be ts refs sp st m dm
           ((z,m (a + bytes_in_word)) :: (RefPtr bl p,v) ::
             vars))`)
  CHEAT_TAC;;

let memory_rel_Thunk_inlined = cake_theorem "memory_rel_Thunk_inlined"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((RefPtr bl p,(w:'a word_loc))
  :: vars) /\
     ((?l1 l2. w = Loc l1 l2) \/ (?w1. w = wordLang_Word w1 /\
       ~(FAPPLY w1 0))) /\
     lookup p refs = SOME (Thunk ev z) /\
     good_dimindex (:'a) ==>
       ev = Evaluated /\
       memory_rel c be ts refs sp st m dm ((z,w) :: vars)`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:11655-11657: the ML values
   that the definitions below antiquote *)

let get_byte_set_byte_alt = cake_theorem "get_byte_set_byte_alt"
  (fun () ->
    `good_dimindex (:'a) /\ ~(w = v) /\ byte_align w = byte_align v /\
      get_byte w s be = x ==>
      get_byte w (set_byte v b (s:'a word) be) be = x`)
  CHEAT_TAC;;

let get_byte_bytes_to_word = cake_theorem "get_byte_bytes_to_word"
  (fun () ->
    `!zs (t:'a word).
        i < LENGTH zs /\ i < 2 EXP k /\
        2 EXP k = dimindex (:'a) DIV 8 /\ good_dimindex (:'a) ==>
        get_byte (n2w i) (bytes_to_word (2 EXP k) (n2w 0) zs t
          be) be = EL i zs`)
  CHEAT_TAC;;

let MOD_MULT_MOD_LEMMA = cake_theorem "MOD_MULT_MOD_LEMMA[local]"
  (fun () ->
    `k MOD n = 0 /\ x MOD n = t /\ 0 < k /\ 0 < n /\ n <= k ==>
       x MOD k MOD n = t`)
  CHEAT_TAC;;

let w2n_add_byte_align_lemma = cake_theorem "w2n_add_byte_align_lemma"
  (fun () ->
    `good_dimindex (:'a) ==>
      w2n (a' + byte_align (a:'a word)) MOD (dimindex (:'a) DIV 8)
        =
      w2n a' MOD (dimindex (:'a) DIV 8)`)
  CHEAT_TAC;;

let get_byte_byte_align = cake_theorem "get_byte_byte_align"
  (fun () ->
    `good_dimindex (:'a) ==>
      get_byte (a' + byte_align a) w be = get_byte a' (w:'a word)
        be`)
  CHEAT_TAC;;

let get_byte_eq = cake_theorem "get_byte_eq"
  (fun () ->
    `good_dimindex (:'a) /\ a = byte_align a + a' ==>
      get_byte a w be = get_byte a' (w:'a word) be`)
  CHEAT_TAC;;

let write_bytes_same = cake_theorem "write_bytes_same"
  (fun () ->
    `!ws b1 b2.
     (!n. n < LENGTH (ws:('a word) list) * (dimindex (:'a) DIV 8)
       ==> n < LENGTH b1 /\ n < LENGTH b2 /\ EL n b1 = EL n b2) ==>
       write_bytes b1 ws be = write_bytes b2 ws be`)
  CHEAT_TAC;;

let set_byte_bytes_to_word = cake_theorem "set_byte_bytes_to_word"
  (fun () ->
    `i < LENGTH ls /\ i < 2 EXP k /\ 2 EXP k = dimindex (:'a) DIV 8 /\
     good_dimindex (:'a) ==>
     set_byte (n2w i) b (bytes_to_word (2 EXP k) (n2w 0) ls t be)
       be =
     bytes_to_word (2 EXP k) ((n2w 0):'a word) (LUPDATE b i ls) t
       be`)
  CHEAT_TAC;;

let heap_in_memory_store_UpdateByte =
  cake_theorem "heap_in_memory_store_UpdateByte"
  (fun () ->
    `heap_in_memory_store heap a sp sp1 gens c s m dm limit /\
     heap = ha ++ [Bytes be fl bs ws] ++ hb /\ i < LENGTH bs /\
     ad = curr + bytes_in_word + n2w i + (bytes_in_word:'a word) *
       n2w (heap_length ha) /\
     FLOOKUP s CurrHeap = SOME (wordLang_Word curr) /\
     m (byte_align ad) = wordLang_Word w /\ good_dimindex (:'a) ==>
     heap_in_memory_store (ha ++ [Bytes be fl (LUPDATE b i bs) ws]
       ++ hb)
     a sp sp1 gens c s
     ((byte_align ad =+ wordLang_Word (set_byte ad b w be)) m) dm
       limit`)
  CHEAT_TAC;;

let hide_memory_rel_def = cake_define
  `hide_memory_rel = memory_rel`;;

let hide_heap_in_memory_store_def = cake_define
  `hide_heap_in_memory_store = heap_in_memory_store`;;

let memory_rel_ByteArray_IMP = cake_theorem "memory_rel_ByteArray_IMP"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((RefPtr bl p,(v:'a word_loc))
  :: vars) /\
     lookup p refs = SOME (ByteArray fl vals) /\ good_dimindex
       (:'a) ==>
     (?w a x l.
       v = wordLang_Word w /\ FAPPLY w 0 /\
       make_byte_header c fl (LENGTH vals) = x /\
       ~(word_bit 3 x) /\ (word_bit 4 x <=> ~fl) /\ word_bit 2 x /\
       get_real_simple_addr c st w = SOME a /\
       get_real_addr c st w = SOME a /\
       m a = wordLang_Word x /\ a IN dm /\
       (!i. i < LENGTH vals ==>
            mem_load_byte_aux m dm be (a + bytes_in_word + n2w i) =
            SOME (EL i vals)) /\
       (!i w. i < LENGTH vals ==>
         (let addr' = a + bytes_in_word + n2w i in
         memory_rel c be ts (insert p (ByteArray fl (LUPDATE w i
           vals)) refs) sp st
           ((byte_align addr' =+
             wordLang_Word (set_byte addr' w (theWord (m
               (byte_align addr'))) be)) m) dm
             ((RefPtr bl p,v) :: vars))) /\
       (if dimindex (:'a) = 32 then
         LENGTH vals + 4 < 2 EXP (dimindex (:'a) - 3) /\
         (x >>> (dimindex (:'a) - data_to_word_config_len_size c -
           2) = n2w (LENGTH vals + 4)) else
         LENGTH vals + 8 < 2 EXP (dimindex (:'a) - 3) /\
         (x >>> (dimindex (:'a) - data_to_word_config_len_size c
           - 3) = n2w (LENGTH vals + 8))))`)
  CHEAT_TAC;;

let memory_rel_RefPtr_IMP_lemma =
  cake_theorem "memory_rel_RefPtr_IMP_lemma"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((RefPtr bl p,(v:'a word_loc))
  :: vars) ==>
      (?res. lookup p refs = SOME res)`)
  CHEAT_TAC;;

(* a compare-by-pointer RefPtr can never point at a MutBlock: v_inv's RefPtr
   case demands ~b when the ref is a MutBlock *)
let memory_rel_MutBlock_IMP_F =
  cake_theorem "memory_rel_MutBlock_IMP_F[local]"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((RefPtr T p,(v:'a word_loc)) ::
  vars) /\
     lookup p refs = SOME (bvlSem_MutBlock tg fin ls cv rs) ==> F`)
  CHEAT_TAC;;

let memory_rel_RefPtr_T_IMP = cake_theorem "memory_rel_RefPtr_T_IMP"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((RefPtr T p,v) :: vars) /\
     good_dimindex (:'a) ==>
       (?w a x.
         v = wordLang_Word w /\ FAPPLY w 0 /\
         (word_bit 3 x <=> ~(word_bit 2 x)) /\
         get_real_addr c st w = SOME a /\
         get_real_simple_addr c st w = SOME a /\
         m a = wordLang_Word (x:'a word) /\ a IN dm)`)
  CHEAT_TAC;;

(* the MutBlock exclusion is needed: a MutBlock is laid out with a BlockTag
   header, whose bits 2 and 3 are both clear, so the conclusion below fails *)
let memory_rel_RefPtr_IMP = cake_theorem "memory_rel_RefPtr_IMP"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((RefPtr bl p,v) :: vars) /\
     good_dimindex (:'a) /\
     (!t a. ~(lookup p refs = SOME (Thunk t a))) /\
     (!tg fin l cv rs. ~(lookup p refs = SOME (bvlSem_MutBlock tg
       fin l cv rs))) ==>
       (?w a x.
         v = wordLang_Word w /\ FAPPLY w 0 /\
         (word_bit 3 x <=> ~(word_bit 2 x)) /\
         get_real_addr c st w = SOME a /\
         get_real_simple_addr c st w = SOME a /\
         m a = wordLang_Word (x:'a word) /\ a IN dm)`)
  CHEAT_TAC;;

let memory_rel_RefPtr_gen_IMP = cake_theorem "memory_rel_RefPtr_gen_IMP"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((RefPtr bl p,v) :: vars) /\
     good_dimindex (:'a) ==>
     (?r. lookup p refs = SOME r /\
     (match r with Thunk Evaluated x ->
       (!w. v = wordLang_Word w /\ FAPPLY w 0 ==>
          (?a x. get_real_addr c st w = SOME a /\
                m a = wordLang_Word x /\ a IN dm /\ ~((x && (n2w
                  0b111100)) = n2w ((0 + 6) * 4)))) | bvlSem_MutBlock
                  _48 _49 _50 _51 _52 -> T | _53 ->
       (?w a x.
         v = wordLang_Word w /\ FAPPLY w 0 /\
         (word_bit 3 x <=> ~(word_bit 2 x)) /\
         get_real_addr c st w = SOME a /\
         get_real_simple_addr c st w = SOME a /\
         m a = wordLang_Word (x:'a word) /\ a IN dm)))`)
  CHEAT_TAC;;

let smallnum_bits = cake_theorem "Smallnum_bits"
  (fun () ->
    `((n2w 1) && Smallnum i) = (n2w 0) /\ ((n2w 2) && Smallnum i) =
  (n2w 0)`)
  CHEAT_TAC;;

let memory_rel_any_Number_IMP = cake_theorem "memory_rel_any_Number_IMP"
  (fun () ->
    `good_dimindex (:'a) /\
      memory_rel c be ts refs sp st m dm ((Number i,(v:'a
        word_loc)) :: vars) ==>
      (?w. v = wordLang_Word w /\ (FAPPLY w 0 <=> ~(small_int
        (:'a) i)))`)
  CHEAT_TAC;;

let memory_rel_Number_IMP = cake_theorem "memory_rel_Number_IMP"
  (fun () ->
    `good_dimindex (:'a) /\ small_int (:'a) i /\
      memory_rel c be ts refs sp st m dm ((Number i,(v:'a
        word_loc)) :: vars) ==>
      v = wordLang_Word (Smallnum i)`)
  CHEAT_TAC;;

let memory_rel_Number_bignum_IMP_ALT =
  cake_theorem "memory_rel_Number_bignum_IMP_ALT"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Number i,v) :: vars) /\
      ~(small_int (:'a) i) /\ good_dimindex (:'a) ==>
      (?ff w x a y.
        v = wordLang_Word w /\ ~((w && (n2w 1)) = ((n2w 0):'a
          word)) /\
        get_real_addr c st w = SOME a /\
        a IN dm /\ m a = wordLang_Word x /\ (~((x && (n2w 8)) =
          (n2w 0))) /\
        word_bit 2 x /\ word_bit 3 x /\
        (word_bit 4 x <=> i < (&0)) /\
        (misc_word_list (a + bytes_in_word)
          (MAP wordLang_Word (n2mw (num_of_int (abs i)))) * ff)
            (fun2set (m,dm)) /\
        a + bytes_in_word IN dm /\
        m (a + bytes_in_word) = wordLang_Word (n2w (num_of_int (abs
          i))) /\
        ((x && (n2w 16)) = (n2w 0) <=> (&0) <= i) /\
        LENGTH (n2mw (num_of_int (abs i)):('a word) list) < 2 EXP
          (dimindex (:'a) - 4) /\
        LENGTH (n2mw (num_of_int (abs i)):('a word) list) < dimword
          (:'a) /\
        decode_length c x = n2w
          (LENGTH (n2mw (num_of_int (abs i)):('a word) list)))`)
  CHEAT_TAC;;

let memory_rel_Number_bignum_header =
  cake_theorem "memory_rel_Number_bignum_header"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Number i,(v:'a word_loc)) ::
  vars) /\
      ~(small_int (:'a) i) /\ good_dimindex (:'a) ==>
      (?ff w x a y.
        v = wordLang_Word w /\ get_real_addr c st w = SOME a /\
        IS_SOME ((encode_header c (w2n ((b2w (i < (&0)) << 2 ||
          (n2w 3)):'a word))
            (LENGTH (n2mw (num_of_int (abs i)):('a word)
              list))):('a word) option) /\
        m a = wordLang_Word (make_header c (b2w (i < (&0)) << 2 ||
          (n2w 3))
                (LENGTH (n2mw (num_of_int (abs i)):('a word)
                  list))))`)
  CHEAT_TAC;;

let memory_rel_bignum_cmp = cake_theorem "memory_rel_bignum_cmp"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
          ((Number i1,v1) :: (Number i2,(v2:'a word_loc)) :: vars)
            /\
      good_dimindex (:'a) /\ ~(small_int (:'a) i1) /\ ~(small_int
        (:'a) i2) ==>
      (?w1 w2 a1 a2 x1 x2.
         v1 = wordLang_Word w1 /\ v2 = wordLang_Word w2 /\
         get_real_addr c st w1 = SOME a1 /\
         get_real_addr c st w2 = SOME a2 /\
         m a1 = wordLang_Word x1 /\
         m a2 = wordLang_Word x2 /\
         (~(x1 = x2) ==>
          (decode_length c (x1) = decode_length c (x2)) ==>
            ~((((n2w 16) && x1) = (n2w 0)) = (((n2w 16) && x2) = (n2w
            0)))))`)
  CHEAT_TAC;;

let memory_rel_Number_bignum_IMP =
  cake_theorem "memory_rel_Number_bignum_IMP"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Number i,v) :: vars) /\
      ~(small_int (:'a) i) /\ good_dimindex (:'a) ==>
      (?w x a y.
        v = wordLang_Word w /\ ~((w && (n2w 1)) = ((n2w 0):'a
          word)) /\
        get_real_addr c st w = SOME a /\
        a IN dm /\ m a = wordLang_Word x /\ (~((x && (n2w 8)) =
          (n2w 0))) /\
        a + bytes_in_word IN dm /\
        m (a + bytes_in_word) = wordLang_Word (n2w (num_of_int (abs
          i))) /\
        ((x && (n2w 16)) = (n2w 0) <=> (&0) <= i))`)
  CHEAT_TAC;;

let memory_rel_Word64_IMP = cake_theorem "memory_rel_Word64_IMP"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Word64 w64,(v:'a word_loc)) ::
  vars) /\
     good_dimindex (:'a) ==>
     (?ptr x w.
       v = wordLang_Word (get_addr c ptr (wordLang_Word (n2w 0)))
         /\
       get_real_addr c st (get_addr c ptr (wordLang_Word (n2w 0)))
         = SOME x /\
       x IN dm /\ m x = wordLang_Word w /\ word_bit 3 w /\
         ~(word_bit 4 w) /\ word_bit 2 w /\
       (x + bytes_in_word) IN dm /\
       (if dimindex (:'a) < 64 then
         (m (x + bytes_in_word) = wordLang_Word ((63 >< 32) w64) /\
          (x + (bytes_in_word << 1)) IN dm /\ m (x + (bytes_in_word
            << 1)) = wordLang_Word ((31 >< 0) w64) /\
         decode_length c w = (n2w 2) /\
         w = make_header c (n2w 3) 2) else
         (m (x + bytes_in_word) = wordLang_Word ((63 >< 0) w64)) /\
         decode_length c w = (n2w 1) /\
         w = make_header c (n2w 3) 1))`)
  CHEAT_TAC;;

let IMP_memory_rel_Number_num3 =
  cake_theorem "IMP_memory_rel_Number_num3"
  (fun () ->
    `good_dimindex (:'a) /\ n < 2 EXP (dimindex (:'a) - 3) /\
      memory_rel c be ts refs sp st m dm vars ==>
      memory_rel c be ts refs sp st m dm
       ((Number (&n),wordLang_Word ((n2w n << 2):'a word)) ::
         vars)`)
  CHEAT_TAC;;

let IMP_memory_rel_Number_num = cake_theorem "IMP_memory_rel_Number_num"
  (fun () ->
    `good_dimindex (:'a) /\ n < 2 EXP (dimindex (:'a) - 4) /\
      memory_rel c be ts refs sp st m dm vars ==>
      memory_rel c be ts refs sp st m dm
       ((Number (&n),wordLang_Word ((n2w n << 2):'a word)) ::
         vars)`)
  CHEAT_TAC;;

let memory_rel_Number_EQ = cake_theorem "memory_rel_Number_EQ"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
        ((Number i1,w1) :: (Number i2,w2) :: vars) /\
      (small_int (:'a) i1 \/ small_int (:'a) i2) /\
      good_dimindex (:'a) ==>
        (?v1 v2. w1 = wordLang_Word v1 /\ w2 = wordLang_Word
          (v2:'a word) /\ (v1 = v2 <=> i1 = i2))`)
  CHEAT_TAC;;

let memory_rel_Number_LESS = cake_theorem "memory_rel_Number_LESS"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
        ((Number i1,w1) :: (Number i2,w2) :: vars) /\
      small_int (:'a) i1 /\
      small_int (:'a) i2 /\
      good_dimindex (:'a) ==>
        (?v1 v2. w1 = wordLang_Word v1 /\ w2 = wordLang_Word v2
          /\ (v1 < (v2:'a word) <=> i1 < i2))`)
  CHEAT_TAC;;

let memory_rel_Number_LESS_EQ = cake_theorem "memory_rel_Number_LESS_EQ"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
        ((Number i1,w1) :: (Number i2,w2) :: vars) /\
      small_int (:'a) i1 /\
      small_int (:'a) i2 /\
      good_dimindex (:'a) ==>
        (?v1 v2. w1 = wordLang_Word v1 /\ w2 = wordLang_Word v2
          /\ (v1 <= (v2:'a word) <=> i1 <= i2))`)
  CHEAT_TAC;;

let memory_rel_Number_word_msb =
  cake_theorem "memory_rel_Number_word_msb"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Number i1,wordLang_Word (w:'a
  word)) :: vars) /\
      good_dimindex (:'a) /\ small_int (:'a) i1 ==>
      (word_msb w <=> i1 < (&0))`)
  CHEAT_TAC;;

let memory_rel_RefPtr_EQ_lemma =
  cake_theorem "memory_rel_RefPtr_EQ_lemma[local]"
  (fun () ->
    `n * 2 EXP k < dimword (:'a) /\ m * 2 EXP k < dimword (:'a) /\ 0 < k
  /\
       (n2w n << k || (n2w 1)) = (n2w m << k || ((n2w 1):'a
         word)) ==> n = m`)
  CHEAT_TAC;;

let memory_rel_RefPtr_EQ = cake_theorem "memory_rel_RefPtr_EQ"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
        ((RefPtr T i1,w1) :: (RefPtr T i2,w2) :: vars) /\
          good_dimindex (:'a) ==>
        (?v1 v2. w1 = wordLang_Word v1 /\ w2 = wordLang_Word
          (v2:'a word) /\ (v1 = v2 <=> i1 = i2))`)
  CHEAT_TAC;;

let memory_rel_RefPtr_EQ_IMP = cake_theorem "memory_rel_RefPtr_EQ_IMP"
  (fun () ->
    `memory_rel c be ts refs sp st m (dm:'a word->bool)
       ((RefPtr b1 i1,wordLang_Word w1) :: (RefPtr b2
         i1,wordLang_Word w2) :: vars) /\ good_dimindex (:'a) /\
     lookup i1 refs = SOME (ByteArray ys_fl ys) ==>
     w1 = w2`)
  CHEAT_TAC;;

let memory_rel_Boolv_T = cake_theorem "memory_rel_Boolv_T"
  (fun () ->
    `memory_rel c be ts refs sp st m dm vars /\ good_dimindex (:'a)
  ==> memory_rel c be ts refs sp st m dm ((Boolv T,wordLang_Word ((n2w
  18):'a word)) :: vars)`)
  CHEAT_TAC;;

let memory_rel_Boolv_F = cake_theorem "memory_rel_Boolv_F"
  (fun () ->
    `memory_rel c be ts refs sp st m dm vars /\ good_dimindex (:'a)
  ==> memory_rel c be ts refs sp st m dm ((Boolv F,wordLang_Word ((n2w
  2):'a word)) :: vars)`)
  CHEAT_TAC;;

let memory_rel_Boolv = cake_theorem "memory_rel_Boolv"
  (fun () ->
    `memory_rel c be ts refs sp st m dm vars /\ good_dimindex (:'a) /\
     (b ==> v = wordLang_Word (n2w 18)) /\ (~b ==> v =
       wordLang_Word ((n2w 2):'a word)) ==>
     memory_rel c be ts refs sp st m dm ((Boolv b,v) :: vars)`)
  CHEAT_TAC;;

let word_ml_inv_SP_LIMIT = cake_theorem "word_ml_inv_SP_LIMIT"
  (fun () ->
    `word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs stack ==> sp
  <= limit`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:12767-12769: the ML values
   that the definitions below antiquote *)

let smallnum_test = cake_theorem "Smallnum_test[local]"
  (fun () ->
    `((Smallnum i && --(n2w 1) << (dimindex (:'a) - 2)) = ((n2w 0):'a
  word)) /\
       good_dimindex (:'a) /\ small_int (:'a) i ==>
       ~(i < (&0)) /\ i < &(2 EXP (dimindex (:'a) - 4))`)
  CHEAT_TAC;;

let small_int_w2i_i2w = cake_theorem "small_int_w2i_i2w[local]"
  (fun () ->
    `small_int (:'a) i /\ good_dimindex (:'a) ==>
     w2i ((i2w ((&4) * i)):'a word) = (&4) * i`)
  CHEAT_TAC;;

let memory_rel_Add = cake_theorem "memory_rel_Add"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
        ((Number i,wordLang_Word wi) :: (Number j,wordLang_Word wj)
          :: vars) /\
      ~(word_bit 0 wi) /\ ~(word_bit 0 wj) /\
      good_dimindex (:'a) /\ (w2i (wi + wj) = w2i wi + w2i wj) ==>
      memory_rel c be ts refs sp st m dm
        ((Number (i + j),wordLang_Word (wi + (wj:'a word))) ::
          vars)`)
  CHEAT_TAC;;

let memory_rel_Sub = cake_theorem "memory_rel_Sub"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
        ((Number i,wordLang_Word wi) :: (Number j,wordLang_Word wj)
          :: vars) /\
      ~(word_bit 0 wi) /\ ~(word_bit 0 wj) /\
      good_dimindex (:'a) /\ (w2i (wi - wj) = w2i wi - w2i wj) ==>
      memory_rel c be ts refs sp st m dm
        ((Number (i - j),wordLang_Word (wi - (wj:'a word))) ::
          vars)`)
  CHEAT_TAC;;

let exists_num = cake_theorem "exists_num[local]"
  (fun () ->
    `~(i < (&0)) <=> (?n. i = &n)`)
  CHEAT_TAC;;

let small_int_w2n = cake_theorem "small_int_w2n[simp]"
  (fun () ->
    `good_dimindex (:'a) ==> small_int (:'a) (&(w2n (w:word8)))`)
  CHEAT_TAC;;

let memory_rel_And = cake_theorem "memory_rel_And"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
        ((Number (&(w2n (i:word8))),wordLang_Word wi) :: (Number
          (&(w2n j)),wordLang_Word wj) :: vars) /\
      good_dimindex (:'a) ==>
      memory_rel c be ts refs sp st m dm
        ((Number (&(w2n (i && j))),wordLang_Word (wi && (wj:'a
          word))) :: vars)`)
  CHEAT_TAC;;

let memory_rel_Or = cake_theorem "memory_rel_Or"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
        ((Number (&(w2n (i:word8))),wordLang_Word wi) :: (Number
          (&(w2n j)),wordLang_Word wj) :: vars) /\
      good_dimindex (:'a) ==>
      memory_rel c be ts refs sp st m dm
        ((Number (&(w2n (i || j))),wordLang_Word (wi || (wj:'a
          word))) :: vars)`)
  CHEAT_TAC;;

let memory_rel_Xor = cake_theorem "memory_rel_Xor"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
        ((Number (&(w2n (i:word8))),wordLang_Word wi) :: (Number
          (&(w2n j)),wordLang_Word wj) :: vars) /\
      good_dimindex (:'a) ==>
      memory_rel c be ts refs sp st m dm
        ((Number (&(w2n (word_xor i j))),wordLang_Word (word_xor
          wi wj:'a word)) :: vars)`)
  CHEAT_TAC;;

let memory_rel_Number_IMP_Word =
  cake_theorem "memory_rel_Number_IMP_Word"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Number i,v) :: vars) ==>
  (?w. v = wordLang_Word w)`)
  CHEAT_TAC;;

let memory_rel_Number_IMP_Word_2 =
  cake_theorem "memory_rel_Number_IMP_Word_2"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Number i,v) :: (Number j,w) ::
  vars) ==>
      (?w1 w2. v = wordLang_Word w1 /\ w = wordLang_Word w2)`)
  CHEAT_TAC;;

let memory_rel_zero_space = cake_theorem "memory_rel_zero_space"
  (fun () ->
    `memory_rel c be ts refs sp st m dm vars ==>
      memory_rel c be ts refs 0 st m dm vars`)
  CHEAT_TAC;;

let memory_rel_less_space = cake_theorem "memory_rel_less_space"
  (fun () ->
    `memory_rel c be ts refs sp st m dm vars /\ sp' <= sp ==>
     memory_rel c be ts refs sp' st m dm vars`)
  CHEAT_TAC;;

let all_ones_bit = cake_theorem "all_ones_bit"
  (fun () ->
    `i < dimindex (:'a) ==>
     (FAPPLY (all_ones e b:'a word) i <=> b <= i /\ i < e)`)
  CHEAT_TAC;;

let maxout_bits_bit = cake_theorem "maxout_bits_bit"
  (fun () ->
    `FAPPLY
       (maxout_bits n l b:'a word) i /\ i < dimindex (:'a) ==>
       b <= i /\ i < b + l`)
  CHEAT_TAC;;

let maxout_bits_IMP = cake_theorem "maxout_bits_IMP"
  (fun () ->
    `i < dimindex (:'a) /\ FAPPLY (maxout_bits tag k n:'a word) i ==>
  i < n + k`)
  CHEAT_TAC;;

let make_cons_ptr_thm = cake_theorem "make_cons_ptr_thm"
  (fun () ->
    `make_cons_ptr conf (f:'a word) tag len =
       wordLang_Word ((f << (shift_length conf -
         backend_common_word_shift (:'a)) || (n2w 1) ||
              ptr_bits conf tag len))`)
  CHEAT_TAC;;

let Num_ABS_lemmas = cake_theorem "Num_ABS_lemmas[local]"
  (fun () ->
    `num_of_int (abs (&n)) = n /\ num_of_int (abs (--(&n))) = n`)
  CHEAT_TAC;;

let word_cmp_res_def = cake_define
  `word_cmp_res i (j:int) =
     (if i = j then (n2w 1) else if i < j then (n2w 0) else (n2w
       2))`;;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let word_cmp_loop_def = cake_define_cheat CHEAT_TAC
  `word_cmp_loop (l:'a word) (a1:'a word) a2 dm (m:'a word->'a word_loc)
  =
     (if l = (n2w 0) then SOME (n2w 1) else
       if a1 IN dm /\ a2 IN dm then
         match (m a1,m a2) with (wordLang_Word w1,wordLang_Word w2)
           ->
             (if w1 = w2 then
               word_cmp_loop (l - (n2w 1)) (a1 - bytes_in_word)
                 (a2 - bytes_in_word) dm m else if w1 <+ w2 then
                   SOME (n2w 0) else SOME ((n2w 2):'a word)) | _54 ->
                   NONE else NONE)`;;

(* HOL4 data_to_word_memoryProofScript.sml:13106: ML code, not ported *)

let word_cmp_loop_thm = cake_theorem "word_cmp_loop_thm[local]"
  (fun () ->
    `!xs1 (xs2:('a word) list) f1 f2 (a1:'a word) a2.
       LENGTH xs1 = LENGTH xs2 /\ LENGTH xs1 < dimword (:'a) /\
       (misc_word_list (a1 + bytes_in_word) (MAP wordLang_Word xs1)
         * f1) (fun2set (m,dm)) /\
       (misc_word_list (a2 + bytes_in_word) (MAP wordLang_Word xs2)
         * f2) (fun2set (m,dm)) ==>
       word_cmp_loop (n2w (LENGTH xs1))
         (a1 + bytes_in_word * n2w (LENGTH xs1))
         (a2 + bytes_in_word * n2w (LENGTH xs1)) dm m =
         SOME (match mw_cmp xs1 xs2 with NONE -> (n2w 1) | SOME T
           -> (n2w 0) | SOME F -> (n2w 2))`)
  CHEAT_TAC;;

let memory_rel_Number_cmp = cake_theorem "memory_rel_Number_cmp"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Number i1,v1) :: (Number
  i2,v2) :: vars) /\
     good_dimindex (:'a) ==>
     (?w1 w2.
       v1 = wordLang_Word w1 /\ v2 = wordLang_Word (w2:'a word) /\
       (if ~(word_bit 0 w1) /\ ~(word_bit 0 w2) then
         (i1 < i2 <=> w1 < w2) /\ (i1 = i2 <=> w1 = w2) else if
           ~(word_bit 0 w1) /\ word_bit 0 w2 then ~(i1 = i2) /\
         (?a x2. get_real_addr c st w2 = SOME a /\
                m a = wordLang_Word x2 /\ a IN dm /\
                word_cmp_res i1 i2 = (if (x2 && (n2w 16)) = (n2w 0)
                  then (n2w 0) else (n2w 2):'a word)) else if word_bit 0
                  w1 /\ word_bit 0 w2 then
         ?a1 x1 a2 x2.
           get_real_addr c st w1 = SOME a1 /\ m a1 = wordLang_Word
             x1 /\ a1 IN dm /\
           get_real_addr c st w2 = SOME a2 /\ m a2 = wordLang_Word
             x2 /\ a2 IN dm /\
           (if x1 = x2 then
             let (a1,a2) = (if (x1 && (n2w 16)) = (n2w 0) then
               (a1,a2) else (a2,a1)) in
               word_cmp_loop (decode_length c x1)
                 (a1 + bytes_in_word * (decode_length c x1))
                 (a2 + bytes_in_word * (decode_length c x2))
                   dm m = SOME (word_cmp_res i1 i2) else
             word_cmp_res i1 i2 =
             (if (x1 && (n2w 16)) = (n2w 0) then
                if (x2 && (n2w 16)) = (n2w 0) then
                  if decode_length c x1 <+ decode_length c x2 then
                    (n2w 0) else (n2w 2):'a word else
                  (n2w 2) else
                if (x2 && (n2w 16)) = (n2w 0) then
                  (n2w 0) else
                  if decode_length c x1 <+ decode_length c x2
                    then (n2w 2) else (n2w 0))) else T))`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:13234-13244: a theorem
   that HOL4 states as the value of an ML expression:
   word_cmp_loop_refl *)

(* HOL4 data_to_word_memoryProofScript.sml:13246: ML code, not ported *)

let _ = size_thms "dataSem_v";;
(* HOL4 data_to_word_memoryProofScript.sml:13255-13261: the tactic
   that proves the termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let v_same_type_def = cake_define_try_tac (fun () ->
  `MEASURE (dataSem_v_size o FST)`)
  CHEAT_TAC
  `v_same_type x1 x2 =
        match (x1,x2) with
          ((Number _57:dataSem_v),(Number _58:dataSem_v)) -> T
        | ((Word64 _59),(Word64 _60)) -> T
        | ((Block _61 t1 l1),(Block _62 t2 l2)) -> (t1 = t2 /\ LENGTH
          l1 = LENGTH l2 ==> LIST_REL v_same_type l1 l2)
        | ((CodePtr _63),(CodePtr _64)) -> T
        | ((RefPtr _65 _66),(RefPtr _67 _68)) -> T
        | (_69,_70) -> F`;;

let memory_rel_Block_MEM = cake_theorem "memory_rel_Block_MEM"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Block ts' n ls,(v:'a
  word_loc)) :: vars) /\
     i < LENGTH ls /\
     good_dimindex (:'a) ==>
     (?w a y.
     get_real_offset (Smallnum (&i)) = SOME y /\
     v = wordLang_Word w /\ get_real_addr c st w = SOME a /\ (a +
       y) IN dm /\
     memory_rel c be ts refs sp st m dm ((EL i ls,m (a + y)) ::
       (Block ts' n ls,v) :: vars))`)
  CHEAT_TAC;;

let smallnum_0 = cake_theorem "Smallnum_0"
  (fun () ->
    `~(FAPPLY (Smallnum i:'a word) 0)`)
  CHEAT_TAC;;

let smallnum_1 = cake_theorem "Smallnum_1"
  (fun () ->
    `good_dimindex (:'a) ==> ~(FAPPLY (Smallnum i:'a word) 1)`)
  CHEAT_TAC;;

let do_eq_list_F_IMP_MEM = cake_theorem "do_eq_list_F_IMP_MEM[local]"
  (fun () ->
    `!l l'.
       do_eq_list refs l l' = Eq_val F /\ LENGTH l' = LENGTH l ==>
       (?i. i < LENGTH l /\ do_eq refs (EL i l) (EL i l') =
         Eq_val F)`)
  CHEAT_TAC;;

let memory_rel_rotate3 = cake_theorem "memory_rel_rotate3[local]"
  (fun () ->
    `memory_rel c be ts refs sp st m dm (x1 :: x2 :: x3 :: vars) ==>
     memory_rel c be ts refs sp st m dm (x3 :: x1 :: x2 :: vars)`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:13328-13410: a theorem
   that HOL4 states as the value of an ML expression:
   memory_rel_pointer_eq *)

(* HOL4 data_to_word_memoryProofScript.sml:13412-13416: a theorem
   whose statement the port cannot state yet: v1_size_map *)

let _ = size_thms "dataSem_v";;
(* HOL4 data_to_word_memoryProofScript.sml:13421-13425: the tactic
   that proves the termination *)
let v_depth_def = cake_define_wf
  `MEASURE dataSem_v_size`
  `v_depth x1 =
        match x1 with
          (Block _73 _74 ls:dataSem_v) -> (if NULL ls then 0 else 1)
            + MAX_LIST (MAP v_depth ls)
        | _75 -> 0`;;

(* HOL4 data_to_word_memoryProofScript.sml:13427: ML code, not ported *)

let v_inv_Block_tag_limit = cake_theorem "v_inv_Block_tag_limit"
  (fun () ->
    `v_inv c (Block ts n l) refs (v,f,tf,(heap:(('a
  word_loc,data_to_word_memoryProof_tag#('a word_loc) list)heap_element)
  list)) /\
     heap_in_memory_store heap a sp sp1 gens c s m (dm:'a
       word->bool) limit ==> n < dimword (:'a) DIV 16`)
  CHEAT_TAC;;

let elements_list_def = cake_define_list
  [`elements_list [] = T`;
   `elements_list [v] = T`;
   `elements_list (v :: w :: vs) =
       (?ts t ls1 ls2.
         w = Block ts t (ls1 ++ [v] ++ ls2) /\
         elements_list (w :: vs))`];;

(* HOL4 data_to_word_memoryProofScript.sml:13453: ML code, not ported *)

let memory_rel_depth_limit = cake_theorem "memory_rel_depth_limit"
  (fun () ->
    `!v w vars'.
      memory_rel c b ts refs sp st m dm ((v,(w:'a word_loc)) ::
        vars') /\
      elements_list (v :: (MAP FST vars')) /\ good_dimindex (:'a)
        ==>
      (?ls.
         memory_rel c b ts refs sp st m dm (ls ++ ((v,w) :: vars'))
           /\
         v_depth v = LENGTH ls /\
         elements_list (MAP FST ls ++ (v :: (MAP FST vars'))))`)
  CHEAT_TAC;;

let not_all_distinct_map_snd =
  cake_theorem "not_all_distinct_map_snd[local]"
  (fun () ->
    `~(ALL_DISTINCT (MAP SND xs)) ==>
     (?xs1 xs2 xs3 x y1 y2. xs = xs1 ++ [(y1,x)] ++ xs2 ++
       [(y2,x)] ++ xs3)`)
  CHEAT_TAC;;

let IN_all_vs_HD = cake_theorem "IN_all_vs_HD"
  (fun () ->
    `x IN all_vs refs (x :: xs)`)
  CHEAT_TAC;;

let IN_all_vs_TL = cake_theorem "IN_all_vs_TL"
  (fun () ->
    `x IN all_vs refs xs ==>
     x IN all_vs refs (y :: xs)`)
  CHEAT_TAC;;

let get_lowerbits_shift_length =
  cake_theorem "get_lowerbits_shift_length[local]"
  (fun () ->
    `(w2 >>> n) = (n2w 0) ==>
       ((w1 || w2) >>> n) = (w1 >>> n)`)
  CHEAT_TAC;;

let shift_shift = cake_theorem "shift_shift[local]"
  (fun () ->
    `n1 * (2 EXP l) < dimword (:'a) ==>
       n2w n1 << l >>> l = (n2w n1:'a word)`)
  CHEAT_TAC;;

let word_addr_Data_NE_get_addr =
  cake_theorem "word_addr_Data_NE_get_addr[local]"
  (fun () ->
    `good_dimindex (:'a) ==> ~(word_addr c (gc_shared_Data a1) =
  wordLang_Word (get_addr c n a2:'a word))`)
  CHEAT_TAC;;

let memory_rel_Block_ptr_eq = cake_theorem "memory_rel_Block_ptr_eq"
  (fun () ->
    `memory_rel c be ts refs sp st m (dm:'a word->bool)
       ((Block t1 a1 b1,x) :: (Block t2 a2 b2,x) :: rest) /\
     good_dimindex (:'a) ==>
     Block t1 a1 b1 = Block t2 a2 b2`)
  CHEAT_TAC;;

let elements_list_all_blocks = cake_theorem "elements_list_all_blocks"
  (fun () ->
    `elements_list xs /\ ~(xs = []) /\ (?t a b. HD xs = Block t a b) ==>
     EVERY (\x. ?t a b. x = Block t a b) xs /\
     SORTED (\x y. vb_size x < vb_size y) xs`)
  CHEAT_TAC;;

let memory_rel_elements_list_distinct_lemma =
  cake_theorem "memory_rel_elements_list_distinct_lemma[local]"
  (fun () ->
    `!vs vars' tag a b.
       memory_rel c be ts refs sp st m (dm:'a word->bool) vars' /\
       elements_list vs /\ vs = MAP FST vars' /\
       good_dimindex (:'a) /\ ~(vs = []) /\
       HD vs = Block tag a b ==>
       ALL_DISTINCT (MAP SND vars')`)
  CHEAT_TAC;;

let memory_rel_elements_list_distinct =
  cake_theorem "memory_rel_elements_list_distinct"
  (fun () ->
    `!vs vars'.
       memory_rel c be ts refs sp st m (dm:'a word->bool) vars' /\
       elements_list vs /\ vs = MAP FST vars' /\
       good_dimindex (:'a) ==>
       ALL_DISTINCT (MAP SND (TL vars'))`)
  CHEAT_TAC;;

let memory_rel_elements_list_words =
  cake_theorem "memory_rel_elements_list_words"
  (fun () ->
    `!vs vars'.
       memory_rel c be ts refs sp st m (dm:'a word->bool) vars' /\
       elements_list vs /\ vs = MAP FST vars' /\
       good_dimindex (:'a) ==> ~(vars' = []) ==> EVERY isWord (TL
         (MAP SND vars'))`)
  CHEAT_TAC;;

let memory_rel_depth_size_limit =
  cake_theorem "memory_rel_depth_size_limit"
  (fun () ->
    `!v w vars'.
     memory_rel c be ts refs sp st m dm ((v,(w:'a word_loc)) ::
       vars') /\
     good_dimindex (:'a) ==>
     vb_size v <= dimword (:'a) EXP (v_depth v + 1)`)
  CHEAT_TAC;;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let vb_eq_size_def = cake_define_list_cheat CHEAT_TAC
  [`vb_eq_size refs (Block _78 t1 l1:dataSem_v) (Block _79 t2
  l2:dataSem_v) =
         (if isClos t1 l1 \/ isClos t2 l2 then if isClos t1 l1 /\
           isClos t2 l2 then SOME ((1:num),T) else NONE else if (t1 =
           t2) /\ (LENGTH l1 = LENGTH l2) then OPTION_MAP (\(n,b). (n
           + 1,b)) (vb_eq_size_list refs l1 l2) else SOME (1,F))`;
   `vb_eq_size refs (RefPtr b1 n1:dataSem_v) (RefPtr b2 n2:dataSem_v) =
         (if b1 /\ b2 then
           (match (sptree_lookup n1 refs,sptree_lookup n2 refs) with
              (SOME (ByteArray T bs1),SOME (ByteArray T bs2)) ->
                SOME (1,(bs1 = bs2)) | (SOME (ByteArray T bs1),_86)
                -> NONE | (_87,SOME (ByteArray T bs2)) -> NONE | _88
                -> SOME (1,(n1 = n2))) else NONE)`;
   `vb_eq_size _89 (Number n1:dataSem_v) (Number n2:dataSem_v) = SOME
  (1,(n1 = n2))`;
   `vb_eq_size _90 (Word64 w1:dataSem_v) (Word64 w2:dataSem_v) = SOME
  (1,(w1 = w2))`;
   `vb_eq_size _91 _92 _93 = NONE`;
   `vb_eq_size_list _94 [] [] = SOME (0,T)`;
   `vb_eq_size_list _95 [] _96 = SOME (0,F)`;
   `vb_eq_size_list _97 _98 [] = SOME (0,F)`;
   `vb_eq_size_list refs (v1 :: vs1) (v2 :: vs2) =
         (match vb_eq_size refs v1 v2 with NONE -> NONE | SOME (n,F)
           -> SOME (n + 1,F) | SOME (n,T) -> (
           match vb_eq_size_list refs vs1 vs2 with NONE -> NONE
             | SOME (m,b) -> SOME (m + n + 1,b)))`];;

let vb_eq_size_IMP_vb_size = cake_theorem "vb_eq_size_IMP_vb_size"
  (fun () ->
    `(!(refs:('a bvlSem_ref) spt) v1 v2 n b.
       vb_eq_size refs v1 v2 = SOME (n,b) ==> n <= vb_size v1) /\
     (!(refs:('a bvlSem_ref) spt) v1 v2 n b.
       vb_eq_size_list refs v1 v2 = SOME (n,b) ==> n <= SUM (MAP
         vb_size v1) + LENGTH v1)`)
  CHEAT_TAC;;

let memory_rel_limit = cake_theorem "memory_rel_limit"
  (fun () ->
    `!v w.
       memory_rel c be ts refs sp st m dm
         ((v1,(w1:'a word_loc)) :: (v2,(w2:'a word_loc)) :: vars)
           /\
       vb_eq_size refs v1 v2 = SOME (n,b) /\
       good_dimindex (:'a) ==>
       n * dimword (:'a) < MustTerminate_limit (:'a) - dimword
         (:'a)`)
  CHEAT_TAC;;

let memory_rel_ptr_eq = cake_theorem "memory_rel_ptr_eq"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((v1,x1) :: (v2,(x1:'a
  word_loc)) :: vars) /\
     do_eq refs v1 v2 = Eq_val b /\
     good_dimindex (:'a) ==> b`)
  CHEAT_TAC;;

let memory_rel_Block_Block_small_eq =
  cake_theorem "memory_rel_Block_Block_small_eq[local]"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
       ((Block ts1 t1 v1,wordLang_Word (w1:'a word)) :: (Block ts2
         t2 v2,wordLang_Word w2) :: vars) /\
     good_dimindex (:'a) /\ ~(w1 = w2) /\ ~(word_bit 0 w1) ==>
       ~(LENGTH v1 = LENGTH v2) \/ ~(t1 = t2)`)
  CHEAT_TAC;;

let memory_rel_simple_eq = cake_theorem "memory_rel_simple_eq"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((v1,x1) :: (v2,x2) :: vars) /\
     do_eq refs v1 v2 = Eq_val b /\
     good_dimindex (:'a) ==>
     (?w1 (w2:'a word).
       x1 = wordLang_Word w1 /\ x2 = wordLang_Word w2 /\
       (~(word_bit 0 w1) \/ ~(word_bit 0 w2) ==>
       (w1 = w2) = b))`)
  CHEAT_TAC;;

let word_header_def = cake_define
  `word_header c st a dm m =
     (match get_real_addr c st a with NONE -> NONE | SOME a1 ->
         (if ~(a1 IN dm) then NONE else
           match m a1 with wordLang_Word x1 -> SOME (a1,x1) | _99
             -> NONE))`;;

let fix_clock_def = cake_define_list
  [`data_to_word_memoryProof_fix_clock ck (l:num) NONE = NONE`;
   `data_to_word_memoryProof_fix_clock ck (l:num) (SOME
  (y,(l1:num),(ck1:num))) =
    (let new_ck = (if ck < ck1 then ck else ck1) in let
        new_l = (if l < l1 then l else l1) in SOME
          (y,new_l,new_ck))`];;
hol4_overload "fix_clock" "data_to_word_memoryProof_fix_clock";;

let data_to_word_memoryProof_fix_clock_IMP =
  cake_theorem "fix_clock_IMP[local]"
  (fun () ->
    `!ck l x. fix_clock ck l x = SOME (w,l1,ck1) ==> ck1 <= ck /\ l1
  <= l`)
  CHEAT_TAC;;

let word_is_clos_def = cake_define
  `word_is_clos c h <=>
     (h && (tag_mask c || (n2w 2))) = n2w (16 * closure_tag + 2) \/
     (h && (tag_mask c || (n2w 2))) = n2w (16 * partial_app_tag +
       2)`;;

(* l  corresponds to the functional big-step semantics clock.
      Used to show that equality comparisons respect the
      MustTerminate limit.
   ck is an upper bound on the number of stack frames
      allocated by an equality comparison.
  *)
(* HOL4 data_to_word_memoryProofScript.sml:14020-14025: the tactic
   that proves the termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let word_eq_def = cake_define_try_tac (fun () ->
  `MEASURE (\x. match x with INL (c,st,dm,m,l1,ck1,w1,w2) -> l1 | INR
  (c,st,dm,m,l1,ck1,w,a1,a2) -> l1)`)
  CHEAT_TAC
  `(word_eq c st dm m l ck w1 (w2:'a word) =
      (if w1 = w2 then SOME (((n2w 1):'a word),l,ck) else
      if ~(word_bit 0 w1 /\ word_bit 0 w2) then SOME ((n2w 0),l,ck)
        else
        match (word_header c st w1 dm m,word_header c st w2 dm m)
          with (SOME (a1,h1),SOME (a2,h2)) ->
            (if (h1 && (n2w 0b1100)) = (n2w 0) then
              if word_is_clos c h1 then SOME ((n2w 1),l,ck) else
              if ~(h1 = h2) then SOME ((n2w 0),l,ck) else
              if l = 0 then NONE else
                word_eq_list c st dm m (l - 1) ck (decode_length c
                  h1)
                  (a1 + bytes_in_word) (a2 + bytes_in_word) else
            if ~(h1 = h2) then SOME ((n2w 0),l,ck) else
            if ~(word_bit 2 h1) then SOME ((n2w 0),l,ck) else
            if ~(word_bit 3 h1) /\ word_bit 4 h1 then
              SOME ((n2w 0),l,ck) else
             (if l <= w2n (decode_length c h1) then NONE else
              match word_cmp_loop (decode_length c h1)
                (a1 + bytes_in_word * (decode_length c h1))
                (a2 + bytes_in_word * (decode_length c h1)) dm m with
                  NONE -> NONE | SOME res -> SOME (res,l - 1 - w2n
                  (decode_length c h1),ck))) | _100 -> NONE)) /\
   (word_eq_list c st dm m l ck w a1 a2 =
      (if w = ((n2w 0):'a word) then SOME ((n2w 1),l,ck) else
      if ~(a1 IN dm) \/ ~(a2 IN dm) \/ (l = 0) \/ (ck = 0) then NONE
        else
        match (m a1,m a2) with (wordLang_Word w1,wordLang_Word w2) ->
         (match fix_clock (ck - 1) (l - 1) (word_eq c st dm m (l - 1)
           (ck - 1) w1 w2) with NONE -> NONE | SOME (x,l,ck') -> (if ~(x
           = (n2w 1)) then SOME (x,l,ck) else
                             if l = 0 then NONE else
                              word_eq_list c st dm m (l - 1) ck (w -
                                (n2w 1))
                              (a1 + bytes_in_word) (a2 +
                                bytes_in_word))) | _101 -> NONE))`;;

(* HOL4 data_to_word_memoryProofScript.sml:14027: ML code, not ported *)

let word_eq_LESS_EQ = cake_theorem "word_eq_LESS_EQ"
  (fun () ->
    `(!c st dm m l ck w1 (w2:'a word) x0 l1 ck1.
          word_eq c st dm m l ck w1 w2 = SOME (x0,l1,ck1) ==> l1 <=
            l /\ ck1 <= ck) /\
       (!c st dm m l ck w a1 (a2:'a word) x0 l1 ck1.
          word_eq_list c st dm m l ck w a1 a2 = SOME (x0,l1,ck1)
            ==> l1 <= l /\ ck1 <= ck)`)
  CHEAT_TAC;;

let fix_clock_word_eq = cake_theorem "fix_clock_word_eq[local]"
  (fun () ->
    `fix_clock ck l (word_eq c st dm m l ck w1 w2) = word_eq c st dm m
  l ck w1 w2`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:14055-14056: a theorem
   that HOL4 states as the value of an ML expression: word_eq_def *)

(* HOL4 data_to_word_memoryProofScript.sml:14058-14059: a theorem
   that HOL4 states as the value of an ML expression: word_eq_ind *)

let bit_pattern_1100 = cake_theorem "bit_pattern_1100[simp]"
  (fun () ->
    `good_dimindex (:'a) ==>
      (((n2w 0b1100) && x1) = (n2w 0) <=> ~(word_bit 2 x1) /\
        ~(word_bit 3 (x1:'a word)))`)
  CHEAT_TAC;;

let word_eq_add_clock = cake_theorem "word_eq_add_clock"
  (fun () ->
    `(!c st dm m l ck (a1:'a word) a2 res l' ck1 n.
     word_eq c st dm m l ck a1 a2 = SOME (res,l',ck1) ==>
     (word_eq c st dm m l (ck + n) a1 a2 = SOME (res,l',ck1 + n)))
       /\
     (!c st dm m l ck w (a1:'a word) a2 res l' ck1 n.
     word_eq_list c st dm m l ck w a1 a2 = SOME (res,l',ck1) ==>
     word_eq_list c st dm m l (ck + n) w a1 a2 = SOME (res,l',ck1
       + n))`)
  CHEAT_TAC;;

let word_eq_max_clock = cake_theorem "word_eq_max_clock"
  (fun () ->
    `(!c st dm m l ck (a1:'a word) a2 res l' ck1 n.
     word_eq c st dm m l ck a1 a2 = SOME (res,l',ck1) ==>
     (word_eq c st dm m l (MAX ck n) a1 a2 = SOME (res,l',ck1 + (n
       - ck)))) /\
     (!c st dm m l ck w (a1:'a word) a2 res l' ck1 n.
     word_eq_list c st dm m l ck w a1 a2 = SOME (res,l',ck1) ==>
     word_eq_list c st dm m l (MAX ck n) w a1 a2 = SOME
       (res,l',ck1 + (n - ck)))`)
  CHEAT_TAC;;

let word_eq_min_max_clock = cake_theorem "word_eq_min_max_clock"
  (fun () ->
    `(!x y. word_eq c st dm m l (MIN a b) a1 a2 = SOME (res,l',ck1) ==>
     (?ck1'. word_eq c st dm m l (MIN (MAX a x) (MAX b y)) a1 a2 =
       SOME (res,l',ck1'))) /\
     (!x y. word_eq_list c st dm m l (MIN a b) w a1 a2 = SOME
       (res,l',ck1) ==>
     (?ck1'. word_eq_list c st dm m l (MIN (MAX a x) (MAX b y)) w
       a1 a2 = SOME (res,l',ck1')))`)
  CHEAT_TAC;;

let memory_rel_isClos = cake_theorem "memory_rel_isClos[local]"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Block ts1 t1 v1,wordLang_Word
  (w1:'a word)) :: vars) /\
     word_bit 0 w1 /\
     get_real_addr c st w1 = SOME a' /\ m a' = wordLang_Word x' /\
       good_dimindex (:'a) ==>
     (isClos t1 v1 <=> word_is_clos c x')`)
  CHEAT_TAC;;

let eq_assum_def = cake_define_list
  [`eq_assum a m dm [] = T`;
   `eq_assum a m dm (v :: vs) <=>
         a IN dm /\ eq_assum (a + bytes_in_word) m dm vs`];;

let eq_explode_def = cake_define_list
  [`eq_explode a m dm [] = []`;
   `eq_explode a m dm (v :: vs) = (v,m a) :: eq_explode (a +
  bytes_in_word) m dm vs`];;

let eq_explode_APPEND = cake_theorem "eq_explode_APPEND[local]"
  (fun () ->
    `!xs ys a.
       eq_explode a m dm (xs ++ ys) =
       eq_explode a m dm xs ++
       eq_explode (a + n2w (LENGTH xs) * bytes_in_word) m dm ys`)
  CHEAT_TAC;;

let eq_assum_APPEND = cake_theorem "eq_assum_APPEND[local]"
  (fun () ->
    `!xs ys a.
       eq_assum a m dm (xs ++ ys) <=>
       eq_assum a m dm xs /\
       eq_assum (a + n2w (LENGTH xs) * bytes_in_word) m dm ys`)
  CHEAT_TAC;;

let memory_rel_Block_explode_lemma =
  cake_theorem "memory_rel_Block_explode_lemma[local]"
  (fun () ->
    `!n.
       memory_rel c be ts refs sp st m dm ((Block ts1 t1
         v1,wordLang_Word w1) :: vars) /\
       word_bit 0 w1 /\ get_real_addr c st w1 = SOME a /\
         good_dimindex (:'a) ==>
       memory_rel c be ts refs sp st m dm
         (eq_explode (a + bytes_in_word) m dm (TAKE n v1) ++ (
          (Block ts1 t1 v1,wordLang_Word (w1:'a word)) :: vars)) /\
       eq_assum (a + bytes_in_word) m dm (TAKE n v1)`)
  CHEAT_TAC;;

let memory_rel_Block_explode = cake_theorem "memory_rel_Block_explode"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Block ts1 t1 v1,wordLang_Word
  w1) :: vars) /\
      word_bit 0 w1 /\ get_real_addr c st w1 = SOME a /\
        good_dimindex (:'a) ==>
      memory_rel c be ts refs sp st m dm
        (eq_explode (a + (bytes_in_word:'a word)) m dm v1 ++ vars)
          /\
      eq_assum (a + bytes_in_word) m dm v1`)
  CHEAT_TAC;;

let memory_rel_Loc = cake_theorem "memory_rel_Loc"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((v1,Loc n k) :: vars) /\
     (!ptr. ~(v1 = RefPtr F ptr)) ==>
     v1 = CodePtr n`)
  CHEAT_TAC;;

let memory_rel_ByteArray_words_IMP =
  cake_theorem "memory_rel_ByteArray_words_IMP"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((RefPtr bl p,wordLang_Word
  (w:'a word)) :: vars) /\
     lookup p refs = SOME (ByteArray fl vals) /\
     good_dimindex (:'a) /\
     get_real_addr c st w = SOME a ==>
     (?x frame.
       m a = wordLang_Word x /\
       (
        misc_word_list (a + bytes_in_word)
          (MAP wordLang_Word (write_bytes vals (REPLICATE (w2n
            (decode_length c x)) (n2w 0)) be)) * frame) (fun2set (m,dm))
            /\
     w2n (decode_length c x) < dimword (:'a) /\
     w2n (decode_length c x) = LENGTH vals DIV (dimindex (:'a)
       DIV 8) + 1)`)
  CHEAT_TAC;;

let poly_inj_lemma = cake_theorem "poly_inj_lemma"
  (fun () ->
    `(a:num) < b /\ a' < b /\ a + b * c = a' + b * c' ==> a = a' /\ c
  = c'`)
  CHEAT_TAC;;

let mw2n_inj = cake_theorem "mw2n_inj"
  (fun () ->
    `!x y. LENGTH x = LENGTH y ==> (mw2n (x:('a word) list) = mw2n y
  <=> x = y)`)
  CHEAT_TAC;;

let write_bytes_inj = cake_theorem "write_bytes_inj"
  (fun () ->
    `good_dimindex (:'a) ==>
     (!ws bs1 bs2.
       LENGTH bs1 = LENGTH bs2 /\
       LENGTH bs1 <= LENGTH ws * (dimindex (:'a) DIV 8) /\
       LENGTH ws <= LENGTH bs1 DIV (dimindex (:'a) DIV 8) + 1 ==>
       (write_bytes bs1 (ws:('a word) list) be = write_bytes bs2
         ws be <=> bs1 = bs2))`)
  CHEAT_TAC;;

let MIN_ADD = cake_theorem "MIN_ADD[local]"
  (fun () ->
    `MIN a b + c = MIN (a + c) (b + c)`)
  CHEAT_TAC;;

let MIN_SUB = cake_theorem "MIN_SUB[local]"
  (fun () ->
    `MIN a b - c = MIN (a - c) (b - c)`)
  CHEAT_TAC;;

let MAX_ADD = cake_theorem "MAX_ADD[local]"
  (fun () ->
    `MAX a b + c = MAX (a + c) (b + c)`)
  CHEAT_TAC;;

let MAX_SUB = cake_theorem "MAX_SUB[local]"
  (fun () ->
    `MAX a b - c = MAX (a - c) (b - c)`)
  CHEAT_TAC;;

let do_eq_IFF_vb_eq_size = cake_theorem "do_eq_IFF_vb_eq_size"
  (fun () ->
    `(!(refs:('a bvlSem_ref) spt) v1 v2 b.
        do_eq refs v1 v2 = Eq_val b <=>
          (?n. vb_eq_size refs v1 v2 = SOME (n,b))) /\
     (!(refs:('a bvlSem_ref) spt) v1 v2 b.
        do_eq_list refs v1 v2 = Eq_val b <=>
          (?n. vb_eq_size_list refs v1 v2 = SOME (n,b)))`)
  CHEAT_TAC;;

let do_eq_IMP_vb_eq_size = cake_theorem "do_eq_IMP_vb_eq_size"
  (fun () ->
    `do_eq refs v1 v2 = Eq_val b ==>
       (?n. vb_eq_size refs v1 v2 = SOME (n,b))`)
  CHEAT_TAC;;

let vb_eq_size_IMP_do_eq = cake_theorem "vb_eq_size_IMP_do_eq"
  (fun () ->
    `vb_eq_size refs v1 v2 = SOME (n,b) ==>
     do_eq refs v1 v2 = Eq_val b`)
  CHEAT_TAC;;

let memory_rel_ptr_vb_eq = cake_theorem "memory_rel_ptr_vb_eq"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((v1,x1) :: (v2,(x1:'a
  word_loc)) :: vars) /\
     vb_eq_size refs v1 v2 = SOME (n,b) /\
     good_dimindex (:'a) ==> b`)
  CHEAT_TAC;;

let word_eq_thm0 = cake_theorem "word_eq_thm0"
  (fun () ->
    `(!refs v1 v2 l ck b w1 w2 n.
          memory_rel c be ts refs sp st m dm
             ((v1,wordLang_Word w1) :: (v2,(wordLang_Word w2:'a
               word_loc)) :: vars) /\
          vb_eq_size refs v1 v2 = SOME (n,b) /\
          ck = MIN (vs_depth v1) (vs_depth v2) /\
          n * dimword (:'a) < l /\
          good_dimindex (:'a) ==>
          (?res l1 ck1. word_eq c st dm m l ck w1 w2 = SOME
            (res,l1,ck1) /\
                   (b <=> (res = (n2w 1))) /\
                   l <= l1 + n * dimword (:'a))) /\
       (!refs v1 v2 l ck b w1 w2 t1 t2 n.
          memory_rel c be ts refs sp st m dm
             (eq_explode w1 m dm v1 ++ eq_explode w2 m dm v2 ++
               vars) /\
          LENGTH v2 = LENGTH v1 /\ LENGTH v1 < dimword (:'a) /\
          eq_assum w1 m dm v1 /\ eq_assum w2 m dm v2 /\
          vb_eq_size_list refs v1 v2 = SOME (n,b) /\
          ck = MIN (vs_depth_list v1) (vs_depth_list v2) /\
          n * dimword (:'a) < l /\
          good_dimindex (:'a) ==>
          (?res l1 ck1. word_eq_list c st dm m l ck (n2w (LENGTH
            v1)) w1 w2 = SOME (res,l1,ck1) /\
                   (b <=> (res = (n2w 1))) /\
                   l <= l1 + n * dimword (:'a)))`)
  CHEAT_TAC;;

let word_eq_thm = cake_theorem "word_eq_thm"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
        ((v1,wordLang_Word w1) :: (v2,(wordLang_Word w2:'a
          word_loc)) :: vars) /\
      do_eq refs v1 v2 = Eq_val b /\ good_dimindex (:'a) ==>
      (?res l1 ck1.
         word_eq c st dm m (MustTerminate_limit (:'a) - 1)
           (MIN (vs_depth v1) (vs_depth v2)) w1 w2 = SOME
             (res,l1,ck1) /\
         (b <=> (res = (n2w 1))))`)
  CHEAT_TAC;;

let word_mem_eq_def = cake_define_list
  [`word_mem_eq a [] dm m = SOME T`;
   `word_mem_eq a (x :: xs) dm m =
         (if ~(a IN dm) then NONE else
         if ~(isWord (m a)) then NONE else
         if ~(m a = wordLang_Word x) then SOME F else
           word_mem_eq (a + bytes_in_word) xs dm m)`];;

let word_mem_eq_thm = cake_theorem "word_mem_eq_thm[local]"
  (fun () ->
    `!xs ys a ff.
      (misc_word_list a (MAP wordLang_Word xs) * ff) (fun2set
        (m,dm)) /\
      LENGTH xs = LENGTH ys ==>
      word_mem_eq a ys dm m = SOME (xs = ys)`)
  CHEAT_TAC;;

let bignum_words_def = cake_define
  `bignum_words c i =
     (let (sign,payload) = i2mw i in
       match encode_header c (if sign then 7 else 3) (LENGTH
         payload) with NONE -> NONE | SOME h -> SOME (h :: payload))`;;

let memory_rel_Number_const_test =
  cake_theorem "memory_rel_Number_const_test"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Number i,wordLang_Word (w:'a
  word)) :: vars) /\
      good_dimindex (:'a) ==>
      (if small_int (:'a) j then
        (Smallnum j = w <=> i = j) else
        match bignum_words c j with NONE -> ~(i = j) | SOME words
          ->
          (if ~(word_bit 0 w) then ~(i = j) else
            ?a. get_real_addr c st w = SOME a /\
                word_mem_eq a words dm m = SOME (i = j)))`)
  CHEAT_TAC;;

let memory_rel_Word64_const_test =
  cake_theorem "memory_rel_Word64_const_test"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Word64 i,v) :: vars) /\
     good_dimindex (:'a) ==>
       (?(w:'a word) a words h.
         v = wordLang_Word w /\ get_real_addr c st w = SOME a /\
         word_mem_eq (a + bytes_in_word) words dm m = SOME (i = j)
           /\
         encode_header c 3 (LENGTH words) = SOME (h:'a word) /\
         (if dimindex (:'a) < 64 then
           words = [(63 >< 32) j; (31 >< 0) j] else
           words = [(63 >< 0) j]))`)
  CHEAT_TAC;;

let or_seven_eq = cake_theorem "or_seven_eq[local]"
  (fun () ->
    `~((w << k) = (v << k)) /\ 2 < k ==> ~(((w << k) || (n2w 7)) = ((v
  << k) || (n2w 7)))`)
  CHEAT_TAC;;

let make_byte_header_eq = cake_theorem "make_byte_header_eq"
  (fun () ->
    `byte_len (:'a) m < 2 EXP data_to_word_config_len_size c /\
     byte_len (:'a) m < 2 EXP (dimindex (:'a) - 4) /\
     byte_len (:'a) n < 2 EXP data_to_word_config_len_size c /\
     byte_len (:'a) n < 2 EXP (dimindex (:'a) - 4) /\
     good_dimindex (:'a) /\
     2 < dimindex (:'a) - (if dimindex (:'a) = 32 then 2 else 3) -
       data_to_word_config_len_size c ==>
     (make_byte_header c T m = (make_byte_header c T n:'a word)
       <=> m = n)`)
  CHEAT_TAC;;

let memory_rel_String_const_test =
  cake_theorem "memory_rel_String_const_test"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((RefPtr bl i,v) :: vars) /\
     lookup i refs = SOME (ByteArray T other) /\
     good_dimindex (:'a) ==>
     (let t = implode (MAP (CHR o w2n) other) in
       (part_to_words c LN (closLang_Str s) ((n2w 0):'a word) =
         NONE ==> ~(s = t)) /\
       (!x res.
         part_to_words c LN (closLang_Str s) (n2w 0) = SOME (x,res)
           ==>
         (?(w:'a word) a.
           v = wordLang_Word w /\ get_real_addr c st w = SOME a /\
           word_mem_eq a (MAP (get_Word o SND) res) dm m = SOME
             (s = t))))`)
  CHEAT_TAC;;

let word_1_and_eq_0 = cake_theorem "word_1_and_eq_0[local]"
  (fun () ->
    `(((n2w 1) && w) = (n2w 0)) <=> ~(word_bit 0 w)`)
  CHEAT_TAC;;

let memory_rel_Number_single_mul =
  cake_theorem "memory_rel_Number_single_mul"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
        ((Number i1,wordLang_Word (w1:'a word)) :: (Number
          i2,wordLang_Word w2) :: vars) /\
      good_dimindex (:'a) ==>
        (let (lw,hw) = single_mul w1 (w2 >>> 1) (n2w 0) in
          (hw || ((w1 || w2) && (n2w 1))) = (n2w 0) ==>
          memory_rel c be ts refs sp st m dm ((Number (i1 *
            i2),wordLang_Word (lw >>> 1)) :: vars))`)
  CHEAT_TAC;;

let memory_rel_bounds_check = cake_theorem "memory_rel_bounds_check"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Number i1,wordLang_Word (w1:'a
  word)) :: vars) /\
      small_int (:'a) (&n) /\ good_dimindex (:'a) ==>
      (word_ror w1 2 <+ n2w n <=> (&0) <= i1 /\ i1 < &n) /\
      (word_ror w1 2 <=+ n2w n <=> (&0) <= i1 /\ i1 <= &n)`)
  CHEAT_TAC;;

let memory_rel_ByteArray_IMP_store =
  cake_theorem "memory_rel_ByteArray_IMP_store"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((RefPtr bl p,wordLang_Word
  (w:'a word)) :: vars) /\
      lookup p refs = SOME (ByteArray fl vals) /\ good_dimindex
        (:'a) /\
      get_real_addr c st w = SOME a /\ i < LENGTH vals ==>
      (?m1. mem_store_byte_aux m dm be (a + bytes_in_word + n2w i)
        b = SOME m1 /\
           memory_rel c be ts (insert p (ByteArray fl (LUPDATE b i
             vals)) refs) sp st m1 dm
             ((RefPtr bl p,wordLang_Word (w:'a word)) :: vars))`)
  CHEAT_TAC;;

(* copy forward *)

(* HOL4 data_to_word_memoryProofScript.sml:15324-15329: the tactic
   that proves the termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let word_copy_fwd_def = cake_define_try_tac (fun () ->
  `MEASURE (w2n o FST o SND)`)
  CHEAT_TAC
  `word_copy_fwd be' (n:'a word) a b (m:'a word->'a word_loc) dm =
     (if dimword (:'a) <= 4 then NONE else
     if n <+ (n2w 4) then
       if n <+ (n2w 2) then
         if n = (n2w 0) then SOME m else
           OPTION_BIND (mem_load_byte_aux m dm be' a)
                       (\w. mem_store_byte_aux m dm be' b w) else
         OPTION_BIND (mem_load_byte_aux m dm be' a) (\w1.
         OPTION_BIND (mem_load_byte_aux m dm be' (a + (n2w 1))) (\w2.
           if n = (n2w 2) then
             OPTION_BIND (mem_store_byte_aux m dm be' b w1) (\m.
             OPTION_BIND (mem_store_byte_aux m dm be' (b + (n2w 1))
               w2) (\m. SOME m)) else
             OPTION_BIND (mem_load_byte_aux m dm be' (a + (n2w 2)))
               (\w3.
             OPTION_BIND (mem_store_byte_aux m dm be' b w1) (\m.
             OPTION_BIND (mem_store_byte_aux m dm be' (b + (n2w 1))
               w2) (\m.
             OPTION_BIND (mem_store_byte_aux m dm be' (b + (n2w 2))
               w3) (\m. SOME m)))))) else
       OPTION_BIND (mem_load_byte_aux m dm be' a) (\w1.
       OPTION_BIND (mem_load_byte_aux m dm be' (a + (n2w 1))) (\w2.
       OPTION_BIND (mem_load_byte_aux m dm be' (a + (n2w 2))) (\w3.
       OPTION_BIND (mem_load_byte_aux m dm be' (a + (n2w 3))) (\w4.
       OPTION_BIND (mem_store_byte_aux m dm be' b w1) (\m.
       OPTION_BIND (mem_store_byte_aux m dm be' (b + (n2w 1)) w2)
         (\m.
       OPTION_BIND (mem_store_byte_aux m dm be' (b + (n2w 2)) w3)
         (\m.
       OPTION_BIND (mem_store_byte_aux m dm be' (b + (n2w 3)) w4)
         (\m.
         word_copy_fwd be' (n - (n2w 4)) (a + (n2w 4)) (b + (n2w
           4)) m dm)))))))))`;;

let list_copy_fwd_def = cake_define
  `list_copy_fwd n xp xs yp ys =
     (if xp + n <= LENGTH xs /\ yp + n <= LENGTH ys then
       if n = 0 then SOME ys else
       if n = 1 then SOME (LUPDATE (EL xp xs) yp ys) else
       if n = 2 then SOME ((LUPDATE (EL (xp + 1) xs) (yp + 1) o
                            LUPDATE (EL (xp + 0) xs) (yp + 0)) ys)
                              else
       if n = 3 then SOME ((LUPDATE (EL (xp + 2) xs) (yp + 2) o
                            LUPDATE (EL (xp + 1) xs) (yp + 1) o
                            LUPDATE (EL (xp + 0) xs) (yp + 0)) ys)
                              else
         list_copy_fwd (n - 4) (xp + 4) xs (yp + 4)
                          ((LUPDATE (EL (xp + 3) xs) (yp + 3) o
                            LUPDATE (EL (xp + 2) xs) (yp + 2) o
                            LUPDATE (EL (xp + 1) xs) (yp + 1) o
                            LUPDATE (EL (xp + 0) xs) (yp + 0)) ys)
                              else NONE)`;;

let list_copy_fwd_alias_def = cake_define
  `list_copy_fwd_alias n xp yp ys =
     (if xp + n <= LENGTH ys /\ yp + n <= LENGTH ys then
       if n = 0 then SOME ys else
       if n = 1 then SOME (LUPDATE (EL xp ys) yp ys) else
       if n = 2 then SOME ((LUPDATE (EL (xp + 1) ys) (yp + 1) o
                            LUPDATE (EL (xp + 0) ys) (yp + 0)) ys)
                              else
       if n = 3 then SOME ((LUPDATE (EL (xp + 2) ys) (yp + 2) o
                            LUPDATE (EL (xp + 1) ys) (yp + 1) o
                            LUPDATE (EL (xp + 0) ys) (yp + 0)) ys)
                              else
         list_copy_fwd_alias (n - 4) (xp + 4) (yp + 4)
                          ((LUPDATE (EL (xp + 3) ys) (yp + 3) o
                            LUPDATE (EL (xp + 2) ys) (yp + 2) o
                            LUPDATE (EL (xp + 1) ys) (yp + 1) o
                            LUPDATE (EL (xp + 0) ys) (yp + 0)) ys)
                              else NONE)`;;

let word_copy_fwd_thm = cake_theorem "word_copy_fwd_thm"
  (fun () ->
    `!n xp yp ys ys1 m.
        memory_rel c be ts (insert p2 (ByteArray fl_ys ys) refs)
          sp st m dm ((RefPtr bl1 p1,v1) :: (RefPtr bl2 p2,v2) ::
            vars) /\
        lookup p1 refs = SOME (ByteArray fl_xs xs) /\
        list_copy_fwd n xp xs yp ys = SOME ys1 /\
        good_dimindex (:'a) /\ n < dimword (:'a) /\ ~(p1 = p2) ==>
        (?w1 (w2:'a word) a1 a2 m1.
          v1 = wordLang_Word w1 /\ v2 = wordLang_Word w2 /\
          get_real_addr c st w1 = SOME a1 /\
          get_real_addr c st w2 = SOME a2 /\
          word_copy_fwd be (n2w n) (a1 + bytes_in_word + n2w xp)
            (a2 + bytes_in_word + n2w yp) m dm = SOME m1 /\
          memory_rel c be ts (insert p2 (ByteArray fl_ys ys1) refs)
            sp st m1 dm ((RefPtr bl1 p1,v1) :: (RefPtr bl2 p2,v2)
              :: vars))`)
  CHEAT_TAC;;

let word_copy_fwd_alias_thm = cake_theorem "word_copy_fwd_alias_thm"
  (fun () ->
    `!n xp yp ys ys1 m.
        memory_rel c be ts (insert p2 (ByteArray fl_ys ys) refs)
          sp st m dm ((RefPtr bl p2,v2) :: vars) /\
        list_copy_fwd_alias n xp yp ys = SOME ys1 /\
        good_dimindex (:'a) /\ n < dimword (:'a) ==>
        (?(w2:'a word) a2 m1.
          v2 = wordLang_Word w2 /\
          get_real_addr c st w2 = SOME a2 /\
          word_copy_fwd be (n2w n) (a2 + bytes_in_word + n2w xp)
            (a2 + bytes_in_word + n2w yp) m dm = SOME m1 /\
          memory_rel c be ts (insert p2 (ByteArray fl_ys ys1) refs)
            sp st m1 dm ((RefPtr bl p2,v2) :: vars))`)
  CHEAT_TAC;;

(* copy backward *)

(* HOL4 data_to_word_memoryProofScript.sml:15569-15574: the tactic
   that proves the termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let word_copy_bwd_def = cake_define_try_tac (fun () ->
  `MEASURE (w2n o FST o SND)`)
  CHEAT_TAC
  `word_copy_bwd be' (n:'a word) a b (m:'a word->'a word_loc) dm =
     (if dimword (:'a) <= 4 then NONE else
     if n <+ (n2w 4) then
       if n <+ (n2w 2) then
         if n = (n2w 0) then SOME m else
           OPTION_BIND (mem_load_byte_aux m dm be' a)
                       (\w. mem_store_byte_aux m dm be' b w) else
         OPTION_BIND (mem_load_byte_aux m dm be' a) (\w1.
         OPTION_BIND (mem_load_byte_aux m dm be' (a - (n2w 1))) (\w2.
           if n = (n2w 2) then
             OPTION_BIND (mem_store_byte_aux m dm be' b w1) (\m.
             OPTION_BIND (mem_store_byte_aux m dm be' (b - (n2w 1))
               w2) (\m. SOME m)) else
             OPTION_BIND (mem_load_byte_aux m dm be' (a - (n2w 2)))
               (\w3.
             OPTION_BIND (mem_store_byte_aux m dm be' b w1) (\m.
             OPTION_BIND (mem_store_byte_aux m dm be' (b - (n2w 1))
               w2) (\m.
             OPTION_BIND (mem_store_byte_aux m dm be' (b - (n2w 2))
               w3) (\m. SOME m)))))) else
       OPTION_BIND (mem_load_byte_aux m dm be' a) (\w1.
       OPTION_BIND (mem_load_byte_aux m dm be' (a - (n2w 1))) (\w2.
       OPTION_BIND (mem_load_byte_aux m dm be' (a - (n2w 2))) (\w3.
       OPTION_BIND (mem_load_byte_aux m dm be' (a - (n2w 3))) (\w4.
       OPTION_BIND (mem_store_byte_aux m dm be' b w1) (\m.
       OPTION_BIND (mem_store_byte_aux m dm be' (b - (n2w 1)) w2)
         (\m.
       OPTION_BIND (mem_store_byte_aux m dm be' (b - (n2w 2)) w3)
         (\m.
       OPTION_BIND (mem_store_byte_aux m dm be' (b - (n2w 3)) w4)
         (\m.
         word_copy_bwd be' (n - (n2w 4)) (a - (n2w 4)) (b - (n2w
           4)) m dm)))))))))`;;

let minus_def = cake_define
  `minus m n = m - (n:num)`;;

let list_copy_bwd_def = cake_define
  `list_copy_bwd (n:num) xp xs yp ys =
     (if n <= xp + 1 /\ xp < LENGTH xs /\ n <= yp + 1 /\ yp < LENGTH
       ys then
       if n = 0 then SOME ys else
       if n = 1 then SOME (LUPDATE (EL xp xs) yp ys) else
       if n = 2 then SOME ((LUPDATE (EL (minus xp 1) xs) (minus yp 1)
         o
                            LUPDATE (EL (minus xp 0) xs) (minus yp
                              0)) ys) else
       if n = 3 then SOME ((LUPDATE (EL (minus xp 2) xs) (minus yp 2)
         o
                            LUPDATE (EL (minus xp 1) xs) (minus yp 1)
                              o
                            LUPDATE (EL (minus xp 0) xs) (minus yp
                              0)) ys) else
         list_copy_bwd (n - 4) (minus xp 4) xs (minus yp 4)
                          ((LUPDATE (EL (minus xp 3) xs) (minus yp 3)
                            o
                            LUPDATE (EL (minus xp 2) xs) (minus yp 2)
                              o
                            LUPDATE (EL (minus xp 1) xs) (minus yp 1)
                              o
                            LUPDATE (EL (minus xp 0) xs) (minus yp
                              0)) ys) else NONE)`;;

(* HOL4 data_to_word_memoryProofScript.sml:15598: ML code, not ported *)

let list_copy_bwd_alias_def = cake_define
  `list_copy_bwd_alias n xp yp ys =
     (if n <= xp + 1 /\ xp < LENGTH ys /\ n <= yp + 1 /\ yp < LENGTH
       ys then
       if n = 0 then SOME ys else
       if n = 1 then SOME (LUPDATE (EL xp ys) yp ys) else
       if n = 2 then SOME ((LUPDATE (EL (minus xp 1) ys) (minus yp 1)
         o
                            LUPDATE (EL (minus xp 0) ys) (minus yp
                              0)) ys) else
       if n = 3 then SOME ((LUPDATE (EL (minus xp 2) ys) (minus yp 2)
         o
                            LUPDATE (EL (minus xp 1) ys) (minus yp 1)
                              o
                            LUPDATE (EL (minus xp 0) ys) (minus yp
                              0)) ys) else
         list_copy_bwd_alias (n - 4) (minus xp 4) (minus yp 4)
                          ((LUPDATE (EL (minus xp 3) ys) (minus yp 3)
                            o
                            LUPDATE (EL (minus xp 2) ys) (minus yp 2)
                              o
                            LUPDATE (EL (minus xp 1) ys) (minus yp 1)
                              o
                            LUPDATE (EL (minus xp 0) ys) (minus yp
                              0)) ys) else NONE)`;;
(* HOL4 data_to_word_memoryProofScript.sml:15617-15618: ML code, not
   ported *)

let word_copy_bwd_thm = cake_theorem "word_copy_bwd_thm"
  (fun () ->
    `!n xp yp ys ys1 m.
        memory_rel c be ts (insert p2 (ByteArray fl_ys ys) refs)
          sp st m dm ((RefPtr bl1 p1,v1) :: (RefPtr bl2 p2,v2) ::
            vars) /\
        lookup p1 refs = SOME (ByteArray fl_xs xs) /\
        list_copy_bwd n xp xs yp ys = SOME ys1 /\
        good_dimindex (:'a) /\ n < dimword (:'a) /\ ~(p1 = p2) ==>
        (?w1 (w2:'a word) a1 a2 m1.
          v1 = wordLang_Word w1 /\ v2 = wordLang_Word w2 /\
          get_real_addr c st w1 = SOME a1 /\
          get_real_addr c st w2 = SOME a2 /\
          word_copy_bwd be (n2w n) (a1 + bytes_in_word + n2w xp)
            (a2 + bytes_in_word + n2w yp) m dm = SOME m1 /\
          memory_rel c be ts (insert p2 (ByteArray fl_ys ys1) refs)
            sp st m1 dm ((RefPtr bl1 p1,v1) :: (RefPtr bl2 p2,v2)
              :: vars))`)
  CHEAT_TAC;;

let word_copy_bwd_alias_thm = cake_theorem "word_copy_bwd_alias_thm"
  (fun () ->
    `!n xp yp ys ys1 m.
        memory_rel c be ts (insert p2 (ByteArray fl_ys ys) refs)
          sp st m dm ((RefPtr bl p2,v2) :: vars) /\
        list_copy_bwd_alias n xp yp ys = SOME ys1 /\
        good_dimindex (:'a) /\ n < dimword (:'a) ==>
        (?(w2:'a word) a2 m1.
          v2 = wordLang_Word w2 /\
          get_real_addr c st w2 = SOME a2 /\
          word_copy_bwd be (n2w n) (a2 + bytes_in_word + n2w xp)
            (a2 + bytes_in_word + n2w yp) m dm = SOME m1 /\
          memory_rel c be ts (insert p2 (ByteArray fl_ys ys1) refs)
            sp st m1 dm ((RefPtr bl p2,v2) :: vars))`)
  CHEAT_TAC;;

(* copy array *)

let list_copy_def = cake_define
  `list_copy n xp xs yp ys =
     (if yp <= xp \/ n + xp = 0 then list_copy_fwd n xp xs yp ys
       else list_copy_bwd n ((xp + n) - 1) xs ((yp + n) - 1) ys)`;;

let list_copy_alias_def = cake_define
  `list_copy_alias n xp yp ys =
     (if yp <= xp \/ n + xp = 0 then list_copy_fwd_alias n xp yp
       ys else list_copy_bwd_alias n ((xp + n) - 1) ((yp + n) - 1)
       ys)`;;

let list_copy_fwd_eq = cake_theorem "list_copy_fwd_eq[local]"
  (fun () ->
    `!n xp xs yp ys.
     xp + n <= LENGTH xs /\
     yp + n <= LENGTH ys ==>
     list_copy_fwd n xp xs yp ys =
       SOME
         (TAKE yp ys ++
         TAKE n (DROP xp xs) ++
         DROP (n + yp) ys)`)
  CHEAT_TAC;;

let list_copy_bwd_eq = cake_theorem "list_copy_bwd_eq[local]"
  (fun () ->
    `!n xp xs yp ys.
     n <= xp + 1 /\ xp < LENGTH xs /\
     n <= yp + 1 /\ yp < LENGTH ys ==>
     list_copy_bwd n xp xs yp ys =
       SOME
         (TAKE ((yp + 1) - n) ys ++
         TAKE n (DROP ((xp + 1) - n) xs) ++
         DROP (yp + 1) ys)`)
  CHEAT_TAC;;

let list_copy_thm = cake_theorem "list_copy_thm"
  (fun () ->
    `!xs ys xp yp n ys1.
        copy_array (xs,&xp) (&n) (SOME (ys,&yp)) = SOME ys1 ==>
        list_copy n xp xs yp ys = SOME ys1`)
  CHEAT_TAC;;

(* see more interesting theorem below *)

let list_copy_fwd_alias_eq =
  cake_theorem "list_copy_fwd_alias_eq[local]"
  (fun () ->
    `!n xp yp ys.
     yp <= xp /\
     xp + n <= LENGTH ys /\
     yp + n <= LENGTH ys ==>
     list_copy_fwd_alias n xp yp ys =
       SOME
         (TAKE yp ys ++
         TAKE n (DROP xp ys) ++
         DROP (n + yp) ys)`)
  CHEAT_TAC;;

let list_copy_bwd_alias_eq =
  cake_theorem "list_copy_bwd_alias_eq[local]"
  (fun () ->
    `!n xp yp ys.
     xp <= yp /\
     n <= xp + 1 /\ xp < LENGTH ys /\
     n <= yp + 1 /\ yp < LENGTH ys ==>
     list_copy_bwd_alias n xp yp ys =
       SOME
         (TAKE ((yp + 1) - n) ys ++
         TAKE n (DROP ((xp + 1) - n) ys) ++
         DROP (yp + 1) ys)`)
  CHEAT_TAC;;

let list_copy_alias_thm = cake_theorem "list_copy_alias_thm"
  (fun () ->
    `!ys xp yp n ys1.
        copy_array (ys,&xp) (&n) (SOME (ys,&yp)) = SOME ys1 ==>
        list_copy_alias n xp yp ys = SOME ys1`)
  CHEAT_TAC;;

let copy_array_NONE_IMP = cake_theorem "copy_array_NONE_IMP"
  (fun () ->
    `!xs ys xp n.
        copy_array (xs,&xp) (&n) NONE = SOME ys ==>
        list_copy_fwd n xp xs 0 (REPLICATE n (n2w 0)) = SOME ys`)
  CHEAT_TAC;;

(*

val xs = EVAL ``GENLIST I 20`` |> concl |> rand

fun cross [] xs = []
  | cross (y::ys) xs = map (fn x => (y,x)) xs @ cross ys xs

val nums = xs |> listSyntax.dest_list |> fst

val inputs = cross nums (cross nums nums)

fun test (n1,(n2,n3)) =
  (ISPEC xs list_copy_alias_thm
   |> Q.SPECL [`1`,`4`,`18`] |> SPEC_ALL
   |> CONV_RULE (RATOR_CONV EVAL THENC RAND_CONV EVAL)
   |> GEN_ALL |> SIMP_RULE std_ss [] |> concl) = T

val (n1,(n2,n3)) = first (not o test) inputs

*)

let word_copy_array_def = cake_define
  `word_copy_array be' n a a1 b b1 (m:'a word->'a word_loc) dm =
     (if b1 <=+ a1 then
       word_copy_fwd be' n (a + a1) (b + b1) m dm else
       word_copy_bwd be' n ((a + a1 + n) - (n2w 1)) ((b + b1 + n)
         - (n2w 1)) m dm)`;;

let word_copy_bwd_0 = cake_theorem "word_copy_bwd_0[local]"
  (fun () ->
    `good_dimindex (:'a) ==>
     word_copy_bwd be ((n2w 0):'a word) a1 a2 m dm = SOME m`)
  CHEAT_TAC;;

let word_copy_array_thm = cake_theorem "word_copy_array_thm"
  (fun () ->
    `!n xp yp xs ys ys1 m.
        memory_rel c be ts refs sp st m dm ((RefPtr bl1 p1,v1) ::
          (RefPtr bl2 p2,v2) :: vars) /\
        lookup p1 refs = SOME (ByteArray fl_xs xs) /\
        lookup p2 refs = SOME (ByteArray fl_ys ys) /\
        copy_array (xs,&xp) (&n) (SOME (ys,&yp)) = SOME ys1 /\
        good_dimindex (:'a) /\ ~(p1 = p2) ==>
        (?w1 (w2:'a word) a1 a2 m1.
          v1 = wordLang_Word w1 /\ v2 = wordLang_Word w2 /\
          get_real_addr c st w1 = SOME a1 /\
          get_real_addr c st w2 = SOME a2 /\
          word_copy_array be (n2w n) (a1 + bytes_in_word) (n2w xp)
            (a2 + bytes_in_word) (n2w yp) m dm = SOME m1 /\
          memory_rel c be ts (insert p2 (ByteArray fl_ys ys1) refs)
            sp st m1 dm ((RefPtr bl1 p1,v1) :: (RefPtr bl2 p2,v2)
              :: vars))`)
  CHEAT_TAC;;

let word_copy_array_alias_thm = cake_theorem "word_copy_array_alias_thm"
  (fun () ->
    `!n xp yp ys ys1 m.
        memory_rel c be ts refs sp st m dm ((RefPtr bl p2,v2) ::
          vars) /\
        lookup p2 refs = SOME (ByteArray fl_ys ys) /\
        copy_array (ys,&xp) (&n) (SOME (ys,&yp)) = SOME ys1 /\
        good_dimindex (:'a) ==>
        (?(w2:'a word) a2 m1.
          v2 = wordLang_Word w2 /\
          get_real_addr c st w2 = SOME a2 /\
          word_copy_array be (n2w n) (a2 + bytes_in_word) (n2w xp)
            (a2 + bytes_in_word) (n2w yp) m dm = SOME m1 /\
          memory_rel c be ts (insert p2 (ByteArray fl_ys ys1) refs)
            sp st m1 dm ((RefPtr bl p2,v2) :: vars))`)
  CHEAT_TAC;;

let word_of_byte_0 = cake_theorem "word_of_byte_0"
  (fun () ->
    `word_of_byte (n2w 0) = (n2w 0)`)
  CHEAT_TAC;;

let last_bytes_0 = cake_theorem "last_bytes_0"
  (fun () ->
    `!nb a. last_bytes nb (n2w 0) a (n2w 0) be = (n2w 0)`)
  CHEAT_TAC;;

let LUPDATE_REPLICATE = cake_theorem "LUPDATE_REPLICATE[simp]"
  (fun () ->
    `!n a. LUPDATE x a (REPLICATE n x) = REPLICATE n x`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:16179-16183: ML code, not
   ported *)

let memory_rel_copy_array_NONE =
  cake_theorem "memory_rel_copy_array_NONE"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((RefPtr bl p1,(v1:'a word_loc))
  :: vars) /\ ~(new IN (domain refs)) /\
      lookup p1 refs = SOME (ByteArray fl_xs xs) /\
      copy_array (xs,&xp) (&n) NONE = SOME ys /\
      byte_len (:'a) n < sp /\ byte_len (:'a) n < 2 EXP (dimindex
        (:'a) - 4) /\
      byte_len (:'a) n < 2 EXP data_to_word_config_len_size c /\
        good_dimindex (:'a) ==>
      (?free' curr a1 a2 m1 m2 w1 w2.
        v1 = wordLang_Word w1 /\
        get_real_addr c st w1 = SOME a1 /\
        make_ptr c (free' - curr) (n2w 0) (byte_len (:'a) n) =
          wordLang_Word w2 /\
        get_real_addr c st w2 = SOME a2 /\
        FLOOKUP st NextFree = SOME (wordLang_Word free') /\
        FLOOKUP st CurrHeap = SOME (wordLang_Word curr) /\
        data_to_word_memoryProof_store_list free'
          (wordLang_Word (make_byte_header c fl n) ::
               REPLICATE (byte_len (:'a) n) (wordLang_Word (n2w
                 0))) m dm = SOME m1 /\
        word_copy_fwd be (n2w n) (a1 + bytes_in_word + n2w xp)
          (a2 + bytes_in_word) m1 dm = SOME m2 /\
        memory_rel c be ts (insert new (ByteArray fl ys) refs)
         (sp - (byte_len (:'a) n + 1))
         (st |+ (NextFree,
                 wordLang_Word (free' + bytes_in_word * n2w
                   (byte_len (:'a) n + 1)))) m2 dm
         ((RefPtr T new,wordLang_Word w2) :: vars))`)
  CHEAT_TAC;;

let write_bytearray_isWord = cake_theorem "write_bytearray_isWord"
  (fun () ->
    `!ls a m x.
     isWord (m x) ==>
     isWord (write_bytearray a ls m dm be x)`)
  CHEAT_TAC;;

let write_bytearray_append = cake_theorem "write_bytearray_append"
  (fun () ->
    `!xs ys a m dm be'.
       (!i. i < LENGTH xs + LENGTH ys ==>
            (?b. mem_load_byte_aux m dm be' (a + n2w i) = SOME b))
              ==>
       write_bytearray a (xs ++ ys) m dm be' =
       write_bytearray a xs (write_bytearray (a + n2w (LENGTH
         xs)) ys m dm be') dm be'`)
  CHEAT_TAC;;

let memory_rel_write_bytearray_lemma =
  cake_theorem "memory_rel_write_bytearray_lemma[local]"
  (fun () ->
    `!rest bytes bytes0 m refs.
       memory_rel c be stm refs sp st m dm ((RefPtr b
         n,wordLang_Word (w:'a word)) :: vs) /\
       lookup n refs = SOME (ByteArray F (bytes0 ++ rest)) /\
         LENGTH bytes = LENGTH bytes0 /\
       get_real_simple_addr c st w = SOME a /\ good_dimindex (:'a)
         ==>
       memory_rel c be stm (insert n (ByteArray F (bytes ++ rest))
         refs) sp st
         (write_bytearray (a + bytes_in_word) bytes m dm be)
         dm ((RefPtr b n,wordLang_Word w) :: vs)`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:16298-16299: a theorem
   that HOL4 states as the value of an ML expression:
   memory_rel_write_bytearray *)

let memory_rel_space_max = cake_theorem "memory_rel_space_max"
  (fun () ->
    `memory_rel c be ts refs old_sp st m dm vars ==>
      (?next_free trig_gc sp.
        FLOOKUP st NextFree = SOME (wordLang_Word next_free) /\
        FLOOKUP st TriggerGC = SOME (wordLang_Word trig_gc) /\
        trig_gc - next_free = bytes_in_word * (n2w sp:'a word) /\
          old_sp <= sp /\
        memory_rel c be ts refs sp st m dm vars /\
        (good_dimindex (:'a) ==> (dimindex (:'a) DIV 8) * sp <
          dimword (:'a)))`)
  CHEAT_TAC;;

let get_lowerbits_ptrbits = cake_theorem "get_lowerbits_ptrbits"
  (fun () ->
    `get_lowerbits c (wordLang_Word (ptr_bits c x y)) = (ptr_bits c x
  y || (n2w 1))`)
  CHEAT_TAC;;

let append_writes_def = cake_define_list
  [`append_writes c ptr (hdr:'a word) [] l = ARB`;
   `append_writes c ptr (hdr:'a word) (x :: xs) l =
      wordLang_Word hdr :: x ::
        (if xs = [] then [l] else
          let ptr = ptr + ((n2w 3) << shift_length c) in
            wordLang_Word ptr ::
            append_writes c ptr hdr xs l)`];;

let append_writes_LENGTH = cake_theorem "append_writes_LENGTH"
  (fun () ->
    `!xs ptr. ~(xs = []) ==> LENGTH (append_writes c ptr hdr xs l) = 3
  * LENGTH xs`)
  CHEAT_TAC;;

let ptr_bits_or_1_add_1 = cake_theorem "ptr_bits_or_1_add_1"
  (fun () ->
    `ptr_bits c tag len || (n2w 1) = ptr_bits c tag len + (n2w 1)`)
  CHEAT_TAC;;

let all_ones_n2w = cake_theorem "all_ones_n2w"
  (fun () ->
    `all_ones (l + b) b = n2w (2 EXP l - 1) << b`)
  CHEAT_TAC;;

let ptr_bits_lemma = cake_theorem "ptr_bits_lemma"
  (fun () ->
    `(w << shift_length conf || ptr_bits conf 0 2 || (n2w 1)) =
     w << shift_length conf + ptr_bits conf 0 2 + (n2w 1)`)
  CHEAT_TAC;;

let encode_header_lemma = cake_theorem "encode_header_lemma"
  (fun () ->
    `1 < data_to_word_config_len_size c /\ data_to_word_config_len_size
  c + 5 < dimindex (:'a) /\
     good_dimindex (:'a) ==>
     decode_length c (make_header c (n2w 0) 2) = ((n2w 2):'a word)
       /\
     encode_header c 0 2 = SOME (make_header c ((n2w 0):'a word)
       2)`)
  CHEAT_TAC;;

let append_writes_list_to_BlockReps =
  cake_theorem "append_writes_list_to_BlockReps"
  (fun () ->
    `!xs ws x w offset init_ptr.
       LENGTH xs = LENGTH ws /\
       good_dimindex (:'a) /\
       1 < data_to_word_config_len_size c /\
         data_to_word_config_len_size c + 5 < dimindex (:'a) /\
       backend_common_word_shift (:'a) <= shift_length c /\
       LIST_REL (\v w. word_addr c v = w) (x :: xs) (w :: ws) /\
       wordLang_Word init_ptr = make_cons_ptr c (bytes_in_word *
         (n2w offset:'a word)) 0 2 ==>
       misc_word_list (curr + bytes_in_word * (n2w offset:'a word))
         (append_writes c init_ptr
            (make_header c (n2w 0) 2) (w :: ws) (word_addr c v)) =
       word_heap (curr + bytes_in_word * (n2w offset:'a word))
         (list_to_BlockReps c v offset (x :: xs)) c`)
  CHEAT_TAC;;

let bind_each_eq_tf = cake_theorem "bind_each_eq_tf"
  (fun () ->
    `!k tf ts n i x.
       (!t. t IN FDOM tf ==> t < ts) /\ x < ts ==> FAPPLY
         (bind_each tf ts n i k) x = FAPPLY tf x`)
  CHEAT_TAC;;

let bind_each_FDOM = cake_theorem "bind_each_FDOM"
  (fun () ->
    `!n tf ts k i.
      FDOM (bind_each tf ts k i n) = FDOM tf UNION {x | ts <= x
        /\ x < ts + n}`)
  CHEAT_TAC;;

let bind_each_eq_tf_FDOM = cake_theorem "bind_each_eq_tf_FDOM"
  (fun () ->
    `!k tf ts n i x.
       (!t. t IN FDOM tf ==> t < ts) /\ x < ts /\ x IN FDOM
         (bind_each tf ts n i k) ==> x IN FDOM tf`)
  CHEAT_TAC;;

let bind_each_eq_lt_FAPPLY = cake_theorem "bind_each_eq_lt_FAPPLY"
  (fun () ->
    `!n tf ts k i x.
      FAPPLY
      (bind_each tf ts k i n) x < k ==> FAPPLY (bind_each tf ts k
        i n) x = FAPPLY tf x`)
  CHEAT_TAC;;

let bind_each_eq_lt_FDOM = cake_theorem "bind_each_eq_lt_FDOM"
  (fun () ->
    `!n tf ts k i x.
      x IN FDOM (bind_each tf ts k i n) /\ FAPPLY (bind_each tf
        ts k i n) x < k ==> x IN FDOM tf`)
  CHEAT_TAC;;

let bind_each_eq_gt_FAPPLY = cake_theorem "bind_each_eq_gt_FAPPLY"
  (fun () ->
    `!n tf ts k i x.
      i * n + k < FAPPLY (bind_each tf ts k i n) x ==> FAPPLY
        (bind_each tf ts k i n) x = FAPPLY tf x`)
  CHEAT_TAC;;

let bind_each_eq_gt_FDOM = cake_theorem "bind_each_eq_gt_FDOM"
  (fun () ->
    `!n tf ts k i x.
      x IN FDOM (bind_each tf ts k i n) /\ i * n + k < FAPPLY
        (bind_each tf ts k i n) x ==> x IN FDOM tf`)
  CHEAT_TAC;;

let bind_each_eq_ge_FDOM = cake_theorem "bind_each_eq_ge_FDOM"
  (fun () ->
    `!n tf ts k i x.
      x IN FDOM (bind_each tf ts k i n) /\
      i * n + k <= FAPPLY (bind_each tf ts k i n) x /\ ~(i = 0)
        ==> x IN FDOM tf`)
  CHEAT_TAC;;

let bind_each_fdom_limit = cake_theorem "bind_each_fdom_limit"
  (fun () ->
    `!k tf ts n i x.
       (!t. t IN FDOM tf ==> t < ts) /\ ts + k < x ==> ~(x IN
         FDOM (bind_each tf ts n i k))`)
  CHEAT_TAC;;

let bind_each_FUPDATE = cake_theorem "bind_each_FUPDATE"
  (fun () ->
    `!n i tf ts1 ts2 k1 k2.
      ts1 < ts2 /\ k1 < k2 ==> bind_each (tf |+ (ts1,k1)) ts2 k2
        i n = bind_each tf ts2 k2 i n |+ (ts1,k1)`)
  CHEAT_TAC;;

let bind_each_MINUS = cake_theorem "bind_each_MINUS"
  (fun () ->
    `!n tf ts x k1 k2 i.
      (!t. t IN FDOM tf ==> t < ts) /\
      x IN {x | ts <= x /\ x < ts + n} /\ k2 <= k1 ==> FAPPLY
        (bind_each tf ts k1 i n) x - k2 = FAPPLY (bind_each tf ts (k1
        - k2) i n) x`)
  CHEAT_TAC;;

let data_to_word_memoryProof_isSomeDataElement_heap_lookup =
  cake_theorem "isSomeDataElement_heap_lookup[allow_rebind]"
  (fun () ->
    `!n a sp b.
      isSomeDataElement (heap_lookup n (a ++ [Unused sp] ++ b))
        ==> n < heap_length a \/ el_length (Unused sp) + heap_length a
        <= n`)
  CHEAT_TAC;;

let isSomeDataElement_heap_lookup_eq =
  cake_theorem "isSomeDataElement_heap_lookup_eq"
  (fun () ->
    `!ls n p k1 k2 conf.
      isSomeDataElement (heap_lookup n
        ((list_to_BlockReps conf p k2 ls):(('a
          word_loc,data_to_word_memoryProof_tag#'b list)heap_element)
          list)) ==> isSomeDataElement (heap_lookup n
        ((list_to_BlockReps conf p k1 ls):(('a
          word_loc,data_to_word_memoryProof_tag#'b list)heap_element)
          list))`)
  CHEAT_TAC;;

let bind_each_isSomeDataElement =
  cake_theorem "bind_each_isSomeDataElement"
  (fun () ->
    `!l tf ts x p k conf.
      ~(l = []) /\
      x IN {x | ts <= x /\ x < ts + (LENGTH l)} /\ (!t. t IN FDOM
        tf ==> t < ts) ==> isSomeDataElement (heap_lookup ((FAPPLY
        (bind_each tf ts 0 3 (LENGTH l)) x))
                          (list_to_BlockReps conf p k l))`)
  CHEAT_TAC;;

let bind_each_eq_INJ = cake_theorem "bind_each_eq_INJ"
  (fun () ->
    `!n x y tf ts k i.
     FAPPLY
     (bind_each tf ts k i n) x = FAPPLY (bind_each tf ts k i n) y
       /\
     ~(i = 0) /\ x IN {x | ts <= x /\ x < ts + n} /\
     ~(x IN FDOM tf) /\ y IN {x | ts <= x /\ x < ts + n} /\ ~(y
       IN FDOM tf) ==> x = y`)
  CHEAT_TAC;;

let all_ts_list_to_v_SUBSET = cake_theorem "all_ts_list_to_v_SUBSET"
  (fun () ->
    `!xs ts (refs:(dataSem_v bvlSem_ref) spt) t.
      {x | ts <= x /\ x < ts + LENGTH xs} SUBSET all_ts refs
        [list_to_v ts t xs]`)
  CHEAT_TAC;;

let all_ts_SUBSET_list_to_v = cake_theorem "all_ts_SUBSET_list_to_v"
  (fun () ->
    `!refs t xs stack' ts.
       all_ts refs (t :: (xs ++ stack')) SUBSET
       all_ts refs (list_to_v ts t xs :: stack')`)
  CHEAT_TAC;;

let new_all_ts_SUBSET_list_to_v =
  cake_theorem "new_all_ts_SUBSET_list_to_v"
  (fun () ->
    `!refs t xs stack' ts.
       {x | ts <= x /\ x < ts + LENGTH xs} SUBSET
       all_ts refs (list_to_v ts t xs :: stack')`)
  CHEAT_TAC;;

let FDOM_bind_each_lemma = cake_theorem "FDOM_bind_each_lemma"
  (fun () ->
    `!tf k ts h.
       FDOM tf SUBSET {n | n < ts} ==>
       FDOM (bind_each tf ts h n k) SUBSET {n | n < ts + k}`)
  CHEAT_TAC;;

let v_all_vs_list_to_v1 = cake_theorem "v_all_vs_list_to_v1"
  (fun () ->
    `!xs stack' ts t t1 a1 xs1.
       t1 < ts /\
       MEM (Block t1 a1 xs1) (v_all_vs (list_to_v ts t xs ::
         stack')) ==>
         MEM (Block t1 a1 xs1) (v_all_vs (t :: (xs ++ stack')))`)
  CHEAT_TAC;;

let blocks_unique_GT_ts = cake_theorem "blocks_unique_GT_ts"
  (fun () ->
    `blocks_unique ts (all_vs refs (t :: (xs ++ stack))) /\
     t' >= ts /\ ~(xs1 = []) ==> ~(Block t' a1 xs1 IN all_vs refs
       (t :: (xs ++ stack)))`)
  CHEAT_TAC;;

let Block_NOT_IN_all_vs = cake_theorem "Block_NOT_IN_all_vs"
  (fun () ->
    `!xs t t' a2 xs2 h stack' refs. ~(Block t' a2 xs2 IN all_vs refs (t
  :: h :: (xs ++ stack'))) ==>
       (!m. m > 0 ==> ~(MEM (Block t' a2 xs2) (v_all_vs
         [list_to_v (t' + m) t xs])))`)
  CHEAT_TAC;;

let v_all_vs_list_to_v2 = cake_theorem "v_all_vs_list_to_v2"
  (fun () ->
    `!xs t' a1 a2 xs1 xs2 ts t stack' refs.
     MEM (Block t' a1 xs1) (v_all_vs (list_to_v ts t xs :: stack'))
       /\ ~(xs1 = []) /\
     MEM (Block t' a2 xs2) (v_all_vs (list_to_v ts t xs :: stack'))
       /\ ~(xs2 = []) /\ ~(Block t' a1 xs1 IN all_vs refs (t :: (xs ++
       stack'))) /\ ~(Block t' a2 xs2 IN all_vs refs (t :: (xs ++
       stack'))) ==>
       a1 = a2 /\ xs1 = xs2 /\ t' < ts + LENGTH xs`)
  CHEAT_TAC;;

let blocks_unique_cons_multi = cake_theorem "blocks_unique_cons_multi"
  (fun () ->
    `blocks_unique ts (all_vs refs (t :: (xs ++ stack))) ==>
       blocks_unique (ts + LENGTH xs) (all_vs refs (list_to_v ts
         t xs :: stack))`)
  CHEAT_TAC;;

let cons_multi_thm = cake_theorem "cons_multi_thm"
  (fun () ->
    `abs_ml_inv conf ((t :: xs) ++ stack) refs
  (roots,heap,be,a,sp,sp1,gens) limit ts /\
     3 * LENGTH xs <= sp /\ ~(xs = []) ==>
        (?rt rs roots2 heap1 heap2.
          let Allocd = list_to_BlockReps conf rt a rs in
            (roots = (rt :: rs) ++ roots2) /\ (LENGTH rs = LENGTH
              xs) /\
            heap = heap1 ++ heap_expand (sp + sp1) ++ heap2 /\
            a = heap_length heap1 /\
            abs_ml_inv conf
              (list_to_v ts t xs :: stack) refs
              (gc_shared_Pointer a (wordLang_Word (ptr_bits conf
                cons_tag 2)) :: roots2,
               heap1 ++ Allocd ++ heap_expand ((sp + sp1) -
                 heap_length Allocd) ++ heap2,be,
               a + heap_length Allocd,sp - heap_length
                 Allocd,sp1,gens) limit (ts + LENGTH xs))`)
  CHEAT_TAC;;

let memory_rel_append = cake_theorem "memory_rel_append"
  (fun () ->
    `memory_rel c be ts refs sp st m1 dm
        (((v,h) :: ZIP in1 ws) ++ vars) /\
      (misc_word_list next_free
        (append_writes c init_ptr (make_header c (n2w 0) 2) ws h) *
          SEP_T)
        (fun2set (m1,dm)) /\
      1 < data_to_word_config_len_size c /\
      LENGTH in1 = LENGTH ws /\ ~(in1 = []) /\
      3 * LENGTH in1 <= sp /\ good_dimindex (:'a) /\
      wordLang_Word init_ptr = make_cons_ptr c (next_free - curr) 0
        2 /\
      FLOOKUP st CurrHeap = SOME (wordLang_Word curr) /\
      FLOOKUP st NextFree = SOME (wordLang_Word (next_free:'a
        word)) ==>
      memory_rel c be (ts + LENGTH in1) refs (sp - 3 * LENGTH in1)
         (st |+ (NextFree,
                 wordLang_Word (next_free + bytes_in_word * n2w (3
                   * LENGTH in1)))) m1 dm
         ((list_to_v ts v in1,wordLang_Word init_ptr) :: vars)`)
  CHEAT_TAC;;

(* --- ML lists cannot exceed heap size: --- *)

let walk_def = cake_define
  `data_to_word_memoryProof_walk conf heap ptr n =
     (if n = 0 then [] else if n = 1 then [ptr] else
       match some (\p.
         ?x y.
         heap_lookup ptr heap = SOME (BlockRep cons_tag [x; y]) /\
         y = gc_shared_Pointer p (wordLang_Word (ptr_bits conf
           cons_tag 2))) with
         NONE -> [] | SOME p ->
           ptr :: data_to_word_memoryProof_walk conf heap p (n -
             1))`;;
hol4_overload "walk" "data_to_word_memoryProof_walk";;

let v_inv_v_to_list_lemma = cake_theorem "v_inv_v_to_list_lemma"
  (fun () ->
    `v_inv c v refs (y,f,tf,heap) /\
     v_to_list v = SOME vs /\ ~(vs = []) ==>
      (?p ys. y = gc_shared_Pointer p (wordLang_Word (ptr_bits c
        cons_tag 2)) /\
                 heap_lookup p heap = SOME (BlockRep cons_tag
                   ys))`)
  CHEAT_TAC;;

let walk_LENGTH = cake_theorem "walk_LENGTH"
  (fun () ->
    `!vs ptr ps v ts.
       v_inv c v refs (gc_shared_Pointer ptr (wordLang_Word
         (ptr_bits c cons_tag 2)),f,tf,heap) /\
       v_to_list v = SOME vs /\ ~(vs = []) /\
       data_to_word_memoryProof_walk c heap ptr (LENGTH vs) = ps
         ==>
       LENGTH ps = LENGTH vs`)
  CHEAT_TAC;;

let BlockRep_heap_length = cake_theorem "BlockRep_heap_length[simp]"
  (fun () ->
    `heap_length [BlockRep tag [x; y]] = 3`)
  CHEAT_TAC;;

let ALL_DISTINCT_FILTER_LENGTH =
  cake_theorem "ALL_DISTINCT_FILTER_LENGTH"
  (fun () ->
    `ALL_DISTINCT xs ==>
     LENGTH (FILTER ((~) o P) xs) + LENGTH (FILTER P xs) = LENGTH
       xs`)
  CHEAT_TAC;;

let heap_length_Blocks = cake_theorem "heap_length_Blocks"
  (fun () ->
    `!ps (heap:(('a word_loc,data_to_word_memoryProof_tag#('a word_loc)
  list)heap_element) list).
       ALL_DISTINCT ps /\
       EVERY (\p. ?x y. heap_lookup p heap = SOME (BlockRep
         cons_tag [x; y])) ps ==>
       3 * LENGTH ps <= heap_length heap`)
  CHEAT_TAC;;

let walk_heap_lookup = cake_theorem "walk_heap_lookup"
  (fun () ->
    `!vs p ps v ts.
       v_inv c v refs
         (gc_shared_Pointer p (wordLang_Word (ptr_bits c cons_tag
           2)),f,tf,heap) /\
       v_to_list v = SOME vs /\ ~(vs = []) /\
       data_to_word_memoryProof_walk c heap p (LENGTH vs) = ps ==>
       EVERY (\p. ?x y. heap_lookup p heap = SOME (BlockRep
         cons_tag [x; y])) ps`)
  CHEAT_TAC;;

let walk_MEM = cake_theorem "walk_MEM"
  (fun () ->
    `v_inv c v refs (gc_shared_Pointer ptr (wordLang_Word (ptr_bits c
  cons_tag 2)),f,tf,heap) /\
     v_to_list v = SOME vs /\ ~(vs = []) ==>
     MEM ptr (data_to_word_memoryProof_walk c heap ptr (LENGTH
       vs))`)
  CHEAT_TAC;;

let walk_EL = cake_theorem "walk_EL"
  (fun () ->
    `!vs ptr ps v ts.
       v_inv c v refs (gc_shared_Pointer ptr (wordLang_Word
         (ptr_bits c cons_tag 2)),f,tf,heap) /\
       v_to_list v = SOME vs /\ ~(vs = []) /\
       data_to_word_memoryProof_walk c heap ptr (LENGTH vs) = ps
         ==>
       (!n. SUC n < LENGTH vs ==>
         (?x.
           heap_lookup (EL n ps) heap =
             SOME (BlockRep cons_tag [x;
               gc_shared_Pointer (EL (SUC n) ps) (wordLang_Word
                 (ptr_bits c cons_tag 2))])))`)
  CHEAT_TAC;;

let v_to_list_same_LENGTH = cake_theorem "v_to_list_same_LENGTH"
  (fun () ->
    `!xs x ys v1 v2 ts1 ts2.
       v_inv c v1 refs (x,f,tf,heap) /\
       v_inv c v2 refs (x,f,tf,heap) /\
       v_to_list v1 = SOME xs /\
       v_to_list v2 = SOME ys ==>
       LENGTH xs = LENGTH ys`)
  CHEAT_TAC;;

let block_drop_def = cake_define
  `block_drop x1 v =
      match (x1,v) with
        (0,v) -> SOME v
      | (SUC n,(Block ts tag [h; vl]:dataSem_v)) -> block_drop n vl
      | (_102,_103) -> NONE`;;

let v_to_list_DROP = cake_theorem "v_to_list_DROP"
  (fun () ->
    `!vs ptr ps k v ts.
     v_inv c v refs (gc_shared_Pointer ptr (wordLang_Word (ptr_bits
       c cons_tag 2)),f,tf,heap) /\
     v_to_list v = SOME vs /\ ~(vs = []) /\
     data_to_word_memoryProof_walk c heap ptr (LENGTH vs) = ps /\
     ALL_DISTINCT ps /\
     k < LENGTH vs ==>
     v_inv c (THE (block_drop k v)) refs
       (gc_shared_Pointer (EL k ps) (wordLang_Word (ptr_bits c
         cons_tag 2)),f,tf,heap)`)
  CHEAT_TAC;;

let block_drop_DROP = cake_theorem "block_drop_DROP"
  (fun () ->
    `!n v vs.
     v_to_list v = SOME vs /\ n < LENGTH vs ==> v_to_list (THE
       (block_drop n v)) = SOME (DROP n vs)`)
  CHEAT_TAC;;

let walk_ALL_DISTINCT = cake_theorem "walk_ALL_DISTINCT"
  (fun () ->
    `!vs ptr ps v ts.
       v_inv c v refs (gc_shared_Pointer ptr (wordLang_Word
         (ptr_bits c cons_tag 2)),f,tf,heap) /\
       v_to_list v = SOME vs /\ ~(vs = []) /\
       data_to_word_memoryProof_walk c heap ptr (LENGTH vs) = ps
         ==>
       ALL_DISTINCT ps`)
  CHEAT_TAC;;

let v_to_list_heap_length = cake_theorem "v_to_list_heap_length"
  (fun () ->
    `v_inv c v refs (x,f,tf,heap) /\
     v_to_list v = SOME vs /\ ~(vs = []) ==>
     3 * LENGTH vs <= heap_length heap`)
  CHEAT_TAC;;

(* ------------------------------------------------------------------------- *)

let memory_rel_list_limit = cake_theorem "memory_rel_list_limit"
  (fun () ->
    `memory_rel c be ts refs sp0 st m dm ((v,(w:'a word_loc)) :: vars)
  /\
     v_to_list v = SOME xs /\
     good_dimindex (:'a) ==>
     3 * (LENGTH xs + 1) * (dimindex (:'a) DIV 8) < dimword (:'a)`)
  CHEAT_TAC;;

let build_part_words_def = cake_define_list
  [`build_part_words c m (Int i:const_part) (offset:'a word) =
      (if small_int (:'a) i then SOME (wordLang_Word (Smallnum
        i),[]) else let (sign,ws) = i2mw i in
              match encode_header c (w2n (b2w sign << 2 || ((n2w
                3):'a word))) (LENGTH ws) with NONE -> NONE | SOME hd ->
                SOME (make_ptr c offset ((n2w 0):'a word) (LENGTH ws),
                              MAP wordLang_Word (hd :: ws)))`;
   `build_part_words c m (Con t ns:const_part) (offset:'a word) =
      (if NULL ns then
         if t < dimword (:'a) DIV 16 then SOME (wordLang_Word (n2w
           (16 * t + 2)),[]) else NONE else
         match encode_header c (4 * t) (LENGTH ns) with NONE -> NONE
           | SOME hd -> SOME (make_cons_ptr c offset t (LENGTH ns),
                            wordLang_Word hd :: (MAP m ns)))`;
   `build_part_words c m (W64 w:const_part) (offset:'a word) =
      (let ws = (if dimindex (:'a) < 64 then [((63 >< 32) w); ((31
        >< 0) w)] else [((63 >< 0) w):'a word]) in
         match encode_header c 3 (LENGTH ws) with NONE -> NONE |
           SOME hd -> SOME (make_ptr c offset ((n2w 0):'a word) (LENGTH
           ws),
                            MAP wordLang_Word (hd :: ws)))`;
   `build_part_words c m (closLang_Str s:const_part) (offset:'a word) =
      (let bytes = MAP (n2w o ORD) (explode s) in
       let n = LENGTH bytes in
       let hd = make_byte_header c T n in
       let ws = write_bytes bytes (REPLICATE (byte_len (:'a) n) (n2w
         0)) (be c) in
         if byte_len (:'a) n < 2 EXP (dimindex (:'a) - 4) /\
            byte_len (:'a) n < 2 EXP
              data_to_word_config_len_size c then SOME (make_ptr c
              offset ((n2w 0):'a word) (byte_len (:'a) n),MAP
              wordLang_Word (hd :: ws)) else NONE)`];;

let build_words_def = cake_define_list
  [`build_words c m i [] (off:'a word) = SOME (m (i - (1:num)),[])`;
   `build_words c m i (x :: parts') (off:'a word) =
      (match build_part_words c m x off with NONE -> NONE | SOME
        (w,xs) ->
        (match build_words c ((i =+ w) m) (i + 1) parts' (off +
          bytes_in_word * n2w (LENGTH xs)) with NONE -> NONE | SOME
          (r,ys) -> SOME (r,xs ++ ys)))`];;

let do_part_SOME_IMP_SOME = cake_theorem "do_part_SOME_IMP_SOME"
  (fun () ->
    `do_part map0 h refs (SOME ts) = (x,s1,ts1) ==> (?ts'. ts1 = SOME
  ts')`)
  CHEAT_TAC;;

let memory_rel_IMP_MAP_UPDATE = cake_theorem "memory_rel_IMP_MAP_UPDATE"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
             (((b,w) :: MAP (\k. (map0 k,map0' k)) ks) ++ vars) ==>
     memory_rel c be ts refs sp st m dm
             (MAP (\k. ((i =+ b) map0 k,((i =+ w) map0' k))) ks
               ++ vars)`)
  CHEAT_TAC;;

let data_to_word_memoryProof_ZIP_MAP_MAP =
  cake_theorem "ZIP_MAP_MAP[local]"
  (fun () ->
    `!xs. ZIP (MAP f xs) (MAP g xs) = MAP (\k. (f k,g k)) xs`)
  CHEAT_TAC;;

let LENGTH_n2mw_LE_num_size =
  cake_theorem "LENGTH_n2mw_LE_num_size[local]"
  (fun () ->
    `!n m. good_dimindex (:'a) /\ n <= m ==> SUC (LENGTH (n2mw n:('a
  word) list)) <= num_size m`)
  CHEAT_TAC;;

let least_notin_domain = cake_theorem "least_notin_domain"
  (fun () ->
    `~((LEAST (\ptr. ~(ptr IN domain refs))) IN domain (refs:'a spt))`)
  CHEAT_TAC;;

let memory_rel_do_build = cake_theorem "memory_rel_do_build"
  (fun () ->
    `!parts' i st free' curr sp map0 map0' refs ts refs1 v m v ws.
       do_build map0 i parts' refs (SOME ts) = (v,refs1,SOME ts1)
         /\
       build_words c map0' i parts' (free' - (curr:'a word)) = SOME
         (w,ws) /\
       SUM (MAP part_space_req parts') <= sp /\
       FLOOKUP st NextFree = SOME (wordLang_Word free') /\
       FLOOKUP st CurrHeap = SOME (wordLang_Word curr) /\
       (!ks. memory_rel c be ts refs sp st m dm (MAP (\k. (map0
         k,(map0' k))) ks ++ vars)) /\
       good_dimindex (:'a) ==>
       (?m1.
         let nf = free' + bytes_in_word * n2w (LENGTH ws) in
           memory_rel c be ts1 refs1 (sp - LENGTH ws)
             (st |+ (NextFree,wordLang_Word nf)) m1 dm ((v,w) ::
               vars) /\
           data_to_word_memoryProof_store_list free' ws m dm =
             SOME m1)`)
  CHEAT_TAC;;

let word_and_lsr_0 = cake_theorem "word_and_lsr_0"
  (fun () ->
    `(!i. k <= i /\ i < dimindex (:'a) ==> ~(FAPPLY w i)) ==> w && n
  << k = ((n2w 0):'a word)`)
  CHEAT_TAC;;

let byte_aligned_IMP_shift = cake_theorem "byte_aligned_IMP_shift"
  (fun () ->
    `byte_aligned (w:'a word) /\ good_dimindex (:'a) ==>
     (?v. w = v << backend_common_word_shift (:'a))`)
  CHEAT_TAC;;

let make_cons_ptr_add = cake_theorem "make_cons_ptr_add"
  (fun () ->
    `byte_aligned n /\ good_dimindex (:'a) /\ backend_common_word_shift
  (:'a) <= shift_length c ==>
     make_cons_ptr c n tag len =
     wordLang_Word (n << (shift_length c -
       backend_common_word_shift (:'a)) +
           (get_lowerbits c (wordLang_Word (ptr_bits c tag
             len)):'a word))`)
  CHEAT_TAC;;

let make_ptr_add = cake_theorem "make_ptr_add"
  (fun () ->
    `byte_aligned n /\ good_dimindex (:'a) /\ backend_common_word_shift
  (:'a) <= shift_length c ==>
     make_ptr c n tag len =
     wordLang_Word (n << (shift_length c -
       backend_common_word_shift (:'a)) + ((n2w 1):'a word))`)
  CHEAT_TAC;;

let word_cond_add_def = cake_define
  `word_cond_add c a x3 =
      match x3 with
        (F,x) -> (x:'a word_loc)
      | (T,wordLang_Word w) -> wordLang_Word (w + a << (shift_length
        c - backend_common_word_shift (:'a)))
      | (T,other) -> other`;;

let part_to_words_add = cake_theorem "part_to_words_add"
  (fun () ->
    `!part m off a w ws m1.
       byte_aligned off /\ byte_aligned a /\
       good_dimindex (:'a) /\ backend_common_word_shift (:'a) <=
         shift_length c ==>
       part_to_words c m part (off:'a word) = SOME (w,ws) /\
       (!i. SND (lookup_mem m1 i) = word_cond_add c a (lookup_mem m
         i)) ==>
       (?v vs. part_to_words c m1 part (off + (a:'a word)) = SOME
         (v,vs) /\
              MAP SND vs = MAP (word_cond_add c a) ws /\
              SND v = word_cond_add c a w)`)
  CHEAT_TAC;;

let byte_aligned_bytes_in_word =
  cake_theorem "byte_aligned_bytes_in_word"
  (fun () ->
    `good_dimindex (:'a) ==>
     byte_aligned (bytes_in_word:'a word)`)
  CHEAT_TAC;;

let byte_align_mult_bytes_in_word =
  cake_theorem "byte_align_mult_bytes_in_word"
  (fun () ->
    `good_dimindex (:'a) ==>
     byte_aligned (w * (bytes_in_word:'a word)) /\
     byte_aligned (bytes_in_word * (w:'a word))`)
  CHEAT_TAC;;

let parts_to_words_add = cake_theorem "parts_to_words_add"
  (fun () ->
    `!parts' m i off a w ws m1.
       parts_to_words c m i parts' (off:'a word) = SOME (w,ws) /\
       byte_aligned off /\ byte_aligned a /\
       good_dimindex (:'a) /\ backend_common_word_shift (:'a) <=
         shift_length c /\
       (!i. SND (lookup_mem m1 i) = word_cond_add c a (lookup_mem m
         i)) ==>
       (?v vs. parts_to_words c m1 i parts' (off + (a:'a word)) =
         SOME (v,vs) /\
              MAP SND vs = MAP (word_cond_add c a) ws /\
              SND v = word_cond_add c a w)`)
  CHEAT_TAC;;

let part_to_words_IMP_build_words =
  cake_theorem "part_to_words_IMP_build_words"
  (fun () ->
    `part_to_words c m p (off:'a word) = SOME (w,ws) /\ good_dimindex
  (:'a) /\
     byte_aligned off /\ backend_common_word_shift (:'a) <=
       shift_length c ==>
     build_part_words c (\i. SND (lookup_mem m i)) p off = SOME
       (SND w,MAP SND ws)`)
  CHEAT_TAC;;

let parts_to_words_IMP_build_words =
  cake_theorem "parts_to_words_IMP_build_words"
  (fun () ->
    `!c m i parts' (off:'a word) w ws.
       parts_to_words c m i parts' off = SOME (w,ws) /\
         good_dimindex (:'a) /\
       byte_aligned off /\ backend_common_word_shift (:'a) <=
         shift_length c ==>
       build_words c (\i. SND (lookup_mem m i)) i parts' off =
         SOME (SND w,MAP SND ws)`)
  CHEAT_TAC;;

let LESS_EQ_num_size = cake_theorem "LESS_EQ_num_size"
  (fun () ->
    `good_dimindex (:'a) ==>
     (!m n. n <= m ==> SUC (LENGTH (n2mw n:('a word) list)) <=
       num_size m)`)
  CHEAT_TAC;;

let part_to_words_LENGTH = cake_theorem "part_to_words_LENGTH"
  (fun () ->
    `part_to_words c m h a = SOME ((w:bool#'a word_loc),ws) /\
     good_dimindex (:'a) ==>
     LENGTH ws <= part_space_req h`)
  CHEAT_TAC;;

let const_parts_to_words_LENGTH =
  cake_theorem "const_parts_to_words_LENGTH"
  (fun () ->
    `const_parts_to_words c parts = SOME ((w:bool#'a word_loc),ws) /\
     good_dimindex (:'a) ==>
     LENGTH ws <= SUM (MAP part_space_req parts)`)
  CHEAT_TAC;;

let good_loc_def = cake_define
  `good_loc code x2 =
      match x2 with
        wordLang_Loc n m -> (m = 0 /\ n IN code)
      | _104 -> T`;;

let const_parts_to_words_good_loc =
  cake_theorem "const_parts_to_words_good_loc"
  (fun () ->
    `const_parts_to_words c parts = SOME ((y0,y1),y2) ==>
     good_loc s y1 /\ EVERY (good_loc s o SND) y2`)
  CHEAT_TAC;;

let memory_rel_do_build_const = cake_theorem "memory_rel_do_build_const"
  (fun () ->
    `do_build_const parts refs (SOME ts) = (v,refs1,SOME ts1) /\
     const_parts_to_words c parts = SOME (w,ws) /\
     memory_rel c be ts refs sp st m dm vars /\
     SUM (MAP part_space_req parts) <= sp /\
     FLOOKUP st NextFree = SOME (wordLang_Word free) /\
     FLOOKUP st CurrHeap = SOME (wordLang_Word curr) /\
     good_dimindex (:'a) ==>
     (?m1.
       let nf = free + bytes_in_word * n2w (LENGTH ws) in
       let adjust = word_cond_add c (free - (curr:'a word)) in
         memory_rel c be ts1 refs1 (sp - LENGTH ws)
           (st |+ (NextFree,wordLang_Word nf)) m1 dm ((v,adjust w)
             :: vars) /\
         data_to_word_memoryProof_store_list free (MAP adjust ws)
           m dm = SOME m1)`)
  CHEAT_TAC;;

let read_word_def = cake_define
  `read_word dm m a = (theWord (m a),(a IN dm /\ isWord (m a)))`;;

(* HOL4 data_to_word_memoryProofScript.sml:18378-18384: the tactic
   that proves the termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let word_xor_bytes_def = cake_define_try_tac (fun () ->
  `MEASURE (\(a1,a2,len,dm,m). w2n len)`)
  CHEAT_TAC
  `word_xor_bytes (a1:'a word) (a2:'a word) (len:'a word) dm m =
     (if len <+ (n2w 2) \/ ~(good_dimindex (:'a)) then
       if len = (n2w 0) then SOME m else
         let (w1a,c1) = read_word dm m a1 in
         let (w2a,c2) = read_word dm m a2 in
         let a = word_xor w1a w2a in
         let m = (a2 =+ wordLang_Word (a:'a word)) m in
           if c1 /\ c2 then SOME m else NONE else
       let (w1a,c1) = read_word dm m a1 in
       let (w2a,c2) = read_word dm m a2 in
       let (w1b,c3) = read_word dm m (a1 + bytes_in_word) in
       let (w2b,c4) = read_word dm m (a2 + bytes_in_word) in
       let a = word_xor w1a w2a in
       let b = word_xor w1b w2b in
       let m = ((a2 + bytes_in_word) =+ wordLang_Word b) ((a2 =+
         wordLang_Word a) m) in
         if c1 /\ c2 /\ c3 /\ c4 then
           word_xor_bytes (a1 + (n2w 2) * bytes_in_word) (a2 + (n2w
             2) * bytes_in_word)
             (len - (n2w 2)) dm m else NONE)`;;

let make_zeros_def = cake_define
  `make_zeros (vals:word8 list) =
     REPLICATE (LENGTH vals DIV (dimindex (:'a) DIV 8) + 1) ((n2w
       0):'a word)`;;

let xor_words_def = cake_define
  `xor_words xs ys =
      match (xs,ys) with
        ([],ys) -> SOME ys
      | (xs,[]) -> NONE
      | ((x :: xs),(y :: ys)) ->
     (match xor_words xs ys with NONE -> NONE | SOME rest -> SOME
       (word_xor (x:'a word) y :: rest))`;;

let word_xor_set_byte = cake_theorem "word_xor_set_byte"
  (fun () ->
    `word_xor (set_byte a h1 w1 be) (set_byte a h2 w2 be) =
     set_byte a (word_xor h1 h2) (word_xor w1 w2) be`)
  CHEAT_TAC;;

let xor_bytes_bytes_to_word =
  cake_theorem "xor_bytes_bytes_to_word[local]"
  (fun () ->
    `!k vals1 vals2 res_vals a.
       xor_bytes vals1 vals2 = SOME res_vals ==>
       bytes_to_word k a vals1 (n2w 0) be ??
       bytes_to_word k a vals2 (n2w 0) be =
       bytes_to_word k a res_vals (n2w 0) be`)
  CHEAT_TAC;;

let xor_bytes_length = cake_theorem "xor_bytes_length"
  (fun () ->
    `!xs ys zs.
       xor_bytes xs ys = SOME zs ==>
       LENGTH xs <= LENGTH zs /\ LENGTH zs = LENGTH ys`)
  CHEAT_TAC;;

let xor_bytes_drop = cake_theorem "xor_bytes_drop[local]"
  (fun () ->
    `!n xs ys zs.
       xor_bytes xs ys = SOME zs ==>
       xor_bytes (DROP n xs) (DROP n ys) = SOME (DROP n zs)`)
  CHEAT_TAC;;

let xor_bytes_xor_words = cake_theorem "xor_bytes_xor_words[local]"
  (fun () ->
    `!zs1 zs2 vals1 vals2 res_vals.
       xor_bytes vals1 vals2 = SOME res_vals /\ good_dimindex (:'a)
         /\
       EVERY (\w. w = (n2w 0)) zs1 /\ EVERY (\w. w = (n2w 0)) zs2
         /\
       LENGTH zs1 = LENGTH vals1 DIV (dimindex (:'a) DIV 8) + 1 /\
       LENGTH zs2 = LENGTH vals2 DIV (dimindex (:'a) DIV 8) + 1 ==>
       xor_words (write_bytes vals1 zs1 be)
                 (write_bytes vals2 zs2 be) =
       SOME (write_bytes res_vals zs2 be:('a word) list)`)
  CHEAT_TAC;;

let data_to_word_memoryProof_xor_bytes_xor_words =
  cake_theorem "xor_bytes_xor_words"
  (fun () ->
    `xor_bytes vals1 vals2 = SOME res_vals /\ good_dimindex (:'a) ==>
     xor_words (write_bytes vals1 (make_zeros vals1) be)
               (write_bytes vals2 (make_zeros vals2) be) =
     SOME (write_bytes res_vals (make_zeros vals2) be:('a word)
       list)`)
  CHEAT_TAC;;

let xor_words_word_list = cake_theorem "xor_words_word_list"
  (fun () ->
    `!vals1 vals2 res_vals a1 a2 be' frame m.
       xor_words vals1 vals2 = SOME res_vals /\
       good_dimindex (:'a) /\ LENGTH vals1 < dimword (:'a) /\
       (misc_word_list a1 (MAP wordLang_Word vals1) *
        misc_word_list a2 (MAP wordLang_Word vals2) *
        frame) (fun2set (m,dm)) ==>
       (?m1.
         (misc_word_list a1 (MAP wordLang_Word vals1) *
          misc_word_list a2 (MAP wordLang_Word res_vals) *
          frame) (fun2set (m1,(dm:'a word->bool))) /\
         word_xor_bytes a1 a2 (n2w (LENGTH vals1)) dm m = SOME
           m1)`)
  CHEAT_TAC;;

let xor_words_word_list_alias = cake_theorem "xor_words_word_list_alias"
  (fun () ->
    `!vals1 res_vals a1 be' frame m.
       xor_words vals1 vals1 = SOME res_vals /\
       good_dimindex (:'a) /\ LENGTH vals1 < dimword (:'a) /\
       (misc_word_list a1 (MAP wordLang_Word vals1) *
        frame) (fun2set (m,dm)) ==>
       (?m1.
         (misc_word_list a1 (MAP wordLang_Word res_vals) *
          frame) (fun2set (m1,(dm:'a word->bool))) /\
         word_xor_bytes a1 a1 (n2w (LENGTH vals1)) dm m = SOME
           m1)`)
  CHEAT_TAC;;

let xor_bytes_word_list = cake_theorem "xor_bytes_word_list"
  (fun () ->
    `!a1 a2 be' frame.
       xor_bytes vals1 vals2 = SOME res_vals /\
       good_dimindex (:'a) /\ LENGTH (make_zeros vals1:('a word)
         list) < dimword (:'a) /\
       (misc_word_list a1 (MAP wordLang_Word (write_bytes vals1
         (make_zeros vals1) be')) *
        misc_word_list a2 (MAP wordLang_Word (write_bytes vals2
          (make_zeros vals2) be')) *
        frame) (fun2set (m,dm)) ==>
       (?m1.
         (misc_word_list a1 (MAP wordLang_Word (write_bytes vals1
           (make_zeros vals1:('a word) list) be')) *
          misc_word_list a2 (MAP wordLang_Word (write_bytes
            res_vals (make_zeros vals2:('a word) list) be')) *
          frame) (fun2set (m1,(dm:'a word->bool))) /\
         word_xor_bytes a1 a2 (n2w (LENGTH (make_zeros vals1:('a
           word) list))) dm m = SOME m1)`)
  CHEAT_TAC;;

let xor_bytes_word_list_alias = cake_theorem "xor_bytes_word_list_alias"
  (fun () ->
    `!a1 be' frame.
       xor_bytes vals1 vals1 = SOME res_vals1 /\
       good_dimindex (:'a) /\ LENGTH (make_zeros vals1:('a word)
         list) < dimword (:'a) /\
       (misc_word_list a1 (MAP wordLang_Word (write_bytes vals1
         (make_zeros vals1) be')) *
        frame) (fun2set (m,dm)) ==>
       (?m1.
         (misc_word_list a1 (MAP wordLang_Word (write_bytes
           res_vals1 (make_zeros vals1:('a word) list) be')) *
          frame) (fun2set (m1,(dm:'a word->bool))) /\
         word_xor_bytes a1 a1 (n2w (LENGTH (make_zeros vals1:('a
           word) list))) dm m = SOME m1)`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:18637-18644: code that the
   source has in a comment *)

let el_length_Bytes = cake_theorem "el_length_Bytes"
  (fun () ->
    `el_length (Bytes be fl vals zeros) = LENGTH zeros + 1`)
  CHEAT_TAC;;

let blocks_unique_insert_ByteArray2 =
  cake_theorem "blocks_unique_insert_ByteArray2"
  (fun () ->
    `blocks_unique ts
       (all_vs refs (RefPtr bl1 p1 :: RefPtr bl2 p2 :: MAP FST
         vars)) ==>
       blocks_unique ts
         (all_vs (insert p2 (ByteArray fl2 res_vals) refs)
            (RefPtr bl1 p1 :: RefPtr bl2 p2 :: MAP FST vars))`)
  CHEAT_TAC;;

let memory_rel_xor_bytes = cake_theorem "memory_rel_xor_bytes"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
       ((RefPtr bl1 p1,(v1:'a word_loc)) :: (RefPtr bl2 p2,(v2:'a
         word_loc)) :: vars) /\
     lookup p1 refs = SOME (ByteArray fl1 vals1) /\
     lookup p2 refs = SOME (ByteArray fl2 vals2) /\
     xor_bytes vals1 vals2 = SOME res_vals /\
     good_dimindex (:'a) ==>
     (?w1 a1 w2 a2 x1 m1.
       v1 = wordLang_Word w1 /\
       v2 = wordLang_Word w2 /\
       get_real_addr c st w1 = SOME a1 /\
       get_real_addr c st w2 = SOME a2 /\
       m a1 = wordLang_Word x1 /\ a1 IN dm /\
       word_xor_bytes (a1 + bytes_in_word) (a2 + bytes_in_word)
                      (decode_length c x1) dm m = SOME m1 /\
       memory_rel c be ts (insert p2 (ByteArray fl2 res_vals) refs)
         sp st m1 dm
         ((RefPtr bl1 p1,(v1:'a word_loc)) :: (RefPtr bl2
           p2,(v2:'a word_loc)) :: vars))`)
  CHEAT_TAC;;

(* --------- str_cmp --------- *)

let word_str_cmp_loop_def = cake_define
  `word_str_cmp_loop (a1:'a word) (a2:'a word) r1 r2 (len:'a word) dm m
  be' ck =
     (if ck = 0 then NONE else
     if len = bytes_in_word then
       SOME (r1,r2) else
       match mem_load_byte_aux m dm be' a1 with NONE -> NONE | SOME
         b1 ->
       (match mem_load_byte_aux m dm be' a2 with NONE -> NONE | SOME
         b2 ->
         (if b1 = b2 then
           word_str_cmp_loop (a1 + (n2w 1)) (a2 + (n2w 1)) r1 r2 (len
             - (n2w 1)) dm m be' (ck - (1:num)) else
           SOME (w2w b1,w2w b2))))`;;

let word_str_cmp_def = cake_define
  `word_str_cmp b (a1:'a word) (a2:'a word) dm m be' c =
     (let k = (dimindex (:'a) - data_to_word_config_len_size c -
       backend_common_word_shift (:'a)) in
       if a1 IN dm /\ a2 IN dm /\ isWord (m a1) /\ isWord (m a2) then
         let l1 = (theWord (m a1) >>> k) in
         let l2 = (theWord (m a2) >>> k) in
           if b then
             (if ~(l1 = l2) then SOME (l1,l2) else
                word_str_cmp_loop (a1 + bytes_in_word) (a2 +
                  bytes_in_word) l1 l1 l1 dm m be' (dimword (:'a))) else
             (let l = n2w (MIN (w2n l1) (w2n l2)) in
                word_str_cmp_loop (a1 + bytes_in_word) (a2 +
                  bytes_in_word) l1 l2 l dm m be' (dimword (:'a)))
                  else NONE)`;;

let find_diff_def = cake_define_list
  [`find_diff [] [] r1 r2 = (r1,r2)`;
   `find_diff (x :: xs) (y :: ys) r1 r2 = (if x = y then find_diff
  xs ys r1 r2 else (w2w x,w2w y))`];;

let word_str_loop_thm = cake_theorem "word_str_loop_thm"
  (fun () ->
    `!k a1 a2 r1 r2 dm m be' d vals1 vals2.
       (!i. i < LENGTH vals1 ==> mem_load_byte_aux m dm be' (a1 +
         n2w i) = SOME (EL i vals1)) /\
       (!i. i < LENGTH vals2 ==> mem_load_byte_aux m dm be' (a2 +
         n2w i) = SOME (EL i vals2)) /\
       k <= LENGTH vals1 /\
       k <= LENGTH vals2 /\
       k < d /\ d <= dimword (:'a) ==>
       word_str_cmp_loop a1 a2 r1 r2 (n2w k + (bytes_in_word:'a
         word)) dm m be' d =
       SOME (find_diff (TAKE k vals1) (TAKE k vals2) r1 r2)`)
  CHEAT_TAC;;

let compoare_aux_append_xs =
  cake_theorem "compoare_aux_append_xs[local]"
  (fun () ->
    `!zs z xs ys r.
       LENGTH xs <= LENGTH ys ==>
       compare_aux (implode (z :: (zs ++ xs)))
                   (implode (z :: (zs ++ ys))) r (LENGTH zs + 1)
                     (STRLEN xs) =
       compare_aux (implode (zs ++ xs)) (implode (zs ++ ys)) r
         (LENGTH zs) (STRLEN xs)`)
  CHEAT_TAC;;

let compoare_aux_append_ys =
  cake_theorem "compoare_aux_append_ys[local]"
  (fun () ->
    `!zs z xs ys r.
       LENGTH ys <= LENGTH xs ==>
       compare_aux (implode (z :: (zs ++ xs)))
                   (implode (z :: (zs ++ ys))) r (LENGTH zs + 1)
                     (STRLEN ys) =
       compare_aux (implode (zs ++ xs)) (implode (zs ++ ys)) r
         (LENGTH zs) (STRLEN ys)`)
  CHEAT_TAC;;

let compare_same = cake_theorem "compare_same"
  (fun () ->
    `compare (implode (x :: xs)) (implode (x :: ys)) =
     compare (implode xs) (implode ys)`)
  CHEAT_TAC;;

let str_cmp_cons = cake_theorem "str_cmp_cons"
  (fun () ->
    `str_cmp b cmp (implode (x :: xs)) (implode (x :: ys)) =
     str_cmp b cmp (implode xs) (implode ys)`)
  CHEAT_TAC;;

let find_diff_str_cmp_thm1 = cake_theorem "find_diff_str_cmp_thm1"
  (fun () ->
    `!vals1 vals2.
       LENGTH (vals1:word8 list) = LENGTH (vals2:word8 list) /\
       good_dimindex (:'a) ==>
       (?(r1:'a word) (r2:'a word).
         find_diff vals1 vals2 (n2w l) (n2w l) = (r1,r2) /\
         (str_cmp T cmp (implode (MAP (CHR o w2n) vals1)) (implode
           (MAP (CHR o w2n) vals2)) <=>
          num_cmp cmp (w2n r1) (w2n r2)))`)
  CHEAT_TAC;;

let MIN_SUC_SUC = cake_theorem "MIN_SUC_SUC"
  (fun () ->
    `MIN (SUC m) (SUC n) = SUC (MIN m n)`)
  CHEAT_TAC;;

let find_diff_str_cmp_thm2 = cake_theorem "find_diff_str_cmp_thm2"
  (fun () ->
    `!k vals1 vals2 l1 l2.
       Abbrev (l1 = LENGTH vals1 + 2 EXP backend_common_word_shift
         (:'a)) /\
       Abbrev (l2 = LENGTH vals2 + 2 EXP backend_common_word_shift
         (:'a)) /\
       k + l1 < dimword (:'a) /\ k + l2 < dimword (:'a) /\
         good_dimindex (:'a) ==>
       (?(r1:'a word) (r2:'a word).
         find_diff (TAKE (MIN (LENGTH vals1) (LENGTH vals2))
           (vals1:word8 list))
                   (TAKE (MIN (LENGTH vals1) (LENGTH vals2)) vals2)
                   (n2w (k + l1))
                   (n2w (k + l2)) = (r1,r2) /\
         (str_cmp F cmp (implode (MAP (CHR o w2n) vals1))
                        (implode (MAP (CHR o w2n) vals2)) <=>
          num_cmp cmp (w2n r1) (w2n r2)))`)
  CHEAT_TAC;;

let memory_rel_str_cmp = cake_theorem "memory_rel_str_cmp"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
       ((RefPtr bl1 p1,(v1:'a word_loc)) :: (RefPtr bl2 p2,(v2:'a
         word_loc)) :: vars) /\
     lookup p1 refs = SOME (ByteArray fl1 vals1) /\
     lookup p2 refs = SOME (ByteArray fl2 vals2) /\
     good_dimindex (:'a) ==>
     (?w1 a1 w2 a2 x1 m1 r1 r2.
       v1 = wordLang_Word w1 /\
       v2 = wordLang_Word w2 /\
       get_real_addr c st w1 = SOME a1 /\
       get_real_addr c st w2 = SOME a2 /\
       word_str_cmp b a1 a2 dm m be c = SOME (r1,r2) /\
       str_cmp b cmp (implode (MAP (CHR o w2n) vals1))
                     (implode (MAP (CHR o w2n) vals2)) =
       semanticPrimitives_num_cmp cmp (w2n r1) (w2n r2))`)
  CHEAT_TAC;;

cake_hide [];;
