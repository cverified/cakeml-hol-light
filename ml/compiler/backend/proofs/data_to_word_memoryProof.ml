(* ======================================================== *)
(*  data_to_word_memoryProof: ported from HOL4's
    compiler/backend/proofs/data_to_word_memoryProofScript.sml  *)
(* ======================================================== *)

(*
  Part of the correctness proof for data_to_word
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/backend_passes.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/gc/copying_gc.ml";;
needs "compiler/backend/gc/gc_combined.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
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
needs "lib/byte.ml";;
needs "lib/multiword.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;
(* HOL4 ancestors outside the port: int_bitwise While *)


(* HOL4 ML code, not ported:
val shift_def = backend_commonTheory.word_shift_def;
val good_dimindex_def = miscTheory.good_dimindex_def;
*)

(* TODO: move? *)
(* HOL4 ML code, not ported:
val clean_tac = rpt var_eq_tac \\ rpt (qpat_x_assum `T` kall_tac)
fun rpt_drule th = old_drule (th |> GEN_ALL) \\ rpt (disch_then
  old_drule \\ fs [])
*)

(* HOL4 ML code, not ported:
val _ = augment_srw_ss[rewrites[LENGTH_REPLICATE]]
*)
(* HOL4 overload (expanded in the port):
     good_dimindex = misc$good_dimindex *)

(* HOL4 ML code, not ported:
val LESS_4 = DECIDE ``i < 4 <=> (i = 0) \/ (i = 1) \/ (i = 2) \/ (i =
  3n)``
val LESS_8 = DECIDE ``i < 8 <=> (i = 0) \/ (i = 1) \/ (i = 2) \/ (i =
  3n) \/
                                (i = 4) \/ (i = 5) \/ (i = 6) \/ (i =
                                  7)``
*)

(* MutBlock payloads have the shape l ++ [c] ++ r, which simplifiers
   split
   into three membership tests; this puts EL_MEM into the same split
     form *)

(* -- *)

let data_to_word_memoryProof_tag_INDUCT,
    data_to_word_memoryProof_tag_RECURSION =
  define_datatype
  "data_to_word_memoryProof_tag = BlockTag (num) | RefTag | BytesTag \
   (bool) (num) | ThunkTag (thunk_mode) | NumTag (bool) | Word64Tag";;

let BlockRep_def = cake_define
  `BlockRep tag xs = DataElement xs (LENGTH xs) (BlockTag tag,[])`;;

(* HOL4 type abbreviation (expanded in the port):
     ml_el = ('a word_loc, tag # ('a word_loc list)) heap_element *)
(* HOL4 type abbreviation (expanded in the port):
     ml_heap = 'a ml_el list *)

let bytes_def = cake_define
  `((Bytes is_bigendian cmp_by_contents (bs:word8 list) (ws:('a word)
  list)):('a word_loc,num#('a word_loc) list)heap_element) =
     (let ws = write_bytes bs ws is_bigendian in
       DataElement [] (LENGTH ws) (BytesTag cmp_by_contents
         (LENGTH bs),MAP Word ws))`;;

let bignum_def = cake_define
  `Bignum i =
     (let (sign,(payload:('a word) list)) = i2mw i in
       DataElement [] (LENGTH payload) (NumTag sign,MAP Word
         payload))`;;

let BlockNil_def = cake_define
  `BlockNil n = n2w n << 4 + (n2w 2)`;;

let Word64Rep_def = cake_define
  `Word64Rep (:'a) (w:word64) =
     (if dimindex (:'a) < 64 then
       DataElement [] 2 (Word64Tag,[Word ((63 >< 32) w); Word ((31 ><
         0) w)]) else
       DataElement [] 1 (Word64Tag,[Word (((63 >< 0) w):'a
         word)]))`;;

let ThunkBlock_def = cake_define
  `ThunkBlock ev x = DataElement [x] 1 (ThunkTag ev,[])`;;

(* v_inv conf v refs (x,f,tf,heap)
   v    : the dataSem value
   x    : the abstract gc value
   f    : reference values in dataLang to gc address (sort of like the
     content of the pointer)
   tf   : time-stamps in dataLang to gc addresses
   heap : is the gc abstract heap
 *)

(* The word annotation carried by a pointer to a ref. It is 0 for
   ordinary
   refs, but a MutBlock must carry exactly the annotation its finalised
     Block
   carries, since FinaliseCons is a no-op at word level. *)
let ref_ptr_annot_def = cake_define
  `ref_ptr_annot conf x2 =
      match x2 with
        (SOME (MutBlock tg fin l c r)) ->
     (Word (ptr_bits conf tg (LENGTH l + 1 + LENGTH r)):'a word_loc)
      | _1 -> Word (n2w 0)`;;

let v_inv_ck = cake_inductive
  `small_int (:'a) i ==>
     v_inv_ck ck conf (Number i) (refs:(dataSem_v bvlSem_ref)
       sptree_num_map)
                (Data (Word (Smallnum i)),f,tf,(heap:(('a
                  word_loc,num#('a word_loc) list)heap_element) list))
                  /\
   ~small_int (:'a) i /\
   heap_lookup ptr heap = SOME (Bignum i) ==>
     v_inv_ck ck conf (Number i) refs (Pointer ptr (Word (n2w
       0)),f,tf,(heap:(('a word_loc,num#('a word_loc) list)heap_element)
       list)) /\
   heap_lookup ptr heap = SOME (Word64Rep (:'a) w) ==>
     v_inv_ck ck conf (Word64 w) refs (Pointer ptr (Word (n2w
       0)),f,tf,(heap:(('a word_loc,num#('a word_loc) list)heap_element)
       list)) /\
   v_inv_ck ck conf (CodePtr n) refs (Data (Loc n 0),f,tf,(heap:(('a
     word_loc,num#('a word_loc) list)heap_element) list)) /\
   n IN FDOM f /\
   (!ev v. ~(lookup n refs = SOME (Thunk ev v))) /\
   (!tg fin l c r. lookup n refs = SOME (MutBlock tg fin l c r) ==>
     ~b) ==>
     v_inv_ck ck conf (RefPtr b n) refs
                (Pointer (FAPPLY f n) (ref_ptr_annot conf (lookup n
                  refs)),
                 f,tf,(heap:(('a word_loc,num#('a word_loc)
                   list)heap_element) list)) /\
   lookup n refs = SOME (Thunk ev v) /\
   (ev = Evaluated ==> dest_thunk v refs = NotThunk) /\
   n IN FDOM f /\
   heap_lookup (FAPPLY f n) heap = SOME (ThunkBlock ev x) /\
   (~(ck = (0:num)) ==> v_inv_ck (ck - 1) conf v refs (x,f,tf,heap))
     ==>
     v_inv_ck ck conf (RefPtr F n) refs
                (Pointer (FAPPLY f n) (Word (n2w 0)),f,tf,(heap:(('a
                  word_loc,num#('a word_loc) list)heap_element) list))
                  /\
   lookup n refs = SOME (Thunk Evaluated v) /\
   dest_thunk v refs = NotThunk /\
   (~(ck = 0) ==> v_inv_ck (ck - 1) conf v refs (x,f,tf,heap)) ==>
     v_inv_ck ck conf (RefPtr F n) refs (x,f,tf,(heap:(('a
       word_loc,num#('a word_loc) list)heap_element) list)) /\
   vs = [] /\
   n < dimword (:'a) DIV 16 /\
   ts = 0 ==>
     v_inv_ck ck conf (Block ts n vs) refs
                (Data (Word (BlockNil n)),f,tf,(heap:(('a
                  word_loc,num#('a word_loc) list)heap_element) list))
                  /\ ~(
   vs = []) /\
   (~(ck = 0) ==> EVERY2 (\v x. v_inv_ck (ck - 1) conf v refs
     (x,f,tf,heap)) vs xs) /\
   FLOOKUP tf ts = SOME ptr /\
   heap_lookup ptr heap = SOME (BlockRep n xs) ==>
     v_inv_ck ck conf (Block ts n vs) refs
                (Pointer ptr (Word (ptr_bits conf n (LENGTH xs))),
                 f,tf,(heap:(('a word_loc,num#('a word_loc)
                   list)heap_element) list))`;;

let v_inv_eq = cake_define
  `v_inv conf v refs (x,f,tf,heap) =
     (!ck. v_inv_ck ck conf v refs (x,f,tf,heap))`;;

(* a compare-by-pointer RefPtr never points at a thunk or a MutBlock, so
   its
   pointer annotation is always 0 *)

let _ = size_thms "v";;
(* HOL4 termination: \\ rpt strip_tac \\ Induct_on `vs` \\ srw_tac []
   [v_size_def] \\ res_tac \\ DECIDE_TAC *)
let get_refs_def = cake_define_wf
  `MEASURE (v_size)`
  `(get_refs (Number _2) = []) /\
   (get_refs (Word64 _3) = []) /\
   (get_refs (CodePtr _4) = []) /\
   (get_refs (RefPtr _5 p) = [p]) /\
   (get_refs (Block _6 _7 vs) = FLAT (MAP get_refs vs))`;;

let ref_edge_def = cake_define
  `ref_edge refs x res =
     (match lookup x refs with SOME (ValueArray ys) -> MEM res
       (get_refs (Block 0 ARB ys)) | SOME (Thunk _8 v) -> MEM res
       (get_refs (Block 0 ARB [v])) | SOME (MutBlock _9 _10 l c r) ->
       MEM res (get_refs (Block 0 ARB (l ++ [c] ++ r))) | _11 -> F)`;;

let reachable_refs_def = cake_define
  `reachable_refs roots refs t =
     (?x r. MEM x roots /\ MEM r (get_refs x) /\ RTC (ref_edge
       refs) r t)`;;

let RefBlock_def = cake_define
  `RefBlock xs = DataElement xs (LENGTH xs) (RefTag,[])`;;

let dest_evaluated_thunk_rel = cake_inductive
  `!x. dest_evaluated_thunk_rel (ThunkBlock Evaluated x) x`;;

let bc_ref_inv_def = cake_define
  `bc_ref_inv conf n refs (f,tf,heap,be) =
     (match (FLOOKUP f n,lookup n refs) with (SOME x,SOME (ValueArray
       ys)) ->
         (?zs. heap_lookup x heap = SOME (RefBlock zs) /\
               EVERY2 (\z y. v_inv conf y refs (z,f,tf,heap)) zs ys)
                 | (SOME x,SOME (ByteArray flag bs)) ->
         (let ws = LENGTH bs DIV (dimindex (:'ga) DIV 8) + 1 in
           (heap_lookup x heap = SOME (Bytes be flag bs (REPLICATE ws
             ((n2w 0):'a word))))) | (SOME x,SOME (Thunk ev v)) ->
         (?(z).
            heap_lookup x heap = SOME (ThunkBlock ev z) /\
            (ev = Evaluated ==> dest_thunk v refs = NotThunk) /\
            v_inv conf v refs (z,f,tf,heap)) | (SOME x,SOME (MutBlock
              tg fin l c r)) ->
         (!gs. ~(data_to_word_config_gc_kind conf = Generational gs))
           /\
         (~fin ==> ~(x IN IMAGE (FAPPLY tf) (FDOM tf))) /\
         (?zs. heap_lookup x heap = SOME (BlockRep tg zs) /\
               EVERY2 (\z y. v_inv conf y refs (z,f,tf,heap)) zs
                 (l ++ [c] ++ r)) | _12 -> F)`;;

(* TODO: MOVE *)
let _ = size_thms "v";;
(* HOL4 termination: \\ rpt strip_tac \\ Induct_on `xs` \\ srw_tac []
   [v_size_def] \\ res_tac \\ DECIDE_TAC *)
let v_all_ts_def = cake_define_wf
  `MEASURE (v_size)`
  `v_all_ts x1 =
      match x1 with
        (Block ts _13 xs) -> ts :: FLAT (MAP v_all_ts xs)
      | _14 -> []`;;

let find_ref_def = cake_define
  `find_ref x1 x =
      match x1 with
        (ValueArray l) -> MEM x l
      | (Thunk m v) -> (v = x)
      | (MutBlock tg fin l c r) -> MEM x (l ++ [c] ++ r)
      | _15 -> F`;;

(* TODO: MOVE *)
let all_ts_def = cake_define
  `all_ts refs stack =
     (let refs_v = {x | ?n r. sptree_lookup n refs = SOME r /\
       find_ref r x} in {ts | ?x. (x IN refs_v \/ MEM x stack) /\ MEM
       ts (v_all_ts x)})`;;

let be_ok_def = cake_define
  `be_ok b1 b2 <=> b1 = b2`;;

let v_all_vs_def = cake_define
  `v_all_vs x1 =
      match x1 with
        (Block ts tag l :: xs) -> (Block ts tag l :: v_all_vs l) ++
          v_all_vs xs
      | (x :: xs) -> x :: v_all_vs xs
      | [] -> []`;;

let all_vs_def = cake_define
  `all_vs refs stack =
     {v | ?(n:num) l. lookup n refs = SOME (ValueArray l) /\ MEM v
       (v_all_vs l)} UNION
     {v | ?n ev x. lookup n refs = SOME (Thunk ev x) /\ MEM v
       (v_all_vs [x])} UNION
     {v | ?n tg fin l c r. lookup n refs = SOME (MutBlock tg fin l c
       r) /\
                            MEM v (v_all_vs (l ++ [c] ++ r))} UNION
     {v | MEM v (v_all_vs stack)}`;;

let blocks_unique_def = cake_define
  `blocks_unique ts vs =
     (!t a1 xs1 a2 xs2.
       Block t a1 xs1 IN vs /\ ~(xs1 = []) /\
       Block t a2 xs2 IN vs /\ ~(xs2 = []) ==>
       a1 = a2 /\ xs1 = xs2 /\ t < ts)`;;

(* THIS IS IMPORTANT *)
let bc_stack_ref_inv_def = cake_define
  `bc_stack_ref_inv conf ts stack refs (roots,heap,be) =
     (?f tf.
       INJ (FAPPLY f) (FDOM f) {a | isSomeDataElement (heap_lookup a
         heap)} /\
       FDOM f SUBSET (domain refs) /\
       INJ (FAPPLY tf) (FDOM tf) {a | isSomeDataElement (heap_lookup
         a heap)} /\
       FDOM tf SUBSET (all_ts refs stack) /\
       FDOM tf SUBSET {n | n < ts} /\ be_ok (?_be conf) be /\
       blocks_unique ts (all_vs refs stack) /\
       EVERY2 (\v x. v_inv conf v refs (x,f,tf,heap)) stack roots /\
       (!n.
         reachable_refs stack refs n /\
         n IN FDOM f ==>
           bc_ref_inv conf n refs (f,tf,heap,be)))`;;

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
  `isRef x1 =
      match x1 with
        (DataElement ys l (tag,qs)) -> isMutTag tag
      | _16 -> F`;;

let gen_start_ok_def = cake_define
  `gen_start_ok heap refs_start gen_start =
     (?h1 h2.
       heap_split gen_start heap = SOME (h1,h2) /\
       (!xs l d p e.
         MEM (DataElement xs l d) h1 /\ MEM (Pointer p e) xs ==>
         p < gen_start \/ refs_start <= p))`;;

let gen_state_ok_def = cake_define
  `gen_state_ok a refs_start heap (GenState _17 starts) <=>
     EVERY (\s. s <= a) starts /\
     EVERY (gen_start_ok heap refs_start) starts`;;

let gc_kind_inv_def = cake_define
  `gc_kind_inv c a sp sp1 (gens:gen_state) heap <=>
     (match data_to_word_config_gc_kind c with None -> (sp1 = 0) |
       Simple -> (sp1 = 0) | Generational sizes ->
         gen_state_ok a (a + sp + sp1) heap gens /\
         (?h1 h2. (heap_split (a + sp + sp1) heap = SOME (h1,h2)) /\
                 EVERY (\x. ~isRef x) h1 /\ EVERY isRef h2))`;;

let abs_ml_inv_def = cake_define
  `abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts <=>
     roots_ok roots heap /\ heap_ok heap limit /\
     gc_kind_inv conf a sp sp1 gens heap /\
     unused_space_inv a (sp + sp1) heap /\
     bc_stack_ref_inv conf ts stack refs (roots,heap,be)`;;

(* --- *)

(* TODO: move/reorganise various things in this file *)

(* HOL4 ML code, not ported:
val EVERY2_LENGTH = LIST_REL_LENGTH
val EVERY2_IMP_LENGTH = EVERY2_LENGTH
*)

(* HOL4 ML code, not ported:
val EVERY2_IMP_APPEND = rich_listTheory.EVERY2_APPEND_suff
val IMP_EVERY2_APPEND = EVERY2_IMP_APPEND
*)

(* HOL4 ML code, not ported:
val EVERY2_EQ_EL = LIST_REL_EL_EQN
*)

(* HOL4 ML code, not ported:
val EVERY2_IMP_EL = METIS_PROVE[EVERY2_EQ_EL]
  ``!xs ys P. EVERY2 P xs ys ==> !n. n < LENGTH ys ==> P (EL n xs) (EL n
    ys)``
*)

(* Prove refinement is maintained past GC calls *)

(* HOL4 ML code, not ported:
val _ = augment_srw_ss [rewrites [LIST_REL_def]];
*)

let evaluated_thunk_ptr_def = cake_define
  `evaluated_thunk_ptr refs n <=> (?v. lookup n refs = SOME (Thunk
  Evaluated v))`;;

(* HOL4 ML code, not ported:
val v_ind =
  TypeBase.induction_of``:v``
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE(srw_ss())[]
  |> UNDISCH_ALL |> CONJUNCT1
  |> DISCH_ALL
*)

let gc_inline_rel = cake_inductive
  `[~(unchanged:)] gc_inline_rel inline h1 x x /\
     heap_lookup p h1 = SOME block /\
     inline block x ==>
       gc_inline_rel inline h1 (Pointer p u) x`;;

let gc_heap_inline_rel = cake_inductive
  `[~(unchanged:)] gc_heap_inline_rel inline h1 x x /\
     LIST_REL (gc_inline_rel inline h1) xs ys ==>
       gc_heap_inline_rel inline h1 (DataElement xs n d)
         (DataElement ys n d)`;;

let gc_inline_def = cake_define
  `gc_inline inline (r1,h1) (r2,h2) <=>
     LIST_REL (gc_inline_rel inline h1) r1 r2 /\
     LIST_REL (gc_heap_inline_rel inline h1) h1 h2`;;

let gc_related_roots_heap_def = cake_define
  `gc_related_roots_heap f (r1,h1) (r2,h2) <=>
     gc_related f h1 h2 /\
     r2 = ADDR_MAP ((FAPPLY) f) r1 /\
     (!ptr u. MEM (Pointer ptr u) r1 ==> ptr IN FDOM f)`;;

let gc_inline_related_def = cake_define
  `gc_inline_related inline f (r1,h1) (r2,h2) =
     (?ri hi. gc_inline inline (r1,h1) (ri,hi) /\
             gc_related_roots_heap f (ri,hi) (r2,h2))`;;

let all_reachable_from_roots_def = cake_define
  `all_reachable_from_roots roots heap <=>
     (!p xs l d.
        heap_lookup p heap = SOME (DataElement xs l d) ==>
        p IN reachable_addresses roots heap)`;;

let make_gc_conf_def = cake_define
  `make_gc_conf limit =
     (mk_? limit (isMutTag o FST):(num#'a) gen_gc_conf)`;;

let reset_gens_def = cake_define
  `reset_gens conf a =
     (match data_to_word_config_gc_kind conf with Generational
       sizes -> GenState 0 (MAP (K a) sizes) | _18 -> GenState 0 [])`;;

let has_gen_def = cake_define
  `has_gen (GenState _19 xs) <=> ~(xs = [])`;;

let data_pointers_def = cake_define
  `data_pointers x1 =
        match x1 with
          [] -> []
        | ((DataElement x y z) :: rest) ->
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

(* Write to unused heap space is fine, e.g. cons *)

let heap_store_def = cake_define
  `(heap_store a y [] = ([],F)) /\
   (heap_store a y (x :: xs) =
     (if a = 0 then (y ++ xs,(el_length x = heap_length y)) else
     if a < el_length x then (x :: xs,F) else
       let (xs,c) = heap_store (a - el_length x) y xs in
         (x :: xs,c)))`;;

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

let heap_store_rel_def = cake_define
  `heap_store_rel heap heap2 <=>
     (!ptr. isSomeDataElement (heap_lookup ptr heap) ==>
            (heap_lookup ptr heap2 = heap_lookup ptr heap))`;;

(* cons *)

(* --- Allocating multiple cons-elements in one go --- *)

let list_to_BlockReps_def = cake_define
  `list_to_BlockReps conf t a [] = ARB /\
   list_to_BlockReps conf t a (h :: l) =
     (match l with
       [] -> [BlockRep cons_tag [h; t]] | _21 ->
         BlockRep cons_tag
           [h; Pointer (a + 3) (Word (ptr_bits conf cons_tag 2))] ::
             list_to_BlockReps conf t (a + 3) l)`;;

(* HOL4 ML code, not ported:
fun unlength_tac thms =
  fs ([heap_length_def, el_length_def, SUM_APPEND] @ thms)
  \\ fs [GSYM heap_length_def]
*)

let bind_each_def = cake_define
  `bind_each tf ts (k:num) i 0 = tf /\
   bind_each tf ts (k:num) i (SUC n) = bind_each tf (ts + 1) (k +
     i) i n |+ (ts,k)`;;

(* A timestamp that is not in the  *)

(* NOT USED *)

(* NOT USED *)

(* word64 *)

(* bignum *)

(* update ref *)

let isRefBlock_def = cake_define
  `isRefBlock x = (?p. x = RefBlock p)`;;

let RefBlock_inv_def = cake_define
  `RefBlock_inv heap heap2 <=>
     (!n x. (heap_lookup n heap = SOME x) /\ ~(isRefBlock x) ==>
            (heap_lookup n heap2 = SOME x)) /\
     (!n x. (heap_lookup n heap2 = SOME x) /\ ~(isRefBlock x) ==>
            (heap_lookup n heap = SOME x))`;;

(* inserting a *fresh* MutBlock ref cannot disturb any existing v_inv:
   the only
   way v_inv inspects refs is through a RefPtr, and those are confined
     to
   FDOM f, which sits inside domain refs *)

(* v_inv cannot see a MutBlock's finalised flag: ref_ptr_annot ignores
   it and
   dest_thunk sends every MutBlock to NotThunk.  Flipping the flag
     therefore
   preserves v_inv -- this is what makes FinaliseCons a no-op at word
     level. *)

(* bound variables deliberately avoid the names used at the use sites,
   so that
   irule/MATCH_MP_TAC does not fail on a free/bound name clash *)

(* ---- MutCons: the Cons allocation, but the value handed back is a
   fresh ref *)

(* like all_ts_SUBSET_gen, but the witness on the right may be a
   different
   value, as long as it carries the timestamp -- needed when a value
     only
   survives inside a newly built Block *)

(* the only new edge leaves ptr and lands inside the payload, which is
   exactly
   what used to sit on the stack *)

(* lifting a v_inv across the MutCons allocation: refs gains a fresh ref
   and f
   gains its binding, and the heap only grew *)

(* a value that is not a thunk cannot become one by adding a fresh ref
   *)

(* mirrors cons_thm_alt: the allocation is the Cons allocation, but the
   value
   handed back is a RefPtr into refs, so f (not tf) gains a binding and
     no
   timestamp is consumed *)

(* HOL4 ML code, not ported:
val update_ref_gen_state_ok = prove(
  ``heap_store b [RefBlock t1] heap = (heap2,T) /\ a <= b /\
    gen_state_ok a (a + (sp + sp1)) heap gens ==>
    gen_state_ok a (a + (sp + sp1)) heap2 gens``,
  Cases_on `gens` \\ fs [gen_state_ok_def]
  \\ fs [EVERY_MEM] \\ rpt strip_tac \\ fs [] \\ res_tac
  \\ fs [gen_start_ok_def] \\ rpt strip_tac
  \\ old_drule (GEN_ALL heap_split_heap_store)
  \\ disch_then old_drule \\ fs [] \\ strip_tac
  \\ fs [] \\ rpt strip_tac \\ res_tac \\ fs []) |> GEN_ALL;
*)

(* HOL4 ML code, not ported:
val update_thunk_gen_state_ok = prove(
  ``heap_store b [ThunkBlock ev t1] heap = (heap2,T) ∧ a <= b ∧
    gen_state_ok a (a + (sp + sp1)) heap gens ⇒
    gen_state_ok a (a + (sp + sp1)) heap2 gens``,
  Cases_on `gens` \\ fs [gen_state_ok_def]
  \\ fs [EVERY_MEM] \\ rpt strip_tac \\ fs [] \\ res_tac
  \\ fs [gen_start_ok_def] \\ rpt strip_tac
  \\ old_drule (GEN_ALL heap_split_heap_store)
  \\ disch_then old_drule \\ fs [] \\ strip_tac
  \\ fs [] \\ rpt strip_tac \\ res_tac \\ fs []) |> GEN_ALL;
*)

let heap_deref_def = cake_define
  `(heap_deref a heap =
     (match heap_lookup a heap with SOME (DataElement xs l
       (RefTag,[])) -> SOME xs | _22 -> NONE))`;;

let thunk_deref_def = cake_define
  `(thunk_deref a heap =
     (match heap_lookup a heap with SOME (DataElement xs l
       (ThunkTag NotEvaluated,[])) -> SOME xs | _23 -> NONE))`;;

(* ---- UpdateCons: writing the hole of an unfinalised MutBlock.  The
   cell is
   laid out as a BlockRep, so the heap-level machinery is the RefBlock/
   ThunkBlock machinery transposed to BlockRep.  What is new is that
     v_inv can
   read BlockRep cells, so rewriting one is only safe because no
     timestamp
   points at an unfinalised MutBlock -- exactly what bc_ref_inv records.
     *)

(* v_inv survives an in-place rewrite of a BlockRep cell that no
   timestamp
   points at: Bignum/Word64Rep/ThunkBlock cells cannot be that cell
     because
   their tags differ, and a Block's cell is in the range of tf *)

(* the binders are renamed apart from the names used at the application
   sites,
   so that qexists can name the witnesses *)

(* v_inv cannot see what sits in a MutBlock's hole, only how long the
   two
   sides of it are *)

(* the only new edges out of ptr land in the value that was written,
   which is
   itself on the stack *)

(* mirrors update_thunk_thm: the hole is rewritten in place, so f and
   the heap
   layout are untouched and only tf shrinks *)

(* update byte ref *)

(* new ref *)

(* deref *)

let heap_el_def = cake_define
  `heap_el x1 n heap =
        match x1 with
          (Pointer a u) ->
       match heap_lookup a heap with SOME (DataElement xs l d) ->
           (if n < LENGTH xs then (EL n xs,T) else (ARB,F)) | _24 ->
             (ARB,F)
        | _25 -> (ARB,F)`;;

(* el *)

(* new byte array *)

(* equality *)

(* permute stack *)

(* pop *)

(* duplicate *)

(* move *)

(* splits *)


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
           (n2w 1) | _26 -> all_ones (data_to_word_config_len_bits
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
          (Data (Loc l1 l2)) -> Loc l1 0
        | (Data (Word v)) -> Word (v && (--(n2w 1)))
        | (Pointer n w) -> Word (get_addr conf n w)`;;

let thunk_tag_to_bits_def = cake_define
  `thunk_tag_to_bits Evaluated = (n2w 1) /\
   thunk_tag_to_bits NotEvaluated = (n2w 0)`;;

let word_payload_def = cake_define
  `(word_payload ys l (BlockTag n) qs conf =
      (make_header conf (n2w n << 2) (LENGTH ys),
       MAP (word_addr conf) ys,(
       (qs = []) /\ (LENGTH ys = l) /\
       encode_header conf (n * 4) (LENGTH ys) =
         SOME (make_header conf (n2w n << 2) (LENGTH ys):'a word))))
           /\
   (word_payload ys l (RefTag) qs conf =
      (make_header conf (n2w 2) (LENGTH ys),
       MAP (word_addr conf) ys,(
       (qs = []) /\ (LENGTH ys = l)))) /\
   (word_payload ys l (ThunkTag e) qs conf =
      (make_header conf (thunk_tag_to_bits e << 3 || (n2w 6)) (LENGTH
        ys),
       MAP (word_addr conf) ys,(
       (qs = []) /\ (LENGTH ys = 1) /\ l = 1))) /\
   (word_payload ys l Word64Tag qs conf =
      (make_header conf (n2w 3) l,
       qs,((ys = []) /\ (LENGTH qs = l) /\
           IS_SOME ((encode_header conf 3 l):('a word) option)))) /\
   (word_payload ys l (NumTag b) qs conf =
      (make_header conf (b2w b << 2 || ((n2w 3):'a word)) (LENGTH
        qs),
       qs,((ys = []) /\ (LENGTH qs = l) /\
           IS_SOME ((encode_header conf (w2n (b2w b << 2 || ((n2w
             3):'a word)))
                       (LENGTH qs)):('a word) option)))) /\
   (word_payload ys l (BytesTag fl n) qs conf =
      (((make_byte_header conf fl n):'a word),
       qs,((ys = []) /\ (LENGTH qs = l) /\
           (let k = if dimindex (:'a) = 32 then 2 else 3 in
           n + 2 EXP k < 2 EXP (data_to_word_config_len_size conf
             + k)))))`;;

let word_el_def = cake_define
  `(word_el a (Unused l) conf = word_list_exists (a:'a word) (l + 1)) /\
   (word_el a (ForwardPointer n d l) conf =
      set_sep_one (a,Word (n2w n << 2)) *
      word_list_exists (a + bytes_in_word) l) /\
   (word_el a (DataElement ys l (tag,qs)) conf =
      (let (h,ts,c) = word_payload ys l tag qs conf in
        word_list a (Word h :: ts) *
        cond (LENGTH ts < 2 EXP (dimindex (:'a) - 4) /\
              decode_length conf h = n2w (LENGTH ts) /\ c)))`;;

let word_heap_def = cake_define
  `(word_heap a ([]:(('a word_loc,num#('a word_loc) list)heap_element)
  list) conf = emp) /\
   (word_heap a (x :: xs) conf =
      word_el a x conf *
      word_heap (a + bytes_in_word * n2w (el_length x)) xs conf)`;;

let gen_starts_in_store_def = cake_define
  `gen_starts_in_store c x2 x3 =
      match (x2,x3) with
        ((GenState _27 gen_starts),(SOME (Word w))) ->
     (!gen_sizes. data_to_word_config_gc_kind
        c = Generational gen_sizes ==>
        LENGTH gen_starts = LENGTH gen_sizes /\
        (!x xs. gen_starts = x :: xs ==>
               w = (bytes_in_word * n2w x)))
      | (_28,_29) -> F`;;

let glob_real_inv_def = cake_define
  `glob_real_inv c (curr:'a word) globals globreal <=>
     (?w. globals = SOME (Word w) /\
         globreal = SOME (Word (curr + (w >>> (shift_length c) <<
           (backend_common_word_shift) (:'ga)))))`;;

let heap_in_memory_store_def = cake_define
  `heap_in_memory_store heap a sp sp1 gens c s m dm limit <=>
     heap_length heap <= dimword (:'a) DIV 2 EXP shift_length c /\
     (heap_length heap + 3) * (dimindex (:'a) DIV 8) < dimword (:'a)
       /\
     (backend_common_word_shift) (:'a) <= shift_length c /\
       ~(data_to_word_config_len_size c = 0) /\
       data_to_word_config_len_size
     c + 7 < dimindex (:'a) /\
     shift_length c < dimindex (:'a) /\ Globals IN FDOM s /\
     (?curr other.
       byte_aligned curr /\ byte_aligned other /\
       (FLOOKUP s CurrHeap = SOME (Word (curr:'a word))) /\
       (FLOOKUP s OtherHeap = SOME (Word other)) /\
       (FLOOKUP s NextFree = SOME (Word (curr + bytes_in_word * n2w
         a))) /\
       (FLOOKUP s TriggerGC = SOME (Word (curr + bytes_in_word * n2w
         (a + sp)))) /\
       (FLOOKUP s EndOfHeap = SOME (Word (curr + bytes_in_word * n2w
         (a + sp + sp1)))) /\
       (FLOOKUP s HeapLength = SOME (Word (bytes_in_word * n2w
         limit))) /\
       glob_real_inv c curr (FLOOKUP s Globals) (FLOOKUP s GlobReal)
         /\
       gen_starts_in_store c gens (FLOOKUP s GenStart) /\
       (word_heap curr heap c *
        word_heap other (heap_expand limit) c) (fun2set (m,dm)))`;;

let word_ml_inv_def = cake_define
  `word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs stack <=>
     (?hs. abs_ml_inv c (MAP FST stack) refs
       (hs,heap,be,a,sp,sp1,gens) limit ts /\
          EVERY2 (\v w. word_addr c v = w) hs (MAP SND stack))`;;

let memory_rel_def = cake_define
  `memory_rel c be ts refs space' st (m:'a word->'a word_loc) dm vars
  <=>
     (?heap limit a sp sp1 gens.
        heap_in_memory_store heap a sp sp1 gens c st m dm limit /\
        word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs vars /\
        (limit + 3) * (dimindex (:'ga) DIV 8) + 1 < dimword (:'ga)
          /\ space' <= sp)`;;

let get_real_addr_def = cake_define
  `get_real_addr conf st (w:'a word) =
     (let k = (backend_common_word_shift) (:'ga) in
       match FLOOKUP st CurrHeap with SOME (Word curr) ->
           (if k = shift_length conf /\ data_to_word_config_len_bits
             conf = 0 /\ data_to_word_config_tag_bits conf = 0 then SOME
             ((curr + w) - (n2w 1)) else
             if k <= data_to_word_config_pad_bits conf + 1 then
               SOME (curr + (w >>> (shift_length conf - k))) else
               SOME (curr + (w >>> (shift_length conf) << k))) | _30
               -> NONE)`;;

let get_real_offset_def = cake_define
  `get_real_offset (w:'a word) =
     (if dimindex (:'a) = 32 then SOME (w + bytes_in_word) else
       SOME (w << 1 + bytes_in_word))`;;

let get_real_simple_addr_def = cake_define
  `get_real_simple_addr conf st (w:'a word) =
     (match FLOOKUP st CurrHeap with SOME (Word curr) -> SOME
       (curr + w >>> shift_length conf << (backend_common_word_shift)
       (:'ga)) | _31 -> NONE)`;;

(* mirrors memory_rel_Update: writing the hole of an unfinalised
   MutBlock is
   the same single memory write as updating a reference's payload *)

let store_list_def = cake_define
  `(data_to_word_memoryProof_store_list a [] (m:'a word->'a word_loc) dm
  = SOME m) /\
   (data_to_word_memoryProof_store_list a (w :: ws) m dm =
      (if a IN dm then
        data_to_word_memoryProof_store_list (a + bytes_in_word) ws
          ((a =+ w) m) dm else NONE))`;;
hol4_overload "store_list" "data_to_word_memoryProof_store_list";;

(* mirrors memory_rel_Cons1: a MutBlock is laid out exactly like the
   Block it
   finalises to, so the allocation is the Cons allocation; what differs
     is that
   the abstract value handed back is a RefPtr into refs rather than a
     Block,
   and no timestamp is consumed *)

(* ---- FinaliseCons: the MutBlock at ptr keeps its payload and only
   flips its
   fin flag, and the value handed back is the Block that payload
     denotes.
   Neither all_ts, all_vs, ref_edge nor dest_thunk can observe fin, so
     the
   only real work is relocating the payload from the ref into the new
     Block. *)

(* every value reachable after finalisation was reachable before, except
   the
   new Block itself *)

(* the hole of a MutBlock is reachable from the pointer to it *)

(* the payload of the finalised cell moves into the new Block, so the
   refs it
   reaches are the ones the pointer used to reach *)

let word_of_byte_def = cake_define
  `word_of_byte (w:'a word) =
     (let w = (w << 8 || w) in
     let w = (w << 16 || w) in
       if dimindex (:'a) = 32 then w else w << 32 || w)`;;

(* HOL4 ML code, not ported:
val (set_byte_sort_dec,set_byte_sort_asc) = let
  fun cross [] ys = []
    | cross (x::xs) ys = map (fn y => (x,y)) ys :: cross xs ys
  val xs = [0,1,2,3,4,5,6,7]
  val ys = cross xs xs |> Lib.flatten
  fun f (x,y) =
    SPECL [numSyntax.term_of_int x,numSyntax.term_of_int y]
      set_byte_sort
    |> SIMP_RULE (srw_ss()) [good_dimindex_def]
  val ts1 = filter (fn (x,y) => x < y) ys
  val ts2 = filter (fn (x,y) => y < x) ys
  in (LIST_CONJ (map f ts1), LIST_CONJ (map f ts2)) end
*)

(* slow *)

(* slow *)

let last_bytes_def = cake_define
  `last_bytes k b a w be =
     (if k = 0 then w else
       set_byte a b (last_bytes (k - 1) b (a + (n2w 1)) w be) be)`;;

let copy_list_def = cake_define
  `copy_list c' st k (a,x,(b:'a word),(m:'a word->'a word_loc),dm) =
     (let c = (b IN dm) in
     let m = (b =+ x) m in
     let b = b + bytes_in_word in
       if k = 0 then (if c then SOME (b,m) else NONE) else
         match a with Loc _32 _33 -> NONE | Word a ->
         (match get_real_addr c' st a with NONE -> NONE | SOME a ->
           (let c = (c /\ a + (n2w 2) * bytes_in_word IN dm /\ a +
             bytes_in_word IN dm) in
           let x = m (a + bytes_in_word) in
           let a = m (a + (n2w 2) * bytes_in_word) in
             if c then copy_list c' st (k - 1) (a,x,b,m,dm) else
               NONE)))`;;

(* HOL4 ML code, not ported:
val not_bit_lt_2 = not_bit_lt_2exp |> Q.SPEC `0` |> SIMP_RULE (srw_ss())
  []
*)

(* HOL4 ML code, not ported:
val expand_num =
  DECIDE ``4 = SUC 3 /\ 3 = SUC 2 /\ 2 = SUC 1 /\ 1 = SUC 0 /\
           5 = SUC 4 /\ 6 = SUC 5 /\ 7 = SUC 6 /\ 8 = SUC 7``
*)

let hide_memory_rel_def = cake_define
  `hide_memory_rel = memory_rel`;;

let hide_heap_in_memory_store_def = cake_define
  `hide_heap_in_memory_store = heap_in_memory_store`;;

(* a compare-by-pointer RefPtr can never point at a MutBlock: v_inv's
   RefPtr
   case demands ~b when the ref is a MutBlock *)

(* the MutBlock exclusion is needed: a MutBlock is laid out with a
   BlockTag
   header, whose bits 2 and 3 are both clear, so the conclusion below
     fails *)

(* HOL4 ML code, not ported:
val lt8 =
  DECIDE ``(n < 8n) = (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/
                       n = 4 \/ n = 5 \/ n = 6 \/ n = 7)``
*)

let word_cmp_res_def = cake_define
  `word_cmp_res i (j:int) =
     (if i = j then (n2w 1) else if i < j then (n2w 0) else (n2w
       2))`;;

let word_cmp_loop_def = cake_define
  `word_cmp_loop (l:'a word) (a1:'a word) a2 dm (m:'a word->'a word_loc)
  =
     (if l = (n2w 0) then SOME (n2w 1) else
       if a1 IN dm /\ a2 IN dm then
         match (m a1,m a2) with (Word w1,Word w2) ->
             (if w1 = w2 then
               word_cmp_loop (l - (n2w 1)) (a1 - bytes_in_word)
                 (a2 - bytes_in_word) dm m else if w1 <+ w2 then
                   SOME (n2w 0) else SOME ((n2w 2):'a word)) | _34 ->
                   NONE else NONE)`;;

(* HOL4 ML code, not ported:
val word_cmp_loop_ind =  theorem"word_cmp_loop_ind";
*)

(* HOL4 ML code, not ported:
val good_dimindex_def = good_dimindex_def;
*)

(* TERMINATION: wf_rel_tac`measure (v_size o FST)`
 \\ Induct_on`l1` \\ ntac 2 (rw[v_size_def])
 \\ Cases_on`l2` \\ fs[] \\ rw[]
 \\ res_tac \\ fs[] \\ rfs[]
 \\ first_x_assum(qspecl_then[`0`,`t1`]mp_tac) \\ rw[] *)
let v_same_type_def = cake_define
  `v_same_type x1 x2 =
        match (x1,x2) with
          ((Number _35),(Number _36)) -> T
        | ((Word64 _37),(Word64 _38)) -> T
        | ((Block _39 t1 l1),(Block _40 t2 l2)) -> (t1 = t2 /\ LENGTH
          l1 = LENGTH l2 ==> LIST_REL v_same_type l1 l2)
        | ((CodePtr _41),(CodePtr _42)) -> T
        | ((RefPtr _43 _44),(RefPtr _45 _46)) -> T
        | (_47,_48) -> F`;;

let _ = size_thms "v";;
(* HOL4 termination: \\ ntac 2 gen_tac \\ Induct \\ rw[v_size_def] \\
   rw[] \\ res_tac \\ rw[] *)
let v_depth_def = cake_define_wf
  `MEASURE v_size`
  `v_depth x1 =
        match x1 with
          (Block _49 _50 ls) -> (if NULL ls then 0 else 1) + MAX_LIST
            (MAP v_depth ls)
        | _51 -> 0`;;

(* HOL4 ML code, not ported:
val v_depth_ind = theorem"v_depth_ind";
*)

let elements_list_def = cake_define
  `(elements_list [] = T) /\
   (elements_list [v] = T) /\
   (elements_list (v :: w :: vs) =
    (?ts t ls1 ls2.
      w = Block ts t (ls1 ++ [v] ++ ls2) /\
      elements_list (w :: vs)))`;;

(* HOL4 ML code, not ported:
val elements_list_ind = theorem"elements_list_ind";
*)

let vb_eq_size_def = cake_define
  `vb_eq_size refs x2 x3 =
        match (x2,x3) with
          ((Block _52 t1 l1),(Block _53 t2 l2)) ->
        if isClos t1 l1 \/ isClos t2 l2 then if isClos t1 l1 /\
          isClos t2 l2 then SOME ((1:num),T) else NONE else if (t1 = t2)
          /\ (LENGTH l1 = LENGTH l2) then OPTION_MAP (\(n,b). (n + 1,b))
          (vb_eq_size_list refs l1 l2) else SOME (1,F)
        | ((RefPtr b1 n1),(RefPtr b2 n2)) ->
        if b1 /\ b2 then
          (match (sptree_lookup n1 refs,sptree_lookup n2 refs) with
             (SOME (ByteArray T bs1),SOME (ByteArray T bs2)) -> SOME
               (1,(bs1 = bs2)) | (SOME (ByteArray T bs1),_54) -> NONE |
               (_55,SOME (ByteArray T bs2)) -> NONE | _56 -> SOME (1,(n1
               = n2))) else NONE
        | ((Number n1),(Number n2)) -> SOME (1,(n1 = n2))
        | ((Word64 w1),(Word64 w2)) -> SOME (1,(w1 = w2))
        | (_57,_58) -> NONE
        | ([],[]) -> SOME (0,T)
        | ([],_59) -> SOME (0,F)
        | (_60,[]) -> SOME (0,F)
        | ((v1 :: vs1),(v2 :: vs2)) ->
        match vb_eq_size refs v1 v2 with NONE -> NONE | SOME (n,F) ->
          SOME (n + 1,F) | SOME (n,T) -> (
          match vb_eq_size_list refs vs1 vs2 with NONE -> NONE |
            SOME (m,b) -> SOME (m + n + 1,b))`;;

let word_header_def = cake_define
  `word_header c st a dm m =
     (match get_real_addr c st a with NONE -> NONE | SOME a1 ->
         (if ~(a1 IN dm) then NONE else
           match m a1 with Word x1 -> SOME (a1,x1) | _61 -> NONE))`;;

let fix_clock_def = cake_define
  `data_to_word_memoryProof_fix_clock ck l NONE = NONE /\
   data_to_word_memoryProof_fix_clock ck (l:num) (SOME
     (y,(l1:num),(ck1:num))) =
   (let new_ck = if ck < ck1 then ck else ck1 in let
       new_l = if l < l1 then l else l1 in SOME (y,new_l,new_ck))`;;
hol4_overload "fix_clock" "data_to_word_memoryProof_fix_clock";;

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
(* HOL4 termination: >> rw[] >> imp_res_tac fix_clock_IMP >> rw[] *)
let word_eq_def = cake_define_wf
  `MEASURE (\x. match x with INL (c,st,dm,m,l1,ck1,w1,w2) -> l1 | INR
  (c,st,dm,m,l1,ck1,w,a1,a2) -> l1)`
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
                  (decode_length c h1),ck))) | _62 -> NONE)) /\
   (word_eq_list c st dm m l ck w a1 a2 =
      (if w = ((n2w 0):'a word) then SOME ((n2w 1),l,ck) else
      if ~(a1 IN dm) \/ ~(a2 IN dm) \/ (l = 0) \/ (ck = 0) then NONE
        else
        match (m a1,m a2) with (Word w1,Word w2) ->
         (match fix_clock (ck - 1) (l - 1) (word_eq c st dm m (l - 1)
           (ck - 1) w1 w2) with NONE -> NONE | SOME (x,l,ck') -> (if ~(x
           = (n2w 1)) then SOME (x,l,ck) else
                             if l = 0 then NONE else
                              word_eq_list c st dm m (l - 1) ck (w -
                                (n2w 1))
                              (a1 + bytes_in_word) (a2 +
                                bytes_in_word))) | _63 -> NONE))`;;

(* HOL4 ML code, not ported:
val word_eq_ind = theorem "word_eq_ind";
*)

let eq_assum_def = cake_define
  `(eq_assum a m dm [] = T) /\
   (eq_assum a m dm (v :: vs) <=>
      a IN dm /\ eq_assum (a + bytes_in_word) m dm vs)`;;

let eq_explode_def = cake_define
  `(eq_explode a m dm [] = []) /\
   (eq_explode a m dm (v :: vs) = (v,m a) :: eq_explode (a +
     bytes_in_word) m dm vs)`;;

let word_mem_eq_def = cake_define
  `(word_mem_eq a [] dm m <=> SOME T) /\
   (word_mem_eq a (x :: xs) dm m <=>
      (if ~(a IN dm) then NONE else
      if ~isWord (m a) then NONE else
      if ~(m a = Word x) then SOME F else
        word_mem_eq (a + bytes_in_word) xs dm m))`;;

let bignum_words_def = cake_define
  `bignum_words c i =
     (let (sign,payload) = i2mw i in
       match encode_header c (if sign then 7 else 3) (LENGTH
         payload) with NONE -> NONE | SOME h -> SOME (h :: payload))`;;

(* copy forward *)

(* HOL4 termination: \\ Cases_on `n` \\ fs [] \\ rw [] \\ fs
   [WORD_LO] \\ rfs [NOT_LESS] \\ rewrite_tac
   [addressTheory.word_arith_lemma2,GSYM word_sub_def] \\ fs [] *)
let word_copy_fwd_def = cake_define_wf
  `MEASURE (w2n o FST o SND)`
  `word_copy_fwd be (n:'a word) a b (m:'a word->'a word_loc) dm =
     (if dimword (:'a) <= 4 then NONE else
     if n <+ (n2w 4) then
       if n <+ (n2w 2) then
         if n = (n2w 0) then SOME m else
           OPTION_BIND (mem_load_byte_aux m dm be a)
                       (\w. mem_store_byte_aux m dm be b w) else
         OPTION_BIND (mem_load_byte_aux m dm be a) (\w1.
         OPTION_BIND (mem_load_byte_aux m dm be (a + (n2w 1))) (\w2.
           if n = (n2w 2) then
             OPTION_BIND (mem_store_byte_aux m dm be b w1) (\m.
             OPTION_BIND (mem_store_byte_aux m dm be (b + (n2w 1))
               w2) (\m. SOME m)) else
             OPTION_BIND (mem_load_byte_aux m dm be (a + (n2w 2)))
               (\w3.
             OPTION_BIND (mem_store_byte_aux m dm be b w1) (\m.
             OPTION_BIND (mem_store_byte_aux m dm be (b + (n2w 1))
               w2) (\m.
             OPTION_BIND (mem_store_byte_aux m dm be (b + (n2w 2))
               w3) (\m. SOME m)))))) else
       OPTION_BIND (mem_load_byte_aux m dm be a) (\w1.
       OPTION_BIND (mem_load_byte_aux m dm be (a + (n2w 1))) (\w2.
       OPTION_BIND (mem_load_byte_aux m dm be (a + (n2w 2))) (\w3.
       OPTION_BIND (mem_load_byte_aux m dm be (a + (n2w 3))) (\w4.
       OPTION_BIND (mem_store_byte_aux m dm be b w1) (\m.
       OPTION_BIND (mem_store_byte_aux m dm be (b + (n2w 1)) w2) (\m.
       OPTION_BIND (mem_store_byte_aux m dm be (b + (n2w 2)) w3) (\m.
       OPTION_BIND (mem_store_byte_aux m dm be (b + (n2w 3)) w4) (\m.
         word_copy_fwd be (n - (n2w 4)) (a + (n2w 4)) (b + (n2w
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

(* copy backward *)

(* HOL4 termination: \\ Cases_on `n` \\ fs [] \\ rw [] \\ fs
   [WORD_LO] \\ rfs [NOT_LESS] \\ rewrite_tac
   [addressTheory.word_arith_lemma2,GSYM word_sub_def] \\ fs [] *)
let word_copy_bwd_def = cake_define_wf
  `MEASURE (w2n o FST o SND)`
  `word_copy_bwd be (n:'a word) a b (m:'a word->'a word_loc) dm =
     (if dimword (:'a) <= 4 then NONE else
     if n <+ (n2w 4) then
       if n <+ (n2w 2) then
         if n = (n2w 0) then SOME m else
           OPTION_BIND (mem_load_byte_aux m dm be a)
                       (\w. mem_store_byte_aux m dm be b w) else
         OPTION_BIND (mem_load_byte_aux m dm be a) (\w1.
         OPTION_BIND (mem_load_byte_aux m dm be (a - (n2w 1))) (\w2.
           if n = (n2w 2) then
             OPTION_BIND (mem_store_byte_aux m dm be b w1) (\m.
             OPTION_BIND (mem_store_byte_aux m dm be (b - (n2w 1))
               w2) (\m. SOME m)) else
             OPTION_BIND (mem_load_byte_aux m dm be (a - (n2w 2)))
               (\w3.
             OPTION_BIND (mem_store_byte_aux m dm be b w1) (\m.
             OPTION_BIND (mem_store_byte_aux m dm be (b - (n2w 1))
               w2) (\m.
             OPTION_BIND (mem_store_byte_aux m dm be (b - (n2w 2))
               w3) (\m. SOME m)))))) else
       OPTION_BIND (mem_load_byte_aux m dm be a) (\w1.
       OPTION_BIND (mem_load_byte_aux m dm be (a - (n2w 1))) (\w2.
       OPTION_BIND (mem_load_byte_aux m dm be (a - (n2w 2))) (\w3.
       OPTION_BIND (mem_load_byte_aux m dm be (a - (n2w 3))) (\w4.
       OPTION_BIND (mem_store_byte_aux m dm be b w1) (\m.
       OPTION_BIND (mem_store_byte_aux m dm be (b - (n2w 1)) w2) (\m.
       OPTION_BIND (mem_store_byte_aux m dm be (b - (n2w 2)) w3) (\m.
       OPTION_BIND (mem_store_byte_aux m dm be (b - (n2w 3)) w4) (\m.
         word_copy_bwd be (n - (n2w 4)) (a - (n2w 4)) (b - (n2w
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

(* HOL4 ML code, not ported:
val list_copy_bwd_def = list_copy_bwd_def |> REWRITE_RULE [minus_def];
*)

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
(* HOL4 ML code, not ported:
val list_copy_bwd_alias_def = list_copy_bwd_alias_def
                                |> REWRITE_RULE [minus_def];
*)

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

(* see more interesting theorem below *)

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
  `word_copy_array be n a a1 b b1 (m:'a word->'a word_loc) dm =
     (if b1 <=+ a1 then
       word_copy_fwd be n (a + a1) (b + b1) m dm else
       word_copy_bwd be n ((a + a1 + n) - (n2w 1)) ((b + b1 + n) -
         (n2w 1)) m dm)`;;

(* HOL4 ML code, not ported:
val memory_rel_copy_array_NONE_lemma =
  memory_rel_RefByte_alt
  |> Q.INST [`w`|->`0w`]
  |> SIMP_RULE (srw_ss()) [w2w_def,w2n_n2w,word_of_byte_0,last_bytes_0,
       LET_THM,LUPDATE_REPLICATE]
*)

let append_writes_def = cake_define
  `append_writes c ptr hdr [] l = ARB /\
   append_writes c ptr (hdr:'a word) (x :: xs) l =
     Word hdr :: x ::
       (if xs = [] then [l] else
         let ptr = ptr + ((n2w 3) << shift_length c) in
           Word ptr ::
           append_writes c ptr hdr xs l)`;;

(* --- ML lists cannot exceed heap size: --- *)

let walk_def = cake_define
  `data_to_word_memoryProof_walk conf heap ptr n =
     (if n = 0 then [] else if n = 1 then [ptr] else
       match some (\p.
         ?x y.
         heap_lookup ptr heap = SOME (BlockRep cons_tag [x; y]) /\
         y = Pointer p (Word (ptr_bits conf cons_tag 2))) with
         NONE -> [] | SOME p ->
           ptr :: data_to_word_memoryProof_walk conf heap p (n -
             1))`;;
hol4_overload "walk" "data_to_word_memoryProof_walk";;

let block_drop_def = cake_define
  `block_drop x1 v =
      match (x1,v) with
        (0,v) -> SOME v
      | ((SUC n),(Block ts tag [h; vl])) -> block_drop n vl
      | (_64,_65) -> NONE`;;

(* ---------------------------------------------------------------------
   ---- *)

let build_part_words_def = cake_define
  `build_part_words c m (Int i) offset =
     (if small_int (:'a) i then SOME (Word (Smallnum i),[]) else let
       (sign,ws) = i2mw i in
             match encode_header c (w2n (b2w sign << 2 || ((n2w 3):'a
               word))) (LENGTH ws) with NONE -> NONE | SOME hd -> SOME
               (make_ptr c offset ((n2w 0):'a word) (LENGTH ws),
                              MAP Word (hd :: ws))) /\
   build_part_words c m (Con t ns) (offset:'a word) =
     (if NULL ns then
        if t < dimword (:'a) DIV 16 then SOME (Word (n2w (16 * t +
          2)),[]) else NONE else
        match encode_header c (4 * t) (LENGTH ns) with NONE -> NONE |
          SOME hd -> SOME (make_cons_ptr c offset t (LENGTH ns),
                           Word hd :: (MAP m ns))) /\
   build_part_words c m (W64 w) offset =
     (let ws = (if dimindex (:'ga) < 64 then [((63 >< 32) w); ((31 ><
       0) w)] else [((63 >< 0) w):'a word]) in
        match encode_header c 3 (LENGTH ws) with NONE -> NONE | SOME
          hd -> SOME (make_ptr c offset ((n2w 0):'a word) (LENGTH ws),
                           MAP Word (hd :: ws))) /\
   build_part_words c m (Str s) offset =
     (let bytes = MAP (n2w o ORD) (explode s) in
      let n = LENGTH bytes in
      let hd = make_byte_header c T n in
      let ws = write_bytes bytes (REPLICATE (byte_len (:'ga) n) (n2w
        0)) (?_be c) in
        if byte_len (:'ga) n < 2 EXP (dimindex (:'ga) - 4) /\
           byte_len (:'ga) n < 2 EXP data_to_word_config_len_size
             c then SOME (make_ptr c offset ((n2w 0):'a word)
             (byte_len (:'ga) n),MAP Word (hd :: ws)) else NONE)`;;

let build_words_def = cake_define
  `build_words c m i [] off = SOME (m (i - (1:num)),[]) /\
   build_words c m i (x :: parts) (off:'a word) =
     (match build_part_words c m x off with NONE -> NONE | SOME
       (w,xs) ->
       (match build_words c ((i =+ w) m) (i + 1) parts (off +
         bytes_in_word * n2w (LENGTH xs)) with NONE -> NONE | SOME
         (r,ys) -> SOME (r,xs ++ ys)))`;;

let word_cond_add_def = cake_define
  `word_cond_add c a x3 =
      match x3 with
        (F,x) -> (x:'a word_loc)
      | (T,Word w) -> Word (w + a << (shift_length c -
        (backend_common_word_shift) (:'a)))
      | (T,other) -> other`;;

let good_loc_def = cake_define
  `good_loc code x2 =
      match x2 with
        (Loc n m) -> (m = 0 /\ n IN code)
      | _66 -> T`;;

let read_word_def = cake_define
  `read_word dm m a = (theWord (m a),(a IN dm /\ isWord (m a)))`;;

(* HOL4 termination: \\ Cases_on ‘len’ \\ gvs [WORD_LO] \\
   rewrite_tac [GSYM word_sub_def,addressTheory.word_arith_lemma2] \\
   Cases_on ‘good_dimindex (:α)’ \\ simp [] \\ gvs
   [dimword_def,good_dimindex_def] *)
let word_xor_bytes_def = cake_define_wf
  `MEASURE (\(a1,a2,len,dm,m). w2n len)`
  `word_xor_bytes (a1:'a word) (a2:'a word) (len:'a word) dm m =
     (if len <+ (n2w 2) \/ ~(good_dimindex) (:'a) then
       if len = (n2w 0) then SOME m else
         let (w1a,c1) = read_word dm m a1 in
         let (w2a,c2) = read_word dm m a2 in
         let a = word_xor w1a w2a in
         let m = (a2 =+ Word (a:'a word)) m in
           if c1 /\ c2 then SOME m else NONE else
       let (w1a,c1) = read_word dm m a1 in
       let (w2a,c2) = read_word dm m a2 in
       let (w1b,c3) = read_word dm m (a1 + bytes_in_word) in
       let (w2b,c4) = read_word dm m (a2 + bytes_in_word) in
       let a = word_xor w1a w2a in
       let b = word_xor w1b w2b in
       let m = ((a2 + bytes_in_word) =+ Word b) ((a2 =+ Word a) m) in
         if c1 /\ c2 /\ c3 /\ c4 then
           word_xor_bytes (a1 + (n2w 2) * bytes_in_word) (a2 + (n2w
             2) * bytes_in_word)
             (len - (n2w 2)) dm m else NONE)`;;

let make_zeros_def = cake_define
  `make_zeros (vals:word8 list) =
     REPLICATE (LENGTH vals DIV (dimindex (:'ga) DIV 8) + 1) ((n2w
       0):'a word)`;;

let xor_words_def = cake_define
  `xor_words xs ys =
      match (xs,ys) with
        ([],ys) -> SOME ys
      | (xs,[]) -> NONE
      | ((x :: xs),(y :: ys)) ->
     match xor_words xs ys with NONE -> NONE | SOME rest -> SOME
       (word_xor (x:'a word) y :: rest)`;;

(*
Theorem xor_bytes_length:
  ∀xs ys zs. xor_bytes xs ys = SOME zs ⇒ LENGTH zs = LENGTH ys
Proof
  Induct \\ Cases_on ‘ys’ \\ gvs
    [semanticPrimitivesTheory.xor_bytes_def,AllCaseEqs()]
  \\ rw [] \\ gvs []
QED
*)

(* --------- str_cmp --------- *)

let word_str_cmp_loop_def = cake_define
  `word_str_cmp_loop (a1:'a word) (a2:'a word) r1 r2 (len:'a word) dm m
  be ck =
     (if ck = 0 then NONE else
     if len = bytes_in_word then
       SOME (r1,r2) else
       match mem_load_byte_aux m dm be a1 with NONE -> NONE | SOME b1
         ->
       (match mem_load_byte_aux m dm be a2 with NONE -> NONE | SOME
         b2 ->
         (if b1 = b2 then
           word_str_cmp_loop (a1 + (n2w 1)) (a2 + (n2w 1)) r1 r2 (len
             - (n2w 1)) dm m be (ck - (1:num)) else
           SOME (w2w b1,w2w b2))))`;;

let word_str_cmp_def = cake_define
  `word_str_cmp b (a1:'a word) (a2:'a word) dm m be c =
     (let k = (dimindex (:'ga) - data_to_word_config_len_size c -
       (backend_common_word_shift) (:'a)) in
       if a1 IN dm /\ a2 IN dm /\ isWord (m a1) /\ isWord (m a2) then
         let l1 = (theWord (m a1) >>> k) in
         let l2 = (theWord (m a2) >>> k) in
           if b then
             (if ~(l1 = l2) then SOME (l1,l2) else
                word_str_cmp_loop (a1 + bytes_in_word) (a2 +
                  bytes_in_word) l1 l1 l1 dm m be (dimword (:'a))) else
             (let l = n2w (MIN (w2n l1) (w2n l2)) in
                word_str_cmp_loop (a1 + bytes_in_word) (a2 +
                  bytes_in_word) l1 l2 l dm m be (dimword (:'a)))
                  else NONE)`;;

let find_diff_def = cake_define
  `find_diff [] [] r1 r2 = (r1,r2) /\
   find_diff (x :: xs) (y :: ys) r1 r2 = (if x = y then find_diff
     xs ys r1 r2 else (w2w x,w2w y))`;;
