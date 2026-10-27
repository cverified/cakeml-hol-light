(* tools/wip-update_byte.ml: the lemmas that the proof of
   update_byte_ref_thm of data_to_word_memoryProof needs, each
   proved in a session cut at the statement (tools/bin/trybase) and
   waiting for the proof itself.  Nothing loads this file: the
   lemmas go into the EXTRA_BEFORE block of the statement when the
   proof is done, and the file is deleted then.

   What is still to write: gc_kind_byte_update (the halves of the
   split of the new heap, over the port's own heap_split_replace),
   bc_ref_inv_update_byte_at (the arm of the reference written) and
   the proof itself, which is update_thunk_thm's with a byte array
   for the thunk -- except that the heap is given as an append
   (h1 ++ [Bytes ...] ++ h2) and not by a heap_store. *)

(* the two elements of a byte array that is written are of a
   length, whatever the bytes are *)
let samelen_bytes = prove
 (cake_as_vars (fun () ->
    `el_length (Bytes be fl ys ws) = el_length (Bytes be fl xs ws)`),
  REWRITE_TAC[bytes_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[el_length_def; LENGTH_write_bytes]);;

(* the element of a byte array is data *)
let isSomeDataElement_Bytes = prove
 (cake_as_vars (fun () ->
    `isSomeDataElement (SOME (Bytes be fl bs ws))`),
  REWRITE_TAC[isSomeDataElement_def; bytes_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  W(fun (asl,w) ->
    let vs,bod = strip_exists w in
    MAP_EVERY EXISTS_TAC
      (snd (strip_comb (rand (lhand bod))))) THEN
  REWRITE_TAC[]);;

(* so the addresses that hold data are the ones that held data *)
let isSomeDataElement_byte_update = prove
 (cake_as_vars (fun () ->
    `!n. isSomeDataElement
           (heap_lookup n (ha ++ [Bytes be fl ys ws] ++ hb)) =
         isSomeDataElement
           (heap_lookup n (ha ++ [Bytes be fl xs ws] ++ hb))`),
  GEN_TAC THEN
  REWRITE_TAC[GSYM APPEND_ASSOC;
              data_to_word_memoryProof_heap_lookup_APPEND;
              heap_length_clauses; ADD_CLAUSES; heap_lookup_def;
              samelen_bytes] THEN
  REPEAT (COND_CASES_TAC THEN
          ASM_REWRITE_TAC[isSomeDataElement_Bytes]) THEN
  REWRITE_TAC[isSomeDataElement_Bytes]);;

(* the heap stays good when a byte array is written: it is as long
   as it was, it has the forward pointers it had, and the element
   written holds no pointer *)
let heap_ok_byte_update = prove
 (cake_as_vars (fun () ->
    `heap_ok (ha ++ [Bytes be fl xs ws] ++ hb) limit' /\
     LENGTH xs = LENGTH ys
     ==> heap_ok (ha ++ [Bytes be fl ys ws] ++ hb) limit'`),
  REWRITE_TAC[heap_ok_def; heap_length_APPEND;
              heap_length_clauses; ADD_CLAUSES; samelen_bytes;
              FILTER_APPEND; FILTER] THEN
  REWRITE_TAC[bytes_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[isForwardPointer_def; LENGTH_write_bytes] THEN
  STRIP_TAC THEN SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MEM_APPEND; MEM] THEN
  STRIP_TAC THEN
  (let isd = REWRITE_RULE[LENGTH_write_bytes]
               (CONV_RULE(TOP_DEPTH_CONV let_CONV)
                 (REWRITE_RULE[bytes_def]
                    isSomeDataElement_byte_update)) in
   REWRITE_TAC[isd]) THEN
  FIRST_ASSUM (fun ho ->
    if not (length (fst (strip_forall (concl ho))) = 5) then fail()
    else MATCH_MP_TAC ho) THEN
  REWRITE_TAC[MEM_APPEND; MEM] THEN
  RULE_ASSUM_TRY (REWRITE_RULE[injectivity "heap_element"]) THEN
  SPLIT_ASM_TAC THEN
  REPEAT (FIRST_X_ASSUM (fun e ->
    let c = concl e in
    if not (is_eq c) || not (is_var (lhand c)) then fail() else
    SUBST_ALL_TAC e)) THEN
  TRY (SOLVED (ASM_MESON_TAC[MEM])) THEN
  ASM_MESON_TAC[MEM]);;

(* an insert of a byte array where one was leaves what a value says
   of a thunk *)
let dest_thunk_insert_ByteArray = prove
 (cake_as_vars (fun () ->
    `sptree_lookup ptr refs = SOME (bvlSem_ByteArray fl xs)
     ==> dest_thunk v (insert ptr (ByteArray fl ys) refs) =
         dest_thunk v refs`),
  STRIP_TAC THEN
  CASES_ON_TAC (cake_as_vars (fun () -> `v:dataSem_v`)) THEN
  REWRITE_TAC[dataSem_dest_thunk_def] THEN
  MATCH_REDUCE_TAC THEN TRY (SOLVED (REWRITE_TAC[])) THEN
  ASM_CASES_TAC `a1:num = ptr` THEN
  ASM_REWRITE_TAC[lookup_insert] THEN
  (let ds = [distinctness "option"; distinctness "bvlSem_ref"] in
   REWRITE_TAC (injectivity "option" :: ds @ map GSYM ds)) THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  REWRITE_TAC[SELECT_REFL; EXISTS_UNIQUE_REFL] THEN
  MATCH_REDUCE_TAC THEN REWRITE_TAC[]);;

(* what the insert of a byte array asks of the cell it writes *)
let ByteArray_in_domain = prove
 (cake_as_vars (fun () ->
    `sptree_lookup ptr refs = SOME (bvlSem_ByteArray fl xs)
     ==> (ptr IN domain refs
          ==> ?a b. sptree_lookup ptr refs =
                    SOME (bvlSem_ByteArray a b))`),
  STRIP_TAC THEN DISCH_THEN (K ALL_TAC) THEN
  EXISTS_TAC (cake_as_vars (fun () -> `fl:bool`)) THEN
  EXISTS_TAC (cake_as_vars (fun () -> `xs:(word8)list`)) THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* a byte array has no edge to another reference, so a reference
   that the stack reaches after the update it reached before *)
let reach_refs_update_byte = prove
 (cake_as_vars (fun () ->
    `reachable_refs stack' (insert ptr (ByteArray fl ys) refs) n /\
     sptree_lookup ptr refs = SOME (bvlSem_ByteArray fl xs)
     ==> reachable_refs stack' refs n`),
  STRIP_TAC THEN
  REWRITE_TAC[reachable_refs_def] THEN
  SUBGOAL_THEN (cake_as_vars (fun () ->
    `ref_edge (insert ptr (ByteArray fl ys)
       (refs:((dataSem_v)bvlSem_ref)spt)) = ref_edge refs`))
    (fun e -> FIRST_X_ASSUM (fun rr ->
       if not (hd_is "reachable_refs" (concl rr)) then fail() else
       ACCEPT_TAC (REWRITE_RULE[e]
         (REWRITE_RULE[reachable_refs_def] rr)))) THEN
  REWRITE_TAC[FUN_EQ_THM; ref_edge_def; lookup_insert] THEN
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_REDUCE_TAC THEN REWRITE_TAC[]);;

(* the three transfers that a store into a byte array leaves *)
let BA_trans = prove
 (cake_as_vars (fun () ->
    `sptree_lookup ptr refs = SOME (bvlSem_ByteArray fl xs)
     ==> (!w1 w2. v_inv conf w1 refs
                    (w2,f,tf,ha ++ [Bytes be fl xs ws] ++ hb)
                  ==> v_inv conf w1
                        (insert ptr (ByteArray fl ys) refs)
                        (w2,f,tf,ha ++ [Bytes be fl ys ws] ++ hb)) /\
         (!w. dest_thunk w refs = NotThunk
              ==> dest_thunk w (insert ptr (ByteArray fl ys) refs) =
                  NotThunk) /\
         (!m. ~(m = ptr)
              ==> sptree_lookup m
                    (insert ptr (ByteArray fl ys) refs) =
                  sptree_lookup m refs)`),
  DISCH_THEN (fun lk ->
    REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN
      DISCH_THEN (fun vi ->
        MATCH_ACCEPT_TAC (MATCH_MP v_inv_ByteArray_insert
          (CONJ (MATCH_MP v_inv_IMP vi)
            (MATCH_MP ByteArray_in_domain lk))));
      GEN_TAC THEN
      REWRITE_TAC[MATCH_MP dest_thunk_insert_ByteArray lk] THEN
      DISCH_THEN ACCEPT_TAC;
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[lookup_insert]]));;
