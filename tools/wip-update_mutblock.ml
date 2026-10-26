(* tools/wip-update_mutblock.ml: the lemmas that the proof of
   update_mutblock_thm of data_to_word_memoryProof needs, each
   proved in a session and waiting for the proof itself.  Nothing
   loads this file: the lemmas go into the EXTRA_BEFORE block of
   the statement when the proof is done, and LUPDATE_LENGTH into
   ml/lib/lemmas.ml with the other three theorems of HOL4's
   listTheory about LUPDATE; this file is deleted then.

   What is still to write is the proof itself, which is the one of
   update_thunk_thm with a mutable block for the thunk; PLAN.md
   says what differs. *)

(* HOL4 listTheory: the update of the element past a prefix *)
let LUPDATE_LENGTH = prove
 (`!(l:A list) x y r. LUPDATE x (LENGTH l) (l ++ (y :: r)) =
                      l ++ (x :: r)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; APPEND; LUPDATE; SUC_SUB1; NOT_SUC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(SUC n = 0)`]);;

(* HOL4 data_to_word_memoryProofScript.sml: the theorem that HOL4
   states as the value of an ML expression, which is the lemma with
   the counter of the induction generalised away *)
let v_inv_BlockRep_upd =
  let ckv,_ = dest_forall (concl v_inv_BlockRep_upd_lemma) in
  GEN_ALL (DISCH_ALL (REWRITE_RULE[GSYM v_inv_eq]
    (GEN ckv (UNDISCH (SPEC_ALL v_inv_BlockRep_upd_lemma)))));;

(* an insert of a mutable block where one was leaves what a value
   says of a thunk *)
let dest_thunk_insert_MutBlock = prove
 (cake_as_vars (fun () ->
    `sptree_lookup ptr refs = SOME (bvlSem_MutBlock tag fin l cv r)
     ==> dest_thunk v (insert ptr (MutBlock tag fin2 l h r) refs) =
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

(* the pointers of the element that an update of one value writes:
   the pointer put in, or one that the element had *)
let ptrs_store_el = prove
 (`heap_ok heap limit' /\
   (!pt u. w = gc_shared_Pointer pt u
           ==> isSomeDataElement (heap_lookup pt heap)) /\
   heap_lookup p heap = SOME (DataElement zs l2 d2)
   ==> (!pt u. MEM (gc_shared_Pointer pt u) (LUPDATE w i zs)
               ==> isSomeDataElement (heap_lookup pt heap))`,
  REWRITE_TAC[heap_ok_def] THEN STRIP_TAC THEN
  SPLIT_ASM_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM (fun m ->
    if not (hd_is "MEM" (concl m)) then fail() else
    STRIP_ASSUME_TAC (MATCH_MP MEM_LUPDATE_E m)) THENL
   [(* the pointer written *)
    W(fun gl ->
      let pw = the_asm (fun c ->
                 let vs,bd = strip_forall c in
                 length vs = 2 && is_imp bd &&
                 hd_is "isSomeDataElement" (rand bd)) gl in
      let eq = the_asm (fun c -> is_eq c &&
                 hd_is "gc_shared_Pointer" (lhand c)) gl in
      ACCEPT_TAC (MATCH_MP pw (SYM eq)));
    (* a pointer of the element, which was in a good heap *)
    W(fun gl ->
      let ho = the_asm (fun c ->
        length (fst (strip_forall c)) = 5) gl in
      let hl = the_asm (fun c -> is_eq c &&
                 hd_is "heap_lookup" (lhand c)) gl in
      let md = MATCH_MP heap_lookup_MEM hl in
      let mp = the_asm (fun c -> hd_is "MEM" c &&
                 hd_is "gc_shared_Pointer"
                   (el 0 (snd (strip_comb c)))) gl in
      ACCEPT_TAC (MATCH_MP ho (CONJ md mp)))]);;

(* the three transfers that an update of the hole of a mutable
   block leaves: over the heap (v_inv_BlockRep_upd, which asks that
   no timestamp points at the cell) and over the references
   (v_inv_MutBlock_hole) *)
let MB_trans = prove
 (cake_as_vars (fun () ->
    `heap_lookup p heap = SOME (BlockRep tag zs) /\
     (!t. t IN FDOM (tf:(num,num)fmap) ==> ~(FAPPLY tf t = p)) /\
     (!m y. ~(m = p) /\ heap_lookup m heap = SOME y
            ==> heap_lookup m heap2 = SOME y) /\
     sptree_lookup ptr refs = SOME (bvlSem_MutBlock tag2 fin l cv r)
     ==> (!w1 w2. v_inv conf w1 refs (w2,f,tf,heap)
                  ==> v_inv conf w1
                        (insert ptr (MutBlock tag2 fin2 l h r) refs)
                        (w2,f,tf,heap2)) /\
         (!w. dest_thunk w refs = NotThunk
              ==> dest_thunk w (insert ptr
                    (MutBlock tag2 fin2 l h r) refs) = NotThunk) /\
         (!m. ~(m = ptr)
              ==> sptree_lookup m
                    (insert ptr (MutBlock tag2 fin2 l h r) refs) =
                  sptree_lookup m refs)`),
  DISCH_THEN (fun hs ->
    let hl = CONJUNCT1 hs in
    let tfc = CONJUNCT1 (CONJUNCT2 hs) in
    let tr = CONJUNCT1 (CONJUNCT2 (CONJUNCT2 hs)) in
    let lk = CONJUNCT2 (CONJUNCT2 (CONJUNCT2 hs)) in
    REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN
      DISCH_THEN (fun vi ->
        MATCH_ACCEPT_TAC (MATCH_MP v_inv_MutBlock_hole
          (CONJ (MATCH_MP v_inv_BlockRep_upd
                   (CONJ vi (CONJ hl (CONJ tfc tr)))) lk)));
      GEN_TAC THEN
      REWRITE_TAC[MATCH_MP dest_thunk_insert_MutBlock lk] THEN
      DISCH_THEN ACCEPT_TAC;
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[lookup_insert]]));;

(* the invariant of the reference written when the hole of a
   mutable block is filled: the element is the one stored, and its
   values are the old ones with the value put in its place *)
let bc_ref_inv_update_mutblock_at = prove
 (cake_as_vars (fun () ->
    `FLOOKUP (f:(num,num)fmap) ptr = SOME p /\
     heap_lookup p heap2 =
       SOME (BlockRep tag (LUPDATE rr (LENGTH l) zs)) /\
     sptree_lookup ptr refs = SOME (bvlSem_MutBlock tag F l cv r) /\
     EVERY2 (\z y. v_inv conf y refs (z,f,tf,heap)) zs
       (l ++ [cv] ++ r) /\
     v_inv conf h refs (rr,f,tf,heap) /\
     (!gs. ~(data_to_word_config_gc_kind conf =
             data_to_word_Generational gs)) /\
     ~(p IN IMAGE (FAPPLY (tf:(num,num)fmap)) (FDOM tf)) /\
     (!w1 w2. v_inv conf w1 refs (w2,f,tf,heap)
              ==> v_inv conf w1
                    (insert ptr (MutBlock tag F l h r) refs)
                    (w2,f,tf,heap2)) /\
     (!v. MEM v (l ++ [h] ++ r)
          ==> v IN all_vs (insert ptr (MutBlock tag F l h r) refs)
                    stack')
     ==> bc_ref_inv conf ptr
           (insert ptr (MutBlock tag F l h r) refs)
           (f,DRESTRICT tf
                (all_ts (insert ptr (MutBlock tag F l h r) refs)
                   stack'),heap2,be')`),
  STRIP_TAC THEN
  (* the new references hold the block with the hole filled *)
  W(fun (asl,w) ->
    let ins = find_term (hd_is "sptree_insert") w in
    let args = snd (strip_comb ins) in
    SUBGOAL_THEN
      (mk_eq (list_mk_icomb "sptree_lookup" [el 0 args; ins],
              list_mk_icomb "SOME" [el 1 args]))
      ASSUME_TAC THENL
     [REWRITE_TAC[lookup_insert]; ALL_TAC]) THEN
  (* which is the arm of a mutable block *)
  W(fun (asl,w as gl) ->
    let lk1 = the_asm (fun c -> is_eq c &&
                hd_is "FLOOKUP" (lhand c)) gl in
    let ins = find_term (hd_is "sptree_insert") w in
    REWRITE_TAC[MATCH_MP arm_MB (CONJ lk1 (a_lkref ins gl))]) THEN
  REPEAT CONJ_TAC THEN
  TRY (SOLVED (FIRST_ASSUM ACCEPT_TAC)) THEN
  (* no timestamp points at the cell, and the map only shrinks *)
  TRY (SOLVED
        (W(fun gl ->
           let nim = the_asm (fun c -> is_neg c &&
                       hd_is "IN" (rand c)) gl in
           MATCH_ACCEPT_TAC
             (MATCH_MP IMAGE_DRESTRICT_NOT nim)))) THEN
  (* the element is the one stored, and its values are the old ones
     with the value put in the place of the hole *)
  W(fun (asl,w as gl) ->
    let hl = the_asm (fun c -> is_eq c &&
               hd_is "heap_lookup" (lhand c)) gl in
    let lup = rand (rand (rand (concl hl))) in
    let old = the_asm (fun c -> hd_is "ALL2" c) gl in
    let oargs = snd (strip_comb (concl old)) in
    let vi = the_asm (hd_is "v_inv") gl in
    let vargs = snd (strip_comb (concl vi)) in
    let i = el 1 (snd (strip_comb lup)) in
    let hv = el 1 vargs in
    let newys = list_mk_icomb "LUPDATE" [hv; i; el 2 oargs] in
    let bod = snd (strip_exists w) in
    let goalys = el 2 (snd (strip_comb (rand bod))) in
    EXISTS_TAC lup THEN
    CONJ_TAC THENL
     [ACCEPT_TAC hl;
      SUBGOAL_THEN (mk_eq (goalys,newys))
        (fun e -> ONCE_REWRITE_TAC[e]) THENL
       [REWRITE_TAC[APPEND; LUPDATE_LENGTH];
        ALL_TAC] THEN
      W(fun (asl,w as gl) ->
        let th = CONV_RULE(TOP_DEPTH_CONV BETA_CONV)
                   (ISPECL [el 0 oargs; el 1 oargs; el 2 oargs; i;
                            el 0 (tparts (el 3 vargs)); hv]
                      EVERY2_LUPDATE_same) in
        let old2 = MATCH_MP th (CONJ vi old) in
        let mem = ONCE_REWRITE_RULE[ASSUME (mk_eq (goalys,newys))]
                    (the_asm (fun c ->
                       length (fst (strip_forall c)) = 1 &&
                       is_imp (snd (strip_forall c)) &&
                       hd_is "MEM" (lhand (snd (strip_forall c))))
                       gl) in
        ACCEPT_TAC (MATCH_MP EVERY2_v_inv_update_gen
          (CONJ (a_vtr gl) (CONJ mem old2))))]));;
