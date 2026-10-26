(* tools/wip-update_ref.ml: the lemmas that the proof of
   update_ref_thm of data_to_word_memoryProof needs, each proved in
   the session and waiting for the proof itself.  Nothing loads this
   file: it goes into the EXTRA_BEFORE block of the statement when
   the proof is done, and this file is deleted then. *)

let LIST_REL_APPEND_IMP = prove
 (`!(P:A->B->bool) xs ys xs1 ys1.
     EVERY2 P (xs ++ xs1) (ys ++ ys1) /\ LENGTH xs = LENGTH ys
     ==> EVERY2 P xs ys /\ EVERY2 P xs1 ys1`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[APPEND; LENGTH] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(ys:B list) = []` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TRY (REWRITE_RULE[APPEND]) THEN
    ASM_REWRITE_TAC[APPEND; ALL2_DEF];
    REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(ISPEC `ys:B list` (cases_of `:(B)list`)) THEN
    REWRITE_TAC[APPEND; LENGTH; ALL2_DEF; HD; TL; NOT_CONS_NIL;
                NOT_SUC; SUC_INJ] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let EVERY2_MEM_MONO = prove
 (`!(P:A->B->bool) Q l1 l2.
     (!x y. MEM (x,y) (ZIP l1 l2) /\ P x y ==> Q x y) /\
     EVERY2 P l1 l2 ==> EVERY2 Q l1 l2`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` (cases_of `:(B)list`)) THEN
  REWRITE_TAC[ZIP; ALL2_DEF; MEM; HD; TL; NOT_CONS_NIL;
              PAIR_EQ] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let reach_refptr = prove
 (cake_as_vars (fun () ->
    `MEM (RefPtr b ptr) stack' ==> reachable_refs stack' refs ptr`),
  REWRITE_TAC[reachable_refs_def] THEN STRIP_TAC THEN
  EXISTS_TAC (cake_as_vars (fun () -> `RefPtr b ptr:dataSem_v`)) THEN
  EXISTS_TAC `ptr:num` THEN
  ASM_REWRITE_TAC[get_refs_def; MEM] THEN
  MESON_TAC[RTC_RULES]);;

let roots_ok_iso = prove
 (`roots_ok roots heap /\
   (!a. isSomeDataElement (heap_lookup a heap2) =
        isSomeDataElement (heap_lookup a heap))
   ==> roots_ok roots heap2`,
  REWRITE_TAC[roots_ok_def] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let heap_ok_store_ref = prove
 (`heap_ok heap limit' /\ roots_ok (rs ++ (r :: roots2)) heap /\
   (!a. isSomeDataElement (heap_lookup a heap2) =
        isSomeDataElement (heap_lookup a heap)) /\
   heap_length heap2 = heap_length heap /\
   FILTER isForwardPointer heap2 = FILTER isForwardPointer heap /\
   (!xs l d. MEM (DataElement xs l d) heap2
             ==> (DataElement xs l d = RefBlock rs) \/
                 MEM (DataElement xs l d) heap)
   ==> heap_ok heap2 limit'`,
  REWRITE_TAC[heap_ok_def] THEN STRIP_TAC THEN
  SPLIT_ASM_TAC THEN
  REPEAT CONJ_TAC THEN TRY (SOLVED (ASM_REWRITE_TAC[])) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  W(fun gl ->
    let mm = the_asm (fun c ->
      let bd = snd (strip_forall c) in
      is_imp bd && is_disj (rand bd)) gl in
    let mh = the_asm (fun c -> hd_is "MEM" c &&
      hd_is "DataElement" (el 0 (snd (strip_comb c)))) gl in
    STRIP_ASSUME_TAC (MATCH_MP (SPEC_ALL mm) mh)) THENL
   [(* the element written: its pointers are roots of their own *)
    RULE_ASSUM_TRY (REWRITE_RULE[RefBlock_def;
                                 injectivity "heap_element"]) THEN
    SPLIT_ASM_TAC THEN
    REPEAT (FIRST_X_ASSUM (fun e ->
      let c = concl e in
      if not (is_eq c) || not (is_var (lhand c)) then fail() else
      SUBST_ALL_TAC e)) THEN
    W(fun gl ->
      let m = the_asm (fun c -> hd_is "MEM" c &&
        hd_is "gc_shared_Pointer" (el 0 (snd (strip_comb c)))) gl in
      let ro = REWRITE_RULE[roots_ok_def]
                 (the_asm (hd_is "roots_ok") gl) in
      MP_TAC ro THEN MP_TAC m) THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN
    REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[];
    (* an old element of a heap that was good *)
    W(fun gl ->
      let ho = the_asm (fun c ->
        length (fst (strip_forall c)) = 5) gl in
      let md = the_asm (fun c -> hd_is "MEM" c &&
        hd_is "DataElement" (el 0 (snd (strip_comb c)))) gl in
      let mp = the_asm (fun c -> hd_is "MEM" c &&
        hd_is "gc_shared_Pointer" (el 0 (snd (strip_comb c)))) gl in
      ACCEPT_TAC (MATCH_MP ho (CONJ md mp)))]);;

let unused_store_ref = prove
 (`unused_space_inv a l heap /\ RefBlock_inv heap heap2 /\
   heap_length heap2 = heap_length heap /\
   heap_store p [RefBlock rs] heap = (heap2,T)
   ==> unused_space_inv a l heap2`,
  REWRITE_TAC[unused_space_inv_def] THEN STRIP_TAC THEN
  SPLIT_ASM_TAC THEN
  REPEAT CONJ_TAC THEN TRY (SOLVED (ASM_REWRITE_TAC[])) THENL
   [(* the unused element is not a reference, so it is still there *)
    DISCH_TAC THEN
    FIRST_X_ASSUM (fun ri ->
      if not (hd_is "RefBlock_inv" (concl ri)) then fail() else
      MATCH_MP_TAC (CONJUNCT1 (REWRITE_RULE[RefBlock_inv_def] ri))) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[isRefBlock_def; RefBlock_def] THEN
      REWRITE_TAC[distinctness "heap_element"] THEN MESON_TAC[]];
    (* and the data before it is still data *)
    W(fun gl ->
      let du = the_asm (hd_is "data_up_to") gl in
      let st = the_asm (fun c -> is_eq c &&
                 hd_is "heap_store" (lhand c)) gl in
      let y = lhand (el 1 (snd (strip_comb (lhand (concl st))))) in
      SUBGOAL_THEN (list_mk_icomb "isDataElement" [y])
        (fun isd -> ACCEPT_TAC (MATCH_MP data_up_to_heap_store
          (CONJ du (CONJ st isd)))) THEN
      REWRITE_TAC[isDataElement_def; RefBlock_def] THEN
      MESON_TAC[])]);;

let DRESTRICT_DEF = prove
 (`!(fm:(A,B)fmap) s.
     FDOM (DRESTRICT fm s) = FDOM fm INTER s /\
     (!x. x IN s ==> FAPPLY (DRESTRICT fm s) x = FAPPLY fm x)`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[FDOM; FMAP_FN_DRESTRICT; EXTENSION; IN_INTER;
                IN_ELIM_THM] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[fmap_apply; FMAP_FN_DRESTRICT] THEN
    ASM_REWRITE_TAC[]]);;

let domain_insert = prove
 (`!k (v:A) t. domain (sptree_insert k v t) = k INSERT domain t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; domain_lookup; IN_INSERT; lookup_insert] THEN
  GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  MESON_TAC[]);;

let INJ_SUBSET_DOM = prove
 (`!(g:A->B) s t u. INJ g s u /\ t SUBSET s ==> INJ g t u`,
  REWRITE_TAC[INJ; SUBSET] THEN MESON_TAC[]);;

let INJ_DRESTRICT = prove
 (`!(tf:(A,B)fmap) s P.
     INJ (FAPPLY tf) (FDOM tf) s
     ==> INJ (FAPPLY (DRESTRICT tf P)) (FDOM (DRESTRICT tf P)) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[INJ; (CONJUNCT1 o SPEC_ALL) DRESTRICT_DEF;
              IN_INTER] THEN
  STRIP_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[(CONJUNCT2 o SPEC_ALL) DRESTRICT_DEF] THEN
  ASM_MESON_TAC[(CONJUNCT2 o SPEC_ALL) DRESTRICT_DEF]);;

let mem_zip_left = prove
 (`!(l1:A list) (l2:B list) x y.
     LENGTH l1 = LENGTH l2 /\ MEM (x,y) (ZIP l1 l2) ==> MEM x l1`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `l2:B list` THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` (cases_of `:(B)list`)) THEN
  REWRITE_TAC[ZIP; MEM; PAIR_EQ; LENGTH; NOT_SUC;
              ARITH_RULE `~(0 = SUC n)`; SUC_INJ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let v_inv_update_ref = prove
 (cake_as_vars (fun () ->
    `RefBlock_inv heap heap2 /\
     sptree_lookup ptr refs = SOME (bvlSem_ValueArray as1) /\
     v_inv conf v1 refs (v2,f,tf,heap) /\ MEM v1 stack'
     ==> v_inv conf v1 (insert ptr (ValueArray xs) refs)
           (v2,f,
            DRESTRICT tf (all_ts (insert ptr (ValueArray xs) refs)
                            stack'),heap2)`),
  STRIP_TAC THEN
  MATCH_MP_TAC v_inv_tf_restrict THEN
  EXISTS_TAC (cake_as_vars (fun () -> `stack':(dataSem_v)list`)) THEN
  REPEAT CONJ_TAC THENL
   [(* the value in the new references and heap *)
    MATCH_MP_TAC v_inv_ValueArray_insert THEN
    W(fun gl ->
      let ri = the_asm (hd_is "RefBlock_inv") gl in
      EXISTS_TAC (el 0 (snd (strip_comb (concl ri))))) THEN
    REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
    ASM_MESON_TAC[];
    (* its timestamps are timestamps of the stack *)
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (GEN_ALL MEM_in_all_ts) THEN
    EXISTS_TAC (cake_as_vars (fun () -> `v1:dataSem_v`)) THEN
    CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC MEM_stack_all_vs THEN FIRST_ASSUM ACCEPT_TAC;
    (* and the ones of the stack are kept *)
    REWRITE_TAC[]]);;

let MEM_ref_all_vs = prove
 (cake_as_vars (fun () ->
    `sptree_lookup n refs = SOME (bvlSem_ValueArray l) /\ MEM v l
     ==> v IN all_vs refs stack'`),
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN
  REPEAT DISJ1_TAC THEN
  EXISTS_TAC `n:num` THEN
  EXISTS_TAC (cake_as_vars (fun () -> `l:(dataSem_v)list`)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEM_v_all_vs THEN FIRST_ASSUM ACCEPT_TAC);;

let v_inv_update_ref_ref = prove
 (cake_as_vars (fun () ->
    `RefBlock_inv heap heap2 /\
     sptree_lookup ptr refs = SOME (bvlSem_ValueArray as1) /\
     v_inv conf v1 refs (v2,f,tf,heap) /\
     sptree_lookup m (insert ptr (ValueArray xs) refs) =
       SOME (ValueArray l) /\
     MEM v1 l
     ==> v_inv conf v1 (insert ptr (ValueArray xs) refs)
           (v2,f,
            DRESTRICT tf (all_ts (insert ptr (ValueArray xs) refs)
                            stack'),heap2)`),
  STRIP_TAC THEN
  MATCH_MP_TAC v_inv_tf_restrict THEN
  EXISTS_TAC (cake_as_vars (fun () -> `stack':(dataSem_v)list`)) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC v_inv_ValueArray_insert THEN
    W(fun gl ->
      let ri = the_asm (hd_is "RefBlock_inv") gl in
      EXISTS_TAC (el 0 (snd (strip_comb (concl ri))))) THEN
    REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (GEN_ALL MEM_in_all_ts) THEN
    EXISTS_TAC (cake_as_vars (fun () -> `v1:dataSem_v`)) THEN
    CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC (GEN_ALL MEM_ref_all_vs) THEN
    W(fun gl ->
      let lk = the_asm (fun c -> is_eq c &&
                 hd_is "sptree_lookup" (lhand c) &&
                 can (fun t -> hd_is "bvlSem_ValueArray" (rand t))
                   (rand c) &&
                 hd_is "sptree_insert" (rand (lhand c))) gl in
      let args = snd (strip_comb (lhand (concl lk))) in
      EXISTS_TAC (el 0 args) THEN
      EXISTS_TAC (rand (rand (rand (concl lk))))) THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[]]);;
