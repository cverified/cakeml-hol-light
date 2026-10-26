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

(* the halves of the split after a store above the first one: the
   second half is the old one with the element replaced, so it is
   still all references (HOL4 does this inline, with
   heap_split_length of gen_gc_partialTheory) *)

let heap_split_store_ref = prove
 (`heap_split k heap = SOME (h1,h2) /\
   heap_lookup p heap = SOME (RefBlock zs) /\
   ~(p < k) /\ LENGTH rs = LENGTH zs /\
   heap_store p [RefBlock rs] heap = (heap2,T) /\
   EVERY isRef h2
   ==> (?h3. heap_split k heap2 = SOME (h1,h3) /\ EVERY isRef h3)`,
  STRIP_TAC THEN
  (* the heap is its two halves, and the first is of the length *)
  FIRST_ASSUM (fun hs ->
    if not (is_eq (concl hs)) ||
       not (hd_is "heap_split" (lhand (concl hs))) then fail() else
    STRIP_ASSUME_TAC (MATCH_MP heap_split_heap_length hs)) THEN
  FIRST_X_ASSUM (fun e ->
    let c = concl e in
    if not (is_eq c) || not (hd_is "APPEND" (lhand c)) ||
       not (is_var (rand c)) then fail() else
    SUBST_ALL_TAC (SYM e)) THEN
  (* so the element written is in the second half *)
  FIRST_X_ASSUM (fun hl ->
    let c = concl hl in
    if not (is_eq c) || not (hd_is "heap_lookup" (lhand c))
    then fail() else
    ASSUME_TAC (REWRITE_RULE[heap_lookup_APPEND] hl)) THEN
  ASM_FS_TAC THEN
  (* and the second half splits there *)
  W(fun gl ->
    let hl2 = the_asm (fun c -> is_eq c &&
                hd_is "heap_lookup" (lhand c) &&
                hd_is "SOME" (rand c)) gl in
    STRIP_ASSUME_TAC (MATCH_MP heap_lookup_SPLIT hl2)) THEN
  REPEAT (FIRST_X_ASSUM (fun e ->
    let c = concl e in
    if not (is_eq c) || not (is_var (lhand c)) then fail() else
    SUBST_ALL_TAC e)) THEN
  (* the address written is the length of what lies before it *)
  W(fun gl ->
    let e = the_asm (fun c -> is_eq c &&
              hd_is "-" (lhand c) &&
              hd_is "heap_length" (rand c)) gl in
    let ha = rand (rand (concl e)) in
    let hl1 = the_asm (fun c -> is_eq c &&
                hd_is "heap_length" (lhand c) &&
                not (hd_is "APPEND" (rand (lhand c)))) gl in
    let h1 = rand (lhand (concl hl1)) in
    let p = lhand (lhand (concl e)) in
    SUBGOAL_THEN (mk_eq (p, list_mk_icomb "heap_length"
                              [list_mk_icomb "APPEND" [h1; ha]]))
      ASSUME_TAC THENL
     [REWRITE_TAC[heap_length_APPEND] THEN ASM_ARITH_TAC;
      ALL_TAC]) THEN
  FIRST_X_ASSUM (fun e ->
    let c = concl e in
    if not (is_eq c) || not (is_var (lhand c)) ||
       not (hd_is "heap_length" (rand c)) then fail() else
    SUBST_ALL_TAC e) THEN
  (* so the store writes the new element in the middle *)
  RULE_ASSUM_TRY (REWRITE_RULE[APPEND_ASSOC]) THEN
  RULE_ASSUM_TRY (REWRITE_RULE[heap_store_lemma; PAIR_EQ]) THEN
  SPLIT_ASM_TAC THEN
  REPEAT (FIRST_X_ASSUM (fun e ->
    let c = concl e in
    if not (is_eq c) || not (is_var (rand c)) ||
       not (hd_is "APPEND" (lhand c)) then fail() else
    SUBST_ALL_TAC (SYM e))) THEN
  (* so the split of the new heap keeps the first half *)
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  W(fun gl ->
    let e = the_asm (fun c -> is_eq c &&
              hd_is "heap_length" (lhand c) &&
              is_var (rand (lhand c)) && is_var (rand c)) gl in
    ONCE_REWRITE_TAC[SYM e]) THEN
  REWRITE_TAC[heap_split_length] THEN
  W(fun (asl,w) ->
    let bod = snd (strip_exists w) in
    let sm = rand (lhand (hd (conjuncts bod))) in
    EXISTS_TAC (rand sm)) THEN
  REWRITE_TAC[] THEN
  (* and the second half is the old one with the new element *)
  RULE_ASSUM_TRY (REWRITE_RULE[ALL_APPEND; ALL]) THEN
  REWRITE_TAC[ALL_APPEND; ALL] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[isRef_def; RefBlock_def] THEN
  MATCH_REDUCE_TAC THEN
  REWRITE_TAC[isMutTag_def]);;

(* and so the kind of the collection survives the store *)

let gc_kind_store_ref = prove
 (cake_as_vars (fun () ->
    `gc_kind_inv conf a sp sp1 gens heap /\
     heap_store p [RefBlock rs] heap = (heap2,T) /\
     heap_lookup p heap = SOME (RefBlock zs) /\
     LENGTH rs = LENGTH zs
     ==> gc_kind_inv conf a sp sp1 gens heap2`),
  REWRITE_TAC[gc_kind_inv_def] THEN STRIP_TAC THEN
  W(fun (asl,w) ->
    CASES_ON_TAC (find_term
      (hd_is "data_to_word_config_gc_kind") w)) THEN
  RULE_ASSUM_TRY (CONV_RULE(TOP_DEPTH_CONV MATCH_CONV)) THEN
  MATCH_REDUCE_TAC THEN
  TRY (SOLVED (FIRST_ASSUM ACCEPT_TAC)) THEN
  SPLIT_ASM_TAC THEN
  FIRST_X_ASSUM (fun ex ->
    if not (is_exists (concl ex)) then fail() else
    STRIP_ASSUME_TAC ex) THEN
  (* a RefBlock is a reference, so the element written is not in
     the half of the split that holds none *)
  W(fun (asl,w as gl) ->
    let hs = the_asm (fun c -> is_eq c &&
               hd_is "heap_split" (lhand c)) gl in
    let hl = the_asm (fun c -> is_eq c &&
               hd_is "heap_lookup" (lhand c)) gl in
    let k = el 0 (snd (strip_comb (lhand (concl hs)))) in
    let p = el 0 (snd (strip_comb (lhand (concl hl)))) in
    SUBGOAL_THEN (mk_neg (mk_binop `(<):num->num->bool` p k))
      ASSUME_TAC THENL
     [DISCH_TAC THEN
      MP_TAC (MATCH_MP heap_lookup_heap_split (CONJ hs hl)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      W(fun (asl,w as gl) ->
        let m = the_asm (hd_is "MEM") gl in
        let ev = the_asm (fun c -> hd_is "ALL" c &&
                   el 1 (snd (strip_comb c)) = rand (concl m)) gl in
        MP_TAC (MATCH_MP (REWRITE_RULE[GSYM ALL_MEM] ev) m)) THEN
      REWRITE_TAC[isRef_def; RefBlock_def] THEN
      MATCH_REDUCE_TAC THEN
      REWRITE_TAC[isMutTag_def];
      ALL_TAC]) THEN
  CONJ_TAC THENL
   [(* the generation state: the store is above the nursery *)
    W(fun gl ->
      let st = the_asm (fun c -> is_eq c &&
                 hd_is "heap_store" (lhand c)) gl in
      let gs = the_asm (hd_is "gen_state_ok") gl in
      let p = el 0 (snd (strip_comb (lhand (concl st)))) in
      let a = el 0 (snd (strip_comb (concl gs))) in
      SUBGOAL_THEN (mk_binop `(<=):num->num->bool` a p)
        (fun le -> MATCH_ACCEPT_TAC
          (MATCH_MP update_ref_gen_state_ok
            (CONJ st (CONJ le gs)))) THEN
      POP_ASSUM_LIST (fun l -> MAP_EVERY ASSUME_TAC (filter
        (fun t -> let c = concl t in
           hd_is "<" c || (is_neg c && hd_is "<" (rand c)) ||
           hd_is "<=" c) l)) THEN
      ASM_ARITH_TAC);
    (* and the two halves of the new heap *)
    W(fun gl ->
      let hs = the_asm (fun c -> is_eq c &&
                 hd_is "heap_split" (lhand c)) gl in
      let hl = the_asm (fun c -> is_eq c &&
                 hd_is "heap_lookup" (lhand c)) gl in
      let nlt = the_asm (fun c -> is_neg c && hd_is "<" (rand c)) gl in
      let len = the_asm (fun c -> is_eq c &&
                  hd_is "LENGTH" (lhand c)) gl in
      let st = the_asm (fun c -> is_eq c &&
                 hd_is "heap_store" (lhand c)) gl in
      let h2 = rand (rand (rand (concl hs))) in
      let ev = the_asm (fun c -> hd_is "ALL" c &&
                 el 1 (snd (strip_comb c)) = h2) gl in
      STRIP_ASSUME_TAC (MATCH_MP heap_split_store_ref
        (CONJ hs (CONJ hl (CONJ nlt (CONJ len (CONJ st ev))))))) THEN
    W(fun gl ->
      let hs2 = the_asm (fun c -> is_eq c &&
                  hd_is "heap_split" (lhand c) &&
                  hd_is "SOME" (rand c)) gl in
      EXISTS_TAC (lhand (rand (rand (concl hs2)))) THEN
      EXISTS_TAC (rand (rand (rand (concl hs2))))) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------ *)
(* The proof of update_ref_thm as far as it goes.  What it closes:    *)
(* the split of the roots, the arm of the reference, the store, the   *)
(* five witnesses, and of the new invariant roots_ok, heap_ok,        *)
(* gc_kind_inv, unused_space_inv, the two maps with the timestamps    *)
(* restricted, and the values of the stack.  What is left is the one  *)
(* goal of the arms of the references that the stack reaches (HOL4    *)
(* data_to_word_memoryProofScript.sml:4845 onwards): for the          *)
(* reference written it takes the new roots, and for another one it   *)
(* keeps its element, because the store only touched the address of   *)
(* the written one -- which needs the four arms, the INJ of f for     *)
(* the two addresses being different, and a dest_thunk that an        *)
(* insert of a ValueArray does not change.                           *)
(* ------------------------------------------------------------------ *)

(*
let _ = bt "update_ref_thm" update_ref_thm
 (fun () ->
  STRIP_TAC THEN
  (* what the invariant says of the stack with the pointer in it *)
  FIRST_X_ASSUM (fun inv ->
    if not (hd_is "abs_ml_inv" (concl inv)) then fail() else
    STRIP_ASSUME_TAC (REWRITE_RULE[abs_ml_inv_def;
                                   bc_stack_ref_inv_def] inv)) THEN
  (* the roots split where the pointer is *)
  FIRST_ASSUM (fun lr ->
    if not (hd_is "ALL2" (concl lr)) then fail() else
    STRIP_ASSUME_TAC (MATCH_MP EVERY2_APPEND_CONS lr)) THEN
  RULE_ASSUM_TRY (CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
  (* and the root of the pointer is the address of its reference *)
  FIRST_ASSUM (fun vr ->
    let c = concl vr in
    if not (hd_is "v_inv" c) ||
       not (hd_is "dataSem_RefPtr" (el 1 (snd (strip_comb c)))) then fail()
    else STRIP_ASSUME_TAC (REWRITE_RULE[v_inv_def] vr)) THEN
  RULE_ASSUM_TRY (REWRITE_RULE ref_rws) THEN
  ASM_FS_TAC THEN
  RULE_ASSUM_TRY (REWRITE_RULE ref_rws) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  SPLIT_ASM_TAC THEN
  (* the reference has an address, and it is reachable, so the
     invariant holds of it *)
  SUBGOAL_THEN (cake_as_vars (fun () ->
    `FLOOKUP (f:(num,num)fmap) (ptr:num) = SOME (FAPPLY f ptr:num)`))
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FLOOKUP_DEF]; ALL_TAC] THEN
  SUBGOAL_THEN (cake_as_vars (fun () ->
    `reachable_refs (xs ++ (RefPtr b ptr :: stack)) refs ptr`))
    ASSUME_TAC THENL
   [FIRST
     [SOLVED (MATCH_MP_TAC (GEN_ALL reach_refptr) THEN
              REWRITE_TAC[MEM_APPEND; MEM]);
      SOLVED (MATCH_MP_TAC (GEN_ALL reach_refptr) THEN
              EXISTS_TAC `b:bool` THEN
              REWRITE_TAC[MEM_APPEND; MEM]);
      SOLVED (REWRITE_TAC[reachable_refs_def] THEN
              EXISTS_TAC (cake_as_vars (fun () ->
                `RefPtr b ptr:dataSem_v`)) THEN
              EXISTS_TAC `ptr:num` THEN
              REWRITE_TAC[MEM_APPEND; MEM; get_refs_def] THEN
              MESON_TAC[RTC_RULES])];
    ALL_TAC] THEN
  FIRST_ASSUM (fun bri ->
    let bd = snd (strip_forall (concl bri)) in
    if not (is_imp bd) || not (hd_is "bc_ref_inv" (rand bd))
    then fail() else MP_TAC (SPEC `ptr:num` bri)) THEN
  (ANTS_TAC THENL
    [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  (* which is the arm of a ValueArray *)
  W(fun gl ->
    let lk1 = the_asm (fun c -> is_eq c &&
                hd_is "FLOOKUP" (lhand c)) gl in
    let lk2 = the_asm (fun c -> is_eq c &&
                hd_is "sptree_lookup" (lhand c)) gl in
    DISCH_THEN (fun inv ->
      STRIP_ASSUME_TAC
        (REWRITE_RULE[MATCH_MP arm_VA (CONJ lk1 lk2)] inv))) THEN
  (* the lengths of the array, of its values and of their roots *)
  ASSUM_LIST (fun l -> MAP_EVERY ASSUME_TAC
    (mapfilter (MATCH_MP LIST_REL_LENGTH) l)) THEN
  (* the store of the new values into the reference *)
  W(fun gl ->
    let sp = the_asm (fun c -> is_eq c &&
               hd_is "APPEND" (rand c)) gl in
    let t1 = lhand (rand (concl sp)) in
    let hl = the_asm (fun c -> is_eq c &&
               hd_is "heap_lookup" (lhand c) &&
               can (fun t -> hd_is "RefBlock" (rand t)) (rand c)) gl in
    let zs = rand (rand (rand (concl hl))) in
    SUBGOAL_THEN (mk_eq (list_mk_icomb "LENGTH" [zs],
                         list_mk_icomb "LENGTH" [t1]))
      (fun le -> STRIP_ASSUME_TAC
        (MATCH_MP heap_store_RefBlock (CONJ le hl)) THEN
        ASSUME_TAC le THEN ASSUME_TAC (SYM le)) THENL
     [POP_ASSUM_LIST (fun l -> MAP_EVERY ASSUME_TAC (filter
        (fun t -> let c = concl t in
           is_eq c && (hd_is "LENGTH" (lhand c) ||
                       hd_is "LENGTH" (rand c))) l)) THEN
      ASM_ARITH_TAC;
      ALL_TAC]) THEN
  (* the witnesses: the address of the reference, the roots of the
     new values, the rest of the roots and the new heap *)
  W(fun gl ->
    let sp = the_asm (fun c -> is_eq c &&
               hd_is "APPEND" (rand c)) gl in
    let t1 = lhand (rand (concl sp)) in
    let t2 = rand (rand (rand (concl sp))) in
    let pt = the_asm (fun c -> is_eq c &&
               hd_is "gc_shared_Pointer" (rand c)) gl in
    let p = lhand (rand (concl pt)) in
    let u = rand (rand (concl pt)) in
    let st = the_asm (fun c -> is_eq c &&
               hd_is "heap_store" (lhand c)) gl in
    let h2 = lhand (rand (concl st)) in
    MAP_EVERY EXISTS_TAC [p; t1; t2; h2; u]) THEN
  REPEAT CONJ_TAC THEN
  TRY (SOLVED (ASM_REWRITE_TAC[])) THEN
  (* and the invariant of the new heap and references *)
  REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN
  REPEAT CONJ_TAC THEN TRY (SOLVED (ASM_REWRITE_TAC[])) THEN
  (* the roots and the heap are as good as they were *)
  (* the roots are the ones of the split *)
  W(fun gl ->
    let sp = the_asm (fun c -> is_eq c &&
               hd_is "APPEND" (rand c)) gl in
    ONCE_REWRITE_TAC[sp]) THEN
  TRY (SOLVED
        (W(fun gl ->
           let iso = the_asm (fun c ->
             let bd = snd (strip_forall c) in
             is_eq bd && hd_is "isSomeDataElement" (lhand bd)) gl in
           let ro = the_asm (hd_is "roots_ok") gl in
           ACCEPT_TAC (MATCH_MP roots_ok_iso (CONJ ro iso))))) THEN
  TRY (SOLVED
        (W(fun gl ->
           let sp = the_asm (fun c -> is_eq c &&
                      hd_is "APPEND" (rand c)) gl in
           let iso = the_asm (fun c ->
             let bd = snd (strip_forall c) in
             is_eq bd && hd_is "isSomeDataElement" (lhand bd)) gl in
           let ro = REWRITE_RULE[sp] (the_asm (hd_is "roots_ok") gl) in
           let ho = the_asm (hd_is "heap_ok") gl in
           let hlen = the_asm (fun c -> is_eq c &&
                        hd_is "heap_length" (lhand c)) gl in
           let flt = the_asm (fun c -> is_eq c &&
                       hd_is "FILTER" (lhand c)) gl in
           let mm = the_asm (fun c ->
             let bd = snd (strip_forall c) in
             is_imp bd && is_disj (rand bd)) gl in
           ACCEPT_TAC (MATCH_MP heap_ok_store_ref
             (CONJ ho (CONJ ro (CONJ iso (CONJ hlen
               (CONJ flt mm))))))))) THEN
  (* and the unused space is where it was *)
  TRY (SOLVED
        (W(fun gl ->
           let us = the_asm (hd_is "unused_space_inv") gl in
           let ri = the_asm (hd_is "RefBlock_inv") gl in
           let hlen = the_asm (fun c -> is_eq c &&
                        hd_is "heap_length" (lhand c)) gl in
           let st = the_asm (fun c -> is_eq c &&
                      hd_is "heap_store" (lhand c)) gl in
           ACCEPT_TAC (MATCH_MP unused_store_ref
             (CONJ us (CONJ ri (CONJ hlen st))))))) THEN
  (* the kind of the collection: the store is above the nursery and
     writes a reference where one was (gc_kind_store_ref) *)
  TRY (SOLVED
        (W(fun gl ->
           let gk = the_asm (hd_is "gc_kind_inv") gl in
           let st = the_asm (fun c -> is_eq c &&
                      hd_is "heap_store" (lhand c)) gl in
           let hl = the_asm (fun c -> is_eq c &&
                      hd_is "heap_lookup" (lhand c) &&
                      can (fun t -> hd_is "RefBlock" (rand t))
                        (rand c) &&
                      el 1 (snd (strip_comb (lhand c))) =
                        el 2 (snd (strip_comb (lhand (concl st))))) gl in
           let zs = rand (rand (rand (concl hl))) in
           let len = the_asm (fun c -> is_eq c &&
                       hd_is "LENGTH" (lhand c) &&
                       rand c = list_mk_icomb "LENGTH" [zs]) gl in
           MATCH_ACCEPT_TAC (MATCH_MP gc_kind_store_ref
             (CONJ gk (CONJ st (CONJ hl len))))))) THEN
  (* the maps of the new invariant: the addresses are the ones they
     were, and the timestamps are cut to the ones of the new
     references and stack *)
  W(fun (asl,w as gl) ->
    if not (is_exists w) then ALL_TAC else
    (let sub p = rand (lhand (concl (the_asm (fun c ->
       hd_is "SUBSET" c && hd_is p (rand c)) gl))) in
     let ats = find_term (hd_is "all_ts") w in
     EXISTS_TAC (sub "domain") THEN
     EXISTS_TAC (list_mk_icomb "DRESTRICT" [sub "all_ts"; ats]))) THEN
  REPEAT CONJ_TAC THEN TRY (SOLVED (FIRST_ASSUM ACCEPT_TAC)) THEN
  (* the addresses of the maps are the ones of the old heap *)
  TRY (SOLVED
        (W(fun gl ->
           let iso = the_asm (fun c ->
             let bd = snd (strip_forall c) in
             is_eq bd && hd_is "isSomeDataElement" (lhand bd)) gl in
           ONCE_REWRITE_TAC[iso]) THEN
         FIRST [SOLVED (FIRST_ASSUM ACCEPT_TAC);
                SOLVED (W(fun (asl,w as gl) ->
                  let dr = find_term (hd_is "DRESTRICT") w in
                  let inj = the_asm (fun c -> hd_is "INJ" c &&
                    rand (el 0 (snd (strip_comb c))) = lhand dr) gl in
                  MATCH_ACCEPT_TAC
                    (MATCH_MP INJ_DRESTRICT inj)))])) THEN
  (* the domain of the references has the key in it *)
  TRY (SOLVED
        (REWRITE_TAC[domain_insert] THEN
         MATCH_MP_TAC SUBSET_TRANS THEN
         W(fun gl ->
           let su = the_asm (fun c -> hd_is "SUBSET" c &&
                      hd_is "domain" (rand c)) gl in
           EXISTS_TAC (rand (concl su))) THEN
         CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
         SET_TAC[])) THEN
  (* the timestamps of the restricted map are of the stack, and
     below the counter *)
  TRY (SOLVED
        (REWRITE_TAC[(CONJUNCT1 o SPEC_ALL) DRESTRICT_DEF] THEN
         FIRST [SOLVED (REWRITE_TAC[INTER_SUBSET]);
                SOLVED (MATCH_MP_TAC SUBSET_TRANS THEN
                        W(fun gl ->
                          let su = the_asm (fun c ->
                            hd_is "SUBSET" c &&
                            hd_is "FDOM" (lhand c)) gl in
                          EXISTS_TAC (lhand (concl su))) THEN
                        CONJ_TAC THEN
                        TRY (FIRST_ASSUM ACCEPT_TAC) THEN
                        REWRITE_TAC[INTER_SUBSET])])) THEN
  (* the blocks of the stack stay unique *)
  TRY (SOLVED
        (W(fun gl ->
           let bu = the_asm (hd_is "blocks_unique") gl in
           ACCEPT_TAC (MATCH_MP blocks_unique_update_ref bu)))) THEN
  (* the values of the stack: the update of the reference and the
     cut of the timestamps leave what the invariant says of them
     (v_inv_update_ref) *)
  W(fun (asl,w) -> if not (hd_is "ALL2" w) then ALL_TAC else
        (MATCH_MP_TAC EVERY2_MEM_MONO THEN
         W(fun (asl,w as gl) ->
           let bod = snd (strip_exists w) in
           let l1 = el 1 (snd (strip_comb (last (conjuncts bod)))) in
           let old = the_asm (fun c -> hd_is "ALL2" c &&
                       el 1 (snd (strip_comb c)) = l1) gl in
           EXISTS_TAC (el 0 (snd (strip_comb (concl old))))) THEN
         CONJ_TAC THENL
          [REPEAT GEN_TAC THEN
           CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
           STRIP_TAC THEN
           W(fun (asl,w as gl) ->
             let gargs = snd (strip_comb w) in
             let x = el 1 gargs in
             let y = el 0 (tparts (el 3 gargs)) in
             let vi = the_asm (fun c -> hd_is "v_inv" c &&
                        el 1 (snd (strip_comb c)) = x &&
                        el 0 (tparts (el 3 (snd (strip_comb c))))
                          = y) gl in
             let ri = the_asm (hd_is "RefBlock_inv") gl in
             let lk = the_asm (fun c -> is_eq c &&
                        hd_is "sptree_lookup" (lhand c)) gl in
             let mz = the_asm (fun c -> hd_is "MEM" c &&
                        hd_is "ZIP" (rand c)) gl in
             let l1 = el 0 (snd (strip_comb (rand (concl mz)))) in
             let le = the_asm (fun c -> is_eq c &&
                        lhand c = list_mk_icomb "LENGTH" [l1]) gl in
             MATCH_ACCEPT_TAC (MATCH_MP v_inv_update_ref
               (CONJ ri (CONJ lk (CONJ vi
                 (MATCH_MP mem_zip_left (CONJ le mz)))))));
           FIRST_ASSUM ACCEPT_TAC])) THEN
  (* and the invariant of each reference that the stack reaches:
     it was reachable before the update (reachable_refs_UPDATE) *)
  W(fun (asl,w) -> if not (is_forall w) then ALL_TAC else
    (REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM (fun rr ->
       if not (hd_is "reachable_refs" (concl rr)) then fail() else
       ASSUME_TAC (MATCH_MP reachable_refs_UPDATE rr)) THEN
     (* the reference written, or another one *)
     W(fun (asl,w as gl) ->
       let n = el 1 (snd (strip_comb w)) in
       let lk = the_asm (fun c -> is_eq c &&
                  hd_is "sptree_lookup" (lhand c) &&
                  not (hd_is "sptree_insert"
                         (rand (lhand c)))) gl in
       ASM_CASES_TAC (mk_eq (n,
         el 0 (snd (strip_comb (lhand (concl lk))))))) THEN
     TRY VAR_EQ_TAC THEN
     (* the arm that the two lookups give *)
     W(fun (asl,w as gl) ->
       let lk1 = the_asm (fun c -> is_eq c &&
                   hd_is "FLOOKUP" (lhand c)) gl in
       let ins = find_term (hd_is "sptree_insert") w in
       let args = snd (strip_comb ins) in
       let n = el 1 (snd (strip_comb w)) in
       let nl = mk_eq (list_mk_icomb "sptree_lookup" [n; ins],
                       list_mk_icomb "SOME"
                         [if n = el 0 args then el 1 args
                          else rand (concl (the_asm (fun c ->
                            is_eq c &&
                            hd_is "sptree_lookup" (lhand c) &&
                            el 0 (snd (strip_comb (lhand c))) = n &&
                            not (hd_is "sptree_insert"
                                   (rand (lhand c)))) gl))]) in
       SUBGOAL_THEN nl (fun lk2 ->
         REWRITE_TAC[MATCH_MP arm_VA (CONJ lk1 lk2)]) THENL
        [ASM_REWRITE_TAC[lookup_insert];
         ALL_TAC]) THEN
     SHOW "an arm of the references")) THEN
  SHOW "what is left of the invariant");;
*)
