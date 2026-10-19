(* ======================================================== *)
(*  data_to_wordProof: ported from HOL4's
    compiler/backend/proofs/data_to_wordProofScript.sml
    A proof theory about data_to_word.ml, with 3 definitions and 75
    theorems.  Needed by backendProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for data_to_word
*)

needs "basis/pure/mlvector.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi_to_data.ml";;
needs "compiler/backend/bvl_to_bvi.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/data_space.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/gc/copying_gc.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "compiler/backend/gc/gen_gc_partial.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/proofs/data_to_word_assignProof.ml";;
needs "compiler/backend/proofs/data_to_word_bignumProof.ml";;
needs "compiler/backend/proofs/data_to_word_gcProof.ml";;
needs "compiler/backend/proofs/data_to_word_memoryProof.ml";;
needs "compiler/backend/proofs/wordConvsProof.ml";;
needs "compiler/backend/proofs/word_bignumProof.ml";;
needs "compiler/backend/proofs/word_gcFunctions.ml";;
needs "compiler/backend/proofs/word_to_wordProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/backend/word_to_word.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/alignment.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "lib/term.ml";;
needs "lib/toto.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/semanticPrimitives.ml";;

cake_hide ["all"; "vars"];;

cake_hide_consts
  ["code_buffer","code_buffer";
   "data_buffer","data_buffer";
   "memory","memory"];;
(* HOL4 ancestors outside the port: int_bitwise finite_map While *)

(* HOL4 data_to_wordProofScript.sml:23-24: a proof *)

(* HOL4 data_to_wordProofScript.sml:26-27: ML code, not ported *)

(* HOL4 data_to_wordProofScript.sml:29-35: ML code, not ported *)

let state_rel_with_locals_sfs =
  cake_theorem "state_rel_with_locals_sfs[simp]"
  (fun () ->
    `state_rel c l1 l2 (dataSem_state_safe_for_space_fupd (K m)
  (state_locals_fupd (K l) x)) r t locs <=>
     state_rel c l1 l2 (state_locals_fupd (K l) x) r t locs`)
  CHEAT_TAC;;

let do_space_code_const = cake_theorem "do_space_code_const"
  (fun () ->
    `do_space op vs (s:('a,'b)dataSem_state) = SOME s1 ==> state_code
     s1 = dataSem_state_code s /\ compile_oracle s1 =
       dataSem_state_compile_oracle s`)
  CHEAT_TAC;;

let word_test_lemma1 = cake_theorem "word_test_lemma1[local]"
  (fun () ->
    `good_dimindex (:'a) ==>
     ((n2w 0b111100) && x = (n2w ((8 + 6) * 4):'a word) <=>
      ~(word_bit 2 x) /\ word_bit 3 x /\ word_bit 4 x /\ word_bit
        5 x)`)
  CHEAT_TAC;;

let word_test_lemma2 = cake_theorem "word_test_lemma2[local]"
  (fun () ->
    `good_dimindex (:'a) ==>
     ((n2w 0b111100) && x = (n2w ((0 + 6) * 4):'a word) <=>
      ~(word_bit 2 x) /\ word_bit 3 x /\ word_bit 4 x /\
        ~(word_bit 5 x))`)
  CHEAT_TAC;;

let memory_rel_Thunk_bits = cake_theorem "memory_rel_Thunk_bits"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((RefPtr bl p,wordLang_Word
  (w:'a word)) :: vars) /\
     lookup p refs = SOME (Thunk ev z) /\
     good_dimindex (:'a) /\
     get_real_addr c st w = SOME a /\
     m a = wordLang_Word x /\ FAPPLY
     w 0 ==>
     (~bl /\ ev = Evaluated /\ ~(((n2w 0b111100) && x) = n2w ((0 +
       6) * 4)) /\ ~(((n2w 0b111100) && x) = n2w ((8 + 6) * 4))) \/
     (match ev with NotEvaluated -> (n2w 0b111100) && x = n2w ((0
       + 6) * 4) | Evaluated -> (n2w 0b111100) && x = n2w ((8 + 6) *
       4))`)
  CHEAT_TAC;;

let MEM_join_env_cut_env = cake_theorem "MEM_join_env_cut_env"
  (fun () ->
    `!(a:dataSem_v#'a word_loc) t r s.
       MEM a (join_env x (toAList (inter t (adjust_set x)))) /\
       dataSem_cut_env r s = SOME x ==>
       MEM a (join_env s (toAList (inter t (adjust_set s))))`)
  CHEAT_TAC;;

let jump_exc_locals = cake_theorem "jump_exc_locals"
  (fun () ->
    `wordSem_jump_exc (wordSem_state_locals_fupd (K l) t) = jump_exc t`)
  CHEAT_TAC;;

(* HOL4 data_to_wordProofScript.sml:123-126: a theorem that HOL4
   states as the value of an ML expression:
   state_rel_cut_env_IMP_cut_env *)

let v_inv_Loc = cake_theorem "v_inv_Loc[local]"
  (fun () ->
    `v_inv c v1 (state_refs s) (v2,f,tf,heap) /\
     word_addr c v2 = Loc n1 n2 ==>
       n2 = 0`)
  CHEAT_TAC;;

let state_rel_get_var_RefPtr_Loc =
  cake_theorem "state_rel_get_var_RefPtr_Loc[local]"
  (fun () ->
    `state_rel c l1 l2 s t v1 locs /\
     get_var n (state_locals s) = SOME (RefPtr b p) /\
     get_var (adjust_var n) t = SOME (Loc n1 n2) ==>
       n2 = 0`)
  CHEAT_TAC;;

let cut_state_opt_ffi = cake_theorem "cut_state_opt_ffi[local]"
  (fun () ->
    `dataSem_cut_state_opt names_opt r = SOME v1 ==> state_ffi v1 =
  state_ffi r`)
  CHEAT_TAC;;

(* shared conjunct tail for the two popped-frame cases (Env / Exc) of
   state_rel_pop_env_set_vars_IMP below. *)
(* HOL4 data_to_wordProofScript.sml:179-252: a proof *)

(* multi-value generalisation of state_rel_pop_env_set_var_IMP (gcProof): the
   returning-Call reconstruction places the whole result list via set_vars. *)
let state_rel_pop_env_set_vars_IMP =
  cake_theorem "state_rel_pop_env_set_vars_IMP[local]"
  (fun () ->
    `state_rel c q l s1 (t1:('a,'c,'ffi)wordSem_state) (SOME (ZIP as
  ws)) locs /\
     LENGTH as = LENGTH ws /\ LENGTH ns = LENGTH as /\ ALL_DISTINCT
       ns /\
     pop_env s1 = SOME s2 ==>
     (?t2 l8 l9 ll.
       pop_env t1 = SOME t2 /\ locs = (l8,l9) :: ll /\
       state_rel c l8 l9 (set_vars ns as s2) (set_vars (MAP
         adjust_var ns) ws t2) NONE ll)`)
  CHEAT_TAC;;

(* HOL4 data_to_wordProofScript.sml:283-285: a proof *)

(* HOL4 data_to_wordProofScript.sml:287-289: a proof *)

(* HOL4 data_to_wordProofScript.sml:291: a proof *)

let data_compile_correct = cake_theorem "data_compile_correct"
  (fun () ->
    `!prog s c n l l1 l2 res s1 (t:('a,'c,'ffi)wordSem_state) locs.
        (dataSem_evaluate (prog,s) = (res,s1)) /\ ~(res = SOME
          (Rerr (Rabort Rtype_error))) /\
        state_rel c l1 l2 s t NONE locs /\ wordSem_state_termdep
        t > 1 ==>
        (?t1 res1.
          (wordSem_evaluate (FST (comp c n l prog),t) = (res1,t1))
            /\
           option_le (state_stack_max t1) (state_stack_max s1) /\
          (res1 = SOME wordSem_NotEnoughSpace ==>
            ffi_state_io_events (state_ffi
             t1) <<= ffi_state_io_events (state_ffi s1) /\
             (~(data_to_word_config_gc_kind c = None) ==>
               ~(dataSem_state_safe_for_space s1))) /\
          (~(res1 = SOME wordSem_NotEnoughSpace) ==>
           (match res with NONE -> state_rel c l1 l2 s1 t1 NONE
             locs /\ (res1 = NONE) | SOME (Rval v) ->
               (?ws. LENGTH ws = LENGTH v /\
                    state_rel c l1 l2 s1 t1 (SOME (ZIP v ws)) locs
                      /\
                    (res1 = SOME (wordSem_Result (wordLang_Loc l1
                      l2) ws))) | SOME (Rerr (Rraise v)) -> (state_ffi
                      t1 = state_ffi s1) /\
               (?w l5 l6 ll.
                 (res1 = SOME (wordSem_Exception (mk_loc (jump_exc
                   t)) w)) /\
                 (~(jump_exc t = NONE) ==>
                  LASTN (LENGTH (stack s1) + 1) locs = (l5,l6) ::
                    ll /\
                  (!i. state_rel c l5 l6 (set_var i v s1)
                         (set_var (adjust_var i) w t1) NONE ll)))
                           | SOME (Rerr (Rabort (Rffi_error f))) ->
                           (res1 = SOME (wordSem_FinalFFI f) /\
                           state_ffi t1 = state_ffi s1) | SOME (Rerr
                           (Rabort e)) -> (res1 = SOME TimeOut) /\
                           state_ffi t1 = state_ffi s1)))`)
  CHEAT_TAC;;

(* HOL4 data_to_wordProofScript.sml:348-351: a proof *)

(* HOL4 data_to_wordProofScript.sml:353-365: a proof *)

(* HOL4 data_to_wordProofScript.sml:367-389: a proof *)

(* HOL4 data_to_wordProofScript.sml:391-741: a proof *)

(* HOL4 data_to_wordProofScript.sml:743-751: a proof *)

(* HOL4 data_to_wordProofScript.sml:753-832: a proof *)

(* HOL4 data_to_wordProofScript.sml:834-843: a proof *)

(* HOL4 data_to_wordProofScript.sml:845-868: a proof *)

(* HOL4 data_to_wordProofScript.sml:870-907: a proof *)

(* HOL4 data_to_wordProofScript.sml:909-932: a proof *)

(* HOL4 data_to_wordProofScript.sml:934-970: a proof *)
  (* dataSem now has the up-front `ALL_DISTINCT q` guard (matching wordSem), so
     `res <> Rtype_error` forces `ALL_DISTINCT q`. *)
(* HOL4 data_to_wordProofScript.sml:973-1152: a proof *)

(* HOL4 data_to_wordProofScript.sml:1154: a proof *)


let compile_correct_lemma = cake_theorem "compile_correct_lemma"
  (fun () ->
    `!s c l1 l2 res s1 (t:('a,'c,'ffi)wordSem_state) start'.
        (dataSem_evaluate (Call NONE (SOME start') [] NONE,s) =
          (res,s1)) /\ ~(res = SOME (Rerr (Rabort Rtype_error))) /\
          wordSem_state_termdep
        t > 1 /\
        state_rel c l1 l2 s t NONE [] ==>
        (?t1 res1.
          (wordSem_evaluate (Call NONE (SOME start') [0] NONE,t) =
            (res1,t1)) /\
          option_le (state_stack_max t1) (state_stack_max s1) /\
          (res1 = SOME wordSem_NotEnoughSpace ==>
            ffi_state_io_events (state_ffi
             t1) <<= ffi_state_io_events (state_ffi s1) /\
             (~(data_to_word_config_gc_kind c = None) ==>
               ~(dataSem_state_safe_for_space s1))) /\
          (~(res1 = SOME wordSem_NotEnoughSpace) ==>
           (match res with NONE -> (state_ffi t1 = state_ffi s1) /\
             (res1 = NONE) | SOME (Rval v) -> (state_ffi t1 = state_ffi
             s1) /\
                             (?w. (res1 = SOME (wordSem_Result
                               (wordLang_Loc l1 l2) w))) | SOME (Rerr
                               (Rraise v)) -> (state_ffi t1 = state_ffi
                               s1) /\
                              (?v w. res1 = SOME
                                (wordSem_Exception v w)) | SOME (Rerr
                                (Rabort (Rffi_error f))) -> (res1 =
                                SOME (wordSem_FinalFFI f) /\ state_ffi
                                t1 = state_ffi s1) | SOME (Rerr
                                (Rabort e)) -> (res1 = SOME TimeOut)
                                /\ state_ffi t1 = state_ffi s1)))`)
  CHEAT_TAC;;

let state_rel_ext_def = cake_define
  `state_rel_ext c l1 l2 s u <=>
     (?t l.
       state_rel c l1 l2 s t NONE [] /\
       domain (wordSem_state_code t) = domain l /\
         wordSem_state_termdep
       t > 1 /\
       (?tt kk aa co. wordSem_state_compile_oracle
          u =
            (I ## MAP (\p. full_compile_single tt kk aa co (p,NONE)))
              o wordSem_state_compile_oracle
              t /\ wordSem_state_compile
          t = (\conf progs. wordSem_state_compile u conf
            (MAP (\p. full_compile_single tt kk aa co (p,NONE))
              progs))) /\
       (!n v. lookup n (wordSem_state_code t) = SOME v ==>
              (?t' k' a' c' col.
              lookup n l = SOME (SND (full_compile_single t' k' a' c'
                ((n,v),col))))) /\
       u = wordSem_state_compile_oracle_fupd (K
         (wordSem_state_compile_oracle u))
         (wordSem_state_compile_fupd (K (wordSem_state_compile u))
         (wordSem_state_termdep_fupd (K 0) (wordSem_state_code_fupd
         (K l) t))))`;;

let data_to_wordProof_compile_correct = cake_theorem "compile_correct"
  (fun () ->
    `!x s l1 l2 res s1 (t:('a,'c,'ffi)wordSem_state) start'.
        (dataSem_evaluate (Call NONE (SOME start') [] NONE,s) =
          (res,s1)) /\ ~(res = SOME (Rerr (Rabort Rtype_error))) /\
        state_rel_ext x l1 l2 s t ==>
        (?ck t1 res1.
          (wordSem_evaluate (Call NONE (SOME start') [0] NONE,
             (wordProps_inc_clock ck t)) = (res1,t1)) /\
          option_le (state_stack_max t1) (state_stack_max s1) /\
          (res1 = SOME wordSem_NotEnoughSpace ==>
            ffi_state_io_events (state_ffi
             t1) <<= ffi_state_io_events (state_ffi s1) /\
             (~(data_to_word_config_gc_kind x = None) ==>
               ~(dataSem_state_safe_for_space s1))) /\
          (~(res1 = SOME wordSem_NotEnoughSpace) ==>
           (state_ffi t1 = state_ffi s1) /\
           (match res with NONE -> (res1 = NONE) | SOME (Rval v)
             -> (?w. (res1 = SOME (wordSem_Result (wordLang_Loc l1 l2)
             w))) | SOME (Rerr (Rraise v)) -> (?v w. res1 = SOME
             (wordSem_Exception v w)) | SOME (Rerr (Rabort (Rffi_error
             f))) -> (res1 = SOME (wordSem_FinalFFI f)) | SOME (Rerr
             (Rabort e)) -> (res1 = SOME TimeOut))))`)
  CHEAT_TAC;;

let state_rel_ext_with_clock =
  cake_theorem "state_rel_ext_with_clock[local]"
  (fun () ->
    `state_rel_ext a b c s1 s2 ==>
       state_rel_ext a b c (state_clock_fupd (K k) s1)
         (state_clock_fupd (K k) s2)`)
  CHEAT_TAC;;

(* observational semantics preservation *)

let compile_semantics_lemma = cake_theorem "compile_semantics_lemma"
  (fun () ->
    `state_rel_ext conf 1 0 (initial_state (ffi:'ffi ffi_state)
  (fromAList prog) co cc T lims (wordSem_state_stack_size t)
  (wordSem_state_clock t)) (t:('a,'c,'ffi)wordSem_state) /\ fs =
  wordSem_state_stack_size t /\ ~(semantics ffi (fromAList prog) co cc
  lims fs start = Fail) ==>
     semantics t start IN
       extend_with_resource_limit {semantics ffi (fromAList prog)
         co cc lims fs start}`)
  CHEAT_TAC;;

let compile_semantics_precise_lemma =
  cake_theorem "compile_semantics_precise_lemma"
  (fun () ->
    `state_rel_ext conf 1 0 (initial_state (ffi:'ffi ffi_state)
  (fromAList prog) co cc T lims (wordSem_state_stack_size t)
  (wordSem_state_clock t)) (t:('a,'c,'ffi)wordSem_state) /\ fs =
  wordSem_state_stack_size t /\
     data_lang_safe_for_space ffi (fromAList prog) lims fs start /\
       ~(data_to_word_config_gc_kind conf = None) /\ ~(semantics ffi
       (fromAList prog) co cc lims fs start = Fail) ==>
     semantics t start IN
       extend_with_resource_limit' T {semantics ffi (fromAList
         prog) co cc lims fs start}`)
  CHEAT_TAC;;

let compile_semantics_precise = cake_theorem "compile_semantics_precise"
  (fun () ->
    `state_rel_ext conf 1 0 (initial_state (ffi:'ffi ffi_state)
  (fromAList prog) co cc T lims (wordSem_state_stack_size t)
  (wordSem_state_clock t)) (t:('a,'c,'ffi)wordSem_state) /\
     fs = wordSem_state_stack_size t /\
       ~(data_to_word_config_gc_kind conf = None) /\ ~(semantics ffi
       (fromAList prog) co cc lims fs start = Fail) /\
     data_lang_safe_for_space ffi (fromAList prog) lims fs start
       ==>
     semantics t start = semantics ffi (fromAList prog) co cc
       lims fs start`)
  CHEAT_TAC;;

let get_limits_def = cake_define
  `get_limits c (t:('a,'c,'ffi)wordSem_state) =
     mk_limits (w2n (theWord (FAPPLY (wordSem_state_store t)
       HeapLength)) DIV (dimindex (:'a) DIV 8))
       (data_to_word_config_len_size c) (wordSem_state_stack_limit t)
       (dimindex (:'a) = 64) (has_fp_ops c)
       (data_to_word_config_has_fp_tern c)`;;

let option_le_SOME = cake_theorem "option_le_SOME"
  (fun () ->
    `option_le x (SOME n) <=> (?m. x = SOME m /\ m <= n)`)
  CHEAT_TAC;;

let data_to_wordProof_compile_semantics =
  cake_theorem "compile_semantics"
  (fun () ->
    `wordSem_state_handler
       (t:('a,'c,'ffi)wordSem_state) = 0 /\ wordSem_state_gc_fun t
         = word_gc_fun c /\
       init_store_ok c (wordSem_state_store t)
         (wordSem_state_memory t) (wordSem_state_mdomain t)
         (wordSem_state_code_buffer t) (wordSem_state_data_buffer t) /\
       good_dimindex (:'a) /\ lookup 0 (wordSem_state_locals t) =
         SOME (Loc 1 0) /\ wordSem_state_stack t = [] /\
       conf_ok (:'a) c /\ wordSem_state_termdep t = 0 /\ code_rel c
         (fromAList prog) x1 /\
       cc =
       (\cfg.
            OPTION_MAP (I ## MAP upper_w2w ## I) o tcc cfg o
            MAP (compile_part c)) /\
       Abbrev (tco = (I ## MAP (compile_part c)) o co) /\
       (!n. EVERY (\(n,_1). data_num_stubs <= n) (SND (co n))) /\
       code_rel_ext x1 (wordSem_state_code t) /\ domain x1 = domain
         (wordSem_state_code t) /\ wordSem_state_be t =
         data_to_word_config_be c /\ wordSem_state_stack_max
       t = SOME 1 /\ wordSem_state_locals_size t = SOME 0 /\
         ~(wordSem_state_stack_limit t = 0) /\
         wordSem_state_compile_oracle
       t =
       (I ## MAP (\p. full_compile_single tt kk aa coo (p,NONE))) o
         tco /\
       Abbrev
         (tcc =
          (\conf progs. wordSem_state_compile
               t conf
                 (MAP (\p. full_compile_single tt kk aa coo
                   (p,NONE)) progs))) /\
       fs = wordSem_state_stack_size t /\ ~(Fail = semantics
         (wordSem_state_ffi t) (fromAList prog) co cc zero_limits fs
         start) ==>
       (data_lang_safe_for_space (wordSem_state_ffi t) (fromAList
         prog) (get_limits c t) fs start /\
         ~(data_to_word_config_gc_kind
        c = None) ==> word_lang_safe_for_space t start) /\
       semantics t start IN
       extend_with_resource_limit'
         (data_lang_safe_for_space (wordSem_state_ffi t) (fromAList
           prog) (get_limits c t) fs
            start /\ ~(data_to_word_config_gc_kind c = None))
         {semantics (wordSem_state_ffi t) (fromAList prog) co cc
           zero_limits fs start}`)
  CHEAT_TAC;;

(* HOL4 data_to_wordProofScript.sml:1917: ML code, not ported *)

(* HOL4 data_to_wordProofScript.sml:1919: ML code, not ported *)

let extract_labels_MemEqList =
  cake_theorem "extract_labels_MemEqList[simp]"
  (fun () ->
    `!a x. wordConvs_extract_labels (MemEqList a x) = []`)
  CHEAT_TAC;;

let extract_labels_StoreEach = cake_theorem "extract_labels_StoreEach"
  (fun () ->
    `!xs a d. wordConvs_extract_labels (StoreEach a xs d) = []`)
  CHEAT_TAC;;

let extract_labels_StoreAnyConsts =
  cake_theorem "extract_labels_StoreAnyConsts"
  (fun () ->
    `!r1 r2 r3 ws w. wordConvs_extract_labels (StoreAnyConsts r1 r2 r3
  ws w) = []`)
  CHEAT_TAC;;

(* TODO: goes away on inlineenc branch *)
let extract_labels_WordOp64_on_32 =
  cake_theorem "extract_labels_WordOp64_on_32[local]"
  (fun () ->
    `wordConvs_extract_labels (WordOp64_on_32 f) = []`)
  CHEAT_TAC;;

let extract_labels_WordShift64_on_32 =
  cake_theorem "extract_labels_WordShift64_on_32[local]"
  (fun () ->
    `wordConvs_extract_labels (WordShift64_on_32 f g) = []`)
  CHEAT_TAC;;

let extract_labels_assignWordOp =
  cake_theorem "extract_labels_assignWordOp[local]"
  (fun () ->
    `assign a b c d (closLang_WordOp (WordOpw e f)) g h = (i,j) ==>
     wordConvs_extract_labels i = [] /\ c <= j`)
  CHEAT_TAC;;

let extract_labels_assignWordShift =
  cake_theorem "extract_labels_assignWordShift[local]"
  (fun () ->
    `assign a b c d (closLang_WordOp (WordShift e f k)) g h = (i,j) ==>
     wordConvs_extract_labels i = [] /\ c <= j`)
  CHEAT_TAC;;

(* HOL4 data_to_wordProofScript.sml:1987-1989: ML code, not ported *)

let data_to_word_lab_pres_lem = cake_theorem "data_to_word_lab_pres_lem"
  (fun () ->
    `!c n l p. ~(l = 0) ==>
       (let (cp,l') = comp c n l p in
       l <= l' /\
       EVERY (\(l1,l2). l1 = n /\ l <= l2 /\ l2 < l')
         (wordConvs_extract_labels cp) /\
       ALL_DISTINCT (wordConvs_extract_labels cp))`)
  CHEAT_TAC;;

let labels_rel_emp = cake_theorem "labels_rel_emp[local]"
  (fun () ->
    `labels_rel [] ls ==> ls = []`)
  CHEAT_TAC;;

let stub_labels = cake_theorem "stub_labels"
  (fun () ->
    `EVERY (\(n,m,p).
     EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
       (wordConvs_extract_labels p) /\
                      ALL_DISTINCT (wordConvs_extract_labels p))
     (stubs (:'a) data_conf)`)
  CHEAT_TAC;;

let stubs_with_has_fp_ops = cake_theorem "stubs_with_has_fp_ops[simp]"
  (fun () ->
    `stubs (:'a) (has_fp_ops_fupd (K b) data_conf) = stubs (:'a)
  data_conf`)
  CHEAT_TAC;;

let stubs_with_has_fp_tern = cake_theorem "stubs_with_has_fp_tern[simp]"
  (fun () ->
    `stubs (:'a) (data_to_word_config_has_fp_tern_fupd (K b)
  data_conf) = stubs (:'a) data_conf`)
  CHEAT_TAC;;

(* no ShareInst in the compiled program *)

let list_Seq_no_share_inst = cake_theorem "list_Seq_no_share_inst"
  (fun () ->
    `!xs. no_share_inst (list_Seq xs) = EVERY no_share_inst xs`)
  CHEAT_TAC;;

let StoreEach_no_share_inst = cake_theorem "StoreEach_no_share_inst"
  (fun () ->
    `!v xs offset. no_share_inst (StoreEach v xs offset)`)
  CHEAT_TAC;;

let MemEqList_no_share_inst = cake_theorem "MemEqList_no_share_inst"
  (fun () ->
    `!a xs. no_share_inst (MemEqList a xs)`)
  CHEAT_TAC;;

let StoreAnyConsts_no_share_inst =
  cake_theorem "StoreAnyConsts_no_share_inst"
  (fun () ->
    `!r1 r2 r3 vs v.
       no_share_inst (StoreAnyConsts r1 r2 r3 vs v)`)
  CHEAT_TAC;;

let stubs_no_share_inst = cake_theorem "stubs_no_share_inst"
  (fun () ->
    `EVERY (\x. no_share_inst (SND (SND x))) (data_to_word_stubs (:'a)
  data_conf)`)
  CHEAT_TAC;;

let comp_no_share_inst = cake_theorem "comp_no_share_inst"
  (fun () ->
    `!c secn l prog prog' l'.
     data_to_word_comp c secn l prog = (prog',l') ==>
     no_share_inst prog'`)
  CHEAT_TAC;;

let MAP_FST_ZIP = cake_theorem "MAP_FST_ZIP[local]"
  (fun () ->
    `!xs ys. MAP FST (ZIP xs ys) = TAKE (LENGTH ys) xs`)
  CHEAT_TAC;;

let compile_no_share_inst = cake_theorem "compile_no_share_inst"
  (fun () ->
    `data_to_word_compile data_conf word_conf asm_conf prog = (xx,prog')
  ==>
     EVERY (\(n,m,pp). no_share_inst pp) prog'`)
  CHEAT_TAC;;

(***)

let data_to_word_compile_lab_pres =
  cake_theorem "data_to_word_compile_lab_pres"
  (fun () ->
    `let (c,p) = compile data_conf word_conf asm_conf prog in
     MAP FST p = MAP FST (stubs (:'a) data_conf) ++ MAP FST prog /\
     EVERY (\(n,m,(p:'a wordLang_prog)).
       let labs = wordConvs_extract_labels p in
       EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) labs /\
       ALL_DISTINCT labs) p`)
  CHEAT_TAC;;

let StoreEach_no_inst = cake_theorem "StoreEach_no_inst[local]"
  (fun () ->
    `!a ls off.
     every_inst (inst_ok_less ac) (StoreEach a ls off)`)
  CHEAT_TAC;;

let MemEqList_no_inst = cake_theorem "MemEqList_no_inst[local]"
  (fun () ->
    `!a x.
     every_inst (inst_ok_less ac) (MemEqList a x)`)
  CHEAT_TAC;;

let StoreAnyConsts_no_inst =
  cake_theorem "StoreAnyConsts_no_inst[local]"
  (fun () ->
    `!r1 r2 r3 ws w. every_inst (inst_ok_less ac) (StoreAnyConsts r1
  r2 r3 ws w)`)
  CHEAT_TAC;;

(* HOL4 data_to_wordProofScript.sml:2294-2296: ML code, not ported *)

let assign_no_inst = cake_theorem "assign_no_inst[local]"
  (fun () ->
    `((data_to_word_config_has_longdiv a ==> (asm_config_ISA ac =
  x86_64)) /\
      (data_to_word_config_has_div a ==> (asm_config_ISA ac IN
        {ARMv8,MIPS,RISC_V})) /\
      (has_fp_ops a ==> 1 < asm_config_fp_reg_count ac) /\
      (data_to_word_config_has_fp_tern a ==> 2 <
        asm_config_fp_reg_count ac /\ asm_config_ISA ac = ARMv7) /\
     asm_offset_ok 0 (asm_config_addr_offset ac) (n2w 0) /\
       asm_offset_ok 0 (asm_config_byte_offset ac) (n2w 0)) ==>
     every_inst (inst_ok_less ac) (FST (assign a b c d e f g))`)
  CHEAT_TAC;;

(*
inst_ok_less_def
*)

let comp_no_inst = cake_theorem "comp_no_inst"
  (fun () ->
    `!c n m p.
     ((data_to_word_config_has_longdiv c ==> (asm_config_ISA ac =
       x86_64)) /\
     (data_to_word_config_has_div c ==> (asm_config_ISA ac IN
       {ARMv8,MIPS,RISC_V})) /\
     (has_fp_ops c ==> 1 < asm_config_fp_reg_count ac) /\
     (data_to_word_config_has_fp_tern c ==> 2 <
       asm_config_fp_reg_count ac /\ asm_config_ISA ac = ARMv7)) /\
     asm_offset_ok 0 (asm_config_addr_offset ac) (n2w 0) /\
       asm_offset_ok 0 (asm_config_byte_offset ac) (n2w 0) ==>
     every_inst (inst_ok_less ac) (FST (comp c n m p))`)
  CHEAT_TAC;;

let bounds_lem = cake_theorem "bounds_lem[local]"
  (fun () ->
    `(dimindex (:'a) = 32 \/ dimindex (:'a) = 64) /\
     ((w:'a word) = --(n2w 3) \/
     w = --(n2w 2) \/
     w = --(n2w 1) \/
     w = (n2w 0) \/
     w = (n2w 1) \/
     w = (n2w 2) \/
     w = (n2w 3) \/
     w = (n2w 4) \/
     w = (n2w 5) \/
     w = (n2w 6) \/
     w = (n2w 7)) ==>
     --(n2w 8) <= w /\ w <= (n2w 8)`)
  CHEAT_TAC;;

let data_to_word_compile_conventions =
  cake_theorem "data_to_word_compile_conventions"
  (fun () ->
    `good_dimindex (:'a) ==>
     (let (c,p) = compile data_conf wc ac prog in
     EVERY (\(n,m,prog).
     flat_exp_conventions (prog:'a wordLang_prog) /\
     post_alloc_conventions (asm_config_reg_count ac - (5 + LENGTH
       (asm_config_avoid_regs ac))) prog /\
     (
     (data_to_word_config_has_longdiv data_conf ==> (asm_config_ISA
       ac = x86_64)) /\
     (data_to_word_config_has_div data_conf ==> (asm_config_ISA ac
       IN {ARMv8,MIPS,RISC_V})) /\
     asm_offset_ok 0 (asm_config_addr_offset ac) (n2w 0) /\
     asm_offset_ok 0 (asm_config_hw_offset ac) (n2w 0) /\
     (
      // NOTE: this condition is
      // stricter than necessary, but we have much more byte_offset space
      // anyway on all the targets
      !w. --(n2w 8) <= w /\ w <= (n2w 8) ==> asm_offset_ok 0
        (asm_config_byte_offset ac) w) ==> full_inst_ok_less ac prog) /\
     (asm_config_two_reg_arith ac ==> every_inst two_reg_inst prog)
       /\
     (no_share_inst prog \/ ~(asm_config_ISA ac = Ag32))) p)`)
  CHEAT_TAC;;

let data_to_word_names = cake_theorem "data_to_word_names"
  (fun () ->
    `word_to_word_compile c1 c2 (stubs (:'a) (backend_config_data_conf
  c) ++ MAP (compile_part c3) prog) = (col,p) ==>
      MAP FST p = (MAP FST (stubs (:'a) (backend_config_data_conf
        c))) ++ MAP FST prog`)
  CHEAT_TAC;;

let ALL_DISTINCT_MAP_FST_stubs =
  cake_theorem "ALL_DISTINCT_MAP_FST_stubs"
  (fun () ->
    `ALL_DISTINCT (MAP FST (data_to_word_stubs a c))`)
  CHEAT_TAC;;

let MAP_FST_stubs_bound = cake_theorem "MAP_FST_stubs_bound"
  (fun () ->
    `MEM n (MAP FST (data_to_word_stubs a c)) ==> n < data_num_stubs`)
  CHEAT_TAC;;

let max_heap_limit_has_fp_ops =
  cake_theorem "max_heap_limit_has_fp_ops[simp]"
  (fun () ->
    `max_heap_limit (:'a) (has_fp_ops_fupd (K b) conf) =
      max_heap_limit (:'a) conf`)
  CHEAT_TAC;;

let data_to_wordProof_FST_compile_part =
  cake_theorem "FST_compile_part[simp]"
  (fun () ->
    `FST (compile_part a b) = (FST b)`)
  CHEAT_TAC;;

(* HOL4 data_to_wordProofScript.sml:2482: the overload
   data_get_code_labels, which the port expands *)
(* HOL4 data_to_wordProofScript.sml:2483: the overload
   data_good_code_labels, which the port expands *)

let word_get_code_labels_StoreEach =
  cake_theorem "word_get_code_labels_StoreEach[local]"
  (fun () ->
    `!ls off.
     wordConvs_get_code_labels (StoreEach v ls off) = {}`)
  CHEAT_TAC;;

let word_get_code_labels_MemEqList =
  cake_theorem "word_get_code_labels_MemEqList[local]"
  (fun () ->
    `!x b.
     wordConvs_get_code_labels (MemEqList b x) = {}`)
  CHEAT_TAC;;

let part_to_words_isWord = cake_theorem "part_to_words_isWord[local]"
  (fun () ->
    `!h c m i w ws.
       part_to_words c m h i = SOME (w,ws) /\
       (!n v. sptree_lookup n m = SOME v ==> isWord (SND v)) ==>
       EVERY isWord (MAP SND ws) /\ isWord (SND w)`)
  CHEAT_TAC;;

let parts_to_words_isWord = cake_theorem "parts_to_words_isWord[local]"
  (fun () ->
    `!ps c w ws m n i.
       parts_to_words c m n ps i = SOME (w,ws) /\
       (!n v. sptree_lookup n m = SOME v ==> isWord (SND v)) ==>
       EVERY isWord (MAP SND ws) /\ isWord (SND w)`)
  CHEAT_TAC;;

let const_parts_to_words_isWord =
  cake_theorem "const_parts_to_words_isWord"
  (fun () ->
    `!c ps w ws.
       const_parts_to_words c ps = SOME (w,ws) ==>
       EVERY isWord (MAP SND ws) /\ isWord (SND w)`)
  CHEAT_TAC;;

let word_get_code_labels_StoreAnyConsts =
  cake_theorem "word_get_code_labels_StoreAnyConsts[local]"
  (fun () ->
    `const_parts_to_words c ps = SOME (w,ws) ==>
     wordConvs_get_code_labels (StoreAnyConsts r1 r2 r3 ws w) =
       EMPTY`)
  CHEAT_TAC;;

let getWords_good_loc = cake_theorem "getWords_good_loc[local]"
  (fun () ->
    `!xs ys ws vs1 s.
       getWords xs ys = (ws,vs1) /\
       EVERY (good_loc s o SND) xs ==>
       EVERY (good_loc s o SND) vs1`)
  CHEAT_TAC;;

let const_parts_to_words_labels =
  cake_theorem "const_parts_to_words_labels"
  (fun () ->
    `const_parts_to_words c bs = SOME (q,r) ==>
     wordConvs_get_code_labels (StoreAnyConsts (adjust_var w) 1 3 r
       q) SUBSET
     assign_get_code_label (closLang_BlockOp (closLang_Build bs))`)
  CHEAT_TAC;;

(* semi-slow... *)
let word_get_code_labels_assign =
  cake_theorem "word_get_code_labels_assign[local]"
  (fun () ->
    `!x.
       assign c secn v w x y z = (res1,res2) ==>
       wordConvs_get_code_labels res1 SUBSET
       assign_get_code_label x UNION (set_of_list (MAP FST (stubs
         (:'a) c)))`)
  CHEAT_TAC;;

let data_to_word_comp_code_labels =
  cake_theorem "data_to_word_comp_code_labels[local]"
  (fun () ->
    `!c secn l p.
     wordConvs_get_code_labels ((FST (comp c secn l p)):'a
       wordLang_prog) SUBSET
     dataProps_get_code_labels p UNION set_of_list (MAP FST
       (stubs (:'a) c))`)
  CHEAT_TAC;;

let word_good_handlers_StoreEach =
  cake_theorem "word_good_handlers_StoreEach[local]"
  (fun () ->
    `!ls off.
     good_handlers secn (StoreEach v ls off)`)
  CHEAT_TAC;;

let word_good_handlers_MemEqList =
  cake_theorem "word_good_handlers_MemEqList[local]"
  (fun () ->
    `!x b.
     good_handlers secn (MemEqList b x)`)
  CHEAT_TAC;;

let word_good_handlers_StoreAnyConsts =
  cake_theorem "word_good_handlers_StoreAnyConsts[local]"
  (fun () ->
    `!r1 r2 r3 ws w. good_handlers secn (StoreAnyConsts r1 r2 r3 ws w)`)
  CHEAT_TAC;;

(* slow... *)
let word_good_handlers_assign =
  cake_theorem "word_good_handlers_assign[local]"
  (fun () ->
    `!x.
       assign c secn v w x y z = (res1,res2) ==>
       good_handlers secn res1`)
  CHEAT_TAC;;

let data_to_word_comp_good_handlers =
  cake_theorem "data_to_word_comp_good_handlers[local]"
  (fun () ->
    `!c secn l p.
     good_handlers secn ((FST (comp c secn l p)):'a
       wordLang_prog)`)
  CHEAT_TAC;;

let stubs_labels = cake_theorem "stubs_labels[local]"
  (fun () ->
    `BIGUNION (set_of_list (MAP (\(n,m,pp). wordConvs_get_code_labels
  pp) (stubs (:'a) dc))) SUBSET set_of_list (MAP FST (stubs (:'a) dc))`)
  CHEAT_TAC;;

let data_to_word_good_code_labels =
  cake_theorem "data_to_word_good_code_labels"
  (fun () ->
    `(data_to_word_compile data_conf word_conf asm_conf prog) =
  (xx,prog') /\
     dataProps_good_code_labels prog elabs ==>
     wordConvs_good_code_labels prog' elabs`)
  CHEAT_TAC;;

(* HOL4 data_to_wordProofScript.sml:2750: the ML values that the
   definitions below antiquote *)

(* TODO: move somewhere better *)
let stubs_fst_def = cake_define
  `stubs_fst = MAP FST (data_to_word_stubs (:1)
                 (ARB:data_to_word_config))`;;

(* HOL4 data_to_wordProofScript.sml:2757-2758: a theorem that HOL4
   states as the value of an ML expression: stubs_fst_eq *)

(* The incremental version ONLY does data_to_word
  TODO: MAP FST stubs is independent of the data conf,
  not sure if generality is needed
*)
let data_to_word_good_code_labels_incr =
  cake_theorem "data_to_word_good_code_labels_incr"
  (fun () ->
    `set_of_list stubs_fst SUBSET elabs /\
     dataProps_good_code_labels progs elabs ==>
     wordConvs_good_code_labels (MAP (compile_part dc) progs)
       elabs`)
  CHEAT_TAC;;

let data_to_word_good_handlers =
  cake_theorem "data_to_word_good_handlers"
  (fun () ->
    `(data_to_word_compile data_conf word_conf asm_conf prog) =
  (xx,prog') ==>
     EVERY (\(n,m,pp). good_handlers n pp) prog'`)
  CHEAT_TAC;;

let data_to_word_good_handlers_incr =
  cake_theorem "data_to_word_good_handlers_incr"
  (fun () ->
    `EVERY (\(n,m,pp). good_handlers n pp) (MAP (compile_part dc)
  progs)`)
  CHEAT_TAC;;

cake_hide [];;

cake_hide_consts [];;
