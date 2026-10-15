(* ======================================================== *)
(*  word_cseProof: ported from HOL4's
    compiler/backend/proofs/word_cseProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for word_cse
*)

needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_cse.ml";;
needs "compiler/backend/word_simp.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
(* HOL4 ancestors outside the port: alist toto *)

(* The reads of a stored arith fact, tracked as self-mappings in
   to_canonical (registered at fact creation), so that a later write to
     any
   of them resets the data. *)
let in_names_set_def = cake_define
  `in_names_set (a:'a asm_arith) tc <=>
     EVERY (\r. sptree_lookup r tc = SOME r) (arithReads a)`;;

(* The invariant is factored into a STATE-FREE syntactic part (wf_data)
   and
   a state-dependent semantic part (sem_inv). The If-join merge needs
   syntactic facts about the not-taken branch's data without having run
     that
   branch: wf_data is established for it by the standalone syntactic
     theorem
   word_cse_wf_data. The (:'a) itself argument ties the quantified arith
   instructions to the state's word width. *)
let wf_data_def = cake_define
  `wf_data (:'a) (data:knowledge) <=>
     (!r v.
        lookup r (knowledge_to_canonical data) = SOME v ==>
        lookup v (knowledge_to_canonical data) = SOME v /\ ODD r /\
          ODD v) /\
     (!r v.
        lookup r (knowledge_to_latest data) = SOME v ==>
        r IN domain (knowledge_to_canonical data) /\
        v IN domain (knowledge_to_canonical data)) /\
     (!k v.
        balanced_map_lookup listCmp k (knowledge_instrs_mem data) =
          SOME v ==>
        lookup v (knowledge_to_canonical data) = SOME v) /\
     (!(a:'a asm_arith) v.
        balanced_map_lookup listCmp (instToNumList (Arith a))
          (knowledge_instrs_mem data) = SOME v ==>
        in_names_set a (knowledge_to_canonical data) /\ can_mem_arith
          a) /\
     (!op src v.
        balanced_map_lookup listCmp (OpCurrHeapToNumList op src)
          (knowledge_instrs_mem data) = SOME v ==>
        lookup src (knowledge_to_canonical data) = SOME src) /\
     (!x v.
        ALOOKUP (knowledge_gets_mem data) x = SOME v ==>
        lookup v (knowledge_to_canonical data) = SOME v) /\
     ALL_DISTINCT (MAP FST (knowledge_gets_mem data)) /\
     balanced_map_invariant listCmp (knowledge_instrs_mem data) /\
     (!k v.
        balanced_map_lookup listCmp k (knowledge_loads_mem data) =
          SOME v ==>
        lookup v (knowledge_to_canonical data) = SOME v) /\
     (!op a (ofs:'a word) v.
        balanced_map_lookup listCmp (loadToNumList op a ofs)
          (knowledge_loads_mem data) = SOME v ==>
        lookup a (knowledge_to_canonical data) = SOME a) /\
     balanced_map_invariant listCmp (knowledge_loads_mem data)`;;

let sem_inv_def = cake_define
  `sem_inv (data:knowledge) (s:('a,'c,'ffi)wordSem_state) <=>
     (!r v.
        lookup r (knowledge_to_canonical data) = SOME v ==>
        get_var r s = get_var v s) /\
     (!r v.
        lookup r (knowledge_to_latest data) = SOME v ==>
        get_var r s = get_var v s) /\
     (!n c v.
        balanced_map_lookup listCmp (instToNumList (Const n c))
          (knowledge_instrs_mem data) = SOME v ==>
        lookup v (wordSem_state_locals s) = SOME (Word c)) /\
     (!(a:'a asm_arith) v.
        balanced_map_lookup listCmp (instToNumList (Arith a))
          (knowledge_instrs_mem data) = SOME v ==>
        (?w. get_var v s = SOME w /\
            evaluate (Inst (Arith a),s) = (NONE,set_var
              (firstRegOfArith a) w s))) /\
     (!op src v.
        balanced_map_lookup listCmp (OpCurrHeapToNumList op src)
          (knowledge_instrs_mem data) = SOME v ==>
        (?w. word_exp s (Op op [Var src; Lookup CurrHeap]) = SOME w
          /\
            get_var v s = SOME w)) /\
     (!l v.
        balanced_map_lookup listCmp [48; l] (knowledge_instrs_mem
          data) = SOME v ==>
        lookup v (wordSem_state_locals s) = SOME (Loc l 0)) /\
     (!x v.
        ALOOKUP (knowledge_gets_mem data) x = SOME v ==>
        (?w. FLOOKUP (wordSem_state_store s) x = SOME w /\ get_var v
          s = SOME w)) /\
     (!op a ofs v.
        ~is_store op /\
        balanced_map_lookup listCmp (loadToNumList op a ofs)
          (knowledge_loads_mem data) = SOME v ==>
        (?w. get_var v s = SOME w /\
            (!r. evaluate (Inst (Mem op r (Addr a ofs)),s) =
              (NONE,set_var r w s))))`;;

let data_inv_def = cake_define
  `data_inv (data:knowledge) (s:('a,'c,'ffi)wordSem_state) <=>
     wf_data (:'a) data /\ sem_inv data s`;;

(* Some usefull proofs to automize *)

(* A stored arith fact concerns a can_mem_arith shape, whose evaluation
   is
   a single set_var of a value computed from the registers it reads; the
   fact transports across a write to any register the instruction does
     not
   read. *)

(* A successful load evaluation determines the loaded value from the
   address
   register and memory alone, so the same load at ANY destination
     evaluates
   the same way — this gives the ∀-quantified-destination form stored by
     the
   loads clause of sem_inv. *)

(* A load reads its address register, the memory fields and be; the
   evaluation equation transports across a write to any OTHER register,
     for
   any destination (including the written one, by insert collapsing). *)

(* A load's address register may be replaced by any register holding the
   same value — the bridge from the executed address to its canonical
   representative. *)

(* A storable arith instruction reads and writes registers only; its
   evaluation equation is insensitive to the memory contents. *)

(* Every register mentioned by the invariant lies in the domain of
   to_canonical, so an untracked register is unmentioned. *)

(* The unset_var (locals-delete) clones of the set_var transports, for
   StoreConsts' two unsets. *)

(* The loads-wipe transport: a pure memory write preserves the whole
   invariant once the load facts are wiped — every other clause reads
     only
   locals, store and code. Used by the Mem-store and StoreConsts cases.
     *)

(* A storable arith instruction reads and writes locals only; its
   evaluation
   equation transports to any state with the same locals. *)

(* A load reads its address register, the memory fields and be; its
   evaluation equation transports to any state agreeing on those. *)

(* The generic state-agreement transport: the whole invariant depends
   only
   on locals, store and the memory fields.  Covers buffer writes, ffi
   extensions and stack changes in one lemma. *)

(* IF-JOIN MERGE SUPPORT

   bm_inter_eq_acc m2 m1 acc inserts into acc exactly the entries of m1
     that
   are present with an equal value in m2; characterised pointwise on
     to_fmap. *)

(* A merged fact is present (with equal value) in both branches' data;
   its
   semantic content comes from whichever branch actually ran, its
     syntactic
   well-formedness from both. *)

(* ---------------------------------------------------------------------
   ---
   KNOWLEDGE-UPDATE SUPPORT

   Lookups in an extended instruction map, read registration, transport
     of
   data_inv across the writes a rewritten program performs, and generic
   extension lemmas for the knowledge fields.
   ---------------------------------------------------------------------
     --- *)

(* Extending to_canonical with a fresh key mapped to itself or to an
   already-canonical register preserves the invariant: the fresh key is
   unmentioned elsewhere, and existing self-maps survive the insert. *)

(* to_latest entries only require domain membership and agreeing values.
   *)

(* Record a fresh Get fact: the destination becomes self-tracked and the
   store name maps to it.  Matches the Get-miss arm of word_cse. *)

(* Dropping store facts never hurts. Matches the Set-arm FILTER. *)

(* Record a true store fact about an already-tracked register.  Matches
   the
   Set-arm cons. *)

(* A store write to a name no fact mentions preserves the invariant:
   only
   the OpCurrHeap clause (CurrHeap) and the gets clauses read the store.
     *)

(* Re-registering a register's canonical entry is sound: fresh self-map
   for
   an untracked register, no-op for a tracked one. *)

(* Invalidation facts for multi-output instructions. *)

(* The invariant never reads the fp registers. *)

(* data_inv is insensitive to writes to untracked registers. *)

(* The Move every cache hit emits. *)

(* The instruction-map key of a can_mem_arith instruction determines its
   operation and reads (but not its destination), hence also the value
     it
   computes: two instructions with the same key evaluate identically up
     to
   the destination register. The sem_inv arith clause quantifies over
     all
   instructions with a stored key, so inserting a fact for one of them
     must
   yield the fact for all of them. *)

(* Storing a new fact: one lemma per key family, each requiring the
   holder
   to be self-mapped and the fact's semantic content to hold. *)

(* Generic correctness of add_to_data_aux, with the family-specific
   content
   as premises: a hit's holder carries the computed value, and (for the
     odd
   destination of a miss) inserting the new fact preserves the
     invariant.
   The destination is freshly invalidated at every call site. *)

(* A canonical representative is itself canonical (by idempotence) or an
   untracked register mapped to itself by the next registration. *)

(* The avoiding variant only differs when the canonical representative
   is
   the (freshly invalidated) destination, which forces the argument
     itself
   to be that untracked destination. *)

(* Correctness of add_to_data_const: a repeated constant keeps its
   register
   equivalence (to_canonical/to_latest) but is rematerialised — both
     arms emit
   Inst (Const r w), so the destination ends up holding Word w either
     way and
   the data invariant is maintained. The destination is freshly
     invalidated at
   the call site (ODD r, untracked). *)

(* Storing a new load fact (the loads_mem sibling of the F-family): the
   holder and the address must be self-mapped, and the fact's
     ∀-destination
   evaluation equation must hold. *)

(* Generic correctness of add_to_load_aux — the loads_mem mirror of
   add_to_data_aux_correct, with the same premise structure. *)

(* The instantiation of add_to_load_aux_correct at the word_cseInst
   Mem-arm
   call site. *)

(* Field-explicit corollaries of the two extension lemmas, in the shape
   the
   map_insert induction produces. *)

(* One recorded register equivalence (fresh destination,
   already-canonical
   source) on top of arbitrary to_canonical/to_latest contents. *)

(* Recording a list of register equivalences (fresh destination,
   canonical
   source) pair by pair: the Move case's knowledge update. *)

(* The Move case: registering the sources and recording the surviving
   destination/canonical-source equivalences preserves the invariant
     across
   the parallel assignment. *)

(* ---------------------------------------------------------------------
   ---
   THE MAIN CORRECTNESS THEOREM

   One suspend/Resume ladder over the evaluate induction: the dispatcher
   names every case, Break and Continue close inline (word_cse keeps the
   data and the program unchanged), and each Resume block below carries
     one
   case's proof.
   ---------------------------------------------------------------------
     --- *)

(* The stored evaluation equations are insensitive to the clock and
   termdep
   fields — clones of the memory transports for the Tick/MustTerminate
   cases. *)

(* data_inv is insensitive to the clock and termdep fields. *)

(* ---------------------------------------------------------------------
   ---
   SYNTACTIC WF PRESERVATION

   word_cse preserves the state-free half of the invariant with no
   semantic premises.  The If case of comp_correct needs wf_data of the
   NOT-taken branch's output, which no evaluation establishes; these
   lemmas mirror the data_inv-level update lemmas above restricted to
   their wf_data content, and culminate in word_cse_wf_data.
   ---------------------------------------------------------------------
     --- *)

(* Wiping the load facts only removes obligations. *)

(* wf sibling of data_inv_insert_to_canonical. *)

(* wf sibling of data_inv_insert_to_latest. *)

(* wf siblings of the per-family fact-insert lemmas (F1-F5): a new fact
   with a self-mapped holder (and, per family, self-mapped reads) keeps
     the
   data well-formed. *)

(* wf mirror of add_to_data_aux_correct: the hit case re-points the
   destination at the stored (self-mapped) holder; the family-specific
   miss case arrives as a premise in the same nested-with form. *)

(* wf mirror of add_to_data_const_correct: both arms keep the data
   well-formed
   — the hit re-points the destination at the (self-mapped) holder, the
     miss
   records a fresh self-mapped constant fact. *)

(* wf siblings of the Get/Set knowledge-update lemmas. *)

(* wf sibling of data_inv_merge_l/_r: well-formedness of both arms is
   enough for the equality-intersection merge. *)

(* wf sibling of data_inv_move_pairs — WITHOUT the ALL_DISTINCT premise:
   word_cse runs on syntactically arbitrary Moves, including ones with
   duplicate destinations that the semantics would reject, so the proof
     is
   a direct characterization via lookup_map_insert0 rather than the
   pair-by-pair induction.  Sources are self-mapped, hence never
   destinations, so their entries survive every insert. *)

(* wf sibling of canonicalMoveRegs_lemma's knowledge-update content. *)

(* wf-premise variants of the self-or-fresh lemmas (the data_inv
   versions
   above only use the wf half of their premise). *)

(* The reads of a canonicalized storable arith are canonical registers:
   tracked-and-self-mapped, or untracked (registered as self-maps next).
     *)

(* The main syntactic preservation theorem, one Resume per constructor
   whose case updates the knowledge (the catch-all closes the identity
     and
   full-reset cases).  Consumed by the If case of comp_correct for the
   not-taken branch. *)

(* HOL4 ML code, not ported:
Resume word_cse_wf_data[Move]:
  gvs [word_cse_def, wf_canonicalMoveRegs]
QED
*)

(* HOL4 ML code, not ported:
Resume word_cse_wf_data[Inst]:
  gvs [word_cse_def]
  \\ Cases_on ‘word_cseInst data i’ \\ gvs []
  \\ namedCases_on ‘i’ ["", "n c", "a", "m n ad", "f"]
  >- ((* Skip *)
      gvs [word_cseInst_def])
  >- ((* Const *)
      gvs [word_cseInst_def]
      \\ ‘wf_data (:'a) (invalidate_data data n) ∧
          lookup n (invalidate_data data n).to_canonical = NONE’ by
           (rw [invalidate_data_def, keep_data_def] \\ gvs
             [empty_data_def])
      \\ Cases_on ‘EVEN n’ \\ gvs []
      \\ drule_all wf_add_to_data_const \\ gvs [])
  >- ((* Arith *)
      gvs [word_cseInst_def]
      \\ ‘wf_data (:'a) (invalidate_regs data (arithWrites a))’ by
           gvs [wf_data_invalidate_regs]
      \\ ‘lookup (firstRegOfArith a)
            (invalidate_regs data (arithWrites a)).to_canonical = NONE’
              by
           (irule lookup_invalidate_regs
            \\ Cases_on ‘a’ \\ gvs [arithWrites_def,
              firstRegOfArith_def])
      \\ qmatch_asmsub_abbrev_tac ‘if GATE then _ else _’
      \\ Cases_on ‘GATE’ \\ gvs [markerTheory.Abbrev_def]
      \\ gvs [add_to_data_def]
      \\ ‘in_names_set
            (canonicalArith (invalidate_regs data (arithWrites a)) a)
            (register_reads (invalidate_regs data (arithWrites a))
               (arithReads
                  (canonicalArith (invalidate_regs data (arithWrites a))
                    a))).
              to_canonical’ by
           (irule in_names_set_register_reads
            \\ gvs [can_mem_arith_ODD_reads,
                    canonicalArith_reads_self_or_fresh])
      \\ ‘wf_data (:'a)
            (register_reads (invalidate_regs data (arithWrites a))
               (arithReads
                  (canonicalArith (invalidate_regs data (arithWrites a))
                    a)))’
           by gvs [wf_data_register_reads]
      \\ ‘lookup (firstRegOfArith a)
            (register_reads (invalidate_regs data (arithWrites a))
               (arithReads
                  (canonicalArith (invalidate_regs data (arithWrites a))
                    a))).
              to_canonical = NONE’ by gvs [lookup_register_reads]
      \\ qpat_x_assum ‘wf_data _ (register_reads _ _)’
           (mp_then (Pos hd) mp_tac wf_add_to_data_aux)
      \\ disch_then drule
      \\ disch_then drule
      \\ impl_tac
      >- (strip_tac
          \\ qmatch_goalsub_abbrev_tac ‘wf_data _ DD’
          \\ ‘DD = (register_reads (invalidate_regs data (arithWrites
            a))
                      (arithReads
                         (canonicalArith
                            (invalidate_regs data (arithWrites a)) a))
                              with
                      to_canonical :=
                        insert (firstRegOfArith a) (firstRegOfArith a)
                          (register_reads
                             (invalidate_regs data (arithWrites a))
                             (arithReads
                                (canonicalArith
                                   (invalidate_regs data (arithWrites
                                     a)) a))).
                            to_canonical)
                   with instrs_mem :=
                     insert listCmp
                       (instToNumList
                          (Arith
                             (canonicalArith
                                (invalidate_regs data (arithWrites a))
                                  a)))
                       (firstRegOfArith a)
                       ((register_reads (invalidate_regs data
                         (arithWrites a))
                           (arithReads
                              (canonicalArith
                                 (invalidate_regs data (arithWrites a))
                                   a)) with
                           to_canonical :=
                             insert (firstRegOfArith a) (firstRegOfArith
                               a)
                               (register_reads
                                  (invalidate_regs data (arithWrites a))
                                  (arithReads
                                     (canonicalArith
                                        (invalidate_regs data
                                           (arithWrites a))
                                             a))).to_canonical).
                          instrs_mem)’ by (unabbrev_all_tac \\ simp [])
          \\ pop_assum SUBST1_TAC
          \\ irule wf_data_insert_instrs_Arith
          \\ gvs [lookup_insert, in_names_set_insert_self]
          \\ irule wf_data_insert_to_canonical
          \\ gvs [lookup_insert, ODD_EVEN, wf_data_register_reads,
                  wf_data_invalidate_regs])
      \\ simp [])
  >- ((* Mem *)
      namedCases_on ‘ad’ ["ar ofs"]
      \\ gvs [word_cseInst_def]
      \\ Cases_on ‘is_store m’ \\ gvs [wf_data_loads_wipe]
      \\ ‘wf_data (:'a) (invalidate_data data n) ∧
          lookup n (invalidate_data data n).to_canonical = NONE’ by
           (rw [invalidate_data_def, keep_data_def] \\ gvs
             [empty_data_def])
      \\ Cases_on ‘EVEN n ∨ EVEN ar ∨ ar = n’ \\ gvs []
      \\ ‘ODD (canonicalRegs' n (invalidate_data data n) ar) ∧
          canonicalRegs' n (invalidate_data data n) ar ≠ n ∧
          lookup (canonicalRegs' n (invalidate_data data n) ar)
            (register_read (invalidate_data data n)
               (canonicalRegs' n (invalidate_data data n)
                 ar)).to_canonical =
          SOME (canonicalRegs' n (invalidate_data data n) ar) ∧
          lookup n
            (register_read (invalidate_data data n)
               (canonicalRegs' n (invalidate_data data n)
                 ar)).to_canonical =
          NONE’ by
           (qpat_x_assum ‘wf_data _ (invalidate_data data n)’ mp_tac
            \\ rw [wf_data_def]
            \\ gvs [lookup_register_read, canonicalRegs'_def,
                    canonicalRegs_def, lookup_any_def]
            \\ Cases_on ‘lookup ar (invalidate_data data
              n).to_canonical’
            \\ gvs [ODD_EVEN]
            \\ res_tac \\ gvs [] \\ rw [] \\ gvs [])
      \\ ‘wf_data (:'a)
            (register_read (invalidate_data data n)
               (canonicalRegs' n (invalidate_data data n) ar))’ by
           gvs [wf_data_register_read]
      \\ qpat_x_assum ‘wf_data _ (register_read _ _)’
           (mp_then (Pos hd) mp_tac wf_add_to_load_aux)
      \\ disch_then drule
      \\ disch_then drule
      \\ impl_tac
      >- (strip_tac
          \\ qmatch_goalsub_abbrev_tac ‘wf_data _ DD’
          \\ ‘DD = (register_read (invalidate_data data n)
                      (canonicalRegs' n (invalidate_data data n) ar)
                        with
                      to_canonical :=
                        insert n n
                          (register_read (invalidate_data data n)
                             (canonicalRegs' n (invalidate_data data n)
                               ar)).
                            to_canonical)
                   with loads_mem :=
                     insert listCmp
                       (loadToNumList m
                          (canonicalRegs' n (invalidate_data data n) ar)
                            ofs) n
                       ((register_read (invalidate_data data n)
                           (canonicalRegs' n (invalidate_data data n)
                             ar) with
                           to_canonical :=
                             insert n n
                               (register_read (invalidate_data data n)
                                  (canonicalRegs' n (invalidate_data
                                    data n)
                                     ar)).to_canonical).loads_mem)’
               by (unabbrev_all_tac \\ simp [])
          \\ pop_assum SUBST1_TAC
          \\ irule wf_data_insert_loads
          \\ gvs [lookup_insert]
          \\ irule wf_data_insert_to_canonical
          \\ gvs [lookup_insert, ODD_EVEN, wf_data_register_read,
                  wf_data_invalidate])
      \\ simp [])
  \\ (* FP *)
    gvs [word_cseInst_def, wf_data_invalidate_regs]
QED
*)

(* HOL4 ML code, not ported:
Resume word_cse_wf_data[Get]:
  gvs [word_cse_def]
  \\ ‘wf_data (:'a) (invalidate_data data n) ∧
      lookup n (invalidate_data data n).to_canonical = NONE’ by
       (rw [invalidate_data_def, keep_data_def] \\ gvs [empty_data_def])
  \\ namedCases_on ‘ALOOKUP (invalidate_data data n).gets_mem s’ ["",
    "k"]
  \\ gvs []
  >- (Cases_on ‘EVEN n’ \\ gvs []
      \\ irule wf_data_insert_gets \\ gvs [ODD_EVEN])
  \\ Cases_on ‘EVEN n’ \\ gvs []
  \\ ‘lookup k (invalidate_data data n).to_canonical = SOME k ∧ ODD k’
    by
       (qpat_x_assum ‘wf_data _ (invalidate_data data n)’ mp_tac
        \\ rw [wf_data_def] \\ res_tac \\ gvs [])
  \\ ‘k ≠ n’ by (strip_tac \\ gvs [])
  \\ qmatch_goalsub_abbrev_tac ‘wf_data _ DD’
  \\ ‘DD = (invalidate_data data n with to_canonical :=
              insert n k (invalidate_data data n).to_canonical)
            with to_latest :=
              insert k n
                ((invalidate_data data n with to_canonical :=
                    insert n k (invalidate_data data n).to_canonical).
                   to_latest)’ by (unabbrev_all_tac \\ simp [])
  \\ pop_assum SUBST1_TAC
  \\ irule wf_data_insert_to_latest
  \\ simp [domain_lookup, lookup_insert]
  \\ irule wf_data_insert_to_canonical
  \\ gvs [lookup_insert, ODD_EVEN]
QED
*)

(* HOL4 ML code, not ported:
Resume word_cse_wf_data[Set]:
  gvs [word_cse_def]
  \\ Cases_on ‘s = CurrHeap’ \\ gvs []
  \\ namedCases_on ‘dest_Var e’ ["", "v"] \\ gvs [wf_data_filter_gets]
  \\ Cases_on ‘EVEN v’ \\ gvs [wf_data_filter_gets]
  \\ ‘lookup (canonicalRegs data v)
        (insert v (lookup_any v data.to_canonical v) data.to_canonical)
          =
      SOME (canonicalRegs data v)’ by
       (gvs [canonicalRegs_def, lookup_any_def]
        \\ Cases_on ‘lookup v data.to_canonical’ \\ gvs [lookup_insert]
        \\ qpat_x_assum ‘wf_data _ data’ mp_tac
        \\ rw [wf_data_def] \\ res_tac \\ gvs [] \\ rw [] \\ gvs [])
  \\ qmatch_goalsub_abbrev_tac ‘wf_data _ DD’
  \\ ‘DD = ((data with to_canonical :=
               insert v (lookup_any v data.to_canonical v)
                 data.to_canonical)
             with gets_mem :=
               FILTER (λ(m,n). m ≠ s)
                 (data with to_canonical :=
                    insert v (lookup_any v data.to_canonical v)
                      data.to_canonical).gets_mem)
            with gets_mem :=
              (s,canonicalRegs data v)::
                ((data with to_canonical :=
                    insert v (lookup_any v data.to_canonical v)
                      data.to_canonical)
                  with gets_mem :=
                    FILTER (λ(m,n). m ≠ s)
                      (data with to_canonical :=
                         insert v (lookup_any v data.to_canonical v)
                           data.to_canonical).gets_mem).gets_mem’
       by (unabbrev_all_tac \\ simp [])
  \\ pop_assum SUBST1_TAC
  \\ irule wf_data_cons_gets
  \\ rpt conj_tac
  >- gvs [ALOOKUP_FILTER]
  >- gvs []
  \\ irule wf_data_filter_gets
  \\ irule wf_data_reinsert_canonical
  \\ gvs [ODD_EVEN]
QED
*)

(* HOL4 ML code, not ported:
Resume word_cse_wf_data[Store]:
  gvs [word_cse_def, wf_data_loads_wipe]
QED
*)

(* HOL4 ML code, not ported:
Resume word_cse_wf_data[MustTerminate]:
  gvs [word_cse_def] \\ pairarg_tac \\ gvs []
  \\ first_x_assum drule \\ gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume word_cse_wf_data[Seq]:
  gvs [word_cse_def]
  \\ pairarg_tac \\ gvs []
  \\ pairarg_tac \\ gvs []
  \\ last_x_assum drule \\ strip_tac
  \\ last_x_assum drule \\ strip_tac
  \\ gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume word_cse_wf_data[If]:
  gvs [word_cse_def]
  \\ pairarg_tac \\ gvs []
  \\ pairarg_tac \\ gvs []
  \\ last_x_assum drule \\ strip_tac
  \\ first_x_assum (qspec_then ‘data’ mp_tac) \\ impl_tac >- simp []
  \\ strip_tac
  \\ gvs [wf_data_merge]
QED
*)

(* HOL4 ML code, not ported:
Resume word_cse_wf_data[OpCurrHeap]:
  gvs [word_cse_def]
  \\ ‘wf_data (:'a) (invalidate_data data n) ∧
      lookup n (invalidate_data data n).to_canonical = NONE’ by
       (rw [invalidate_data_def, keep_data_def] \\ gvs [empty_data_def])
  \\ Cases_on ‘EVEN n0 ∨ n0 = n’ \\ gvs []
  \\ ‘ODD (canonicalRegs' n (invalidate_data data n) n0) ∧
      canonicalRegs' n (invalidate_data data n) n0 ≠ n ∧
      lookup (canonicalRegs' n (invalidate_data data n) n0)
        (register_read (invalidate_data data n)
           (canonicalRegs' n (invalidate_data data n) n0)).to_canonical
             =
      SOME (canonicalRegs' n (invalidate_data data n) n0) ∧
      lookup n
        (register_read (invalidate_data data n)
           (canonicalRegs' n (invalidate_data data n) n0)).to_canonical
             =
      NONE’ by
       (qpat_x_assum ‘wf_data _ (invalidate_data data n)’ mp_tac
        \\ rw [wf_data_def]
        \\ gvs [lookup_register_read, canonicalRegs'_def,
          canonicalRegs_def,
                lookup_any_def]
        \\ Cases_on ‘lookup n0 (invalidate_data data n).to_canonical’
        \\ gvs [ODD_EVEN]
        \\ res_tac \\ gvs [] \\ rw [] \\ gvs [])
  \\ ‘wf_data (:'a)
        (register_read (invalidate_data data n)
           (canonicalRegs' n (invalidate_data data n) n0))’ by
       gvs [wf_data_register_read]
  \\ Cases_on ‘add_to_data_aux
                 (register_read (invalidate_data data n)
                    (canonicalRegs' n (invalidate_data data n) n0)) n
                 (OpCurrHeapToNumList b
                    (canonicalRegs' n (invalidate_data data n) n0))
                 (OpCurrHeap b n n0)’ \\ gvs []
  \\ qpat_x_assum ‘wf_data _ (register_read _ _)’
       (mp_then (Pos hd) mp_tac wf_add_to_data_aux)
  \\ disch_then drule
  \\ disch_then drule
  \\ impl_tac
  >- (strip_tac
      \\ qmatch_goalsub_abbrev_tac ‘wf_data _ DD’
      \\ ‘DD = (register_read (invalidate_data data n)
                  (canonicalRegs' n (invalidate_data data n) n0) with
                  to_canonical :=
                    insert n n
                      (register_read (invalidate_data data n)
                         (canonicalRegs' n (invalidate_data data n)
                           n0)).
                        to_canonical)
               with instrs_mem :=
                 insert listCmp
                   (OpCurrHeapToNumList b
                      (canonicalRegs' n (invalidate_data data n) n0)) n
                   ((register_read (invalidate_data data n)
                       (canonicalRegs' n (invalidate_data data n) n0)
                         with
                       to_canonical :=
                         insert n n
                           (register_read (invalidate_data data n)
                              (canonicalRegs' n (invalidate_data data n)
                                n0)).
                             to_canonical).instrs_mem)’
           by (unabbrev_all_tac \\ simp [])
      \\ pop_assum SUBST1_TAC
      \\ irule wf_data_insert_instrs_OpCurrHeap
      \\ gvs [lookup_insert]
      \\ irule wf_data_insert_to_canonical
      \\ gvs [lookup_insert, ODD_EVEN, wf_data_register_read,
              wf_data_invalidate])
  \\ simp []
QED
*)

(* HOL4 ML code, not ported:
Resume word_cse_wf_data[LocValue]:
  gvs [word_cse_def]
  \\ ‘wf_data (:'a) (invalidate_data data n) ∧
      lookup n (invalidate_data data n).to_canonical = NONE’ by
       (rw [invalidate_data_def, keep_data_def] \\ gvs [empty_data_def])
  \\ Cases_on ‘add_to_data_aux (invalidate_data data n) n [48; n0]
                 (LocValue n n0)’ \\ gvs []
  \\ qpat_x_assum ‘wf_data _ (invalidate_data data n)’
       (mp_then (Pos hd) mp_tac wf_add_to_data_aux)
  \\ disch_then drule
  \\ disch_then drule
  \\ impl_tac
  >- (strip_tac
      \\ qmatch_goalsub_abbrev_tac ‘wf_data _ DD’
      \\ ‘DD = (invalidate_data data n with
                  to_canonical :=
                    insert n n (invalidate_data data n).to_canonical)
               with instrs_mem :=
                 insert listCmp [48; n0] n
                   ((invalidate_data data n with
                       to_canonical :=
                         insert n n (invalidate_data data
                           n).to_canonical).
                      instrs_mem)’ by (unabbrev_all_tac \\ simp [])
      \\ pop_assum SUBST1_TAC
      \\ irule wf_data_insert_instrs_LocValue
      \\ gvs [lookup_insert]
      \\ irule wf_data_insert_to_canonical
      \\ gvs [lookup_insert, ODD_EVEN, wf_data_invalidate])
  \\ simp []
QED
*)

(* HOL4 ML code, not ported:
Resume word_cse_wf_data[StoreConsts]:
  gvs [word_cse_def, wf_data_loads_wipe, wf_data_invalidate_regs]
QED
*)

(* HOL4 ML code, not ported:
Resume word_cse_wf_data[ShareInst]:
  gvs [word_cse_def] \\ rw [wf_data_invalidate]
QED
*)

(* HOL4 ML code, not ported:
Resume word_cse_wf_data[Loop]:
  simp [Once word_cse_def] \\ pairarg_tac \\ gvs []
QED
*)

(* HOL4 ML code, not ported:
Finalise word_cse_wf_data;
*)

(* proof of the cases *)

(* HOL4 ML code, not ported:
Resume comp_correct[Skip]:
  gvs [word_cse_def, evaluate_def]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Alloc]:
  gvs [word_cse_def]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Move]:
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def, evaluate_def, AllCaseEqs()]
  \\ irule canonicalMoveRegs_lemma \\ gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Inst]:
  rpt gen_tac \\ strip_tac
  \\ namedCases_on ‘i’ ["", "n c", "a", "m n ad", "f"]
  >- ((* Skip *)
      gvs [word_cse_def, word_cseInst_def, evaluate_def, inst_def,
           AllCaseEqs()])
  >- ((* Const *)
      gvs [word_cse_def, word_cseInst_def, evaluate_def, inst_def,
        assign_def,
           word_exp_def, AllCaseEqs()]
      \\ ‘data_inv (invalidate_data data n) s ∧
          lookup n (invalidate_data data n).to_canonical = NONE’ by
           (rw [invalidate_data_def, keep_data_def] \\ gvs
             [empty_data_def])
      \\ Cases_on ‘EVEN n’
      \\ gvs [evaluate_def, inst_def, assign_def, word_exp_def,
              data_inv_set_var]
      \\ Cases_on ‘add_to_data_const (invalidate_data data n) n c’
      \\ gvs []
      \\ drule_all add_to_data_const_correct \\ gvs [])
  >- ((* Arith *)
      gvs [word_cse_def, word_cseInst_def]
      \\ ‘data_inv (invalidate_regs data (arithWrites a)) s’ by
           gvs [data_inv_invalidate_regs]
      \\ ‘lookup (firstRegOfArith a)
            (invalidate_regs data (arithWrites a)).to_canonical = NONE’
              by
           (irule lookup_invalidate_regs
            \\ Cases_on ‘a’ \\ gvs [arithWrites_def,
              firstRegOfArith_def])
      \\ qmatch_asmsub_abbrev_tac ‘if GATE then _ else _’
      \\ Cases_on ‘GATE’ \\ gvs [markerTheory.Abbrev_def]
      >- (
          namedCases_on ‘a’
            ["b n n0 ri", "sh n n0 ri", "n n0 n1", "n n0 n1 n2",
             "n n0 n1 n2 n3", "n n0 n1 n2", "n n0 n1 n2", "n n0 n1 n2"]
          \\ gvs [canonicalArith_def, can_mem_arith_def,
            firstRegOfArith_def]
          >- ((* Binop *)
              ‘∃w. res = NONE ∧
                   s' = set_var (firstRegOfArith (Binop b n n0 ri)) w s’
                     by
                (Cases_on ‘ri’
                 \\ gvs [evaluate_def, inst_def, assign_def,
                   word_exp_def,
                         the_words_def, firstRegOfArith_def,
                           AllCaseEqs()]
                 \\ irule_at Any EQ_REFL)
              \\ gvs [] \\ pairarg_tac \\ gvs []
              \\ qspecl_then [‘invalidate_regs data (arithWrites (Binop
                b n n0 ri))’,
                              ‘s’, ‘Binop b n n0 ri’,
                              ‘Binop b n
                                 (canonicalRegs' n
                                    (invalidate_regs data
                                       (arithWrites (Binop b n n0 ri)))
                                         n0)
                                 (canonicalImmReg' n
                                    (invalidate_regs data
                                       (arithWrites (Binop b n n0 ri)))
                                         ri)’,
                              ‘n’, ‘w’, ‘data'’, ‘p’]
                   mp_tac add_to_data_Arith_correct
              \\ impl_tac >- gvs [canonicalArith_def,
                firstRegOfArith_def]
              \\ gvs [firstRegOfArith_def])
          >- ((* Shift *)
              ‘∃w. res = NONE ∧
                   s' = set_var (firstRegOfArith (Shift sh n n0 ri)) w
                     s’ by
                (Cases_on ‘ri’
                 \\ gvs [evaluate_def, inst_def, assign_def,
                   word_exp_def,
                         the_words_def, firstRegOfArith_def,
                         can_mem_arith_def, canonicalImmReg'_def,
                         AllCaseEqs()]
                 \\ irule_at Any EQ_REFL)
              \\ gvs [] \\ pairarg_tac \\ gvs []
              \\ qspecl_then [‘invalidate_regs data (arithWrites (Shift
                sh n n0 ri))’,
                              ‘s’, ‘Shift sh n n0 ri’,
                              ‘Shift sh n
                                 (canonicalRegs' n
                                    (invalidate_regs data
                                       (arithWrites (Shift sh n n0 ri)))
                                         n0)
                                 (canonicalImmReg' n
                                    (invalidate_regs data
                                       (arithWrites (Shift sh n n0 ri)))
                                         ri)’,
                              ‘n’, ‘w’, ‘data'’, ‘p’]
                   mp_tac add_to_data_Arith_correct
              \\ impl_tac >- gvs [canonicalArith_def,
                firstRegOfArith_def]
              \\ gvs [firstRegOfArith_def])
          \\ (* Div *)
             ‘∃w. res = NONE ∧ s' = set_var (firstRegOfArith (Div n n0
               n1)) w s’ by
               (gvs [evaluate_def, inst_def, assign_def, word_exp_def,
                 the_words_def,
                     get_vars_def, get_var_def, firstRegOfArith_def,
                       AllCaseEqs()]
                \\ irule_at Any EQ_REFL)
          \\ gvs [] \\ pairarg_tac \\ gvs []
          \\ qpat_x_assum ‘data_inv (invalidate_regs _ _) _’
               (mp_then (Pos hd) mp_tac add_to_data_Arith_correct)
          \\ disch_then (drule_at (Pos last))
          \\ simp [canonicalArith_def, firstRegOfArith_def,
            can_mem_arith_def,
                   arithReads_def])
      \\ strip_tac \\ gvs []
      \\ Cases_on ‘a’
      \\ gvs [evaluate_def, inst_def, assign_def, word_exp_def,
        the_words_def,
              get_vars_def, get_var_def, arithWrites_def, AllCaseEqs(),
              data_inv_set_var, lookup_invalidate_regs]
      \\ pairarg_tac \\ gvs [data_inv_set_var, lookup_invalidate_regs])
  >- ((* Mem *)
      namedCases_on ‘ad’ ["ar ofs"]
      \\ gvs [word_cse_def, word_cseInst_def]
      \\ Cases_on ‘is_store m’ \\ gvs []
      >- ((* store: wipe the load facts, keep the register facts *)
          strip_tac \\ Cases_on ‘m’
          \\ gvs [is_store_def, evaluate_def, inst_def, word_exp_def,
                  the_words_def, mem_store_def, AllCaseEqs(),
                    data_inv_memory])
      \\ (* load *)
      ‘data_inv (invalidate_data data n) s ∧
       lookup n (invalidate_data data n).to_canonical = NONE’ by
        (rw [invalidate_data_def, keep_data_def] \\ gvs
          [empty_data_def])
      \\ ‘∃w. res = NONE ∧ s' = set_var n w s’ by
           (Cases_on ‘m’
            \\ gvs [is_store_def, evaluate_def, inst_def, AllCaseEqs()]
            \\ irule_at Any EQ_REFL)
      \\ gvs []
      \\ Cases_on ‘EVEN n ∨ EVEN ar ∨ ar = n’
      \\ gvs [evaluate_def, data_inv_set_var]
      \\ pairarg_tac \\ gvs []
      \\ qpat_x_assum ‘data_inv (invalidate_data _ _) _’
           (mp_then (Pos hd) mp_tac add_to_load_correct)
      \\ disch_then (drule_at (Pos last))
      \\ simp []
      \\ disch_then (qspec_then ‘w’ mp_tac) \\ gvs []
      \\ impl_tac >- gvs [evaluate_def]
      \\ gvs [])
  \\ (* FP *)
    gvs [word_cse_def, word_cseInst_def]
    \\ Cases_on ‘f’
    \\ gvs [evaluate_def, inst_def, fpWrites_def, AllCaseEqs(),
            data_inv_set_var, lookup_invalidate_regs,
              data_inv_invalidate_regs]
    \\ pairarg_tac \\ gvs [invalidate_regs_def]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Assign]:
  fs [flat_exp_conventions_def]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Get]:
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def, evaluate_def, AllCaseEqs(), invalidate_data_def,
          keep_data_def]
  >- gvs [data_inv_set_var]
  >- (IF_CASES_TAC \\ gvs []
      \\ irule data_inv_insert_gets
      \\ gvs [set_var_def, get_var_def, lookup_insert, get_store_def,
              ODD_EVEN, empty_data_def, SRULE [set_var_def]
                data_inv_set_var])
  >- (‘get_var k s = SOME x’ by
        (qpat_x_assum ‘data_inv data s’ mp_tac
         \\ rw [data_inv_def, sem_inv_def]
         \\ res_tac \\ gvs [get_store_def])
      \\ ‘get_var (lookup_any k data.to_latest k) s = SOME x’ by
           (gvs [lookup_any_def] \\ Cases_on ‘lookup k data.to_latest’
             \\ gvs []
            \\ qpat_x_assum ‘data_inv data _’ mp_tac
            \\ rw [data_inv_def, sem_inv_def]
            \\ res_tac \\ gvs [])
      \\ conj_tac
      >- (qexists_tac ‘[x]’
          \\ gvs [get_vars_def, set_vars_def, alist_insert_def,
            set_var_def])
      \\ gvs [data_inv_set_var])
  >- gvs [empty_data_def]
  \\ IF_CASES_TAC \\ gvs [empty_data_def]
  \\ ‘get_var k s = SOME x’ by
       (qpat_x_assum ‘data_inv data s’ mp_tac
        \\ rw [data_inv_def, sem_inv_def]
        \\ res_tac \\ gvs [get_store_def])
  \\ ‘lookup k data.to_canonical = SOME k ∧ ODD k’ by
       (qpat_x_assum ‘data_inv data s’ mp_tac
        \\ rw [data_inv_def, wf_data_def]
        \\ res_tac \\ gvs [])
  \\ ‘k ≠ v’ by (strip_tac \\ gvs [])
  \\ ‘get_var (lookup_any k data.to_latest k) s = SOME x’ by
       (gvs [lookup_any_def] \\ Cases_on ‘lookup k data.to_latest’ \\
         gvs []
        \\ qpat_x_assum ‘data_inv data _’ mp_tac
        \\ rw [data_inv_def, sem_inv_def]
        \\ res_tac \\ gvs [])
  \\ conj_tac
  >- (qexists_tac ‘[x]’
      \\ gvs [get_vars_def, set_vars_def, alist_insert_def,
        set_var_def])
  \\ qmatch_goalsub_abbrev_tac ‘data_inv DD _’
  \\ ‘DD = (data with to_canonical := insert v k data.to_canonical)
             with to_latest :=
               insert k v
                 (data with to_canonical := insert v k
                   data.to_canonical).
                 to_latest’
       by (unabbrev_all_tac \\ simp [])
  \\ pop_assum SUBST1_TAC
  \\ irule data_inv_insert_to_latest
  \\ rpt conj_tac
  >- gvs [get_var_def, set_var_def, lookup_insert]
  >- gvs [domain_insert, domain_lookup, lookup_insert, SF SFY_ss]
  >- gvs [domain_insert]
  \\ irule data_inv_insert_to_canonical
  \\ gvs [lookup_insert, ODD_EVEN, get_var_def, set_var_def,
          SRULE [set_var_def] data_inv_set_var]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Set]:
  rpt gen_tac \\ strip_tac
  \\ Cases_on ‘exp’ \\ gvs [flat_exp_conventions_def]
  \\ gvs [word_cse_def, evaluate_def, dest_Var_def, word_exp_def,
    AllCaseEqs()]
  >- (irule data_inv_set_store \\ gvs [ALOOKUP_FILTER,
    data_inv_filter_gets])
  \\ ‘get_var (canonicalRegs data n) s = SOME w’ by gvs []
  \\ ‘lookup (canonicalRegs data n)
        (insert n (lookup_any n data.to_canonical n) data.to_canonical)
          =
      SOME (canonicalRegs data n)’ by
       (gvs [canonicalRegs_def, lookup_any_def]
        \\ Cases_on ‘lookup n data.to_canonical’ \\ gvs [lookup_insert]
        \\ qpat_x_assum ‘data_inv data s’ mp_tac
        \\ rw [data_inv_def, wf_data_def] \\ res_tac \\ gvs [] \\ rw []
          \\ gvs [])
  \\ qmatch_goalsub_abbrev_tac ‘data_inv DD _’
  \\ ‘DD = ((data with to_canonical :=
               insert n (lookup_any n data.to_canonical n)
                 data.to_canonical)
             with gets_mem :=
               FILTER (λ(m,n'). m ≠ v)
                 (data with to_canonical :=
                    insert n (lookup_any n data.to_canonical n)
                      data.to_canonical).gets_mem)
            with gets_mem :=
              (v,canonicalRegs data n)::
                ((data with to_canonical :=
                    insert n (lookup_any n data.to_canonical n)
                      data.to_canonical)
                  with gets_mem :=
                    FILTER (λ(m,n'). m ≠ v)
                      (data with to_canonical :=
                         insert n (lookup_any n data.to_canonical n)
                           data.to_canonical).gets_mem).gets_mem’
       by (unabbrev_all_tac \\ simp [])
  \\ pop_assum SUBST1_TAC
  \\ irule data_inv_cons_gets
  \\ rpt conj_tac
  >- gvs [ALOOKUP_FILTER]
  >- gvs []
  >- (qexists_tac ‘w’ \\ gvs [set_store_def, FLOOKUP_UPDATE,
    get_var_def])
  \\ irule data_inv_set_store \\ gvs [ALOOKUP_FILTER]
  \\ qmatch_goalsub_abbrev_tac ‘data_inv D2 _’
  \\ ‘D2 = (data with to_canonical :=
              insert n (lookup_any n data.to_canonical n)
                data.to_canonical)
            with gets_mem :=
              FILTER (λ(m,n'). m ≠ v)
                (data with to_canonical :=
                   insert n (lookup_any n data.to_canonical n)
                     data.to_canonical).gets_mem’
       by (unabbrev_all_tac \\ simp [])
  \\ pop_assum SUBST1_TAC
  \\ irule data_inv_filter_gets
  \\ irule data_inv_reinsert_canonical \\ gvs [ODD_EVEN]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[OpCurrHeap]:
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def, evaluate_def, AllCaseEqs()]
  \\ ‘data_inv (invalidate_data data dst) s ∧
      lookup dst (invalidate_data data dst).to_canonical = NONE’ by
       (rw [invalidate_data_def, keep_data_def] \\ gvs [empty_data_def])
  >- gvs [data_inv_set_var]
  >- gvs [data_inv_set_var]
  \\ qspecl_then [‘invalidate_data data dst’, ‘s’, ‘b’, ‘dst’, ‘src’,
                  ‘canonicalRegs' dst (invalidate_data data dst) src’,
                    ‘w’,
                  ‘data'’, ‘p'’] mp_tac add_to_data_OpCurrHeap_correct
  \\ impl_tac >- gvs []
  \\ gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Store]:
  fs [flat_exp_conventions_def]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Tick]:
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def, evaluate_def, AllCaseEqs()]
  \\ drule_then (qspecl_then [‘s.clock - 1’, ‘s.termdep’] assume_tac)
    data_inv_clock
  \\ ‘s with <|clock := s.clock - 1; termdep := s.termdep|> = dec_clock
    s’
       by gvs [dec_clock_def, state_component_equality]
  \\ gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[MustTerminate]:
  rpt gen_tac
  \\ strip_tac
  \\ rpt gen_tac
  \\ strip_tac
  \\ gs [word_cse_def]
  \\ pairarg_tac \\ gvs [evaluate_def, flat_exp_conventions_def]
  \\ gvs [AllCaseEqs()]
  \\ pairarg_tac \\ gvs []
  \\ pairarg_tac \\ gvs []
  \\ first_x_assum (drule_at Any)
  \\ Cases_on ‘res'' = SOME TimeOut’ \\ gvs []
  \\ impl_tac
  >- gvs [data_inv_clock]
  \\ rpt (strip_tac \\ gvs [data_inv_clock])
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Seq]:
  rpt gen_tac \\
  strip_tac \\
  rpt gen_tac \\
  strip_tac \\
  gvs [word_cse_def, evaluate_def, flat_exp_conventions_def] \\
  rpt (pairarg_tac \\ gvs []) \\
  reverse (gvs [AllCaseEqs(), evaluate_def])
  >- (pairarg_tac \\ gvs [] \\
      first_x_assum drule_all \\ gs []) \\
  pairarg_tac \\ gvs [] \\
  first_x_assum drule_all \\ gs [] \\
  strip_tac \\ gvs [] \\
  first_x_assum drule_all \\
  fs []
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Return]:
  fs [word_cse_def, evaluate_def, flat_exp_conventions_def]
  \\ rw []
  \\ gvs [AllCaseEqs()]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Raise]:
  fs [word_cse_def, evaluate_def, flat_exp_conventions_def]
  \\ rw []
  \\ gvs [AllCaseEqs()]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[If]:
  rpt gen_tac \\ strip_tac
  \\ rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def]
  \\ pairarg_tac \\ gvs []
  \\ pairarg_tac \\ gvs []
  \\ gvs [evaluate_def, flat_exp_conventions_def, AllCaseEqs()]
  >- (first_x_assum drule_all \\ strip_tac
      \\ gvs [] \\ strip_tac \\ gvs []
      \\ irule data_inv_merge_l
      \\ ‘wf_data (:'a) data’ by gvs [data_inv_def]
      \\ drule word_cse_wf_data
      \\ disch_then (qspec_then ‘c2’ assume_tac)
      \\ gvs [data_inv_def])
  \\ first_x_assum drule_all \\ strip_tac
  \\ gvs [] \\ strip_tac \\ gvs []
  \\ irule data_inv_merge_r
  \\ ‘wf_data (:'a) data’ by gvs [data_inv_def]
  \\ drule word_cse_wf_data
  \\ disch_then (qspec_then ‘c1’ assume_tac)
  \\ gvs [data_inv_def]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[LocValue]:
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def, evaluate_def, AllCaseEqs()]
  \\ ‘data_inv (invalidate_data data r) s ∧
      lookup r (invalidate_data data r).to_canonical = NONE’ by
       (rw [invalidate_data_def, keep_data_def] \\ gvs [empty_data_def])
  \\ drule_all add_to_data_LocValue_correct \\ gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Install]:
  gvs [word_cse_def]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[CodeBufferWrite]:
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def, evaluate_def, AllCaseEqs()]
  \\ irule data_inv_state_agree
  \\ qexists_tac ‘s’ \\ gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[DataBufferWrite]:
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def, evaluate_def, AllCaseEqs()]
  \\ irule data_inv_state_agree
  \\ qexists_tac ‘s’ \\ gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[FFI]:
  gvs [word_cse_def]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Call]:
  gvs [word_cse_def]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[StoreConsts]:
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def, evaluate_def, AllCaseEqs(), invalidate_regs_def,
          invalidate_data_def, keep_data_def]
  \\ rpt IF_CASES_TAC
  \\ gvs [data_inv_memory, data_inv_set_var, data_inv_unset_var]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[ShareInst]:
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def, evaluate_def, AllCaseEqs()]
  \\ Cases_on ‘op’
  \\ gvs [is_store_def, share_inst_def, sh_mem_load_def,
    sh_mem_load_byte_def,
          sh_mem_load16_def, sh_mem_load32_def, sh_mem_set_var_def,
          sh_mem_store_def, sh_mem_store_byte_def, sh_mem_store16_def,
          sh_mem_store32_def, invalidate_data_def, keep_data_def,
            AllCaseEqs()]
  >- (irule data_inv_state_agree \\ qexists_tac ‘s’ \\ gvs [])
  >- (irule data_inv_state_agree \\ qexists_tac ‘s’ \\ gvs [])
  >- (irule data_inv_state_agree \\ qexists_tac ‘s’ \\ gvs [])
  >- (irule data_inv_state_agree \\ qexists_tac ‘s’ \\ gvs [])
  \\ strip_tac \\ IF_CASES_TAC \\ gvs []
  \\ qpat_x_assum ‘sh_mem_set_var _ _ _ = _’ mp_tac
  \\ IF_CASES_TAC \\ simp [sh_mem_set_var_def]
  \\ qmatch_goalsub_abbrev_tac ‘sh_mem_set_var (SOME ffires) _ _’
  \\ Cases_on ‘ffires’ \\ simp [sh_mem_set_var_def]
  \\ strip_tac \\ gvs []
  \\ qmatch_goalsub_abbrev_tac ‘data_inv _ (sv with ffi := _)’
  \\ irule data_inv_state_agree \\ qexists_tac ‘sv’
  \\ gvs [Abbr ‘sv’, data_inv_set_var]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Loop]:
  rpt gen_tac >> strip_tac >>
  gvs [word_cse_def] >> rpt (pairarg_tac >> gvs []) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘evaluate (Loop _ _ _, _) = _’ mp_tac >>
  once_rewrite_tac [evaluate_def] >>
  simp [cut_state_def, UNCURRY, STOP_def] >>
  TOP_CASE_TAC >> simp [] >>
  Cases_on ‘evaluate (c, x)’ >> simp [] >> strip_tac >>
  ‘q ≠ SOME Error’ by
    (CCONTR_TAC >> gvs [cont_loop_def, exit_loop_def, AllCaseEqs()]) >>
  ‘evaluate (c', x) = (q, r)’ by
    (qpat_x_assum ‘∀v. cut_state _ _ = SOME v ⇒ _’ (qspec_then ‘x’
      mp_tac) >>
     impl_tac >- gvs [cut_state_def, AllCaseEqs()] >>
     disch_then (qspecl_then [‘q’,‘r’,‘empty_data’,‘c'’,‘_0’] mp_tac) >>
     gvs [flat_exp_conventions_def, data_inv_empty]) >>
  simp [] >>
  qpat_x_assum ‘(if cont_loop _ then _ else _) = _’ mp_tac >>
  IF_CASES_TAC >> simp []
  >- (IF_CASES_TAC >> simp [] >> strip_tac >>
      first_x_assum (qspecl_then [‘x’,‘q’,‘r’] mp_tac) >>
      impl_tac >- gvs [cut_state_def, AllCaseEqs()] >>
      disch_then (qspecl_then [‘res’,‘s'’,‘empty_data’,
        ‘Loop names c' exit_names’,‘empty_data’] mp_tac) >>
      simp [STOP_def, flat_exp_conventions_def, data_inv_empty,
        word_cse_def] >>
      rpt (pairarg_tac >> gvs []))
QED
*)

(* HOL4 ML code, not ported:
Finalise comp_correct;
*)

(* ---------------------------------------------------------------------
   ---
   SYNTACTIC CONVENTIONS

   word_cse emits only original instructions or Moves (the canonicalized
   arith only feeds the hash key, never the output program), so every
   syntactic convention transports with no well-formedness premise.
   ---------------------------------------------------------------------
     --- *)
