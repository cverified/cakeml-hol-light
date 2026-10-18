(* ======================================================== *)
(*  word_cseProof: ported from HOL4's
    compiler/backend/proofs/word_cseProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for word_cse
*)

needs "compiler/backend/reg_alloc/reg_alloc.ml";;
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
        wordSem_get_var r s = wordSem_get_var v s) /\
     (!r v.
        lookup r (knowledge_to_latest data) = SOME v ==>
        wordSem_get_var r s = wordSem_get_var v s) /\
     (!n c v.
        balanced_map_lookup listCmp (instToNumList (Const n c))
          (knowledge_instrs_mem data) = SOME v ==>
        lookup v (wordSem_state_locals s) = SOME (wordLang_Word c))
          /\
     (!(a:'a asm_arith) v.
        balanced_map_lookup listCmp (instToNumList (Arith a))
          (knowledge_instrs_mem data) = SOME v ==>
        (?w. wordSem_get_var v s = SOME w /\
            wordSem_evaluate (Inst (Arith a),s) =
              (NONE,wordSem_set_var (firstRegOfArith a) w s))) /\
     (!op src v.
        balanced_map_lookup listCmp (OpCurrHeapToNumList op src)
          (knowledge_instrs_mem data) = SOME v ==>
        (?w. wordSem_word_exp s (wordLang_Op op [Var src;
          wordLang_Lookup CurrHeap]) = SOME w /\
            wordSem_get_var v s = SOME w)) /\
     (!l v.
        balanced_map_lookup listCmp [48; l] (knowledge_instrs_mem
          data) = SOME v ==>
        lookup v (wordSem_state_locals s) = SOME (Loc l 0)) /\
     (!x v.
        ALOOKUP (knowledge_gets_mem data) x = SOME v ==>
        (?w. FLOOKUP (wordSem_state_store s) x = SOME w /\
          wordSem_get_var v s = SOME w)) /\
     (!op a ofs v.
        ~is_store op /\
        balanced_map_lookup listCmp (loadToNumList op a ofs)
          (knowledge_loads_mem data) = SOME v ==>
        (?w. wordSem_get_var v s = SOME w /\
            (!r. wordSem_evaluate (Inst (asm_Mem op r (Addr a
              ofs)),s) = (NONE,wordSem_set_var r w s))))`;;

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

(* HOL4 word_cseProofScript.sml:2935-2937: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:2939-3092: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3094-3121: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3123-3162: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3164-3166: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3168-3171: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3173-3180: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3182-3190: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3192-3258: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3260-3289: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3291-3293: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3295-3297: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3299-3301: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3303: ML code, not ported *)

(* proof of the cases *)

(* HOL4 word_cseProofScript.sml:3343-3345: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3347-3349: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3351-3355: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3357-3484: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3486-3488: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3490-3547: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3549-3600: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3602-3615: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3617-3619: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3621-3628: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3630-3645: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3647-3662: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3664-3668: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3670-3674: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3676-3697: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3699-3706: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3708-3710: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3712-3717: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3719-3724: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3726-3728: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3730-3732: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3734-3740: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3742-3763: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3765-3791: ML code, not ported *)

(* HOL4 word_cseProofScript.sml:3793: ML code, not ported *)

(* ---------------------------------------------------------------------
   ---
   SYNTACTIC CONVENTIONS

   word_cse emits only original instructions or Moves (the canonicalized
   arith only feeds the hash key, never the output program), so every
   syntactic convention transports with no well-formedness premise.
   ---------------------------------------------------------------------
     --- *)
