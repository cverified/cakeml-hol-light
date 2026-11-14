(* ======================================================== *)
(*  word_cseProof: ported from HOL4's
    compiler/backend/proofs/word_cseProofScript.sml
    A proof theory about word_cse.ml, with 4 definitions and 136
    theorems.  Needed by word_to_wordProof.ml.  *)
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
needs "lib/balanced_map.ml";;
needs "lib/comparison.ml";;
needs "lib/sptree.ml";;
needs "lib/ternaryComparisons.ml";;
needs "lib/toto.ml";;
needs "misc/misc.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "word_cseProof"
  ["reg_alloc"; "wordConvs"; "wordLang"; "wordProps"; "wordSem";
   "word_cse"; "word_simp"];;

let _ = do_list hide_constant ["Greater"];;
(* HOL4 ancestors outside the port: alist *)

(* The reads of a stored arith fact, tracked as self-mappings in
   to_canonical (registered at fact creation), so that a later write to any
   of them resets the data. *)
let in_names_set_def = new_definition
  `in_names_set (a:'a asm_arith) tc <=>
     ALL (\r. sptree_lookup r tc = SOME r) (arithReads a)`;;

(* The invariant is factored into a STATE-FREE syntactic part (wf_data) and
   a state-dependent semantic part (sem_inv). The If-join merge needs
   syntactic facts about the not-taken branch's data without having run that
   branch: wf_data is established for it by the standalone syntactic theorem
   word_cse_wf_data. The (:'a) itself argument ties the quantified arith
   instructions to the state's word width. *)
let wf_data_def = new_definition
  `wf_data (:'a) (data:knowledge) <=>
     (!r v.
        balanced_map_lookup r (knowledge_to_canonical data) = SOME v
          ==>
        balanced_map_lookup v (knowledge_to_canonical data) = SOME v
          /\ ODD r /\ ODD v) /\
     (!r v.
        balanced_map_lookup r (knowledge_to_latest data) = SOME v ==>
        r IN domain (knowledge_to_canonical data) /\
        v IN domain (knowledge_to_canonical data)) /\
     (!k v.
        balanced_map_lookup listCmp k (knowledge_instrs_mem data) =
          SOME v ==>
        balanced_map_lookup v (knowledge_to_canonical data) = SOME v)
          /\
     (!(a:'a asm_arith) v.
        balanced_map_lookup listCmp (instToNumList (asm_Arith a))
          (knowledge_instrs_mem data) = SOME v ==>
        in_names_set a (knowledge_to_canonical data) /\ can_mem_arith
          a) /\
     (!op src v.
        balanced_map_lookup listCmp (OpCurrHeapToNumList op src)
          (knowledge_instrs_mem data) = SOME v ==>
        balanced_map_lookup src (knowledge_to_canonical data) = SOME
          src) /\
     (!x v.
        ALOOKUP (knowledge_gets_mem data) x = SOME v ==>
        balanced_map_lookup v (knowledge_to_canonical data) = SOME v)
          /\
     ALL_DISTINCT (MAP FST (knowledge_gets_mem data)) /\
     balanced_map_invariant listCmp (knowledge_instrs_mem data) /\
     (!k v.
        balanced_map_lookup listCmp k (knowledge_loads_mem data) =
          SOME v ==>
        balanced_map_lookup v (knowledge_to_canonical data) = SOME v)
          /\
     (!op a (ofs:'a word) v.
        balanced_map_lookup listCmp (loadToNumList op a ofs)
          (knowledge_loads_mem data) = SOME v ==>
        balanced_map_lookup a (knowledge_to_canonical data) = SOME a)
          /\
     balanced_map_invariant listCmp (knowledge_loads_mem data)`;;

let sem_inv_def = new_definition
  `sem_inv (data:knowledge) (s:('a,'c,'ffi)wordSem_state) <=>
     (!r v.
        balanced_map_lookup r (knowledge_to_canonical data) = SOME v
          ==>
        wordSem_get_var r s = wordSem_get_var v s) /\
     (!r v.
        balanced_map_lookup r (knowledge_to_latest data) = SOME v ==>
        wordSem_get_var r s = wordSem_get_var v s) /\
     (!n c v.
        balanced_map_lookup listCmp (instToNumList (wordLang_Const n
          c)) (knowledge_instrs_mem data) = SOME v ==>
        balanced_map_lookup v (wordSem_state_locals s) = SOME
          (wordLang_Word c)) /\
     (!(a:'a asm_arith) v.
        balanced_map_lookup listCmp (instToNumList (asm_Arith a))
          (knowledge_instrs_mem data) = SOME v ==>
        (?w. wordSem_get_var v s = SOME w /\
            wordSem_evaluate (wordLang_Inst (asm_Arith a),s) =
              (NONE,wordSem_set_var (firstRegOfArith a) w s))) /\
     (!op src v.
        balanced_map_lookup listCmp (OpCurrHeapToNumList op src)
          (knowledge_instrs_mem data) = SOME v ==>
        (?w. wordSem_word_exp s (wordLang_Op op [wordLang_Var src;
          wordLang_Lookup CurrHeap]) = SOME w /\
            wordSem_get_var v s = SOME w)) /\
     (!l v.
        balanced_map_lookup listCmp [48; l] (knowledge_instrs_mem
          data) = SOME v ==>
        balanced_map_lookup v (wordSem_state_locals s) = SOME
          (wordLang_Loc l 0)) /\
     (!x v.
        ALOOKUP (knowledge_gets_mem data) x = SOME v ==>
        (?w. FLOOKUP (wordSem_state_store s) x = SOME w /\
          wordSem_get_var v s = SOME w)) /\
     (!op a ofs v.
        ~(is_store op) /\
        balanced_map_lookup listCmp (loadToNumList op a ofs)
          (knowledge_loads_mem data) = SOME v ==>
        (?w. wordSem_get_var v s = SOME w /\
            (!r. wordSem_evaluate (wordLang_Inst (asm_Mem op r
              (Addr a ofs)),s) = (NONE,wordSem_set_var r w s))))`;;

let data_inv_def = new_definition
  `data_inv (data:knowledge) (s:('a,'c,'ffi)wordSem_state) <=>
     wf_data (:'a) data /\ sem_inv data s`;;

let canonicalRegs_correct = prove
 (`!data r s. data_inv data s ==> wordSem_get_var (canonicalRegs data
  r) s = wordSem_get_var r s`,
  CHEAT_TAC);;
add_simp canonicalRegs_correct;;

let canonicalRegs'_correct = prove
 (`!a data r s. data_inv data s ==> wordSem_get_var (canonicalRegs' a
  data r) s = wordSem_get_var r s`,
  CHEAT_TAC);;
add_simp canonicalRegs'_correct;;

let canonicalRegs_correct_bis = prove
 (`!data r s. data_inv data s ==> balanced_map_lookup (canonicalRegs
  data r) (wordSem_state_locals s) = balanced_map_lookup r
  (wordSem_state_locals s)`,
  CHEAT_TAC);;
add_simp canonicalRegs_correct_bis;;

let canonicalArith_correct = prove
 (`!data s a. data_inv data s ==> wordSem_inst (asm_Arith
  (canonicalArith data a)) s = wordSem_inst (asm_Arith a) s`,
  CHEAT_TAC);;
add_simp canonicalArith_correct;;

let wordToNum_unique = prove
 (`!c1 c2. wordToNum c1 = wordToNum c2 <=> c1 = c2`,
  CHEAT_TAC);;
add_simp wordToNum_unique;;

let arithOpToNum_eq = prove
 (`!op1 op2. arithOpToNum op1 = arithOpToNum op2 <=> op1 = op2`,
  CHEAT_TAC);;
add_simp arithOpToNum_eq;;

let memOpToNum_eq = prove
 (`!op1 op2. memOpToNum op1 = memOpToNum op2 <=> op1 = op2`,
  CHEAT_TAC);;
add_simp memOpToNum_eq;;

let firstRegOfArith_canonicalArith = prove
 (`!data a. firstRegOfArith (canonicalArith data a) = firstRegOfArith
  a`,
  CHEAT_TAC);;
add_simp firstRegOfArith_canonicalArith;;

(* Some usefull proofs to automize *)

let data_inv_locals = prove
 (`!s. wordSem_state_locals_fupd (K (wordSem_state_locals s)) s = s`,
  CHEAT_TAC);;
add_simp data_inv_locals;;

let insert_eq = prove
 (`!(n1:num) n2 v1 v2 l. balanced_map_insert n1 v1 l =
  balanced_map_insert n1 v2 l <=> v1 = v2`,
  CHEAT_TAC);;

(* A stored arith fact concerns a can_mem_arith shape, whose evaluation is
   a single set_var of a value computed from the registers it reads; the
   fact transports across a write to any register the instruction does not
   read. *)
let evaluate_arith_set_var = prove
 (`!a r u w s.
     can_mem_arith a /\ ~(MEM r (arithReads a)) ==>
     (wordSem_evaluate (wordLang_Inst (asm_Arith a),wordSem_set_var r
       u s) =
        (NONE,wordSem_set_var (firstRegOfArith a) w (wordSem_set_var
          r u s)) <=>
      wordSem_evaluate (wordLang_Inst (asm_Arith a),s) =
        (NONE,wordSem_set_var (firstRegOfArith a) w s))`,
  CHEAT_TAC);;

(* A successful load evaluation determines the loaded value from the address
   register and memory alone, so the same load at ANY destination evaluates
   the same way — this gives the ∀-quantified-destination form stored by the
   loads clause of sem_inv. *)
let evaluate_load_any_dest = prove
 (`!op r0 a ofs w s r.
     ~(is_store op) /\
     wordSem_evaluate (wordLang_Inst (asm_Mem op r0 (Addr a ofs)),s)
       = (NONE,wordSem_set_var r0 w s) ==>
     wordSem_evaluate (wordLang_Inst (asm_Mem op r (Addr a ofs)),s)
       = (NONE,wordSem_set_var r w s)`,
  CHEAT_TAC);;

(* A load reads its address register, the memory fields and be; the
   evaluation equation transports across a write to any OTHER register, for
   any destination (including the written one, by insert collapsing). *)
let evaluate_load_set_var = prove
 (`!op r a ofs n u w s.
     ~(is_store op) /\ ~(a = n) ==>
     (wordSem_evaluate (wordLang_Inst (asm_Mem op r (Addr a
       ofs)),wordSem_set_var n u s) =
        (NONE,wordSem_set_var r w (wordSem_set_var n u s)) <=>
      wordSem_evaluate (wordLang_Inst (asm_Mem op r (Addr a
        ofs)),s) = (NONE,wordSem_set_var r w s))`,
  CHEAT_TAC);;

(* A load's address register may be replaced by any register holding the
   same value — the bridge from the executed address to its canonical
   representative. *)
(* [local] *)
let evaluate_load_change_addr = prove
 (`!op r a a' ofs w (s:('a,'c,'ffi)wordSem_state).
     ~(is_store op) /\
     balanced_map_lookup a' (wordSem_state_locals s) =
       balanced_map_lookup a (wordSem_state_locals s) /\
     wordSem_evaluate (wordLang_Inst (asm_Mem op r (Addr a ofs)),s) =
       (NONE,wordSem_set_var r w s) ==>
     wordSem_evaluate (wordLang_Inst (asm_Mem op r (Addr a'
       ofs)),s) = (NONE,wordSem_set_var r w s)`,
  CHEAT_TAC);;

(* A storable arith instruction reads and writes registers only; its
   evaluation equation is insensitive to the memory contents. *)
(* [local] *)
let evaluate_arith_memory = prove
 (`!a w s m.
     can_mem_arith a ==>
     (wordSem_evaluate (wordLang_Inst (asm_Arith
       a),wordSem_state_memory_fupd (K m) s) =
        (NONE,wordSem_state_memory_fupd (K m) (wordSem_set_var
          (firstRegOfArith a) w s)) <=>
      wordSem_evaluate (wordLang_Inst (asm_Arith a),s) =
        (NONE,wordSem_set_var (firstRegOfArith a) w s))`,
  CHEAT_TAC);;

(* Every register mentioned by the invariant lies in the domain of
   to_canonical, so an untracked register is unmentioned. *)
let wf_data_untracked = prove
 (`!data n.
     wf_data (:'a) data /\ sptree_lookup n (knowledge_to_canonical
       data) = NONE ==>
     (!r v. balanced_map_lookup r (knowledge_to_canonical data) =
       SOME v ==> ~(r = n) /\ ~(v = n)) /\
     (!r v. balanced_map_lookup r (knowledge_to_latest data) = SOME v
       ==> ~(r = n) /\ ~(v = n)) /\
     (!k v. balanced_map_lookup listCmp k (knowledge_instrs_mem data)
       = SOME v ==> ~(v = n)) /\
     (!(a:'a asm_arith) v.
        balanced_map_lookup listCmp (instToNumList (asm_Arith a))
          (knowledge_instrs_mem data) = SOME v ==>
        ~(MEM n (arithReads a)) /\ can_mem_arith a) /\
     (!op src v.
        balanced_map_lookup listCmp (OpCurrHeapToNumList op src)
          (knowledge_instrs_mem data) = SOME v ==> ~(src = n)) /\
     (!x v. ALOOKUP (knowledge_gets_mem data) x = SOME v ==> ~(v =
       n)) /\
     (!k v. balanced_map_lookup listCmp k (knowledge_loads_mem data)
       = SOME v ==> ~(v = n)) /\
     (!op a (ofs:'a word) v.
        balanced_map_lookup listCmp (loadToNumList op a ofs)
          (knowledge_loads_mem data) = SOME v ==> ~(a = n))`,
  CHEAT_TAC);;

let data_inv_set_var = prove
 (`!data s n v.
     sptree_lookup n (knowledge_to_canonical data) = NONE ==>
     data_inv data (wordSem_set_var n v s) = data_inv data s`,
  CHEAT_TAC);;

(* The unset_var (locals-delete) clones of the set_var transports, for
   StoreConsts' two unsets. *)
(* [local] *)
let evaluate_arith_unset_var = prove
 (`!a r w (s:('a,'c,'ffi)wordSem_state).
     can_mem_arith a /\ ~(MEM r (arithReads a)) ==>
     (wordSem_evaluate (wordLang_Inst (asm_Arith a),wordSem_unset_var
       r s) =
        (NONE,wordSem_set_var (firstRegOfArith a) w
          (wordSem_unset_var r s)) <=>
      wordSem_evaluate (wordLang_Inst (asm_Arith a),s) =
        (NONE,wordSem_set_var (firstRegOfArith a) w s))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_load_unset_var = prove
 (`!op r a ofs n w (s:('a,'c,'ffi)wordSem_state).
     ~(is_store op) /\ ~(a = n) ==>
     (wordSem_evaluate (wordLang_Inst (asm_Mem op r (Addr a
       ofs)),wordSem_unset_var n s) =
        (NONE,wordSem_set_var r w (wordSem_unset_var n s)) <=>
      wordSem_evaluate (wordLang_Inst (asm_Mem op r (Addr a
        ofs)),s) = (NONE,wordSem_set_var r w s))`,
  CHEAT_TAC);;

let data_inv_unset_var = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) n.
     sptree_lookup n (knowledge_to_canonical data) = NONE ==>
     data_inv data (wordSem_unset_var n s) = data_inv data s`,
  CHEAT_TAC);;

let not_seen_data_inv_alist_insert = prove
 (`!data s l r v.
     sptree_lookup r (knowledge_to_canonical data) = NONE ==>
     data_inv data (wordSem_state_locals_fupd (K l) s) ==>
     data_inv data (wordSem_state_locals_fupd (K
       (balanced_map_insert r v l)) s)`,
  CHEAT_TAC);;
add_simp not_seen_data_inv_alist_insert;;

let listCmpEq_correct = prove
 (`!L1 L2. listCmp L1 L2 = asm_Equal <=> L1 = L2`,
  CHEAT_TAC);;

let antisym_listCmp = prove
 (`!x y. listCmp x y = GREATER <=> listCmp y x = asm_Less`,
  CHEAT_TAC);;

let transit_listCmp = prove
 (`!x y z. listCmp x y = asm_Less /\ listCmp y z = asm_Less ==>
  listCmp x z = asm_Less`,
  CHEAT_TAC);;

let TotOrd_listCmp = prove
 (`TotOrd listCmp`,
  CHEAT_TAC);;
add_simp TotOrd_listCmp;;

let good_cmp_listCmp = prove
 (`good_cmp listCmp`,
  CHEAT_TAC);;
add_simp good_cmp_listCmp;;

let lookup_listCmp_empty = prove
 (`balanced_map_lookup listCmp k balanced_map_empty = NONE`,
  CHEAT_TAC);;
add_simp lookup_listCmp_empty;;

let data_inv_empty = prove
 (`!s. data_inv empty_data s`,
  CHEAT_TAC);;
add_simp data_inv_empty;;

let invariant_listCmp_empty = prove
 (`balanced_map_invariant listCmp balanced_map_empty`,
  CHEAT_TAC);;
add_simp invariant_listCmp_empty;;

(* The loads-wipe transport: a pure memory write preserves the whole
   invariant once the load facts are wiped — every other clause reads only
   locals, store and code. Used by the Mem-store and StoreConsts cases. *)
let data_inv_memory = prove
 (`!data s m.
     data_inv data s ==>
     data_inv (knowledge_loads_mem_fupd (K balanced_map_empty)
       data) (wordSem_state_memory_fupd (K m) s)`,
  CHEAT_TAC);;

(* A storable arith instruction reads and writes locals only; its evaluation
   equation transports to any state with the same locals. *)
(* [local] *)
let evaluate_arith_agree = prove
 (`!a w (s1:('a,'c,'ffi)wordSem_state) (s2:('a,'c,'ffi)wordSem_state).
     wordSem_evaluate (wordLang_Inst (asm_Arith a),s1) =
       (NONE,wordSem_set_var (firstRegOfArith a) w s1) /\
     can_mem_arith a /\ wordSem_state_locals s2 =
       wordSem_state_locals s1 ==>
     wordSem_evaluate (wordLang_Inst (asm_Arith a),s2) =
       (NONE,wordSem_set_var (firstRegOfArith a) w s2)`,
  CHEAT_TAC);;

(* A load reads its address register, the memory fields and be; its
   evaluation equation transports to any state agreeing on those. *)
(* [local] *)
let evaluate_load_agree = prove
 (`!op r a ofs w (s1:('a,'c,'ffi)wordSem_state)
  (s2:('a,'c,'ffi)wordSem_state).
     wordSem_evaluate (wordLang_Inst (asm_Mem op r (Addr a ofs)),s1)
       = (NONE,wordSem_set_var r w s1) /\
     ~(is_store op) /\ wordSem_state_locals s2 = wordSem_state_locals
       s1 /\ wordSem_state_memory s2 = wordSem_state_memory s1 /\
       wordSem_state_mdomain
     s2 = wordSem_state_mdomain s1 /\ wordSem_state_be s2 =
       wordSem_state_be s1 ==>
     wordSem_evaluate (wordLang_Inst (asm_Mem op r (Addr a
       ofs)),s2) = (NONE,wordSem_set_var r w s2)`,
  CHEAT_TAC);;

(* The generic state-agreement transport: the whole invariant depends only
   on locals, store and the memory fields.  Covers buffer writes, ffi
   extensions and stack changes in one lemma. *)
let data_inv_state_agree = prove
 (`!data (s1:('a,'c,'ffi)wordSem_state) (s2:('a,'c,'ffi)wordSem_state).
     data_inv data s1 /\ wordSem_state_locals
     s2 = wordSem_state_locals s1 /\ wordSem_state_store s2 =
       wordSem_state_store s1 /\ wordSem_state_memory s2 =
       wordSem_state_memory s1 /\ wordSem_state_mdomain
     s2 = wordSem_state_mdomain s1 /\ wordSem_state_be s2 =
       wordSem_state_be s1 ==>
     data_inv data s2`,
  CHEAT_TAC);;

(* IF-JOIN MERGE SUPPORT

   bm_inter_eq_acc m2 m1 acc inserts into acc exactly the entries of m1 that
   are present with an equal value in m2; characterised pointwise on to_fmap. *)
let bm_inter_eq_acc_thm = prove
 (`!m2 m1 acc.
     balanced_map_invariant listCmp m2 /\ balanced_map_invariant
       listCmp m1 /\ balanced_map_invariant listCmp acc ==>
     balanced_map_invariant listCmp (bm_inter_eq_acc m2 m1 acc) /\
     (!ks. FLOOKUP (to_fmap listCmp (bm_inter_eq_acc m2 m1 acc)) ks =
          (match FLOOKUP (to_fmap listCmp m1) ks with NONE ->
            FLOOKUP (to_fmap listCmp acc) ks | SOME v -> (if FLOOKUP
            (to_fmap listCmp m2) ks = SOME v then SOME v else FLOOKUP
            (to_fmap listCmp acc) ks)))`,
  CHEAT_TAC);;

let invariant_bm_inter_eq = prove
 (`!m1 m2.
     balanced_map_invariant listCmp m1 /\ balanced_map_invariant
       listCmp m2 ==>
     balanced_map_invariant listCmp (bm_inter_eq m1 m2)`,
  CHEAT_TAC);;

let lookup_bm_inter_eq = prove
 (`!m1 m2 k v.
     balanced_map_invariant listCmp m1 /\ balanced_map_invariant
       listCmp m2 ==>
     (balanced_map_lookup listCmp k (bm_inter_eq m1 m2) = SOME v <=>
      balanced_map_lookup listCmp k m1 = SOME v /\
      balanced_map_lookup listCmp k m2 = SOME v)`,
  CHEAT_TAC);;

(* [local] *)
let ALL_DISTINCT_MAP_FST_FILTER = prove
 (`!l P. ALL_DISTINCT (MAP FST l) ==> ALL_DISTINCT (MAP FST (FILTER P
  l))`,
  CHEAT_TAC);;

(* A merged fact is present (with equal value) in both branches' data; its
   semantic content comes from whichever branch actually ran, its syntactic
   well-formedness from both. *)
let data_inv_merge_l = prove
 (`!d1 d2 (s:('a,'c,'ffi)wordSem_state).
     wf_data (:'a) d1 /\ wf_data (:'a) d2 /\ sem_inv d1 s ==>
     data_inv (merge_data d1 d2) s`,
  CHEAT_TAC);;

let data_inv_merge_r = prove
 (`!d1 d2 (s:('a,'c,'ffi)wordSem_state).
     wf_data (:'a) d1 /\ wf_data (:'a) d2 /\ sem_inv d2 s ==>
     data_inv (merge_data d1 d2) s`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------
   KNOWLEDGE-UPDATE SUPPORT

   Lookups in an extended instruction map, read registration, transport of
   data_inv across the writes a rewritten program performs, and generic
   extension lemmas for the knowledge fields.
   ------------------------------------------------------------------------ *)

let lookup_insert_listCmp = prove
 (`!k i v m.
     balanced_map_invariant listCmp m ==>
     balanced_map_invariant listCmp (balanced_map_insert listCmp i v
       m) /\
     balanced_map_lookup listCmp k (balanced_map_insert listCmp i v
       m) =
     (if k = i then SOME v else balanced_map_lookup listCmp k m)`,
  CHEAT_TAC);;

let register_read_simps = prove
 (`knowledge_instrs_mem
     (register_read data r) = knowledge_instrs_mem data /\
       knowledge_to_latest
     (register_read data r) = knowledge_to_latest data /\
       knowledge_gets_mem
     (register_read data r) = knowledge_gets_mem data /\
       knowledge_loads_mem
     (register_read data r) = knowledge_loads_mem data`,
  CHEAT_TAC);;
add_simp register_read_simps;;

let register_reads_simps = prove
 (`!rs data. knowledge_instrs_mem
     (register_reads data rs) = knowledge_instrs_mem data /\
       knowledge_to_latest
     (register_reads data rs) = knowledge_to_latest data /\
       knowledge_gets_mem
     (register_reads data rs) = knowledge_gets_mem data /\
       knowledge_loads_mem
     (register_reads data rs) = knowledge_loads_mem data`,
  CHEAT_TAC);;
add_simp register_reads_simps;;

let lookup_register_read = prove
 (`sptree_lookup x (knowledge_to_canonical (register_read data r)) =
   (if x = r /\ ~(EVEN r) /\ sptree_lookup r
     (knowledge_to_canonical data) = NONE then SOME r else
     sptree_lookup x (knowledge_to_canonical data))`,
  CHEAT_TAC);;

let lookup_register_reads = prove
 (`!rs data x.
     sptree_lookup x (knowledge_to_canonical (register_reads data
       rs)) =
     (if MEM x rs /\ ~(EVEN x) /\ sptree_lookup x
       (knowledge_to_canonical data) = NONE then SOME x else
       sptree_lookup x (knowledge_to_canonical data))`,
  CHEAT_TAC);;

(* Extending to_canonical with a fresh key mapped to itself or to an
   already-canonical register preserves the invariant: the fresh key is
   unmentioned elsewhere, and existing self-maps survive the insert. *)
let data_inv_insert_to_canonical = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) x y.
     data_inv data s /\
     sptree_lookup x (knowledge_to_canonical data) = NONE /\
     sptree_lookup y (balanced_map_insert x y (knowledge_to_canonical
       data)) = SOME y /\
     ODD x /\ ODD y /\
     wordSem_get_var x s = wordSem_get_var y s ==>
     data_inv (knowledge_to_canonical_fupd (K (balanced_map_insert
       x y (knowledge_to_canonical data))) data) s`,
  CHEAT_TAC);;

(* to_latest entries only require domain membership and agreeing values. *)
let data_inv_insert_to_latest = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) x y.
     data_inv data s /\
     x IN domain (knowledge_to_canonical data) /\ y IN domain
       (knowledge_to_canonical data) /\
     wordSem_get_var x s = wordSem_get_var y s ==>
     data_inv (knowledge_to_latest_fupd (K (balanced_map_insert x y
       (knowledge_to_latest data))) data) s`,
  CHEAT_TAC);;

(* Record a fresh Get fact: the destination becomes self-tracked and the
   store name maps to it.  Matches the Get-miss arm of word_cse. *)
(* [local] *)
let data_inv_insert_gets = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) name v w.
     data_inv data s /\
     sptree_lookup v (knowledge_to_canonical data) = NONE /\ ODD v /\
     ALOOKUP (knowledge_gets_mem data) name = NONE /\
     FLOOKUP (wordSem_state_store s) name = SOME w /\ wordSem_get_var
       v s = SOME w ==>
     data_inv (knowledge_gets_mem_fupd (K (CONS (name,v)
       (knowledge_gets_mem data))) (knowledge_to_latest_fupd (K
       (balanced_map_insert v v (knowledge_to_latest data)))
       (knowledge_to_canonical_fupd (K (balanced_map_insert v v
       (knowledge_to_canonical data))) data))) s`,
  CHEAT_TAC);;

(* Dropping store facts never hurts. Matches the Set-arm FILTER. *)
(* [local] *)
let data_inv_filter_gets = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) x.
     data_inv data s ==>
     data_inv (knowledge_gets_mem_fupd (K (FILTER (\(m,n). ~(m =
       x)) (knowledge_gets_mem data))) data) s`,
  CHEAT_TAC);;

(* Record a true store fact about an already-tracked register.  Matches the
   Set-arm cons. *)
(* [local] *)
let data_inv_cons_gets = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) x h w.
     data_inv data s /\
     ALOOKUP (knowledge_gets_mem data) x = NONE /\
     sptree_lookup h (knowledge_to_canonical data) = SOME h /\
     FLOOKUP (wordSem_state_store s) x = SOME w /\ wordSem_get_var h
       s = SOME w ==>
     data_inv (knowledge_gets_mem_fupd (K (CONS (x,h)
       (knowledge_gets_mem data))) data) s`,
  CHEAT_TAC);;

(* A store write to a name no fact mentions preserves the invariant: only
   the OpCurrHeap clause (CurrHeap) and the gets clauses read the store. *)
let data_inv_set_store = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) x w.
     data_inv data s /\ ~(x = CurrHeap) /\ ALOOKUP
       (knowledge_gets_mem data) x = NONE ==>
     data_inv data (wordSem_set_store x w s)`,
  CHEAT_TAC);;

(* Re-registering a register's canonical entry is sound: fresh self-map for
   an untracked register, no-op for a tracked one. *)
(* [local] *)
let data_inv_reinsert_canonical = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) v.
     data_inv data s /\ ODD v ==>
     data_inv (knowledge_to_canonical_fupd (K
                 (balanced_map_insert v (lookup_any v
                   (knowledge_to_canonical data) v)
                   (knowledge_to_canonical
                   data))) data) s`,
  CHEAT_TAC);;

let empty_data_loads_wipe = prove
 (`knowledge_loads_mem_fupd (K balanced_map_empty)
     empty_data = empty_data`,
  CHEAT_TAC);;
add_simp empty_data_loads_wipe;;

let lookup_empty_data = prove
 (`sptree_lookup r (knowledge_to_canonical empty_data) = NONE`,
  CHEAT_TAC);;
add_simp lookup_empty_data;;

let data_inv_register_read = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) r.
     data_inv data s ==> data_inv (register_read data r) s`,
  CHEAT_TAC);;

let data_inv_register_reads = prove
 (`!rs data (s:('a,'c,'ffi)wordSem_state).
     data_inv data s ==> data_inv (register_reads data rs) s`,
  CHEAT_TAC);;

(* Invalidation facts for multi-output instructions. *)
(* [local] *)
let lookup_invalidate_regs_mono = prove
 (`!ws data r.
     sptree_lookup r (knowledge_to_canonical data) = NONE ==>
     sptree_lookup r (knowledge_to_canonical (invalidate_regs data
       ws)) = NONE`,
  CHEAT_TAC);;

(* [local] *)
let lookup_invalidate_regs = prove
 (`!ws data r.
     MEM r ws ==>
     sptree_lookup r (knowledge_to_canonical (invalidate_regs data
       ws)) = NONE`,
  CHEAT_TAC);;

(* [local] *)
let data_inv_invalidate_regs = prove
 (`!ws data (s:('a,'c,'ffi)wordSem_state).
     data_inv data s ==> data_inv (invalidate_regs data ws) s`,
  CHEAT_TAC);;

(* The invariant never reads the fp registers. *)
let data_inv_set_fp_var = prove
 (`!data v x (s:('a,'c,'ffi)wordSem_state).
     data_inv data (wordSem_set_fp_var v x s) = data_inv data s`,
  CHEAT_TAC);;
add_simp data_inv_set_fp_var;;

(* [local] *)
let with_locals_insert = prove
 (`wordSem_state_locals_fupd (K (balanced_map_insert r v l))
     s = wordSem_set_var r v (wordSem_state_locals_fupd (K l) s)`,
  CHEAT_TAC);;

(* [local] *)
let data_inv_alist_insert_locals = prove
 (`!xs ys data (s:('a,'c,'ffi)wordSem_state) l.
     ALL (\x. sptree_lookup x (knowledge_to_canonical data) = NONE)
       xs ==>
     (data_inv data (wordSem_state_locals_fupd (K (alist_insert xs ys
       l)) s) <=>
      data_inv data (wordSem_state_locals_fupd (K l) s))`,
  CHEAT_TAC);;

(* data_inv is insensitive to writes to untracked registers. *)
let data_inv_set_vars = prove
 (`!xs ys data (s:('a,'c,'ffi)wordSem_state).
     ALL (\x. sptree_lookup x (knowledge_to_canonical data) = NONE)
       xs ==>
     (data_inv data (wordSem_set_vars xs ys s) <=> data_inv data s)`,
  CHEAT_TAC);;

(* The Move every cache hit emits. *)
let evaluate_Move1 = prove
 (`!pri r k w (s:('a,'c,'ffi)wordSem_state).
     wordSem_get_var k s = SOME w ==>
     wordSem_evaluate (wordLang_Move pri [(r,k)],s) =
       (NONE,wordSem_set_var r w s)`,
  CHEAT_TAC);;

let shiftToNum_eq = prove
 (`!s1 s2. shiftToNum s1 = shiftToNum s2 <=> s1 = s2`,
  CHEAT_TAC);;
add_simp shiftToNum_eq;;

(* The instruction-map key of a can_mem_arith instruction determines its
   operation and reads (but not its destination), hence also the value it
   computes: two instructions with the same key evaluate identically up to
   the destination register. The sem_inv arith clause quantifies over all
   instructions with a stored key, so inserting a fact for one of them must
   yield the fact for all of them. *)
let arith_keys_eq = prove
 (`!a1 a2.
     can_mem_arith a1 /\ arithToNumList a1 = arithToNumList a2 ==>
     can_mem_arith a2 /\ arithReads a2 = arithReads a1 /\
     (!(s:('a,'c,'ffi)wordSem_state) w.
       wordSem_evaluate (wordLang_Inst (asm_Arith a1),s) =
         (NONE,wordSem_set_var (firstRegOfArith a1) w s) ==>
       wordSem_evaluate (wordLang_Inst (asm_Arith a2),s) =
         (NONE,wordSem_set_var (firstRegOfArith a2) w s))`,
  CHEAT_TAC);;

(* Storing a new fact: one lemma per key family, each requiring the holder
   to be self-mapped and the fact's semantic content to hold. *)
(* [local] *)
let data_inv_insert_instrs_Const = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) r n (w:'a word).
     data_inv data s /\
     sptree_lookup r (knowledge_to_canonical data) = SOME r /\
     balanced_map_lookup r (wordSem_state_locals s) = SOME
       (wordLang_Word w) ==>
     data_inv (knowledge_instrs_mem_fupd (K
                 (balanced_map_insert listCmp (instToNumList
                   (wordLang_Const n w)) r (knowledge_instrs_mem
                   data))) data) s`,
  CHEAT_TAC);;

(* [local] *)
let data_inv_insert_instrs_Arith = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) r (a:'a asm_arith) w.
     data_inv data s /\
     sptree_lookup r (knowledge_to_canonical data) = SOME r /\
     can_mem_arith a /\ in_names_set a (knowledge_to_canonical data)
       /\
     wordSem_get_var r s = SOME w /\
     wordSem_evaluate (wordLang_Inst (asm_Arith a),s) =
       (NONE,wordSem_set_var (firstRegOfArith a) w s) ==>
     data_inv (knowledge_instrs_mem_fupd (K
                 (balanced_map_insert listCmp (instToNumList
                   (asm_Arith a)) r (knowledge_instrs_mem data)))
                   data) s`,
  CHEAT_TAC);;

(* [local] *)
let data_inv_insert_instrs_OpCurrHeap = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) r op src w.
     data_inv data s /\
     sptree_lookup r (knowledge_to_canonical data) = SOME r /\
     sptree_lookup src (knowledge_to_canonical data) = SOME src /\
     wordSem_word_exp s (wordLang_Op op [wordLang_Var src;
       wordLang_Lookup CurrHeap]) = SOME w /\
     wordSem_get_var r s = SOME w ==>
     data_inv (knowledge_instrs_mem_fupd (K
                 (balanced_map_insert listCmp (OpCurrHeapToNumList
                   op src) r (knowledge_instrs_mem data))) data) s`,
  CHEAT_TAC);;

(* [local] *)
let data_inv_insert_instrs_LocValue = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) r l.
     data_inv data s /\
     sptree_lookup r (knowledge_to_canonical data) = SOME r /\
     balanced_map_lookup r (wordSem_state_locals s) = SOME
       (wordLang_Loc l 0) ==>
     data_inv (knowledge_instrs_mem_fupd (K
                 (balanced_map_insert listCmp [48; l] r
                   (knowledge_instrs_mem data))) data) s`,
  CHEAT_TAC);;

(* Generic correctness of add_to_data_aux, with the family-specific content
   as premises: a hit's holder carries the computed value, and (for the odd
   destination of a miss) inserting the new fact preserves the invariant.
   The destination is freshly invalidated at every call site. *)
let add_to_data_aux_correct = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) r i p w data' p'.
     data_inv data s /\
     sptree_lookup r (knowledge_to_canonical data) = NONE /\
     add_to_data_aux data r i p = (data',p') /\
     wordSem_evaluate (p,s) = (NONE,wordSem_set_var r w s) /\
     (!v. balanced_map_lookup listCmp i (knowledge_instrs_mem data) =
       SOME v ==>
          wordSem_get_var v s = SOME w) /\
     (~(EVEN r) ==>
        data_inv (
                  knowledge_instrs_mem_fupd (K
                    (balanced_map_insert listCmp i r
                      (knowledge_instrs_mem
                      (knowledge_to_canonical_fupd (K
                         (balanced_map_insert r r
                           (knowledge_to_canonical data))) data))))
                           (knowledge_to_canonical_fupd (K
                           (balanced_map_insert r r
                           (knowledge_to_canonical data))) data))
                 (wordSem_set_var r w s)) ==>
     wordSem_evaluate (p',s) = (NONE,wordSem_set_var r w s) /\
     data_inv data' (wordSem_set_var r w s)`,
  CHEAT_TAC);;

(* A canonical representative is itself canonical (by idempotence) or an
   untracked register mapped to itself by the next registration. *)
(* [local] *)
let canonicalRegs_self_or_fresh = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) x.
     data_inv data s ==>
     sptree_lookup (canonicalRegs data x) (knowledge_to_canonical
       data) =
       SOME (canonicalRegs data x) \/
     sptree_lookup (canonicalRegs data x) (knowledge_to_canonical
       data) = NONE`,
  CHEAT_TAC);;

(* The avoiding variant only differs when the canonical representative is
   the (freshly invalidated) destination, which forces the argument itself
   to be that untracked destination. *)
(* [local] *)
let canonicalRegs'_self_or_fresh = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) r1 x.
     data_inv data s /\ sptree_lookup r1 (knowledge_to_canonical
       data) = NONE ==>
     sptree_lookup (canonicalRegs' r1 data x) (knowledge_to_canonical
       data) =
       SOME (canonicalRegs' r1 data x) \/
     sptree_lookup (canonicalRegs' r1 data x)
       (knowledge_to_canonical data) = NONE`,
  CHEAT_TAC);;

(* [local] *)
let can_mem_arith_ODD_reads = prove
 (`!a. can_mem_arith a ==> ALL ODD (arithReads a)`,
  CHEAT_TAC);;

(* Correctness of add_to_data_const: a repeated constant keeps its register
   equivalence (to_canonical/to_latest) but is rematerialised — both arms emit
   Inst (Const r w), so the destination ends up holding Word w either way and
   the data invariant is maintained. The destination is freshly invalidated at
   the call site (ODD r, untracked). *)
let add_to_data_const_correct = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) r (w:'a word) data' p'.
     data_inv data s /\
     sptree_lookup r (knowledge_to_canonical data) = NONE /\ ~(EVEN
       r) /\
     add_to_data_const data r w = (data',p') ==>
     wordSem_evaluate (p',s) = (NONE,wordSem_set_var r (wordLang_Word
       w) s) /\
     data_inv data' (wordSem_set_var r (wordLang_Word w) s)`,
  CHEAT_TAC);;

let add_to_data_LocValue_correct = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) r l data' p'.
     data_inv data s /\
     sptree_lookup r (knowledge_to_canonical data) = NONE /\
     l IN domain (wordSem_state_code s) /\
     add_to_data_aux data r [48; l] (wordLang_LocValue r l) =
       (data',p') ==>
     wordSem_evaluate (p',s) = (NONE,wordSem_set_var r (wordLang_Loc
       l 0) s) /\
     data_inv data' (wordSem_set_var r (wordLang_Loc l 0) s)`,
  CHEAT_TAC);;

let add_to_data_OpCurrHeap_correct = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) b r1 r2 r2' w data' p'.
     data_inv data s /\
     sptree_lookup r1 (knowledge_to_canonical data) = NONE /\
     r2' = canonicalRegs' r1 data r2 /\
     ~(EVEN r2) /\ ~(r2 = r1) /\
     wordSem_word_exp s (wordLang_Op b [wordLang_Var r2;
       wordLang_Lookup CurrHeap]) = SOME w /\
     add_to_data_aux (register_read data r2') r1 (OpCurrHeapToNumList
       b r2')
       (wordLang_OpCurrHeap b r1 r2) = (data',p') ==>
     wordSem_evaluate (p',s) = (NONE,wordSem_set_var r1 w s) /\
     data_inv data' (wordSem_set_var r1 w s)`,
  CHEAT_TAC);;

let add_to_data_Arith_correct = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) a a' r w data' p'.
     data_inv data s /\
     sptree_lookup r (knowledge_to_canonical data) = NONE /\
     a' = canonicalArith data a /\
     can_mem_arith a' /\ ~(MEM r (arithReads a')) /\
     r = firstRegOfArith a /\
     wordSem_evaluate (wordLang_Inst (asm_Arith a),s) =
       (NONE,wordSem_set_var r w s) /\
     add_to_data (register_reads data (arithReads a')) r (asm_Arith
       a') (asm_Arith a) = (data',p') ==>
     wordSem_evaluate (p',s) = (NONE,wordSem_set_var r w s) /\
     data_inv data' (wordSem_set_var r w s)`,
  CHEAT_TAC);;

(* Storing a new load fact (the loads_mem sibling of the F-family): the
   holder and the address must be self-mapped, and the fact's ∀-destination
   evaluation equation must hold. *)
(* [local] *)
let data_inv_insert_loads = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) r op a (ofs:'a word) w.
     data_inv data s /\
     sptree_lookup r (knowledge_to_canonical data) = SOME r /\
     sptree_lookup a (knowledge_to_canonical data) = SOME a /\
     ~(is_store op) /\
     wordSem_get_var r s = SOME w /\
     (!r'. wordSem_evaluate (wordLang_Inst (asm_Mem op r' (Addr a
       ofs)),s) = (NONE,wordSem_set_var r' w s)) ==>
     data_inv (knowledge_loads_mem_fupd (K
                 (balanced_map_insert listCmp (loadToNumList op a
                   ofs) r (knowledge_loads_mem data))) data) s`,
  CHEAT_TAC);;

(* Generic correctness of add_to_load_aux — the loads_mem mirror of
   add_to_data_aux_correct, with the same premise structure. *)
let add_to_load_aux_correct = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) r i p w data' p'.
     data_inv data s /\
     sptree_lookup r (knowledge_to_canonical data) = NONE /\
     add_to_load_aux data r i p = (data',p') /\
     wordSem_evaluate (p,s) = (NONE,wordSem_set_var r w s) /\
     (!v. balanced_map_lookup listCmp i (knowledge_loads_mem data) =
       SOME v ==>
          wordSem_get_var v s = SOME w) /\
     (~(EVEN r) ==>
        data_inv (
                  knowledge_loads_mem_fupd (K
                    (balanced_map_insert listCmp i r
                      (knowledge_loads_mem
                      (knowledge_to_canonical_fupd (K
                         (balanced_map_insert r r
                           (knowledge_to_canonical data))) data))))
                           (knowledge_to_canonical_fupd (K
                           (balanced_map_insert r r
                           (knowledge_to_canonical data))) data))
                 (wordSem_set_var r w s)) ==>
     wordSem_evaluate (p',s) = (NONE,wordSem_set_var r w s) /\
     data_inv data' (wordSem_set_var r w s)`,
  CHEAT_TAC);;

(* The instantiation of add_to_load_aux_correct at the word_cseInst Mem-arm
   call site. *)
let add_to_load_correct = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) op r a a' (ofs:'a word) w data'
  p'.
     data_inv data s /\
     sptree_lookup r (knowledge_to_canonical data) = NONE /\
     a' = canonicalRegs' r data a /\
     ~(is_store op) /\ ~(EVEN r) /\ ~(EVEN a) /\ ~(a = r) /\
     wordSem_evaluate (wordLang_Inst (asm_Mem op r (Addr a ofs)),s) =
       (NONE,wordSem_set_var r w s) /\
     add_to_load_aux (register_read data a') r (loadToNumList op a'
       ofs)
       (wordLang_Inst (asm_Mem op r (Addr a ofs))) = (data',p') ==>
     wordSem_evaluate (p',s) = (NONE,wordSem_set_var r w s) /\
     data_inv data' (wordSem_set_var r w s)`,
  CHEAT_TAC);;

(* [local] *)
let MAP_FST_lemma = prove
 (`!moves. MAP FST (MAP (\(a,b). (a,canonicalRegs data b)) moves) =
  MAP FST moves`,
  CHEAT_TAC);;

(* [local] *)
let MAP_SND_lemma = prove
 (`!moves x.
     wordSem_get_vars (MAP SND moves) s = SOME x /\ data_inv data s
       ==>
     wordSem_get_vars (MAP SND (MAP (\(a,b). (a,canonicalRegs data
       b)) moves)) s = SOME x`,
  CHEAT_TAC);;

let lookup_map_insert0 = prove
 (`!xs r. balanced_map_lookup r (map_insert xs m) =
          (match ALOOKUP xs r with NONE -> balanced_map_lookup r m
            | SOME r' -> SOME r')`,
  CHEAT_TAC);;

let get_set_vars_lemma = prove
 (`!xs xs' x y s. ~(MEM x xs) /\ ~(MEM y xs) ==>
                  wordSem_get_var x s = wordSem_get_var y s ==>
                  wordSem_get_var x (wordSem_set_vars xs xs' s) =
                    wordSem_get_var y (wordSem_set_vars xs xs' s)`,
  CHEAT_TAC);;

(* [local] *)
let get_set_vars_not_in = prove
 (`!rs vs r s. ~(MEM r rs) ==> wordSem_get_var r (wordSem_set_vars rs
  vs s) = wordSem_get_var r s`,
  CHEAT_TAC);;

let MEM_FST_reduc = prove
 (`!moves r p_2. MEM (r,p_2) moves ==> MEM r (MAP FST moves)`,
  CHEAT_TAC);;

(* [local] *)
let get_set_vars_in = prove
 (`!moves r p_2 x s.
     MEM (r,p_2) moves ==>
     ALL_DISTINCT (MAP FST moves) ==>
     wordSem_get_vars (MAP SND moves) s = SOME x ==>
     wordSem_get_var r (wordSem_set_vars (MAP FST moves) x s) =
       wordSem_get_var p_2 s`,
  CHEAT_TAC);;

(* [local] *)
let get_set_vars_in_2 = prove
 (`!moves r p_2 x' x data s.
     MEM (r,p_2) moves ==>
     ALL_DISTINCT (MAP FST moves) ==>
     balanced_map_lookup p_2 (knowledge_to_canonical data) = SOME x'
       ==>
     wordSem_get_vars (MAP SND (MAP (\(a,b). (a,canonicalRegs data
       b)) moves)) s = SOME x ==>
     wordSem_get_var r (wordSem_set_vars (MAP FST moves) x s) =
       wordSem_get_var x' s`,
  CHEAT_TAC);;

(* [local] *)
let lookup_set_vars_not_in = prove
 (`!moves v data c x.
     ~(MEM v (MAP FST moves)) ==>
     balanced_map_lookup v (wordSem_state_locals s) = SOME
       (wordLang_Word c) ==>
     balanced_map_lookup v (wordSem_state_locals (wordSem_set_vars
       (MAP FST moves) x s)) = SOME (wordLang_Word c)`,
  CHEAT_TAC);;

(* [local] *)
let list_insert_insert = prove
 (`!l n an. list_insert l (balanced_map_insert n one an) =
  balanced_map_insert n one (list_insert l an)`,
  CHEAT_TAC);;

(* Field-explicit corollaries of the two extension lemmas, in the shape the
   map_insert induction produces. *)
(* [local] *)
let data_inv_insert_canonical_pair = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) x y tc tl.
     data_inv (knowledge_to_latest_fupd (K tl)
       (knowledge_to_canonical_fupd (K tc) data)) s /\
     sptree_lookup x tc = NONE /\
     sptree_lookup y (balanced_map_insert x y tc) = SOME y /\
     ODD x /\ ODD y /\
     wordSem_get_var x s = wordSem_get_var y s ==>
     data_inv (knowledge_to_latest_fupd (K tl)
       (knowledge_to_canonical_fupd (K (balanced_map_insert x y tc))
       data)) s`,
  CHEAT_TAC);;

(* One recorded register equivalence (fresh destination, already-canonical
   source) on top of arbitrary to_canonical/to_latest contents. *)
(* [local] *)
let data_inv_insert_pair = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) x y tc tl.
     data_inv (knowledge_to_latest_fupd (K tl)
       (knowledge_to_canonical_fupd (K tc) data)) s /\
     sptree_lookup x tc = NONE /\ sptree_lookup y tc = SOME y /\
     ODD x /\ ODD y /\ wordSem_get_var x s = wordSem_get_var y s ==>
     data_inv (knowledge_to_latest_fupd (K (balanced_map_insert y x
       tl)) (knowledge_to_canonical_fupd (K (balanced_map_insert x y
       tc)) data)) s`,
  CHEAT_TAC);;

(* Recording a list of register equivalences (fresh destination, canonical
   source) pair by pair: the Move case's knowledge update. *)
(* [local] *)
let data_inv_move_pairs = prove
 (`!ps data (s:('a,'c,'ffi)wordSem_state).
     data_inv data s /\
     ALL_DISTINCT (MAP FST ps) /\
     ALL (\(x,y). sptree_lookup x (knowledge_to_canonical data) =
       NONE /\
                    sptree_lookup y (knowledge_to_canonical data) =
                      SOME y /\
                    ODD x /\ wordSem_get_var x s = wordSem_get_var y
                      s) ps ==>
     data_inv (knowledge_to_latest_fupd (K (map_insert (MAP (\(a,b).
       (b,a)) ps) (knowledge_to_latest
                              data))) (knowledge_to_canonical_fupd
                                (K (map_insert ps
                                (knowledge_to_canonical data))) data))
                                s`,
  CHEAT_TAC);;

(* The Move case: registering the sources and recording the surviving
   destination/canonical-source equivalences preserves the invariant across
   the parallel assignment. *)
let canonicalMoveRegs_lemma = prove
 (`!data (s:('a,'c,'ffi)wordSem_state) rs vs.
     data_inv data s /\
     ALL_DISTINCT (MAP FST rs) /\
     wordSem_get_vars (MAP SND rs) s = SOME vs ==>
     data_inv (canonicalMoveRegs data rs) (wordSem_set_vars (MAP
       FST rs) vs s)`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------
   THE MAIN CORRECTNESS THEOREM

   One suspend/Resume ladder over the evaluate induction: the dispatcher
   names every case, Break and Continue close inline (word_cse keeps the
   data and the program unchanged), and each Resume block below carries one
   case's proof.
   ------------------------------------------------------------------------ *)

(* [local] *)
let if_eq_rw = prove
 (`(if x = y then y else x) = x`,
  CHEAT_TAC);;
add_simp if_eq_rw;;

(* The stored evaluation equations are insensitive to the clock and termdep
   fields — clones of the memory transports for the Tick/MustTerminate
   cases. *)
(* [local] *)
let evaluate_arith_clock = prove
 (`!a w s c td.
     can_mem_arith a ==>
     (wordSem_evaluate (wordLang_Inst (asm_Arith
       a),wordSem_state_termdep_fupd (K td) (state_clock_fupd (K c) s))
       =
        (NONE,wordSem_state_termdep_fupd (K td) (state_clock_fupd (K
          c)
         (wordSem_set_var (firstRegOfArith a) w s))) <=>
      wordSem_evaluate (wordLang_Inst (asm_Arith a),s) =
        (NONE,wordSem_set_var (firstRegOfArith a) w s))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_load_clock = prove
 (`!op r a ofs w s c td.
     ~(is_store op) ==>
     (wordSem_evaluate (wordLang_Inst (asm_Mem op r (Addr a
       ofs)),wordSem_state_termdep_fupd (K td) (state_clock_fupd (K c)
                s)) =
        (NONE,wordSem_state_termdep_fupd (K td) (state_clock_fupd (K
          c) (wordSem_set_var r w s))) <=>
      wordSem_evaluate (wordLang_Inst (asm_Mem op r (Addr a
        ofs)),s) = (NONE,wordSem_set_var r w s))`,
  CHEAT_TAC);;

(* data_inv is insensitive to the clock and termdep fields. *)
let data_inv_clock = prove
 (`!data s c td.
     data_inv data s ==> data_inv data (wordSem_state_termdep_fupd
       (K td) (state_clock_fupd (K c) s))`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------
   SYNTACTIC WF PRESERVATION

   word_cse preserves the state-free half of the invariant with no
   semantic premises.  The If case of comp_correct needs wf_data of the
   NOT-taken branch's output, which no evaluation establishes; these
   lemmas mirror the data_inv-level update lemmas above restricted to
   their wf_data content, and culminate in word_cse_wf_data.
   ------------------------------------------------------------------------ *)

let wf_data_empty = prove
 (`wf_data (:'a) empty_data`,
  CHEAT_TAC);;
add_simp wf_data_empty;;

(* Wiping the load facts only removes obligations. *)
let wf_data_loads_wipe = prove
 (`!data. wf_data (:'a) data ==> wf_data (:'a)
  (knowledge_loads_mem_fupd (K balanced_map_empty) data)`,
  CHEAT_TAC);;

let wf_data_invalidate = prove
 (`!data r. wf_data (:'a) data ==> wf_data (:'a) (invalidate_data data
  r)`,
  CHEAT_TAC);;

let wf_data_invalidate_regs = prove
 (`!rs data. wf_data (:'a) data ==> wf_data (:'a) (invalidate_regs
  data rs)`,
  CHEAT_TAC);;

(* wf sibling of data_inv_insert_to_canonical. *)
let wf_data_insert_to_canonical = prove
 (`!data x y.
     wf_data (:'a) data /\
     sptree_lookup x (knowledge_to_canonical data) = NONE /\
     sptree_lookup y (balanced_map_insert x y (knowledge_to_canonical
       data)) = SOME y /\
     ODD x /\ ODD y ==>
     wf_data (:'a) (knowledge_to_canonical_fupd (K
       (balanced_map_insert x y (knowledge_to_canonical data))) data)`,
  CHEAT_TAC);;

(* wf sibling of data_inv_insert_to_latest. *)
let wf_data_insert_to_latest = prove
 (`!data x y.
     wf_data (:'a) data /\
     x IN domain (knowledge_to_canonical data) /\ y IN domain
       (knowledge_to_canonical data) ==>
     wf_data (:'a) (knowledge_to_latest_fupd (K
       (balanced_map_insert x y (knowledge_to_latest data))) data)`,
  CHEAT_TAC);;

let wf_data_register_read = prove
 (`!data r. wf_data (:'a) data ==> wf_data (:'a) (register_read data
  r)`,
  CHEAT_TAC);;

let wf_data_register_reads = prove
 (`!rs data. wf_data (:'a) data ==> wf_data (:'a) (register_reads data
  rs)`,
  CHEAT_TAC);;

(* wf siblings of the per-family fact-insert lemmas (F1-F5): a new fact
   with a self-mapped holder (and, per family, self-mapped reads) keeps the
   data well-formed. *)
(* [local] *)
let wf_data_insert_instrs_Const = prove
 (`!data r n (w:'a word).
     wf_data (:'a) data /\
     sptree_lookup r (knowledge_to_canonical data) = SOME r ==>
     wf_data (:'a) (knowledge_instrs_mem_fupd (K
                      (balanced_map_insert listCmp (instToNumList
                        (wordLang_Const n w)) r (knowledge_instrs_mem
                        data))) data)`,
  CHEAT_TAC);;

(* [local] *)
let wf_data_insert_instrs_Arith = prove
 (`!data r (a:'a asm_arith).
     wf_data (:'a) data /\
     sptree_lookup r (knowledge_to_canonical data) = SOME r /\
     can_mem_arith a /\ in_names_set a (knowledge_to_canonical data)
       ==>
     wf_data (:'a) (knowledge_instrs_mem_fupd (K
                      (balanced_map_insert listCmp (instToNumList
                        (asm_Arith a)) r (knowledge_instrs_mem
                        data))) data)`,
  CHEAT_TAC);;

(* [local] *)
let wf_data_insert_instrs_OpCurrHeap = prove
 (`!data r op src.
     wf_data (:'a) data /\
     sptree_lookup r (knowledge_to_canonical data) = SOME r /\
     sptree_lookup src (knowledge_to_canonical data) = SOME src ==>
     wf_data (:'a) (knowledge_instrs_mem_fupd (K
                      (balanced_map_insert listCmp
                        (OpCurrHeapToNumList op src) r
                        (knowledge_instrs_mem
                        data))) data)`,
  CHEAT_TAC);;

(* [local] *)
let wf_data_insert_instrs_LocValue = prove
 (`!data r l.
     wf_data (:'a) data /\
     sptree_lookup r (knowledge_to_canonical data) = SOME r ==>
     wf_data (:'a) (knowledge_instrs_mem_fupd (K
                      (balanced_map_insert listCmp [48; l] r
                        (knowledge_instrs_mem data))) data)`,
  CHEAT_TAC);;

(* [local] *)
let wf_data_insert_loads = prove
 (`!data r op a (ofs:'a word).
     wf_data (:'a) data /\
     sptree_lookup r (knowledge_to_canonical data) = SOME r /\
     sptree_lookup a (knowledge_to_canonical data) = SOME a ==>
     wf_data (:'a) (knowledge_loads_mem_fupd (K
                      (balanced_map_insert listCmp (loadToNumList op
                        a ofs) r (knowledge_loads_mem
                        data))) data)`,
  CHEAT_TAC);;

(* wf mirror of add_to_data_aux_correct: the hit case re-points the
   destination at the stored (self-mapped) holder; the family-specific
   miss case arrives as a premise in the same nested-with form. *)
let wf_add_to_data_aux = prove
 (`!data r i (p:'a wordLang_prog) data' p'.
     wf_data (:'a) data /\
     sptree_lookup r (knowledge_to_canonical data) = NONE /\
     add_to_data_aux data r i p = (data',p') /\
     (~(EVEN r) ==>
        wf_data (:'a)
          (
           knowledge_instrs_mem_fupd (K
             (balanced_map_insert listCmp i r (knowledge_instrs_mem
               (knowledge_to_canonical_fupd (K
                  (balanced_map_insert r r (knowledge_to_canonical
                    data))) data)))) (knowledge_to_canonical_fupd (K
                    (balanced_map_insert r r (knowledge_to_canonical
                    data))) data))) ==>
     wf_data (:'a) data'`,
  CHEAT_TAC);;

(* wf mirror of add_to_data_const_correct: both arms keep the data well-formed
   — the hit re-points the destination at the (self-mapped) holder, the miss
   records a fresh self-mapped constant fact. *)
let wf_add_to_data_const = prove
 (`!data r (w:'a word) data' p'.
     wf_data (:'a) data /\
     sptree_lookup r (knowledge_to_canonical data) = NONE /\ ~(EVEN
       r) /\
     add_to_data_const data r w = (data',p') ==>
     wf_data (:'a) data'`,
  CHEAT_TAC);;

let wf_add_to_load_aux = prove
 (`!data r i (p:'a wordLang_prog) data' p'.
     wf_data (:'a) data /\
     sptree_lookup r (knowledge_to_canonical data) = NONE /\
     add_to_load_aux data r i p = (data',p') /\
     (~(EVEN r) ==>
        wf_data (:'a)
          (
           knowledge_loads_mem_fupd (K
             (balanced_map_insert listCmp i r (knowledge_loads_mem
               (knowledge_to_canonical_fupd (K
                  (balanced_map_insert r r (knowledge_to_canonical
                    data))) data)))) (knowledge_to_canonical_fupd (K
                    (balanced_map_insert r r (knowledge_to_canonical
                    data))) data))) ==>
     wf_data (:'a) data'`,
  CHEAT_TAC);;

(* wf siblings of the Get/Set knowledge-update lemmas. *)
(* [local] *)
let wf_data_insert_gets = prove
 (`!data name v.
     wf_data (:'a) data /\
     sptree_lookup v (knowledge_to_canonical data) = NONE /\ ODD v /\
     ALOOKUP (knowledge_gets_mem data) name = NONE ==>
     wf_data (:'a) (knowledge_gets_mem_fupd (K (CONS (name,v)
       (knowledge_gets_mem data))) (knowledge_to_latest_fupd (K
       (balanced_map_insert v v (knowledge_to_latest data)))
       (knowledge_to_canonical_fupd (K (balanced_map_insert v v
       (knowledge_to_canonical data))) data)))`,
  CHEAT_TAC);;

(* [local] *)
let wf_data_filter_gets = prove
 (`!data x.
     wf_data (:'a) data ==>
     wf_data (:'a) (knowledge_gets_mem_fupd (K
                      (FILTER (\(m,n). ~(m = x))
                        (knowledge_gets_mem data))) data)`,
  CHEAT_TAC);;

(* [local] *)
let wf_data_cons_gets = prove
 (`!data x h.
     wf_data (:'a) data /\
     ALOOKUP (knowledge_gets_mem data) x = NONE /\
     sptree_lookup h (knowledge_to_canonical data) = SOME h ==>
     wf_data (:'a) (knowledge_gets_mem_fupd (K (CONS (x,h)
       (knowledge_gets_mem data))) data)`,
  CHEAT_TAC);;

(* [local] *)
let wf_data_reinsert_canonical = prove
 (`!data v.
     wf_data (:'a) data /\ ODD v ==>
     wf_data (:'a) (knowledge_to_canonical_fupd (K
                      (balanced_map_insert v (lookup_any v
                        (knowledge_to_canonical data) v)
                        (knowledge_to_canonical
                        data))) data)`,
  CHEAT_TAC);;

(* wf sibling of data_inv_merge_l/_r: well-formedness of both arms is
   enough for the equality-intersection merge. *)
let wf_data_merge = prove
 (`!d1 d2.
     wf_data (:'a) d1 /\ wf_data (:'a) d2 ==> wf_data (:'a)
       (merge_data d1 d2)`,
  CHEAT_TAC);;

(* wf sibling of data_inv_move_pairs — WITHOUT the ALL_DISTINCT premise:
   word_cse runs on syntactically arbitrary Moves, including ones with
   duplicate destinations that the semantics would reject, so the proof is
   a direct characterization via lookup_map_insert0 rather than the
   pair-by-pair induction.  Sources are self-mapped, hence never
   destinations, so their entries survive every insert. *)
(* [local] *)
let wf_data_move_pairs = prove
 (`!ps data.
     wf_data (:'a) data /\
     ALL (\(x,y). sptree_lookup x (knowledge_to_canonical data) =
       NONE /\
                    sptree_lookup y (knowledge_to_canonical data) =
                      SOME y /\
                    ODD x /\ ODD y) ps ==>
     wf_data (:'a)
       (knowledge_to_latest_fupd (K (map_insert (MAP (\(a,b). (b,a))
         ps) (knowledge_to_latest
                              data))) (knowledge_to_canonical_fupd
                                (K (map_insert ps
                                (knowledge_to_canonical data))) data))`,
  CHEAT_TAC);;

(* wf sibling of canonicalMoveRegs_lemma's knowledge-update content. *)
let wf_canonicalMoveRegs = prove
 (`!data rs. wf_data (:'a) data ==> wf_data (:'a) (canonicalMoveRegs
  data rs)`,
  CHEAT_TAC);;

(* wf-premise variants of the self-or-fresh lemmas (the data_inv versions
   above only use the wf half of their premise). *)
(* [local] *)
let canonicalRegs_self_or_fresh_wf = prove
 (`!data x.
     wf_data (:'a) data ==>
     sptree_lookup (canonicalRegs data x) (knowledge_to_canonical
       data) =
       SOME (canonicalRegs data x) \/
     sptree_lookup (canonicalRegs data x) (knowledge_to_canonical
       data) = NONE`,
  CHEAT_TAC);;

(* [local] *)
let canonicalRegs'_self_or_fresh_wf = prove
 (`!data r1 x.
     wf_data (:'a) data /\ sptree_lookup r1 (knowledge_to_canonical
       data) = NONE ==>
     sptree_lookup (canonicalRegs' r1 data x) (knowledge_to_canonical
       data) =
       SOME (canonicalRegs' r1 data x) \/
     sptree_lookup (canonicalRegs' r1 data x)
       (knowledge_to_canonical data) = NONE`,
  CHEAT_TAC);;

(* [local] *)
let in_names_set_insert_self = prove
 (`!a tc x. in_names_set a tc ==> in_names_set a (balanced_map_insert
  x x tc)`,
  CHEAT_TAC);;

(* [local] *)
let in_names_set_register_reads = prove
 (`!a data.
     ALL ODD (arithReads a) /\
     ALL (\w. sptree_lookup w (knowledge_to_canonical data) = NONE \/
                sptree_lookup w (knowledge_to_canonical data) = SOME
                  w) (arithReads a) ==>
     in_names_set a (knowledge_to_canonical (register_reads data
       (arithReads a)))`,
  CHEAT_TAC);;

(* The reads of a canonicalized storable arith are canonical registers:
   tracked-and-self-mapped, or untracked (registered as self-maps next). *)
(* [local] *)
let canonicalArith_reads_self_or_fresh = prove
 (`!data (a:'a asm_arith).
     wf_data (:'a) data /\
     can_mem_arith (canonicalArith data a) /\
     sptree_lookup (firstRegOfArith a) (knowledge_to_canonical data)
       = NONE ==>
     ALL (\w. sptree_lookup w (knowledge_to_canonical data) = NONE \/
                sptree_lookup w (knowledge_to_canonical data) = SOME
                  w)
           (arithReads (canonicalArith data a))`,
  CHEAT_TAC);;

(* The main syntactic preservation theorem, one Resume per constructor
   whose case updates the knowledge (the catch-all closes the identity and
   full-reset cases).  Consumed by the If case of comp_correct for the
   not-taken branch. *)
let word_cse_wf_data = prove
 (`!p data.
     wf_data (:'a) data ==> wf_data (:'a) (FST (word_cse data (p:'a
       wordLang_prog)))`,
  CHEAT_TAC);;

(* HOL4 word_cseProofScript.sml:2935-2937: a proof *)

(* HOL4 word_cseProofScript.sml:2939-3092: a proof *)

(* HOL4 word_cseProofScript.sml:3094-3121: a proof *)

(* HOL4 word_cseProofScript.sml:3123-3162: a proof *)

(* HOL4 word_cseProofScript.sml:3164-3166: a proof *)

(* HOL4 word_cseProofScript.sml:3168-3171: a proof *)

(* HOL4 word_cseProofScript.sml:3173-3180: a proof *)

(* HOL4 word_cseProofScript.sml:3182-3190: a proof *)

(* HOL4 word_cseProofScript.sml:3192-3258: a proof *)

(* HOL4 word_cseProofScript.sml:3260-3289: a proof *)

(* HOL4 word_cseProofScript.sml:3291-3293: a proof *)

(* HOL4 word_cseProofScript.sml:3295-3297: a proof *)

(* HOL4 word_cseProofScript.sml:3299-3301: a proof *)

(* HOL4 word_cseProofScript.sml:3303: a proof *)

let comp_correct = prove
 (`!v v1 res s' data p' data'.
     wordSem_evaluate (v,v1) = (res,s') /\ flat_exp_conventions v /\
       data_inv data v1 /\ ~(res = SOME wordSem_Error) /\ word_cse data
       v = (data',p') ==>
     wordSem_evaluate (p',v1) = (res,s') /\ (res = NONE ==>
       data_inv data' s')`,
  CHEAT_TAC);;

(* proof of the cases *)

(* HOL4 word_cseProofScript.sml:3343-3345: a proof *)

(* HOL4 word_cseProofScript.sml:3347-3349: a proof *)

(* HOL4 word_cseProofScript.sml:3351-3355: a proof *)

(* HOL4 word_cseProofScript.sml:3357-3484: a proof *)

(* HOL4 word_cseProofScript.sml:3486-3488: a proof *)

(* HOL4 word_cseProofScript.sml:3490-3547: a proof *)

(* HOL4 word_cseProofScript.sml:3549-3600: a proof *)

(* HOL4 word_cseProofScript.sml:3602-3615: a proof *)

(* HOL4 word_cseProofScript.sml:3617-3619: a proof *)

(* HOL4 word_cseProofScript.sml:3621-3628: a proof *)

(* HOL4 word_cseProofScript.sml:3630-3645: a proof *)

(* HOL4 word_cseProofScript.sml:3647-3662: a proof *)

(* HOL4 word_cseProofScript.sml:3664-3668: a proof *)

(* HOL4 word_cseProofScript.sml:3670-3674: a proof *)

(* HOL4 word_cseProofScript.sml:3676-3697: a proof *)

(* HOL4 word_cseProofScript.sml:3699-3706: a proof *)

(* HOL4 word_cseProofScript.sml:3708-3710: a proof *)

(* HOL4 word_cseProofScript.sml:3712-3717: a proof *)

(* HOL4 word_cseProofScript.sml:3719-3724: a proof *)

(* HOL4 word_cseProofScript.sml:3726-3728: a proof *)

(* HOL4 word_cseProofScript.sml:3730-3732: a proof *)

(* HOL4 word_cseProofScript.sml:3734-3740: a proof *)

(* HOL4 word_cseProofScript.sml:3742-3763: a proof *)

(* HOL4 word_cseProofScript.sml:3765-3791: a proof *)

(* HOL4 word_cseProofScript.sml:3793: a proof *)

let word_common_subexp_elim_correct = prove
 (`wordSem_evaluate (p,s) = (res,s1) /\
   flat_exp_conventions p /\ ~(res = SOME wordSem_Error) ==>
   wordSem_evaluate (word_common_subexp_elim p,s) = (res,s1)`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------
   SYNTACTIC CONVENTIONS

   word_cse emits only original instructions or Moves (the canonicalized
   arith only feeds the hash key, never the output program), so every
   syntactic convention transports with no well-formedness premise.
   ------------------------------------------------------------------------ *)

let word_cse_full_inst_ok_less = prove
 (`!p data c data' (q:'a wordLang_prog).
     full_inst_ok_less c p /\ word_cse data p = (data',q) ==>
     full_inst_ok_less c q`,
  CHEAT_TAC);;

let word_cse_pre_alloc_conventions = prove
 (`!p data data' (q:'a wordLang_prog).
     pre_alloc_conventions p /\ word_cse data p = (data',q) ==>
     pre_alloc_conventions q`,
  CHEAT_TAC);;

let word_cse_every_inst_distinct_tar_reg = prove
 (`!p data data' (q:'a wordLang_prog).
     every_inst distinct_tar_reg p /\ word_cse data p = (data',q) ==>
     every_inst distinct_tar_reg q`,
  CHEAT_TAC);;

let word_cse_every_inst_two_reg = prove
 (`!p data data' (q:'a wordLang_prog).
     every_inst two_reg_inst p /\ word_cse data p = (data',q) ==>
     every_inst two_reg_inst q`,
  CHEAT_TAC);;

let every_inst_distinct_tar_reg_word_common_subexp_elim = prove
 (`every_inst distinct_tar_reg p ==>
   every_inst distinct_tar_reg (word_common_subexp_elim p)`,
  CHEAT_TAC);;

let pre_alloc_conventions_word_common_subexp_elim = prove
 (`pre_alloc_conventions p ==>
   pre_alloc_conventions (word_common_subexp_elim p)`,
  CHEAT_TAC);;

let full_inst_ok_less_word_common_subexp_elim = prove
 (`full_inst_ok_less ac p ==>
   full_inst_ok_less ac (word_common_subexp_elim p)`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["Greater"];;
