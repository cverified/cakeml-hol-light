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
needs "basis/pure/mlvector.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/data_space.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/flat_elim.ml";;
needs "compiler/backend/gc/copying_gc.ml";;
needs "compiler/backend/gc/gc_combined.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "compiler/backend/gc/gen_gc_partial.ml";;
needs "compiler/backend/labLang.ml";;
needs "compiler/backend/proofs/word_gcFunctions.ml";;
needs "compiler/backend/reg_alloc/linear_scan.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/labSem.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/encoders/asm/asmProps.ml";;
needs "lib/alignment.ml";;
needs "lib/balanced_map.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/byte.ml";;
needs "lib/comparison.ml";;
needs "lib/errorMonad.ml";;
needs "lib/integer_word.ml";;
needs "lib/multiword.ml";;
needs "lib/peg.ml";;
needs "lib/regexp_compiler.ml";;
needs "lib/set_sep.ml";;
needs "lib/sorting.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/cmlPtreeConversion.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

cake_hide ["do_partial"; "not"; "parts"; "vars"];;
(* HOL4 ancestors outside the port: int_bitwise While *)


(* HOL4 data_to_word_memoryProofScript.sml:13-14: ML code, not ported *)

(* TODO: move? *)
(* HOL4 data_to_word_memoryProofScript.sml:21-22: a proof *)

(* HOL4 data_to_word_memoryProofScript.sml:24: ML code, not ported *)

cake_hide_more ["el"; "sign"];;
(* HOL4 data_to_word_memoryProofScript.sml:28: the overload
   good_dimindex, which the port expands *)

(* HOL4 data_to_word_memoryProofScript.sml:30-32: the ML values that
   the definitions below antiquote *)

let word_eq = cake_theorem "word_eq"
  (fun () ->
    `!w v. w = v <=> (!n. word_bit n w = word_bit n v)`)
  (MATCH_ACCEPT_TAC WORD_EQ_BITS);;

let ZIP_REPLICATE = cake_theorem "ZIP_REPLICATE"
  (fun () ->
    `!n. ZIP (REPLICATE n x) (REPLICATE n y) = REPLICATE n (x,y)`)
  (INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; ZIP]);;

(* MutBlock payloads have the shape l ++ [c] ++ r, which simplifiers split
   into three membership tests; this puts EL_MEM into the same split form *)
let MEM_EL_APPEND_MID = cake_theorem "MEM_EL_APPEND_MID"
  (fun () ->
    `!n l c r.
       n < LENGTH l + (LENGTH r + 1) ==>
       MEM (EL n (l ++ [c] ++ r)) l \/ EL n (l ++ [c] ++ r) = c \/
       MEM (EL n (l ++ [c] ++ r)) r`)
  (* the element is one of the list, and MEM of the three parts is
     what the split of the append and of the singleton says *)
  (let lem = MESON[MEM_APPEND; MEM]
     `!e l c r. MEM e (APPEND l (APPEND [c] r))
                ==> MEM e l \/ e = c \/ MEM e r` in
   REPEAT STRIP_TAC THEN MATCH_MP_TAC lem THEN MATCH_MP_TAC MEM_EL THEN
   ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC);;

let MAX_LIST_sum_bound = cake_theorem "MAX_LIST_sum_bound"
  (fun () ->
    `SUM ls <= MAX_LIST ls * LENGTH ls`)
  (* HOL4's SUM is ITLIST (+) l 0 in the port (ml/lib/hol4.ml), so
     its clauses come first *)
  (let sum_cl = prove
    (`SUM [] = 0 /\ (!h t. SUM (CONS h t) = h + SUM t)`,
     REWRITE_TAC[SUM_DEF; ITLIST]) in
   SPEC_TAC(`ls:num list`,`ls:num list`) THEN LIST_INDUCT_TAC THEN
   REWRITE_TAC[sum_cl; MAX_LIST; LENGTH; MULT_CLAUSES; LE_REFL] THEN
   MATCH_MP_TAC LE_ADD2 THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a <= MAX a b`];
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `MAX_LIST (t:num list) * LENGTH t` THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
    REWRITE_TAC[ARITH_RULE `b <= MAX a b`]]);;

let MAX_LIST_bounded_elements = cake_theorem "MAX_LIST_bounded_elements"
  (fun () ->
    `!l1 l2. LIST_REL (<=) l1 l2 ==> MAX_LIST l1 <= MAX_LIST l2`)
  (LIST_INDUCT_TAC THEN GEN_TAC THEN CASES_BY_NAME "l2" THEN
   REWRITE_TAC[ALL2; MAX_LIST; LE_REFL] THEN STRIP_TAC THEN
   MATCH_MP_TAC(ARITH_RULE
     `a <= c /\ b <= d ==> MAX a b <= MAX c d`) THEN
   ASM_SIMP_TAC[]);;

let MAX_LIST_MAP = cake_theorem "MAX_LIST_MAP"
  (fun () ->
    `!f l. (!x y. x < y ==> f x < f y) ==> MAX_LIST (MAP f l) = (if
  NULL l then 0 else f (MAX_LIST l))`)
  (* a strictly monotonic f is monotonic, so it commutes with MAX,
     and the induction is then a rewrite; the last goal is the one
     of the empty tail, where MAX_LIST [] = 0 and f 0 <= f h *)
  (REPEAT GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `!a b:num. (f:num->num) a <= f b <=> a <= b`
     ASSUME_TAC THENL
    [REPEAT GEN_TAC THEN
     ASM_CASES_TAC `a:num <= b` THEN ASM_REWRITE_TAC[] THENL
      [ASM_CASES_TAC `a:num = b` THENL
        [ASM_REWRITE_TAC[LE_REFL];
         MATCH_MP_TAC LT_IMP_LE THEN FIRST_ASSUM MATCH_MP_TAC THEN
         ASM_ARITH_TAC];
       REWRITE_TAC[NOT_LE] THEN FIRST_ASSUM MATCH_MP_TAC THEN
       ASM_ARITH_TAC];
     ALL_TAC] THEN
   SUBGOAL_THEN `!a b:num. (f:num->num) (MAX a b) = MAX (f a) (f b)`
     ASSUME_TAC THENL
    [REPEAT GEN_TAC THEN ASM_REWRITE_TAC[MAX] THEN
     COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
   SPEC_TAC(`l:num list`,`l:num list`) THEN
   LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MAX_LIST; NULL; NULL_EQ] THEN
   ASM_CASES_TAC `t:num list = []` THEN
   ASM_REWRITE_TAC[MAP; MAX_LIST; NULL; NULL_EQ] THEN
   REWRITE_TAC[ARITH_RULE `MAX x 0 = x`] THEN
   ASM_REWRITE_TAC[MAX] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
   AP_TERM_TAC THEN ASM_ARITH_TAC);;

let w2i_i2w_IMP = cake_theorem "w2i_i2w_IMP"
  (fun () ->
    `(w2i ((i2w i):'a word)) = i ==> INT_MIN (:'a) <= i /\ i <=
  INT_MAX (:'a)`)
  (* the bound that the round trip of an integer through a word
     gives: HOL Light's ival of a word is between the two powers,
     and the integer that the word has as its ival is the one *)
  (DISCH_TAC THEN
   MP_TAC(ISPEC `(i2w i):'a word` IVAL_BOUND) THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[integer_word_INT_MIN; integer_word_INT_MAX; INT_MIN;
               GSYM INT_OF_NUM_POW] THEN
   INT_ARITH_TAC);;

let word_i2w_sub = cake_theorem "word_i2w_sub"
  (fun () ->
    `!a b. i2w a - i2w b = i2w (a - b)`)
  (REWRITE_TAC[IWORD_INT_SUB]);;

(* -- *)

let data_to_word_memoryProof_tag_INDUCT,
    data_to_word_memoryProof_tag_RECURSION =
  define_datatype
  "data_to_word_memoryProof_tag = BlockTag (num) \
   // immutable Block\n\
   | RefTag \
   // mutable arrays / references\n\
   | BytesTag (bool) (num) \
   // mutable byte arrays / immutable strings\n\
   | ThunkTag (thunk_mode) \
   // mutable thunks\n\
   | NumTag (bool) \
   // immutable bignum on the heap\n\
   | Word64Tag \
   // immutable word64 on the heap";;

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
  (* the first argument is the type itself, which the clause of the
     definition fixes, so the lambda form of it is what rewrites
     here; the witness is the list that the branch has *)
  (let take_ws (asl,w as gl) =
     let bod = snd(dest_exists w) in
     let ws = snd(dest_pair(last(snd(strip_comb(lhs bod))))) in
     (EXISTS_TAC ws THEN REWRITE_TAC[LENGTH; ARITH]) gl in
   REPEAT GEN_TAC THEN REWRITE_TAC[cake_raw "Word64Rep"] THEN
   COND_CASES_TAC THEN take_ws);;

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
  (REWRITE_TAC[cake_def "ThunkBlock"; injectivity "heap_element";
               injectivity "data_to_word_memoryProof_tag"; CONS_11;
               PAIR_EQ] THEN
   CONV_TAC TAUT);;

let v_inv_ck_mono = cake_theorem "v_inv_ck_mono"
  (fun () ->
    `!ck conf v refs x f tf heap.
       v_inv_ck ck conf v refs (x,f,tf,heap) ==>
         (!ck'. ck' <= ck ==> v_inv_ck ck' conf v refs
           (x,f,tf,heap))`)
  (* rule induction: every rule asks for the relation at ck - 1 and
     only when ck is not 0, so a smaller ck asks for less.  The two
     thunk rules name their value and their heap element in the
     premises and not in the conclusion, which a MATCH_MP_TAC would
     leave undetermined, so MESON applies them *)
  (let (vr,vi,vc) = v_inv_ck in
   let rl = CONJUNCTS vr in
   let _ = vc in
   let ar = ARITH_RULE
     `!a b. a <= b /\ ~(a = 0) ==> ~(b = 0) /\ a - 1 <= b - 1` in
   let PRE_TAC = REPEAT GEN_TAC THEN REPEAT STRIP_TAC in
   let mono = prove
    (`!ck conf (v:dataSem_v) refs y.
        v_inv_ck ck conf v refs y
        ==> !ck'. ck' <= ck ==> v_inv_ck ck' conf v refs y`,
     MATCH_MP_TAC vi THEN REPEAT CONJ_TAC THENL
      [PRE_TAC THEN MATCH_MP_TAC(el 0 rl) THEN ASM_REWRITE_TAC[];
       PRE_TAC THEN MATCH_MP_TAC(el 1 rl) THEN ASM_REWRITE_TAC[];
       PRE_TAC THEN MATCH_MP_TAC(el 2 rl) THEN ASM_REWRITE_TAC[];
       PRE_TAC THEN MATCH_ACCEPT_TAC(el 3 rl);
       PRE_TAC THEN MATCH_MP_TAC(el 4 rl) THEN ASM_REWRITE_TAC[];
       PRE_TAC THEN ASM_MESON_TAC[el 5 rl; ar];
       PRE_TAC THEN ASM_MESON_TAC[el 6 rl; ar];
       PRE_TAC THEN MATCH_MP_TAC(el 7 rl) THEN ASM_REWRITE_TAC[];
       (* and the elements of a Block one by one, with the ck of the
          induction hypothesis brought down to the new one *)
       PRE_TAC THEN MATCH_MP_TAC(el 8 rl) THEN
       ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
       TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN DISCH_TAC THEN
       FIRST_ASSUM(fun le -> FIRST_ASSUM(fun nz ->
         let a = MATCH_MP ar (CONJ le nz) in
         FIRST_X_ASSUM(fun ih ->
           MP_TAC(MATCH_MP ih (CONJUNCT1 a))) THEN
         MATCH_MP_TAC MONO_ALL2 THEN BETA_TAC THEN
         REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
         MATCH_ACCEPT_TAC(CONJUNCT2 a)))]) in
   REPEAT STRIP_TAC THEN ASM_MESON_TAC[mono]);;

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
  (* v_inv is v_inv_ck for every ck, so each clause is the cases
     theorem of the relation with the constructor of the value put
     in: the disjuncts of the other constructors go by
     distinctness, and the existentials of the rule are unwound
     against the arguments of the clause.
     Where a rule is recursive the two directions differ.  From a
     clause to the relation the value of the clause holds for every
     ck, so it holds for ck - 1.  The other way round the witness
     of the rule has to be the same for every ck: of a Block it is,
     because the pointer of x fixes the heap element and the
     element fixes the list (ALL2_SWAP then pulls the ck out of the
     list).  Of a RefPtr there are two rules for a thunk -- the
     value lives in a ThunkBlock of the heap, or it is x itself --
     and a derivation may use either at any ck.  So the one that
     every ck admits is found by taking the ck at which the other
     one fails and using v_inv_ck_mono to bring a derivation of a
     greater ck down to it *)
  (let (vr,vi,vc) = v_inv_ck in
   let rl = CONJUNCTS vr in
   let mono_thm = cake_thm "v_inv_ck_mono" in
   let unw = CONV_TAC(REDEPTH_CONV UNWIND_CONV) THEN
             REWRITE_TAC tidy_rws in
   let cas th = ONCE_REWRITE_RULE[vc] th in
   let dis = [distinctness "dataSem_v"; injectivity "dataSem_v";
              PAIR_EQ] in
   let base = REWRITE_TAC[v_inv_eq] THEN ONCE_REWRITE_TAC[vc] THEN
              REWRITE_TAC dis THEN unw in
   let ls_tm = `ys:(('a word_loc)heap_address)list` in
   let y_tm = `y:(('a word_loc)heap_address)` in
   (* a Block of a value that is no list of its own *)
   let blk_tac =
     REWRITE_TAC[v_inv_eq] THEN
     ASM_CASES_TAC `vs:(dataSem_v) list = []` THEN
     ASM_REWRITE_TAC[] THENL
      [base;
       EQ_TAC THENL
        [DISCH_TAC THEN
         FIRST_ASSUM(fun th -> MP_TAC(cas (SPEC `0` th))) THEN
         REWRITE_TAC dis THEN unw THEN ASM_REWRITE_TAC[] THEN
         DISCH_THEN(X_CHOOSE_THEN `p:num`
           (X_CHOOSE_THEN ls_tm STRIP_ASSUME_TAC)) THEN
         SUBST_LHS_TAC THEN
         MAP_EVERY EXISTS_TAC [`p:num`; ls_tm] THEN
         ASM_REWRITE_TAC[] THEN
         MATCH_MP_TAC ALL2_SWAP THEN X_GEN_TAC `ck:num` THEN
         FIRST_ASSUM(fun th -> MP_TAC(cas (SPEC `ck + 1` th))) THEN
         REWRITE_TAC(dis @ [injectivity "heap_address";
                            distinctness "heap_address"]) THEN
         unw THEN ASM_REWRITE_TAC[] THEN
         REWRITE_TAC[injectivity "option"; cake_def "BlockRep";
                     injectivity "heap_element"; PAIR_EQ] THEN
         unw THEN
         REWRITE_TAC[ARITH_RULE `~(ck + 1 = 0)`;
                     ARITH_RULE `(ck + 1) - 1 = ck`] THEN
         DISCH_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
         DISCH_THEN(X_CHOOSE_THEN `p:num`
           (X_CHOOSE_THEN ls_tm STRIP_ASSUME_TAC)) THEN
         X_GEN_TAC `ck:num` THEN SUBST_LHS_TAC THEN
         MATCH_MP_TAC(el 8 rl) THEN
         REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN
         DISCH_TAC THEN
         FIRST_ASSUM(fun th ->
           if can (term_match []
                     `EVERY2 (p:A->B->bool) l m`) (concl th)
           then MP_TAC th else fail()) THEN
         MATCH_MP_TAC MONO_ALL2 THEN BETA_TAC THEN
         REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]] in
   (* a RefPtr: the thunk of the two recursive rules is named by the
      lookup of the refs and its heap element by the pointer, so a
      derivation of one ck tells what the other ones must say *)
   let step = prove
    (`!ck conf n (refs:(dataSem_v bvlSem_ref) spt) b ev vv y x f tf
         (heap:(('a word_loc,data_to_word_memoryProof_tag#('a
           word_loc) list)heap_element) list).
        v_inv_ck (ck + 1) conf (RefPtr b n) refs (x,f,tf,heap) /\
        lookup n refs = SOME (Thunk ev vv) /\
        heap_lookup (FAPPLY f n) heap = SOME (ThunkBlock ev y)
        ==> (n IN FDOM f /\ ~b /\
             x = gc_shared_Pointer (FAPPLY f n)
                   (wordLang_Word (n2w 0)) /\
             (ev = Evaluated ==> dest_thunk vv refs = NotThunk) /\
             v_inv_ck ck conf vv refs (y,f,tf,heap)) \/
            (ev = Evaluated /\ dest_thunk vv refs = NotThunk /\ ~b /\
             v_inv_ck ck conf vv refs (x,f,tf,heap))`,
     REPEAT GEN_TAC THEN
     DISCH_THEN(fun th ->
       MP_TAC(cas (CONJUNCT1 th)) THEN
       MAP_EVERY ASSUME_TAC (CONJUNCTS(CONJUNCT2 th))) THEN
     REWRITE_TAC dis THEN unw THEN
     ASM_REWRITE_TAC[injectivity "option"; injectivity "bvlSem_ref";
                     distinctness "bvlSem_ref"; ThunkBlock_11;
                     GSYM NOT_EXISTS_THM] THEN
     unw THEN
     REWRITE_TAC[ARITH_RULE `~(ck + 1 = 0)`;
                 ARITH_RULE `(ck + 1) - 1 = ck`] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[]) in
   (* and the same where the heap element is not known yet *)
   let step2 = prove
    (`!ck conf n (refs:(dataSem_v bvlSem_ref) spt) b ev vv x f tf
         (heap:(('a word_loc,data_to_word_memoryProof_tag#('a
           word_loc) list)heap_element) list).
        v_inv_ck (ck + 1) conf (RefPtr b n) refs (x,f,tf,heap) /\
        lookup n refs = SOME (Thunk ev vv)
        ==> (?y. heap_lookup (FAPPLY f n) heap =
                   SOME (ThunkBlock ev y) /\
                 n IN FDOM f /\ ~b /\
                 x = gc_shared_Pointer (FAPPLY f n)
                       (wordLang_Word (n2w 0)) /\
                 (ev = Evaluated ==> dest_thunk vv refs = NotThunk)
                 /\ v_inv_ck ck conf vv refs (y,f,tf,heap)) \/
            (ev = Evaluated /\ dest_thunk vv refs = NotThunk /\ ~b /\
             v_inv_ck ck conf vv refs (x,f,tf,heap))`,
     REPEAT GEN_TAC THEN
     DISCH_THEN(fun th ->
       MP_TAC(cas (CONJUNCT1 th)) THEN
       MAP_EVERY ASSUME_TAC (CONJUNCTS(CONJUNCT2 th))) THEN
     REWRITE_TAC dis THEN unw THEN
     ASM_REWRITE_TAC[injectivity "option"; injectivity "bvlSem_ref";
                     distinctness "bvlSem_ref"; ThunkBlock_11;
                     GSYM NOT_EXISTS_THM] THEN
     unw THEN
     REWRITE_TAC[ARITH_RULE `~(ck + 1 = 0)`;
                 ARITH_RULE `(ck + 1) - 1 = ck`] THEN
     STRIP_TAC THEN ASM_MESON_TAC[]) in
   (* the three shapes that the relation at ck = 0 can have *)
   let fwd_pre =
     DISCH_TAC THEN
     FIRST_ASSUM(fun th -> MP_TAC(cas (SPEC `0` th))) THEN
     REWRITE_TAC dis THEN unw THEN ASM_REWRITE_TAC[] THEN
     DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC
       (DISJ_CASES_THEN2
          (X_CHOOSE_THEN `ev:thunk_mode`
             (X_CHOOSE_THEN `vv:dataSem_v`
                (X_CHOOSE_THEN y_tm STRIP_ASSUME_TAC)))
          (X_CHOOSE_THEN `vv:dataSem_v` STRIP_ASSUME_TAC))) in
   (* the terms are written with the type of a heap address in
      them, because a variable of the goal that the parser is left
      to type gets a type of its own and is another variable *)
   let vy = `!ck. v_inv_ck ck conf vv refs
                    (y:(('a word_loc)heap_address),f,tf,heap)` in
   let vx = `!ck. v_inv_ck ck conf vv refs
                    (x:(('a word_loc)heap_address),f,tf,heap)` in
   let sg_tm =
     `!ck2. ev = Evaluated /\ dest_thunk vv refs = NotThunk /\
            v_inv_ck ck2 conf vv refs
              (x:(('a word_loc)heap_address),f,tf,heap)` in
   let case2 =
     DISJ2_TAC THEN
     ASM_CASES_TAC vy THENL
      [DISJ1_TAC THEN
       MAP_EVERY EXISTS_TAC
         [`ev:thunk_mode`; `vv:dataSem_v`; y_tm] THEN
       ASM_REWRITE_TAC[];
       FIRST_ASSUM(fun nf ->
         MP_TAC(REWRITE_RULE[NOT_FORALL_THM] nf)) THEN
       DISCH_THEN(X_CHOOSE_THEN `ck1:num` ASSUME_TAC) THEN
       DISJ2_TAC THEN EXISTS_TAC `vv:dataSem_v` THEN
       SUBGOAL_THEN sg_tm ASSUME_TAC THENL
        [X_GEN_TAC `ck2:num` THEN
         FIRST_ASSUM(fun v -> FIRST_ASSUM(fun l ->
           FIRST_ASSUM(fun h ->
             MP_TAC(MATCH_MP step
               (CONJ (SPEC `(ck1 + ck2) + 1` v)
                     (CONJ l h)))))) THEN
         DISCH_THEN(DISJ_CASES_THEN2
           (fun l2 ->
              MP_TAC(MP (SPEC `ck1:num`
                (MATCH_MP mono_thm (last(CONJUNCTS l2))))
                (ARITH_RULE `ck1 <= ck1 + ck2`)) THEN
              ASM_REWRITE_TAC[])
           (fun r2 ->
              REWRITE_TAC[CONJUNCT1 r2;
                          CONJUNCT1(CONJUNCT2 r2)] THEN
              MATCH_ACCEPT_TAC(MP (SPEC `ck2:num`
                (MATCH_MP mono_thm (last(CONJUNCTS r2))))
                (ARITH_RULE `ck2 <= ck1 + ck2`))));
         FIRST_ASSUM(fun sg ->
           let s0 = SPEC `0` sg in
           ASM_REWRITE_TAC[CONJUNCT1 s0;
                           CONJUNCT1(CONJUNCT2 s0)] THEN
           X_GEN_TAC `ck:num` THEN
           MATCH_ACCEPT_TAC(last(CONJUNCTS(SPEC `ck:num` sg))))]] in
   let case3 =
     DISJ2_TAC THEN
     ASM_CASES_TAC vx THENL
      [DISJ2_TAC THEN EXISTS_TAC `vv:dataSem_v` THEN
       ASM_REWRITE_TAC[];
       FIRST_ASSUM(fun nf ->
         MP_TAC(REWRITE_RULE[NOT_FORALL_THM] nf)) THEN
       DISCH_THEN(X_CHOOSE_THEN `ck2:num` ASSUME_TAC) THEN
       DISJ1_TAC THEN
       FIRST_ASSUM(fun v -> FIRST_ASSUM(fun l ->
         MP_TAC(MATCH_MP step2 (CONJ (SPEC `ck2 + 1` v) l)))) THEN
       DISCH_THEN(DISJ_CASES_THEN2
         (X_CHOOSE_THEN y_tm (fun l ->
            MAP_EVERY EXISTS_TAC
              [`Evaluated`; `vv:dataSem_v`; y_tm] THEN
            ASM_REWRITE_TAC(CONJUNCTS l) THEN
            X_GEN_TAC `ck:num` THEN
            FIRST_ASSUM(fun v -> FIRST_ASSUM(fun l7 ->
              MP_TAC(MATCH_MP step
                (CONJ (SPEC `(ck + ck2) + 1` v)
                      (CONJ l7 (CONJUNCT1 l)))))) THEN
            DISCH_THEN(DISJ_CASES_THEN2
              (fun l2 -> MATCH_ACCEPT_TAC(MP (SPEC `ck:num`
                 (MATCH_MP mono_thm (last(CONJUNCTS l2))))
                 (ARITH_RULE `ck <= ck + ck2`)))
              (fun r2 ->
                 MP_TAC(MP (SPEC `ck2:num`
                   (MATCH_MP mono_thm (last(CONJUNCTS r2))))
                   (ARITH_RULE `ck2 <= ck + ck2`)) THEN
                 ASM_REWRITE_TAC[]))))
         (fun r ->
            MP_TAC(last(CONJUNCTS r)) THEN ASM_REWRITE_TAC[]))] in
   let rev_tac =
     DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC
       (DISJ_CASES_THEN2
          (X_CHOOSE_THEN `ev:thunk_mode`
             (X_CHOOSE_THEN `vv:dataSem_v`
                (X_CHOOSE_THEN y_tm STRIP_ASSUME_TAC)))
          (X_CHOOSE_THEN `vv:dataSem_v` STRIP_ASSUME_TAC))) THENL
      [X_GEN_TAC `ck:num` THEN SUBST_LHS_TAC THEN
       MATCH_MP_TAC(el 4 rl) THEN ASM_REWRITE_TAC[];
       X_GEN_TAC `ck:num` THEN ASM_MESON_TAC[el 5 rl];
       X_GEN_TAC `ck:num` THEN ASM_MESON_TAC[el 6 rl]] in
   let rp_tac =
     REWRITE_TAC[v_inv_eq] THEN EQ_TAC THENL
      [fwd_pre THENL
        [DISJ1_TAC THEN ASM_REWRITE_TAC[]; case2; case3];
       rev_tac] in
   REPEAT CONJ_TAC THENL
    [base THEN ASM_CASES_TAC `small_int (:'a) i` THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
     base; base; rp_tac; blk_tac]);;

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
  (* a RefPtr T is no thunk and no MutBlock, so the two rules of
     v_inv that ask for a RefPtr F do not apply and the annotation
     of the pointer is zero *)
  (let rpa = prove
    (`!conf o1.
        (!tg fin l c r.
           ~(o1 = SOME (bvlSem_MutBlock tg fin l c r))) ==>
        ref_ptr_annot conf o1 = wordLang_Word (n2w 0)`,
     REPEAT GEN_TAC THEN CASES_ON_NAME "o1" THEN
     REWRITE_TAC[cake_def "ref_ptr_annot"] THEN
     TRY(CASES_ON_NAME "a") THEN
     TRY MATCH_REDUCE_TAC THEN REWRITE_TAC[] THEN
     REWRITE_TAC[injectivity "option"; injectivity "bvlSem_ref"] THEN
     MESON_TAC[]) in
   REWRITE_TAC[v_inv_def] THEN EQ_TAC THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[rpa] THEN
   TRY(DISJ1_TAC THEN ASM_SIMP_TAC[rpa]));;


let MEM_IMP_v_size = cake_theorem "MEM_IMP_v_size[local]"
  (fun () ->
    `!l a. MEM a l ==> dataSem_v_size a < 1 + list_size dataSem_v_size
  l`)
  (REPEAT STRIP_TAC THEN
   MATCH_MP_TAC(ARITH_RULE `a <= b ==> a < 1 + b`) THEN
   MATCH_MP_TAC MEM_list_size THEN ASM_REWRITE_TAC[]);;

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
         (
          // a MutBlock is laid out exactly as the Block it finalises to; it is
          // mutable but carries an immutable BlockTag, so it is invisible to the
          // generational GC's isRef -- hence only the other GC kinds.
          //
          // While it is unfinalised, no timestamp may point at its cell: on
          // finalisation the very same pointer becomes a Block, which adds a
          // binding to tf, and INJ tf would break if one were there already.
          // MutCons allocates out of the unused space, so this holds on
          // creation; finalisation discharges it by setting fin.
          !gs. ~(data_to_word_config_gc_kind conf =
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
  (* a list of words without a repeat is no longer than the
     number of words there are: the values of its elements are
     a list of distinct numbers below dimword, and such a list
     is a subset of the numbers below dimword *)
  (let dist_lt = prove
    (`!(l:num list) n. ALL_DISTINCT l /\ (!x. MEM x l ==> x < n)
        ==> LENGTH l <= n`,
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     MP_TAC(REWRITE_RULE[GSYM ALL_DISTINCT]
       (ISPEC `l:num list` HAS_SIZE_SET_OF_LIST)) THEN
     ASM_REWRITE_TAC[HAS_SIZE] THEN
     DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
     TRANS_TAC LE_TRANS `CARD {i | i < (n:num)}` THEN CONJ_TAC THENL
      [MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
        [REWRITE_TAC[SUBSET; IN_SET_OF_LIST; IN_ELIM_THM] THEN
         ASM_MESON_TAC[];
         MESON_TAC[HAS_SIZE_NUMSEG_LT; HAS_SIZE]];
       REWRITE_TAC[CARD_NUMSEG_LT; LE_REFL]]) in
   STRIP_TAC THEN
   MP_TAC(ISPECL [`MAP (\x. w2n (theWord x)) (ws:('a word_loc) list)`;
                  `dimword (:'a)`] dist_lt) THEN
   REWRITE_TAC[LENGTH_MAP] THEN
   DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
    [FIRST_X_ASSUM MP_TAC THEN FIRST_X_ASSUM MP_TAC THEN
     REWRITE_TAC[TAUT `(p ==> q ==> r) <=> (p /\ q ==> r)`] THEN
     SPEC_TAC(`ws:('a word_loc) list`,`ws:('a word_loc) list`) THEN
     LIST_INDUCT_TAC THEN
     REWRITE_TAC[MAP; ALL_DISTINCT_CLAUSES; ALL] THEN
     STRIP_TAC THEN CONJ_TAC THENL
      [REWRITE_TAC[MEM_MAP; NOT_EXISTS_THM] THEN
       X_GEN_TAC `y:('a)word_loc` THEN STRIP_TAC THEN
       SUBGOAL_THEN `isWord (y:('a)word_loc)` MP_TAC THENL
        [ASM_MESON_TAC[ALL_MEM]; ALL_TAC] THEN
       UNDISCH_TAC `isWord (h:('a)word_loc)` THEN
       REWRITE_TAC[cake_thm "isWord_exists"] THEN
       DISCH_THEN(X_CHOOSE_THEN `wh:('a)word` SUBST_ALL_TAC) THEN
       DISCH_THEN(X_CHOOSE_THEN `wy:('a)word` SUBST_ALL_TAC) THEN
       ASM_MESON_TAC[cake_def "theWord"; VAL_EQ];
       FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
     REWRITE_TAC[MEM_MAP] THEN REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC[dimword; VAL_BOUND]]);;

let MOD_EQ_0_0 = cake_theorem "MOD_EQ_0_0"
  (fun () ->
    `!n b. 0 < b ==> (n MOD b = 0) ==> n < b ==> (n = 0)`)
  (REPEAT STRIP_TAC THEN ASM_MESON_TAC[MOD_LT]);;

let EVERY2_IMP_EVERY = cake_theorem "EVERY2_IMP_EVERY"
  (fun () ->
    `!xs ys. EVERY2 P xs ys ==> EVERY (\(x,y). P y x) (ZIP ys xs)`)
  (LIST_INDUCT_TAC THEN GEN_TAC THEN CASES_BY_NAME "ys" THEN
   REWRITE_TAC[ALL2; ALL; ZIP] THEN
   CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN ASM_SIMP_TAC[]);;

let EVERY2_IMP_EVERY2 = cake_theorem "EVERY2_IMP_EVERY2"
  (fun () ->
    `!xs ys P1 P2.
        (!x y. MEM x xs /\ MEM y ys /\ P1 x y ==> P2 x y) ==>
        EVERY2 P1 xs ys ==> EVERY2 P2 xs ys`)
  (* the relations are fixed before the induction, so that the
     induction hypothesis applies to the tails by MATCH_MP_TAC *)
  (let aux = prove
    (`!(P1:A->B->bool) P2 xs ys.
        (!x y. MEM x xs /\ MEM y ys /\ P1 x y ==> P2 x y) /\
        ALL2 P1 xs ys ==> ALL2 P2 xs ys`,
     GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
     X_GEN_TAC `ys:B list` THEN
     STRUCT_CASES_TAC(ISPEC `ys:B list` list_CASES_v) THEN
     REWRITE_TAC[ALL2; MEM] THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[]) in
   REPEAT GEN_TAC THEN
   REWRITE_TAC[TAUT `(p ==> q ==> r) <=> (p /\ q ==> r)`] THEN
   MATCH_ACCEPT_TAC aux);;

let MEM_EVERY2_IMP = cake_theorem "MEM_EVERY2_IMP"
  (fun () ->
    `!l x zs P. MEM x l /\ EVERY2 P zs l ==> (?z. MEM z zs /\ P z x)`)
  (LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN CASES_BY_NAME "zs" THEN
   REWRITE_TAC[ALL2; MEM] THEN STRIP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 data_to_word_memoryProofScript.sml:621-622: ML code, not
   ported *)

let EVERY2_APPEND_CONS = cake_theorem "EVERY2_APPEND_CONS"
  (fun () ->
    `!xs y ys zs P. EVERY2 P (xs ++ (y :: ys)) zs ==>
                     (?t1 t t2. (zs = t1 ++ (t :: t2)) /\ (LENGTH
                       t1 = LENGTH xs) /\
                              EVERY2 P xs t1 /\ P y t /\ EVERY2 P
                                ys t2)`)
  (let aux = prove
    (`!(P:A->B->bool) xs y ys zs.
        ALL2 P (APPEND xs (CONS y ys)) zs
        ==> ?u1 u u2. zs = APPEND u1 (CONS u u2) /\
                      LENGTH u1 = LENGTH xs /\
                      ALL2 P xs u1 /\ P y u /\ ALL2 P ys u2`,
     GEN_TAC THEN LIST_INDUCT_TAC THENL
      [REPEAT GEN_TAC THEN
       STRUCT_CASES_TAC(ISPEC `zs:B list` list_CASES_v) THEN
       REWRITE_TAC[APPEND; ALL2; LENGTH] THEN STRIP_TAC THEN
       MAP_EVERY EXISTS_TAC [`[]:B list`; `v:B`; `vs:B list`] THEN
       ASM_REWRITE_TAC[APPEND; LENGTH; ALL2];
       REPEAT GEN_TAC THEN
       STRUCT_CASES_TAC(ISPEC `zs:B list` list_CASES_v) THEN
       REWRITE_TAC[APPEND; ALL2; LENGTH] THEN STRIP_TAC THEN
       USE_IH THEN STRIP_TAC THEN
       MAP_EVERY EXISTS_TAC [`CONS (v:B) u1`; `u:B`; `u2:B list`] THEN
       ASM_REWRITE_TAC[APPEND; LENGTH; ALL2]]) in
   REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC aux);;

let EVERY2_SWAP = cake_theorem "EVERY2_SWAP"
  (fun () ->
    `!xs ys. EVERY2 P xs ys ==> EVERY2 (\y x. P x y) ys xs`)
  (LIST_INDUCT_TAC THEN GEN_TAC THEN CASES_BY_NAME "ys" THEN
   ASM_REWRITE_TAC[ALL2] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   ASM_SIMP_TAC[]);;

let EVERY2_APPEND_IMP_APPEND = cake_theorem "EVERY2_APPEND_IMP_APPEND"
  (fun () ->
    `!xs1 xs2 ys P.
        EVERY2 P (xs1 ++ xs2) ys ==>
        (?ys1 ys2. (ys = ys1 ++ ys2) /\ EVERY2 P xs1 ys1 /\
          EVERY2 P xs2 ys2)`)
  (let aux = prove
    (`!(P:A->B->bool) xs1 xs2 ys.
        ALL2 P (APPEND xs1 xs2) ys
        ==> ?u1 u2. ys = APPEND u1 u2 /\ ALL2 P xs1 u1 /\
                    ALL2 P xs2 u2`,
     GEN_TAC THEN LIST_INDUCT_TAC THENL
      [REPEAT GEN_TAC THEN REWRITE_TAC[APPEND] THEN STRIP_TAC THEN
       MAP_EVERY EXISTS_TAC [`[]:B list`; `ys:B list`] THEN
       ASM_REWRITE_TAC[APPEND; ALL2];
       REPEAT GEN_TAC THEN
       STRUCT_CASES_TAC(ISPEC `ys:B list` list_CASES_v) THEN
       REWRITE_TAC[APPEND; ALL2] THEN STRIP_TAC THEN
       USE_IH THEN STRIP_TAC THEN
       MAP_EVERY EXISTS_TAC [`CONS (v:B) u1`; `u2:B list`] THEN
       ASM_REWRITE_TAC[APPEND; ALL2]]) in
   REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC aux);;

(* HOL4 data_to_word_memoryProofScript.sml:654-655: ML code, not
   ported *)

(* HOL4 data_to_word_memoryProofScript.sml:657: ML code, not ported *)

(* HOL4 data_to_word_memoryProofScript.sml:659-660: ML code, not
   ported *)

let EVERY2_MAP_FST_SND = cake_theorem "EVERY2_MAP_FST_SND[local]"
  (fun () ->
    `!xs. EVERY2 P (MAP FST xs) (MAP SND xs) = EVERY (\(x,y). P x y)
  xs`)
  (let aux = prove
    (`!(P:A->B->bool) xs.
        ALL2 P (MAP FST xs) (MAP SND xs) <=> ALL (\(x,y). P x y) xs`,
     GEN_TAC THEN LIST_INDUCT_TAC THEN
     REWRITE_TAC[MAP; ALL2; ALL] THEN
     STRUCT_CASES_TAC(ISPEC `h:A#B` PAIR_SURJECTIVE) THEN
     ASM_REWRITE_TAC[FST; SND] THEN
     CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]) in
   REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC aux);;

let fapply_fupdate_update = cake_theorem "fapply_fupdate_update"
  (fun () ->
    `(FAPPLY) (f |+ p) = (FST p =+ SND p) ((FAPPLY) f)`)
  (let aux = prove
    (`!(f:(A,B)fmap) p. FAPPLY (f |+ p) = (FST p =+ SND p) (FAPPLY f)`,
     REPEAT GEN_TAC THEN
     STRUCT_CASES_TAC(ISPEC `p:A#B` PAIR_SURJECTIVE) THEN
     REWRITE_TAC[FUN_EQ_THM; UPDATE; FST; SND; FAPPLY_FUPDATE_THM] THEN
     GEN_TAC THEN REWRITE_TAC[EQ_SYM_EQ]) in
   REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC aux);;

let heap_lookup_APPEND1 = cake_theorem "heap_lookup_APPEND1[local]"
  (fun () ->
    `!h1 z h2.
       heap_length h1 <= z ==>
       (heap_lookup z (h1 ++ h2) = heap_lookup (z - heap_length
         h1) h2)`)
  (* past the first heap the lookup is the one of the second, and
     the two conditions of the clause are false by arithmetic *)
  (let hl = cake_def "heap_lookup" in
   let hlen_cl = prove
    (`heap_length [] = 0 /\
      (!x xs. heap_length (CONS x xs) =
              el_length x + heap_length xs)`,
     REWRITE_TAC[cake_def "heap_length"; MAP; SUM_DEF; ITLIST]) in
   LIST_INDUCT_TAC THEN
   REWRITE_TAC[hlen_cl; APPEND; hl; SUB_0; LE_0] THEN
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   MP_ISPEC_NAME "h" el_length_GT_0 THEN DISCH_TAC THEN
   COND_CASES_TAC THENL
    [SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
   COND_CASES_TAC THENL
    [SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[ARITH_RULE `a - (b + c) = a - b - c`] THEN
   FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let heap_lookup_APPEND2 = cake_theorem "heap_lookup_APPEND2[local]"
  (fun () ->
    `!h1 z h2.
       z < heap_length h1 ==>
       (heap_lookup z (h1 ++ h2) = heap_lookup z h1)`)
  (* heap_length is the SUM of the el_lengths, so its clauses come
     first here too *)
  (let hl = cake_def "heap_lookup" in
   let hlen_cl = prove
    (`heap_length [] = 0 /\
      (!x xs. heap_length (CONS x xs) =
              el_length x + heap_length xs)`,
     REWRITE_TAC[cake_def "heap_length"; MAP; SUM_DEF; ITLIST]) in
   LIST_INDUCT_TAC THEN
   REWRITE_TAC[hlen_cl; LT; APPEND; hl] THEN
   REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
   COND_CASES_TAC THEN REWRITE_TAC[] THEN
   DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let data_to_word_memoryProof_heap_lookup_APPEND =
  cake_theorem "heap_lookup_APPEND"
  (fun () ->
    `heap_lookup a (h1 ++ h2) =
      (if a < heap_length h1 then
      heap_lookup a h1 else
      heap_lookup (a - heap_length h1) h2)`)
  (COND_CASES_TAC THENL
    [MATCH_MP_TAC heap_lookup_APPEND2 THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC heap_lookup_APPEND1 THEN ASM_ARITH_TAC]);;

(* Prove refinement is maintained past GC calls *)

let data_to_word_memoryProof_LENGTH_ADDR_MAP =
  cake_theorem "LENGTH_ADDR_MAP[local]"
  (fun () ->
    `!xs f. LENGTH (ADDR_MAP f xs) = LENGTH xs`)
  (REPEAT GEN_TAC THEN
   MATCH_ACCEPT_TAC(GSYM (SPEC_ALL ADDR_MAP_LENGTH)));;

let EL_ADDR_MAP = cake_theorem "EL_ADDR_MAP[local]"
  (fun () ->
    `!xs n f.
         n < LENGTH xs ==> (EL n (ADDR_MAP f xs) = ADDR_APPLY f
           (EL n xs))`)
  (let addrmap = cake_def "ADDR_MAP" in
   let addrapply = cake_def "ADDR_APPLY" in
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; LT];
    REPEAT GEN_TAC THEN CASES_BY_NAME "h" THEN
    STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
    ASM_REWRITE_TAC[addrmap; addrapply; EL; HD; TL; LENGTH;
                    LT_SUC; LT_0]]);;

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
  (REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[v_inv_eq; v_inv_related_lemma]);;

let EVERY2_ADDR_MAP = cake_theorem "EVERY2_ADDR_MAP[local]"
  (fun () ->
    `!zs l. EVERY2 P (ADDR_MAP g zs) l <=>
              EVERY2 (\x y. P (ADDR_APPLY g x) y) zs l`)
  (let aux = prove
    (`!P g zs l.
        ALL2 P (ADDR_MAP g zs) l <=>
        ALL2 (\x y. P (ADDR_APPLY g x) y) zs l`,
     GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
     REWRITE_TAC[cake_def "ADDR_MAP"; ALL2_DEF] THEN
     CASES_BY_NAME "h" THEN
     REWRITE_TAC[cake_def "ADDR_MAP"; cake_def "ADDR_APPLY";
                 ALL2_DEF] THEN
     ASM_REWRITE_TAC[]) in
   REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC aux);;

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
  (* two heaps of which the elements are related have the same
     lengths of elements and the same elements that are data, which
     is what the cases of the relation say, so a lookup in the one is
     data exactly when the lookup in the other is *)
  (let (_,_,cases) = gc_heap_inline_rel in
   let isd = prove
    (`!xs n d. isSomeDataElement (SOME (DataElement xs n d))`,
     REWRITE_TAC[cake_def "isSomeDataElement"] THEN MESON_TAC[]) in
   let lem = prove
    (`!x y. gc_heap_inline_rel dest_evaluated_thunk_rel heap x y
        ==> el_length x = el_length y /\
            (isSomeDataElement (SOME x) <=>
             isSomeDataElement (SOME y))`,
     REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [cases] THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC[cake_def "el_length"; isd]) in
   let lcases =
     W(fun (_,w) ->
       STRUCT_CASES_TAC(ISPEC (rand(lhand w)) list_CASES_v)) in
   LIST_INDUCT_TAC THEN GEN_TAC THEN lcases THEN
   REWRITE_TAC[ALL2; cake_def "heap_lookup"] THEN
   STRIP_TAC THEN
   FIRST_ASSUM(fun r -> MP_TAC(MATCH_MP lem r)) THEN
   DISCH_THEN(CONJUNCTS_THEN2 (fun e -> REWRITE_TAC[e])
     ASSUME_TAC) THEN
   GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   FIRST_ASSUM(fun ih -> FIRST_ASSUM(fun r ->
     MATCH_ACCEPT_TAC(MATCH_MP ih r))));;

let ThunkBlock_not_EQ = cake_theorem "ThunkBlock_not_EQ[local]"
  (fun () ->
    `~(ThunkBlock ev x = Bignum i) /\ ~(ThunkBlock ev x = Word64Rep
  (:'a) w) /\ ~(ThunkBlock ev x = BlockRep n xs) /\ ~(ThunkBlock ev x
  = RefBlock zs) /\ ~(ThunkBlock ev x = Bytes be flag bs ys)`)
  (REWRITE_TAC[cake_def "ThunkBlock"; cake_def "Bignum";
               cake_def "Word64Rep"; cake_def "BlockRep";
               cake_def "RefBlock"; cake_def "Bytes"] THEN
   PAIRARG_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   COND_CASES_TAC THEN
   REWRITE_TAC[injectivity "heap_element"; PAIR_EQ;
               distinctness "data_to_word_memoryProof_tag";
               NOT_CONS_NIL]);;

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
  (* the lookup of the one heap is data, so the element of the other
     at that address is the one the relation relates it to: either
     the same element, or the data of the same length and the same
     tag whose addresses the relation relates one by one *)
  (let (_,_,cases) = gc_heap_inline_rel in
   let (irules,_,_) = gc_inline_rel in
   let ellen = prove
    (`!inline h1 x y. gc_heap_inline_rel inline h1 x y
        ==> el_length x = el_length y`,
     REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [cases] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[cake_def "el_length"]) in
   let refl2 = prove
    (`!inline h1 l. ALL2 (gc_inline_rel inline h1) l l`,
     GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC[ALL2; CONJUNCT1 irules]) in
   let lcases =
     W(fun (_,w) ->
       STRUCT_CASES_TAC(ISPEC (rand(lhand w)) list_CASES_v)) in
   (* the witness of the existential is what the first conjunct of
      its body equates the bound variable with *)
   let eq_exists =
     W(fun (_,w) ->
       let v,bod = dest_exists w in
       let eq = hd (conjuncts bod) in
       EXISTS_TAC (if rand eq = v then lhand eq else rand eq)) in
   LIST_INDUCT_TAC THEN GEN_TAC THEN lcases THEN
   REWRITE_TAC[ALL2; cake_def "heap_lookup";
               distinctness "option"] THEN
   STRIP_TAC THEN GEN_TAC THEN
   FIRST_ASSUM(fun r -> REWRITE_TAC[MATCH_MP ellen r]) THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
    [REWRITE_TAC[injectivity "option"] THEN
     DISCH_THEN SUBST_ALL_TAC THEN USE_CHANGED [cases] THEN
     REWRITE_TAC[injectivity "heap_element"] THEN STRIP_TAC THEN
     ASM_REWRITE_TAC[injectivity "heap_element"] THEN
     eq_exists THEN ASM_REWRITE_TAC[refl2];
     COND_CASES_TAC THEN
     REWRITE_TAC[distinctness "option"] THEN
     FIRST_ASSUM(fun ih -> FIRST_ASSUM(fun r ->
       MATCH_ACCEPT_TAC(MATCH_MP ih r)))]);;

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
  (REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[v_inv_eq; gc_heap_inline_rel_v_inv_lemma]);;

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
  (REWRITE_TAC[cake_def "gc_inline_related"] THEN REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[bc_stack_ref_inv_gc_inline;
                 bc_stack_ref_inv_gc_related_roots_heap]);;

let data_up_to_APPEND = cake_theorem "data_up_to_APPEND[simp]"
  (fun () ->
    `data_up_to (heap_length xs) (xs ++ ys) <=> EVERY isDataElement xs`)
  (REWRITE_TAC[cake_def "data_up_to"; heap_split_APPEND_if; LT_REFL;
               SUB_REFL; heap_split_0] THEN
   MATCH_REDUCE_TAC THEN
   REWRITE_TAC[APPEND_NIL; injectivity "option"; PAIR_EQ] THEN
   MESON_TAC[]);;

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
  (* an address of the second heap is in the range of f, so it is the
     image of an address of the first, which is reachable *)
  (REWRITE_TAC[cake_def "all_reachable_from_roots"] THEN
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(p:num) IN FRANGE (f:(num,num)fmap)` MP_TAC THENL
    [ASM_REWRITE_TAC[IN_ELIM_THM; cake_def "isSomeDataElement"] THEN
     ASM_MESON_TAC[];
     REWRITE_TAC[FMAP_IN_FRANGE] THEN STRIP_TAC THEN
     FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
     MATCH_MP_TAC reachable_addresses_related THEN
     CONJ_TAC THENL
      [ASM_MESON_TAC[];
       CONJ_TAC THENL
        [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[SUBSET_REFL]]]]);;

let heap_lookup_expand_eq_SOME =
  cake_theorem "heap_lookup_expand_eq_SOME"
  (fun () ->
    `heap_lookup a (heap ++ heap_expand n) = SOME (DataElement ys l d)
  <=>
     heap_lookup a heap = SOME (DataElement ys l d)`)
  (* past the heap the lookup is in the expansion, which is one
     Unused element, and that is not a DataElement *)
  (let hexp = cake_def "heap_expand" in
   let hlk = cake_def "heap_lookup" in
   let opt = [distinctness "option"; injectivity "option";
              distinctness "heap_element"] in
   REWRITE_TAC[heap_lookup_APPEND] THEN COND_CASES_TAC THEN
   REWRITE_TAC[] THEN
   MATCH_MP_TAC(TAUT `~a /\ ~b ==> (a <=> b)`) THEN CONJ_TAC THENL
    [REWRITE_TAC[hexp] THEN COND_CASES_TAC THEN REWRITE_TAC[hlk] THEN
     REPEAT COND_CASES_TAC THEN REWRITE_TAC opt;
     DISCH_TAC THEN
     FIRST_ASSUM(MP_TAC o MATCH_MP heap_lookup_LESS) THEN
     ASM_ARITH_TAC]);;

let isSomeDataElement_heap_lookup =
  cake_theorem "isSomeDataElement_heap_lookup"
  (fun () ->
    `isSomeDataElement (heap_lookup a (heap ++ heap_expand n)) =
     isSomeDataElement (heap_lookup a heap)`)
  (let hexp = cake_def "heap_expand" in
   let hlk = cake_def "heap_lookup" in
   let isde = cake_def "isSomeDataElement" in
   let opt = [distinctness "option"; injectivity "option";
              distinctness "heap_element"] in
   REWRITE_TAC[heap_lookup_APPEND] THEN COND_CASES_TAC THEN
   REWRITE_TAC[] THEN
   MATCH_MP_TAC(TAUT `~a /\ ~b ==> (a <=> b)`) THEN CONJ_TAC THENL
    [REWRITE_TAC[hexp] THEN COND_CASES_TAC THEN
     REWRITE_TAC[hlk; isde] THEN REPEAT COND_CASES_TAC THEN
     REWRITE_TAC(isde :: opt);
     REWRITE_TAC[isde] THEN STRIP_TAC THEN
     FIRST_ASSUM(MP_TAC o MATCH_MP heap_lookup_LESS) THEN
     ASM_ARITH_TAC]);;

let gc_related_APPEND_heap_expand =
  cake_theorem "gc_related_APPEND_heap_expand"
  (fun () ->
    `gc_related f heap (heap2 ++ heap_expand n) = gc_related f heap
  heap2`)
  (REWRITE_TAC[cake_def "gc_related"; isSomeDataElement_heap_lookup;
               heap_lookup_expand_eq_SOME]);;

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
  (* a move of the gc keeps the data in h2 and the references in
     r4: of a Data it changes nothing, of a Pointer at a
     DataElement it puts the element in r4 when its tag is a
     mutable one and at the end of h2 when it is not, and the
     statement's hypothesis says that isRef of the configuration
     is exactly that.  The section's `record_simps` is what HOL4's
     record simp set does: the accessors of gc_state over its
     updates, which HOL Light's define_record does not give *)
  (let hd_is n t =
   (try fst(dest_const(fst(strip_comb t))) = n
    with Failure _ -> false) in
   (* the accessors of a record over its updates: what HOL4's record
      simp set does and HOL Light's define_record does not *)
   let record_simps name flds =
     let tbl = assoc name (!the_records) in
     let accof (_,(accth,_)) =
       fst(strip_comb(lhs(snd(strip_forall(concl accth))))) in
     let updof (_,(_,updth)) =
       fst(strip_comb(lhs(snd(strip_forall(concl updth))))) in
     let rty = hd(tl(fst(splitlist dest_fun_ty
                           (type_of (updof (hd tbl)))))) in
     let sv = mk_var("s",rty) in
     let cas = cases_of rty in
     itlist (fun a l ->
       if not (mem (fst a) flds) then l else
       itlist (fun u l ->
         let acc = accof a and upd = updof u in
         let fty = hd(fst(splitlist dest_fun_ty (type_of upd))) in
         let f = mk_var("f",fty) in
         let lhs' = mk_comb(acc,mk_comb(mk_comb(upd,f),sv)) in
         let rhs' = if fst a = fst u then mk_comb(f,mk_comb(acc,sv))
                    else mk_comb(acc,sv) in
         prove(mk_eq(lhs',rhs'),
               STRUCT_CASES_TAC(ISPEC sv cas) THEN
               REWRITE_TAC(record_thms name)) :: l) tbl l) tbl [] in
   let gcsimps = record_simps "gc_state" ["h2"; "r4"] in
   (* a DataElement is a reference when its tag is a mutable one *)
   let isref = prove
    (`!ys l tag qs.
        data_to_word_memoryProof_isRef (DataElement ys l (tag,qs)) <=>
        isMutTag tag`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[cake_def "data_to_word_memoryProof_isRef"] THEN
     MATCH_REDUCE_TAC THEN
     REWRITE_TAC[injectivity "heap_element"; PAIR_EQ] THEN
     CONV_TAC(REDEPTH_CONV UNWIND_CONV) THEN
     REWRITE_TAC[EXISTS_UNIQUE_REFL; SELECT_REFL]) in
   let isdata = prove
    (`!ys l d. isDataElement (DataElement ys l d)`,
     REWRITE_TAC[cake_def "isDataElement"] THEN MESON_TAC[]) in
   DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
   FIRST_X_ASSUM(fun th ->
     if (try hd_is "gen_gc_gc_move" (lhs (concl th))
         with Failure _ -> false)
     then MP_TAC th else fail()) THEN
   CASES_BY_NAME "x" THEN
   REWRITE_TAC[cake_def "gen_gc_gc_move"] THEN
   EVERY_CASE_TAC THEN
   TRY(CASES_BY_NAME "a2") THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   TRY COND_CASES_TAC THEN
   TRY(W(fun (asl,w) ->
     let t = find_term (fun u ->
       hd_is "gc_forward_ptr" u &&
       length (snd(strip_comb u)) = 5) w in
     MP_TAC(ISPEC t PAIR_SURJECTIVE)) THEN
     DISCH_THEN(CHOOSE_THEN(CHOOSE_THEN SUBST1_TAC))) THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
   REPEAT(FIRST_X_ASSUM(fun th ->
     if is_conj (concl th) then STRIP_ASSUME_TAC th else fail())) THEN
   VAR_EQ_TAC THEN
   ASM_REWRITE_TAC(gcsimps @
                   [K_DEF; ALL_APPEND; ALL; isdata; isref]) THEN
   TRY(FIRST_X_ASSUM(fun h ->
     if is_forall (concl h) then RULE_ASSUM_TAC(REWRITE_RULE[h])
     else fail())) THEN
   ASM_REWRITE_TAC[]);;

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
  (* the move of a list is the move of its head and then of its
     tail, and each of them keeps the three invariants, which is
     what the theorem about one move says *)
  (let gmd = GEN_ALL (cake_thm "gc_move_data_refs_split") in
   LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
    [REWRITE_TAC[cake_def "gen_gc_gc_move_list"; PAIR_EQ] THEN
     DISCH_THEN(CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM))
       STRIP_ASSUME_TAC) THEN
     ASM_REWRITE_TAC[];
     REWRITE_TAC[cake_def "gen_gc_gc_move_list"] THEN
     PAIRARG_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     PAIRARG_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[PAIR_EQ] THEN
     DISCH_THEN(CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM))
       STRIP_ASSUME_TAC) THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_EXISTS_TAC THEN
     ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC gmd THEN ASM_EXISTS_TAC THEN ASM_REWRITE_TAC[]]);;

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
  (* the loop moves the refs or the data and goes round again, and
     each step keeps the three invariants: the clock is the
     induction, the two theorems above are the step, and an update
     of the ok, the r2 or the r4 field leaves the heaps alone *)
  (let okf = prove
     (`!f (s:('a,'b)gc_state).
         (gc_state_h1 (gc_state_ok_fupd f s) = gc_state_h1 s) /\
         (gc_state_h2 (gc_state_ok_fupd f s) = gc_state_h2 s) /\
         (gc_state_r1 (gc_state_ok_fupd f s) = gc_state_r1 s) /\
         (gc_state_r2 (gc_state_ok_fupd f s) = gc_state_r2 s) /\
         (gc_state_r3 (gc_state_ok_fupd f s) = gc_state_r3 s) /\
         (gc_state_r4 (gc_state_ok_fupd f s) = gc_state_r4 s)`,
      REPEAT GEN_TAC THEN RECORD_CASES_TAC `s:('a,'b)gc_state`) in
    let fupds = prove
     (`!(x:(('a,'b)heap_element)list) (s:('a,'b)gc_state).
         (gc_state_h1 (gc_state_r2_fupd (K x) s) = gc_state_h1 s) /\
         (gc_state_h2 (gc_state_r2_fupd (K x) s) = gc_state_h2 s) /\
         (gc_state_r1 (gc_state_r2_fupd (K x) s) = gc_state_r1 s) /\
         (gc_state_r2 (gc_state_r2_fupd (K x) s) = x) /\
         (gc_state_r3 (gc_state_r2_fupd (K x) s) = gc_state_r3 s) /\
         (gc_state_r4 (gc_state_r2_fupd (K x) s) = gc_state_r4 s) /\
         (gc_state_h1 (gc_state_r4_fupd (K x) s) = gc_state_h1 s) /\
         (gc_state_h2 (gc_state_r4_fupd (K x) s) = gc_state_h2 s) /\
         (gc_state_r1 (gc_state_r4_fupd (K x) s) = gc_state_r1 s) /\
         (gc_state_r2 (gc_state_r4_fupd (K x) s) = gc_state_r2 s) /\
         (gc_state_r3 (gc_state_r4_fupd (K x) s) = gc_state_r3 s) /\
         (gc_state_r4 (gc_state_r4_fupd (K x) s) = x)`,
      REPEAT GEN_TAC THEN RECORD_CASES_TAC `s:('a,'b)gc_state`) in
    let gmrd = GEN_ALL (cake_thm "gc_move_refs_data_refs_split") in
    let gmdd = GEN_ALL (cake_thm "gc_move_data_data_refs_split") in
    let refl_exists (asl,w as gl) =
      let vs,bod = strip_exists w in
      let l,r = dest_eq (hd (conjuncts bod)) in
      let i = term_match [] l r in
      MAP_EVERY EXISTS_TAC (map (instantiate i) vs) gl in
    INDUCT_TAC THEN REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV)
      [cake_def "gen_gc_gc_move_loop"] THEN
    EVERY_CASE_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[NOT_SUC; ARITH_RULE `SUC n - 1 = n`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[okf] THEN
    TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN refl_exists THEN
        ASM_REWRITE_TAC[]) THEN
    TRY(MATCH_MP_TAC gmdd THEN refl_exists THEN ASM_REWRITE_TAC[]) THEN
    TRY(MATCH_MP_TAC gmrd THEN refl_exists THEN
        REWRITE_TAC[fupds] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND]) THEN
        ASM_REWRITE_TAC[ALL_APPEND; ALL]));;

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
  (REWRITE_TAC[cake_def "heap_expand"] THEN COND_CASES_TAC THEN
   REWRITE_TAC[ALL; cake_def "data_to_word_memoryProof_isRef"] THEN
   MATCH_REDUCE_TAC THEN REWRITE_TAC[]);;

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
  (* the generations that reset_gens makes all start where the first
     heap ends, and nothing of that heap points into the space that
     the expansion leaves: a pointer of a DataElement points at a
     DataElement, and what is in the expansion is an Unused *)
  (let notin = prove
    (`!(hh:((A,B)heap_element) list) rr n p.
        heap_length hh <= p /\ p < n + heap_length hh
        ==> ~(isSomeDataElement
                (heap_lookup p (hh ++ heap_expand n ++ rr)))`,
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     REWRITE_TAC[cake_thm "heap_lookup_APPEND"] THEN
     ASM_SIMP_TAC[ARITH_RULE `(h:num) <= p ==> ~(p < h)`;
                  cake_thm "heap_length_heap_expand"] THEN
     SUBGOAL_THEN `p - heap_length (hh:((A,B)heap_element) list) < n`
       ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
      [ASM_ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[cake_def "heap_expand"] THEN
     REWRITE_TAC[cake_def "heap_lookup"; cake_def "el_length"] THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC[cake_def "isSomeDataElement";
                     injectivity "option"; distinctness "option";
                     distinctness "heap_element"] THEN
     ASM_SIMP_TAC[ARITH_RULE
       `p - h < n /\ ~(n = 0) ==> p - h < (n - 1) + 1`] THEN
     REWRITE_TAC[cake_def "isSomeDataElement"; distinctness "option"]) in
   STRIP_TAC THEN
   REWRITE_TAC[cake_def "reset_gens"] THEN
   STRUCT_CASES_TAC (ISPEC `data_to_word_config_gc_kind conf`
     (cases "gc_kind")) THEN
   MATCH_REDUCE_TAC THEN
   REWRITE_TAC[cake_def "gen_state_ok"; ALL] THEN
   REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; K_DEF] THEN
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN
   REWRITE_TAC[cake_def "gen_start_ok"] THEN
   ONCE_REWRITE_TAC[cake_thm "heap_split_APPEND_if"] THEN
   REWRITE_TAC[LT_REFL; SUB_REFL; cake_thm "heap_split_0"] THEN
   MATCH_REDUCE_TAC THEN
   REWRITE_TAC[APPEND_NIL] THEN
   W(fun (asl,w) ->
     let bod = snd(strip_exists w) in
     let pr = rand(lhs(lhand bod)) in
     let a,b = dest_pair pr in
     MAP_EVERY EXISTS_TAC [a; b]) THEN
   REWRITE_TAC[] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   MATCH_MP_TAC(TAUT `(~a /\ ~b ==> F) ==> a \/ b`) THEN
   STRIP_TAC THEN
   W(fun (asl,w) ->
     let ths = map snd asl in
     let hd_is n th =
       (try fst(dest_const(fst(strip_comb(concl th)))) = n
        with Failure _ -> false) in
     let arg_is n th =
       (try fst(dest_const(fst(strip_comb(
              el 0 (snd(strip_comb(concl th))))))) = n
        with Failure _ -> false) in
     let okth = find (hd_is "heap_ok") ths in
     let memd = find (fun th -> hd_is "MEM" th && arg_is "DataElement" th)
                  ths in
     let memp = find (fun th -> hd_is "MEM" th &&
                                arg_is "gc_shared_Pointer" th) ths in
     let dargs = snd(strip_comb(el 0 (snd(strip_comb(concl memd))))) in
     let pargs = snd(strip_comb(el 0 (snd(strip_comb(concl memp))))) in
     let cl = CONJUNCT2(CONJUNCT2
       (REWRITE_RULE[cake_def "heap_ok"] okth)) in
     MP_TAC(SPECL (dargs @ pargs) cl)) THEN
   ASM_REWRITE_TAC[MEM_APPEND] THEN
   DISCH_TAC THEN
   W(fun (asl,w) ->
     let ths = map snd asl in
     let hd_is n th =
       (try fst(dest_const(fst(strip_comb(concl th)))) = n
        with Failure _ -> false) in
     let sde = find (hd_is "isSomeDataElement") ths in
     let heap = rand(el 0 (snd(strip_comb(concl sde)))) in
     let hh = lhand heap in
     let rr = rand(rand heap) in
     MP_TAC(ISPECL [hh; rr] notin)) THEN
   ASM_SIMP_TAC[] THEN
   DISCH_THEN(fun th -> MP_TAC(SPEC_ALL th)) THEN
   ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

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
  (* the split at the later point goes through the earlier one: the
     middle piece is what the split of the second half gives, and
     the induction follows the two splits down the heap, one element
     at a time *)
  (let exwit = W(fun (asl,w) ->
     EXISTS_TAC (lhs (el 1 (conjuncts (snd(strip_exists w)))))) in
   let stripconj =
     REPEAT(FIRST_X_ASSUM(fun th ->
       if is_conj (concl th) then STRIP_ASSUME_TAC th else fail())) in
   let aux = prove
    (`!(heap:((A,B)heap_element) list) n1 n2 h1 h2 h3 h4.
        heap_split n2 heap = SOME (h3,h4) /\
        heap_split n1 heap = SOME (h1,h2) /\ n1 <= n2
        ==> ?m. h2 = m ++ h4 /\ h3 = h1 ++ m /\
                heap = h1 ++ m ++ h4 /\
                heap_split (n2 - heap_length h1) h2 = SOME (m,h4)`,
     LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
     REWRITE_TAC[cake_def "heap_split"] THENL
      [ASM_CASES_TAC `n2 = 0` THEN
       ASM_REWRITE_TAC[distinctness "option"] THEN
       ASM_CASES_TAC `n1 = 0` THEN
       ASM_REWRITE_TAC[distinctness "option"] THEN
       REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
       STRIP_TAC THEN VAR_EQ_TAC THEN
       EXISTS_TAC `[]:((A,B)heap_element) list` THEN
       REWRITE_TAC[APPEND; cake_thm "heap_length_NIL"; SUB_0] THEN
       ASM_REWRITE_TAC[cake_def "heap_split"];
       ALL_TAC] THEN
     ASM_CASES_TAC `n2 = 0` THEN
     ASM_REWRITE_TAC[distinctness "option"] THENL
      [STRIP_TAC THEN
       SUBGOAL_THEN `n1 = 0` SUBST_ALL_TAC THENL
        [ASM_ARITH_TAC; ALL_TAC] THEN
       RULE_ASSUM_TAC(REWRITE_RULE[injectivity "option"; PAIR_EQ]) THEN
       stripconj THEN VAR_EQ_TAC THEN
       EXISTS_TAC `[]:((A,B)heap_element) list` THEN
       REWRITE_TAC[APPEND; cake_thm "heap_length_NIL"; SUB_0;
                   cake_def "heap_split"];
       ALL_TAC] THEN
     ASM_CASES_TAC `n2 < el_length (h:(A,B)heap_element)` THEN
     ASM_REWRITE_TAC[distinctness "option"] THEN
     ASM_CASES_TAC `n1 = 0` THEN ASM_REWRITE_TAC[] THENL
      [EVERY_CASE_TAC THEN
       REWRITE_TAC[distinctness "option"; injectivity "option";
                   PAIR_EQ] THEN
       STRIP_TAC THEN stripconj THEN VAR_EQ_TAC THEN
       REWRITE_TAC[APPEND; cake_thm "heap_length_NIL"; SUB_0] THEN
       exwit THEN
       FIRST_X_ASSUM(fun ih ->
         FIRST_ASSUM(fun a1 ->
           MP_TAC(MATCH_MP ih (CONJ a1 (CONJ
             (ISPEC `t:((A,B)heap_element) list`
                (GEN_ALL (cake_thm "heap_split_0")))
             (SPEC `n2 - el_length (h:(A,B)heap_element)`
                LE_0)))))) THEN
       REWRITE_TAC[APPEND] THEN
       DISCH_THEN(X_CHOOSE_THEN `mm:((A,B)heap_element) list`
         STRIP_ASSUME_TAC) THEN
       VAR_EQ_TAC THEN
       ASM_REWRITE_TAC[APPEND; CONS_11; cake_def "heap_split"] THEN
       MATCH_REDUCE_TAC THEN REWRITE_TAC[];
       ALL_TAC] THEN
     ASM_CASES_TAC `n1 < el_length (h:(A,B)heap_element)` THEN
     ASM_REWRITE_TAC[distinctness "option"] THEN
     EVERY_CASE_TAC THEN
     REWRITE_TAC[distinctness "option"; injectivity "option";
                 PAIR_EQ] THEN
     STRIP_TAC THEN stripconj THEN VAR_EQ_TAC THEN
     SUBGOAL_THEN `n1 - el_length (h:(A,B)heap_element) <=
                   n2 - el_length (h:(A,B)heap_element)`
       ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     FIRST_X_ASSUM(fun ih ->
       FIRST_ASSUM(fun a1 -> FIRST_ASSUM(fun a2 -> FIRST_ASSUM(fun a3 ->
         MP_TAC(MATCH_MP ih (CONJ a1 (CONJ a2 a3))) THEN
         DISCH_THEN(X_CHOOSE_THEN `mm:((A,B)heap_element) list`
           STRIP_ASSUME_TAC) THEN
         VAR_EQ_TAC THEN
         EXISTS_TAC `mm:((A,B)heap_element) list` THEN
         ASM_REWRITE_TAC[APPEND; CONS_11;
                         cake_thm "heap_length_CONS"] THEN
         REWRITE_TAC[ARITH_RULE `a - (b + c) = (a - b) - c`] THEN
         ASM_REWRITE_TAC[]))))) in
   REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC aux);;

let heap_split_LESS_EQ = cake_theorem "heap_split_LESS_EQ"
  (fun () ->
    `!heap n x. heap_split n heap = SOME x ==> n <= heap_length heap`)
  (LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[cake_def "heap_split"; heap_length_NIL;
               heap_length_CONS] THEN
   EVERY_CASE_TAC THEN REPEAT COND_CASES_TAC THEN
   ASM_REWRITE_TAC[distinctness "option"; LE_0] THEN
   DISCH_TAC THEN USE_IH THEN ASM_ARITH_TAC);;

let isRef_heap_expand = cake_theorem "isRef_heap_expand[local]"
  (fun () ->
    `!x. EVERY (\x. ~(data_to_word_memoryProof_isRef x)) (heap_expand
  x)`)
  (GEN_TAC THEN REWRITE_TAC[cake_def "heap_expand"] THEN
   COND_CASES_TAC THEN
   REWRITE_TAC[ALL; cake_def "data_to_word_memoryProof_isRef"] THEN
   MATCH_REDUCE_TAC THEN REWRITE_TAC[]);;

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
  (* the expansion is one element that is not a DataElement, so it
     contributes no pointer and shifts none *)
  (let dp = cake_def "data_pointers" in
   let aux = prove
    (`!heap n. data_pointers (APPEND heap (heap_expand n)) =
               data_pointers heap`,
     LIST_INDUCT_TAC THENL
      [GEN_TAC THEN REWRITE_TAC[APPEND; cake_def "heap_expand"] THEN
       COND_CASES_TAC THEN
       GEN_REWRITE_TAC LAND_CONV [dp] THEN MATCH_REDUCE_TAC THEN
       REWRITE_TAC[dp] THEN MATCH_REDUCE_TAC THEN REWRITE_TAC[MAP];
       GEN_TAC THEN REWRITE_TAC[APPEND] THEN CASES_BY_NAME "h" THEN
       GEN_REWRITE_TAC LAND_CONV [dp] THEN MATCH_REDUCE_TAC THEN
       GEN_REWRITE_TAC RAND_CONV [dp] THEN MATCH_REDUCE_TAC THEN
       ASM_REWRITE_TAC[]]) in
   MATCH_ACCEPT_TAC aux);;

let data_length_APPEND_heap_expand =
  cake_theorem "data_length_APPEND_heap_expand"
  (fun () ->
    `data_length (heap ++ heap_expand n) = data_length heap`)
  (* the expansion contributes no data element, and the data length
     of a cons is the length of the head when it is one *)
  (let hl = cake_def "heap_lookup" in
   let dp = cake_def "data_pointers" in
   let dl = cake_def "data_length" in
   let ll = cake_def "lookup_len" in
   (* a lookup past the first element is one in the tail *)
   let shift_lookup = prove
    (`!(x:((A),(B))heap_element) xs n.
        heap_lookup (n + el_length x) (CONS x xs) = heap_lookup n xs`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [hl] THEN
     MP_TAC(ISPEC `x:((A),(B))heap_element` el_length_GT_0) THEN
     DISCH_TAC THEN
     COND_CASES_TAC THENL
      [SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
     COND_CASES_TAC THENL
      [SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC) in
   let map_shift = prove
    (`!(x:((A),(B))heap_element) xs ps.
        MAP (lookup_len (CONS x xs)) (MAP (\n. n + el_length x) ps) =
        MAP (lookup_len xs) ps`,
     GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC[MAP; ll; shift_lookup]) in
   let dl_cons = prove
    (`(!ys l d xs. data_length (CONS (DataElement ys l d) xs) =
                   el_length (DataElement ys l d) + data_length xs) /\
      (!k xs. data_length (CONS (Unused k:((A),(B))heap_element) xs) =
              data_length xs) /\
      (!n d l xs.
         data_length (CONS (ForwardPointer n d l:((A),(B))heap_element)
                           xs) = data_length xs)`,
     REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [dl] THEN
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [dp] THEN
     MATCH_REDUCE_TAC THEN
     REWRITE_TAC[MAP; map_shift; SUM_DEF; ITLIST; dl; ll; hl] THEN
     REWRITE_TAC[ADD_CLAUSES]) in
   let aux = prove
    (`!heap n. data_length (APPEND heap (heap_expand n)) =
               data_length heap`,
     LIST_INDUCT_TAC THENL
      [GEN_TAC THEN REWRITE_TAC[APPEND; cake_def "heap_expand"] THEN
       COND_CASES_TAC THEN
       REWRITE_TAC[dl; dp; MAP; SUM_DEF; ITLIST] THEN
       MATCH_REDUCE_TAC THEN REWRITE_TAC[MAP; SUM_DEF; ITLIST];
       GEN_TAC THEN REWRITE_TAC[APPEND] THEN
       CASES_ON_NAME "h" THEN
       ASM_REWRITE_TAC[dl_cons]]) in
   MATCH_ACCEPT_TAC aux);;

let data_length_heap_length = cake_theorem "data_length_heap_length"
  (fun () ->
    `EVERY isDataElement heap ==>
     data_length heap = heap_length heap`)
  (* every element is a data element, so each contributes its own
     length and the data length is the heap length *)
  (let hl = cake_def "heap_lookup" in
   let dp = cake_def "data_pointers" in
   let dl = cake_def "data_length" in
   let ll = cake_def "lookup_len" in
   (* a lookup past the first element is one in the tail *)
   let shift_lookup = prove
    (`!(x:((A),(B))heap_element) xs n.
        heap_lookup (n + el_length x) (CONS x xs) = heap_lookup n xs`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [hl] THEN
     MP_TAC(ISPEC `x:((A),(B))heap_element` el_length_GT_0) THEN
     DISCH_TAC THEN
     COND_CASES_TAC THENL
      [SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
     COND_CASES_TAC THENL
      [SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC) in
   let map_shift = prove
    (`!(x:((A),(B))heap_element) xs ps.
        MAP (lookup_len (CONS x xs)) (MAP (\n. n + el_length x) ps) =
        MAP (lookup_len xs) ps`,
     GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC[MAP; ll; shift_lookup]) in
   let dl_cons = prove
    (`(!ys l d xs. data_length (CONS (DataElement ys l d) xs) =
                   el_length (DataElement ys l d) + data_length xs) /\
      (!k xs. data_length (CONS (Unused k:((A),(B))heap_element) xs) =
              data_length xs) /\
      (!n d l xs.
         data_length (CONS (ForwardPointer n d l:((A),(B))heap_element)
                           xs) = data_length xs)`,
     REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [dl] THEN
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [dp] THEN
     MATCH_REDUCE_TAC THEN
     REWRITE_TAC[MAP; map_shift; SUM_DEF; ITLIST; dl; ll; hl] THEN
     REWRITE_TAC[ADD_CLAUSES]) in
   let hlen_cl = prove
    (`heap_length [] = 0 /\
      (!x xs. heap_length (CONS x xs) =
              el_length x + heap_length xs)`,
     REWRITE_TAC[cake_def "heap_length"; MAP; SUM_DEF; ITLIST]) in
   let aux = prove
    (`!heap. EVERY isDataElement heap
             ==> data_length heap = heap_length heap`,
     LIST_INDUCT_TAC THENL
      [REWRITE_TAC[dl; dp] THEN MATCH_REDUCE_TAC THEN
       REWRITE_TAC[MAP; SUM_DEF; ITLIST; hlen_cl];
       REWRITE_TAC[ALL] THEN STRIP_TAC THEN
       CASES_ON_NAME "h" THEN
       RULE_ASSUM_TAC(REWRITE_RULE[cake_def "isDataElement";
                                   distinctness "heap_element";
                                   injectivity "heap_element"]) THEN
       TRY(FIRST_ASSUM CONTR_TAC) THEN
       ASM_SIMP_TAC[dl_cons; hlen_cl]]) in
   MATCH_ACCEPT_TAC aux);;

let data_length_CONS = cake_theorem "data_length_CONS"
  (fun () ->
    `!x xs. data_length (x :: xs) = data_length [x] + data_length xs`)
  (* what HOL4's simp set does with data_pointers and lookup_len: the
     pointers of the tail are shifted by the length of the head, and
     a lookup at a shifted pointer is the lookup in the tail *)
  (let dp = cake_def "data_pointers" in
   let dl = cake_def "data_length" in
   let ll = cake_def "lookup_len" in
   let dp_cl = prove
    (`data_pointers ([]:((A,B)heap_element)list) = [] /\
      (!xs l d (t:((A,B)heap_element)list).
         data_pointers (CONS (DataElement xs l d) t) =
         CONS 0 (MAP (\n. n + el_length
                             (DataElement xs l d:(A,B)heap_element))
                     (data_pointers t))) /\
      (!k (t:((A,B)heap_element)list).
         data_pointers (CONS (Unused k) t) =
         MAP (\n. n + el_length (Unused k:(A,B)heap_element))
             (data_pointers t)) /\
      (!a b c (t:((A,B)heap_element)list).
         data_pointers (CONS (ForwardPointer a b c) t) =
         MAP (\n. n + el_length
                        (ForwardPointer a b c:(A,B)heap_element))
             (data_pointers t))`,
     REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [dp] THEN MATCH_REDUCE_TAC THEN
     REWRITE_TAC[]) in
   let hl_sh = prove
    (`!n (x:(A,B)heap_element) xs.
        heap_lookup (n + el_length x) (CONS x xs) = heap_lookup n xs`,
     REPEAT GEN_TAC THEN
     MP_TAC(ISPEC `x:(A,B)heap_element` el_length_GT_0) THEN
     REWRITE_TAC[cake_def "heap_lookup"] THEN DISCH_TAC THEN
     COND_CASES_TAC THENL
      [SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
     COND_CASES_TAC THENL
      [SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[ARITH_RULE `(n + m) - m = n`]) in
   let map_sh = prove
    (`!l (x:(A,B)heap_element) xs.
        MAP (lookup_len (CONS x xs)) (MAP (\n. n + el_length x) l) =
        MAP (lookup_len xs) l`,
     LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ll; hl_sh]) in
   let ll_0 = prove
    (`!(x:(A,B)heap_element) xs.
        lookup_len (CONS x xs) 0 = el_length x`,
     REWRITE_TAC[ll; cake_def "heap_lookup"] THEN
     CONV_TAC(ONCE_DEPTH_CONV MATCH_CONV) THEN REWRITE_TAC[]) in
   let aux = prove
    (`!(x:(A,B)heap_element) xs.
        data_length (CONS x xs) = data_length [x] + data_length xs`,
     GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[dl] THEN
     STRUCT_CASES_TAC
       (ISPEC `x:(A,B)heap_element`
              (cases_of `:(A,B)heap_element`)) THEN
     REWRITE_TAC[dp_cl; MAP; map_sh; ll_0; SUM_DEF; ITLIST] THEN
     ARITH_TAC) in
   MATCH_ACCEPT_TAC aux);;

let data_length_APPEND = cake_theorem "data_length_APPEND"
  (fun () ->
    `!xs ys. data_length (xs ++ ys) = data_length xs + data_length ys`)
  (let dl_nil = prove
    (`data_length ([]:((A,B)heap_element)list) = 0`,
     REWRITE_TAC[cake_def "data_length"] THEN
     GEN_REWRITE_TAC ONCE_DEPTH_CONV [cake_def "data_pointers"] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[MAP; SUM_DEF; ITLIST]) in
   LIST_INDUCT_TAC THENL
    [REWRITE_TAC[APPEND; dl_nil] THEN ARITH_TAC;
     GEN_TAC THEN REWRITE_TAC[APPEND] THEN
     GEN_REWRITE_TAC LAND_CONV [data_length_CONS] THEN
     GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [data_length_CONS] THEN
     ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let data_length_heap_expand = cake_theorem "data_length_heap_expand"
  (fun () ->
    `data_length (heap_expand n) = 0`)
  (REWRITE_TAC[cake_def "heap_expand"] THEN COND_CASES_TAC THEN
   REWRITE_TAC[cake_def "data_length"] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [cake_def "data_pointers"] THEN
   MATCH_REDUCE_TAC THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [cake_def "data_pointers"] THEN
   MATCH_REDUCE_TAC THEN REWRITE_TAC[MAP; SUM_DEF; ITLIST]);;

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
  (LIST_INDUCT_TAC THENL
    [REPEAT GEN_TAC THEN
     REWRITE_TAC[heap_length_NIL; APPEND; cake_def "heap_store"] THEN
     REWRITE_TAC[PAIR_EQ; EQ_SYM_EQ];
     REPEAT GEN_TAC THEN
     REWRITE_TAC[heap_length_CONS; APPEND] THEN
     GEN_REWRITE_TAC LAND_CONV [cake_def "heap_store"] THEN
     MP_ISPEC_NAME "h" el_length_GT_0 THEN DISCH_TAC THEN
     ASM_SIMP_TAC[ARITH_RULE `1 <= a ==> ~(a + b = 0)`;
                  ARITH_RULE `1 <= a ==> ~(a + b < a)`;
                  ARITH_RULE `(a + b) - a = b`] THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[PAIR_EQ]]);;

let heap_store_rel_def = cake_define
  `heap_store_rel heap heap2 <=>
     (!ptr. isSomeDataElement (heap_lookup ptr heap) ==>
            (heap_lookup ptr heap2 = heap_lookup ptr heap))`;;

let isSomeDataElement_heap_lookup_lemma1 =
  cake_theorem "isSomeDataElement_heap_lookup_lemma1[local]"
  (fun () ->
    `isSomeDataElement (heap_lookup n (Unused k :: xs)) <=>
       k < n /\ isSomeDataElement (heap_lookup (n - (k + 1)) xs)`)
  (let isde = cake_def "isSomeDataElement" in
   let opt = [distinctness "option"; injectivity "option";
              distinctness "heap_element"] in
   REWRITE_TAC[cake_def "heap_lookup"; cake_def "el_length"] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC(isde :: opt) THENL
    [MATCH_MP_TAC(TAUT `~a ==> ~(a /\ b)`) THEN ASM_ARITH_TAC;
     COND_CASES_TAC THEN ASM_REWRITE_TAC(isde :: opt) THENL
      [MATCH_MP_TAC(TAUT `~a ==> ~(a /\ b)`) THEN ASM_ARITH_TAC;
       SUBGOAL_THEN `(k:num) < n` (fun th -> REWRITE_TAC[th]) THEN
       ASM_ARITH_TAC]]);;

let isSomeDataElement_heap_lookup_lemma2 =
  cake_theorem "isSomeDataElement_heap_lookup_lemma2[local]"
  (fun () ->
    `isSomeDataElement (heap_lookup n (heap_expand k ++ xs)) <=>
       k <= n /\ isSomeDataElement (heap_lookup (n - k) xs)`)
  (REWRITE_TAC[cake_def "heap_expand"] THEN COND_CASES_TAC THEN
   ASM_REWRITE_TAC[APPEND; SUB_0; LE_0] THEN
   REWRITE_TAC[isSomeDataElement_heap_lookup_lemma1] THEN
   ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> (n - (k - 1 + 1) = n - k)`;
                ARITH_RULE `~(k = 0) ==> (k - 1 < n <=> k <= n)`]);;

let isSomeDataElement_heap_lookup_lemma3 =
  cake_theorem "isSomeDataElement_heap_lookup_lemma3[local]"
  (fun () ->
    `~(n = 0) ==>
         (isSomeDataElement (heap_lookup n (x :: xs)) <=>
          el_length x <= n /\ isSomeDataElement (heap_lookup (n -
            el_length x) xs))`)
  (let isde = cake_def "isSomeDataElement" in
   let opt = [distinctness "option"; injectivity "option";
              distinctness "heap_element"] in
   DISCH_TAC THEN REWRITE_TAC[cake_def "heap_lookup"] THEN
   ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
   ASM_REWRITE_TAC(isde :: opt) THENL
    [MATCH_MP_TAC(TAUT `~a ==> ~(a /\ b)`) THEN ASM_ARITH_TAC;
     ASM_SIMP_TAC[ARITH_RULE `~(a:num < b) ==> (b <= a <=> T)`]]);;

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
  (REWRITE_TAC[cake_def "heap_store_rel";
               cake_def "isSomeDataElement"] THEN
   MESON_TAC[]);;

(* cons *)

let v_inv_SUBMAP_lemma = cake_theorem "v_inv_SUBMAP_lemma[local]"
  (fun () ->
    `!ck w refs x f tf heap.
       v_inv conf w refs (x,f,tf,heap) ==>
         f SUBMAP f1 /\
         tf SUBMAP tf1 /\
         heap_store_rel heap heap1 ==>
           v_inv_ck ck conf w refs (x,f1,tf1,heap1)`)
  (* complete induction on the ck of the relation: the value of the
     invariant is taken apart with v_inv_def and the rule of the
     relation for that shape is applied, where the greater maps
     give the same values and the greater heap the same data
     elements.  What the rule asks of a value inside the value is
     the induction hypothesis at ck - 1 *)
  (let (vr,_,_) = v_inv_ck in
   let rl = CONJUNCTS vr in
   let vdef = cake_thm "v_inv_def" in
   (* a data element of the heap is still there after the store *)
   let keep = prove
    (`!h1 h2 n e.
        heap_store_rel h1 h2 ==> heap_lookup n h1 = SOME e ==>
        isDataElement e ==> heap_lookup n h2 = SOME e`,
     REWRITE_TAC[cake_def "heap_store_rel"] THEN
     REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `n:num` th)) THEN
     ASM_REWRITE_TAC[cake_def "isSomeDataElement";
                     injectivity "option"] THEN
     FIRST_X_ASSUM(MP_TAC o
                   REWRITE_RULE[cake_def "isDataElement"]) THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]) in
   (* the four shapes of a data element that the invariant uses.
      The theorem of the file that says this and more stands
      later in the file than this one does *)
   let isde4 = prove
    (`isDataElement (BlockRep tag ys1) /\
      isDataElement (Word64Rep (:'a) w) /\
      isDataElement (ThunkBlock ev v) /\
      isDataElement (Bignum i)`,
     REWRITE_TAC[cake_def "isDataElement"; cake_def "BlockRep";
                 cake_def "Word64Rep"; cake_def "ThunkBlock";
                 cake_def "Bignum"] THEN
     PAIRARG_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REPEAT CONJ_TAC THEN TRY COND_CASES_TAC THEN MESON_TAC[]) in
   let keep_of hsr hl =
     REWRITE_RULE[isde4] (MATCH_MP (MATCH_MP keep hsr) hl) in
   let KEEP_TAC =
     FIRST_ASSUM(fun hsr -> FIRST_ASSUM(fun hl ->
       MATCH_ACCEPT_TAC(keep_of hsr hl))) in
   let lt1 = ARITH_RULE `~(ck = 0) ==> ck - 1 < ck` in
   (* the b of a RefPtr that the two thunk rules ask to be false *)
   let NOT_VAR_TAC =
     FIRST_ASSUM(fun nb ->
       if is_neg(concl nb) && is_var(rand(concl nb))
       then SUBST_ALL_TAC(EQF_INTRO nb) else fail()) in
   let setup =
     MATCH_MP_TAC num_WF THEN X_GEN_TAC `ck:num` THEN
     DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
     CASES_ON_NAME "w" THEN USE_CHANGED [vdef] in
   (* a Number is a small one or a Bignum of the heap *)
   let c1 =
     COND_CASES_TAC THEN STRIP_TAC THEN SUBST_LHS_TAC THENL
      [MATCH_MP_TAC(el 0 rl) THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC(el 1 rl) THEN ASM_REWRITE_TAC[] THEN KEEP_TAC] in
   let c2 = STRIP_TAC THEN REPEAT SUBST_LHS_TAC THEN
            MATCH_MP_TAC(el 2 rl) THEN KEEP_TAC in
   (* a Block is a BlockNil or a BlockRep whose elements the
      induction hypothesis carries over one by one *)
   let c3 =
     COND_CASES_TAC THEN STRIP_TAC THEN REPEAT SUBST_LHS_TAC THENL
      [MATCH_MP_TAC(el 7 rl) THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC(el 8 rl) THEN REPEAT CONJ_TAC THENL
        [FIRST_ASSUM MATCH_ACCEPT_TAC;
         DISCH_TAC THEN
         FIRST_ASSUM(fun a2th ->
           if can (term_match [] `EVERY2 (p:A->B->bool) l m`)
                  (concl a2th)
           then MP_TAC a2th else fail()) THEN
         MATCH_MP_TAC MONO_ALL2 THEN BETA_TAC THEN
         REPEAT STRIP_TAC THEN CK_IH_TAC;
         FIRST_ASSUM(fun sm -> FIRST_ASSUM(fun fl ->
           MATCH_ACCEPT_TAC(MATCH_MP FLOOKUP_SUBMAP (CONJ sm fl))));
         KEEP_TAC]] in
   let c4 = STRIP_TAC THEN REPEAT SUBST_LHS_TAC THEN
            MATCH_ACCEPT_TAC(el 3 rl) in
   (* and a RefPtr is a plain reference or one of the two thunks,
      whose value and heap element the rule names and not its
      conclusion, so MESON applies the rule *)
   let d5 =
     FIRST_ASSUM(fun sm -> FIRST_ASSUM(fun fd ->
       let s = MATCH_MP (MATCH_MP SUBMAP_FAPPLY sm) fd in
       REPEAT SUBST_LHS_TAC THEN REWRITE_TAC[CONJUNCT2 s] THEN
       MATCH_MP_TAC(el 4 rl) THEN
       REWRITE_TAC[CONJUNCT1 s] THEN REPEAT CONJ_TAC THEN
       TRY(FIRST_ASSUM MATCH_ACCEPT_TAC))) in
   let d6 =
     NOT_VAR_TAC THEN
     FIRST_ASSUM(fun sm -> FIRST_ASSUM(fun fd ->
       let s = MATCH_MP (MATCH_MP SUBMAP_FAPPLY sm) fd in
       RULE_ASSUM_TRY(REWRITE_RULE[CONJUNCT2 s]) THEN
       REPEAT SUBST_LHS_TAC THEN
       REWRITE_TAC[CONJUNCT2 s] THEN
       FIRST_ASSUM(fun hsr -> FIRST_ASSUM(fun hl ->
         FIRST_ASSUM(fun ih ->
           ASM_MESON_TAC[el 5 rl; CONJUNCT1 s; keep_of hsr hl;
                         SPEC `ck - 1` ih; lt1]))))) in
   let d7 =
     NOT_VAR_TAC THEN
     FIRST_ASSUM(fun ih ->
       ASM_MESON_TAC[el 6 rl; SPEC `ck - 1` ih; lt1]) in
   let c5 =
     DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC
       (DISJ_CASES_THEN2 STRIP_ASSUME_TAC STRIP_ASSUME_TAC)) THENL
      [d5; d6; d7] in
   setup THENL [c1; c2; c3; c4; c5]);;

let v_inv_SUBMAP = cake_theorem "v_inv_SUBMAP[local]"
  (fun () ->
    `!w x.
         f SUBMAP f1 /\ tf SUBMAP tf1 /\
         heap_store_rel heap heap1 /\
         v_inv conf w refs (x,f,tf,heap) ==>
         v_inv conf w refs (x,f1,tf1,heap1)`)
  (REPEAT STRIP_TAC THEN ASM_MESON_TAC[v_inv_eq; v_inv_SUBMAP_lemma]);;

let heap_store_rel_v_inv = cake_theorem "heap_store_rel_v_inv"
  (fun () ->
    `!w x.
         heap_store_rel heap heap1 /\
         v_inv conf w refs (x,f,tf,heap) ==>
         v_inv conf w refs (x,f,tf,heap1)`)
  (REPEAT STRIP_TAC THEN MATCH_MP_TAC v_inv_SUBMAP THEN
   ASM_REWRITE_TAC[SUBMAP_REFL]);;

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
  (* the store into the unused space is a store at the address it
     keeps, so the lookup below that address gives the same; the
     induction is the one of the theorem about a store and a lookup
     that the file states further down, and HOL4 repeats it here as
     well *)
  (let hsl = prove
    (`!heap heap2 a (x:((A,B)heap_element)list) n.
        heap_store a x heap = (heap2,T) /\ n < a
        ==> heap_lookup n heap = heap_lookup n heap2`,
     LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
      [REWRITE_TAC[cake_def "heap_store"; PAIR_EQ];
       GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV)
         [cake_def "heap_store"] THEN
       COND_CASES_TAC THENL
        [ASM_REWRITE_TAC[ARITH_RULE `((n:num) < 0) <=> F`];
         ALL_TAC] THEN
       COND_CASES_TAC THENL
        [REWRITE_TAC[PAIR_EQ]; ALL_TAC] THEN
       PAIRARG_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
       REWRITE_TAC[PAIR_EQ] THEN
       DISCH_THEN(CONJUNCTS_THEN2
         (CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
            (fun th -> SUBST_ALL_TAC(EQT_INTRO th)))
         ASSUME_TAC) THEN
       ONCE_REWRITE_TAC[cake_def "heap_lookup"] THEN
       COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
       COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_EXISTS_TAC THEN
       ASM_REWRITE_TAC[] THEN ARITH_ASM_TAC]) in
   REPEAT GEN_TAC THEN
   REWRITE_TAC[cake_def "heap_store_unused_alt"] THEN
   COND_CASES_TAC THENL
    [MATCH_ACCEPT_TAC hsl;
     REWRITE_TAC[PAIR_EQ]]);;

let heap_split_heap_store = cake_theorem "heap_split_heap_store[local]"
  (fun () ->
    `!heap e h1 h2 a y heap2.
       heap_split e heap = SOME (h1,h2) /\
       heap_store a y heap = (heap2,T) /\ e <= a ==>
       (?h3. heap_split e heap2 = SOME (h1,h3))`)
  (* a store above the split leaves the first half of the split as
     it was: the store goes down the heap one element at a time and
     the induction carries the split along *)
  (let stripconj =
     REPEAT(FIRST_X_ASSUM(fun th ->
       if is_conj (concl th) then STRIP_ASSUME_TAC th else fail())) in
   let aux = prove
    (`!(heap:((A,B)heap_element) list) e h1 h2 a y heap2.
        heap_split e heap = SOME (h1,h2) /\
        heap_store a y heap = (heap2,T) /\ e <= a
        ==> ?h3. heap_split e heap2 = SOME (h1,h3)`,
     LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
     REWRITE_TAC[cake_def "heap_split"; cake_def "heap_store"] THENL
      [REWRITE_TAC[PAIR_EQ];
       ALL_TAC] THEN
     ASM_CASES_TAC `e = 0` THEN ASM_REWRITE_TAC[] THENL
      [REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
       STRIP_TAC THEN stripconj THEN VAR_EQ_TAC THEN
       W(fun (asl,w) ->
         EXISTS_TAC (rand(lhs(snd(strip_exists w))))) THEN
       REWRITE_TAC[cake_thm "heap_split_0"];
       ALL_TAC] THEN
     ASM_CASES_TAC `e < el_length (h:(A,B)heap_element)` THEN
     ASM_REWRITE_TAC[distinctness "option"] THEN
     STRIP_TAC THEN
     SUBGOAL_THEN
       `~(a = 0) /\ ~(a < el_length (h:(A,B)heap_element))`
       STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     RULE_ASSUM_TAC(REWRITE_RULE
       [ASSUME `~(a = 0)`;
        ASSUME `~(a < el_length (h:(A,B)heap_element))`]) THEN
     FIRST_X_ASSUM(fun st ->
       if (try fst(dest_const(fst(strip_comb(rhs(concl st))))) =
                "," with Failure _ -> false)
       then MP_TAC st else fail()) THEN
     MP_TAC(ISPEC
       `heap_store (a - el_length (h:(A,B)heap_element))
          (y:((A,B)heap_element) list) t`
       PAIR_SURJECTIVE) THEN
     DISCH_THEN(X_CHOOSE_THEN `xs1:((A,B)heap_element) list`
       (X_CHOOSE_THEN `c1:bool` ASSUME_TAC)) THEN
     ASM_REWRITE_TAC[] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN VAR_EQ_TAC THEN
     RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `c1:bool`]) THEN
     FIRST_X_ASSUM(fun sp ->
       if (try fst(dest_const(rator(rhs(concl sp)))) = "SOME"
           with Failure _ -> false)
       then MP_TAC sp else fail()) THEN
     EVERY_CASE_TAC THEN
     REWRITE_TAC[distinctness "option"; injectivity "option";
                 PAIR_EQ] THEN
     STRIP_TAC THEN stripconj THEN VAR_EQ_TAC THEN
     SUBGOAL_THEN `e - el_length (h:(A,B)heap_element) <=
                   a - el_length (h:(A,B)heap_element)`
       ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     FIRST_X_ASSUM(fun ih ->
       FIRST_ASSUM(fun a1 -> FIRST_ASSUM(fun a2 -> FIRST_ASSUM(fun a3 ->
         MP_TAC(MATCH_MP ih (CONJ a1 (CONJ a2 a3))) THEN
         DISCH_THEN(X_CHOOSE_TAC `h3:((A,B)heap_element) list`) THEN
         EXISTS_TAC `h3:((A,B)heap_element) list` THEN
         ASM_REWRITE_TAC[cake_def "heap_split"] THEN
         MATCH_REDUCE_TAC THEN REWRITE_TAC[]))))) in
   REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC aux);;

let heap_store_unused_alt_gen_state_ok =
  cake_theorem "heap_store_unused_alt_gen_state_ok[local]"
  (fun () ->
    `heap_store_unused_alt a k x heap = (heap2,T) /\
     gen_state_ok a (a + k) heap gens ==>
     gen_state_ok (a + el_length x) (a + k) heap2 gens`)
  (* and the same of the store at the low end: the references start
     where they started, and a is higher by the element, which no
     start of a generation is above *)
  (
   let transfer = prove
    (`!(hp:((A,B)heap_element)list) hp2 aa kk xx ss.
        heap_store aa ([xx] ++ heap_expand (kk - el_length xx)) hp =
          (hp2,T) /\
        ss <= aa /\ gen_start_ok hp (aa + kk) ss
        ==> gen_start_ok hp2 (aa + kk) ss`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[cake_def "gen_start_ok"] THEN
     DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (REPEAT_TCL CHOOSE_THEN
         (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
     FIRST_ASSUM(fun hs -> FIRST_ASSUM(fun sp -> FIRST_ASSUM(fun le ->
       MP_TAC(MATCH_MP (cake_thm "heap_split_heap_store")
         (CONJ sp (CONJ hs le)))))) THEN
     DISCH_THEN(X_CHOOSE_THEN `h3:((A,B)heap_element)list`
       ASSUME_TAC) THEN
     ASM_EXISTS_TAC THEN ASM_REWRITE_TAC[]) in
   STRIP_TAC THEN CASES_ON_NAME "gens" THEN
   RULE_ASSUM_TAC(REWRITE_RULE[cake_def "gen_state_ok"]) THEN
   REWRITE_TAC[cake_def "gen_state_ok"] THEN
   USE_CHANGED [cake_def "heap_store_unused_alt"] THEN
   COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
   FIRST [DISCH_THEN(fun th ->
            CONTR_TAC(REWRITE_RULE[] (CONJUNCT2 th)));
          DISCH_TAC] THEN
   FIRST_ASSUM(fun gs ->
     let c1 = CONJUNCT1 gs and c2 = CONJUNCT2 gs in
     CONJ_TAC THENL
      [MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC (lhand (concl c1)) THEN
       CONJ_TAC THENL
        [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_ARITH_TAC;
         ACCEPT_TAC c1];
       MATCH_MP_TAC ALL_IMP THEN
       EXISTS_TAC (lhand (concl c2)) THEN
       CONJ_TAC THENL
        [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC transfer THEN
         W(fun (asl,w) ->
           let hs = find (fun (_,th) ->
             (try fst(dest_const(fst(strip_comb(lhand(concl th))))) =
                  "heap_store"
              with Failure _ -> false)) asl in
           EXISTS_TAC (el 2 (snd(strip_comb
             (lhand (concl (snd hs))))))) THEN
         W(fun gl -> EXISTS_TAC (var_by_name "x" gl)) THEN
         ASM_REWRITE_TAC[] THEN
         FIRST_ASSUM(fun m ->
           ACCEPT_TAC(MATCH_MP (REWRITE_RULE[GSYM ALL_MEM] c1) m));
         ACCEPT_TAC c2]]));;

let isDataElement_lemmas = cake_theorem "isDataElement_lemmas[simp]"
  (fun () ->
    `isDataElement (DataElement x1 x2 x3) /\
      isDataElement (BlockRep tag ys1) /\
      isDataElement (Word64Rep (:'a) w) /\
      isDataElement (RefBlock ws) /\
      isDataElement (Bytes y1 y2 y3 y4) /\
      isDataElement (ThunkBlock ev v) /\
      isDataElement (Bignum i)`)
  (REWRITE_TAC[cake_def "isDataElement"; cake_def "BlockRep";
               cake_def "Word64Rep"; cake_def "RefBlock";
               cake_def "Bytes"; cake_def "ThunkBlock";
               cake_def "Bignum"] THEN
   PAIRARG_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REPEAT CONJ_TAC THEN TRY COND_CASES_TAC THEN MESON_TAC[]);;

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
  (* the induction hypothesis has a hypothesis (the tail is not
     empty), so the step is a SIMP and not a REWRITE *)
  (LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN GEN_TAC THEN
   ONCE_REWRITE_TAC[cake_def "list_to_BlockReps"] THEN
   CASES_ON_NAME "t" THEN MATCH_REDUCE_TAC THEN
   ASM_SIMP_TAC[heap_length_NIL; heap_length_CONS;
                cake_def "BlockRep"; cake_def "el_length";
                LENGTH; NOT_CONS_NIL] THEN
   ARITH_TAC);;

let heap_lookup_heap_length = cake_theorem "heap_lookup_heap_length"
  (fun () ->
    `heap_lookup (heap_length h1) (h1 ++ h2) = heap_lookup 0 h2`)
  (REWRITE_TAC[heap_lookup_APPEND; LT_REFL; SUB_REFL]);;

let list_to_BlockReps_heap_lookup_0 =
  cake_theorem "list_to_BlockReps_heap_lookup_0"
  (fun () ->
    `~(xs = []) ==>
     isSomeDataElement (heap_lookup 0 (list_to_BlockReps conf x
       len xs))`)
  (LIST_CASES_TAC ["xs"] THEN REWRITE_TAC[NOT_CONS_NIL] THEN
   ONCE_REWRITE_TAC[cake_def "list_to_BlockReps"] THEN
   LIST_CASES_TAC ["t"] THEN MATCH_REDUCE_TAC THEN
   REWRITE_TAC[cake_def "heap_lookup"; cake_def "isSomeDataElement";
               cake_def "BlockRep"] THEN
   MESON_TAC[]);;

let list_to_BlockReps_isDataElement =
  cake_theorem "list_to_BlockReps_isDataElement"
  (fun () ->
    `!xs x len.
       ~(xs = []) ==>
       EVERY isDataElement (list_to_BlockReps conf x len xs)`)
  (LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC[cake_def "list_to_BlockReps"] THEN
   CASES_ON_NAME "t" THEN MATCH_REDUCE_TAC THEN
   ASM_SIMP_TAC[ALL; isDataElement_lemmas; NOT_CONS_NIL]);;

let list_to_BlockReps_data_up_to_lem =
  cake_theorem "list_to_BlockReps_data_up_to_lem[local]"
  (fun () ->
    `~(xs = []) /\
        h1 = list_to_BlockReps conf x len xs ==>
        data_up_to (heap_length h1) (h1 ++ h2)`)
  (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[data_up_to_APPEND] THEN
   MATCH_MP_TAC list_to_BlockReps_isDataElement THEN
   ASM_REWRITE_TAC[]);;

(* HOL4 data_to_word_memoryProofScript.sml:2360-2363: a theorem that
   HOL4 states as the value of an ML expression:
   list_to_BlockReps_data_up_to *)

let list_to_BlockReps_ForwardPointer =
  cake_theorem "list_to_BlockReps_ForwardPointer"
  (fun () ->
    `~(xs = []) ==> FILTER isForwardPointer (list_to_BlockReps conf x
  len xs) = []`)
  (* every element is a DataElement, and a DataElement is not a
     ForwardPointer *)
  (let fl = prove
    (`!l:((A,B)heap_element)list.
        ALL isDataElement l ==> FILTER isForwardPointer l = []`,
     LIST_INDUCT_TAC THEN
     REWRITE_TAC[ALL; FILTER; cake_def "isDataElement"] THEN
     REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC[cake_def "isForwardPointer"] THEN
     MATCH_REDUCE_TAC THEN ASM_SIMP_TAC[]) in
   DISCH_TAC THEN MATCH_MP_TAC fl THEN
   MATCH_MP_TAC list_to_BlockReps_isDataElement THEN
   ASM_REWRITE_TAC[]);;

let list_to_BlockReps_Ref = cake_theorem "list_to_BlockReps_Ref"
  (fun () ->
    `!xs len x conf. ~(xs = []) ==> EVERY (\v.
  ~(data_to_word_memoryProof_isRef v)) (list_to_BlockReps conf x len
  xs)`)
  (let not_ref = prove
    (`!tag ys. ~(isRef (BlockRep tag ys))`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[cake_def "BlockRep";
                 cake_def "data_to_word_memoryProof_isRef"] THEN
     MATCH_REDUCE_TAC THEN
     REWRITE_TAC[cake_def "isMutTag";
                 distinctness "data_to_word_memoryProof_tag"]) in
   LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC[cake_def "list_to_BlockReps"] THEN
   CASES_ON_NAME "t" THEN MATCH_REDUCE_TAC THEN
   ASM_SIMP_TAC[ALL; not_ref; NOT_CONS_NIL]);;

let list_to_BlockReps_NULL = cake_theorem "list_to_BlockReps_NULL"
  (fun () ->
    `~(xs = []) ==> ~(list_to_BlockReps conf x len xs = [])`)
  (LIST_CASES_TAC ["xs"] THEN REWRITE_TAC[NOT_CONS_NIL] THEN
   ONCE_REWRITE_TAC[cake_def "list_to_BlockReps"] THEN
   LIST_CASES_TAC ["t"] THEN MATCH_REDUCE_TAC THEN
   REWRITE_TAC[NOT_CONS_NIL]);;

(* HOL4 data_to_word_memoryProofScript.sml:2388-2390: a proof *)

let list_to_BlockReps_MEM = cake_theorem "list_to_BlockReps_MEM"
  (fun () ->
    `MEM v (list_to_BlockReps conf x len (h :: t)) ==>
       MEM v (list_to_BlockReps conf x (len + 3) t) \/
       v = BlockRep cons_tag
             [h; gc_shared_Pointer (len + 3) (wordLang_Word
               (ptr_bits conf cons_tag 2))] \/
       v = BlockRep cons_tag [h; x]`)
  (ONCE_REWRITE_TAC[cake_def "list_to_BlockReps"] THEN
   LIST_CASES_TAC ["t"] THEN MATCH_REDUCE_TAC THEN
   REWRITE_TAC[MEM] THEN MESON_TAC[]);;

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
  (LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
    [REWRITE_TAC[cake_def "dataSem_list_to_v"] THEN DISCH_TAC THEN
     EXISTS_TAC `t:dataSem_v` THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[cake_def "dataSem_list_to_v"; cake_def "get_refs";
                 MAP; FLAT; APPEND_NIL; MEM_APPEND; MEM] THEN
     STRIP_TAC THEN ASM_MESON_TAC[]]);;

let v_inv_lemma = cake_theorem "v_inv_lemma"
  (fun () ->
    `!ck v refs y x f tf.
       v_inv conf v refs (x,f,tf,ha ++ heap_expand sp ++ hb) ==>
         0 < heap_length hs /\
         heap_length hs <= sp ==>
           v_inv_ck ck conf v refs (x,f,tf,
                              ha ++ hs ++ heap_expand (sp -
                                heap_length hs) ++ hb)`)
  (* the heap grows by the hs that is taken out of its unused
     space, and that is a heap_store_rel: a data element of the old
     heap is in ha or in hb, the unused space holds none, and the
     two middle parts are of a length.  So v_inv_SUBMAP_lemma
     carries the invariant over, with the two maps unchanged *)
  (let hlen_cl = prove
    (`heap_length [] = 0 /\
      (!x xs. heap_length (CONS x xs) =
              el_length x + heap_length xs)`,
     REWRITE_TAC[cake_def "heap_length"; MAP; SUM_DEF; ITLIST]) in
   let hlen_exp = prove
    (`!n. heap_length (heap_expand n) = n`,
     GEN_TAC THEN REWRITE_TAC[cake_def "heap_expand"] THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC[hlen_cl; cake_def "el_length"] THEN
     ASM_ARITH_TAC) in
   (* the unused space holds no data element at all: its one
      element is an Unused, and past it the lookup is of [] *)
   let isde_rws = [cake_def "isSomeDataElement";
                   distinctness "option"; injectivity "option";
                   distinctness "heap_element"] in
   let exp_none = prove
    (`!n m. ~(isSomeDataElement
                (heap_lookup m
                   (heap_expand n:((A,B)heap_element)list)))`,
     REPEAT GEN_TAC THEN REWRITE_TAC[cake_def "heap_expand"] THEN
     COND_CASES_TAC THEN
     REWRITE_TAC(cake_def "heap_lookup" :: cake_def "el_length" ::
                 isde_rws) THEN
     REPEAT COND_CASES_TAC THEN
     REWRITE_TAC(cake_def "heap_lookup" :: isde_rws)) in
   let expand_rel = prove
    (`!ha hs hb sp.
        0 < heap_length hs /\ heap_length hs <= sp
        ==> heap_store_rel (ha ++ heap_expand sp ++ hb)
              (ha ++ hs ++ heap_expand (sp - heap_length hs) ++ hb)`,
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     REWRITE_TAC[cake_def "heap_store_rel"] THEN
     X_GEN_TAC `n:num` THEN
     REWRITE_TAC[GSYM APPEND_ASSOC] THEN
     REWRITE_TAC[cake_thm "heap_lookup_APPEND"; hlen_exp;
                 heap_length_APPEND] THEN
     (* the three parts of the old heap, and of the new one: the
        splits are the same, because the lookup of a data element
        falls in ha or in hb either way *)
     COND_CASES_TAC THEN REWRITE_TAC[exp_none] THEN
     COND_CASES_TAC THEN REWRITE_TAC[exp_none] THEN
     COND_CASES_TAC THENL
      [SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
     COND_CASES_TAC THENL
      [SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
     DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     ASM_ARITH_TAC) in
   REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
   FIRST_ASSUM(fun vi ->
     MATCH_MP_TAC(MATCH_MP (cake_thm "v_inv_SUBMAP_lemma") vi)) THEN
   REWRITE_TAC[SUBMAP_REFL] THEN
   MATCH_MP_TAC expand_rel THEN ASM_REWRITE_TAC[]);;

let data_to_word_memoryProof_v_inv_lemma =
  cake_theorem "v_inv_lemma[allow_rebind]"
  (fun () ->
    `!conf v refs x f tf hs ha hb sp.
      0 < heap_length hs /\
      heap_length hs <= sp /\
      v_inv conf v refs (x,f,tf,ha ++ heap_expand sp ++ hb) ==>
      v_inv conf v refs (x,f,tf,ha ++ hs ++ heap_expand (sp -
        heap_length hs) ++ hb)`)
  (REPEAT STRIP_TAC THEN ASM_MESON_TAC[v_inv_eq; v_inv_lemma]);;

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
  (REWRITE_TAC[LIST_REL_EL_EQN] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC data_to_word_memoryProof_v_inv_lemma THEN
   ASM_SIMP_TAC[]);;

let bind_each_def = cake_define_list
  [`bind_each tf ts (k:num) i 0 = tf`;
   `bind_each tf ts (k:num) i (SUC n) = bind_each tf (ts + 1) (k +
  i) i n |+ (ts,k)`];;

let bind_each_MONO = cake_theorem "bind_each_MONO"
  (fun () ->
    `!n t1 t2 tf k i.
      t1 < t2 /\ (!t. t IN FDOM tf ==> t < t1) ==> ~(t1 IN FDOM
        (bind_each tf t2 k i n))`)
  (INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   REWRITE_TAC[cake_def "bind_each"] THENL
    [ASM_MESON_TAC[LT_REFL];
     REWRITE_TAC[FDOM_FUPDATE; IN_INSERT; DE_MORGAN_THM] THEN
     CONJ_TAC THENL
      [ASM_ARITH_TAC;
       FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
        [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]]]);;

let bind_each_SUBMAP = cake_theorem "bind_each_SUBMAP"
  (fun () ->
    `!n tf ts k i.
      (!t. t IN FDOM tf ==> t < ts) ==> tf SUBMAP bind_each tf ts
        k i n`)
  (* every binding of tf is below ts and bind_each adds none below
     it, so what it adds is on top of tf *)
  (INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[cake_def "bind_each"] THENL
    [MATCH_ACCEPT_TAC SUBMAP_REFL;
     REWRITE_TAC[SUBMAP; FDOM_FUPDATE; IN_INSERT;
                 FAPPLY_FUPDATE_THM] THEN
     GEN_TAC THEN DISCH_TAC THEN
     SUBGOAL_THEN `~((x:num) = ts)` ASSUME_TAC THENL
      [FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `x:num` th)) THEN
       ASM_REWRITE_TAC[] THEN ARITH_TAC;
       ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(fun ih ->
       MP_TAC(SPECL [`tf:(num,num)fmap`; `ts + 1`; `k + i`; `i:num`]
                    ih)) THEN
     ANTS_TAC THENL
      [GEN_TAC THEN DISCH_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `t:num`) THEN
       ASM_REWRITE_TAC[] THEN ARITH_TAC;
       REWRITE_TAC[SUBMAP] THEN
       DISCH_THEN(fun th -> MP_TAC(SPEC `x:num` th)) THEN
       ASM_REWRITE_TAC[]]]);;

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
  (* the timestamps of a Block on the stack are its own timestamp
     and the ones of its payload, which the payload in front of the
     stack has; the set that the refs contribute is the same on
     both sides, so the proof is about the stack alone *)
  (let (vnil,vsing,vats,vcons) = v_all_vs_clauses () in
   let mems = [vats; MEM; MEM_FLAT; MEM_MAP] in
   let gen = prove
    (`!(s:dataSem_v->bool) ts tag xs stack.
        {t | ?x. (x IN s \/ MEM x (Block ts tag xs :: stack)) /\
                 MEM t (v_all_ts x)} =
        ts INSERT {t | ?x. (x IN s \/ MEM x (xs ++ stack)) /\
                           MEM t (v_all_ts x)}`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM; MEM;
                 MEM_APPEND] THEN
     X_GEN_TAC `t:num` THEN EQ_TAC THENL
      [DISCH_THEN(X_CHOOSE_THEN `y:dataSem_v`
         (CONJUNCTS_THEN2 (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC)
                          ASSUME_TAC)) THENL
        [DISJ2_TAC THEN EXISTS_TAC `y:dataSem_v` THEN
         ASM_REWRITE_TAC[];
         FIRST_X_ASSUM SUBST_ALL_TAC THEN
         FIRST_X_ASSUM(MP_TAC o REWRITE_RULE mems) THEN
         DISCH_THEN(DISJ_CASES_THEN2
           (fun th -> DISJ1_TAC THEN ACCEPT_TAC th)
           (X_CHOOSE_THEN `u:num list`
             (CONJUNCTS_THEN2
                (X_CHOOSE_THEN `z:dataSem_v`
                   (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))
                MP_TAC))) THEN
         ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
         DISJ2_TAC THEN EXISTS_TAC `z:dataSem_v` THEN
         ASM_REWRITE_TAC[];
         DISJ2_TAC THEN EXISTS_TAC `y:dataSem_v` THEN
         ASM_REWRITE_TAC[]];
       DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
         (X_CHOOSE_THEN `y:dataSem_v`
           (CONJUNCTS_THEN2 (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC)
                            ASSUME_TAC))) THENL
        [EXISTS_TAC `Block ts tag xs` THEN
         ASM_REWRITE_TAC[vats; MEM];
         EXISTS_TAC `y:dataSem_v` THEN ASM_REWRITE_TAC[];
         EXISTS_TAC `Block ts tag xs` THEN
         REWRITE_TAC mems THEN DISJ2_TAC THEN
         EXISTS_TAC `v_all_ts (y:dataSem_v)` THEN
         CONJ_TAC THENL
          [EXISTS_TAC `y:dataSem_v` THEN ASM_REWRITE_TAC[];
           ASM_REWRITE_TAC[]];
         EXISTS_TAC `y:dataSem_v` THEN ASM_REWRITE_TAC[]]]) in
   REPEAT GEN_TAC THEN REWRITE_TAC[cake_def "all_ts"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   MATCH_ACCEPT_TAC gen);;

let all_ts_cons_no_block = cake_theorem "all_ts_cons_no_block"
  (fun () ->
    `!refs stack' v.
       (!ts tag xs. ~(v = Block ts tag xs)) ==> all_ts refs (v ::
         stack') = all_ts refs stack'`)
  (* a value that is not a Block has no timestamp in it, so the head
     of the stack adds nothing to the set *)
  (let keep = EXISTS_TAC `x:dataSem_v` THEN ASM_MESON_TAC[] in
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `v_all_ts (v:dataSem_v) = []` ASSUME_TAC THENL
    [CASES_ON_NAME "v" THEN
     GEN_REWRITE_TAC LAND_CONV [cake_def "v_all_ts"] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[cake_def "all_ts"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM; MEM] THEN
   X_GEN_TAC `t:num` THEN EQ_TAC THEN STRIP_TAC THENL
    [keep; ASM_MESON_TAC[MEM]; keep; keep; keep]);;

(* NOT USED *)
let all_ts_in_no_block = cake_theorem "all_ts_in_no_block"
  (fun () ->
    `!refs stack' v t.
       (!ts tag xs. ~(v = Block ts tag xs)) /\
       t IN all_ts refs (v :: stack') ==> t IN all_ts refs stack'`)
  (REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(fun th ->
     ASSUME_TAC(MATCH_MP all_ts_cons_no_block th)) THEN
   ASM_MESON_TAC[]);;

let all_ts_append = cake_theorem "all_ts_append"
  (fun () ->
    `!refs x y. all_ts refs (x ++ y) = all_ts refs x UNION all_ts refs
  y`)
  (REPEAT GEN_TAC THEN REWRITE_TAC[cake_def "all_ts"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; MEM_APPEND] THEN
   MESON_TAC[]);;

let all_ts_head = cake_theorem "all_ts_head"
  (fun () ->
    `!refs x xs. all_ts refs (x :: xs) = all_ts refs [x] UNION all_ts
  refs xs`)
  (REPEAT GEN_TAC THEN REWRITE_TAC[GSYM all_ts_append; APPEND]);;

let v_all_vs_MEM = cake_theorem "v_all_vs_MEM"
  (fun () ->
    `!l ts tag xs.
       MEM (Block ts tag xs) (v_all_vs l) ==> (?x y. v_all_vs l =
         x ++ (Block ts tag xs :: v_all_vs xs) ++ y)`)
  (* the values of a list are the values of its head followed by
     the ones of its tail, and a Block among them is followed by
     the values of its payload: the induction of the type gives
     both halves at once, and what each case does to the two
     pieces of the append is what the three lemmas say *)
  (let (vnil,vsing,vats,vcons) = v_all_vs_clauses () in
   let ext0 = prove
    (`!b:dataSem_v list. ?p q. b = p ++ b ++ q`,
     GEN_TAC THEN EXISTS_TAC `[]:dataSem_v list` THEN
     EXISTS_TAC `[]:dataSem_v list` THEN
     REWRITE_TAC[APPEND; APPEND_NIL]) in
   let extc = prove
    (`!(h:dataSem_v) t b. (?p q. t = p ++ b ++ q)
                          ==> (?p q. CONS h t = p ++ b ++ q)`,
     REPEAT GEN_TAC THEN
     DISCH_THEN(X_CHOOSE_THEN `p:dataSem_v list`
       (X_CHOOSE_THEN `q:dataSem_v list` SUBST1_TAC)) THEN
     EXISTS_TAC `CONS (h:dataSem_v) p` THEN
     EXISTS_TAC `q:dataSem_v list` THEN REWRITE_TAC[APPEND]) in
   let extl = prove
    (`!(s:dataSem_v list) t b. (?p q. t = p ++ b ++ q)
                               ==> (?p q. s ++ t = p ++ b ++ q)`,
     REPEAT GEN_TAC THEN
     DISCH_THEN(X_CHOOSE_THEN `p:dataSem_v list`
       (X_CHOOSE_THEN `q:dataSem_v list` SUBST1_TAC)) THEN
     EXISTS_TAC `s ++ p:dataSem_v list` THEN
     EXISTS_TAC `q:dataSem_v list` THEN
     REWRITE_TAC[GSYM APPEND_ASSOC]) in
   let extr = prove
    (`!(s:dataSem_v list) t b. (?p q. t = p ++ b ++ q)
                               ==> (?p q. t ++ s = p ++ b ++ q)`,
     REPEAT GEN_TAC THEN
     DISCH_THEN(X_CHOOSE_THEN `p:dataSem_v list`
       (X_CHOOSE_THEN `q:dataSem_v list` SUBST1_TAC)) THEN
     EXISTS_TAC `p:dataSem_v list` THEN
     EXISTS_TAC `q ++ s:dataSem_v list` THEN
     REWRITE_TAC[APPEND_ASSOC]) in
   let triv = REPEAT GEN_TAC THEN
     REWRITE_TAC[vsing; MEM; distinctness "dataSem_v"] in
   SUBGOAL_THEN
     `(!x ts tag xs.
         MEM (Block ts tag xs) (v_all_vs [x])
         ==> (?p q. v_all_vs [x] =
                    p ++ (Block ts tag xs :: v_all_vs xs) ++ q)) /\
      (!l ts tag xs.
         MEM (Block ts tag xs) (v_all_vs l)
         ==> (?p q. v_all_vs l =
                    p ++ (Block ts tag xs :: v_all_vs xs) ++ q))`
     (fun th -> MATCH_ACCEPT_TAC(CONJUNCT2 th)) THEN
   MATCH_MP_TAC (dataSem_v_induct ()) THEN REPEAT CONJ_TAC THENL
    [triv; triv;
     REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
     REWRITE_TAC[vsing; MEM; injectivity "dataSem_v"] THEN
     DISCH_THEN(DISJ_CASES_THEN2
       (fun eq -> STRIP_ASSUME_TAC eq THEN ASM_REWRITE_TAC[] THEN
                  MATCH_ACCEPT_TAC ext0)
       (fun m -> FIRST_ASSUM(fun ih ->
                   MATCH_ACCEPT_TAC(MATCH_MP extc (MATCH_MP ih m)))));
     triv; triv;
     REWRITE_TAC[vnil; MEM];
     REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
     ONCE_REWRITE_TAC[vcons] THEN REWRITE_TAC[MEM_APPEND] THEN
     DISCH_THEN(DISJ_CASES_THEN2
       (fun m -> FIRST_ASSUM(fun ih ->
                   MATCH_ACCEPT_TAC(MATCH_MP extr (MATCH_MP ih m))))
       (fun m -> FIRST_ASSUM(fun ih ->
                   MATCH_ACCEPT_TAC(MATCH_MP extl
                     (MATCH_MP ih m)))))]);;

let v_in_all_vs = cake_theorem "v_in_all_vs"
  (fun () ->
    `!x y stack' refs.
       x IN all_vs refs stack' /\ MEM y (v_all_vs [x]) ==> y IN
         all_vs refs stack'`)
  (* a value of a value of what the refs and the stack hold is one
     of them as well: each of the four parts of all_vs is a list
     and the values of a list are transitively closed *)
  (REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM] THEN
   REPEAT GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THEN
   FIRST_ASSUM(fun mx -> FIRST_ASSUM(fun my ->
     ASSUME_TAC(MATCH_MP (snd (v_all_vs_trans_thm ()))
                         (CONJ mx my)))) THEN
   ASM_MESON_TAC[]);;

let v_all_vs_MEM2 = cake_theorem "v_all_vs_MEM2"
  (fun () ->
    `!l ts tag xs.
       MEM (Block ts tag xs) (v_all_vs l) ==> (?x. MEM x l /\ MEM
         (Block ts tag xs) (v_all_vs [x]))`)
  (* the values of v_all_vs (x::xs) are x itself, the values of its
     payload where it is a Block, and the values of v_all_vs xs: the
     first two are the values of v_all_vs [x] and the third is what
     the induction hypothesis is about *)
  (let vav = cake_def "v_all_vs" in
   let vnil = prove
    (`v_all_vs ([]:dataSem_v list) = []`,
     GEN_REWRITE_TAC LAND_CONV [vav] THEN MATCH_REDUCE_TAC THEN
     REWRITE_TAC[]) in
   let vsing = prove
    (`!t tag xs y. MEM y (v_all_vs [Block t tag xs]) <=>
        y = Block t tag xs \/ MEM y (v_all_vs xs)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [vav] THEN
     MATCH_REDUCE_TAC THEN
     REWRITE_TAC[vnil; APPEND_NIL; MEM; MEM_APPEND]) in
   LIST_INDUCT_TAC THENL
    [REWRITE_TAC[vnil; MEM];
     REPEAT GEN_TAC THEN CASES_ON_NAME "h" THEN
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [vav] THEN
     MATCH_REDUCE_TAC THEN
     REWRITE_TAC[MEM; MEM_APPEND; distinctness "dataSem_v"] THEN
     ASM_MESON_TAC[vsing]]);;

let v_all_vs_ts = cake_theorem "v_all_vs_ts"
  (fun () ->
    `!x ts tag xs. MEM (Block ts tag xs) (v_all_vs [x]) ==> MEM ts
  (v_all_ts x)`)
  (* induction on the value and on a list of values at once, which
     is what define_datatype gives for a type that nests a list of
     itself: the timestamp of a Block among the values of a value is
     one of the timestamps of that value *)
  (let (vnil,vsing,vats,vcons) = v_all_vs_clauses () in
   let triv = REPEAT GEN_TAC THEN
     REWRITE_TAC[vsing; MEM; distinctness "dataSem_v"] in
   SUBGOAL_THEN
     `(!x ts tag xs.
         MEM (Block ts tag xs) (v_all_vs [x]) ==> MEM ts (v_all_ts x))
      /\
      (!l ts tag xs.
         MEM (Block ts tag xs) (v_all_vs l)
         ==> MEM ts (FLAT (MAP v_all_ts l)))`
     (fun th -> MATCH_ACCEPT_TAC(CONJUNCT1 th)) THEN
   MATCH_MP_TAC dataSem_v_INDUCT THEN REPEAT CONJ_TAC THENL
    [triv; triv;
     REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
     REWRITE_TAC[vsing; vats; MEM; injectivity "dataSem_v"] THEN
     ASM_MESON_TAC[];
     triv; triv;
     REWRITE_TAC[vnil; MEM];
     REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
     ONCE_REWRITE_TAC[vcons] THEN
     REWRITE_TAC[MEM_APPEND; MAP; FLAT] THEN
     ASM_MESON_TAC[]]);;

let MEM_v_all_vs = cake_theorem "MEM_v_all_vs"
  (fun () ->
    `!l v. MEM v l ==> MEM v (v_all_vs l)`)
  (let vav = cake_def "v_all_vs" in
   LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN GEN_TAC THEN
   CASES_ON_NAME "h" THEN
   GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [vav] THEN
   MATCH_REDUCE_TAC THEN
   REWRITE_TAC[MEM_APPEND; MEM] THEN ASM_MESON_TAC[]);;

let MEM_stack_all_vs = cake_theorem "MEM_stack_all_vs"
  (fun () ->
    `!v stack' refs. MEM v stack' ==> v IN all_vs refs stack'`)
  (REPEAT STRIP_TAC THEN
   REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM] THEN
   REPEAT DISJ2_TAC THEN MATCH_MP_TAC MEM_v_all_vs THEN
   ASM_REWRITE_TAC[]);;

let v_all_vs_ts_MEM = cake_theorem "v_all_vs_ts_MEM"
  (fun () ->
    `!x y ts. MEM ts (v_all_ts x) /\ MEM x (v_all_vs [y]) ==> MEM ts
  (v_all_ts y)`)
  (* the induction that ml/lib/tactics.ml does for the proofs that
     need this before the file states it *)
  (let (c1,_) = v_all_vs_ts_thm () in
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_ASSUM(fun a2 -> FIRST_ASSUM(fun a1 ->
     MATCH_ACCEPT_TAC(MATCH_MP c1 (CONJ a1 a2)))));;

let v_all_vs_trans = cake_theorem "v_all_vs_trans"
  (fun () ->
    `!x y z. MEM y (v_all_vs x) /\ MEM z (v_all_vs [y]) ==> MEM z
  (v_all_vs x)`)
  (* the induction that ml/lib/tactics.ml does for the proofs that
     need this before the file states it *)
  (MATCH_ACCEPT_TAC (snd (v_all_vs_trans_thm ())));;

let MEM_in_all_ts = cake_theorem "MEM_in_all_ts"
  (fun () ->
    `!x ts stack' refs.
       x IN all_vs refs stack' /\ MEM ts (v_all_ts x) ==> ts IN
         all_ts refs stack'`)
  (* only a Block has a timestamp, and a Block among the values of
     what the refs and the stack hold is among the values of one of
     the values that a ref holds or of one on the stack, whose
     timestamps are therefore timestamps of the stack *)
  (let (c1,_) = v_all_vs_ts_thm () in
   let (vnil,vsing,vats,vcons) = v_all_vs_clauses () in
   let fr = prove
    (`(!l x. find_ref (bvlSem_ValueArray l) x <=> MEM x l) /\
      (!m v x. find_ref (Thunk m v) x <=> (v = x)) /\
      (!tg fin l c r x. find_ref (bvlSem_MutBlock tg fin l c r) x <=>
         MEM x (l ++ [c] ++ r))`,
     REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [cake_def "find_ref"] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `?t tag l. (x:dataSem_v) = Block t tag l`
     STRIP_ASSUME_TAC THENL
    [CASES_ON_NAME "x" THEN
     RULE_ASSUM_TAC(REWRITE_RULE[vats; MEM]) THEN
     TRY(FIRST_ASSUM CONTR_TAC) THEN MESON_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[cake_def "all_vs"; IN_UNION;
                               IN_ELIM_THM]) THEN
   REWRITE_TAC[cake_def "all_ts"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[IN_ELIM_THM] THEN
   ASM_MESON_TAC[v_all_vs_MEM2; c1; fr; MEM_APPEND]);;

let MEM_in_all_vs = cake_theorem "MEM_in_all_vs"
  (fun () ->
    `!x y refs stack'. x IN all_vs refs stack' /\ MEM y (v_all_vs [x])
  ==> y IN all_vs refs stack'`)
  (REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM] THEN
   REPEAT STRIP_TAC THEN ASM_MESON_TAC[v_all_vs_trans]);;

(* NOT USED *)
let v_all_vs_ts_list = cake_theorem "v_all_vs_ts_list"
  (fun () ->
    `!x y ts. MEM x (v_all_vs y) /\ MEM ts (v_all_ts x) ==> MEM ts
  (FLAT (MAP v_all_ts y))`)
  (* the other half of that induction: the timestamps of a value
     among the values of a list are timestamps of the list *)
  (let (_,c2) = v_all_vs_ts_thm () in
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_ASSUM(fun a2 -> FIRST_ASSUM(fun a1 ->
     MATCH_ACCEPT_TAC(MATCH_MP c2 (CONJ a1 a2)))));;

let v_inv_tf_update_thm_lemma = cake_theorem "v_inv_tf_update_thm_lemma"
  (fun () ->
    `!ck v refs y f tf heap ts' a.
       v_inv conf v refs (y,f,tf,heap) /\ ~(ts' IN FDOM tf) ==>
         v_inv_ck ck conf v refs (y,f,tf |+ (ts',a),heap)`)
  (* the same complete induction as v_inv_SUBMAP_lemma, but only the
     map of the timestamps changes and by an update at a timestamp
     that is not in its domain: a Block of the invariant has its
     timestamp in that domain, so its lookup is the one it was *)
  (let (vr,_,_) = v_inv_ck in
   let rl = CONJUNCTS vr in
   let vdef = cake_thm "v_inv_def" in
   let NOT_VAR_TAC =
     FIRST_ASSUM(fun nb ->
       if is_neg(concl nb) && is_var(rand(concl nb))
       then SUBST_ALL_TAC(EQF_INTRO nb) else fail()) in
   let FLU_TAC =
     ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN COND_CASES_TAC THEN
     ASM_REWRITE_TAC[] THEN
     FIRST_ASSUM(fun fl -> MP_TAC(MATCH_MP FLOOKUP_IN_FDOM fl)) THEN
     ASM_REWRITE_TAC[] in
   let lt1 = ARITH_RULE `~(ck = 0) ==> ck - 1 < ck` in
   let setup =
     MATCH_MP_TAC num_WF THEN X_GEN_TAC `ck:num` THEN DISCH_TAC THEN
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     CASES_ON_NAME "v" THEN USE_CHANGED [vdef] in
   setup THENL
    [COND_CASES_TAC THEN STRIP_TAC THEN SUBST_LHS_TAC THENL
      [MATCH_MP_TAC(el 0 rl) THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC(el 1 rl) THEN ASM_REWRITE_TAC[]];
     STRIP_TAC THEN REPEAT SUBST_LHS_TAC THEN
     MATCH_MP_TAC(el 2 rl) THEN ASM_REWRITE_TAC[];
     COND_CASES_TAC THEN STRIP_TAC THEN REPEAT SUBST_LHS_TAC THENL
      [MATCH_MP_TAC(el 7 rl) THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC(el 8 rl) THEN REPEAT CONJ_TAC THENL
        [FIRST_ASSUM MATCH_ACCEPT_TAC;
         DISCH_TAC THEN
         FIRST_ASSUM(fun a2th ->
           if can (term_match [] `EVERY2 (p:A->B->bool) l m`)
                  (concl a2th)
           then MP_TAC a2th else fail()) THEN
         MATCH_MP_TAC MONO_ALL2 THEN BETA_TAC THEN
         REPEAT STRIP_TAC THEN CK_IH_TAC;
         FLU_TAC;
         FIRST_ASSUM MATCH_ACCEPT_TAC]];
     STRIP_TAC THEN REPEAT SUBST_LHS_TAC THEN
     MATCH_ACCEPT_TAC(el 3 rl);
     DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC
       (DISJ_CASES_THEN2 STRIP_ASSUME_TAC STRIP_ASSUME_TAC)) THENL
      [REPEAT SUBST_LHS_TAC THEN MATCH_MP_TAC(el 4 rl) THEN
       REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN
       ASM_REWRITE_TAC[];
       NOT_VAR_TAC THEN
       FIRST_ASSUM(fun ih ->
         ASM_MESON_TAC[el 5 rl; SPEC `ck - 1` ih; lt1]);
       NOT_VAR_TAC THEN
       FIRST_ASSUM(fun ih ->
         ASM_MESON_TAC[el 6 rl; SPEC `ck - 1` ih; lt1])]]);;

let v_inv_tf_update_thm = cake_theorem "v_inv_tf_update_thm"
  (fun () ->
    `!conf v refs y f tf heap ts' a.
       v_inv conf v refs (y,f,tf,heap) /\ ~(ts' IN FDOM tf) ==>
       v_inv conf v refs (y,f,tf |+ (ts',a),heap)`)
  (REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[v_inv_eq; v_inv_tf_update_thm_lemma]);;

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
  (REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[v_inv_eq; v_inv_tf_update_thm_alt_lemma]);;

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
  (REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[v_inv_eq; v_inv_tf_update_lemma]);;

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
  (REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[v_inv_eq; v_inv_tf_restrict_lemma]);;

let v_all_vs_append = cake_theorem "v_all_vs_append"
  (fun () ->
    `!x y. v_all_vs (x ++ y) = v_all_vs x ++ v_all_vs y`)
  (let vav = cake_def "v_all_vs" in
   let vnil = prove
    (`v_all_vs ([]:dataSem_v list) = []`,
     GEN_REWRITE_TAC LAND_CONV [vav] THEN MATCH_REDUCE_TAC THEN
     REWRITE_TAC[]) in
   LIST_INDUCT_TAC THENL
    [REWRITE_TAC[APPEND; vnil];
     GEN_TAC THEN REWRITE_TAC[APPEND] THEN CASES_ON_NAME "h" THEN
     GEN_REWRITE_TAC LAND_CONV [vav] THEN MATCH_REDUCE_TAC THEN
     GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [vav] THEN
     MATCH_REDUCE_TAC THEN
     ASM_REWRITE_TAC[APPEND; GSYM APPEND_ASSOC]]);;

let MEM_v_all_vs_split = cake_theorem "MEM_v_all_vs_split"
  (fun () ->
    `!x v xs. MEM x (v_all_vs (v :: xs)) ==> MEM x (v_all_vs [v]) \/
  MEM x (v_all_vs xs)`)
  (let cons_app = prove
    (`!(h:dataSem_v) t. CONS h t = APPEND [h] t`,
     REWRITE_TAC[APPEND]) in
   REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [cons_app] THEN
   REWRITE_TAC[v_all_vs_append; MEM_APPEND]);;

let MEM_v_all_vs_split2 = cake_theorem "MEM_v_all_vs_split2"
  (fun () ->
    `MEM x (v_all_vs (v :: y :: xs)) ==>
       MEM x (v_all_vs (v :: xs)) \/ MEM x (v_all_vs [y])`)
  (* v_all_vs of a cons splits into the values of the head and the
     values of the tail (v_all_vs_append, as the source has it), and
     the three parts of v :: y :: xs go where they belong *)
  (let cons_app = prove
    (`!(h:dataSem_v) t. CONS h t = APPEND [h] t`,
     REWRITE_TAC[APPEND]) in
   let vcons = prove
    (`!(v:dataSem_v) xs y. MEM y (v_all_vs (CONS v xs)) <=>
        MEM y (v_all_vs [v]) \/ MEM y (v_all_vs xs)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
       [cons_app] THEN
     REWRITE_TAC[v_all_vs_append; MEM_APPEND]) in
   MESON_TAC[vcons]);;

let MEM_v_all_vs_extend_tl = cake_theorem "MEM_v_all_vs_extend_tl"
  (fun () ->
    `!x v xs. MEM x (v_all_vs [v]) ==> MEM x (v_all_vs (v :: xs))`)
  (let cons_app = prove
    (`!(h:dataSem_v) t. CONS h t = APPEND [h] t`,
     REWRITE_TAC[APPEND]) in
   REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [cons_app] THEN
   REWRITE_TAC[v_all_vs_append; MEM_APPEND] THEN CONV_TAC TAUT);;

let MEM_v_all_vs_extend_hd = cake_theorem "MEM_v_all_vs_extend_hd"
  (fun () ->
    `!x v xs. MEM x (v_all_vs xs) ==> MEM x (v_all_vs (v :: xs))`)
  (let cons_app = prove
    (`!(h:dataSem_v) t. CONS h t = APPEND [h] t`,
     REWRITE_TAC[APPEND]) in
   REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [cons_app] THEN
   REWRITE_TAC[v_all_vs_append; MEM_APPEND] THEN CONV_TAC TAUT);;

let MEM_v_all_vs_extend_append =
  cake_theorem "MEM_v_all_vs_extend_append"
  (fun () ->
    `MEM x (v_all_vs xs) ==> MEM x (v_all_vs (xs ++ ys))`)
  (REWRITE_TAC[v_all_vs_append; MEM_APPEND] THEN CONV_TAC TAUT);;

let MEM_v_all_vs_EL = cake_theorem "MEM_v_all_vs_EL"
  (fun () ->
    `!xs i x.
       i < LENGTH xs /\
       MEM x (v_all_vs [EL i xs]) ==>
         MEM x (v_all_vs xs)`)
  (LIST_INDUCT_TAC THENL
    [REWRITE_TAC[LENGTH; LT];
     GEN_TAC THEN STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
     REWRITE_TAC[EL; HD; TL; LENGTH; LT_SUC; LT_0] THEN
     ASM_MESON_TAC[MEM_v_all_vs_extend_hd; MEM_v_all_vs_extend_tl]]);;

let MEM_v_all_vs_LUPDATE = cake_theorem "MEM_v_all_vs_LUPDATE"
  (fun () ->
    `!xs i v x.
       MEM x (v_all_vs (LUPDATE v i xs)) ==>
         MEM x (v_all_vs [v]) \/ MEM x (v_all_vs xs)`)
  (* the LUPDATE puts v where the index says and leaves the rest,
     so a value of the result is one of v or one of the list *)
  (let vnil = prove
    (`v_all_vs ([]:dataSem_v list) = []`,
     GEN_REWRITE_TAC LAND_CONV [cake_def "v_all_vs"] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   LIST_INDUCT_TAC THEN REWRITE_TAC[LUPDATE] THENL
    [REWRITE_TAC[vnil; MEM];
     REPEAT GEN_TAC THEN COND_CASES_TAC THEN
     DISCH_THEN(fun th -> MP_TAC(MATCH_MP MEM_v_all_vs_split th)) THEN
     STRIP_TAC THEN
     FIRST [DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
            DISJ2_TAC THEN MATCH_MP_TAC MEM_v_all_vs_extend_hd THEN
            FIRST_ASSUM ACCEPT_TAC;
            DISJ2_TAC THEN MATCH_MP_TAC MEM_v_all_vs_extend_tl THEN
            FIRST_ASSUM ACCEPT_TAC;
            FIRST_ASSUM(fun ih -> MP_TAC(SPECL
              [`i - 1`; `v:dataSem_v`; `x:dataSem_v`] ih)) THEN
            ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
            MATCH_MP_TAC(TAUT `(b ==> c) ==> (a \/ b ==> a \/ c)`) THEN
            MATCH_ACCEPT_TAC MEM_v_all_vs_extend_hd]]);;

let all_vs_Block = cake_theorem "all_vs_Block"
  (fun () ->
    `all_vs refs ((Block t tag xs:dataSem_v) :: ys) =
     Block t tag xs INSERT all_vs refs (xs ++ ys)`)
  (let vav_block = prove
    (`!t tag xs ys.
        v_all_vs (CONS (Block t tag xs) ys) =
        APPEND (CONS (Block t tag xs) (v_all_vs xs)) (v_all_vs ys)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [cake_def "v_all_vs"] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   REWRITE_TAC[cake_def "all_vs"; v_all_vs_append; vav_block] THEN
   REWRITE_TAC[EXTENSION; IN_INSERT; IN_UNION; IN_ELIM_THM;
               MEM_APPEND; MEM] THEN
   MESON_TAC[]);;

let blocks_unique_cons_thm = cake_theorem "blocks_unique_cons_thm"
  (fun () ->
    `blocks_unique ts s ==>
     blocks_unique (ts + 1) (Block ts tag xs INSERT s)`)
  (* the four cases of the two Blocks: both the new one (the goal is
     then an equation of the arguments), one of them the new one (the
     other has a timestamp below ts, so the two cannot be equal), or
     both in the set (which is what the hypothesis is about).  The
     instance of the hypothesis is written down, because its
     antecedent has to be discharged by the assumptions as they
     stand: rewriting with t = ts first would put the antecedent out
     of reach of them. *)
  (let inst a b c d =
     FIRST_ASSUM(fun h -> MP_TAC(SPECL [`t:num`; a; b; c; d] h)) THEN
     ANTS_TAC THENL
      [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] in
   let a1 = `a1:num` and x1 = `xs1:dataSem_v list`
   and a2 = `a2:num` and x2 = `xs2:dataSem_v list` in
   REWRITE_TAC[cake_def "blocks_unique"; IN_INSERT;
               injectivity "dataSem_v"] THEN
   DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
   FIRST
    [ASM_REWRITE_TAC[] THEN ARITH_TAC;
     inst a1 x1 a2 x2 THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_ARITH_TAC;
     inst a2 x2 a2 x2 THEN STRIP_TAC THEN
     SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC;
     inst a1 x1 a1 x1 THEN STRIP_TAC THEN
     SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC]);;

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
  (* a Block of all_vs refs (Word64 w :: stack) is one of
     all_vs refs (ws ++ stack): the Word64 is no Block, and the rest
     of v_all_vs (Word64 w :: stack) is v_all_vs stack *)
  (let vw64 = prove
    (`!(w:word64) ys. v_all_vs (CONS (Word64 w) ys) =
        CONS (Word64 w) (v_all_vs ys)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [cake_def "v_all_vs"] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   let inc = prove
    (`!refs ws stack' (w:word64) t a xs.
        Block t a xs IN all_vs refs (CONS (Word64 w) stack') ==>
        Block t a xs IN all_vs refs (APPEND ws stack')`,
     REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM; vw64;
                 v_all_vs_append; MEM; MEM_APPEND;
                 distinctness "dataSem_v"] THEN MESON_TAC[]) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN DISCH_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THEN ASM_MESON_TAC[inc]);;

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
  (let vnum = prove
    (`!(i:int) ys. v_all_vs (CONS (Number i) ys) =
        CONS (Number i) (v_all_vs ys)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [cake_def "v_all_vs"] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   let inc = prove
    (`!refs ws stack' (i:int) t a xs.
        Block t a xs IN all_vs refs (CONS (Number i) stack') ==>
        Block t a xs IN all_vs refs (APPEND ws stack')`,
     REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM; vnum;
                 v_all_vs_append; MEM; MEM_APPEND;
                 distinctness "dataSem_v"] THEN MESON_TAC[]) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN DISCH_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THEN ASM_MESON_TAC[inc]);;

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
  (REWRITE_TAC[cake_def "ref_edge"; lookup_insert] THEN
   COND_CASES_TAC THEN REWRITE_TAC[] THEN MATCH_REDUCE_TAC THEN
   REWRITE_TAC[]);;

let ref_edge_Thunk = cake_theorem "ref_edge_Thunk[local]"
  (fun () ->
    `ref_edge (insert ptr (Thunk ev v) refs) x y =
       (if x = ptr then MEM y (get_refs (Block 0 ARB [v])) else
         ref_edge refs x y)`)
  (REWRITE_TAC[cake_def "ref_edge"; lookup_insert] THEN
   COND_CASES_TAC THEN REWRITE_TAC[] THEN MATCH_REDUCE_TAC THEN
   REWRITE_TAC[]);;

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
  (REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[v_inv_eq; v_inv_ByteArray_insert_lemma]);;

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
  (* heap_store_lemma stores at the length of the prefix, and the
     condition it leaves is that the two RefBlocks are of a length *)
  (let hlen_cl = prove
    (`heap_length [] = 0 /\
      (!x xs. heap_length (CONS x xs) = el_length x + heap_length xs)`,
     REWRITE_TAC[cake_def "heap_length"; MAP; SUM_DEF; ITLIST]) in
   GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[heap_store_lemma; APPEND; PAIR_EQ; hlen_cl;
               cake_def "RefBlock"; cake_def "el_length"] THEN
   ASM_ARITH_TAC);;

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
  (* the lookup in the append is the one in ha or the one in the
     RefBlock and what follows it, and a RefBlock is LENGTH y + 1
     long *)
  (REWRITE_TAC[data_to_word_memoryProof_heap_lookup_APPEND;
               cake_def "heap_lookup"; cake_def "RefBlock";
               cake_def "el_length"] THEN
   REPEAT COND_CASES_TAC THEN
   ASM_REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
   TRY(POP_ASSUM_LIST(fun ths ->
     MP_TAC(end_itlist CONJ (rev ths))) THEN ARITH_TAC) THEN
   TRY(MATCH_ACCEPT_TAC EQ_SYM_EQ) THEN
   REWRITE_TAC[]);;

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
  (* the tag of a RefBlock is RefTag, and the three shapes have
     another one; the conditional of Word64Rep is split after the
     first rewrite, so the injectivity is used again under it *)
  (let rws = [injectivity "heap_element"; PAIR_EQ;
              distinctness "data_to_word_memoryProof_tag"] in
   REWRITE_TAC[cake_def "isRefBlock"; cake_def "RefBlock";
               cake_def "Bignum"; cake_raw "Word64Rep"] THEN
   PAIRARG_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC rws THEN
   REPEAT CONJ_TAC THEN TRY COND_CASES_TAC THEN
   REWRITE_TAC rws);;

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
  (* v_inv_Ref_lemma says that the clocked relation does not see the
     difference between the two heaps, of a value that the relation
     holds of; the unclocked one is the clocked one at every clock,
     so each side gives the other.  The lemma's heap2 is a free
     variable, so the other direction is the lemma with the two
     heaps exchanged, and RefBlock_inv is symmetric *)
  (let lem = cake_thm "v_inv_Ref_lemma" in
   let hp = find_term (fun t -> is_var t && fst(dest_var t) = "heap")
              (concl lem) in
   let hp2 = find_term
               (fun t -> is_var t && fst(dest_var t) = "heap2")
               (concl lem) in
   let swapped = INST [hp2,hp; hp,hp2] lem in
   let sym_rb = prove
    (`!h1 h2. RefBlock_inv h1 h2 ==> RefBlock_inv h2 h1`,
     REWRITE_TAC[cake_def "RefBlock_inv"] THEN MESON_TAC[]) in
   let step lemm rbt =
     ONCE_REWRITE_TAC[v_inv_eq] THEN
     FIRST_ASSUM(fun rb -> FIRST_ASSUM(fun vi ->
       let th = MATCH_MP lemm (CONJ vi (rbt rb)) in
       let ckv = find_term
                   (fun t -> is_var t && fst(dest_var t) = "ck")
                   (concl th) in
       MP_TAC(GEN ckv th))) THEN
     DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
     FIRST_ASSUM(fun vi -> ACCEPT_TAC(REWRITE_RULE[v_inv_eq] vi)) in
   DISCH_TAC THEN REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
    [step swapped (MATCH_MP sym_rb);
     step lem (fun th -> th)]);;

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
  (REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[v_inv_eq; v_inv_ValueArray_insert_lemma;
                 v_inv_Ref]);;

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
  (REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[v_inv_eq; v_inv_MutBlock_insert_lemma]);;

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
  (REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[v_inv_eq; v_inv_MutBlock_fin_lemma]);;

(* ---- MutCons: the Cons allocation, but the value handed back is a fresh ref *)

let all_ts_SUBSET_gen = cake_theorem "all_ts_SUBSET_gen[local]"
  (fun () ->
    `(!x. ((?n r'. lookup n refs1 = SOME r' /\ find_ref r' x) \/ MEM x
  stack1) ==>
          ((?n r'. lookup n refs2 = SOME r' /\ find_ref r' x) \/
            MEM x stack2)) ==>
     all_ts refs1 stack1 SUBSET all_ts refs2 stack2`)
  (REWRITE_TAC[cake_def "all_ts"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

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
  (REWRITE_TAC[cake_def "all_ts"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let all_ts_mutcons = cake_theorem "all_ts_mutcons[local]"
  (fun () ->
    `~(ptr IN domain refs) ==>
       all_ts refs ((l ++ [c] ++ r) ++ stack) SUBSET
       all_ts (insert ptr (bvlSem_MutBlock tag F l c r) refs)
         (RefPtr F ptr :: stack)`)
  (* every value that the old refs and stack reach is reached by the
     new ones: one of the refs is not the fresh pointer, because the
     fresh one has no value in refs at all, and the three parts of
     the MutBlock are what find_ref gives of it *)
  (let fr = prove
    (`!tg fin l c r x.
        find_ref (bvlSem_MutBlock tg fin l c r) x <=>
        MEM x l \/ x = c \/ MEM x r`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [cake_def "find_ref"] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[MEM_APPEND; MEM]) in
   let li = prove
    (`!k1 k2 v (t:(A)spt) y.
        (sptree_lookup k1 (sptree_insert k2 v t) = SOME y) <=>
        (k1 = k2 /\ v = y) \/
        (~(k1 = k2) /\ sptree_lookup k1 t = SOME y)`,
     REPEAT GEN_TAC THEN REWRITE_TAC[lookup_insert] THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC[injectivity "option"] THEN
     CONV_TAC TAUT) in
   DISCH_THEN(fun hyp ->
     MATCH_MP_TAC all_ts_SUBSET_gen THEN GEN_TAC THEN
     REWRITE_TAC[MEM_APPEND; MEM; li] THEN
     MESON_TAC[fr; REWRITE_RULE[GSYM lookup_NONE_domain] hyp;
               distinctness "option"]));;

let blocks_unique_mutcons = cake_theorem "blocks_unique_mutcons[local]"
  (fun () ->
    `blocks_unique ts (all_vs refs ((l ++ [c] ++ r) ++ stack)) ==>
     blocks_unique ts
       (all_vs (insert ptr (bvlSem_MutBlock tag F l c r) refs)
         (RefPtr F ptr :: stack))`)
  (* a Block of the new refs and stack is one of the old ones: the
     MutBlock at the fresh pointer holds the values that the old
     stack has in front of it, and the RefPtr is no Block *)
  (let vrefptr = prove
    (`!b p ys. v_all_vs (CONS (RefPtr b p) ys) =
        CONS (RefPtr b p) (v_all_vs ys)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [cake_def "v_all_vs"] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   let li = prove
    (`!k1 k2 v (t:(A)spt) y.
        (sptree_lookup k1 (sptree_insert k2 v t) = SOME y) <=>
        (k1 = k2 /\ v = y) \/
        (~(k1 = k2) /\ sptree_lookup k1 t = SOME y)`,
     REPEAT GEN_TAC THEN REWRITE_TAC[lookup_insert] THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC[injectivity "option"] THEN CONV_TAC TAUT) in
   let inc = prove
    (`!refs ptr tag l c r stack' t a xs.
        Block t a xs IN
          all_vs (insert ptr (bvlSem_MutBlock tag F l c r) refs)
                 (CONS (RefPtr F ptr) stack') ==>
        Block t a xs IN
          all_vs refs (APPEND (APPEND l (APPEND [c] r)) stack')`,
     REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM; vrefptr;
                 v_all_vs_append; MEM; MEM_APPEND; li;
                 distinctness "dataSem_v"; distinctness "bvlSem_ref";
                 injectivity "bvlSem_ref"] THEN MESON_TAC[]) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN DISCH_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THEN ASM_MESON_TAC[inc]);;

let ref_edge_MutBlock = cake_theorem "ref_edge_MutBlock[local]"
  (fun () ->
    `ref_edge (insert ptr (bvlSem_MutBlock tag fin l c r) refs) x y =
       (if x = ptr then MEM y (get_refs (Block 0 ARB (l ++ [c] ++
         r))) else ref_edge refs x y)`)
  (REWRITE_TAC[cake_def "ref_edge"; lookup_insert] THEN
   COND_CASES_TAC THEN REWRITE_TAC[] THEN MATCH_REDUCE_TAC THEN
   REWRITE_TAC[]);;

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
  (* induction along the reflexive transitive closure: an edge of
     the new refs is one of the old ones, or it leaves ptr and
     lands in the payload of the MutBlock *)
  (MATCH_MP_TAC RTC_INDUCT THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN DISJ1_TAC THEN
    MATCH_ACCEPT_TAC(CONJUNCT1(SPEC_ALL RTC_RULES));
    REPEAT GEN_TAC THEN
    REWRITE_TAC[ref_edge_MutBlock] THEN
    COND_CASES_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    ASM_MESON_TAC[RTC_RULES]]);;

let reachable_refs_MutCons =
  cake_theorem "reachable_refs_MutCons[local]"
  (fun () ->
    `reachable_refs (RefPtr F ptr :: stack)
       (insert ptr (bvlSem_MutBlock tag F l c r) refs) n /\ ~(n =
         ptr) /\ ~(ptr IN domain refs) ==>
     reachable_refs ((l ++ [c] ++ r) ++ stack) refs n`)
  (* reachable_refs_MutCons_lemma says of a path through the new
     references that it is one of the old ones or that it starts
     inside the payload of the MutBlock.  A root of the stack keeps
     its path; the only other root is the pointer to the MutBlock,
     whose path cannot start at all, because ptr is fresh and so has
     no edge; and a path from the payload has its root among the
     payload's values *)
  (
   let mem_block_refs = prove
    (`!(ys:(dataSem_v)list) ss tt aa.
        MEM ss (get_refs (Block tt aa ys))
        ==> ?yy. MEM yy ys /\ MEM ss (get_refs yy)`,
     REWRITE_TAC[cake_def "get_refs"; MEM_FLAT; MEM_MAP] THEN
     MESON_TAC[]) in
   let subst_vars =
     REPEAT(FIRST_X_ASSUM(fun th ->
       if is_eq(concl th) && is_var(lhand(concl th))
       then SUBST_ALL_TAC th else fail())) in
   let payload b =
     X_CHOOSE_THEN `ss:num` (CONJUNCTS_THEN2
       (fun m -> MP_TAC(MATCH_MP mem_block_refs m)) ASSUME_TAC) b THEN
     DISCH_THEN(X_CHOOSE_THEN `yy:dataSem_v` STRIP_ASSUME_TAC) THEN
     MAP_EVERY EXISTS_TAC [`yy:dataSem_v`; `ss:num`] THEN
     ASM_REWRITE_TAC[MEM_APPEND] in
   let noedge a =
     MP_TAC(ONCE_REWRITE_RULE[RTC_CASES] a) THEN
     FIRST_ASSUM(fun nd ->
       let th = REWRITE_RULE[GSYM lookup_NONE_domain] nd in
       if concl th = concl nd then fail()
       else REWRITE_TAC[cake_def "ref_edge"; th]) THEN
     MATCH_REDUCE_TAC THEN ASM_REWRITE_TAC[] in
   let stackcase a =
     ASSUME_TAC a THEN
     W(fun gl -> MAP_EVERY (fun n -> EXISTS_TAC (var_by_name n gl))
                   ["x"; "r'"]) THEN
     ASM_REWRITE_TAC[MEM_APPEND] in
   let uselemma =
     FIRST_ASSUM(fun rtc -> FIRST_ASSUM(fun ne ->
       MP_TAC(MATCH_MP (MATCH_MP
         (cake_thm "reachable_refs_MutCons_lemma") rtc) ne))) in
   REWRITE_TAC[cake_def "reachable_refs"; MEM] THEN STRIP_TAC THENL
    [subst_vars THEN
     RULE_ASSUM_TAC(REWRITE_RULE[cake_def "get_refs"; MEM]) THEN
     subst_vars THEN uselemma THEN
     DISCH_THEN(DISJ_CASES_THEN2 noedge payload);
     uselemma THEN DISCH_THEN(DISJ_CASES_THEN2 stackcase payload)]);;

(* lifting a v_inv across the MutCons allocation: refs gains a fresh ref and f
   gains its binding, and the heap only grew *)
let v_inv_MutCons_step = cake_theorem "v_inv_MutCons_step[local]"
  (fun () ->
    `v_inv conf v refs (y,f,tf,heap) /\ ~(ptr IN domain refs) /\
     FDOM f SUBSET domain refs /\ heap_store_rel heap heap2 ==>
       v_inv conf v (insert ptr (bvlSem_MutBlock tag F l c r) refs)
         (y,f |+ (ptr,a),tf,heap2)`)
  (* the point is fresh in the references, so it is not in the
     domain of the map and the map is a SUBMAP of its update there;
     v_inv_MutBlock_insert adds the MutBlock to the references and
     v_inv_SUBMAP takes the relation to the bigger map and the
     bigger heap *)
  (
   let submap_fupd = prove
    (`!(g:(A,B)fmap) k v. ~(k IN FDOM g) ==> g SUBMAP (g |+ (k,v))`,
     REWRITE_TAC[SUBMAP; FDOM_FUPDATE; IN_INSERT;
                 FAPPLY_FUPDATE_THM] THEN MESON_TAC[]) in
   STRIP_TAC THEN
   SUBGOAL_THEN `~(ptr IN FDOM (f:(num,num)fmap))` ASSUME_TAC THENL
    [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
   FIRST_ASSUM(fun nf -> ASSUME_TAC(MATCH_MP submap_fupd nf)) THEN
   FIRST_ASSUM(fun vi -> FIRST_ASSUM(fun nd -> FIRST_ASSUM(fun sub ->
     ASSUME_TAC(MATCH_MP (cake_thm "v_inv_MutBlock_insert")
       (CONJ vi (CONJ nd sub)))))) THEN
   MATCH_MP_TAC (GEN_ALL (cake_thm "v_inv_SUBMAP")) THEN
   W(fun gl -> MAP_EVERY (fun n -> EXISTS_TAC (var_by_name n gl))
                 ["f"; "tf"; "heap"]) THEN
   ASM_REWRITE_TAC[SUBMAP_REFL]);;

let take_el_drop = cake_theorem "take_el_drop[local]"
  (fun () ->
    `!index vals. index < LENGTH vals ==>
       TAKE index vals ++ [EL index vals] ++ DROP (index + 1)
         vals = vals`)
  (* DROP_EL_CONS puts the element and the DROP after it back
     together, and TAKE_DROP puts the two halves back together *)
  (REPEAT STRIP_TAC THEN REWRITE_TAC[APPEND] THEN
   FIRST_ASSUM(fun th ->
     MP_TAC(REWRITE_RULE[ADD1] (MATCH_MP DROP_EL_CONS th))) THEN
   DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[TAKE_DROP]);;

(* a value that is not a thunk cannot become one by adding a fresh ref *)
let dest_thunk_insert_fresh =
  cake_theorem "dest_thunk_insert_fresh[local]"
  (fun () ->
    `~(ptr IN domain refs) /\ dest_thunk v refs = NotThunk ==>
       dest_thunk v (insert ptr x refs) = NotThunk`)
  (* only a RefPtr reads the refs, and at a pointer that the refs
     have no value for the old dest_thunk is BadRef, which the
     assumption says it is not; away from the pointer the lookup is
     the one it was *)
  (let dt_def = cake_def "dataSem_dest_thunk" in
   let dtr = [distinctness "dataSem_dest_thunk_ret";
              injectivity "dataSem_dest_thunk_ret"] in
   let opt_rws = [distinctness "option"; injectivity "option"] in
   STRIP_TAC THEN CASES_ON_NAME "v" THEN
   ONCE_REWRITE_TAC[dt_def] THEN
   RULE_ASSUM_TAC(ONCE_REWRITE_RULE[dt_def]) THEN
   SAFE_MATCH_REDUCE_TAC THEN REWRITE_TAC[] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[GSYM lookup_NONE_domain]) THEN
   REWRITE_TAC[lookup_insert] THEN
   ASM_CASES_TAC `a1:num = ptr` THEN ASM_REWRITE_TAC[] THEN
   EVERY_CASE_TAC THEN ASM_REWRITE_TAC dtr THEN
   REPEAT COND_CASES_TAC THEN
   ASM_MESON_TAC (dtr @ opt_rws));;

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
  (* take_el_drop writes the values as the three parts of the
     MutBlock, which is what mutcons_thm_alt is about, and its
     statement with those three parts in is the goal *)
  (
   STRIP_TAC THEN
   FIRST_ASSUM(fun ix ->
     let eq = REWRITE_RULE[APPEND_ASSOC]
                (MATCH_MP (cake_thm "take_el_drop") ix) in
     W(fun (asl,w) ->
       let hd_is n t = (try fst(dest_const(fst(strip_comb t))) = n
                        with Failure _ -> false) in
       let alt = cake_thm "mutcons_thm_alt" in
       let fv n = find_term
         (fun t -> is_var t && fst(dest_var t) = n) (concl alt) in
       let args = snd(strip_comb
         (find_term (hd_is "bvlSem_MutBlock") w)) in
       let alt = REWRITE_RULE[APPEND_ASSOC; eq]
         (INST [el 2 args, fv "l"; el 3 args, fv "c";
                el 4 args, fv "r"] alt) in
       (* the statement of the theorem and the statement of the goal
          invented type variables of their own, so the one is
          instantiated at the other: with the three parts in, the two
          conclusions are the same term but for those variables *)
       MP_TAC(INSTANTIATE (term_match [] (rand (concl alt)) w) alt))) THEN
   ASM_REWRITE_TAC[] THEN TRY(DISCH_THEN ACCEPT_TAC));;

let heap_store_ThunkBlock_thm = cake_theorem "heap_store_ThunkBlock_thm"
  (fun () ->
    `!ha.
       (heap_store (heap_length ha) [ThunkBlock ev1 v1] (ha ++
         (ThunkBlock ev2 v2 :: hb)) =
       (ha ++ (ThunkBlock ev1 v1 :: hb),T))`)
  (* a ThunkBlock is one element long whatever it holds, so the
     store leaves the lengths to agree *)
  (let hlen_cl = prove
    (`heap_length [] = 0 /\
      (!x xs. heap_length (CONS x xs) = el_length x + heap_length xs)`,
     REWRITE_TAC[cake_def "heap_length"; MAP; SUM_DEF; ITLIST]) in
   GEN_TAC THEN
   REWRITE_TAC[heap_store_lemma; APPEND; PAIR_EQ; hlen_cl;
               cake_def "ThunkBlock"; cake_def "el_length"] THEN
   ARITH_TAC);;

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
  (* and a ThunkBlock is two long *)
  (REWRITE_TAC[data_to_word_memoryProof_heap_lookup_APPEND;
               cake_def "heap_lookup"; cake_def "ThunkBlock";
               cake_def "el_length"] THEN
   REPEAT COND_CASES_TAC THEN
   ASM_REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
   TRY(POP_ASSUM_LIST(fun ths ->
     MP_TAC(end_itlist CONJ (rev ths))) THEN ARITH_TAC) THEN
   TRY(MATCH_ACCEPT_TAC EQ_SYM_EQ) THEN
   REWRITE_TAC[]);;

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
  (REWRITE_TAC[INJ] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

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
  (* the element that a lookup finds is in the half of the split
     that its address falls in: heap_lookup_SPLIT cuts the heap at
     the element, and the split of that append is the one of the
     first part or the one that keeps the element *)
  (let stripconj =
     REPEAT(FIRST_X_ASSUM(fun th ->
       if is_conj (concl th) then STRIP_ASSUME_TAC th else fail())) in
   let aux = prove
    (`!(heap:((A,B)heap_element) list) a b h1 h2 x.
        heap_split a heap = SOME (h1,h2) /\
        heap_lookup b heap = SOME x
        ==> (if b < a then MEM x h1 else MEM x h2)`,
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     FIRST_X_ASSUM(fun th ->
       if (try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
                "heap_lookup"
           with Failure _ -> false)
       then MP_TAC(MATCH_MP (cake_thm "heap_lookup_SPLIT") th)
       else fail()) THEN
     DISCH_THEN(X_CHOOSE_THEN `ha:((A,B)heap_element) list`
       (X_CHOOSE_THEN `hb:((A,B)heap_element) list`
         STRIP_ASSUME_TAC)) THEN
     VAR_EQ_TAC THEN
     FIRST_X_ASSUM(fun th ->
       MP_TAC(ONCE_REWRITE_RULE
         [cake_thm "heap_split_APPEND_if"] th)) THEN
     COND_CASES_TAC THEN
     REWRITE_TAC[cake_def "heap_split"] THEN
     ASM_CASES_TAC
       `a - heap_length (ha:((A,B)heap_element) list) = 0` THEN
     ASM_REWRITE_TAC[] THEN
     ASM_CASES_TAC
       `a - heap_length (ha:((A,B)heap_element) list) <
        el_length (x:(A,B)heap_element)` THEN
     ASM_REWRITE_TAC[distinctness "option"] THEN
     EVERY_CASE_TAC THEN
     REWRITE_TAC[distinctness "option"; injectivity "option";
                 PAIR_EQ] THEN
     STRIP_TAC THEN stripconj THEN VAR_EQ_TAC THEN
     ASM_REWRITE_TAC[MEM_APPEND; MEM] THEN
     TRY(CONV_TAC TAUT) THEN TRY ASM_ARITH_TAC) in
   REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC aux);;

let heap_store_heap_lookup = cake_theorem "heap_store_heap_lookup"
  (fun () ->
    `!heap heap2 a x n.
        heap_store a x heap = (heap2,T) /\ n < a ==>
        heap_lookup n heap = heap_lookup n heap2`)
  (* the store leaves the elements before the address it writes at
     where they are, so the lookup below it gives the same *)
  (LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
    [REWRITE_TAC[cake_def "heap_store"; PAIR_EQ];
     GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV)
       [cake_def "heap_store"] THEN
     COND_CASES_TAC THENL
      [ASM_REWRITE_TAC[ARITH_RULE `((n:num) < 0) <=> F`];
       ALL_TAC] THEN
     COND_CASES_TAC THENL
      [REWRITE_TAC[PAIR_EQ]; ALL_TAC] THEN
     PAIRARG_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[PAIR_EQ] THEN
     DISCH_THEN(CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
          (fun th -> SUBST_ALL_TAC(EQT_INTRO th)))
       ASSUME_TAC) THEN
     ONCE_REWRITE_TAC[cake_def "heap_lookup"] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_EXISTS_TAC THEN
     ASM_REWRITE_TAC[] THEN ARITH_ASM_TAC]);;

let update_ref_gen_state_ok = cake_theorem "update_ref_gen_state_ok"
  (fun () ->
    `heap_store b [RefBlock t1] heap = (heap2,T) /\ a <= b /\
         gen_state_ok a (a + (sp + sp1)) heap gens ==>
         gen_state_ok a (a + (sp + sp1)) heap2 gens`)
  CHEAT_TAC;;

let data_up_to_alt = cake_theorem "data_up_to_alt[local]"
  (fun () ->
    `(data_up_to n [] <=> (n = 0)) /\
     (data_up_to n (x :: xs) <=>
        (if n = 0 then T else
        if n < el_length x \/ ~(isDataElement x) then F else
          data_up_to (n - el_length x) xs))`)
  (let opt = [injectivity "option"; distinctness "option";
              PAIR_EQ] in
   REWRITE_TAC[cake_def "data_up_to"; cake_def "heap_split"] THEN
   CONJ_TAC THEN COND_CASES_TAC THEN
   ASM_REWRITE_TAC(ALL :: opt) THENL
    [CONV_TAC(REDEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[ALL];
     CONV_TAC(REDEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[ALL];
     COND_CASES_TAC THEN ASM_REWRITE_TAC(ALL :: opt) THEN
     EVERY_CASE_TAC THEN ASM_REWRITE_TAC(ALL :: opt) THEN
     CONV_TAC(REDEPTH_CONV UNWIND_CONV) THEN
     ASM_REWRITE_TAC(ALL :: opt) THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[]]);;

let update_thunk_gen_state_ok = cake_theorem "update_thunk_gen_state_ok"
  (fun () ->
    `heap_store b [ThunkBlock ev t1] heap = (heap2,T) /\ a <= b /\
         gen_state_ok a (a + (sp + sp1)) heap gens ==>
         gen_state_ok a (a + (sp + sp1)) heap2 gens`)
  CHEAT_TAC;;

let data_up_to_heap_store = cake_theorem "data_up_to_heap_store"
  (fun () ->
    `!heap a b heap2 y.
        data_up_to a heap /\ heap_store b [y] heap = (heap2,T) /\
        isDataElement y ==> data_up_to a heap2`)
  (* the store of a data element keeps the elements below the
     address it writes at, and writes a data element where it
     writes, so the heap stays data up to the address it was *)
  (let hl1 = prove
    (`!y:(A,B)heap_element. heap_length [y] = el_length y`,
     REWRITE_TAC[cake_def "heap_length"; MAP; SUM_DEF; ITLIST] THEN
     ARITH_TAC) in
   let dac1 = prove
    (`!a (h:(A,B)heap_element) t.
        data_up_to a (CONS h t) /\ ~(a = 0)
        ==> ~(a < el_length h) /\ isDataElement h /\
            data_up_to (a - el_length h) t`,
     REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[data_up_to_alt] THEN
     COND_CASES_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
     COND_CASES_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
     POP_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[]) in
   LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
    [REWRITE_TAC[cake_def "heap_store"; PAIR_EQ];
     GEN_REWRITE_TAC
       (LAND_CONV o RAND_CONV o LAND_CONV o LAND_CONV)
       [cake_def "heap_store"] THEN
     COND_CASES_TAC THENL
      [REWRITE_TAC[PAIR_EQ; APPEND; hl1] THEN
       DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
         (CONJUNCTS_THEN2
            (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC)
            ASSUME_TAC)) THEN
       ONCE_REWRITE_TAC[data_up_to_alt] THEN
       COND_CASES_TAC THEN REWRITE_TAC[] THEN
       FIRST_ASSUM(fun du -> FIRST_ASSUM(fun ne ->
         MP_TAC(MATCH_MP dac1 (CONJ du ne)))) THEN
       ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     COND_CASES_TAC THENL
      [REWRITE_TAC[PAIR_EQ]; ALL_TAC] THEN
     PAIRARG_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[PAIR_EQ] THEN
     DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2
          (CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
             (fun th -> SUBST_ALL_TAC(EQT_INTRO th)))
          ASSUME_TAC)) THEN
     ONCE_REWRITE_TAC[data_up_to_alt] THEN
     COND_CASES_TAC THEN REWRITE_TAC[] THEN
     FIRST_ASSUM(fun du -> FIRST_ASSUM(fun ne ->
       MP_TAC(MATCH_MP dac1 (CONJ du ne)))) THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let blocks_unique_update_ref = cake_theorem "blocks_unique_update_ref"
  (fun () ->
    `blocks_unique ts (all_vs refs (xs ++ (RefPtr b ptr :: stack))) ==>
       blocks_unique ts
         (all_vs (insert ptr (ValueArray xs) refs)
            (xs ++ (RefPtr b ptr :: stack)))`)
  (* the ValueArray that the pointer is given holds the values that
     the stack has in front of it *)
  (let li = prove
    (`!k1 k2 v (t:(A)spt) y.
        (sptree_lookup k1 (sptree_insert k2 v t) = SOME y) <=>
        (k1 = k2 /\ v = y) \/
        (~(k1 = k2) /\ sptree_lookup k1 t = SOME y)`,
     REPEAT GEN_TAC THEN REWRITE_TAC[lookup_insert] THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC[injectivity "option"] THEN CONV_TAC TAUT) in
   let inc = prove
    (`!refs ptr xs b stack' t a q.
        Block t a q IN
          all_vs (insert ptr (ValueArray xs) refs)
                 (APPEND xs (CONS (RefPtr b ptr) stack')) ==>
        Block t a q IN
          all_vs refs (APPEND xs (CONS (RefPtr b ptr) stack'))`,
     REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM;
                 v_all_vs_append; MEM_APPEND; li;
                 distinctness "bvlSem_ref";
                 injectivity "bvlSem_ref"] THEN MESON_TAC[]) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN DISCH_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THEN ASM_MESON_TAC[inc]);;

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
  (* the values of the updated array are the old ones and the head
     of the list, which the stack already holds, so every value of
     the new store is one of the old store, and what was unique
     there stays unique *)
  (let lk_ins = prove
    (`!n p (y:(dataSem_v)bvlSem_ref) rfs z.
        lookup n (insert p y rfs) = SOME z <=>
        (n = p /\ y = z) \/ (~(n = p) /\ lookup n rfs = SOME z)`,
     REPEAT GEN_TAC THEN REWRITE_TAC[lookup_insert] THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
     CONV_TAC TAUT) in
   let hd_cons = prove
    (`!(xs:dataSem_v list). 0 < LENGTH xs
        ==> ?t. xs = CONS (HD xs) t`,
     LIST_INDUCT_TAC THEN
     REWRITE_TAC[LENGTH; LT_REFL; HD; LT_0] THEN
     EXISTS_TAC `t:dataSem_v list` THEN REWRITE_TAC[]) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
   FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP hd_cons th)) THEN
   DISCH_THEN(X_CHOOSE_TAC `tt:dataSem_v list`) THEN
   SUBGOAL_THEN
     `!v. MEM v (v_all_vs (LUPDATE (HD (xs:dataSem_v list)) i xs1))
          ==> MEM v (v_all_vs xs1) \/ MEM v (v_all_vs xs)`
     ASSUME_TAC THENL
    [GEN_TAC THEN DISCH_TAC THEN
     FIRST_ASSUM(fun th ->
       MP_TAC(MATCH_MP (cake_thm "MEM_v_all_vs_LUPDATE") th)) THEN
     DISCH_THEN(DISJ_CASES_THEN2
       (fun hd1 -> DISJ2_TAC THEN
         FIRST_ASSUM(fun xe ->
           if (try fst(dest_var(lhs(concl xe))) = "xs"
               with Failure _ -> false)
           then GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [xe]
           else fail()) THEN
         MATCH_MP_TAC (cake_thm "MEM_v_all_vs_extend_tl") THEN
         ACCEPT_TAC hd1)
       (fun t2 -> DISJ1_TAC THEN ACCEPT_TAC t2));
     ALL_TAC] THEN
   W(fun (asl,w) ->
     let hd_is n t =
       (try fst(dest_const(fst(strip_comb t))) = n
        with Failure _ -> false) in
     let allvs t = hd_is "all_vs" t &&
                   length (snd(strip_comb t)) = 2 in
     let newset = find_term allvs w in
     let oldset = find_term allvs
       (concl (find (fun th -> can (find_term allvs) (concl th))
                 (map snd asl))) in
     let vv = mk_var("v",hd(snd(dest_type(type_of newset)))) in
     let inn a s =
       mk_comb(mk_comb(inst [type_of a,`:A`]
         `(IN):A->(A->bool)->bool`, a), s) in
     SUBGOAL_THEN
       (mk_forall(vv, mk_imp(inn vv newset, inn vv oldset)))
       ASSUME_TAC) THENL
    [GEN_TAC THEN
     REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM; lk_ins;
                 injectivity "bvlSem_ref"; distinctness "bvlSem_ref";
                 v_all_vs_append; MEM_APPEND] THEN
     STRIP_TAC THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC);;

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
  (* the value that the thunk is given is on the stack already *)
  (let li = prove
    (`!k1 k2 v (t:(A)spt) y.
        (sptree_lookup k1 (sptree_insert k2 v t) = SOME y) <=>
        (k1 = k2 /\ v = y) \/
        (~(k1 = k2) /\ sptree_lookup k1 t = SOME y)`,
     REPEAT GEN_TAC THEN REWRITE_TAC[lookup_insert] THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC[injectivity "option"] THEN CONV_TAC TAUT) in
   let vcons = prove
    (`!(v:dataSem_v) xs y. MEM y (v_all_vs (CONS v xs)) <=>
        MEM y (v_all_vs [v]) \/ MEM y (v_all_vs xs)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
       [prove(`!(h:dataSem_v) t. CONS h t = APPEND [h] t`,
              REWRITE_TAC[APPEND])] THEN
     REWRITE_TAC[v_all_vs_append; MEM_APPEND]) in
   let inc = prove
    (`!refs ptr ev h stack' t a q.
        Block t a q IN
          all_vs (insert ptr (Thunk ev h) refs)
                 (CONS h (CONS (RefPtr F ptr) stack')) ==>
        Block t a q IN
          all_vs refs (CONS h (CONS (RefPtr F ptr) stack'))`,
     REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM; li;
                 distinctness "bvlSem_ref";
                 injectivity "bvlSem_ref"] THEN
     MESON_TAC[vcons]) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN DISCH_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THEN ASM_MESON_TAC[inc]);;

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
  (* as the store into a RefBlock above: heap_store_lemma stores at
     the length of the prefix and leaves the lengths to agree *)
  (let hlen_cl = prove
    (`heap_length [] = 0 /\
      (!x xs. heap_length (CONS x xs) = el_length x + heap_length xs)`,
     REWRITE_TAC[cake_def "heap_length"; MAP; SUM_DEF; ITLIST]) in
   GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[heap_store_lemma; APPEND; PAIR_EQ; hlen_cl;
               cake_def "BlockRep"; cake_def "el_length"] THEN
   ASM_ARITH_TAC);;

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
  (* where an address falls in a heap that a BlockRep splits: below
     the first part, at the element itself, or past the element,
     whose el_length is one more than the length of its list *)
  (let pick = W(fun (asl,w) ->
     ASM_CASES_TAC (el 0 (snd(strip_comb (rhs w))))) in
   let contra = SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC in
   pick THENL
    [ASM_SIMP_TAC[cake_thm "LESS_IMP_heap_lookup"];
     ASM_SIMP_TAC[cake_thm "NOT_LESS_IMP_heap_lookup"] THEN
     REWRITE_TAC[cake_def "heap_lookup"; cake_def "BlockRep";
                 cake_def "el_length"] THEN
     pick THENL
      [ASM_REWRITE_TAC[SUB_REFL] THEN
       REWRITE_TAC[injectivity "option"] THEN
       MATCH_ACCEPT_TAC EQ_SYM_EQ;
       ASM_REWRITE_TAC[] THEN pick THEN ASM_REWRITE_TAC[] THENL
        [COND_CASES_TAC THENL [contra; ALL_TAC] THEN
         COND_CASES_TAC THENL [contra; ALL_TAC] THEN
         REWRITE_TAC[];
         COND_CASES_TAC THENL [contra; ALL_TAC] THEN
         COND_CASES_TAC THENL
          [REWRITE_TAC[distinctness "option"]; contra]]]]);;

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
  (REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[v_inv_eq; v_inv_MutBlock_hole_lemma]);;

let blocks_unique_update_mutblock =
  cake_theorem "blocks_unique_update_mutblock[local]"
  (fun () ->
    `lookup ptr refs = SOME (bvlSem_MutBlock tag fin l cv r) /\
     blocks_unique ts (all_vs refs (h :: RefPtr F ptr :: stack))
       ==>
       blocks_unique ts
         (all_vs (insert ptr (bvlSem_MutBlock tag fin l h r) refs)
                 (h :: RefPtr F ptr :: stack))`)
  (* the elements of the updated reference are among the ones of
     the old store, so what was unique there stays unique: the
     block that the update puts in has its head and its tail in
     the elements of the store it replaces *)
  (let cons_app = prove
    (`!(h:dataSem_v) t. CONS h t = APPEND [h] t`,
     REWRITE_TAC[APPEND]) in
   let lk_ins = prove
    (`!n p (y:(dataSem_v)bvlSem_ref) rfs z.
        lookup n (insert p y rfs) = SOME z <=>
        (n = p /\ y = z) \/ (~(n = p) /\ lookup n rfs = SOME z)`,
     REPEAT GEN_TAC THEN REWRITE_TAC[lookup_insert] THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
     CONV_TAC TAUT) in
   let hd_is n t =
     (try fst(dest_const(fst(strip_comb t))) = n
      with Failure _ -> false) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
   W(fun (asl,w) ->
     let gel = el 0 (snd(strip_comb w)) in
     FIRST_ASSUM(fun inm ->
       let c = concl inm in
       if not (hd_is "IN" c) || not (el 0 (snd(strip_comb c)) = gel)
       then fail() else
       FIRST_ASSUM(fun lk ->
         if not (hd_is "=" (concl lk)) then fail() else
         MP_TAC(REWRITE_RULE[cake_def "all_vs"; IN_UNION; IN_ELIM_THM;
                             lk_ins; v_all_vs_append; MEM_APPEND;
                             injectivity "bvlSem_ref";
                             distinctness "bvlSem_ref"]
                  (ONCE_REWRITE_RULE[cons_app] inm)) THEN
         MP_TAC lk THEN
         REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM;
                     v_all_vs_append; MEM_APPEND] THEN
         MESON_TAC[cake_thm "MEM_v_all_vs_extend_tl";
                   cake_thm "MEM_v_all_vs_extend_hd"]))));;

let ref_edge_MutBlock_UPDATE =
  cake_theorem "ref_edge_MutBlock_UPDATE[local]"
  (fun () ->
    `lookup ptr refs = SOME (bvlSem_MutBlock tg fin ll cc rr) /\
     ref_edge (insert ptr (bvlSem_MutBlock tg fin ll h rr) refs) r1
       z /\
     ~(MEM z (get_refs h)) ==> ref_edge refs r1 z`)
  (* the edge of the updated reference is an edge of the old one:
     the payload of the MutBlock differs in the hole only, and the
     element of the hole is not z *)
  (let flat_app = prove
    (`!(l1:((A)list)list) l2.
        FLAT (APPEND l1 l2) = APPEND (FLAT l1) (FLAT l2)`,
     LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC[FLAT; APPEND; APPEND_ASSOC]) in
   let mem_refs = prove
    (`!z ll a rr.
        MEM z (get_refs (Block 0 ARB (APPEND ll (APPEND [a] rr)))) <=>
        MEM z (get_refs (Block 0 ARB ll)) \/ MEM z (get_refs a) \/
        MEM z (get_refs (Block 0 ARB rr))`,
     REWRITE_TAC[cake_def "get_refs"; MAP_APPEND; MAP; flat_app;
                 FLAT; MEM_APPEND; APPEND_NIL]) in
   let swap_refs = prove
    (`!z ll a b rr.
        MEM z (get_refs (Block 0 ARB (APPEND ll (APPEND [a] rr)))) /\
        ~MEM z (get_refs a)
        ==> MEM z (get_refs (Block 0 ARB (APPEND ll
                                           (APPEND [b] rr))))`,
     REWRITE_TAC[mem_refs] THEN MESON_TAC[]) in
   REWRITE_TAC[ref_edge_MutBlock] THEN COND_CASES_TAC THEN
   REPEAT STRIP_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
   SUBGOAL_THEN
     `sptree_lookup r1 (refs:(dataSem_v bvlSem_ref) spt) =
      SOME (bvlSem_MutBlock tg fin ll cc rr)`
     (fun th -> ONCE_REWRITE_TAC[cake_def "ref_edge"] THEN
                REWRITE_TAC[th]) THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
   MATCH_REDUCE_TAC THEN
   FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
     MATCH_ACCEPT_TAC(MATCH_MP swap_refs (CONJ th1 th2)))));;

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
  (LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[cake_def "write_bytes"] THEN
   CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
   ASM_REWRITE_TAC[LENGTH]);;

let LIST_REL_IMP_LIST_REL = cake_theorem "LIST_REL_IMP_LIST_REL[local]"
  (fun () ->
    `!xs ys.
         (!x y. MEM x xs ==> P x y ==> Q x y) ==>
         LIST_REL P xs ys ==> LIST_REL Q xs ys`)
  (let aux = prove
    (`!(P:A->B->bool) Q xs ys.
        (!x y. MEM x xs /\ P x y ==> Q x y) /\ ALL2 P xs ys
        ==> ALL2 Q xs ys`,
     GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
     X_GEN_TAC `ys:B list` THEN
     STRUCT_CASES_TAC(ISPEC `ys:B list` list_CASES_v) THEN
     REWRITE_TAC[ALL2; MEM] THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[]) in
   REPEAT GEN_TAC THEN
   REWRITE_TAC[TAUT `(p ==> q ==> r) <=> (p /\ q ==> r)`] THEN
   MATCH_ACCEPT_TAC aux);;

let v_size_LESS_EQ = cake_theorem "v_size_LESS_EQ[local]"
  (fun () ->
    `!l x. MEM x l ==> dataSem_v_size x <= list_size dataSem_v_size l`)
  (REPEAT STRIP_TAC THEN MATCH_MP_TAC MEM_list_size THEN
   ASM_REWRITE_TAC[]);;

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
  (* the lemma is applied to the assumption and not to the goal:
     where a type variable of the statement stands only in the
     antecedent, MATCH_MP_TAC leaves the lemma's own one there *)
  (REWRITE_TAC[v_inv_eq] THEN REPEAT GEN_TAC THEN
   DISCH_THEN(fun th ->
     GEN_TAC THEN
     MATCH_ACCEPT_TAC(MATCH_MP v_inv_IMP_lemma
       (REWRITE_RULE[GSYM v_inv_eq] th))));;

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
  (* a ByteArray holds no value of the language *)
  (let li = prove
    (`!k1 k2 v (t:(A)spt) y.
        (sptree_lookup k1 (sptree_insert k2 v t) = SOME y) <=>
        (k1 = k2 /\ v = y) \/
        (~(k1 = k2) /\ sptree_lookup k1 t = SOME y)`,
     REPEAT GEN_TAC THEN REWRITE_TAC[lookup_insert] THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC[injectivity "option"] THEN CONV_TAC TAUT) in
   let inc = prove
    (`!refs p fl ys s t a q.
        Block t a q IN all_vs (insert p (ByteArray fl ys) refs) s ==>
        Block t a q IN all_vs refs s`,
     REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM; li;
                 distinctness "bvlSem_ref";
                 injectivity "bvlSem_ref"] THEN MESON_TAC[]) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN DISCH_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THEN ASM_MESON_TAC[inc]);;

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
  (* and the same for the store that keeps the unused space at the
     end *)
  (REPEAT GEN_TAC THEN
   REWRITE_TAC[cake_def "heap_store_unused"] THEN
   COND_CASES_TAC THENL
    [MATCH_ACCEPT_TAC heap_store_heap_lookup;
     REWRITE_TAC[PAIR_EQ]]);;

let heap_store_unused_gen_state_ok =
  cake_theorem "heap_store_unused_gen_state_ok[local]"
  (fun () ->
    `heap_store_unused a k x heap = (heap2,T) /\
     gen_state_ok a (a + k) heap gens ==>
     gen_state_ok a ((a + k) - el_length x) heap2 gens`)
  (* a start of a generation is below a, so the split of the heap
     there is the split of the stored heap (heap_split_heap_store),
     with the same first half; and the references start lower than
     before, which is a weaker bound on the pointers.  The transfer
     is a lemma with type variables of its own, so that it can be
     used on the heaps of the goal (PORTING-GUIDE.md entry 25) *)
  (
   let transfer = prove
    (`!(hp:((A,B)heap_element)list) hp2 aa kk xx ss.
        heap_store aa (heap_expand (kk - el_length xx) ++ [xx]) hp =
          (hp2,T) /\
        ss <= aa /\ gen_start_ok hp (aa + kk) ss
        ==> gen_start_ok hp2 ((aa + kk) - el_length xx) ss`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[cake_def "gen_start_ok"] THEN
     DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (REPEAT_TCL CHOOSE_THEN
         (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
     FIRST_ASSUM(fun hs -> FIRST_ASSUM(fun sp -> FIRST_ASSUM(fun le ->
       MP_TAC(MATCH_MP (cake_thm "heap_split_heap_store")
         (CONJ sp (CONJ hs le)))))) THEN
     DISCH_THEN(X_CHOOSE_THEN `h3:((A,B)heap_element)list`
       ASSUME_TAC) THEN
     ASM_EXISTS_TAC THEN ASM_REWRITE_TAC[] THEN
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     FIRST_ASSUM(fun pc -> FIRST_ASSUM(fun m1 -> FIRST_ASSUM(fun m2 ->
       MP_TAC(MATCH_MP pc (CONJ m1 m2))))) THEN
     ARITH_TAC) in
   STRIP_TAC THEN CASES_ON_NAME "gens" THEN
   RULE_ASSUM_TAC(REWRITE_RULE[cake_def "gen_state_ok"]) THEN
   REWRITE_TAC[cake_def "gen_state_ok"] THEN
   USE_CHANGED [cake_def "heap_store_unused"] THEN
   COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
   FIRST [DISCH_THEN(fun th ->
            CONTR_TAC(REWRITE_RULE[] (CONJUNCT2 th)));
          DISCH_TAC] THEN
   FIRST_ASSUM(fun gs ->
     let c1 = CONJUNCT1 gs and c2 = CONJUNCT2 gs in
     CONJ_TAC THENL
      [ACCEPT_TAC c1;
       MATCH_MP_TAC ALL_IMP THEN
       EXISTS_TAC (lhand (concl c2)) THEN
       CONJ_TAC THENL
        [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC transfer THEN
         W(fun (asl,w) ->
           let hs = find (fun (_,th) ->
             (try fst(dest_const(fst(strip_comb(lhand(concl th))))) =
                  "heap_store"
              with Failure _ -> false)) asl in
           EXISTS_TAC (el 2 (snd(strip_comb
             (lhand (concl (snd hs))))))) THEN
         ASM_REWRITE_TAC[] THEN
         FIRST_ASSUM(fun m ->
           ACCEPT_TAC(MATCH_MP (REWRITE_RULE[GSYM ALL_MEM] c1) m));
         ACCEPT_TAC c2]]));;

(* new ref *)

let blocks_unique_new_ref = cake_theorem "blocks_unique_new_ref"
  (fun () ->
    `blocks_unique ts (all_vs refs (xs ++ stack)) ==>
       blocks_unique ts
         (all_vs (insert ptr (ValueArray xs) refs)
            (xs ++ (RefPtr T ptr :: stack)))`)
  (* the ValueArray of the new reference holds the values that the
     stack has in front of it already *)
  (let li = prove
    (`!k1 k2 v (t:(A)spt) y.
        (sptree_lookup k1 (sptree_insert k2 v t) = SOME y) <=>
        (k1 = k2 /\ v = y) \/
        (~(k1 = k2) /\ sptree_lookup k1 t = SOME y)`,
     REPEAT GEN_TAC THEN REWRITE_TAC[lookup_insert] THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC[injectivity "option"] THEN CONV_TAC TAUT) in
   let vrefptr = prove
    (`!b p ys. v_all_vs (CONS (RefPtr b p) ys) =
        CONS (RefPtr b p) (v_all_vs ys)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [cake_def "v_all_vs"] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   let inc = prove
    (`!refs p xs stack' t a q.
        Block t a q IN
          all_vs (insert p (ValueArray xs) refs)
                 (APPEND xs (CONS (RefPtr T p) stack')) ==>
        Block t a q IN all_vs refs (APPEND xs stack')`,
     REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM; li;
                 vrefptr; v_all_vs_append; MEM; MEM_APPEND;
                 distinctness "dataSem_v";
                 distinctness "bvlSem_ref";
                 injectivity "bvlSem_ref"] THEN MESON_TAC[]) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN DISCH_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THEN ASM_MESON_TAC[inc]);;

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
  (* the value that the thunk holds is on the stack already,
     and the RefPtr that is put there is no Block *)
  (let li = prove
    (`!k1 k2 v (t:(A)spt) y.
        (sptree_lookup k1 (sptree_insert k2 v t) = SOME y) <=>
        (k1 = k2 /\ v = y) \/
        (~(k1 = k2) /\ sptree_lookup k1 t = SOME y)`,
     REPEAT GEN_TAC THEN REWRITE_TAC[lookup_insert] THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC[injectivity "option"] THEN CONV_TAC TAUT) in
   let cons_app = prove
    (`!(h:dataSem_v) t. CONS h t = APPEND [h] t`,
     REWRITE_TAC[APPEND]) in
   let vrefptr = prove
    (`!b p ys. v_all_vs (CONS (RefPtr b p) ys) =
        CONS (RefPtr b p) (v_all_vs ys)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [cake_def "v_all_vs"] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   let f1 = prove
    (`!(v:dataSem_v) p xs y.
        MEM y (v_all_vs (CONS v (CONS (RefPtr F p) xs))) <=>
        MEM y (v_all_vs [v]) \/ y = RefPtr F p \/
        MEM y (v_all_vs xs)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
       [cons_app] THEN
     REWRITE_TAC[v_all_vs_append; MEM_APPEND; vrefptr; MEM]) in
   let inc = prove
    (`!refs ptr ev v stack' t a q.
        Block t a q IN
          all_vs (insert ptr (Thunk ev v) refs)
                 (CONS v (CONS (RefPtr F ptr) stack')) ==>
        Block t a q IN all_vs refs (CONS v stack')`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM; li; f1;
                 distinctness "bvlSem_ref"; injectivity "bvlSem_ref";
                 distinctness "dataSem_v"] THEN
     MESON_TAC[MEM_v_all_vs_extend_tl; MEM_v_all_vs_extend_hd]) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN DISCH_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THEN ASM_MESON_TAC[inc]);;

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
  (* the value of the thunk is a value of the refs already *)
  (let vcons = prove
    (`!(v:dataSem_v) xs y. MEM y (v_all_vs (CONS v xs)) <=>
        MEM y (v_all_vs [v]) \/ MEM y (v_all_vs xs)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
       [prove(`!(h:dataSem_v) t. CONS h t = APPEND [h] t`,
              REWRITE_TAC[APPEND])] THEN
     REWRITE_TAC[v_all_vs_append; MEM_APPEND]) in
   let inc = prove
    (`!refs ptr a' stack' t a q.
        sptree_lookup ptr refs = SOME (Thunk NotEvaluated a') /\
        Block t a q IN all_vs refs (CONS a' (CONS (RefPtr F ptr)
          stack')) ==>
        Block t a q IN all_vs refs (CONS (RefPtr F ptr) stack')`,
     REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM] THEN
     MESON_TAC[vcons]) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN STRIP_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THEN ASM_MESON_TAC[inc]);;

let blocks_unique_deref2 = cake_theorem "blocks_unique_deref2"
  (fun () ->
    `n < LENGTH l /\
     lookup ptr refs = SOME (ValueArray l) /\
     blocks_unique ts (all_vs refs (RefPtr b ptr :: stack)) ==>
       blocks_unique ts (all_vs refs (EL n l :: RefPtr b ptr ::
         stack))`)
  (* the value that the dereference puts on the stack is one
     of the ValueArray that the pointer holds *)
  (let cons_app = prove
    (`!(h:dataSem_v) t. CONS h t = APPEND [h] t`,
     REWRITE_TAC[APPEND]) in
   let vrefptr = prove
    (`!b p ys. v_all_vs (CONS (RefPtr b p) ys) =
        CONS (RefPtr b p) (v_all_vs ys)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [cake_def "v_all_vs"] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   let fref = prove
    (`!(v:dataSem_v) p b xs y.
        MEM y (v_all_vs (CONS v (CONS (RefPtr b p) xs))) <=>
        MEM y (v_all_vs [v]) \/ y = RefPtr b p \/ MEM y (v_all_vs xs)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
       [cons_app] THEN
     REWRITE_TAC[v_all_vs_append; MEM_APPEND; vrefptr; MEM]) in
   let inc = prove
    (`!refs ptr b l n stack' t a q.
        n < LENGTH l /\
        sptree_lookup ptr refs = SOME (ValueArray l) /\
        Block t a q IN
          all_vs refs (CONS (EL n l) (CONS (RefPtr b ptr) stack')) ==>
        Block t a q IN all_vs refs (CONS (RefPtr b ptr) stack')`,
     REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM; fref;
                 distinctness "dataSem_v"] THEN
     MESON_TAC[MEM_v_all_vs_EL; MEM_v_all_vs_extend_hd]) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN STRIP_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THEN ASM_MESON_TAC[inc]);;

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
  (* and the element of a Block is one of its payload *)
  (let cons_app = prove
    (`!(h:dataSem_v) t. CONS h t = APPEND [h] t`,
     REWRITE_TAC[APPEND]) in
   let vblk = prove
    (`!t tag xs ys. v_all_vs (CONS (Block t tag xs) ys) =
        APPEND (CONS (Block t tag xs) (v_all_vs xs)) (v_all_vs ys)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [cake_def "v_all_vs"] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   let fblk = prove
    (`!(v:dataSem_v) t tag xs ys y.
        MEM y (v_all_vs (CONS v (CONS (Block t tag xs) ys))) <=>
        MEM y (v_all_vs [v]) \/ y = Block t tag xs \/
        MEM y (v_all_vs xs) \/ MEM y (v_all_vs ys)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
       [cons_app] THEN
     REWRITE_TAC[v_all_vs_append; MEM_APPEND; vblk; MEM;
                 DISJ_ASSOC]) in

   let inc = prove
    (`!refs t0 n xs i stack' t a q.
        i < LENGTH xs /\
        Block t a q IN
          all_vs refs (CONS (EL i xs) (CONS (Block t0 n xs)
            stack')) ==>
        Block t a q IN all_vs refs (CONS (Block t0 n xs) stack')`,
     REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM; fblk;
                 vblk; MEM; MEM_APPEND] THEN
     MESON_TAC[MEM_v_all_vs_EL]) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN STRIP_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THEN ASM_MESON_TAC[inc]);;

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
  (* and the RefPtr that the stack is given is no Block *)
  (let li = prove
    (`!k1 k2 v (t:(A)spt) y.
        (sptree_lookup k1 (sptree_insert k2 v t) = SOME y) <=>
        (k1 = k2 /\ v = y) \/
        (~(k1 = k2) /\ sptree_lookup k1 t = SOME y)`,
     REPEAT GEN_TAC THEN REWRITE_TAC[lookup_insert] THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC[injectivity "option"] THEN CONV_TAC TAUT) in
   let vrefptr = prove
    (`!b p ys. v_all_vs (CONS (RefPtr b p) ys) =
        CONS (RefPtr b p) (v_all_vs ys)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [cake_def "v_all_vs"] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   let inc = prove
    (`!refs p fl bs b stack' t a q.
        Block t a q IN
          all_vs (insert p (ByteArray fl bs) refs)
                 (CONS (RefPtr b p) stack') ==>
        Block t a q IN all_vs refs stack'`,
     REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM; li;
                 vrefptr; MEM; distinctness "dataSem_v";
                 distinctness "bvlSem_ref";
                 injectivity "bvlSem_ref"] THEN MESON_TAC[]) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN DISCH_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THEN ASM_MESON_TAC[inc]);;

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
  (REWRITE_TAC[cake_def "abs_ml_inv";
               cake_def "bc_stack_ref_inv"] THEN
   STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ALL2; v_inv_RefPtr_T; INJ]) THEN
   ASM_MESON_TAC[injectivity "heap_address"]);;

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
  (* Smallnum writes the two cases of i2w out: a negative integer
     is the negation of the word of its absolute value, and & of
     the number of a non-negative integer is the integer itself *)
  (REWRITE_TAC[cake_def "Smallnum"] THEN COND_CASES_TAC THENL
    [REWRITE_TAC[WORD_SUB_LZERO] THEN
     ONCE_REWRITE_TAC[WORD_IWORD] THEN
     REWRITE_TAC[GSYM IWORD_INT_NEG] THEN AP_TERM_TAC THEN
     SUBGOAL_THEN `&0 <= &4 * ((&0) - (i:int))` (fun th ->
       REWRITE_TAC[MATCH_MP INT_OF_NUM_OF_INT th]) THENL
      [ASM_INT_ARITH_TAC; INT_ARITH_TAC];
     ONCE_REWRITE_TAC[WORD_IWORD] THEN AP_TERM_TAC THEN
     MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC]);;

let small_int_IMP_MIN_MAX = cake_theorem "small_int_IMP_MIN_MAX"
  (fun () ->
    `good_dimindex (:'a) /\ small_int (:'a) i ==>
      INT_MIN (:'a) <= (&4) * i /\ (&4) * i <= INT_MAX (:'a)`)
  (* the bound of a small integer is a quarter of the dimword and
     INT_MIN and INT_MAX are a half of it, so four times a small
     integer is between them *)
  (REWRITE_TAC[cake_def "good_dimindex"; cake_def "small_int";
               dimword; integer_word_INT_MIN; integer_word_INT_MAX;
               INT_MIN] THEN
   STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
   RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
   CONV_TAC NUM_REDUCE_CONV THEN ASM_INT_ARITH_TAC);;

let num_less_thm = cake_theorem "num_less_thm"
  (fun () ->
    `good_dimindex (:'a) /\ small_int (:'a) i1 /\ small_int (:'a) i2 ==>
      ((i1 < i2) <=> (Smallnum i1 < (Smallnum i2:'a word)))`)
  (* the words are the i2w of four times the integers, whose
     ival is the integer itself because a small integer times
     four is between INT_MIN and INT_MAX *)
  (let bnds = prove
    (`good_dimindex (:'a) /\ small_int (:'a) i ==>
       --(&2 pow (dimindex (:'a) - 1)) <= (&4) * i /\
       (&4) * i < &2 pow (dimindex (:'a) - 1)`,
     REWRITE_TAC[cake_def "good_dimindex"; cake_def "small_int";
                 dimword] THEN
     STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
     RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     CONV_TAC(ONCE_DEPTH_CONV INT_POW_CONV) THEN
     ASM_INT_ARITH_TAC) in
   STRIP_TAC THEN
   REWRITE_TAC[smallnum_i2w; word_ilt; irelational2] THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   ASSUM_LIST(fun ths ->
     REWRITE_TAC(mapfilter (fun (a,b) ->
       MATCH_MP IVAL_IWORD (MATCH_MP bnds (CONJ a b)))
       (allpairs (fun a b -> (a,b)) ths ths))) THEN
   INT_ARITH_TAC);;

(* permute stack *)

let all_ts_permute = cake_theorem "all_ts_permute"
  (fun () ->
    `!(refs:(dataSem_v bvlSem_ref) spt) stack' stack'.
       PERM stack' stack' ==> all_ts refs stack' = all_ts refs
         stack'`)
  (* the two variables of HOL4's statement, `stack` and `stack'`,
     became one name in the port, so what it states here is that
     the timestamps of a list are the timestamps of that same list
     (see ISSUES.md, "A statement whose two variables became one
     name"): nothing uses it, in the port or in HOL4, and the
     statement is what has to be put right, not the proof *)
  (REWRITE_TAC[]);;

let reachable_refs_stack_subset =
  cake_theorem "reachable_refs_stack_subset"
  (fun () ->
    `!x y refs n. reachable_refs y refs n /\ set_of_list y SUBSET
  set_of_list x ==> reachable_refs x refs n`)
  (* the roots of the one stack are roots of the other, and
     reachable_refs asks for nothing else of them *)
  (REWRITE_TAC[cake_def "reachable_refs"] THEN
   REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET; IN_SET_OF_LIST] THEN
   STRIP_TAC THEN ASM_MESON_TAC[]);;

let MEM_v_all_vs_FST = cake_theorem "MEM_v_all_vs_FST"
  (fun () ->
    `!xs h0 h1 x.
     MEM (h0,h1) xs /\
     MEM x (v_all_vs [h0]) ==>
       MEM x (v_all_vs (MAP FST xs))`)
  (* the head of the list is the pair that holds the value, or the
     value is one of the tail *)
  (LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM] THEN
   REPEAT GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THENL
    [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
     REWRITE_TAC[FST] THEN
     MATCH_MP_TAC MEM_v_all_vs_extend_tl THEN
     FIRST_ASSUM ACCEPT_TAC;
     MATCH_MP_TAC MEM_v_all_vs_extend_hd THEN
     FIRST_ASSUM(fun ih -> FIRST_ASSUM(fun a1 ->
       FIRST_ASSUM(fun a2 ->
         ACCEPT_TAC(MATCH_MP ih (CONJ a1 a2)))))]);;

let MEM_v_all_vs_SUBSET = cake_theorem "MEM_v_all_vs_SUBSET"
  (fun () ->
    `!ys xs x.
       set_of_list ys SUBSET set_of_list xs /\
       MEM x (v_all_vs (MAP FST ys)) ==>
         MEM x (v_all_vs (MAP FST xs))`)
  (* the head of ys is a pair of xs, so its value is one of the
     values of xs; the tail is the induction hypothesis *)
  (let vnil = prove
    (`v_all_vs ([]:dataSem_v list) = []`,
     GEN_REWRITE_TAC LAND_CONV [cake_def "v_all_vs"] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   let pairit = CONV_RULE(ONCE_DEPTH_CONV(REWR_CONV(GSYM PAIR))) in
   LIST_INDUCT_TAC THEN REWRITE_TAC[MAP] THENL
    [REWRITE_TAC[vnil; MEM];
     REPEAT GEN_TAC THEN
     DISCH_THEN(CONJUNCTS_THEN2
       (ASSUME_TAC o REWRITE_RULE[SUBSET; IN_SET_OF_LIST; MEM])
       (fun th -> MP_TAC(MATCH_MP MEM_v_all_vs_split th))) THEN
     STRIP_TAC THENL
      [FIRST_X_ASSUM(fun sub ->
         let v,bod = dest_forall(concl sub) in
         let dis = lhand bod in
         let p = rand(lhand dis) in
         ASSUME_TAC(MP (SPEC p sub)
           (DISJ1 (REFL p) (vsubst [p,v] (rand dis))))) THEN
       FIRST_ASSUM(fun m1 -> FIRST_ASSUM(fun m2 ->
         ACCEPT_TAC(MATCH_MP MEM_v_all_vs_FST
           (CONJ (pairit m1) m2))));
       FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
        [REWRITE_TAC[SUBSET; IN_SET_OF_LIST] THEN
         GEN_TAC THEN DISCH_TAC THEN
         FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
         FIRST_ASSUM ACCEPT_TAC]]]);;

let blocks_unique_stack_permute =
  cake_theorem "blocks_unique_stack_permute"
  (fun () ->
    `set_of_list ys SUBSET set_of_list xs /\
     blocks_unique ts (all_vs refs (MAP FST xs ++ stack)) ==>
       blocks_unique ts (all_vs refs (MAP FST ys ++ stack))`)
  (* and a sublist of the pairs has a sublist of the values *)
  (let inc = prove
    (`!refs (ys:(dataSem_v#A)list) xs stack' t a q.
        set_of_list ys SUBSET set_of_list xs /\
        Block t a q IN all_vs refs (APPEND (MAP FST ys) stack') ==>
        Block t a q IN all_vs refs (APPEND (MAP FST xs) stack')`,
     REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM;
                 v_all_vs_append; MEM_APPEND] THEN
     MESON_TAC[MEM_v_all_vs_SUBSET]) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN STRIP_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THEN ASM_MESON_TAC[inc]);;

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
  (* the stack permutation that keeps none of the values that are
     popped: the pairs of the two lists are the ZIP of them *)
  (let pop = prove
    (`!conf (xs:(dataSem_v)list) (rs:(('a word_loc)heap_address)list)
         stack roots heap be a sp sp1 gens limit ts refs.
        abs_ml_inv conf (xs ++ stack) refs
          (rs ++ roots,heap,be,a,sp,sp1,gens) limit ts /\
        LENGTH xs = LENGTH rs
        ==> abs_ml_inv conf stack refs
              (roots,heap,be,a,sp,sp1,gens) limit ts`,
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     MP_TAC(ISPECL
       [`ZIP (xs:(dataSem_v)list)
             (rs:(('a word_loc)heap_address)list)`;
        `[]:(dataSem_v#('a word_loc)heap_address)list`]
       (cake_thm "abs_ml_inv_stack_permute")) THEN
     ASM_SIMP_TAC[MAP_FST_ZIP; MAP_SND_ZIP; MAP; APPEND;
                  set_of_list; EMPTY_SUBSET]) in
   MATCH_ACCEPT_TAC pop);;

(* duplicate *)

let blocks_unique_duplicate = cake_theorem "blocks_unique_duplicate"
  (fun () ->
    `blocks_unique ts (all_vs refs (xs ++ stack)) ==>
       blocks_unique ts (all_vs refs (xs ++ xs ++ stack))`)
  (* the values of xs ++ xs ++ stack are the values of xs ++ stack *)
  (let inc = prove
    (`!refs xs stack' t a q.
        Block t a q IN all_vs refs (APPEND xs (APPEND xs stack')) ==>
        Block t a q IN all_vs refs (APPEND xs stack')`,
     REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM;
                 v_all_vs_append; MEM_APPEND] THEN MESON_TAC[]) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN DISCH_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THEN ASM_MESON_TAC[inc]);;

let duplicate_thm = cake_theorem "duplicate_thm"
  (fun () ->
    `abs_ml_inv conf (xs ++ stack) refs (rs ++
  roots,heap,be,a,sp,sp1,gens) limit ts /\
     (LENGTH xs = LENGTH rs) ==>
     abs_ml_inv conf (xs ++ xs ++ stack) refs (rs ++ rs ++
       roots,heap,be,a,sp,sp1,gens) limit ts`)
  (* the invariant of the doubled stack: the roots and the
     reachable references are the ones of the stack it doubles,
     blocks_unique_duplicate gives the uniqueness, the timestamps of
     the doubled stack are more and the relation of the values is
     the one of the two parts, which the split of a LIST_REL over an
     append gives *)
  (let gv n =
     W(fun (asl,_) ->
       let tms = itlist (fun (_,th) acc -> union (frees(concl th)) acc)
                   asl [] in
       EXISTS_TAC (find (fun t -> fst(dest_var t) = n) tms)) in
   let rel_app_eq = prove
    (`!(P:A->B->bool) xs1 ys1 xs2 ys2. LENGTH xs1 = LENGTH ys1
        ==> (ALL2 P (xs1 ++ xs2) (ys1 ++ ys2) <=>
             ALL2 P xs1 ys1 /\ ALL2 P xs2 ys2)`,
     GEN_TAC THEN LIST_INDUCT_TAC THEN X_GEN_TAC `ys1:B list` THEN
     STRUCT_CASES_TAC(ISPEC `ys1:B list` list_CASES_v) THEN
     REWRITE_TAC[LENGTH; APPEND; ALL2; NOT_SUC; SUC_INJ;
                 ARITH_RULE `~(SUC n = 0)`;
                 ARITH_RULE `~(0 = SUC n)`] THEN
     REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
     CONV_TAC TAUT) in
   let rr_mono = prove
    (`!(as:(dataSem_v)list) bs rfs n.
        (!x. MEM x as ==> MEM x bs) /\ reachable_refs as rfs n
        ==> reachable_refs bs rfs n`,
     REWRITE_TAC[cake_def "reachable_refs"] THEN MESON_TAC[]) in
   REWRITE_TAC[cake_def "abs_ml_inv"; cake_def "bc_stack_ref_inv"] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [USE_CHANGED [cake_def "roots_ok"] THEN
     REWRITE_TAC[cake_def "roots_ok"; MEM_APPEND] THEN MESON_TAC[];
     ALL_TAC] THEN
   gv "f" THEN gv "tf" THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THENL
    [FIRST_ASSUM(fun sub ->
       let t = rand(concl sub) in
       if (try fst(dest_const(fst(strip_comb t))) = "all_ts"
           with Failure _ -> false)
       then MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC t THEN
            CONJ_TAC THENL [ACCEPT_TAC sub; ALL_TAC]
       else fail()) THEN
     REWRITE_TAC[cake_def "all_ts"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[SUBSET; IN_ELIM_THM; MEM_APPEND] THEN
     GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
     CONV_TAC TAUT;
     MATCH_MP_TAC (cake_thm "blocks_unique_duplicate") THEN
     ASM_REWRITE_TAC[];
     W(fun (asl,_) ->
       let eqs = mapfilter (fun (_,th) -> MATCH_MP rel_app_eq th) asl in
       RULE_ASSUM_TAC(REWRITE_RULE eqs) THEN REWRITE_TAC eqs) THEN
     ASM_REWRITE_TAC[];
     GEN_TAC THEN STRIP_TAC THEN
     FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
      [FIRST_ASSUM(fun rr ->
         MATCH_MP_TAC rr_mono THEN
         EXISTS_TAC (rand(rator(rator(concl rr)))) THEN
         CONJ_TAC THENL
          [REWRITE_TAC[MEM_APPEND] THEN GEN_TAC THEN CONV_TAC TAUT;
           ACCEPT_TAC rr]);
       FIRST_ASSUM ACCEPT_TAC]]);;

(* HOL4 data_to_word_memoryProofScript.sml:7427-7429: a theorem that
   HOL4 states as the value of an ML expression: duplicate1_thm *)

(* move *)

let blocks_unique_move = cake_theorem "blocks_unique_move"
  (fun () ->
    `blocks_unique ts (all_vs refs (xs1 ++ xs2 ++ xs3 ++ stack)) ==>
       blocks_unique ts (all_vs refs (xs1 ++ xs3 ++ xs2 ++
         stack))`)
  (* the values of a stack do not depend on the order of its
     three parts *)
  (let inc = prove
    (`!refs xs1 xs2 xs3 stack' t a q.
        Block t a q IN
          all_vs refs (APPEND xs1 (APPEND xs3 (APPEND xs2 stack')))
        ==>
        Block t a q IN
          all_vs refs (APPEND xs1 (APPEND xs2 (APPEND xs3 stack')))`,
     REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM;
                 v_all_vs_append; MEM_APPEND] THEN MESON_TAC[]) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN DISCH_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THEN ASM_MESON_TAC[inc]);;

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
  (* the invariant of the stack with its second and third part
     exchanged: nothing of it depends on the order of the parts, so
     each conjunct is the one of the assumption -- the relation of
     the values after splitting it into the four parts, and
     blocks_unique_move for the uniqueness *)
  (let gv n =
     W(fun (asl,_) ->
       let tms = itlist (fun (_,th) acc -> union (frees(concl th)) acc)
                   asl [] in
       EXISTS_TAC (find (fun t -> fst(dest_var t) = n) tms)) in
   let rel_app_eq = prove
    (`!(P:A->B->bool) xs1 ys1 xs2 ys2. LENGTH xs1 = LENGTH ys1
        ==> (ALL2 P (xs1 ++ xs2) (ys1 ++ ys2) <=>
             ALL2 P xs1 ys1 /\ ALL2 P xs2 ys2)`,
     GEN_TAC THEN LIST_INDUCT_TAC THEN X_GEN_TAC `ys1:B list` THEN
     STRUCT_CASES_TAC(ISPEC `ys1:B list` list_CASES_v) THEN
     REWRITE_TAC[LENGTH; APPEND; ALL2; NOT_SUC; SUC_INJ;
                 ARITH_RULE `~(SUC n = 0)`;
                 ARITH_RULE `~(0 = SUC n)`] THEN
     REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
     CONV_TAC TAUT) in
   let rr_mono = prove
    (`!(as:(dataSem_v)list) bs rfs n.
        (!x. MEM x as ==> MEM x bs) /\ reachable_refs as rfs n
        ==> reachable_refs bs rfs n`,
     REWRITE_TAC[cake_def "reachable_refs"] THEN MESON_TAC[]) in
   REPEAT GEN_TAC THEN
   REWRITE_TAC[cake_def "abs_ml_inv"; cake_def "bc_stack_ref_inv"] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [USE_CHANGED [cake_def "roots_ok"] THEN
     REWRITE_TAC[cake_def "roots_ok"; MEM_APPEND] THEN MESON_TAC[];
     ALL_TAC] THEN
   gv "f" THEN gv "tf" THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THENL
    [FIRST_ASSUM(fun sub ->
       let t = rand(concl sub) in
       if (try fst(dest_const(fst(strip_comb t))) = "all_ts"
           with Failure _ -> false)
       then MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC t THEN
            CONJ_TAC THENL [ACCEPT_TAC sub; ALL_TAC]
       else fail()) THEN
     REWRITE_TAC[cake_def "all_ts"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[SUBSET; IN_ELIM_THM; MEM_APPEND] THEN
     GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
     CONV_TAC TAUT;
     MATCH_MP_TAC (cake_thm "blocks_unique_move") THEN
     ASM_REWRITE_TAC[];
     W(fun (asl,_) ->
       let eqs = mapfilter (fun (_,th) -> MATCH_MP rel_app_eq th) asl in
       RULE_ASSUM_TAC(REWRITE_RULE eqs) THEN REWRITE_TAC eqs) THEN
     ASM_REWRITE_TAC[];
     GEN_TAC THEN STRIP_TAC THEN
     FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
      [FIRST_ASSUM(fun rr ->
         MATCH_MP_TAC rr_mono THEN
         EXISTS_TAC (rand(rator(rator(concl rr)))) THEN
         CONJ_TAC THENL
          [REWRITE_TAC[MEM_APPEND] THEN GEN_TAC THEN CONV_TAC TAUT;
           ACCEPT_TAC rr]);
       FIRST_ASSUM ACCEPT_TAC]]);;

(* splits *)

let split1_thm = cake_theorem "split1_thm"
  (fun () ->
    `abs_ml_inv conf (xs1 ++ stack) refs (roots,heap,be,a,sp,sp1,gens)
  limit ts ==>
      (?rs1 roots1. (roots = rs1 ++ roots1) /\ (LENGTH rs1 =
        LENGTH xs1))`)
  (REWRITE_TAC[cake_def "abs_ml_inv"; cake_def "bc_stack_ref_inv";
               LIST_REL_SPLIT1] THEN
   STRIP_TAC THEN ASM_MESON_TAC[LIST_REL_LENGTH]);;

let split2_thm = cake_theorem "split2_thm"
  (fun () ->
    `abs_ml_inv conf (xs1 ++ xs2 ++ stack) refs
  (roots,heap,be,a,sp,sp1,gens) limit ts ==>
      (?rs1 rs2 roots1. (roots = rs1 ++ rs2 ++ roots1) /\
        (LENGTH rs1 = LENGTH xs1) /\ (LENGTH rs2 = LENGTH xs2))`)
  (REWRITE_TAC[cake_def "abs_ml_inv"; cake_def "bc_stack_ref_inv";
               GSYM APPEND_ASSOC; LIST_REL_SPLIT1] THEN
   STRIP_TAC THEN ASM_MESON_TAC[LIST_REL_LENGTH]);;

let split3_thm = cake_theorem "split3_thm"
  (fun () ->
    `abs_ml_inv conf (xs1 ++ xs2 ++ xs3 ++ stack) refs
  (roots,heap,be,a,sp,sp1,gens) limit ts ==>
      (?rs1 rs2 rs3 roots1. (roots = rs1 ++ rs2 ++ rs3 ++ roots1)
        /\
        (LENGTH rs1 = LENGTH xs1) /\ (LENGTH rs2 = LENGTH xs2) /\
        (LENGTH rs3 = LENGTH xs3))`)
  (REWRITE_TAC[cake_def "abs_ml_inv"; cake_def "bc_stack_ref_inv";
               GSYM APPEND_ASSOC; LIST_REL_SPLIT1] THEN
   STRIP_TAC THEN ASM_MESON_TAC[LIST_REL_LENGTH]);;

let abs_ml_inv_Num = cake_theorem "abs_ml_inv_Num"
  (fun () ->
    `abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts
  /\ small_int (:'a) i ==>
      abs_ml_inv conf (Number i :: stack) refs
        (gc_shared_Data (wordLang_Word ((Smallnum i):'a word)) ::
          roots,heap,be,a,sp,sp1,gens) limit ts`)
  (* the new root is a Data, so the roots stay ok; the value has no
     refs and no timestamps of its own, so what the stack reaches
     and what the timestamps are stay as they are, and v_inv of a
     small Number is its Smallnum *)
  (let gr0 = CONJUNCT1 (cake_def "get_refs") in
  let reach = prove
   (`!(sk:(dataSem_v)list) rfs n i.
       reachable_refs (Number i :: sk) rfs n
       ==> reachable_refs sk rfs n`,
    REWRITE_TAC[cake_def "reachable_refs"; MEM] THEN
    MESON_TAC[gr0; MEM]) in
  REWRITE_TAC[cake_def "abs_ml_inv"; cake_def "bc_stack_ref_inv"] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[cake_def "roots_ok"]) THEN
    REWRITE_TAC[cake_def "roots_ok"; MEM;
                distinctness "heap_address"] THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THENL
     [(fun (asl,w) ->
        let ats = rand w in
        let wit = mk_comb(rator ats, rand(rand ats)) in
        (MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC wit) (asl,w)) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC (cake_thm "all_ts_SUBSET_gen") THEN
      REWRITE_TAC[MEM] THEN GEN_TAC THEN
      DISCH_THEN(DISJ_CASES_THEN2
        (fun p -> DISJ1_TAC THEN ACCEPT_TAC p)
        (fun m -> DISJ2_TAC THEN DISJ2_TAC THEN ACCEPT_TAC m));
      MATCH_MP_TAC (INST [`[]:(dataSem_v)list`,`ws:(dataSem_v)list`]
        (cake_thm "blocks_unique_Number")) THEN
      ASM_REWRITE_TAC[APPEND];
      REWRITE_TAC[ALL2] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[cake_thm "v_inv_def"] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `nn:num` THEN STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [FIRST_ASSUM(fun rr -> MATCH_ACCEPT_TAC(MATCH_MP reach rr));
        FIRST_ASSUM MATCH_ACCEPT_TAC]]]);;

let heap_store_unused_IMP_length =
  cake_theorem "heap_store_unused_IMP_length"
  (fun () ->
    `heap_store_unused a sp' x heap = (heap2,T) ==>
       heap_length heap2 = heap_length heap`)
  (* the lookup splits the heap at the unused element, the store
     lemma says what the store gives back, and the lengths add up *)
  (REWRITE_TAC[cake_def "heap_store_unused"] THEN
   COND_CASES_TAC THENL
    [FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
     FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP heap_lookup_SPLIT th)) THEN
     DISCH_THEN STRIP_ASSUME_TAC THEN VAR_EQ_TAC THEN
     ASM_REWRITE_TAC[heap_store_lemma; PAIR_EQ] THEN
     STRIP_TAC THEN VAR_EQ_TAC THEN
     ASM_REWRITE_TAC[heap_length_APPEND; heap_length_CONS] THEN
     ASM_ARITH_TAC;
     REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let heap_store_unused_alt_IMP_length =
  cake_theorem "heap_store_unused_alt_IMP_length"
  (fun () ->
    `heap_store_unused_alt a sp' x heap = (heap2,T) ==>
      heap_length heap2 = heap_length heap`)
  (REWRITE_TAC[cake_def "heap_store_unused_alt"] THEN
   COND_CASES_TAC THENL
    [FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
     FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP heap_lookup_SPLIT th)) THEN
     DISCH_THEN STRIP_ASSUME_TAC THEN VAR_EQ_TAC THEN
     ASM_REWRITE_TAC[heap_store_lemma; PAIR_EQ] THEN
     STRIP_TAC THEN VAR_EQ_TAC THEN
     ASM_REWRITE_TAC[heap_length_APPEND; heap_length_CONS] THEN
     ASM_ARITH_TAC;
     REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;


(* -------------------------------------------------------
    representation in memory
   ------------------------------------------------------- *)

let pointer_bits_def = cake_define
  `// pointers have tag and len bits
   pointer_bits conf abs_heap n =
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
  (REWRITE_TAC[cake_def "b2w"; cake_def "b2n"]);;

let thunk_tag_to_bits_def = cake_define_list
  [`thunk_tag_to_bits Evaluated = (n2w 1)`;
   `thunk_tag_to_bits NotEvaluated = (n2w 0)`];;

let word_payload_def = cake_define_list
  [`word_payload ys l (BlockTag n) qs conf =
         (
          // header: ...00[11] here i in ...i[11] must be 0 for the GC
          make_header conf (n2w n << 2) (LENGTH ys),
          MAP (word_addr conf) ys,(
          (qs = []) /\ (LENGTH ys = l) /\
          encode_header conf (n * 4) (LENGTH ys) =
            SOME (make_header conf (n2w n << 2) (LENGTH ys):'a
              word)))`;
   `word_payload ys l RefTag qs conf =
         (
          // header: ...010[11] here i in ...i[11] must be 0 for the GC
          make_header conf (n2w 2) (LENGTH ys),
          MAP (word_addr conf) ys,(
          (qs = []) /\ (LENGTH ys = l)))`;
   `word_payload ys l (ThunkTag e) qs conf =
         (
          // header: ...e110[11] here i in ...i[11] must be 0 for the GC
          make_header conf (thunk_tag_to_bits e << 3 || (n2w 6))
            (LENGTH ys),
          MAP (word_addr conf) ys,(
          (qs = []) /\ (LENGTH ys = 1) /\ l = 1))`;
   `word_payload ys l Word64Tag qs conf =
         (
          // header: ...011[11] here i in ...i[11] must be 1 for the GC
          make_header conf (n2w 3) l,
          qs,((ys = []) /\ (LENGTH qs = l) /\
              IS_SOME ((encode_header conf 3 l):('a word)
                option)))`;
   `word_payload ys l (NumTag b) qs conf =
         (
          // header: ...111[11] or ...011[11]
          // here i in ...i[11] must be 1 for GC
          make_header conf (b2w b << 2 || ((n2w 3):'a word)) (LENGTH
            qs),
          qs,((ys = []) /\ (LENGTH qs = l) /\
              IS_SOME ((encode_header conf (w2n (b2w b << 2 || ((n2w
                3):'a word)))
                          (LENGTH qs)):('a word) option)))`;
   `word_payload ys l (BytesTag fl n) qs conf =
         (((
           // header: ...101[11] or ...001[11] (compare-by-contents)
           // here i in ...i[11] must be 1 for the GC
           make_byte_header conf fl n):'a word),
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
  (* the six tags each give a header of make_header or of
     make_byte_header, and the third component of the payload says
     what the length is.  The bit two of a header is the bit zero of
     its tag, because the length sits above the bit two (the length
     size and two are below the dimindex) and the three at the
     bottom has the bit two clear; of make_byte_header it is set,
     whichever of the two tags it takes *)
  (let hdr_bit2 = prove
    (`!conf tg len.
        data_to_word_config_len_size conf + 2 < dimindex (:'a)
        ==> (word_bit 2 (make_header conf (tg:'a word) len) <=>
             word_bit 0 tg)`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     FIRST_ASSUM(fun th ->
       ASSUME_TAC(MATCH_MP
         (ARITH_RULE `k + 2 < d ==> 2 < d`) th)) THEN
     REWRITE_TAC[cake_def "make_header"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     ASM_SIMP_TAC[ARITH_RULE `k + 2 < d ==> ~(d - k <= 2)`] THEN
     ASM_REWRITE_TAC[]) in
   let byte_hdr_bit2 = prove
    (`!conf fl n. 2 < dimindex (:'a)
        ==> word_bit 2 (make_byte_header conf fl n:'a word)`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC[cake_def "make_byte_header"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REPEAT COND_CASES_TAC THEN
     ASM_REWRITE_TAC[BIT_WORD_OR; BIT_WORD] THEN
     CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]) in
   STRIP_TAC THEN
   FIRST_ASSUM(fun th ->
     ASSUME_TAC(MATCH_MP (ARITH_RULE `k + 2 < d ==> 2 < d`) th) THEN
     ASSUME_TAC(MATCH_MP (ARITH_RULE `k + 2 < d ==> 0 < d`) th)) THEN
   CASES_ON_NAME "tag" THEN
   RULE_ASSUM_TAC(REWRITE_RULE[cake_def "word_payload"; PAIR_EQ;
                               EQ_CLAUSES]) THEN
   REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
   REPEAT(FIRST_X_ASSUM(fun th ->
     let c = concl th in
     if is_eq c && is_var(rand c) && not(is_var(lhand c))
     then SUBST_ALL_TAC(SYM th) else fail())) THEN
   ASM_SIMP_TAC[hdr_bit2; byte_hdr_bit2; LENGTH_MAP; BIT_WORD_SHL;
                BIT_WORD; BIT_WORD_OR] THEN
   CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

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
  (CASES_ON_NAME "x" THEN CASES_ON_NAME "gens" THEN
   REWRITE_TAC[cake_def "gen_starts_in_store"] THEN
   SAFE_MATCH_REDUCE_TAC THEN REWRITE_TAC[] THEN
   TRY(CASES_ON_NAME "a" THEN
       REWRITE_TAC[cake_def "gen_starts_in_store"] THEN
       SAFE_MATCH_REDUCE_TAC THEN REWRITE_TAC[]) THEN
   MESON_TAC[]);;

let glob_real_inv_def = cake_define
  `glob_real_inv c (curr:'a word) globals globreal <=>
     (?w. globals = SOME (wordLang_Word w) /\
         globreal = SOME (wordLang_Word (curr + (w >>>
           (shift_length c) << backend_common_word_shift (:'a)))))`;;

let heap_in_memory_store_def = cake_define
  `heap_in_memory_store heap a sp sp1 gens c s m dm limit' <=>
     heap_length heap <= dimword (:'a) DIV 2 EXP shift_length c /\
     (
      // +3 is breathing room for lists:
      heap_length heap + 3) * (dimindex (:'a) DIV 8) < dimword (:'a)
        /\
     backend_common_word_shift (:'a) <= shift_length c /\
       ~(data_to_word_config_len_size c = 0) /\
       data_to_word_config_len_size
     c + 7 <
             // 5 tag bits + 2-3 bits for byte arrays
             dimindex (:'a) /\
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
  (DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[THE]);;

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
  (let aux = prove
    (`!(P:B->C->bool) f g (xs:A list).
        ALL2 P (MAP f xs) (MAP g xs) <=> ALL (\x. P (f x) (g x)) xs`,
     GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC[MAP; ALL2; ALL]) in
   REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC aux);;

let MEM_FIRST_EL = cake_theorem "MEM_FIRST_EL"
  (fun () ->
    `!xs x.
        MEM x xs <=>
        (?n. n < LENGTH xs /\ (EL n xs = x) /\
            (!m. m < n ==> (~(EL m xs = EL n xs))))`)
  (* a member of a list is at some index, and the least such index
     is one where no earlier element is that element *)
  (let lemma = prove
    (`!(xs:A list) x.
        MEM x xs <=>
        (?n. n < LENGTH xs /\ EL n xs = x /\
             (!m. m < n ==> ~(EL m xs = EL n xs)))`,
     REPEAT GEN_TAC THEN EQ_TAC THENL
      [DISCH_TAC THEN
       MP_TAC(SPEC `\n. n < LENGTH (xs:A list) /\ EL n xs = x`
         num_WOP) THEN
       REWRITE_TAC[] THEN
       DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
       ANTS_TAC THENL
        [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[MEM_EXISTS_EL]) THEN
         MESON_TAC[];
         ALL_TAC] THEN
       DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
       EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
       X_GEN_TAC `m:num` THEN DISCH_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
       ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC(TAUT `p ==> (~(p /\ q) ==> ~q)`) THEN
       ASM_ARITH_TAC;
       DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
       REWRITE_TAC[MEM_EXISTS_EL] THEN EXISTS_TAC `n:num` THEN
       ASM_REWRITE_TAC[]]) in
   MATCH_ACCEPT_TAC lemma);;

let ALOOKUP_ZIP_EL = cake_theorem "ALOOKUP_ZIP_EL"
  (fun () ->
    `!xs hs n.
        n < LENGTH xs /\ LENGTH hs = LENGTH xs /\
        (!m. m < n ==> ~(EL m xs = EL n xs)) ==>
        ALOOKUP (ZIP xs hs) (EL n xs) = SOME (EL n hs)`)
  (* the lookup of the nth key walks past the n keys before it,
     which the hypothesis says are not that key, and the pair that
     the zip has there is the nth key with the nth value *)
  (let split = prove
    (`!(h:A) t k. (!m. m < SUC k ==> ~(EL m (CONS h t) = EL k t))
        ==> ~(h = EL k t) /\ (!m. m < k ==> ~(EL m t = EL k t))`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
      [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
       REWRITE_TAC[LT_0; EL; HD];
       GEN_TAC THEN DISCH_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `SUC m`) THEN
       REWRITE_TAC[EL; TL; LT_SUC] THEN ASM_REWRITE_TAC[]]) in
   LIST_INDUCT_TAC THENL
    [REWRITE_TAC[LENGTH; ARITH_RULE `((n:num) < 0) <=> F`];
     (fun (asl,w as gl) ->
        let hsv = fst(dest_forall w) in
        (X_GEN_TAC hsv THEN
         STRUCT_CASES_TAC(ISPEC hsv list_CASES_v)) gl) THEN
     GEN_TAC THEN
     STRUCT_CASES_TAC(ISPEC `n:num` num_CASES) THEN
     REWRITE_TAC[LENGTH; ZIP; ALOOKUP; EL; HD; TL; FST; SND;
                 ARITH_RULE `(0 = SUC n) <=> F`;
                 ARITH_RULE `(SUC n = 0) <=> F`] THEN
     TRY(CONV_TAC TAUT) THEN
     STRIP_TAC THEN
     FIRST_ASSUM(fun th -> STRIP_ASSUME_TAC (MATCH_MP split th)) THEN
     ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
     ASM_REWRITE_TAC[]]);;

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
  (* the witnesses of the goal's existential are the ones the
     assumption has: HOL4's asm_exists_tac, ml/lib/tactics.ml *)
  (REWRITE_TAC[cake_def "memory_rel"] THEN REPEAT STRIP_TAC THEN
   ASM_EXISTS_TAC THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(fun th -> MP_TAC th THEN
     MATCH_MP_TAC word_ml_inv_rearrange) THEN
   ASM_REWRITE_TAC[]);;

let memory_rel_tl = cake_theorem "memory_rel_tl"
  (fun () ->
    `memory_rel c be ts refs sp st m dm (x :: xs) ==>
     memory_rel c be ts refs sp st m dm xs`)
  (* the source's match_mp_tac takes the lemma's second antecedent
     for the goal's; HOL Light's takes the conclusion, so the two
     antecedents are swapped first and the assumption discharges
     the one that says what the memory holds *)
  (DISCH_TAC THEN
   FIRST_ASSUM(fun th ->
     MATCH_MP_TAC(MATCH_MP
       (ONCE_REWRITE_RULE[TAUT `(p ==> q ==> r) <=> (q ==> p ==> r)`]
          memory_rel_rearrange) th)) THEN
   REWRITE_TAC[MEM] THEN MESON_TAC[]);;

let word_ml_inv_Unit = cake_theorem "word_ml_inv_Unit"
  (fun () ->
    `word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs ws /\
      good_dimindex (:'a) ==>
      word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
        ((Unit,wordLang_Word ((n2w 2):'a word)) :: ws)`)
  (* Unit is the empty Block of the tuple tag, which cons_thm_EMPTY
     puts on the stack with the root Data (Word (BlockNil 0)), and
     that word is two, whose lowest bit word_addr takes off *)
  (let blocknil0 = prove
    (`BlockNil 0 = (n2w 2:'a word)`,
     REWRITE_TAC[cake_def "BlockNil"] THEN CONV_TAC WORD_RULE) in
   let and2 = prove
    (`(n2w 2:(N)word) && word_not (n2w 1) = n2w 2`,
     WORD_NUM_BIT_TAC 2) in
   let dimword16 = prove
    (`good_dimindex (:'a) ==> 0 < dimword (:'a) DIV 16`,
     REWRITE_TAC[cake_def "good_dimindex"; dimword] THEN
     DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
     CONV_TAC NUM_REDUCE_CONV) in
   let waddr = hd (word_addr_clauses ()) in
   let cons0 = REWRITE_RULE[blocknil0]
     (INST [`0`,`tag:num`] (cake_thm "cons_thm_EMPTY")) in
   REWRITE_TAC[cake_def "word_ml_inv"] THEN REPEAT STRIP_TAC THEN
   EXISTS_TAC
     `CONS (gc_shared_Data (wordLang_Word (n2w 2:'a word))) hs` THEN
   REWRITE_TAC[MAP; ALL2; waddr; and2] THEN
   ASM_REWRITE_TAC[cake_def "dataSem_Unit";
                   cake_def "tuple_tag"] THEN
   MATCH_MP_TAC cons0 THEN
   ASM_SIMP_TAC[dimword16]);;

let memory_rel_Unit = cake_theorem "memory_rel_Unit"
  (fun () ->
    `memory_rel c be ts refs sp st m dm xs /\ good_dimindex (:'a) ==>
     memory_rel c be ts refs sp st m dm ((Unit,wordLang_Word
       ((n2w 2):'a word)) :: xs)`)
  (REWRITE_TAC[cake_def "memory_rel"] THEN REPEAT STRIP_TAC THEN
   ASM_EXISTS_TAC THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC word_ml_inv_Unit THEN ASM_REWRITE_TAC[]);;

let get_lowerbits_LSL_shift_length =
  cake_theorem "get_lowerbits_LSL_shift_length"
  (fun () ->
    `get_lowerbits conf a >>> shift_length conf = (n2w 0)`)
  (* the lower bits are below small_shift_length, which is below
     shift_length, so the shift leaves nothing *)
  (CASES_ON_NAME "a" THEN
   REWRITE_TAC[cake_def "get_lowerbits"] THEN MATCH_REDUCE_TAC THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_0; BIT_WORD_USHR;
               BIT_WORD_OR; BIT_WORD_1; word_bits; BIT_WORD_SUBWORD;
               cake_def "small_shift_length";
               cake_def "shift_length"] THEN
   REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

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
  (* the lowest bit of a word, or one, is one *)
  (GEN_TAC THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR; word_bits;
               BIT_WORD_SUBWORD; BIT_WORD_1] THEN
   X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   TRY(REWRITE_TAC[ARITH_RULE `0 < d <=> 1 <= d`; DIMINDEX_GE_1]) THEN
   POP_ASSUM_LIST(fun ths -> MAP_EVERY MP_TAC ths) THEN ARITH_TAC);;

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
  (* the offset of an index is four times it, which a dimindex of
     32 adds to the bytes in a word as it stands and one of 64
     doubles first *)
  (let shl1 = prove
    (`!(v:(N)word). word_shl v 1 = word 2 * v`,
     REWRITE_TAC[word_shl; GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD] THEN
     CONV_TAC MOD_DOWN_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[MULT_AC]) in
   REWRITE_TAC[cake_def "good_dimindex"; cake_def "get_real_offset";
               cake_def "bytes_in_word"] THEN
   DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[injectivity "option"; shl1; WORD_MUL] THEN
   CONV_TAC WORD_RULE);;

let word_heap_APPEND = cake_theorem "word_heap_APPEND"
  (fun () ->
    `!xs ys a.
        word_heap a (xs ++ ys) conf =
        word_heap a xs conf *
        word_heap (a + bytes_in_word * n2w (heap_length xs)) ys
          conf`)
  (* the address of the second half is the first address shifted by
     the length of the first half, which is a word ring identity *)
  (LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC[APPEND; cake_def "word_heap"; heap_length_NIL;
                   heap_length_CONS; emp_STAR; STAR_ASSOC;
                   WORD_ADD_MUL_SPLIT; WORD_ADD_MUL_0]);;

let FORALL_WORD = cake_theorem "FORALL_WORD"
  (fun () ->
    `(!(v:'a word). P v) <=> (!n. n < dimword (:'a) ==> P (n2w n))`)
  (EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   ONCE_REWRITE_TAC[GSYM WORD_VAL] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   REWRITE_TAC[dimword; VAL_BOUND]);;

let BlockNil_and_lemma = cake_theorem "BlockNil_and_lemma"
  (fun () ->
    `good_dimindex (:'a) ==>
      (--(n2w 2) && (n2w 16) * tag + (n2w 2)) = (n2w 16) * tag +
        ((n2w 2):'a word)`)
  (* sixteen times a word has its four lowest bits clear, so the
     and with the complement of one leaves it alone; the port reads
     the statement as the and of that complement with the multiple
     of sixteen, and HOL4 as the and with the sum, because the two
     give the bitwise operators another precedence (see ISSUES.md,
     "The precedence of a word's bitwise operators") -- both are
     true, and this is the one the port states *)
  (let shl16 = prove
    (`!(v:(N)word). word 16 * v = word_shl v 4`,
     REWRITE_TAC[word_shl; GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD] THEN
     CONV_TAC MOD_DOWN_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[MULT_AC]) in
   let not1 = WORD_RULE `--(word 2):(N)word = word_not (word 1)` in
   DISCH_TAC THEN
   REWRITE_TAC[shl16; not1] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_NOT;
               BIT_WORD_1; BIT_WORD_SHL] THEN
   X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   ASM_CASES_TAC `(i:num) = 0` THEN ASM_REWRITE_TAC[] THEN
   CONV_TAC NUM_REDUCE_CONV THEN TRY(CONV_TAC TAUT));;

let word_ml_inv_num_lemma = cake_theorem "word_ml_inv_num_lemma"
  (fun () ->
    `good_dimindex (:'a) ==> (--(n2w 2) && (n2w 4) * v) = (n2w 4) *
  (v:'a word)`)
  (* four times a word has its two lowest bits clear, and -2 is the
     complement of 1, which has only the lowest *)
  (let shl4 = prove
    (`!(v:(N)word). word 4 * v = word_shl v 2`,
     REWRITE_TAC[word_shl; GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD] THEN
     CONV_TAC MOD_DOWN_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[MULT_AC]) in
   let neg2 = prove
    (`word_neg (word 2):(N)word = word_not (word 1)`,
     CONV_TAC WORD_RULE) in
   DISCH_TAC THEN
   REWRITE_TAC[neg2; shl4] THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_NOT;
               BIT_WORD_1; BIT_WORD_SHL] THEN
   REPEAT STRIP_TAC THEN ASM_CASES_TAC `2 <= i` THEN
   ASM_REWRITE_TAC[] THEN
   ASM_SIMP_TAC[ARITH_RULE `2 <= i ==> ~(i = 0)`]);;

let word_ml_inv_num = cake_theorem "word_ml_inv_num"
  (fun () ->
    `word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c (dataSem_state_refs
  s) ws /\
      good_dimindex (:'a) /\
      small_enough_int (&n) ==>
      word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c
        (dataSem_state_refs s)
        ((Number (&n),wordLang_Word (n2w (4 * n):'a word)) :: ws)`)
  CHEAT_TAC;;

(* HOL4 data_to_word_memoryProofScript.sml:8032-8033: a theorem that
   HOL4 states as the value of an ML expression: word_ml_inv_zero *)

let word_ml_inv_neg_num_lemma = cake_theorem "word_ml_inv_neg_num_lemma"
  (fun () ->
    `good_dimindex (:'a) ==> (--(n2w 2) && --(n2w 4) * v) = --(n2w 4)
  * (v:'a word)`)
  (* and so does minus four times a word *)
  (let shl4 = prove
    (`!(v:(N)word). word 4 * v = word_shl v 2`,
     REWRITE_TAC[word_shl; GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD] THEN
     CONV_TAC MOD_DOWN_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[MULT_AC]) in
   let neg2 = prove
    (`word_neg (word 2):(N)word = word_not (word 1)`,
     CONV_TAC WORD_RULE) in
   let nshl4 = prove
    (`!(v:(N)word). word_neg (word 4) * v = word_shl (word_neg v) 2`,
     REWRITE_TAC[GSYM shl4] THEN CONV_TAC WORD_RULE) in
   DISCH_TAC THEN
   REWRITE_TAC[neg2; nshl4] THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_NOT;
               BIT_WORD_1; BIT_WORD_SHL] THEN
   REPEAT STRIP_TAC THEN ASM_CASES_TAC `2 <= i` THEN
   ASM_REWRITE_TAC[] THEN
   ASM_SIMP_TAC[ARITH_RULE `2 <= i ==> ~(i = 0)`]);;

let word_ml_inv_neg_num = cake_theorem "word_ml_inv_neg_num"
  (fun () ->
    `word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c (dataSem_state_refs
  s) ws /\
      good_dimindex (:'a) /\
      small_enough_int (--(&n)) /\ ~(n = 0) ==>
      word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c
        (dataSem_state_refs s)
        ((Number (--(&n)),wordLang_Word (--(n2w (4 * n):'a
          word))) :: ws)`)
  (* the root of a negative small number is the Data of its
     Smallnum, which is minus four times the number; its two lowest
     bits are clear, so the complement of one takes nothing off, and
     abs_ml_inv_Num adds the Number to the stack once the bound of
     small_enough_int gives the one of small_int *)
  (
   let waddr = hd (word_addr_clauses ()) in
   let smallneg = prove
    (`~(n = 0) ==> Smallnum (--(&n)) = --(n2w (4 * n)):'a word`,
     DISCH_TAC THEN REWRITE_TAC[cake_def "Smallnum"] THEN
     SUBGOAL_THEN `--(&n) < (&0:int)` (fun th -> REWRITE_TAC[th]) THENL
      [SUBGOAL_THEN `(&0:int) < &n` MP_TAC THENL
        [REWRITE_TAC[INT_OF_NUM_LT] THEN ASM_ARITH_TAC;
         INT_ARITH_TAC];
       ALL_TAC] THEN
     SUBGOAL_THEN `num_of_int (&4 * (&0 - --(&n))) = 4 * n`
       SUBST1_TAC THENL
      [REWRITE_TAC[INT_ARITH `&0 - --(&n) = &n:int`;
                   INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM];
       CONV_TAC WORD_RULE]) in
   let andneg = prove
    (`(--(n2w (4 * n)):(N)word) && word_not (n2w 1) =
       --(n2w (4 * n))`,
     let shl4 = prove
      (`!(v:(N)word). word 4 * v = word_shl v 2`,
       REWRITE_TAC[word_shl; GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD] THEN
       CONV_TAC MOD_DOWN_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
       REWRITE_TAC[MULT_AC]) in
     let nshl = prove
      (`!(k:num). --(n2w (4 * k)):(N)word = word_shl (--(n2w k)) 2`,
       GEN_TAC THEN REWRITE_TAC[GSYM shl4] THEN CONV_TAC WORD_RULE) in
     let and_shl = prove
      (`!(v:(N)word). word_shl v 2 && word_not (word 1) =
                      word_shl v 2`,
       REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_NOT;
                   BIT_WORD_1; BIT_WORD_SHL] THEN
       REPEAT STRIP_TAC THEN ASM_CASES_TAC `2 <= i` THEN
       ASM_REWRITE_TAC[] THEN
       ASM_SIMP_TAC[ARITH_RULE `2 <= i ==> ~(i = 0)`]) in
     ONCE_REWRITE_TAC[nshl] THEN MATCH_ACCEPT_TAC and_shl) in
   let smalln = prove
    (`good_dimindex (:'a) /\ small_enough_int (--(&n))
        ==> small_int (:'a) (--(&n))`,
     REWRITE_TAC[cake_def "good_dimindex"; cake_def "small_int";
                 cake_def "small_enough_int"; dimword] THEN
     DISCH_THEN(CONJUNCTS_THEN2
       (DISJ_CASES_THEN SUBST1_TAC) MP_TAC) THEN
     CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC) in
   REWRITE_TAC[cake_def "word_ml_inv"] THEN REPEAT STRIP_TAC THEN
   EXISTS_TAC
     `CONS (gc_shared_Data (wordLang_Word
        (Smallnum (--(&n)):'a word))) hs` THEN
   REWRITE_TAC[MAP; ALL2; waddr] THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC (cake_thm "abs_ml_inv_Num") THEN
     ASM_SIMP_TAC[smalln];
     ASM_SIMP_TAC[smallneg] THEN REWRITE_TAC[andneg];
     FIRST_ASSUM ACCEPT_TAC]);;

let word_list_APPEND = cake_theorem "word_list_APPEND"
  (fun () ->
    `!xs ys a. misc_word_list a (xs ++ ys) =
                misc_word_list a xs * misc_word_list (a + n2w
                  (LENGTH xs) * bytes_in_word) ys`)
  (LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC[APPEND; cake_def "misc_word_list"; LENGTH;
                   emp_STAR; STAR_ASSOC; WORD_ADD_SUC_MUL;
                   WORD_ADD_0_MUL]);;

let all_ts_head_eq = cake_theorem "all_ts_head_eq"
  (fun () ->
    `!v refs stack' ts.
      v IN all_vs refs stack' ==> all_ts refs stack' = all_ts
        refs (v :: stack')`)
  (* a value that the refs or the stack already hold adds no
     timestamp to the stack, which is what MEM_in_all_ts says of
     the value itself and all_ts_head of the head of a stack *)
  (REPEAT GEN_TAC THEN DISCH_TAC THEN
   ONCE_REWRITE_TAC[all_ts_head] THEN
   MATCH_MP_TAC(SET_RULE `s SUBSET t ==> t = s UNION t`) THEN
   REWRITE_TAC[SUBSET] THEN X_GEN_TAC `u:num` THEN
   REWRITE_TAC[cake_def "all_ts"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[IN_ELIM_THM; MEM] THEN
   DISCH_THEN(X_CHOOSE_THEN `y:dataSem_v`
     (CONJUNCTS_THEN2
        (DISJ_CASES_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM))
        ASSUME_TAC)) THENL
    [EXISTS_TAC `y:dataSem_v` THEN ASM_REWRITE_TAC[];
     MP_TAC(SPECL [`y:dataSem_v`; `u:num`; `stack':(dataSem_v)list`;
                   `refs:(dataSem_v bvlSem_ref) spt`]
       MEM_in_all_ts) THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[cake_def "all_ts"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[IN_ELIM_THM]]);;

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
  (let hd_is n t =
   (try fst(dest_const(fst(strip_comb t))) = n
    with Failure _ -> false) in
 let rec facs t =
   if hd_is "STAR" t then
     let args = snd(strip_comb t) in
     facs (el 0 args) @ facs (el 1 args)
   else [t] in
 let rec remove1 t = function
     [] -> []
   | h :: rest -> if h = t then rest else h :: remove1 t rest in
 let grab asl p =
   tryfind (fun (_,th) ->
     if (try p th with Failure _ -> false) then th else fail())
     asl in
 let is_hl th = hd_is "heap_lookup" (lhs (concl th)) in
 let swapmul a =
   let args = snd(strip_comb (rand a)) in
   let mul = fst(strip_comb (rand a)) in
   mk_comb(rator a, mk_comb(mk_comb(mul,el 1 args),el 0 args)) in
 let realaddr =
   W(fun (asl,w) ->
     let hl = grab asl is_hl in
     let hlen = grab asl (fun th ->
       hd_is "heap_length" (lhand (concl th))) in
     let cu = grab asl (fun th ->
       hd_is "FLOOKUP" (lhs (concl th)) &&
       fst(dest_const(rand(lhs(concl th)))) = "CurrHeap") in
     let gd = grab asl (fun th ->
       hd_is "good_dimindex" (concl th)) in
     let gat = tryfind (fun t ->
       find_term (fun u ->
         hd_is "get_addr" u && length (snd(strip_comb u)) = 3) t)
       (w :: map (fun (_,th) -> concl th) asl) in
     let mm = MATCH_MP (cake_thm "get_real_addr_get_addr")
                (CONJ hlen (CONJ hl (CONJ cu gd))) in
     let wv = find (fun v -> fst(dest_var v) = "w")
                (frees (concl mm)) in
     let th = SPEC (last (snd(strip_comb gat))) (GEN wv mm) in
     let a = rand (rhs (concl (CONJUNCT1 th))) in
     EXISTS_TAC (swapmul a) THEN
     STRIP_ASSUME_TAC(REWRITE_RULE[WORD_RULE (mk_eq(a,swapmul a))]
                        th)) in
   let all2cons = prove
    (`!P h t (l:(A)list).
        ALL2 P l (CONS (h:B) t) <=>
        ?a b. l = CONS a b /\ P a h /\ ALL2 P b t`,
     REPEAT GEN_TAC THEN
     STRUCT_CASES_TAC(ISPEC `l:(A)list` list_CASES) THEN
     REWRITE_TAC[ALL2; NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]) in
   let addreq = WORD_RULE
     `!(a:(N)word) i.
        (a + bytes_in_word) + n2w i * bytes_in_word =
        a + bytes_in_word + bytes_in_word * n2w i` in
   (* the element of a heap that an address and an index name *)
   let heapel = prove
    (`!a u n (heap:(('a,'b)heap_element)list) xs l d y.
        heap_lookup a heap = SOME (DataElement xs l d) /\
        n < LENGTH xs /\
        heap_el (gc_shared_Pointer a u) n heap = (y,T)
        ==> y = EL n xs`,
     REPEAT GEN_TAC THEN
     DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
     REWRITE_TAC[cake_def "heap_el"] THEN
     MATCH_REDUCE_TAC THEN
     ASM_REWRITE_TAC[] THEN
     MATCH_REDUCE_TAC THEN
     ASM_REWRITE_TAC[PAIR_EQ] THEN
     REWRITE_TAC[injectivity "option"; injectivity "heap_element";
                 PAIR_EQ] THEN
     CONV_TAC(REDEPTH_CONV UNWIND_CONV) THEN
     REWRITE_TAC[EXISTS_UNIQUE_REFL; SELECT_REFL] THEN
     ASM_REWRITE_TAC[PAIR_EQ] THEN
     DISCH_THEN(ACCEPT_TAC o SYM)) in
   DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
   SUBGOAL_THEN `~(vals:(dataSem_v)list = [])` ASSUME_TAC THENL
    [DISCH_TAC THEN VAR_EQ_TAC THEN
     FIRST_X_ASSUM(fun th ->
       if (try hd_is "<" (concl th) with Failure _ -> false)
       then MP_TAC(REWRITE_RULE[LENGTH; LT] th) else fail()) THEN
     REWRITE_TAC[];
     ALL_TAC] THEN
   FIRST_ASSUM(fun mr ->
     if hd_is "memory_rel" (concl mr)
     then MP_TAC(REWRITE_RULE[cake_def "memory_rel";
                              cake_def "word_ml_inv"; MAP; FST] mr)
     else fail()) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   FIRST_X_ASSUM(fun a2 ->
     if hd_is "ALL2" (concl a2)
     then MP_TAC(REWRITE_RULE[MAP; all2cons] a2) else fail()) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   VAR_EQ_TAC THEN
   FIRST_ASSUM(fun am ->
     if hd_is "abs_ml_inv" (concl am)
     then MP_TAC(REWRITE_RULE[cake_def "abs_ml_inv";
                              cake_def "bc_stack_ref_inv"] am)
     else fail()) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   FIRST_X_ASSUM(fun a2 ->
     if hd_is "ALL2" (concl a2) &&
        can (find_term (hd_is "v_inv")) (concl a2)
     then MP_TAC(REWRITE_RULE[ALL2; NOT_CONS_NIL; HD; TL] a2)
     else fail()) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   FIRST_X_ASSUM(fun vi ->
     if hd_is "v_inv" (concl vi)
     then MP_TAC(REWRITE_RULE[cake_thm "v_inv_def"] vi)
     else fail()) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   FIRST_X_ASSUM(fun e ->
     if is_eq (concl e) && is_var (lhs (concl e)) &&
        hd_is "gc_shared_Pointer" (rhs (concl e))
     then SUBST_ALL_TAC e else fail()) THEN
   RULE_ASSUM_TAC(REWRITE_RULE(word_addr_clauses ())) THEN
   REWRITE_TAC(word_addr_clauses ()) THEN
   W(fun (asl,w) ->
     let vs,bod = strip_exists w in
     EXISTS_TAC (rand (lhs (hd (conjuncts bod))))) THEN
   REWRITE_TAC[] THEN
   FIRST_ASSUM(fun th ->
     if hd_is "heap_in_memory_store" (concl th)
     then MP_TAC(REWRITE_RULE[cake_def "heap_in_memory_store"] th)
     else fail()) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   realaddr THEN
   FIRST_ASSUM(fun lr ->
     if hd_is "ALL2" (concl lr) &&
        can (find_term (hd_is "v_inv")) (concl lr)
     then ASSUME_TAC(MATCH_MP LIST_REL_LENGTH lr) else fail()) THEN
   W(fun (asl,w) ->
     let lt = grab asl (fun th ->
       hd_is "<" (concl th) && hd_is "LENGTH" (rand (concl th))) in
     let le = grab asl (fun th ->
       hd_is "=" (concl th) && hd_is "LENGTH" (lhs (concl th)) &&
       hd_is "LENGTH" (rhs (concl th))) in
     MP_TAC(MATCH_MP (cake_thm "LESS_LENGTH")
              (REWRITE_RULE[le] lt))) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   VAR_EQ_TAC THEN
   W(fun (asl,w) ->
     MP_TAC(MATCH_MP (cake_thm "heap_lookup_SPLIT")
              (grab asl is_hl))) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   VAR_EQ_TAC THEN
   FIRST_X_ASSUM(fun th ->
     if (try hd_is "STAR" (rator (concl th)) with Failure _ -> false)
     then MP_TAC th else fail()) THEN
   REWRITE_TAC[cake_thm "word_heap_APPEND"; cake_def "word_heap";
               cake_def "BlockRep"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[cake_def "word_el"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[cake_def "word_payload"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[MAP_APPEND; MAP; cake_thm "word_list_APPEND";
               cake_def "misc_word_list"; LENGTH_MAP] THEN
   ASM_REWRITE_TAC[addreq] THEN
   W(fun (asl,w) ->
     let addr = lhand (hd (conjuncts (rand w))) in
     let pred = rator (lhand w) in
     let fs = facs pred in
     let one = find (fun t ->
       hd_is "set_sep_one" t && fst(dest_pair (rand t)) = addr) fs in
     let rest = remove1 one fs in
     let st = fst(strip_comb pred) in
     let mk a b = mk_comb(mk_comb(st,a),b) in
     SUBGOAL_THEN (mk_eq(pred, mk one (end_itlist mk rest)))
       SUBST1_TAC THENL [REWRITE_TAC[STAR_AC]; ALL_TAC]) THEN
   DISCH_THEN(fun sep ->
     STRIP_ASSUME_TAC(MATCH_MP read_fun2set sep)) THEN
   ASM_REWRITE_TAC[] THEN
   W(fun (asl,w) ->
     let am = grab asl (fun th -> hd_is "abs_ml_inv" (concl th)) in
     let lt = grab asl (fun th ->
       hd_is "<" (concl th) &&
       hd_is "LENGTH" (rand (concl th)) &&
       fst(dest_var(rand(rand(concl th)))) = "vals") in
     MP_TAC(MATCH_MP (cake_thm "el_thm") (CONJ am lt))) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[CONS_11]) THEN
   REPEAT(FIRST_X_ASSUM(fun th ->
     if is_conj (concl th) then STRIP_ASSUME_TAC th else fail())) THEN
   VAR_EQ_TAC THEN
   W(fun (asl,w) ->
     let hl = REWRITE_RULE[cake_def "BlockRep"] (grab asl is_hl) in
     let he = REWRITE_RULE[cake_def "BlockRep"]
                (grab asl (fun th ->
                   hd_is "heap_el" (lhs (concl th)))) in
     let le = grab asl (fun th ->
       hd_is "=" (concl th) && hd_is "LENGTH" (lhs (concl th)) &&
       hd_is "LENGTH" (rhs (concl th))) in
     let n = el 1 (snd(strip_comb (lhs (concl he)))) in
     let lt = prove(mk_binop `(<):num->num->bool` n
                      (rhs (concl le)),
                    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
                    ARITH_TAC) in
     SUBST_ALL_TAC(REWRITE_RULE[EL_APPEND; LT_REFL; SUB_REFL; EL; HD]
       (MATCH_MP heapel (CONJ hl (CONJ lt he))))) THEN
   REWRITE_TAC[cake_def "memory_rel"] THEN
   W(fun (asl,w) ->
     let hm = grab asl (fun th ->
       hd_is "heap_in_memory_store" (concl th)) in
     let args = snd(strip_comb (concl hm)) in
     EXISTS_TAC (el 0 args) THEN EXISTS_TAC (el 9 args) THEN
     EXISTS_TAC (el 1 args) THEN EXISTS_TAC (el 2 args) THEN
     EXISTS_TAC (el 3 args) THEN EXISTS_TAC (el 4 args)) THEN
   ASM_REWRITE_TAC[cake_def "word_ml_inv"] THEN
   REWRITE_TAC[MAP; FST; SND] THEN
   W(fun (asl,w) ->
     let am = grab asl (fun th ->
       hd_is "abs_ml_inv" (concl th) &&
       hd_is "EL" (lhand (el 1 (snd(strip_comb (concl th)))))) in
     EXISTS_TAC
       (fst(dest_pair (el 3 (snd(strip_comb (concl am))))))) THEN
   ASM_REWRITE_TAC[MAP; ALL2; HD; TL; NOT_CONS_NIL] THEN
   REWRITE_TAC(word_addr_clauses ()));;

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
  (DISCH_TAC THEN
   FIRST_ASSUM(fun th ->
     MATCH_MP_TAC(MATCH_MP
       (ONCE_REWRITE_RULE[TAUT `(p ==> q ==> r) <=> (q ==> p ==> r)`]
          memory_rel_rearrange) th)) THEN
   REWRITE_TAC[MEM] THEN MESON_TAC[]);;

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
  (* an element of a reference's array, read out of the memory: the
     same shape as memory_rel_El', with bc_ref_inv's RefBlock in
     place of the Block's BlockRep and deref_thm in place of
     el_thm.  The thunk rules of v_inv are out because the
     reference holds a ValueArray, and the address of the element
     is the pointer of the root, which is not a variable here, so
     the heap's split has to be substituted by hand *)
  (let hd_is n t =
   (try fst(dest_const(fst(strip_comb t))) = n
    with Failure _ -> false) in
 let rec facs t =
   if hd_is "STAR" t then
     let args = snd(strip_comb t) in
     facs (el 0 args) @ facs (el 1 args)
   else [t] in
 let rec remove1 t = function
     [] -> []
   | h :: rest -> if h = t then rest else h :: remove1 t rest in
 let grab asl p =
   tryfind (fun (_,th) ->
     if (try p th with Failure _ -> false) then th else fail())
     asl in
 let is_hl th = hd_is "heap_lookup" (lhs (concl th)) in
 let killthunk =
   TRY(FIRST_ASSUM(fun t1 -> FIRST_ASSUM(fun t2 ->
     CONTR_TAC(REWRITE_RULE[injectivity "option";
                            distinctness "bvlSem_ref"]
                 (TRANS (SYM t1) t2))))) in
 let refinv ptr root =
   FIRST_X_ASSUM(fun th ->
     if is_forall (concl th) &&
        hd_is "bc_ref_inv" (rand (snd(strip_forall(concl th))))
     then MP_TAC(SPEC ptr th) else fail()) THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL
      [REWRITE_TAC[cake_def "reachable_refs"; MEM] THEN
       EXISTS_TAC root THEN EXISTS_TAC ptr THEN
       REWRITE_TAC[cake_def "get_refs"; MEM;
                   CONJUNCT1(SPEC_ALL RTC_RULES)];
       ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   REWRITE_TAC[cake_def "bc_ref_inv"] THEN
   ASM_SIMP_TAC[FLOOKUP_DEF] THEN
   MATCH_REDUCE_TAC in
 let swapmul a =
   let args = snd(strip_comb (rand a)) in
   let mul = fst(strip_comb (rand a)) in
   mk_comb(rator a, mk_comb(mk_comb(mul,el 1 args),el 0 args)) in
 let realaddr =
   W(fun (asl,w) ->
     let hl = grab asl is_hl in
     let hlen = grab asl (fun th ->
       hd_is "heap_length" (lhand (concl th))) in
     let cu = grab asl (fun th ->
       hd_is "FLOOKUP" (lhs (concl th)) &&
       fst(dest_const(rand(lhs(concl th)))) = "CurrHeap") in
     let gd = grab asl (fun th ->
       hd_is "good_dimindex" (concl th)) in
     let gat = tryfind (fun t ->
       find_term (fun u ->
         hd_is "get_addr" u && length (snd(strip_comb u)) = 3) t)
       (w :: map (fun (_,th) -> concl th) asl) in
     let mm = MATCH_MP (cake_thm "get_real_addr_get_addr")
                (CONJ hlen (CONJ hl (CONJ cu gd))) in
     let wv = find (fun v -> fst(dest_var v) = "w")
                (frees (concl mm)) in
     let th = SPEC (last (snd(strip_comb gat))) (GEN wv mm) in
     let a = rand (rhs (concl (CONJUNCT1 th))) in
     EXISTS_TAC (swapmul a) THEN
     STRIP_ASSUME_TAC(REWRITE_RULE[WORD_RULE (mk_eq(a,swapmul a))]
                        th)) in
   let all2cons = prove
    (`!P h t (l:(A)list).
        ALL2 P l (CONS (h:B) t) <=>
        ?a b. l = CONS a b /\ P a h /\ ALL2 P b t`,
     REPEAT GEN_TAC THEN
     STRUCT_CASES_TAC(ISPEC `l:(A)list` list_CASES) THEN
     REWRITE_TAC[ALL2; NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]) in
   let addreq = WORD_RULE
     `!(a:(N)word) i.
        (a + bytes_in_word) + n2w i * bytes_in_word =
        a + bytes_in_word + bytes_in_word * n2w i` in
   (* the element of a heap that an address and an index name *)
   let heapel = prove
    (`!a u n (heap:(('a,'b)heap_element)list) xs l d y.
        heap_lookup a heap = SOME (DataElement xs l d) /\
        n < LENGTH xs /\
        heap_el (gc_shared_Pointer a u) n heap = (y,T)
        ==> y = EL n xs`,
     REPEAT GEN_TAC THEN
     DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
     REWRITE_TAC[cake_def "heap_el"] THEN
     MATCH_REDUCE_TAC THEN
     ASM_REWRITE_TAC[] THEN
     MATCH_REDUCE_TAC THEN
     ASM_REWRITE_TAC[PAIR_EQ] THEN
     REWRITE_TAC[injectivity "option"; injectivity "heap_element";
                 PAIR_EQ] THEN
     CONV_TAC(REDEPTH_CONV UNWIND_CONV) THEN
     REWRITE_TAC[EXISTS_UNIQUE_REFL; SELECT_REFL] THEN
     ASM_REWRITE_TAC[PAIR_EQ] THEN
     DISCH_THEN(ACCEPT_TAC o SYM)) in
   DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
   SUBGOAL_THEN `~(vals:(dataSem_v)list = [])` ASSUME_TAC THENL
    [DISCH_TAC THEN VAR_EQ_TAC THEN
     FIRST_X_ASSUM(fun th ->
       if (try hd_is "<" (concl th) with Failure _ -> false)
       then MP_TAC(REWRITE_RULE[LENGTH; LT] th) else fail()) THEN
     REWRITE_TAC[];
     ALL_TAC] THEN
   FIRST_ASSUM(fun mr ->
     if hd_is "memory_rel" (concl mr)
     then MP_TAC(REWRITE_RULE[cake_def "memory_rel";
                              cake_def "word_ml_inv"; MAP; FST] mr)
     else fail()) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   FIRST_X_ASSUM(fun a2 ->
     if hd_is "ALL2" (concl a2)
     then MP_TAC(REWRITE_RULE[MAP; all2cons] a2) else fail()) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   VAR_EQ_TAC THEN
   FIRST_ASSUM(fun am ->
     if hd_is "abs_ml_inv" (concl am)
     then MP_TAC(REWRITE_RULE[cake_def "abs_ml_inv";
                              cake_def "bc_stack_ref_inv"] am)
     else fail()) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   FIRST_X_ASSUM(fun a2 ->
     if hd_is "ALL2" (concl a2) &&
        can (find_term (hd_is "v_inv")) (concl a2)
     then MP_TAC(REWRITE_RULE[ALL2; NOT_CONS_NIL; HD; TL] a2)
     else fail()) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   FIRST_X_ASSUM(fun vi ->
     if hd_is "v_inv" (concl vi)
     then MP_TAC(REWRITE_RULE[cake_thm "v_inv_def"] vi)
     else fail()) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   killthunk THEN
   FIRST_X_ASSUM(fun e ->
     if is_eq (concl e) && is_var (lhs (concl e)) &&
        hd_is "gc_shared_Pointer" (rhs (concl e))
     then SUBST_ALL_TAC e else fail()) THEN
   RULE_ASSUM_TAC(REWRITE_RULE(word_addr_clauses ())) THEN
   REWRITE_TAC(word_addr_clauses ()) THEN
   W(fun (asl,w) ->
     let vs,bod = strip_exists w in
     EXISTS_TAC (rand (lhs (hd (conjuncts bod))))) THEN
   REWRITE_TAC[] THEN
   refinv `nn:num` `RefPtr bl nn:dataSem_v` THEN
   ASM_REWRITE_TAC[] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   FIRST_ASSUM(fun th ->
     if hd_is "heap_in_memory_store" (concl th)
     then MP_TAC(REWRITE_RULE[cake_def "heap_in_memory_store"] th)
     else fail()) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   realaddr THEN
   FIRST_ASSUM(fun lr ->
     if hd_is "ALL2" (concl lr) &&
        can (find_term (hd_is "v_inv")) (concl lr)
     then ASSUME_TAC(MATCH_MP LIST_REL_LENGTH lr) else fail()) THEN
   W(fun (asl,w) ->
     let lt = grab asl (fun th ->
       hd_is "<" (concl th) && hd_is "LENGTH" (rand (concl th))) in
     let le = grab asl (fun th ->
       hd_is "=" (concl th) && hd_is "LENGTH" (lhs (concl th)) &&
       hd_is "LENGTH" (rhs (concl th))) in
     MP_TAC(MATCH_MP (cake_thm "LESS_LENGTH")
              (REWRITE_RULE[GSYM le] lt))) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   VAR_EQ_TAC THEN
   W(fun (asl,w) ->
     MP_TAC(MATCH_MP (cake_thm "heap_lookup_SPLIT")
              (grab asl is_hl))) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   VAR_EQ_TAC THEN
   TRY(FIRST_X_ASSUM(fun th ->
     if (try hd_is "fmap_apply" (lhs (concl th))
         with Failure _ -> false)
     then SUBST_ALL_TAC th else fail())) THEN
   FIRST_X_ASSUM(fun th ->
     if (try hd_is "STAR" (rator (concl th)) with Failure _ -> false)
     then MP_TAC th else fail()) THEN
   REWRITE_TAC[cake_thm "word_heap_APPEND"; cake_def "word_heap";
               cake_def "RefBlock"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[cake_def "word_el"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[cake_def "word_payload"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[MAP_APPEND; MAP; cake_thm "word_list_APPEND";
               cake_def "misc_word_list"; LENGTH_MAP] THEN
   ASM_REWRITE_TAC[addreq] THEN
   W(fun (asl,w) ->
     let addr = lhand (hd (conjuncts (rand w))) in
     let pred = rator (lhand w) in
     let fs = facs pred in
     let one = find (fun t ->
       hd_is "set_sep_one" t && fst(dest_pair (rand t)) = addr) fs in
     let rest = remove1 one fs in
     let st = fst(strip_comb pred) in
     let mk a b = mk_comb(mk_comb(st,a),b) in
     SUBGOAL_THEN (mk_eq(pred, mk one (end_itlist mk rest)))
       SUBST1_TAC THENL [REWRITE_TAC[STAR_AC]; ALL_TAC]) THEN
   DISCH_THEN(fun sep ->
     STRIP_ASSUME_TAC(MATCH_MP read_fun2set sep)) THEN
   ASM_REWRITE_TAC[] THEN
   W(fun (asl,w) ->
     let am = grab asl (fun th -> hd_is "abs_ml_inv" (concl th)) in
     MP_TAC(MATCH_MP (cake_thm "deref_thm") am)) THEN
   ASM_REWRITE_TAC[THE] THEN
   MATCH_REDUCE_TAC THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   W(fun (asl,w) ->
     let fa = grab asl (fun th ->
       is_forall (concl th) &&
       can (find_term (hd_is "heap_el")) (concl th)) in
     let lt = grab asl (fun th ->
       hd_is "<" (concl th) && hd_is "LENGTH" (rand (concl th))) in
     MP_TAC(MP (SPEC (lhand (concl lt)) fa) lt)) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[CONS_11]) THEN
   REPEAT(FIRST_X_ASSUM(fun th ->
     if is_conj (concl th) then STRIP_ASSUME_TAC th else fail())) THEN
   VAR_EQ_TAC THEN
   W(fun (asl,w) ->
     let hl = REWRITE_RULE[cake_def "RefBlock"] (grab asl is_hl) in
     let he = REWRITE_RULE[cake_def "RefBlock"]
                (grab asl (fun th ->
                   hd_is "heap_el" (lhs (concl th)))) in
     let n = el 1 (snd(strip_comb (lhs (concl he)))) in
     let len = el 1 (snd(strip_comb (rand (rhs (concl hl))))) in
     let lt = prove(mk_binop `(<):num->num->bool` n len,
                    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
                    ARITH_TAC) in
     SUBST_ALL_TAC(REWRITE_RULE[EL_APPEND; LT_REFL; SUB_REFL; EL; HD]
       (MATCH_MP heapel (CONJ hl (CONJ lt he))))) THEN
   REWRITE_TAC[cake_def "memory_rel"] THEN
   W(fun (asl,w) ->
     let hm = grab asl (fun th ->
       hd_is "heap_in_memory_store" (concl th)) in
     let args = snd(strip_comb (concl hm)) in
     EXISTS_TAC (el 0 args) THEN EXISTS_TAC (el 9 args) THEN
     EXISTS_TAC (el 1 args) THEN EXISTS_TAC (el 2 args) THEN
     EXISTS_TAC (el 3 args) THEN EXISTS_TAC (el 4 args)) THEN
   ASM_REWRITE_TAC[cake_def "word_ml_inv"] THEN
   REWRITE_TAC[MAP; FST; SND] THEN
   W(fun (asl,w) ->
     let am = grab asl (fun th ->
       hd_is "abs_ml_inv" (concl th) &&
       hd_is "EL" (lhand (el 1 (snd(strip_comb (concl th)))))) in
     EXISTS_TAC
       (fst(dest_pair (el 3 (snd(strip_comb (concl am))))))) THEN
   ASM_REWRITE_TAC[MAP; ALL2; HD; TL; NOT_CONS_NIL] THEN
   REWRITE_TAC(word_addr_clauses ()));;

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
  (let lrw = [LENGTH; CONS_11; NOT_CONS_NIL; LENGTH_EQ_NIL;
              EQ_SYM_EQ; ARITH_RULE `~(0 = 1)`;
              ARITH_RULE `(SUC n = 1) <=> (n = 0)`] in
   let aux = prove
    (`!xs:A list. (LENGTH xs = 1 <=> ?a1. xs = [a1]) /\
                  (1 = LENGTH xs <=> ?a1. xs = [a1])`,
     GEN_TAC THEN
     STRUCT_CASES_TAC(ISPEC `xs:A list` list_CASES_v) THEN
     REWRITE_TAC lrw THEN
     CONV_TAC(REDEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[]) in
   REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC aux);;

let LENGTH_EQ_2 = cake_theorem "LENGTH_EQ_2"
  (fun () ->
    `(LENGTH xs = 2 <=> (?a1 a2. xs = [a1; a2])) /\
      (2 = LENGTH xs <=> (?a1 a2. xs = [a1; a2]))`)
  (let lrw = [LENGTH; CONS_11; NOT_CONS_NIL; LENGTH_EQ_NIL;
              EQ_SYM_EQ; ARITH_RULE `~(0 = 1)`;
              ARITH_RULE `~(0 = 2)`;
              ARITH_RULE `(SUC n = 1) <=> (n = 0)`;
              ARITH_RULE `(SUC n = 2) <=> (n = 1)`] in
   let aux = prove
    (`!xs:A list. (LENGTH xs = 2 <=> ?a1 a2. xs = [a1; a2]) /\
                  (2 = LENGTH xs <=> ?a1 a2. xs = [a1; a2])`,
     GEN_TAC THEN
     STRUCT_CASES_TAC(ISPEC `xs:A list` list_CASES_v) THEN
     REWRITE_TAC lrw THEN
     TRY(CONV_TAC(REDEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[]) THEN
     STRUCT_CASES_TAC(ISPEC `vs:A list` list_CASES_v) THEN
     REWRITE_TAC lrw THEN
     CONV_TAC(REDEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[]) in
   REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC aux);;

let LENGTH_EQ_3 = cake_theorem "LENGTH_EQ_3"
  (fun () ->
    `(LENGTH xs = 3 <=> (?a1 a2 a3. xs = [a1; a2; a3])) /\
      (3 = LENGTH xs <=> (?a1 a2 a3. xs = [a1; a2; a3]))`)
  (* one element off the front and LENGTH_EQ_2 says the rest *)
  (let lrw = [LENGTH; CONS_11; NOT_CONS_NIL; LENGTH_EQ_NIL;
              EQ_SYM_EQ; ARITH_RULE `~(0 = 3)`;
              ARITH_RULE `(SUC n = 3) <=> (n = 2)`] in
   let aux = prove
    (`!xs:A list. (LENGTH xs = 3 <=> ?a1 a2 a3. xs = [a1; a2; a3]) /\
                  (3 = LENGTH xs <=> ?a1 a2 a3. xs = [a1; a2; a3])`,
     GEN_TAC THEN
     STRUCT_CASES_TAC(ISPEC `xs:A list` list_CASES_v) THEN
     REWRITE_TAC lrw THEN
     TRY(CONV_TAC(REDEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[]) THEN
     MATCH_ACCEPT_TAC(CONJUNCT1 LENGTH_EQ_2)) in
   REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC aux);;

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
  (REWRITE_TAC[heap_split_APPEND_if] THEN REPEAT GEN_TAC THEN
   COND_CASES_TAC THEN EVERY_CASE_TAC THEN
   ASM_REWRITE_TAC[injectivity "option"; distinctness "option";
                   PAIR_EQ] THEN
   MESON_TAC[]);;

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
  (* the store of the append stores xs and then ys, at the address
     that the length of xs moves on to *)
  (LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
   ASM_REWRITE_TAC[APPEND;
                   cake_def "data_to_word_memoryProof_store_list";
                   LENGTH; WORD_ADD_MUL_0; WORD_ADD_MUL_SUC] THEN
   TRY(COND_CASES_TAC) THEN
   ASM_REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
   MESON_TAC[]);;

let minus_lemma = cake_theorem "minus_lemma[local]"
  (fun () ->
    `--(n2w 1) * (bytes_in_word * w) = bytes_in_word * --w`)
  (CONV_TAC WORD_RULE);;

let n2w_lsr_eq_0 = cake_theorem "n2w_lsr_eq_0"
  (fun () ->
    `n DIV 2 EXP k = 0 /\ n < dimword (:'a) ==> n2w n >>> k = ((n2w
  0):'a word)`)
  (REPEAT STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[dimword]) THEN
   ASM_SIMP_TAC[GSYM VAL_EQ_0; VAL_WORD_USHR; VAL_WORD; MOD_LT]);;

let LESS_EXO_SUB = cake_theorem "LESS_EXO_SUB[local]"
  (fun () ->
    `n < 2 EXP (k - m) ==> n < 2 EXP k`)
  (DISCH_TAC THEN MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `2 EXP (k - m)` THEN
   ASM_REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ARITH_TAC);;

let LESS_EXO_SUB_ALT = cake_theorem "LESS_EXO_SUB_ALT[local]"
  (fun () ->
    `m <= k ==> n < 2 EXP (k - m) ==> n * 2 EXP m < 2 EXP k`)
  (REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `2 EXP k = 2 EXP (k - m) * 2 EXP m` SUBST1_TAC THENL
    [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
     ASM_REWRITE_TAC[LT_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ]]);;

let less_pow_dimindex_sub_imp =
  cake_theorem "less_pow_dimindex_sub_imp[local]"
  (fun () ->
    `n < 2 EXP (dimindex (:'a) - k) ==> n < dimword (:'a)`)
  (REWRITE_TAC[dimword] THEN MATCH_ACCEPT_TAC LESS_EXO_SUB);;

let encode_header_NEQ_0 = cake_theorem "encode_header_NEQ_0"
  (fun () ->
    `encode_header c n k = SOME w ==> ~(w = (n2w 0))`)
  (* the header has the lowest bit of its three set, and a word
     with a bit is not zero *)
  (REWRITE_TAC[cake_def "encode_header"] THEN
   COND_CASES_TAC THEN
   REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
   DISCH_THEN(SUBST1_TAC o SYM) THEN
   REWRITE_TAC[cake_def "make_header"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
   DISCH_THEN(MP_TAC o SPEC `0`) THEN
   REWRITE_TAC[BIT_WORD_OR; BIT_WORD_0; BIT_WORD] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[ARITH_RULE `0 < d <=> 1 <= d`; DIMINDEX_GE_1]);;

let encode_header_IMP = cake_theorem "encode_header_IMP[local]"
  (fun () ->
    `encode_header c tag len = SOME (hd:'a word) /\
  data_to_word_config_len_size
       c + 5 < dimindex (:'a) /\ good_dimindex (:'a) ==>
       len < 2 EXP (dimindex (:'a) - 4) /\
       decode_length c hd = n2w len`)
  (* what encode_header gives back is make_header of the tag and the
     length, so the length is the one of its condition and the shift
     down of decode_length undoes the shift up that make_header did:
     the tag and the three are below the shift, so the shift down
     loses them *)
  (let hi = prove
    (`!n r (i:num). n < 2 EXP r /\ r <= i
        ==> ~(bit i ((n2w n):'a word))`,
     MATCH_ACCEPT_TAC BIT_WORD_HI) in
   let b3 = prove
    (`!j. j < dimindex (:'a)
          ==> (bit j ((n2w 3):'a word) <=> j < 2)`,
     GEN_TAC THEN DISCH_TAC THEN
     ASM_CASES_TAC `(j:num) < 2` THEN ASM_REWRITE_TAC[] THENL
      [FIRST_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP
         (ARITH_RULE `(j:num) < 2 ==> j = 0 \/ j = 1`)) THEN
       ASM_REWRITE_TAC[BIT_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
       ASM_ARITH_TAC;
       MP_TAC(ISPECL [`3`; `2`; `j:num`] hi) THEN
       ASM_SIMP_TAC[ARITH_RULE `~((j:num) < 2) ==> 2 <= j`] THEN
       CONV_TAC NUM_REDUCE_CONV]) in
   REWRITE_TAC[cake_def "encode_header"] THEN
   COND_CASES_TAC THEN
   REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
   REPEAT(FIRST_X_ASSUM(fun th ->
     if is_conj (concl th) then STRIP_ASSUME_TAC th else fail())) THEN
   DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC) THEN
   CONJ_TAC THENL
    [FIRST_ASSUM ACCEPT_TAC;
     REWRITE_TAC[cake_def "decode_length"; cake_def "make_header"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     SUBGOAL_THEN
       `!j. bit j (((n2w tag) << 2 || (n2w 3)):'a word)
            ==> j < dimindex (:'a) -
                    data_to_word_config_len_size c`
       (fun th -> REWRITE_TAC[MATCH_MP USHR_OR_LOW th]) THENL
      [X_GEN_TAC `j:num` THEN
       REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL] THEN STRIP_TAC THENL
        [MP_TAC(ISPECL
           [`tag:num`;
            `dimindex (:'a) - data_to_word_config_len_size c - 2`;
            `j - 2`] hi) THEN
         ASM_REWRITE_TAC[] THEN ARITH_NO_BIT_TAC;
         MP_TAC(MATCH_MP b3 (ASSUME `j < dimindex (:'a)`)) THEN
         ASM_REWRITE_TAC[] THEN ARITH_NO_BIT_TAC];
       MATCH_MP_TAC USHR_SHL_CANCEL THEN
       X_GEN_TAC `j:num` THEN
       ASM_CASES_TAC `bit j ((n2w len):'a word)` THEN
       ASM_REWRITE_TAC[] THEN
       MP_TAC(ISPECL
         [`len:num`; `data_to_word_config_len_size c`; `j:num`] hi) THEN
       ASM_REWRITE_TAC[] THEN ARITH_NO_BIT_TAC]]);;

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
  (* three is the tag of an evaluated thunk, so the word is 8 or 6 *)
  (REWRITE_TAC[cake_def "thunk_tag_to_bits"] THEN
   MATCH_REDUCE_TAC THEN
   WORD_NUM_BIT_TAC 4);;

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
  (* the two clauses of word_list_exists: at zero it is emp, and at
     a successor it is the cell at the address beside the list of
     the rest -- the existential of the definition is over the list
     of the words, and the condition on its length picks the empty
     list or a cons *)
  (CONJ_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   REWRITE_TAC[cake_def "word_list_exists"] THEN
   REWRITE_TAC[STAR_SEP_EXISTS; SEP_EXISTS_THM] THEN
   REWRITE_TAC[STAR_ASSOC; STAR_cond] THEN
   REWRITE_TAC[GSYM(CONJUNCT2(cake_def "misc_word_list"))] THEN
   REWRITE_TAC[LENGTH_EQ_NIL; emp_def] THENL
    [REWRITE_TAC[UNWIND_THM2; cake_def "misc_word_list"; emp_def];
     MESON_TAC[LENGTH_EQ_CONS; LENGTH]]);;

let word_list_exists_ADD = cake_theorem "word_list_exists_ADD"
  (fun () ->
    `!m n a.
        word_list_exists a (m + n) =
        word_list_exists a m *
        word_list_exists (a + bytes_in_word * n2w m) n`)
  (* the SEP_EXISTS of the head comes out of the separating
     conjunction (the first clause of HOL4's SEP_CLAUSES), and the
     address of the tail is the head's address shifted once *)
  (INDUCT_TAC THEN
   ASM_REWRITE_TAC[word_list_exists_thm; ADD; emp_STAR; STAR_ASSOC;
                   SEP_EXISTS_STAR; WORD_ADD_MUL_SUC;
                   WORD_ADD_MUL_0]);;

let store_list_thm = cake_theorem "store_list_thm"
  (fun () ->
    `!xs a frame m dm.
        (word_list_exists a (LENGTH xs) * frame) (fun2set (m,dm))
          ==>
        (?m1.
          data_to_word_memoryProof_store_list a xs m dm = SOME m1
            /\
          (misc_word_list a xs * frame) (fun2set (m1,dm)))`)
  (* the store of a list of words into a space that word_list_exists
     describes: the space of a cons is a cell and the space of the
     rest, read_fun2set says the address of the cell is in the
     domain, write_fun2set says what the store at it leaves, and the
     induction hypothesis stores the rest with the cell in the frame *)
  (let aux = prove
    (`!(xs:((N)word_loc) list) (a:(N)word) frame m dm.
        (word_list_exists a (LENGTH xs) * frame) (fun2set (m,dm))
        ==> ?m1. data_to_word_memoryProof_store_list a xs m dm =
                 SOME m1 /\
                 (misc_word_list a xs * frame) (fun2set (m1,dm))`,
     LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
      [REWRITE_TAC[LENGTH; cake_thm "word_list_exists_thm";
                   cake_def "misc_word_list";
                   cake_def "data_to_word_memoryProof_store_list"] THEN
       DISCH_TAC THEN
       EXISTS_TAC `m:(N)word->(N)word_loc` THEN
       ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     REWRITE_TAC[LENGTH; cake_thm "word_list_exists_thm";
                 cake_def "misc_word_list";
                 cake_def "data_to_word_memoryProof_store_list"] THEN
     REWRITE_TAC[SEP_EXISTS_STAR; SEP_EXISTS_THM] THEN
     DISCH_THEN(X_CHOOSE_THEN `w:(N)word_loc` MP_TAC) THEN
     REWRITE_TAC[GSYM STAR_ASSOC] THEN DISCH_TAC THEN
     FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP read_fun2set th)) THEN
     DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC) THEN
     ASM_REWRITE_TAC[] THEN
     FIRST_ASSUM(fun th ->
       MP_TAC(MATCH_MP (ISPEC `h:(N)word_loc` write_fun2set) th)) THEN
     DISCH_TAC THEN
     FIRST_X_ASSUM(fun ih ->
       MP_TAC(SPECL [`a + bytes_in_word:(N)word`;
                     `set_sep_one (a:(N)word,h:(N)word_loc) * frame`;
                     `(a =+ (h:(N)word_loc)) (m:(N)word->(N)word_loc)`;
                     `dm:(N)word->bool`] ih)) THEN
     ANTS_TAC THENL
      [FIRST_X_ASSUM(fun th -> MP_TAC th) THEN
       REWRITE_TAC[STAR_AC];
       ALL_TAC] THEN
     DISCH_THEN(X_CHOOSE_THEN `m1:(N)word->(N)word_loc`
       STRIP_ASSUME_TAC) THEN
     EXISTS_TAC `m1:(N)word->(N)word_loc` THEN
     ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(fun th -> MP_TAC th) THEN
     REWRITE_TAC[STAR_AC]) in
   MATCH_ACCEPT_TAC aux);;

let store_list_domain = cake_theorem "store_list_domain"
  (fun () ->
    `!a xs m dm m1.
     data_to_word_memoryProof_store_list a xs m dm = SOME m1 ==>
     (!n. n < LENGTH xs ==> a + n2w n * bytes_in_word IN dm)`)
  (* the n-th address of the store is the first one shifted n
     times, which the induction over the list takes apart *)
  (let aux = prove
    (`!xs (a:(N)word) m dm m1.
        data_to_word_memoryProof_store_list a xs m dm = SOME m1
        ==> !n. n < LENGTH xs
                ==> a + n2w n * bytes_in_word IN dm`,
     LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
     REWRITE_TAC[cake_def "data_to_word_memoryProof_store_list";
                 LENGTH; CONJUNCT1 LT] THEN
     COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
     DISCH_TAC THEN X_GEN_TAC `k:num` THEN
     STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN
     ASM_REWRITE_TAC[WORD_ADD_0_MUL; LT_SUC; WORD_ADD_SUC_MUL;
                     LT_0] THEN
     DISCH_TAC THEN USE_IH THEN DISCH_THEN MATCH_MP_TAC THEN
     FIRST_ASSUM ACCEPT_TAC) in
   REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC aux);;

let store_list_append_imp = cake_theorem "store_list_append_imp"
  (fun () ->
    `!w1 a m dm m' w2.
     data_to_word_memoryProof_store_list a (w1 ++ w2) m dm = SOME
       m' ==>
     (?m''. data_to_word_memoryProof_store_list a w1 m dm = SOME
       m'' /\
           data_to_word_memoryProof_store_list (a + n2w (LENGTH
             w1) * bytes_in_word) w2 m'' dm = SOME m')`)
  (let aux = prove
    (`!w1 (a:(N)word) m dm m' w2.
        data_to_word_memoryProof_store_list a (APPEND w1 w2) m dm =
          SOME m'
        ==> ?m''.
              data_to_word_memoryProof_store_list a w1 m dm =
                SOME m'' /\
              data_to_word_memoryProof_store_list
                (a + n2w (LENGTH w1) * bytes_in_word) w2 m'' dm =
                SOME m'`,
     LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
     REWRITE_TAC[APPEND;
                 cake_def "data_to_word_memoryProof_store_list";
                 LENGTH; WORD_ADD_0_MUL; WORD_ADD_SUC_MUL] THEN
     TRY COND_CASES_TAC THEN
     REWRITE_TAC[distinctness "option"] THEN DISCH_TAC THEN
     TRY USE_IH THEN ASM_MESON_TAC[]) in
   REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC aux);;

let store_list_update_m_outside =
  cake_theorem "store_list_update_m_outside"
  (fun () ->
    `!ws a m dm m'.
     data_to_word_memoryProof_store_list a ws m dm = SOME m' /\
     (!i. i < LENGTH ws ==> ~(a + n2w i * bytes_in_word = a')) ==>
     data_to_word_memoryProof_store_list a ws ((a' =+ v) m) dm =
       SOME ((a' =+ v) m')`)
  (* the store of a list of words does not disturb an address that
     none of its stores touches, and the update of the memory at
     such an address commutes with every store of the list; the
     address of the i-th store of the tail is the one of the
     (i+1)-th store of the list *)
  (let upd_comm = prove
    (`!a b x y (f:A->B). ~(a = b)
        ==> (a =+ x) ((b =+ y) f) = (b =+ y) ((a =+ x) f)`,
     REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; UPDATE] THEN
     GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[]) in
   let wzero = prove
    (`!(a:(N)word). a + n2w 0 * bytes_in_word = a`,
     CONV_TAC WORD_RULE) in
   let wsuc = prove
    (`!(a:(N)word) i.
        (a + bytes_in_word) + n2w i * bytes_in_word =
        a + n2w (SUC i) * bytes_in_word`,
     REWRITE_TAC[ADD1; WORD_ADD] THEN CONV_TAC WORD_RULE) in
   LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[cake_def "data_to_word_memoryProof_store_list"] THENL
    [REWRITE_TAC[injectivity "option"] THEN
     DISCH_THEN(fun th -> REWRITE_TAC[SYM(CONJUNCT1 th)]);
     COND_CASES_TAC THEN
     REWRITE_TAC[distinctness "option"] THEN STRIP_TAC THEN
     FIRST_ASSUM(fun th ->
       let th' = REWRITE_RULE[wzero; LENGTH; LT_0] (SPEC `0` th) in
       if is_neg (concl th') then ASSUME_TAC th' else fail()) THEN
     FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP upd_comm th]) THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[wsuc] THEN
     GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[LENGTH; LT_SUC]]);;

let word_payload_IMP = cake_theorem "word_payload_IMP"
  (fun () ->
    `word_payload addrs ll tags tt1 conf = (h,ts,T) ==> LENGTH ts = ll`)
  (* every clause of word_payload gives the payload as a list of
     the same length as the one it is made of; the equation that
     says what ts is has to be used the other way round, and MESON
     does not get past the header of the clause *)
  (let use_ts (asl,w as gl) =
     let v = var_by_name "ts" gl in
     let ok t = can rhs (concl t) && rhs(concl t) = v in
     let th = tryfind (fun (_,t) -> if ok t then t else fail()) asl in
     (SUBST1_TAC(SYM th) THEN ASM_REWRITE_TAC[LENGTH_MAP]) gl in
   CASES_ON_NAME "tags" THEN
   REWRITE_TAC[cake_def "word_payload"; PAIR_EQ] THEN
   EVERY_CASE_TAC THEN REPEAT STRIP_TAC THEN use_ts);;

let word_el_IMP_word_list_exists =
  cake_theorem "word_el_IMP_word_list_exists"
  (fun () ->
    `!temp p curr.
        (p * word_el curr temp conf) s ==>
        (p * word_list_exists curr (el_length temp)) s`)
  (* whatever a heap element says of the memory, the space it takes
     is free space of its own length: an Unused element is that
     space already, a ForwardPointer is a cell and the space after
     it, and a DataElement is a word_list, whose length the
     condition of word_el and word_payload_IMP give *)
  (let wlie = prove
    (`!(xs:((M)word_loc) list) (a:(N)word) p s.
        (p * misc_word_list a xs) s
        ==> (p * word_list_exists a (LENGTH xs)) s`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[cake_def "word_list_exists"; STAR_SEP_EXISTS;
                 SEP_EXISTS_THM] THEN
     DISCH_TAC THEN EXISTS_TAC `xs:((M)word_loc) list` THEN
     REWRITE_TAC[STAR_ASSOC; STAR_cond] THEN
     ASM_REWRITE_TAC[]) in
   let aux = prove
    (`!conf s (temp:((M)word_loc,
                     data_to_word_memoryProof_tag #
                     ((M)word_loc) list)heap_element) p (curr:(N)word).
        (p * word_el curr temp conf) s
        ==> (p * word_list_exists curr (el_length temp)) s`,
     REPEAT GEN_TAC THEN CASES_ON_NAME "temp" THENL
      [REWRITE_TAC[cake_def "word_el"; cake_def "el_length"];
       REWRITE_TAC[cake_def "word_el"; cake_def "el_length"] THEN
       REWRITE_TAC[GSYM ADD1; cake_thm "word_list_exists_thm"] THEN
       REWRITE_TAC[STAR_SEP_EXISTS; SEP_EXISTS_THM] THEN
       DISCH_TAC THEN
       EXISTS_TAC `wordLang_Word ((n2w a0 << 2):(M)word)` THEN
       FIRST_ASSUM ACCEPT_TAC;
       MP_TAC(ISPEC `a2:data_to_word_memoryProof_tag #
                        ((M)word_loc) list` PAIR_SURJECTIVE) THEN
       DISCH_THEN(X_CHOOSE_THEN `tag:data_to_word_memoryProof_tag`
         (X_CHOOSE_THEN `qs:((M)word_loc) list` SUBST1_TAC)) THEN
       REWRITE_TAC[cake_def "word_el"; cake_def "el_length"] THEN
       W(fun (asl,w) ->
         let pr = find_term (fun t ->
           (try fst(dest_const(fst(strip_comb t))) = "word_payload"
            with Failure _ -> false)) w in
         MP_TAC(ISPEC pr PAIR_SURJECTIVE)) THEN
       DISCH_THEN(X_CHOOSE_THEN `hh:(M)word`
         (X_CHOOSE_THEN `rest:((M)word_loc) list # bool`
           ASSUME_TAC)) THEN
       MP_TAC(ISPEC `rest:((M)word_loc) list # bool`
         PAIR_SURJECTIVE) THEN
       DISCH_THEN(X_CHOOSE_THEN `ts:((M)word_loc) list`
         (X_CHOOSE_THEN `cc:bool` SUBST_ALL_TAC)) THEN
       ASM_REWRITE_TAC[] THEN
       CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
       REWRITE_TAC[STAR_ASSOC; STAR_cond] THEN
       STRIP_TAC THEN
       RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `cc:bool`]) THEN
       FIRST_ASSUM(fun pay ->
         MP_TAC(MATCH_MP (cake_thm "word_payload_IMP") pay)) THEN
       DISCH_TAC THEN
       FIRST_ASSUM(fun st ->
         MP_TAC(MATCH_MP wlie
           (REWRITE_RULE[GSYM STAR_ASSOC] st))) THEN
       ASM_REWRITE_TAC[LENGTH; ADD1]]) in
   REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC aux);;

let word_heap_IMP_word_list_exists =
  cake_theorem "word_heap_IMP_word_list_exists"
  (fun () ->
    `!temp p curr.
        (p * word_heap curr temp conf) s ==>
        (p * word_list_exists curr (heap_length temp)) s`)
  (* and the same of a whole heap, element by element: the space of
     a cons splits by word_list_exists_ADD, and the induction
     hypothesis takes the rest with the first element's space in the
     frame *)
  (let swap2 = prove
    (`!(p:((A)->bool)->bool) q r. (p * q) * r = (p * r) * q`,
     REWRITE_TAC[STAR_AC]) in
   let aux = prove
    (`!(temp:(((M)word_loc,
               data_to_word_memoryProof_tag #
               ((M)word_loc) list)heap_element) list) conf s p
        (curr:(N)word).
        (p * word_heap curr temp conf) s
        ==> (p * word_list_exists curr (heap_length temp)) s`,
     LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
      [REWRITE_TAC[cake_def "word_heap"; cake_thm "heap_length_NIL";
                   cake_thm "word_list_exists_thm"];
       ALL_TAC] THEN
     REWRITE_TAC[cake_def "word_heap";
                 cake_thm "heap_length_CONS"] THEN
     REWRITE_TAC[cake_thm "word_list_exists_ADD"] THEN
     REWRITE_TAC[STAR_ASSOC] THEN
     DISCH_TAC THEN
     FIRST_ASSUM(fun st ->
       MP_TAC(ONCE_REWRITE_RULE[swap2] st)) THEN
     DISCH_THEN(fun st ->
       MP_TAC(MATCH_MP (cake_thm "word_el_IMP_word_list_exists")
         st)) THEN
     DISCH_THEN(fun st -> MP_TAC(ONCE_REWRITE_RULE[swap2] st)) THEN
     FIRST_X_ASSUM(fun ih ->
       DISCH_THEN(fun st -> MP_TAC(MATCH_MP ih st))) THEN
     REWRITE_TAC[]) in
   REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC aux);;

let EVERY2_f_EQ = cake_theorem "EVERY2_f_EQ[local]"
  (fun () ->
    `!rs ws f. EVERY2 (\v w. f v = w) rs ws <=> MAP f rs = ws`)
  (let aux = prove
    (`!(f:A->B) rs ws. ALL2 (\v w. f v = w) rs ws <=> MAP f rs = ws`,
     GEN_TAC THEN LIST_INDUCT_TAC THEN X_GEN_TAC `ws:B list` THEN
     STRUCT_CASES_TAC(ISPEC `ws:B list` list_CASES_v) THEN
     ASM_REWRITE_TAC[ALL2; MAP; CONS_11; NOT_CONS_NIL;
                     EQ_SYM_EQ]) in
   REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC aux);;

let word_heap_heap_expand = cake_theorem "word_heap_heap_expand"
  (fun () ->
    `word_heap a (heap_expand n) conf = word_list_exists a n`)
  (STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
   ASM_REWRITE_TAC[cake_def "heap_expand"; NOT_SUC;
                   cake_def "word_heap"; cake_def "word_el";
                   STAR_emp; CONJUNCT1 word_list_exists_thm;
                   ARITH_RULE `SUC n - 1 = n`; ADD1]);;

let get_lowerbits_or_1 = cake_theorem "get_lowerbits_or_1[local]"
  (fun () ->
    `get_lowerbits c v = (get_lowerbits c v || (n2w 1))`)
  (CASES_ON_NAME "v" THEN
   REWRITE_TAC[cake_def "get_lowerbits"] THEN
   MATCH_REDUCE_TAC THEN WORD_BITWISE_TAC);;

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
  (* the new key is not in the domain and the new value not in the
     range, so the update stays injective.  The negated existential
     of the range is turned into an implication, which is what
     ASM_SIMP_TAC can use of it *)
  (REWRITE_TAC[INJ; FDOM_FUPDATE; IN_INSERT; FMAP_IN_FRANGE;
               NOT_EXISTS_THM; DE_MORGAN_THM;
               TAUT `(~a \/ ~b) <=> (a ==> ~b)`;
               FAPPLY_FUPDATE_THM] THEN
   REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
   ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]);;

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
  (* rule induction on v_inv_ck.  Every premise of a rule reads the
     refs through a lookup only, dest_thunk included, so lookups
     that agree at every pointer let the derivation be replayed
     with the other refs; the ck of the relation is untouched, and
     v_inv is the relation for every ck *)
  (let (vr,vi,vcases) = v_inv_ck in
   let rl = CONJUNCTS vr in
   let _ = vcases in
   let dt = prove
    (`!(v:dataSem_v) refs refs1.
        (!n. sptree_lookup n refs = sptree_lookup n refs1)
        ==> dataSem_dest_thunk v refs = dataSem_dest_thunk v refs1`,
     REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC[cake_def "dataSem_dest_thunk"]) in
   (* the assumption that the two lookups agree, which the cases of
      the induction each need in both directions *)
   let is_cnd th =
     let t = concl th in
     is_forall t &&
     (let b = snd(dest_forall t) in
      is_eq b &&
      (try fst(dest_const(fst(strip_comb(lhs b)))) = "sptree_lookup"
       with Failure _ -> false)) in
   let CND ttac =
     FIRST_ASSUM(fun th -> if is_cnd th then ttac th else fail()) in
   let PRE_TAC = REPEAT GEN_TAC THEN REPEAT STRIP_TAC in
   let swap = prove
    (`!ck conf (v:dataSem_v) refs1 y.
        v_inv_ck ck conf v refs1 y
        ==> !refs. (!n. sptree_lookup n refs = sptree_lookup n refs1)
                   ==> v_inv_ck ck conf v refs y`,
     MATCH_MP_TAC vi THEN REPEAT CONJ_TAC THENL
      [PRE_TAC THEN MATCH_MP_TAC(el 0 rl) THEN ASM_REWRITE_TAC[];
       PRE_TAC THEN MATCH_MP_TAC(el 1 rl) THEN ASM_REWRITE_TAC[];
       PRE_TAC THEN MATCH_MP_TAC(el 2 rl) THEN ASM_REWRITE_TAC[];
       PRE_TAC THEN MATCH_ACCEPT_TAC(el 3 rl);
       (* the annotation of the pointer is a lookup of the refs *)
       PRE_TAC THEN CND(fun cnd ->
         REWRITE_TAC[GSYM cnd] THEN MATCH_MP_TAC(el 4 rl) THEN
         REWRITE_TAC[cnd] THEN ASM_REWRITE_TAC[] THEN
         REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_ACCEPT_TAC));
       (* the thunk of the rule is named by its lookup, which is
          what MESON takes from the assumptions *)
       PRE_TAC THEN CND(fun cnd ->
         ASM_MESON_TAC[el 5 rl; MATCH_MP dt cnd]);
       PRE_TAC THEN CND(fun cnd ->
         ASM_MESON_TAC[el 6 rl; MATCH_MP dt cnd]);
       PRE_TAC THEN MATCH_MP_TAC(el 7 rl) THEN ASM_REWRITE_TAC[];
       (* and the elements of a Block are carried over one by one *)
       PRE_TAC THEN CND(fun cnd ->
         MATCH_MP_TAC(el 8 rl) THEN ASM_REWRITE_TAC[] THEN
         REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN
         DISCH_TAC THEN
         FIRST_X_ASSUM(fun ih ->
           FIRST_ASSUM(fun nz -> MP_TAC(MATCH_MP ih nz))) THEN
         MATCH_MP_TAC MONO_ALL2 THEN BETA_TAC THEN
         REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
         ASM_REWRITE_TAC[])]) in
   REWRITE_TAC[v_inv_eq] THEN REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[swap]);;

let bc_stack_ref_inv_swap_refs =
  cake_theorem "bc_stack_ref_inv_swap_refs"
  (fun () ->
    `bc_stack_ref_inv c ts vars refs (xs,heap,be) /\
     (!n. sptree_lookup n refs = lookup n refs1) ==>
     bc_stack_ref_inv c ts vars refs1 (xs,heap,be)`)
  (* each part of the invariant reads the refs through a lookup
     only: the domain by domain_lookup, all_ts, all_vs and ref_edge
     by their definitions, and v_inv by v_inv_swap_refs.  So the
     whole of it is rewritten from the one refs to the other and
     the assumption is the goal *)
  (let domq = prove
    (`!refs refs1:(A)spt.
        (!n. sptree_lookup n refs = sptree_lookup n refs1)
        ==> domain refs = domain refs1`,
     REPEAT STRIP_TAC THEN
     REWRITE_TAC[EXTENSION; domain_lookup] THEN ASM_REWRITE_TAC[]) in
   let atq = prove
    (`!refs refs1 stack.
        (!n. sptree_lookup n refs = sptree_lookup n refs1)
        ==> all_ts refs stack = all_ts refs1 stack`,
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[cake_def "all_ts"]) in
   let avq = prove
    (`!refs refs1 stack.
        (!n. sptree_lookup n refs = sptree_lookup n refs1)
        ==> all_vs refs stack = all_vs refs1 stack`,
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[cake_def "all_vs"]) in
   let reqq = prove
    (`!refs refs1.
        (!n. sptree_lookup n refs = sptree_lookup n refs1)
        ==> ref_edge refs = ref_edge refs1`,
     REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
     REPEAT GEN_TAC THEN ASM_REWRITE_TAC[cake_def "ref_edge"]) in
   let rchq = prove
    (`!refs refs1.
        (!n. sptree_lookup n refs = sptree_lookup n refs1)
        ==> !roots t. reachable_refs roots refs t <=>
                      reachable_refs roots refs1 t`,
     REPEAT STRIP_TAC THEN
     REWRITE_TAC[cake_def "reachable_refs"] THEN
     FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP reqq th])) in
   let viq = prove
    (`!refs refs1.
        (!n. sptree_lookup n refs = sptree_lookup n refs1)
        ==> !c (v:dataSem_v) y. v_inv c v refs y <=>
                                v_inv c v refs1 y`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
     EQ_TAC THEN ASM_MESON_TAC[cake_thm "v_inv_swap_refs"]) in
   let dtq = prove
    (`!refs refs1.
        (!n. sptree_lookup n refs = sptree_lookup n refs1)
        ==> !v. dataSem_dest_thunk v refs =
                dataSem_dest_thunk v refs1`,
     REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC[cake_def "dataSem_dest_thunk"]) in
   let brq = prove
    (`!refs refs1.
        (!n. sptree_lookup n refs = sptree_lookup n refs1)
        ==> !c n x. bc_ref_inv c n refs x <=> bc_ref_inv c n refs1 x`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
     FIRST_ASSUM(fun th ->
       ASM_REWRITE_TAC[cake_def "bc_ref_inv"; MATCH_MP viq th;
                       MATCH_MP dtq th])) in
   DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
   FIRST_ASSUM(fun cnd ->
     DISCH_THEN(MP_TAC o REWRITE_RULE
       [cake_def "bc_stack_ref_inv"; MATCH_MP domq cnd;
        MATCH_MP atq cnd; MATCH_MP avq cnd; MATCH_MP rchq cnd;
        MATCH_MP viq cnd; MATCH_MP brq cnd]) THEN
     REWRITE_TAC[cake_def "bc_stack_ref_inv"]));;

(* ---- FinaliseCons: the MutBlock at ptr keeps its payload and only flips its
   fin flag, and the value handed back is the Block that payload denotes.
   Neither all_ts, all_vs, ref_edge nor dest_thunk can observe fin, so the
   only real work is relocating the payload from the ref into the new Block. *)

let blocks_unique_SUBSET = cake_theorem "blocks_unique_SUBSET[local]"
  (fun () ->
    `blocks_unique ts vs2 /\ vs1 SUBSET vs2 ==> blocks_unique ts vs1`)
  (REWRITE_TAC[cake_def "blocks_unique"; SUBSET] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   ASM_SIMP_TAC[]);;

let blocks_unique_INSERT = cake_theorem "blocks_unique_INSERT[local]"
  (fun () ->
    `blocks_unique ts vs ==> blocks_unique (SUC ts) (Block ts tag l
  INSERT vs)`)
  (let inst a b c d =
     FIRST_ASSUM(fun h -> MP_TAC(SPECL [`t:num`; a; b; c; d] h)) THEN
     ANTS_TAC THENL
      [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] in
   let a1 = `a1:num` and x1 = `xs1:dataSem_v list`
   and a2 = `a2:num` and x2 = `xs2:dataSem_v list` in
   REWRITE_TAC[cake_def "blocks_unique"; IN_INSERT;
               injectivity "dataSem_v"] THEN
   DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
   FIRST
    [ASM_REWRITE_TAC[] THEN ARITH_TAC;
     inst a1 x1 a2 x2 THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_ARITH_TAC;
     inst a2 x2 a2 x2 THEN STRIP_TAC THEN
     SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC;
     inst a1 x1 a1 x1 THEN STRIP_TAC THEN
     SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC]);;

let all_ts_CONS_SUBSET = cake_theorem "all_ts_CONS_SUBSET[local]"
  (fun () ->
    `all_ts refs stack SUBSET all_ts refs (x :: stack)`)
  (MATCH_MP_TAC all_ts_SUBSET_gen THEN REWRITE_TAC[MEM] THEN
   MESON_TAC[]);;

let in_all_vs_stack = cake_theorem "in_all_vs_stack[local]"
  (fun () ->
    `MEM v (v_all_vs stack) ==> v IN all_vs refs stack`)
  (DISCH_TAC THEN
   REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM] THEN
   REPEAT DISJ2_TAC THEN ASM_REWRITE_TAC[]);;

let in_all_vs_MutBlock = cake_theorem "in_all_vs_MutBlock[local]"
  (fun () ->
    `lookup n refs = SOME (bvlSem_MutBlock tg fin l c r) /\
     MEM v (v_all_vs (l ++ [c] ++ r)) ==>
     v IN all_vs refs stack`)
  (REPEAT STRIP_TAC THEN
   REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM] THEN
   DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN ASM_MESON_TAC[]);;

let all_vs_CONS_SUBSET = cake_theorem "all_vs_CONS_SUBSET[local]"
  (fun () ->
    `x IN all_vs refs stack ==> all_vs refs (x :: stack) SUBSET all_vs
  refs stack`)
  (* the three parts of all_vs that read the refs are the same, and
     a value of the head is a value of the refs or of the stack
     already, because the head itself is *)
  (let (vnil,vsing,vats,vcons) = v_all_vs_clauses () in
   DISCH_TAC THEN REWRITE_TAC[SUBSET] THEN GEN_TAC THEN
   GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [cake_def "all_vs"] THEN
   REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [vcons] THEN
   REWRITE_TAC[MEM_APPEND] THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[vnil; MEM]) THEN
   TRY(FIRST_ASSUM CONTR_TAC) THEN
   TRY(FIRST_ASSUM(fun m -> FIRST_ASSUM(fun xm ->
     MATCH_ACCEPT_TAC(MATCH_MP (cake_thm "v_in_all_vs")
       (CONJ xm m))))) THEN
   REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM] THEN
   ASM_MESON_TAC[]);;

let all_vs_MutBlock_centre =
  cake_theorem "all_vs_MutBlock_centre[local]"
  (fun () ->
    `lookup ptr refs = SOME (bvlSem_MutBlock tag fin left cen right) ==>
     all_vs refs (cen :: stack) SUBSET all_vs refs stack`)
  (* the centre of the MutBlock is a value of the refs already, so
     putting it on the stack adds nothing *)
  (DISCH_TAC THEN MATCH_MP_TAC all_vs_CONS_SUBSET THEN
   ASM_MESON_TAC[in_all_vs_MutBlock; MEM_v_all_vs; MEM_APPEND; MEM]);;

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
  (* the centre of the MutBlock is reachable from the pointer to it
     in one step of ref_edge, because it is inside the payload, so
     what the centre reaches the pointer reaches as well; a root
     other than the centre is a root of the shorter list *)
  (REWRITE_TAC[cake_def "reachable_refs"; MEM] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC)) THENL
    [FIRST_X_ASSUM(fun th ->
       if is_eq(concl th) && is_var(lhand(concl th))
       then SUBST_ALL_TAC th else fail()) THEN
     MAP_EVERY EXISTS_TAC [`RefPtr b ptr:dataSem_v`; `ptr:num`] THEN
     REWRITE_TAC[cake_def "get_refs"; MEM] THEN
     MATCH_MP_TAC(CONJUNCT2 (SPEC_ALL RTC_RULES)) THEN
     EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[cake_def "ref_edge"] THEN MATCH_REDUCE_TAC THEN
     REWRITE_TAC[cake_def "get_refs"; MEM_FLAT; MEM_MAP; MEM_APPEND;
                 MEM] THEN
     ASM_MESON_TAC[];
     MAP_EVERY EXISTS_TAC [`x:dataSem_v`; `r:num`] THEN
     ASM_REWRITE_TAC[];
     MAP_EVERY EXISTS_TAC [`x:dataSem_v`; `r:num`] THEN
     ASM_REWRITE_TAC[]]);;

let ref_edge_insert_MutBlock =
  cake_theorem "ref_edge_insert_MutBlock[local]"
  (fun () ->
    `lookup ptr refs = SOME (bvlSem_MutBlock tg fin1 l c r) ==>
     ref_edge (insert ptr (bvlSem_MutBlock tg fin2 l c r) refs) =
       ref_edge refs`)
  (DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[ref_edge_MutBlock] THEN COND_CASES_TAC THENL
    [SUBGOAL_THEN
       `sptree_lookup x (refs:(dataSem_v bvlSem_ref) spt) =
        SOME (bvlSem_MutBlock tg fin1 l c r)`
       ASSUME_TAC THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN
     ONCE_REWRITE_TAC[cake_def "ref_edge"] THEN ASM_REWRITE_TAC[] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[];
     REWRITE_TAC[]]);;

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
  (* and a MutBlock is no Thunk, so the dest_thunk of the pointer
     is NotThunk before the insert and after it *)
  (let dt_def = cake_def "dataSem_dest_thunk" in
   let opt_rws = [distinctness "option"; injectivity "option"] in
   let ref_rws = [distinctness "bvlSem_ref"; injectivity "bvlSem_ref";
                  distinctness "thunk_mode"] in
   DISCH_TAC THEN CASES_ON_NAME "v" THEN
   ONCE_REWRITE_TAC[dt_def] THEN
   SAFE_MATCH_REDUCE_TAC THEN REWRITE_TAC[] THEN
   REWRITE_TAC[lookup_insert] THEN
   ASM_CASES_TAC `a1:num = ptr` THEN ASM_REWRITE_TAC[] THEN
   TRY MATCH_REDUCE_TAC THEN
   REWRITE_TAC(opt_rws @ ref_rws) THEN
   REPEAT COND_CASES_TAC THEN REWRITE_TAC[]);;

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
  (* the two refs have the same lookup everywhere: at ptr the delete
     takes the value out of the left half and the insert puts the
     same value in the right one, and away from ptr neither changes
     anything *)
  (STRIP_TAC THEN
   SUBGOAL_THEN
     `!n. sptree_lookup n
            (sptree_union (refs:(dataSem_v bvlSem_ref) spt) frame) =
          sptree_lookup n (sptree_union (sptree_delete ptr refs)
                             (sptree_insert ptr x frame))`
     ASSUME_TAC THENL
    [GEN_TAC THEN
     REWRITE_TAC[lookup_union; OPT_MATCH_COND; lookup_delete;
                 lookup_insert] THEN
     ASM_CASES_TAC `n:num = ptr` THEN
     ASM_REWRITE_TAC[distinctness "option"];
     ALL_TAC] THEN
   FIRST_ASSUM(fun c -> FIRST_ASSUM(fun h ->
     MATCH_ACCEPT_TAC(MATCH_MP
       (cake_thm "bc_stack_ref_inv_swap_refs") (CONJ h c)))));;

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
  (* the empty Block of a tag has the root Data (Word (BlockNil
     tag)), which cons_thm_EMPTY adds, and the BlockNil is sixteen
     times the tag plus two, whose lowest bit is clear.  HOL4 has
     that last fact as BlockNil_and_lemma; the port's statement of
     that lemma is the and of the complement with the multiple of
     sixteen, not with the sum (see ISSUES.md, "The precedence of a
     word's bitwise operators"), so the fact is proved again here *)
  (let bw2 = prove
     (`!i. bit i (word 2:(N)word) <=> i = 1 /\ 1 < dimindex(:N)`,
      GEN_TAC THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
        [ARITH_RULE `2 = 2 EXP 1`] THEN
      REWRITE_TAC[BIT_WORD_POW2]) in
    let addor = prove
     (`!(v:(N)word). word_shl v 4 + word 2 = word_shl v 4 || word 2`,
      GEN_TAC THEN MATCH_MP_TAC WORD_ADD_OR THEN
      REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0;
                  BIT_WORD_SHL; bw2] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(i:num) = 1` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN TRY(CONV_TAC TAUT)) in
    let andsum = prove
     (`!(tag:(N)word).
         (word_shl tag 4 + word 2) && word_not (word 1) =
         word_shl tag 4 + word 2`,
      GEN_TAC THEN REWRITE_TAC[addor] THEN
      REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_NOT;
                  BIT_WORD_1; BIT_WORD_OR; BIT_WORD_SHL; bw2] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(i:num) = 0` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN TRY(CONV_TAC TAUT)) in
    let waddr = hd (word_addr_clauses ()) in
    REWRITE_TAC[cake_def "memory_rel"; cake_def "word_ml_inv"] THEN
    REPEAT STRIP_TAC THEN ASM_EXISTS_TAC THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC
      `CONS (gc_shared_Data (wordLang_Word (BlockNil tag:'a word))) hs`
    THEN
    REWRITE_TAC[MAP; ALL2; waddr] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC (cake_thm "cons_thm_EMPTY") THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[cake_def "BlockNil"] THEN AP_TERM_TAC THEN
      MATCH_ACCEPT_TAC andsum]);;

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
  (* a word_list that lies inside free space takes the front of it:
     the cell of the head is the first cell of the space (both are
     the memory at the address, which read_fun2set reads off), and
     the induction hypothesis takes the tail with that cell in the
     frame *)
  (let has nm th =
     can (find_term (fun t ->
       (try fst(dest_const(fst(strip_comb t))) = nm
        with Failure _ -> false))) (concl th) in
   let aux = prove
    (`!(ws:(M)list) (aa:(N)word) frame n m dm.
        (misc_word_list aa ws * SEP_T) (fun2set (m,dm)) /\
        (word_list_exists aa n * frame) (fun2set (m,dm)) /\
        LENGTH ws <= n
        ==> (misc_word_list aa ws *
             word_list_exists (aa + bytes_in_word * n2w (LENGTH ws))
               (n - LENGTH ws) * frame) (fun2set (m,dm))`,
     LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
      [REWRITE_TAC[cake_def "misc_word_list"; LENGTH; emp_STAR;
                   SUB_0; WORD_ADD_MUL_0] THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     STRIP_TAC THEN
     (SUBGOAL_THEN `?n':num. n = SUC n'` MP_TAC THENL
       [EXISTS_TAC `n - 1` THEN
        FIRST_X_ASSUM(fun th -> MP_TAC th) THEN
        REWRITE_TAC[LENGTH] THEN ARITH_TAC;
        ALL_TAC]) THEN
     DISCH_THEN(X_CHOOSE_THEN `n':num` SUBST_ALL_TAC) THEN
     RULE_ASSUM_TAC(REWRITE_RULE
       [cake_def "misc_word_list"; LENGTH;
        cake_thm "word_list_exists_thm";
        SEP_EXISTS_STAR; SEP_EXISTS_THM]) THEN
     FIRST_X_ASSUM(fun ex ->
       if is_exists (concl ex) then
         X_CHOOSE_THEN `w:M` ASSUME_TAC ex else fail()) THEN
     REWRITE_TAC[cake_def "misc_word_list"; LENGTH] THEN
     REWRITE_TAC[ARITH_RULE `SUC a - SUC b = a - b`;
                 WORD_ADD_MUL_SUC] THEN
     SUBGOAL_THEN `(w:M) = h` SUBST_ALL_TAC THENL
      [FIRST_ASSUM(fun a1 ->
         if has "SEP_T" a1
         then MP_TAC(MATCH_MP read_fun2set
                (REWRITE_RULE[GSYM STAR_ASSOC] a1))
         else fail()) THEN
       FIRST_ASSUM(fun a2 ->
         if has "word_list_exists" a2
         then MP_TAC(MATCH_MP read_fun2set
                (REWRITE_RULE[GSYM STAR_ASSOC] a2))
         else fail()) THEN
       MESON_TAC[];
       ALL_TAC] THEN
     FIRST_X_ASSUM(fun ih ->
       if is_forall (concl ih) then
         MP_TAC(SPECL [`aa + bytes_in_word:(N)word`;
                       `set_sep_one (aa:(N)word,h:M) *
                        frame`;
                       `n':num`; `m:(N)word->M`;
                       `dm:(N)word->bool`] ih)
       else fail()) THEN
     ANTS_TAC THENL
      [REPEAT CONJ_TAC THENL
        [FIRST_ASSUM(fun a1 ->
           if has "SEP_T" a1
           then MP_TAC(REWRITE_RULE[GSYM STAR_ASSOC; STAR_SEP_T] a1)
           else fail()) THEN
         REWRITE_TAC[STAR_SEP_T] THEN
         DISCH_THEN(X_CHOOSE_THEN `u:((N)word # M)->bool`
           (CONJUNCTS_THEN2 ASSUME_TAC
             (fun st -> MP_TAC(REWRITE_RULE[one_STAR] st)))) THEN
         DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC) THEN
         EXISTS_TAC
           `(u:((N)word # M)->bool) DELETE (aa,h)` THEN
         ASM_REWRITE_TAC[] THEN
         FIRST_X_ASSUM(fun th ->
           if has "SUBSET" th then MP_TAC th else fail()) THEN
         SET_TAC[];
         FIRST_ASSUM(fun a2 ->
           if has "word_list_exists" a2 then MP_TAC a2 else fail()) THEN
         REWRITE_TAC[STAR_AC];
         FIRST_X_ASSUM(fun th ->
           if has "LENGTH" th then MP_TAC th else fail()) THEN
         REWRITE_TAC[LENGTH] THEN ARITH_TAC];
       ALL_TAC] THEN
     DISCH_THEN(fun th -> MP_TAC th) THEN
     REWRITE_TAC[STAR_AC]) in
   REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC aux);;

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
  (MATCH_MP_TAC memory_rel_rearrange THEN
   GEN_TAC THEN REWRITE_TAC[MEM_APPEND; MEM_REPLICATE; MEM] THEN
   CONV_TAC TAUT);;

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
  (* every set_byte of the word that repeats a byte writes the byte
     it already has there: the byte index is a multiple of eight, so
     the position inside the byte is the position modulo eight, and
     that is the bit of the byte that word_of_byte put there *)
  (let bsb0 = prove
    (`!(a:(N)word) b (h:(N)word) bb j. j < dimindex (:N)
        ==> (bit j (set_byte a b h bb) <=>
             (if byte_index a bb <= j /\ j < byte_index a bb + 8
              then bit (j - byte_index a bb) b else bit j h))`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC[cake_def "set_byte"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     ASM_SIMP_TAC[BIT_WORD_OR; BIT_WORD_SLICE_ALT_LT; BIT_WORD_SHL;
                  BIT_WORD_ZX; DIMINDEX_8] THEN
     MP_TAC(REWRITE_RULE[DIMINDEX_8]
       (ISPECL [`b:(8)word`; `j - byte_index (a:(N)word) bb`]
          BIT_TRIVIAL)) THEN
     ASM_CASES_TAC `byte_index (a:(N)word) bb <= j` THEN
     ASM_CASES_TAC `j < byte_index (a:(N)word) bb + 8` THEN
     ASM_CASES_TAC `bit j (h:(N)word)` THEN
     ASM_CASES_TAC `bit (j - byte_index (a:(N)word) bb) (b:(8)word)` THEN
     ASM_REWRITE_TAC[] THEN ARITH_NO_BIT_TAC) in
   let modgen = prove
    (`!i k. 8 * k <= i /\ i < 8 * k + 8 ==> i MOD 8 = i - 8 * k`,
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     SUBGOAL_THEN `(8 * k + (i - 8 * k)) MOD 8 = i - 8 * k` MP_TAC THENL
      [ONCE_REWRITE_TAC[ARITH_RULE `8 * k + r = k * 8 + r`] THEN
       REWRITE_TAC[MOD_MULT_ADD] THEN
       MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
       ASM_SIMP_TAC[ARITH_RULE
         `8 * k <= i ==> 8 * k + (i - 8 * k) = i`]]) in
   let modfacts =
     map (fun k -> REWRITE_RULE[LE_0; SUB_0]
       (CONV_RULE NUM_REDUCE_CONV
         (SPECL [`i:num`; mk_small_numeral k] modgen)))
       [0; 1; 2; 3; 4; 5; 6; 7] in
   let bix8 = prove
    (`!(a:'a word) bb. ?k. byte_index a bb = 8 * k /\
                           (0 < dimindex (:'a) DIV 8
                            ==> k < dimindex (:'a) DIV 8)`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[cake_def "byte_index"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     COND_CASES_TAC THENL
      [EXISTS_TAC `(dimindex (:'a) DIV 8 - 1) -
                   w2n (a:'a word) MOD (dimindex (:'a) DIV 8)`;
       EXISTS_TAC `w2n (a:'a word) MOD (dimindex (:'a) DIV 8)`] THEN
     REWRITE_TAC[] THEN DISCH_TAC THEN
     ASM_SIMP_TAC[DIVISION] THEN ASM_ARITH_TAC) in
   let rules =
     let num k = mk_small_numeral k in
     let le a b = mk_binop `(<=):num->num->bool` a b in
     let lt a b = mk_binop `(<):num->num->bool` a b in
     let iv = `i:num` in
     let ks = [8; 16; 24; 32; 40; 48; 56; 64] in
     itlist (fun k acc -> itlist (fun k2 acc ->
       (if k <= k2
        then [ARITH_RULE(mk_imp(le (num k2) iv, le (num k) iv));
              ARITH_RULE(mk_imp(lt iv (num k), lt iv (num k2)))]
        else []) @
       (if k2 <= k
        then [ARITH_RULE(mk_imp(lt iv (num k2), mk_neg(le (num k) iv)));
              ARITH_RULE(mk_imp(le (num k) iv, mk_neg(lt iv (num k2))))]
        else []) @ acc) ks acc) ks
       [ARITH_RULE `i < 64 ==> (i - m < 64 <=> T)`;
        ARITH_RULE `i < 32 ==> (i - m < 32 <=> T)`;
        ARITH_RULE `(8 <= i - 8 <=> 16 <= i) /\
                    (8 <= i - 16 <=> 24 <= i) /\
                    (8 <= i - 24 <=> 32 <= i) /\
                    (8 <= i - 32 <=> 40 <= i) /\
                    (8 <= i - 40 <=> 48 <= i) /\
                    (8 <= i - 48 <=> 56 <= i) /\
                    (16 <= i - 32 <=> 48 <= i)`] in
   let killbit tm =
     TRY(MP_TAC(REWRITE_RULE[DIMINDEX_8]
           (ISPECL [`w:(8)word`; tm] BIT_TRIVIAL)) THEN
         (ANTS_TAC THENL
           [ASM_ARITH_TAC;
            DISCH_THEN(fun th -> REWRITE_TAC[th])])) in
   let wobbit = prove
    (`!i. good_dimindex (:'a) /\ i < dimindex (:'a)
          ==> (bit i (word_of_byte ((w2w (w:(8)word)):'a word)) <=>
               bit (i MOD 8) w)`,
     GEN_TAC THEN STRIP_TAC THEN
     FIRST_ASSUM(DISJ_CASES_THEN ASSUME_TAC o
       REWRITE_RULE[cake_def "good_dimindex"]) THEN
     REWRITE_TAC[cake_def "word_of_byte"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_ZX; DIMINDEX_8] THEN
     REWRITE_TAC[ARITH_RULE
       `(((i - 32) - 16) - 8 = i - 56) /\ ((i - 32) - 16 = i - 48) /\
        ((i - 32) - 8 = i - 40) /\ ((i - 16) - 8 = i - 24)`] THEN
     (SUBGOAL_THEN
        `(i:num) < 8 \/ (8 <= i /\ i < 16) \/ (16 <= i /\ i < 24) \/
         (24 <= i /\ i < 32) \/ (32 <= i /\ i < 40) \/
         (40 <= i /\ i < 48) \/ (48 <= i /\ i < 56) \/
         (56 <= i /\ i < 64)`
        MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
     STRIP_TAC THEN
     killbit `i:num` THEN killbit `i - 8` THEN killbit `i - 16` THEN
     killbit `i - 24` THEN killbit `i - 32` THEN killbit `i - 40` THEN
     killbit `i - 48` THEN
     ASM_SIMP_TAC (modfacts @ rules) THEN
     TRY(SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC)) in
   let stripconj =
     REPEAT(FIRST_X_ASSUM(fun th ->
       if is_conj (concl th) then STRIP_ASSUME_TAC th else fail())) in
   DISCH_TAC THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
   X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   ASM_SIMP_TAC[bsb0; wobbit] THEN
   W(fun (asl,w) ->
     let bidx = find_term (fun t ->
       (try fst(dest_const(fst(strip_comb t))) = "byte_index"
        with Failure _ -> false)) w in
     MP_TAC(ISPECL (snd(strip_comb bidx)) bix8)) THEN
   DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   stripconj THEN
   FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
     MP_TAC(MATCH_MP modgen (CONJ th1 th2)) THEN
     DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[])));;

let w2w_word_of_byte_w2w = cake_theorem "w2w_word_of_byte_w2w"
  (fun () ->
    `good_dimindex (:'a) ==>
     (w2w (word_of_byte (w2w w:'a word)):word8) = w`)
  (* the word of a byte repeats the byte, and the low eight bits of
     it are the byte itself: the shifts of the definition are by
     eight, sixteen and thirty-two, which no bit below eight is
     above *)
  (DISCH_TAC THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_8] THEN
   X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   REWRITE_TAC[cake_def "word_of_byte"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   FIRST_ASSUM(DISJ_CASES_THEN (fun th -> ASSUME_TAC th) o
     REWRITE_RULE[cake_def "good_dimindex"]) THEN
   ASM_REWRITE_TAC[ARITH_EQ] THEN
   ASM_REWRITE_TAC[BIT_WORD_ZX; BIT_WORD_OR; BIT_WORD_SHL;
                   DIMINDEX_8] THEN
   ASM_SIMP_TAC[ARITH_RULE `i < 8 ==> ~(8 <= i)`;
                ARITH_RULE `i < 8 ==> ~(16 <= i)`;
                ARITH_RULE `i < 8 ==> ~(32 <= i)`;
                ARITH_RULE `i < 8 ==> i < 32`;
                ARITH_RULE `i < 8 ==> i < 64`]);;

let write_bytes_REPLICATE = cake_theorem "write_bytes_REPLICATE[local]"
  (fun () ->
    `!n m.
         good_dimindex (:'a) ==>
         write_bytes (REPLICATE m w) (REPLICATE n (word_of_byte
           (w2w w))) be =
         REPLICATE n (word_of_byte ((w2w w):'a word))`)
  (* the words are written one by one, and writing the bytes of a
     word of one byte over and over leaves it as it is, which
     set_byte_word_of_byte says of each byte.  The flag of the
     endianness is called b2 in the two lemmas, because be is the
     field of the configuration and not a variable *)
  (let drop0 = prove
    (`!l:A list. DROP 0 l = l`,
     LIST_INDUCT_TAC THEN REWRITE_TAC[DROP]) in
   let drop_rep = prove
    (`!k m (x:A). DROP k (REPLICATE m x) = REPLICATE (m - k) x`,
     INDUCT_TAC THENL
      [REWRITE_TAC[drop0; SUB_0];
       REPEAT GEN_TAC THEN
       STRUCT_CASES_TAC(ISPEC `m:num` num_CASES) THEN
       ASM_REWRITE_TAC[REPLICATE; DROP; NOT_SUC; SUC_SUB1; SUB_0;
                       SUB_SUC; ARITH_RULE `0 - SUC k = 0`]]) in
   let head = prove
    (`good_dimindex (:'a) ==>
      !k a m b2.
        bytes_to_word k (a:'a word) (REPLICATE m (w:(8)word))
          (word_of_byte ((w2w w):'a word)) b2 =
        word_of_byte ((w2w w):'a word)`,
     DISCH_TAC THEN INDUCT_TAC THENL
      [ONCE_REWRITE_TAC[cake_def "bytes_to_word"] THEN
       REWRITE_TAC[];
       REPEAT GEN_TAC THEN
       ONCE_REWRITE_TAC[cake_def "bytes_to_word"] THEN
       REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN
       STRUCT_CASES_TAC(ISPEC `m:num` num_CASES) THEN
       REWRITE_TAC[REPLICATE] THEN MATCH_REDUCE_TAC THEN
       ASM_REWRITE_TAC[] THEN
       ASM_SIMP_TAC[cake_thm "set_byte_word_of_byte"]]) in
   INDUCT_TAC THENL
    [REWRITE_TAC[REPLICATE; cake_def "write_bytes"];
     GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC[REPLICATE] THEN
     ONCE_REWRITE_TAC[cake_def "write_bytes"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     ASM_SIMP_TAC[head; drop_rep] THEN
     FIRST_ASSUM(fun th ->
       ASM_SIMP_TAC[SPEC `m - dimindex (:'a) DIV 8` th])]);;

let IMP_EXP_LESS = cake_theorem "IMP_EXP_LESS"
  (fun () ->
    `m <= l ==> 2 EXP m <= 2 EXP l`)
  (REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ARITH_TAC);;

let shift_shift_lemma = cake_theorem "shift_shift_lemma[local]"
  (fun () ->
    `l = k + backend_common_word_shift (:'a) /\ t < k /\ n DIV i < 2 EXP
  t /\ l = dimindex (:'a) /\
       i = 2 EXP backend_common_word_shift (:'a) /\ n < dimword
         (:'a) ==>
       n2w n << (k - t) >>> (l - t) = ((n2w (n DIV i)):'a word)`)
  (* the shift up and down of a word that keeps t of its bits:
     the bit that the two shifts leave at j is the one of n at
     j plus the word shift, and above t there is none, because
     n divided by the word shift is below two to the t *)
  (let ARITH_NO_DIV_TAC =
     POP_ASSUM_LIST(fun l ->
       MAP_EVERY MP_TAC
         (filter (fun th ->
            not (can (find_term (fun t ->
              (try fst(dest_const(fst(strip_comb t))) = "DIV"
               with Failure _ -> false))) (concl th))) l)) THEN
     ARITH_TAC in
   STRIP_TAC THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
   X_GEN_TAC `j:num` THEN DISCH_TAC THEN
   REWRITE_TAC[BIT_WORD_USHR; BIT_WORD_SHL; BIT_WORD] THEN
   SUBGOAL_THEN
     `(j + (l - t)) - (k - t) =
      j + backend_common_word_shift (:'a)`
     SUBST1_TAC THENL [ARITH_NO_DIV_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `(n DIV i) DIV 2 EXP j =
                 n DIV 2 EXP (j + backend_common_word_shift (:'a))`
     SUBST1_TAC THENL
    [ASM_REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
     AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
     ALL_TAC] THEN
   ASM_CASES_TAC `(j:num) < t` THENL
    [SUBGOAL_THEN
       `(k - t <= j + (l - t)) /\ (j + (l - t) < dimindex (:'a)) /\
        (j + backend_common_word_shift (:'a) < dimindex (:'a)) /\
        j < dimindex (:'a)`
       (fun th -> REWRITE_TAC[th]) THENL
      [ARITH_NO_DIV_TAC];
     SUBGOAL_THEN
       `n DIV 2 EXP (j + backend_common_word_shift (:'a)) = 0`
       SUBST1_TAC THENL
      [SUBGOAL_THEN
         `n DIV 2 EXP (j + backend_common_word_shift (:'a)) =
          (n DIV i) DIV 2 EXP j` SUBST1_TAC THENL
        [ASM_REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
         AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
         MATCH_MP_TAC DIV_LT THEN
         TRANS_TAC LTE_TRANS `2 EXP t` THEN
         ASM_REWRITE_TAC[LE_EXP] THEN
         CONV_TAC NUM_REDUCE_CONV THEN ARITH_NO_DIV_TAC];
       REWRITE_TAC[ODD]]]);;

let write_bytes_APPEND = cake_theorem "write_bytes_APPEND"
  (fun () ->
    `!xs ys vals be'.
        write_bytes vals (xs ++ (ys:('a word) list)) be' =
        write_bytes vals xs be' ++
        write_bytes (DROP ((dimindex (:'a) DIV 8) * LENGTH xs)
          vals) ys be'`)
  (* induction on the first list of words: each word takes the
     bytes of its own length off the front, so the words of the
     second list see the bytes that the first list leaves *)
  (LIST_INDUCT_TAC THEN
   REWRITE_TAC[APPEND; cake_def "write_bytes"; LENGTH; MULT_CLAUSES;
               DROP_0] THEN
   REPEAT GEN_TAC THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ASM_REWRITE_TAC[APPEND; DROP_DROP] THEN
   REWRITE_TAC[ARITH_RULE `(d * SUC n) = d + d * n`] THEN
   REWRITE_TAC[DROP_DROP; ADD_AC]);;

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
  (* two set_bytes of a word commute when they write different
     bytes of it: the byte index of a number below the number of
     bytes is eight times it (or eight times its mirror), so two
     such indices are different, and no bit is in both ranges; when
     the two are the same byte the outer write covers the inner *)
  (let bsb0 = prove
  (`!(a:(N)word) b (h:(N)word) bb j. j < dimindex (:N)
      ==> (bit j (set_byte a b h bb) <=>
           (if byte_index a bb <= j /\ j < byte_index a bb + 8
            then bit (j - byte_index a bb) b else bit j h))`,
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[cake_def "set_byte"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ASM_SIMP_TAC[BIT_WORD_OR; BIT_WORD_SLICE_ALT_LT; BIT_WORD_SHL;
                BIT_WORD_ZX; DIMINDEX_8] THEN
   MP_TAC(REWRITE_RULE[DIMINDEX_8]
     (ISPECL [`b:(8)word`; `j - byte_index (a:(N)word) bb`]
        BIT_TRIVIAL)) THEN
   ASM_CASES_TAC `byte_index (a:(N)word) bb <= j` THEN
   ASM_CASES_TAC `j < byte_index (a:(N)word) bb + 8` THEN
   ASM_CASES_TAC `bit j (h:(N)word)` THEN
   ASM_CASES_TAC `bit (j - byte_index (a:(N)word) bb) (b:(8)word)` THEN
   ASM_REWRITE_TAC[] THEN ARITH_NO_BIT_TAC) in
 let bixval = prove
  (`!n bb. good_dimindex (:'a) /\ n < dimindex (:'a) DIV 8
      ==> byte_index ((n2w n):'a word) bb =
          8 * (if bb then (dimindex (:'a) DIV 8 - 1) - n else n)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC[cake_def "good_dimindex"; cake_def "byte_index"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[VAL_WORD; dimword] THEN
   STRIP_TAC THEN
   FIRST_ASSUM(fun dd ->
     if (try fst(dest_const(fst(strip_comb(lhs(concl dd))))) =
              "dimindex" with Failure _ -> false)
     then REWRITE_TAC[dd] THEN RULE_ASSUM_TAC(REWRITE_RULE[dd]) THEN
          ASSUME_TAC dd
     else fail()) THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   RULE_ASSUM_TAC(fun th ->
     try CONV_RULE NUM_REDUCE_CONV th with Failure _ -> th) THEN
   (FIRST
     [(SUBGOAL_THEN `n MOD 4294967296 MOD 4 = n` SUBST1_TAC THENL
        [MP_TAC(SPECL [`n:num`; `4`; `1073741824`] MOD_MOD) THEN
         CONV_TAC NUM_REDUCE_CONV THEN
         DISCH_THEN SUBST1_TAC THEN
         MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
         ALL_TAC]);
      (SUBGOAL_THEN `n MOD 18446744073709551616 MOD 8 = n`
         SUBST1_TAC THENL
        [MP_TAC(SPECL [`n:num`; `8`; `2305843009213693952`]
           MOD_MOD) THEN
         CONV_TAC NUM_REDUCE_CONV THEN
         DISCH_THEN SUBST1_TAC THEN
         MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
         ALL_TAC])]) THEN
   COND_CASES_TAC THEN REWRITE_TAC[]) in
   let usebe =
     TRY(FIRST_ASSUM(fun th ->
       let c = concl th in
       if is_var c || (is_neg c && is_var (rand c))
       then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th
       else fail())) in
   let numred =
     RULE_ASSUM_TAC(fun th ->
       try CONV_RULE NUM_REDUCE_CONV th with Failure _ -> th) in
   let stripconj =
     REPEAT(FIRST_X_ASSUM(fun th ->
       if is_conj (concl th) then STRIP_ASSUME_TAC th else fail())) in
   REPEAT GEN_TAC THEN
   COND_CASES_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
     X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     ASM_SIMP_TAC[bsb0] THEN
     COND_CASES_TAC THEN REWRITE_TAC[];
     COND_CASES_TAC THENL
      [stripconj THEN
       REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
       X_GEN_TAC `i:num` THEN DISCH_TAC THEN
       ASM_SIMP_TAC[bsb0; bixval] THEN
       REPEAT COND_CASES_TAC THEN usebe THEN numred THEN
       ASM_REWRITE_TAC[] THEN
       TRY(SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC);
       REWRITE_TAC[]]]);;

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
  (* the bit of a set_byte is the byte's bit inside the byte and the
     word's outside it, so two set_bytes of the same byte agree
     exactly when the two words agree outside it -- which does not
     depend on what the byte is *)
  (let bsb = prove
    (`!a b (h:(N)word) bb j.
        byte_index a bb + 8 <= dimindex (:N) /\ j < dimindex (:N)
        ==> (bit j (set_byte a b h bb) <=>
             (if byte_index a bb <= j /\ j < byte_index a bb + 8
              then bit (j - byte_index a bb) b else bit j h))`,
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     REWRITE_TAC[cake_def "set_byte"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     ASM_SIMP_TAC[BIT_WORD_OR; BIT_WORD_SLICE_ALT;
                  ARITH_RULE `0 <= (i:num)`;
                  BIT_WORD_SHL; BIT_WORD_ZX; DIMINDEX_8] THEN
     MP_TAC(REWRITE_RULE[DIMINDEX_8]
       (ISPECL [`b:(8)word`; `j - byte_index (a:(N)word) bb`]
          BIT_TRIVIAL)) THEN
     ASM_CASES_TAC `byte_index (a:(N)word) bb <= j` THEN
     ASM_CASES_TAC `j < byte_index (a:(N)word) bb + 8` THEN
     ASM_CASES_TAC `bit j (h:(N)word)` THEN
     ASM_CASES_TAC
       `bit (j - byte_index (a:(N)word) bb) (b:(8)word)` THEN
     ASM_REWRITE_TAC[] THEN ARITH_NO_BIT_TAC) in
   let bib = prove
    (`!(k:num) bb. good_dimindex (:'a)
        ==> byte_index ((n2w k):'a word) bb + 8 <= dimindex (:'a)`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[cake_def "byte_index"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[cake_def "good_dimindex"] THEN
     DISCH_THEN(DISJ_CASES_THEN (fun th -> SUBST1_TAC th)) THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     (MP_TAC(SPEC `w2n ((n2w k):'a word)`
        (MATCH_MP DIVISION (ARITH_RULE `~(4 = 0)`))) ORELSE
      MP_TAC(SPEC `w2n ((n2w k):'a word)`
        (MATCH_MP DIVISION (ARITH_RULE `~(8 = 0)`)))) THEN
     COND_CASES_TAC THEN ARITH_TAC) in
   DISCH_TAC THEN REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
   ASM_SIMP_TAC[bsb; bib; COND_SAME_IFF]);;

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
     // ∧
     // LENGTH bs ≤ LENGTH (w1:α word list) * (dimindex (:α) DIV 8)
     // ∧ LENGTH (w1:α word list) ≤ LENGTH bs DIV (dimindex(:α) DIV 8) +1
     write_bytes bs' w1 be = write_bytes bs' w2 be)`)
  (* the words are written one by one: the first word of the one
     list and of the other are the same word written over the same
     bytes, which bytes_to_word_eq_lemma takes to the other bytes,
     and the rest follows by the induction with the bytes dropped *)
  (let len_drop = prove
    (`!k (l:A list). LENGTH (DROP k l) = LENGTH l - k`,
     INDUCT_TAC THEN LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC[DROP; LENGTH; SUB_0; NOT_SUC; SUC_SUB1;
                     ARITH_RULE `0 - SUC k = 0`; SUB_SUC]) in
   DISCH_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
   CASES_ON_NAME "w2" THEN
   REWRITE_TAC[cake_def "write_bytes"; LENGTH; NOT_SUC;
               ARITH_RULE `~(0 = SUC n)`] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[CONS_11; SUC_INJ] THEN REPEAT GEN_TAC THEN
   STRIP_TAC THEN CONJ_TAC THENL
    [FIRST_ASSUM(fun gd -> FIRST_ASSUM(fun lb -> FIRST_ASSUM(fun bw ->
       ACCEPT_TAC(MATCH_MP (cake_thm "bytes_to_word_eq_lemma")
         (CONJ gd (CONJ lb bw))))));
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     FIRST_ASSUM(fun th ->
       EXISTS_TAC(rand(rator(rator(lhand(concl th))))) THEN
       ASM_REWRITE_TAC[len_drop])]);;

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
  (* and the eight bytes of a word of sixty-four bits cover it the
     same way *)
  (let bsb = prove
    (`!a b (h:(N)word) bb j.
        byte_index a bb + 8 <= dimindex (:N) /\ j < dimindex (:N)
        ==> (bit j (set_byte a b h bb) <=>
             (if byte_index a bb <= j /\ j < byte_index a bb + 8
              then bit (j - byte_index a bb) b else bit j h))`,
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     REWRITE_TAC[cake_def "set_byte"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     ASM_SIMP_TAC[BIT_WORD_OR; BIT_WORD_SLICE_ALT;
                  ARITH_RULE `0 <= (i:num)`;
                  BIT_WORD_SHL; BIT_WORD_ZX; DIMINDEX_8] THEN
     MP_TAC(REWRITE_RULE[DIMINDEX_8]
       (ISPECL [`b:(8)word`; `j - byte_index (a:(N)word) bb`]
          BIT_TRIVIAL)) THEN
     ASM_CASES_TAC `byte_index (a:(N)word) bb <= j` THEN
     ASM_CASES_TAC `j < byte_index (a:(N)word) bb + 8` THEN
     ASM_CASES_TAC `bit j (h:(N)word)` THEN
     ASM_CASES_TAC
       `bit (j - byte_index (a:(N)word) bb) (b:(8)word)` THEN
     ASM_REWRITE_TAC[] THEN ARITH_NO_BIT_TAC) in
   let bib = prove
    (`!(k:num) bb. good_dimindex (:'a)
        ==> byte_index ((n2w k):'a word) bb + 8 <= dimindex (:'a)`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[cake_def "byte_index"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[cake_def "good_dimindex"] THEN
     DISCH_THEN(DISJ_CASES_THEN (fun th -> SUBST1_TAC th)) THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     (MP_TAC(SPEC `w2n ((n2w k):'a word)`
        (MATCH_MP DIVISION (ARITH_RULE `~(4 = 0)`))) ORELSE
      MP_TAC(SPEC `w2n ((n2w k):'a word)`
        (MATCH_MP DIVISION (ARITH_RULE `~(8 = 0)`)))) THEN
     COND_CASES_TAC THEN ARITH_TAC) in
   DISCH_TAC THEN
   SUBGOAL_THEN `good_dimindex (:'a)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[cake_def "good_dimindex"]; ALL_TAC] THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
   ASM_SIMP_TAC[bsb; bib; COND_SAME_IFF] THEN
   X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   REWRITE_TAC[cake_def "byte_index"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ASM_REWRITE_TAC[VAL_WORD] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   CONV_TAC NUM_REDUCE_CONV THEN ARITH_NO_BIT_TAC);;

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
  (* the four bytes of a word of thirty-two bits cover it, so what
     the fourth set_byte writes over is never read: every index is in
     one of the four byte ranges, whichever way round the endianness
     puts them *)
  (let bsb = prove
    (`!a b (h:(N)word) bb j.
        byte_index a bb + 8 <= dimindex (:N) /\ j < dimindex (:N)
        ==> (bit j (set_byte a b h bb) <=>
             (if byte_index a bb <= j /\ j < byte_index a bb + 8
              then bit (j - byte_index a bb) b else bit j h))`,
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     REWRITE_TAC[cake_def "set_byte"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     ASM_SIMP_TAC[BIT_WORD_OR; BIT_WORD_SLICE_ALT;
                  ARITH_RULE `0 <= (i:num)`;
                  BIT_WORD_SHL; BIT_WORD_ZX; DIMINDEX_8] THEN
     MP_TAC(REWRITE_RULE[DIMINDEX_8]
       (ISPECL [`b:(8)word`; `j - byte_index (a:(N)word) bb`]
          BIT_TRIVIAL)) THEN
     ASM_CASES_TAC `byte_index (a:(N)word) bb <= j` THEN
     ASM_CASES_TAC `j < byte_index (a:(N)word) bb + 8` THEN
     ASM_CASES_TAC `bit j (h:(N)word)` THEN
     ASM_CASES_TAC
       `bit (j - byte_index (a:(N)word) bb) (b:(8)word)` THEN
     ASM_REWRITE_TAC[] THEN ARITH_NO_BIT_TAC) in
   let bib = prove
    (`!(k:num) bb. good_dimindex (:'a)
        ==> byte_index ((n2w k):'a word) bb + 8 <= dimindex (:'a)`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[cake_def "byte_index"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[cake_def "good_dimindex"] THEN
     DISCH_THEN(DISJ_CASES_THEN (fun th -> SUBST1_TAC th)) THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     (MP_TAC(SPEC `w2n ((n2w k):'a word)`
        (MATCH_MP DIVISION (ARITH_RULE `~(4 = 0)`))) ORELSE
      MP_TAC(SPEC `w2n ((n2w k):'a word)`
        (MATCH_MP DIVISION (ARITH_RULE `~(8 = 0)`)))) THEN
     COND_CASES_TAC THEN ARITH_TAC) in
   DISCH_TAC THEN
   SUBGOAL_THEN `good_dimindex (:'a)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[cake_def "good_dimindex"]; ALL_TAC] THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
   ASM_SIMP_TAC[bsb; bib; COND_SAME_IFF] THEN
   X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   REWRITE_TAC[cake_def "byte_index"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ASM_REWRITE_TAC[VAL_WORD] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   CONV_TAC NUM_REDUCE_CONV THEN ARITH_NO_BIT_TAC);;

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
  (* and the same of a word of sixty-four bits, with eight
     set_bytes and one shift more *)
  (let bsb0 = prove
    (`!(a:(N)word) b (h:(N)word) bb j. j < dimindex (:N)
        ==> (bit j (set_byte a b h bb) <=>
             (if byte_index a bb <= j /\ j < byte_index a bb + 8
              then bit (j - byte_index a bb) b else bit j h))`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC[cake_def "set_byte"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     ASM_SIMP_TAC[BIT_WORD_OR; BIT_WORD_SLICE_ALT_LT; BIT_WORD_SHL;
                  BIT_WORD_ZX; DIMINDEX_8] THEN
     MP_TAC(REWRITE_RULE[DIMINDEX_8]
       (ISPECL [`b:(8)word`; `j - byte_index (a:(N)word) bb`]
          BIT_TRIVIAL)) THEN
     ASM_CASES_TAC `byte_index (a:(N)word) bb <= j` THEN
     ASM_CASES_TAC `j < byte_index (a:(N)word) bb + 8` THEN
     ASM_CASES_TAC `bit j (h:(N)word)` THEN
     ASM_CASES_TAC
       `bit (j - byte_index (a:(N)word) bb) (b:(8)word)` THEN
     ASM_REWRITE_TAC[] THEN ARITH_NO_BIT_TAC) in
   let killbit tm =
     TRY(MP_TAC(REWRITE_RULE[DIMINDEX_8]
           (ISPECL [`w:(8)word`; tm] BIT_TRIVIAL)) THEN
         ANTS_TAC THENL
          [ASM_ARITH_TAC;
           DISCH_THEN(fun th -> REWRITE_TAC[th])]) in
   let rules =
     let num k = mk_small_numeral k in
     let le a b = mk_binop `(<=):num->num->bool` a b in
     let lt a b = mk_binop `(<):num->num->bool` a b in
     let iv = `i:num` in
     let ks = [8; 16; 24; 32; 40; 48; 56; 64] in
     itlist (fun k acc -> itlist (fun k2 acc ->
       (if k <= k2
        then [ARITH_RULE(mk_imp(le (num k2) iv, le (num k) iv));
              ARITH_RULE(mk_imp(lt iv (num k), lt iv (num k2)))]
        else []) @
       (if k2 <= k
        then [ARITH_RULE(mk_imp(lt iv (num k2), mk_neg(le (num k) iv)));
              ARITH_RULE(mk_imp(le (num k) iv, mk_neg(lt iv (num k2))))]
        else []) @ acc) ks acc) ks
       [ARITH_RULE `i < 64 ==> (i - m < 64 <=> T)`;
        ARITH_RULE `(8 <= i - 8 <=> 16 <= i) /\
                    (8 <= i - 16 <=> 24 <= i) /\
                    (8 <= i - 24 <=> 32 <= i) /\
                    (8 <= i - 32 <=> 40 <= i) /\
                    (8 <= i - 40 <=> 48 <= i) /\
                    (8 <= i - 48 <=> 56 <= i) /\
                    (16 <= i - 32 <=> 48 <= i)`] in
   let usebe =
     TRY(FIRST_ASSUM(fun th ->
       let c = concl th in
       if is_var c || (is_neg c && is_var (rand c))
       then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th
       else fail())) in
   let numred =
     RULE_ASSUM_TAC(fun th ->
       try CONV_RULE NUM_REDUCE_CONV th with Failure _ -> th) in
   let stripconj =
     REPEAT(FIRST_X_ASSUM(fun th ->
       if is_conj (concl th) then STRIP_ASSUME_TAC th else fail())) in
   DISCH_TAC THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
   X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   ASM_SIMP_TAC[bsb0] THEN
   REWRITE_TAC[cake_def "byte_index"; cake_def "word_of_byte"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ASM_REWRITE_TAC[VAL_WORD; dimword] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_ZX; DIMINDEX_8] THEN
   SUBGOAL_THEN `(i:num) < 64` ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
   REPEAT COND_CASES_TAC THEN usebe THEN numred THEN stripconj THEN
   TRY(SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC) THEN
   REWRITE_TAC[ARITH_RULE
     `(((i - 32) - 16) - 8 = i - 56) /\ ((i - 32) - 16 = i - 48) /\
      ((i - 32) - 8 = i - 40) /\ ((i - 16) - 8 = i - 24) /\
      (i - 0 = i)`] THEN
   killbit `i:num` THEN killbit `i - 8` THEN killbit `i - 16` THEN
   killbit `i - 24` THEN killbit `i - 32` THEN killbit `i - 40` THEN
   killbit `i - 48` THEN
   ASM_SIMP_TAC rules THEN
   TRY(SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC));;

let word_of_byte_set_byte_32 = cake_theorem "word_of_byte_set_byte_32"
  (fun () ->
    `dimindex (:'a) = 32 ==>
     word_of_byte (w2w w) =
     set_byte (n2w 0) w
       (set_byte (n2w 1) w
         (set_byte (n2w 2) w
                   (set_byte (n2w 3) w (x:'a word) be) be) be) be`)
  (* the word that repeats a byte is what the four set_bytes of a
     word of thirty-two bits write the byte into: at every bit the
     shifts of word_of_byte give the bit of the byte at the position
     modulo eight, and so does the set_byte whose range the position
     falls in *)
  (let bsb0 = prove
    (`!(a:(N)word) b (h:(N)word) bb j. j < dimindex (:N)
        ==> (bit j (set_byte a b h bb) <=>
             (if byte_index a bb <= j /\ j < byte_index a bb + 8
              then bit (j - byte_index a bb) b else bit j h))`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC[cake_def "set_byte"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     ASM_SIMP_TAC[BIT_WORD_OR; BIT_WORD_SLICE_ALT_LT; BIT_WORD_SHL;
                  BIT_WORD_ZX; DIMINDEX_8] THEN
     MP_TAC(REWRITE_RULE[DIMINDEX_8]
       (ISPECL [`b:(8)word`; `j - byte_index (a:(N)word) bb`]
          BIT_TRIVIAL)) THEN
     ASM_CASES_TAC `byte_index (a:(N)word) bb <= j` THEN
     ASM_CASES_TAC `j < byte_index (a:(N)word) bb + 8` THEN
     ASM_CASES_TAC `bit j (h:(N)word)` THEN
     ASM_CASES_TAC
       `bit (j - byte_index (a:(N)word) bb) (b:(8)word)` THEN
     ASM_REWRITE_TAC[] THEN ARITH_NO_BIT_TAC) in
   let afacts =
     [ARITH_RULE `(i:num) < 8 ==> ~(8 <= i)`;
      ARITH_RULE `(i:num) < 8 ==> ~(16 <= i)`;
      ARITH_RULE `(i:num) < 8 ==> ~(24 <= i)`;
      ARITH_RULE `~((i:num) < 8) ==> 8 <= i`;
      ARITH_RULE `~((i:num) < 16) ==> 16 <= i`;
      ARITH_RULE `~((i:num) < 24) ==> 24 <= i`;
      ARITH_RULE `(i:num) < 16 ==> ~(16 <= i)`;
      ARITH_RULE `(i:num) < 24 ==> ~(24 <= i)`;
      ARITH_RULE `(i:num) < 16 ==> i - 8 < 8`;
      ARITH_RULE `(i:num) < 24 ==> i - 16 < 8`;
      ARITH_RULE `(i:num) < 32 ==> i - 24 < 8`;
      SUB_0;
      REWRITE_RULE[DIMINDEX_8] (ISPEC `w:(8)word` BIT_TRIVIAL);
      ARITH_RULE `~((i:num) < 16) ==> 8 <= i - 8`;
      ARITH_RULE `~((i:num) < 24) ==> 8 <= i - 16`;
      ARITH_RULE `(i:num) < 32 ==> i - 8 < 32`;
      ARITH_RULE `(i:num) < 32 ==> i - 16 < 32`;
      ARITH_RULE `(i:num) < 32 ==> i - 24 < 32`] in
   let killbit tm =
     TRY(MP_TAC(REWRITE_RULE[DIMINDEX_8]
           (ISPECL [`w:(8)word`; tm] BIT_TRIVIAL)) THEN
         ANTS_TAC THENL
          [ASM_ARITH_TAC;
           DISCH_THEN(fun th -> REWRITE_TAC[th])]) in
   DISCH_TAC THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
   X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   ASM_SIMP_TAC[bsb0] THEN
   REWRITE_TAC[cake_def "byte_index"; cake_def "word_of_byte"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ASM_REWRITE_TAC[VAL_WORD; dimword] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_ZX; DIMINDEX_8] THEN
   REWRITE_TAC[ARITH_RULE `(i - 16) - 8 = i - 24`] THEN
   SUBGOAL_THEN `(i:num) < 32` ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_CASES_TAC `(i:num) < 8` THEN
   ASM_CASES_TAC `(i:num) < 16` THEN
   ASM_CASES_TAC `(i:num) < 24` THEN
   REPEAT COND_CASES_TAC THEN
   TRY(SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC) THEN
   killbit `i:num` THEN killbit `i - 8` THEN killbit `i - 16` THEN
   ASM_SIMP_TAC afacts THEN
   TRY(SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC));;

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
  (* the bytes of a replicated byte written one after the other are
     what last_bytes writes, by the induction on the number *)
  (SUBGOAL_THEN
      `!n k a (w:'a word) bb bend. n <= k
         ==> bytes_to_word k a (REPLICATE n bb) w bend =
             last_bytes n bb a w bend`
      (fun th -> REPEAT GEN_TAC THEN
         DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
           (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST1_TAC)) THEN
         FIRST_ASSUM(fun le ->
           MATCH_ACCEPT_TAC(MATCH_MP (SPEC_ALL th) le)))
    THEN
    INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
     [ONCE_REWRITE_TAC[cake_def "bytes_to_word"] THEN
      ONCE_REWRITE_TAC[cake_def "last_bytes"] THEN
      REWRITE_TAC[REPLICATE] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      MATCH_REDUCE_TAC THEN REWRITE_TAC[];
      ONCE_REWRITE_TAC[cake_def "bytes_to_word"] THEN
      ONCE_REWRITE_TAC[cake_def "last_bytes"] THEN
      REWRITE_TAC[REPLICATE; NOT_SUC; ARITH_RULE `SUC n - 1 = n`] THEN
      COND_CASES_TAC THENL
       [FIRST_ASSUM(fun th -> MP_TAC th) THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_REDUCE_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

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
  (* decode_length shifts down by two (or three) more than
     make_byte_header shifted up, so it reads the length plus the
     word size divided by it, which is between the length divided by
     the word size and one more than that *)
  (let hi = prove
    (`!n r (i:num). n < 2 EXP r /\ r <= i
        ==> ~(bit i ((n2w n):'a word))`,
     MATCH_ACCEPT_TAC BIT_WORD_HI) in
   let tag5 = prove
    (`!fl j. bit j ((if fl then (n2w 7) else (n2w 23)):'a word)
             ==> j < 5`,
     REPEAT GEN_TAC THEN
     ASM_CASES_TAC `(j:num) < 5` THEN ASM_REWRITE_TAC[] THEN
     COND_CASES_TAC THENL
      [MP_TAC(ISPECL [`7`; `5`; `j:num`] hi);
       MP_TAC(ISPECL [`23`; `5`; `j:num`] hi)] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     ASM_SIMP_TAC[ARITH_RULE `~((j:num) < 5) ==> 5 <= j`]) in
   let ushr_shl = prove
    (`!(x:'a word) s k. (!j. bit j x ==> j + s < dimindex (:'a))
        ==> word_ushr (word_shl x s) (s + k) = word_ushr x k`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_SHL] THEN
     X_GEN_TAC `j:num` THEN DISCH_TAC THEN
     REWRITE_TAC[ARITH_RULE
       `s <= (j + s + k) /\ ((j + s + k) - s = j + k)`] THEN
     ASM_CASES_TAC `bit (j + k) (x:'a word)` THEN
     ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `j + k` th)) THEN
     ASM_REWRITE_TAC[] THEN ARITH_TAC) in
   let usedim =
     FIRST_X_ASSUM(fun dd ->
       let c = concl dd in
       if is_eq c &&
          (try fst(dest_const(fst(strip_comb(lhs c)))) = "dimindex"
           with Failure _ -> false)
       then RULE_ASSUM_TAC(REWRITE_RULE[dd;
              cake_def "backend_common_word_shift"]) THEN
            ASSUME_TAC dd
       else fail()) in
   STRIP_TAC THEN
   FIRST_ASSUM(DISJ_CASES_THEN ASSUME_TAC o
     REWRITE_RULE[cake_def "good_dimindex"]) THEN
   usedim THEN
   RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
   REWRITE_TAC[cake_def "decode_length";
               cake_def "make_byte_header"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THENL
    [SUBGOAL_THEN
       `32 - data_to_word_config_len_size c =
        (30 - data_to_word_config_len_size c) + 2`
       SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN
       `!j. bit j ((if fl then (n2w 7) else (n2w 23)):'a word)
            ==> j < (30 - data_to_word_config_len_size c) + 2`
       (fun th -> REWRITE_TAC[MATCH_MP USHR_OR_LOW th]) THENL
      [GEN_TAC THEN DISCH_THEN(fun th -> MP_TAC(MATCH_MP tag5 th)) THEN
       ASM_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN
       `!j. bit j ((n2w (len + 4)):'a word)
            ==> j + (30 - data_to_word_config_len_size c) <
                dimindex (:'a)`
       (fun th -> REWRITE_TAC[MATCH_MP ushr_shl th]) THENL
      [X_GEN_TAC `j:num` THEN
       ASM_CASES_TAC
         `j + (30 - data_to_word_config_len_size c) <
          dimindex (:'a)` THEN
       ASM_REWRITE_TAC[] THEN
       MP_TAC(ISPECL [`len + 4`;
                      `data_to_word_config_len_size c + 2`;
                      `j:num`] hi) THEN
       SUBGOAL_THEN `data_to_word_config_len_size c + 2 <= j`
         (fun th -> REWRITE_TAC[th]) THENL
        [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
       ALL_TAC] THEN
     REWRITE_TAC[VAL_WORD_USHR; VAL_WORD] THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
     SUBGOAL_THEN `(len + 4) MOD 4294967296 = len + 4` SUBST1_TAC THENL
      [MATCH_MP_TAC MOD_LT THEN
       TRANS_TAC LTE_TRANS
         `2 EXP (data_to_word_config_len_size c + 2)` THEN
       ASM_REWRITE_TAC[] THEN
       TRANS_TAC LE_TRANS `2 EXP 32` THEN
       SIMP_TAC[LE_EXP; ARITH] THEN
       CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
       ALL_TAC] THEN
     MP_TAC(SPEC `len:num` (MATCH_MP DIVISION (ARITH_RULE `~(4 = 0)`)))
     THEN
     MP_TAC(SPEC `len + 4` (MATCH_MP DIVISION
       (ARITH_RULE `~(4 = 0)`))) THEN
     ARITH_TAC;
     SUBGOAL_THEN
       `64 - data_to_word_config_len_size c =
        (61 - data_to_word_config_len_size c) + 3`
       SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN
       `!j. bit j ((if fl then (n2w 7) else (n2w 23)):'a word)
            ==> j < (61 - data_to_word_config_len_size c) + 3`
       (fun th -> REWRITE_TAC[MATCH_MP USHR_OR_LOW th]) THENL
      [GEN_TAC THEN DISCH_THEN(fun th -> MP_TAC(MATCH_MP tag5 th)) THEN
       ASM_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN
       `!j. bit j ((n2w (len + 8)):'a word)
            ==> j + (61 - data_to_word_config_len_size c) <
                dimindex (:'a)`
       (fun th -> REWRITE_TAC[MATCH_MP ushr_shl th]) THENL
      [X_GEN_TAC `j:num` THEN
       ASM_CASES_TAC
         `j + (61 - data_to_word_config_len_size c) <
          dimindex (:'a)` THEN
       ASM_REWRITE_TAC[] THEN
       MP_TAC(ISPECL [`len + 8`;
                      `data_to_word_config_len_size c + 3`;
                      `j:num`] hi) THEN
       SUBGOAL_THEN `data_to_word_config_len_size c + 3 <= j`
         (fun th -> REWRITE_TAC[th]) THENL
        [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
       ALL_TAC] THEN
     REWRITE_TAC[VAL_WORD_USHR; VAL_WORD] THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
     SUBGOAL_THEN
       `(len + 8) MOD 18446744073709551616 = len + 8`
       SUBST1_TAC THENL
      [MATCH_MP_TAC MOD_LT THEN
       TRANS_TAC LTE_TRANS
         `2 EXP (data_to_word_config_len_size c + 3)` THEN
       ASM_REWRITE_TAC[] THEN
       TRANS_TAC LE_TRANS `2 EXP 64` THEN
       SIMP_TAC[LE_EXP; ARITH] THEN
       CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
       ALL_TAC] THEN
     MP_TAC(SPEC `len:num` (MATCH_MP DIVISION (ARITH_RULE `~(8 = 0)`)))
     THEN
     MP_TAC(SPEC `len + 8` (MATCH_MP DIVISION
       (ARITH_RULE `~(8 = 0)`))) THEN
     ARITH_TAC]);;

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
  (DISCH_TAC THEN
   FIRST_ASSUM(fun th ->
     MATCH_MP_TAC(MATCH_MP
       (ONCE_REWRITE_RULE[TAUT `(p ==> q ==> r) <=> (q ==> p ==> r)`]
          memory_rel_rearrange) th)) THEN
   REWRITE_TAC[MEM] THEN MESON_TAC[]);;

let memory_rel_drop = cake_theorem "memory_rel_drop"
  (fun () ->
    `memory_rel c be ts refs sp st m dm (vs ++ vars) ==>
      memory_rel c be ts refs sp st m dm vars`)
  (DISCH_TAC THEN
   FIRST_ASSUM(fun th ->
     MATCH_MP_TAC(MATCH_MP
       (ONCE_REWRITE_RULE[TAUT `(p ==> q ==> r) <=> (q ==> p ==> r)`]
          memory_rel_rearrange) th)) THEN
   REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[]);;

let memory_rel_IMP_word_list_exists =
  cake_theorem "memory_rel_IMP_word_list_exists"
  (fun () ->
    `memory_rel c be ts refs sp st m dm vars /\ n <= sp /\
      FLOOKUP st NextFree = SOME (wordLang_Word f) ==>
      (word_list_exists f n * SEP_T) (fun2set (m,dm))`)
  (* the free space of the heap is the Unused element at the
     address that NextFree points at, and word_el makes it a
     word_list_exists of its length; the part of it that the
     statement asks for is the first n cells, which
     word_list_exists_ADD splits off, and the rest of the memory
     goes into the SEP_T *)
  (let hd_is n t =
     (try fst(dest_const(fst(strip_comb t))) = n
      with Failure _ -> false) in
   let rec facs t =
     if hd_is "STAR" t then
       let args = snd(strip_comb t) in
       facs (el 0 args) @ facs (el 1 args)
     else [t] in
   let star_T = prove
    (`!(p:(A->bool)->bool) q s. (p * q) s ==> (p * SEP_T) s`,
     REWRITE_TAC[STAR_SEP_T; STAR_def; SPLIT_LEMMA] THEN
     MESON_TAC[]) in
   let sep_T_tac = W(fun (asl,w) ->
     let tgt = lhand (rator w) in
     let ante = tryfind (fun (_,th) ->
       let c = concl th in
       if hd_is "STAR" (rator c) && mem tgt (facs (rator c))
       then rator c else fail()) asl in
     let rec remove1 t = function
         [] -> []
       | h :: rest -> if h = t then rest else h :: remove1 t rest in
     let rest = remove1 tgt (facs ante) in
     let st = fst(strip_comb ante) in
     let mk a b = mk_comb(mk_comb(st,a),b) in
     MATCH_MP_TAC star_T THEN
     EXISTS_TAC (end_itlist mk rest) THEN
     FIRST_ASSUM(fun th ->
       if (try hd_is "STAR" (rator (concl th))
           with Failure _ -> false)
       then MP_TAC th else fail()) THEN
     REWRITE_TAC[STAR_AC]) in
   REWRITE_TAC[cake_def "memory_rel"; cake_def "word_ml_inv";
               cake_def "abs_ml_inv";
               cake_def "bc_stack_ref_inv"] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM(fun th ->
     if hd_is "heap_in_memory_store" (concl th)
     then MP_TAC(REWRITE_RULE[cake_def "heap_in_memory_store"] th)
     else fail()) THEN
   STRIP_TAC THEN
   ASM_CASES_TAC `n = 0` THENL
    [ASM_REWRITE_TAC[CONJUNCT1 (cake_thm "word_list_exists_thm");
                     emp_STAR; SEP_T_def];
     ALL_TAC] THEN
   FIRST_ASSUM(fun t1 -> FIRST_ASSUM(fun t2 ->
     let e = REWRITE_RULE[injectivity "option";
                          injectivity "word_loc"]
               (TRANS (SYM t1) t2) in
     if is_eq (concl e) && is_var (lhs (concl e))
     then SUBST1_TAC e else fail())) THEN
   FIRST_X_ASSUM(fun th ->
     if hd_is "unused_space_inv" (concl th)
     then MP_TAC(REWRITE_RULE[cake_def "unused_space_inv"] th)
     else fail()) THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `~(sp' + sp1 = 0)` ASSUME_TAC THENL
    [UNDISCH_TAC `(n:num) <= sp` THEN
     UNDISCH_TAC `(sp:num) <= sp'` THEN
     UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC;
     ALL_TAC] THEN
   FIRST_X_ASSUM(fun imp -> FIRST_ASSUM(fun ne ->
     MP_TAC(MATCH_MP (cake_thm "heap_lookup_SPLIT") (MP imp ne)))) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   VAR_EQ_TAC THEN
   FIRST_X_ASSUM(fun th ->
     if (try hd_is "STAR" (rator (concl th)) with Failure _ -> false)
     then MP_TAC th else fail()) THEN
   REWRITE_TAC[cake_thm "word_heap_APPEND"; cake_def "word_heap";
               cake_def "word_el"] THEN
   SUBGOAL_THEN `(sp' + sp1) - 1 + 1 = n + ((sp' + sp1) - n)`
     SUBST1_TAC THENL
    [UNDISCH_TAC `(n:num) <= sp` THEN
     UNDISCH_TAC `(sp:num) <= sp'` THEN
     UNDISCH_TAC `~(sp' + sp1 = 0)` THEN ARITH_TAC;
     ALL_TAC] THEN
   REWRITE_TAC[cake_thm "word_list_exists_ADD"] THEN
   DISCH_TAC THEN sep_T_tac);;

let get_addr_0 = cake_theorem "get_addr_0"
  (fun () ->
    `FAPPLY
        (get_addr c n u) 0`)
  (* the lowest bit of get_addr is the one that get_lowerbits ors
     in, whichever of its two clauses applies *)
  (REWRITE_TAC[word_index; cake_def "get_addr"] THEN
   CASES_ON_NAME "u" THEN
   REWRITE_TAC[cake_def "get_lowerbits"] THEN MATCH_REDUCE_TAC THEN
   REWRITE_TAC[BIT_WORD_OR; BIT_WORD_1] THEN
   MESON_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> 0 < n`]);;

let word_addr_eq_Loc = cake_theorem "word_addr_eq_Loc"
  (fun () ->
    `word_addr c v = Loc l1 l2 <=> l2 = 0 /\ (?l2. v = gc_shared_Data
  (Loc l1 l2))`)
  (* only the Data of a Loc has a Loc for its word_addr, and the
     second component of it is zero *)
  (CASES_ON_NAME "v" THEN TRY(CASES_ON_NAME "a") THEN
   REWRITE_TAC[cake_def "word_addr"] THEN MATCH_REDUCE_TAC THEN
   REWRITE_TAC[distinctness "word_loc"; injectivity "word_loc";
               distinctness "heap_address";
               injectivity "heap_address"] THEN
   MESON_TAC[]);;

let blocks_unique_CodePtr = cake_theorem "blocks_unique_CodePtr"
  (fun () ->
    `blocks_unique ts (all_vs refs (MAP FST vars)) ==>
       blocks_unique ts (all_vs refs (CodePtr lab :: MAP FST
         vars))`)
  (* a CodePtr is no Block *)
  (let vcodeptr = prove
    (`!l ys. v_all_vs (CONS (CodePtr l) ys) =
        CONS (CodePtr l) (v_all_vs ys)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [cake_def "v_all_vs"] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   let inc = prove
    (`!refs l vs t a q.
        Block t a q IN all_vs refs (CONS (CodePtr l) vs) ==>
        Block t a q IN all_vs refs vs`,
     REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM; vcodeptr;
                 MEM; distinctness "dataSem_v"] THEN MESON_TAC[]) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN DISCH_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THEN ASM_MESON_TAC[inc]);;

let memory_rel_CodePtr = cake_theorem "memory_rel_CodePtr"
  (fun () ->
    `memory_rel c be ts refs sp st m dm vars ==>
      memory_rel c be ts refs sp st m dm ((CodePtr lab,Loc lab 0)
        :: vars)`)
  (* the root of a CodePtr is the Data of its Loc, which word_addr
     gives the Loc of; a CodePtr is no Block, so the timestamps and
     the unique blocks of the stack stay as they are, and it has no
     refs, so what the stack reaches stays as it is *)
  (let grc = prove
    (`!l. get_refs (CodePtr l) = []`,
     GEN_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [cake_def "get_refs"] THEN
     REWRITE_TAC[]) in
   let reach = prove
    (`!(sk:(dataSem_v)list) rfs n l.
        reachable_refs (CodePtr l :: sk) rfs n
        ==> reachable_refs sk rfs n`,
     REWRITE_TAC[cake_def "reachable_refs"; MEM] THEN
     MESON_TAC[grc; MEM]) in
   let waddr = el 2 (word_addr_clauses ()) in
   REWRITE_TAC[cake_def "memory_rel"; cake_def "word_ml_inv"] THEN
   REPEAT STRIP_TAC THEN ASM_EXISTS_TAC THEN
   ASM_REWRITE_TAC[] THEN
   (* the root that goes in front has the type that the statement
      left to the parser, so it is built with that type *)
   (fun (asl,w as gl) ->
      let v = fst(dest_exists w) in
      let tm = `CONS (gc_shared_Data (wordLang_Loc lab 0)) hs` in
      EXISTS_TAC (inst (type_match (type_of tm) (type_of v) []) tm)
        gl) THEN
   REWRITE_TAC[MAP; ALL2; waddr] THEN
   ASM_REWRITE_TAC[] THEN
   USE_CHANGED [cake_def "abs_ml_inv"; cake_def "bc_stack_ref_inv"]
   THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   REWRITE_TAC[cake_def "abs_ml_inv"; cake_def "bc_stack_ref_inv"] THEN
   REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[cake_def "roots_ok"]) THEN
     REWRITE_TAC[cake_def "roots_ok"; MEM;
                 distinctness "heap_address"] THEN
     FIRST_ASSUM MATCH_ACCEPT_TAC;
     MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`] THEN
     REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THENL
      [(fun (asl,w as gl) ->
         let th = PART_MATCH (lhs o rand)
                    (cake_thm "all_ts_cons_no_block") (rand w) in
         (MP_TAC th THEN REWRITE_TAC[distinctness "dataSem_v"] THEN
          DISCH_THEN(fun e -> ASM_REWRITE_TAC[e])) gl);
       MATCH_MP_TAC (cake_thm "blocks_unique_CodePtr") THEN
       ASM_REWRITE_TAC[];
       REWRITE_TAC[ALL2] THEN ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[cake_thm "v_inv_def"];
       X_GEN_TAC `nn:num` THEN STRIP_TAC THEN
       FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
        [FIRST_ASSUM(fun rr -> MATCH_ACCEPT_TAC(MATCH_MP reach rr));
         FIRST_ASSUM MATCH_ACCEPT_TAC]]]);;

let memory_rel_Block_IMP = cake_theorem "memory_rel_Block_IMP"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Block ts' tag vals,(v:'a
  word_loc)) :: vars) /\
      good_dimindex (:'a) ==>
      (?w. v = wordLang_Word w /\
          // ASK: If the Block has no vals then it's timestamp is 0
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
  (* what the root of a Block is: of an empty one the Data of its
     BlockNil, whose and with the complement of one leaves it alone
     (its lowest bit is clear, because sixteen times the tag plus
     two is even); of a non-empty one a pointer at the BlockRep,
     whose header the memory holds, with the length and the
     encode_header off the cond of the word_el and the two bits
     read off make_header.  The timestamp is below ts because tf
     binds it and its domain is below ts *)
  (let hd_is n t =
   (try fst(dest_const(fst(strip_comb t))) = n
    with Failure _ -> false) in
 let rec facs t =
   if hd_is "STAR" t then
     let args = snd(strip_comb t) in
     facs (el 0 args) @ facs (el 1 args)
   else [t] in
 let grab asl p =
   tryfind (fun (_,th) ->
     if (try p th with Failure _ -> false) then th else fail())
     asl in
 let is_hl th = hd_is "heap_lookup" (lhs (concl th)) in
 let sepfront names =
   W(fun (asl,w) ->
     let pred = rator (lhand w) in
     let fs = facs pred in
     let picked = map (fun n -> find (hd_is n) fs) names in
     let rest = filter (fun t -> not (mem t picked)) fs in
     let st = fst(strip_comb pred) in
     let mk a b = mk_comb(mk_comb(st,a),b) in
     let target = itlist mk picked (end_itlist mk rest) in
     SUBGOAL_THEN (mk_eq(pred,target)) SUBST1_TAC THENL
      [REWRITE_TAC[STAR_AC]; ALL_TAC]) in
 let swapmul a =
   let args = snd(strip_comb (rand a)) in
   let mul = fst(strip_comb (rand a)) in
   mk_comb(rator a, mk_comb(mk_comb(mul,el 1 args),el 0 args)) in
 let realaddr =
   W(fun (asl,w) ->
     let hl = grab asl is_hl in
     let hlen = grab asl (fun th ->
       hd_is "heap_length" (lhand (concl th))) in
     let cu = grab asl (fun th ->
       hd_is "FLOOKUP" (lhs (concl th)) &&
       fst(dest_const(rand(lhs(concl th)))) = "CurrHeap") in
     let gd = grab asl (fun th ->
       hd_is "good_dimindex" (concl th)) in
     let gat = tryfind (fun t ->
       find_term (fun u ->
         hd_is "get_addr" u && length (snd(strip_comb u)) = 3) t)
       (w :: map (fun (_,th) -> concl th) asl) in
     let mm = MATCH_MP (cake_thm "get_real_addr_get_addr")
                (CONJ hlen (CONJ hl (CONJ cu gd))) in
     let wv = find (fun v -> fst(dest_var v) = "w")
                (frees (concl mm)) in
     let th = SPEC (last (snd(strip_comb gat))) (GEN wv mm) in
     let a = rand (rhs (concl (CONJUNCT1 th))) in
     EXISTS_TAC (swapmul a) THEN
     STRIP_ASSUME_TAC(REWRITE_RULE[WORD_RULE (mk_eq(a,swapmul a))]
                        th)) in
   let shl16 = prove
    (`!(v:(N)word). word_shl v 4 = word 16 * v`,
     REWRITE_TAC[word_shl; GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD] THEN
     CONV_TAC MOD_DOWN_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[MULT_AC]) in
   let shl1 = prove
    (`!(v:(N)word). word_shl v 1 = word 2 * v`,
     REWRITE_TAC[word_shl; GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD] THEN
     CONV_TAC MOD_DOWN_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[MULT_AC]) in
   let andid = prove
    (`!(x:(N)word).
        word_and (word_shl x 4 + word 2) (word_not (word 1)) =
        x * word 16 + word 2`,
     GEN_TAC THEN
     SUBGOAL_THEN
       `word_shl (x:(N)word) 4 + word 2 = x * word 16 + word 2`
       SUBST1_TAC THENL
      [REWRITE_TAC[shl16] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
     SUBGOAL_THEN `~(bit 0 ((x:(N)word) * word 16 + word 2))`
       MP_TAC THENL
      [SUBGOAL_THEN `(x:(N)word) * word 16 + word 2 =
                     word_shl (word 8 * x + word 1) 1` SUBST1_TAC THENL
        [REWRITE_TAC[shl1] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
       REWRITE_TAC[BIT_WORD_SHL] THEN CONV_TAC NUM_REDUCE_CONV;
       ALL_TAC] THEN
     DISCH_TAC THEN
     REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_NOT;
                 BIT_WORD_1] THEN
     X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     ASM_CASES_TAC `(i:num) = 0` THEN ASM_REWRITE_TAC[] THEN
     CONV_TAC TAUT) in
   MEMORY_REL_TAC THEN
   ASM_CASES_TAC `vals:(dataSem_v)list = []` THEN
   ASM_REWRITE_TAC[] THENL
    [VAR_EQ_TAC THEN V_INV_TAC THEN
     REWRITE_TAC(word_addr_clauses ()) THEN
     W(fun (asl,w) ->
       EXISTS_TAC
         (rand (lhs (hd (conjuncts (snd(strip_exists w))))))) THEN
     ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
      [REWRITE_TAC[cake_def "BlockNil"; andid] THEN
       CONV_TAC WORD_RULE;
       REWRITE_TAC[word_index; BIT_WORD_AND; BIT_WORD_NOT;
                   BIT_WORD_1] THEN
       CONV_TAC NUM_REDUCE_CONV];
     V_INV_TAC THEN
     FIRST_ASSUM(fun ne ->
       if is_neg (concl ne)
       then RULE_ASSUM_TAC(REWRITE_RULE[cake_thm "v_inv_def"; ne])
       else fail()) THEN
     REPEAT(FIRST_X_ASSUM(fun th ->
       if is_exists (concl th) then CHOOSE_TAC th else fail())) THEN
     REPEAT(FIRST_X_ASSUM(fun th ->
       if is_conj (concl th) then STRIP_ASSUME_TAC th
       else fail())) THEN
     FIRST_ASSUM(fun e ->
       let c = concl e in
       if is_eq c && is_var (rand c) && hd_is "wordLang_Word" (lhs c)
       then SUBST1_TAC (SYM e) else fail()) THEN
     REWRITE_TAC[injectivity "word_loc"] THEN
     CONV_TAC(REDEPTH_CONV UNWIND_CONV) THEN
     REWRITE_TAC[cake_thm "get_addr_0"] THEN
     FIRST_X_ASSUM(fun th ->
       if hd_is "heap_in_memory_store" (concl th)
       then MP_TAC(REWRITE_RULE[cake_def "heap_in_memory_store"] th)
       else fail()) THEN
     STRIP_TAC THEN
     W(fun (asl,w) ->
       MP_TAC(MATCH_MP (cake_thm "heap_lookup_SPLIT")
                (grab asl is_hl))) THEN
     DISCH_THEN STRIP_ASSUME_TAC THEN
     VAR_EQ_TAC THEN
     realaddr THEN
     FIRST_X_ASSUM(fun th ->
       if (try hd_is "STAR" (rator (concl th))
           with Failure _ -> false)
       then MP_TAC th else fail()) THEN
     REWRITE_TAC[cake_thm "word_heap_APPEND"; cake_def "word_heap";
                 cake_def "BlockRep"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[cake_def "word_el"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[cake_def "word_payload"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[cake_def "misc_word_list"; LENGTH_MAP] THEN
     sepfront ["cond"] THEN
     REWRITE_TAC[cond_STAR] THEN
     DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
     sepfront ["set_sep_one"] THEN
     DISCH_THEN(fun sep ->
       let rd = MATCH_MP read_fun2set sep in
       EXISTS_TAC (rand (rhs (concl (CONJUNCT1 rd)))) THEN
       STRIP_ASSUME_TAC rd) THEN
     FIRST_ASSUM(fun lr ->
       if hd_is "ALL2" (concl lr) then
         let e = MATCH_MP LIST_REL_LENGTH lr in
         if fst(dest_var(rand(lhs(concl e)))) = "vals"
         then SUBST1_TAC e else fail()
       else fail()) THEN
     SUBGOAL_THEN `(ts':num) < ts` ASSUME_TAC THENL
      [FIRST_ASSUM(fun fl ->
         if (try hd_is "FLOOKUP" (lhs (concl fl)) &&
                  fst(dest_var(rand(lhs(concl fl)))) = "ts'"
             with Failure _ -> false)
         then MP_TAC(REWRITE_RULE[FLOOKUP_DEF] fl) else fail()) THEN
       COND_CASES_TAC THEN
       REWRITE_TAC[distinctness "option"] THEN
       DISCH_THEN(K ALL_TAC) THEN
       FIRST_ASSUM(fun i -> FIRST_ASSUM(fun sub ->
         MP_TAC(REWRITE_RULE[IN_ELIM_THM]
           (MATCH_MP (REWRITE_RULE[SUBSET] sub) i)))) THEN
       REWRITE_TAC[];
       ALL_TAC] THEN
     ASM_REWRITE_TAC[MULT_SYM] THEN
     REWRITE_TAC[cake_def "make_header"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     SUBGOAL_THEN
       `~(dimindex (:'a) - data_to_word_config_len_size c <= 3) /\
        ~(dimindex (:'a) - data_to_word_config_len_size c <= 2)`
       (fun th -> REWRITE_TAC[th]) THEN
     UNDISCH_TAC
       `data_to_word_config_len_size c + 7 < dimindex (:'a)` THEN
     ARITH_TAC]);;

let IMP_memory_rel_Number = cake_theorem "IMP_memory_rel_Number"
  (fun () ->
    `good_dimindex (:'a) /\ small_int (:'a) i /\
      memory_rel c be ts refs sp st m dm vars ==>
      memory_rel c be ts refs sp st m dm
       ((Number i,(wordLang_Word (Smallnum i):'a word_loc)) ::
         vars)`)
  (* the root of a small Number is the Data of its Smallnum, which
     abs_ml_inv_Num adds to the roots, and Smallnum is four times
     the integer up to the sign, so word_addr leaves it alone *)
  (let nmul = prove
    (`!(i:int). &0 <= i
        ==> n2w (num_of_int (&4 * i)) =
            (n2w 4 * n2w (num_of_int i):(N)word)`,
     REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `num_of_int (&4 * (i:int)) = 4 * num_of_int i`
       SUBST1_TAC THENL
      [FIRST_ASSUM(fun th ->
         GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
           [GSYM(MATCH_MP INT_OF_NUM_OF_INT th)]) THEN
       REWRITE_TAC[INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM];
       REWRITE_TAC[WORD_MUL]]) in
   let and_sym = WORD_BITWISE_RULE `(x:(N)word) && y = y && x` in
   let andnot1 = prove
    (`good_dimindex (:'a)
      ==> ((n2w 4 * v:'a word) && word_not (n2w 1) = n2w 4 * v) /\
          ((--(n2w 4) * v:'a word) && word_not (n2w 1) =
           --(n2w 4) * v)`,
     DISCH_TAC THEN
     SUBGOAL_THEN `word_not (n2w 1:'a word) = --(n2w 2)`
       SUBST1_TAC THENL
      [CONV_TAC WORD_RULE; ALL_TAC] THEN
     ONCE_REWRITE_TAC[and_sym] THEN
     ASM_SIMP_TAC[cake_thm "word_ml_inv_num_lemma";
                  cake_thm "word_ml_inv_neg_num_lemma"]) in
   let neg_mul = WORD_RULE
     `word_neg (word 4 * (v:(N)word)) = word_neg (word 4) * v` in
   let waddr = hd (word_addr_clauses ()) in
   REWRITE_TAC[cake_def "memory_rel"; cake_def "word_ml_inv"] THEN
   REPEAT STRIP_TAC THEN ASM_EXISTS_TAC THEN
   ASM_REWRITE_TAC[] THEN
   EXISTS_TAC
     `CONS (gc_shared_Data (wordLang_Word (Smallnum i:'a word))) hs`
   THEN
   REWRITE_TAC[MAP; ALL2; waddr] THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [MATCH_MP_TAC (cake_thm "abs_ml_inv_Num") THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[cake_def "Smallnum"] THEN COND_CASES_TAC THENL
      [SUBGOAL_THEN `&0 <= ((&0) - (i:int))` ASSUME_TAC THENL
        [ASM_INT_ARITH_TAC; ALL_TAC] THEN
       FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP nmul th]) THEN
       REWRITE_TAC[WORD_SUB_LZERO; neg_mul] THEN
       ASM_SIMP_TAC[andnot1];
       SUBGOAL_THEN `&0 <= (i:int)` ASSUME_TAC THENL
        [ASM_INT_ARITH_TAC; ALL_TAC] THEN
       FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP nmul th]) THEN
       ASM_SIMP_TAC[andnot1]]]);;

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
  (* the same statement as memory_rel_El', up to an existential
     that neither of the two uses: the source proves it again from
     memory_rel_El, with a Number put into the list for the offset,
     and the port takes the primed one, which is already there *)
  (let hd_is n t =
   (try fst(dest_const(fst(strip_comb t))) = n
    with Failure _ -> false) in
 let grab asl p =
   tryfind (fun (_,th) ->
     if (try p th with Failure _ -> false) then th else fail())
     asl in
   DISCH_TAC THEN
   FIRST_ASSUM(fun th ->
     MP_TAC(MATCH_MP (cake_thm "memory_rel_El'") th)) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   W(fun (asl,w) ->
     let pe = grab asl (fun th ->
       hd_is "wordLang_Word" (rhs (concl th))) in
     let ga = grab asl (fun th ->
       hd_is "get_real_addr" (lhs (concl th))) in
     let pw = rand (rhs (concl pe)) in
     let x = rand (rhs (concl ga)) in
     EXISTS_TAC pw THEN EXISTS_TAC x THEN EXISTS_TAC x) THEN
   ASM_REWRITE_TAC[]);;

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
  (* the tag mask keeps the bits of a header between the second and
     the one the length size leaves, and those are the bits of four
     times the tag; above them the tag has none, because it is below
     two to the width of its field *)
  (let hi = prove
    (`!n r (i:num). n < 2 EXP r /\ r <= i
        ==> ~(bit i ((n2w n):'a word))`,
     MATCH_ACCEPT_TAC BIT_WORD_HI) in
   let b3 = prove
    (`!j. j < dimindex (:'a)
          ==> (bit j ((n2w 3):'a word) <=> j < 2)`,
     GEN_TAC THEN DISCH_TAC THEN
     ASM_CASES_TAC `(j:num) < 2` THEN ASM_REWRITE_TAC[] THENL
      [FIRST_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP
         (ARITH_RULE `(j:num) < 2 ==> j = 0 \/ j = 1`)) THEN
       ASM_REWRITE_TAC[BIT_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
       ASM_ARITH_TAC;
       MP_TAC(ISPECL [`3`; `2`; `j:num`] hi) THEN
       ASM_SIMP_TAC[ARITH_RULE `~((j:num) < 2) ==> 2 <= j`] THEN
       CONV_TAC NUM_REDUCE_CONV]) in
   let btm = prove
    (`!c j. j < dimindex (:'a)
        ==> (bit j ((tag_mask c):'a word) <=>
             2 <= j /\
             j < dimindex (:'a) - data_to_word_config_len_size c)`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC[cake_def "tag_mask"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     ASM_SIMP_TAC[BIT_WORD_SLICE; BIT_WORD_NOT; BIT_WORD_0] THEN
     ASM_ARITH_TAC) in
   let bmh = prove
    (`!c (t:'a word) n j. j < dimindex (:'a)
        ==> (bit j (make_header c t n:'a word) <=>
             j < 2 \/ (2 <= j /\ bit (j - 2) t) \/
             (dimindex (:'a) - data_to_word_config_len_size c <= j /\
              bit (j - (dimindex (:'a) -
                        data_to_word_config_len_size c))
                  ((n2w n):'a word)))`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC[cake_def "make_header"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     ASM_SIMP_TAC[BIT_WORD_OR; BIT_WORD_SHL; b3] THEN
     CONV_TAC TAUT) in
   let n4 = prove
    (`!k. (n2w (4 * k):(N)word) = word_shl (n2w k) 2`,
     let shl4 = prove
      (`!(v:(N)word). word 4 * v = word_shl v 2`,
       REWRITE_TAC[word_shl; GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD] THEN
       CONV_TAC MOD_DOWN_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
       REWRITE_TAC[MULT_AC]) in
     GEN_TAC THEN REWRITE_TAC[GSYM shl4; WORD_MUL]) in
   DISCH_TAC THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
   X_GEN_TAC `j:num` THEN DISCH_TAC THEN
   ASM_SIMP_TAC[BIT_WORD_AND; btm; bmh; n4; BIT_WORD_SHL] THEN
   MP_TAC(ISPECL
     [`k:num`;
      `dimindex (:'a) - (data_to_word_config_len_size c + 2)`;
      `j - 2`] hi) THEN
   ASM_CASES_TAC `2 <= (j:num)` THEN
   ASM_CASES_TAC
     `j < dimindex (:'a) - data_to_word_config_len_size c` THEN
   ASM_CASES_TAC `bit (j - 2) ((n2w k):'a word)` THEN
   ASM_REWRITE_TAC[] THEN ARITH_NO_BIT_TAC);;

let make_header_and_2 = cake_theorem "make_header_and_2[local]"
  (fun () ->
    `((n2w 2) && make_header c w n) = (n2w 2)`)
  (* make_header ors a 3 in, whose second bit is the one that the 2
     masks out *)
  (let bw2 = prove
    (`!i. bit i (word 2:(N)word) <=> i = 1 /\ 1 < dimindex(:N)`,
     GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
       [ARITH_RULE `2 = 2 EXP 1`] THEN
     REWRITE_TAC[BIT_WORD_POW2]) in
   let bw3_1 = prove
    (`bit 1 (word 3:(N)word) <=> 1 < dimindex(:N)`,
     REWRITE_TAC[BIT_WORD] THEN CONV_TAC NUM_REDUCE_CONV) in
   REWRITE_TAC[cake_def "make_header"] THEN
   CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_OR; bw2] THEN
   GEN_TAC THEN DISCH_TAC THEN
   ASM_CASES_TAC `i = 1` THEN ASM_REWRITE_TAC[bw3_1] THEN
   CONV_TAC TAUT);;

let encode_header_tag_mask = cake_theorem "encode_header_tag_mask"
  (fun () ->
    `encode_header c (4 * tag) n = SOME (w:'a word) /\ good_dimindex
  (:'a) ==>
      tag < dimword (:'a) DIV 16 /\
      (w && (tag_mask c || (n2w 2))) = n2w (16 * tag + 2)`)
  (* the header of encode_header is make_header of four times the
     tag, whose and with the tag mask make_header_tag_mask says is
     sixteen times the tag and whose and with the two
     make_header_and_2 says is the two; the or of those two is their
     sum, because sixteen times a number has no bit as low as the
     second *)
  (
   let bw2 = prove
    (`!i. bit i (word 2:(N)word) <=> i = 1 /\ 1 < dimindex(:N)`,
     GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
       [ARITH_RULE `2 = 2 EXP 1`] THEN
     REWRITE_TAC[BIT_WORD_POW2]) in
   let n16 = prove
    (`!k. (n2w (16 * k):(N)word) = word_shl (n2w k) 4`,
     let shl16 = prove
      (`!(v:(N)word). word 16 * v = word_shl v 4`,
       REWRITE_TAC[word_shl; GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD] THEN
       CONV_TAC MOD_DOWN_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
       REWRITE_TAC[MULT_AC]) in
     GEN_TAC THEN REWRITE_TAC[GSYM shl16; WORD_MUL]) in
   let and2_0 = prove
    (`!k. (n2w (16 * k):(N)word) && n2w 2 = n2w 0`,
     GEN_TAC THEN REWRITE_TAC[n16] THEN
     REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0;
                 BIT_WORD_SHL; bw2] THEN
     X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     ASM_CASES_TAC `(i:num) = 1` THEN ASM_REWRITE_TAC[] THEN
     CONV_TAC NUM_REDUCE_CONV) in
   let orsum = prove
    (`!k. (n2w (16 * k):(N)word) || n2w 2 = n2w (16 * k + 2)`,
     GEN_TAC THEN
     MP_TAC(SPEC_ALL (ISPECL [`n2w (16 * k):(N)word`; `n2w 2:(N)word`]
       WORD_ADD_OR)) THEN
     REWRITE_TAC[and2_0] THEN
     DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
     REWRITE_TAC[WORD_ADD]) in
   let distr = WORD_BITWISE_RULE
     `!(x:(N)word) a b. x && (a || b) = (x && a) || (x && b)` in
   STRIP_TAC THEN
   USE_CHANGED [cake_def "encode_header"] THEN
   COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
   REWRITE_TAC[injectivity "option"] THEN
   DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
   FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
   CONJ_TAC THENL
    [ASM_ARITH_TAC;
     REWRITE_TAC[distr] THEN
     ONCE_REWRITE_TAC[WORD_AND_SYM] THEN
     REWRITE_TAC[cake_thm "make_header_and_2"] THEN
     SUBGOAL_THEN
       `tag_mask c && make_header c ((n2w (4 * tag)):'a word) n =
        n2w (4 * (4 * tag))`
       SUBST1_TAC THENL
      [MATCH_MP_TAC (cake_thm "make_header_tag_mask") THEN
       REWRITE_TAC[ARITH_RULE `d - (k + 2) = d - k - 2`] THEN
       ASM_REWRITE_TAC[];
       ONCE_REWRITE_TAC[WORD_AND_SYM] THEN
       REWRITE_TAC[ARITH_RULE `4 * (4 * tag) = 16 * tag`; orsum]]]);;

let memory_rel_tag_limit = cake_theorem "memory_rel_tag_limit"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Block ts' tag l,(w:'a
  word_loc)) :: rest) /\
      good_dimindex (:'a) ==>
      tag < dimword (:'a) DIV 16`)
  (* the tag of an empty Block is below the bound by what
     memory_rel_Block_IMP says, and the tag of a Block with a
     payload by the header that encode_header gives it *)
  (STRIP_TAC THEN USE2 memory_rel_Block_IMP THEN STRIP_TAC THEN
   OPEN_COND THEN
   TRY(FIRST_ASSUM ACCEPT_TAC) THEN
   USE2 encode_header_tag_mask THEN STRIP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC);;

let LESS_DIV_16_IMP = cake_theorem "LESS_DIV_16_IMP[local]"
  (fun () ->
    `n < k DIV 16 ==> 16 * n + 2 < (k:num)`)
  (ARITH_TAC);;

let MULT_BIT0 = cake_theorem "MULT_BIT0[local]"
  (fun () ->
    `BIT 0 (m * n) <=> BIT 0 m /\ BIT 0 n`)
  (* HOL4's BIT0_ODD, which the port does not have of bitTheory *)
  (let bit0 = prove
    (`!n. BIT 0 n <=> ODD n`,
     REWRITE_TAC[BIT; BITS; MOD_2EXP; DIV_2EXP; SUB_0; EXP; DIV_1;
                 ARITH_RULE `SUC 0 = 1`; EXP_1] THEN
     GEN_TAC THEN
     MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN
     REWRITE_TAC[ARITH_EQ] THEN
     MP_TAC(SPEC `n:num` EVEN_OR_ODD) THEN
     REWRITE_TAC[EVEN_MOD; ODD_MOD] THEN ARITH_TAC) in
   REWRITE_TAC[bit0; ODD_MULT]);;

let memory_rel_test_nil_eq = cake_theorem "memory_rel_test_nil_eq"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Block ts' tag l,(w:'a
  word_loc)) :: rest) /\
      n < dimword (:'a) DIV 16 /\ good_dimindex (:'a) ==>
      (?v. w = wordLang_Word v /\ (v = n2w (16 * n + 2) <=> tag =
        n /\ l = []))`)
  (* memory_rel_Block_IMP says what the word of the Block is: of an
     empty Block it is sixteen times the tag plus two, whose lowest
     bit is clear, and of a Block with values it is a pointer, whose
     lowest bit is set.  So of an empty Block the two words are
     equal exactly when the two numbers are, both of which are below
     dimword by LESS_DIV_16_IMP, and of a Block with values the test
     fails on the lowest bit *)
  (let ldi = cake_thm "LESS_DIV_16_IMP" in
   let n2w_11 = prove
    (`!a b. a < dimword (:N) /\ b < dimword (:N)
        ==> ((n2w a:(N)word) = n2w b <=> a = b)`,
     REPEAT STRIP_TAC THEN
     REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; GSYM dimword] THEN
     ASM_SIMP_TAC[MOD_LT]) in
   STRIP_TAC THEN
   FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun gd ->
     MP_TAC(MATCH_MP (cake_thm "memory_rel_Block_IMP")
       (CONJ mr gd)))) THEN
   DISCH_THEN(X_CHOOSE_THEN `u:'a word`
     (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
    [DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC) THEN
     EXISTS_TAC `n2w tag * n2w 16 + (n2w 2):'a word` THEN
     REWRITE_TAC[GSYM WORD_MUL; GSYM WORD_ADD] THEN
     MP_TAC(SPECL [`tag * 16 + 2`; `16 * n + 2`]
       (INST_TYPE [`:'a`,`:N`] n2w_11)) THEN
     ANTS_TAC THENL
      [CONJ_TAC THENL
        [MP_TAC(INST [`tag:num`,`n:num`;
                      `dimword (:'a)`,`k:num`] ldi);
         MP_TAC(INST [`dimword (:'a)`,`k:num`] ldi)] THEN
       ASM_ARITH_TAC;
       DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ARITH_TAC];
     STRIP_TAC THEN EXISTS_TAC `u:'a word` THEN REWRITE_TAC[] THEN
     DISCH_THEN SUBST_ALL_TAC THEN
     FIRST_ASSUM(fun b0 ->
       CONTR_TAC(REWRITE_RULE[word_index; BIT_WORD; EXP; DIV_1;
         ODD_ADD; ODD_MULT; ARITH] b0))]);;

let memory_rel_test_none_eq = cake_theorem "memory_rel_test_none_eq"
  (fun () ->
    `encode_header c (4 * n) len = (NONE:('a word) option) /\
      memory_rel c be ts refs sp st m dm ((Block ts' tag l,(w:'a
        word_loc)) :: rest) /\ ~(len = 0) /\ good_dimindex (:'a) ==>
      ~(tag = n /\ LENGTH l = len)`)
  (* the Block has values, because its length is not zero, so
     memory_rel_Block_IMP gives its header, and encode_header of the
     tag and that length is SOME of it, not NONE *)
  (REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `~(l:(dataSem_v)list = [])` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun gd ->
     MP_TAC(MATCH_MP (cake_thm "memory_rel_Block_IMP")
       (CONJ mr gd)))) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   (* the equations of the chosen witnesses are used up, the tag and
      the length first *)
   REPEAT(FIRST_X_ASSUM(fun th ->
     if is_eq(concl th) && is_var(lhand(concl th))
     then SUBST_ALL_TAC th else fail())) THEN
   FIRST_X_ASSUM(fun th ->
     let c = concl th in
     if is_eq c && is_var(rand c) && not(is_var(lhand c))
     then SUBST_ALL_TAC(SYM th) else fail()) THEN
   FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
     CONTR_TAC(REWRITE_RULE[th1; option_DISTINCT] th2))));;

let not_bit_lt_2exp = cake_theorem "not_bit_lt_2exp[local]"
  (fun () ->
    `!p x n. n < 2 EXP (p + 1) ==> ~(BIT (p + (x + 1)) n)`)
  (* the number is below 2 EXP (p + 1), so every bit of it from
     there up is zero *)
  (REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[BIT; BITS; MOD_2EXP;
                                       DIV_2EXP]) THEN
   SUBGOAL_THEN `n DIV (2 EXP (p + (x + 1))) = 0` SUBST1_TAC THENL
    [MATCH_MP_TAC DIV_LT THEN
     MATCH_MP_TAC LTE_TRANS THEN
     EXISTS_TAC `2 EXP (p + 1)` THEN ASM_REWRITE_TAC[LE_EXP] THEN
     CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
     REWRITE_TAC[ARITH_RULE `SUC a - a = 1`] THEN
     CONV_TAC NUM_REDUCE_CONV]);;

(* HOL4 data_to_word_memoryProofScript.sml:11090: ML code, not ported *)

let encode_header_EQ = cake_theorem "encode_header_EQ"
  (fun () ->
    `encode_header c t1 l1 = SOME (w1:'a word) /\
      encode_header c t2 l2 = SOME (w2:'a word) /\
        data_to_word_config_len_size
      c + 2 < dimindex (:'a) ==>
      (w1 = w2 <=> t1 = t2 /\ l1 = l2)`)
  (* two headers with the same bits have the same fields: the bit of
     the tag at j is the bit of the header at j plus two, the bit of
     the length at j is the one at j plus the shift, and above their
     fields both tags and both lengths have no bit at all *)
  (let hi = prove
    (`!n r (i:num). n < 2 EXP r /\ r <= i
        ==> ~(bit i ((n2w n):'a word))`,
     MATCH_ACCEPT_TAC BIT_WORD_HI) in
   let b3 = prove
    (`!j. j < dimindex (:'a)
          ==> (bit j ((n2w 3):'a word) <=> j < 2)`,
     GEN_TAC THEN DISCH_TAC THEN
     ASM_CASES_TAC `(j:num) < 2` THEN ASM_REWRITE_TAC[] THENL
      [FIRST_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP
         (ARITH_RULE `(j:num) < 2 ==> j = 0 \/ j = 1`)) THEN
       ASM_REWRITE_TAC[BIT_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
       ASM_ARITH_TAC;
       MP_TAC(ISPECL [`3`; `2`; `j:num`] hi) THEN
       ASM_SIMP_TAC[ARITH_RULE `~((j:num) < 2) ==> 2 <= j`] THEN
       CONV_TAC NUM_REDUCE_CONV]) in
   let bmh = prove
    (`!c (t:'a word) n j. j < dimindex (:'a)
        ==> (bit j (make_header c t n:'a word) <=>
             j < 2 \/ (2 <= j /\ bit (j - 2) t) \/
             (dimindex (:'a) - data_to_word_config_len_size c <= j /\
              bit (j - (dimindex (:'a) -
                        data_to_word_config_len_size c))
                  ((n2w n):'a word)))`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC[cake_def "make_header"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     ASM_SIMP_TAC[BIT_WORD_OR; BIT_WORD_SHL; b3] THEN
     CONV_TAC TAUT) in
   let n2w_inj = prove
    (`!a b m. a < 2 EXP m /\ b < 2 EXP m /\ m <= dimindex (:'a) /\
              ((n2w a):'a word = n2w b)
        ==> a = b`,
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o AP_TERM `val:'a word->num`) THEN
     REWRITE_TAC[VAL_WORD] THEN
     SUBGOAL_THEN
       `a < 2 EXP dimindex (:'a) /\ b < 2 EXP dimindex (:'a)`
       STRIP_ASSUME_TAC THENL
      [CONJ_TAC THEN TRANS_TAC LTE_TRANS `2 EXP m` THEN
       ASM_SIMP_TAC[LE_EXP; ARITH];
       ASM_SIMP_TAC[MOD_LT]]) in
   REWRITE_TAC[cake_def "encode_header"] THEN
   COND_CASES_TAC THEN COND_CASES_TAC THEN
   REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
   REPEAT(FIRST_X_ASSUM(fun th ->
     if is_conj (concl th) then STRIP_ASSUME_TAC th else fail())) THEN
   DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
     (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC)) THEN
   EQ_TAC THENL
    [DISCH_THEN(fun hdeq ->
       ASSUME_TAC(REWRITE_RULE[WORD_EQ_BITS_ALT] hdeq)) THEN
     SUBGOAL_THEN
       `((n2w t1):'a word = n2w t2) /\ ((n2w l1):'a word = n2w l2)`
       MP_TAC THENL
      [CONJ_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
       X_GEN_TAC `j:num` THEN DISCH_TAC THENL
        [ASM_CASES_TAC `j < dimindex (:'a) -
                        data_to_word_config_len_size c - 2` THENL
          [SUBGOAL_THEN
             `~(j + 2 < 2) /\ 2 <= j + 2 /\
              ~(dimindex (:'a) - data_to_word_config_len_size c <=
                j + 2) /\
              (j + 2) - 2 = j /\ j + 2 < dimindex (:'a)`
             STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
           FIRST_X_ASSUM(fun bits -> MP_TAC(SPEC `j + 2` bits)) THEN
           ASM_SIMP_TAC[bmh] THEN TRY(DISCH_THEN ACCEPT_TAC);
           MP_TAC(ISPECL
             [`t1:num`; `dimindex (:'a) -
               data_to_word_config_len_size c - 2`; `j:num`] hi) THEN
           MP_TAC(ISPECL
             [`t2:num`; `dimindex (:'a) -
               data_to_word_config_len_size c - 2`; `j:num`] hi) THEN
           ASM_SIMP_TAC[ARITH_RULE `~((j:num) < m) ==> m <= j`] THEN
           DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
           DISCH_THEN(fun th -> REWRITE_TAC[th])];
         ASM_CASES_TAC `j < data_to_word_config_len_size c` THENL
          [SUBGOAL_THEN
             `~(j + (dimindex (:'a) -
                     data_to_word_config_len_size c) < 2) /\
              2 <= j + (dimindex (:'a) -
                        data_to_word_config_len_size c) /\
              dimindex (:'a) - data_to_word_config_len_size c <=
              j + (dimindex (:'a) -
                   data_to_word_config_len_size c) /\
              (j + (dimindex (:'a) -
                    data_to_word_config_len_size c)) -
              (dimindex (:'a) - data_to_word_config_len_size c) = j /\
              j + (dimindex (:'a) -
                   data_to_word_config_len_size c) <
              dimindex (:'a) /\
              dimindex (:'a) - data_to_word_config_len_size c - 2 <=
              (j + (dimindex (:'a) -
                    data_to_word_config_len_size c)) - 2`
             STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
           FIRST_X_ASSUM(fun bits -> MP_TAC(SPEC
             `j + (dimindex (:'a) -
                   data_to_word_config_len_size c)` bits)) THEN
           ASM_SIMP_TAC[bmh] THEN
           MP_TAC(ISPECL
             [`t1:num`; `dimindex (:'a) -
               data_to_word_config_len_size c - 2`;
              `(j + (dimindex (:'a) -
                     data_to_word_config_len_size c)) - 2`] hi) THEN
           MP_TAC(ISPECL
             [`t2:num`; `dimindex (:'a) -
               data_to_word_config_len_size c - 2`;
              `(j + (dimindex (:'a) -
                     data_to_word_config_len_size c)) - 2`] hi) THEN
           ASM_REWRITE_TAC[] THEN
           DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
           DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
           TRY(DISCH_THEN ACCEPT_TAC);
           MP_TAC(ISPECL
             [`l1:num`; `data_to_word_config_len_size c`;
              `j:num`] hi) THEN
           MP_TAC(ISPECL
             [`l2:num`; `data_to_word_config_len_size c`;
              `j:num`] hi) THEN
           ASM_SIMP_TAC[ARITH_RULE `~((j:num) < m) ==> m <= j`] THEN
           DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
           DISCH_THEN(fun th -> REWRITE_TAC[th])]];
       STRIP_TAC THEN CONJ_TAC THENL
        [MATCH_MP_TAC n2w_inj THEN
         EXISTS_TAC `dimindex (:'a) -
                     data_to_word_config_len_size c - 2` THEN
         ASM_REWRITE_TAC[] THEN ARITH_TAC;
         MATCH_MP_TAC n2w_inj THEN
         EXISTS_TAC `data_to_word_config_len_size c` THEN
         ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]];
     DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN REFL_TAC]);;

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
  (* the header of a reference's array, read out of the memory: as
     for a byte array, the v_inv of the RefPtr gives the pointer
     (whose lowest bit is set, which is get_addr_0), bc_ref_inv
     gives the RefBlock of the heap and get_real_addr_get_addr the
     address.  The cond of the word_el says what decode_length of
     the header is, and the three bits of the statement are read
     off make_header: the tag of a RefTag is two, which puts the
     bit at three, and the length sits above the len_size, which
     heap_in_memory_store keeps seven below the word size *)
  (let hd_is n t =
     (try fst(dest_const(fst(strip_comb t))) = n
      with Failure _ -> false) in
   let rec facs t =
     if hd_is "STAR" t then
       let args = snd(strip_comb t) in
       facs (el 0 args) @ facs (el 1 args)
     else [t] in
   let grab asl p =
     tryfind (fun (_,th) ->
       if (try p th with Failure _ -> false) then th else fail()) asl in
   let is_hl th = hd_is "heap_lookup" (lhs (concl th)) in
   let sepfront names =
     W(fun (asl,w) ->
       let pred = rator (lhand w) in
       let fs = facs pred in
       let picked = map (fun n -> find (hd_is n) fs) names in
       let rest = filter (fun t -> not (mem t picked)) fs in
       let st = fst(strip_comb pred) in
       let mk a b = mk_comb(mk_comb(st,a),b) in
       let target = itlist mk picked (end_itlist mk rest) in
       SUBGOAL_THEN (mk_eq(pred,target)) SUBST1_TAC THENL
        [REWRITE_TAC[STAR_AC]; ALL_TAC]) in
   MEMORY_REL_TAC THEN V_INV_TAC THEN
   TRY(FIRST_ASSUM(fun t1 -> FIRST_ASSUM(fun t2 ->
     CONTR_TAC(REWRITE_RULE[injectivity "option";
                            distinctness "bvlSem_ref"]
                 (TRANS (SYM t1) t2))))) THEN
   FIRST_ASSUM(fun e ->
     let c = concl e in
     if is_eq c && is_var (rand c) && hd_is "wordLang_Word" (lhs c)
     then SUBST1_TAC (SYM e) else fail()) THEN
   REWRITE_TAC[injectivity "word_loc"] THEN
   CONV_TAC(REDEPTH_CONV UNWIND_CONV) THEN
   REWRITE_TAC[cake_thm "get_addr_0"] THEN
   FIRST_X_ASSUM(fun th ->
     if is_forall (concl th) &&
        hd_is "bc_ref_inv" (rand (snd(strip_forall(concl th))))
     then MP_TAC(SPEC `p:num` th) else fail()) THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL
      [REWRITE_TAC[cake_def "reachable_refs"; MEM] THEN
       EXISTS_TAC `RefPtr bl p:dataSem_v` THEN
       EXISTS_TAC `p:num` THEN
       REWRITE_TAC[cake_def "get_refs"; MEM;
                   CONJUNCT1(SPEC_ALL RTC_RULES)];
       ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   REWRITE_TAC[cake_def "bc_ref_inv"] THEN
   ASM_SIMP_TAC[FLOOKUP_DEF] THEN
   MATCH_REDUCE_TAC THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   FIRST_X_ASSUM(fun th ->
     if hd_is "heap_in_memory_store" (concl th)
     then MP_TAC(REWRITE_RULE[cake_def "heap_in_memory_store"] th)
     else fail()) THEN
   STRIP_TAC THEN
   W(fun (asl,w) ->
     MP_TAC(MATCH_MP (cake_thm "heap_lookup_SPLIT")
              (grab asl is_hl))) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   VAR_EQ_TAC THEN
   FIRST_X_ASSUM(fun th ->
     if (try hd_is "fmap_apply" (lhs (concl th))
         with Failure _ -> false)
     then SUBST_ALL_TAC th else fail()) THEN
   W(fun (asl,w) ->
     let hl = grab asl is_hl in
     let hlen = grab asl (fun th ->
       hd_is "heap_length" (lhand (concl th))) in
     let cu = grab asl (fun th ->
       hd_is "FLOOKUP" (lhs (concl th)) &&
       fst(dest_const(rand(lhs(concl th)))) = "CurrHeap") in
     let gd = grab asl (fun th -> concl th = `good_dimindex (:'a)`) in
     let gat = tryfind (fun t ->
       find_term (fun u ->
         hd_is "get_addr" u && length (snd(strip_comb u)) = 3) t)
       (w :: map (fun (_,th) -> concl th) asl) in
     let th = SPEC (last (snd(strip_comb gat)))
       (GEN `w:('a)word_loc`
         (MATCH_MP (cake_thm "get_real_addr_get_addr")
           (CONJ hlen (CONJ hl (CONJ cu gd))))) in
     let r = rhs (concl (CONJUNCT1 th)) in
     let a = rand r in
     let args = snd(strip_comb (rand a)) in
     let mul = fst(strip_comb (rand a)) in
     let swap = mk_comb(rator a,
                  mk_comb(mk_comb(mul,el 1 args),el 0 args)) in
     let sw = WORD_RULE (mk_eq(a,swap)) in
     EXISTS_TAC swap THEN
     STRIP_ASSUME_TAC(REWRITE_RULE[sw] th)) THEN
   FIRST_X_ASSUM(fun th ->
     if (try hd_is "STAR" (rator (concl th)) with Failure _ -> false)
     then MP_TAC th else fail()) THEN
   REWRITE_TAC[cake_thm "word_heap_APPEND"; cake_def "word_heap";
               cake_def "RefBlock"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[cake_def "word_el"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[cake_def "word_payload"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[cake_def "misc_word_list"; LENGTH_MAP] THEN
   sepfront ["cond"] THEN
   REWRITE_TAC[cond_STAR] THEN
   DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
   sepfront ["set_sep_one"] THEN
   DISCH_THEN(fun sep ->
     let rd = MATCH_MP read_fun2set sep in
     EXISTS_TAC (rand (rhs (concl (CONJUNCT1 rd)))) THEN
     STRIP_ASSUME_TAC rd) THEN
   FIRST_ASSUM(fun lr ->
     if hd_is "ALL2" (concl lr)
     then SUBST1_TAC(SYM(MATCH_MP LIST_REL_LENGTH lr)) else fail()) THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[cake_def "make_header"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   UNDISCH_TAC `data_to_word_config_len_size c + 7 < dimindex (:'a)`
     THEN ARITH_TAC);;

let blocks_unique_Thunk = cake_theorem "blocks_unique_Thunk"
  (fun () ->
    `lookup p refs = SOME (Thunk ev x) /\
     blocks_unique ts (all_vs refs (RefPtr bl p :: MAP FST vars))
       ==>
       blocks_unique ts (all_vs refs (x :: MAP FST vars))`)
  (* the value of the thunk is a value of the refs already *)
  (let vcons = prove
    (`!(v:dataSem_v) xs y. MEM y (v_all_vs (CONS v xs)) <=>
        MEM y (v_all_vs [v]) \/ MEM y (v_all_vs xs)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
       [prove(`!(h:dataSem_v) t. CONS h t = APPEND [h] t`,
              REWRITE_TAC[APPEND])] THEN
     REWRITE_TAC[v_all_vs_append; MEM_APPEND]) in
   let inc = prove
    (`!refs p ev x bl vs t a q.
        sptree_lookup p refs = SOME (Thunk ev x) /\
        Block t a q IN all_vs refs (CONS x vs) ==>
        Block t a q IN all_vs refs (CONS (RefPtr bl p) vs)`,
     REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM] THEN
     MESON_TAC[vcons]) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN STRIP_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THEN ASM_MESON_TAC[inc]);;

let blocks_unique_Thunk2 = cake_theorem "blocks_unique_Thunk2"
  (fun () ->
    `lookup p refs = SOME (Thunk ev v') /\
     blocks_unique ts (all_vs refs (RefPtr F p :: MAP FST vars))
       ==>
       blocks_unique ts (all_vs refs (v' :: RefPtr F p :: MAP FST
         vars))`)
  (* the value of the Thunk at p is already among the values of the
     references, so the stack with it in front has the same values
     as the stack without it, and the uniqueness carries over.  The
     element of the goal picks the assumption about it (there are
     two), and the two sides of the transfer are split the same way
     so that the disjuncts match one by one *)
  (
   let cons_app = prove
    (`!(h:dataSem_v) t. CONS h t = APPEND [h] t`,
     REWRITE_TAC[APPEND]) in
   let hd_is n t =
     (try fst(dest_const(fst(strip_comb t))) = n
      with Failure _ -> false) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
   W(fun (asl,w) ->
     let gel = el 0 (snd(strip_comb w)) in
     FIRST_ASSUM(fun inm ->
       let c = concl inm in
       if not (hd_is "IN" c) || not (el 0 (snd(strip_comb c)) = gel)
       then fail() else
       FIRST_ASSUM(fun lk ->
         if not (hd_is "=" (concl lk)) then fail() else
         MP_TAC(REWRITE_RULE[cake_def "all_vs"; IN_UNION;
                             IN_ELIM_THM; v_all_vs_append;
                             MEM_APPEND]
                  (ONCE_REWRITE_RULE[cons_app] inm)) THEN
         MP_TAC lk THEN
         REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM;
                     v_all_vs_append; MEM_APPEND] THEN
         MESON_TAC[]))));;

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
  (REPEAT STRIP_TAC THEN ASM_MESON_TAC[get_byte_set_byte_diff]);;

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
  (* n divides k, so k is n times the quotient and MOD_MOD gives
     the modulus of the modulus *)
  (STRIP_TAC THEN
   SUBGOAL_THEN `?q. k:num = n * q` (CHOOSE_THEN SUBST_ALL_TAC) THENL
    [EXISTS_TAC `k DIV n` THEN
     MP_TAC(SPECL [`k:num`; `n:num`] DIVISION) THEN
     ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
     ASM_REWRITE_TAC[ADD_CLAUSES] THEN MESON_TAC[MULT_SYM];
     ASM_REWRITE_TAC[MOD_MOD]]);;

let w2n_add_byte_align_lemma = cake_theorem "w2n_add_byte_align_lemma"
  (fun () ->
    `good_dimindex (:'a) ==>
      w2n (a' + byte_align (a:'a word)) MOD (dimindex (:'a) DIV 8)
        =
      w2n a' MOD (dimindex (:'a) DIV 8)`)
  (* the alignment of a word is the word shifted down and up again,
     so its lowest bits are clear and adding it does not change the
     value by the bytes in a word -- which is two to the shift, as
     the two good dimindexes give *)
  (let LOG2_RED =
     REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV(REWR_CONV LOG2) THENC
                          NUM_REDUCE_CONV THENC REWRITE_CONV[])) in
   let slice_shl = prove
    (`!p (w:(N)word).
        word_slice (dimindex (:N) - 1) p w =
        word_shl (word_ushr w p) p`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[word_slice; word_bits; WORD_EQ_BITS_ALT;
                 BIT_WORD_SHL; BIT_WORD_SUBWORD; BIT_WORD_USHR] THEN
     X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     ASM_CASES_TAC `p:num <= i` THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN
       `i - p < MIN ((dimindex (:N) - 1 + 1) - p) (dimindex (:N))`
       (fun th -> REWRITE_TAC[th]) THENL
      [REWRITE_TAC[ARITH_RULE
         `MIN a b = if a <= b then a else b`] THEN
       COND_CASES_TAC THEN ASM_ARITH_TAC;
       REWRITE_TAC[ARITH_RULE `p + (i - p) = (i - p) + p`]]) in
   let main = prove
    (`!p d (x:(N)word) y. d = 2 EXP p /\ p <= dimindex (:N)
        ==> w2n (x + word_shl y p) MOD d = w2n x MOD d`,
     REPEAT GEN_TAC THEN
     DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
     REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SHL; MOD_MOD_EXP_MIN] THEN
     ASM_SIMP_TAC[ARITH_RULE `p <= d ==> MIN d p = p`] THEN
     ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
     REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
     ASM_SIMP_TAC[ARITH_RULE `p <= d ==> MIN d p = p`] THEN
     REWRITE_TAC[MOD_MULT; ADD_CLAUSES; MOD_MOD_REFL]) in
   DISCH_TAC THEN
   REWRITE_TAC[cake_def "byte_align"; cake_def "align";
               slice_shl] THEN
   MATCH_MP_TAC main THEN
   FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o
     REWRITE_RULE[cake_def "good_dimindex"]) THEN
   CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC LOG2_RED THEN
   CONV_TAC NUM_REDUCE_CONV);;

let get_byte_byte_align = cake_theorem "get_byte_byte_align"
  (fun () ->
    `good_dimindex (:'a) ==>
      get_byte (a' + byte_align a) w be = get_byte a' (w:'a word)
        be`)
  (* which byte an address picks out is its remainder by the bytes
     in a word, which adding a byte aligned word does not change *)
  (DISCH_TAC THEN
   REWRITE_TAC[cake_def "get_byte"] THEN
   AP_TERM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[cake_def "byte_index"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ASM_SIMP_TAC[cake_thm "w2n_add_byte_align_lemma"]);;

let get_byte_eq = cake_theorem "get_byte_eq"
  (fun () ->
    `good_dimindex (:'a) /\ a = byte_align a + a' ==>
      get_byte a w be = get_byte a' (w:'a word) be`)
  (* the byte that an address selects does not change when the
     address is taken modulo the word it is in *)
  (STRIP_TAC THEN
   FIRST_X_ASSUM(fun th -> ONCE_REWRITE_TAC[th]) THEN
   ONCE_REWRITE_TAC[WORD_ADD_SYM] THEN
   FIRST_ASSUM(fun gd ->
     MATCH_ACCEPT_TAC(MATCH_MP get_byte_byte_align gd)));;

let write_bytes_same = cake_theorem "write_bytes_same"
  (fun () ->
    `!ws b1 b2.
     (!n. n < LENGTH (ws:('a word) list) * (dimindex (:'a) DIV 8)
       ==> n < LENGTH b1 /\ n < LENGTH b2 /\ EL n b1 = EL n b2) ==>
       write_bytes b1 ws be = write_bytes b2 ws be`)
  (* the words come out the same because every byte that one of
     them reads is the same in the two lists: the head word reads
     the first bytes (the bytes_to_word of a list of bytes that
     agree up to the count), and the tail reads the rest, which the
     DROP shifts by the count *)
  (let btw = prove
    (`!k a b1 b2 (w:(N)word) be.
        (!n. n < k ==> n < LENGTH b1 /\ n < LENGTH b2 /\
             EL n b1 = EL n b2)
        ==> bytes_to_word k a b1 w be = bytes_to_word k a b2 w be`,
     INDUCT_TAC THEN REPEAT GEN_TAC THENL
      [REWRITE_TAC[cake_def "bytes_to_word"]; ALL_TAC] THEN
     DISCH_TAC THEN
     GEN_REWRITE_TAC BINOP_CONV [cake_def "bytes_to_word"] THEN
     REWRITE_TAC[NOT_SUC] THEN
     FIRST_ASSUM(MP_TAC o SPEC `0`) THEN
     REWRITE_TAC[LT_0] THEN STRIP_TAC THEN
     MP_TAC(ISPEC `b1:(word8)list` list_CASES) THEN
     DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
       (X_CHOOSE_THEN `h1:word8`
         (X_CHOOSE_THEN `t1:(word8)list` SUBST_ALL_TAC))) THENL
      [ASM_MESON_TAC[LENGTH; LT_REFL]; ALL_TAC] THEN
     MP_TAC(ISPEC `b2:(word8)list` list_CASES) THEN
     DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
       (X_CHOOSE_THEN `h2:word8`
         (X_CHOOSE_THEN `t2:(word8)list` SUBST_ALL_TAC))) THENL
      [ASM_MESON_TAC[LENGTH; LT_REFL]; ALL_TAC] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[EL; HD]) THEN
     ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     REWRITE_TAC[SUC_SUB1] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     X_GEN_TAC `n:num` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
     ASM_REWRITE_TAC[LT_SUC; LENGTH; EL; TL] THEN
     ASM_ARITH_TAC) in
   let lt1 = ARITH_RULE `!n m b:num. n < b ==> n < m * b + b` in
   let lt2 = ARITH_RULE
     `!n m b:num. n < m * b ==> n + b < m * b + b` in
   let lt3 = ARITH_RULE `!n b l:num. n + b < l ==> n < l - b` in
   LIST_INDUCT_TAC THEN
   REWRITE_TAC[cake_def "write_bytes"] THEN
   REPEAT GEN_TAC THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[CONS_11] THEN
   DISCH_TAC THEN CONJ_TAC THENL
    [MATCH_MP_TAC btw THEN
     X_GEN_TAC `n:num` THEN DISCH_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     REWRITE_TAC[LENGTH; MULT] THEN
     MATCH_MP_TAC lt1 THEN ASM_REWRITE_TAC[];
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     X_GEN_TAC `n:num` THEN DISCH_TAC THEN
     REWRITE_TAC[LENGTH_DROP] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `n + dimindex (:'a) DIV 8`) THEN
     ANTS_TAC THENL
      [REWRITE_TAC[LENGTH; MULT] THEN
       MATCH_MP_TAC lt2 THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     STRIP_TAC THEN ASM_SIMP_TAC[EL_DROP] THEN
     REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC lt3) THEN
     ASM_REWRITE_TAC[]]);;

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
  (* every rule of v_inv for a RefPtr says that the pointer is in
     the refs: the first through the domain of f, the other two
     with the lookup itself *)
  (MEMORY_REL_TAC THEN V_INV_TAC THEN
   ASM_MESON_TAC[domain_lookup; SUBSET]);;

(* a compare-by-pointer RefPtr can never point at a MutBlock: v_inv's RefPtr
   case demands ~b when the ref is a MutBlock *)
let memory_rel_MutBlock_IMP_F =
  cake_theorem "memory_rel_MutBlock_IMP_F[local]"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((RefPtr T p,(v:'a word_loc)) ::
  vars) /\
     lookup p refs = SOME (bvlSem_MutBlock tg fin ls cv rs) ==> F`)
  (* a RefPtr T is no MutBlock: every rule of v_inv that gives one
     a root says so *)
  (MEMORY_REL_TAC THEN V_INV_TAC THEN ASM_MESON_TAC[]);;

let memory_rel_RefPtr_T_IMP = cake_theorem "memory_rel_RefPtr_T_IMP"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((RefPtr T p,v) :: vars) /\
     good_dimindex (:'a) ==>
       (?w a x.
         v = wordLang_Word w /\ FAPPLY w 0 /\
         (
          // (word_bit 4 x ⇒ word_bit 2 x) ∧
          word_bit 3 x <=> ~(word_bit 2 x)) /\
         get_real_addr c st w = SOME a /\
         get_real_simple_addr c st w = SOME a /\
         m a = wordLang_Word (x:'a word) /\ a IN dm)`)
  (* a RefPtr T is no thunk (the rule of v_inv for one asks for a
     RefPtr F) and no MutBlock, so the four cases of the value in
     the refs are the two arrays and two contradictions *)
  (STRIP_TAC THEN
   FIRST_ASSUM(fun mr ->
     MP_TAC(MATCH_MP memory_rel_RefPtr_IMP_lemma mr)) THEN
   STRIP_TAC THEN CASES_ON_NAME "res" THEN
   ALL_INST3 memory_rel_ValueArray_IMP THEN
   ALL_INST3 memory_rel_ByteArray_IMP THEN
   ALL_INST3 memory_rel_Thunk_IMP THEN
   ALL_INST2 memory_rel_MutBlock_IMP_F THEN
   RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
   TRY(FIRST_X_ASSUM CONTR_TAC) THEN
   ASM_MESON_TAC[]);;

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
         (
          // (word_bit 4 x ⇒ word_bit 2 x) ∧
          word_bit 3 x <=> ~(word_bit 2 x)) /\
         get_real_addr c st w = SOME a /\
         get_real_simple_addr c st w = SOME a /\
         m a = wordLang_Word (x:'a word) /\ a IN dm)`)
  (* the pointer has a value in the refs, which is a ValueArray or
     a ByteArray because the hypotheses exclude the other two *)
  (STRIP_TAC THEN
   FIRST_ASSUM(fun mr ->
     MP_TAC(MATCH_MP memory_rel_RefPtr_IMP_lemma mr)) THEN
   STRIP_TAC THEN CASES_ON_NAME "res" THEN
   TRY(FIRST_X_ASSUM(fun th -> FIRST_ASSUM(fun a ->
     CONTR_TAC(MP (NOT_ELIM(SPEC_ALL th)) a)))) THEN
   ALL_INST3 memory_rel_ValueArray_IMP THEN
   ALL_INST3 memory_rel_ByteArray_IMP THEN
   ASM_MESON_TAC[]);;

let memory_rel_RefPtr_gen_IMP = cake_theorem "memory_rel_RefPtr_gen_IMP"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((RefPtr bl p,v) :: vars) /\
     good_dimindex (:'a) ==>
     (?r. lookup p refs = SOME r /\
     (match r with Thunk Evaluated x ->
       (!w. v = wordLang_Word w /\ FAPPLY w 0 ==>
          (?a x. get_real_addr c st w = SOME a /\
                m a = wordLang_Word x /\ a IN dm /\ ~((x && (n2w
                  0b111100)) = n2w ((0 + 6) * 4)))) |
       // a MutBlock carries a BlockTag header, for which the bit pattern below
       // does not hold; this theorem has no users, so the case is left trivial
       bvlSem_MutBlock _48 _49 _50 _51 _52 -> T | _53 ->
       (?w a x.
         v = wordLang_Word w /\ FAPPLY w 0 /\
         (
          // (word_bit 4 x ⇒ word_bit 2 x) ∧
          word_bit 3 x <=> ~(word_bit 2 x)) /\
         get_real_addr c st w = SOME a /\
         get_real_simple_addr c st w = SOME a /\
         m a = wordLang_Word (x:'a word) /\ a IN dm)))`)
  CHEAT_TAC;;

let smallnum_bits = cake_theorem "Smallnum_bits"
  (fun () ->
    `((n2w 1) && Smallnum i) = (n2w 0) /\ ((n2w 2) && Smallnum i) =
  (n2w 0)`)
  (* Smallnum is four times the integer, up to the sign, so
     its two lowest bits are clear *)
  (let bw2 = prove
    (`!i. bit i (word 2:(N)word) <=> i = 1 /\ 1 < dimindex(:N)`,
     GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
       [ARITH_RULE `2 = 2 EXP 1`] THEN
     REWRITE_TAC[BIT_WORD_POW2]) in
   let shl4 = prove
    (`!(v:(N)word). word 4 * v = word_shl v 2`,
     REWRITE_TAC[word_shl; GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD] THEN
     CONV_TAC MOD_DOWN_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[MULT_AC]) in
   let bits01 = prove
    (`!(v:(N)word). (word 1 && word_shl v 2 = word 0) /\
                    (word 2 && word_shl v 2 = word 0)`,
     GEN_TAC THEN
     REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0;
                 BIT_WORD_1; bw2; BIT_WORD_SHL] THEN
     CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THEN ARITH_TAC) in
   let nmul = prove
    (`!(i:int). &0 <= i
        ==> n2w (num_of_int (&4 * i)) =
            (n2w 4 * n2w (num_of_int i):(N)word)`,
     REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `num_of_int (&4 * (i:int)) = 4 * num_of_int i`
       SUBST1_TAC THENL
      [FIRST_ASSUM(fun th ->
         GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
           [GSYM(MATCH_MP INT_OF_NUM_OF_INT th)]) THEN
       REWRITE_TAC[INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM];
       REWRITE_TAC[WORD_MUL]]) in
   REWRITE_TAC[cake_def "Smallnum"] THEN COND_CASES_TAC THENL
    [SUBGOAL_THEN `&0 <= ((&0) - (i:int))` ASSUME_TAC THENL
      [ASM_INT_ARITH_TAC; ALL_TAC] THEN
     FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP nmul th]) THEN
     REWRITE_TAC[WORD_SUB_LZERO; shl4] THEN
     GEN_REWRITE_TAC (ONCE_DEPTH_CONV)
       [WORD_RULE `word_neg (word_shl v 2) = word_shl (word_neg v) 2`]
     THEN REWRITE_TAC[bits01];
     SUBGOAL_THEN `&0 <= (i:int)` ASSUME_TAC THENL
      [ASM_INT_ARITH_TAC; ALL_TAC] THEN
     FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP nmul th]) THEN
     REWRITE_TAC[shl4; bits01]]);;

let memory_rel_any_Number_IMP = cake_theorem "memory_rel_any_Number_IMP"
  (fun () ->
    `good_dimindex (:'a) /\
      memory_rel c be ts refs sp st m dm ((Number i,(v:'a
        word_loc)) :: vars) ==>
      (?w. v = wordLang_Word w /\ (FAPPLY w 0 <=> ~(small_int
        (:'a) i)))`)
  (* the root of a Number is the Data of its Smallnum, whose lowest
     bit the and with the complement of one clears, or a Pointer,
     whose address has that bit set (get_addr_0) *)
  (MEMORY_REL_TAC THEN V_INV_TAC THEN
    FIRST_ASSUM(fun e ->
      let c = concl e in
      if is_eq c && is_var (rand c) then SUBST1_TAC (SYM e)
      else fail()) THEN
    REWRITE_TAC[injectivity "word_loc"] THEN
    CONV_TAC(REDEPTH_CONV UNWIND_CONV) THEN
    REWRITE_TAC[word_index; cake_thm "get_addr_0"; BIT_WORD_AND;
                BIT_WORD_NOT; BIT_WORD_1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `0 < d <=> 1 <= d`; DIMINDEX_GE_1]);;

let memory_rel_Number_IMP = cake_theorem "memory_rel_Number_IMP"
  (fun () ->
    `good_dimindex (:'a) /\ small_int (:'a) i /\
      memory_rel c be ts refs sp st m dm ((Number i,(v:'a
        word_loc)) :: vars) ==>
      v = wordLang_Word (Smallnum i)`)
  (* the root of a small Number is the Data of its Smallnum,
     whose word_addr takes the tag bit off -- and Smallnum is
     four times the integer, which has that bit clear *)
  (let nmul = prove
    (`!(i:int). &0 <= i
        ==> n2w (num_of_int (&4 * i)) =
            (n2w 4 * n2w (num_of_int i):(N)word)`,
     REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `num_of_int (&4 * (i:int)) = 4 * num_of_int i`
       SUBST1_TAC THENL
      [FIRST_ASSUM(fun th ->
         GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
           [GSYM(MATCH_MP INT_OF_NUM_OF_INT th)]) THEN
       REWRITE_TAC[INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM];
       REWRITE_TAC[WORD_MUL]]) in
   let neg2 = prove
    (`word_not (word 1):(N)word = word_neg (word 2)`,
     CONV_TAC WORD_RULE) in
   let sm_and = prove
    (`good_dimindex (:'a) ==>
        ((Smallnum i && word_not (n2w 1)) = (Smallnum i:'a word))`,
     DISCH_TAC THEN REWRITE_TAC[cake_def "Smallnum"] THEN
     REWRITE_TAC[neg2] THEN ONCE_REWRITE_TAC[WORD_AND_SYM] THEN
     COND_CASES_TAC THENL
      [SUBGOAL_THEN `&0 <= ((&0) - (i:int))` ASSUME_TAC THENL
        [ASM_INT_ARITH_TAC; ALL_TAC] THEN
       FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP nmul th]) THEN
       REWRITE_TAC[WORD_SUB_LZERO] THEN
       SUBGOAL_THEN
         `word_neg (n2w 4 * n2w (num_of_int ((&0) - (i:int)))) =
          word_neg (n2w 4) * (n2w (num_of_int ((&0) - i)):'a word)`
         SUBST1_TAC THENL
        [CONV_TAC WORD_RULE; ALL_TAC] THEN
       MATCH_MP_TAC word_ml_inv_neg_num_lemma THEN
       FIRST_ASSUM ACCEPT_TAC;
       SUBGOAL_THEN `&0 <= (i:int)` ASSUME_TAC THENL
        [ASM_INT_ARITH_TAC; ALL_TAC] THEN
       FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP nmul th]) THEN
       MATCH_MP_TAC word_ml_inv_num_lemma THEN
       FIRST_ASSUM ACCEPT_TAC]) in
   MEMORY_REL_TAC THEN V_INV_TAC THEN
   TRY CONTRA_TAC THEN
   FIRST_ASSUM(fun gd ->
     RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP sm_and gd])) THEN
   ASM_MESON_TAC[]);;

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
  (let hd_is n t =
     (try fst(dest_const(fst(strip_comb t))) = n
      with Failure _ -> false) in
   let sep_cond_front =
     W(fun (asl,w) ->
       let star t = hd_is "STAR" t in
       let rec facs t =
         if star t then
           let args = snd(strip_comb t) in
           facs (el 0 args) @ facs (el 1 args)
         else [t] in
       let pred = rator (lhand w) in
       let fs = facs pred in
       let isone t = hd_is "set_sep_one" t in
       let iscond t = hd_is "cond" t in
       let one = find isone fs and cnd = find iscond fs in
       let rest = filter (fun t -> not (isone t) && not (iscond t))
                    fs in
       let st = fst(strip_comb pred) in
       let mk a b = mk_comb(mk_comb(st,a),b) in
       let target = mk cnd (mk one (end_itlist mk rest)) in
       SUBGOAL_THEN (mk_eq(pred,target)) SUBST1_TAC THENL
        [REWRITE_TAC[STAR_AC]; ALL_TAC]) in
   MEMORY_REL_TAC THEN
   FIRST_ASSUM(fun vi ->
     if hd_is "v_inv" (concl vi)
     then MP_TAC(REWRITE_RULE[cake_thm "v_inv_def"] vi)
     else fail()) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `ptr:num` STRIP_ASSUME_TAC) THEN
   VAR_EQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE(word_addr_clauses ())) THEN
   FIRST_ASSUM(fun hm ->
     if hd_is "heap_in_memory_store" (concl hm)
     then MP_TAC(REWRITE_RULE[cake_def "heap_in_memory_store"] hm)
     else fail()) THEN
   STRIP_TAC THEN
   REPEAT(FIRST_X_ASSUM(fun th ->
     if is_exists (concl th) then
       (X_CHOOSE_THEN `curr:'a word`
         (X_CHOOSE_THEN `other:'a word` STRIP_ASSUME_TAC)) th
     else fail())) THEN
   REWRITE_TAC(word_addr_clauses ()) THEN
   EXISTS_TAC `get_addr c ptr (wordLang_Word ((n2w 0):'a word))` THEN
   EXISTS_TAC `curr + n2w ptr * bytes_in_word:'a word` THEN
   REWRITE_TAC[] THEN CONJ_TAC THENL
    [FIRST_ASSUM(fun hl ->
       if hd_is "=" (concl hl) && hd_is "heap_lookup" (lhs(concl hl))
       then FIRST_ASSUM(fun hlen ->
         FIRST_ASSUM(fun cu ->
           FIRST_ASSUM(fun gd ->
             MP_TAC(SPEC `wordLang_Word ((n2w 0):'a word)`
               (GEN `w:('a)word_loc`
                 (MATCH_MP (cake_thm "get_real_addr_get_addr")
                   (CONJ hlen (CONJ hl (CONJ cu gd)))))))))
       else fail()) THEN
     DISCH_THEN(ACCEPT_TAC o CONJUNCT2);
     ALL_TAC] THEN
   FIRST_ASSUM(fun hl ->
     if hd_is "=" (concl hl) && hd_is "heap_lookup" (lhs(concl hl))
     then MP_TAC(MATCH_MP (cake_thm "heap_lookup_SPLIT") hl)
     else fail()) THEN
   DISCH_THEN(X_CHOOSE_THEN
     `ha:(('a word_loc,data_to_word_memoryProof_tag#('a word_loc)
           list)heap_element) list`
     (X_CHOOSE_THEN
       `hb:(('a word_loc,data_to_word_memoryProof_tag#('a word_loc)
             list)heap_element) list` STRIP_ASSUME_TAC)) THEN
   VAR_EQ_TAC THEN
   FIRST_X_ASSUM(fun hs ->
     if (try hd_is "STAR" (rator(concl hs)) with Failure _ -> false)
     then MP_TAC hs else fail()) THEN
   REWRITE_TAC[cake_thm "word_heap_APPEND"; cake_def "word_heap";
               cake_def "Bignum"; cake_def "i2mw"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[cake_def "word_el"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[cake_def "word_payload"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[cake_def "misc_word_list"; LENGTH_MAP] THEN
   sep_cond_front THEN
   REWRITE_TAC[cond_STAR] THEN
   DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
     (fun st -> MP_TAC(MATCH_MP read_fun2set st))) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN
   AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

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
  (* the ALT of it says more; this is what the source keeps *)
  (STRIP_TAC THEN
   FIRST_ASSUM(fun t1 -> FIRST_ASSUM(fun t2 -> FIRST_ASSUM(fun t3 ->
     MP_TAC(MATCH_MP memory_rel_Number_bignum_IMP_ALT
       (CONJ t1 (CONJ t2 t3)))))) THEN
   STRIP_TAC THEN
   REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
   REPEAT(FIRST_X_ASSUM(fun th ->
     if is_exists(concl th) then CHOOSE_TAC th else fail())) THEN
   ASM_MESON_TAC[]);;

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
  (* the Smallnum of a natural number is it shifted up by two, and
     a number below two to the dimindex less three is small *)
  (let shl2 = prove
    (`!(v:(N)word). word_shl v 2 = word 4 * v`,
     REWRITE_TAC[word_shl; GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD] THEN
     CONV_TAC MOD_DOWN_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[MULT_AC]) in
   let smallnum_shl = prove
    (`Smallnum (&n) = ((n2w n << 2):'a word)`,
     REWRITE_TAC[cake_def "Smallnum"; INT_OF_NUM_LT;
                 ARITH_RULE `~(n < 0)`; INT_OF_NUM_MUL;
                 NUM_OF_INT_OF_NUM; shl2; WORD_MUL]) in
   STRIP_TAC THEN
   MP_TAC(INST [`&n:int`,`i:int`]
     (cake_thm "IMP_memory_rel_Number")) THEN
   REWRITE_TAC[smallnum_shl] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[cake_def "small_int"; INT_OF_NUM_LT; dimword] THEN
   CONJ_TAC THENL
    [INT_ARITH_TAC;
     UNDISCH_TAC `good_dimindex (:'a)` THEN
     REWRITE_TAC[cake_def "good_dimindex"] THEN
     DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
     RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
     CONV_TAC NUM_REDUCE_CONV THEN ARITH_ASM_TAC]);;

let IMP_memory_rel_Number_num = cake_theorem "IMP_memory_rel_Number_num"
  (fun () ->
    `good_dimindex (:'a) /\ n < 2 EXP (dimindex (:'a) - 4) /\
      memory_rel c be ts refs sp st m dm vars ==>
      memory_rel c be ts refs sp st m dm
       ((Number (&n),wordLang_Word ((n2w n << 2):'a word)) ::
         vars)`)
  (* and so is one below two to the dimindex less four *)
  (let shl2 = prove
    (`!(v:(N)word). word_shl v 2 = word 4 * v`,
     REWRITE_TAC[word_shl; GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD] THEN
     CONV_TAC MOD_DOWN_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[MULT_AC]) in
   let smallnum_shl = prove
    (`Smallnum (&n) = ((n2w n << 2):'a word)`,
     REWRITE_TAC[cake_def "Smallnum"; INT_OF_NUM_LT;
                 ARITH_RULE `~(n < 0)`; INT_OF_NUM_MUL;
                 NUM_OF_INT_OF_NUM; shl2; WORD_MUL]) in
   STRIP_TAC THEN
   MP_TAC(INST [`&n:int`,`i:int`]
     (cake_thm "IMP_memory_rel_Number")) THEN
   REWRITE_TAC[smallnum_shl] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[cake_def "small_int"; INT_OF_NUM_LT; dimword] THEN
   CONJ_TAC THENL
    [INT_ARITH_TAC;
     UNDISCH_TAC `good_dimindex (:'a)` THEN
     REWRITE_TAC[cake_def "good_dimindex"] THEN
     DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
     RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
     CONV_TAC NUM_REDUCE_CONV THEN ARITH_ASM_TAC]);;

let memory_rel_Number_EQ = cake_theorem "memory_rel_Number_EQ"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
        ((Number i1,w1) :: (Number i2,w2) :: vars) /\
      (small_int (:'a) i1 \/ small_int (:'a) i2) /\
      good_dimindex (:'a) ==>
        (?v1 v2. w1 = wordLang_Word v1 /\ w2 = wordLang_Word
          (v2:'a word) /\ (v1 = v2 <=> i1 = i2))`)
  (* two Numbers of which at least one is small: if both are, both
     roots are Smallnums and num_eq_thm says that two Smallnums are
     equal only for equal integers; if one is not, the lowest bits
     of the two roots differ (that bit says whether the Number is
     small), so the words differ, and so do the integers *)
  (let hd_is n t =
   (try fst(dest_const(fst(strip_comb t))) = n
    with Failure _ -> false) in
   let clash =
     FIRST_ASSUM(fun n ->
       if is_neg (concl n) then
         FIRST_ASSUM(fun p ->
           if concl p = rand (concl n)
           then CONTR_TAC(EQ_MP (EQF_INTRO n) p) else fail())
       else fail()) in
   let all2cons = prove
    (`!P h t (l:(A)list).
        ALL2 P l (CONS (h:B) t) <=>
        ?a b. l = CONS a b /\ P a h /\ ALL2 P b t`,
     REPEAT GEN_TAC THEN
     STRUCT_CASES_TAC(ISPEC `l:(A)list` list_CASES) THEN
     REWRITE_TAC[ALL2; NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]) in
   (* one of the two is small and the other is not: their lowest
      bits differ, so the words differ, and the integers differ
      because small_int holds of one and not of the other *)
   let bits =
     MATCH_MP_TAC(TAUT `~p /\ ~q ==> (p <=> q)`) THEN CONJ_TAC THENL
      [DISCH_THEN SUBST_ALL_TAC THEN
       W(fun (asl,w) ->
         MP_TAC(end_itlist CONJ
           (map snd (filter (fun (_,th) ->
              let c = concl th in
              is_eq c && type_of (lhs c) = bool_ty) asl)))) THEN
       ASM_REWRITE_TAC[];
       DISCH_THEN SUBST_ALL_TAC THEN clash] in
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
   FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun gd ->
     MP_TAC(MATCH_MP (cake_thm "memory_rel_any_Number_IMP")
              (CONJ gd mr)))) THEN
   DISCH_THEN(X_CHOOSE_THEN `v1:'a word` STRIP_ASSUME_TAC) THEN
   FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun gd ->
     let tl = MATCH_MP (cake_thm "memory_rel_tail") mr in
     MP_TAC(MATCH_MP (cake_thm "memory_rel_any_Number_IMP")
              (CONJ gd tl)))) THEN
   DISCH_THEN(X_CHOOSE_THEN `v2:'a word` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `v1:'a word` THEN EXISTS_TAC `v2:'a word` THEN
   ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `small_int (:'a) i1` THEN
   ASM_CASES_TAC `small_int (:'a) i2` THENL
    [(* both are small, so both roots are Smallnums, and num_eq_thm
        says that two Smallnums are equal only for equal integers *)
     FIRST_ASSUM(fun e1 ->
       FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun gd ->
         FIRST_ASSUM(fun si ->
           let ni = MATCH_MP (cake_thm "memory_rel_Number_IMP")
                      (CONJ gd (CONJ si mr)) in
           SUBST_ALL_TAC(REWRITE_RULE[injectivity "word_loc"]
                           (TRANS (SYM e1) ni)))))) THEN
     FIRST_ASSUM(fun e2 ->
       FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun gd ->
         FIRST_ASSUM(fun si ->
           let tl = MATCH_MP (cake_thm "memory_rel_tail") mr in
           let ni = MATCH_MP (cake_thm "memory_rel_Number_IMP")
                      (CONJ gd (CONJ si tl)) in
           SUBST_ALL_TAC(REWRITE_RULE[injectivity "word_loc"]
                           (TRANS (SYM e2) ni)))))) THEN
     FIRST_ASSUM(fun mr ->
       if hd_is "memory_rel" (concl mr)
       then MP_TAC(REWRITE_RULE[cake_def "memory_rel";
                                cake_def "word_ml_inv"; MAP; FST] mr)
       else fail()) THEN
     DISCH_THEN STRIP_ASSUME_TAC THEN
     FIRST_X_ASSUM(fun a2 ->
       if hd_is "ALL2" (concl a2)
       then MP_TAC(REWRITE_RULE[MAP; all2cons] a2) else fail()) THEN
     DISCH_THEN STRIP_ASSUME_TAC THEN
     VAR_EQ_TAC THEN
     FIRST_ASSUM(fun am -> FIRST_ASSUM(fun s1 -> FIRST_ASSUM(fun s2 ->
       MP_TAC(MATCH_MP (cake_thm "num_eq_thm")
                (CONJ am (CONJ s1 s2)))))) THEN
     DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
       (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
     REWRITE_TAC[injectivity "word_loc";
                 injectivity "heap_address"] THEN
     DISCH_THEN(ACCEPT_TAC o GSYM);
     bits;
     bits;
     (* neither is small, which the statement's disjunction denies *)
     FIRST_ASSUM(fun d ->
       if is_disj (concl d) then DISJ_CASES_TAC d else fail()) THEN
     clash]);;

let memory_rel_Number_LESS = cake_theorem "memory_rel_Number_LESS"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
        ((Number i1,w1) :: (Number i2,w2) :: vars) /\
      small_int (:'a) i1 /\
      small_int (:'a) i2 /\
      good_dimindex (:'a) ==>
        (?v1 v2. w1 = wordLang_Word v1 /\ w2 = wordLang_Word v2
          /\ (v1 < (v2:'a word) <=> i1 < i2))`)
  (* both words are the Smallnum of their integer, and num_less_thm
     says that the order of the two is the order of the integers *)
  (STRIP_TAC THEN
   FIRST_ASSUM(fun mr -> ASSUME_TAC(MATCH_MP memory_rel_swap mr)) THEN
   ALL_INST3 memory_rel_Number_IMP THEN
   ASM_MESON_TAC[num_less_thm]);;

let memory_rel_Number_LESS_EQ = cake_theorem "memory_rel_Number_LESS_EQ"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
        ((Number i1,w1) :: (Number i2,w2) :: vars) /\
      small_int (:'a) i1 /\
      small_int (:'a) i2 /\
      good_dimindex (:'a) ==>
        (?v1 v2. w1 = wordLang_Word v1 /\ w2 = wordLang_Word v2
          /\ (v1 <= (v2:'a word) <=> i1 <= i2))`)
  (* the order or the equality, which the two theorems above give *)
  (let wle = prove
    (`!(x:(N)word) y. x <= y <=> x < y \/ x = y`,
     REWRITE_TAC[word_ile; word_ilt; irelational2] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC[GSYM IVAL_EQ] THEN INT_ARITH_TAC) in
   STRIP_TAC THEN
   FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun s1 -> FIRST_ASSUM(fun s2 ->
     FIRST_ASSUM(fun gd ->
       MP_TAC(MATCH_MP memory_rel_Number_EQ
         (CONJ mr (CONJ (DISJ1 s1 (concl s2)) gd))) THEN
       MP_TAC(MATCH_MP memory_rel_Number_LESS
         (CONJ mr (CONJ s1 (CONJ s2 gd)))))))) THEN
   REPEAT STRIP_TAC THEN
   REPEAT(FIRST_X_ASSUM(fun th ->
     if is_eq(concl th) && is_var(lhs(concl th))
     then SUBST_ALL_TAC th else fail())) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[injectivity "word_loc"]) THEN
   ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[wle; INT_LE_LT]);;

let memory_rel_Number_word_msb =
  cake_theorem "memory_rel_Number_word_msb"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Number i1,wordLang_Word (w:'a
  word)) :: vars) /\
      good_dimindex (:'a) /\ small_int (:'a) i1 ==>
      (word_msb w <=> i1 < (&0))`)
  (* zero is a small integer, so the relation holds of it as
     well, and the order of the two Smallnums is the order of
     the integers: the sign bit of the word says which side of
     zero it is on *)
  (let si0 = prove
    (`good_dimindex (:'a) ==> small_int (:'a) (&0)`,
     REWRITE_TAC[cake_def "good_dimindex"; cake_def "small_int";
                 dimword] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC) in
   let sm0 = prove
    (`Smallnum (&0) = (word 0:(N)word)`,
     REWRITE_TAC[cake_def "Smallnum"] THEN
     REWRITE_TAC[INT_ARITH `~((&0:int) < &0)`] THEN
     REWRITE_TAC[INT_ARITH `(&4:int) * &0 = &0`;
                 NUM_OF_INT_OF_NUM]) in
   STRIP_TAC THEN
   FIRST_ASSUM(fun gd -> ASSUME_TAC(MATCH_MP si0 gd)) THEN
   ALL_INST3 IMP_memory_rel_Number THEN
   RULE_ASSUM_TAC(REWRITE_RULE[sm0]) THEN
   ALL_INST4 memory_rel_Number_LESS_EQ THEN
   RULE_ASSUM_TAC(REWRITE_RULE[injectivity "word_loc"]) THEN
   REWRITE_TAC[word_msb; MSB_IVAL] THEN
   ASM_MESON_TAC[word_ile; irelational2; IVAL_WORD_0;
                 INT_ARITH `(i:int) < &0 <=> ~(&0 <= i)`]);;

let memory_rel_RefPtr_EQ_lemma =
  cake_theorem "memory_rel_RefPtr_EQ_lemma[local]"
  (fun () ->
    `n * 2 EXP k < dimword (:'a) /\ m * 2 EXP k < dimword (:'a) /\ 0 < k
  /\
       (n2w n << k || (n2w 1)) = (n2w m << k || ((n2w 1):'a
         word)) ==> n = m`)
  (* the one in the lowest bit is free of the shifted pointer, so
     the or is a sum, the sum cancels and the shift is a
     multiplication by two to the shift, which cancels as well
     because both products are below the dimword *)
  (
   let shl_n2w = prove
    (`!n k. word_shl (n2w n:(N)word) k = n2w (n * 2 EXP k)`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[word_shl; GSYM VAL_EQ; VAL_WORD] THEN
     CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_AC]) in
   let and1 = prove
    (`!(v:(N)word) k. 0 < k ==> word_shl v k && n2w 1 = n2w 0`,
     REPEAT STRIP_TAC THEN
     REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0;
                 BIT_WORD_SHL; BIT_WORD_1] THEN
     X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     ASM_CASES_TAC `(i:num) = 0` THEN ASM_REWRITE_TAC[] THEN
     ASM_ARITH_TAC) in
   let n2w_11 = prove
    (`!a b. a < dimword (:N) /\ b < dimword (:N)
        ==> ((n2w a:(N)word) = n2w b <=> a = b)`,
     REPEAT STRIP_TAC THEN
     REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; GSYM dimword] THEN
     ASM_SIMP_TAC[MOD_LT]) in
   STRIP_TAC THEN
   FIRST_ASSUM(fun pk ->
     let a1 = MATCH_MP (ISPEC `n2w n:'a word` and1) pk
     and a2 = MATCH_MP (ISPEC `n2w m:'a word` and1) pk in
     RULE_ASSUM_TAC(REWRITE_RULE
       [GSYM (MATCH_MP WORD_ADD_OR a1);
        GSYM (MATCH_MP WORD_ADD_OR a2)])) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[shl_n2w;
     WORD_ARITH `!(x:(N)word) y a. (x + a = y + a) <=> (x = y)`]) THEN
   FIRST_ASSUM(fun eq ->
     FIRST_ASSUM(fun b1 -> FIRST_ASSUM(fun b2 ->
       MP_TAC(EQ_MP (MATCH_MP n2w_11 (CONJ b1 b2)) eq)))) THEN
   SUBGOAL_THEN `~(2 EXP k = 0)` MP_TAC THENL
    [REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
   MESON_TAC[EQ_MULT_RCANCEL]);;

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
  (* the value at the pointer is a ByteArray, so the two RefPtrs
     are no thunks and the rule of v_inv for a plain reference
     gives both of them the same address *)
  (let LOOKUP_SUBST =
     FIRST_ASSUM(fun th ->
       let c = concl th in
       if is_eq c &&
          (try fst(dest_const(fst(strip_comb(lhs c)))) =
               "sptree_lookup"
           with Failure _ -> false)
       then RULE_ASSUM_TRY(REWRITE_RULE[th]) else fail()) in
   MEMORY_REL_TAC THEN V_INV_TAC THEN SPLIT_ROOTS_TAC THEN
   V_INV_TAC THEN
   LOOKUP_SUBST THEN
   RULE_ASSUM_TAC(REWRITE_RULE[injectivity "option";
                              distinctness "bvlSem_ref"]) THEN
   TRY(FIRST_ASSUM CONTR_TAC) THEN
   FIRST_ASSUM(fun t1 -> FIRST_ASSUM(fun t2 ->
     MATCH_ACCEPT_TAC(TRANS (SYM t1) t2))));;

let memory_rel_Boolv_T = cake_theorem "memory_rel_Boolv_T"
  (fun () ->
    `memory_rel c be ts refs sp st m dm vars /\ good_dimindex (:'a)
  ==> memory_rel c be ts refs sp st m dm ((Boolv T,wordLang_Word ((n2w
  18):'a word)) :: vars)`)
  (* the true Boolv is the empty Block of the true tag, which is
     one, so its root is the Data of BlockNil 1, the word eighteen *)
  (let shl16 = prove
    (`word_shl (word 1:(N)word) 4 = word 16`,
     REWRITE_TAC[word_shl; GSYM VAL_EQ; VAL_WORD] THEN
     CONV_TAC MOD_DOWN_CONV THEN CONV_TAC NUM_REDUCE_CONV) in
   let blocknil1 = prove
    (`BlockNil 1 = (n2w 18:'a word)`,
     REWRITE_TAC[cake_def "BlockNil"; shl16] THEN
     CONV_TAC WORD_RULE) in
   let and18 = prove
    (`(n2w 18:(N)word) && word_not (n2w 1) = n2w 18`,
     WORD_NUM_BIT_TAC 5) in
   let dimword16 = prove
    (`good_dimindex (:'a) ==> 1 < dimword (:'a) DIV 16`,
     REWRITE_TAC[cake_def "good_dimindex"; dimword] THEN
     DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
     CONV_TAC NUM_REDUCE_CONV) in
   let waddr = hd (word_addr_clauses ()) in
   let cons1 = REWRITE_RULE[blocknil1]
     (INST [`1`,`tag:num`] (cake_thm "cons_thm_EMPTY")) in
   REWRITE_TAC[cake_def "memory_rel"; cake_def "word_ml_inv"] THEN
   REPEAT STRIP_TAC THEN ASM_EXISTS_TAC THEN
   ASM_REWRITE_TAC[] THEN
   EXISTS_TAC
     `CONS (gc_shared_Data (wordLang_Word (n2w 18:'a word))) hs` THEN
   REWRITE_TAC[MAP; ALL2; waddr; and18] THEN
   ASM_REWRITE_TAC[cake_def "dataSem_Boolv";
                   cake_def "bool_to_tag"; cake_def "true_tag"] THEN
   MATCH_MP_TAC cons1 THEN
   ASM_SIMP_TAC[dimword16]);;

let memory_rel_Boolv_F = cake_theorem "memory_rel_Boolv_F"
  (fun () ->
    `memory_rel c be ts refs sp st m dm vars /\ good_dimindex (:'a)
  ==> memory_rel c be ts refs sp st m dm ((Boolv F,wordLang_Word ((n2w
  2):'a word)) :: vars)`)
  (* the false Boolv is the empty Block of the false tag, which is
     zero, so it is the same root as the one of Unit *)
  (let blocknil0 = prove
    (`BlockNil 0 = (n2w 2:'a word)`,
     REWRITE_TAC[cake_def "BlockNil"] THEN CONV_TAC WORD_RULE) in
   let and2 = prove
    (`(n2w 2:(N)word) && word_not (n2w 1) = n2w 2`,
     WORD_NUM_BIT_TAC 2) in
   let dimword16 = prove
    (`good_dimindex (:'a) ==> 0 < dimword (:'a) DIV 16`,
     REWRITE_TAC[cake_def "good_dimindex"; dimword] THEN
     DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
     CONV_TAC NUM_REDUCE_CONV) in
   let waddr = hd (word_addr_clauses ()) in
   let cons0 = REWRITE_RULE[blocknil0]
     (INST [`0`,`tag:num`] (cake_thm "cons_thm_EMPTY")) in
   REWRITE_TAC[cake_def "memory_rel"; cake_def "word_ml_inv"] THEN
   REPEAT STRIP_TAC THEN ASM_EXISTS_TAC THEN
   ASM_REWRITE_TAC[] THEN
   EXISTS_TAC
     `CONS (gc_shared_Data (wordLang_Word (n2w 2:'a word))) hs` THEN
   REWRITE_TAC[MAP; ALL2; waddr; and2] THEN
   ASM_REWRITE_TAC[cake_def "dataSem_Boolv";
                   cake_def "bool_to_tag"; cake_def "false_tag"] THEN
   MATCH_MP_TAC cons0 THEN
   ASM_SIMP_TAC[dimword16]);;

let memory_rel_Boolv = cake_theorem "memory_rel_Boolv"
  (fun () ->
    `memory_rel c be ts refs sp st m dm vars /\ good_dimindex (:'a) /\
     (b ==> v = wordLang_Word (n2w 18)) /\ (~b ==> v =
       wordLang_Word ((n2w 2):'a word)) ==>
     memory_rel c be ts refs sp st m dm ((Boolv b,v) :: vars)`)
  (STRIP_TAC THEN ASM_CASES_TAC `b:bool` THEN ASM_SIMP_TAC[] THENL
    [MATCH_MP_TAC memory_rel_Boolv_T;
     MATCH_MP_TAC memory_rel_Boolv_F] THEN
   ASM_REWRITE_TAC[]);;

let word_ml_inv_SP_LIMIT = cake_theorem "word_ml_inv_SP_LIMIT"
  (fun () ->
    `word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs stack ==> sp
  <= limit`)
  (* the unused space of the invariant lies inside the heap and the
     heap is of the limit *)
  (REWRITE_TAC[cake_def "word_ml_inv"; cake_def "abs_ml_inv";
               cake_def "unused_space_inv"; cake_def "heap_ok"] THEN
   REPEAT STRIP_TAC THEN ARITH_ASM_TAC);;

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
  (* four times a small integer is between INT_MIN and INT_MAX, so
     the i2w of it has it for its w2i *)
  (let bnds = prove
    (`good_dimindex (:'a) /\ small_int (:'a) i ==>
       --(&2 pow (dimindex (:'a) - 1)) <= (&4) * i /\
       (&4) * i < &2 pow (dimindex (:'a) - 1)`,
     REWRITE_TAC[cake_def "good_dimindex"; cake_def "small_int";
                 dimword] THEN
     STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
     RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     CONV_TAC(ONCE_DEPTH_CONV INT_POW_CONV) THEN
     ASM_INT_ARITH_TAC) in
   STRIP_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
   FIRST_ASSUM(fun t1 -> FIRST_ASSUM(fun t2 ->
     ACCEPT_TAC(MATCH_MP bnds (CONJ t1 t2)))));;

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
    `~(i < (&0:int)) <=> (?n. i = &n)`)
  (* an integer that is not below zero is the injection of a
     number, which is HOL Light's INT_OF_NUM_EXISTS *)
  (REWRITE_TAC[INT_OF_NUM_EXISTS; INT_NOT_LT]);;

let small_int_w2n = cake_theorem "small_int_w2n[simp]"
  (fun () ->
    `good_dimindex (:'a) ==> small_int (:'a) (&(w2n (w:word8)))`)
  (* a byte is below 256 and the bound of a small integer is a
     quarter of the dimword, which good_dimindex makes 2 EXP 29 at
     the least *)
  (REWRITE_TAC[cake_def "good_dimindex"; cake_def "small_int";
               dimword] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(INT_ARITH
     `&0 <= (i:int) /\ i < n ==> --n <= i /\ i < n`) THEN
   REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN
   MP_TAC(ISPEC `w:word8` VAL_BOUND) THEN
   REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
   ARITH_TAC);;

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
  (* a Number stands for a Data of its Smallnum or for a Pointer at
     its Bignum, and the word_addr of either is a Word *)
  (MEMORY_REL_TAC THEN V_INV_TAC THEN ASM_MESON_TAC[]);;

let memory_rel_Number_IMP_Word_2 =
  cake_theorem "memory_rel_Number_IMP_Word_2"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Number i,v) :: (Number j,w) ::
  vars) ==>
      (?w1 w2. v = wordLang_Word w1 /\ w = wordLang_Word w2)`)
  (* the same of the two Numbers at the head of the list *)
  (MEMORY_REL_TAC THEN SPLIT_ROOTS_TAC THEN V_INV_TAC THEN
   ASM_MESON_TAC[]);;

let memory_rel_zero_space = cake_theorem "memory_rel_zero_space"
  (fun () ->
    `memory_rel c be ts refs sp st m dm vars ==>
      memory_rel c be ts refs 0 st m dm vars`)
  (REWRITE_TAC[cake_def "memory_rel"] THEN STRIP_TAC THEN
   ASM_EXISTS_TAC THEN ASM_REWRITE_TAC[LE_0]);;

let memory_rel_less_space = cake_theorem "memory_rel_less_space"
  (fun () ->
    `memory_rel c be ts refs sp st m dm vars /\ sp' <= sp ==>
     memory_rel c be ts refs sp' st m dm vars`)
  (REWRITE_TAC[cake_def "memory_rel"] THEN REPEAT STRIP_TAC THEN
   ASM_EXISTS_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let all_ones_bit = cake_theorem "all_ones_bit"
  (fun () ->
    `i < dimindex (:'a) ==>
     (FAPPLY (all_ones e b:'a word) i <=> b <= i /\ i < e)`)
  (* all_ones is the slice of the word of all ones, so its bit is
     the one of the subword that the slice shifts up *)
  (DISCH_TAC THEN
   REWRITE_TAC[word_index; cake_def "all_ones"] THEN
   COND_CASES_TAC THENL
    [REWRITE_TAC[BIT_WORD_0] THEN
     FIRST_ASSUM(fun th -> MP_TAC th) THEN ARITH_TAC;
     ALL_TAC] THEN
   ASM_SIMP_TAC[word_slice; word_bits; BIT_WORD_SHL;
                BIT_WORD_SUBWORD; BIT_WORD_NOT; BIT_WORD_0] THEN
   REWRITE_TAC[ARITH_RULE `MIN a b = if a <= b then a else b`] THEN
   REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   POP_ASSUM_LIST(fun ths -> MAP_EVERY MP_TAC ths) THEN ARITH_TAC);;

let maxout_bits_bit = cake_theorem "maxout_bits_bit"
  (fun () ->
    `FAPPLY
       (maxout_bits n l b:'a word) i /\ i < dimindex (:'a) ==>
       b <= i /\ i < b + l`)
  (* maxout_bits is the number shifted up by the base, and a number
     below two to the width of the field has no bit at the width or
     above, or it is all the ones of the field *)
  (let odd_div = prove
    (`!k m i. k < 2 EXP m /\ m <= i
              ==> (ODD (k DIV 2 EXP i) <=> F)`,
     REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `k DIV 2 EXP i = 0` SUBST1_TAC THENL
      [MATCH_MP_TAC DIV_LT THEN
       TRANS_TAC LTE_TRANS `2 EXP m` THEN
       ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC;
       REWRITE_TAC[ODD]]) in
   REWRITE_TAC[word_index; cake_def "maxout_bits"] THEN
   COND_CASES_TAC THENL
    [REWRITE_TAC[BIT_WORD_SHL; BIT_WORD] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     MP_TAC(SPECL [`n:num`; `l:num`; `i - b`] odd_div) THEN
     ASM_REWRITE_TAC[] THEN
     ASM_SIMP_TAC[ARITH_RULE `n < m - 1 ==> n < m`] THEN
     ARITH_ASM_TAC;
     STRIP_TAC THEN
     ASM_MESON_TAC[REWRITE_RULE[word_index] all_ones_bit]]);;

let maxout_bits_IMP = cake_theorem "maxout_bits_IMP"
  (fun () ->
    `i < dimindex (:'a) /\ FAPPLY (maxout_bits tag k n:'a word) i ==>
  i < n + k`)
  (REPEAT STRIP_TAC THEN
   FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
     MP_TAC(MATCH_MP maxout_bits_bit (CONJ th1 th2)))) THEN
   ARITH_TAC);;

let make_cons_ptr_thm = cake_theorem "make_cons_ptr_thm"
  (fun () ->
    `make_cons_ptr conf (f:'a word) tag len =
       wordLang_Word ((f << (shift_length conf -
         backend_common_word_shift (:'a)) || (n2w 1) ||
              ptr_bits conf tag len))`)
  (* the lower bits of ptr_bits are ptr_bits itself, which the
     source proves here as well (the theorem that states it on its
     own stands further down the file) *)
  (let mb = REWRITE_RULE[word_index] maxout_bits_IMP in
   let bits_lt = prove
    (`!i. i < dimindex (:'a) /\ bit i (ptr_bits c x y:'a word)
          ==> i < small_shift_length c`,
     REWRITE_TAC[cake_def "ptr_bits"; cake_def "small_shift_length";
                 BIT_WORD_OR] THEN
     REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(fun th ->
       MP_TAC(MATCH_MP mb
         (CONJ (ASSUME `i < dimindex (:'a)`) th))) THEN
     ARITH_TAC) in
   let glp = prove
    (`get_lowerbits c (wordLang_Word (ptr_bits c x y)) =
      (ptr_bits c x y || (n2w 1))`,
     REWRITE_TAC[cake_def "get_lowerbits"] THEN MATCH_REDUCE_TAC THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN
     REWRITE_TAC[WORD_EQ_BITS_ALT; word_bits; BIT_WORD_SUBWORD;
                 ADD_CLAUSES] THEN
     GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
      [SIMP_TAC[];
       DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
       FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
         MP_TAC(MATCH_MP bits_lt (CONJ th2 th1)))) THEN
       ASM_ARITH_TAC]) in
   REWRITE_TAC[cake_def "make_cons_ptr"; glp] THEN
   AP_TERM_TAC THEN WORD_BITWISE_TAC);;

let Num_ABS_lemmas = cake_theorem "Num_ABS_lemmas[local]"
  (fun () ->
    `num_of_int (abs (&n)) = n /\ num_of_int (abs (--(&n))) = n`)
  (REWRITE_TAC[INT_ABS_NUM; INT_ABS_NEG; NUM_OF_INT_OF_NUM]);;

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
                // 0 <= i1
                if (x2 && (n2w 16)) = (n2w 0) then
                  // 0 <= i2
                  if decode_length c x1 <+ decode_length c x2 then
                    (n2w 0) else (n2w 2):'a word else
                  (n2w 2) else
                if (x2 && (n2w 16)) = (n2w 0) then
                  // 0 <= i2
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
  (* Smallnum_bits says that the one of its two lowest bits is
     clear; a bit is clear exactly when the and with the word of
     that bit is zero *)
  (let bit0_and = prove
    (`!x:(N)word. bit 0 x <=> ~((n2w 1 && x) = n2w 0)`,
     GEN_TAC THEN
     REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0;
                 BIT_WORD_1] THEN
     MESON_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= d ==> 0 < d:num`]) in
   REWRITE_TAC[word_index; bit0_and;
               CONJUNCT1 (cake_thm "Smallnum_bits")]);;

let smallnum_1 = cake_theorem "Smallnum_1"
  (fun () ->
    `good_dimindex (:'a) ==> ~(FAPPLY (Smallnum i:'a word) 1)`)
  (* and the other one, where the word of the bit is two and the
     dimindex has to be above one, which good_dimindex gives *)
  (let bw2 = prove
    (`!i. bit i (n2w 2:(N)word) <=> i = 1 /\ 1 < dimindex(:N)`,
     GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
       [ARITH_RULE `2 = 2 EXP 1`] THEN
     REWRITE_TAC[BIT_WORD_POW2]) in
   let bit1_and = prove
    (`!x:(N)word. 1 < dimindex(:N)
                  ==> (bit 1 x <=> ~((n2w 2 && x) = n2w 0))`,
     GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0;
                 bw2] THEN
     ASM_MESON_TAC[]) in
   DISCH_TAC THEN REWRITE_TAC[word_index] THEN
   FIRST_ASSUM(fun gd ->
     MP_TAC(REWRITE_RULE[cake_def "good_dimindex"] gd)) THEN
   STRIP_TAC THEN
   ASM_SIMP_TAC[bit1_and; CONJUNCT2 (cake_thm "Smallnum_bits");
                ARITH_RULE `d = 32 ==> 1 < d:num`;
                ARITH_RULE `d = 64 ==> 1 < d:num`]);;

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
  (MATCH_MP_TAC memory_rel_rearrange THEN
   GEN_TAC THEN REWRITE_TAC[MEM] THEN CONV_TAC TAUT);;

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
  (* the header of the BlockRep that the Block points at is an
     encode_header of four times the tag, and encode_header is only
     a SOME when that is below a sixteenth of the word size *)
  (let hd_is n t =
     (try fst(dest_const(fst(strip_comb t))) = n
      with Failure _ -> false) in
   let rec facs t =
     if hd_is "STAR" t then
       let args = snd(strip_comb t) in
       facs (el 0 args) @ facs (el 1 args)
     else [t] in
   let sepfront names =
     W(fun (asl,w) ->
       let pred = rator (lhand w) in
       let fs = facs pred in
       let picked = map (fun n -> find (hd_is n) fs) names in
       let rest = filter (fun t -> not (mem t picked)) fs in
       let st = fst(strip_comb pred) in
       let mk a b = mk_comb(mk_comb(st,a),b) in
       let target = itlist mk picked (end_itlist mk rest) in
       SUBGOAL_THEN (mk_eq(pred,target)) SUBST1_TAC THENL
        [REWRITE_TAC[STAR_AC]; ALL_TAC]) in
   DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
   REWRITE_TAC[cake_thm "v_inv_def"] THEN
   COND_CASES_TAC THENL
    [STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   FIRST_X_ASSUM(fun th ->
     if hd_is "heap_in_memory_store" (concl th)
     then MP_TAC(REWRITE_RULE[cake_def "heap_in_memory_store"] th)
     else fail()) THEN
   STRIP_TAC THEN
   FIRST_ASSUM(fun th ->
     if hd_is "heap_lookup" (lhs (concl th))
     then MP_TAC(MATCH_MP (cake_thm "heap_lookup_SPLIT") th)
     else fail()) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   VAR_EQ_TAC THEN
   FIRST_X_ASSUM(fun th ->
     if (try hd_is "STAR" (rator (concl th)) with Failure _ -> false)
     then MP_TAC th else fail()) THEN
   REWRITE_TAC[cake_thm "word_heap_APPEND"; cake_def "word_heap";
               cake_def "word_el"; cake_def "BlockRep"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[cake_def "word_payload"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   sepfront ["cond"] THEN
   REWRITE_TAC[cond_STAR] THEN
   DISCH_THEN(MP_TAC o CONJUNCT1) THEN
   REWRITE_TAC[cake_def "encode_header"] THEN
   COND_CASES_TAC THEN
   REWRITE_TAC[distinctness "option"] THEN
   POP_ASSUM MP_TAC THEN ARITH_TAC);;

let elements_list_def = cake_define_list
  [`elements_list [] = T`;
   `elements_list [v] = T`;
   `elements_list (v :: w :: vs) =
       (?ts t ls1 ls2.
         w = Block ts t (ls1 ++ [v] ++ ls2) /\
         // EVERY (λe. ∀p. e ≠ RefPtr F p) ls1 ∧
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
  (* a list whose seconds repeat: the induction finds the first
     repetition, either the head's second in the tail -- and then
     the head is the first of the two -- or inside the tail, which
     the hypothesis splits.  The lemma states the split with the
     types of the pairs named, so the two pairs can be taken apart
     and the witnesses written down *)
  (let lem = prove
    (`!l:(A#B)list. ~(ALL_DISTINCT (MAP SND l))
        ==> ?l1 l2 l3 x y1 y2.
              l = l1 ++ [(y1,x)] ++ l2 ++ [(y2,x)] ++ l3`,
     LIST_INDUCT_TAC THEN
     REWRITE_TAC[MAP; ALL_DISTINCT_CLAUSES; DE_MORGAN_THM] THEN
     MP_TAC(ISPEC `h:A#B` PAIR_SURJECTIVE) THEN
     DISCH_THEN(X_CHOOSE_THEN `a:A`
       (X_CHOOSE_THEN `b:B` SUBST_ALL_TAC)) THEN
     REWRITE_TAC[SND; MEM_MAP; MEM_APPEND_DECOMPOSE] THEN
     DISCH_THEN(DISJ_CASES_THEN2
       (X_CHOOSE_THEN `p:A#B` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `m1:(A#B)list`
            (X_CHOOSE_THEN `m2:(A#B)list` SUBST_ALL_TAC))
          ASSUME_TAC))
       ASSUME_TAC) THENL
      [MP_TAC(ISPEC `p:A#B` PAIR_SURJECTIVE) THEN
       DISCH_THEN(X_CHOOSE_THEN `c:A`
         (X_CHOOSE_THEN `d:B` SUBST_ALL_TAC)) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[SND]) THEN
       FIRST_X_ASSUM SUBST_ALL_TAC THEN
       MAP_EVERY EXISTS_TAC
         [`[]:(A#B)list`; `m1:(A#B)list`; `m2:(A#B)list`;
          `d:B`; `a:A`; `c:A`] THEN
       REWRITE_TAC[APPEND];
       FIRST_X_ASSUM(fun ih -> FIRST_X_ASSUM(fun nd ->
         MP_TAC(MATCH_MP ih nd))) THEN
       DISCH_THEN(REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
       MAP_EVERY EXISTS_TAC
         [`CONS (a:A,b:B) (l1:(A#B)list)`; `l2:(A#B)list`;
          `l3:(A#B)list`; `x:B`; `y1:A`; `y2:A`] THEN
       REWRITE_TAC[APPEND]]) in
   MATCH_ACCEPT_TAC lem);;

let IN_all_vs_HD = cake_theorem "IN_all_vs_HD"
  (fun () ->
    `x IN all_vs refs (x :: xs)`)
  (REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM] THEN
   REPEAT DISJ2_TAC THEN MATCH_MP_TAC MEM_v_all_vs THEN
   REWRITE_TAC[MEM]);;

let IN_all_vs_TL = cake_theorem "IN_all_vs_TL"
  (fun () ->
    `x IN all_vs refs xs ==>
     x IN all_vs refs (y :: xs)`)
  (* the three parts of all_vs that read the refs are the same, and
     what the stack reaches is still reached when a value is put in
     front of it: the values of that one come first, whatever it is *)
  (let tl_mem = prove
    (`!y xs x. MEM x (v_all_vs xs) ==> MEM x (v_all_vs (CONS y xs))`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     STRUCT_CASES_TAC(ISPEC `y:dataSem_v` (cases_of `:dataSem_v`)) THEN
     GEN_REWRITE_TAC ONCE_DEPTH_CONV [cake_def "v_all_vs"] THEN
     MATCH_REDUCE_TAC THEN
     ASM_REWRITE_TAC[MEM; MEM_APPEND]) in
   REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM] THEN
   STRIP_TAC THEN ASM_MESON_TAC[tl_mem]);;

let get_lowerbits_shift_length =
  cake_theorem "get_lowerbits_shift_length[local]"
  (fun () ->
    `(w2 >>> n) = (n2w 0) ==>
       ((w1 || w2) >>> n) = (w1 >>> n)`)
  (* the bits of the shifted or are the shifted bits of each, and
     the second word has none left; BIT_GUARD is what says that a
     bit that is set is one of the word's own *)
  (DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o
     REWRITE_RULE[WORD_EQ_BITS_ALT; BIT_WORD_0;
                  BIT_WORD_USHR]) THEN
   DISCH_TAC THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR; BIT_WORD_USHR] THEN
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
   GEN_REWRITE_TAC RAND_CONV [BIT_GUARD] THEN REWRITE_TAC[]);;

let shift_shift = cake_theorem "shift_shift[local]"
  (fun () ->
    `n1 * (2 EXP l) < dimword (:'a) ==>
       n2w n1 << l >>> l = (n2w n1:'a word)`)
  (* the shift up multiplies by two to the shift, which stays below
     the dimword, so the shift down divides it out again *)
  (let e2 = prove
    (`!l. 1 <= 2 EXP l`,
     REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0;
                 ARITH_EQ]) in
   DISCH_TAC THEN
   SUBGOAL_THEN `n1 < dimword (:'a) /\ 2 EXP l * n1 < dimword (:'a)`
     STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
      [TRANS_TAC LET_TRANS `n1 * 2 EXP l` THEN ASM_REWRITE_TAC[] THEN
       SUBGOAL_THEN `n1 * 1 <= n1 * 2 EXP l` MP_TAC THENL
        [REWRITE_TAC[LE_MULT_LCANCEL] THEN
         DISJ2_TAC THEN MATCH_ACCEPT_TAC e2;
         ARITH_TAC];
       ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD_SHL; VAL_WORD;
               GSYM dimword] THEN
   CONV_TAC MOD_DOWN_CONV THEN
   ASM_SIMP_TAC[MOD_LT; DIV_MULT; EXP_EQ_0; ARITH_EQ]);;

let word_addr_Data_NE_get_addr =
  cake_theorem "word_addr_Data_NE_get_addr[local]"
  (fun () ->
    `good_dimindex (:'a) ==> ~(word_addr c (gc_shared_Data a1) =
  wordLang_Word (get_addr c n a2:'a word))`)
  (* the address of a Data of a Loc is a Loc, and the one of a Data
     of a word has its lowest bit taken off, where get_addr_0 says
     that the lowest bit of an address is set *)
  (DISCH_TAC THEN CASES_ON_NAME "a1" THEN
   REWRITE_TAC(word_addr_clauses () @
               [distinctness "word_loc"; injectivity "word_loc"]) THEN
   DISCH_TAC THEN
   FIRST_ASSUM(fun eq ->
     let ga = PART_MATCH (rand o rator)
                (GEN_ALL (cake_thm "get_addr_0")) (rand (concl eq)) in
     CONTR_TAC(REWRITE_RULE[GSYM eq; word_index; BIT_WORD_AND;
                            BIT_WORD_NOT; BIT_WORD_1] ga)));;

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
  (* the elements of an elements_list are the payload of the next
     one, so each of them is a Block when the first is, and each is
     smaller than the next: the size of a Block counts the sizes of
     its payload, and the element is one of that payload *)
  (let sumc = prove
    (`SUM [] = 0 /\ (!h t. SUM (CONS h t) = h + SUM t)`,
     REWRITE_TAC[SUM_DEF; ITLIST]) in
   let sum_append = prove
    (`!l1 l2. SUM (l1 ++ l2) = SUM l1 + SUM l2`,
     LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC[APPEND; sumc; ADD_CLAUSES; ADD_ASSOC]) in
   let vbs = prove
    (`!ts t ls. vb_size (Block ts t ls) =
                1 + t + SUM (MAP vb_size ls) + LENGTH ls`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [cake_def "vb_size"] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   SUBGOAL_THEN
     `!xs. elements_list xs /\ ~(xs = []) /\
           (?t a b. HD xs = Block t a b)
           ==> EVERY (\x. ?t a b. x = Block t a b) xs /\
               SORTED (\x y. vb_size x < vb_size y) xs`
     (fun th -> MATCH_ACCEPT_TAC th) THEN
   LIST_INDUCT_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
   POP_ASSUM MP_TAC THEN
   STRUCT_CASES_TAC(ISPEC `t:(dataSem_v)list` list_CASES_v) THEN
   DISCH_TAC THENL
    [REWRITE_TAC[ALL; SORTED_DEF; HD] THEN MESON_TAC[];
     REWRITE_TAC[cake_def "elements_list"; HD; ALL; SORTED_DEF] THEN
     STRIP_TAC THEN
     SUBGOAL_THEN
       `EVERY (\x. ?t a b. x = Block t a b) (CONS v vs) /\
        SORTED (\x y. vb_size x < vb_size y) (CONS v vs)`
       (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[ALL] th)) THENL
      [FIRST_X_ASSUM MATCH_MP_TAC THEN
       ASM_REWRITE_TAC[NOT_CONS_NIL; HD] THEN ASM_MESON_TAC[];
       ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[vbs; MAP_APPEND; sum_append; LENGTH_APPEND;
                     MAP; LENGTH; sumc] THEN
     REPEAT CONJ_TAC THEN TRY ARITH_TAC THEN MESON_TAC[]]);;

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
  (* the roots of the tail of an elements_list are distinct: the
     tail is what the lemma says it of, whose Block the second
     clause of elements_list names (the head of the list is an
     element of it).  The tail of the empty list is empty, which is
     HOL4's clause for it (ml/lib/hol4.ml) *)
  (let hd_is n t =
   (try fst(dest_const(fst(strip_comb t))) = n
    with Failure _ -> false) in
 let grab asl p =
   tryfind (fun (_,th) ->
     if (try p th with Failure _ -> false) then th else fail())
     asl in
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   VAR_EQ_TAC THEN
   CASES_ON_NAME "vars'" THEN
   REWRITE_TAC[hol4_TL] THEN
   TRY(REWRITE_TAC[MAP; ALL_DISTINCT; PAIRWISE] THEN NO_TAC) THEN
   FIRST_ASSUM(fun mr ->
     if hd_is "memory_rel" (concl mr)
     then ASSUME_TAC(MATCH_MP (cake_thm "memory_rel_tl") mr)
     else fail()) THEN
   CASES_ON_NAME "a1" THEN
   REWRITE_TAC[hol4_TL] THEN
   TRY(REWRITE_TAC[MAP; ALL_DISTINCT; PAIRWISE] THEN NO_TAC) THEN
   FIRST_X_ASSUM(fun el ->
     if hd_is "elements_list" (concl el)
     then MP_TAC(REWRITE_RULE[MAP; cake_def "elements_list"] el)
     else fail()) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   MATCH_MP_TAC
     (cake_thm "memory_rel_elements_list_distinct_lemma") THEN
   W(fun (asl,w) ->
     let be = grab asl (fun th ->
       is_eq (concl th) && hd_is "dataSem_Block" (rhs (concl th))) in
     let args = snd(strip_comb (rhs (concl be))) in
     let cs = conjuncts (snd(strip_exists w)) in
     EXISTS_TAC (rhs (el 2 cs)) THEN
     EXISTS_TAC (el 0 args) THEN EXISTS_TAC (el 1 args) THEN
     EXISTS_TAC (el 2 args)) THEN
   FIRST_ASSUM(fun e ->
     if is_eq (concl e) && hd_is "dataSem_Block" (rhs (concl e))
     then RULE_ASSUM_TAC(REWRITE_RULE[e]) THEN
          ASM_REWRITE_TAC[e; MAP; HD; NOT_CONS_NIL; PAIRWISE;
                          hol4_TL]
     else fail()));;

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
  (* the first Block has its lowest bit clear, so it is the empty
     one, whose word is sixteen times its tag plus two.  If the two
     had the same length and the same tag the second would be the
     empty one of the same tag, whose word is the same word, which
     the assumption says it is not *)
  (let subst_vars =
     REPEAT(FIRST_X_ASSUM(fun th ->
       if is_eq(concl th) && is_var(lhand(concl th))
       then SUBST_ALL_TAC th else fail())) in
   STRIP_TAC THEN
   FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun gd ->
     MP_TAC(MATCH_MP (cake_thm "memory_rel_Block_IMP")
       (CONJ mr gd)))) THEN
   REWRITE_TAC[injectivity "word_loc"; word_index] THEN
   DISCH_THEN(X_CHOOSE_THEN `u:'a word`
     (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   ONCE_REWRITE_TAC[GSYM DE_MORGAN_THM] THEN
   UNDISCH_TAC `(v1:(dataSem_v)list) = []` THEN
   DISCH_THEN SUBST_ALL_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
   SUBGOAL_THEN `(v2:(dataSem_v)list) = []` SUBST_ALL_TAC THENL
    [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun gd ->
     MP_TAC(MATCH_MP (cake_thm "memory_rel_Block_IMP")
       (CONJ (MATCH_MP (cake_thm "memory_rel_tail") mr) gd)))) THEN
   REWRITE_TAC[injectivity "word_loc"; word_index] THEN
   DISCH_THEN(X_CHOOSE_THEN `u2:'a word`
     (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
   REWRITE_TAC[] THEN STRIP_TAC THEN subst_vars THEN
   FIRST_ASSUM(fun th -> CONTR_TAC(REWRITE_RULE[] th)));;

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
  (REPEAT GEN_TAC THEN CASES_ON_NAME "x" THEN
   REWRITE_TAC[cake_def "data_to_word_memoryProof_fix_clock";
               distinctness "option"] THEN
   TRY(CASES_ON_NAME "a" THEN CASES_ON_NAME "y" THEN
       REWRITE_TAC[cake_def
                     "data_to_word_memoryProof_fix_clock"]) THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
   REPEAT COND_CASES_TAC THEN REPEAT STRIP_TAC THEN
   ASM_ARITH_TAC);;

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
              // is Block
              if word_is_clos c h1 then
                    // isClos
                    SOME ((n2w 1),l,ck) else
              if ~(h1 = h2) then SOME ((n2w 0),l,ck) else
              if l = 0 then
                   // \/ ck = 0
                   NONE else
                word_eq_list c st dm m (l - 1) ck (decode_length c
                  h1)
                  (a1 + bytes_in_word) (a2 + bytes_in_word) else
            if ~(h1 = h2) then SOME ((n2w 0),l,ck) else
            if ~(word_bit 2 h1) then
                     // is array
                     SOME ((n2w 0),l,ck) else
            if ~(word_bit 3 h1) /\ word_bit 4 h1 then
              // is cmp-by-pointer byte array
              SOME ((n2w 0),l,ck) else
             (
              // must be a bignum or word64 or cmp-by-contents byte array
              if l <= w2n (decode_length c h1) then NONE else
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
  (* word_eq gives a clock and a budget that are no larger than the
     ones it was given, so fix_clock leaves its result alone *)
  (let wle = CONJUNCT1 word_eq_LESS_EQ in
   (fun (asl,w as gl) -> CASES_ON_TAC (rand w) gl) THEN
   REWRITE_TAC[cake_def "data_to_word_memoryProof_fix_clock"] THEN
   TRY(CASES_ON_NAME "a" THEN CASES_ON_NAME "y" THEN
       REWRITE_TAC[cake_def
                     "data_to_word_memoryProof_fix_clock"]) THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
   FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP wle th)) THEN
   ARITH_TAC);;

(* HOL4 data_to_word_memoryProofScript.sml:14055-14056: a theorem
   that HOL4 states as the value of an ML expression: word_eq_def *)

(* HOL4 data_to_word_memoryProofScript.sml:14058-14059: a theorem
   that HOL4 states as the value of an ML expression: word_eq_ind *)

let bit_pattern_1100 = cake_theorem "bit_pattern_1100[simp]"
  (fun () ->
    `good_dimindex (:'a) ==>
      (((n2w 0b1100) && x1) = (n2w 0) <=> ~(word_bit 2 x1) /\
        ~(word_bit 3 (x1:'a word)))`)
  (* 12 is the two bits 2 and 3, which good_dimindex puts inside
     the word *)
  (let bw12 = prove
    (`!i. bit i (word 12:(N)word) <=>
          (i = 2 \/ i = 3) /\ i < dimindex(:N)`,
     GEN_TAC THEN REWRITE_TAC[BIT_WORD] THEN
     ASM_CASES_TAC `i < 4` THENL
      [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE
         [ARITH_RULE
            `i < 4 <=> i = 0 \/ i = 1 \/ i = 2 \/ i = 3`]) THEN
       DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
       CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC TAUT;
       SUBGOAL_THEN `12 DIV 2 EXP i = 0` SUBST1_TAC THENL
        [MATCH_MP_TAC DIV_LT THEN
         MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 4` THEN
         ASM_REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
         ASM_ARITH_TAC;
         CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]]) in
   DISCH_TAC THEN
   SUBGOAL_THEN `2 < dimindex (:'a) /\ 3 < dimindex (:'a)`
     STRIP_ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o
       REWRITE_RULE[cake_def "good_dimindex"]) THEN
     ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0;
               bw12] THEN
   ASM_MESON_TAC[]);;

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
  (* the MAX is the clock itself or the clock plus the difference,
     and word_eq_add_clock gives the second *)
  (let step th1 =
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     ASM_CASES_TAC `ck < n:num` THENL
      [SUBGOAL_THEN `MAX ck n = ck + (n - ck)` SUBST1_TAC THENL
        [ASM_ARITH_TAC; ALL_TAC] THEN
       FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC(MATCH_MP th1 th));
       SUBGOAL_THEN `MAX ck n = ck /\ n - ck = 0`
         (CONJUNCTS_THEN SUBST1_TAC) THENL
        [ASM_ARITH_TAC; ALL_TAC] THEN
       ASM_REWRITE_TAC[ADD_CLAUSES]] in
   CONJ_TAC THENL [step (CONJUNCT1 word_eq_add_clock);
                   step (CONJUNCT2 word_eq_add_clock)]);;

let word_eq_min_max_clock = cake_theorem "word_eq_min_max_clock"
  (fun () ->
    `(!x y. word_eq c st dm m l (MIN a b) a1 a2 = SOME (res,l',ck1) ==>
     (?ck1'. word_eq c st dm m l (MIN (MAX a x) (MAX b y)) a1 a2 =
       SOME (res,l',ck1'))) /\
     (!x y. word_eq_list c st dm m l (MIN a b) w a1 a2 = SOME
       (res,l',ck1) ==>
     (?ck1'. word_eq_list c st dm m l (MIN (MAX a x) (MAX b y)) w
       a1 a2 = SOME (res,l',ck1')))`)
  (* the clock of the goal is above the clock of the assumption,
     because each MAX is above its first argument, so the difference
     is what word_eq_add_clock adds *)
  (let step cj =
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     SUBGOAL_THEN `?n. MIN (MAX a x) (MAX b y) = MIN a b + n`
       (CHOOSE_THEN SUBST1_TAC) THENL
      [EXISTS_TAC `MIN (MAX a x) (MAX b y) - MIN a b` THEN
       ARITH_TAC;
       ALL_TAC] THEN
     EXISTS_TAC `ck1 + n` THEN
     FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC(MATCH_MP cj th)) in
   CONJ_TAC THENL
    [step (CONJUNCT1 (cake_thm "word_eq_add_clock"));
     step (CONJUNCT2 (cake_thm "word_eq_add_clock"))]);;

let memory_rel_isClos = cake_theorem "memory_rel_isClos[local]"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Block ts1 t1 v1,wordLang_Word
  (w1:'a word)) :: vars) /\
     word_bit 0 w1 /\
     get_real_addr c st w1 = SOME a' /\ m a' = wordLang_Word x' /\
       good_dimindex (:'a) ==>
     (isClos t1 v1 <=> word_is_clos c x')`)
  (* the Block has values, because the lowest bit of its word is
     set, so memory_rel_Block_IMP gives its header and the address
     and the header word are the ones of the goal;
     encode_header_tag_mask reads the tag off the header as sixteen
     times the tag plus two, and both that and the two closure tags
     are below the dimword, where the two numbers are equal exactly
     when the tags are *)
  (
   let n2w_11 = prove
    (`!a b. a < dimword (:N) /\ b < dimword (:N)
        ==> ((n2w a:(N)word) = n2w b <=> a = b)`,
     REPEAT STRIP_TAC THEN
     REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; GSYM dimword] THEN
     ASM_SIMP_TAC[MOD_LT]) in
   let ldi = cake_thm "LESS_DIV_16_IMP" in
   STRIP_TAC THEN
   FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun gd ->
     MP_TAC(MATCH_MP (cake_thm "memory_rel_Block_IMP")
       (CONJ mr gd)))) THEN
   REWRITE_TAC[injectivity "word_loc"; word_index] THEN
   DISCH_THEN(X_CHOOSE_THEN `u:'a word`
     (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
   COND_CASES_TAC THEN STRIP_TAC THENL
    [FIRST_ASSUM(fun pos -> FIRST_ASSUM(fun neg ->
       CONTR_TAC(MP (NOT_ELIM neg) pos)));
     ALL_TAC] THEN
   (* the address and the header word are the ones of the goal *)
   REPEAT(FIRST_X_ASSUM(fun g2 ->
     FIRST_ASSUM(fun g1 ->
       let th = REWRITE_RULE[g1; injectivity "option";
                             injectivity "word_loc"] g2 in
       if concl th = concl g2 then fail() else SUBST_ALL_TAC th))) THEN
   REWRITE_TAC[cake_def "word_is_clos"; cake_def "dataSem_isClos";
               cake_def "closure_tag"; cake_def "partial_app_tag"] THEN
   FIRST_ASSUM(fun eh -> FIRST_ASSUM(fun gd ->
     MP_TAC(MATCH_MP (cake_thm "encode_header_tag_mask")
       (CONJ eh gd)))) THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `16 * t1 + 2 < dimword (:'a)` ASSUME_TAC THENL
    [FIRST_ASSUM(fun th ->
       MP_TAC(INST [`t1:num`,`n:num`;
                    `dimword (:'a)`,`k:num`] ldi)) THEN
     ASM_ARITH_TAC;
     ALL_TAC] THEN
   SUBGOAL_THEN `16 * 30 + 2 < dimword (:'a) /\
                 16 * 31 + 2 < dimword (:'a)`
     STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[dimword] THEN
     FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o
       REWRITE_RULE[cake_def "good_dimindex"]) THEN
     CONV_TAC NUM_REDUCE_CONV;
     ALL_TAC] THEN
   ASM_SIMP_TAC[n2w_11] THEN ARITH_TAC);;

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
  (LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
   ASM_REWRITE_TAC[APPEND; cake_def "eq_explode"; LENGTH;
                   WORD_ADD_0_MUL; WORD_ADD_SUC_MUL]);;

let eq_assum_APPEND = cake_theorem "eq_assum_APPEND[local]"
  (fun () ->
    `!xs ys a.
       eq_assum a m dm (xs ++ ys) <=>
       eq_assum a m dm xs /\
       eq_assum (a + n2w (LENGTH xs) * bytes_in_word) m dm ys`)
  (LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
   ASM_REWRITE_TAC[APPEND; cake_def "eq_assum"; LENGTH;
                   WORD_ADD_0_MUL; WORD_ADD_SUC_MUL; CONJ_ASSOC]);;

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
  (* memory_rel_Block_explode_lemma says it of the first n values of
     the Block, so at the length of the Block it says it of all of
     them; what it gives has the Block itself still in front of the
     rest, which memory_rel_rearrange drops *)
  (let take_all = prove
    (`!l:A list. TAKE (LENGTH l) l = l`,
     LIST_INDUCT_TAC THEN
     REWRITE_TAC[TAKE; LENGTH; NOT_SUC; SUC_SUB1] THEN
     ASM_REWRITE_TAC[]) in
   let rearrange =
     ONCE_REWRITE_RULE [TAUT `(p ==> q ==> r) <=> (q ==> p ==> r)`]
       (cake_thm "memory_rel_rearrange") in
   STRIP_TAC THEN
   MP_TAC(SPEC `LENGTH (v1:(dataSem_v)list)`
     (cake_thm "memory_rel_Block_explode_lemma")) THEN
   ASM_REWRITE_TAC[take_all] THEN STRIP_TAC THEN CONJ_TAC THENL
    [FIRST_ASSUM(fun th ->
       MATCH_MP_TAC(MATCH_MP rearrange th) THEN
       REWRITE_TAC[MEM_APPEND; MEM] THEN MESON_TAC[]);
     FIRST_ASSUM ACCEPT_TAC]);;

let memory_rel_Loc = cake_theorem "memory_rel_Loc"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((v1,Loc n k) :: vars) /\
     (!ptr. ~(v1 = RefPtr F ptr)) ==>
     v1 = CodePtr n`)
  (* the word_addr of a root is a Loc only for a Data of a Loc,
     which only a CodePtr stands for: the RefPtr that could is a
     RefPtr F, which the hypothesis excludes *)
  (let noforall = MESON[] `(!p. ~(q /\ (x:num) = p)) <=> ~q` in
   MEMORY_REL_TAC THEN CASES_ON_NAME "v1" THEN
   RULE_ASSUM_TAC(REWRITE_RULE[injectivity "dataSem_v";
                               noforall]) THEN
   V_INV_TAC THEN ASM_REWRITE_TAC[]);;

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
  (* the words of a byte array, read out of the memory: the
     reference's v_inv gives the pointer, bc_ref_inv (at the
     reference itself, which reaches itself) gives the Bytes
     element of the heap, get_real_addr_get_addr turns the pointer
     into the address, and the word_el of the element is the header
     cell beside the word_list of the bytes.  The length comes off
     the cond of the word_el, where decode_length of the header is
     the length of the list, and the w2n of that is the length
     itself because the cond also bounds it *)
  (let hd_is n t =
     (try fst(dest_const(fst(strip_comb t))) = n
      with Failure _ -> false) in
   let rec facs t =
     if hd_is "STAR" t then
       let args = snd(strip_comb t) in
       facs (el 0 args) @ facs (el 1 args)
     else [t] in
   let rec remove1 t = function
       [] -> []
     | h :: rest -> if h = t then rest else h :: remove1 t rest in
   let grab asl p =
     tryfind (fun (_,th) ->
       if (try p th with Failure _ -> false) then th else fail()) asl in
   let is_hl th = hd_is "heap_lookup" (lhs (concl th)) in
   let sepfront names =
     W(fun (asl,w) ->
       let pred = rator (lhand w) in
       let fs = facs pred in
       let picked = map (fun n -> find (hd_is n) fs) names in
       let rest = filter (fun t -> not (mem t picked)) fs in
       let st = fst(strip_comb pred) in
       let mk a b = mk_comb(mk_comb(st,a),b) in
       let target = itlist mk picked (end_itlist mk rest) in
       SUBGOAL_THEN (mk_eq(pred,target)) SUBST1_TAC THENL
        [REWRITE_TAC[STAR_AC]; ALL_TAC]) in
   let usesep =
     FIRST_ASSUM(fun th ->
       if (try hd_is "STAR" (rator (concl th))
           with Failure _ -> false)
       then MP_TAC th else fail()) in
   MEMORY_REL_TAC THEN V_INV_TAC THEN
   TRY(FIRST_ASSUM(fun t1 -> FIRST_ASSUM(fun t2 ->
     CONTR_TAC(REWRITE_RULE[injectivity "option";
                            distinctness "bvlSem_ref"]
                 (TRANS (SYM t1) t2))))) THEN
   FIRST_X_ASSUM(fun th ->
     if is_forall (concl th) &&
        hd_is "bc_ref_inv" (rand (snd(strip_forall(concl th))))
     then MP_TAC(SPEC `p:num` th) else fail()) THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL
      [REWRITE_TAC[cake_def "reachable_refs"; MEM] THEN
       EXISTS_TAC `RefPtr bl p:dataSem_v` THEN
       EXISTS_TAC `p:num` THEN
       REWRITE_TAC[cake_def "get_refs"; MEM;
                   CONJUNCT1(SPEC_ALL RTC_RULES)];
       ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   REWRITE_TAC[cake_def "bc_ref_inv"] THEN
   ASM_SIMP_TAC[FLOOKUP_DEF] THEN
   MATCH_REDUCE_TAC THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   DISCH_TAC THEN
   FIRST_X_ASSUM(fun th ->
     if hd_is "heap_in_memory_store" (concl th)
     then MP_TAC(REWRITE_RULE[cake_def "heap_in_memory_store"] th)
     else fail()) THEN
   STRIP_TAC THEN
   W(fun (asl,w) ->
     let hl = grab asl is_hl in
     let hlen = grab asl (fun th ->
       hd_is "heap_length" (lhand (concl th))) in
     let cu = grab asl (fun th ->
       hd_is "FLOOKUP" (lhs (concl th)) &&
       fst(dest_const(rand(lhs(concl th)))) = "CurrHeap") in
     let gd = grab asl (fun th -> concl th = `good_dimindex (:'a)`) in
     let ga = grab asl (fun th -> hd_is "get_addr" (lhs (concl th))) in
     let gr = grab asl (fun th ->
       hd_is "get_real_addr" (lhs (concl th))) in
     let th = CONJUNCT2(SPEC (rand (lhs (concl ga)))
       (GEN `w:('a)word_loc`
         (MATCH_MP (cake_thm "get_real_addr_get_addr")
           (CONJ hlen (CONJ hl (CONJ cu gd)))))) in
     let eq = REWRITE_RULE[injectivity "option"]
                (TRANS (SYM gr) (REWRITE_RULE[ga] th)) in
     let r = rhs (concl eq) in
     let args = snd(strip_comb (rand r)) in
     let mul = fst(strip_comb (rand r)) in
     let swap = mk_comb(rator r,
                  mk_comb(mk_comb(mul,el 1 args),el 0 args)) in
     SUBST_ALL_TAC(TRANS eq (WORD_RULE (mk_eq(r,swap))))) THEN
   W(fun (asl,w) ->
     MP_TAC(MATCH_MP (cake_thm "heap_lookup_SPLIT")
              (grab asl is_hl))) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   VAR_EQ_TAC THEN
   FIRST_X_ASSUM(fun th ->
     if (try hd_is "fmap_apply" (lhs (concl th))
         with Failure _ -> false)
     then SUBST_ALL_TAC th else fail()) THEN
   FIRST_X_ASSUM(fun th ->
     if (try hd_is "STAR" (rator (concl th)) with Failure _ -> false)
     then MP_TAC th else fail()) THEN
   REWRITE_TAC[cake_thm "word_heap_APPEND"; cake_def "word_heap";
               cake_def "Bytes"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[cake_def "word_el"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[cake_def "word_payload"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[cake_def "misc_word_list"; LENGTH_MAP;
               cake_thm "LENGTH_write_bytes"; LENGTH_REPLICATE] THEN
   sepfront ["cond"] THEN
   REWRITE_TAC[cond_STAR] THEN
   DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
   sepfront ["set_sep_one"] THEN
   DISCH_THEN(fun sep ->
     let rd = MATCH_MP read_fun2set sep in
     EXISTS_TAC (rand (rhs (concl (CONJUNCT1 rd)))) THEN
     ASSUME_TAC sep THEN STRIP_ASSUME_TAC rd) THEN
   W(fun (asl,w) ->
     let sep = grab asl (fun th -> hd_is "STAR" (rator (concl th))) in
     let fs = facs (rator (concl sep)) in
     let wl = find (hd_is "misc_word_list") fs in
     let rest = remove1 wl fs in
     let st = fst(strip_comb (rator (concl sep))) in
     let mk a b = mk_comb(mk_comb(st,a),b) in
     EXISTS_TAC (end_itlist mk rest)) THEN
   FIRST_ASSUM(fun dl ->
     if (try hd_is "decode_length" (lhs (concl dl))
         with Failure _ -> false)
     then REWRITE_TAC[dl] else fail()) THEN
   REWRITE_TAC[VAL_WORD; GSYM dimword] THEN
   SUBGOAL_THEN
     `(LENGTH (vals:(word8)list) DIV (dimindex (:'a) DIV 8) + 1)
        MOD dimword (:'a) =
      LENGTH vals DIV (dimindex (:'a) DIV 8) + 1`
     SUBST1_TAC THENL
    [MATCH_MP_TAC MOD_LT THEN
     TRANS_TAC LTE_TRANS `2 EXP (dimindex (:'a) - 4)` THEN
     ASM_REWRITE_TAC[dimword] THEN
     SIMP_TAC[LE_EXP; ARITH] THEN ARITH_TAC;
     ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THENL
    [usesep THEN REWRITE_TAC[STAR_AC];
     TRANS_TAC LTE_TRANS `2 EXP (dimindex (:'a) - 4)` THEN
     ASM_REWRITE_TAC[dimword] THEN
     SIMP_TAC[LE_EXP; ARITH] THEN ARITH_TAC]);;

let poly_inj_lemma = cake_theorem "poly_inj_lemma"
  (fun () ->
    `(a:num) < b /\ a' < b /\ a + b * c = a' + b * c' ==> a = a' /\ c
  = c'`)
  (* the remainder of the division by b gives a and a', and what is
     left of the equation then cancels b *)
  (STRIP_TAC THEN
   SUBGOAL_THEN `(a:num) = a'` ASSUME_TAC THENL
    [SUBGOAL_THEN
       `((a:num) + b * c) MOD b = (a' + b * c') MOD b` MP_TAC THENL
      [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
     REWRITE_TAC[MOD_MULT_ADD] THEN ASM_SIMP_TAC[MOD_LT];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `(a:num) + b * c = a' + b * c'` THEN
   ASM_REWRITE_TAC[EQ_ADD_LCANCEL; EQ_MULT_LCANCEL] THEN
   ARITH_ASM_TAC);;

let mw2n_inj = cake_theorem "mw2n_inj"
  (fun () ->
    `!x y. LENGTH x = LENGTH y ==> (mw2n (x:('a word) list) = mw2n y
  <=> x = y)`)
  (* the value of a multiword is its first word plus the dimword
     times the value of the rest, and a word is below the dimword,
     so poly_inj_lemma takes the sum apart *)
  (let pil = GEN_ALL (cake_thm "poly_inj_lemma") in
   let wlt = prove
    (`!(x:(N)word). w2n x < dimword (:N)`,
     REWRITE_TAC[dimword; VAL_BOUND]) in
   LIST_INDUCT_TAC THEN GEN_TAC THEN
   STRUCT_CASES_TAC(ISPEC `y:('a word)list` list_CASES_v) THEN
   REWRITE_TAC[LENGTH; cake_def "mw2n"; CONS_11; NOT_CONS_NIL;
               ARITH_RULE `(0 = SUC n) <=> F`;
               ARITH_RULE `(SUC n = 0) <=> F`; SUC_INJ] THEN
   DISCH_TAC THEN EQ_TAC THENL
    [DISCH_TAC THEN
     FIRST_ASSUM(fun eq ->
       MP_TAC(MATCH_MP pil (CONJ (ISPEC `h:'a word` wlt)
         (CONJ (ISPEC `v:'a word` wlt) eq)))) THEN
     DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
     CONJ_TAC THENL
      [ASM_MESON_TAC[VAL_EQ];
       FIRST_X_ASSUM(fun ih ->
         MP_TAC(SPEC `vs:('a word)list` ih)) THEN
       ASM_REWRITE_TAC[]];
     DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN REWRITE_TAC[]]);;

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
  (ARITH_TAC);;

let MIN_SUB = cake_theorem "MIN_SUB[local]"
  (fun () ->
    `MIN a b - c = MIN (a - c) (b - c)`)
  (ARITH_TAC);;

let MAX_ADD = cake_theorem "MAX_ADD[local]"
  (fun () ->
    `MAX a b + c = MAX (a + c) (b + c)`)
  (ARITH_TAC);;

let MAX_SUB = cake_theorem "MAX_SUB[local]"
  (fun () ->
    `MAX a b - c = MAX (a - c) (b - c)`)
  (ARITH_TAC);;

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
  (REWRITE_TAC[CONJUNCT1 do_eq_IFF_vb_eq_size]);;

let vb_eq_size_IMP_do_eq = cake_theorem "vb_eq_size_IMP_do_eq"
  (fun () ->
    `vb_eq_size refs v1 v2 = SOME (n,b) ==>
     do_eq refs v1 v2 = Eq_val b`)
  (REWRITE_TAC[CONJUNCT1 do_eq_IFF_vb_eq_size] THEN MESON_TAC[]);;

let memory_rel_ptr_vb_eq = cake_theorem "memory_rel_ptr_vb_eq"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((v1,x1) :: (v2,(x1:'a
  word_loc)) :: vars) /\
     vb_eq_size refs v1 v2 = SOME (n,b) /\
     good_dimindex (:'a) ==> b`)
  (* a vb_eq_size that gives b is a do_eq that gives Eq_val b *)
  (STRIP_TAC THEN
   FIRST_ASSUM(fun th ->
     MP_TAC(MATCH_MP vb_eq_size_IMP_do_eq th)) THEN
   DISCH_TAC THEN
   MATCH_MP_TAC (cake_thm "memory_rel_ptr_eq") THEN
   ASM_MESON_TAC[]);;

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
  (* do_eq gives the size of the comparison, memory_rel_limit bounds
     it by the clock of MustTerminate (and the dimword is at least
     one, so the bound by the limit less one holds as well), and
     word_eq_thm0 is the comparison itself *)
  (STRIP_TAC THEN
   FIRST_ASSUM(fun de ->
     MP_TAC(MATCH_MP (cake_thm "do_eq_IMP_vb_eq_size") de)) THEN
   DISCH_THEN(X_CHOOSE_THEN `nn:num` ASSUME_TAC) THEN
   FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun vb -> FIRST_ASSUM(fun gd ->
     ASSUME_TAC(MATCH_MP (SPEC_ALL (cake_thm "memory_rel_limit"))
       (CONJ mr (CONJ vb gd)))))) THEN
   SUBGOAL_THEN `1 <= dimword (:'a)` ASSUME_TAC THENL
    [REWRITE_TAC[dimword; ARITH_RULE `1 <= n <=> ~(n = 0)`;
                 EXP_EQ_0; ARITH_EQ];
     ALL_TAC] THEN
   SUBGOAL_THEN
     `nn * dimword (:'a) < MustTerminate_limit (:'a) - 1`
     ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
   FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun vb -> FIRST_ASSUM(fun lt ->
     FIRST_ASSUM(fun gd ->
       let ck = REFL `MIN (vs_depth v1) (vs_depth v2)` in
       let th = MATCH_MP (CONJUNCT1 (cake_thm "word_eq_thm0"))
                  (CONJ mr (CONJ vb (CONJ ck (CONJ lt gd)))) in
       MP_TAC th)))) THEN
   STRIP_TAC THEN ASM_EXISTS_TAC THEN ASM_REWRITE_TAC[]);;

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
  (* the memory holds the words of the list, so the loop reads them
     one at a time: the cell at the address is the head, which
     read_fun2set takes out of the separating product, and the
     induction hypothesis takes the cell into the frame *)
  (let hd_is n t =
     (try fst(dest_const(fst(strip_comb t))) = n
      with Failure _ -> false) in
   let rec facs t =
     if hd_is "STAR" t then
       let args = snd(strip_comb t) in
       facs (el 0 args) @ facs (el 1 args)
     else [t] in
   let sepasm (asl,w) =
     tryfind (fun (_,th) ->
       let c = concl th in
       if hd_is "STAR" (rator c) then rator c else fail()) asl in
   let witness = W(fun gl ->
     let ante = sepasm gl in
     let fs = facs ante in
     let one = find (hd_is "set_sep_one") fs in
     let rest = filter (fun t -> not (hd_is "set_sep_one" t) &&
                                 not (hd_is "misc_word_list" t)) fs in
     let st = fst(strip_comb ante) in
     let mk a b = mk_comb(mk_comb(st,a),b) in
     EXISTS_TAC (mk one (end_itlist mk rest))) in
   let usesep =
     FIRST_ASSUM(fun th ->
       if hd_is "STAR" (rator (concl th)) then MP_TAC th else fail()) in
   LIST_INDUCT_TAC THEN GEN_TAC THEN CASES_BY_NAME "ys" THEN
   REWRITE_TAC[cake_def "word_mem_eq"; LENGTH; MAP; NOT_CONS_NIL;
               NOT_SUC; GSYM NOT_SUC; SUC_INJ; CONS_11] THEN
   REPEAT GEN_TAC THEN
   REWRITE_TAC[cake_def "misc_word_list"; GSYM STAR_ASSOC] THEN
   STRIP_TAC THEN
   FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP read_fun2set th)) THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
   ASM_REWRITE_TAC[cake_def "isWord"; injectivity "word_loc"] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[]) THEN VAR_EQ_TAC THEN
   REWRITE_TAC[] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN witness THEN
   ASM_REWRITE_TAC[] THEN usesep THEN REWRITE_TAC[STAR_AC]);;

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
  (* seven has no bit above the second, and the shift by more than
     two has none below the third, so the bit where the shifts
     differ is a bit where the ors differ *)
  (let odd_div = prove
    (`!k m i. k < 2 EXP m /\ m <= i
              ==> (ODD (k DIV 2 EXP i) <=> F)`,
     REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `k DIV 2 EXP i = 0` SUBST1_TAC THENL
      [MATCH_MP_TAC DIV_LT THEN
       TRANS_TAC LTE_TRANS `2 EXP m` THEN
       ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC;
       REWRITE_TAC[ODD]]) in
   let bit7 = prove
    (`!i. 3 <= i ==> (word_bit i (n2w 7:(N)word) <=> F)`,
     REPEAT STRIP_TAC THEN REWRITE_TAC[BIT_WORD] THEN
     MP_TAC(SPECL [`7`; `3`; `i:num`] odd_div) THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
     DISCH_THEN(fun th -> REWRITE_TAC[th])) in
   MATCH_MP_TAC(TAUT `(q ==> b ==> a) ==> (~a /\ q ==> ~b)`) THEN
   DISCH_TAC THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR; BIT_WORD_SHL] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
   ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `3 <= i` THENL
    [ASM_SIMP_TAC[bit7];
     ASM_SIMP_TAC[ARITH_RULE `~(3 <= i) /\ 2 < k ==> ~(k <= i)`]]);;

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
  (* the header of a byte array keeps the length in the field above
     the shift, so two of them agree only when their lengths do: the
     tag is below the shift and the length plus the word size is
     below two to the width of the field, because the byte length is
     below two to the length size *)
  (let hi = prove
    (`!n r (i:num). n < 2 EXP r /\ r <= i
        ==> ~(bit i ((n2w n):'a word))`,
     MATCH_ACCEPT_TAC BIT_WORD_HI) in
   let b7 = prove
    (`!j. j < dimindex (:'a)
          ==> (bit j ((n2w 7):'a word) <=> j < 3)`,
     GEN_TAC THEN DISCH_TAC THEN
     ASM_CASES_TAC `(j:num) < 3` THEN ASM_REWRITE_TAC[] THENL
      [FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP
         (ARITH_RULE `(j:num) < 3 ==> j = 0 \/ j = 1 \/ j = 2`)) THEN
       ASM_REWRITE_TAC[BIT_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
       ASM_ARITH_TAC;
       MP_TAC(ISPECL [`7`; `3`; `j:num`] hi) THEN
       ASM_SIMP_TAC[ARITH_RULE `~((j:num) < 3) ==> 3 <= j`] THEN
       CONV_TAC NUM_REDUCE_CONV]) in
   let n2w_inj = prove
    (`!a b m. a < 2 EXP m /\ b < 2 EXP m /\ m <= dimindex (:'a) /\
              ((n2w a):'a word = n2w b)
        ==> a = b`,
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o AP_TERM `val:'a word->num`) THEN
     REWRITE_TAC[VAL_WORD] THEN
     SUBGOAL_THEN
       `a < 2 EXP dimindex (:'a) /\ b < 2 EXP dimindex (:'a)`
       STRIP_ASSUME_TAC THENL
      [CONJ_TAC THEN TRANS_TAC LTE_TRANS `2 EXP m` THEN
       ASM_SIMP_TAC[LE_EXP; ARITH];
       ASM_SIMP_TAC[MOD_LT]]) in
   let gen = prove
    (`!(s:num) a m n.
        3 <= s /\ s < dimindex (:'a) /\
        m + a < 2 EXP (dimindex (:'a) - s) /\
        n + a < 2 EXP (dimindex (:'a) - s) /\
        ((((n2w (m + a)):'a word) << s || n2w 7) =
         (((n2w (n + a)):'a word) << s || n2w 7))
        ==> m = n`,
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     SUBGOAL_THEN `!j. bit j ((n2w 7):'a word) ==> j < s`
       ASSUME_TAC THENL
      [X_GEN_TAC `j:num` THEN
       ASM_CASES_TAC `j < dimindex (:'a)` THENL
        [ASM_SIMP_TAC[b7] THEN ASM_ARITH_TAC;
         ASM_SIMP_TAC[BIT_TRIVIAL;
                      ARITH_RULE `~((a:num) < b) ==> b <= a`]];
       ALL_TAC] THEN
     SUBGOAL_THEN
       `(!j. bit j ((n2w (m + a)):'a word) ==> j + s < dimindex (:'a))
        /\
        (!j. bit j ((n2w (n + a)):'a word) ==> j + s < dimindex (:'a))`
       STRIP_ASSUME_TAC THENL
      [CONJ_TAC THEN X_GEN_TAC `j:num` THEN
       ASM_CASES_TAC `j + s < dimindex (:'a)` THEN
       ASM_REWRITE_TAC[] THENL
        [MP_TAC(ISPECL [`m + a:num`; `dimindex (:'a) - s`; `j:num`] hi);
         MP_TAC(ISPECL [`n + a:num`; `dimindex (:'a) - s`;
                        `j:num`] hi)] THEN
       ASM_SIMP_TAC[ARITH_RULE
         `~(j + s < d) /\ s < d ==> d - s <= j`] THEN
       REWRITE_TAC[];
       ALL_TAC] THEN
     SUBGOAL_THEN `m + a = n + a` MP_TAC THENL
      [MATCH_MP_TAC n2w_inj THEN
       EXISTS_TAC `dimindex (:'a) - s` THEN
       ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
        [ARITH_TAC; ALL_TAC] THEN
       FIRST_X_ASSUM(fun th -> MP_TAC(AP_TERM
         `\w:'a word. word_ushr w s` th)) THEN
       CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
       ASM_SIMP_TAC[USHR_OR_LOW; USHR_SHL_CANCEL];
       ARITH_TAC]) in
   let usedim =
     FIRST_X_ASSUM(fun dd ->
       let c = concl dd in
       if is_eq c &&
          (try fst(dest_const(fst(strip_comb(lhs c)))) = "dimindex"
           with Failure _ -> false)
       then RULE_ASSUM_TAC(REWRITE_RULE[dd; cake_def "byte_len"]) THEN
            ASSUME_TAC dd
       else fail()) in
   STRIP_TAC THEN EQ_TAC THENL
    [ALL_TAC; DISCH_THEN SUBST1_TAC THEN REFL_TAC] THEN
   FIRST_ASSUM(DISJ_CASES_THEN ASSUME_TAC o
     REWRITE_RULE[cake_def "good_dimindex"]) THEN
   usedim THEN
   REWRITE_TAC[cake_def "make_byte_header"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
   DISCH_TAC THEN MATCH_MP_TAC gen THENL
    [MAP_EVERY EXISTS_TAC
       [`30 - data_to_word_config_len_size c`; `4`] THEN
     SUBGOAL_THEN
       `dimindex (:'a) - (30 - data_to_word_config_len_size c) =
        data_to_word_config_len_size c + 2`
       SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
     REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
     MP_TAC(SPEC `m:num` (MATCH_MP DIVISION (ARITH_RULE `~(4 = 0)`)))
     THEN
     MP_TAC(SPEC `n:num` (MATCH_MP DIVISION (ARITH_RULE `~(4 = 0)`)))
     THEN ASM_ARITH_TAC;
     MAP_EVERY EXISTS_TAC
       [`61 - data_to_word_config_len_size c`; `8`] THEN
     SUBGOAL_THEN
       `dimindex (:'a) - (61 - data_to_word_config_len_size c) =
        data_to_word_config_len_size c + 3`
       SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
     REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
     MP_TAC(SPEC `m:num` (MATCH_MP DIVISION (ARITH_RULE `~(8 = 0)`)))
     THEN
     MP_TAC(SPEC `n:num` (MATCH_MP DIVISION (ARITH_RULE `~(8 = 0)`)))
     THEN ASM_ARITH_TAC]);;

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
  (REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0;
               BIT_WORD_1] THEN
   MESON_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> 0 < n`]);;

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
  (* a byte of a byte array can be stored: memory_rel_ByteArray_IMP
     says that the load of that byte works, which tells that the
     cell the store writes holds a word and is in the domain, and
     it says that the memory relation survives the write.  Those
     two are about the address of the lemma's own existential, and
     the statement's is the same because get_real_addr is a
     function *)
  (let hd_is n t =
   (try fst(dest_const(fst(strip_comb t))) = n
    with Failure _ -> false) in
   (* what a load of a byte says about the cell it reads: it holds a
      word and its address is in the domain *)
   let loadword = prove
    (`!(m:('a)word->('a)word_loc) dm be' w x.
        mem_load_byte_aux m dm be' w = SOME x
        ==> (?v. m (byte_align w) = wordLang_Word v) /\
            byte_align w IN dm`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[cake_def "mem_load_byte_aux"] THEN
     STRUCT_CASES_TAC(ISPEC `(m:('a)word->('a)word_loc) (byte_align w)`
                        (cases_of `:('a)word_loc`)) THEN
     MATCH_REDUCE_TAC THEN
     REWRITE_TAC[distinctness "option"] THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC[distinctness "option"] THEN
     MESON_TAC[]) in
   DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
   FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun lk -> FIRST_ASSUM(fun gd ->
     MP_TAC(MATCH_MP (cake_thm "memory_rel_ByteArray_IMP")
              (CONJ mr (CONJ lk gd)))))) THEN
   DISCH_THEN(STRIP_ASSUME_TAC o
              REWRITE_RULE[injectivity "word_loc"]) THEN
   VAR_EQ_TAC THEN
   FIRST_ASSUM(fun e1 -> FIRST_ASSUM(fun e2 ->
     let e = REWRITE_RULE[injectivity "option"] (TRANS (SYM e1) e2) in
     if is_var (lhs (concl e)) && lhs (concl e) <> rhs (concl e)
     then SUBST_ALL_TAC e else fail())) THEN
   FIRST_X_ASSUM(fun ld ->
     if is_forall (concl ld) &&
        (try hd_is "mem_load_byte_aux"
               (lhs (rand (snd(strip_forall (concl ld)))))
         with Failure _ -> false)
     then MP_TAC(SPEC `i:num` ld) else fail()) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(fun le -> STRIP_ASSUME_TAC(MATCH_MP loadword le)) THEN
   FIRST_X_ASSUM(fun st ->
     if is_forall (concl st) &&
        (try hd_is "memory_rel"
               (snd(dest_let(rand(snd(strip_forall (concl st))))))
         with Failure _ -> false)
     then MP_TAC(SPECL [`i:num`; `b:(word8)`] st) else fail()) THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ASM_REWRITE_TAC[cake_def "theWord"] THEN
   DISCH_TAC THEN
   ASM_REWRITE_TAC[cake_def "mem_store_byte_aux"] THEN
   MATCH_REDUCE_TAC THEN
   ASM_REWRITE_TAC[injectivity "option"; UNWIND_THM1; UNWIND_THM2]);;

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
  (* the offsets are of naturals, so copy_array is NONE exactly when
     the source is too short and otherwise takes the n elements from
     the offset on, and list_copy_fwd_eq copies them into a list of
     n zeroes: the whole of it, so nothing of the zeroes is left *)
  (let take0 = prove
    (`!l:A list. TAKE 0 l = []`,
     LIST_INDUCT_TAC THEN REWRITE_TAC[TAKE]) in
   let dropall = prove
    (`!n (x:A). DROP n (REPLICATE n x) = []`,
     INDUCT_TAC THEN
     ASM_REWRITE_TAC[DROP; REPLICATE; NOT_SUC; SUC_SUB1]) in
   REPEAT GEN_TAC THEN
   REWRITE_TAC[cake_def "copy_array"; I_THM; INT_OF_NUM_ADD;
               INT_ABS_NUM; NUM_OF_INT_OF_NUM; INT_OF_NUM_LT;
               LT] THEN
   COND_CASES_TAC THEN
   REWRITE_TAC[distinctness "option"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[injectivity "option"] THEN
   DISCH_THEN(SUBST1_TAC o SYM) THEN
   W(fun (_,w) -> MP_TAC(PART_MATCH (lhs o rand)
       (cake_thm "list_copy_fwd_eq") (lhand w))) THEN
   REWRITE_TAC[LENGTH_REPLICATE; ADD_CLAUSES; LE_REFL] THEN
   ANTS_TAC THENL
    [ASM_ARITH_TAC;
     REWRITE_TAC[take0; dropall; APPEND; APPEND_NIL] THEN
     DISCH_THEN ACCEPT_TAC]);;

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
  (* a copy of no bytes is the memory itself, and good_dimindex puts
     the dimword above the four that the clause asks for *)
  (REWRITE_TAC[cake_def "good_dimindex"] THEN STRIP_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [cake_def "word_copy_bwd"] THEN
   ASM_REWRITE_TAC[dimword; WORD_ULT; VAL_WORD; VAL_WORD_0] THEN
   CONV_TAC NUM_REDUCE_CONV);;

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
  (REWRITE_TAC[cake_def "word_of_byte"] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   COND_CASES_TAC THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR; BIT_WORD_SHL;
               BIT_WORD_0]);;

let last_bytes_0 = cake_theorem "last_bytes_0"
  (fun () ->
    `!nb a. last_bytes nb (n2w 0) a (n2w 0) be = (n2w 0)`)
  (* the bytes of zero written into zero leave zero: a byte set to
     zero in a word of zeroes is an or of words with no bit *)
  (let sb0 = prove
    (`!a be. set_byte a (n2w 0) (n2w 0:(N)word) be = n2w 0`,
     REPEAT GEN_TAC THEN REWRITE_TAC[cake_def "set_byte"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[word_slice_alt; WORD_EQ_BITS_ALT; BIT_WORD_OR;
                 BIT_WORD_SHL; BIT_WORD_0; BIT_WORD_SUBWORD;
                 BIT_WORD_ZX] THEN
     REWRITE_TAC[BIT_WORD_0]) in
   INDUCT_TAC THEN GEN_TAC THEN
   ONCE_REWRITE_TAC[cake_def "last_bytes"] THEN
   REWRITE_TAC[ARITH_RULE `~(SUC n = 0)`] THEN
   ASM_REWRITE_TAC[ARITH_RULE `SUC n - 1 = n`; sb0]);;

let LUPDATE_REPLICATE = cake_theorem "LUPDATE_REPLICATE[simp]"
  (fun () ->
    `!n a. LUPDATE x a (REPLICATE n x) = REPLICATE n x`)
  (INDUCT_TAC THEN GEN_TAC THEN REWRITE_TAC[REPLICATE; LUPDATE] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

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
  (* writing bytes leaves a word a word: the write either updates
     the address with a word or leaves the memory alone *)
  (let isw = prove
    (`!w. isWord (wordLang_Word w)`,
     GEN_TAC THEN REWRITE_TAC[cake_def "isWord"] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[]) in
   LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
    [REWRITE_TAC[cake_def "write_bytearray"] THEN
     FIRST_ASSUM ACCEPT_TAC;
     REWRITE_TAC[cake_def "write_bytearray";
                 cake_def "mem_store_byte_aux"] THEN
     EVERY_CASE_TAC THEN
     POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
     REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN
     REWRITE_TAC[UPDATE] THEN
     COND_CASES_TAC THEN REWRITE_TAC[isw] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

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
  (* the space of the statement is the sp of the invariant itself:
     the store's NextFree and TriggerGC are the two ends of it, so
     their difference is the bytes in a word times it, and what is
     left to see is that it fits in a word, which the heap's own
     bound gives because the unused space is part of the heap *)
  (let hd_is n t =
   (try fst(dest_const(fst(strip_comb t))) = n
    with Failure _ -> false) in
 let grab asl p =
   tryfind (fun (_,th) ->
     if (try p th with Failure _ -> false) then th else fail())
     asl in
   DISCH_TAC THEN
   FIRST_ASSUM(fun mr ->
     if hd_is "memory_rel" (concl mr)
     then MP_TAC(REWRITE_RULE[cake_def "memory_rel"] mr)
     else fail()) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   FIRST_ASSUM(fun hm ->
     if hd_is "heap_in_memory_store" (concl hm)
     then MP_TAC(REWRITE_RULE[cake_def "heap_in_memory_store"] hm)
     else fail()) THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   W(fun (asl,w) ->
     let look n = grab asl (fun th ->
       hd_is "FLOOKUP" (lhs (concl th)) &&
       fst(dest_const(rand(lhs(concl th)))) = n) in
     let hm = grab asl (fun th ->
       hd_is "heap_in_memory_store" (concl th)) in
     let args = snd(strip_comb (concl hm)) in
     EXISTS_TAC (rand (rand (rhs (concl (look "NextFree"))))) THEN
     EXISTS_TAC (rand (rand (rhs (concl (look "TriggerGC"))))) THEN
     EXISTS_TAC (el 2 args) THEN
     ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THENL
      [REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC WORD_RULE;
       REWRITE_TAC[cake_def "memory_rel"] THEN
       EXISTS_TAC (el 0 args) THEN EXISTS_TAC (el 9 args) THEN
       EXISTS_TAC (el 1 args) THEN EXISTS_TAC (el 2 args) THEN
       EXISTS_TAC (el 3 args) THEN EXISTS_TAC (el 4 args) THEN
       ASM_REWRITE_TAC[LE_REFL];
       DISCH_TAC THEN
       FIRST_ASSUM(fun wm ->
         if hd_is "word_ml_inv" (concl wm)
         then MP_TAC(REWRITE_RULE[cake_def "word_ml_inv";
                                  cake_def "abs_ml_inv";
                                  cake_def "unused_space_inv"] wm)
         else fail()) THEN
       DISCH_THEN STRIP_ASSUME_TAC THEN
       W(fun (asl,w) ->
         let hb = grab asl (fun th ->
           hd_is "<" (concl th) && hd_is "*" (lhand (concl th)) &&
           hd_is "+" (lhand (lhand (concl th)))) in
         TRANS_TAC LET_TRANS (lhand (concl hb))) THEN
       ASM_REWRITE_TAC[] THEN
       GEN_REWRITE_TAC LAND_CONV [MULT_SYM] THEN
       REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
       W(fun (asl,w) ->
         let us = grab asl (fun th ->
           hd_is "<=" (concl th) && hd_is "+" (lhand (concl th))) in
         UNDISCH_TAC (concl us)) THEN
       ARITH_TAC]));;

let get_lowerbits_ptrbits = cake_theorem "get_lowerbits_ptrbits"
  (fun () ->
    `get_lowerbits c (wordLang_Word (ptr_bits c x y)) = (ptr_bits c x
  y || (n2w 1))`)
  (* the bits of ptr_bits are below small_shift_length (that is what
     maxout_bits_IMP says of each of the two), so the word_bits of
     it is itself *)
  (let mb = REWRITE_RULE[word_index] maxout_bits_IMP in
   let bits_lt = prove
    (`!i. i < dimindex (:'a) /\ bit i (ptr_bits c x y:'a word)
          ==> i < small_shift_length c`,
     REWRITE_TAC[cake_def "ptr_bits"; cake_def "small_shift_length";
                 BIT_WORD_OR] THEN
     REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(fun th ->
       MP_TAC(MATCH_MP mb
         (CONJ (ASSUME `i < dimindex (:'a)`) th))) THEN
     ARITH_TAC) in
   REWRITE_TAC[cake_def "get_lowerbits"] THEN MATCH_REDUCE_TAC THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT; word_bits; BIT_WORD_SUBWORD;
               ADD_CLAUSES] THEN
   GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
    [SIMP_TAC[];
     DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
     FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
       MP_TAC(MATCH_MP bits_lt (CONJ th2 th1)))) THEN
     ASM_ARITH_TAC]);;

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
  (LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN GEN_TAC THEN
   ONCE_REWRITE_TAC[cake_def "append_writes"] THEN
   CASES_ON_NAME "t" THEN MATCH_REDUCE_TAC THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ASM_SIMP_TAC[LENGTH; NOT_CONS_NIL] THEN ARITH_TAC);;

let ptr_bits_or_1_add_1 = cake_theorem "ptr_bits_or_1_add_1"
  (fun () ->
    `ptr_bits c tag len || (n2w 1) = ptr_bits c tag len + (n2w 1)`)
  (* the lowest bit of ptr_bits is clear, because both of the
     maxouts it ors are shifted up by at least one, so the or with
     one is the sum with one *)
  (CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORD_ADD_OR THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0;
               BIT_WORD_1] THEN
   X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[cake_def "ptr_bits"; BIT_WORD_OR;
               cake_def "maxout_bits"] THEN
   REPEAT COND_CASES_TAC THEN
   REWRITE_TAC[BIT_WORD_SHL; GSYM word_index] THEN
   ASM_SIMP_TAC[cake_thm "all_ones_bit";
                ARITH_RULE `0 < d <=> 1 <= d:num`; DIMINDEX_GE_1] THEN
   REWRITE_TAC[ARITH_RULE `~(1 + n <= 0)`;
               ARITH_RULE `~(1 <= 0)`] THEN
   CONV_TAC TAUT);;

let all_ones_n2w = cake_theorem "all_ones_n2w"
  (fun () ->
    `all_ones (l + b) b = n2w (2 EXP l - 1) << b`)
  (* and the same word is the mask of l ones shifted up by b, whose
     bits HOL Light's BIT_MASK_WORD gives *)
  (REWRITE_TAC[cake_def "all_ones"] THEN COND_CASES_TAC THENL
    [SUBGOAL_THEN `l = 0` SUBST1_TAC THENL
      [POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
     CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_RULE;
     ALL_TAC] THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT; word_slice; word_bits;
               BIT_WORD_SHL; BIT_WORD_SUBWORD; BIT_WORD_NOT;
               BIT_WORD_0; BIT_MASK_WORD] THEN
   X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   REWRITE_TAC[ARITH_RULE `MIN a b = if a <= b then a else b`] THEN
   REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   POP_ASSUM_LIST(fun ths -> MAP_EVERY MP_TAC ths) THEN ARITH_TAC);;

let ptr_bits_lemma = cake_theorem "ptr_bits_lemma"
  (fun () ->
    `(w << shift_length conf || ptr_bits conf 0 2 || (n2w 1)) =
     w << shift_length conf + ptr_bits conf 0 2 + (n2w 1)`)
  (* the three parts of a pointer do not share a bit, so the or
     of them is their sum: the bits of a maxout_bits lie between
     its shift and its shift plus its width, so the ones of
     ptr_bits lie below the shift_length and above the zeroth *)
  (let bit_hi = prove
    (`!n r (i:num). n < 2 EXP r /\ r <= i
        ==> ~(bit i ((n2w n):(N)word))`,
     REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[BIT_WORD] THEN
     SUBGOAL_THEN `n DIV 2 EXP i = 0` SUBST1_TAC THENL
      [MATCH_MP_TAC DIV_LT THEN
       TRANS_TAC LTE_TRANS `2 EXP r` THEN
       ASM_SIMP_TAC[LE_EXP; ARITH];
       REWRITE_TAC[ODD]]) in
   let bit_maxout = prove
    (`!n rep k j. bit j ((maxout_bits n rep k):(N)word)
        ==> k <= j /\ j < k + rep`,
     REPEAT GEN_TAC THEN REWRITE_TAC[cake_def "maxout_bits"] THEN
     COND_CASES_TAC THEN REWRITE_TAC[cake_def "all_ones"] THENL
      [REWRITE_TAC[BIT_WORD_SHL] THEN STRIP_TAC THEN
       CONJ_TAC THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC(ARITH_RULE
         `k <= j /\ ~(rep <= j - k) ==> j < k + rep`) THEN
       ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
       MP_TAC(ISPECL [`n:num`; `rep:num`; `j - k`] bit_hi) THEN
       ASM_REWRITE_TAC[] THEN ARITH_NO_BIT_TAC;
       COND_CASES_TAC THEN
       REWRITE_TAC[BIT_WORD_0; word_slice; word_bits; BIT_WORD_SHL;
                   BIT_WORD_SUBWORD] THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_NO_BIT_TAC]) in
   let bit_pb = prove
    (`!conf j. bit j ((ptr_bits conf 0 2):(N)word)
        ==> 1 <= j /\ j < small_shift_length conf`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[cake_def "ptr_bits"; cake_def "small_shift_length";
                 BIT_WORD_OR] THEN
     DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (DISJ_CASES_THEN
       (fun th -> MP_TAC(MATCH_MP bit_maxout th)))) THEN
     ARITH_TAC) in
   let sl = prove
    (`!conf. small_shift_length conf <= shift_length conf /\
             2 <= shift_length conf`,
     REWRITE_TAC[cake_def "small_shift_length";
                 cake_def "shift_length"] THEN ARITH_TAC) in
   let pb1 = prove
    (`!conf. ((ptr_bits conf 0 2) && (n2w 1):(N)word) = n2w 0`,
     GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
     X_GEN_TAC `j:num` THEN DISCH_TAC THEN
     REWRITE_TAC[BIT_WORD_AND; BIT_WORD_0; BIT_WORD_1] THEN
     REWRITE_TAC[TAUT `(p <=> F) <=> ~p`] THEN STRIP_TAC THEN
     FIRST_ASSUM(MP_TAC o MATCH_MP bit_pb) THEN
     ASM_REWRITE_TAC[] THEN ARITH_TAC) in
   let aw = prove
    (`!(w:(N)word) conf.
        (w << shift_length conf) &&
        (ptr_bits conf 0 2 || n2w 1) = n2w 0`,
     REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
     X_GEN_TAC `j:num` THEN DISCH_TAC THEN
     REWRITE_TAC[BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_0; BIT_WORD_1;
                 BIT_WORD_SHL] THEN
     REWRITE_TAC[TAUT `(p <=> F) <=> ~p`] THEN STRIP_TAC THEN
     TRY(FIRST_ASSUM(MP_TAC o MATCH_MP bit_pb)) THEN
     MP_TAC(SPEC_ALL sl) THEN ARITH_NO_BIT_TAC) in
   let gen = prove
    (`!(w:(N)word) conf.
        (w << shift_length conf || ptr_bits conf 0 2 || n2w 1) =
        w << shift_length conf + ptr_bits conf 0 2 + n2w 1`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[GEN_ALL(MATCH_MP WORD_ADD_OR (SPEC_ALL pb1));
                 GEN_ALL(MATCH_MP WORD_ADD_OR (SPEC_ALL aw))]) in
   MATCH_ACCEPT_TAC gen);;

let encode_header_lemma = cake_theorem "encode_header_lemma"
  (fun () ->
    `1 < data_to_word_config_len_size c /\ data_to_word_config_len_size
  c + 5 < dimindex (:'a) /\
     good_dimindex (:'a) ==>
     decode_length c (make_header c (n2w 0) 2) = ((n2w 2):'a word)
       /\
     encode_header c 0 2 = SOME (make_header c ((n2w 0):'a word)
       2)`)
  (* the four conditions of encode_header hold of the tag 0 and the
     length 2 (the length size is above one, so two is below two to
     that power), so the header is SOME of what make_header gives,
     and encode_header_IMP reads the length back off it *)
  (let gdcases =
     FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o
       REWRITE_RULE[cake_def "good_dimindex"]) in
   STRIP_TAC THEN
   SUBGOAL_THEN
     `0 < 2 EXP (dimindex (:'a) -
                 data_to_word_config_len_size c - 2) /\
      0 < dimword (:'a) DIV 16 /\
      2 < 2 EXP (dimindex (:'a) - 4) /\
      2 < 2 EXP (data_to_word_config_len_size c)`
     STRIP_ASSUME_TAC THENL
    [REPEAT CONJ_TAC THENL
      [REWRITE_TAC[LT_NZ; EXP_EQ_0; ARITH_EQ];
       REWRITE_TAC[dimword] THEN gdcases THEN
       CONV_TAC NUM_REDUCE_CONV;
       gdcases THEN CONV_TAC NUM_REDUCE_CONV;
       MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 2` THEN
       CONJ_TAC THENL
        [CONV_TAC NUM_REDUCE_CONV;
         REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
         ASM_ARITH_TAC]];
     ALL_TAC] THEN
   SUBGOAL_THEN
     `encode_header c 0 2 = SOME (make_header c ((n2w 0):'a word) 2)`
     ASSUME_TAC THENL
    [ASM_REWRITE_TAC[cake_def "encode_header"]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   FIRST_ASSUM(fun eh -> FIRST_ASSUM(fun ls -> FIRST_ASSUM(fun gd ->
     ACCEPT_TAC(CONJUNCT2(MATCH_MP (cake_thm "encode_header_IMP")
       (CONJ eh (CONJ ls gd))))))));;

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
  (* the bindings that bind_each adds are above ts, so a timestamp
     below it keeps the value that tf gives it *)
  (INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   REWRITE_TAC[cake_def "bind_each"] THEN
   REWRITE_TAC[FAPPLY_FUPDATE_THM] THEN
   COND_CASES_TAC THENL
    [SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC;
     FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
      [GEN_TAC THEN DISCH_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `t:num`) THEN
       ASM_REWRITE_TAC[] THEN ARITH_TAC;
       ASM_ARITH_TAC]]);;

let bind_each_FDOM = cake_theorem "bind_each_FDOM"
  (fun () ->
    `!n tf ts k i.
      FDOM (bind_each tf ts k i n) = FDOM tf UNION {x | ts <= x
        /\ x < ts + n}`)
  (* bind_each ts ... n binds the n timestamps from ts up *)
  (INDUCT_TAC THEN REPEAT GEN_TAC THEN
   ASM_REWRITE_TAC[cake_def "bind_each"; FDOM_FUPDATE] THEN
   REWRITE_TAC[EXTENSION; IN_UNION; IN_INSERT; IN_ELIM_THM] THEN
   GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   TRY(DISJ2_TAC THEN ASM_ARITH_TAC) THEN
   TRY(DISJ1_TAC THEN ASM_ARITH_TAC) THEN
   ASM_ARITH_TAC);;

let bind_each_eq_tf_FDOM = cake_theorem "bind_each_eq_tf_FDOM"
  (fun () ->
    `!k tf ts n i x.
       (!t. t IN FDOM tf ==> t < ts) /\ x < ts /\ x IN FDOM
         (bind_each tf ts n i k) ==> x IN FDOM tf`)
  (REWRITE_TAC[bind_each_FDOM; IN_UNION; IN_ELIM_THM] THEN
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let bind_each_eq_lt_FAPPLY = cake_theorem "bind_each_eq_lt_FAPPLY"
  (fun () ->
    `!n tf ts k i x.
      FAPPLY
      (bind_each tf ts k i n) x < k ==> FAPPLY (bind_each tf ts k
        i n) x = FAPPLY tf x`)
  (* a value below the first key that bind_each gives out is one of
     tf: the keys it gives are k, k + i, k + 2 * i, ... *)
  (INDUCT_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[cake_def "bind_each"; FAPPLY_FUPDATE_THM] THEN
   COND_CASES_TAC THEN REWRITE_TAC[LT_REFL] THEN
   DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let bind_each_eq_lt_FDOM = cake_theorem "bind_each_eq_lt_FDOM"
  (fun () ->
    `!n tf ts k i x.
      x IN FDOM (bind_each tf ts k i n) /\ FAPPLY (bind_each tf
        ts k i n) x < k ==> x IN FDOM tf`)
  (INDUCT_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[cake_def "bind_each"; FAPPLY_FUPDATE_THM;
               FDOM_FUPDATE; IN_INSERT] THENL
    [CONV_TAC TAUT;
     COND_CASES_TAC THEN REWRITE_TAC[LT_REFL] THEN
     STRIP_TAC THEN
     FIRST_X_ASSUM(fun ih -> MP_TAC(SPECL
       [`tf:(num,num)fmap`; `ts + 1`; `k + i`; `i:num`; `x:num`]
       ih)) THEN
     ANTS_TAC THENL
      [CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_ARITH_TAC;
       DISCH_THEN ACCEPT_TAC]]);;

let bind_each_eq_gt_FAPPLY = cake_theorem "bind_each_eq_gt_FAPPLY"
  (fun () ->
    `!n tf ts k i x.
      i * n + k < FAPPLY (bind_each tf ts k i n) x ==> FAPPLY
        (bind_each tf ts k i n) x = FAPPLY tf x`)
  (* and a value above the last one is one of tf as well *)
  (INDUCT_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[cake_def "bind_each"; FAPPLY_FUPDATE_THM;
               MULT_SUC] THEN
   COND_CASES_TAC THEN
   TRY(DISCH_THEN(fun th -> MP_TAC th THEN ARITH_TAC)) THEN
   DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let bind_each_eq_gt_FDOM = cake_theorem "bind_each_eq_gt_FDOM"
  (fun () ->
    `!n tf ts k i x.
      x IN FDOM (bind_each tf ts k i n) /\ i * n + k < FAPPLY
        (bind_each tf ts k i n) x ==> x IN FDOM tf`)
  (INDUCT_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[cake_def "bind_each"; FAPPLY_FUPDATE_THM;
               FDOM_FUPDATE; IN_INSERT; MULT_SUC] THENL
    [CONV_TAC TAUT;
     COND_CASES_TAC THENL
      [STRIP_TAC THEN ASM_ARITH_TAC;
       STRIP_TAC THEN
       FIRST_X_ASSUM(fun ih -> MP_TAC(SPECL
         [`tf:(num,num)fmap`; `ts + 1`; `k + i`; `i:num`; `x:num`]
         ih)) THEN
       ANTS_TAC THENL
        [CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
         ASM_ARITH_TAC;
         DISCH_THEN ACCEPT_TAC]]]);;

let bind_each_eq_ge_FDOM = cake_theorem "bind_each_eq_ge_FDOM"
  (fun () ->
    `!n tf ts k i x.
      x IN FDOM (bind_each tf ts k i n) /\
      i * n + k <= FAPPLY (bind_each tf ts k i n) x /\ ~(i = 0)
        ==> x IN FDOM tf`)
  (INDUCT_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[cake_def "bind_each"; FAPPLY_FUPDATE_THM;
               FDOM_FUPDATE; IN_INSERT; MULT_SUC] THENL
    [CONV_TAC TAUT;
     COND_CASES_TAC THENL
      [STRIP_TAC THEN ASM_ARITH_TAC;
       STRIP_TAC THEN
       FIRST_X_ASSUM(fun ih -> MP_TAC(SPECL
         [`tf:(num,num)fmap`; `ts + 1`; `k + i`; `i:num`; `x:num`]
         ih)) THEN
       ANTS_TAC THENL
        [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
         ASM_ARITH_TAC;
         DISCH_THEN ACCEPT_TAC]]]);;

let bind_each_fdom_limit = cake_theorem "bind_each_fdom_limit"
  (fun () ->
    `!k tf ts n i x.
       (!t. t IN FDOM tf ==> t < ts) /\ ts + k < x ==> ~(x IN
         FDOM (bind_each tf ts n i k))`)
  (* bind_each binds the k timestamps from ts up, so a timestamp
     above ts + k is in neither it nor tf *)
  (INDUCT_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[cake_def "bind_each"; FDOM_FUPDATE; IN_INSERT;
               DE_MORGAN_THM] THEN
   STRIP_TAC THENL
    [DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN
     ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
     CONJ_TAC THENL
      [ASM_ARITH_TAC;
       FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
        [GEN_TAC THEN DISCH_TAC THEN
         FIRST_X_ASSUM(MP_TAC o SPEC `t:num`) THEN
         ASM_REWRITE_TAC[] THEN ARITH_TAC;
         ASM_ARITH_TAC]]]);;

let bind_each_FUPDATE = cake_theorem "bind_each_FUPDATE"
  (fun () ->
    `!n i tf ts1 ts2 k1 k2.
      ts1 < ts2 /\ k1 < k2 ==> bind_each (tf |+ (ts1,k1)) ts2 k2
        i n = bind_each tf ts2 k2 i n |+ (ts1,k1)`)
  (* the binding of the timestamps of a block does not touch a
     timestamp below the ones it binds, so an update of that one
     commutes with it (ml/lib/lemmas.ml has FUPDATE_COMMUTES) *)
  (INDUCT_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[cake_def "bind_each"] THEN
   DISCH_TAC THEN
   FIRST_X_ASSUM(fun ih ->
     MP_TAC(SPECL [`i:num`; `tf:(num,num)fmap`; `ts1:num`;
                   `ts2 + 1`; `k1:num`; `k2 + i`] ih)) THEN
   ASM_REWRITE_TAC[ARITH_RULE `(ts1 < ts2 + 1) <=> ts1 <= ts2`] THEN
   ANTS_TAC THENL
    [ASM_ARITH_TAC;
     DISCH_THEN SUBST1_TAC THEN
     MATCH_MP_TAC FUPDATE_COMMUTES THEN ASM_ARITH_TAC]);;

let bind_each_MINUS = cake_theorem "bind_each_MINUS"
  (fun () ->
    `!n tf ts x k1 k2 i.
      (!t. t IN FDOM tf ==> t < ts) /\
      x IN {x | ts <= x /\ x < ts + n} /\ k2 <= k1 ==> FAPPLY
        (bind_each tf ts k1 i n) x - k2 = FAPPLY (bind_each tf ts (k1
        - k2) i n) x`)
  (* the binding of each timestamp of a block gives the one at ts
     the clock k and the ones above it k + i, k + 2i, ...: taking k2
     off every one of them is the binding that starts k2 lower *)
  (INDUCT_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[cake_def "bind_each"; IN_ELIM_THM] THEN
    STRIP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `(x:num) = ts` THENL
     [ASM_REWRITE_TAC[FAPPLY_FUPDATE_THM];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[FAPPLY_FUPDATE_THM] THEN
    SUBGOAL_THEN `(k1 - k2) + i = (k1 + i) - k2` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
    GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(fun fd -> FIRST_ASSUM(fun h ->
      MP_TAC(MATCH_MP fd h))) THEN
    ARITH_TAC);;

let data_to_word_memoryProof_isSomeDataElement_heap_lookup =
  cake_theorem "isSomeDataElement_heap_lookup[allow_rebind]"
  (fun () ->
    `!n a sp b.
      isSomeDataElement (heap_lookup n (a ++ [Unused sp] ++ b))
        ==> n < heap_length a \/ el_length (Unused sp) + heap_length a
        <= n`)
  (* the lookup falls in the first heap, or past the Unused in the
     second: the Unused itself holds no data element *)
  (let hlen_cl = prove
    (`heap_length [] = 0 /\
      (!x xs. heap_length (CONS x xs) =
              el_length x + heap_length xs)`,
     REWRITE_TAC[cake_def "heap_length"; MAP; SUM_DEF; ITLIST]) in
   let isde_rws = [cake_def "isSomeDataElement";
                   distinctness "option"; injectivity "option";
                   distinctness "heap_element"] in
   let un_none = prove
    (`!sp m. ~(isSomeDataElement
                 (heap_lookup m [Unused sp:((A,B)heap_element)]))`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC(cake_def "heap_lookup" :: cake_def "el_length" ::
                 isde_rws) THEN
     REPEAT COND_CASES_TAC THEN
     REWRITE_TAC(cake_def "heap_lookup" :: isde_rws)) in
   REPEAT GEN_TAC THEN
   REWRITE_TAC[GSYM APPEND_ASSOC; cake_thm "heap_lookup_APPEND"] THEN
   COND_CASES_TAC THEN REWRITE_TAC[] THEN
   REWRITE_TAC[hlen_cl; ADD_CLAUSES] THEN
   COND_CASES_TAC THEN REWRITE_TAC[un_none] THEN
   DISCH_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[cake_def "el_length"]) THEN
   REWRITE_TAC[cake_def "el_length"] THEN ARITH_ASM_TAC);;

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
  (* the heap that the list builds has the same elements whatever
     the address it starts at: the first block is a data element
     either way, and the lookup past it is the induction *)
  (let isde = prove
    (`!ys l d. isSomeDataElement (SOME (DataElement ys l d))`,
     REWRITE_TAC[cake_def "isSomeDataElement"] THEN MESON_TAC[]) in
   let isdeN = prove
    (`~isSomeDataElement NONE`,
     REWRITE_TAC[cake_def "isSomeDataElement";
                 distinctness "option"]) in
   LIST_INDUCT_TAC THENL
    [REWRITE_TAC[cake_def "list_to_BlockReps"]; ALL_TAC] THEN
   REPEAT GEN_TAC THEN POP_ASSUM MP_TAC THEN
   REWRITE_TAC[cake_def "list_to_BlockReps"] THEN
   (fun (asl,w as gl) ->
      let scr = hd (filter is_var (match_scruts w)) in
      STRUCT_CASES_TAC(ISPEC scr list_CASES_v) gl) THEN
   MATCH_REDUCE_TAC THEN
   REWRITE_TAC[] THEN
   DISCH_TAC THEN
   ONCE_REWRITE_TAC[cake_def "heap_lookup"] THEN
   REWRITE_TAC[cake_def "BlockRep"; cake_def "el_length"; LENGTH] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[isde] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[isdeN] THEN
   DISCH_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_EXISTS_TAC THEN
   ASM_REWRITE_TAC[]);;

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
  (* the binding gives each timestamp its own clock: the one at ts
     gets k and the ones above it more than k, which
     bind_each_eq_lt_FDOM says, so two of them with one clock are
     one timestamp *)
  (let eqlt = cake_thm "bind_each_eq_lt_FDOM" in
    let bfd = cake_thm "bind_each_FDOM" in
    let use_eqlt v =
      MP_TAC(SPECL [`n:num`; `tf:(num,num)fmap`; `ts + 1`; `k + i`;
                    `i:num`; v] eqlt) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [REWRITE_TAC[bfd; IN_UNION; IN_ELIM_THM] THEN ASM_ARITH_TAC;
          FIRST_ASSUM(fun e -> REWRITE_TAC[GSYM e]) THEN ASM_ARITH_TAC];
        ASM_REWRITE_TAC[]] in
    INDUCT_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[cake_def "bind_each"; IN_ELIM_THM] THENL
     [STRIP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[FAPPLY_FUPDATE_THM] THEN
    ASM_CASES_TAC `(x:num) = ts` THEN ASM_CASES_TAC `(y:num) = ts` THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [use_eqlt `y:num`;
      use_eqlt `x:num`;
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC
        [`tf:(num,num)fmap`; `ts + 1`; `k + i`; `i:num`] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT CONJ_TAC THEN ASM_ARITH_TAC]);;

let all_ts_list_to_v_SUBSET = cake_theorem "all_ts_list_to_v_SUBSET"
  (fun () ->
    `!xs ts (refs:(dataSem_v bvlSem_ref) spt) t.
      {x | ts <= x /\ x < ts + LENGTH xs} SUBSET all_ts refs
        [list_to_v ts t xs]`)
  (* the list that list_to_v builds is a Block of each timestamp
     from ts up, one for each element, and the timestamps of a
     Block on the stack are its own and the ones of its payload *)
  (SUBGOAL_THEN
     `!xs ts refs (tv:dataSem_v).
        {x | ts <= x /\ x < ts + LENGTH xs} SUBSET
        all_ts refs [list_to_v ts tv xs]`
     (fun th -> MATCH_ACCEPT_TAC th) THEN
   LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
    [REWRITE_TAC[SUBSET; IN_ELIM_THM; LENGTH; ADD_CLAUSES] THEN
     GEN_TAC THEN MATCH_MP_TAC(TAUT `~p ==> (p ==> q)`) THEN
     ARITH_TAC;
     REWRITE_TAC[cake_def "dataSem_list_to_v"] THEN
     ONCE_REWRITE_TAC[all_ts_cons] THEN
     REWRITE_TAC[APPEND; APPEND_NIL] THEN
     ONCE_REWRITE_TAC[all_ts_head] THEN
     FIRST_X_ASSUM(MP_TAC o SPECL
       [`(ts:num) + 1`; `refs:(dataSem_v bvlSem_ref) spt`;
        `tv:dataSem_v`]) THEN
     REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; IN_UNION;
                 LENGTH] THEN
     DISCH_TAC THEN X_GEN_TAC `u:num` THEN STRIP_TAC THEN
     ASM_CASES_TAC `(u:num) = ts` THENL
      [DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
       DISJ2_TAC THEN DISJ2_TAC THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let all_ts_SUBSET_list_to_v = cake_theorem "all_ts_SUBSET_list_to_v"
  (fun () ->
    `!refs t xs stack' ts.
       all_ts refs (t :: (xs ++ stack')) SUBSET
       all_ts refs (list_to_v ts t xs :: stack')`)
  (* and so are the timestamps of the elements and of the tail of
     the list, which are the same values in another order *)
  (let all_ts_perm = prove
    (`!refs (xs:dataSem_v list) ys.
        (!x. MEM x xs <=> MEM x ys)
        ==> all_ts refs xs = all_ts refs ys`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC[cake_def "all_ts"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     ASM_REWRITE_TAC[]) in
   SUBGOAL_THEN
     `!xs refs (tv:dataSem_v) stk ts.
        all_ts refs (CONS tv (xs ++ stk)) SUBSET
        all_ts refs (CONS (list_to_v ts tv xs) stk)`
     (fun th -> REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC th) THEN
   LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
    [REWRITE_TAC[cake_def "dataSem_list_to_v"; APPEND; SUBSET_REFL];
     REWRITE_TAC[cake_def "dataSem_list_to_v"] THEN
     ONCE_REWRITE_TAC[all_ts_cons] THEN
     REWRITE_TAC[APPEND] THEN
     SUBGOAL_THEN
       `all_ts refs (CONS (tv:dataSem_v) (CONS h (t ++ stk))) =
        all_ts refs (CONS tv (t ++ CONS h stk))`
       SUBST1_TAC THENL
      [MATCH_MP_TAC all_ts_perm THEN
       REWRITE_TAC[MEM; MEM_APPEND] THEN CONV_TAC TAUT;
       ALL_TAC] THEN
     SUBGOAL_THEN
       `all_ts refs (CONS (h:dataSem_v)
          (CONS (list_to_v ((ts:num) + 1) tv t) stk)) =
        all_ts refs (CONS (list_to_v (ts + 1) tv t) (CONS h stk))`
       SUBST1_TAC THENL
      [MATCH_MP_TAC all_ts_perm THEN REWRITE_TAC[MEM] THEN
       CONV_TAC TAUT;
       ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o SPECL
       [`refs:(dataSem_v bvlSem_ref) spt`; `tv:dataSem_v`;
        `CONS (h:dataSem_v) stk`; `(ts:num) + 1`]) THEN
     SET_TAC[]]);;

let new_all_ts_SUBSET_list_to_v =
  cake_theorem "new_all_ts_SUBSET_list_to_v"
  (fun () ->
    `!refs t xs stack' ts.
       {x | ts <= x /\ x < ts + LENGTH xs} SUBSET
       all_ts refs (list_to_v ts t xs :: stack')`)
  (* and those timestamps are timestamps of the stack that the
     list is on, whatever else that stack holds *)
  (let all_ts_perm = prove
    (`!refs (xs:dataSem_v list) ys.
        (!x. MEM x xs <=> MEM x ys)
        ==> all_ts refs xs = all_ts refs ys`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC[cake_def "all_ts"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     ASM_REWRITE_TAC[]) in
   SUBGOAL_THEN
     `!xs refs (tv:dataSem_v) stk ts.
        {x | ts <= x /\ x < ts + LENGTH xs} SUBSET
        all_ts refs (CONS (list_to_v ts tv xs) stk)`
     (fun th -> REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC th) THEN
   LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
    [REWRITE_TAC[SUBSET; IN_ELIM_THM; LENGTH; ADD_CLAUSES] THEN
     GEN_TAC THEN MATCH_MP_TAC(TAUT `~p ==> (p ==> q)`) THEN
     ARITH_TAC;
     REWRITE_TAC[cake_def "dataSem_list_to_v"] THEN
     ONCE_REWRITE_TAC[all_ts_cons] THEN
     REWRITE_TAC[APPEND] THEN
     SUBGOAL_THEN
       `all_ts refs (CONS (h:dataSem_v)
          (CONS (list_to_v ((ts:num) + 1) tv t) stk)) =
        all_ts refs (CONS (list_to_v (ts + 1) tv t) (CONS h stk))`
       SUBST1_TAC THENL
      [MATCH_MP_TAC all_ts_perm THEN REWRITE_TAC[MEM] THEN
       CONV_TAC TAUT;
       ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o SPECL
       [`refs:(dataSem_v bvlSem_ref) spt`; `tv:dataSem_v`;
        `CONS (h:dataSem_v) stk`; `(ts:num) + 1`]) THEN
     REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; LENGTH] THEN
     DISCH_TAC THEN X_GEN_TAC `u:num` THEN STRIP_TAC THEN
     ASM_CASES_TAC `(u:num) = ts` THENL
      [DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
       DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       ASM_ARITH_TAC]]);;

let FDOM_bind_each_lemma = cake_theorem "FDOM_bind_each_lemma"
  (fun () ->
    `!tf k ts h.
       FDOM tf SUBSET {n | n < ts} ==>
       FDOM (bind_each tf ts h n k) SUBSET {n | n < ts + k}`)
  (* induction on the number of bindings: each one is a timestamp
     one higher than the last, and the domain grows by that one *)
  (let aux = prove
    (`!k tf ts h i. FDOM tf SUBSET {m | m < ts}
        ==> FDOM (bind_each tf ts h i k) SUBSET {m | m < ts + k}`,
     INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
      [ASM_REWRITE_TAC[cake_def "bind_each"; ADD_CLAUSES];
       REWRITE_TAC[cake_def "bind_each"; FDOM_FUPDATE;
                   INSERT_SUBSET; IN_ELIM_THM] THEN
       CONJ_TAC THENL
        [ARITH_TAC;
         FIRST_ASSUM(fun ih ->
           MP_TAC(SPECL [`tf:(num,num)fmap`; `ts + 1`; `h + i:num`;
                         `i:num`] ih)) THEN
         REWRITE_TAC[ARITH_RULE `(ts + 1) + k = ts + SUC k`] THEN
         DISCH_THEN MATCH_MP_TAC THEN
         FIRST_ASSUM(fun sub -> MP_TAC sub) THEN
         REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
         MESON_TAC[ARITH_RULE `!a b:num. a < b ==> a < b + 1`]]]) in
   REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC(SPEC_ALL aux));;

let v_all_vs_list_to_v1 = cake_theorem "v_all_vs_list_to_v1"
  (fun () ->
    `!xs stack' ts t t1 a1 xs1.
       t1 < ts /\
       MEM (Block t1 a1 xs1) (v_all_vs (list_to_v ts t xs ::
         stack')) ==>
         MEM (Block t1 a1 xs1) (v_all_vs (t :: (xs ++ stack')))`)
  (* the list that list_to_v builds is a chain of conses, and the
     Blocks of the chain itself have the timestamps from ts on,
     which the Block of the goal is below; so a Block among the
     values of the chain is one of the values of the list or of the
     stack, which the induction follows cons by cons *)
  (
   let (vnil,vsing,vats,vcons) = v_all_vs_clauses () in
   let split = cake_thm "MEM_v_all_vs_split"
   and ext_hd = cake_thm "MEM_v_all_vs_extend_hd"
   and ext_tl = cake_thm "MEM_v_all_vs_extend_tl" in
   let mem_app = prove
    (`!(x:dataSem_v) l1 l2.
        MEM x (v_all_vs (l1 ++ l2)) <=>
        MEM x (v_all_vs l1) \/ MEM x (v_all_vs l2)`,
     REWRITE_TAC[v_all_vs_append; MEM_APPEND]) in
   LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[cake_def "dataSem_list_to_v"; APPEND] THENL
    [DISCH_THEN(fun th -> ACCEPT_TAC(CONJUNCT2 th));
     STRIP_TAC THEN
     SUBGOAL_THEN `t1 < ts + 1` ASSUME_TAC THENL
      [ASM_ARITH_TAC; ALL_TAC] THEN
     FIRST_ASSUM(fun m ->
       let th = MATCH_MP split m in
       MP_TAC(REWRITE_RULE[vsing; MEM] th)) THEN
     STRIP_TAC THEN
     ASM_MESON_TAC[split; ext_hd; ext_tl; mem_app;
                   injectivity "dataSem_v"; LT_REFL]]);;

let blocks_unique_GT_ts = cake_theorem "blocks_unique_GT_ts"
  (fun () ->
    `blocks_unique ts (all_vs refs (t :: (xs ++ stack))) /\
     t' >= ts /\ ~(xs1 = []) ==> ~(Block t' a1 xs1 IN all_vs refs
       (t :: (xs ++ stack)))`)
  (* blocks_unique gives the timestamp of a Block of the set as one
     below ts, and this one is not *)
  (REWRITE_TAC[cake_def "blocks_unique"] THEN REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[ARITH_RULE `!a b:num. a >= b /\ a < b ==> F`]);;

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
  (* a list of at least one element is a Block of the cons tag with
     two elements, and the invariant of a Block that is not empty
     is a pointer at a BlockRep of as many elements *)
  (STRIP_TAC THEN
   CASES_ON_NAME "vs" THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
     ALL_TAC] THEN
   FIRST_ASSUM(fun th ->
     MP_TAC(SPEC_ALL(MATCH_MP v_to_list_SOME_CONS_IMP th))) THEN
   DISCH_THEN(X_CHOOSE_THEN `ts2:num`
     (X_CHOOSE_THEN `ys2:dataSem_v` STRIP_ASSUME_TAC)) THEN
   REPEAT SUBST_LHS_TAC THEN
   USE_CHANGED [cake_thm "v_inv_def"] THEN
   REWRITE_TAC[NOT_CONS_NIL] THEN STRIP_TAC THEN
   FIRST_ASSUM(fun a2 ->
     let len = CONV_RULE NUM_REDUCE_CONV
       (REWRITE_RULE[LENGTH] (MATCH_MP LIST_REL_LENGTH a2)) in
     RULE_ASSUM_TAC(REWRITE_RULE[SYM len])) THEN
   FIRST_ASSUM(fun eq -> FIRST_ASSUM(fun hl ->
     MAP_EVERY EXISTS_TAC
       [rand(rator(rhs(concl eq))); rand(rand(rhs(concl hl)))] THEN
     ASM_REWRITE_TAC[])));;

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
  (REWRITE_TAC[cake_def "BlockRep"; heap_length_CONS; heap_length_NIL;
               cake_def "el_length"; LENGTH] THEN ARITH_TAC);;

let ALL_DISTINCT_FILTER_LENGTH =
  cake_theorem "ALL_DISTINCT_FILTER_LENGTH"
  (fun () ->
    `ALL_DISTINCT xs ==>
     LENGTH (FILTER ((~) o P) xs) + LENGTH (FILTER P xs) = LENGTH
       xs`)
  (* the two filters take each element once, whether the list has
     repetitions or not *)
  (let lem = prove
    (`!xs:A list. LENGTH (FILTER ((~) o P) xs) + LENGTH (FILTER P xs)
                  = LENGTH xs`,
     LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; LENGTH; o_THM] THEN
     ASM_CASES_TAC `(P:A->bool) h` THEN ASM_REWRITE_TAC[LENGTH] THEN
     ASM_ARITH_TAC) in
   DISCH_TAC THEN MATCH_ACCEPT_TAC lem);;

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
  (* induction on the number: a drop of none is the value itself,
     and one more goes down the tail of the cons that the list of
     the value is, which v_to_list_SOME_CONS_IMP names *)
  (let suc1 = ARITH_RULE `SUC n - 1 = n` in
   INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
    [REWRITE_TAC[cake_def "block_drop"] THEN MATCH_REDUCE_TAC THEN
     ASM_REWRITE_TAC[THE; DROP_0];
     CASES_ON_NAME "vs" THENL
      [FIRST_ASSUM(fun th -> CONTR_TAC(REWRITE_RULE[LENGTH; LT] th));
       ALL_TAC] THEN
     FIRST_ASSUM(fun th ->
       MP_TAC(SPEC_ALL(MATCH_MP v_to_list_SOME_CONS_IMP th))) THEN
     DISCH_THEN(X_CHOOSE_THEN `ts':num`
       (X_CHOOSE_THEN `ys:dataSem_v` STRIP_ASSUME_TAC)) THEN
     REPEAT SUBST_LHS_TAC THEN
     ONCE_REWRITE_TAC[cake_def "block_drop"] THEN
     MATCH_REDUCE_TAC THEN
     REWRITE_TAC[DROP; NOT_SUC; suc1] THEN
     FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN ARITH_ASM_TAC]);;

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
  (* the walk of the heap from the pointer of the value gives one
     pointer per element of the list, they are distinct, and each
     holds a BlockRep of two: three words of the heap each.  The
     list of pointers is the walk itself, which the first premise
     of walk_LENGTH names, so the theorem is matched against the
     invariant and the walk is read off that instance *)
  (let wl = cake_thm "walk_LENGTH"
   and wad = cake_thm "walk_ALL_DISTINCT"
   and whl = cake_thm "walk_heap_lookup"
   and hlb = cake_thm "heap_length_Blocks" in
   STRIP_TAC THEN
   FIRST_ASSUM(fun vi -> FIRST_ASSUM(fun vl -> FIRST_ASSUM(fun ne ->
     MP_TAC(MATCH_MP (cake_thm "v_inv_v_to_list_lemma")
              (CONJ vi (CONJ vl ne)))))) THEN
   STRIP_TAC THEN REPEAT SUBST_LHS_TAC THEN
   FIRST_ASSUM(fun vi -> FIRST_ASSUM(fun vl -> FIRST_ASSUM(fun ne ->
     let w1 = PART_MATCH (hd o conjuncts o lhand) wl (concl vi) in
     let wt = lhs (last (conjuncts (lhand (concl w1)))) in
     let prem = CONJ vi (CONJ vl (CONJ ne (REFL wt))) in
     let len = SPEC_ALL(MATCH_MP wl prem)
     and ad = SPEC_ALL(MATCH_MP wad prem)
     and ev = SPEC_ALL(MATCH_MP whl prem) in
     MP_TAC(REWRITE_RULE[len] (MATCH_MP hlb (CONJ ad ev)))))) THEN
   REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)

let memory_rel_list_limit = cake_theorem "memory_rel_list_limit"
  (fun () ->
    `memory_rel c be ts refs sp0 st m dm ((v,(w:'a word_loc)) :: vars)
  /\
     v_to_list v = SOME xs /\
     good_dimindex (:'a) ==>
     3 * (LENGTH xs + 1) * (dimindex (:'a) DIV 8) < dimword (:'a)`)
  (* the heap holds three words per element of the list, and the
     heap in memory leaves room for the limit and three more *)
  (let mul_le = prove
    (`!a b d x. 3 * a <= b /\ (b + 3) * d + 1 < x
                ==> 3 * (a + 1) * d < x`,
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `(b + 3) * d` THEN
     CONJ_TAC THENL
      [REWRITE_TAC[MULT_ASSOC;
                   ARITH_RULE `3 * (a + 1) = 3 * a + 3`;
                   LE_MULT_RCANCEL] THEN
       DISJ1_TAC THEN ASM_ARITH_TAC;
       ASM_ARITH_TAC]) in
   MEMORY_REL_TAC THEN USE_CHANGED [cake_def "heap_ok"] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `3 * LENGTH (xs:(dataSem_v)list) <= limit'`
     MP_TAC THENL
    [ASM_CASES_TAC `xs:(dataSem_v)list = []` THENL
      [ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC;
       FIRST_ASSUM(fun vi -> FIRST_ASSUM(fun vl ->
         FIRST_ASSUM(fun ne ->
           MP_TAC(MATCH_MP (cake_thm "v_to_list_heap_length")
                    (CONJ vi (CONJ vl ne)))))) THEN
       ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   DISCH_TAC THEN
   FIRST_ASSUM(fun le -> FIRST_ASSUM(fun dw ->
     MATCH_ACCEPT_TAC(MATCH_MP mul_le (CONJ le dw)))));;

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
  (* every clause of do_part gives the timestamp back as a SOME,
     and the one of a Str gives it under a let *)
  (CASES_ON_NAME "h" THEN
   REWRITE_TAC[cake_def "dataSem_do_part"] THEN
   REPEAT(CHANGED_TAC
     (REWRITE_TAC[PAIR_EQ] THEN
      CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
      REPEAT COND_CASES_TAC THEN REPEAT STRIP_TAC)) THEN
   RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
   REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
   ASM_MESON_TAC[]);;

let memory_rel_IMP_MAP_UPDATE = cake_theorem "memory_rel_IMP_MAP_UPDATE"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
             (((b,w) :: MAP (\k. (map0 k,map0' k)) ks) ++ vars) ==>
     memory_rel c be ts refs sp st m dm
             (MAP (\k. ((i =+ b) map0 k,((i =+ w) map0' k))) ks
               ++ vars)`)
  (MATCH_MP_TAC memory_rel_rearrange THEN
   GEN_TAC THEN REWRITE_TAC[MEM_APPEND; MEM_MAP; MEM] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[UPDATE] THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[]);;

let data_to_word_memoryProof_ZIP_MAP_MAP =
  cake_theorem "ZIP_MAP_MAP[local]"
  (fun () ->
    `!xs. ZIP (MAP f xs) (MAP g xs) = MAP (\k. (f k,g k)) xs`)
  (let aux = prove
    (`!(f:A->B) (g:A->C) xs.
        ZIP (MAP f xs) (MAP g xs) = MAP (\k. (f k,g k)) xs`,
     GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC[MAP; ZIP]) in
   REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC aux);;

let LENGTH_n2mw_LE_num_size =
  cake_theorem "LENGTH_n2mw_LE_num_size[local]"
  (fun () ->
    `!n m. good_dimindex (:'a) /\ n <= m ==> SUC (LENGTH (n2mw n:('a
  word) list)) <= num_size m`)
  CHEAT_TAC;;

let least_notin_domain = cake_theorem "least_notin_domain"
  (fun () ->
    `~((LEAST (\ptr. ~(ptr IN domain refs))) IN domain (refs:'a spt))`)
  (* the domain of a tree is finite, so some number is not in it,
     and the least number that is not in it is one of those *)
  (let fin = prove
    (`!t:A spt. FINITE (domain t)`,
     MATCH_MP_TAC spt_INDUCT THEN
     SIMP_TAC[cake_def "domain"; FINITE_EMPTY; FINITE_INSERT;
              FINITE_UNION; FINITE_IMAGE]) in
   let notin = prove
    (`!s:num->bool. FINITE s ==> ?n. ~(n IN s)`,
     GEN_TAC THEN REWRITE_TAC[num_FINITE] THEN
     DISCH_THEN(X_CHOOSE_TAC `a:num`) THEN
     EXISTS_TAC `a + 1` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `a + 1`) THEN
     ASM_REWRITE_TAC[] THEN ARITH_TAC) in
   let least_lemma = prove
    (`!s:num->bool. FINITE s ==> ~((LEAST (\n. ~(n IN s))) IN s)`,
     GEN_TAC THEN DISCH_TAC THEN
     MP_TAC(ISPEC `\n:num. ~(n IN s)` MINIMAL) THEN
     REWRITE_TAC[LEAST] THEN
     ASM_SIMP_TAC[notin] THEN
     DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th])) in
   MATCH_ACCEPT_TAC (MATCH_MP least_lemma (SPEC_ALL fin)));;

cake_hide_more ["free"];;

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
  (REWRITE_TAC[word_index] THEN DISCH_TAC THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_0; BIT_WORD_AND;
               BIT_WORD_SHL] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[]);;

let byte_aligned_IMP_shift = cake_theorem "byte_aligned_IMP_shift"
  (fun () ->
    `byte_aligned (w:'a word) /\ good_dimindex (:'a) ==>
     (?v. w = v << backend_common_word_shift (:'a))`)
  (* a byte aligned word is its own slice above the shift of the
     dimindex, and such a slice is the word shifted down and up
     again *)
  (let LOG2_RED =
     REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV(REWR_CONV LOG2) THENC
                          NUM_REDUCE_CONV THENC REWRITE_CONV[])) in
   let key = prove
    (`!p (w:(N)word). word_slice (dimindex (:N) - 1) p w = w
        ==> w = word_shl (word_ushr w p) p`,
     REPEAT GEN_TAC THEN
     DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
     REWRITE_TAC[word_slice; word_bits; WORD_EQ_BITS_ALT;
                 BIT_WORD_SHL; BIT_WORD_SUBWORD; BIT_WORD_USHR] THEN
     X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     ASM_CASES_TAC `p:num <= i` THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN
       `i - p < MIN ((dimindex (:N) - 1 + 1) - p) (dimindex (:N))`
       (fun th -> REWRITE_TAC[th]) THENL
      [REWRITE_TAC[ARITH_RULE
         `MIN a b = if a <= b then a else b`] THEN
       COND_CASES_TAC THEN ASM_ARITH_TAC;
       REWRITE_TAC[ARITH_RULE `p + (i - p) = (i - p) + p`]]) in
   REWRITE_TAC[cake_def "byte_aligned"; cake_def "alignment_aligned";
               cake_def "align"] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `LOG2 (dimindex (:'a) DIV 8) =
                 backend_common_word_shift (:'a)`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [FIRST_ASSUM(fun g -> MP_TAC g) THEN
     REWRITE_TAC[cake_def "good_dimindex";
                 cake_def "backend_common_word_shift"] THEN
     DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
     CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC LOG2_RED;
     EXISTS_TAC
       `word_ushr (w:'a word) (backend_common_word_shift (:'a))` THEN
     MATCH_MP_TAC key THEN FIRST_ASSUM ACCEPT_TAC]);;

let make_cons_ptr_add = cake_theorem "make_cons_ptr_add"
  (fun () ->
    `byte_aligned n /\ good_dimindex (:'a) /\ backend_common_word_shift
  (:'a) <= shift_length c ==>
     make_cons_ptr c n tag len =
     wordLang_Word (n << (shift_length c -
       backend_common_word_shift (:'a)) +
           (get_lowerbits c (wordLang_Word (ptr_bits c tag
             len)):'a word))`)
  (* and the same for the pointer of a cons, where the one that
     the lower bits already hold is absorbed first *)
  (let lb1 = prove
     (`!c (x:(N)word).
         word 1 || get_lowerbits c (wordLang_Word x) =
         get_lowerbits c (wordLang_Word x)`,
      REPEAT GEN_TAC THEN REWRITE_TAC[cake_def "get_lowerbits"] THEN
      MATCH_REDUCE_TAC THEN CONV_TAC WORD_BITWISE_RULE) in
    STRIP_TAC THEN
    REWRITE_TAC[cake_def "make_cons_ptr"] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[lb1] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORD_ADD_OR THEN
    FIRST_ASSUM(fun ba -> FIRST_ASSUM(fun gd ->
      MP_TAC(MATCH_MP (cake_thm "byte_aligned_IMP_shift")
        (CONJ ba gd)))) THEN
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
    REWRITE_TAC[cake_def "get_lowerbits"] THEN
    MATCH_REDUCE_TAC THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_OR;
                BIT_WORD_1; BIT_WORD_0; BIT_WORD_SHL; word_bits;
                BIT_WORD_SUBWORD;
                ARITH_RULE `MIN a b = if a <= b then a else b`] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[cake_def "shift_length";
                cake_def "small_shift_length"] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THEN
    POP_ASSUM_LIST(fun ths -> MAP_EVERY MP_TAC ths) THEN
    REWRITE_TAC[cake_def "shift_length";
                cake_def "small_shift_length"] THEN
    ARITH_TAC);;

let make_ptr_add = cake_theorem "make_ptr_add"
  (fun () ->
    `byte_aligned n /\ good_dimindex (:'a) /\ backend_common_word_shift
  (:'a) <= shift_length c ==>
     make_ptr c n tag len =
     wordLang_Word (n << (shift_length c -
       backend_common_word_shift (:'a)) + ((n2w 1):'a word))`)
  (* a byte aligned word is a word shifted up by the shift, so the
     pointer it makes has its lowest bit clear and the or with one
     is an add *)
  (STRIP_TAC THEN
    REWRITE_TAC[cake_def "make_ptr"] THEN
    AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORD_ADD_OR THEN
    FIRST_ASSUM(fun ba -> FIRST_ASSUM(fun gd ->
      MP_TAC(MATCH_MP (cake_thm "byte_aligned_IMP_shift")
        (CONJ ba gd)))) THEN
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_1;
                BIT_WORD_0; BIT_WORD_SHL] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(i:num) = 0` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun gd ->
      if can (find_term (fun t ->
        try fst(dest_const t) = "good_dimindex"
        with Failure _ -> false))
        (concl gd)
      then MP_TAC gd else failwith "no") THEN
    REWRITE_TAC[cake_def "good_dimindex";
                cake_def "backend_common_word_shift"] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    POP_ASSUM_LIST(fun ths -> MAP_EVERY MP_TAC ths) THEN ARITH_TAC);;

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
  (* the alignment of a word is the slice that drops its lowest
     bits, and the bytes in a word of a good dimindex are four or
     eight, which have no bit as low as that *)
  (let LOG2_RED =
     REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV(REWR_CONV LOG2) THENC
                          NUM_REDUCE_CONV THENC REWRITE_CONV[])) in
   let slice_lemma = prove
    (`!h p (w:(N)word).
        dimindex (:N) <= h + 1 /\ (!i. i < p ==> ~word_bit i w)
        ==> word_slice h p w = w`,
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     REWRITE_TAC[word_slice; word_bits; WORD_EQ_BITS_ALT;
                 BIT_WORD_SHL; BIT_WORD_SUBWORD] THEN
     X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     ASM_CASES_TAC `p:num <= i` THENL
      [SUBGOAL_THEN `(p + (i - p) = i) /\
                     i - p < MIN ((h + 1) - p) (dimindex (:N))`
         STRIP_ASSUME_TAC THENL
        [CONJ_TAC THENL
          [ASM_ARITH_TAC;
           REWRITE_TAC[ARITH_RULE
             `MIN a b = if a <= b then a else b`] THEN
           COND_CASES_TAC THEN ASM_ARITH_TAC];
         ASM_REWRITE_TAC[]];
       ASM_REWRITE_TAC[] THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
       ASM_SIMP_TAC[ARITH_RULE `~(p <= i) ==> (i:num) < p`]]) in
   REWRITE_TAC[cake_def "good_dimindex"; cake_def "byte_aligned";
               cake_def "alignment_aligned"; cake_def "align";
               cake_def "bytes_in_word"] THEN
   DISCH_THEN(DISJ_CASES_THEN
     (fun th -> SUBST1_TAC th THEN ASSUME_TAC th)) THEN
   CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC LOG2_RED THEN
   MATCH_MP_TAC slice_lemma THEN
   (CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN ARITH_TAC;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `i = 0 \/ i = 1 \/ i = 2` MP_TAC THENL
       [ASM_ARITH_TAC;
        DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
        REWRITE_TAC[BIT_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
        TRY(REWRITE_TAC[]) THEN TRY(ASM_ARITH_TAC)]]));;

let byte_align_mult_bytes_in_word =
  cake_theorem "byte_align_mult_bytes_in_word"
  (fun () ->
    `good_dimindex (:'a) ==>
     byte_aligned (w * (bytes_in_word:'a word)) /\
     byte_aligned (bytes_in_word * (w:'a word))`)
  (* the bytes in a word are two to the shift, so a multiple of them
     is the word shifted up, and the alignment of a word shifted up
     is the word shifted down and up again, which is the word
     itself *)
  (
   let LOG2_RED =
     REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV(REWR_CONV LOG2) THENC
                          NUM_REDUCE_CONV THENC REWRITE_CONV[])) in
   let slice_shl = prove
    (`!p (w:(N)word).
        word_slice (dimindex (:N) - 1) p w = word_shl (word_ushr w p) p`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[word_slice; word_bits; WORD_EQ_BITS_ALT;
                 BIT_WORD_SHL; BIT_WORD_SUBWORD; BIT_WORD_USHR] THEN
     X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     ASM_CASES_TAC `p:num <= i` THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN
       `i - p < MIN ((dimindex (:N) - 1 + 1) - p) (dimindex (:N))`
       (fun th -> REWRITE_TAC[th]) THENL
      [REWRITE_TAC[ARITH_RULE `MIN a b = if a <= b then a else b`] THEN
       COND_CASES_TAC THEN ASM_ARITH_TAC;
       REWRITE_TAC[ARITH_RULE `p + (i - p) = (i - p) + p`]]) in
   let shl_slice = prove
    (`!p (w:(N)word).
        word_slice (dimindex (:N) - 1) p (word_shl w p) =
        word_shl w p`,
     REPEAT GEN_TAC THEN REWRITE_TAC[slice_shl] THEN
     REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SHL; BIT_WORD_USHR] THEN
     X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     ASM_CASES_TAC `p:num <= i` THEN
     ASM_SIMP_TAC[ARITH_RULE `p <= i ==> (i - p) + p = i`] THEN
     ASM_REWRITE_TAC[BIT_WORD_SHL]) in
   let mul_shl = prove
    (`!p d (w:(N)word). d = 2 EXP p ==> w * n2w d = word_shl w p`,
     REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC[word_shl] THEN
     GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM WORD_VAL] THEN
     REWRITE_TAC[GSYM WORD_MUL]) in
   DISCH_TAC THEN
   SUBGOAL_THEN
     `dimindex (:'a) DIV 8 = 2 EXP (LOG2 (dimindex (:'a) DIV 8))`
     ASSUME_TAC THENL
    [FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o
       REWRITE_RULE[cake_def "good_dimindex"]) THEN
     CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC LOG2_RED THEN
     CONV_TAC NUM_REDUCE_CONV;
     ALL_TAC] THEN
   REWRITE_TAC[cake_def "byte_aligned";
               cake_def "alignment_aligned"; cake_def "align";
               cake_def "bytes_in_word"] THEN
   CONJ_TAC THENL
    [ALL_TAC;
     SUBST1_TAC(WORD_RULE
       `n2w (dimindex (:'a) DIV 8) * (w:'a word) =
        w * n2w (dimindex (:'a) DIV 8)`)] THEN
   FIRST_ASSUM(fun f1 -> REWRITE_TAC[MATCH_MP mul_shl f1]) THEN
   MATCH_ACCEPT_TAC shl_slice);;

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
  (* the same as LENGTH_n2mw_LE_num_size, with the good_dimindex
     pulled out in front, as the source states it twice *)
  (DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
   FIRST_ASSUM(fun le -> FIRST_ASSUM(fun gd ->
     MATCH_ACCEPT_TAC(MATCH_MP (cake_thm "LENGTH_n2mw_LE_num_size")
                        (CONJ gd le)))));;

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
  (let bsa = prove
    (`!h l (w:(N)word) j. j < dimindex (:N)
        ==> (bit j (word_slice_alt h l w) <=>
             l <= j /\ j < h /\ bit j w)`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC[word_slice_alt; BIT_WORD_SHL; BIT_WORD_SUBWORD] THEN
     REWRITE_TAC[ARITH_RULE `MIN a b = if a <= b then a else b`] THEN
     ASM_CASES_TAC `l:num <= j` THEN ASM_REWRITE_TAC[] THEN
     ASM_SIMP_TAC[ARITH_RULE `l <= j ==> l + j - l = j`] THEN
     COND_CASES_TAC THEN
     ASM_CASES_TAC `bit j (w:(N)word)` THEN ASM_REWRITE_TAC[] THEN
     ARITH_NO_BIT_TAC) in
   let bsb0 = prove
    (`!(a:(N)word) b (h:(N)word) bb j. j < dimindex (:N)
        ==> (bit j (set_byte a b h bb) <=>
             (if byte_index a bb <= j /\ j < byte_index a bb + 8
              then bit (j - byte_index a bb) b else bit j h))`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC[cake_def "set_byte"] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     ASM_SIMP_TAC[BIT_WORD_OR; bsa; BIT_WORD_SHL; BIT_WORD_ZX;
                  DIMINDEX_8] THEN
     MP_TAC(REWRITE_RULE[DIMINDEX_8]
       (ISPECL [`b:(8)word`; `j - byte_index (a:(N)word) bb`]
          BIT_TRIVIAL)) THEN
     ASM_CASES_TAC `byte_index (a:(N)word) bb <= j` THEN
     ASM_CASES_TAC `j < byte_index (a:(N)word) bb + 8` THEN
     ASM_CASES_TAC `bit j (h:(N)word)` THEN
     ASM_CASES_TAC
       `bit (j - byte_index (a:(N)word) bb) (b:(8)word)` THEN
     ASM_REWRITE_TAC[] THEN ARITH_NO_BIT_TAC) in
   let gen = prove
    (`!(a:(N)word) h1 h2 w1 w2 bb.
        word_xor (set_byte a h1 w1 bb) (set_byte a h2 w2 bb) =
        set_byte a (word_xor h1 h2) (word_xor w1 w2) bb`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
     X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     ASM_SIMP_TAC[BIT_WORD_XOR; bsb0] THEN
     COND_CASES_TAC THEN
     TRY(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
     ASM_SIMP_TAC[BIT_WORD_XOR; DIMINDEX_8;
                  ARITH_RULE `b <= i /\ i < b + 8 ==> i - b < 8`]) in
   MATCH_ACCEPT_TAC gen);;

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
  (* the xor of two lists of bytes is as long as the second and at
     least as long as the first, by the induction of the
     definition; the case of the xor of the tails is what
     EVERY_CASE_TAC splits *)
  (let xb = cake_def "xor_bytes" in
   LIST_INDUCT_TAC THENL
    [REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [xb] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[injectivity "option"] THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LENGTH; LE_0];
     (fun (asl,w as gl) ->
        let ysv = fst(dest_forall w) in
        (X_GEN_TAC ysv THEN
         STRUCT_CASES_TAC(ISPEC ysv list_CASES_v)) gl) THEN
     GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [xb] THEN
     EVERY_CASE_TAC THEN
     REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
     TRY(DISCH_THEN(SUBST1_TAC o SYM)) THEN
     REWRITE_TAC[LENGTH; LE_SUC; SUC_INJ] THEN
     FIRST_ASSUM(fun st -> FIRST_ASSUM(fun ih ->
       ACCEPT_TAC(MATCH_MP ih st)))]);;

let xor_bytes_drop = cake_theorem "xor_bytes_drop[local]"
  (fun () ->
    `!n xs ys zs.
       xor_bytes xs ys = SOME zs ==>
       xor_bytes (DROP n xs) (DROP n ys) = SOME (DROP n zs)`)
  (* dropping from both lists drops from the xor as well, by the
     induction of the definition *)
  (let xb = cake_def "xor_bytes" in
   SUBGOAL_THEN
     `!xs n ys zs. xor_bytes xs ys = SOME zs
        ==> xor_bytes (DROP n xs) (DROP n ys) = SOME (DROP n zs)`
     (fun th -> REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC th) THEN
   LIST_INDUCT_TAC THENL
    [REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [xb] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[injectivity "option"] THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN
     REWRITE_TAC[DROP] THEN
     GEN_REWRITE_TAC LAND_CONV [xb] THEN
     MATCH_REDUCE_TAC THEN REWRITE_TAC[];
     GEN_TAC THEN
     (fun (asl,w as gl) ->
        let ysv = fst(dest_forall w) in
        (X_GEN_TAC ysv THEN
         STRUCT_CASES_TAC(ISPEC ysv list_CASES_v)) gl) THEN
     GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [xb] THEN
     EVERY_CASE_TAC THEN
     REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
     TRY(DISCH_THEN(SUBST1_TAC o SYM)) THEN
     REWRITE_TAC[DROP] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
      [GEN_REWRITE_TAC LAND_CONV [xb] THEN
       ASM_REWRITE_TAC[] THEN MATCH_REDUCE_TAC THEN REWRITE_TAC[];
       FIRST_ASSUM(fun st -> FIRST_ASSUM(fun ih ->
         MATCH_ACCEPT_TAC(MATCH_MP ih st)))]]);;

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
  (* the zeroes of make_zeros are as many as the lemma above asks
     for, and they are all zero *)
  (let all_zero = prove
    (`!n. ALL (\w. w = ((n2w 0):(N)word)) (REPLICATE n (n2w 0))`,
     INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; ALL]) in
   STRIP_TAC THEN MATCH_MP_TAC xor_bytes_xor_words THEN
   ASM_REWRITE_TAC[cake_def "make_zeros"; all_zero;
                   LENGTH_REPLICATE]);;

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
  (* the words of the two byte lists are as many as the zeroes, so
     xor_words_word_list is about them, and the xor of the two is
     the one of the result by xor_bytes_xor_words *)
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   ONCE_REWRITE_TAC[GSYM (ISPECL
     [`make_zeros vals1:('a word)list`; `vals1:(word8)list`;
      `be':bool`] LENGTH_write_bytes)] THEN
   MATCH_MP_TAC (cake_thm "xor_words_word_list") THEN
   EXISTS_TAC `write_bytes vals2 (make_zeros vals2:('a word)list)
                 be'` THEN
   ASM_REWRITE_TAC[LENGTH_write_bytes] THEN
   MATCH_MP_TAC (cake_thm "xor_bytes_xor_words") THEN
   ASM_REWRITE_TAC[]);;

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
  (* and the same where the two lists are one *)
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   ONCE_REWRITE_TAC[GSYM (ISPECL
     [`make_zeros vals1:('a word)list`; `vals1:(word8)list`;
      `be':bool`] LENGTH_write_bytes)] THEN
   MATCH_MP_TAC (cake_thm "xor_words_word_list_alias") THEN
   ASM_REWRITE_TAC[LENGTH_write_bytes] THEN
   MATCH_MP_TAC (cake_thm "xor_bytes_xor_words") THEN
   ASM_REWRITE_TAC[]);;

(* HOL4 data_to_word_memoryProofScript.sml:18637-18644: code that the
   source has in a comment *)

let el_length_Bytes = cake_theorem "el_length_Bytes"
  (fun () ->
    `el_length (Bytes be fl vals zeros) = LENGTH zeros + 1`)
  (REWRITE_TAC[cake_def "Bytes"] THEN
   CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[cake_def "el_length"; LENGTH_write_bytes]);;

let blocks_unique_insert_ByteArray2 =
  cake_theorem "blocks_unique_insert_ByteArray2"
  (fun () ->
    `blocks_unique ts
       (all_vs refs (RefPtr bl1 p1 :: RefPtr bl2 p2 :: MAP FST
         vars)) ==>
       blocks_unique ts
         (all_vs (insert p2 (ByteArray fl2 res_vals) refs)
            (RefPtr bl1 p1 :: RefPtr bl2 p2 :: MAP FST vars))`)
  (* a ByteArray holds no value of the language, so the insert adds
     no Block *)
  (let li = prove
    (`!k1 k2 v (t:(A)spt) y.
        (sptree_lookup k1 (sptree_insert k2 v t) = SOME y) <=>
        (k1 = k2 /\ v = y) \/
        (~(k1 = k2) /\ sptree_lookup k1 t = SOME y)`,
     REPEAT GEN_TAC THEN REWRITE_TAC[lookup_insert] THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC[injectivity "option"] THEN CONV_TAC TAUT) in
   let inc = prove
    (`!refs p2 fl2 res_vals s t a q.
        Block t a q IN
          all_vs (insert p2 (ByteArray fl2 res_vals) refs) s ==>
        Block t a q IN all_vs refs s`,
     REWRITE_TAC[cake_def "all_vs"; IN_UNION; IN_ELIM_THM; li;
                 distinctness "bvlSem_ref";
                 injectivity "bvlSem_ref"] THEN MESON_TAC[]) in
   REWRITE_TAC[cake_def "blocks_unique"] THEN DISCH_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THEN ASM_MESON_TAC[inc]);;

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
  (* the same character in front of both strings and the index one
     further on compare the same characters: the induction is on the
     length that is left to compare, and the premise about the two
     lengths is not needed *)
  (let shift_lemma = prove
    (`!len start r (zz:char) l1 l2.
        compare_aux (implode (CONS zz l1)) (implode (CONS zz l2)) r
          (start + 1) len =
        compare_aux (implode l1) (implode l2) r start len`,
     let el_suc = prove
      (`!n h (t:A list). EL (n + 1) (CONS h t) = EL n t`,
       REWRITE_TAC[GSYM ADD1; EL; TL]) in
     INDUCT_TAC THEN REPEAT GEN_TAC THEN
     ONCE_REWRITE_TAC[cake_def "compare_aux"] THEN
     REWRITE_TAC[NOT_SUC; SUC_SUB1; cake_def "strsub"; el_suc] THEN
     ASM_REWRITE_TAC[]) in
   REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_ACCEPT_TAC shift_lemma);;

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
  (* and the same of the shorter second string *)
  (let shift_lemma = prove
    (`!len start r (zz:char) l1 l2.
        compare_aux (implode (CONS zz l1)) (implode (CONS zz l2)) r
          (start + 1) len =
        compare_aux (implode l1) (implode l2) r start len`,
     let el_suc = prove
      (`!n h (t:A list). EL (n + 1) (CONS h t) = EL n t`,
       REWRITE_TAC[GSYM ADD1; EL; TL]) in
     INDUCT_TAC THEN REPEAT GEN_TAC THEN
     ONCE_REWRITE_TAC[cake_def "compare_aux"] THEN
     REWRITE_TAC[NOT_SUC; SUC_SUB1; cake_def "strsub"; el_suc] THEN
     ASM_REWRITE_TAC[]) in
   REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_ACCEPT_TAC shift_lemma);;

let compare_same = cake_theorem "compare_same"
  (fun () ->
    `compare (implode (x :: xs)) (implode (x :: ys)) =
     compare (implode xs) (implode ys)`)
  (* the first characters are the same, so the comparison steps over
     them: the index goes up by one, which the shift of
     compoare_aux_append_xs takes off again, and the lengths are one
     less on both sides *)
  (let shift_lemma = prove
    (`!len start r (zz:char) l1 l2.
        compare_aux (implode (CONS zz l1)) (implode (CONS zz l2)) r
          (start + 1) len =
        compare_aux (implode l1) (implode l2) r start len`,
     let el_suc = prove
      (`!n h (t:A list). EL (n + 1) (CONS h t) = EL n t`,
       REWRITE_TAC[GSYM ADD1; EL; TL]) in
     INDUCT_TAC THEN REPEAT GEN_TAC THEN
     ONCE_REWRITE_TAC[cake_def "compare_aux"] THEN
     REWRITE_TAC[NOT_SUC; SUC_SUB1; cake_def "strsub"; el_suc] THEN
     ASM_REWRITE_TAC[]) in
   let first_eq = prove
    (`!r (zz:char) l1 l2 n.
        compare_aux (implode (CONS zz l1)) (implode (CONS zz l2)) r 0
          (SUC n) =
        compare_aux (implode l1) (implode l2) r 0 n`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC LAND_CONV [cake_def "compare_aux"] THEN
     REWRITE_TAC[NOT_SUC; SUC_SUB1; cake_def "strsub"; EL; HD;
                 char_lt; LT_REFL; shift_lemma]) in
   REWRITE_TAC[cake_def "mlstring_compare"; cake_def "strlen";
               LENGTH; LT_SUC; first_eq]);;

let str_cmp_cons = cake_theorem "str_cmp_cons"
  (fun () ->
    `str_cmp b cmp (implode (x :: xs)) (implode (x :: ys)) =
     str_cmp b cmp (implode xs) (implode ys)`)
  (* each of the eight comparisons is the one of mlstring_compare,
     which compare_same takes off the first character, or a
     comparison of the lengths, which are one less *)
  (REWRITE_TAC[cake_def "str_cmp"] THEN
   CASES_ON_NAME "b" THEN CASES_ON_NAME "cmp" THEN
   MATCH_REDUCE_TAC THEN
   REWRITE_TAC[cake_def "mlstring_lt"; cake_def "mlstring_le";
               cake_def "mlstring_gt"; cake_def "mlstring_ge";
               cake_def "fast_lt"; cake_def "fast_le";
               cake_def "fast_gt"; cake_def "fast_ge";
               cake_thm "compare_same"; cake_def "strlen";
               LENGTH; SUC_INJ; LT_SUC; LE_SUC;
               GT; GE; ARITH_RULE `SUC m >= SUC n <=> m >= n`;
               ARITH_RULE `SUC m > SUC n <=> m > n`]);;

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
  (ARITH_TAC);;

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
