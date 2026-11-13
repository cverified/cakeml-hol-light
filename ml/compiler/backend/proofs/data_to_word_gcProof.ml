(* ======================================================== *)
(*  data_to_word_gcProof: ported from HOL4's
    compiler/backend/proofs/data_to_word_gcProofScript.sml
    A proof theory, with 26 definitions and 400 theorems.  Needed by
    data_to_wordProof.ml, data_to_word_assignProof.ml,
    data_to_word_bignumProof.ml and stack_to_labProof.ml.  *)
(* ======================================================== *)

(*
  Part of the correctness proof for data_to_word
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/gc/copying_gc.ml";;
needs "compiler/backend/gc/gc_combined.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "compiler/backend/gc/gen_gc_partial.ml";;
needs "compiler/backend/proofs/data_to_word_memoryProof.ml";;
needs "compiler/backend/proofs/word_bignumProof.ml";;
needs "compiler/backend/proofs/word_gcFunctions.ml";;
needs "compiler/backend/proofs/word_simpProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/alignment.ml";;
needs "lib/byte.ml";;
needs "lib/multiword.ml";;
needs "lib/set_sep.ml";;
needs "lib/sorting.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "data_to_word_gcProof"
  ["backendProps"; "copying_gc"; "dataProps"; "dataSem";
   "data_to_word"; "data_to_word_memoryProof"; "gc_shared"; "gen_gc";
   "gen_gc_partial"; "mllist"; "semanticsProps"; "wordLang";
   "wordProps"; "wordSem"; "word_bignum"; "word_bignumProof";
   "word_gcFunctions"];;

let _ = do_list hide_constant ["stack_alloc"; "vars"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["code_buffer","code_buffer";
   "data_buffer","data_buffer"];;
(* HOL4 ancestors outside the port: int_bitwise finite_map While *)

(* HOL4 data_to_word_gcProofScript.sml:19-23: ML code, not ported *)

(* HOL4 data_to_word_gcProofScript.sml:25: the overload lookup, which
   the port expands *)

(* TODO: move *)
(* HOL4 data_to_word_gcProofScript.sml:30: the type abbreviation
   state, which the port expands *)

(* HOL4 data_to_word_gcProofScript.sml:32-33: ML code, not ported *)

(* HOL4 data_to_word_gcProofScript.sml:35-36: a proof *)

let LESS_EQ_IMP_APPEND_ALT = prove
 (`!n xs. n <= LENGTH xs ==> (?ys zs. xs = ys ++ zs /\ LENGTH zs = n)`,
  CHEAT_TAC);;

let word_asr_dimindex = prove
 (`!(w:'a word) n. dimindex (:'a) <= n ==> (w >> n = w >> (dimindex
  (:'a) - 1))`,
  CHEAT_TAC);;

let WORD_MUL_BIT0 = prove
 (`!a b. FAPPLY (a * b) 0 <=> FAPPLY a 0 /\ FAPPLY b 0`,
  CHEAT_TAC);;

let word_lsl_index = prove
 (`i < dimindex (:'a) ==>
    (FAPPLY ((w:'a word) << n) i <=> n <= i /\ FAPPLY w (i - n))`,
  CHEAT_TAC);;

let word_lsr_index = prove
 (`i < dimindex (:'a) ==>
   (FAPPLY ((w:'a word) >>> n) i <=> i + n < dimindex (:'a) /\
     FAPPLY w (i + n))`,
  CHEAT_TAC);;

let lsr_lsl = prove
 (`!w n. alignment_aligned n w ==> (w >>> n << n = w)`,
  CHEAT_TAC);;

let word_index_test = prove
 (`n < dimindex (:'a) ==> (FAPPLY w n <=> (~((w && n2w (2 EXP n)) =
  ((n2w 0):'a word))))`,
  CHEAT_TAC);;

let word_and_one_eq_0_iff = prove
 (`// same in stack_alloc
   !w. ((w && (n2w 1)) = (n2w 0)) <=> ~(FAPPLY w 0)`,
  CHEAT_TAC);;

let word_index_0 = prove
 (`!w. FAPPLY w 0 <=> ~(((n2w 1) && w) = (n2w 0))`,
  CHEAT_TAC);;

(* [simp] *)
let ABS_w2n = prove
 (`abs (&(w2n w)) = &(w2n w)`,
  CHEAT_TAC);;

let n2mw_w2n = prove
 (`!w. n2mw (w2n w) = (if w = (n2w 0) then [] else [w])`,
  CHEAT_TAC);;

(* get_var_set_var[simp] *)
let data_to_word_gcProof_get_var_set_var = prove
 (`get_var n (set_var n w s) = SOME w`,
  CHEAT_TAC);;

(* [simp] *)
let set_var_set_var = prove
 (`set_var n v (wordSem_set_var n w s) = set_var n v s`,
  CHEAT_TAC);;

(* [simp] *)
let toAList_LN = prove
 (`toAList LN = []`,
  CHEAT_TAC);;

(* [simp] *)
let adjust_set_LN = prove
 (`adjust_set LN = LN`,
  CHEAT_TAC);;

let push_env_termdep = prove
 (`wordSem_state_termdep
      (push_env y opt t) = wordSem_state_termdep t`,
  CHEAT_TAC);;

let ALOOKUP_SKIP_LEMMA = prove
 (`~(MEM n (MAP FST xs)) /\ d = e ==>
    ALOOKUP (xs ++ [(n,d)] ++ ys) n = SOME e`,
  CHEAT_TAC);;

let LAST_EQ = prove
 (`(LAST (x :: xs) = (if xs = [] then x else LAST xs)) /\
    (FRONT (x :: xs) = (if xs = [] then [] else x :: FRONT xs))`,
  CHEAT_TAC);;

let LASTN_LIST_REL_LEMMA = prove
 (`!xs1 ys1 xs n y ys x P.
      LASTN n xs1 = x :: xs /\ LIST_REL P xs1 ys1 ==>
      (?y ys. LASTN n ys1 = y :: ys /\ P x y /\ LIST_REL P xs ys)`,
  CHEAT_TAC);;

let LASTN_CONS_IMP_LENGTH = prove
 (`!xs n y ys.
      n <= LENGTH xs ==>
      (LASTN n xs = y :: ys) ==> LENGTH (y :: ys) = n`,
  CHEAT_TAC);;

let LASTN_IMP_APPEND = prove
 (`!xs n ys.
      n <= LENGTH xs /\ (LASTN n xs = ys) ==>
      (?zs. xs = zs ++ ys /\ LENGTH ys = n)`,
  CHEAT_TAC);;

let NOT_NIL_IMP_LAST = prove
 (`!xs x. ~(xs = []) ==> LAST (x :: xs) = LAST xs`,
  CHEAT_TAC);;

let IS_SOME_IF = prove
 (`IS_SOME (if b then x else y) = (if b then IS_SOME x else IS_SOME y)`,
  CHEAT_TAC);;

let IS_SOME_ALOOKUP_EQ = prove
 (`!l x. IS_SOME (ALOOKUP l x) = MEM x (MAP FST l)`,
  CHEAT_TAC);;

let MEM_IMP_IS_SOME_ALOOKUP = prove
 (`!l x y. MEM (x,y) l ==> IS_SOME (ALOOKUP l x)`,
  CHEAT_TAC);;

let SUBSET_INSERT_EQ_SUBSET = prove
 (`~(x IN s) ==> (s SUBSET (x INSERT t) <=> s SUBSET t)`,
  CHEAT_TAC);;

let EVERY2_IMP_EL = prove
 (`!xs ys P n. EVERY2 P xs ys /\ n < LENGTH ys ==> P (EL n xs) (EL n
  ys)`,
  CHEAT_TAC);;

let FST_PAIR_EQ = prove
 (`!x v. (FST x,v) = x <=> v = SND x`,
  CHEAT_TAC);;

let EVERY2_APPEND_IMP = prove
 (`!xs1 xs2 zs P.
      EVERY2 P (xs1 ++ xs2) zs ==>
      (?zs1 zs2. zs = zs1 ++ zs2 /\ EVERY2 P xs1 zs1 /\ EVERY2 P
        xs2 zs2)`,
  CHEAT_TAC);;

let ZIP_ID = prove
 (`!xs. ZIP (MAP FST xs) (MAP SND xs) = xs`,
  CHEAT_TAC);;

let FOLDL_LENGTH_LEMMA = prove
 (`!xs k l d q r.
      FOLDL (\(i,t) a. (i + d,insert i a t)) (k,l) xs = (q,r) ==>
      q = LENGTH xs * d + k`,
  CHEAT_TAC);;

let fromList_SNOC = prove
 (`!xs y. fromList (SNOC y xs) = insert (LENGTH xs) y (fromList xs)`,
  CHEAT_TAC);;

let fromList2_SNOC = prove
 (`!xs y. fromList2 (SNOC y xs) = insert (2 * LENGTH xs) y (fromList2
  xs)`,
  CHEAT_TAC);;

(* -- *)

(* -------------------------------------------------------
    word_ml_inv: definition and lemmas
   ------------------------------------------------------- *)

let join_env_def = new_definition
  `join_env env vs =
     MAP (\(n,v). (THE (sptree_lookup ((n - 2) DIV 2) env),v))
       (FILTER (\(n,v). ~(n = 0) /\ EVEN n) vs)`;;

let _ = size_thms "dataSem_stack";;
let _ = size_thms "stack_frame";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let flat_def,flat_ind = define_wf
  `MEASURE (\(x0,x1).      list_size dataSem_stack_size x0 +
  list_size (stack_frame_size (\x. 0)) x1)`
  [`flat x1 x2 =
        match (x1,x2) with
          (((Env _2 env:dataSem_stack) :: xs),(StackFrame _3 _4 vs
            _5 :: ys)) ->
        join_env env vs ++ flat xs ys
        | ((dataSem_Exc _6 env _7 :: xs),(StackFrame _8 _9 vs _10 ::
          ys)) ->
        join_env env vs ++ flat xs ys
        | (_11,_12) -> []`];;

let flat_APPEND = prove
 (`!xs ys xs1 ys1.
      LENGTH xs = LENGTH ys ==>
      flat (xs ++ xs1) (ys ++ ys1) = flat xs ys ++ flat xs1 ys1`,
  CHEAT_TAC);;

let adjust_var_DIV_2 = prove
 (`(adjust_var n - 2) DIV 2 = n`,
  CHEAT_TAC);;

let adjust_var_DIV_2_ANY = prove
 (`(adjust_var n) DIV 2 = n + 1`,
  CHEAT_TAC);;

let EVEN_adjust_var = prove
 (`EVEN (adjust_var n)`,
  CHEAT_TAC);;

(* [simp] *)
let adjust_var_eq_numeral = prove
 (`adjust_var n = NUMERAL k <=>
    EVEN (NUMERAL k) /\ ~(NUMERAL k = 0) /\ n = (NUMERAL k - 2) DIV
      2`,
  CHEAT_TAC);;

(* [simp] *)
let adjust_var_NEQ_0 = prove
 (`~(adjust_var n = 0)`,
  CHEAT_TAC);;

let adjust_var_NEQ_1 = prove
 (`~(adjust_var n = 1)`,
  CHEAT_TAC);;

(* [simp] *)
let adjust_var_NEQ = prove
 (`~(adjust_var n = 0) /\ ~(adjust_var n = 1) /\ ~(adjust_var n = 3)
  /\ ~(adjust_var n = 5) /\ ~(adjust_var n = 7) /\ ~(adjust_var n = 9)
  /\ ~(adjust_var n = 11) /\ ~(adjust_var n = 13)`,
  CHEAT_TAC);;

let unit_opt_eq = prove
 (`(x = (y:1 option)) <=> (IS_SOME x <=> IS_SOME y)`,
  CHEAT_TAC);;

let adjust_var_11 = prove
 (`(adjust_var n = adjust_var m) <=> n = m`,
  CHEAT_TAC);;

let lookup_adjust_var_adjust_set = prove
 (`sptree_lookup (adjust_var n) (adjust_set s) = sptree_lookup n s`,
  CHEAT_TAC);;

let adjust_var_IN_adjust_set = prove
 (`adjust_var n IN domain (adjust_set (s:1 spt)) <=> n IN domain s`,
  CHEAT_TAC);;

let none_opt_eq = prove
 (`((x = NONE) = (y = NONE)) <=> (IS_SOME x <=> IS_SOME y)`,
  CHEAT_TAC);;

let lookup_adjust_var_adjust_set_NONE = prove
 (`sptree_lookup (adjust_var n) (adjust_set s) = NONE <=>
  sptree_lookup n s = NONE`,
  CHEAT_TAC);;

let lookup_adjust_var_adjust_set_SOME_UNIT = prove
 (`sptree_lookup (adjust_var n) (adjust_set s) = SOME one <=> IS_SOME
  (sptree_lookup n s)`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_ml_inv_lookup = prove
 (cake_as_vars (fun () ->
    `word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
        (ys ++ join_env l1 (toAList (inter l2 (adjust_set l1))) ++
          xs) /\
      sptree_lookup n l1 = SOME x /\
      sptree_lookup (adjust_var n) l2 = SOME w ==>
      word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
        (ys ++ [(x,w)] ++ join_env l1 (toAList (inter l2
          (adjust_set l1))) ++ xs)`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_ml_inv_get_var_IMP_lemma = prove
 (cake_as_vars (fun () ->
    `word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
        (join_env ll (toAList (inter (wordSem_state_locals t)
          (adjust_set ll))) ++ envs) /\
      get_var n ll = SOME x /\
      get_var (adjust_var n) t = SOME w ==>
      word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
        ([(x,w)] ++ join_env ll
            (toAList (inter (wordSem_state_locals t) (adjust_set
              ll))) ++ envs)`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_ml_inv_get_var_IMP = prove
 (cake_as_vars (fun () ->
    `word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
        (join_env (state_locals s) (toAList (inter
          (wordSem_state_locals t) (adjust_set (state_locals s)))) ++
          envs) /\
      get_var n (state_locals s) = SOME x /\
      get_var (adjust_var n) t = SOME w ==>
      word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
        ([(x,w)] ++ join_env (state_locals s)
            (toAList (inter (wordSem_state_locals t) (adjust_set
              (state_locals s)))) ++ envs)`),
  CHEAT_TAC);;

(* [allow_rebind] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_ml_inv_get_vars_IMP_lemma = prove
 (cake_as_vars (fun () ->
    `!n x w envs'.
           word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
             (join_env ll
                (toAList (inter (wordSem_state_locals t)
                  (adjust_set ll))) ++ envs') /\
           get_vars n ll = SOME x /\
           get_vars (MAP adjust_var n) t = SOME w ==>
           word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
             (ZIP x w ++ join_env ll
                (toAList (inter (wordSem_state_locals t)
                  (adjust_set ll))) ++ envs')`),
  CHEAT_TAC);;

(* [allow_rebind] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_ml_inv_get_vars_IMP = prove
 (cake_as_vars (fun () ->
    `!n x w envs'.
           word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
             (join_env (state_locals s)
                (toAList (inter (wordSem_state_locals t)
                  (adjust_set (state_locals s)))) ++ envs') /\
           get_vars n (state_locals s) = SOME x /\
           get_vars (MAP adjust_var n) t = SOME w ==>
           word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
             (ZIP x w ++ join_env (state_locals s)
                (toAList (inter (wordSem_state_locals t)
                  (adjust_set (state_locals s)))) ++ envs')`),
  CHEAT_TAC);;

let IMP_adjust_var = prove
 (`~(n = 0) /\ EVEN n ==> adjust_var ((n - 2) DIV 2) = n`,
  CHEAT_TAC);;

let unit_some_eq_IS_SOME = prove
 (`!x. (x = SOME one) <=> IS_SOME x`,
  CHEAT_TAC);;

let IS_SOME_lookup_domain = prove
 (`IS_SOME (sptree_lookup k m) <=> k IN domain m`,
  CHEAT_TAC);;


(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_ml_inv_insert = prove
 (cake_as_vars (fun () ->
    `word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
        ([(x,w)] ++ join_env d (toAList (inter l (adjust_set d)))
          ++ xs) ==>
      word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
        (join_env (insert dest x d)
          (toAList (inter (insert (adjust_var dest) w l)
                             (adjust_set (insert dest x d)))) ++
                               xs)`),
  CHEAT_TAC);;

let one_and_or_1 = prove
 (`((n2w 1) && (w || (n2w 1))) = (n2w 1)`,
  CHEAT_TAC);;

let one_and_or_3 = prove
 (`((n2w 3) && (w || (n2w 3))) = (n2w 3)`,
  CHEAT_TAC);;

let ODD_not_zero = prove
 (`ODD n ==> ~(n2w n = (n2w 0))`,
  CHEAT_TAC);;

(* [simp] *)
let three_not_0 = prove
 (`~((n2w 3) = (n2w 0))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:583: the ML values that the
   definitions below antiquote *)

let three_and_shift_2 = prove
 (`((n2w 3) && (w << 2)) = (n2w 0)`,
  CHEAT_TAC);;

let shift_to_zero = prove
 (`(n2w 3) >>> 2 = (n2w 0)`,
  CHEAT_TAC);;

let shift_around_under_big_shift = prove
 (`!w n k. n <= k ==> (w << n >>> n << k = w << k)`,
  CHEAT_TAC);;

let select_shift_out = prove
 (`~(n = 0) /\ n <= m ==> ((word_bits (n - 1) 0) (w || v << m) =
  (word_bits (n - 1) 0) w)`,
  CHEAT_TAC);;

(* [simp] *)
let shift_length_NOT_ZERO = prove
 (`~(shift_length conf = 0)`,
  CHEAT_TAC);;

let get_addr_and_1_not_0 = prove
 (`~(((n2w 1) && get_addr conf k a) = (n2w 0))`,
  CHEAT_TAC);;

let one_lsr_shift_length = prove
 (`(n2w 1) >>> shift_length conf = (n2w 0)`,
  CHEAT_TAC);;

let ptr_to_addr_get_addr = prove
 (`k * 2 EXP shift_length conf < dimword (:'a) ==>
    ptr_to_addr conf curr (get_addr conf k a) =
    curr + n2w k * (bytes_in_word:'a word)`,
  CHEAT_TAC);;

let is_fws_ptr_OR_3 = prove
 (`is_fwd_ptr (wordLang_Word (w << 2)) /\ ~(is_fwd_ptr (wordLang_Word
  (w || (n2w 3))))`,
  CHEAT_TAC);;

let is_fws_ptr_OR_15 = prove
 (`~(is_fwd_ptr (wordLang_Word (w || (n2w 15))))`,
  CHEAT_TAC);;

let is_fws_ptr_OR_10111 = prove
 (`~(is_fwd_ptr (wordLang_Word (w || (n2w 0b10111))))`,
  CHEAT_TAC);;

let is_fws_ptr_OR_7 = prove
 (`~(is_fwd_ptr (wordLang_Word (w || (n2w 7))))`,
  CHEAT_TAC);;

let select_get_lowerbits = prove
 (`(word_bits (shift_length conf - 1) 0) (get_lowerbits conf a) =
   get_lowerbits conf a /\
   (word_bits (small_shift_length conf - 1) 0) (get_lowerbits conf a)
     =
   get_lowerbits conf a`,
  CHEAT_TAC);;

let LE_DIV_LT_IMP = prove
 (`n <= l DIV 2 EXP m /\ k < n ==> k * 2 EXP m < l`,
  CHEAT_TAC);;

let word_bits_eq_slice_shift = prove
 (`((word_bits k n) w) = (((word_slice k n) w) >>> n)`,
  CHEAT_TAC);;

let word_slice_or = prove
 (`(word_slice k n) (w || v) = ((word_slice k n) w || (word_slice k n)
  v)`,
  CHEAT_TAC);;

let word_slice_lsl_eq_0 = prove
 (`(word_slice k n) (w << (k + 1)) = (n2w 0)`,
  CHEAT_TAC);;

let word_slice_2_3_eq_0 = prove
 (`(word_slice n 2) (n2w 3) = (n2w 0)`,
  CHEAT_TAC);;

let can_select_def = new_definition
  `can_select k n w <=> ((word_bits (k - 1) n) (w << n) = w)`;;

let read_length_lemma = prove
 (`can_select (n + 2) 2 (n2w k:'a word) ==>
    (((word_bits (n + 1) 2) (h << (2 + n) || n2w k << 2 || (n2w
      3))) = (n2w k:'a word))`,
  CHEAT_TAC);;

let memcpy_thm = prove
 (`!xs (a:'a word) c b m m1 dm b1 ys frame.
      memcpy (n2w (LENGTH xs):'a word) a b m dm = (b1,m1,c) /\
      (LENGTH ys = LENGTH xs) /\ LENGTH xs < dimword (:'a) /\
      (frame * misc_word_list a xs * misc_word_list b ys) (fun2set
        (m,dm)) ==>
      (frame * misc_word_list a xs * misc_word_list b xs) (fun2set
        (m1,dm)) /\
      b1 = b + n2w (LENGTH xs) * bytes_in_word /\ c`,
  CHEAT_TAC);;

let LESS_EQ_IMP_APPEND = prove
 (`!n xs. n <= LENGTH xs ==> (?ys zs. xs = ys ++ zs /\ LENGTH ys = n)`,
  CHEAT_TAC);;

let NOT_is_fwd_ptr = prove
 (`word_payload addrs ll tag tt1 conf = (h,ts,c5) ==> ~(is_fwd_ptr
  (wordLang_Word h))`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_gc_move_thm = prove
 (cake_as_vars (fun () ->
    `(copying_gc_gc_move (x,[],a,n,heap,T,limit) =
  (x1,h1,a1,n1,heap1,T)) /\
      heap_length heap <= dimword (:'a) DIV 2 EXP shift_length conf
        /\
      (word_heap curr heap conf * misc_word_list pa xs * frame)
        (fun2set (m,dm)) /\
      (word_gc_move conf (word_addr conf x,n2w a,pa,curr,m,dm) =
        ((w:'a word_loc),i1,pa1,m1,c1)) /\
      LENGTH xs = n ==>
      (?xs1.
        (word_heap curr heap1 conf *
         word_heap pa h1 conf *
         misc_word_list pa1 xs1 * frame) (fun2set (m1,dm)) /\
        (w = word_addr conf x1) /\
        heap_length heap1 = heap_length heap /\
        c1 /\ (i1 = n2w a1) /\ n1 = LENGTH xs1 /\
        pa1 = pa + bytes_in_word * n2w (heap_length h1))`),
  CHEAT_TAC);;

let word_gc_move_roots_thm = prove
 (`!x a n heap limit' pa x1 h1 a1 n1 heap1 pa1 m m1 xs i1 c1 w frame.
      (gc_move_list (x,[],a,n,heap,T,limit') = (x1,h1,a1,n1,heap1,T))
        /\
      heap_length heap <= dimword (:'a) DIV 2 EXP shift_length conf
        /\
      (word_heap curr heap conf * misc_word_list pa xs * frame)
        (fun2set (m,dm)) /\
      (word_gc_move_roots conf (MAP (word_addr conf) x,n2w
        a,pa,curr,m,dm) =
        ((w:('a word_loc) list),i1,pa1,m1,c1)) /\
      LENGTH xs = n ==>
      (?xs1.
        (word_heap curr heap1 conf *
         word_heap pa h1 conf *
         misc_word_list pa1 xs1 * frame) (fun2set (m1,dm)) /\
        (w = MAP (word_addr conf) x1) /\
        heap_length heap1 = heap_length heap /\
        c1 /\ (i1 = n2w a1) /\ n1 = LENGTH xs1 /\
        pa1 = pa + n2w (heap_length h1) * bytes_in_word)`,
  CHEAT_TAC);;

let word_gc_move_list_thm = prove
 (`!x a n heap limit' pa x1 h1 a1 n1 heap1 pa1 m m1 xs i1 c1 frame k k1.
      (copying_gc_gc_move_list (x,[],a,n,heap,T,limit') =
        (x1,h1,a1,n1,heap1,T)) /\
      heap_length heap <= dimword (:'a) DIV 2 EXP shift_length conf
        /\
      (word_gc_move_list conf (k,n2w (LENGTH x),n2w a,pa,curr,m,dm) =
        (k1,i1,pa1,m1,c1)) /\
      (word_heap curr heap conf * misc_word_list pa xs *
       misc_word_list k (MAP (word_addr conf) x) * frame) (fun2set
         (m,dm)) /\
      LENGTH xs = n /\ LENGTH x < dimword (:'a) ==>
      (?xs1.
        (word_heap curr heap1 conf *
         word_heap (pa:'a word) h1 conf *
         misc_word_list pa1 xs1 *
         misc_word_list k (MAP (word_addr conf) x1) * frame) (fun2set
           (m1,dm)) /\
        heap_length heap1 = heap_length heap /\
        c1 /\ (i1 = n2w a1) /\ n1 = LENGTH xs1 /\
        k1 = k + n2w (LENGTH x) * bytes_in_word /\
        pa1 = pa + n2w (heap_length h1) * bytes_in_word)`,
  CHEAT_TAC);;

let word_payload_swap = prove
 (`word_payload l5 (LENGTH l5) tag r conf = (h,MAP (word_addr conf)
  l5,T) /\
    LENGTH xs' = LENGTH l5 ==>
    word_payload xs' (LENGTH l5) tag r conf = (h,MAP (word_addr
      conf) xs',T)`,
  CHEAT_TAC);;

let word_gc_move_loop_thm = prove
 (`!h1 h2 a n heap c0 limit' h11 a1 n1 heap1 i1 pa1 m1 c1 xs frame m k.
      (gc_move_loop (h1,h2,a,n,heap,c0,limit') = (h11,a1,n1,heap1,T))
        /\ c0 /\
      heap_length heap <= dimword (:'a) DIV 2 EXP shift_length conf
        /\
      heap_length heap * (dimindex (:'a) DIV 8) < dimword (:'a) /\
        data_to_word_config_len_size
      conf + 2 < dimindex (:'a) /\
      (word_heap curr heap conf *
       word_heap new (h1 ++ h2) conf *
       misc_word_list (new + n2w (heap_length (h1 ++ h2)) *
         bytes_in_word) xs * frame)
         (fun2set (m,dm)) /\
      limit' - heap_length h1 <= k /\
      limit' = heap_length heap /\ good_dimindex (:'a) /\
      (word_gc_move_loop k conf (new + n2w (heap_length h1) *
        bytes_in_word,n2w a,
           new + n2w (heap_length (h1 ++ h2)) *
             bytes_in_word,curr,m,dm,T) =
         (i1,pa1,m1,c1)) /\ LENGTH xs = n ==>
      (?xs1.
        (word_heap curr heap1 conf *
         word_heap (new:'a word) h11 conf *
         misc_word_list pa1 xs1 * frame) (fun2set (m1,dm)) /\
        heap_length heap1 = heap_length heap /\
        c1 /\ (i1 = n2w a1) /\ n1 = LENGTH xs1 /\
        pa1 = new + bytes_in_word * n2w (heap_length h11))`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_full_gc_thm = prove
 (cake_as_vars (fun () ->
    `(full_gc (roots,heap,limit) = (roots1,heap1,a1,T)) /\
      heap_length heap <= dimword (:'a) DIV 2 EXP shift_length conf
        /\
      heap_length heap * (dimindex (:'a) DIV 8) < dimword (:'a) /\
        data_to_word_config_len_size
      conf + 2 < dimindex (:'a) /\
      (word_heap (curr:'a word) heap conf *
       word_heap new (heap_expand limit) conf * frame) (fun2set
         (m,dm)) /\
      limit = heap_length heap /\ good_dimindex (:'a) /\
      (word_full_gc conf (MAP (word_addr conf) roots,new,curr,m,dm)
        =
         (rs1,i1,pa1,m1,c1)) ==>
      (word_heap new (heap1 ++ heap_expand (limit - a1)) conf *
       word_heap curr (heap_expand limit) conf * frame) (fun2set
         (m1,dm)) /\
      c1 /\ i1 = n2w a1 /\
      rs1 = MAP (word_addr conf) roots1 /\
      pa1 = new + bytes_in_word * n2w a1`),
  CHEAT_TAC);;

let LIST_REL_EQ_MAP = prove
 (`!vs ws f. LIST_REL (\v w. f v = w) vs ws <=> ws = MAP f vs`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let full_gc_IMP = prove
 (cake_as_vars (fun () ->
    `full_gc (xs,heap,limit) = (t,heap2,n,T) ==>
      n <= limit /\ limit = heap_length heap`),
  CHEAT_TAC);;

let is_ref_header_alt = prove
 (`good_dimindex (:'a) ==>
    (is_ref_header (w:'a word) <=> ~(FAPPLY w 2) /\ (FAPPLY w 3))`,
  CHEAT_TAC);;

let is_ref_header_thm = prove
 (`(word_payload addrs ll tt0 tt1 conf = (h,ts,c5)) /\ good_dimindex
  (:'a) /\ data_to_word_config_len_size
    conf + 5 <= dimindex (:'a) ==>
    (is_ref_header (h:'a word) <=> isMutTag tt0)`,
  CHEAT_TAC);;

let is_Ref_def = new_definition
  `is_Ref is_ref_tag x2 =
      match x2 with
        DataElement xs l r -> is_ref_tag r
      | _13 -> F`;;

let len_inv_def = new_definition
  `len_inv s <=>
     heap_length (gc_state_heap s) =
     heap_length (gc_state_h1 s ++ gc_state_h2 s) + gc_state_n s +
       heap_length (gc_state_r4 s ++ gc_state_r3 s ++ gc_state_r2 s
       ++ gc_state_r1 s)`;;

let word_gen_gc_move_thm = prove
 (`(gen_gc_gc_move gen_conf s x = (x1,s1)) /\ gc_state_ok s1 /\
  gc_state_h2 s = [] /\ gc_state_r4 s = [] /\
    heap_length (gc_state_heap s) <= dimword (:'a) DIV 2 EXP
      shift_length conf /\
    (!t r. (isRef gen_conf (t,r) <=> isMutTag t)) /\
      data_to_word_config_len_size
    conf + 5 <= dimindex (:'a) /\
    (word_heap curr (gc_state_heap s) conf *
     misc_word_list pa xs * frame) (fun2set (m,dm)) /\
    (word_gen_gc_move conf (word_addr conf x,n2w (gc_state_a s),pa,
        n2w (gc_state_a s + gc_state_n s),pa + bytes_in_word * n2w
          (gc_state_n s),curr,m,dm) =
      ((w:'a word_loc),i1,pa1,ib1,pb1,m1,c1)) /\
    LENGTH xs = gc_state_n s /\ good_dimindex (:'a) /\
    EVERY (is_Ref (isRef gen_conf)) (gc_state_r4 s ++ gc_state_r3 s
      ++ gc_state_r2 s ++ gc_state_r1 s) ==>
    (?xs1.
      (word_heap curr (gc_state_heap s1) conf *
       word_heap pa (gc_state_h2 s1) conf *
       word_heap pb1 (gc_state_r4 s1) conf *
       misc_word_list pa1 xs1 *
       frame) (fun2set (m1,dm)) /\
      (w = word_addr conf x1) /\
      heap_length (gc_state_heap s1) = heap_length (gc_state_heap s)
        /\ c1 /\
      (i1 = n2w (gc_state_a s1)) /\
      (ib1 = n2w (gc_state_a s1 + gc_state_n s1)) /\ gc_state_n
      s1 = LENGTH xs1 /\ gc_state_n
      s = heap_length (gc_state_h2 s1) + gc_state_n s1 + heap_length
        (gc_state_r4 s1) /\
      pa1 = pa + bytes_in_word * n2w (heap_length (gc_state_h2 s1))
        /\
      pb1 = pa1 + bytes_in_word * n2w (gc_state_n s1) /\
      EVERY (is_Ref (isRef gen_conf)) (gc_state_r4 s1 ++
        gc_state_r3 s1 ++ gc_state_r2 s1 ++ gc_state_r1 s1))`,
  CHEAT_TAC);;

let gc_move_with_NIL = prove
 (`!x s y t.
      gen_gc_gc_move gen_conf s x = (y,t) /\ gc_state_ok t ==>
      (let (y,s1) = gc_move gen_conf (gc_state_r4_fupd (K [])
        (gc_state_h2_fupd (K []) s)) x in
        (y,gc_state_r4_fupd (K (gc_state_r4 s1 ++ gc_state_r4 s))
          (gc_state_h2_fupd (K (gc_state_h2 s ++ gc_state_h2 s1))
          s1))) = (y,t)`,
  CHEAT_TAC);;

let gc_move_with_NIL_LEMMA = prove
 (`!x s y t h2 r4 y1 t1.
      gen_gc_gc_move gen_conf s x = (y1,t1) /\ gc_state_ok t1 ==>
      (?x1 x2. gc_state_h2
        t1 = gc_state_h2 s ++ x1 /\ gc_state_r4
        t1 = x2 ++ gc_state_r4 s /\
        gen_gc_gc_move gen_conf (gc_state_r4_fupd (K [])
          (gc_state_h2_fupd (K []) s)) x =
          (y1,gc_state_r4_fupd (K x2) (gc_state_h2_fupd (K x1)
            t1)))`,
  CHEAT_TAC);;

(* [local] *)
let gc_move_list_ok_irr0 = prove
 (`!x s y1 y2 t1 t2 h2 r4.
     gen_gc_gc_move gen_conf s x = (y1,t1) /\
     gen_gc_gc_move gen_conf (gc_state_r4_fupd (K r4)
       (gc_state_h2_fupd (K h2) s)) x = (y2,t2) ==>
     y1 = y2 /\ (?x1 x2. t2 = gc_state_r4_fupd (K x2)
       (gc_state_h2_fupd (K x1) t1))`,
  CHEAT_TAC);;

let gc_move_list_ok_irr = prove
 (`!x s y1 y2 t1 t2 h2 r4.
      gen_gc_gc_move_list gen_conf s x = (y1,t1) /\ gc_state_ok t1 /\
      gen_gc_gc_move_list gen_conf (gc_state_r4_fupd (K r4)
        (gc_state_h2_fupd (K h2) s)) x = (y2,t2) ==> gc_state_ok
      t2`,
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:1485-1505: a theorem that HOL4
   states as the value of an ML expression:
   gc_move_list_with_NIL_LEMMA *)

let gc_move_list_with_NIL = prove
 (`!x s y t.
      gen_gc_gc_move_list gen_conf s x = (y,t) /\ gc_state_ok t ==>
      (let (y,s1) = gc_move_list gen_conf (gc_state_r4_fupd (K [])
        (gc_state_h2_fupd (K []) s)) x in
        (y,gc_state_r4_fupd (K (gc_state_r4 s1 ++ gc_state_r4 s))
          (gc_state_h2_fupd (K (gc_state_h2 s ++ gc_state_h2 s1))
          s1))) = (y,t)`,
  CHEAT_TAC);;

let word_gen_gc_move_roots_thm = prove
 (`!x xs x1 w s1 s pb1 pa1 pa m1 m ib1 i1 frame dm curr c1.
    (gen_gc_gc_move_list gen_conf s x = (x1,s1)) /\ gc_state_ok s1 /\
      gc_state_h2 s = [] /\ gc_state_r4 s = [] /\
    heap_length (gc_state_heap s) <= dimword (:'a) DIV 2 EXP
      shift_length conf /\
    (!t r. (isRef gen_conf (t,r) <=> isMutTag t)) /\
      data_to_word_config_len_size
    conf + 5 <= dimindex (:'a) /\
    (word_heap curr (gc_state_heap s) conf *
     misc_word_list pa xs * frame) (fun2set (m,dm)) /\
    (word_gen_gc_move_roots conf (MAP (word_addr conf) x,n2w
      (gc_state_a s),pa,
        n2w (gc_state_a s + gc_state_n s),pa + bytes_in_word * n2w
          (gc_state_n s),curr,m,dm) =
      ((w:('a word_loc) list),i1,pa1,ib1,pb1,m1,c1)) /\
    EVERY (is_Ref (isRef gen_conf)) (gc_state_r4 s ++ gc_state_r3 s
      ++ gc_state_r2 s ++ gc_state_r1 s) /\
    LENGTH xs = gc_state_n s /\ good_dimindex (:'a) ==>
    (?xs1.
      (word_heap curr (gc_state_heap s1) conf *
       word_heap pa (gc_state_h2 s1) conf *
       word_heap pb1 (gc_state_r4 s1) conf *
       misc_word_list pa1 xs1 *
       frame) (fun2set (m1,dm)) /\
      (w = MAP (word_addr conf) x1) /\
      heap_length (gc_state_heap s1) = heap_length (gc_state_heap s)
        /\
      c1 /\ (i1 = n2w (gc_state_a s1)) /\ (ib1 = n2w (gc_state_a s1 +
        gc_state_n s1)) /\ gc_state_n s1 = LENGTH xs1 /\ gc_state_n
      s = heap_length (gc_state_h2 s1) + gc_state_n s1 + heap_length
        (gc_state_r4 s1) /\
      pa1 = pa + bytes_in_word * n2w (heap_length (gc_state_h2 s1))
        /\
      pb1 = pa1 + bytes_in_word * n2w (gc_state_n s1) /\
      EVERY (is_Ref (isRef gen_conf)) (gc_state_r4 s1 ++
        gc_state_r3 s1 ++ gc_state_r2 s1 ++ gc_state_r1 s1))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:1571-1631: a theorem that HOL4
   states as the value of an ML expression: word_gen_gc_move_list_thm *)

let word_heap_parts_def = assume_definition
  "free: word_heap:(?1655030)word->((?1655018,?1655019)heap_ele"
  [`word_heap_parts conf p s xs =
     word_heap p (gc_state_h1 s ++ gc_state_h2 s) conf *
     misc_word_list (p + bytes_in_word * n2w (heap_length
       (gc_state_h1 s ++ gc_state_h2 s))) xs *
     word_heap (p + bytes_in_word * n2w (heap_length (gc_state_h1 s
       ++ gc_state_h2 s) + LENGTH xs))
       (gc_state_r4 s ++ gc_state_r3 s ++ gc_state_r2 s ++
         gc_state_r1 s) conf`];;

let gc_move_const = prove
 (`!l s xs' s'.
      gen_gc_gc_move gen_conf s l = (xs',s') ==> gc_state_h1
      s' = gc_state_h1 s /\ gc_state_r1 s' = gc_state_r1 s /\
        gc_state_r2 s' = gc_state_r2 s /\ gc_state_r3 s' = gc_state_r3
        s`,
  CHEAT_TAC);;

let gc_move_list_const = prove
 (`!l s xs' s'.
      gen_gc_gc_move_list gen_conf s l = (xs',s') ==> gc_state_h1
      s' = gc_state_h1 s /\ gc_state_r1 s' = gc_state_r1 s /\
        gc_state_r2 s' = gc_state_r2 s /\ gc_state_r3 s' = gc_state_r3
        s`,
  CHEAT_TAC);;

let gc_move_data_const = prove
 (`!gen_conf s s'.
      gen_gc_gc_move_data gen_conf s = s' ==> gc_state_r1
      s' = gc_state_r1 s /\ gc_state_r2 s' = gc_state_r2 s /\
        gc_state_r3 s' = gc_state_r3 s`,
  CHEAT_TAC);;

let gc_move_refs_const = prove
 (`!gen_conf s s'.
      gc_move_refs gen_conf s = s' ==> gc_state_h1
      s' = gc_state_h1 s`,
  CHEAT_TAC);;

let heap_length_gc_forward_ptr = prove
 (`!hs n k a ok heap.
      gc_forward_ptr n hs k a ok = (heap,T) ==>
      heap_length heap = heap_length hs /\ ok`,
  CHEAT_TAC);;

(* gc_move_thm *)
let data_to_word_gcProof_gc_move_thm = prove
 (`!l s l1 s1.
      gen_gc_gc_move gen_conf s l = (l1,s1) /\ gc_state_ok s1 /\
        len_inv s ==>
      len_inv s1`,
  CHEAT_TAC);;

(* gc_move_list_thm *)
let data_to_word_gcProof_gc_move_list_thm = prove
 (`!l s l1 s1.
      gen_gc_gc_move_list gen_conf s l = (l1,s1) /\ gc_state_ok s1 /\
        len_inv s ==>
      len_inv s1`,
  CHEAT_TAC);;

let word_list_IMP_limit = prove
 (`(misc_word_list (curr:'a word) hs * frame) (fun2set (m,dm)) /\
    good_dimindex (:'a) ==>
    LENGTH hs <= dimword (:'a) DIV (dimindex (:'a) DIV 8)`,
  CHEAT_TAC);;

let word_el_eq_word_list = prove
 (`!hs curr frame.
      (word_el (curr:'a word) hs conf * frame) (fun2set (m,dm)) ==>
      (?xs. (misc_word_list curr xs * frame) (fun2set (m,dm)) /\
           el_length hs = LENGTH xs /\
           (!frame1 curr1 m1. (misc_word_list curr1 xs * frame1)
             (fun2set (m1,dm)) ==>
            (word_el curr1 hs conf * frame1) (fun2set (m1,dm))))`,
  CHEAT_TAC);;

let word_heap_eq_word_list_strong = prove
 (`!(hs:(('a word_loc,data_to_word_memoryProof_tag#('a word_loc)
  list)heap_element) list) curr frame.
      (word_heap (curr:'a word) (hs:(('a
        word_loc,data_to_word_memoryProof_tag#('a word_loc)
        list)heap_element) list) conf * frame) (fun2set (m,dm)) ==>
      (?xs. (misc_word_list curr xs * frame) (fun2set (m,dm)) /\
            heap_length hs = LENGTH xs /\
            (!curr1 frame1 m1.
              (misc_word_list curr1 xs * frame1) (fun2set (m1,dm))
                ==> (word_heap curr1 hs conf * frame1) (fun2set
                (m1,dm))))`,
  CHEAT_TAC);;

let word_heap_eq_word_list = prove
 (`!(hs:(('a word_loc,data_to_word_memoryProof_tag#('a word_loc)
  list)heap_element) list) curr frame.
      (word_heap (curr:'a word) (hs:(('a
        word_loc,data_to_word_memoryProof_tag#('a word_loc)
        list)heap_element) list) conf * frame) (fun2set (m,dm)) ==>
      (?xs. (misc_word_list curr xs * frame) (fun2set (m,dm)) /\
            heap_length hs = LENGTH xs)`,
  CHEAT_TAC);;

let word_heap_IMP_limit = prove
 (`(word_heap (curr:'a word) (hs:(('a
  word_loc,data_to_word_memoryProof_tag#('a word_loc) list)heap_element)
  list) conf * frame) (fun2set (m,dm)) /\
    good_dimindex (:'a) ==>
    heap_length hs <= dimword (:'a) DIV (dimindex (:'a) DIV 8)`,
  CHEAT_TAC);;

let muttag_header_def = assume_definition
  "free: thunk_tag_to_bits:thunk_mode->(?1655824)word"
  [`muttag_header x1 =
      match x1 with
        ThunkTag e -> (thunk_tag_to_bits e << 3 || (n2w 6))
      | _14 -> (n2w 2)`];;

let isMutTag_word_payload_IMP = prove
 (`!x1 x2 x3.
     word_payload ys l t qs conf = (x1,x2,x3) /\
     isMutTag t ==>
     x1 = make_header conf (muttag_header t) (LENGTH ys) /\
     x2 = MAP (word_addr conf) ys /\
     x3 = (qs = [] /\ LENGTH ys = l /\ (~(t = RefTag) ==> l = 1))`,
  CHEAT_TAC);;

let word_gen_gc_move_refs_thm = prove
 (`!k s m dm curr xs s1 pb1 pa1 m1 ib1 i1 frame c1 p1.
    (gc_move_refs gen_conf s = s1) /\ gc_state_ok s1 /\
    heap_length (gc_state_heap s) <= dimword (:'a) DIV 2 EXP
      shift_length conf /\
    heap_length (gc_state_heap s) * (dimindex (:'a) DIV 8) < dimword
      (:'a) /\
    (!t r. (isRef gen_conf (t,r) <=> isMutTag t)) /\
      data_to_word_config_len_size
    conf + 5 <= dimindex (:'a) /\
    (word_gen_gc_move_refs conf k
       (
         // r2a
         p + bytes_in_word *
          n2w (heap_length (gc_state_h1 s ++ gc_state_h2 s ++
            gc_state_r4 s ++ gc_state_r3 s) + LENGTH xs),
         // r1a
         p + bytes_in_word *
          n2w (heap_length (gc_state_h1 s ++ gc_state_h2 s ++
            gc_state_r4 s ++ gc_state_r3 s ++ gc_state_r2 s) + LENGTH
            xs),
        n2w (gc_state_a s),
         // pa
         p + bytes_in_word * n2w (heap_length (gc_state_h1 s ++
           gc_state_h2 s)),
        n2w (gc_state_a s + gc_state_n s),
         // pb
         p + bytes_in_word * n2w (heap_length (gc_state_h1 s ++
           gc_state_h2 s) + gc_state_n s),
        (curr:'a word),m,dm) =
      (p1,i1,pa1,ib1,pb1,m1,c1)) /\
    LENGTH (gc_state_r2 s) <= k /\ len_inv s /\
    (word_heap curr (gc_state_heap s) conf *
     word_heap_parts conf p s xs *
     frame) (fun2set (m,dm)) /\
    EVERY (is_Ref (isRef gen_conf)) (gc_state_r4 s ++ gc_state_r3 s
      ++ gc_state_r2 s ++ gc_state_r1 s) /\
    LENGTH xs = gc_state_n s /\ good_dimindex (:'a) ==>
    (?xs1.
      (word_heap curr (gc_state_heap s1) conf *
       word_heap_parts conf p s1 xs1 *
       frame) (fun2set (m1,dm)) /\ gc_state_r3 s1 = [] /\ gc_state_r2
         s1 = [] /\
      heap_length (gc_state_heap s1) = heap_length (gc_state_heap s)
        /\
      c1 /\ (i1 = n2w (gc_state_a s1)) /\ (ib1 = n2w (gc_state_a s1 +
        gc_state_n s1)) /\ gc_state_n s1 = LENGTH xs1 /\
      heap_length (gc_state_h2 s) + gc_state_n s + heap_length
        (gc_state_r4 s) =
      heap_length (gc_state_h2 s1) + gc_state_n s1 + heap_length
        (gc_state_r4 s1) /\
      pa1 = p + bytes_in_word * n2w (heap_length (gc_state_h1 s1 ++
        gc_state_h2 s1)) /\
      pb1 = p + bytes_in_word * n2w (heap_length (gc_state_h1 s1 ++
        gc_state_h2 s1) + gc_state_n s1) /\
      p1 = p + bytes_in_word * n2w (heap_length
              (gc_state_h1 s ++ gc_state_h2 s ++ gc_state_r4 s ++
                gc_state_r3 s ++ gc_state_r2 s) + LENGTH xs) /\ len_inv
                s1 /\
      EVERY (is_Ref (isRef gen_conf)) (gc_state_r4 s1 ++
        gc_state_r3 s1 ++ gc_state_r2 s1 ++ gc_state_r1 s1))`,
  CHEAT_TAC);;

let word_gen_gc_move_data_thm = prove
 (`!k s m dm curr xs s1 pb1 pa1 m1 ib1 i1 frame c1.
    (gen_gc_gc_move_data gen_conf s = s1) /\ gc_state_ok s1 /\
    heap_length (gc_state_heap s) <= dimword (:'a) DIV 2 EXP
      shift_length conf /\
    heap_length (gc_state_heap s) * (dimindex (:'a) DIV 8) < dimword
      (:'a) /\ data_to_word_config_len_size
    conf + 2 < dimindex (:'a) /\
    (!t r. (isRef gen_conf (t,r) <=> isMutTag t)) /\
      data_to_word_config_len_size
    conf + 5 <= dimindex (:'a) /\
    (word_gen_gc_move_data conf k
       (
         // h2a
         p + bytes_in_word * n2w (heap_length (gc_state_h1 s)),
        n2w (gc_state_a s),
         // pa
         p + bytes_in_word * n2w (heap_length (gc_state_h1 s ++
           gc_state_h2 s)),
        n2w (gc_state_a s + gc_state_n s),
         // pb
         p + bytes_in_word * n2w (heap_length (gc_state_h1 s ++
           gc_state_h2 s) + gc_state_n s),
        (curr:'a word),m,dm) =
      (i1,pa1,ib1,pb1,m1,c1)) /\
    heap_length (gc_state_h2 s) + gc_state_n s + heap_length
      (gc_state_r4 s) <= k /\ len_inv s /\
    (word_heap curr (gc_state_heap s) conf *
     word_heap_parts conf p s xs *
     frame) (fun2set (m,dm)) /\
    EVERY (is_Ref (isRef gen_conf)) (gc_state_r4 s ++ gc_state_r3 s
      ++ gc_state_r2 s ++ gc_state_r1 s) /\
    LENGTH xs = gc_state_n s /\ good_dimindex (:'a) ==>
    (?xs1.
      (word_heap curr (gc_state_heap s1) conf *
       word_heap_parts conf p s1 xs1 *
       frame) (fun2set (m1,dm)) /\ gc_state_h2 s1 = [] /\
      heap_length (gc_state_heap s1) = heap_length (gc_state_heap s)
        /\
      c1 /\ (i1 = n2w (gc_state_a s1)) /\ (ib1 = n2w (gc_state_a s1 +
        gc_state_n s1)) /\ gc_state_n
      s1 = LENGTH xs1 /\ len_inv s1 /\
      heap_length (gc_state_h1 s1 ++ gc_state_h2 s1 ++ gc_state_r4
        s1) + gc_state_n s1 =
      heap_length (gc_state_h1 s ++ gc_state_h2 s ++ gc_state_r4 s) +
        gc_state_n s /\
      pa1 = p + bytes_in_word * n2w (heap_length (gc_state_h1 s1 ++
        gc_state_h2 s1)) /\
      pb1 = p + bytes_in_word * n2w (heap_length (gc_state_h1 s1 ++
        gc_state_h2 s1) + gc_state_n s1) /\
      EVERY (is_Ref (isRef gen_conf)) (gc_state_r4 s1 ++
        gc_state_r3 s1 ++ gc_state_r2 s1 ++ gc_state_r1 s1))`,
  CHEAT_TAC);;

let LENGTH_LESS_EQ_SUM_el_length = prove
 (`!t. LENGTH t <= SUM (MAP el_length t)`,
  CHEAT_TAC);;

let word_gen_gc_move_loop_thm = prove
 (`!k s m dm curr xs s1 pb1 pa1 m1 ib1 i1 frame c1.
    (gen_gc_gc_move_loop gen_conf s k = s1) /\ gc_state_ok s1 /\
    heap_length (gc_state_heap s) <= dimword (:'a) DIV 2 EXP
      shift_length conf /\
    heap_length (gc_state_heap s) * (dimindex (:'a) DIV 8) < dimword
      (:'a) /\ data_to_word_config_len_size
    conf + 2 < dimindex (:'a) /\ gc_state_r3 s = [] /\ gc_state_r2 s
      = [] /\
    (!t r. (isRef gen_conf (t,r) <=> isMutTag t)) /\
      data_to_word_config_len_size
    conf + 5 <= dimindex (:'a) /\
    (word_gen_gc_move_loop conf k
       (
         // pax
         p + bytes_in_word * n2w (heap_length (gc_state_h1 s)),
        n2w (gc_state_a s),
         // pa
         p + bytes_in_word * n2w (heap_length (gc_state_h1 s ++
           gc_state_h2 s)),
        n2w (gc_state_a s + gc_state_n s),
         // pb
         p + bytes_in_word * n2w (heap_length (gc_state_h1 s ++
           gc_state_h2 s) + gc_state_n s),
         // pbx
         p + bytes_in_word * n2w (heap_length (gc_state_h1 s ++
           gc_state_h2 s ++ gc_state_r4 s) + gc_state_n s),
        (curr:'a word),m,dm) =
      (i1,pa1,ib1,pb1,m1,c1)) /\ len_inv s /\
    (word_heap curr (gc_state_heap s) conf *
     word_heap_parts conf p s xs *
     frame) (fun2set (m,dm)) /\
    EVERY (is_Ref (isRef gen_conf)) (gc_state_r4 s ++ gc_state_r3 s
      ++ gc_state_r2 s ++ gc_state_r1 s) /\
    LENGTH xs = gc_state_n s /\ good_dimindex (:'a) ==>
    (?xs1.
      (word_heap curr (gc_state_heap s1) conf *
       word_heap_parts conf p s1 xs1 *
       frame) (fun2set (m1,dm)) /\ gc_state_h2
      s1 = [] /\ gc_state_r4 s1 = [] /\ gc_state_r3 s1 = [] /\
        gc_state_r2 s1 = [] /\
      heap_length (gc_state_heap s1) = heap_length (gc_state_heap s)
        /\
      c1 /\ (i1 = n2w (gc_state_a s1)) /\ gc_state_n s1 = LENGTH xs1
        /\ len_inv s1 /\
      pa1 = p + bytes_in_word * n2w (heap_length (gc_state_h1 s1)) /\
      pb1 = p + bytes_in_word * n2w (heap_length (gc_state_h1 s1) +
        gc_state_n s1) /\
      (ib1 = n2w (gc_state_a s1 + gc_state_n s1)) /\
      EVERY (is_Ref (isRef gen_conf)) (gc_state_r1 s1))`,
  CHEAT_TAC);;

let word_gen_gc_thm = prove
 (`!m dm curr s1 pb1 pa1 m1 ib1 i1 frame c1 roots heap roots1 roots1'
  new.
    (gen_gc gen_conf (roots,heap) = (roots1,s1)) /\ gc_state_ok s1 /\
    (word_gen_gc conf (MAP (word_addr conf) roots,curr,new,
          bytes_in_word * n2w (heap_length heap),m,dm) =
      (roots1',i1,(pa1:'a word),ib1,pb1,m1,c1)) /\
    heap_length heap <= dimword (:'a) DIV 2 EXP shift_length conf /\
    heap_length heap * (dimindex (:'a) DIV 8) < dimword (:'a) /\
      data_to_word_config_len_size
    conf + 2 < dimindex (:'a) /\
    (!t r. (isRef gen_conf (t,r) <=> isMutTag t)) /\
      data_to_word_config_len_size
    conf + 5 <= dimindex (:'a) /\
    good_dimindex (:'a) /\
    (word_heap curr heap conf *
     word_list_exists new (heap_length heap) *
     frame) (fun2set (m,dm)) /\ good_dimindex (:'a) ==>
    (?xs1.
      (word_heap curr (gc_state_heap s1) conf *
       word_heap_parts conf new s1 xs1 *
       frame) (fun2set (m1,dm)) /\ gc_state_h2
      s1 = [] /\ gc_state_r4 s1 = [] /\ gc_state_r3 s1 = [] /\
        gc_state_r2 s1 = [] /\
      roots1' = MAP (word_addr conf) roots1 /\
      heap_length (gc_state_heap s1) = heap_length heap /\
      c1 /\ (i1 = n2w (gc_state_a s1)) /\ (ib1 = n2w (gc_state_a s1 +
        gc_state_n s1)) /\
      pa1 = new + bytes_in_word * n2w (heap_length (gc_state_h1 s1))
        /\
      pb1 = new + bytes_in_word * n2w (heap_length (gc_state_h1 s1) +
        gc_state_n s1) /\
      roots1' = MAP (word_addr conf) roots1 /\ gc_state_n
      s1 = LENGTH xs1 /\ len_inv s1 /\
      EVERY (is_Ref (isRef gen_conf)) (gc_state_r1 s1))`,
  CHEAT_TAC);;

(* gc_forward_ptr_APPEND *)
let data_to_word_gcProof_gc_forward_ptr_APPEND = prove
 (`!h1 n h2 a b ok.
   gc_forward_ptr n (h1 ++ h2) a b ok =
   (if n < heap_length h1 then
   (\(h,ok). (h ++ h2,ok)) (gc_forward_ptr n h1 a b ok) else
   (\(h,ok). (h1 ++ h,ok)) (gc_forward_ptr (n - heap_length h1) h2
     a b ok))`,
  CHEAT_TAC);;

let heap_split_APPEND = prove
 (`heap_split (heap_length h1) (h1 ++ h2) = SOME (h1,h2)`,
  CHEAT_TAC);;

let heap_split_APPEND' = prove
 (`heap_split (SUM (MAP el_length h1)) (h1 ++ h2) = SOME (h1,h2)`,
  CHEAT_TAC);;

let heap_drop_APPEND = prove
 (`heap_drop (heap_length h1) (h1 ++ h2) = h2`,
  CHEAT_TAC);;

let heap_take_APPEND = prove
 (`heap_take (heap_length h1) (h1 ++ h2) = h1`,
  CHEAT_TAC);;

let heap_drop_0 = prove
 (`heap_drop 0 h = h`,
  CHEAT_TAC);;

let gc_forward_ptr_heap_split = prove
 (`!h1 h2 n h3 l n' b ok ok1 heap a b'.
   (heap_lookup n (h1 ++ h2 ++ h3) = SOME (DataElement l n' b)) /\
   (gc_forward_ptr n (h1 ++ h2 ++ h3) a b' ok = (heap,ok1)) /\
   n >= heap_length h1 /\ n < heap_length (h1 ++ h2) ==> heap = h1
     ++ heap_take (heap_length h2) (heap_drop (heap_length h1) heap)
     ++ h3`,
  CHEAT_TAC);;

let partial_gc_move_heap_split = prove
 (`(gen_gc_partial_gc_move conf s x = (x1,s1)) /\
   heap_segment (gen_gc_partial_conf_gen_start
     conf,gen_gc_partial_conf_refs_start conf) (gc_state_heap s) =
     SOME (h1,h2,h3) /\ gen_gc_partial_conf_gen_start conf <=
     gen_gc_partial_conf_refs_start conf ==> gc_state_heap s1 = h1 ++
     heap_take (heap_length h2) (heap_drop (heap_length h1)
     (gc_state_heap s1)) ++ h3`,
  CHEAT_TAC);;

let partial_gc_move_list_heap_split = prove
 (`!x conf s x1 s1 h1 h2 h3.
   (gen_gc_partial_gc_move_list conf s x = (x1,s1)) /\
   heap_segment (gen_gc_partial_conf_gen_start
     conf,gen_gc_partial_conf_refs_start conf) (gc_state_heap s) =
     SOME (h1,h2,h3) /\ gen_gc_partial_conf_gen_start conf <=
     gen_gc_partial_conf_refs_start conf ==> gc_state_heap s1 = h1 ++
     heap_take (heap_length h2) (heap_drop (heap_length h1)
     (gc_state_heap s1)) ++ h3`,
  CHEAT_TAC);;

let word_gen_gc_partial_move_thm = prove
 (`(gen_gc_partial_gc_move gc_conf gcstate x = (x1,gcstate1)) /\
  gc_state_h2
    gcstate = [] /\ gc_state_r4 gcstate = [] /\ gc_state_ok gcstate1
      /\ limit
    gc_conf = heap_length (gc_state_heap gcstate) /\
    good_dimindex (:'a) /\
    heap_length (gc_state_heap gcstate) <= dimword (:'a) DIV 2 EXP
      shift_length conf /\ gen_gc_partial_conf_gen_start
    gc_conf <= gen_gc_partial_conf_refs_start gc_conf /\
      gen_gc_partial_conf_refs_start
    gc_conf <= heap_length (gc_state_heap gcstate) /\
    (heap_segment (gen_gc_partial_conf_gen_start
      gc_conf,gen_gc_partial_conf_refs_start gc_conf) (gc_state_heap
      gcstate) = SOME (old,current,refs)) /\
    heap_length (gc_state_heap gcstate) * (dimindex (:'a) DIV 8) <
      dimword (:'a) /\
    (word_heap (curr + bytes_in_word * n2w (heap_length old)) current
      conf * misc_word_list pa xs * frame) (fun2set (m,dm)) /\
    (!t r. (isRef gc_conf (t,r) <=> isMutTag t)) /\
    (word_gen_gc_partial_move conf (word_addr conf x,n2w (gc_state_a
      gcstate),pa,curr,m,dm,
                              bytes_in_word * n2w
                                (gen_gc_partial_conf_gen_start gc_conf),
                              bytes_in_word * n2w
                                (gen_gc_partial_conf_refs_start
                                gc_conf)) =
      ((w:'a word_loc),i1,pa1,m1,c1)) /\
    LENGTH xs = gc_state_n gcstate ==>
    (?xs1 current1.
      (word_heap (curr + bytes_in_word * n2w (heap_length old))
        current1 conf *
       word_heap pa (gc_state_h2 gcstate1) conf *
       misc_word_list pa1 xs1 * frame) (fun2set (m1,dm)) /\
      (w = word_addr conf x1) /\
      heap_length (gc_state_heap gcstate1) = heap_length
        (gc_state_heap gcstate) /\
      (heap_segment (gen_gc_partial_conf_gen_start
        gc_conf,gen_gc_partial_conf_refs_start gc_conf) (gc_state_heap
        gcstate1) = SOME (old,current1,refs)) /\
      c1 /\ (i1 = n2w (gc_state_a gcstate1)) /\ gc_state_n gcstate1 =
        LENGTH xs1 /\ gc_state_n
      gcstate = heap_length (gc_state_h2 gcstate1) + gc_state_n
        gcstate1 + heap_length (gc_state_r4 gcstate1) /\
      pa1 = pa + bytes_in_word * n2w (heap_length (gc_state_h2
        gcstate1)))`,
  CHEAT_TAC);;

let gc_partial_move_ok_irr = prove
 (`!x s y1 y2 t1 t2 h2 r4.
      gen_gc_partial_gc_move gen_conf s x = (y1,t1) /\
      gen_gc_partial_gc_move gen_conf (gc_state_r4_fupd (K r4)
        (gc_state_h2_fupd (K h2) s)) x = (y2,t2) ==>
      y1 = y2 /\ (?x1 x2. t2 = gc_state_r4_fupd (K x2)
        (gc_state_h2_fupd (K x1) t1))`,
  CHEAT_TAC);;

let gc_partial_move_ok_before = prove
 (`gen_gc_partial_gc_move gen_conf s x = (x1,s1) /\ gc_state_ok s1 ==>
  gc_state_ok s`,
  CHEAT_TAC);;

let gc_partial_move_list_ok_before = prove
 (`!x s x1 s1. gen_gc_partial_gc_move_list gen_conf s x = (x1,s1) /\
  gc_state_ok s1 ==> gc_state_ok s`,
  CHEAT_TAC);;

let gc_partial_move_ref_list_ok_before = prove
 (`!x s x1 s1. gc_move_ref_list gen_conf s x = (x1,s1) /\ gc_state_ok
  s1 ==> gc_state_ok s`,
  CHEAT_TAC);;

let gc_partial_move_data_ok_before = prove
 (`!gen_conf s s1. gen_gc_partial_gc_move_data gen_conf s = s1 /\
  gc_state_ok s1 ==> gc_state_ok s`,
  CHEAT_TAC);;

let gc_partial_move_list_ok_irr = prove
 (`!x s y1 y2 t1 t2 h2 r4.
      gen_gc_partial_gc_move_list gen_conf s x = (y1,t1) /\
        gc_state_ok t1 /\
      gen_gc_partial_gc_move_list gen_conf (gc_state_r4_fupd (K r4)
        (gc_state_h2_fupd (K h2) s)) x = (y2,t2) ==> gc_state_ok
      t2`,
  CHEAT_TAC);;

let gc_partial_move_list_ok_irr' = prove
 (`!x s y1 y2 t1 t2 h2 r4.
      gen_gc_partial_gc_move_list gen_conf s x = (y1,t1) /\
      gen_gc_partial_gc_move_list gen_conf (gc_state_r4_fupd (K r4)
        (gc_state_h2_fupd (K h2) s)) x = (y2,t2) ==>
      y1 = y2 /\ (?x1 x2. t2 = gc_state_r4_fupd (K x2)
        (gc_state_h2_fupd (K x1) t1))`,
  CHEAT_TAC);;

let gc_partial_move_ref_list_ok_irr = prove
 (`!x s y1 y2 t1 t2 h2 r4.
      gc_move_ref_list gen_conf s x = (y1,t1) /\ gc_state_ok t1 /\
      gc_move_ref_list gen_conf (gc_state_r4_fupd (K r4)
        (gc_state_h2_fupd (K h2) s)) x = (y2,t2) ==> gc_state_ok
      t2`,
  CHEAT_TAC);;

let gc_partial_move_with_NIL = prove
 (`!x s y t.
      gen_gc_partial_gc_move gen_conf s x = (y,t) /\ gc_state_ok t
        ==>
      (let (y,s1) = gc_move gen_conf (gc_state_r4_fupd (K [])
        (gc_state_h2_fupd (K []) s)) x in
        (y,gc_state_r4_fupd (K (gc_state_r4 s1 ++ gc_state_r4 s))
          (gc_state_h2_fupd (K (gc_state_h2 s ++ gc_state_h2 s1))
          s1))) = (y,t)`,
  CHEAT_TAC);;

let gc_partial_move_with_NIL_LEMMA = prove
 (`!x s y t h2 r4 y1 t1.
      gen_gc_partial_gc_move gen_conf s x = (y1,t1) /\ gc_state_ok t1
        ==>
      (?x1 x2. gc_state_h2
        t1 = gc_state_h2 s ++ x1 /\ gc_state_r4
        t1 = x2 ++ gc_state_r4 s /\
        gen_gc_partial_gc_move gen_conf (gc_state_r4_fupd (K [])
          (gc_state_h2_fupd (K []) s)) x =
          (y1,gc_state_r4_fupd (K x2) (gc_state_h2_fupd (K x1)
            t1)))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:2935-2955: a theorem that HOL4
   states as the value of an ML expression:
   gc_partial_move_list_with_NIL_LEMMA *)

let gc_partial_move_list_with_NIL = prove
 (`!x s y t.
      gen_gc_partial_gc_move_list gen_conf s x = (y,t) /\ gc_state_ok
        t ==>
      (let (y,s1) = gen_gc_partial_gc_move_list gen_conf
        (gc_state_r4_fupd (K []) (gc_state_h2_fupd (K []) s)) x in
       (y,gc_state_r4_fupd (K (gc_state_r4 s1 ++ gc_state_r4 s))
         (gc_state_h2_fupd (K (gc_state_h2 s ++ gc_state_h2 s1)) s1)))
         = (y,t)`,
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:2967-2989: a theorem that HOL4
   states as the value of an ML expression:
   gc_partial_move_ref_list_with_NIL_LEMMA *)

let gc_partial_move_ref_list_with_NIL = prove
 (`!x s y t.
      gc_move_ref_list gen_conf s x = (y,t) /\ gc_state_ok t ==>
      (let (y,s1) = gc_move_ref_list gen_conf (gc_state_r4_fupd (K
        []) (gc_state_h2_fupd (K []) s)) x in
       (y,gc_state_r4_fupd (K (gc_state_r4 s1 ++ gc_state_r4 s))
         (gc_state_h2_fupd (K (gc_state_h2 s ++ gc_state_h2 s1)) s1)))
         = (y,t)`,
  CHEAT_TAC);;

let word_gen_gc_partial_move_roots_thm = prove
 (`!x xs x1 w s1 s pa1 pa m1 m i1 frame dm curr c1 old current refs.
    (gen_gc_partial_gc_move_list gen_conf s x = (x1,s1)) /\
      gc_state_ok s1 /\ gc_state_h2 s = [] /\ gc_state_r4 s = [] /\
      limit
    gen_conf = heap_length (gc_state_heap s) /\
    heap_length (gc_state_heap s) <= dimword (:'a) DIV 2 EXP
      shift_length conf /\ gen_gc_partial_conf_gen_start
    gen_conf <= gen_gc_partial_conf_refs_start gen_conf /\
      gen_gc_partial_conf_refs_start
    gen_conf <= heap_length (gc_state_heap s) /\
    (heap_segment (gen_gc_partial_conf_gen_start
      gen_conf,gen_gc_partial_conf_refs_start gen_conf) (gc_state_heap
      s) = SOME (old,current,refs)) /\
    (!t r. (isRef gen_conf (t,r) <=> isMutTag t)) /\
    heap_length (gc_state_heap s) * (dimindex (:'a) DIV 8) < dimword
      (:'a) /\
    (word_heap (curr + bytes_in_word * n2w (heap_length old)) current
      conf * misc_word_list pa xs * frame) (fun2set (m,dm)) /\
    (word_gen_gc_partial_move_roots conf (MAP (word_addr conf) x,n2w
      (gc_state_a s),pa,
                              (curr:'a word),m,dm,
                              bytes_in_word * n2w
                                (gen_gc_partial_conf_gen_start
                                gen_conf),
                              bytes_in_word * n2w
                                (gen_gc_partial_conf_refs_start
                                gen_conf)) =
      ((w:('a word_loc) list),i1,pa1,m1,c1)) /\
    LENGTH xs = gc_state_n s /\ good_dimindex (:'a) ==>
    (?xs1 current1.
      (word_heap (curr + bytes_in_word * n2w (heap_length old))
        current1 conf *
       word_heap pa (gc_state_h2 s1) conf *
       misc_word_list pa1 xs1 * frame) (fun2set (m1,dm)) /\
      (w = MAP (word_addr conf) x1) /\
      heap_length (gc_state_heap s1) = heap_length (gc_state_heap s)
        /\
      (heap_segment (gen_gc_partial_conf_gen_start
        gen_conf,gen_gc_partial_conf_refs_start gen_conf) (gc_state_heap
        s1) = SOME (old,current1,refs)) /\
      c1 /\ (i1 = n2w (gc_state_a s1)) /\ gc_state_n s1 = LENGTH xs1
        /\ gc_state_n
      s = heap_length (gc_state_h2 s1) + gc_state_n s1 + heap_length
        (gc_state_r4 s1) /\
      pa1 = pa + bytes_in_word * n2w (heap_length (gc_state_h2
        s1)))`,
  CHEAT_TAC);;

let word_gen_gc_partial_move_list_thm = prove
 (`!x xs x1 s1 s pa1 pa m1 m i1 frame dm curr c1 k old current refs.
    (gen_gc_partial_gc_move_list gen_conf s x = (x1,s1)) /\
      gc_state_ok s1 /\ gc_state_h2 s = [] /\ gc_state_r4 s = [] /\
      limit
    gen_conf = heap_length (gc_state_heap s) /\
    heap_length (gc_state_heap s) <= dimword (:'a) DIV 2 EXP
      shift_length conf /\ gen_gc_partial_conf_gen_start
    gen_conf <= gen_gc_partial_conf_refs_start gen_conf /\
      gen_gc_partial_conf_refs_start
    gen_conf <= heap_length (gc_state_heap s) /\
    (heap_segment (gen_gc_partial_conf_gen_start
      gen_conf,gen_gc_partial_conf_refs_start gen_conf) (gc_state_heap
      s) = SOME (old,current,refs)) /\
    (!t r. (isRef gen_conf (t,r) <=> isMutTag t)) /\
    heap_length (gc_state_heap s) * (dimindex (:'a) DIV 8) < dimword
      (:'a) /\
    (word_heap (curr + bytes_in_word * n2w (heap_length old)) current
      conf * misc_word_list pa xs *
     misc_word_list k (MAP (word_addr conf) x) * frame) (fun2set
       (m,dm)) /\
    (word_gen_gc_partial_move_list conf (k,n2w (LENGTH x),n2w
      (gc_state_a s),pa,
                              (curr:'a word),m,dm,
                              bytes_in_word * n2w
                                (gen_gc_partial_conf_gen_start
                                gen_conf),
                              bytes_in_word * n2w
                                (gen_gc_partial_conf_refs_start
                                gen_conf)) =
      (k1,i1,pa1,m1,c1)) /\
    LENGTH xs = gc_state_n s /\ good_dimindex (:'a) /\ LENGTH x <
      dimword (:'a) ==>
    (?xs1 current1.
      (word_heap (curr + bytes_in_word * n2w (heap_length old))
        current1 conf *
       word_heap pa (gc_state_h2 s1) conf *
       misc_word_list pa1 xs1 *
       misc_word_list k (MAP (word_addr conf) x1) *
       frame) (fun2set (m1,dm)) /\
      heap_length (gc_state_heap s1) = heap_length (gc_state_heap s)
        /\
      (heap_segment (gen_gc_partial_conf_gen_start
        gen_conf,gen_gc_partial_conf_refs_start gen_conf) (gc_state_heap
        s1) = SOME (old,current1,refs)) /\
      c1 /\ (i1 = n2w (gc_state_a s1)) /\ gc_state_n s1 = LENGTH xs1
        /\ gc_state_n
      s = heap_length (gc_state_h2 s1) + gc_state_n s1 + heap_length
        (gc_state_r4 s1) /\
      k1 = k + n2w (LENGTH x) * bytes_in_word /\
      pa1 = pa + bytes_in_word * n2w (heap_length (gc_state_h2
        s1)))`,
  CHEAT_TAC);;

let gc_partial_move_heap_lengths = prove
 (`gen_gc_partial_gc_move gen_conf s x = (x1,s1) /\ gc_state_ok s1 ==>
  gc_state_n
    s + heap_length (gc_state_h2 s) = gc_state_n s1 + heap_length
      (gc_state_h2 s1)`,
  CHEAT_TAC);;

let gc_partial_move_list_heap_lengths = prove
 (`!x gen_conf s x1 s1. gen_gc_partial_gc_move_list gen_conf s x =
  (x1,s1) /\ gc_state_ok s1 ==> gc_state_n
     s + heap_length (gc_state_h2 s) = gc_state_n s1 + heap_length
       (gc_state_h2 s1)`,
  CHEAT_TAC);;

let partial_len_inv_def = new_definition
  `partial_len_inv s <=>
     heap_length (gc_state_heap s) =
     heap_length (gc_state_h1 s ++ gc_state_h2 s) + gc_state_n s +
       heap_length (gc_state_r4 s ++ gc_state_r3 s ++ gc_state_r2 s
       ++ gc_state_r1 s ++ gc_state_old s)`;;

let word_gen_gc_partial_move_data_thm = prove
 (`!k s m dm curr xs s1 pa1 m1 i1 frame c1 old current refs.
    (gen_gc_partial_gc_move_data gen_conf s = s1) /\ gc_state_ok s1
      /\ limit
    gen_conf = heap_length (gc_state_heap s) /\
    heap_length (gc_state_heap s) <= dimword (:'a) DIV 2 EXP
      shift_length conf /\
    heap_length (gc_state_heap s) * (dimindex (:'a) DIV 8) < dimword
      (:'a) /\ gen_gc_partial_conf_gen_start
    gen_conf <= gen_gc_partial_conf_refs_start gen_conf /\
      gen_gc_partial_conf_refs_start
    gen_conf <= heap_length (gc_state_heap s) /\
    (heap_segment (gen_gc_partial_conf_gen_start
      gen_conf,gen_gc_partial_conf_refs_start gen_conf) (gc_state_heap
      s) = SOME (old,current,refs)) /\ data_to_word_config_len_size
    conf + 2 < dimindex (:'a) /\
    (!t r. (isRef gen_conf (t,r) <=> isMutTag t)) /\
    (word_gen_gc_partial_move_data conf k
       (
         // h2a
         p + bytes_in_word * n2w (heap_length (gc_state_h1 s)),
        n2w (gc_state_a s),
         // pa
         p + bytes_in_word * n2w (heap_length (gc_state_h1 s ++
           gc_state_h2 s)),
        (curr:'a word),m,dm,
        bytes_in_word * n2w (gen_gc_partial_conf_gen_start gen_conf),
        bytes_in_word * n2w (gen_gc_partial_conf_refs_start
          gen_conf)) =
      (i1,pa1,m1,c1)) /\
    heap_length (gc_state_h2 s) + gc_state_n s <= k /\
      partial_len_inv s /\
    (word_heap (curr + bytes_in_word * n2w (heap_length old)) current
      conf *
     word_heap p (gc_state_h1 s ++ gc_state_h2 s) conf *
     misc_word_list (p + bytes_in_word * n2w (heap_length
       (gc_state_h1 s ++ gc_state_h2 s))) xs *
     frame) (fun2set (m,dm)) /\
    EVERY (is_Ref (isRef gen_conf)) (gc_state_r4 s ++ gc_state_r3 s
      ++ gc_state_r2 s ++ gc_state_r1 s) /\
    LENGTH xs = gc_state_n s /\ good_dimindex (:'a) ==>
    (?xs1 current1.
      (word_heap (curr + bytes_in_word * n2w (heap_length old))
        current1 conf *
       word_heap p (gc_state_h1 s1 ++ gc_state_h2 s1) conf *
       misc_word_list (p + bytes_in_word * n2w (heap_length
         (gc_state_h1 s1 ++ gc_state_h2 s1))) xs1 *
       frame) (fun2set (m1,dm)) /\ gc_state_h2 s1 = [] /\
      heap_length (gc_state_heap s1) = heap_length (gc_state_heap s)
        /\
      (heap_segment (gen_gc_partial_conf_gen_start
        gen_conf,gen_gc_partial_conf_refs_start gen_conf) (gc_state_heap
        s1) = SOME (old,current1,refs)) /\
      c1 /\ (i1 = n2w (gc_state_a s1)) /\ gc_state_n
      s1 = LENGTH xs1 /\ partial_len_inv s1 /\
      heap_length (gc_state_h1 s1 ++ gc_state_h2 s1 ++ gc_state_r4
        s1) + gc_state_n s1 =
      heap_length (gc_state_h1 s ++ gc_state_h2 s ++ gc_state_r4 s) +
        gc_state_n s /\
      pa1 = p + bytes_in_word * n2w (heap_length (gc_state_h1 s1 ++
        gc_state_h2 s1)) /\
      EVERY (is_Ref (isRef gen_conf)) (gc_state_r4 s1 ++
        gc_state_r3 s1 ++ gc_state_r2 s1 ++ gc_state_r1 s1))`,
  CHEAT_TAC);;

let word_gen_gc_partial_move_ref_list_thm = prove
 (`!x ck xs x1 s1 s pa1 pa m1 m i1 frame dm curr c1 k old current refs.
    (gc_move_ref_list gen_conf s x = (x1,s1)) /\ gc_state_ok s1 /\
      gc_state_h2 s = [] /\ gc_state_r4 s = [] /\
    heap_length x <= ck /\ limit
    gen_conf = heap_length (gc_state_heap s) /\
    heap_length (gc_state_heap s) <= dimword (:'a) DIV 2 EXP
      shift_length conf /\ gen_gc_partial_conf_gen_start
    gen_conf <= gen_gc_partial_conf_refs_start gen_conf /\
      gen_gc_partial_conf_refs_start
    gen_conf <= heap_length (gc_state_heap s) /\
    heap_segment (gen_gc_partial_conf_gen_start
      gen_conf,gen_gc_partial_conf_refs_start gen_conf) (gc_state_heap
      s) = SOME (old,current,refs) /\
    heap_length x <= heap_length (gc_state_heap s) /\
    EVERY data_to_word_memoryProof_isRef x /\
    (!t r. (isRef gen_conf (t,r) <=> isMutTag t)) /\
    heap_length (gc_state_heap s) * (dimindex (:'a) DIV 8) < dimword
      (:'a) /\
    (word_heap (curr + bytes_in_word * n2w (heap_length old)) current
      conf * misc_word_list pa xs *
     word_heap k x conf * frame) (fun2set (m,dm)) /\
    (word_gen_gc_partial_move_ref_list ck conf (k,n2w (gc_state_a
      s),pa,
                              (curr:'a word),m,dm,T,
                              bytes_in_word * n2w
                                (gen_gc_partial_conf_gen_start
                                gen_conf),
                              bytes_in_word * n2w
                                (gen_gc_partial_conf_refs_start
                                gen_conf),
                              k + bytes_in_word * n2w (heap_length
                                x)) =
      (i1,pa1,m1,c1)) /\
    LENGTH xs = gc_state_n s /\ good_dimindex (:'a) /\ LENGTH x <
      dimword (:'a) ==>
    (?xs1 current1.
      (word_heap (curr + bytes_in_word * n2w (heap_length old))
        current1 conf *
       word_heap pa (gc_state_h2 s1) conf *
       misc_word_list pa1 xs1 *
       word_heap k x1 conf *
       frame) (fun2set (m1,dm)) /\
      heap_segment (gen_gc_partial_conf_gen_start
        gen_conf,gen_gc_partial_conf_refs_start gen_conf) (gc_state_heap
        s1) = SOME (old,current1,refs) /\
      heap_length (gc_state_heap s1) = heap_length (gc_state_heap s)
        /\
      c1 /\ (i1 = n2w (gc_state_a s1)) /\ gc_state_n s1 = LENGTH xs1
        /\
      EVERY data_to_word_memoryProof_isRef x1 /\ gc_state_n
      s = heap_length (gc_state_h2 s1) + gc_state_n s1 + heap_length
        (gc_state_r4 s1) /\
   pa1 = pa + bytes_in_word * n2w (heap_length (gc_state_h2 s1)))`,
  CHEAT_TAC);;

(* gc_move_ref_list_IMP[local] *)
let data_to_word_gcProof_gc_move_ref_list_IMP = prove
 (`!conf state refs state1 refs1.
   (gc_move_ref_list conf state refs = (refs1,state1)) ==>
   (gc_state_old state1 = gc_state_old state) /\
   (gc_state_h1 state1 = gc_state_h1 state) /\
   (gc_state_r1 state1 = gc_state_r1 state) /\
   (gc_state_r2 state1 = gc_state_r2 state) /\
   (gc_state_r3 state1 = gc_state_r3 state) /\
   (gc_state_r4 state1 = gc_state_r4 state) /\
   (heap_length refs = heap_length refs1) /\
   (!ptr.
      isSomeDataElement (heap_lookup ptr refs) ==>
      isSomeDataElement (heap_lookup ptr refs1))`,
  CHEAT_TAC);;

let heap_length_LENGTH = prove
 (`LENGTH x <= heap_length x`,
  CHEAT_TAC);;

let partial_gc_move_ref_list_isRef = prove
 (`!refs s refs' state'.
   gc_move_ref_list gen_conf s refs = (refs',state') ==> EVERY
     (is_Ref (isRef gen_conf)) refs' = EVERY (is_Ref (isRef gen_conf))
     refs`,
  CHEAT_TAC);;

let EVERY_is_Ref_isRef = prove
 (`(!t r. f (t,r) <=> isMutTag t) ==> EVERY (is_Ref f) refs = EVERY
  data_to_word_memoryProof_isRef refs`,
  CHEAT_TAC);;

let ends_with_refs_def = new_definition
  `ends_with_refs rs heap =
     (?h1 h2. heap_split rs heap = SOME (h1,h2) /\ EVERY
       data_to_word_memoryProof_isRef h2)`;;

let word_gen_gc_partial_thm = prove
 (`!m dm curr s1 pa1 m1 i1 frame c1 roots heap roots1 roots1' new.
     (partial_gc gen_conf (roots,heap) = (roots1,s1)) /\ gc_state_ok
       s1 /\
     heap_length heap <= dimword (:'a) DIV 2 EXP shift_length conf /\
     heap_length heap * (dimindex (:'a) DIV 8) < dimword (:'a) /\
       limit
     gen_conf = heap_length heap /\ gen_gc_partial_conf_gen_start
     gen_conf <= gen_gc_partial_conf_refs_start gen_conf /\
       gen_gc_partial_conf_refs_start
     gen_conf <= heap_length heap /\
     ends_with_refs (gen_gc_partial_conf_refs_start gen_conf) heap /\
     heap_length heap * (dimindex (:'a) DIV 8) < dimword (:'a) /\
       data_to_word_config_len_size
     conf + 2 < dimindex (:'a) /\
     (!t r. (isRef gen_conf (t,r) <=> isMutTag t)) /\
     (word_gen_gc_partial conf (MAP (word_addr conf) roots,curr,new,
                              bytes_in_word * n2w (heap_length
                                heap),m,dm,
                              bytes_in_word * n2w
                                (gen_gc_partial_conf_gen_start
                                gen_conf),
                              bytes_in_word * n2w
                                (gen_gc_partial_conf_refs_start
                                gen_conf)) = (roots1',i1,(pa1:'a
                                word),m1,c1)) /\
     (word_heap curr heap conf *
      word_list_exists new (gen_gc_partial_conf_refs_start gen_conf -
        gen_gc_partial_conf_gen_start gen_conf) *
      frame) (fun2set (m,dm)) /\ good_dimindex (:'a) ==>
     (?xs1 current1 refs1.
      (word_heap curr (gc_state_old s1 ++ current1 ++ gc_state_r1 s1)
        conf *
        word_heap new (gc_state_h1 s1) conf *
        misc_word_list (new + bytes_in_word * n2w (heap_length
          (gc_state_h1 s1))) xs1 *
        frame) (fun2set (m1,dm)) /\ gc_state_h2
       s1 = [] /\ gc_state_r4 s1 = [] /\ gc_state_r3 s1 = [] /\
         gc_state_r2 s1 = [] /\
       roots1' = MAP (word_addr conf) roots1 /\
       heap_length (gc_state_heap s1) = heap_length heap /\
       heap_segment (gen_gc_partial_conf_gen_start
         gen_conf,gen_gc_partial_conf_refs_start gen_conf)
         (gc_state_heap s1) = SOME (gc_state_old s1,current1,refs1) /\
       c1 /\ (i1 = n2w (gc_state_a s1)) /\ pa1 = new + bytes_in_word
         * n2w (heap_length (gc_state_h1 s1)) /\ gc_state_n
       s1 = LENGTH xs1 /\ partial_len_inv s1 /\ heap_length
         (gc_state_h1 s1) <= heap_length current1 /\
       heap_length (gc_state_h1 s1) + LENGTH xs1 +
         gen_gc_partial_conf_gen_start gen_conf =
         gen_gc_partial_conf_refs_start gen_conf /\
       EVERY (is_Ref (isRef gen_conf)) (gc_state_r1 s1))`,
  CHEAT_TAC);;

let word_gen_gc_partial_full_thm = prove
 (`!m dm curr s1 pa1 m1 i1 frame c1 roots heap roots1 roots1' new.
    (partial_gc gen_conf (roots,heap) = (roots1,s1)) /\ gc_state_ok
      s1 /\
    heap_length heap <= dimword (:'a) DIV 2 EXP shift_length conf /\
    heap_length heap * (dimindex (:'a) DIV 8) < dimword (:'a) /\
    ends_with_refs (gen_gc_partial_conf_refs_start gen_conf) heap /\
      limit
    gen_conf = heap_length heap /\ gen_gc_partial_conf_gen_start
    gen_conf <= gen_gc_partial_conf_refs_start gen_conf /\
      gen_gc_partial_conf_refs_start
    gen_conf <= heap_length heap /\
    heap_length heap * (dimindex (:'a) DIV 8) < dimword (:'a) /\
      data_to_word_config_len_size
    conf + 2 < dimindex (:'a) /\
    (!t r. (isRef gen_conf (t,r) <=> isMutTag t)) /\
    (word_gen_gc_partial_full conf (MAP (word_addr conf)
      roots,curr,new,
                              bytes_in_word * n2w (heap_length
                                heap),m,dm,
                              bytes_in_word * n2w
                                (gen_gc_partial_conf_gen_start
                                gen_conf),
                              bytes_in_word * n2w
                                (gen_gc_partial_conf_refs_start
                                gen_conf)) = (roots1',i1,(pa1:'a
                                word),m1,c1)) /\
    (word_heap curr heap conf *
     word_list_exists new (heap_length heap) *
     frame) (fun2set (m,dm)) /\ good_dimindex (:'a) ==>
    (?current1 refs1.
      (word_heap curr (gc_state_old s1) conf *
       word_heap (curr + bytes_in_word * n2w (heap_length
         (gc_state_old s1))) (gc_state_h1 s1) conf *
       word_list_exists pa1 (gc_state_n s1) *
       word_heap (pa1 + bytes_in_word * n2w (gc_state_n s1))
         (gc_state_r1 s1) conf *
       word_list_exists new (heap_length heap) *
       frame) (fun2set (m1,dm)) /\ gc_state_h2
      s1 = [] /\ gc_state_r4 s1 = [] /\ gc_state_r3 s1 = [] /\
        gc_state_r2 s1 = [] /\
      roots1' = MAP (word_addr conf) roots1 /\
      heap_length (gc_state_heap s1) = heap_length heap /\
      heap_segment (gen_gc_partial_conf_gen_start
        gen_conf,gen_gc_partial_conf_refs_start gen_conf) (gc_state_heap
        s1) = SOME (gc_state_old s1,current1,refs1) /\
      c1 /\ (i1 = n2w (gc_state_a s1)) /\ pa1 = curr + bytes_in_word
        * n2w (heap_length (gc_state_old s1 ++ gc_state_h1 s1)) /\
      partial_len_inv s1 /\
      EVERY (is_Ref (isRef gen_conf)) (gc_state_r1 s1))`,
  CHEAT_TAC);;

let gen_starts_in_store_IMP_SOME_Word = prove
 (`gen_starts_in_store c gens x ==> (?w. x = SOME (wordLang_Word w))`,
  CHEAT_TAC);;

let glob_real_inv = prove
 (`glob_real_inv c other (SOME w) (SOME (glob_real c other w)) <=>
  isWord w`,
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:3819-3873: a theorem that HOL4
   states as the value of an ML expression: word_gc_fun_lemma_Simple *)

let do_partial_def = new_definition
  `do_partial c s =
     (match data_to_word_config_gc_kind c with
       data_to_word_Generational l -> word_gen_gc_can_do_partial l s
       | _15 -> F)`;;

let heap_segment_IMP_split = prove
 (`heap_segment (m,n) heap = SOME (x1,x2,x3) ==>
    heap_split m heap = SOME (x1,x2 ++ x3) /\
    heap_split n heap = SOME (x1 ++ x2,x3)`,
  CHEAT_TAC);;

let heap_split_IMP_heap_length = prove
 (`!heap n h1 h2.
      heap_split n heap = SOME (h1,h2) ==>
      heap_length h1 = n`,
  CHEAT_TAC);;

let heap_split_APPEND_EQ = prove
 (`!h1 h2 a.
      heap_split a (h1 ++ h2) = SOME (h1,h2) <=>
      a = heap_length h1`,
  CHEAT_TAC);;

let heap_split_IMP_APPEND = prove
 (`!heap n h1 h2. heap_split n heap = SOME (h1,h2) ==> heap = h1 ++ h2`,
  CHEAT_TAC);;

let heap_length_nil = prove
 (`heap_length m = 0 <=> m = []`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let abs_ml_inv_GenState_IMP_heap_length_FILTER = prove
 (cake_as_vars (fun () ->
    `abs_ml_inv c stack refs
          (xs,heap,be,a,sp,sp1,GenState n (t :: ts))
          (heap_length heap) tss /\ data_to_word_config_gc_kind
      c = data_to_word_Generational (y :: ys) /\
      heap_split (a + sp + sp1) heap = SOME (h1,h2) ==>
      EVERY isDataElement h2 /\
      heap_length (FILTER isDataElement heap) = a + heap_length
        h2`),
  CHEAT_TAC);;

(* [local] *)
let new_trig_ok = prove
 (`a <=+ (bytes_in_word * n2w n) /\ good_dimindex (:'a) ==>
   a <=+ new_trig (bytes_in_word * ((n2w n):'a word)) a x`,
  CHEAT_TAC);;

let byte_aligned_IMP_bytes_in_word = prove
 (`byte_aligned w /\ good_dimindex (:'a) ==> (?v. w = bytes_in_word *
  (v:'a word))`,
  CHEAT_TAC);;

let MULT_bytes_in_word_LESS_EQ_IMP = prove
 (`w2n (k * (bytes_in_word:'a word)) <= w2n (bytes_in_word * (n2w n:'a
  word)) /\
    good_dimindex (:'a) ==>
    (?l. k * bytes_in_word = n2w l * bytes_in_word /\ l <= n)`,
  CHEAT_TAC);;

(* [local] *)
let new_trig_LESS_EQ = prove
 (`good_dimindex (:'a) ==>
   (?k. new_trig (bytes_in_word * ((n2w n):'a word)) a22 a33 =
       bytes_in_word * n2w k /\ k <= n)`,
  CHEAT_TAC);;

let alloc_size_def = new_definition
  `alloc_size k = ((if k * (dimindex (:'a) DIV 8) < dimword (:'a) then
                     n2w (k * (dimindex (:'a) DIV 8)) else (--(n2w
                       1))):'a word)`;;

(* HOL4 data_to_word_gcProofScript.sml:4045-4319: a theorem that HOL4
   states as the value of an ML expression: word_gc_fun_lemma *)

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let abs_ml_inv_ADD = prove
 (cake_as_vars (fun () ->
    `abs_ml_inv c xs refs (ys,heap2,be,a2,k2 + k3,0,gens2) limit ts /\
  data_to_word_config_gc_kind
     c = data_to_word_Generational l ==>
     abs_ml_inv c xs refs (ys,heap2,be,a2,k2,k3,gens2) limit ts`),
  CHEAT_TAC);;

let alloc_size_check = prove
 (`w2n (bytes_in_word * (n2w k2:'a word)) < w2n (alloc_size k:'a word)
  ==>
   k2 * (dimindex (:'a) DIV 8) < dimword (:'a) /\ good_dimindex (:'a)
     ==>
   k2 < k`,
  CHEAT_TAC);;

let alloc_size_LEQ_IMP = prove
 (`alloc_size k <=+ bytes_in_word * (n2w sp1:'a word) /\
   sp1 * (dimindex (:'a) DIV 8) < dimword (:'a) /\
   good_dimindex (:'a) ==> k <= sp1`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_gc_fun_correct = prove
 (cake_as_vars (fun () ->
    `good_dimindex (:'a) /\
      heap_in_memory_store heap a sp sp1 gens c s m dm limit /\
      word_ml_inv ((heap:(('a
        word_loc,data_to_word_memoryProof_tag#('a word_loc)
        list)heap_element) list),be,a,sp,sp1,gens) limit ts c refs
        ((v,FAPPLY s Globals) :: stack) ==>
      (?stack1 m1 s1 heap1 a1 sp1 sp2 gens2 v1 xs.
        word_gc_fun c (MAP SND stack,m,dm,s) = SOME (stack1,m1,s1)
          /\
        heap_in_memory_store heap1 a1 sp1 sp2 gens2 c s1 m1 dm
          limit /\
        abs_ml_inv c (v :: MAP FST (ZIP (MAP FST stack) stack1))
          refs
          (v1 :: xs,heap1,be,a1,sp1,sp2,gens2) limit ts /\
        word_addr c v1 = FAPPLY s1 Globals /\
        LIST_REL (\v w. word_addr c v = w) xs
          (MAP SND (ZIP (MAP FST stack) stack1)) /\
        (FLOOKUP s AllocSize = SOME (wordLang_Word (alloc_size k))
          /\
         wordSem_has_space (wordLang_Word ((alloc_size k):'a word))
           (wordSem_state_store_fupd (K s1) t) = SOME F /\
           ~(data_to_word_config_gc_kind
         c = None) ==>
           sp1 + sp2 < k /\
           all_reachable_from_roots (v1 :: xs) heap1 /\
           heap_length heap1 = data_length heap1 + sp1 + sp2))`),
  CHEAT_TAC);;

(* -------------------------------------------------------
    definition of state relation
   ------------------------------------------------------- *)

let data_to_word_gcProof_code_rel_def = new_definition
  `data_to_word_gcProof_code_rel c s_code (t_code:(num#'a wordLang_prog)
  spt) <=>
     domain t_code = domain s_code UNION set_of_list (MAP FST
       (data_to_word_stubs (:'a) c)) /\
     EVERY (\(n,x). sptree_lookup n t_code = SOME x)
       (data_to_word_stubs (:'a) c) /\
     (!n arg_count prog.
       (sptree_lookup n s_code = SOME ((arg_count:num),prog)) ==>
       (sptree_lookup n t_code = SOME (arg_count + 1,FST
         (data_to_word_comp c n 2 prog))))`;;
hol4_overload "code_rel" "data_to_word_gcProof_code_rel";;

let stack_rel_def,stack_rel_ind = define_guess
  [`data_to_word_gcProof_stack_rel x1 x2 =
        match (x1,x2) with
          ((Env s1 env:dataSem_stack),StackFrame s2 ws vs NONE) ->
        EVERY (\(x1,x2). ~(x1 = 0) /\ EVEN x1) vs /\ s1 = s2 /\
        EVERY (\(x1,x2). x1 = 0) ws /\
        ALL_DISTINCT (MAP FST vs) /\
        (!n. IS_SOME (sptree_lookup n env) <=>
            IS_SOME (sptree_lookup (adjust_var n) (fromAList vs)))
        | ((dataSem_Exc s1 env n),(StackFrame s2 ws vs (SOME
          (x1,x2,x3)))) ->
        data_to_word_gcProof_stack_rel (Env s1 env) (StackFrame s2
          ws vs NONE) /\ (x1 = n)
        | (_16,_17) -> F`];;
hol4_overload "stack_rel" "data_to_word_gcProof_stack_rel";;

let the_global_def = new_definition
  `the_global g = the (Number (&0)) (OPTION_MAP (RefPtr T) g)`;;

let contains_loc_def = define_general
  [`contains_loc (StackFrame _18 vs _19 _20) (l1,l2) = (ALOOKUP vs 0
  = SOME (Loc l1 l2))`];;

let code_oracle_rel_def = new_definition
  `code_oracle_rel c (s_compile:'c->(num#num#dataLang_prog) list->(word8
  list#word64 list#'c) option)
       s_compile_oracle t_store (t_compile:'c->(num#num#'a
         wordLang_prog) list->(word8 list#('a word) list#'c) option)
       t_compile_oracle t_code_buffer t_data_buffer <=> buffer_buffer
     t_code_buffer = [] /\ buffer_buffer
     t_data_buffer = [] /\
     FLOOKUP t_store CodeBuffer = SOME (wordLang_Word
       (buffer_position t_code_buffer)) /\
     FLOOKUP t_store CodeBufferEnd =
       SOME (wordLang_Word (buffer_position t_code_buffer + n2w
         (buffer_space_left t_code_buffer))) /\
     FLOOKUP t_store BitmapBuffer = SOME (wordLang_Word
       (buffer_position t_data_buffer)) /\
     FLOOKUP t_store BitmapBufferEnd =
       SOME (wordLang_Word (buffer_position t_data_buffer +
                   bytes_in_word * n2w (buffer_space_left
                     t_data_buffer))) /\
     s_compile = (\cfg. OPTION_MAP (I ## MAP upper_w2w ## I) o
       t_compile cfg o
                        MAP (data_to_word_compile_part c)) /\
     t_compile_oracle = (I ## MAP (data_to_word_compile_part c)) o
       s_compile_oracle /\
     (!n. EVERY (\(n,_21). data_num_stubs <= n) (SND
       (s_compile_oracle n)))`;;

(* [simp] *)
let code_oracle_rel_NextFree = prove
 (`code_oracle_rel c scc sco (ts |+ (NextFree,x)) tcc tco cb db <=>
   code_oracle_rel c scc sco ts tcc tco cb db`,
  CHEAT_TAC);;

let limits_inv_def = new_definition
  `limits_inv (lims:limits) heaplength t_stack_limit c_len_size
  c_has_fp_ops c_has_fp_tern <=> limits_stack_limit
     lims = t_stack_limit /\ limits_length_limit
     lims = c_len_size /\ limits_arch_64_bit
     lims = (dimindex (:'a) = 64) /\
     heaplength = SOME (wordLang_Word (bytes_in_word * (n2w
       (limits_heap_limit lims):'a word))) /\ limits_heap_limit
     lims * w2n (bytes_in_word:'a word) < dimword (:'a) /\
       limits_has_fp_ops
     lims = c_has_fp_ops /\ limits_has_fp_tops
     lims = c_has_fp_tern`;;

(* HOL4 data_to_word_gcProofScript.sml:4501: the ML values that the
   definitions below antiquote *)

let state_rel_thm = assume_definition
  "free: memory_rel:data_to_word_config->bool->num->((dataSem_v"
  [`data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
  (t:('a,'c,'ffi)wordSem_state) v1 locs <=>
     (wordSem_state_ffi
      // I/O, clock and handler are the same, GC is fixed, code is compiled
      t = dataSem_state_ffi s) /\
     (wordSem_state_clock t = dataSem_state_clock s) /\
     (wordSem_state_handler t = dataSem_state_handler s) /\
     (wordSem_state_gc_fun t = word_gc_fun c) /\
     code_rel c (dataSem_state_code s) (wordSem_state_code t) /\
     code_oracle_rel c (dataSem_state_compile s)
       (dataSem_state_compile_oracle s) (wordSem_state_store t)
       (wordSem_state_compile
       t) (wordSem_state_compile_oracle t)
         (wordSem_state_code_buffer t) (wordSem_state_data_buffer t) /\
     good_dimindex (:'a) /\
     shift_length c < dimindex (:'a) /\
     IS_SOME (dataSem_state_tstamps s) /\
     // the store
     EVERY (\n. n IN FDOM (wordSem_state_store t)) [Globals] /\
     (
      // every local is represented in word lang
      v1 = NONE ==> sptree_lookup 0 (wordSem_state_locals t) = SOME
        (Loc l1 l2)) /\
     (!n. IS_SOME (sptree_lookup n (dataSem_state_locals s)) ==>
          IS_SOME (sptree_lookup (adjust_var n)
            (wordSem_state_locals t))) /\
     // the stacks contain the same names, have same shape
     EVERY2 data_to_word_gcProof_stack_rel (dataSem_state_stack s)
       (wordSem_state_stack t) /\
     EVERY2 contains_loc (wordSem_state_stack t) locs /\
     option_le (OPTION_MAP2 (+) (stack_size (wordSem_state_stack t))
       (wordSem_state_locals_size t)) (wordSem_state_stack_max t) /\
     option_le (wordSem_state_stack_max t) (dataSem_state_stack_max
       s) /\ wordSem_state_stack_size
     t = dataSem_state_stack_frame_sizes s /\
       wordSem_state_locals_size
     t = dataSem_state_locals_size s /\
     limits_inv (dataSem_state_limits s) (FLOOKUP
       (wordSem_state_store t) HeapLength) (wordSem_state_stack_limit
       t) (data_to_word_config_len_size c) (has_fp_ops c)
       (data_to_word_config_has_fp_tern c) /\
     // there exists some GC-compatible abstraction
     memory_rel c (wordSem_state_be t) (THE (dataSem_state_tstamps
       s)) (dataSem_state_refs s) (dataSem_state_space s)
       (wordSem_state_store t) (wordSem_state_memory t)
       (wordSem_state_mdomain t)
       ((match v1 with NONE -> [] | SOME vs -> vs) ++
        join_env (dataSem_state_locals s) (toAList (inter
          (wordSem_state_locals t) (adjust_set (dataSem_state_locals
          s)))) ++
        [(the_global (dataSem_state_global s),FAPPLY
          (wordSem_state_store t) Globals)] ++
        flat (dataSem_state_stack s) (wordSem_state_stack t))`];;
hol4_overload "state_rel" "data_to_word_gcProof_state_rel";;

(* HOL4 data_to_word_gcProofScript.sml:4538-4539: a theorem that HOL4
   states as the value of an ML expression: state_rel_thm *)

(* HOL4 data_to_word_gcProofScript.sml:4541-4542: a theorem that HOL4
   states as the value of an ML expression: state_rel_def *)

(* state_rel_with_clock *)
let data_to_word_gcProof_state_rel_with_clock = prove
 (`state_rel a b c s1 s2 d e ==>
   state_rel a b c (state_clock_fupd (K k) s1) (state_clock_fupd (K
     k) s2) d e`,
  CHEAT_TAC);;

(* the relation places no constraint on the FP registers *)
let state_rel_with_fp_regs = prove
 (`state_rel a b c s1 (s2:('a,'c,'ffi)wordSem_state) d e ==>
   state_rel a b c s1 (wordSem_state_fp_regs_fupd (K f) s2) d e`,
  CHEAT_TAC);;

(* -------------------------------------------------------
    init
   ------------------------------------------------------- *)

let flat_NIL = prove
 (`flat [] xs = []`,
  CHEAT_TAC);;

let init_store_ok_def = new_definition
  `init_store_ok c store m (dm:'a word->bool) code_buffer' data_buffer'
  <=>
     (?limit' curr.
       limit' <= max_heap_limit (:'a) c /\
       FLOOKUP store Globals = SOME (wordLang_Word (n2w 0)) /\
       FLOOKUP store GlobReal = SOME (wordLang_Word curr) /\
       FLOOKUP store GenStart = SOME (wordLang_Word (n2w 0)) /\
       FLOOKUP store CurrHeap = SOME (wordLang_Word curr) /\
       FLOOKUP store OtherHeap = FLOOKUP store EndOfHeap /\
       FLOOKUP store NextFree = SOME (wordLang_Word curr) /\
       FLOOKUP store EndOfHeap =
         SOME (wordLang_Word (curr + bytes_in_word * n2w limit')) /\
       FLOOKUP store TriggerGC =
         SOME (wordLang_Word (match data_to_word_config_gc_kind c
           with data_to_word_Generational _22 -> curr | _23 -> curr +
           bytes_in_word * n2w limit')) /\
       FLOOKUP store HeapLength =
         SOME (wordLang_Word (bytes_in_word * n2w limit')) /\
       FLOOKUP store CodeBuffer = SOME (wordLang_Word
         (buffer_position code_buffer')) /\
       FLOOKUP store CodeBufferEnd =
         SOME (wordLang_Word (buffer_position code_buffer' + n2w
           (buffer_space_left code_buffer'))) /\
       FLOOKUP store BitmapBuffer = SOME (wordLang_Word
         (buffer_position data_buffer')) /\
       FLOOKUP store BitmapBufferEnd = SOME
         (wordLang_Word (buffer_position data_buffer' +
                bytes_in_word * n2w (buffer_space_left
                  data_buffer'))) /\ buffer_buffer
       code_buffer' = [] /\ buffer_buffer
       data_buffer' = [] /\
       (word_list_exists curr (limit' + limit')) (fun2set (m,dm)) /\
       byte_aligned curr)`;;

(* [local] *)
let blocks_unique_empty = prove
 (`blocks_unique v (all_vs LN [])`,
  CHEAT_TAC);;

let state_rel_init = prove
 (`wordSem_state_ffi
       t = ffi /\ wordSem_state_handler t = 0 /\ wordSem_state_gc_fun
         t = word_gc_fun c /\
       code_rel c code (wordSem_state_code t) /\
       code_oracle_rel c cc co (wordSem_state_store t)
         (wordSem_state_compile
         t) (wordSem_state_compile_oracle t)
           (wordSem_state_code_buffer t) (wordSem_state_data_buffer t)
           /\
       good_dimindex (:'a) /\
       sptree_lookup 0 (wordSem_state_locals t) = SOME (Loc l1 l2) /\
         wordSem_state_stack
       t = [] /\ wordSem_state_stack_max
       t = SOME 1 /\ wordSem_state_locals_size
       t = SOME 0 /\ wordSem_state_stack_limit
       t = stack_limit lim /\ data_to_word_config_len_size
       c = limits_length_limit lim /\ be
       c = wordSem_state_be t /\
       (limits_arch_64_bit lim <=> dimindex (:'a) = 64) /\
         limits_heap_limit
       lim * w2n (bytes_in_word:'a word) < dimword (:'a) /\ FAPPLY
         (wordSem_state_store
       t) HeapLength = wordLang_Word (bytes_in_word * n2w
         (limits_heap_limit lim)) /\ has_fp_ops
       lim = has_fp_ops c /\ limits_has_fp_tops
       lim = data_to_word_config_has_fp_tern c /\
       conf_ok (:'a) c /\
       init_store_ok c (wordSem_state_store t) (wordSem_state_memory
         t) (wordSem_state_mdomain t) (wordSem_state_code_buffer t)
         (wordSem_state_data_buffer t) ==>
       state_rel c l1 l2 (initial_state ffi code co cc T lim
         (wordSem_state_stack_size t) (wordSem_state_clock t))
                         (t:('a,'c,'ffi)wordSem_state) NONE []`,
  CHEAT_TAC);;

(* -------------------------------------------------------
    compiler proof
   ------------------------------------------------------- *)

(* [simp] *)
let adjust_var_NOT_0 = prove
 (`~(adjust_var n = 0)`,
  CHEAT_TAC);;

let state_rel_get_var_IMP = prove
 (`state_rel c l1 l2 ((s:('c,'ffi)dataSem_state)) t v1 locs ==>
    (get_var n (dataSem_state_locals s) = SOME x) ==>
    (?w. get_var (adjust_var n) t = SOME w)`,
  CHEAT_TAC);;

let state_rel_get_vars_IMP = prove
 (`!n xs.
      state_rel c l1 l2 ((s:('c,'ffi)dataSem_state)) t NONE locs ==>
      (get_vars n (dataSem_state_locals s) = SOME xs) ==>
      (?ws. get_vars (MAP adjust_var n) t = SOME ws /\ (LENGTH xs =
        LENGTH ws))`,
  CHEAT_TAC);;

let state_rel_0_get_vars_IMP = prove
 (`state_rel c l1 l2 ((s:('c,'ffi)dataSem_state)) t NONE locs ==>
    (get_vars n (dataSem_state_locals s) = SOME xs) ==>
    (?ws. get_vars (0 :: MAP adjust_var n) t = SOME ((Loc l1 l2) ::
      ws) /\
         (LENGTH xs = LENGTH ws))`,
  CHEAT_TAC);;

let get_var_T_OR_F = prove
 (`state_rel c l1 l2 ((s:('c,'ffi)dataSem_state))
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    get_var n (dataSem_state_locals s) = SOME x /\
    get_var (adjust_var n) t = SOME w ==> ~(18 MOD dimword (:'a) = 2
      MOD dimword (:'a)) /\
    ((x = Boolv T) ==> (w = wordLang_Word (n2w 18))) /\
    ((x = Boolv F) ==> (w = wordLang_Word (n2w 2)))`,
  CHEAT_TAC);;

let get_var_isT_OR_isF = prove
 (`state_rel c l1 l2 ((s:('c,'ffi)dataSem_state))
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
     get_var n (dataSem_state_locals s) = SOME x /\
     get_var (adjust_var n) t = SOME w ==> ~(18 MOD dimword (:'a) = 2
       MOD dimword (:'a)) /\
     ((isBool T x) ==> (w = wordLang_Word (n2w 18))) /\
     ((isBool F x) ==> (w = wordLang_Word (n2w 2)))`,
  CHEAT_TAC);;

let mk_loc_def = define_general
  [`mk_loc (SOME (t1,d1,d2)) = wordLang_Loc d1 d2`];;

let cut_env_IMP_cut_env = prove
 (`state_rel c l1 l2 ((s:('c,'ffi)dataSem_state)) t NONE locs /\
    dataSem_cut_env r (dataSem_state_locals s) = SOME x ==>
    (?y. wordSem_cut_env (adjust_sets r) (wordSem_state_locals t) =
      SOME y)`,
  CHEAT_TAC);;

let cut_env_IMP_cut_envs = prove
 (`wordSem_cut_env t l = SOME y ==>
   (?y1 y2. cut_envs t l = SOME (y1,y2) /\ y = union y2 y1)`,
  CHEAT_TAC);;

let set_vars_sing = prove
 (`wordSem_set_vars [q] [w] s = set_var q w s`,
  CHEAT_TAC);;

let jump_exc_call_env = prove
 (`wordSem_jump_exc (call_env x y s) =
   jump_exc (state_stack_max_fupd (K
               (OPTION_MAP2 MAX (state_stack_max s)
                 (OPTION_MAP2 (+) (stack_size (stack s)) y))) s)`,
  CHEAT_TAC);;

let jump_exc_dec_clock = prove
 (`mk_loc (wordSem_jump_exc (dec_clock s)) = mk_loc (jump_exc s)`,
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:4836-4838: a theorem that HOL4
   states as the value of an ML expression: LASTN_ADD1 *)

let jump_exc_push_env_NONE = prove
 (`mk_loc (jump_exc (dec_clock s)) =
   mk_loc (jump_exc s) /\
   mk_loc (jump_exc (push_env y NONE s)) =
   mk_loc (jump_exc (s:('a,'c,'ffi)wordSem_state)) /\
   mk_loc (jump_exc (state_stack_max_fupd (K m) (push_env y NONE s)))
     =
   mk_loc (jump_exc (s:('a,'c,'ffi)wordSem_state))`,
  CHEAT_TAC);;

let option_le_stack_size_cons = prove
 (`option_le (stack_size ys) (stack_size (y :: ys))`,
  CHEAT_TAC);;

let option_le_stack_size_append = prove
 (`!xs ys. option_le (stack_size ys) (stack_size (xs ++ ys))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:4878: ML code, not ported *)

(* [local] *)
let is_some_lookup_union = prove
 (`IS_SOME (sptree_lookup n (union t1 t2)) <=>
   IS_SOME (sptree_lookup n t1) \/ IS_SOME (sptree_lookup n t2)`,
  CHEAT_TAC);;

let option_le_tl = prove
 (`option_le (OPTION_MAP2 (+) (stack_size (StackFrame opt ws vs x ::
  ys)) s) t ==>
   option_le (OPTION_MAP2 (+) (stack_size ys) opt) t`,
  CHEAT_TAC);;

let inter_union_lemma = prove
 (`EVERY (\(x1,x2). x1 = 0) ws ==>
   inter (union t (fromAList ws)) (adjust_set s) =
   inter t (adjust_set s)`,
  CHEAT_TAC);;

let state_rel_pop_env_IMP = prove
 (`state_rel c q l ((s1:('c,'ffi)dataSem_state)) t1 xs locs /\
    pop_env s1 = SOME s2 ==>
    (?t2 l8 l9 ll.
      pop_env t1 = SOME t2 /\ locs = (l8,l9) :: ll /\
      state_rel c l8 l9 s2 t2 xs ll)`,
  CHEAT_TAC);;

let inter_insert_union = prove
 (`inter (insert n x (union t1 t2)) s = inter (union (insert n x t1)
  t2) s`,
  CHEAT_TAC);;

let state_rel_pop_env_set_var_IMP = prove
 (`state_rel c q l ((s1:('c,'ffi)dataSem_state)) t1 (SOME [(a,w)]) locs
  /\
    pop_env s1 = SOME s2 ==>
    (?t2 l8 l9 ll.
      pop_env t1 = SOME t2 /\ locs = (l8,l9) :: ll /\
      state_rel c l8 l9 (set_var q1 a s2) (set_var (adjust_var q1)
        w t2) NONE ll)`,
  CHEAT_TAC);;

let BUTLASTN_APPEND_LASTN = prove
 (`!n l. BUTLASTN n l ++ LASTN n l = l`,
  CHEAT_TAC);;

let state_rel_jump_exc = prove
 (`state_rel c l1 l2 ((s:('c,'ffi)dataSem_state))
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    get_var n (dataSem_state_locals s) = SOME x /\
    get_var (adjust_var n) t = SOME w /\
    jump_exc s = SOME s1 ==>
    (?t1 d1 d2 l5 l6 ll.
      jump_exc t = SOME (t1,d1,d2) /\
      LASTN (LENGTH (stack s1) + 1) locs = (l5,l6) :: ll /\
      (!i. state_rel c l5 l6 (set_var i x s1) (set_var (adjust_var
        i) w t1) NONE ll))`,
  CHEAT_TAC);;

(* get_vars_IMP_LENGTH *)
let data_to_word_gcProof_get_vars_IMP_LENGTH = prove
 (`!x t s. dataSem_get_vars x s = SOME t ==> LENGTH x = LENGTH t`,
  CHEAT_TAC);;

let get_vars_IMP_LENGTH_word = prove
 (`!x t s. wordSem_get_vars x s = SOME t ==> LENGTH x = LENGTH t`,
  CHEAT_TAC);;

let lookup_adjust_var_fromList2 = prove
 (`sptree_lookup (adjust_var n) (fromList2 (w :: ws)) = sptree_lookup
  n (fromList ws)`,
  CHEAT_TAC);;

let stack_rel_IMP_size_of_stack = prove
 (`!xs ys.
     LIST_REL data_to_word_gcProof_stack_rel xs ys ==>
     stack_size ys = size_of_stack xs`,
  CHEAT_TAC);;

let state_rel_call_env = prove
 (`get_vars args (dataSem_state_locals ((s:('c,'ffi)dataSem_state))) =
  SOME q /\
   get_vars (MAP adjust_var args) (t:('a,'c,'ffi)wordSem_state) =
     SOME ws /\
   state_rel c l5 l6 s t NONE locs ==>
   state_rel c l1 l2 (call_env q ss (dec_clock s))
     (call_env (Loc l1 l2 :: ws) ss (dec_clock t)) NONE locs`,
  CHEAT_TAC);;

let data_get_vars_SNOC_IMP = prove
 (`!x2 x. dataSem_get_vars (SNOC x1 x2) s = SOME x ==>
              (?y1 y2. x = SNOC y1 y2 /\
                      dataSem_get_var x1 s = SOME y1 /\
                      dataSem_get_vars x2 s = SOME y2)`,
  CHEAT_TAC);;
(* [allow_rebind] *)
let data_to_word_gcProof_data_get_vars_SNOC_IMP =
  data_get_vars_SNOC_IMP;;

let word_get_vars_SNOC_IMP = prove
 (`!x2 x. wordSem_get_vars (SNOC x1 x2) s = SOME x ==>
              (?y1 y2. x = SNOC y1 y2 /\
                 wordSem_get_var x1 s = SOME y1 /\
                 wordSem_get_vars x2 s = SOME y2)`,
  CHEAT_TAC);;
(* [allow_rebind] *)
let data_to_word_gcProof_word_get_vars_SNOC_IMP =
  word_get_vars_SNOC_IMP;;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_ml_inv_CodePtr = prove
 (cake_as_vars (fun () ->
    `word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c (state_refs s)
  ((CodePtr n,v) :: xs) ==>
      (v = Loc n 0)`),
  CHEAT_TAC);;

let state_rel_CodePtr = prove
 (`state_rel c l1 l2 s t NONE locs /\
    get_vars args (state_locals s) = SOME x /\
    get_vars (MAP adjust_var args) t = SOME y /\
    LAST x = CodePtr n /\ ~(x = []) ==> ~(y = []) /\ LAST y = Loc n
      0`,
  CHEAT_TAC);;

let find_code_thm = prove
 (`!s (t:('a,'c,'ffi)wordSem_state).
         state_rel c l1 l2 ((s:('c,'ffi)dataSem_state)) t NONE locs
           /\
         get_vars args (dataSem_state_locals s) = SOME x /\
         get_vars (0 :: MAP adjust_var args) t = SOME (Loc l1 l2 ::
           ws) /\
         find_code dest x (dataSem_state_code s) fs = SOME (q,r,ss)
           ==>
         (?args1 n1 n2.
           find_code dest (Loc l1 l2 :: ws) (wordSem_state_code t) fs
             = SOME (args1,FST (data_to_word_comp c n1 n2 r),ss) /\
           state_rel c l1 l2 (call_env q ss (dec_clock s))
             (call_env args1 ss (dec_clock t)) NONE locs)`,
  CHEAT_TAC);;
(* [allow_rebind] *)
let data_to_word_gcProof_find_code_thm = find_code_thm;;

let cut_env_adjust_set_lookup_0 = prove
 (`cut_envs (adjust_sets r) (wordSem_state_locals t) = SOME y ==>
   sptree_lookup 0 (FST y) = sptree_lookup 0 (wordSem_state_locals
     t)`,
  CHEAT_TAC);;

let cut_env_IMP_MEM = prove
 (`dataSem_cut_env s r = SOME x ==>
    (IS_SOME (sptree_lookup n x) <=> IS_SOME (sptree_lookup n s))`,
  CHEAT_TAC);;

let cut_env_IMP_lookup = prove
 (`wordSem_cut_env s r = SOME x /\ sptree_lookup n x = SOME q ==>
    sptree_lookup n r = SOME q`,
  CHEAT_TAC);;

let cut_env_IMP_lookup_EQ = prove
 (`dataSem_cut_env r y = SOME x /\ n IN domain r ==>
    sptree_lookup n x = sptree_lookup n y`,
  CHEAT_TAC);;

let cut_env_res_IS_SOME_IMP = prove
 (`cut_envs r x = SOME y /\ IS_SOME (sptree_lookup k (SND y)) ==>
    IS_SOME (sptree_lookup k x) /\ IS_SOME (sptree_lookup k (SND
      r))`,
  CHEAT_TAC);;

let adjust_var_cut_env_IMP_MEM = prove
 (`cut_envs (adjust_sets s) r = SOME x ==>
    domain (SND x) SUBSET EVEN /\
    (IS_SOME (sptree_lookup (adjust_var n) (SND x)) <=> IS_SOME
      (sptree_lookup n s))`,
  CHEAT_TAC);;

let NOT_0_domain = prove
 (`~(0 IN domain (adjust_set names))`,
  CHEAT_TAC);;

let cut_envs_SND_nonzero = prove
 (`cut_envs (adjust_sets r) l = SOME y ==>
   sptree_lookup 0 (SND y) = NONE`,
  CHEAT_TAC);;

let lookup_adjust_var_after_cut = prove
 (`sptree_lookup (adjust_var p_1) (SND y) = SOME z1 /\
   cut_envs x l = SOME y /\
   sptree_lookup (adjust_var p_1) l = SOME z2 ==> z1 = z2`,
  CHEAT_TAC);;

let state_rel_call_env_push_opt = prove
 (`!(opt:(num#'a wordLang_prog#num#num) option).
     state_rel c l1 l2 s t (SOME (ZIP xs ws)) locs /\
     sptree_lookup 0 (wordSem_state_locals t) = SOME (Loc l1 l2) /\
     LENGTH xs = LENGTH ws /\
     cut_env r (state_locals s) = SOME x /\
     cut_envs (adjust_sets r) (wordSem_state_locals t) = SOME y ==>
     state_rel c q l
       (call_env xs ss (push_env x (IS_SOME opt) (dec_clock s)))
       (call_env (Loc q l :: ws) ss (push_env y opt (dec_clock t)))
         NONE
       ((l1,l2) :: locs)`,
  CHEAT_TAC);;

let state_rel_call_env_push = prove
 (`state_rel c l1 l2 s t (SOME (ZIP xs ws)) locs /\
   LENGTH xs = LENGTH ws /\
   sptree_lookup 0 (wordSem_state_locals t) = SOME (Loc l1 l2) /\
   cut_env r (state_locals s) = SOME x /\
   cut_envs (adjust_sets r) (wordSem_state_locals t) = SOME y ==>
   state_rel c q l
     (call_env xs ss (push_env x F (dec_clock s)))
     (call_env (Loc q l :: ws) ss (push_env y NONE (dec_clock t)))
       NONE
     ((l1,l2) :: locs)`,
  CHEAT_TAC);;

let state_rel_call_env_push_env = prove
 (`// TODO: tidy up proof
   !(opt:(num#'a wordLang_prog#num#num) option).
     state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
     get_vars args (state_locals s) = SOME xs /\
     get_vars (MAP adjust_var args) t = SOME ws /\
     dataSem_cut_env r (state_locals s) = SOME x /\
     cut_envs (adjust_sets r) (wordSem_state_locals t) = SOME y ==>
     state_rel c q l (call_env xs ss (push_env x (IS_SOME opt)
       (dec_clock s)))
        (call_env (Loc q l :: ws) ss (push_env y opt (dec_clock t)))
          NONE
        ((l1,l2) :: locs)`,
  CHEAT_TAC);;

let find_code_thm_ret = prove
 (`state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
   get_vars args (state_locals s) = SOME xs /\
   get_vars (MAP adjust_var args) t = SOME ws /\
   find_code dest xs (state_code s) fs = SOME (ys,prog,ss) /\
   dataSem_cut_env r (state_locals s) = SOME x /\
   cut_envs (adjust_sets r) (wordSem_state_locals t) = SOME y ==>
   (?args1 n1 n2.
     find_code dest (Loc q l :: ws) (wordSem_state_code t) fs = SOME
       (args1,FST (data_to_word_comp c n1 n2 prog),ss) /\
     state_rel c q l (call_env ys ss (push_env x F (dec_clock s)))
       (call_env args1 ss (push_env y NONE
       (dec_clock t))) NONE ((l1,l2) :: locs))`,
  CHEAT_TAC);;

let find_code_thm_handler = prove
 (`state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
   get_vars args (state_locals s) = SOME xs /\
   get_vars (MAP adjust_var args) t = SOME ws /\
   find_code dest xs (state_code s) fs = SOME (ys,prog,ss) /\
   dataSem_cut_env r (state_locals s) = SOME x /\
   cut_envs (adjust_sets r) (wordSem_state_locals t) = SOME y ==>
   (?args1 n1 n2.
     find_code dest (Loc q l :: ws) (wordSem_state_code t) fs = SOME
       (args1,FST (data_to_word_comp c n1 n2 prog),ss) /\
     state_rel c q l (call_env ys ss (push_env x T (dec_clock s)))
       (call_env args1 ss (push_env y
          (SOME (adjust_var x0,(prog1:'a wordLang_prog),nn,l + 1))
       (dec_clock t))) NONE ((l1,l2) :: locs))`,
  CHEAT_TAC);;

let data_find_code = prove
 (`dataSem_find_code dest xs code fs = SOME (ys,prog,ss) ==>
  ~(bad_dest_args dest xs)`,
  CHEAT_TAC);;

let s_key_eq_LENGTH = prove
 (`!xs ys. s_key_eq xs ys ==> (LENGTH xs = LENGTH ys)`,
  CHEAT_TAC);;

(* s_key_eq_LASTN *)
let data_to_word_gcProof_s_key_eq_LASTN = prove
 (`!xs ys n. s_key_eq xs ys ==> s_key_eq (LASTN n xs) (LASTN n ys)`,
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:5613-5623: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_mk_loc_EQ *)

(* HOL4 data_to_word_gcProofScript.sml:5625-5644: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   mk_loc_eq_push_env_exc_Exception *)

(* HOL4 data_to_word_gcProofScript.sml:5646-5664: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_IMP_domain_EQ *)

(* HOL4 data_to_word_gcProofScript.sml:5666-5686: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_IMP_domain_EQ_Exc *)

let mk_loc_jump_exc = prove
 (`mk_loc (jump_exc
          (call_env args1 ss
             (push_env y (SOME (adjust_var n,prog1,x0,l))
                (dec_clock t)))) = Loc x0 l`,
  CHEAT_TAC);;

let data_to_word_gcProof_inc_clock_def = new_definition
  `data_to_word_gcProof_inc_clock n (t:('a,'c,'ffi)wordSem_state) =
  wordSem_state_clock_fupd (K (wordSem_state_clock t + n)) t`;;
hol4_overload "inc_clock" "data_to_word_gcProof_inc_clock";;

(* inc_clock_0[simp] *)
let data_to_word_gcProof_inc_clock_0 = prove
 (`!t. inc_clock 0 t = t`,
  CHEAT_TAC);;

(* inc_clock_inc_clock[simp] *)
let data_to_word_gcProof_inc_clock_inc_clock = prove
 (`!t. inc_clock n (inc_clock m t) = inc_clock (n + m) t`,
  CHEAT_TAC);;

(* [simp] *)
let mk_loc_jmup_exc_inc_clock = prove
 (`mk_loc (jump_exc (inc_clock ck t)) = mk_loc (jump_exc t)`,
  CHEAT_TAC);;

let jump_exc_inc_clock_EQ_NONE = prove
 (`jump_exc (inc_clock n s) = NONE <=> jump_exc s = NONE`,
  CHEAT_TAC);;

let state_rel_lookup_globals = prove
 (`state_rel c l1 l2 s t v1 locs /\ dataSem_state_global s = SOME g ==>
   // ∧
   // FLOOKUP s.refs g = SOME (ValueArray gs)
   (?x u.
   FLOOKUP (wordSem_state_store t) Globals = SOME (wordLang_Word
     (get_addr c x u)))`,
  CHEAT_TAC);;

let state_rel_cut_env = prove
 (`state_rel c l1 l2 s t NONE locs /\
    dataSem_cut_env names (state_locals s) = SOME x ==>
    state_rel c l1 l2 (state_locals_fupd (K x) s) t NONE locs`,
  CHEAT_TAC);;

let state_rel_get_var_Block = prove
 (`state_rel c l1 l2 s t v1 locs /\
   get_var n (state_locals s) = SOME (Block ts tag vs) ==>
   (?w. get_var (adjust_var n) t = SOME (wordLang_Word w))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:5826: ML code, not ported *)

let state_rel_cut_state_opt_get_var = prove
 (`state_rel c l1 l2 ((s:('c,'ffi)dataSem_state)) t NONE locs /\
   cut_state_opt names_opt s = SOME x /\
   get_var v (state_locals x) = SOME w ==>
   (?s'. state_rel c l1 l2 ((s':('c,'ffi)dataSem_state)) t NONE locs
     /\
        get_var v (dataSem_state_locals s') = SOME w)`,
  CHEAT_TAC);;

(* [allow_rebind] *)
let jump_exc_push_env_NONE_simp = prove
 (`(jump_exc (wordSem_dec_clock t) = NONE <=> jump_exc t = NONE) /\
   (jump_exc (wordSem_push_env y NONE t) = NONE <=> jump_exc t =
     NONE) /\
   (jump_exc (wordSem_state_stack_max_fupd (K b) t) = NONE <=>
     jump_exc t = NONE)`,
  CHEAT_TAC);;

let s_key_eq_handler_eq_IMP = prove
 (`s_key_eq (wordSem_state_stack t) (stack t1) /\ wordSem_state_handler
  t = state_handler t1 ==>
    (~(jump_exc t1 = NONE) <=> ~(jump_exc t = NONE))`,
  CHEAT_TAC);;

let eval_NONE_IMP_jump_exc_NONE_EQ = prove
 (`wordSem_evaluate (q,t) = (NONE,t1) ==> (jump_exc t1 = NONE <=>
  jump_exc t = NONE)`,
  CHEAT_TAC);;

let jump_exc_push_env_SOME = prove
 (`~(jump_exc (push_env y (SOME (x,prog1,l1,l2)) t) = NONE)`,
  CHEAT_TAC);;

let eval_push_env_T_Raise_IMP_stack_length = prove
 (`evaluate (p,call_env ys ss (push_env x T (dec_clock
  (s:('c,'ffi)dataSem_state)))) =
       (SOME (Rerr (Rraise a)),r') ==>
    LENGTH (stack r') = LENGTH (dataSem_state_stack s)`,
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:5900-5913: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   eval_push_env_SOME_exc_IMP_s_key_eq *)

let eval_exc_stack_shorter = prove
 (`evaluate (c,call_env ys ss (push_env x F (dec_clock
  (s:('c,'ffi)dataSem_state)))) =
      (SOME (Rerr (Rraise a)),r') ==>
    LENGTH (stack r') < LENGTH (dataSem_state_stack s)`,
  CHEAT_TAC);;

let NOT_1_domain = prove
 (`~(1 IN domain (adjust_set names))`,
  CHEAT_TAC);;

let NOT_3_domain = prove
 (`~(3 IN domain (adjust_set names))`,
  CHEAT_TAC);;

let NOT_5_domain = prove
 (`~(5 IN domain (adjust_set names))`,
  CHEAT_TAC);;

let cut_names_adjust_set_insert_1 = prove
 (`cut_names (adjust_set names) (insert 1 w l) = cut_names (adjust_set
  names) l`,
  CHEAT_TAC);;

let cut_names_adjust_set_insert_3 = prove
 (`cut_names (adjust_set names) (insert 3 w l) = cut_names (adjust_set
  names) l`,
  CHEAT_TAC);;

let case_EQ_SOME_IFF = prove
 (`(match p with NONE -> NONE | SOME x -> g x) = SOME y <=>
    (?x. p = SOME x /\ g x = SOME y)`,
  CHEAT_TAC);;

let state_rel_set_store_AllocSize = prove
 (`state_rel c l1 l2 s (wordSem_set_store AllocSize (wordLang_Word w) t)
  v locs =
    state_rel c l1 l2 s t v locs`,
  CHEAT_TAC);;

let inter_insert = prove
 (`inter (insert n x t1) t2 =
    (if n IN domain t2 then insert n x (inter t1 t2) else inter t1
      t2)`,
  CHEAT_TAC);;

let lookup_0_adjust_set = prove
 (`sptree_lookup 0 (adjust_set l) = NONE`,
  CHEAT_TAC);;

let lookup_1_adjust_set = prove
 (`sptree_lookup 1 (adjust_set l) = NONE`,
  CHEAT_TAC);;

let lookup_3_adjust_set = prove
 (`sptree_lookup 3 (adjust_set l) = NONE`,
  CHEAT_TAC);;

let lookup_5_adjust_set = prove
 (`sptree_lookup 5 (adjust_set l) = NONE`,
  CHEAT_TAC);;

let lookup_ODD_adjust_set = prove
 (`ODD n ==> sptree_lookup n (adjust_set l) = NONE`,
  CHEAT_TAC);;

let wf_adjust_set = prove
 (`sptree_wf (adjust_set s)`,
  CHEAT_TAC);;

let lookup_adjust_set = prove
 (`sptree_lookup n (adjust_set s) =
   (if ODD n \/ n = 0 then NONE else
   if (n - 2) DIV 2 IN domain s then SOME one else NONE)`,
  CHEAT_TAC);;

let adjust_set_inter = prove
 (`adjust_set (inter t1 t2) = inter (adjust_set t1) (adjust_set t2)`,
  CHEAT_TAC);;

let state_rel_insert_1 = prove
 (`state_rel c l1 l2 s (wordSem_state_locals_fupd (K (insert 1 x
  (wordSem_state_locals t))) t) v locs =
    state_rel c l1 l2 s t v locs`,
  CHEAT_TAC);;

let state_rel_insert_3 = prove
 (`state_rel c l1 l2 s (wordSem_state_locals_fupd (K (insert 3 x
  (wordSem_state_locals t))) t) v locs =
    state_rel c l1 l2 s t v locs`,
  CHEAT_TAC);;

let state_rel_insert_7 = prove
 (`state_rel c l1 l2 s (wordSem_state_locals_fupd (K (insert 7 x
  (wordSem_state_locals t))) t) v locs =
    state_rel c l1 l2 s t v locs`,
  CHEAT_TAC);;

let state_rel_insert_3_1 = prove
 (`state_rel c l1 l2 s (wordSem_state_locals_fupd (K (insert 3 x (insert
  1 y (wordSem_state_locals t)))) t) v locs =
    state_rel c l1 l2 s t v locs`,
  CHEAT_TAC);;

let state_rel_inc_clock = prove
 (`state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs ==>
    state_rel c l1 l2 (state_clock_fupd (K (state_clock s + 1)) s)
                      (wordSem_state_clock_fupd (K
                        (wordSem_state_clock t + 1)) t) NONE locs`,
  CHEAT_TAC);;

(* dec_clock_inc_clock *)
let data_to_word_gcProof_dec_clock_inc_clock = prove
 (`(dataSem_dec_clock (state_clock_fupd (K (state_clock s + 1)) s) = s)
  /\
    (wordSem_dec_clock (wordSem_state_clock_fupd (K
      (wordSem_state_clock t + 1)) t) = t)`,
  CHEAT_TAC);;

let word_gc_move_IMP_isWord = prove
 (`word_gc_move c' (wordLang_Word c,i,pa,old,m,dm) = (w1,i1,pa1,m1,c1)
  ==> isWord w1`,
  CHEAT_TAC);;

let word_gen_gc_move_IMP_isWord = prove
 (`word_gen_gc_move c' (wordLang_Word c,i,pa,ib,pb,old,m,dm) =
  (w1,i1,pa1,ib1,pb1,m1,c1) ==>
   isWord w1`,
  CHEAT_TAC);;

let word_gen_gc_partial_move_IMP_isWord = prove
 (`word_gen_gc_partial_move c' (wordLang_Word c,i,pa,old,m,dm,gs,rs) =
  (w1,i1,pa1,m1,c1) ==>
   isWord w1`,
  CHEAT_TAC);;

let loc_ok_def = new_definition
  `loc_ok x1 =
      match x1 with
        wordLang_Loc m n -> (n = 0)
      | _24 -> T`;;

let loc_ok_word_addr = prove
 (`loc_ok (word_addr c w)`,
  CHEAT_TAC);;

(* [local] *)
let word_gc_move_roots_IMP_FILTER0 = prove
 (`!ws i pa old m dm ws2 i2 pa2 m2 c2 c.
     word_gc_move_roots c (ws,i,pa,old,m,dm) = (ws2,i2,pa2,m2,c2) /\
     EVERY loc_ok ws ==>
     word_gc_move_roots c (FILTER isWord ws,i,pa,old,m,dm) =
                          (FILTER isWord ws2,i2,pa2,m2,c2)`,
  CHEAT_TAC);;

(* [local] *)
let word_gen_gc_move_roots_IMP_FILTER0 = prove
 (`!ws i pa ib pb old m dm ws2 i2 pa2 ib2 pb2 m2 c2 c.
     word_gen_gc_move_roots c (ws,i,pa,ib,pb,old,m,dm) =
                              (ws2,i2,pa2,ib2,pb2,m2,c2) /\
     EVERY loc_ok ws ==>
     word_gen_gc_move_roots c (FILTER isWord ws,i,pa,ib,pb,old,m,dm)
       =
                              (FILTER isWord
                                ws2,i2,pa2,ib2,pb2,m2,c2)`,
  CHEAT_TAC);;

let word_gen_gc_partial_move_roots_IMP_FILTER = prove
 (`!ws i pa ib pb old m dm ws2 i2 pa2 ib2 pb2 m2 c2 c.
     word_gen_gc_partial_move_roots c (ws,i,pa,old,m,dm,gs,rs) =
                              (ws2,i2,pa2,m2,c2) /\
     EVERY loc_ok ws ==>
     word_gen_gc_partial_move_roots c (FILTER isWord
       ws,i,pa,old,m,dm,gs,rs) =
                              (FILTER isWord ws2,i2,pa2,m2,c2)`,
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:6232: the ML values that the
   definitions below antiquote *)

let word_gc_fun_IMP_FILTER = prove
 (`word_gc_fun c (xs,m,dm,s) = SOME (stack1,m1,s1) /\
   EVERY loc_ok xs ==>
   word_gc_fun c (FILTER isWord xs,m,dm,s) = SOME (FILTER isWord
     stack1,m1,s1)`,
  CHEAT_TAC);;

let _ = size_thms "word_loc";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let loc_merge_def,loc_merge_ind = define_wf
  `MEASURE (\(x0,x1).      list_size (word_loc_size (\x. 0)) x0 +
  list_size (word_loc_size (\x. 0)) x1)`
  [`loc_merge [] ys = []`;
   `loc_merge (wordLang_Loc l1 l2 :: xs) ys = (Loc l1 l2:'a word_loc)
  :: loc_merge xs ys`;
   `loc_merge (wordLang_Word w :: xs) (y :: ys) = y :: loc_merge xs
  ys`;
   `loc_merge (wordLang_Word w :: xs) [] = (wordLang_Word w:'a
  word_loc) :: xs`];;

let LENGTH_loc_merge = prove
 (`!xs ys. LENGTH (loc_merge xs ys) = LENGTH xs`,
  CHEAT_TAC);;

let word_gc_move_roots_IMP_FILTER = prove
 (`!ws i pa old m dm ws2 i2 pa2 m2 c2 c.
      word_gc_move_roots c (FILTER isWord ws,i,pa,old,m,dm) =
                           (ws2,i2,pa2,m2,c2) /\
      EVERY loc_ok ws ==>
      word_gc_move_roots c (ws,i,pa,old,m,dm) =
                           (loc_merge ws ws2,i2,pa2,m2,c2)`,
  CHEAT_TAC);;

let word_gen_gc_move_roots_IMP_FILTER = prove
 (`!ws i pa ib pb old m dm ws2 i2 pa2 ib2 pb2 m2 c2 c.
      word_gen_gc_move_roots c (FILTER isWord ws,i,pa,ib,pb,old,m,dm)
        =
        (ws2,i2,pa2,ib2,pb2,m2,c2) /\
      EVERY loc_ok ws ==>
      word_gen_gc_move_roots c (ws,i,pa,ib,pb,old,m,dm) =
                           (loc_merge ws ws2,i2,pa2,ib2,pb2,m2,c2)`,
  CHEAT_TAC);;

(* word_gen_gc_partial_move_roots_IMP_FILTER[allow_rebind] *)
let data_to_word_gcProof_word_gen_gc_partial_move_roots_IMP_FILTER =
  prove
 (`!ws i pa old m dm gs rs ws2 i2 pa2 m2 c2 c.
      word_gen_gc_partial_move_roots c (FILTER isWord
        ws,i,pa,old,m,dm,gs,rs) =
                              (ws2,i2,pa2,m2,c2) /\
      EVERY loc_ok ws ==>
      word_gen_gc_partial_move_roots c (ws,i,pa,old,m,dm,gs,rs) =
                              (loc_merge ws ws2,i2,pa2,m2,c2)`,
  CHEAT_TAC);;

let loc_merge_FILTER_isWord = prove
 (`!xs. loc_merge xs (FILTER isWord xs) = xs`,
  CHEAT_TAC);;

let word_gc_fun_loc_merge = prove
 (`word_gc_fun c (FILTER isWord xs,m,dm,s) = SOME (ys,m1,s1) /\
   EVERY loc_ok xs ==>
   word_gc_fun c (xs,m,dm,s) = SOME (loc_merge xs ys,m1,s1)`,
  CHEAT_TAC);;

let word_gc_fun_IMP = prove
 (`word_gc_fun c (xs,m,dm,s) = SOME (ys,m1,s1) ==>
    FLOOKUP s1 AllocSize = FLOOKUP s AllocSize /\
    FLOOKUP s1 Handler = FLOOKUP s Handler /\
    FLOOKUP s1 CodeBuffer = FLOOKUP s CodeBuffer /\
    FLOOKUP s1 CodeBufferEnd = FLOOKUP s CodeBufferEnd /\
    FLOOKUP s1 BitmapBuffer = FLOOKUP s BitmapBuffer /\
    FLOOKUP s1 BitmapBufferEnd = FLOOKUP s BitmapBufferEnd /\
    FLOOKUP s1 (Temp (n2w 29)) = FLOOKUP s (Temp (n2w 29)) /\
    FLOOKUP s1 HeapLength = FLOOKUP s HeapLength /\
    Globals IN FDOM s1`,
  CHEAT_TAC);;

let gc_fun_const_ok_word_gc_fun = prove
 (`gc_fun_const_ok (word_gc_fun c)`,
  CHEAT_TAC);;

let gc_fun_ok_word_gc_fun = prove
 (`gc_fun_ok (word_gc_fun c1)`,
  CHEAT_TAC);;

let word_gc_fun_APPEND_IMP = prove
 (`word_gc_fun c (xs ++ ys,m,dm,s) = SOME (zs,m1,s1) ==>
    (?zs1 zs2. zs = zs1 ++ zs2 /\ LENGTH xs = LENGTH zs1 /\ LENGTH
      ys = LENGTH zs2)`,
  CHEAT_TAC);;

(* [allow_rebind] *)
let IMP_loc_merge_APPEND = prove
 (`!ts qs xs ys.
         LENGTH (FILTER isWord ts) = LENGTH qs ==>
         loc_merge (ts ++ xs) (qs ++ ys) = loc_merge ts qs ++
           loc_merge xs ys`,
  CHEAT_TAC);;

let TAKE_DROP_loc_merge_APPEND = prove
 (`TAKE (LENGTH q) (loc_merge (MAP SND q) xs ++ ys) = loc_merge (MAP SND
  q) xs /\
   DROP (LENGTH q) (loc_merge (MAP SND q) xs ++ ys) = ys`,
  CHEAT_TAC);;

let loc_merge_NIL = prove
 (`!xs. loc_merge xs [] = xs`,
  CHEAT_TAC);;

let loc_merge_APPEND = prove
 (`!xs1 xs2 ys.
      ?zs1 zs2. loc_merge (xs1 ++ xs2) ys = zs1 ++ zs2 /\
                LENGTH zs1 = LENGTH xs1 /\ LENGTH xs2 = LENGTH xs2 /\
                (?ts. loc_merge xs2 ts = zs2)`,
  CHEAT_TAC);;

let EVERY2_loc_merge = prove
 (`!xs ys. EVERY2 (\x y. (isWord y ==> isWord x) /\
                          (~(isWord x) ==> x = y)) xs (loc_merge xs
                            ys)`,
  CHEAT_TAC);;

let dec_stack_loc_merge_enc_stack = prove
 (`!xs ys. ?ss. wordSem_dec_stack (loc_merge (wordSem_enc_stack xs)
  ys) xs = SOME ss`,
  CHEAT_TAC);;

let ALOOKUP_ZIP = prove
 (`!l zs1.
      ALOOKUP l (0:num) = SOME (Loc q r) /\
      LIST_REL (\x y. (isWord y ==> isWord x) /\
        (~(isWord x) ==> x = y)) (MAP SND l) zs1 ==>
      ALOOKUP (ZIP (MAP FST l) zs1) 0 = SOME (Loc q r)`,
  CHEAT_TAC);;

let stack_rel_dec_stack_IMP_stack_rel = prove
 (`!xs ys ts stack' locs.
      LIST_REL data_to_word_gcProof_stack_rel ts xs /\ LIST_REL
        contains_loc xs locs /\
      wordSem_dec_stack (loc_merge (wordSem_enc_stack xs) ys) xs =
        SOME stack' ==>
      LIST_REL data_to_word_gcProof_stack_rel ts stack' /\ LIST_REL
        contains_loc stack' locs`,
  CHEAT_TAC);;

let join_env_NIL = prove
 (`join_env s [] = []`,
  CHEAT_TAC);;

let join_env_CONS = prove
 (`join_env s ((n,v) :: xs) =
    (if ~(n = 0) /\ EVEN n then
      (THE (sptree_lookup ((n - 2) DIV 2) s),v) :: join_env s xs
        else join_env s xs)`,
  CHEAT_TAC);;

let FILTER_enc_stack_lemma = prove
 (`!xs ys.
      LIST_REL data_to_word_gcProof_stack_rel xs ys ==>
      FILTER isWord (MAP SND (flat xs ys)) =
      FILTER isWord (wordSem_enc_stack ys)`,
  CHEAT_TAC);;

let stack_rel_simp = prove
 (`(data_to_word_gcProof_stack_rel (Env i s:dataSem_stack) y <=>
    (?rets vs. data_to_word_gcProof_stack_rel ((Env i
      s:dataSem_stack)) y /\ (y = StackFrame i rets vs NONE))) /\
   (data_to_word_gcProof_stack_rel (dataSem_Exc i s n) y <=>
    (?rets vs x1 x2 x3. data_to_word_gcProof_stack_rel (dataSem_Exc
      i s n) y /\ (y = StackFrame i rets vs (SOME (x1,x2,x3)))))`,
  CHEAT_TAC);;

let join_env_EQ_ZIP = prove
 (`!vs s zs1.
      EVERY (\(x1,x2). ~(x1 = 0) /\ EVEN x1) vs /\
      LENGTH (join_env s vs) = LENGTH zs1 /\
      LIST_REL (\x y. isWord x = isWord y /\ (~(isWord x) ==> x = y))
         (MAP SND (join_env s vs)) zs1 ==>
      join_env s
        (ZIP (MAP FST vs) (loc_merge (MAP SND vs) (FILTER isWord
          zs1))) =
      ZIP (MAP FST (join_env s vs)) zs1`,
  CHEAT_TAC);;

let LENGTH_MAP_SND_join_env_IMP = prove
 (`!vs zs1 s.
      LIST_REL (\x y. (isWord x = isWord y) /\ (~(isWord x) ==> x =
        y))
        (MAP SND (join_env s vs)) zs1 /\
      EVERY (\(x1,x2). ~(x1 = 0) /\ EVEN x1) vs /\
      LENGTH (join_env s vs) = LENGTH zs1 ==>
      LENGTH (FILTER isWord (MAP SND vs)) = LENGTH (FILTER isWord
        zs1)`,
  CHEAT_TAC);;

(* lemma1 *)
let data_to_word_gcProof_lemma1 = prove
 (`(y1 = y2) /\ (x1 = x2) ==> (f x1 y1 = f x2 y2)`,
  CHEAT_TAC);;

(* [allow_rebind] *)
let word_gc_fun_EL_lemma = prove
 (`!xs ys stack1 m dm st m1 s1 stack'.
         LIST_REL data_to_word_gcProof_stack_rel xs stack' /\
         EVERY2 (\x y. isWord x = isWord y /\ (~(isWord x) ==> x =
           y))
            (MAP SND (flat xs ys)) stack1 /\
         wordSem_dec_stack (loc_merge (wordSem_enc_stack ys) (FILTER
           isWord stack1)) ys =
           SOME stack' /\ LIST_REL data_to_word_gcProof_stack_rel xs
             ys ==>
         (flat xs stack' =
          ZIP (MAP FST (flat xs ys)) stack1)`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_ml_inv_cons_snoc = prove
 (cake_as_vars (fun () ->
    `word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs (x :: xs) ==>
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs (xs ++
       [x])`),
  CHEAT_TAC);;

let size_of_cons = prove
 (`size_of lims (x :: xs) refs seen =
     (let (n1,refs1,seen1) = size_of lims xs refs seen in
     let (n2,refs2,seen2) = size_of lims [x] refs1 seen1 in
       (n1 + n2,refs2,seen2))`,
  CHEAT_TAC);;

let size_of_global_to_vs = prove
 (`!xs. size_of lims (xs ++ global_to_vs x) refs seen =
        size_of lims (xs ++ [the_global x]) refs seen`,
  CHEAT_TAC);;

let toListA_mk = prove
 (`toListA a (mk_BN t1 t2) = toListA a (BN t1 t2) /\
   toListA a (mk_BS t1 x t2) = toListA a (BS t1 x t2)`,
  CHEAT_TAC);;

let PERM_toList_delete = prove
 (`!k s x.
     sptree_lookup k s = SOME x ==>
     PERM (toList s) (x :: toList (delete k s))`,
  CHEAT_TAC);;

let PERM_lookup_toList_lemma = prove
 (`!l s.
     (!n. IS_SOME (sptree_lookup n s) <=> IS_SOME (ALOOKUP l
       (adjust_var n))) /\
     ALL_DISTINCT (MAP FST l) ==>
     PERM (MAP FST
        (MAP (\(n,v). (THE (sptree_lookup ((n - 2) DIV 2) s),v))
           (FILTER (\(n,v). ~(n = 0) /\ EVEN n) l))) (toList s)`,
  CHEAT_TAC);;

let flat_PERM_extract_stack = prove
 (`!xs ys.
     LIST_REL data_to_word_gcProof_stack_rel xs ys ==>
     PERM (MAP FST (flat xs ys)) (FLAT (MAP extract_stack xs))`,
  CHEAT_TAC);;

let ALL_DISTINCT_data_pointers = prove
 (`!heap. ALL_DISTINCT (data_pointers heap)`,
  CHEAT_TAC);;

let SUM_MAP_lookup_len_LESS_EQ = prove
 (`!p1 p2.
     set_of_list p1 SUBSET set_of_list p2 /\ ALL_DISTINCT p1 ==>
     SUM (MAP (lookup_len heap) p1) <= SUM (MAP (lookup_len heap)
       p2)`,
  CHEAT_TAC);;

let set_data_pointers = prove
 (`set_of_list (data_pointers heap) = {a | isSomeDataElement
  (heap_lookup a heap)}`,
  CHEAT_TAC);;

let traverse_heap = cake_inductive
  `(!heap p1.
      traverse_heap heap p1 [] p1) /\
   (!heap vs1 vs2 vars' p1 p2 p3.
      traverse_heap heap p1 vs1 p2 /\
      traverse_heap heap p2 vs2 p3 /\
      set_of_list vars' = set_of_list (vs1 ++ vs2) ==>
      traverse_heap heap p1 vars' p3) /\
   (!heap p1 d.
      traverse_heap heap p1 [gc_shared_Data d] p1) /\
   (!heap p1 n t.
      MEM n p1 ==>
      traverse_heap heap p1 [gc_shared_Pointer n t] p1) /\
   (!heap p1 n t p2 xs l d.
      heap_lookup n heap = SOME (DataElement xs l d) /\
      traverse_heap heap (n :: p1) xs p2 ==>
      traverse_heap heap p1 [gc_shared_Pointer n t] p2)`;;

(* [local] *)
let size_of_Block = prove
 (`size_of lims [(Block ts tag vs:dataSem_v)] refs seen =
   (if vs = [] \/ IS_SOME (sptree_lookup ts seen) then
     (0,refs,seen) else let (n,refs',seen') = size_of lims vs refs
     (insert ts one seen) in (n + LENGTH vs + 1,refs',seen'))`,
  CHEAT_TAC);;

let LENGTH_n2mw_LE_bignum_digits = prove
 (`!n m.
     good_dimindex (:'a) /\ n <= m ==>
     LENGTH ((n2mw n):('a word) list) <= bignum_digits (dimindex
       (:'a) = 64) m`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let soundness_size_of = prove
 (cake_as_vars (fun () ->
    `!lims roots r1 s1 root_vars
       (vars':(('a word_loc) heap_address) list) n2 r2 s2 p1 refs.
       (!n. reachable_refs root_vars refs n /\ n IN FDOM f ==>
            bc_ref_inv c n refs (f,tf,heap,be)) /\
       no_thunks_in_refs refs /\
       LIST_REL (\v x. v_inv c v refs (x,f,tf,heap)) root_vars
         vars' /\
       PERM roots root_vars /\ good_dimindex (:'a) /\
       IMAGE ((FAPPLY) tf) (domain s1) SUBSET set_of_list p1 /\
       IMAGE ((FAPPLY) f) (domain refs DIFF domain r1) SUBSET
         set_of_list p1 /\
       FDOM f SUBSET domain refs /\ subspt r1 refs /\
       (limits_arch_64_bit lims <=> dimindex (:'a) = 64) /\
       size_of lims roots r1 s1 = (n2,r2,s2) ==>
       (?p2. SUM (MAP (lookup_len heap) p2) <= n2 + SUM (MAP
         (lookup_len heap) p1) /\
            traverse_heap heap p1 vars' p2 /\ subspt r2 refs /\
            IMAGE ((FAPPLY) tf) (domain s2) SUBSET set_of_list p2
              /\
            IMAGE ((FAPPLY) f) (domain refs DIFF domain r2)
              SUBSET set_of_list p2)`),
  CHEAT_TAC);;

let traverse_heap_reachable_set_mono = prove
 (`!heap1 ps vars' ps2. traverse_heap heap1 ps vars' ps2 ==>
   set_of_list ps SUBSET set_of_list ps2`,
  CHEAT_TAC);;

let traverse_heap_reachable_aux_vars_gc_edge = prove
 (`!heap ps vars' ps2. traverse_heap heap ps vars' ps2 ==>
   (!vars2.
   (!y z. MEM y ps /\ gc_edge heap y z ==>
      MEM z ps \/ (?t. MEM (gc_shared_Pointer z t) (vars' ++ vars2)))
        ==>
   (set_of_list ps SUBSET set_of_list ps2) /\
   (!y t. MEM (gc_shared_Pointer y t) vars' ==>
      MEM y ps2 \/ (?t. MEM (gc_shared_Pointer y t) vars2)) /\
   (!y z. MEM y ps2 /\ gc_edge heap y z ==>
      MEM z ps2 \/ (?t. MEM (gc_shared_Pointer z t) vars2)))`,
  CHEAT_TAC);;

let traverse_heap_reachable_RTC_gc_edge = prove
 (`traverse_heap heap [] vars ps2 ==>
   (!p x. RTC (gc_edge heap) p x ==> MEM p ps2 ==> MEM x ps2)`,
  CHEAT_TAC);;

let traverse_heap_reachable = prove
 (`traverse_heap heap1 [] vars p2 /\
   reachable_addresses vars heap1 x ==> MEM x p2`,
  CHEAT_TAC);;

(* [local] *)
let stack_rel_imp_subset = prove
 (`!xs ys.
     LIST_REL data_to_word_gcProof_stack_rel xs ys ==>
     set_of_list (wordSem_enc_stack ys) SUBSET set_of_list (MAP SND
       (flat xs ys))`,
  CHEAT_TAC);;

(* Root-set-generalised alloc chain: the _gen theorems bound the NotEnoughSpace
   heap usage over any roots2 with PERM roots2 (dups ++ canonical roots) and
   set dups SUBSET roots.  alloc_lemma / AllocVar_thm are corollaries (dups:=[]);
   AllocVar_thm_nary supplies the args-prepended narrow cut as roots2. *)

let PERM_toList_lookup_eq = prove
 (`!m1 m2. (!k. sptree_lookup k m1 = sptree_lookup k (m2:'a spt)) ==>
           PERM (toList m1) (toList m2)`,
  CHEAT_TAC);;

let LIST_REL_exists_witness = prove
 (`!xs. (!x. MEM x xs ==> (?y. P x y)) ==> (?ys. LIST_REL P xs ys)`,
  CHEAT_TAC);;

let get_vars_PERM_toList_inter = prove
 (`!args x' (vals:'a list).
     dataSem_get_vars args locals = SOME vals ==>
     (?dups.
       PERM (vals ++ toList (inter locals x'))
            (dups ++ toList (inter locals (list_insert args x'))) /\
       set_of_list dups SUBSET set_of_list vals /\
       set_of_list vals SUBSET set_of_list (toList (inter locals
         (list_insert args x'))))`,
  CHEAT_TAC);;

let soundness_size_of_gen = prove
 (`!lims (roots2:dataSem_v list) dups root_vars
    (vars':(('a word_loc) heap_address) list) n2 r2 s2 refs c f tf
      heap be'.
     (!n. reachable_refs root_vars refs n /\ n IN FDOM f ==>
          bc_ref_inv c n refs (f,tf,heap,be')) /\
     no_thunks_in_refs refs /\
     LIST_REL (\v x. v_inv c v refs (x,f,tf,heap)) root_vars vars' /\
     PERM roots2 (dups ++ root_vars) /\
     set_of_list dups SUBSET set_of_list root_vars /\
     good_dimindex (:'a) /\
     FDOM f SUBSET domain refs /\
     (limits_arch_64_bit lims <=> dimindex (:'a) = 64) /\
     size_of lims roots2 refs LN = (n2,r2,s2) ==>
     (?p2. SUM (MAP (lookup_len heap) p2) <= n2 /\
          (!x. reachable_addresses vars' heap x ==> MEM x p2))`,
  CHEAT_TAC);;

let state_rel_gc_gen = prove
 (`state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs ==>
    FLOOKUP (wordSem_state_store t) AllocSize = SOME (wordLang_Word
      (alloc_size k)) /\ state_locals
    s = LN /\ wordSem_state_locals
    t = LS (Loc l1 l2) ==>
    (?t2 wl m st w1 w2 stack'. wordSem_state_gc_fun
      t (wordSem_enc_stack (wordSem_state_stack
        t),wordSem_state_memory t,wordSem_state_mdomain
        t,wordSem_state_store t) =
        SOME (wl,m,st) /\
      wordSem_dec_stack wl (wordSem_state_stack t) = SOME stack' /\
      FLOOKUP st (Temp (n2w 29)) = FLOOKUP (wordSem_state_store t)
        (Temp (n2w 29)) /\
      FLOOKUP st AllocSize = SOME (wordLang_Word (alloc_size k)) /\
      (wordSem_has_space (wordLang_Word ((alloc_size k):'a word))
        (wordSem_state_store_fupd (K st) t) = SOME F /\
        ~(data_to_word_config_gc_kind
       c = None) /\ no_thunks_in_refs (state_refs s) ==>
         (!roots2 dups n2 r2 s2.
           PERM roots2 (dups ++ FLAT (MAP extract_stack (stack s)) ++
                        [the_global (dataSem_state_global s)]) /\
           set_of_list dups SUBSET set_of_list (FLAT (MAP
             extract_stack (stack s)) ++
                              [the_global (dataSem_state_global s)])
                                /\
           size_of (dataSem_state_limits s) roots2 (state_refs s) LN
             = (n2,r2,s2) ==> limits_heap_limit (dataSem_state_limits
           s) < n2 + k)) /\
      state_rel c l1 l2 (dataSem_state_space_fupd (K 0) s)
        (wordSem_state_memory_fupd (K m) (wordSem_state_store_fupd
          (K st) (wordSem_state_stack_fupd (K stack') t))) NONE locs)`,
  CHEAT_TAC);;


let cut_locals_def = new_definition
  `cut_locals names (s:('a,'b)dataSem_state) =
     (match dataSem_cut_env names (dataSem_state_locals s) with
       SOME env -> dataSem_state_locals_fupd (K env) s | NONE ->
       dataSem_state_locals_fupd (K LN) s)`;;

let size_of_heap_call_push_env = prove
 (`dataSem_cut_env names (state_locals s) = SOME x ==>
   size_of_heap (call_env [] ss (push_env x F s)) = size_of_heap
     (state_locals_fupd (K x) s)`,
  CHEAT_TAC);;

let gc_lemma_gen = prove
 (`let t0 = call_env [Loc l1 l2] ss (push_env y
        (NONE:(num#'a wordLang_prog#num#num) option) t) in
      dataSem_cut_env names (dataSem_state_locals
        (s:('c,'ffi)dataSem_state)) = SOME x /\
      state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      FLOOKUP (wordSem_state_store t) AllocSize = SOME (wordLang_Word
        (alloc_size k)) /\
      cut_envs (adjust_sets names) (wordSem_state_locals t) = SOME y
        ==>
      (?t2 wl m st w1 w2 stack'. wordSem_state_gc_fun
        t0 (wordSem_enc_stack (stack t0),wordSem_state_memory
          t0,wordSem_state_mdomain t0,wordSem_state_store t0) =
          SOME (wl,m,st) /\
        wordSem_dec_stack wl (stack t0) = SOME stack' /\
        pop_env (wordSem_state_memory_fupd (K m)
          (wordSem_state_store_fupd (K st) (stack_fupd (K stack') t0)))
          = SOME t2 /\
        FLOOKUP (wordSem_state_store t2) (Temp (n2w 29)) = FLOOKUP
          (wordSem_state_store t) (Temp (n2w 29)) /\
        FLOOKUP (wordSem_state_store t2) AllocSize = SOME
          (wordLang_Word (alloc_size k)) /\
        (wordSem_has_space (wordLang_Word ((alloc_size k):'a word))
          t2 = SOME F /\ ~(data_to_word_config_gc_kind
         c = None) /\ no_thunks_in_refs (dataSem_state_refs s) ==>
           (!roots2 dups n2 r2 s2.
             PERM roots2 (dups ++ toList x ++ FLAT (MAP extract_stack
               (dataSem_state_stack s)) ++
                          [the_global (dataSem_state_global s)]) /\
             set_of_list dups SUBSET set_of_list (toList x ++ FLAT
               (MAP extract_stack (dataSem_state_stack s)) ++
                              [the_global (dataSem_state_global s)])
                                /\
             size_of (dataSem_state_limits s) roots2
               (dataSem_state_refs s) LN = (n2,r2,s2) ==>
               limits_heap_limit (dataSem_state_limits
             s) < n2 + k)) /\
        state_rel c l1 l2 (dataSem_state_stack_max_fupd (K
          (OPTION_MAP2 MAX
          (OPTION_MAP2 MAX (dataSem_state_stack_max s)
             (size_of_stack (Env (dataSem_state_locals_size s) x ::
               dataSem_state_stack s)))
          (OPTION_MAP2 (+) (size_of_stack (Env
            (dataSem_state_locals_size s) x :: dataSem_state_stack s))
            ss))) (dataSem_state_space_fupd (K 0)
            (dataSem_state_locals_fupd (K x) s))) t2 NONE locs)`,
  CHEAT_TAC);;


let gc_add_call_env = prove
 (`(match wordSem_gc (wordSem_push_env y NONE t5) with NONE -> (SOME
  wordSem_Error,x) | SOME s' -> (match pop_env s' with NONE -> (SOME
  Error,flush_state T s') | SOME s' -> f s')) = (res,t) ==>
    (match wordSem_gc (wordSem_call_env [Loc l1 l2] (SOME 0)
      (push_env y NONE t5)) with NONE -> (SOME Error,x) | SOME s' ->
      (match pop_env s' with NONE -> (SOME Error,flush_state T s') |
      SOME s' -> f s')) = (res,t)`,
  CHEAT_TAC);;

let has_space_state_rel = prove
 (`wordSem_has_space (wordLang_Word ((alloc_size k):'a word))
  (r:('a,'c,'ffi)wordSem_state) = SOME T /\
   state_rel c l1 l2 s r NONE locs ==>
   state_rel c l1 l2 (dataSem_state_space_fupd (K k) s) r NONE locs`,
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:7686-7692: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_IMP_inc_clock *)

(* HOL4 data_to_word_gcProofScript.sml:7694-7700: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_IMP_inc_clock_Ex *)

let get_var_inc_clock = prove
 (`get_var n (inc_clock k s) = get_var n s`,
  CHEAT_TAC);;

let get_vars_inc_clock = prove
 (`get_vars n (inc_clock k s) = get_vars n s`,
  CHEAT_TAC);;

let set_var_inc_clock = prove
 (`set_var n x (inc_clock ck t) = inc_clock ck (set_var n x t)`,
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:7721-7724: ML code, not ported *)

let w2n_minus_1_LESS_EQ = prove
 (`(w2n (--((n2w 1):'a word)) <= w2n (w:'a word)) <=> w + (n2w 1) =
  (n2w 0)`,
  CHEAT_TAC);;

let bytes_in_word_ADD_1_NOT_ZERO = prove
 (`good_dimindex (:'a) ==> ~(bytes_in_word * w + (n2w 1) = ((n2w 0):'a
  word))`,
  CHEAT_TAC);;

let option_le_OPTION_MAP2_MAX = prove
 (`option_le (OPTION_MAP2 MAX n m) n = option_le m n /\
   option_le (OPTION_MAP2 MAX m n) n = option_le m n`,
  CHEAT_TAC);;

let alloc_lemma_gen = prove
 (`state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    dataSem_cut_env names (state_locals s) = SOME x /\
    wordSem_alloc (alloc_size k) (adjust_sets names) t =
      ((q:('a wordSem_result) option),r) ==>
    (q = SOME wordSem_NotEnoughSpace ==> state_ffi
     r = state_ffi s /\ option_le (state_stack_max r)
       (state_stack_max s) /\
     (~(data_to_word_config_gc_kind c = None) /\ no_thunks_in_refs
       (state_refs s) ==>
        (!roots2 dups n2 r2 s2.
          PERM roots2 (dups ++ toList x ++ FLAT (MAP extract_stack
            (stack s)) ++
                       [the_global (dataSem_state_global s)]) /\
          set_of_list dups SUBSET set_of_list (toList x ++ FLAT (MAP
            extract_stack (stack s)) ++
                              [the_global (dataSem_state_global s)])
                                /\
          size_of (dataSem_state_limits s) roots2 (state_refs s) LN =
            (n2,r2,s2) ==> limits_heap_limit (dataSem_state_limits
          s) < n2 + k))) /\
    (~(q = SOME wordSem_NotEnoughSpace) ==>
     state_rel c l1 l2 (dataSem_state_space_fupd (K k)
       (state_locals_fupd (K x) s)) r NONE locs /\ ~(alloc_size k =
       --((n2w 1):'a word)) /\
     FLOOKUP (wordSem_state_store r) (Temp (n2w 29)) = FLOOKUP
       (wordSem_state_store t) (Temp (n2w 29)) /\ state_code
     r = wordSem_state_code t /\ state_code_buffer
     r = wordSem_state_code_buffer t /\ wordSem_state_data_buffer
     r = wordSem_state_data_buffer t /\ compile_oracle
     r = wordSem_state_compile_oracle t /\
     q = NONE)`,
  CHEAT_TAC);;
(* HOL4 data_to_word_gcProofScript.sml:7887-7892: a proof *)

let alloc_lemma = prove
 (`state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    dataSem_cut_env names (state_locals s) = SOME x /\
    wordSem_alloc (alloc_size k) (adjust_sets names) t =
      ((q:('a wordSem_result) option),r) ==>
    (q = SOME wordSem_NotEnoughSpace ==> state_ffi
     r = state_ffi s /\ option_le (state_stack_max r)
       (state_stack_max s) /\
     (~(data_to_word_config_gc_kind c = None) /\ no_thunks_in_refs
       (state_refs s) ==> limits_heap_limit (dataSem_state_limits
       s) < size_of_heap (cut_locals names s) + k)) /\
    (~(q = SOME wordSem_NotEnoughSpace) ==>
     state_rel c l1 l2 (dataSem_state_space_fupd (K k)
       (state_locals_fupd (K x) s)) r NONE locs /\ ~(alloc_size k =
       --((n2w 1):'a word)) /\
     FLOOKUP (wordSem_state_store r) (Temp (n2w 29)) = FLOOKUP
       (wordSem_state_store t) (Temp (n2w 29)) /\ state_code
     r = wordSem_state_code t /\ state_code_buffer
     r = wordSem_state_code_buffer t /\ wordSem_state_data_buffer
     r = wordSem_state_data_buffer t /\ compile_oracle
     r = wordSem_state_compile_oracle t /\
     q = NONE)`,
  CHEAT_TAC);;


let cut_names_adjust_set_insert_ODD = prove
 (`ODD n ==> cut_names (adjust_set the_names) (insert n w s) =
             cut_names (adjust_set the_names) s`,
  CHEAT_TAC);;

let cut_env_adjust_sets_ODD = prove
 (`ODD n ==> cut_env (adjust_sets names) (insert n w s) =
           cut_env (adjust_sets names) s`,
  CHEAT_TAC);;

let cut_envs_adjust_sets_ODD = prove
 (`ODD n ==> cut_envs (adjust_sets names) (insert n w s) =
           cut_envs (adjust_sets names) s`,
  CHEAT_TAC);;

let alloc_locals_insert_1 = prove
 (`wordSem_alloc k (adjust_sets names) (wordSem_state_locals_fupd (K
  (insert 1 w (wordSem_state_locals t))) t) =
   wordSem_alloc k (adjust_sets names) t`,
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:7990-8015: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_GiveUp *)

let insert_insert_3_1 = prove
 (`insert 3 x (insert 1 y t) = insert 1 y (insert 3 x t)`,
  CHEAT_TAC);;

let shift_lsl = prove
 (`good_dimindex (:'a) ==> w << backend_common_word_shift (:'a) = w *
  (bytes_in_word:'a word)`,
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:8030-8035: a proof *)

let alloc_size_dimword = prove
 (`good_dimindex (:'a) ==>
    alloc_size (dimword (:'a)) = --((n2w 1):'a word)`,
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:8045-8049: ML code, not ported *)

let alloc_fail = prove
 (`good_dimindex (:'a) /\ state_rel c l1 l2 ((s:('c,'ffi)dataSem_state))
  t NONE locs /\
   dataSem_cut_env names (dataSem_state_locals s) = SOME x /\
   wordSem_alloc (--((n2w 1):'a word)) (adjust_sets names) t = (q,r)
     ==>
   (q = SOME wordSem_NotEnoughSpace ==> state_ffi r =
     dataSem_state_ffi s /\ option_le (state_stack_max r)
     (dataSem_state_stack_max s)) /\
   q = SOME wordSem_NotEnoughSpace`,
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:8061-8070: a theorem that HOL4
   states as the value of an ML expression: word_exp_rw *)

(* get_var_set_var_thm *)
let data_to_word_gcProof_get_var_set_var_thm = prove
 (`wordSem_get_var n (set_var m x y) = (if n = m then SOME x else
  get_var n y)`,
  CHEAT_TAC);;

let state_rel_cut_env_cut_env = prove
 (`state_rel c l1 l2 s t NONE locs /\
    dataSem_cut_env names (state_locals s) = SOME x /\
    wordSem_cut_env (adjust_sets names) (wordSem_state_locals t) =
      SOME y ==>
    state_rel c l1 l2 (state_locals_fupd (K x) s)
      (wordSem_state_locals_fupd (K y) t) NONE locs`,
  CHEAT_TAC);;

let domain_adjust_set_EVEN = prove
 (`k IN domain (adjust_set s) ==> EVEN k`,
  CHEAT_TAC);;

let cut_env_adjust_sets_insert_ODD = prove
 (`ODD n ==>
   cut_env (adjust_sets names) (insert n w t) =
   cut_env (adjust_sets names) t`,
  CHEAT_TAC);;

let cut_envs_adjust_sets_insert_ODD = prove
 (`ODD n ==>
   cut_envs (adjust_sets names) (insert n w t) =
   cut_envs (adjust_sets names) t`,
  CHEAT_TAC);;

let cut_names_insert_1_insert_1 = prove
 (`cut_names (insert 1 one (adjust_set names)) (insert 1 w t) =
   (match cut_names (adjust_set names) (t:'a spt) with NONE -> NONE
     | SOME e -> SOME (insert 1 w e))`,
  CHEAT_TAC);;

let alloc_store = prove
 (`wordSem_alloc k names t = (NONE,s1) /\ wordSem_state_gc_fun
   t = word_gc_fun c /\
   FLOOKUP (wordSem_state_store t) CurrHeap = SOME (wordLang_Word cu)
     /\
   FLOOKUP (wordSem_state_store t) TriggerGC = SOME (wordLang_Word
     end) /\
   FLOOKUP (wordSem_state_store t) NextFree = SOME (wordLang_Word
     next') /\
   FLOOKUP (wordSem_state_store t) HeapLength = SOME (wordLang_Word
     heap_length1) ==>
   (?end next' heap_length1 cu.
     FLOOKUP (wordSem_state_store s1) CurrHeap = SOME (wordLang_Word
       cu) /\
     FLOOKUP (wordSem_state_store s1) TriggerGC = SOME (wordLang_Word
       end) /\
     FLOOKUP (wordSem_state_store s1) NextFree = SOME (wordLang_Word
       next') /\
     FLOOKUP (wordSem_state_store s1) HeapLength = SOME
       (wordLang_Word heap_length1))`,
  CHEAT_TAC);;

(* [local] *)
let alloc_with_locals_1_3 = prove
 (`wordSem_alloc k (adjust_sets names) (wordSem_state_locals_fupd (K
  (insert 1 w1 (insert 3 w2 (wordSem_state_locals t)))) t) =
   wordSem_alloc k (adjust_sets names) t`,
  CHEAT_TAC);;

let cut_names_imp_wf = prove
 (`cut_names s t = SOME x ==> sptree_wf x`,
  CHEAT_TAC);;

let cut_env_insert_1 = prove
 (`cut_env (FST (adjust_sets names),insert 1 one (SND (adjust_sets
  names))) (insert 1 w t) =
   (match cut_env (adjust_sets names) t with NONE -> NONE | SOME v
     -> SOME (insert 1 w v))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:8272-8459: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   AllocVar_thm_gen *)

(* HOL4 data_to_word_gcProofScript.sml:8461-8498: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   AllocVar_thm *)


(* HOL4 data_to_word_gcProofScript.sml:8501-8562: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   AllocVar_thm_nary *)

let state_rel_with_clock_0 = prove
 (`state_rel c r1 r2 s t x locs ==>
    state_rel c r1 r2 (dataSem_state_space_fupd (K 0) s) t x locs`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_heap_non_empty_limit = prove
 (cake_as_vars (fun () ->
    `~(limit = 0) ==>
           word_heap other (heap_expand limit) c =
           SEP_EXISTS (\w1. set_sep_one (other,w1) *
             word_heap (other + bytes_in_word) (heap_expand
               (limit - 1)) c)`),
  CHEAT_TAC);;

let small_int_0 = prove
 (`good_dimindex (:'a) ==> small_int (:'a) (&0)`,
  CHEAT_TAC);;

let state_rel_imp_clock = prove
 (`state_rel c l1 l2 s t NONE locs ==> state_clock s =
  wordSem_state_clock t`,
  CHEAT_TAC);;

let get_vars_SOME_IFF_data = prove
 (`(get_vars [] t = SOME [] <=> T) /\
    (get_vars (x :: xs) t = SOME (y :: ys) <=>
     dataSem_get_var x t = SOME y /\
     get_vars xs t = SOME ys)`,
  CHEAT_TAC);;

let get_vars_SOME_IFF_data_eq = prove
 (`((get_vars [] t = SOME z) <=> (z = [])) /\
    (get_vars (x :: xs) t = SOME z <=>
    (?y ys. z = y :: ys /\ dataSem_get_var x t = SOME y /\
           get_vars xs t = SOME ys))`,
  CHEAT_TAC);;

let get_vars_SOME_IFF = prove
 (`(get_vars [] t = SOME [] <=> T) /\
    (get_vars (x :: xs) t = SOME (y :: ys) <=>
     get_var x t = SOME y /\
     wordSem_get_vars xs t = SOME ys)`,
  CHEAT_TAC);;

let get_vars_SOME_IFF_eq = prove
 (`((get_vars [] t = SOME z) <=> (z = [])) /\
    (get_vars (x :: xs) t = SOME z <=>
    (?y ys. z = y :: ys /\ wordSem_get_var x t = SOME y /\
           get_vars xs t = SOME ys))`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let memory_rel_get_vars_IMP_lemma = prove
 (cake_as_vars (fun () ->
    `memory_rel c be ts refs sp st m dm
       (join_env ll
          (toAList (inter (wordSem_state_locals t) (adjust_set
            ll))) ++ envs) /\
      get_vars n ll = SOME x /\
      get_vars (MAP adjust_var n) (t:('a,'c,'ffi)wordSem_state) =
        SOME w ==>
      memory_rel c be ts refs sp st m dm
        (ZIP x w ++
         join_env ll
           (toAList (inter (wordSem_state_locals t) (adjust_set
             ll))) ++ envs)`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let memory_rel_get_vars_IMP = prove
 (cake_as_vars (fun () ->
    `memory_rel c be ts (dataSem_state_refs s) sp st m dm
       (join_env (dataSem_state_locals s)
          (toAList (inter (wordSem_state_locals t) (adjust_set
            (dataSem_state_locals s)))) ++ envs) /\
      get_vars n (dataSem_state_locals
        ((s:('c,'ffi)dataSem_state))) = SOME x /\
      get_vars (MAP adjust_var n) (t:('a,'c,'ffi)wordSem_state) =
        SOME w ==>
      memory_rel c be ts (dataSem_state_refs s) sp st m dm
        (ZIP x w ++
         join_env (dataSem_state_locals s)
           (toAList (inter (wordSem_state_locals t) (adjust_set
             (dataSem_state_locals s)))) ++ envs)`),
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:8671-8674: a theorem that HOL4
   states as the value of an ML expression: memory_rel_get_var_IMP *)

let lookup_RefByte_location = prove
 (`state_rel c l1 l2 x t NONE locs ==>
    sptree_lookup RefByte_location (wordSem_state_code t) = SOME
      (4,RefByte_code c) /\
    sptree_lookup RefArray_location (wordSem_state_code t) = SOME
      (3,RefArray_code c) /\
    sptree_lookup FromList_location (wordSem_state_code t) = SOME
      (4,FromList_code c) /\
    sptree_lookup Replicate_location (wordSem_state_code t) = SOME
      (5,Replicate_code) /\
    sptree_lookup AnyArith_location (wordSem_state_code t) = SOME
      (4,AnyArith_code c) /\
    sptree_lookup Add_location (wordSem_state_code t) = SOME
      (3,Add_code) /\
    sptree_lookup Sub_location (wordSem_state_code t) = SOME
      (3,Sub_code) /\
    sptree_lookup Mul_location (wordSem_state_code t) = SOME
      (3,Mul_code) /\
    sptree_lookup Div_location (wordSem_state_code t) = SOME
      (3,Div_code) /\
    sptree_lookup Mod_location (wordSem_state_code t) = SOME
      (3,Mod_code)`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let memory_rel_insert = prove
 (cake_as_vars (fun () ->
    `memory_rel c be ts refs sp st m dm
       ([(x,w)] ++ join_env d (toAList (inter l (adjust_set d))) ++
         xs) ==>
      memory_rel c be ts refs sp st m dm
       (join_env (insert dest x d)
          (toAList
             (inter (insert (adjust_var dest) w l)
                (adjust_set (insert dest x d)))) ++ xs)`),
  CHEAT_TAC);;

let state_rel_IMP_Number_arg = prove
 (`state_rel c l1 l2 (call_env xs ss s) (call_env ys ss t) NONE locs /\
    n < dimword (:'a) DIV 16 /\ LENGTH ys = LENGTH xs + 1 ==>
    state_rel c l1 l2
      (call_env (xs ++ [Number (&n)]) ss s)
      (call_env (ys ++ [wordLang_Word (n2w (4 * n):'a word)]) ss t)
        NONE locs`,
  CHEAT_TAC);;

let state_rel_cut_IMP = prove
 (`state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
   cut_state_opt names_opt s = SOME x ==>
   state_rel c l1 l2 x t NONE locs`,
  CHEAT_TAC);;

let get_vars_1_IMP = prove
 (`wordSem_get_vars [x1] s = SOME [v1] ==>
   get_var x1 s = SOME v1`,
  CHEAT_TAC);;

let get_vars_2_IMP = prove
 (`(wordSem_get_vars [x1; x2] s = SOME [v1; v2]) ==>
    get_var x1 s = SOME v1 /\
    get_var x2 s = SOME v2`,
  CHEAT_TAC);;

let get_vars_3_IMP = prove
 (`(wordSem_get_vars [x1; x2; x3] s = SOME [v1; v2; v3]) ==>
    get_var x1 s = SOME v1 /\
    get_var x2 s = SOME v2 /\
    get_var x3 s = SOME v3`,
  CHEAT_TAC);;

let inter_insert_ODD_adjust_set = prove
 (`!k. ODD k ==>
      inter (insert (adjust_var dest) w (insert k v s)) (adjust_set
        t) =
      inter (insert (adjust_var dest) w s) (adjust_set t)`,
  CHEAT_TAC);;

let inter_insert_ODD_adjust_set_alt = prove
 (`!k. ODD k ==>
      inter (insert k v s) (adjust_set t) =
      inter s (adjust_set t)`,
  CHEAT_TAC);;

let inter_delete_ODD_adjust_set_alt = prove
 (`!k. ODD k ==>
      inter (delete k s) (adjust_set t) =
      inter s (adjust_set t)`,
  CHEAT_TAC);;

(* [simp] *)
let get_vars_termdep = prove
 (`!xs. get_vars xs (wordSem_state_termdep_fupd (K
  (wordSem_state_termdep t - 1)) t) = get_vars xs t`,
  CHEAT_TAC);;

let join_env_locals_def = new_definition
  `join_env_locals sl tl =
     join_env sl (toAList (inter tl (adjust_set sl)))`;;

(* [simp] *)
let join_env_locals_insert_odd = prove
 (`ODD n ==> join_env_locals sl (insert n v ls) = join_env_locals sl
  ls`,
  CHEAT_TAC);;

(* [simp] *)
let join_env_locals_insert_dest_odd = prove
 (`ODD n ==> join_env_locals sl (insert (adjust_var dest) w (insert n
  v ls)) = join_env_locals sl (insert (adjust_var dest) w ls)`,
  CHEAT_TAC);;

(* [simp] *)
let MustTerminate_limit_NOT_0 = prove
 (`~(MustTerminate_limit (:'a) = 0)`,
  CHEAT_TAC);;

(* [simp] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let memory_rel_Temp = prove
 (cake_as_vars (fun () ->
    `memory_rel c be ts refs sp (st |+ (Temp i,w)) m dm vars <=>
      memory_rel c be ts refs sp st m dm vars`),
  CHEAT_TAC);;

(* [simp] *)
let adjust_var_not_15 = prove
 (`~(adjust_var a2 = 15)`,
  CHEAT_TAC);;

let get_vars_sing = prove
 (`wordSem_get_vars [n] t = SOME x <=> (?x1. get_vars [n] t = SOME
  [x1] /\ x = [x1])`,
  CHEAT_TAC);;

(* HOL4 data_to_word_gcProofScript.sml:8846-8850: a theorem that HOL4
   states as the value of an ML expression: word_ml_inv_get_var_IMP *)

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["stack_alloc";
   "vars"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
