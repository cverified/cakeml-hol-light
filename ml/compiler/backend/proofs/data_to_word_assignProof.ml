(* ======================================================== *)
(*  data_to_word_assignProof: ported from HOL4's
    compiler/backend/proofs/data_to_word_assignProofScript.sml
    A proof theory, with 5 definitions and 319 theorems.  Needed by
    data_to_wordProof.ml.  *)
(* ======================================================== *)

(*
  Part of the correctness proof for data_to_word
*)

needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "compiler/backend/backend_common.ml";;
(* for word_add_carry *)
needs "compiler/backend/bvi_to_data.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/gc/copying_gc.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "compiler/backend/gc/gen_gc_partial.ml";;
needs "compiler/backend/proofs/data_to_word_bignumProof.ml";;
needs "compiler/backend/proofs/data_to_word_gcProof.ml";;
needs "compiler/backend/proofs/data_to_word_memoryProof.ml";;
needs "compiler/backend/proofs/word_bignumProof.ml";;
needs "compiler/backend/proofs/word_gcFunctions.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "lib/alignment.ml";;
needs "lib/byte.ml";;
needs "lib/integer_word.ml";;
needs "lib/multiword.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "data_to_word_assignProof"
  ["backendProps"; "backend_common"; "bvi_to_data"; "copying_gc";
   "dataProps"; "dataSem"; "data_to_word"; "data_to_word_bignumProof";
   "data_to_word_gcProof"; "data_to_word_memoryProof"; "gc_shared"; "gen_gc";
   "gen_gc_partial"; "semanticsProps"; "wordLang"; "wordProps"; "wordSem";
   "word_bignum"; "word_bignumProof"; "word_gcFunctions"];;

let _ = do_list hide_constant ["ABS"; "Num"; "parts"; "test"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["code_buffer","code_buffer";
   "data_buffer","data_buffer";
   "vars","vars"];;
(* HOL4 ancestors outside the port: int_bitwise While *)

(* HOL4 data_to_word_assignProofScript.sml:28-29: ML code, not ported *)

(* HOL4 data_to_word_assignProofScript.sml:38: the overload lookup, which
   the port expands *)

(* HOL4 data_to_word_assignProofScript.sml:40-42: ML code, not ported *)

(* HOL4 data_to_word_assignProofScript.sml:44-45: a proof *)

(* HOL4 data_to_word_assignProofScript.sml:47-48: ML code, not ported *)

(* HOL4 data_to_word_assignProofScript.sml:50-53: ML code, not ported *)

(* HOL4 data_to_word_assignProofScript.sml:55-60: a proof *)

(* This list must list all auxiliary definitions used in assign_def *)
let assign_def_extras =
  end_itlist CONJ [LoadWord64_def; WriteWord64_def; BignumHalt_def;
  LoadBignum_def; AnyArith_code_def; add_code_def; sub_code_def;
  mul_code_def; div_code_def; mod_code_def; compare1_code_def;
  compare_code_def; equal1_code_def; equal_code_def; LongDiv1_code_def;
  LongDiv_code_def; ShiftVar_def; generated_bignum_stubs_eq; DivCode_def;
  AddNumSize_def; AnyHeader_def; WriteWord64_on_32_def;
  WriteWord32_on_32_def; AllocVar_def; SilentFFI_def; WordOp64_on_32_def;
  WordShift64_on_32_def; make_ptr_bits_code_def];;

let get_vars_SING = prove
 (`dataSem_get_vars args s = SOME [w] ==> (?y. args = [y])`,
  CHEAT_TAC);;

let state_rel_IMP_tstamps = prove
 (`data_to_word_gcProof_state_rel c l1 l2 x t p locs ==>
   (?next_stamp. dataSem_state_tstamps x = SOME next_stamp)`,
  CHEAT_TAC);;

let INT_EQ_NUM_LEMMA = prove
 (`(&0) <= (i:int) <=> (?index. i = &index)`,
  CHEAT_TAC);;

(* [local] *)
let push_if = prove
 (`(!f x y b. (if b then f x else f y) = f (if b then x else y)) /\
   (!f h x b. (if b then f x else h x) = (if b then f else h) x)`,
  CHEAT_TAC);;

(* [local] *)
let split_if = prove
 (`(if b then f x else h y) = (if b then f else h) (if b then x else y)`,
  CHEAT_TAC);;

let cut_env_IMP_domain = prove
 (`cut_names x y = SOME t ==> sptree_domain t = sptree_domain x`,
  CHEAT_TAC);;

let cut_envs_wf = prove
 (`cut_envs kept_names t = SOME (y1,y2) ==> sptree_wf y1 /\ sptree_wf y2`,
  CHEAT_TAC);;

let domain_list_insert_thm = prove
 (`!l names.
     sptree_domain (list_insert l names) = set_of_list l UNION
       sptree_domain names`,
  CHEAT_TAC);;

let cut_env_lookup = prove
 (`wordSem_cut_env names t = SOME y /\
   sptree_lookup n y = SOME a ==>
   sptree_lookup n t = SOME a`,
  CHEAT_TAC);;

let cut_env_get_vars_get_vars = prove
 (`!vs ws ws'.
     wordSem_cut_env kept_names (wordSem_state_locals t) = SOME y /\
     wordSem_get_vars vs (wordSem_state_locals_fupd (K y) t) = SOME ws /\
     wordSem_get_vars vs t = SOME ws' ==>
     ws = ws'`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let memory_rel_lookup_var_IMP = prove
 (cake_as_vars (fun () ->
    `memory_rel c be ts refs sp st m dm
       (APPEND (join_env ll
          (toAList (inter (wordSem_state_locals t) (adjust_set ll))))
            envs) /\
      dataSem_get_vars n ll = SOME x /\
      wordSem_get_vars (MAP adjust_var n) (t:('a,'c,'ffi)wordSem_state) =
        SOME w ==>
      memory_rel c be ts refs sp st m dm
        (APPEND (APPEND (ZIP x w)
         (join_env ll
           (toAList (inter (wordSem_state_locals t) (adjust_set ll)))))
             envs)`),
  CHEAT_TAC);;

let get_real_offset_lemma = prove
 (`wordSem_get_var v t = SOME (word_Word i_w) /\
    good_dimindex (:'a) /\
    get_real_offset i_w = SOME y ==>
    wordSem_word_exp t (real_offset c v) = SOME (word_Word (y:'a word))`,
  CHEAT_TAC);;

let state_rel_push_env_loc = prove
 (`data_to_word_gcProof_state_rel c n l s (wordSem_call_env args b
  (wordSem_push_env (y1,y2) NONE t)) ys (CONS (l1,l2) locs) ==>
   sptree_lookup 0 y1 = SOME (word_Loc l1 l2)`,
  CHEAT_TAC);;

let evaluate_IMP_domain_union = prove
 (`wordSem_evaluate (p,wordSem_state_termdep_fupd (K tp)
  (wordSem_state_clock_fupd (K ck) (wordSem_call_env args b (wordSem_push_env
  (y1,y2) NONE (t:('a,'c,'ffi)wordSem_state))))) = (SOME (wordSem_Result ret1
  ret2),t1) /\
   wordSem_pop_env t1 = SOME t2 /\
   sptree_lookup 0 y1 = SOME (word_Loc l1 l2) /\
   cut_envs (adjust_sets kept_names) (wordSem_state_locals t) = SOME (y1,y2)
     ==>
   sptree_domain (wordSem_state_locals t2) = sptree_domain y1 UNION
     sptree_domain y2 /\
   sptree_lookup 0 (wordSem_state_locals t2) = SOME (word_Loc l1 l2)`,
  CHEAT_TAC);;

let get_real_byte_offset_lemma = prove
 (`wordSem_get_var v t = SOME (word_Word (w:'a word)) /\ good_dimindex (:'a)
  ==>
   wordSem_word_exp t (real_byte_offset v) = SOME (word_Word
     (bytes_in_word + (w >>> 2)))`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let reorder_lemma = prove
 (cake_as_vars (fun () ->
    `memory_rel c be ts (dataSem_state_refs x) (dataSem_state_space x)
  (wordSem_state_store t) (wordSem_state_memory t) (wordSem_state_mdomain t)
  (CONS x1 (CONS x2 (CONS x3 xs))) ==>
     memory_rel c be ts (dataSem_state_refs x) (dataSem_state_space x)
       (wordSem_state_store t) (wordSem_state_memory t)
       (wordSem_state_mdomain t) (CONS x3 (CONS x1 (CONS x2 xs)))`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let reorder_2_lemma = prove
 (cake_as_vars (fun () ->
    `memory_rel c be ts (dataSem_state_refs x) (dataSem_state_space x)
  (wordSem_state_store t) (wordSem_state_memory t) (wordSem_state_mdomain t)
  (CONS x1 (CONS x2 xs)) ==>
     memory_rel c be ts (dataSem_state_refs x) (dataSem_state_space x)
       (wordSem_state_store t) (wordSem_state_memory t)
       (wordSem_state_mdomain t) (CONS x2 (CONS x1 xs))`),
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:263-289: a theorem that HOL4
   states as the value of an ML expression: evaluate_StoreEach *)

let get_vars_adjust_var = prove
 (`ODD k ==>
    wordSem_get_vars (MAP adjust_var args) (wordSem_state_locals_fupd (K
      (sptree_insert k w s)) t) =
    wordSem_get_vars (MAP adjust_var args) (wordSem_state_locals_fupd (K
      s) t)`,
  CHEAT_TAC);;

let get_vars_with_store = prove
 (`!args. wordSem_get_vars args (wordSem_state_store_fupd (K s)
  (wordSem_state_locals_fupd (K (wordSem_state_locals t)) t)) =
           wordSem_get_vars args t`,
  CHEAT_TAC);;

let word_less_lemma1 = prove
 (`v2 < (v1:'a word) <=> ~(v1 <= v2)`,
  CHEAT_TAC);;

let get_vars_2_imp = prove
 (`wordSem_get_vars [x1; x2] s = SOME [y1; y2] ==>
    wordSem_get_var x1 s = SOME y1 /\
    wordSem_get_var x2 s = SOME y2`,
  CHEAT_TAC);;

let get_vars_1_imp = prove
 (`wordSem_get_vars [x1] s = SOME [y1] ==>
    wordSem_get_var x1 s = SOME y1`,
  CHEAT_TAC);;

(* LESS_DIV_16_IMP *)
let data_to_word_assignProof_LESS_DIV_16_IMP = prove
 (`n < k DIV 16 ==> 16 * n + 2 < (k:num)`,
  CHEAT_TAC);;

let lookup_loc_lemma = prove
 (`env_to_list y2 permute = (l',permute') /\
   cut_envs (adjust_sets keep_names) locals = SOME (y1,y2) /\
   sptree_lookup 0 (sptree_union y2 y1) = SOME (word_Loc l1 l2) ==>
   ALOOKUP l' 0 = NONE /\ sptree_lookup 0 y1 = SOME (word_Loc l1 l2)`,
  CHEAT_TAC);;

let word_exp_real_addr = prove
 (`get_real_addr c (wordSem_state_store t) ptr_w = SOME a /\
    shift_length c < dimindex (:'a) /\ good_dimindex (:'a) /\
    sptree_lookup (adjust_var a1) (wordSem_state_locals
      (t:('a,'c,'ffi)wordSem_state)) = SOME (word_Word ptr_w) ==>
    (!w. wordSem_word_exp (wordSem_state_locals_fupd (K (sptree_insert 1
      (word_Word (w:'a word)) (wordSem_state_locals t))) t)
          (real_addr c (adjust_var a1)) = SOME (word_Word a))`,
  CHEAT_TAC);;

let word_exp_real_addr_2 = prove
 (`get_real_addr c (wordSem_state_store (t:('a,'c,'ffi)wordSem_state)) ptr_w =
  SOME a /\
    shift_length c < dimindex (:'a) /\ good_dimindex (:'a) /\
    sptree_lookup (adjust_var a1) (wordSem_state_locals t) = SOME (word_Word
      ptr_w) ==>
    (!w1 w2.
      wordSem_word_exp
        (wordSem_state_locals_fupd (K (sptree_insert 3 (word_Word (w1:'a
          word)) (sptree_insert 1 (word_Word w2) (wordSem_state_locals t)))) t)
        (real_addr c (adjust_var a1)) = SOME (word_Word a))`,
  CHEAT_TAC);;

let encode_header_IMP_BIT0 = prove
 (`encode_header c tag l = SOME w ==> FAPPLY w 0`,
  CHEAT_TAC);;

let get_addr_inj = prove
 (`p1 * 2 EXP shift_length c < dimword (:'a) /\
   p2 * 2 EXP shift_length c < dimword (:'a) /\
   get_addr c p1 (word_Word ((n2w 0):'a word)) = get_addr c p2 (word_Word
     (n2w 0)) ==> p1 = p2`,
  CHEAT_TAC);;

let Word64Rep_inj = prove
 (`good_dimindex (:'a) ==>
   (Word64Rep (:'a) w1 = Word64Rep (:'a) w2 <=> w1 = w2)`,
  CHEAT_TAC);;

let IMP_read_bytearray_GENLIST = prove
 (`!ls len a.
   len = LENGTH ls /\
   (!i. i < len ==> g (a + n2w i) = SOME (EL i ls)) ==> read_bytearray a
     len g = SOME ls`,
  CHEAT_TAC);;

let lookup_IMP_insert_EQ = prove
 (`!t x y. sptree_lookup x t = SOME y ==> sptree_insert x y t = t`,
  CHEAT_TAC);;

(* set_vars_sing *)
let data_to_word_assignProof_set_vars_sing = prove
 (`wordSem_set_vars [n] [w] t = wordSem_set_var n w t`,
  CHEAT_TAC);;

let NONNEG_INT = prove
 (`(&0) <= (i:int) ==> (?j. i = &j)`,
  CHEAT_TAC);;

let BIT_X_1 = prove
 (`BIT i 1 = (i = 0)`,
  CHEAT_TAC);;

let minus_2_word_and_id = prove
 (`~(FAPPLY w 0) ==> (--(n2w 2) && w) = w`,
  CHEAT_TAC);;

let FOUR_MUL_LSL = prove
 (`n2w (4 * i) << k = n2w i << (k + 2)`,
  CHEAT_TAC);;

let evaluate_BignumHalt = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
    wordSem_get_var reg t = SOME (word_Word w) ==>
    (?r. (wordSem_evaluate (BignumHalt reg,t) =
          (if FAPPLY w 0 then (SOME wordSem_NotEnoughSpace,r)
          else (NONE,t))) /\ wordSem_state_ffi r = dataSem_state_ffi s
            /\ wordSem_state_ffi t = dataSem_state_ffi s)`,
  CHEAT_TAC);;

(* TODO: should probably replace evaluate_GiveUp directly *)
let evaluate_GiveUp2 = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE
  locs ==>
   (?r. wordSem_evaluate (GiveUp,t) = (SOME wordSem_NotEnoughSpace,r)
     /\ wordSem_state_ffi
     r = dataSem_state_ffi s /\ wordSem_state_ffi t = dataSem_state_ffi s /\
     option_le (wordSem_state_stack_max r) (wordSem_state_stack_max t))`,
  CHEAT_TAC);;

let evaluate_BignumHalt2 = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
    wordSem_get_var reg t = SOME (word_Word w) ==>
    (?r. (wordSem_evaluate (BignumHalt reg,t) =
          (if FAPPLY w 0 then (SOME wordSem_NotEnoughSpace,r)
          else (NONE,t))) /\ wordSem_state_ffi r = dataSem_state_ffi s
            /\ wordSem_state_ffi t = dataSem_state_ffi s /\
                           option_le (wordSem_state_stack_max r)
                             (wordSem_state_stack_max t))`,
  CHEAT_TAC);;

let state_rel_get_var_Number_IMP_alt = prove
 (`!k i. data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
          dataSem_get_var k (dataSem_state_locals s) = SOME (dataSem_Number
            i) /\
          wordSem_get_var (2 * k + 2) t = SOME a1 ==>
          (?(w:'a word). a1 = word_Word w /\ FAPPLY w 0 = ~(small_int
            (:'a) i))`,
  CHEAT_TAC);;

(* TODO: move to sptreeTheory *)
(* [local] *)
let EXISTS_NOT_IN_spt_DOMAIN = prove
 (`?x. ~(x IN sptree_domain (refs:'a spt))`,
  CHEAT_TAC);;

(* TODO: move to sptreeTheory *)
let LEAST_NOTIN_spt_DOMAIN = prove
 (`!refs. ~((minimal x. ~(x IN sptree_domain (refs:'a spt))) IN sptree_domain
  refs)`,
  CHEAT_TAC);;

(*TODO: move to backendProps *)
let option_le_add_indv = prove
 (`option_le (OPTION_MAP2 (+) n m) r ==> option_le n r /\ option_le m r`,
  CHEAT_TAC);;

let option_le_add_drop_right = prove
 (`option_le x y ==>
   option_le x (OPTION_MAP2 (+) z y)`,
  CHEAT_TAC);;

let word_exp_SmallLsr = prove
 (`n < dimindex (:'a) ==>
    wordSem_word_exp s (SmallLsr e n) =
       (match wordSem_word_exp s e with SOME (word_Word w) -> SOME
         (word_Word ((w:'a word) >>> n))
         | res -> (if n = 0 then res else NONE))`,
  CHEAT_TAC);;

let evaluate_MakeBytes = prove
 (`good_dimindex (:'a) ==>
    wordSem_evaluate (MakeBytes n,s) =
      (match wordSem_get_var n s with SOME (word_Word w) ->
        (NONE,wordSem_set_var n (word_Word (word_of_byte ((w:'a word) >>> 2)))
        s)
      | _ -> (SOME wordSem_Error,s))`,
  CHEAT_TAC);;

let w2w_shift_shift = prove
 (`good_dimindex (:'a) ==> ((w2w (w:word8) << 2 >>> 2):'a word) = w2w w`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:629-631: a proof *)

let evaluate_WriteLastBytes = prove
 (`good_dimindex (:'a) /\ w2n n < dimindex (:'a) DIV 8 /\
   wordSem_get_vars [av; bv; nv] (s:('a,'c,'ffi)wordSem_state) = SOME
     [word_Word (a:'a word); word_Word b; word_Word n] /\
   byte_aligned a /\ a IN wordSem_state_mdomain s /\ wordSem_state_memory s
     a = word_Word w ==>
   wordSem_evaluate (WriteLastBytes av bv nv,s) =
     (NONE,wordSem_state_memory_fupd (K ((a =+ word_Word (last_bytes (w2n
       n) (w2w b) (n2w 0) w (wordSem_state_be s))) (wordSem_state_memory s)))
       s)`,
  CHEAT_TAC);;

(* byte_aligned_bytes_in_word *)
let data_to_word_assignProof_byte_aligned_bytes_in_word = prove
 (`good_dimindex (:'a) ==>
    byte_aligned (w * bytes_in_word) /\
    byte_aligned (bytes_in_word * (w:'a word))`,
  CHEAT_TAC);;

let is_env_def = new_definition
  `is_env st = (?n vs. st = dataSem_Env n vs)`;;

(* TODO: copypasta from costPropsScript *)
let size_of_Number_head = prove
 (`!vs lims refs seen n b.
   small_num (limits_arch_64_bit lims) n ==>
   (size_of lims (CONS (dataSem_Number n) vs) refs seen = size_of lims vs
     refs seen)`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:707-710: a theorem that HOL4
   states as the value of an ML expression: ADD4DIV4 *)

(* HOL4 data_to_word_assignProofScript.sml:712-715: a theorem that HOL4
   states as the value of an ML expression: ADD8DIV8 *)

let RefByte_thm = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE
  locs /\
    dataSem_get_vars [0; 1; 2] (dataSem_state_locals s) = SOME (APPEND vals
      [dataSem_Number (&(if fl then 0 else 4))]) /\ wordSem_state_clock
    t = MustTerminate_limit (:'a) - 1 /\
    dataSem_pop_env s = SOME s1 /\ is_env (HD (dataSem_state_stack s))
      /\ dataSem_state_locals_size
    s = sptree_lookup RefByte_location (dataSem_state_stack_frame_sizes s)
      /\
    dataSem_do_app (clos_MemOp (clos_RefByte fl)) vals s1 = Rval (v,s2) ==>
    (?q r new_c.
      wordSem_evaluate (RefByte_code c,t) = (q,r) /\
      (if q = SOME wordSem_NotEnoughSpace then wordSem_state_ffi
        r = wordSem_state_ffi t /\
        option_le (wordSem_state_stack_max r) (dataSem_state_stack_max s2)
          /\
        (~(data_to_word_config_gc_kind c = data_to_word_None)
          /\ no_thunks_in_refs (dataSem_state_refs s) ==>
         (match vals with
              (CONS (dataSem_Number i) _) ->
              (i < (&0) \/
              ~(small_num (limits_arch_64_bit (dataSem_state_limits s)) i)
                \/
              ~(num_of_int i DIV (arch_size (dataSem_state_limits s) DIV 8)
                < dimword (:'a) DIV arch_size (dataSem_state_limits s)) \/
              ~(num_of_int i DIV (arch_size (dataSem_state_limits s) DIV 8)
                + 1 < (2 EXP data_to_word_config_len_size c)) \/
                limits_heap_limit (dataSem_state_limits
              s1) <
              size_of_heap s1 + num_of_int i DIV (arch_size
                (dataSem_state_limits s) DIV 8) + 2)))
      else ?rv. q = SOME (wordSem_Result (word_Loc l1 l2) [rv]) /\
             data_to_word_gcProof_state_rel c r1 r2
               (dataSem_state_stack_fupd (K (dataSem_state_stack s))
               (dataSem_state_clock_fupd (K new_c)
               (dataSem_state_locals_size_fupd (K (SOME 0))
               (dataSem_state_locals_fupd (K LN) s2))))
                r (SOME [(v,rv)]) locs))`,
  CHEAT_TAC);;

(* TODO: copypaste from costProps *)
let size_of_seen_SUBSET = prove
 (`!lims vs refs seen n1 seen1 refs1.
   (size_of lims vs refs seen = (n1,refs1,seen1)) ==> sptree_domain seen
     SUBSET sptree_domain seen1`,
  CHEAT_TAC);;

let size_of_seen_Block = prove
 (`!lims vs refs seen n1 refs1 seen1 ts tag l.
    size_of lims vs refs seen = (n1,refs1,seen1) ==>
    (MEM (dataSem_Block ts tag l) vs /\ ~(l = []) ==>
     sptree_lookup ts seen1 = SOME one)`,
  CHEAT_TAC);;

let size_of_cons_seen_Block = prove
 (`!lims vs refs seen ts tag l.
    MEM (dataSem_Block ts tag l) vs ==>
    size_of lims (CONS (dataSem_Block ts tag l) vs) refs seen = size_of
      lims vs refs seen`,
  CHEAT_TAC);;

let state_rel_IMP_test_zero = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) vs
  locs /\
    dataSem_get_var i (dataSem_state_locals s) = SOME (dataSem_Number n) ==>
    (?w. wordSem_get_var (adjust_var i) t = SOME (word_Word w) /\ (w =
      (n2w 0) <=> (n = (&0))))`,
  CHEAT_TAC);;

let state_rel_get_var_Number_IMP = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s t vs locs /\
    dataSem_get_var i (dataSem_state_locals s) = SOME (dataSem_Number (&n))
      /\ small_int (:'a) (&n) ==>
    (?w. wordSem_get_var (adjust_var i) t = SOME (word_Word (Smallnum
      (&n):'a word)))`,
  CHEAT_TAC);;

let EXP_LEMMA1 = prove
 (`4 * n * (2 EXP k) = n * 2 EXP (k + 2)`,
  CHEAT_TAC);;

let evaluate_Maxout_bits_code = prove
 (`~(n_reg = dest) /\ n < dimword (:'a) /\ rep_len < dimindex (:'a) /\
       k < dimindex (:'a) /\
       sptree_lookup n_reg (wordSem_state_locals
         (t:('a,'c,'ffi)wordSem_state)) = SOME (word_Word (n2w n:'a word)) ==>
       wordSem_evaluate (Maxout_bits_code rep_len k dest
         n_reg,wordSem_set_var dest (word_Word w) t) =
         (NONE,wordSem_set_var dest (word_Word (w || maxout_bits n rep_len
           k)) t)`,
  CHEAT_TAC);;

(* Make_ptr_bits_thm *)
let make_ptr_bits_thm = prove
 (`~(tag_reg = dest) /\ tag1 < dimword (:'a) /\ data_to_word_config_tag_bits c
  < dimindex (:'a) /\ ~((len_reg:num) = dest) /\ len1 < dimword (:'a)
  /\ data_to_word_config_len_bits c < dimindex (:'a)
  /\ data_to_word_config_len_bits
       c + 1 < dimindex (:'a) /\
       FLOOKUP (wordSem_state_store (t:('a,'c,'ffi)wordSem_state)) NextFree
         = SOME (word_Word f) /\
       FLOOKUP (wordSem_state_store t) CurrHeap = SOME (word_Word d) /\
       sptree_lookup tag_reg (wordSem_state_locals t) = SOME (word_Word (n2w
         tag1)) /\
       sptree_lookup len_reg (wordSem_state_locals t) = SOME (word_Word (n2w
         len1)) /\
       shift_length c < dimindex (:'a) + backend_common_word_shift (:'a) ==>
       (?t1.
         wordSem_evaluate (Make_ptr_bits_code c tag_reg len_reg dest,t) =
           (NONE,wordSem_set_var dest (make_cons_ptr c (f - d) tag1
             len1:'a word_loc) t))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:1387-1391: ML code, not ported *)

let evaluate_LoadWord64 = prove
 (`memory_rel c (be:bool) ts refs sp (wordSem_state_store t)
  (wordSem_state_memory t) (wordSem_state_mdomain t) (CONS (dataSem_Word64 w,v)
  vars) /\
   shift_length c < dimindex (:'a) /\ dimindex (:'a) = 64 /\
   wordSem_get_var src (t:('a,'c,'ffi)wordSem_state) = SOME v ==>
   wordSem_evaluate (LoadWord64 c dest src,t) = (NONE,wordSem_set_var dest
     (word_Word (w2w w)) t)`,
  CHEAT_TAC);;

let evaluate_WriteWord64 = prove
 (`memory_rel c (be:bool) ts refs sp (wordSem_state_store t)
  (wordSem_state_memory t) (wordSem_state_mdomain t)
     (APPEND (join_env_locals sl (wordSem_state_locals t)) vars) /\
   wordSem_get_var src (t:('a,'c,'ffi)wordSem_state) = SOME (word_Word w) /\
   shift_length c < dimindex (:'a) /\ ~(src = 1) /\ 1 < sp /\
   dimindex (:'a) = 64 /\
   encode_header c 3 1 = SOME header /\
   (!n. IS_SOME (sptree_lookup n sl) ==> IS_SOME (sptree_lookup (adjust_var
     n) (wordSem_state_locals t))) ==>
   (?nf m' locals' v.
     wordSem_evaluate (WriteWord64 c header dest src,t) =
       (NONE,wordSem_state_locals_fupd (K locals')
         (wordSem_state_memory_fupd (K m') (wordSem_state_store_fupd (K
         (wordSem_state_store t |+ (NextFree,nf))) t))) /\
     memory_rel c be ts refs (sp - 2) (wordSem_state_store t |+
       (NextFree,nf)) m' (wordSem_state_mdomain t)
       (APPEND (join_env_locals (sptree_insert dest (dataSem_Word64 (w2w w))
         sl) locals') vars) /\
     (!n. IS_SOME (sptree_lookup n sl) ==> IS_SOME (sptree_lookup
       (adjust_var n) locals')) /\
     IS_SOME (sptree_lookup (adjust_var dest) locals') /\
     sptree_lookup 0 locals' = sptree_lookup 0 (wordSem_state_locals t))`,
  CHEAT_TAC);;

let evaluate_WriteWord64_on_32 = prove
 (`memory_rel c (be:bool) ts refs sp (wordSem_state_store t)
  (wordSem_state_memory t) (wordSem_state_mdomain t)
     (APPEND (join_env_locals sl (wordSem_state_locals t)) vars) /\
   wordSem_get_var src1 (t:('a,'c,'ffi)wordSem_state) = SOME (word_Word ((31
     >< 0) w)) /\
   wordSem_get_var src2 (t:('a,'c,'ffi)wordSem_state) = SOME (word_Word ((63
     >< 32) w)) /\
   shift_length c < dimindex (:'a) /\ ~(src1 = 1) /\ ~(src2 = 1) /\ 2 < sp
     /\
   dimindex (:'a) = 32 /\
   encode_header c 3 2 = SOME header /\
   (!n. IS_SOME (sptree_lookup n sl) ==> IS_SOME (sptree_lookup (adjust_var
     n) (wordSem_state_locals t))) ==>
   (?nf m' locals' v.
     wordSem_evaluate (WriteWord64_on_32 c header dest src1 src2,t) =
       (NONE,wordSem_state_locals_fupd (K locals')
         (wordSem_state_memory_fupd (K m') (wordSem_state_store_fupd (K
         (wordSem_state_store t |+ (NextFree,nf))) t))) /\
     memory_rel c be ts refs (sp - 3) (wordSem_state_store t |+
       (NextFree,nf)) m' (wordSem_state_mdomain t)
       (APPEND (join_env_locals (sptree_insert dest (dataSem_Word64 w) sl)
         locals') vars) /\
     (!n. IS_SOME (sptree_lookup n sl) ==> IS_SOME (sptree_lookup
       (adjust_var n) locals')) /\
     IS_SOME (sptree_lookup (adjust_var dest) locals') /\
     sptree_lookup 0 locals' = sptree_lookup 0 (wordSem_state_locals t))`,
  CHEAT_TAC);;

(* [local] *)
let Num_ABS_AND = prove
 (`num_of_int (abs (&n)) = n /\ num_of_int (abs (--(&n))) = n`,
  CHEAT_TAC);;

let evaluate_WriteWord64_on_32_num = prove
 (`memory_rel c (be:bool) ts refs sp (wordSem_state_store t)
  (wordSem_state_memory t) (wordSem_state_mdomain t)
     (APPEND (join_env_locals sl (wordSem_state_locals t)) vars) /\
   wordSem_get_var src1 (t:('a,'c,'ffi)wordSem_state) = SOME (word_Word w1)
     /\
   wordSem_get_var src2 (t:('a,'c,'ffi)wordSem_state) = SOME (word_Word w2)
     /\
   shift_length c < dimindex (:'a) /\ ~(w2 = (n2w 0)) /\ ~(src1 = 1)
     /\ ~(src2 = 1) /\ 2 < sp /\
   dimindex (:'a) = 32 /\
   encode_header c 3 2 = SOME header /\
   (!n. IS_SOME (sptree_lookup n sl) ==> IS_SOME (sptree_lookup (adjust_var
     n) (wordSem_state_locals t))) ==>
   (?nf m' locals' v.
     wordSem_evaluate (WriteWord64_on_32 c header dest src2 src1,t) =
       (NONE,wordSem_state_locals_fupd (K locals')
         (wordSem_state_memory_fupd (K m') (wordSem_state_store_fupd (K
         (wordSem_state_store t |+ (NextFree,nf))) t))) /\
     memory_rel c be ts refs (sp - 3) (wordSem_state_store t |+
       (NextFree,nf)) m' (wordSem_state_mdomain t)
       (APPEND (join_env_locals (sptree_insert dest (dataSem_Number (&(w2n
         w2 * dimword (:'a) + w2n w1))) sl) locals') vars) /\
     (!n. IS_SOME (sptree_lookup n sl) ==> IS_SOME (sptree_lookup
       (adjust_var n) locals')) /\
     IS_SOME (sptree_lookup (adjust_var dest) locals') /\
     sptree_lookup 0 locals' = sptree_lookup 0 (wordSem_state_locals t))`,
  CHEAT_TAC);;

let evaluate_WriteWord32_bignum = prove
 (`memory_rel c (be:bool) ts refs sp (wordSem_state_store t)
  (wordSem_state_memory t) (wordSem_state_mdomain t)
     (APPEND (join_env_locals sl (wordSem_state_locals t)) vars) /\
   wordSem_get_var src (t:('a,'c,'ffi)wordSem_state) = SOME (word_Word w) /\
   shift_length c < dimindex (:'a) /\ ~(src = 1) /\ 1 < sp /\
   dimindex (:'a) = 32 /\
   encode_header c 3 1 = SOME header /\
   ~(small_int (:'a) (&(w2n w))) /\
   (!n. IS_SOME (sptree_lookup n sl) ==> IS_SOME (sptree_lookup (adjust_var
     n) (wordSem_state_locals t))) ==>
   (?nf m' locals' v.
     wordSem_evaluate (WriteWord32_on_32 c header dest src,t) =
       (NONE,wordSem_state_locals_fupd (K locals') (wordSem_state_memory_fupd
       (K m') (wordSem_state_store_fupd (K (wordSem_state_store t |+
       (NextFree,nf))) t))) /\
     memory_rel c be ts refs (sp - 2) (wordSem_state_store t |+
       (NextFree,nf)) m' (wordSem_state_mdomain t)
       (APPEND (join_env_locals (sptree_insert dest (dataSem_Number (&(w2n
         w))) sl) locals') vars) /\
     (!n. IS_SOME (sptree_lookup n sl) ==> IS_SOME (sptree_lookup
       (adjust_var n) locals')) /\
     IS_SOME (sptree_lookup (adjust_var dest) locals') /\
     sptree_lookup 0 locals' = sptree_lookup 0 (wordSem_state_locals t))`,
  CHEAT_TAC);;

let evaluate_WriteWord64_bignum = prove
 (`memory_rel c (be:bool) ts refs sp (wordSem_state_store t)
  (wordSem_state_memory t) (wordSem_state_mdomain t)
     (APPEND (join_env_locals sl (wordSem_state_locals t)) vars) /\
   wordSem_get_var src (t:('a,'c,'ffi)wordSem_state) = SOME (word_Word w) /\
   shift_length c < dimindex (:'a) /\ ~(src = 1) /\ 1 < sp /\
   dimindex (:'a) = 64 /\
   encode_header c 3 1 = SOME header /\
   ~(small_int (:'a) (&(w2n w))) /\
   (!n. IS_SOME (sptree_lookup n sl) ==> IS_SOME (sptree_lookup (adjust_var
     n) (wordSem_state_locals t))) ==>
   (?nf m' locals' v.
     wordSem_evaluate (WriteWord64 c header dest src,t) =
       (NONE,wordSem_state_locals_fupd (K locals') (wordSem_state_memory_fupd
       (K m') (wordSem_state_store_fupd (K (wordSem_state_store t |+
       (NextFree,nf))) t))) /\
     memory_rel c be ts refs (sp - 2) (wordSem_state_store t |+
       (NextFree,nf)) m' (wordSem_state_mdomain t)
       (APPEND (join_env_locals (sptree_insert dest (dataSem_Number (&(w2n
         w))) sl) locals') vars) /\
     (!n. IS_SOME (sptree_lookup n sl) ==> IS_SOME (sptree_lookup
       (adjust_var n) locals')) /\
     IS_SOME (sptree_lookup (adjust_var dest) locals') /\
     sptree_lookup 0 locals' = sptree_lookup 0 (wordSem_state_locals t))`,
  CHEAT_TAC);;

let evaluate_LoadBignum = prove
 (`memory_rel c (be:bool) ts refs sp (wordSem_state_store t)
  (wordSem_state_memory t) (wordSem_state_mdomain t) (CONS (dataSem_Number i,v)
  vars) /\
   ~(small_int (:'a) i) /\ good_dimindex (:'a) /\ shift_length c < dimindex
     (:'a) /\
   wordSem_get_var src (t:('a,'c,'ffi)wordSem_state) = SOME v /\ ~(header =
     w1) ==>
   (?h junk.
   wordSem_evaluate (LoadBignum c header w1 src,t) =
     (NONE,wordSem_set_vars [w1; header; w1]
                     [word_Word (n2w (num_of_int (abs i))); (word_Word h);
                       junk] t) /\
   (((n2w 16) && h) = (n2w 0) <=> (&0) <= i))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:1765-1778: the ML values that the
   definitions below antiquote *)

(* HOL4 data_to_word_assignProofScript.sml:1780-1781: the ML values that the
   definitions below antiquote *)

(* cut_names_adjust_set_insert_1 *)
let data_to_word_assignProof_cut_names_adjust_set_insert_1 = prove
 (`cut_names (adjust_set x) (sptree_insert 1 w l) =
    cut_names (adjust_set x) l`,
  CHEAT_TAC);;

(* cut_names_adjust_set_insert_3 *)
let data_to_word_assignProof_cut_names_adjust_set_insert_3 = prove
 (`cut_names (adjust_set x) (sptree_insert 3 w l) =
    cut_names (adjust_set x) l`,
  CHEAT_TAC);;

let cut_names_adjust_set_insert_5 = prove
 (`cut_names (adjust_set x) (sptree_insert 5 w l) =
    cut_names (adjust_set x) l`,
  CHEAT_TAC);;

let word_bit_test_0 = prove
 (`((n2w 1) && w) = (n2w 0) <=> ~(word_bit 0 w)`,
  CHEAT_TAC);;

(* [local] *)
let MAP_Number_11_w2n_word8 = prove
 (`!ns ns'.
     MAP (dataSem_Number o (&) o w2n) ns = MAP (dataSem_Number o (&) o w2n)
       ns' <=>
     ns = (ns':word8 list)`,
  CHEAT_TAC);;

(* [local] *)
let MAP_Word64_11 = prove
 (`!ns ns'.
     MAP (dataSem_Word64) ns = MAP (dataSem_Word64) ns' <=>
     ns = ns'`,
  CHEAT_TAC);;

let v_to_list_EQ_SOME_NIL = prove
 (`dataSem_v_to_list hv1 = SOME [] <=> (?ts. hv1 = dataSem_Block ts 0 [])`,
  CHEAT_TAC);;

let InstallCode_code_thm = prove
 (`!(t:('a,'c,'ffi)wordSem_state) c hv1 v1 q1 a1 a2 ret_val bptr s1 vars' sp
  refs ts.
      memory_rel c (wordSem_state_be t) ts refs sp (wordSem_state_store t)
        (wordSem_state_memory t) (wordSem_state_mdomain t)
         (CONS (hv1,a1) vars') /\
      sptree_lookup InstallCode_location (wordSem_state_code t) = SOME
        (4,InstallCode_code c) /\
      sptree_lookup InstallData_location (wordSem_state_code t) = SOME
        (4,InstallData_code c) /\
      FLOOKUP (wordSem_state_store t) BitmapBuffer = SOME bptr /\
      dataSem_v_to_bytes hv1 = SOME q1 /\
      LENGTH q1 <= buffer_space_left (wordSem_state_code_buffer t) /\
      LENGTH q1 < wordSem_state_clock t /\
      wordSem_get_var 0 t = SOME ret_val /\
      wordSem_get_var 2 t = SOME a1 /\
      wordSem_get_var 4 t = SOME a2 /\
      wordSem_get_var 6 t = SOME (word_Word (buffer_position
        (wordSem_state_code_buffer t) +
                              n2w (LENGTH (buffer_buffer
                                (wordSem_state_code_buffer t))))) /\
      good_dimindex (:'a) ==>
      (?lsz smx.
      wordSem_evaluate (InstallCode_code c,t) =
      (match
        wordSem_evaluate (InstallData_code c,wordSem_state_stack_max_fupd (K
          smx) (wordSem_state_code_buffer_fupd (K (buffer_space_left_fupd (K
          (buffer_space_left (wordSem_state_code_buffer t) - LENGTH q1))
          (buffer_buffer_fupd (K (APPEND (buffer_buffer
          (wordSem_state_code_buffer t)) q1)) (wordSem_state_code_buffer t))))
          (wordSem_state_clock_fupd (K (wordSem_state_clock t - LENGTH q1 - 1))
          (wordSem_state_locals_size_fupd (K lsz) (wordSem_state_locals_fupd (K
          (fromList2 [ret_val; bptr; a2;
           word_Word (buffer_position (wordSem_state_code_buffer t) +
                 n2w (LENGTH (buffer_buffer (wordSem_state_code_buffer t))
                   + LENGTH q1))])) t))))) with (res,s) -> if
                   wordSem_bad_fun_return res then (SOME wordSem_Error,s)
                   else (res,s)))`,
  CHEAT_TAC);;

let w2w_upper_def = new_definition
  `w2w_upper (w:word64) =
     if dimindex (:'a) = 32 then ((63 >< 32) w):'a word else w2w w`;;

let InstallData_code_thm = prove
 (`!(t:('a,'c,'ffi)wordSem_state) c hv2 v1 q2 a1 a2 ret_val s1 vars' sp refs
  ts.
      memory_rel c (wordSem_state_be t) ts refs sp (wordSem_state_store t)
        (wordSem_state_memory t) (wordSem_state_mdomain t)
         (CONS (hv2,a2) vars') /\
      sptree_lookup InstallData_location (wordSem_state_code t) = SOME
        (4,InstallData_code c) /\
      sptree_lookup Install_location (wordSem_state_code t) = SOME
        (3,Install_code c) /\
      dataSem_v_to_words hv2 = SOME q2 /\
      LENGTH q2 <= buffer_space_left (wordSem_state_data_buffer t) /\
      LENGTH q2 < wordSem_state_clock t /\
      wordSem_get_var 0 t = SOME ret_val /\
      wordSem_get_var 2 t = SOME (word_Word (buffer_position
        (wordSem_state_data_buffer t) +
                              bytes_in_word *
                              n2w (LENGTH (buffer_buffer
                                (wordSem_state_data_buffer t))))) /\
      wordSem_get_var 4 t = SOME a2 /\
      wordSem_get_var 6 t = SOME a1 /\
      good_dimindex (:'a) ==>
      (?smx lsz.
      wordSem_evaluate (InstallData_code c,t) =
      (match
        wordSem_evaluate (Install_code c,wordSem_state_stack_max_fupd (K
          smx) (wordSem_state_locals_size_fupd (K lsz)
          (wordSem_state_data_buffer_fupd (K (buffer_space_left_fupd (K
          (buffer_space_left (wordSem_state_data_buffer t) - LENGTH q2))
          (buffer_buffer_fupd (K (APPEND (buffer_buffer
          (wordSem_state_data_buffer t)) (MAP w2w_upper q2)))
          (wordSem_state_data_buffer t)))) (wordSem_state_clock_fupd (K
          (wordSem_state_clock t - LENGTH q2 - 1)) (wordSem_state_locals_fupd
          (K (fromList2 [ret_val;
               word_Word (buffer_position (wordSem_state_data_buffer t) +
                     bytes_in_word * n2w (LENGTH (buffer_buffer
                       (wordSem_state_data_buffer t))) +
                     bytes_in_word * n2w (LENGTH q2)); a1]))
           t))))) with (res,s) -> if wordSem_bad_fun_return res then (SOME
             wordSem_Error,s) else (res,s)))`,
  CHEAT_TAC);;

let LENGTH_EQ_4 = prove
 (`(LENGTH xs = 4 <=> (?a1 a2 a3 a4. xs = [a1; a2; a3; a4])) /\
    (4 = LENGTH xs <=> (?a1 a2 a3 a4. xs = [a1; a2; a3; a4]))`,
  CHEAT_TAC);;

let w2w_upper_upper_w2w = prove
 (`!z1. good_dimindex (:'a) ==>
         MAP w2w_upper (MAP upper_w2w z1) = (z1:('a word) list)`,
  CHEAT_TAC);;

(* [local] *)
let MAP_FST_MAP_compile_part = prove
 (`!full_list. MAP FST (MAP (data_to_word_compile_part c) full_list) = MAP
  FST full_list`,
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let memory_rel_ignore_buffers = prove
 (cake_as_vars (fun () ->
    `memory_rel c be ts refs sp (st |+ (BitmapBuffer,x)) m dm vars =
     memory_rel c be ts refs sp st m dm vars /\
     memory_rel c be ts refs sp (st |+ (CodeBuffer,x)) m dm vars =
     memory_rel c be ts refs sp st m dm vars`),
  CHEAT_TAC);;

(* [local] *)
let compile_part_loc_IMP = prove
 (`data_to_word_compile_part c (a1,a2) = (n,x) ==> n = a1`,
  CHEAT_TAC);;

let consume_space_stack_max = prove
 (`consume_space a x = SOME s ==> dataSem_state_stack_max x =
  dataSem_state_stack_max s`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:2146-2147: ML code, not ported *)

let do_app_aux_safe_for_space_mono = prove
 (`(dataSem_do_app_aux op xs s = Rval (r,s1)) /\ dataSem_state_safe_for_space
  s1 ==> dataSem_state_safe_for_space s`,
  CHEAT_TAC);;

let do_app_safe_for_space_allowed_op = prove
 (`dataSem_do_app op xs s = Rval (r,s1) /\ dataSem_state_safe_for_space
   s1 ==>
   allowed_op op (LENGTH xs)`,
  CHEAT_TAC);;

let state_rel_cut_state_opt_SOME = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
   dataSem_get_vars args (dataSem_state_locals s) = SOME vals /\
   dataSem_cut_state_opt (SOME kept_names) s = SOME x ==>
   (?y ws.
     wordSem_cut_env (adjust_sets kept_names) (wordSem_state_locals t) =
       SOME y /\
     wordSem_get_vars (MAP adjust_var args) t = SOME ws /\
     LENGTH args = LENGTH vals /\ LENGTH args = LENGTH ws /\
     data_to_word_gcProof_state_rel c l1 l2 x t NONE locs /\
     data_to_word_gcProof_state_rel c l1 l2 x (wordSem_state_locals_fupd
       (K y) t) NONE locs)`,
  CHEAT_TAC);;

let cut_state_opt_SOME_eq = prove
 (`dataSem_cut_state_opt (SOME names) s = SOME x ==>
   x = dataSem_state_locals_fupd (K (mk_wf (inter (dataSem_state_locals s)
     names))) s`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:2210-2212: ML code, not ported *)

let state_rel_cut_state_opt_set_var = prove
 (`data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r NONE
  locs /\
   dataSem_cut_state_opt (SOME names) s2 = SOME s2_cut ==>
   data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2_cut)
     r NONE locs`,
  CHEAT_TAC);;

(* cut_env is idempotent: cutting the same names twice gives the same result. *)
let cut_env_idempotent = prove
 (`dataSem_cut_env ns s_locals = SOME env ==>
   dataSem_cut_env ns env = SOME env`,
  CHEAT_TAC);;

(* Two-stage cut: narrowing an args-augmented cut (list_insert args ns) down to
   ns gives the same env as cutting ns directly. *)
let cut_env_cut_env_list_insert = prove
 (`dataSem_cut_env (list_insert vs ns) env = SOME env_wide /\
   dataSem_cut_env ns env = SOME env_narrow ==>
   dataSem_cut_env ns env_wide = SOME env_narrow`,
  CHEAT_TAC);;

(* A join_env pair-list over (l1,l2) is contained in the one over any
   lookup-supermaps (l1',l2') — moves memory_rel pairs between a cut env
   and the full env (with memory_rel_rearrange). *)
let join_env_submap_MEM = prove
 (`(!k v. sptree_lookup k l1 = SOME v ==> sptree_lookup k l1' = SOME v) /\
   (!k v. sptree_lookup k l2 = SOME v ==> sptree_lookup k l2' = SOME v) /\
   MEM p (join_env l1 (toAList (inter l2 (adjust_set l1)))) ==>
   MEM p (join_env l1' (toAList (inter l2' (adjust_set l1'))))`,
  CHEAT_TAC);;

(* The three heap-store FLOOKUPs follow directly from state_rel.
   Reusable in any op that needs to inspect t.store.{NextFree,CurrHeap,HeapLength}. *)
let state_rel_FLOOKUP_heap = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s t NONE locs ==>
   (?nf cu hl.
     FLOOKUP (wordSem_state_store t) NextFree = SOME (word_Word nf) /\
     FLOOKUP (wordSem_state_store t) CurrHeap = SOME (word_Word cu) /\
     FLOOKUP (wordSem_state_store t) HeapLength = SOME (word_Word hl))`,
  CHEAT_TAC);;

(* Evaluating a SilentFFI block (the c.call_empty_ffi=T form emitted by
   op_requires_names ops, with var slot 3): if the word state's locals can be
   cut by the same names, the FFI call has empty payload and reduces to a
   locals-updated state. Reusable in any op whose generated code begins or
   resumes with `SilentFFI c 3 (adjust_sets <names>)`. *)
let evaluate_SilentFFI_3 = prove
 (`data_to_word_config_call_empty_ffi
     c /\
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     wordSem_cut_env (adjust_sets ns) (wordSem_state_locals t) = SOME env
       ==>
     wordSem_evaluate (SilentFFI c 3 (adjust_sets ns),t) =
       (NONE,wordSem_state_ffi_fupd (K (wordSem_state_ffi t))
         (wordSem_state_memory_fupd (K (wordSem_state_memory t))
         (wordSem_state_fp_regs_fupd (K FEMPTY) (wordSem_state_locals_fupd (K
         env) t))))`,
  CHEAT_TAC);;

(* size_of_heap monotonicity helpers *)

let size_of_app_Number = prove
 (`!xs ys lims i refs seen.
     size_of lims (APPEND xs (CONS (dataSem_Number i) ys)) refs seen =
     let (n,refs',seen') = size_of lims (APPEND xs ys) refs seen in
     let k = (if small_num (limits_arch_64_bit lims) i then 0
             else bignum_size (limits_arch_64_bit lims) i) in
     (n + k,refs',seen')`,
  CHEAT_TAC);;

let toList_delete_split = prove
 (`!k spt vv.
     sptree_lookup k spt = SOME vv ==>
     (?pre post.
       sptree_toList spt = APPEND (APPEND pre [vv]) post /\
       sptree_toList (sptree_delete k spt) = APPEND pre post)`,
  CHEAT_TAC);;

let size_of_heap_delete_Number_LE = prove
 (`!k s i.
     sptree_lookup k (dataSem_state_locals s) = SOME (dataSem_Number i) ==>
     size_of_heap (dataSem_state_locals_fupd (K (sptree_delete k
       (dataSem_state_locals s))) s) <= size_of_heap s`,
  CHEAT_TAC);;

let wf_FOLDR_delete = prove
 (`!ks (L:'a spt). sptree_wf L ==> sptree_wf (ITLIST sptree_delete ks L)`,
  CHEAT_TAC);;

(* lookup_FOLDR_delete *)
let data_to_word_assignProof_lookup_FOLDR_delete = prove
 (`!ks (L:'a spt) h.
     sptree_lookup h (ITLIST sptree_delete ks L) =
     if MEM h ks then NONE else sptree_lookup h L`,
  CHEAT_TAC);;

let size_of_heap_FOLDR_delete_Number_LE = prove
 (`!ks L (state:('a,'b)dataSem_state).
     sptree_wf L /\
     (!k. MEM k ks ==> sptree_lookup k L = NONE \/
                       (?i. sptree_lookup k L = SOME (dataSem_Number i)))
                         ==>
     size_of_heap (dataSem_state_locals_fupd (K (ITLIST sptree_delete ks L))
       state) <=
     size_of_heap (dataSem_state_locals_fupd (K L) state)`,
  CHEAT_TAC);;


(* end size_of_heap monotonicity helpers *)


let assign_Install = prove
 (`(op = clos_Install) ==> (data_to_word_gcProof_state_rel c l1 l2
  (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_MutCons = prove
 (`(?t k. op = clos_MemOp (clos_MutCons t k)) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_UpdateCons = prove
 (`op = clos_MemOp clos_UpdateCons ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_FinaliseCons = prove
 (`op = clos_MemOp clos_FinaliseCons ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let LENGTH_EQ_5 = prove
 (`(LENGTH xs = 5 <=> (?a1 a2 a3 a4 a5. xs = [a1; a2; a3; a4; a5])) /\
    (5 = LENGTH xs <=> (?a1 a2 a3 a4 a5. xs = [a1; a2; a3; a4; a5]))`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let memory_rel_get_num = prove
 (cake_as_vars (fun () ->
    `memory_rel c be ts refs sp st m dm vars /\
      n < dimword (:'a) DIV 8 /\ good_dimindex (:'a) /\
      MEM (dataSem_Number (&n),(a:'a word_loc)) vars ==>
      (?w. a = word_Word w /\ w >>> 2 = n2w n)`),
  CHEAT_TAC);;

let IN_domain_adjust_set_inter = prove
 (`x IN sptree_domain (adjust_set (inter s1 s2)) <=>
    x IN sptree_domain (adjust_set s1) /\
    x IN sptree_domain (adjust_set s2)`,
  CHEAT_TAC);;

let get_var_to_word_exp = prove
 (`wordSem_get_var r s = SOME (word_Word w) ==>
   wordSem_word_exp s (word_Op asm_Add [word_Var r; word_Const (n2w 0)]) =
     SOME (word_Word (w + (n2w 0))) /\
   wordSem_word_exp s (word_Op asm_Add [word_Var r; word_Const (n2w 1)]) =
     SOME (word_Word (w + (n2w 1))) /\
   wordSem_word_exp s (word_Op asm_Add [word_Var r; word_Const (n2w 2)]) =
     SOME (word_Word (w + (n2w 2))) /\
   wordSem_word_exp s (word_Op asm_Add [word_Var r; word_Const (n2w 3)]) =
     SOME (word_Word (w + (n2w 3)))`,
  CHEAT_TAC);;

(* [local] *)
let word_exp_set = prove
 (`(wordSem_word_exp s (word_Op asm_Add [word_Var n; word_Const c]) =
   (match wordSem_get_var n s with
     SOME (word_Word w) -> SOME (word_Word (w + c))
   | _ -> NONE)) /\
   (wordSem_word_exp s (word_Op asm_Sub [word_Var n; word_Const c]) =
   (match wordSem_get_var n s with
     SOME (word_Word w) -> SOME (word_Word (w - c))
   | _ -> NONE))`,
  CHEAT_TAC);;

(* [local] *)
let good_dimindex_w2w_byte = prove
 (`good_dimindex (:'a) ==>
   w2w (w2w (w:word8):'a word) = w`,
  CHEAT_TAC);;

(* [local] *)
let set_var_consts = prove
 (`wordSem_state_memory
     (wordSem_set_var r v s) = wordSem_state_memory s
       /\ wordSem_state_mdomain
     (wordSem_set_var r v s) = wordSem_state_mdomain s /\ wordSem_state_be
     (wordSem_set_var r v s) = wordSem_state_be s /\ wordSem_state_code
     (wordSem_set_var r v s) = wordSem_state_code s`,
  CHEAT_TAC);;

(* [local] *)
let get_var_consts = prove
 (`wordSem_get_var r (wordSem_state_memory_fupd (K m) s) = wordSem_get_var r
  s`,
  CHEAT_TAC);;

let CopyByteAdd_thm = prove
 (`!be' n a1 a2 m dm ret_val l1 l2 (s:('a,'c,'ffi)wordSem_state) m1.
      word_copy_fwd be' n a1 a2 m dm = SOME m1 /\ wordSem_state_memory
      s = m /\ wordSem_state_mdomain s = dm /\ wordSem_state_be
      s = be' /\
      good_dimindex (:'a) /\
      sptree_lookup ByteCopyAdd_location (wordSem_state_code s) = SOME
        (5,ByteCopyAdd_code) /\
      w2n n DIV 4 <= wordSem_state_clock s /\
      wordSem_get_var 0 s = SOME (word_Loc l1 l2) /\
      wordSem_get_var 2 s = SOME (word_Word n) /\
      wordSem_get_var 4 s = SOME (word_Word (a1:'a word)) /\
      wordSem_get_var 6 s = SOME (word_Word a2) /\
      wordSem_get_var 8 s = SOME ret_val ==>
      wordSem_evaluate (ByteCopyAdd_code,s) =
        (SOME (wordSem_Result (word_Loc l1 l2)
          [ret_val]),wordSem_state_stack_max_fupd (K
                   (if n <+ (n2w 4) then wordSem_state_stack_max
                     s
                   else OPTION_MAP2 MAX (wordSem_state_stack_max s)
                       (OPTION_MAP2 (+) (stack_size (wordSem_state_stack s))
                       (sptree_lookup ByteCopyAdd_location
                         (wordSem_state_stack_size s)))))
                         (wordSem_state_locals_size_fupd (K (SOME 0))
                         (wordSem_state_locals_fupd (K LN)
                         (wordSem_state_memory_fupd (K m1)
                         (wordSem_state_clock_fupd (K (wordSem_state_clock s -
                         w2n n DIV 4))
         s)))))`,
  CHEAT_TAC);;

let CopyByteSub_thm = prove
 (`!be' n a1 a2 m dm ret_val l1 l2 (s:('a,'c,'ffi)wordSem_state) m1.
      word_copy_bwd be' n a1 a2 m dm = SOME m1 /\ wordSem_state_memory
      s = m /\ wordSem_state_mdomain s = dm /\ wordSem_state_be
      s = be' /\
      good_dimindex (:'a) /\
      sptree_lookup ByteCopySub_location (wordSem_state_code s) = SOME
        (5,ByteCopySub_code) /\
      w2n n DIV 4 <= wordSem_state_clock s /\
      wordSem_get_var 0 s = SOME (word_Loc l1 l2) /\
      wordSem_get_var 2 s = SOME (word_Word n) /\
      wordSem_get_var 4 s = SOME (word_Word (a1:'a word)) /\
      wordSem_get_var 6 s = SOME (word_Word a2) /\
      wordSem_get_var 8 s = SOME ret_val ==>
      wordSem_evaluate (ByteCopySub_code,s) =
        (SOME (wordSem_Result (word_Loc l1 l2)
          [ret_val]),wordSem_state_stack_max_fupd (K
                   (if n <+ (n2w 4) then wordSem_state_stack_max
                     s
                   else OPTION_MAP2 MAX (wordSem_state_stack_max s)
                       (OPTION_MAP2 (+) (stack_size (wordSem_state_stack s))
                       (sptree_lookup ByteCopySub_location
                         (wordSem_state_stack_size s)))))
                         (wordSem_state_locals_size_fupd (K (SOME 0))
                         (wordSem_state_locals_fupd (K LN)
                         (wordSem_state_memory_fupd (K m1)
                         (wordSem_state_clock_fupd (K (wordSem_state_clock s -
                         w2n n DIV 4))
         s)))))`,
  CHEAT_TAC);;

let push_env_store = prove
 (`wordSem_state_store
      (wordSem_push_env x y s) = wordSem_state_store s
        /\ wordSem_state_memory
       (wordSem_push_env x y s) = wordSem_state_memory s
         /\ wordSem_state_mdomain
       (wordSem_push_env x y s) = wordSem_state_mdomain s
         /\ wordSem_state_code
       (wordSem_push_env x y s) = wordSem_state_code s /\ wordSem_state_be
       (wordSem_push_env x y s) = wordSem_state_be s`,
  CHEAT_TAC);;

(* [local] *)
let not_less_zero_int_eq = prove
 (`~(i < ((&0):int)) <=> (?n. i = &n)`,
  CHEAT_TAC);;

let assign_WordFromWord = prove
 (`(?b. op = clos_WordOp (WordFromWord b)) ==> (data_to_word_gcProof_state_rel
  c l1 l2 (s:('c,'ffi)dataSem_state)
     (t:('a,'c,'ffi)wordSem_state) NONE locs /\
   (~(op_requires_names op = (names_opt = NONE))) /\
   dataSem_cut_state_opt names_opt s = SOME x /\
   dataSem_get_vars args (dataSem_state_locals s) = SOME vals
     /\ wordSem_state_termdep
   t > 1 /\
   dataSem_do_app op vals x = Rval (v,s2) ==>
   (?q (r:('a,'c,'ffi)wordSem_state).
     wordSem_evaluate (FST (data_to_word_assign c n l dest op args
       names_opt),t) = (q,r) /\
     (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
      r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
        (dataSem_state_stack_max s2) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
        ~(dataSem_state_safe_for_space s2))) /\
     (~(q = SOME wordSem_NotEnoughSpace) ==>
      data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
        NONE locs /\
      q = NONE)))`,
  CHEAT_TAC);;

let IS_SOME_lookup = prove
 (`IS_SOME (sptree_lookup n l) <=> n IN sptree_domain l`,
  CHEAT_TAC);;

let IN_adjust_var_lemma = prove
 (`dataSem_cut_env kept_names s_locals = SOME x /\
   cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
   n IN sptree_domain x ==>
   adjust_var n IN sptree_domain y2`,
  CHEAT_TAC);;

let cut_env_envs_lookup_lookup = prove
 (`dataSem_cut_env kept_names s_locals = SOME x /\
   cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
   k IN sptree_domain (adjust_set x) ==>
   (?v. sptree_lookup k t_locals = SOME v /\
       sptree_lookup k y2 = SOME v)`,
  CHEAT_TAC);;

let env_to_list_domain = prove
 (`env_to_list y2 p = (l,permute) ==>
   sptree_domain (fromAList l) = sptree_domain y2`,
  CHEAT_TAC);;

let cut_envs_lookup_0 = prove
 (`cut_envs (adjust_sets names) t_locals = SOME (y1,y2) /\
   env_to_list y2 p = (q,r') /\
   sptree_lookup 0 t_locals = SOME (word_Loc l1 l2) ==>
   ALOOKUP q 0 = NONE /\
   sptree_lookup 0 y1 = SOME (word_Loc l1 l2)`,
  CHEAT_TAC);;

let cut_envs_domain_IN = prove
 (`cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
   dataSem_cut_env kept_names s_locals = SOME x /\
   n IN sptree_domain x ==>
   adjust_var n IN sptree_domain y2`,
  CHEAT_TAC);;

let inter_union_distrib = prove
 (`!x y z. inter (sptree_union x y) z = sptree_union (inter x z) (inter y z)`,
  CHEAT_TAC);;

let cut_envs_inter = prove
 (`cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
   dataSem_cut_env kept_names s_locals = SOME x ==>
   inter (fromAList (toAList y1)) (adjust_set x) = LN`,
  CHEAT_TAC);;

let assign_CopyByte = prove
 (`(?new_flag. op = clos_MemOp (clos_CopyByte new_flag) /\ ~new_flag) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let evaluate_StringCmpLoop = prove
 (`!a1 a2 r1 r2 len be' ck dm m l1 l2 (t1:('a,'c,'ffi)wordSem_state) x1 x2.
     word_str_cmp_loop a1 a2 r1 r2 len dm m be' ck = SOME (x1,x2)
       /\ wordSem_state_memory
     t1 = m /\ wordSem_state_mdomain t1 = dm /\ be' = wordSem_state_be t1 /\
     ck < wordSem_state_clock t1 /\ good_dimindex (:'a) /\
     sptree_lookup StringCmpLoop_location (wordSem_state_code t1) = SOME
       (6,StringCmpLoop_code) /\
     wordSem_get_var 0 t1 = SOME (word_Loc l1 l2) /\
     wordSem_get_var 2 t1 = SOME (word_Word a1) /\
     wordSem_get_var 4 t1 = SOME (word_Word a2) /\
     wordSem_get_var 6 t1 = SOME (word_Word len) /\
     wordSem_get_var 8 t1 = SOME (word_Word r1) /\
     wordSem_get_var 10 t1 = SOME (word_Word r2) ==>
     (?ck max_stack.
       wordSem_evaluate (StringCmpLoop_code,t1) =
       (SOME (wordSem_Result (word_Loc l1 l2) [word_Word x1; word_Word
         x2]),wordSem_state_locals_size_fupd (K (SOME 0))
         (wordSem_state_locals_fupd (K LN) (wordSem_state_stack_max_fupd (K
         max_stack) (wordSem_state_clock_fupd (K ck)
        t1)))) /\
       (~(max_stack = wordSem_state_stack_max t1) ==>
        max_stack = OPTION_MAP2 MAX (wordSem_state_stack_max t1)
                      (OPTION_MAP2 (+) (stack_size (wordSem_state_stack t1))
                         (sptree_lookup StringCmpLoop_location
                           (wordSem_state_stack_size t1)))))`,
  CHEAT_TAC);;

let evaluate_AssignCmp = prove
 (`wordSem_evaluate (AssignCmp dest cmp v1 v2,s) =
     match (wordSem_get_var v1 s,wordSem_get_var v2 s) with (SOME (word_Word
       x1),SOME (word_Word x2)) ->
         (NONE,wordSem_set_var dest (if semanticPrimitives_num_cmp cmp (w2n
           x1) (w2n x2) then word_Word (n2w 18) else word_Word (n2w 2)) s)
     | _ -> wordSem_evaluate (AssignCmp dest cmp v1 v2,s)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_StringCmpMin = prove
 (`wordSem_evaluate (word_Seq (word_Assign 9 (word_Var 5))
                 (word_Seq (word_If asm_Lower 7 (asm_Reg 5) (word_Assign 9
                   (word_Var 7)) word_Skip) p),state_locals_fupd (K l)
             t1) =
   match (sptree_lookup 5 l,sptree_lookup 7 l) with (SOME (word_Word
     w1),SOME (word_Word w2)) ->
       wordSem_evaluate (p,state_locals_fupd (K (sptree_insert 9 (word_Word
         (n2w (MIN (w2n w1) (w2n w2)))) l)) t1)
   | _ ->
       wordSem_evaluate (word_Seq (word_Assign 9 (word_Var 5))
                     (word_Seq (word_If asm_Lower 7 (asm_Reg 5) (word_Assign
                       9 (word_Var 7)) word_Skip) p),state_locals_fupd (K l)
                 t1)`,
  CHEAT_TAC);;

let assign_StringCmp = prove
 (`(?b cmp. op = clos_MemOp (clos_StringCmp b cmp)) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let evaluate_XorLoop = prove
 (`!a1 a2 l dm m l1 l2 (t1:('a,'c,'ffi)wordSem_state) m1.
     word_xor_bytes a1 a2 l dm m = SOME m1 /\ wordSem_state_memory t1 = m
       /\ wordSem_state_mdomain t1 = dm /\
     w2n l < wordSem_state_clock t1 /\ good_dimindex (:'a) /\
     sptree_lookup XorLoop_location (wordSem_state_code t1) = SOME
       (4,XorLoop_code) /\
     wordSem_get_var 0 t1 = SOME (word_Loc l1 l2) /\
     wordSem_get_var 2 t1 = SOME (word_Word a2) /\
     wordSem_get_var 4 t1 = SOME (word_Word a1) /\
     wordSem_get_var 6 t1 = SOME (word_Word l) ==>
     (?ck max_stack.
       wordSem_evaluate (XorLoop_code,t1) =
       (SOME (wordSem_Result (word_Loc l1 l2) [word_Word (n2w
         2)]),wordSem_state_locals_size_fupd (K (SOME 0))
         (wordSem_state_locals_fupd (K LN) (wordSem_state_stack_max_fupd (K
         max_stack) (wordSem_state_clock_fupd (K ck) (wordSem_state_memory_fupd
         (K m1)
        t1))))) /\
       (~(max_stack = wordSem_state_stack_max t1) ==>
        max_stack = OPTION_MAP2 MAX (wordSem_state_stack_max t1)
                      (OPTION_MAP2 (+) (stack_size (wordSem_state_stack t1))
                         (sptree_lookup XorLoop_location
                           (wordSem_state_stack_size t1)))))`,
  CHEAT_TAC);;

let assign_XorByte = prove
 (`op = clos_MemOp clos_XorByte ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_AppendMainLoop_code = prove
 (`!xs ww (t:('a,'c,'ffi)wordSem_state) vars' ptr hdr l k frame r1 r2 next_free
  ts v.
     memory_rel c (wordSem_state_be t) ts (dataSem_state_refs
       (s:('c,'ffi)dataSem_state)) sp (wordSem_state_store t)
       (wordSem_state_memory t) (wordSem_state_mdomain t)
        (CONS (v,word_Word ww) vars') /\ ~(xs = []) /\
     dataSem_v_to_list v = SOME xs /\
     sptree_lookup 10 (wordSem_state_locals t) = SOME (word_Word ptr) /\
     sptree_lookup 8 (wordSem_state_locals t) = SOME (word_Word
       (bytes_in_word * n2w (sp - k))) /\
     sptree_lookup 6 (wordSem_state_locals t) = SOME (word_Word hdr) /\
     sptree_lookup 4 (wordSem_state_locals t) = SOME (word_Word ww) /\
     sptree_lookup 2 (wordSem_state_locals t) = SOME (word_Word next_free)
       /\
     sptree_lookup 0 (wordSem_state_locals t) = SOME (word_Loc r1 r2) /\
     k + 3 * LENGTH xs <= sp /\ good_dimindex (:'a) /\
     sp * (dimindex (:'a) DIV 8) < dimword (:'a) /\
     FLOOKUP (wordSem_state_store t) (Temp (n2w 0)) = SOME tmp0 /\
     FLOOKUP (wordSem_state_store t) (Temp (n2w 2)) = SOME tmp2 /\
     FLOOKUP (wordSem_state_store t) NextFree = SOME (word_Word f) /\
     Abbrev (next_free = f + bytes_in_word * n2w k) /\
     sptree_lookup AppendMainLoop_location (wordSem_state_code t) = SOME
       (6,AppendMainLoop_code c) /\
     sptree_lookup AppendMainLoop_location (wordSem_state_stack_size t) =
       wordSem_state_locals_size t /\
     (word_list_exists next_free (3 * LENGTH xs) * frame)
        (fun2set (wordSem_state_memory t,wordSem_state_mdomain t)) /\ LENGTH
          xs <= wordSem_state_clock t ==>
     (?m1 ws smx.
       wordSem_evaluate (AppendMainLoop_code c,t) =
         (SOME (wordSem_Result (word_Loc r1 r2)
           [tmp2]),wordSem_state_clock_fupd (K (wordSem_state_clock t - (LENGTH
           xs - 1))) (wordSem_state_stack_max_fupd (K smx)
           (wordSem_state_memory_fupd (K m1) (wordSem_state_store_fupd (K
           (wordSem_state_store t |+ (NextFree,word_Word (next_free +
                       bytes_in_word * n2w (3 * LENGTH xs)))))
                         (wordSem_state_locals_size_fupd (K (SOME 0))
                         (wordSem_state_locals_fupd (K LN)
          t)))))) /\
       LENGTH ws = LENGTH xs /\
       option_le smx (OPTION_MAP2 MAX (wordSem_state_stack_max
                        t)
                        (OPTION_MAP2 (+)
                          (OPTION_MAP2 MAX
                            (sptree_lookup AppendMainLoop_location
                              (wordSem_state_stack_size t))
                            (sptree_lookup AppendLenLoop_location
                              (wordSem_state_stack_size t)))
                          (stack_size (wordSem_state_stack t)))) /\
       (misc_word_list next_free (append_writes c ptr hdr ws tmp0) * frame)
         (fun2set (m1,wordSem_state_mdomain t)) /\
       memory_rel c (wordSem_state_be t) ts (dataSem_state_refs s) sp
         (wordSem_state_store t) m1 (wordSem_state_mdomain t)
         (APPEND (ZIP xs ws) vars'))`,
  CHEAT_TAC);;

let data_to_word_assignProof_STOP_def = new_definition
  `data_to_word_assignProof_STOP x = x`;;

(* [local] *)
let evaluate_AppendMainLoop_code_alt = prove
 (`!xs ww (t:('a,'c,'ffi)wordSem_state) vars' ptr hdr l k frame r1 r2 next_free
  ts v.
     memory_rel c (wordSem_state_be t) ts (dataSem_state_refs
       (s:('c,'ffi)dataSem_state)) sp (wordSem_state_store t)
       (wordSem_state_memory t) (wordSem_state_mdomain t)
        (CONS (v,word_Word ww) vars') /\ ~(xs = []) /\
     dataSem_v_to_list v = SOME xs /\
     sptree_lookup 10 (wordSem_state_locals t) = SOME (word_Word ptr) /\
     sptree_lookup 8 (wordSem_state_locals t) = SOME (word_Word
       (bytes_in_word * n2w (sp - k))) /\
     sptree_lookup 6 (wordSem_state_locals t) = SOME (word_Word hdr) /\
     sptree_lookup 4 (wordSem_state_locals t) = SOME (word_Word ww) /\
     sptree_lookup 2 (wordSem_state_locals t) = SOME (word_Word next_free)
       /\
     sptree_lookup 0 (wordSem_state_locals t) = SOME (word_Loc r1 r2) /\
     sp < k + 3 * LENGTH xs /\ good_dimindex (:'a) /\ k <= sp /\
     sp * (dimindex (:'a) DIV 8) < dimword (:'a) /\
     FLOOKUP (wordSem_state_store t) (Temp (n2w 0)) = SOME tmp0 /\
     FLOOKUP (wordSem_state_store t) (Temp (n2w 2)) = SOME tmp2 /\
     FLOOKUP (wordSem_state_store t) NextFree = SOME (word_Word f) /\
     Abbrev (next_free = f + bytes_in_word * n2w k) /\
     sptree_lookup AppendMainLoop_location (wordSem_state_code t) = SOME
       (6,AppendMainLoop_code c) /\
     sptree_lookup AppendLenLoop_location (wordSem_state_code t) = SOME
       (3,AppendLenLoop_code c) /\
     (word_list_exists next_free (sp - k) * frame)
        (fun2set (wordSem_state_memory t,wordSem_state_mdomain t)) /\ LENGTH
          xs <= wordSem_state_clock t ==>
     (?m1 ww2 smx.
       wordSem_evaluate (AppendMainLoop_code c,t) =
         (match data_to_word_assignProof_STOP wordSem_evaluate
           (AppendLenLoop_code c,wordSem_state_clock_fupd (K
           (wordSem_state_clock t - ((sp - k) DIV 3 + 1)))
           (wordSem_state_stack_max_fupd (K smx) (wordSem_state_memory_fupd (K
           m1) (wordSem_state_locals_size_fupd (K (sptree_lookup
           AppendLenLoop_location (wordSem_state_stack_size t)))
           (wordSem_state_locals_fupd (K (fromList2 [word_Loc r1 r2; word_Word
           ww2; word_Word (n2w 0)]))
             t))))) with (res,s) -> if wordSem_bad_fun_return res then (SOME
               wordSem_Error,s) else (res,s)) /\
       option_le (OPTION_MAP2 (+) (stack_size (wordSem_state_stack t))
         (sptree_lookup AppendLenLoop_location (wordSem_state_stack_size t)))
         smx /\
       option_le smx
         (OPTION_MAP2 MAX (wordSem_state_stack_max t)
            (OPTION_MAP2 (+) (stack_size (wordSem_state_stack t))
            (OPTION_MAP2 MAX
               (sptree_lookup AppendLenLoop_location
                 (wordSem_state_stack_size t))
               (sptree_lookup AppendMainLoop_location
                 (wordSem_state_stack_size t))))) /\
       memory_rel c (wordSem_state_be t) ts (dataSem_state_refs s) sp
         (wordSem_state_store t) m1 (wordSem_state_mdomain t)
        (CONS (THE (block_drop ((sp - k) DIV 3) v),word_Word ww2) vars'))`,
  CHEAT_TAC);;
(* HOL4 data_to_word_assignProofScript.sml:5278-5281: ML code, not ported *)

(* [local] *)
let evaluate_AppendLenLoop_code = prove
 (`!k (t:('a,'c,'ffi)wordSem_state) c xs l1 l2 (w:'a word) vars' ts v.
     memory_rel c (wordSem_state_be t) ts refs sp (wordSem_state_store t)
       (wordSem_state_memory t) (wordSem_state_mdomain t)
       (CONS (v,word_Word w) vars') /\
     dataSem_v_to_list v = SOME xs /\
     sptree_lookup 0 (wordSem_state_locals t) = SOME (word_Loc l1 l2) /\
     sptree_lookup 2 (wordSem_state_locals t) = SOME (word_Word w) /\
     sptree_lookup 4 (wordSem_state_locals t) = SOME (word_Word (n2w (12 *
       k))) /\
     sptree_lookup AppendLenLoop_location (wordSem_state_code t) = SOME
       (3,AppendLenLoop_code c) /\ wordSem_state_locals_size
     t = sptree_lookup AppendLenLoop_location (wordSem_state_stack_size t)
       /\
     good_dimindex (:'a) /\
     LENGTH xs <= wordSem_state_clock t ==>
     (?locals smx.
       (match wordSem_evaluate (AppendLenLoop_code c,t) with
         (res,s) -> if wordSem_bad_fun_return res then (SOME
           wordSem_Error,s) else (res,s)) =
       (match wordSem_evaluate (AppendLenLoop_code
         c,wordSem_state_stack_max_fupd (K smx) (wordSem_state_clock_fupd (K
         (wordSem_state_clock t - LENGTH xs)) (wordSem_state_locals_fupd (K
         locals)
               t))) with
         (res,s) -> if wordSem_bad_fun_return res then (SOME
           wordSem_Error,s) else (res,s)) /\
       sptree_lookup 0 locals = SOME (word_Loc l1 l2) /\
       sptree_lookup 2 locals = SOME (word_Word (n2w 2)) /\
       sptree_lookup 4 locals = SOME (word_Word (n2w (12 * (k + LENGTH
         xs)))) /\
       option_le (wordSem_state_stack_max t) smx /\
       option_le smx (OPTION_MAP2 MAX (wordSem_state_stack_max t)
                       (OPTION_MAP2 (+) (stack_size (wordSem_state_stack t))
                       (sptree_lookup AppendLenLoop_location
                         (wordSem_state_stack_size t)))))`,
  CHEAT_TAC);;
(* HOL4 data_to_word_assignProofScript.sml:5370-5371: ML code, not ported *)

let v_to_list_block_drop = prove
 (`!k v l.
    dataSem_v_to_list v = SOME l /\ k < LENGTH l ==> dataSem_v_to_list
      (THE (block_drop k v)) = SOME (DROP k l)`,
  CHEAT_TAC);;

let OPTION_MAP2_NONE_THM = prove
 (`(OPTION_MAP2 f NONE x = NONE) /\
   (OPTION_MAP2 f x NONE = NONE)`,
  CHEAT_TAC);;

(* TODO: declared with [simp] further down *)
(* [local] *)
let opt_map_plus_zero_id = prove
 (`!n. OPTION_MAP2 (+) (SOME 0) n = (n:num option)`,
  CHEAT_TAC);;

(* TODO: move *)
let option_le_flip_neg = prove
 (`~(option_le a b) ==> option_le b a`,
  CHEAT_TAC);;

let cut_state_refs_same = prove
 (`!n s x. dataSem_cut_state n s = SOME x ==> dataSem_state_refs s =
  dataSem_state_refs x`,
  CHEAT_TAC);;

let assign_ListAppend = prove
 (`op = clos_BlockOp clos_ListAppend ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let do_app_AllocThunk = prove
 (`dataSem_do_app (clos_ThunkOp (AllocThunk m)) [v] x =
    match consume_space (1 + 1) x with
      NONE -> Rerr (Rabort Rtype_error)
    | SOME s1 ->
      if dataSem_bad_thunk_update m v (dataSem_state_refs s1) then Rerr
        (Rabort Rtype_error) else Rval
      (dataSem_RefPtr F (minimal ptr. ~(ptr IN sptree_domain
        (dataSem_state_refs s1))),dataSem_state_stack_max_fupd (K
        (dataSem_state_stack_max (
             do_stack
               (clos_ThunkOp (AllocThunk m)) [v]
               (do_lim_safe s1 (clos_ThunkOp (AllocThunk m)) [v]))))
                 (dataSem_state_safe_for_space_fupd (K
                 (dataSem_state_safe_for_space (
             do_stack
               (clos_ThunkOp (AllocThunk m)) [v]
               (do_lim_safe s1 (clos_ThunkOp (AllocThunk m)) [v]))))
                 (dataSem_state_refs_fupd (K (sptree_insert (minimal ptr. ~(ptr
                 IN sptree_domain (dataSem_state_refs s1))) (bvlSem_Thunk m v)
                 (dataSem_state_refs s1)))
         s1)))`,
  CHEAT_TAC);;

let assign_AllocThunk = prove
 (`(?ev. op = clos_ThunkOp (AllocThunk ev)) ==> (data_to_word_gcProof_state_rel
  c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_UpdateThunk = prove
 (`(?ev. op = clos_ThunkOp (UpdateThunk ev)) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

(* ConfigGC: assign-specific helper + body *)
let configGC_size_of_heap_LE = prove
 (`!ns s x k1 k2 i1 i2 (state:('a,'b)dataSem_state).
     dataSem_cut_state_opt (SOME (sptree_insert k2 one (sptree_insert k1 one
       ns))) s = SOME x /\
     sptree_lookup k1 (dataSem_state_locals x) = SOME (dataSem_Number i1) /\
     sptree_lookup k2 (dataSem_state_locals x) = SOME (dataSem_Number i2)
       /\ dataSem_state_refs
     state = dataSem_state_refs s /\ dataSem_state_limits state =
       dataSem_state_limits s /\ dataSem_state_stack
     state = dataSem_state_stack s /\ dataSem_state_global state =
       dataSem_state_global s ==>
     size_of_heap (dataSem_state_locals_fupd (K (mk_wf (inter
       (dataSem_state_locals s) ns))) state) <=
     size_of_heap (dataSem_state_locals_fupd (K (dataSem_state_locals x))
       state)`,
  CHEAT_TAC);;

(* Prepending values to the size_of root list never shrinks the heap count.
   Basis for the args-aware do_space bridge (replaces the two-stage size_of
   narrow/wide reconciliation helpers). *)
(* size_of_LE_append and size_of_heap_LE_args are inherited from
   data_to_word_bignumProof (used there by eval_Call_Arith). *)

(* The single narrow cut state IS cut_locals of the original: alloc_lemma's
   size_of_heap (cut_locals ns s) is exactly size_of_heap x. *)
let cut_state_opt_IMP_cut_locals = prove
 (`dataSem_cut_state_opt (SOME ns) s = SOME x ==> cut_locals ns s = x`,
  CHEAT_TAC);;

let assign_ConfigGC = prove
 (`op = clos_MemOp clos_ConfigGC ==> (data_to_word_gcProof_state_rel c l1 l2
  (s:('c,'ffi)dataSem_state)
     (t:('a,'c,'ffi)wordSem_state) NONE locs /\
   (~(op_requires_names op = (names_opt = NONE))) /\
   dataSem_cut_state_opt names_opt s = SOME x /\
   dataSem_get_vars args (dataSem_state_locals s) = SOME vals
     /\ wordSem_state_termdep
   t > 1 /\
   dataSem_do_app op vals x = Rval (v,s2) ==>
   (?q (r:('a,'c,'ffi)wordSem_state).
     wordSem_evaluate (FST (data_to_word_assign c n l dest op args
       names_opt),t) = (q,r) /\
     (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
      r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
        (dataSem_state_stack_max s2) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
        ~(dataSem_state_safe_for_space s2))) /\
     (~(q = SOME wordSem_NotEnoughSpace) ==>
      data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
        NONE locs /\
      q = NONE)))`,
  CHEAT_TAC);;

let assign_WordToInt = prove
 (`op = clos_WordOp WordToInt ==> (data_to_word_gcProof_state_rel c l1 l2
  (s:('c,'ffi)dataSem_state)
     (t:('a,'c,'ffi)wordSem_state) NONE locs /\
   (~(op_requires_names op = (names_opt = NONE))) /\
   dataSem_cut_state_opt names_opt s = SOME x /\
   dataSem_get_vars args (dataSem_state_locals s) = SOME vals
     /\ wordSem_state_termdep
   t > 1 /\
   dataSem_do_app op vals x = Rval (v,s2) ==>
   (?q (r:('a,'c,'ffi)wordSem_state).
     wordSem_evaluate (FST (data_to_word_assign c n l dest op args
       names_opt),t) = (q,r) /\
     (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
      r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
        (dataSem_state_stack_max s2) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
        ~(dataSem_state_safe_for_space s2))) /\
     (~(q = SOME wordSem_NotEnoughSpace) ==>
      data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
        NONE locs /\
      q = NONE)))`,
  CHEAT_TAC);;

let push_env_tstamps = prove
 (`!x t s. dataSem_state_tstamps (dataSem_push_env x t s) =
  dataSem_state_tstamps s`,
  CHEAT_TAC);;

let dec_clock_tstamps = prove
 (`!s. dataSem_state_tstamps (dataSem_dec_clock s) = dataSem_state_tstamps s`,
  CHEAT_TAC);;

let FromList1_code_thm = prove
 (`!k a b r x m1 a1 a2 a3 a4 a5 a6.
      sptree_lookup FromList1_location (wordSem_state_code r) = SOME
        (6,FromList1_code c) /\
      copy_list c (wordSem_state_store r) k (a,x,b,wordSem_state_memory
        (r:('a,'c,'ffi)wordSem_state),wordSem_state_mdomain
        r) = SOME (b1,m1) /\
      shift_length c < dimindex (:'a) /\ good_dimindex (:'a) /\
      wordSem_get_var a1 r = SOME (word_Loc l1 l2) /\
      wordSem_get_var a2 r = SOME (word_Word (b:'a word)) /\
      wordSem_get_var a3 r = SOME a /\
      wordSem_get_var a4 r = SOME (word_Word (n2w (4 * k))) /\
      wordSem_get_var a5 r = SOME ret_val /\
      wordSem_get_var a6 r = SOME x /\
      4 * k < dimword (:'a) /\
      k < wordSem_state_clock r ==>
      wordSem_evaluate (word_Call NONE (SOME FromList1_location) [a1; a2;
        a3; a4; a5; a6] NONE,r) =
        (SOME (wordSem_Result (word_Loc l1 l2)
          [ret_val]),wordSem_state_stack_max_fupd (K (OPTION_MAP2 MAX
          (wordSem_state_stack_max r) (OPTION_MAP2 (+) (stack_size
          (wordSem_state_stack r))
                              (sptree_lookup FromList1_location
                                (wordSem_state_stack_size r)))))
                                (wordSem_state_store_fupd (K
                                (wordSem_state_store r |+ (NextFree,word_Word
                                b1))) (wordSem_state_locals_size_fupd (K (SOME
                                0)) (wordSem_state_locals_fupd (K LN)
                                (wordSem_state_clock_fupd (K
                                (wordSem_state_clock r - k - 1))
                                (wordSem_state_memory_fupd (K m1)
         r))))))`,
  CHEAT_TAC);;

let FromList_thm = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE
  locs /\ ~(encode_header c (4 * tag) 0 = (NONE:('a word) option)) /\
    dataSem_get_vars [0; 1; 2] (dataSem_state_locals s) = SOME [v1; v2;
      dataSem_Number (&(4 * tag))] /\ wordSem_state_clock
    t = MustTerminate_limit (:'a) - 1 /\
    dataSem_pop_env s = SOME s1 /\ is_env (HD (dataSem_state_stack s))
      /\ dataSem_state_locals_size
    s = sptree_lookup FromList_location (dataSem_state_stack_frame_sizes s)
      /\
    dataSem_do_app (clos_BlockOp (clos_FromList tag)) [v1; v2] s1 = Rval
      (v,s2) /\
    option_le (dataSem_state_stack_max s) (dataSem_state_stack_max s2) /\
    size_of_heap (cut_locals (sptree_fromList [one; one; one]) s) <=
      size_of_heap_args [v1; v2] s1 ==>
    (?q r new_c.
      wordSem_evaluate (FromList_code c,t) = (q,r) /\
      (if q = SOME wordSem_NotEnoughSpace then wordSem_state_ffi
        r = wordSem_state_ffi t /\
        option_le (wordSem_state_stack_max r) (dataSem_state_stack_max s2)
          /\
        (~(data_to_word_config_gc_kind c = data_to_word_None)
          /\ no_thunks_in_refs (dataSem_state_refs s) ==>
         (match (v1,v2) with
           (dataSem_Number n,_) -> ~(small_num (limits_arch_64_bit
             (dataSem_state_limits s)) n) \/
                           ~(num_of_int n < dimword (:'a) DIV 16) \/
                           ~(num_of_int n < 2 EXP
                             data_to_word_config_len_size c) \/
                           (limits_heap_limit (dataSem_state_limits s1) <
                             size_of_heap_args [v1; v2] s1 + num_of_int n +
                               1)))
      else ?rv. q = SOME (wordSem_Result (word_Loc l1 l2) [rv]) /\
             data_to_word_gcProof_state_rel c r1 r2
               (dataSem_state_stack_fupd (K (dataSem_state_stack s))
               (dataSem_state_clock_fupd (K new_c)
               (dataSem_state_locals_size_fupd (K (SOME 0))
               (dataSem_state_locals_fupd (K LN) s2))))
                r (SOME [(v,rv)]) locs))`,
  CHEAT_TAC);;

(* ---- helpers used by assign_FromList's NES/Success arms (also reused by
   assign_RefByte etc. below); hoisted above assign_FromList so they are in
   scope here. ---- *)

(* do_app for FromList sets the result stack_max uniformly (stack_consumed is
   the same for the empty and nonempty cases), regardless of tstamps. *)
(* [local] *)
let do_app_FromList_stack_max = prove
 (`dataSem_do_app (clos_BlockOp (clos_FromList tag)) vals s = Rval (v,s') ==>
  dataSem_state_stack_max
   s' = OPTION_MAP2 MAX (dataSem_state_stack_max s)
     (OPTION_MAP2 (+)
        (stack_consumed (dataSem_state_stack_frame_sizes s)
          (dataSem_state_limits s) (clos_BlockOp (clos_FromList tag)) vals)
        (OPTION_MAP2 (+) (size_of_stack (dataSem_state_stack s))
          (dataSem_state_locals_size s)))`,
  CHEAT_TAC);;

(* do_app for FromList: the result safe_for_space field, uniform over the empty
   and nonempty cases (the empty case lacks the with_fresh_ts/check_lim wrapper,
   but its extra `LENGTH ys < 2 ** length_limit` conjunct is trivially true). The
   add_space_safe_args / the F terms are dataSem overloads; the statement spells
   them out so it parses without the abbreviation. *)
(* [local] *)
let do_app_FromList_safe = prove
 (`dataSem_v_to_list v2 = SOME ys /\
   dataSem_do_app (clos_BlockOp (clos_FromList tag)) [dataSem_Number
     (&(LENGTH ys)); v2] (s:('c,'ffi)dataSem_state) = Rval (v,s') ==>
   (dataSem_state_safe_for_space s' <=>
    (((small_num (limits_arch_64_bit (dataSem_state_limits s)) (&(LENGTH
      ys)) /\
       LENGTH ys < 2 EXP limits_length_limit (dataSem_state_limits s) /\
       LENGTH ys < arch_size (dataSem_state_limits s) DIV 16 /\
       4 * tag < 2 EXP (arch_size (dataSem_state_limits s) -
         (limits_length_limit (dataSem_state_limits s) + 2)) /\
       4 * tag < 2 EXP arch_size (dataSem_state_limits s) DIV 16) /\
      (dataSem_state_safe_for_space s /\
       no_thunks_in_refs (dataSem_state_refs s) /\
       size_of_heap_args [dataSem_Number (&(LENGTH ys)); v2] s + (LENGTH ys
         + 1) <= limits_heap_limit (dataSem_state_limits s))) /\
     the F (OPTION_MAP ((>) (limits_stack_limit (dataSem_state_limits s)))
       (OPTION_MAP2 (+) (OPTION_MAP2 MAX (sptree_lookup FromList_location
         (dataSem_state_stack_frame_sizes s))
                              (sptree_lookup FromList1_location
                                (dataSem_state_stack_frame_sizes s)))
                       (OPTION_MAP2 (+) (size_of_stack
                         (dataSem_state_stack s)) (dataSem_state_locals_size
                         s))))))`,
  CHEAT_TAC);;

(* do_app for FromList: the result value is a Block of the source list, and the
   non-stack/safe/space fields are preserved from the input state (tstamps gains
   a fresh stamp for nonempty lists). Used by assign_FromList's success arm to
   relate s2 (do_app on x) and s2_inner (do_app on s_pop): both share these
   fields because x and s_pop agree on locals/refs/tstamps/.... *)
(* [local] *)
let do_app_FromList_eq = prove
 (`dataSem_v_to_list v2 = SOME ys /\
   dataSem_do_app (clos_BlockOp (clos_FromList tag)) [dataSem_Number
     (&(LENGTH ys)); v2] (s:('c,'ffi)dataSem_state) = Rval (v,s') ==>
   (?ts'. v = dataSem_Block ts' tag ys) /\ dataSem_state_space s' = 0
     /\ dataSem_state_refs
   s' = dataSem_state_refs s /\ dataSem_state_code s' = dataSem_state_code s
     /\ dataSem_state_ffi s' = dataSem_state_ffi s /\ dataSem_state_handler s'
     = dataSem_state_handler s /\ dataSem_state_locals
   s' = dataSem_state_locals s /\ dataSem_state_stack s' =
     dataSem_state_stack s /\ dataSem_state_limits s' = dataSem_state_limits s
     /\ dataSem_state_stack_frame_sizes
   s' = dataSem_state_stack_frame_sizes s /\ dataSem_state_locals_size s' =
     dataSem_state_locals_size s /\ dataSem_state_global
   s' = dataSem_state_global s /\ dataSem_state_compile s' =
     dataSem_state_compile s /\ dataSem_state_compile_oracle s' =
     dataSem_state_compile_oracle s /\ dataSem_state_clock
   s' = dataSem_state_clock s /\ dataSem_state_tstamps
   s' = (if ys = [] then dataSem_state_tstamps s else OPTION_MAP SUC
     (dataSem_state_tstamps s))`,
  CHEAT_TAC);;

(* Variant of call_env_push_env_dec_clock_lift that also absorbs a `locals
   := insert k v t.locals` field update inside the dec_clock. *)
(* [local] *)
let call_env_push_env_dec_clock_lift_locals = prove
 (`wordSem_call_env (args:('a word_loc) list) b (wordSem_push_env (y1,y2) NONE
     (wordSem_dec_clock (wordSem_state_termdep_fupd (K tp)
       (wordSem_state_clock_fupd (K ck') (wordSem_state_locals_fupd (K
       (sptree_insert k v (wordSem_state_locals t)))
       (t:('a,'c,'ffi)wordSem_state)))))) = wordSem_state_termdep_fupd (K tp)
       (wordSem_state_clock_fupd (K (ck' - 1))
   (wordSem_call_env args b (wordSem_push_env (y1,y2) NONE t)))`,
  CHEAT_TAC);;

(* [local] *)
let call_env_push_env_dec_clock_stack_max = prove
 (`dataSem_state_stack_max
     (dataSem_call_env args ls (dataSem_push_env env F
       (dataSem_dec_clock (s:('c,'ffi)dataSem_state)))) =
       OPTION_MAP2 MAX
         (OPTION_MAP2 MAX (dataSem_state_stack_max s)
            (OPTION_MAP2 (((+)):num->num->num) (dataSem_state_locals_size s)
              (size_of_stack (dataSem_state_stack s))))
         (OPTION_MAP2 (((+)):num->num->num)
            (OPTION_MAP2 (((+)):num->num->num) (dataSem_state_locals_size
              s) (size_of_stack (dataSem_state_stack s))) ls)`,
  CHEAT_TAC);;

(* [local] *)
let option_le_stackmax_bridge = prove
 (`!(m:num option) (l_size:num option) (s_size:num option)
     (ls_R:num option) (ls_Re:num option).
     option_le
       (OPTION_MAP2 MAX
          (OPTION_MAP2 MAX
             (OPTION_MAP2 MAX m (OPTION_MAP2 (((+)):num->num->num) l_size
               s_size))
             (OPTION_MAP2 (((+)):num->num->num)
                (OPTION_MAP2 (((+)):num->num->num) l_size s_size) ls_R))
          (OPTION_MAP2 (((+)):num->num->num) (OPTION_MAP2 MAX ls_R ls_Re)
             (OPTION_MAP2 (((+)):num->num->num) s_size l_size)))
       (OPTION_MAP2 MAX m
          (OPTION_MAP2 (((+)):num->num->num) (OPTION_MAP2 MAX ls_R ls_Re)
             (OPTION_MAP2 (((+)):num->num->num) s_size l_size)))`,
  CHEAT_TAC);;

let assign_FromList = prove
 (`(?tag. op = clos_BlockOp (clos_FromList tag)) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

(* TODO: move to backendProps? *)
let not_the_F_option_le = prove
 (`~(the F (OPTION_MAP ((>) n) m)) <=> option_le (SOME n) m`,
  CHEAT_TAC);;

let the_F_not_option_le = prove
 (`the F (OPTION_MAP ((>) n) m) <=> ~(option_le (SOME n) m)`,
  CHEAT_TAC);;

(* Helper: do_app on RefByte gives a precise equation s' = s with <known-update>
   (args-aware single-cut form). Used to bridge s2_inner field equalities in
   assign_RefByte's Success arm. *)
(* [local] *)
let do_app_RefByte_eq = prove
 (`dataSem_do_app (clos_MemOp (clos_RefByte fl)) [dataSem_Number i;
  dataSem_Number (&(w2n (w:word8)))] (s:('c,'ffi)dataSem_state) = Rval (v,s')
  ==>
   (?ptr. v = dataSem_RefPtr T ptr /\ ptr = (minimal p. ~(p IN sptree_domain
     (dataSem_state_refs s))) /\ (&0) <= i /\
         s' = dataSem_state_peak_heap_length_fupd (K
                  ((\k op_args s. MAX (dataSem_state_peak_heap_length s)
                    (size_of_heap_args op_args s + k))
                    (space_consumed s (clos_MemOp (clos_RefByte fl))
                       [dataSem_Number i; dataSem_Number (&(w2n w))])
                    [dataSem_Number i; dataSem_Number (&(w2n w))] s))
                      (dataSem_state_safe_for_space_fupd (K
                  (((num_of_int i DIV (arch_size (dataSem_state_limits s)
                    DIV 8) <
                     2 EXP arch_size (dataSem_state_limits s) DIV arch_size
                       (dataSem_state_limits s) /\
                     num_of_int i DIV (arch_size (dataSem_state_limits s)
                       DIV 8) + 1 <
                     2 EXP limits_length_limit (dataSem_state_limits s) /\
                     small_num (limits_arch_64_bit (dataSem_state_limits s))
                       i) /\
                    no_thunks_in_refs (dataSem_state_refs s) /\
                    (\k op_args s.
                   dataSem_state_safe_for_space s /\ size_of_heap_args
                     op_args s + k <= limits_heap_limit (dataSem_state_limits
                     s))
                      (space_consumed s (clos_MemOp (clos_RefByte fl))
                         [dataSem_Number i; dataSem_Number (&(w2n w))])
                      [dataSem_Number i; dataSem_Number (&(w2n w))] s) /\
                   the F
                     (OPTION_MAP ((>) (limits_stack_limit
                       (dataSem_state_limits s)))
                        (OPTION_MAP2 (+)
                           (stack_consumed (dataSem_state_stack_frame_sizes
                             s) (dataSem_state_limits s)
                              (clos_MemOp (clos_RefByte fl)) [dataSem_Number
                                i; dataSem_Number (&(w2n w))])
                           (OPTION_MAP2 (+) (size_of_stack
                             (dataSem_state_stack s))
                             (dataSem_state_locals_size
                              s)))))) (dataSem_state_space_fupd (K 0)
                                (dataSem_state_refs_fupd (K (sptree_insert ptr
                                (bvlSem_ByteArray fl (REPLICATE (num_of_int i)
                                w)) (dataSem_state_refs s)))
                                (dataSem_state_stack_max_fupd (K
                  (OPTION_MAP2 MAX (dataSem_state_stack_max s)
                    (OPTION_MAP2 (+)
                       (stack_consumed (dataSem_state_stack_frame_sizes s)
                         (dataSem_state_limits s)
                          (clos_MemOp (clos_RefByte fl)) [dataSem_Number i;
                            dataSem_Number (&(w2n w))])
                       (OPTION_MAP2 (+) (size_of_stack
                         (dataSem_state_stack s)) (dataSem_state_locals_size
                         s))))) s)))))`,
  CHEAT_TAC);;

(* Helper: lift inner-with on a dec_clock'd state to outer-with on call_env/push_env.
   Used to bridge the post-Call evaluate term to the shape expected by
   evaluate_IMP_domain_union (which has outer-with). *)
(* [local] *)
let call_env_push_env_dec_clock_lift = prove
 (`wordSem_call_env (args:('a word_loc) list) b (wordSem_push_env (y1,y2) NONE
     (wordSem_dec_clock (wordSem_state_termdep_fupd (K tp)
       (wordSem_state_clock_fupd (K ck') (t:('a,'c,'ffi)wordSem_state))))) =
       wordSem_state_termdep_fupd (K tp) (wordSem_state_clock_fupd (K (ck' -
       1))
   (wordSem_call_env args b (wordSem_push_env (y1,y2) NONE t)))`,
  CHEAT_TAC);;

let assign_RefByte = prove
 (`(?fl. op = clos_MemOp (clos_RefByte fl)) ==> (data_to_word_gcProof_state_rel
  c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let lookup_set_var = prove
 (`sptree_lookup x (wordSem_state_locals (wordSem_set_var x y z)) = SOME y`,
  CHEAT_TAC);;

(* [local] *)
let lookup_2_call_env = prove
 (`sptree_lookup 0 (wordSem_state_locals (wordSem_call_env (CONS x ts) a1 a2))
  = SOME x /\
   sptree_lookup 2 (wordSem_state_locals (wordSem_call_env (CONS x (CONS y
     ts)) a1 a2)) = SOME y /\
   sptree_lookup 4 (wordSem_state_locals (wordSem_call_env (CONS x (CONS y
     (CONS z ts))) a1 a2)) = SOME z`,
  CHEAT_TAC);;

(* Binary (two-argument) instance of AllocVar_thm_nary, used by assign_RefArray. *)
(* [local] *)
let AllocVar_thm_binary = prove
 (`!c l1 l2 s (t:('a,'c,'ffi)wordSem_state) locs a1 a2 x' xa i vv limit' q r.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     dataSem_cut_env (list_insert [a1; a2] x') (dataSem_state_locals s) =
       SOME xa /\
     dataSem_get_vars [a1; a2] (dataSem_state_locals s) = SOME
       [dataSem_Number (&i); vv] /\
     wordSem_get_var 1 t = SOME (word_Word (n2w (4 * i))) /\
     4 * i < dimword (:'a) /\
     wordSem_evaluate (AllocVar c limit' (list_insert [a1; a2] x'),t) =
       (q,r) /\
     limit' < dimword (:'a) DIV 8 ==>
     (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
        r = dataSem_state_ffi s /\ option_le (wordSem_state_stack_max r)
          (dataSem_state_stack_max s) /\
        (~(data_to_word_config_gc_kind c = data_to_word_None) /\ i < limit'
          /\ no_thunks_in_refs (dataSem_state_refs s) ==> limits_heap_limit
          (dataSem_state_limits
           s) <
             size_of_heap_args [dataSem_Number (&i); vv] (cut_locals x' s) +
               (i + 1))) /\
     (~(q = SOME wordSem_NotEnoughSpace) ==>
        i < limit' /\
        data_to_word_gcProof_state_rel c l1 l2
          (dataSem_state_space_fupd (K (i + 1)) (dataSem_state_locals_fupd
            (K xa) s)) r NONE locs /\
        FLOOKUP (wordSem_state_store r) (Temp (n2w 29)) = FLOOKUP
          (wordSem_state_store t) (Temp (n2w 29)) /\ wordSem_state_code
        r = wordSem_state_code t /\ wordSem_state_code_buffer r =
          wordSem_state_code_buffer t /\ wordSem_state_data_buffer
        r = wordSem_state_data_buffer t /\ wordSem_state_compile_oracle r =
          wordSem_state_compile_oracle t /\
        q = NONE)`,
  CHEAT_TAC);;

let assign_RefArray = prove
 (`op = clos_MemOp clos_RefArray ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

(* [local] *)
let LENGTH_n2mw_1 = prove
 (`LENGTH ((n2mw n):('a word) list) = 1 <=> ~(n = 0) /\ n < dimword (:'a)`,
  CHEAT_TAC);;

(* [local] *)
let WordFromInt_DIV_LEMMA = prove
 (`kk < B * B /\ 0 < B ==> B * (kk DIV B) <= B * B - B`,
  CHEAT_TAC);;

(* [local] *)
let explode_less_32 = prove
 (`(!n. n < 32 ==> P (n:num)) <=>
   P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\ P 6 /\ P 7 /\ P 8 /\ P 9 /\
   P 10 /\ P 11 /\ P 12 /\ P 13 /\ P 14 /\ P 15 /\ P 16 /\ P 17 /\ P 18 /\ P
     19 /\
   P 20 /\ P 21 /\ P 22 /\ P 23 /\ P 24 /\ P 25 /\ P 26 /\ P 27 /\ P 28 /\ P
     29 /\
   P 30 /\ P 31`,
  CHEAT_TAC);;

(* [local] *)
let LESS_IMP_NOT_BIT = prove
 (`!k n. n < 2 EXP k ==> ~(BIT k n)`,
  CHEAT_TAC);;

(* Smallnum_alt *)
let data_to_word_assignProof_Smallnum_alt = prove
 (`Smallnum i =
    if i < (&0) then ((n2w 0) - n2w (num_of_int (--i))) << 2 else n2w
      (num_of_int i) << 2`,
  CHEAT_TAC);;

(* [local] *)
let BIT_lemma = prove
 (`BIT n (2 EXP k - i) <=> (if n < k /\ i < 2 EXP k /\ ~(i = 0) then BIT n (2
  EXP (MAX n i + 1) - i)
                          else BIT n (2 EXP k - i))`,
  CHEAT_TAC);;

(* [local] *)
let BIT_Lemma2 = prove
 (`BIT m (2 EXP k - n) = if ~(n = 0) /\ n <= 2 EXP m /\ m < k then T
                        else BIT m (2 EXP k - n)`,
  CHEAT_TAC);;

let assign_WordFromInt = prove
 (`op = clos_WordOp WordFromInt ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_TagEq = prove
 (`(?tag. op = clos_BlockOp (clos_TagEq tag)) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let all_ones_get_addr = prove
 (`all_ones (data_to_word_config_len_bits c + (data_to_word_config_tag_bits c +
  1)) 0 &&
   get_addr c ptr (word_Word (ptr_bits c tag2 len2)) =
   ptr_bits c tag2 len2 || (n2w 1)`,
  CHEAT_TAC);;

let MULT_TWO_EXP_LESS_dimword = prove
 (`!b l n.
     b + l <= dimindex (:'a) /\ n < 2 EXP b ==>
     n * 2 EXP l < dimword (:'a)`,
  CHEAT_TAC);;

let maxout_bits_eq = prove
 (`b + l <= dimindex (:'a) /\ n' < 2 EXP b - 1 ==>
   (maxout_bits n b l = (maxout_bits n' b l:'a word) <=> n = n')`,
  CHEAT_TAC);;

let word_or_eq_word_or_split = prove
 (`w1 && w2 = (n2w 0) /\ v1 && v2 = (n2w 0) /\
   w1 && v2 = (n2w 0) /\ v1 && w2 = (n2w 0) ==>
   ((w1 || w2 = v1 || v2) <=> (w1 = v1 /\ w2 = v2))`,
  CHEAT_TAC);;

let ptr_bits_eq_ptr_bits = prove
 (`tag < 2 EXP data_to_word_config_tag_bits c - 1 /\
   len < 2 EXP data_to_word_config_len_bits c - 1
     /\ data_to_word_config_len_bits
   c + data_to_word_config_tag_bits c < dimindex (:'a) ==>
   ((ptr_bits c tag2 len2 || (n2w 1) =
     ptr_bits c tag len || ((n2w 1):'a word)) <=>
    (tag2 = tag /\ len2 = len))`,
  CHEAT_TAC);;

let maxout_bits_0 = prove
 (`maxout_bits 0 b e = (n2w 0)`,
  CHEAT_TAC);;

let ptr_bits_eq_ptr_bits_len_only = prove
 (`len < 2 EXP data_to_word_config_len_bits c - 1
  /\ data_to_word_config_len_bits
   c < dimindex (:'a) ==>
   ((ptr_bits c 0 len2 || (n2w 1) =
     ptr_bits c 0 len || ((n2w 1):'a word)) <=>
    (len2 = len))`,
  CHEAT_TAC);;

let assign_TagLenEq = prove
 (`(?tag len. op = clos_BlockOp (clos_TagLenEq tag len)) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let all_ones_and_1 = prove
 (`~(k = 0) ==> all_ones k 0 && (n2w 1) = (n2w 1)`,
  CHEAT_TAC);;

let all_ones_and_ptr_bits_tag_0 = prove
 (`all_ones (data_to_word_config_len_bits c + 1) 0 && ptr_bits c tag len =
  ptr_bits c 0 len`,
  CHEAT_TAC);;

let assign_LenEq = prove
 (`(?len. op = clos_BlockOp (clos_LenEq len)) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let state_rel_upd_safe_pkheap = prove
 (`!c l1 l2 s lcl hpk r locs. data_to_word_gcProof_state_rel c l1 l2
  (dataSem_state_stack_max_fupd (K NONE) (dataSem_state_space_fupd (K 0)
  (dataSem_state_locals_fupd (K lcl) s)))
                r NONE locs <=>
   data_to_word_gcProof_state_rel c l1 l2
                (dataSem_state_peak_heap_length_fupd (K hpk)
                  (dataSem_state_safe_for_space_fupd (K F)
                  (dataSem_state_space_fupd (K 0) (dataSem_state_stack_max_fupd
                  (K NONE) (dataSem_state_locals_fupd (K lcl) s)))))
                r NONE locs`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:9692-9693: ML code, not ported *)

(* HOL4 data_to_word_assignProofScript.sml:9695-9696: ML code, not ported *)

(* HOL4 data_to_word_assignProofScript.sml:9698-9699: ML code, not ported *)

(* HOL4 data_to_word_assignProofScript.sml:9701-9702: ML code, not ported *)

(* HOL4 data_to_word_assignProofScript.sml:9704-9705: ML code, not ported *)

let state_rel_ignore_safe_for_space = prove
 (`data_to_word_gcProof_state_rel c l1 l2 (dataSem_state_safe_for_space_fupd (K
  m) (dataSem_state_space_fupd (K s) (dataSem_state_locals_fupd (K l) x))) r t
  locs <=>
   data_to_word_gcProof_state_rel c l1 l2 (dataSem_state_space_fupd (K s)
     (dataSem_state_locals_fupd (K l) x)) r t locs`,
  CHEAT_TAC);;
add_simp state_rel_ignore_safe_for_space;;

let state_rel_peak_heap_length = prove
 (`data_to_word_gcProof_state_rel c l1 l2 (dataSem_state_peak_heap_length_fupd
  (K m) (dataSem_state_space_fupd (K s) (dataSem_state_locals_fupd (K l) x))) r
  t locs <=>
   data_to_word_gcProof_state_rel c l1 l2 (dataSem_state_space_fupd (K s)
     (dataSem_state_locals_fupd (K l) x)) r t locs`,
  CHEAT_TAC);;
add_simp state_rel_peak_heap_length;;

(* opt_map_plus_zero_id *)
let data_to_word_assignProof_opt_map_plus_zero_id = prove
 (`!n. OPTION_MAP2 (+) (SOME 0) n = (n:num option)`,
  CHEAT_TAC);;
add_simp data_to_word_assignProof_opt_map_plus_zero_id;;

let small_num_small_int = prove
 (`good_dimindex (:'a) ==>
   small_num (dimindex (:'a) = 64) = small_int (:'a)`,
  CHEAT_TAC);;
add_simp small_num_small_int;;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let memory_rel_small_int = prove
 (cake_as_vars (fun () ->
    `memory_rel c be ts refs sp st m dm (CONS (dataSem_Number i,word_Word (w:'a
  word)) vars) /\
     word_bit 0 w /\ good_dimindex (:'a) ==>
     ~(small_int (:'a) i)`),
  CHEAT_TAC);;

let small_int_Smallnum_add = prove
 (`good_dimindex (:'a) /\ small_int (:'a) (i1 + i2) ==>
   Smallnum i1 + ((Smallnum i2):'a word) = Smallnum (i1 + i2)`,
  CHEAT_TAC);;

let small_int_INT_MIN_MAX = prove
 (`good_dimindex (:'a) /\ small_int (:'a) i ==>
   (INT_MIN (:'a) <= (&4) * i /\ (&4) * i <= INT_MAX (:'a))`,
  CHEAT_TAC);;

let small_int_w2i_Smallnum_add = prove
 (`good_dimindex (:'a) /\
   small_int (:'a) (i1 + i2) /\
   small_int (:'a) i1 /\
   small_int (:'a) i2 ==>
   w2i (Smallnum i1 + ((Smallnum i2):'a word)) = w2i (Smallnum i1:'a word)
     + w2i (Smallnum i2:'a word)`,
  CHEAT_TAC);;

(* TODO: move? *)
(* OPTION_MAP2_NONE *)
let data_to_word_assignProof_OPTION_MAP2_NONE = prove
 (`(OPTION_MAP2 f NONE n = NONE) /\ (OPTION_MAP2 f n NONE = NONE)`,
  CHEAT_TAC);;
add_simp data_to_word_assignProof_OPTION_MAP2_NONE;;

let state_rel_IMP_arch_64_bit = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) xs
  locs ==>
   (limits_arch_64_bit (dataSem_state_limits s) = (dimindex (:'a) = 64))`,
  CHEAT_TAC);;

let cut_state_opt_twice = prove
 (`dataSem_cut_state_opt names_opt s = SOME x ==>
   dataSem_cut_state_opt names_opt x = SOME x`,
  CHEAT_TAC);;

let cut_state_opt_extra_const = prove
 (`dataSem_cut_state_opt names_opt s = SOME x ==>
  dataSem_state_stack_frame_sizes
   s = dataSem_state_stack_frame_sizes x /\ dataSem_state_locals_size
   s = dataSem_state_locals_size x`,
  CHEAT_TAC);;

let assign_Add = prove
 (`op = clos_IntOp clos_Add ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let small_int_Smallnum_sub = prove
 (`good_dimindex (:'a) /\ small_int (:'a) (i1 - i2) ==>
   Smallnum i1 - ((Smallnum i2):'a word) = Smallnum (i1 - i2)`,
  CHEAT_TAC);;

let small_int_w2i_Smallnum_sub = prove
 (`good_dimindex (:'a) /\ small_int (:'a) (i1 - i2) /\ small_int (:'a) i1
  /\ small_int (:'a) i2 ==>
   w2i (Smallnum i1 - ((Smallnum i2):'a word)) = w2i (Smallnum i1:'a word)
     - w2i (Smallnum i2:'a word)`,
  CHEAT_TAC);;

(* [local] *)
let word_bit_0_sub_lemma = prove
 (`!w1 (w2:'a word). ~(word_bit 0 w1) /\ ~(word_bit 0 w2) ==> ~(word_bit 0
  (w1 + --(n2w 1) * w2))`,
  CHEAT_TAC);;

let assign_Sub = prove
 (`op = clos_IntOp clos_Sub ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let cut_state_opt_IMP_ffi = prove
 (`dataSem_cut_state_opt names_opt s = SOME x ==> dataSem_state_ffi x =
  dataSem_state_ffi s`,
  CHEAT_TAC);;

let quad_times_div_half_double = prove
 (`(4 * j) DIV 2 = 2 * (j:num)`,
  CHEAT_TAC);;

let w2n_mul_less = prove
 (`!w w'.
     (w2n (w:'a word) * w2n (w':'a word)) < dimword (:'a) EXP 2`,
  CHEAT_TAC);;

let assign_Mult = prove
 (`op = clos_IntOp clos_Mult ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let word_bit_lsr_dimindex_1 = prove
 (`word_bit 0 ((w1 >>> (dimindex (:'a) - 1)):'a word) <=> word_msb w1`,
  CHEAT_TAC);;

let state_rel_Number_IMP = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE
  locs /\
    dataSem_get_var a1 (dataSem_state_locals s) = SOME (dataSem_Number i1)
      /\
    sptree_lookup (adjust_var a1) (wordSem_state_locals t) = SOME v1 ==>
    (?w1. (v1 = word_Word w1) /\
         (~(word_bit 0 w1) <=> small_int (:'a) i1) /\
         (~(word_msb w1) /\ ~(word_bit 0 w1) ==> (&0) <= i1 /\ w1 = n2w (4
           * num_of_int i1)))`,
  CHEAT_TAC);;

let option_le_add_comm = prove
 (`option_le (OPTION_MAP2 (+) a b) c ==>
     option_le (OPTION_MAP2 (+) b a) c`,
  CHEAT_TAC);;

let IN_adjust_set_IN = prove
 (`y IN sptree_domain (adjust_set x) ==> (y - 2) DIV 2 IN sptree_domain x`,
  CHEAT_TAC);;

let assign_Div = prove
 (`op = clos_IntOp clos_Div ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_Mod = prove
 (`op = (clos_IntOp clos_Mod) ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_LengthByte = prove
 (`op = clos_MemOp clos_LengthByte ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_Length = prove
 (`op = clos_MemOp clos_Length ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_LengthBlock = prove
 (`op = clos_BlockOp clos_LengthBlock ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_BoundsCheckBlock = prove
 (`data_to_word_assign c secn l dest (clos_BlockOp clos_BoundsCheckBlock) args
  names =
      match args with [v1; v2] -> (data_to_word_list_Seq [word_If asm_Test
        (adjust_var v1) (asm_Imm (n2w 1))
                              (word_Assign 1 (word_Const (n2w 0)))
                              (word_Assign 1
                              (let addr' = real_addr c (adjust_var v1) in
                              let header = word_Load addr' in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c in
                              (\sh e n. word_Shift sh e (word_Const (n2w
                                n))) Lsr header k));
                              word_Assign 3 (ShiftVar Ror (adjust_var v2)
                                2);
                              word_If asm_Lower 3 (asm_Reg 1)
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 18:'a word)))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 2:'a word)))],l)
      | _ -> ((word_Skip:'a word_prog),l)`,
  CHEAT_TAC);;

(* assign_BoundsCheckBlock[allow_rebind] *)
let data_to_word_assignProof_assign_BoundsCheckBlock = prove
 (`op = clos_BlockOp clos_BoundsCheckBlock ==> (data_to_word_gcProof_state_rel
  c l1 l2 (s:('c,'ffi)dataSem_state)
     (t:('a,'c,'ffi)wordSem_state) NONE locs /\
   (~(op_requires_names op = (names_opt = NONE))) /\
   dataSem_cut_state_opt names_opt s = SOME x /\
   dataSem_get_vars args (dataSem_state_locals s) = SOME vals
     /\ wordSem_state_termdep
   t > 1 /\
   dataSem_do_app op vals x = Rval (v,s2) ==>
   (?q (r:('a,'c,'ffi)wordSem_state).
     wordSem_evaluate (FST (data_to_word_assign c n l dest op args
       names_opt),t) = (q,r) /\
     (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
      r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
        (dataSem_state_stack_max s2) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
        ~(dataSem_state_safe_for_space s2))) /\
     (~(q = SOME wordSem_NotEnoughSpace) ==>
      data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
        NONE locs /\
      q = NONE)))`,
  CHEAT_TAC);;

let assign_BoundsCheckArray = prove
 (`data_to_word_assign c secn l dest (clos_MemOp clos_BoundsCheckArray) args
  names =
      match args with [v1; v2] -> (data_to_word_list_Seq [word_Assign 1
                              (let addr' = real_addr c (adjust_var v1) in
                              let header = word_Load addr' in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c in
                              (\sh e n. word_Shift sh e (word_Const (n2w
                                n))) Lsr header k);
                              word_Assign 3 (ShiftVar Ror (adjust_var v2)
                                2);
                              word_If asm_Lower 3 (asm_Reg 1)
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 18:'a word)))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 2:'a word)))],l)
      | _ -> ((word_Skip:'a word_prog),l)`,
  CHEAT_TAC);;

(* assign_BoundsCheckArray[allow_rebind] *)
let data_to_word_assignProof_assign_BoundsCheckArray = prove
 (`op = clos_MemOp clos_BoundsCheckArray ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_BoundsCheckByte = prove
 (`data_to_word_assign c secn l dest (clos_MemOp (clos_BoundsCheckByte leq))
  args names =
      match args with [v1; v2] -> (data_to_word_list_Seq [word_Assign 1
                              (let addr' = real_addr c (adjust_var v1) in
                              let header = word_Load addr' in
                              let extra = (if dimindex (:'a) = 32 then 2
                                else 3) in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c - extra in
                              word_Op asm_Sub [(\sh e n. word_Shift sh e
                                (word_Const (n2w n))) Lsr header k; word_Const
                                bytes_in_word]);
                              word_Assign 3 (ShiftVar Ror (adjust_var v2)
                                2);
                              (if leq then word_If asm_NotLower 1 (asm_Reg
                                3) else word_If asm_Lower 3 (asm_Reg 1))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 18:'a word)))
                              (word_Assign (adjust_var dest) (word_Const
                                (n2w 2:'a word)))],l)
      | _ -> ((word_Skip:'a word_prog),l)`,
  CHEAT_TAC);;

(* assign_BoundsCheckByte[allow_rebind] *)
let data_to_word_assignProof_assign_BoundsCheckByte = prove
 (`(?leq. op = clos_MemOp (clos_BoundsCheckByte leq)) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_LessConstSmall = prove
 (`data_to_word_assign c secn l dest (clos_IntOp (clos_LessConstSmall i)) args
  names =
      match args with [v1] -> (word_If asm_Less (adjust_var v1) (asm_Imm
        (n2w (4 * i)))
                  (word_Assign (adjust_var dest) (word_Const (n2w 18:'a
                    word)))
                  (word_Assign (adjust_var dest) (word_Const (n2w 2:'a
                    word))),l)
      | _ -> ((word_Skip:'a word_prog),l)`,
  CHEAT_TAC);;

(* [allow_rebind] *)
let assign_LessSmallConst = prove
 (`(?i. op = clos_IntOp (clos_LessConstSmall i)) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

(* [allow_rebind] *)
let assign_BoolNot = prove
 (`op = clos_BlockOp clos_BoolNot ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

(* [allow_rebind] *)
let assign_BoolTest = prove
 (`(?test. op = clos_BlockOp (clos_BoolTest test)) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

(* [allow_rebind] *)
let assign_WordTest = prove
 (`(?ws test. op = clos_WordOp (WordTest ws test)) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

(* Compare1_code_thm *)
let compare1_code_thm = prove
 (`!l a1 a2 dm m res (t:('a,'c,'ffi)wordSem_state).
      word_cmp_loop l a1 a2 dm m = SOME res /\
      dm = wordSem_state_mdomain t /\
      m = wordSem_state_memory t /\
      sptree_lookup Compare1_location (wordSem_state_code t) = SOME
        (4,Compare1_code) /\
      sptree_lookup Compare1_location (wordSem_state_stack_size t) =
        wordSem_state_locals_size t /\
      wordSem_get_var 0 t = SOME (word_Loc l1 l2) /\
      wordSem_get_var 2 t = SOME (word_Word l) /\
      wordSem_get_var 4 t = SOME (word_Word a1) /\
      wordSem_get_var 6 t = SOME (word_Word a2) /\
      w2n l <= wordSem_state_clock t ==>
      (?ck smx.
        wordSem_evaluate (Compare1_code,t) =
          (SOME (wordSem_Result (word_Loc l1 l2) [word_Word
            res]),wordSem_state_stack_max_fupd (K smx)
            (wordSem_state_locals_size_fupd (K (SOME 0))
            (wordSem_state_locals_fupd (K LN) (wordSem_state_clock_fupd (K ck)
           t)))) /\
        option_le smx (OPTION_MAP2 MAX (wordSem_state_stack_max t)
                              (OPTION_MAP2 (+) (stack_size
                                (wordSem_state_stack t))
                                (wordSem_state_locals_size t)))
                                /\ wordSem_state_clock
        t <= w2n l + ck)`,
  CHEAT_TAC);;

let word_exp_insert = prove
 (`(~(m = n) ==>
     (wordSem_word_exp (wordSem_state_locals_fupd (K (sptree_insert n w
       (wordSem_state_locals t))) t) (real_addr c m) =
      wordSem_word_exp t (real_addr c m))) /\
    (~(m IN {n,n1}) ==>
     (wordSem_word_exp (wordSem_state_locals_fupd (K (sptree_insert n w
       (sptree_insert n1 w1 (wordSem_state_locals t)))) t) (real_addr c m) =
      wordSem_word_exp t (real_addr c m)))`,
  CHEAT_TAC);;

(* Compare_code_thm *)
let compare_code_thm = prove
 (`memory_rel c (be:bool) ts refs sp st m dm
      (CONS (dataSem_Number i1,word_Word v1) (CONS (dataSem_Number
        i2,word_Word v2) vars)) /\
    dm = wordSem_state_mdomain (t:('a,'c,'ffi)wordSem_state) /\
    m = wordSem_state_memory t /\
    st = wordSem_state_store t /\
    (~(word_bit 0 v1) ==> word_bit 0 v2) /\
    shift_length c < dimindex (:'a) /\
    sptree_lookup Compare1_location (wordSem_state_code t) = SOME
      (4,Compare1_code) /\
    wordSem_get_var 0 t = SOME (word_Loc l1 l2) /\
    wordSem_get_var 2 t = SOME (word_Word (v1:'a word)) /\
    wordSem_get_var 4 t = SOME (word_Word (v2:'a word)) /\
    dimword (:'a) < wordSem_state_clock t /\ ~(data_to_word_config_len_size
    c = 0) /\ data_to_word_config_len_size
    c < dimindex (:'a) /\
    good_dimindex (:'a) ==>
    (?ck smx.
      wordSem_evaluate (Compare_code c,t) =
        (SOME (wordSem_Result (word_Loc l1 l2) [word_Word (word_cmp_res i1
          i2)]),wordSem_state_stack_max_fupd (K smx)
          (wordSem_state_locals_size_fupd (K (SOME 0))
          (wordSem_state_locals_fupd (K LN) (wordSem_state_clock_fupd (K ck)
         t)))) /\
        option_le smx (OPTION_MAP2 MAX (wordSem_state_stack_max
                         t)
                           (OPTION_MAP2 (+) (stack_size (wordSem_state_stack
                             t))
                              (sptree_lookup Compare1_location
                                (wordSem_state_stack_size t)))))`,
  CHEAT_TAC);;

let word_cmp_Less_word_cmp_res = prove
 (`!i i'. good_dimindex (:'a) ==>
           (asm_word_cmp asm_Less (word_cmp_res i i') ((n2w 1):'a word)
             <=> i < i')`,
  CHEAT_TAC);;

let word_cmp_NotLess_word_cmp_res = prove
 (`!i i'. good_dimindex (:'a) ==>
           (asm_word_cmp asm_NotLess ((n2w 1):'a word) (word_cmp_res i i')
             <=> (i <= i'))`,
  CHEAT_TAC);;

let word_cmp_not_NotLess_word_cmp_res = prove
 (`!i i'. good_dimindex (:'a) ==>
           (~(asm_word_cmp asm_NotLess ((n2w 1):'a word) (word_cmp_res i
             i')) <=> (i' < i))`,
  CHEAT_TAC);;

let not_word_cmp_Less_word_cmp_res = prove
 (`!i i'. good_dimindex (:'a) ==>
           (~(asm_word_cmp asm_Less (word_cmp_res i i') ((n2w 1):'a word))
             <=> (i' <= i))`,
  CHEAT_TAC);;

let IMP_spt_eq = prove
 (`sptree_wf t1 /\ sptree_wf t2 /\ (!n. sptree_lookup n t1 = sptree_lookup n
  t2) ==> (t1 = t2)`,
  CHEAT_TAC);;

let env_to_list_cut_env_IMP = prove
 (`env_to_list x (wordSem_state_permute t) = (l,permute) /\ wordSem_cut_env y s
  = SOME x ==>
    (fromAList l = x)`,
  CHEAT_TAC);;

let dimword_LESS_MustTerminate_limit = prove
 (`good_dimindex (:'a) ==> dimword (:'a) < MustTerminate_limit (:'a) - 1`,
  CHEAT_TAC);;

let assign_Less = prove
 (`op = clos_IntOp clos_Less ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_LessEq = prove
 (`op = clos_IntOp clos_LessEq ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let word_exp_set_var_ShiftVar = prove
 (`wordSem_word_exp (wordSem_set_var v (word_Word w) t) (ShiftVar sow v n) =
    OPTION_MAP word_Word (match sow with Lsl -> SOME (w << n)
                         | Lsr -> SOME (w >>> n)
                         | Asr -> SOME (w >> n)
                         | Ror -> SOME (word_ror w n))`,
  CHEAT_TAC);;

(* [local] *)
let MemEqList_thm = prove
 (`!offset t xs dm m b a.
       word_mem_eq (a + offset) xs dm m = SOME b /\
       wordSem_get_var 3 t = SOME (word_Word a) /\ dm =
         wordSem_state_mdomain t /\ m = wordSem_state_memory t ==>
       (?x. wordSem_evaluate (MemEqList offset xs,t) =
             (NONE,wordSem_state_locals_fupd (K (((if b then sptree_insert 1
               (word_Word (n2w 18)) else I) o
                              (if ~(xs = []) then sptree_insert 5 x else
                                I)) (wordSem_state_locals t))) t))`,
  CHEAT_TAC);;
let data_to_word_assignProof_MemEqList_thm =
  SIMP_RULE [WORD_ADD_0] (CAKE_SPEC `(n2w 0)` MemEqList_thm);;

let assign_EqualConst = prove
 (`(?p. op = clos_BlockOp (clos_EqualConst p)) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

(* TODO: move to backendProps *)
let option_map_mult_suc = prove
 (`OPTION_MAP ((*) (SUC n)) m =
   OPTION_MAP2 (+) m (OPTION_MAP ((*) n) m)`,
  CHEAT_TAC);;

let eq_code_stack_max_sub1 = prove
 (`~(l = 0) ==>
     eq_code_stack_max l tsz =
     OPTION_MAP2 ((+))
       (OPTION_MAP2 MAX
         (sptree_lookup Equal_location tsz)
         (OPTION_MAP2 MAX
           (sptree_lookup Equal1_location tsz)
           (sptree_lookup Compare1_location tsz)))
       (eq_code_stack_max (l - 1) tsz)`,
  CHEAT_TAC);;

let eq_code_stack_max_le_mono = prove
 (`a <= b ==>
   option_le (eq_code_stack_max a tsz) (eq_code_stack_max b tsz)`,
  CHEAT_TAC);;

let sane_locals_size_def = new_definition
  `sane_locals_size t = (wordSem_state_locals_size t = sptree_lookup
  Equal_location (wordSem_state_stack_size t) \/ wordSem_state_locals_size
                         t = sptree_lookup Equal1_location
                           (wordSem_state_stack_size t))`;;

(* Equal_code_lemma *)
let equal_code_lemma = prove
 (`(!c st dm m l wck v1 v2 t l1 l2 res l' wck'.
      word_eq c st dm m l wck v1 v2 = SOME (res,l',wck') /\
      dm = wordSem_state_mdomain (t:('a,'c,'ffi)wordSem_state) /\
      m = wordSem_state_memory t /\
      st = wordSem_state_store t /\
      l <= wordSem_state_clock t /\
      shift_length c < dimindex (:'a) /\
      sptree_lookup Equal_location (wordSem_state_code t) = SOME
        (3,Equal_code c) /\
      sptree_lookup Equal1_location (wordSem_state_code t) = SOME
        (4,Equal1_code) /\
      sptree_lookup Compare1_location (wordSem_state_code t) = SOME
        (4,Compare1_code) /\
      wordSem_get_var 0 t = SOME (word_Loc l1 l2) /\
      wordSem_get_var 2 t = SOME (word_Word (v1:'a word)) /\
      wordSem_get_var 4 t = SOME (word_Word (v2:'a word))
        /\ ~(data_to_word_config_len_size
      c = 0) /\ data_to_word_config_len_size
      c < dimindex (:'a) /\
      sane_locals_size t /\
      good_dimindex (:'a) ==>
      (?ck new_p smx.
        wordSem_evaluate (Equal_code c,t) =
         (SOME (wordSem_Result (word_Loc l1 l2) [word_Word
           res]),wordSem_state_stack_max_fupd (K smx)
           (wordSem_state_permute_fupd (K new_p)
           (wordSem_state_locals_size_fupd (K (SOME 0))
           (wordSem_state_locals_fupd (K LN) (wordSem_state_clock_fupd (K ck)
          t))))) /\
        option_le smx (OPTION_MAP2 MAX (wordSem_state_stack_max t)
                              (OPTION_MAP2 (+)
                              (stack_size (wordSem_state_stack t))
                              (eq_code_stack_max (wck + 1)
                                (wordSem_state_stack_size t)))) /\
        l' <= ck)) /\
    (!c st dm m l wck w a1 a2 t l1 l2 res l' wck'.
      word_eq_list c st dm m l wck w a1 a2 = SOME (res,l',wck') /\
      dm = wordSem_state_mdomain (t:('a,'c,'ffi)wordSem_state) /\
      m = wordSem_state_memory t /\
      st = wordSem_state_store t /\
      l <= wordSem_state_clock t /\
      shift_length c < dimindex (:'a) /\
      sptree_lookup Equal_location (wordSem_state_code t) = SOME
        (3,Equal_code c) /\
      sptree_lookup Equal1_location (wordSem_state_code t) = SOME
        (4,Equal1_code) /\
      sptree_lookup Compare1_location (wordSem_state_code t) = SOME
        (4,Compare1_code) /\
      wordSem_get_var 0 t = SOME (word_Loc l1 l2) /\
      wordSem_get_var 2 t = SOME (word_Word (w:'a word)) /\
      wordSem_get_var 4 t = SOME (word_Word (a1:'a word)) /\
      wordSem_get_var 6 t = SOME (word_Word (a2:'a word)) /\
      sane_locals_size t /\ ~(data_to_word_config_len_size
      c = 0) /\ data_to_word_config_len_size
      c < dimindex (:'a) /\
      good_dimindex (:'a) ==>
      (?ck new_p smx.
        wordSem_evaluate (Equal1_code,t) =
          (SOME (wordSem_Result (word_Loc l1 l2) [word_Word
            res]),wordSem_state_stack_max_fupd (K smx)
            (wordSem_state_permute_fupd (K new_p)
            (wordSem_state_locals_size_fupd (K (SOME 0))
            (wordSem_state_locals_fupd (K LN) (wordSem_state_clock_fupd (K ck)
           t))))) /\
        option_le smx (OPTION_MAP2 MAX (wordSem_state_stack_max t)
                              (OPTION_MAP2 (+)
                              (stack_size (wordSem_state_stack t))
                              (eq_code_stack_max (wck + 1)
                                (wordSem_state_stack_size t)))) /\
        l' <= ck))`,
  CHEAT_TAC);;

(* Equal_code_thm *)
let equal_code_thm = prove
 (`word_eq c st dm m l wck v1 v2 = SOME (res,l',wck') /\
   dm = wordSem_state_mdomain (t:('a,'c,'ffi)wordSem_state) /\
   m = wordSem_state_memory t /\
   st = wordSem_state_store t /\
   l <= wordSem_state_clock t /\
   shift_length c < dimindex (:'a) /\ wordSem_state_locals_size
   t = sptree_lookup Equal_location (wordSem_state_stack_size t) /\
   sptree_lookup Equal_location (wordSem_state_code t) = SOME (3,Equal_code
     c) /\
   sptree_lookup Equal1_location (wordSem_state_code t) = SOME
     (4,Equal1_code) /\
   sptree_lookup Compare1_location (wordSem_state_code t) = SOME
     (4,Compare1_code) /\
   wordSem_get_var 0 t = SOME (word_Loc l1 l2) /\
   wordSem_get_var 2 t = SOME (word_Word (v1:'a word)) /\
   wordSem_get_var 4 t = SOME (word_Word (v2:'a word))
     /\ ~(data_to_word_config_len_size
   c = 0) /\ data_to_word_config_len_size
   c < dimindex (:'a) /\
   good_dimindex (:'a) ==>
   (?ck new_p smx.
     wordSem_evaluate (Equal_code c,t) =
       (SOME (wordSem_Result (word_Loc l1 l2) [word_Word
         res]),wordSem_state_stack_max_fupd (K smx) (wordSem_state_permute_fupd
         (K new_p) (wordSem_state_locals_size_fupd (K (SOME 0))
         (wordSem_state_locals_fupd (K LN) (wordSem_state_clock_fupd (K ck)
        t))))) /\
     option_le smx (OPTION_MAP2 MAX (wordSem_state_stack_max t)
                              (OPTION_MAP2 (+)
                              (stack_size (wordSem_state_stack t))
                              (eq_code_stack_max (wck + 1)
                                (wordSem_state_stack_size t)))) /\
     l' <= ck)`,
  CHEAT_TAC);;

(* MIN_SUB[local] *)
let data_to_word_assignProof_MIN_SUB = prove
 (`MIN a b - c = MIN (a - c) (b - c)`,
  CHEAT_TAC);;

let assign_Equal = prove
 (`op = clos_BlockOp clos_Equal ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_WordOpW8 = prove
 (`(?opw. op = clos_WordOp (WordOpw ast_W8 opw)) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:13152-13154: the ML values that
   the definitions below antiquote *)

let mw2n_2_IMP = prove
 (`mw2n [w1; w2:'a word] = n ==>
    w2 = n2w (n DIV dimword (:'a)) /\
    w1 = n2w n`,
  CHEAT_TAC);;

let IMP_mw2n_2 = prove
 (`Abbrev (x2 = (63 >< 32) (n2w n:word64)) /\
    Abbrev (x1 = (31 >< 0) (n2w n:word64)) /\
    n < dimword (:64) /\ dimindex (:'a) = 32 ==>
    mw2n [x1; x2:'a word] = n`,
  CHEAT_TAC);;

let evaluate_WordOp64_on_32 = prove
 (`!l.
    dimindex (:'a) = 32 ==>
    (?w27 w29.
      wordSem_evaluate
       (WordOp64_on_32 opw,wordSem_state_locals_fupd (K
          (sptree_insert 23 (word_Word ((31 >< 0) c''))
            (sptree_insert 21 (word_Word ((63 >< 32) c''))
               (sptree_insert 13 (word_Word ((31 >< 0) c'))
                  (sptree_insert 11 (word_Word ((63 >< 32) c')) l)))))
        (t:('a,'c,'ffi)wordSem_state)) =
     (NONE,wordSem_state_locals_fupd (K
       (sptree_insert 31 (word_Word ((63 >< 32) (opw_lookup opw c' c'')))
        (sptree_insert 33 (word_Word ((31 >< 0) (opw_lookup opw (c':word64)
          (c'':word64))))
          (sptree_insert 27 w27
            (sptree_insert 29 w29
              (sptree_insert 23 (word_Word ((31 >< 0) c''))
                (sptree_insert 21 (word_Word ((63 >< 32) c''))
                  (sptree_insert 13 (word_Word ((31 >< 0) c'))
                    (sptree_insert 11 (word_Word ((63 >< 32) c'))
                      l))))))))) t))`,
  CHEAT_TAC);;

let IMP_encode_header_NOT_NONE = prove
 (`dimindex (:'a) = 32 /\ 1 < data_to_word_config_len_size c /\ 1 < 30 -
  data_to_word_config_len_size c ==> ~(encode_header c 3 2 = (NONE:('a word)
  option))`,
  CHEAT_TAC);;

let assign_WordOpW64 = prove
 (`(?opw. op = clos_WordOp (WordOpw ast_W64 opw)) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_WordShiftW8 = prove
 (`(?sh n. op = clos_WordOp (WordShift ast_W8 sh n)) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:13734-13736: the ML values that
   the definitions below antiquote *)

let evaluate_WordShift64_on_32 = prove
 (`!l.
    dimindex (:'a) = 32 ==>
      wordSem_evaluate
       (WordShift64_on_32 sh n,wordSem_state_locals_fupd (K
          (sptree_insert 13 (word_Word ((31 >< 0) c'))
          (sptree_insert 11 (word_Word ((63 >< 32) c')) l)))
        (t:('a,'c,'ffi)wordSem_state)) =
     (NONE,wordSem_state_locals_fupd (K
       (sptree_insert 31 (word_Word ((63 >< 32) (shift_lookup sh c' n)))
        (sptree_insert 33 (word_Word ((31 >< 0) (shift_lookup sh (c':word64)
          n)))
          (sptree_insert 13 (word_Word ((31 >< 0) c'))
            (sptree_insert 11 (word_Word ((63 >< 32) c')) l))))) t)`,
  CHEAT_TAC);;

let assign_WordShiftW64 = prove
 (`(?sh n. op = clos_WordOp (WordShift ast_W64 sh n)) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:13990-13992: ML code, not ported *)

(* HOL4 data_to_word_assignProofScript.sml:13994-13996: ML code, not ported *)

(* HOL4 data_to_word_assignProofScript.sml:13998-14000: ML code, not ported *)

(* HOL4 data_to_word_assignProofScript.sml:14002-14004: ML code, not ported *)

let w2w_select_id = prove
 (`dimindex (:'a) = 64 ==>
    ((w2w:'a word->word64) ((63 >< 0) w)) = w`,
  CHEAT_TAC);;

let extract_append_id = prove
 (`dimindex (:'a) = 32 ==>
    ((((63 >< 32) w):'a word) @@ (((31 >< 0) w):'a word)) = (w:word64)`,
  CHEAT_TAC);;

let word1_cases = prove
 (`!(w:word1). w = (n2w 0) \/ w = (n2w 1)`,
  CHEAT_TAC);;

let w2w_w2w_64 = prove
 (`!w. dimindex (:'a) = 64 ==> w2w ((w2w w):'a word) = (w:word64)`,
  CHEAT_TAC);;

(* [local] *)
let fp_greater = prove
 (`fp64_greaterThan a b = fp64_lessThan b a /\
   fp64_greaterEqual a b = fp64_lessEqual b a`,
  CHEAT_TAC);;

let assign_FP_cmp = prove
 (`(?fpc. op = clos_WordOp (FP_cmp fpc)) ==> (data_to_word_gcProof_state_rel c
  l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_FP_top = prove
 (`(?fpt. op = clos_WordOp (FP_top fpt)) ==> (data_to_word_gcProof_state_rel c
  l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_FP_bop = prove
 (`(?fpb. op = clos_WordOp (FP_bop fpb)) ==> (data_to_word_gcProof_state_rel c
  l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_FP_uop = prove
 (`(?fpu. op = clos_WordOp (FP_uop fpu)) ==> (data_to_word_gcProof_state_rel c
  l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_Label = prove
 (`(?lab. op = clos_Label lab) ==> (data_to_word_gcProof_state_rel c l1 l2
  (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

(* do_app_Ref *)
let data_to_word_assignProof_do_app_Ref = prove
 (`dataSem_do_app (clos_MemOp clos_Ref) vals x =
    (match consume_space (LENGTH vals + 1) x with
      NONE -> Rerr (Rabort Rtype_error)
    | SOME s1 ->
      Rval
      (dataSem_RefPtr T (minimal ptr. ~(ptr IN sptree_domain
        (dataSem_state_refs s1))),dataSem_state_stack_max_fupd (K
        (dataSem_state_stack_max
             (do_stack (clos_MemOp clos_Ref) vals (do_lim_safe s1
               (clos_MemOp clos_Ref) vals))))
               (dataSem_state_safe_for_space_fupd (K
               (dataSem_state_safe_for_space (do_stack (clos_MemOp clos_Ref)
               vals (do_lim_safe s1 (clos_MemOp clos_Ref) vals))))
               (dataSem_state_refs_fupd (K (sptree_insert (minimal ptr. ~(ptr
               IN sptree_domain (dataSem_state_refs s1))) (bvlSem_ValueArray
               vals) (dataSem_state_refs s1)))
         s1))))`,
  CHEAT_TAC);;

let assign_Ref = prove
 (`op = clos_MemOp clos_Ref ==> (data_to_word_gcProof_state_rel c l1 l2
  (s:('c,'ffi)dataSem_state)
     (t:('a,'c,'ffi)wordSem_state) NONE locs /\
   (~(op_requires_names op = (names_opt = NONE))) /\
   dataSem_cut_state_opt names_opt s = SOME x /\
   dataSem_get_vars args (dataSem_state_locals s) = SOME vals
     /\ wordSem_state_termdep
   t > 1 /\
   dataSem_do_app op vals x = Rval (v,s2) ==>
   (?q (r:('a,'c,'ffi)wordSem_state).
     wordSem_evaluate (FST (data_to_word_assign c n l dest op args
       names_opt),t) = (q,r) /\
     (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
      r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
        (dataSem_state_stack_max s2) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
        ~(dataSem_state_safe_for_space s2))) /\
     (~(q = SOME wordSem_NotEnoughSpace) ==>
      data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
        NONE locs /\
      q = NONE)))`,
  CHEAT_TAC);;

let assign_Update = prove
 (`op = clos_MemOp clos_Update ==> (data_to_word_gcProof_state_rel c l1 l2
  (s:('c,'ffi)dataSem_state)
     (t:('a,'c,'ffi)wordSem_state) NONE locs /\
   (~(op_requires_names op = (names_opt = NONE))) /\
   dataSem_cut_state_opt names_opt s = SOME x /\
   dataSem_get_vars args (dataSem_state_locals s) = SOME vals
     /\ wordSem_state_termdep
   t > 1 /\
   dataSem_do_app op vals x = Rval (v,s2) ==>
   (?q (r:('a,'c,'ffi)wordSem_state).
     wordSem_evaluate (FST (data_to_word_assign c n l dest op args
       names_opt),t) = (q,r) /\
     (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
      r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
        (dataSem_state_stack_max s2) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
        ~(dataSem_state_safe_for_space s2))) /\
     (~(q = SOME wordSem_NotEnoughSpace) ==>
      data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
        NONE locs /\
      q = NONE)))`,
  CHEAT_TAC);;

let assign_El = prove
 (`op = clos_MemOp clos_El ==> (data_to_word_gcProof_state_rel c l1 l2
  (s:('c,'ffi)dataSem_state)
     (t:('a,'c,'ffi)wordSem_state) NONE locs /\
   (~(op_requires_names op = (names_opt = NONE))) /\
   dataSem_cut_state_opt names_opt s = SOME x /\
   dataSem_get_vars args (dataSem_state_locals s) = SOME vals
     /\ wordSem_state_termdep
   t > 1 /\
   dataSem_do_app op vals x = Rval (v,s2) ==>
   (?q (r:('a,'c,'ffi)wordSem_state).
     wordSem_evaluate (FST (data_to_word_assign c n l dest op args
       names_opt),t) = (q,r) /\
     (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
      r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
        (dataSem_state_stack_max s2) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
        ~(dataSem_state_safe_for_space s2))) /\
     (~(q = SOME wordSem_NotEnoughSpace) ==>
      data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
        NONE locs /\
      q = NONE)))`,
  CHEAT_TAC);;

let assign_ElemAt = prove
 (`(?n. op = clos_BlockOp (clos_ElemAt n)) ==> (data_to_word_gcProof_state_rel
  c l1 l2 (s:('c,'ffi)dataSem_state)
     (t:('a,'c,'ffi)wordSem_state) NONE locs /\
   (~(op_requires_names op = (names_opt = NONE))) /\
   dataSem_cut_state_opt names_opt s = SOME x /\
   dataSem_get_vars args (dataSem_state_locals s) = SOME vals
     /\ wordSem_state_termdep
   t > 1 /\
   dataSem_do_app op vals x = Rval (v,s2) ==>
   (?q (r:('a,'c,'ffi)wordSem_state).
     wordSem_evaluate (FST (data_to_word_assign c n l dest op args
       names_opt),t) = (q,r) /\
     (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
      r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
        (dataSem_state_stack_max s2) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
        ~(dataSem_state_safe_for_space s2))) /\
     (~(q = SOME wordSem_NotEnoughSpace) ==>
      data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
        NONE locs /\
      q = NONE)))`,
  CHEAT_TAC);;

let assign_UpdateByte = prove
 (`op = clos_MemOp clos_UpdateByte ==> (data_to_word_gcProof_state_rel c l1 l2
  (s:('c,'ffi)dataSem_state)
     (t:('a,'c,'ffi)wordSem_state) NONE locs /\
   (~(op_requires_names op = (names_opt = NONE))) /\
   dataSem_cut_state_opt names_opt s = SOME x /\
   dataSem_get_vars args (dataSem_state_locals s) = SOME vals
     /\ wordSem_state_termdep
   t > 1 /\
   dataSem_do_app op vals x = Rval (v,s2) ==>
   (?q (r:('a,'c,'ffi)wordSem_state).
     wordSem_evaluate (FST (data_to_word_assign c n l dest op args
       names_opt),t) = (q,r) /\
     (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
      r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
        (dataSem_state_stack_max s2) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
        ~(dataSem_state_safe_for_space s2))) /\
     (~(q = SOME wordSem_NotEnoughSpace) ==>
      data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
        NONE locs /\
      q = NONE)))`,
  CHEAT_TAC);;

let assign_DerefByte = prove
 (`op = clos_MemOp clos_DerefByte ==> (data_to_word_gcProof_state_rel c l1 l2
  (s:('c,'ffi)dataSem_state)
     (t:('a,'c,'ffi)wordSem_state) NONE locs /\
   (~(op_requires_names op = (names_opt = NONE))) /\
   dataSem_cut_state_opt names_opt s = SOME x /\
   dataSem_get_vars args (dataSem_state_locals s) = SOME vals
     /\ wordSem_state_termdep
   t > 1 /\
   dataSem_do_app op vals x = Rval (v,s2) ==>
   (?q (r:('a,'c,'ffi)wordSem_state).
     wordSem_evaluate (FST (data_to_word_assign c n l dest op args
       names_opt),t) = (q,r) /\
     (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
      r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
        (dataSem_state_stack_max s2) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
        ~(dataSem_state_safe_for_space s2))) /\
     (~(q = SOME wordSem_NotEnoughSpace) ==>
      data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
        NONE locs /\
      q = NONE)))`,
  CHEAT_TAC);;

let assign_Const = prove
 (`(?i. op = clos_IntOp (clos_Const i)) ==> (data_to_word_gcProof_state_rel c
  l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_GlobalsPtr = prove
 (`op = clos_GlobOp clos_GlobalsPtr ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_Global = prove
 (`(?n. op = clos_GlobOp (clos_Global n)) ==> (data_to_word_gcProof_state_rel c
  l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_SetGlobal = prove
 (`(?n. op = clos_GlobOp (clos_SetGlobal n)) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_SetGlobalsPtr = prove
 (`op = clos_GlobOp clos_SetGlobalsPtr ==> (
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let IMP = prove
 (`b1 \/ b2 <=> ~b1 ==> b2`,
  CHEAT_TAC);;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let memcopy_def,memcopy_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3,x4). (\n. n) x0)`
  `memcopy k a1 a2 m dm =
     if k = 0 then SOME m else if a1 IN dm /\ a2 IN dm then
         memcopy (k - 1) (a1 + bytes_in_word) (a2 + bytes_in_word) ((a2 =+ m
           a1) m) dm
       else NONE`;;

let MemCopy_thm = prove
 (`!ret_val l1 l2 k a1 a2 (s:('a,'c,'ffi)wordSem_state) m dm m1.
      memcopy k a1 a2 m dm = SOME m1 /\ wordSem_state_memory
      s = m /\ wordSem_state_mdomain s = dm /\
      sptree_lookup MemCopy_location (wordSem_state_code s) = SOME
        (5,MemCopy_code) /\
      k <= wordSem_state_clock s /\ 4 * k < dimword (:'a) /\
      wordSem_get_var 0 s = SOME (word_Loc l1 l2) /\
      wordSem_get_var 2 s = SOME (word_Word (n2w (4 * k))) /\
      wordSem_get_var 4 s = SOME (word_Word (a1:'a word)) /\
      wordSem_get_var 6 s = SOME (word_Word a2) /\
      wordSem_get_var 8 s = SOME ret_val ==>
      (?smx.
      wordSem_evaluate (MemCopy_code,s) =
        (SOME (wordSem_Result (word_Loc l1 l2)
          [ret_val]),wordSem_state_stack_max_fupd (K smx)
          (wordSem_state_locals_size_fupd (K (SOME 0))
          (wordSem_state_locals_fupd (K LN) (wordSem_state_memory_fupd (K m1)
          (wordSem_state_clock_fupd (K (wordSem_state_clock s - k))
         s))))) /\
      option_le smx
        (OPTION_MAP2 MAX (wordSem_state_stack_max s)
          (OPTION_MAP2 (+) (stack_size (wordSem_state_stack s))
                          (sptree_lookup MemCopy_location
                            (wordSem_state_stack_size s)))))`,
  CHEAT_TAC);;

let assign_ConsExtend_expand =
  SIMP_CONV [assign_def] `data_to_word_assign c n l dest (clos_BlockOp
  (clos_ConsExtend tag)) args names_opt`;;

(* get_vars_IMP_domain *)
let data_to_word_assignProof_get_vars_IMP_domain = prove
 (`!xs s y.
      dataSem_get_vars xs s = SOME y ==>
      ALL (\x. x IN sptree_domain s) xs`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let memory_rel_IMP_free_space = prove
 (cake_as_vars (fun () ->
    `memory_rel c be ts refs sp st m dm vars ==>
      (?nfree curr other.
        FLOOKUP st NextFree = SOME (word_Word nfree) /\
        FLOOKUP st CurrHeap = SOME (word_Word curr) /\
        (word_list_exists nfree sp * other) (fun2set (m,dm)))`),
  CHEAT_TAC);;

let IMP_store_list_SOME = prove
 (`!ws a n m dm other.
      (word_list_exists a n * other) (fun2set (m,dm)) /\ LENGTH ws <= n ==>
      (?m1. data_to_word_memoryProof_store_list a ws m dm = SOME m1 /\
           (misc_word_list a ws *
            word_list_exists (a + bytes_in_word * n2w (LENGTH ws)) (n -
              LENGTH ws) *
            other) (fun2set (m1,dm)))`,
  CHEAT_TAC);;

let get_vars_cut_env = prove
 (`!vs bs.
      dataSem_cut_env nms x1 = SOME x2 /\
      dataSem_get_vars vs x1 = SOME bs /\
      ALL (\v. v IN sptree_domain nms) vs ==>
      dataSem_get_vars vs x2 = SOME bs`,
  CHEAT_TAC);;

let word_exp_real_addr_some_value = prove
 (`FLOOKUP (wordSem_state_store s3) CurrHeap = SOME (word_Word curr) /\
    wordSem_get_var a s3 = SOME (word_Word ww) /\
    good_dimindex (:'a) /\ shift_length c < dimindex (:'a) ==>
    (?wx. wordSem_word_exp (s3:('a,'c,'ffi)wordSem_state) (real_addr c a)
      = SOME (word_Word wx))`,
  CHEAT_TAC);;

let store_list_APPEND = prove
 (`!xs ys a m.
      data_to_word_memoryProof_store_list a (APPEND xs ys) m dm =
      match data_to_word_memoryProof_store_list a xs m dm with NONE -> NONE
      | SOME m1 -> data_to_word_memoryProof_store_list (a + bytes_in_word
        * n2w (LENGTH xs)) ys m1 dm`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let memory_rel_store_list_to_unused = prove
 (cake_as_vars (fun () ->
    `!ws2 m dm m1.
        memory_rel c be ts refs n st m dm vars /\
        data_to_word_memoryProof_store_list nfree ws2 m dm = SOME m1 /\
        FLOOKUP st NextFree = SOME (word_Word nfree) /\ LENGTH ws2 <= n
          ==>
        memory_rel c be ts refs n st m1 dm vars`),
  CHEAT_TAC);;

let get_vars_delete_lemma = prove
 (`!t7. wordSem_get_vars (MAP adjust_var t7) (wordSem_state_locals_fupd (K
               (sptree_insert 9 x9
                 (sptree_insert 7 x7
                    (sptree_insert 5 x5
                       (sptree_insert 1 x1 (wordSem_state_locals s1))))))
                         s1) =
      wordSem_get_vars (MAP adjust_var t7) s1`,
  CHEAT_TAC);;

let INTRO_IS_SOME = prove
 (`(?v. x = SOME v) <=> IS_SOME x`,
  CHEAT_TAC);;

let STAR_fun2set_IMP_SEP_T = prove
 (`(p * q) (fun2set (m,dm)) ==> (p * SEP_T) (fun2set (m,dm))`,
  CHEAT_TAC);;

let IMP_memcopy_lemma = prove
 (`memory_rel c (wordSem_state_be s1) ts (dataSem_state_refs x) sp
  (wordSem_state_store s1) m1 (wordSem_state_mdomain s1)
      (CONS (dataSem_Block ts' n' l',word_Word w_ptr) (APPEND (ZIP ys7 ws1)
        vars)) /\
    startptr < LENGTH l' /\ LENGTH ys7 = LENGTH ws1 /\ good_dimindex (:'a)
      /\
    sptree_lookup (adjust_var a1) (wordSem_state_locals s1) = SOME
      (word_Word (w_ptr:'a word)) /\
    wordSem_word_exp s1 (real_addr c (adjust_var a1)) = SOME (word_Word wx)
      ==>
    memory_rel c (wordSem_state_be s1) ts (dataSem_state_refs x) sp
      (wordSem_state_store s1) m1 (wordSem_state_mdomain s1)
      (CONS (dataSem_Block ts' n' l',word_Word w_ptr)
       (APPEND (ZIP (APPEND ys7 [EL startptr l']) (APPEND ws1 [m1 (wx +
         bytes_in_word + bytes_in_word * n2w startptr)])) vars)) /\
    (wx + bytes_in_word + bytes_in_word * n2w startptr) IN
      wordSem_state_mdomain s1`,
  CHEAT_TAC);;

let IMP_memcopy = prove
 (`!len startptr m1 m2 ws1 ys7 k ts.
         memory_rel c (wordSem_state_be s1) ts (dataSem_state_refs x) sp
           (wordSem_state_store s1) m1 (wordSem_state_mdomain s1)
           (CONS (dataSem_Block ts' n' l',word_Word w_ptr) (APPEND (ZIP ys7
             ws1) vars)) /\
         (misc_word_list nfree (CONS (word_Word full_header) ws1) *
          word_list_exists
            (nfree + bytes_in_word * n2w (SUC (LENGTH ws1))) k * other)
              (fun2set (m1,wordSem_state_mdomain s1)) /\ len <= k
                /\ good_dimindex (:'a) /\
         sptree_lookup (adjust_var a1) (wordSem_state_locals s1) = SOME
           (word_Word (w_ptr:'a word)) /\
         wordSem_word_exp s1 (real_addr c (adjust_var a1)) = SOME (word_Word
           wx) /\
         FLOOKUP (wordSem_state_store s1) NextFree = SOME (word_Word nfree)
           /\
         startptr + len <= LENGTH l' /\
         LENGTH ws1 + len < sp /\
         LENGTH ys7 = LENGTH ws1 ==>
         (?m2 ws2.
           memcopy len (wx + bytes_in_word + bytes_in_word * n2w startptr)
             (nfree + bytes_in_word * n2w (LENGTH ws1 + 1)) m1
               (wordSem_state_mdomain s1) =
             SOME m2 /\
           (misc_word_list nfree (CONS (word_Word full_header) (APPEND ws1
             ws2)) * SEP_T)
             (fun2set (m2,wordSem_state_mdomain s1)) /\
           LENGTH ws2 = len /\
           memory_rel c (wordSem_state_be s1) ts (dataSem_state_refs x) sp
             (wordSem_state_store s1) m2 (wordSem_state_mdomain s1)
             (APPEND (ZIP (APPEND ys7 (TAKE len (DROP startptr l')))
               (APPEND ws1 ws2)) vars))`,
  CHEAT_TAC);;

(* cut_envs_adjust_sets_insert_ODD *)
let data_to_word_assignProof_cut_envs_adjust_sets_insert_ODD = prove
 (`ODD n ==>
   cut_envs (adjust_sets names) (sptree_insert n w t) =
   cut_envs (adjust_sets names) t`,
  CHEAT_TAC);;

let IN_domain_adjust_set_IMP = prove
 (`x IN sptree_domain (adjust_set the_names) ==>
   (?xa. x = adjust_var xa /\ xa IN sptree_domain the_names)`,
  CHEAT_TAC);;

let assign_ConsExtend = prove
 (`(?tag. op = clos_BlockOp (clos_ConsExtend tag)) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

let assign_Cons = prove
 (`(?tag. op = clos_BlockOp (clos_Cons tag)) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
     (t:('a,'c,'ffi)wordSem_state) NONE locs /\
   (~(op_requires_names op = (names_opt = NONE))) /\
   dataSem_cut_state_opt names_opt s = SOME x /\
   dataSem_get_vars args (dataSem_state_locals s) = SOME vals
     /\ wordSem_state_termdep
   t > 1 /\
   dataSem_do_app op vals x = Rval (v,s2) ==>
   (?q (r:('a,'c,'ffi)wordSem_state).
     wordSem_evaluate (FST (data_to_word_assign c n l dest op args
       names_opt),t) = (q,r) /\
     (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
      r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
        (dataSem_state_stack_max s2) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
        ~(dataSem_state_safe_for_space s2))) /\
     (~(q = SOME wordSem_NotEnoughSpace) ==>
      data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
        NONE locs /\
      q = NONE)))`,
  CHEAT_TAC);;

let assign_FFI = prove
 (`(?n. op = clos_FFI n) ==> (data_to_word_gcProof_state_rel c l1 l2
  (s:('c,'ffi)dataSem_state)
     (t:('a,'c,'ffi)wordSem_state) NONE locs /\
   (~(op_requires_names op = (names_opt = NONE))) /\
   dataSem_cut_state_opt names_opt s = SOME x /\
   dataSem_get_vars args (dataSem_state_locals s) = SOME vals
     /\ wordSem_state_termdep
   t > 1 /\
   dataSem_do_app op vals x = Rval (v,s2) ==>
   (?q (r:('a,'c,'ffi)wordSem_state).
     wordSem_evaluate (FST (data_to_word_assign c n l dest op args
       names_opt),t) = (q,r) /\
     (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
      r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
        (dataSem_state_stack_max s2) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
        ~(dataSem_state_safe_for_space s2))) /\
     (~(q = SOME wordSem_NotEnoughSpace) ==>
      data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
        NONE locs /\
      q = NONE)))`,
  CHEAT_TAC);;

let assign_FFI_final = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE
  locs /\
   (~(op_requires_names (clos_FFI i) = (names_opt = NONE))) /\
   dataSem_cut_state_opt names_opt s = SOME x /\
   dataSem_get_vars args (dataSem_state_locals s) = SOME vals
     /\ wordSem_state_termdep
   t > 1 /\
   dataSem_do_app (clos_FFI i) vals x = Rerr (Rabort (Rffi_error f)) ==>
   (?q r.
     wordSem_evaluate (FST (data_to_word_assign c n l dest (clos_FFI i) args
       names_opt),t) = (q,r) /\
     option_le (wordSem_state_stack_max r) (dataSem_state_stack_max s)
       /\ ~(q = SOME wordSem_NotEnoughSpace) /\ wordSem_state_ffi r =
       wordSem_state_ffi t /\ q = SOME (wordSem_FinalFFI f))`,
  CHEAT_TAC);;

let getWords_acc = prove
 (`!ws acc.
     getWords ws acc =
       let (cs,c) = getWords ws [] in (APPEND (REVERSE acc) cs,c)`,
  CHEAT_TAC);;

let getWords_thm = prove
 (`!ws cs rest.
     getWords ws [] = (cs,rest) ==>
     ws = APPEND (MAP (\(b,c). (b,word_Word c)) cs) rest`,
  CHEAT_TAC);;

let store_list_word_cond_add_IMP = prove
 (`!y2 m a m1 free'.
     data_to_word_memoryProof_store_list free' (MAP (word_cond_add c (a:'a
       word))
       (MAP (\(b,c). (b,word_Word c)) y2)) m dm = SOME m1 ==>
     const_addresses free' y2 dm /\
     const_writes free' (a << (shift_length c - backend_common_word_shift
       (:'a))) y2 m = m1`,
  CHEAT_TAC);;

let evaluate_StoreAnyConsts = prove
 (`!r1 r2 r3 vs w (s:('a,'c,'ffi)wordSem_state) free' m dm m1.
     data_to_word_memoryProof_store_list free' (MAP (word_cond_add c (a:'a
       word)) vs) m dm = SOME m1 /\
     m = wordSem_state_memory s /\ dm = wordSem_state_mdomain s
       /\ ALL_DISTINCT [r1; r2; r3] /\
     ALL (good_loc (sptree_domain (wordSem_state_code s)) o SND) (CONS w vs)
       /\
     sptree_lookup r2 (wordSem_state_locals s) = SOME (word_Word free') /\
     sptree_lookup r3 (wordSem_state_locals s) = SOME (word_Word (a <<
       (shift_length c - backend_common_word_shift (:'a)))) ==>
     (?ll.
       wordSem_evaluate (StoreAnyConsts r1 r2 r3 vs w,s) =
         (NONE,wordSem_state_store_fupd (K (wordSem_state_store s |+
           (NextFree,word_Word
                            (free' + bytes_in_word * n2w (LENGTH vs)))))
                              (wordSem_state_locals_fupd (K ll)
                              (wordSem_state_memory_fupd (K m1) s))) /\
       sptree_lookup r1 ll = SOME (word_cond_add c a w) /\
       (!n. ~(MEM n [r1; r2; r3]) ==> sptree_lookup n ll = sptree_lookup n
         (wordSem_state_locals s)))`,
  CHEAT_TAC);;

let do_build_const_IMP_SOME = prove
 (`dataSem_do_build_const parts x (SOME ts) = (v,vs,ts1) ==>
   (?ts2. ts1 = SOME ts2)`,
  CHEAT_TAC);;

(* [local] *)
let TWO_POW_LEMMA = prove
 (`(2 EXP n <= 3 ==> n < 2) /\
   (2 EXP n <= 2 ==> n < 2) /\
   (2 EXP n <= 1 ==> n < 1)`,
  CHEAT_TAC);;

let bignum_size = prove
 (`good_dimindex (:'a) ==>
   bignum_size (dimindex (:'a) = 64) i = LENGTH (n2mw (num_of_int (abs
     i)):('a word) list) + 1`,
  CHEAT_TAC);;

let _ = do_list hide_constant ["free"];;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let parts_to_words_NONE = prove
 (cake_as_vars (fun () ->
    `!parts' (off:'a word) m aa (t:('a,'c,'ffi)wordSem_state)
  (s:('c,'ffi)dataSem_state).
       parts_to_words c m aa parts' off = NONE /\ good_dimindex (:'a) /\
       heap_in_memory_store heap a sp sp1 gens c (wordSem_state_store t)
         (wordSem_state_memory t) (wordSem_state_mdomain t) limit ==>
       limits_inv (dataSem_state_limits s) (FLOOKUP (wordSem_state_store
         t) HeapLength) (wordSem_state_stack_limit t)
         (data_to_word_config_len_size
                  c) (data_to_word_config_has_fp_ops c)
                    (data_to_word_config_has_fp_tern c) ==>
       EX ((~) o lim_safe_part (dataSem_state_limits s)) parts'`),
  CHEAT_TAC);;

let assign_Build = prove
 (`(?parts'. op = clos_BlockOp (clos_Build parts')) ==>
  (data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
     (t:('a,'c,'ffi)wordSem_state) NONE locs /\
   (~(op_requires_names op = (names_opt = NONE))) /\
   dataSem_cut_state_opt names_opt s = SOME x /\
   dataSem_get_vars args (dataSem_state_locals s) = SOME vals
     /\ wordSem_state_termdep
   t > 1 /\
   dataSem_do_app op vals x = Rval (v,s2) ==>
   (?q (r:('a,'c,'ffi)wordSem_state).
     wordSem_evaluate (FST (data_to_word_assign c n l dest op args
       names_opt),t) = (q,r) /\
     (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
      r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
        (dataSem_state_stack_max s2) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
        ~(dataSem_state_safe_for_space s2))) /\
     (~(q = SOME wordSem_NotEnoughSpace) ==>
      data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
        NONE locs /\
      q = NONE)))`,
  CHEAT_TAC);;


(* HOL4 data_to_word_assignProofScript.sml:16926: ML code, not ported *)

(* [local] *)
let join_lemma = prove
 (`(b1 ==> x) /\ (b2 ==> x) ==> (b1 \/ b2 ==> x)`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:16931-16933: a theorem that HOL4
   states as the value of an ML expression: imp_assign *)

let assign_thm = prove
 (`(
    data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
      (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    (~(op_requires_names op = (names_opt = NONE))) /\
    dataSem_cut_state_opt names_opt s = SOME x /\
    dataSem_get_vars args (dataSem_state_locals s) = SOME vals
      /\ wordSem_state_termdep
    t > 1 /\
    dataSem_do_app op vals x = Rval (v,s2) ==>
    (?q (r:('a,'c,'ffi)wordSem_state).
      wordSem_evaluate (FST (data_to_word_assign c n l dest op args
        names_opt),t) = (q,r) /\
      (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
       r = wordSem_state_ffi t /\ option_le (wordSem_state_stack_max r)
         (dataSem_state_stack_max s2) /\
       (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~(dataSem_state_safe_for_space s2))) /\
      (~(q = SOME wordSem_NotEnoughSpace) ==>
       data_to_word_gcProof_state_rel c l1 l2 (dataSem_set_var dest v s2) r
         NONE locs /\
       q = NONE)))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["ABS";
   "Num";
   "free";
   "parts";
   "test"];;

(* and the interface *)
let _ = unhide_overloads ();;
