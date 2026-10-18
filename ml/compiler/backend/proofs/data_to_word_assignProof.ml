(* ======================================================== *)
(*  data_to_word_assignProof: ported from HOL4's
    compiler/backend/proofs/data_to_word_assignProofScript.sml
    A proof theory, with 5 definitions and 319 theorems.  Needed by
    data_to_wordProof.ml.  *)
(* ======================================================== *)

(*
  Part of the correctness proof for data_to_word
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi_to_data.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_live.ml";;
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
needs "lib/comparison.ml";;
needs "lib/integer_word.ml";;
needs "lib/multiword.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/semanticPrimitives.ml";;

cake_hide ["code_buffer"; "data_buffer"; "memory"; "parts"; "vars"];;
(* HOL4 ancestors outside the port: (* for word_add_carry *)
   int_bitwise While *)

(* HOL4 data_to_word_assignProofScript.sml:28-29: ML code, not ported *)

(* HOL4 data_to_word_assignProofScript.sml:38: the overload lookup,
   which the port expands *)

(* HOL4 data_to_word_assignProofScript.sml:40-42: ML code, not ported *)

(* HOL4 data_to_word_assignProofScript.sml:44-45: a proof *)

(* HOL4 data_to_word_assignProofScript.sml:47-48: ML code, not ported *)

(* HOL4 data_to_word_assignProofScript.sml:50-53: ML code, not ported *)

(* HOL4 data_to_word_assignProofScript.sml:55-60: a proof *)

(* This list must list all auxiliary definitions used in assign_def *)
(* HOL4 data_to_word_assignProofScript.sml:63-72: a theorem that HOL4
   states as the value of an ML expression: assign_def_extras *)

let get_vars_SING = cake_theorem "get_vars_SING"
  (fun () ->
    `dataSem_get_vars args s = SOME [w] ==> (?y. args = [y])`)
  CHEAT_TAC;;

let state_rel_IMP_tstamps = cake_theorem "state_rel_IMP_tstamps"
  (fun () ->
    `state_rel c l1 l2 x t p locs ==>
     (?next_stamp. dataSem_state_tstamps x = SOME next_stamp)`)
  CHEAT_TAC;;

let INT_EQ_NUM_LEMMA = cake_theorem "INT_EQ_NUM_LEMMA"
  (fun () ->
    `0 <= (i:int) <=> (?index. i = &index)`)
  CHEAT_TAC;;

let push_if = cake_theorem "push_if[local]"
  (fun () ->
    `(!f x y b. (if b then f x else f y) = f (if b then x else y)) /\
     (!f h x b. (if b then f x else h x) = (if b then f else h)
       x)`)
  CHEAT_TAC;;

let split_if = cake_theorem "split_if[local]"
  (fun () ->
    `(if b then f x else h y) = (if b then f else h) (if b then x else
  y)`)
  CHEAT_TAC;;

let cut_env_IMP_domain = cake_theorem "cut_env_IMP_domain"
  (fun () ->
    `cut_names x y = SOME t ==> domain t = domain x`)
  CHEAT_TAC;;

let cut_envs_wf = cake_theorem "cut_envs_wf"
  (fun () ->
    `cut_envs kept_names t = SOME (y1,y2) ==> sptree_wf y1 /\
  sptree_wf y2`)
  CHEAT_TAC;;

let domain_list_insert_thm = cake_theorem "domain_list_insert_thm"
  (fun () ->
    `!l names.
       domain (list_insert l names) = set_of_list l UNION domain
         names`)
  CHEAT_TAC;;

let cut_env_lookup = cake_theorem "cut_env_lookup"
  (fun () ->
    `wordSem_cut_env names t = SOME y /\
     sptree_lookup n y = SOME a ==>
     sptree_lookup n t = SOME a`)
  CHEAT_TAC;;

let cut_env_get_vars_get_vars = cake_theorem "cut_env_get_vars_get_vars"
  (fun () ->
    `!vs ws ws'.
       cut_env kept_names (state_locals t) = SOME y /\
       get_vars vs (state_locals_fupd (K y) t) = SOME ws /\
       get_vars vs t = SOME ws' ==>
       ws = ws'`)
  CHEAT_TAC;;

let memory_rel_lookup_var_IMP = cake_theorem "memory_rel_lookup_var_IMP"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
       (join_env ll
          (toAList (inter (state_locals t) (adjust_set ll))) ++
            envs) /\
      get_vars n ll = SOME x /\
      get_vars (MAP adjust_var n) (t:('a,'c,'ffi)wordSem_state) =
        SOME w ==>
      memory_rel c be ts refs sp st m dm
        (ZIP x w ++
         join_env ll
           (toAList (inter (state_locals t) (adjust_set ll))) ++
             envs)`)
  CHEAT_TAC;;

let get_real_offset_lemma = cake_theorem "get_real_offset_lemma"
  (fun () ->
    `get_var v t = SOME (wordLang_Word i_w) /\
      good_dimindex (:'a) /\
      get_real_offset i_w = SOME y ==>
      wordSem_word_exp t (real_offset c v) = SOME (wordLang_Word
        (y:'a word))`)
  CHEAT_TAC;;

let state_rel_push_env_loc = cake_theorem "state_rel_push_env_loc"
  (fun () ->
    `state_rel c n l s (call_env args b (push_env (y1,y2) NONE t)) ys
  ((l1,l2) :: locs) ==>
     sptree_lookup 0 y1 = SOME (Loc l1 l2)`)
  CHEAT_TAC;;

let evaluate_IMP_domain_union = cake_theorem "evaluate_IMP_domain_union"
  (fun () ->
    `evaluate (p,wordSem_state_termdep_fupd (K tp) (state_clock_fupd (K
  ck) (call_env args b (push_env (y1,y2) NONE
  (t:('a,'c,'ffi)wordSem_state))))) = (SOME (wordSem_Result ret1
  ret2),t1) /\
     pop_env t1 = SOME t2 /\
     sptree_lookup 0 y1 = SOME (Loc l1 l2) /\
     cut_envs (adjust_sets kept_names) (state_locals t) = SOME
       (y1,y2) ==>
     domain (state_locals t2) = domain y1 UNION domain y2 /\
     sptree_lookup 0 (state_locals t2) = SOME (Loc l1 l2)`)
  CHEAT_TAC;;

let get_real_byte_offset_lemma =
  cake_theorem "get_real_byte_offset_lemma"
  (fun () ->
    `get_var v t = SOME (wordLang_Word (w:'a word)) /\ good_dimindex
  (:'a) ==>
     wordSem_word_exp t (real_byte_offset v) = SOME
       (wordLang_Word (bytes_in_word + (w >>> 2)))`)
  CHEAT_TAC;;

let reorder_lemma = cake_theorem "reorder_lemma"
  (fun () ->
    `memory_rel c be ts (state_refs x) (dataSem_state_space x)
  (wordSem_state_store t) (wordSem_state_memory t)
  (wordSem_state_mdomain t) (x1 :: x2 :: x3 :: xs) ==>
     memory_rel c be ts (state_refs x) (dataSem_state_space x)
       (wordSem_state_store t) (wordSem_state_memory t)
       (wordSem_state_mdomain t) (x3 :: x1 :: x2 :: xs)`)
  CHEAT_TAC;;

let reorder_2_lemma = cake_theorem "reorder_2_lemma"
  (fun () ->
    `memory_rel c be ts (state_refs x) (dataSem_state_space x)
  (wordSem_state_store t) (wordSem_state_memory t)
  (wordSem_state_mdomain t) (x1 :: x2 :: xs) ==>
     memory_rel c be ts (state_refs x) (dataSem_state_space x)
       (wordSem_state_store t) (wordSem_state_memory t)
       (wordSem_state_mdomain t) (x2 :: x1 :: xs)`)
  CHEAT_TAC;;

(* HOL4 data_to_word_assignProofScript.sml:263-289: a theorem that
   HOL4 states as the value of an ML expression: evaluate_StoreEach *)

let get_vars_adjust_var = cake_theorem "get_vars_adjust_var"
  (fun () ->
    `ODD k ==>
      get_vars (MAP adjust_var args) (state_locals_fupd (K (insert
        k w s)) t) =
      get_vars (MAP adjust_var args) (state_locals_fupd (K s) t)`)
  CHEAT_TAC;;

let get_vars_with_store = cake_theorem "get_vars_with_store"
  (fun () ->
    `!args. get_vars args (wordSem_state_store_fupd (K s)
  (state_locals_fupd (K (state_locals t)) t)) =
             get_vars args t`)
  CHEAT_TAC;;

let word_less_lemma1 = cake_theorem "word_less_lemma1"
  (fun () ->
    `v2 < (v1:'a word) <=> ~(v1 <= v2)`)
  CHEAT_TAC;;

let get_vars_2_imp = cake_theorem "get_vars_2_imp"
  (fun () ->
    `wordSem_get_vars [x1; x2] s = SOME [y1; y2] ==>
      wordSem_get_var x1 s = SOME y1 /\
      wordSem_get_var x2 s = SOME y2`)
  CHEAT_TAC;;

let get_vars_1_imp = cake_theorem "get_vars_1_imp"
  (fun () ->
    `wordSem_get_vars [x1] s = SOME [y1] ==>
      wordSem_get_var x1 s = SOME y1`)
  CHEAT_TAC;;

let data_to_word_assignProof_LESS_DIV_16_IMP =
  cake_theorem "LESS_DIV_16_IMP"
  (fun () ->
    `n < k DIV 16 ==> 16 * n + 2 < (k:num)`)
  CHEAT_TAC;;

let lookup_loc_lemma = cake_theorem "lookup_loc_lemma"
  (fun () ->
    `env_to_list y2 permute = (l',permute') /\
     cut_envs (adjust_sets keep_names) locals = SOME (y1,y2) /\
     sptree_lookup 0 (union y2 y1) = SOME (Loc l1 l2) ==>
     ALOOKUP l' 0 = NONE /\ sptree_lookup 0 y1 = SOME (Loc l1 l2)`)
  CHEAT_TAC;;

let word_exp_real_addr = cake_theorem "word_exp_real_addr"
  (fun () ->
    `get_real_addr c (wordSem_state_store t) ptr_w = SOME a /\
      shift_length c < dimindex (:'a) /\ good_dimindex (:'a) /\
      sptree_lookup (adjust_var a1) (state_locals
        (t:('a,'c,'ffi)wordSem_state)) = SOME (wordLang_Word ptr_w) ==>
      (!w. wordSem_word_exp (state_locals_fupd (K (insert 1
        (wordLang_Word (w:'a word)) (state_locals t))) t)
            (real_addr c (adjust_var a1)) = SOME (wordLang_Word
              a))`)
  CHEAT_TAC;;

let word_exp_real_addr_2 = cake_theorem "word_exp_real_addr_2"
  (fun () ->
    `get_real_addr c (wordSem_state_store (t:('a,'c,'ffi)wordSem_state))
  ptr_w = SOME a /\
      shift_length c < dimindex (:'a) /\ good_dimindex (:'a) /\
      sptree_lookup (adjust_var a1) (state_locals t) = SOME
        (wordLang_Word ptr_w) ==>
      (!w1 w2.
        wordSem_word_exp
          (state_locals_fupd (K (insert 3 (wordLang_Word (w1:'a
            word)) (insert 1 (wordLang_Word w2) (state_locals t)))) t)
          (real_addr c (adjust_var a1)) = SOME (wordLang_Word a))`)
  CHEAT_TAC;;

let encode_header_IMP_BIT0 = cake_theorem "encode_header_IMP_BIT0"
  (fun () ->
    `encode_header c tag l = SOME w ==> FAPPLY w 0`)
  CHEAT_TAC;;

let get_addr_inj = cake_theorem "get_addr_inj"
  (fun () ->
    `p1 * 2 EXP shift_length c < dimword (:'a) /\
     p2 * 2 EXP shift_length c < dimword (:'a) /\
     get_addr c p1 (wordLang_Word ((n2w 0):'a word)) = get_addr c
       p2 (wordLang_Word (n2w 0)) ==> p1 = p2`)
  CHEAT_TAC;;

let Word64Rep_inj = cake_theorem "Word64Rep_inj"
  (fun () ->
    `good_dimindex (:'a) ==>
     (Word64Rep (:'a) w1 = Word64Rep (:'a) w2 <=> w1 = w2)`)
  CHEAT_TAC;;

let IMP_read_bytearray_GENLIST =
  cake_theorem "IMP_read_bytearray_GENLIST"
  (fun () ->
    `!ls len a.
     len = LENGTH ls /\
     (!i. i < len ==> g (a + n2w i) = SOME (EL i ls)) ==>
       read_bytearray a len g = SOME ls`)
  CHEAT_TAC;;

let lookup_IMP_insert_EQ = cake_theorem "lookup_IMP_insert_EQ"
  (fun () ->
    `!t x y. sptree_lookup x t = SOME y ==> insert x y t = t`)
  CHEAT_TAC;;

let data_to_word_assignProof_set_vars_sing =
  cake_theorem "set_vars_sing"
  (fun () ->
    `set_vars [n] [w] t = set_var n w t`)
  CHEAT_TAC;;

let NONNEG_INT = cake_theorem "NONNEG_INT"
  (fun () ->
    `0 <= (i:int) ==> (?j. i = &j)`)
  CHEAT_TAC;;

let BIT_X_1 = cake_theorem "BIT_X_1"
  (fun () ->
    `BIT i 1 = (i = 0)`)
  CHEAT_TAC;;

let minus_2_word_and_id = cake_theorem "minus_2_word_and_id"
  (fun () ->
    `~(FAPPLY w 0) ==> (--(n2w 2) && w) = w`)
  CHEAT_TAC;;

let FOUR_MUL_LSL = cake_theorem "FOUR_MUL_LSL"
  (fun () ->
    `n2w (4 * i) << k = n2w i << (k + 2)`)
  CHEAT_TAC;;

let evaluate_BignumHalt = cake_theorem "evaluate_BignumHalt"
  (fun () ->
    `state_rel c l1 l2 s t NONE locs /\
      get_var reg t = SOME (wordLang_Word w) ==>
      (?r. (evaluate (BignumHalt reg,t) =
            (if FAPPLY w 0 then (SOME wordSem_NotEnoughSpace,r)
              else (NONE,t))) /\ state_ffi r = state_ffi s /\
              state_ffi t = state_ffi s)`)
  CHEAT_TAC;;

(* TODO: should probably replace evaluate_GiveUp directly *)
let evaluate_GiveUp2 = cake_theorem "evaluate_GiveUp2"
  (fun () ->
    `state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs ==>
     (?r. evaluate (GiveUp,t) = (SOME wordSem_NotEnoughSpace,r) /\
       state_ffi
       r = state_ffi s /\ state_ffi t = state_ffi s /\
       option_le (state_stack_max r) (state_stack_max t))`)
  CHEAT_TAC;;

let evaluate_BignumHalt2 = cake_theorem "evaluate_BignumHalt2"
  (fun () ->
    `state_rel c l1 l2 s t NONE locs /\
      get_var reg t = SOME (wordLang_Word w) ==>
      (?r. (evaluate (BignumHalt reg,t) =
            (if FAPPLY w 0 then (SOME wordSem_NotEnoughSpace,r)
              else (NONE,t))) /\ state_ffi r = state_ffi s /\ state_ffi
              t = state_ffi s /\
                             option_le (state_stack_max r)
                               (state_stack_max t))`)
  CHEAT_TAC;;

let state_rel_get_var_Number_IMP_alt =
  cake_theorem "state_rel_get_var_Number_IMP_alt"
  (fun () ->
    `!k i. state_rel c l1 l2 s t NONE locs /\
            get_var k (state_locals s) = SOME (Number i) /\
            get_var (2 * k + 2) t = SOME a1 ==>
            (?(w:'a word). a1 = wordLang_Word w /\ FAPPLY w 0 =
              ~(small_int (:'a) i))`)
  CHEAT_TAC;;

(* TODO: move to sptreeTheory *)
let EXISTS_NOT_IN_spt_DOMAIN =
  cake_theorem "EXISTS_NOT_IN_spt_DOMAIN[local]"
  (fun () ->
    `?x. ~(x IN domain (refs:'a spt))`)
  CHEAT_TAC;;

(* TODO: move to sptreeTheory *)
let LEAST_NOTIN_spt_DOMAIN = cake_theorem "LEAST_NOTIN_spt_DOMAIN"
  (fun () ->
    `!refs. ~((LEAST (\x. ~(x IN domain (refs:'a spt)))) IN domain
  refs)`)
  CHEAT_TAC;;

(*TODO: move to backendProps *)
let option_le_add_indv = cake_theorem "option_le_add_indv"
  (fun () ->
    `option_le (OPTION_MAP2 (+) n m) r ==> option_le n r /\ option_le
  m r`)
  CHEAT_TAC;;

let option_le_add_drop_right = cake_theorem "option_le_add_drop_right"
  (fun () ->
    `option_le x y ==>
     option_le x (OPTION_MAP2 (+) z y)`)
  CHEAT_TAC;;

let word_exp_SmallLsr = cake_theorem "word_exp_SmallLsr"
  (fun () ->
    `n < dimindex (:'a) ==>
      wordSem_word_exp s (SmallLsr e n) =
         (match wordSem_word_exp s e with SOME (wordLang_Word w)
           -> SOME (wordLang_Word ((w:'a word) >>> n)) | res -> (if n
           = 0 then res else NONE))`)
  CHEAT_TAC;;

let evaluate_MakeBytes = cake_theorem "evaluate_MakeBytes"
  (fun () ->
    `good_dimindex (:'a) ==>
      evaluate (MakeBytes n,s) =
        (match get_var n s with SOME (wordLang_Word w) ->
          (NONE,set_var n (wordLang_Word (word_of_byte ((w:'a word)
          >>> 2))) s) | _1 -> (SOME Error,s))`)
  CHEAT_TAC;;

let w2w_shift_shift = cake_theorem "w2w_shift_shift"
  (fun () ->
    `good_dimindex (:'a) ==> ((w2w (w:word8) << 2 >>> 2):'a word) =
  w2w w`)
  CHEAT_TAC;;

(* HOL4 data_to_word_assignProofScript.sml:629-631: a proof *)

let evaluate_WriteLastBytes = cake_theorem "evaluate_WriteLastBytes"
  (fun () ->
    `good_dimindex (:'a) /\ w2n n < dimindex (:'a) DIV 8 /\
     get_vars [av; bv; nv] (s:('a,'c,'ffi)wordSem_state) = SOME
       [wordLang_Word (a:'a word); wordLang_Word b; wordLang_Word n] /\
     byte_aligned a /\ a IN wordSem_state_mdomain s /\
       wordSem_state_memory s a = wordLang_Word w ==>
     evaluate (WriteLastBytes av bv nv,s) =
       (NONE,wordSem_state_memory_fupd (K ((a =+ wordLang_Word
         (last_bytes (w2n n) (w2w b) (n2w 0) w (be s)))
         (wordSem_state_memory s))) s)`)
  CHEAT_TAC;;

let data_to_word_assignProof_byte_aligned_bytes_in_word =
  cake_theorem "byte_aligned_bytes_in_word"
  (fun () ->
    `good_dimindex (:'a) ==>
      byte_aligned (w * bytes_in_word) /\
      byte_aligned (bytes_in_word * (w:'a word))`)
  CHEAT_TAC;;

let is_env_def = cake_define
  `is_env st = (?n vs. st = Env n vs)`;;

(* TODO: copypasta from costPropsScript *)
let size_of_Number_head = cake_theorem "size_of_Number_head"
  (fun () ->
    `!vs lims refs seen n b.
     small_num (limits_arch_64_bit lims) n ==>
     (size_of lims (Number n :: vs) refs seen = size_of lims vs
       refs seen)`)
  CHEAT_TAC;;

(* HOL4 data_to_word_assignProofScript.sml:707-710: a theorem that
   HOL4 states as the value of an ML expression: ADD4DIV4 *)

(* HOL4 data_to_word_assignProofScript.sml:712-715: a theorem that
   HOL4 states as the value of an ML expression: ADD8DIV8 *)

let RefByte_thm = cake_theorem "RefByte_thm"
  (fun () ->
    `state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      get_vars [0; 1; 2] (state_locals s) = SOME (vals ++ [Number
        (&(if fl then 0 else 4))]) /\ state_clock
      t = MustTerminate_limit (:'a) - 1 /\
      pop_env s = SOME s1 /\ is_env (HD (stack s)) /\
        state_locals_size
      s = sptree_lookup RefByte_location
        (dataSem_state_stack_frame_sizes s) /\
      do_app (closLang_MemOp (closLang_RefByte fl)) vals s1 = Rval
        (v,s2) ==>
      (?q r new_c.
        evaluate (RefByte_code c,t) = (q,r) /\
        (if q = SOME wordSem_NotEnoughSpace then state_ffi
          r = state_ffi t /\
          option_le (state_stack_max r) (state_stack_max s2) /\
          (~(data_to_word_config_gc_kind c = None) /\
            no_thunks_in_refs (state_refs s) ==>
           (match vals with
                (Number i :: _2) ->
                (i < (&0) \/
                ~(small_num (limits_arch_64_bit
                  (dataSem_state_limits s)) i) \/
                ~(num_of_int i DIV (arch_size (dataSem_state_limits
                  s) DIV 8) < dimword (:'a) DIV arch_size
                  (dataSem_state_limits s)) \/
                ~(num_of_int i DIV (arch_size (dataSem_state_limits
                  s) DIV 8) + 1 < (2 EXP data_to_word_config_len_size
                  c)) \/ limits_heap_limit (dataSem_state_limits
                s1) <
                size_of_heap s1 + num_of_int i DIV (arch_size
                  (dataSem_state_limits s) DIV 8) + 2))) else
          ?rv. q = SOME (wordSem_Result (wordLang_Loc l1 l2) [rv])
            /\
               state_rel c r1 r2 (stack_fupd (K (stack s))
                 (state_clock_fupd (K new_c) (state_locals_size_fupd (K
                 (SOME 0)) (state_locals_fupd (K LN) s2))))
                  r (SOME [(v,rv)]) locs))`)
  CHEAT_TAC;;

(* TODO: copypaste from costProps *)
let size_of_seen_SUBSET = cake_theorem "size_of_seen_SUBSET"
  (fun () ->
    `!lims vs refs seen n1 seen1 refs1.
     (size_of lims vs refs seen = (n1,refs1,seen1)) ==> domain
       seen SUBSET domain seen1`)
  CHEAT_TAC;;

let size_of_seen_Block = cake_theorem "size_of_seen_Block"
  (fun () ->
    `!lims vs refs seen n1 refs1 seen1 ts tag l.
      size_of lims vs refs seen = (n1,refs1,seen1) ==>
      (MEM (Block ts tag l) vs /\ ~(l = []) ==>
       sptree_lookup ts seen1 = SOME one)`)
  CHEAT_TAC;;

let size_of_cons_seen_Block = cake_theorem "size_of_cons_seen_Block"
  (fun () ->
    `!lims vs refs seen ts tag l.
      MEM (Block ts tag l) vs ==>
      size_of lims (Block ts tag l :: vs) refs seen = size_of
        lims vs refs seen`)
  CHEAT_TAC;;

let state_rel_IMP_test_zero = cake_theorem "state_rel_IMP_test_zero"
  (fun () ->
    `state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) vs locs /\
      get_var i (state_locals s) = SOME (Number n) ==>
      (?w. get_var (adjust_var i) t = SOME (wordLang_Word w) /\
        (w = (n2w 0) <=> (n = 0)))`)
  CHEAT_TAC;;

let state_rel_get_var_Number_IMP =
  cake_theorem "state_rel_get_var_Number_IMP"
  (fun () ->
    `state_rel c l1 l2 s t vs locs /\
      get_var i (state_locals s) = SOME (Number (&n)) /\ small_int
        (:'a) (&n) ==>
      (?w. get_var (adjust_var i) t = SOME (wordLang_Word
        (Smallnum (&n):'a word)))`)
  CHEAT_TAC;;

let EXP_LEMMA1 = cake_theorem "EXP_LEMMA1"
  (fun () ->
    `4 * n * (2 EXP k) = n * 2 EXP (k + 2)`)
  CHEAT_TAC;;

let evaluate_Maxout_bits_code = cake_theorem "evaluate_Maxout_bits_code"
  (fun () ->
    `~(n_reg = dest) /\ n < dimword (:'a) /\ rep_len < dimindex (:'a) /\
         k < dimindex (:'a) /\
         sptree_lookup n_reg (state_locals
           (t:('a,'c,'ffi)wordSem_state)) = SOME (wordLang_Word (n2w
           n:'a word)) ==>
         evaluate (Maxout_bits_code rep_len k dest n_reg,set_var
           dest (wordLang_Word w) t) =
           (NONE,set_var dest (wordLang_Word (w || maxout_bits n
             rep_len k)) t)`)
  CHEAT_TAC;;

let make_ptr_bits_thm = cake_theorem "Make_ptr_bits_thm"
  (fun () ->
    `~(tag_reg = dest) /\ tag1 < dimword (:'a) /\
  data_to_word_config_tag_bits c < dimindex (:'a) /\ ~(len_reg = dest)
  /\ len1 < dimword (:'a) /\ data_to_word_config_len_bits c < dimindex
  (:'a) /\ data_to_word_config_len_bits
         c + 1 < dimindex (:'a) /\
         FLOOKUP (wordSem_state_store
           (t:('a,'c,'ffi)wordSem_state)) NextFree = SOME (wordLang_Word
           f) /\
         FLOOKUP (wordSem_state_store t) CurrHeap = SOME
           (wordLang_Word d) /\
         sptree_lookup tag_reg (state_locals t) = SOME
           (wordLang_Word (n2w tag1)) /\
         sptree_lookup len_reg (state_locals t) = SOME
           (wordLang_Word (n2w len1)) /\
         shift_length c < dimindex (:'a) +
           backend_common_word_shift (:'a) ==>
         (?t1.
           evaluate (Make_ptr_bits_code c tag_reg len_reg dest,t) =
             (NONE,set_var dest (make_cons_ptr c (f - d) tag1
               len1:'a word_loc) t))`)
  CHEAT_TAC;;

(* HOL4 data_to_word_assignProofScript.sml:1387-1391: ML code, not
   ported *)

let evaluate_LoadWord64 = cake_theorem "evaluate_LoadWord64"
  (fun () ->
    `memory_rel c be ts refs sp (wordSem_state_store t)
  (wordSem_state_memory t) (wordSem_state_mdomain t) ((Word64 w,v) ::
  vars) /\
     shift_length c < dimindex (:'a) /\ dimindex (:'a) = 64 /\
     get_var src (t:('a,'c,'ffi)wordSem_state) = SOME v ==>
     evaluate (LoadWord64 c dest src,t) = (NONE,set_var dest
       (wordLang_Word (w2w w)) t)`)
  CHEAT_TAC;;

let evaluate_WriteWord64 = cake_theorem "evaluate_WriteWord64"
  (fun () ->
    `memory_rel c be ts refs sp (wordSem_state_store t)
  (wordSem_state_memory t) (wordSem_state_mdomain t)
       (join_env_locals sl (state_locals t) ++ vars) /\
     get_var src (t:('a,'c,'ffi)wordSem_state) = SOME
       (wordLang_Word w) /\
     shift_length c < dimindex (:'a) /\ ~(src = 1) /\ 1 < sp /\
     dimindex (:'a) = 64 /\
     encode_header c 3 1 = SOME header /\
     (!n. IS_SOME (sptree_lookup n sl) ==> IS_SOME (sptree_lookup
       (adjust_var n) (state_locals t))) ==>
     (?nf m' locals' v.
       evaluate (WriteWord64 c header dest src,t) =
         (NONE,state_locals_fupd (K locals')
           (wordSem_state_memory_fupd (K m') (wordSem_state_store_fupd
           (K (wordSem_state_store t |+ (NextFree,nf))) t))) /\
       memory_rel c be ts refs (sp - 2) (wordSem_state_store t |+
         (NextFree,nf)) m' (wordSem_state_mdomain t)
         (join_env_locals (insert dest (Word64 (w2w w)) sl) locals'
           ++ vars) /\
       (!n. IS_SOME (sptree_lookup n sl) ==> IS_SOME (sptree_lookup
         (adjust_var n) locals')) /\
       IS_SOME (sptree_lookup (adjust_var dest) locals') /\
       sptree_lookup 0 locals' = sptree_lookup 0 (state_locals
         t))`)
  CHEAT_TAC;;

let evaluate_WriteWord64_on_32 =
  cake_theorem "evaluate_WriteWord64_on_32"
  (fun () ->
    `memory_rel c be ts refs sp (wordSem_state_store t)
  (wordSem_state_memory t) (wordSem_state_mdomain t)
       (join_env_locals sl (state_locals t) ++ vars) /\
     get_var src1 (t:('a,'c,'ffi)wordSem_state) = SOME
       (wordLang_Word ((31 >< 0) w)) /\
     get_var src2 (t:('a,'c,'ffi)wordSem_state) = SOME
       (wordLang_Word ((63 >< 32) w)) /\
     shift_length c < dimindex (:'a) /\ ~(src1 = 1) /\ ~(src2 = 1)
       /\ 2 < sp /\
     dimindex (:'a) = 32 /\
     encode_header c 3 2 = SOME header /\
     (!n. IS_SOME (sptree_lookup n sl) ==> IS_SOME (sptree_lookup
       (adjust_var n) (state_locals t))) ==>
     (?nf m' locals' v.
       evaluate (WriteWord64_on_32 c header dest src1 src2,t) =
         (NONE,state_locals_fupd (K locals')
           (wordSem_state_memory_fupd (K m') (wordSem_state_store_fupd
           (K (wordSem_state_store t |+ (NextFree,nf))) t))) /\
       memory_rel c be ts refs (sp - 3) (wordSem_state_store t |+
         (NextFree,nf)) m' (wordSem_state_mdomain t)
         (join_env_locals (insert dest (Word64 w) sl) locals' ++
           vars) /\
       (!n. IS_SOME (sptree_lookup n sl) ==> IS_SOME (sptree_lookup
         (adjust_var n) locals')) /\
       IS_SOME (sptree_lookup (adjust_var dest) locals') /\
       sptree_lookup 0 locals' = sptree_lookup 0 (state_locals
         t))`)
  CHEAT_TAC;;

let Num_ABS_AND = cake_theorem "Num_ABS_AND[local]"
  (fun () ->
    `num_of_int (abs (&n)) = n /\ num_of_int (abs (--(&n))) = n`)
  CHEAT_TAC;;

let evaluate_WriteWord64_on_32_num =
  cake_theorem "evaluate_WriteWord64_on_32_num"
  (fun () ->
    `memory_rel c be ts refs sp (wordSem_state_store t)
  (wordSem_state_memory t) (wordSem_state_mdomain t)
       (join_env_locals sl (state_locals t) ++ vars) /\
     get_var src1 (t:('a,'c,'ffi)wordSem_state) = SOME
       (wordLang_Word w1) /\
     get_var src2 (t:('a,'c,'ffi)wordSem_state) = SOME
       (wordLang_Word w2) /\
     shift_length c < dimindex (:'a) /\ ~(w2 = (n2w 0)) /\ ~(src1 =
       1) /\ ~(src2 = 1) /\ 2 < sp /\
     dimindex (:'a) = 32 /\
     encode_header c 3 2 = SOME header /\
     (!n. IS_SOME (sptree_lookup n sl) ==> IS_SOME (sptree_lookup
       (adjust_var n) (state_locals t))) ==>
     (?nf m' locals' v.
       evaluate (WriteWord64_on_32 c header dest src2 src1,t) =
         (NONE,state_locals_fupd (K locals')
           (wordSem_state_memory_fupd (K m') (wordSem_state_store_fupd
           (K (wordSem_state_store t |+ (NextFree,nf))) t))) /\
       memory_rel c be ts refs (sp - 3) (wordSem_state_store t |+
         (NextFree,nf)) m' (wordSem_state_mdomain t)
         (join_env_locals (insert dest (Number (&(w2n w2 * dimword
           (:'a) + w2n w1))) sl) locals' ++ vars) /\
       (!n. IS_SOME (sptree_lookup n sl) ==> IS_SOME (sptree_lookup
         (adjust_var n) locals')) /\
       IS_SOME (sptree_lookup (adjust_var dest) locals') /\
       sptree_lookup 0 locals' = sptree_lookup 0 (state_locals
         t))`)
  CHEAT_TAC;;

let evaluate_WriteWord32_bignum =
  cake_theorem "evaluate_WriteWord32_bignum"
  (fun () ->
    `memory_rel c be ts refs sp (wordSem_state_store t)
  (wordSem_state_memory t) (wordSem_state_mdomain t)
       (join_env_locals sl (state_locals t) ++ vars) /\
     get_var src (t:('a,'c,'ffi)wordSem_state) = SOME
       (wordLang_Word w) /\
     shift_length c < dimindex (:'a) /\ ~(src = 1) /\ 1 < sp /\
     dimindex (:'a) = 32 /\
     encode_header c 3 1 = SOME header /\
     ~(small_int (:'a) (&(w2n w))) /\
     (!n. IS_SOME (sptree_lookup n sl) ==> IS_SOME (sptree_lookup
       (adjust_var n) (state_locals t))) ==>
     (?nf m' locals' v.
       evaluate (WriteWord32_on_32 c header dest src,t) =
         (NONE,state_locals_fupd (K locals') (wordSem_state_memory_fupd
         (K m') (wordSem_state_store_fupd (K (wordSem_state_store t |+
         (NextFree,nf))) t))) /\
       memory_rel c be ts refs (sp - 2) (wordSem_state_store t |+
         (NextFree,nf)) m' (wordSem_state_mdomain t)
         (join_env_locals (insert dest (Number (&(w2n w))) sl)
           locals' ++ vars) /\
       (!n. IS_SOME (sptree_lookup n sl) ==> IS_SOME (sptree_lookup
         (adjust_var n) locals')) /\
       IS_SOME (sptree_lookup (adjust_var dest) locals') /\
       sptree_lookup 0 locals' = sptree_lookup 0 (state_locals
         t))`)
  CHEAT_TAC;;

let evaluate_WriteWord64_bignum =
  cake_theorem "evaluate_WriteWord64_bignum"
  (fun () ->
    `memory_rel c be ts refs sp (wordSem_state_store t)
  (wordSem_state_memory t) (wordSem_state_mdomain t)
       (join_env_locals sl (state_locals t) ++ vars) /\
     get_var src (t:('a,'c,'ffi)wordSem_state) = SOME
       (wordLang_Word w) /\
     shift_length c < dimindex (:'a) /\ ~(src = 1) /\ 1 < sp /\
     dimindex (:'a) = 64 /\
     encode_header c 3 1 = SOME header /\
     ~(small_int (:'a) (&(w2n w))) /\
     (!n. IS_SOME (sptree_lookup n sl) ==> IS_SOME (sptree_lookup
       (adjust_var n) (state_locals t))) ==>
     (?nf m' locals' v.
       evaluate (WriteWord64 c header dest src,t) =
         (NONE,state_locals_fupd (K locals') (wordSem_state_memory_fupd
         (K m') (wordSem_state_store_fupd (K (wordSem_state_store t |+
         (NextFree,nf))) t))) /\
       memory_rel c be ts refs (sp - 2) (wordSem_state_store t |+
         (NextFree,nf)) m' (wordSem_state_mdomain t)
         (join_env_locals (insert dest (Number (&(w2n w))) sl)
           locals' ++ vars) /\
       (!n. IS_SOME (sptree_lookup n sl) ==> IS_SOME (sptree_lookup
         (adjust_var n) locals')) /\
       IS_SOME (sptree_lookup (adjust_var dest) locals') /\
       sptree_lookup 0 locals' = sptree_lookup 0 (state_locals
         t))`)
  CHEAT_TAC;;

let evaluate_LoadBignum = cake_theorem "evaluate_LoadBignum"
  (fun () ->
    `memory_rel c be ts refs sp (wordSem_state_store t)
  (wordSem_state_memory t) (wordSem_state_mdomain t) ((Number i,v) ::
  vars) /\
     ~(small_int (:'a) i) /\ good_dimindex (:'a) /\ shift_length c
       < dimindex (:'a) /\
     get_var src (t:('a,'c,'ffi)wordSem_state) = SOME v /\ ~(header
       = w1) ==>
     (?h junk.
     evaluate (LoadBignum c header w1 src,t) =
       (NONE,set_vars [w1; header; w1]
                       [wordLang_Word (n2w (num_of_int (abs i)));
                         (wordLang_Word h); junk] t) /\
     (((n2w 16) && h) = (n2w 0) <=> (&0) <= i))`)
  CHEAT_TAC;;

(* HOL4 data_to_word_assignProofScript.sml:1765-1778: the ML values
   that the definitions below antiquote *)

(* HOL4 data_to_word_assignProofScript.sml:1780-1781: the ML values
   that the definitions below antiquote *)

let data_to_word_assignProof_cut_names_adjust_set_insert_1 =
  cake_theorem "cut_names_adjust_set_insert_1"
  (fun () ->
    `cut_names (adjust_set x) (insert 1 w l) =
      cut_names (adjust_set x) l`)
  CHEAT_TAC;;

let data_to_word_assignProof_cut_names_adjust_set_insert_3 =
  cake_theorem "cut_names_adjust_set_insert_3"
  (fun () ->
    `cut_names (adjust_set x) (insert 3 w l) =
      cut_names (adjust_set x) l`)
  CHEAT_TAC;;

let cut_names_adjust_set_insert_5 =
  cake_theorem "cut_names_adjust_set_insert_5"
  (fun () ->
    `cut_names (adjust_set x) (insert 5 w l) =
      cut_names (adjust_set x) l`)
  CHEAT_TAC;;

let word_bit_test_0 = cake_theorem "word_bit_test_0"
  (fun () ->
    `((n2w 1) && w) = (n2w 0) <=> ~(word_bit 0 w)`)
  CHEAT_TAC;;

let MAP_Number_11_w2n_word8 =
  cake_theorem "MAP_Number_11_w2n_word8[local]"
  (fun () ->
    `!ns ns'.
       MAP (Number o (&) o w2n) ns = MAP (Number o (&) o w2n) ns'
         <=>
       ns = (ns':word8 list)`)
  CHEAT_TAC;;

let MAP_Word64_11 = cake_theorem "MAP_Word64_11[local]"
  (fun () ->
    `!ns ns'.
       MAP (Word64) ns = MAP (Word64) ns' <=>
       ns = ns'`)
  CHEAT_TAC;;

let v_to_list_EQ_SOME_NIL = cake_theorem "v_to_list_EQ_SOME_NIL"
  (fun () ->
    `v_to_list hv1 = SOME [] <=> (?ts. hv1 = Block ts 0 [])`)
  CHEAT_TAC;;

let InstallCode_code_thm = cake_theorem "InstallCode_code_thm"
  (fun () ->
    `!(t:('a,'c,'ffi)wordSem_state) c hv1 v1 q1 a1 a2 ret_val bptr s1
  vars' sp refs ts.
        memory_rel c (be t) ts refs sp (wordSem_state_store t)
          (wordSem_state_memory t) (wordSem_state_mdomain t)
           ((hv1,a1) :: vars') /\
        sptree_lookup InstallCode_location (state_code t) = SOME
          (4,InstallCode_code c) /\
        sptree_lookup InstallData_location (state_code t) = SOME
          (4,InstallData_code c) /\
        FLOOKUP (wordSem_state_store t) BitmapBuffer = SOME bptr /\
        v_to_bytes hv1 = SOME q1 /\
        LENGTH q1 <= buffer_space_left (state_code_buffer t) /\
        LENGTH q1 < state_clock t /\
        get_var 0 t = SOME ret_val /\
        get_var 2 t = SOME a1 /\
        get_var 4 t = SOME a2 /\
        get_var 6 t = SOME (wordLang_Word (buffer_position
          (state_code_buffer t) +
                              n2w (LENGTH (buffer_buffer
                                (state_code_buffer t))))) /\
        good_dimindex (:'a) ==>
        (?lsz smx.
        evaluate (InstallCode_code c,t) =
        (match
          evaluate (InstallData_code c,state_stack_max_fupd (K smx)
            (state_code_buffer_fupd (K (buffer_space_left_fupd (K
            (buffer_space_left (state_code_buffer t) - LENGTH q1))
            (buffer_buffer_fupd (K (buffer_buffer (state_code_buffer t)
            ++ q1)) (state_code_buffer t)))) (state_clock_fupd (K
            (state_clock t - LENGTH q1 - 1)) (state_locals_size_fupd (K
            lsz) (state_locals_fupd (K (fromList2 [ret_val; bptr; a2;
             wordLang_Word (buffer_position (state_code_buffer t) +
                   n2w (LENGTH (buffer_buffer (state_code_buffer
                     t)) + LENGTH q1))])) t))))) with (res,s) -> (if
                     wordSem_bad_fun_return res then (SOME Error,s)
                     else (res,s))))`)
  CHEAT_TAC;;

let w2w_upper_def = cake_define
  `w2w_upper (w:word64) =
     (if dimindex (:'a) = 32 then ((63 >< 32) w):'a word else w2w
       w)`;;

let InstallData_code_thm = cake_theorem "InstallData_code_thm"
  (fun () ->
    `!(t:('a,'c,'ffi)wordSem_state) c hv2 v1 q2 a1 a2 ret_val s1 vars'
  sp refs ts.
        memory_rel c (be t) ts refs sp (wordSem_state_store t)
          (wordSem_state_memory t) (wordSem_state_mdomain t)
           ((hv2,a2) :: vars') /\
        sptree_lookup InstallData_location (state_code t) = SOME
          (4,InstallData_code c) /\
        sptree_lookup Install_location (state_code t) = SOME
          (3,Install_code c) /\
        v_to_words hv2 = SOME q2 /\
        LENGTH q2 <= buffer_space_left (wordSem_state_data_buffer
          t) /\
        LENGTH q2 < state_clock t /\
        get_var 0 t = SOME ret_val /\
        get_var 2 t = SOME (wordLang_Word (buffer_position
          (wordSem_state_data_buffer t) +
                              bytes_in_word *
                              n2w (LENGTH (buffer_buffer
                                (wordSem_state_data_buffer t))))) /\
        get_var 4 t = SOME a2 /\
        get_var 6 t = SOME a1 /\
        good_dimindex (:'a) ==>
        (?smx lsz.
        evaluate (InstallData_code c,t) =
        (match
          evaluate (Install_code c,state_stack_max_fupd (K smx)
            (state_locals_size_fupd (K lsz)
            (wordSem_state_data_buffer_fupd (K (buffer_space_left_fupd
            (K (buffer_space_left (wordSem_state_data_buffer t) - LENGTH
            q2)) (buffer_buffer_fupd (K (buffer_buffer
            (wordSem_state_data_buffer t) ++ MAP w2w_upper q2))
            (wordSem_state_data_buffer t)))) (state_clock_fupd (K
            (state_clock t - LENGTH q2 - 1)) (state_locals_fupd (K
            (fromList2 [ret_val;
                 wordLang_Word (buffer_position
                   (wordSem_state_data_buffer t) +
                       bytes_in_word * n2w (LENGTH (buffer_buffer
                         (wordSem_state_data_buffer t))) +
                       bytes_in_word * n2w (LENGTH q2)); a1]))
             t))))) with (res,s) -> (if wordSem_bad_fun_return
               res then (SOME Error,s) else (res,s))))`)
  CHEAT_TAC;;

let LENGTH_EQ_4 = cake_theorem "LENGTH_EQ_4"
  (fun () ->
    `(LENGTH xs = 4 <=> (?a1 a2 a3 a4. xs = [a1; a2; a3; a4])) /\
      (4 = LENGTH xs <=> (?a1 a2 a3 a4. xs = [a1; a2; a3; a4]))`)
  CHEAT_TAC;;

let w2w_upper_upper_w2w = cake_theorem "w2w_upper_upper_w2w"
  (fun () ->
    `!z1. good_dimindex (:'a) ==>
           MAP w2w_upper (MAP upper_w2w z1) = (z1:('a word) list)`)
  CHEAT_TAC;;

let MAP_FST_MAP_compile_part =
  cake_theorem "MAP_FST_MAP_compile_part[local]"
  (fun () ->
    `!full_list. MAP FST (MAP (compile_part c) full_list) = MAP FST
  full_list`)
  CHEAT_TAC;;

let memory_rel_ignore_buffers =
  cake_theorem "memory_rel_ignore_buffers[local]"
  (fun () ->
    `memory_rel c be ts refs sp (st |+ (BitmapBuffer,x)) m dm vars =
     memory_rel c be ts refs sp st m dm vars /\
     memory_rel c be ts refs sp (st |+ (CodeBuffer,x)) m dm vars =
     memory_rel c be ts refs sp st m dm vars`)
  CHEAT_TAC;;

let compile_part_loc_IMP = cake_theorem "compile_part_loc_IMP[local]"
  (fun () ->
    `compile_part c (a1,a2) = (n,x) ==> n = a1`)
  CHEAT_TAC;;

let consume_space_stack_max = cake_theorem "consume_space_stack_max"
  (fun () ->
    `consume_space a x = SOME s ==> state_stack_max x =
  state_stack_max s`)
  CHEAT_TAC;;

(* HOL4 data_to_word_assignProofScript.sml:2146-2147: ML code, not
   ported *)

let do_app_aux_safe_for_space_mono =
  cake_theorem "do_app_aux_safe_for_space_mono"
  (fun () ->
    `(dataSem_do_app_aux op xs s = Rval (r,s1)) /\
  dataSem_state_safe_for_space s1 ==> dataSem_state_safe_for_space s`)
  CHEAT_TAC;;

let do_app_safe_for_space_allowed_op =
  cake_theorem "do_app_safe_for_space_allowed_op"
  (fun () ->
    `do_app op xs s = Rval (r,s1) /\ dataSem_state_safe_for_space
     s1 ==>
     allowed_op op (LENGTH xs)`)
  CHEAT_TAC;;

let state_rel_cut_state_opt_SOME =
  cake_theorem "state_rel_cut_state_opt_SOME"
  (fun () ->
    `state_rel c l1 l2 s t NONE locs /\
     get_vars args (state_locals s) = SOME vals /\
     cut_state_opt (SOME kept_names) s = SOME x ==>
     (?y ws.
       cut_env (adjust_sets kept_names) (state_locals t) = SOME y
         /\
       get_vars (MAP adjust_var args) t = SOME ws /\
       LENGTH args = LENGTH vals /\ LENGTH args = LENGTH ws /\
       state_rel c l1 l2 x t NONE locs /\
       state_rel c l1 l2 x (state_locals_fupd (K y) t) NONE locs)`)
  CHEAT_TAC;;

let cut_state_opt_SOME_eq = cake_theorem "cut_state_opt_SOME_eq"
  (fun () ->
    `cut_state_opt (SOME names) s = SOME x ==>
     x = state_locals_fupd (K (mk_wf (inter (state_locals s)
       names))) s`)
  CHEAT_TAC;;

(* HOL4 data_to_word_assignProofScript.sml:2210-2212: ML code, not
   ported *)

let state_rel_cut_state_opt_set_var =
  cake_theorem "state_rel_cut_state_opt_set_var"
  (fun () ->
    `state_rel c l1 l2 (set_var dest v s2) r NONE locs /\
     cut_state_opt (SOME names) s2 = SOME s2_cut ==>
     state_rel c l1 l2 (set_var dest v s2_cut) r NONE locs`)
  CHEAT_TAC;;

(* cut_env is idempotent: cutting the same names twice gives the same result. *)
let cut_env_idempotent = cake_theorem "cut_env_idempotent"
  (fun () ->
    `dataSem_cut_env ns s_locals = SOME env ==>
     dataSem_cut_env ns env = SOME env`)
  CHEAT_TAC;;

(* Two-stage cut: narrowing an args-augmented cut (list_insert args ns) down to
   ns gives the same env as cutting ns directly. *)
let cut_env_cut_env_list_insert =
  cake_theorem "cut_env_cut_env_list_insert"
  (fun () ->
    `dataSem_cut_env (list_insert vs ns) env = SOME env_wide /\
     dataSem_cut_env ns env = SOME env_narrow ==>
     dataSem_cut_env ns env_wide = SOME env_narrow`)
  CHEAT_TAC;;

(* A join_env pair-list over (l1,l2) is contained in the one over any
   lookup-supermaps (l1',l2') — moves memory_rel pairs between a cut env
   and the full env (with memory_rel_rearrange). *)
let join_env_submap_MEM = cake_theorem "join_env_submap_MEM"
  (fun () ->
    `(!k v. sptree_lookup k l1 = SOME v ==> sptree_lookup k l1' = SOME
  v) /\
     (!k v. sptree_lookup k l2 = SOME v ==> sptree_lookup k l2' =
       SOME v) /\
     MEM p (join_env l1 (toAList (inter l2 (adjust_set l1)))) ==>
     MEM p (join_env l1' (toAList (inter l2' (adjust_set l1'))))`)
  CHEAT_TAC;;

(* The three heap-store FLOOKUPs follow directly from state_rel.
   Reusable in any op that needs to inspect t.store.{NextFree,CurrHeap,HeapLength}. *)
let state_rel_FLOOKUP_heap = cake_theorem "state_rel_FLOOKUP_heap"
  (fun () ->
    `state_rel c l1 l2 s t NONE locs ==>
     (?nf cu hl.
       FLOOKUP (wordSem_state_store t) NextFree = SOME
         (wordLang_Word nf) /\
       FLOOKUP (wordSem_state_store t) CurrHeap = SOME
         (wordLang_Word cu) /\
       FLOOKUP (wordSem_state_store t) HeapLength = SOME
         (wordLang_Word hl))`)
  CHEAT_TAC;;

(* Evaluating a SilentFFI block (the c.call_empty_ffi=T form emitted by
   op_requires_names ops, with var slot 3): if the word state's locals can be
   cut by the same names, the FFI call has empty payload and reduces to a
   locals-updated state. Reusable in any op whose generated code begins or
   resumes with `SilentFFI c 3 (adjust_sets <names>)`. *)
let evaluate_SilentFFI_3 = cake_theorem "evaluate_SilentFFI_3"
  (fun () ->
    `data_to_word_config_call_empty_ffi
       c /\
       state_rel c l1 l2 s t NONE locs /\
       wordSem_cut_env (adjust_sets ns) (state_locals t) = SOME env
         ==>
       wordSem_evaluate (SilentFFI c 3 (adjust_sets ns),t) =
         (NONE,state_ffi_fupd (K (state_ffi t))
           (wordSem_state_memory_fupd (K (wordSem_state_memory t))
           (fp_regs_fupd (K FEMPTY) (state_locals_fupd (K env) t))))`)
  CHEAT_TAC;;

(* size_of_heap monotonicity helpers *)

let size_of_app_Number = cake_theorem "size_of_app_Number"
  (fun () ->
    `!xs ys lims i refs seen.
       size_of lims (xs ++ (Number i :: ys)) refs seen =
       (let (n,refs',seen') = size_of lims (xs ++ ys) refs seen in
       let k = (if small_num (limits_arch_64_bit lims) i then 0
         else bignum_size (limits_arch_64_bit lims) i) in
       (n + k,refs',seen'))`)
  CHEAT_TAC;;

let toList_delete_split = cake_theorem "toList_delete_split"
  (fun () ->
    `!k spt vv.
       sptree_lookup k spt = SOME vv ==>
       (?pre post.
         sptree_toList spt = pre ++ [vv] ++ post /\
         sptree_toList (sptree_delete k spt) = pre ++ post)`)
  CHEAT_TAC;;

let size_of_heap_delete_Number_LE =
  cake_theorem "size_of_heap_delete_Number_LE"
  (fun () ->
    `!k s i.
       sptree_lookup k (state_locals s) = SOME (Number i) ==>
       size_of_heap (state_locals_fupd (K (sptree_delete k
         (state_locals s))) s) <= size_of_heap s`)
  CHEAT_TAC;;

let wf_FOLDR_delete = cake_theorem "wf_FOLDR_delete"
  (fun () ->
    `!ks (L:'a spt). sptree_wf L ==> sptree_wf (ITLIST sptree_delete
  ks L)`)
  CHEAT_TAC;;

let data_to_word_assignProof_lookup_FOLDR_delete =
  cake_theorem "lookup_FOLDR_delete"
  (fun () ->
    `!ks (L:'a spt) h.
       sptree_lookup h (ITLIST sptree_delete ks L) =
       (if MEM h ks then NONE else sptree_lookup h L)`)
  CHEAT_TAC;;

let size_of_heap_FOLDR_delete_Number_LE =
  cake_theorem "size_of_heap_FOLDR_delete_Number_LE"
  (fun () ->
    `!ks L (state:('a,'b)dataSem_state).
       sptree_wf L /\
       (!k. MEM k ks ==> sptree_lookup k L = NONE \/
                         (?i. sptree_lookup k L = SOME (Number i)))
                           ==>
       size_of_heap (state_locals_fupd (K (ITLIST sptree_delete ks
         L)) state) <=
       size_of_heap (state_locals_fupd (K L) state)`)
  CHEAT_TAC;;


(* end size_of_heap monotonicity helpers *)


let assign_Install = cake_theorem "assign_Install"
  (fun () ->
    `(op = Install) ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_MutCons = cake_theorem "assign_MutCons"
  (fun () ->
    `(?t k. op = closLang_MemOp (closLang_MutCons t k)) ==> (state_rel c
  l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_UpdateCons = cake_theorem "assign_UpdateCons"
  (fun () ->
    `op = closLang_MemOp closLang_UpdateCons ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_FinaliseCons = cake_theorem "assign_FinaliseCons"
  (fun () ->
    `op = closLang_MemOp closLang_FinaliseCons ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let LENGTH_EQ_5 = cake_theorem "LENGTH_EQ_5"
  (fun () ->
    `(LENGTH xs = 5 <=> (?a1 a2 a3 a4 a5. xs = [a1; a2; a3; a4; a5])) /\
      (5 = LENGTH xs <=> (?a1 a2 a3 a4 a5. xs = [a1; a2; a3; a4;
        a5]))`)
  CHEAT_TAC;;

let memory_rel_get_num = cake_theorem "memory_rel_get_num"
  (fun () ->
    `memory_rel c be ts refs sp st m dm vars /\
      n < dimword (:'a) DIV 8 /\ good_dimindex (:'a) /\
      MEM (Number (&n),(a:'a word_loc)) vars ==>
      (?w. a = wordLang_Word w /\ w >>> 2 = n2w n)`)
  CHEAT_TAC;;

let IN_domain_adjust_set_inter =
  cake_theorem "IN_domain_adjust_set_inter"
  (fun () ->
    `x IN domain (adjust_set (inter s1 s2)) <=>
      x IN domain (adjust_set s1) /\
      x IN domain (adjust_set s2)`)
  CHEAT_TAC;;

let get_var_to_word_exp = cake_theorem "get_var_to_word_exp"
  (fun () ->
    `get_var r s = SOME (wordLang_Word w) ==>
     wordSem_word_exp s (Op Add [Var r; Const (n2w 0)]) = SOME
       (wordLang_Word (w + (n2w 0))) /\
     wordSem_word_exp s (Op Add [Var r; Const (n2w 1)]) = SOME
       (wordLang_Word (w + (n2w 1))) /\
     wordSem_word_exp s (Op Add [Var r; Const (n2w 2)]) = SOME
       (wordLang_Word (w + (n2w 2))) /\
     wordSem_word_exp s (Op Add [Var r; Const (n2w 3)]) = SOME
       (wordLang_Word (w + (n2w 3)))`)
  CHEAT_TAC;;

let word_exp_set = cake_theorem "word_exp_set[local]"
  (fun () ->
    `(wordSem_word_exp s (wordLang_Op Add [Var n; Const c]) =
     (match get_var n s with
       SOME (wordLang_Word w) -> SOME (wordLang_Word (w + c)) | _5
         -> NONE)) /\
     (wordSem_word_exp s (Op Sub [Var n; Const c]) =
     (match get_var n s with
       SOME (wordLang_Word w) -> SOME (wordLang_Word (w - c)) |
         _6 -> NONE))`)
  CHEAT_TAC;;

let good_dimindex_w2w_byte =
  cake_theorem "good_dimindex_w2w_byte[local]"
  (fun () ->
    `good_dimindex (:'a) ==>
     w2w (w2w (w:word8):'a word) = w`)
  CHEAT_TAC;;

let set_var_consts = cake_theorem "set_var_consts[local]"
  (fun () ->
    `wordSem_state_memory
       (set_var r v s) = wordSem_state_memory s /\
         wordSem_state_mdomain
       (set_var r v s) = wordSem_state_mdomain s /\ be
       (set_var r v s) = be s /\ state_code
       (set_var r v s) = state_code s`)
  CHEAT_TAC;;

let get_var_consts = cake_theorem "get_var_consts[local]"
  (fun () ->
    `get_var r (wordSem_state_memory_fupd (K m) s) = get_var r s`)
  CHEAT_TAC;;

let CopyByteAdd_thm = cake_theorem "CopyByteAdd_thm"
  (fun () ->
    `!be' n a1 a2 m dm ret_val l1 l2 (s:('a,'c,'ffi)wordSem_state) m1.
        word_copy_fwd be' n a1 a2 m dm = SOME m1 /\
          wordSem_state_memory
        s = m /\ wordSem_state_mdomain s = dm /\ be
        s = be' /\
        good_dimindex (:'a) /\
        sptree_lookup ByteCopyAdd_location (state_code s) = SOME
          (5,ByteCopyAdd_code) /\
        w2n n DIV 4 <= state_clock s /\
        get_var 0 s = SOME (Loc l1 l2) /\
        get_var 2 s = SOME (wordLang_Word n) /\
        get_var 4 s = SOME (wordLang_Word (a1:'a word)) /\
        get_var 6 s = SOME (wordLang_Word a2) /\
        get_var 8 s = SOME ret_val ==>
        evaluate (ByteCopyAdd_code,s) =
          (SOME (wordSem_Result (wordLang_Loc l1 l2)
            [ret_val]),state_stack_max_fupd (K
                     (if n <+ (n2w 4) then state_stack_max
                       s else
                       OPTION_MAP2 MAX (state_stack_max s)
                         (OPTION_MAP2 (+) (stack_size (stack s))
                         (sptree_lookup ByteCopyAdd_location
                           (wordSem_state_stack_size s)))))
                           (state_locals_size_fupd (K (SOME 0))
                           (state_locals_fupd (K LN)
                           (wordSem_state_memory_fupd (K m1)
                           (state_clock_fupd (K (state_clock s - w2n n
                           DIV 4))
           s)))))`)
  CHEAT_TAC;;

let CopyByteSub_thm = cake_theorem "CopyByteSub_thm"
  (fun () ->
    `!be' n a1 a2 m dm ret_val l1 l2 (s:('a,'c,'ffi)wordSem_state) m1.
        word_copy_bwd be' n a1 a2 m dm = SOME m1 /\
          wordSem_state_memory
        s = m /\ wordSem_state_mdomain s = dm /\ be
        s = be' /\
        good_dimindex (:'a) /\
        sptree_lookup ByteCopySub_location (state_code s) = SOME
          (5,ByteCopySub_code) /\
        w2n n DIV 4 <= state_clock s /\
        get_var 0 s = SOME (Loc l1 l2) /\
        get_var 2 s = SOME (wordLang_Word n) /\
        get_var 4 s = SOME (wordLang_Word (a1:'a word)) /\
        get_var 6 s = SOME (wordLang_Word a2) /\
        get_var 8 s = SOME ret_val ==>
        evaluate (ByteCopySub_code,s) =
          (SOME (wordSem_Result (wordLang_Loc l1 l2)
            [ret_val]),state_stack_max_fupd (K
                     (if n <+ (n2w 4) then state_stack_max
                       s else
                       OPTION_MAP2 MAX (state_stack_max s)
                         (OPTION_MAP2 (+) (stack_size (stack s))
                         (sptree_lookup ByteCopySub_location
                           (wordSem_state_stack_size s)))))
                           (state_locals_size_fupd (K (SOME 0))
                           (state_locals_fupd (K LN)
                           (wordSem_state_memory_fupd (K m1)
                           (state_clock_fupd (K (state_clock s - w2n n
                           DIV 4))
           s)))))`)
  CHEAT_TAC;;

let push_env_store = cake_theorem "push_env_store"
  (fun () ->
    `wordSem_state_store
        (push_env x y s) = wordSem_state_store s /\
          wordSem_state_memory
         (push_env x y s) = wordSem_state_memory s /\
           wordSem_state_mdomain
         (push_env x y s) = wordSem_state_mdomain s /\ state_code
         (push_env x y s) = state_code s /\ be
         (push_env x y s) = be s`)
  CHEAT_TAC;;

let not_less_zero_int_eq = cake_theorem "not_less_zero_int_eq[local]"
  (fun () ->
    `~(i < ((&0):int)) <=> (?n. i = &n)`)
  CHEAT_TAC;;

let assign_WordFromWord = cake_theorem "assign_WordFromWord"
  (fun () ->
    `(?b. op = closLang_WordOp (WordFromWord b)) ==> (state_rel c l1 l2
  s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
     (~(op_requires_names op = (names_opt = NONE))) /\
     cut_state_opt names_opt s = SOME x /\
     get_vars args (state_locals s) = SOME vals /\
       wordSem_state_termdep
     t > 1 /\
     do_app op vals x = Rval (v,s2) ==>
     (?q r.
       evaluate (FST (assign c n l dest op args names_opt),t) =
         (q,r) /\
       (q = SOME wordSem_NotEnoughSpace ==> state_ffi
        r = state_ffi t /\ option_le (state_stack_max r)
          (state_stack_max s2) /\
        (~(data_to_word_config_gc_kind c = None) ==>
          ~(dataSem_state_safe_for_space s2))) /\
       (~(q = SOME wordSem_NotEnoughSpace) ==>
        state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
          NONE)))`)
  CHEAT_TAC;;

let IS_SOME_lookup = cake_theorem "IS_SOME_lookup"
  (fun () ->
    `IS_SOME (sptree_lookup n l) <=> n IN domain l`)
  CHEAT_TAC;;

let IN_adjust_var_lemma = cake_theorem "IN_adjust_var_lemma"
  (fun () ->
    `cut_env kept_names s_locals = SOME x /\
     cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
     n IN domain x ==>
     adjust_var n IN domain y2`)
  CHEAT_TAC;;

let cut_env_envs_lookup_lookup =
  cake_theorem "cut_env_envs_lookup_lookup"
  (fun () ->
    `cut_env kept_names s_locals = SOME x /\
     cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
     k IN domain (adjust_set x) ==>
     (?v. sptree_lookup k t_locals = SOME v /\
         sptree_lookup k y2 = SOME v)`)
  CHEAT_TAC;;

let env_to_list_domain = cake_theorem "env_to_list_domain"
  (fun () ->
    `env_to_list y2 p = (l,permute) ==>
     domain (fromAList l) = domain y2`)
  CHEAT_TAC;;

let cut_envs_lookup_0 = cake_theorem "cut_envs_lookup_0"
  (fun () ->
    `cut_envs (adjust_sets names) t_locals = SOME (y1,y2) /\
     env_to_list y2 p = (q,r') /\
     sptree_lookup 0 t_locals = SOME (Loc l1 l2) ==>
     ALOOKUP q 0 = NONE /\
     sptree_lookup 0 y1 = SOME (Loc l1 l2)`)
  CHEAT_TAC;;

let cut_envs_domain_IN = cake_theorem "cut_envs_domain_IN"
  (fun () ->
    `cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
     cut_env kept_names s_locals = SOME x /\
     n IN domain x ==>
     adjust_var n IN domain y2`)
  CHEAT_TAC;;

let inter_union_distrib = cake_theorem "inter_union_distrib"
  (fun () ->
    `!x y z. inter (union x y) z = union (inter x z) (inter y z)`)
  CHEAT_TAC;;

let cut_envs_inter = cake_theorem "cut_envs_inter"
  (fun () ->
    `cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
     cut_env kept_names s_locals = SOME x ==>
     inter (fromAList (toAList y1)) (adjust_set x) = LN`)
  CHEAT_TAC;;

let assign_CopyByte = cake_theorem "assign_CopyByte"
  (fun () ->
    `(?new_flag. op = closLang_MemOp (closLang_CopyByte new_flag) /\
  ~new_flag) ==> (state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE
  locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let evaluate_StringCmpLoop = cake_theorem "evaluate_StringCmpLoop"
  (fun () ->
    `!a1 a2 r1 r2 len be' ck dm m l1 l2 (t1:('a,'c,'ffi)wordSem_state)
  x1 x2.
       word_str_cmp_loop a1 a2 r1 r2 len dm m be' ck = SOME (x1,x2)
         /\ wordSem_state_memory
       t1 = m /\ wordSem_state_mdomain t1 = dm /\ be' = be t1 /\
       ck < state_clock t1 /\ good_dimindex (:'a) /\
       sptree_lookup StringCmpLoop_location (state_code t1) = SOME
         (6,StringCmpLoop_code) /\
       get_var 0 t1 = SOME (Loc l1 l2) /\
       get_var 2 t1 = SOME (wordLang_Word a1) /\
       get_var 4 t1 = SOME (wordLang_Word a2) /\
       get_var 6 t1 = SOME (wordLang_Word len) /\
       get_var 8 t1 = SOME (wordLang_Word r1) /\
       get_var 10 t1 = SOME (wordLang_Word r2) ==>
       (?ck max_stack.
         evaluate (StringCmpLoop_code,t1) =
         (SOME (wordSem_Result (wordLang_Loc l1 l2) [wordLang_Word
           x1; wordLang_Word x2]),state_locals_size_fupd (K (SOME 0))
           (state_locals_fupd (K LN) (state_stack_max_fupd (K max_stack)
           (state_clock_fupd (K ck)
          t1)))) /\
         (~(max_stack = state_stack_max t1) ==>
          max_stack = OPTION_MAP2 MAX (state_stack_max t1)
                        (OPTION_MAP2 (+) (stack_size (stack t1))
                           (sptree_lookup StringCmpLoop_location
                             (wordSem_state_stack_size t1)))))`)
  CHEAT_TAC;;

let evaluate_AssignCmp = cake_theorem "evaluate_AssignCmp"
  (fun () ->
    `evaluate (AssignCmp dest cmp v1 v2,s) =
       (match (get_var v1 s,get_var v2 s) with (SOME (wordLang_Word
         x1),SOME (wordLang_Word x2)) ->
           (NONE,set_var dest (if num_cmp cmp (w2n x1) (w2n x2)
             then wordLang_Word (n2w 18) else wordLang_Word (n2w 2))
             s) | _7 -> evaluate (AssignCmp dest cmp v1 v2,s))`)
  CHEAT_TAC;;

let evaluate_StringCmpMin = cake_theorem "evaluate_StringCmpMin[local]"
  (fun () ->
    `evaluate (wordLang_Seq (Assign 9 (Var 5))
                   (Seq (If asm_Lower 7 (Reg 5) (Assign 9 (Var 7))
                     Skip) p),state_locals_fupd (K l)
               t1) =
     (match (sptree_lookup 5 l,sptree_lookup 7 l) with (SOME
       (wordLang_Word w1),SOME (wordLang_Word w2)) ->
         evaluate (p,state_locals_fupd (K (insert 9 (wordLang_Word
           (n2w (MIN (w2n w1) (w2n w2)))) l)) t1) | _10 ->
         evaluate (Seq (Assign 9 (Var 5))
                       (Seq (If asm_Lower 7 (Reg 5) (Assign 9 (Var
                         7)) Skip) p),state_locals_fupd (K l)
                   t1))`)
  CHEAT_TAC;;

let assign_StringCmp = cake_theorem "assign_StringCmp"
  (fun () ->
    `(?b cmp. op = closLang_MemOp (closLang_StringCmp b cmp)) ==>
  (state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let evaluate_XorLoop = cake_theorem "evaluate_XorLoop"
  (fun () ->
    `!a1 a2 l dm m l1 l2 (t1:('a,'c,'ffi)wordSem_state) m1.
       word_xor_bytes a1 a2 l dm m = SOME m1 /\
         wordSem_state_memory t1 = m /\ wordSem_state_mdomain t1 = dm /\
       w2n l < state_clock t1 /\ good_dimindex (:'a) /\
       sptree_lookup XorLoop_location (state_code t1) = SOME
         (4,XorLoop_code) /\
       get_var 0 t1 = SOME (Loc l1 l2) /\
       get_var 2 t1 = SOME (wordLang_Word a2) /\
       get_var 4 t1 = SOME (wordLang_Word a1) /\
       get_var 6 t1 = SOME (wordLang_Word l) ==>
       (?ck max_stack.
         evaluate (XorLoop_code,t1) =
         (SOME (wordSem_Result (wordLang_Loc l1 l2) [wordLang_Word
           (n2w 2)]),state_locals_size_fupd (K (SOME 0))
           (state_locals_fupd (K LN) (state_stack_max_fupd (K max_stack)
           (state_clock_fupd (K ck) (wordSem_state_memory_fupd (K m1)
          t1))))) /\
         (~(max_stack = state_stack_max t1) ==>
          max_stack = OPTION_MAP2 MAX (state_stack_max t1)
                        (OPTION_MAP2 (+) (stack_size (stack t1))
                           (sptree_lookup XorLoop_location
                             (wordSem_state_stack_size t1)))))`)
  CHEAT_TAC;;

let assign_XorByte = cake_theorem "assign_XorByte"
  (fun () ->
    `op = closLang_MemOp closLang_XorByte ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let evaluate_AppendMainLoop_code =
  cake_theorem "evaluate_AppendMainLoop_code[local]"
  (fun () ->
    `!xs ww (t:('a,'c,'ffi)wordSem_state) vars' ptr hdr l k frame r1 r2
  next_free ts v.
       memory_rel c (be t) ts (state_refs
         (s:('c,'ffi)dataSem_state)) sp (wordSem_state_store t)
         (wordSem_state_memory t) (wordSem_state_mdomain t)
          ((v,wordLang_Word ww) :: vars') /\ ~(xs = []) /\
       v_to_list v = SOME xs /\
       sptree_lookup 10 (state_locals t) = SOME (wordLang_Word ptr)
         /\
       sptree_lookup 8 (state_locals t) = SOME (wordLang_Word
         (bytes_in_word * n2w (sp - k))) /\
       sptree_lookup 6 (state_locals t) = SOME (wordLang_Word hdr)
         /\
       sptree_lookup 4 (state_locals t) = SOME (wordLang_Word ww)
         /\
       sptree_lookup 2 (state_locals t) = SOME (wordLang_Word
         next_free) /\
       sptree_lookup 0 (state_locals t) = SOME (Loc r1 r2) /\
       k + 3 * LENGTH xs <= sp /\ good_dimindex (:'a) /\
       sp * (dimindex (:'a) DIV 8) < dimword (:'a) /\
       FLOOKUP (wordSem_state_store t) (Temp (n2w 0)) = SOME tmp0
         /\
       FLOOKUP (wordSem_state_store t) (Temp (n2w 2)) = SOME tmp2
         /\
       FLOOKUP (wordSem_state_store t) NextFree = SOME
         (wordLang_Word f) /\
       Abbrev (next_free = f + bytes_in_word * n2w k) /\
       sptree_lookup AppendMainLoop_location (state_code t) = SOME
         (6,AppendMainLoop_code c) /\
       sptree_lookup AppendMainLoop_location
         (wordSem_state_stack_size t) = state_locals_size t /\
       (word_list_exists next_free (3 * LENGTH xs) * frame)
          (fun2set (wordSem_state_memory t,wordSem_state_mdomain
            t)) /\ LENGTH xs <= state_clock t ==>
       (?m1 ws smx.
         evaluate (AppendMainLoop_code c,t) =
           (SOME (wordSem_Result (wordLang_Loc r1 r2)
             [tmp2]),state_clock_fupd (K (state_clock t - (LENGTH xs -
             1))) (state_stack_max_fupd (K smx)
             (wordSem_state_memory_fupd (K m1) (wordSem_state_store_fupd
             (K (wordSem_state_store t |+ (NextFree,wordLang_Word
             (next_free +
                         bytes_in_word * n2w (3 * LENGTH xs)))))
                           (state_locals_size_fupd (K (SOME 0))
                           (state_locals_fupd (K LN)
            t)))))) /\
         LENGTH ws = LENGTH xs /\
         option_le smx (OPTION_MAP2 MAX (state_stack_max
                          t)
                          (OPTION_MAP2 (+)
                            (OPTION_MAP2 MAX
                              (sptree_lookup
                                AppendMainLoop_location
                                (wordSem_state_stack_size t))
                              (sptree_lookup AppendLenLoop_location
                                (wordSem_state_stack_size t)))
                            (stack_size (stack t)))) /\
         (misc_word_list next_free (append_writes c ptr hdr ws
           tmp0) * frame)
           (fun2set (m1,wordSem_state_mdomain t)) /\
         memory_rel c (be t) ts (state_refs s) sp
           (wordSem_state_store t) m1 (wordSem_state_mdomain t)
           (ZIP xs ws ++ vars'))`)
  CHEAT_TAC;;

let STOP_def = cake_define
  `data_to_word_assignProof_STOP x = x`;;
hol4_overload "STOP" "data_to_word_assignProof_STOP";;

let evaluate_AppendMainLoop_code_alt =
  cake_theorem "evaluate_AppendMainLoop_code_alt[local]"
  (fun () ->
    `!xs ww (t:('a,'c,'ffi)wordSem_state) vars' ptr hdr l k frame r1 r2
  next_free ts v.
       memory_rel c (be t) ts (state_refs
         (s:('c,'ffi)dataSem_state)) sp (wordSem_state_store t)
         (wordSem_state_memory t) (wordSem_state_mdomain t)
          ((v,wordLang_Word ww) :: vars') /\ ~(xs = []) /\
       v_to_list v = SOME xs /\
       sptree_lookup 10 (state_locals t) = SOME (wordLang_Word ptr)
         /\
       sptree_lookup 8 (state_locals t) = SOME (wordLang_Word
         (bytes_in_word * n2w (sp - k))) /\
       sptree_lookup 6 (state_locals t) = SOME (wordLang_Word hdr)
         /\
       sptree_lookup 4 (state_locals t) = SOME (wordLang_Word ww)
         /\
       sptree_lookup 2 (state_locals t) = SOME (wordLang_Word
         next_free) /\
       sptree_lookup 0 (state_locals t) = SOME (Loc r1 r2) /\
       sp < k + 3 * LENGTH xs /\ good_dimindex (:'a) /\ k <= sp /\
       sp * (dimindex (:'a) DIV 8) < dimword (:'a) /\
       FLOOKUP (wordSem_state_store t) (Temp (n2w 0)) = SOME tmp0
         /\
       FLOOKUP (wordSem_state_store t) (Temp (n2w 2)) = SOME tmp2
         /\
       FLOOKUP (wordSem_state_store t) NextFree = SOME
         (wordLang_Word f) /\
       Abbrev (next_free = f + bytes_in_word * n2w k) /\
       sptree_lookup AppendMainLoop_location (state_code t) = SOME
         (6,AppendMainLoop_code c) /\
       sptree_lookup AppendLenLoop_location (state_code t) = SOME
         (3,AppendLenLoop_code c) /\
       (word_list_exists next_free (sp - k) * frame)
          (fun2set (wordSem_state_memory t,wordSem_state_mdomain
            t)) /\ LENGTH xs <= state_clock t ==>
       (?m1 ww2 smx.
         evaluate (AppendMainLoop_code c,t) =
           (match STOP evaluate (AppendLenLoop_code
             c,state_clock_fupd (K (state_clock t - ((sp - k) DIV 3 +
             1))) (state_stack_max_fupd (K smx)
             (wordSem_state_memory_fupd (K m1) (state_locals_size_fupd
             (K (sptree_lookup AppendLenLoop_location
             (wordSem_state_stack_size t))) (state_locals_fupd (K
             (fromList2 [Loc r1 r2; wordLang_Word ww2; wordLang_Word
             (n2w 0)]))
               t))))) with (res,s) -> (if wordSem_bad_fun_return
                 res then (SOME Error,s) else (res,s))) /\
         option_le (OPTION_MAP2 (+) (stack_size (stack t))
           (sptree_lookup AppendLenLoop_location
           (wordSem_state_stack_size t))) smx /\
         option_le smx
           (OPTION_MAP2 MAX (state_stack_max t)
              (OPTION_MAP2 (+) (stack_size (stack t))
              (OPTION_MAP2 MAX
                 (sptree_lookup AppendLenLoop_location
                   (wordSem_state_stack_size t))
                 (sptree_lookup AppendMainLoop_location
                   (wordSem_state_stack_size t))))) /\
         memory_rel c (be t) ts (state_refs s) sp
           (wordSem_state_store t) m1 (wordSem_state_mdomain t)
          ((THE (block_drop ((sp - k) DIV 3) v),wordLang_Word
            ww2) :: vars'))`)
  CHEAT_TAC;;
(* HOL4 data_to_word_assignProofScript.sml:5278-5281: ML code, not
   ported *)

let evaluate_AppendLenLoop_code =
  cake_theorem "evaluate_AppendLenLoop_code[local]"
  (fun () ->
    `!k (t:('a,'c,'ffi)wordSem_state) c xs l1 l2 (w:'a word) vars' ts v.
       memory_rel c (be t) ts refs sp (wordSem_state_store t)
         (wordSem_state_memory t) (wordSem_state_mdomain t)
         ((v,wordLang_Word w) :: vars') /\
       v_to_list v = SOME xs /\
       sptree_lookup 0 (state_locals t) = SOME (Loc l1 l2) /\
       sptree_lookup 2 (state_locals t) = SOME (wordLang_Word w) /\
       sptree_lookup 4 (state_locals t) = SOME (wordLang_Word (n2w
         (12 * k))) /\
       sptree_lookup AppendLenLoop_location (state_code t) = SOME
         (3,AppendLenLoop_code c) /\ state_locals_size
       t = sptree_lookup AppendLenLoop_location
         (wordSem_state_stack_size t) /\
       good_dimindex (:'a) /\
       LENGTH xs <= state_clock t ==>
       (?locals smx.
         (match evaluate (AppendLenLoop_code c,t) with
           (res,s) -> (if wordSem_bad_fun_return res then (SOME
             Error,s) else (res,s))) =
         (match evaluate (AppendLenLoop_code c,state_stack_max_fupd
           (K smx) (state_clock_fupd (K (state_clock t - LENGTH xs))
           (state_locals_fupd (K locals)
                 t))) with
           (res,s) -> (if wordSem_bad_fun_return res then (SOME
             Error,s) else (res,s))) /\
         sptree_lookup 0 locals = SOME (Loc l1 l2) /\
         sptree_lookup 2 locals = SOME (wordLang_Word (n2w 2)) /\
         sptree_lookup 4 locals = SOME (wordLang_Word (n2w (12 * (k
           + LENGTH xs)))) /\
         option_le (state_stack_max t) smx /\
         option_le smx (OPTION_MAP2 MAX (state_stack_max t)
                         (OPTION_MAP2 (+) (stack_size (stack t))
                         (sptree_lookup AppendLenLoop_location
                           (wordSem_state_stack_size t)))))`)
  CHEAT_TAC;;
(* HOL4 data_to_word_assignProofScript.sml:5370-5371: ML code, not
   ported *)

let v_to_list_block_drop = cake_theorem "v_to_list_block_drop"
  (fun () ->
    `!k v l.
      v_to_list v = SOME l /\ k < LENGTH l ==> v_to_list (THE
        (block_drop k v)) = SOME (DROP k l)`)
  CHEAT_TAC;;

let OPTION_MAP2_NONE_THM = cake_theorem "OPTION_MAP2_NONE_THM"
  (fun () ->
    `(OPTION_MAP2 f NONE x = NONE) /\
     (OPTION_MAP2 f x NONE = NONE)`)
  CHEAT_TAC;;

(* TODO: declared with [simp] further down *)
let opt_map_plus_zero_id = cake_theorem "opt_map_plus_zero_id[local]"
  (fun () ->
    `!n. OPTION_MAP2 (+) (SOME 0) n = (n:num option)`)
  CHEAT_TAC;;

(* TODO: move *)
let option_le_flip_neg = cake_theorem "option_le_flip_neg"
  (fun () ->
    `~(option_le a b) ==> option_le b a`)
  CHEAT_TAC;;

let cut_state_refs_same = cake_theorem "cut_state_refs_same"
  (fun () ->
    `!n s x. dataSem_cut_state n s = SOME x ==> state_refs s =
  state_refs x`)
  CHEAT_TAC;;

let assign_ListAppend = cake_theorem "assign_ListAppend"
  (fun () ->
    `op = closLang_BlockOp ListAppend ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let do_app_AllocThunk = cake_theorem "do_app_AllocThunk"
  (fun () ->
    `do_app (ThunkOp (AllocThunk m):closLang_op) [v] x =
      (match consume_space (1 + 1) x with
        NONE -> Rerr (Rabort Rtype_error) | SOME s1 ->
        (if bad_thunk_update m v (state_refs s1) then Rerr (Rabort
          Rtype_error) else
        Rval
        (RefPtr F (LEAST (\ptr. ~(ptr IN domain (state_refs
          s1)))),state_stack_max_fupd (K (state_stack_max (
               do_stack
                 (ThunkOp (AllocThunk m)) [v]
                 (do_lim_safe s1 (ThunkOp (AllocThunk m)) [v]))))
                   (dataSem_state_safe_for_space_fupd (K
                   (dataSem_state_safe_for_space (
               do_stack
                 (ThunkOp (AllocThunk m)) [v]
                 (do_lim_safe s1 (ThunkOp (AllocThunk m)) [v]))))
                   (state_refs_fupd (K (insert (LEAST (\ptr. ~(ptr IN
                   domain (state_refs s1)))) (Thunk m v) (state_refs
                   s1)))
           s1)))))`)
  CHEAT_TAC;;

let assign_AllocThunk = cake_theorem "assign_AllocThunk"
  (fun () ->
    `(?ev. op = ThunkOp (AllocThunk ev)) ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_UpdateThunk = cake_theorem "assign_UpdateThunk"
  (fun () ->
    `(?ev. op = ThunkOp (UpdateThunk ev)) ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

(* ConfigGC: assign-specific helper + body *)
let configGC_size_of_heap_LE = cake_theorem "configGC_size_of_heap_LE"
  (fun () ->
    `!ns s x k1 k2 i1 i2 (state:('a,'b)dataSem_state).
       dataSem_cut_state_opt (SOME (sptree_insert k2 one
         (sptree_insert k1 one ns))) s = SOME x /\
       sptree_lookup k1 (state_locals x) = SOME (Number i1) /\
       sptree_lookup k2 (state_locals x) = SOME (Number i2) /\
         state_refs
       state = state_refs s /\ dataSem_state_limits state =
         dataSem_state_limits s /\ stack
       state = stack s /\ dataSem_state_global state =
         dataSem_state_global s ==>
       size_of_heap (state_locals_fupd (K (mk_wf (inter
         (state_locals s) ns))) state) <=
       size_of_heap (state_locals_fupd (K (state_locals x))
         state)`)
  CHEAT_TAC;;

(* Prepending values to the size_of root list never shrinks the heap count.
   Basis for the args-aware do_space bridge (replaces the two-stage size_of
   narrow/wide reconciliation helpers). *)
(* size_of_LE_append and size_of_heap_LE_args are inherited from
   data_to_word_bignumProof (used there by eval_Call_Arith). *)

(* The single narrow cut state IS cut_locals of the original: alloc_lemma's
   size_of_heap (cut_locals ns s) is exactly size_of_heap x. *)
let cut_state_opt_IMP_cut_locals =
  cake_theorem "cut_state_opt_IMP_cut_locals"
  (fun () ->
    `cut_state_opt (SOME ns) s = SOME x ==> cut_locals ns s = x`)
  CHEAT_TAC;;

let assign_ConfigGC = cake_theorem "assign_ConfigGC"
  (fun () ->
    `op = closLang_MemOp ConfigGC ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
     (~(op_requires_names op = (names_opt = NONE))) /\
     cut_state_opt names_opt s = SOME x /\
     get_vars args (state_locals s) = SOME vals /\
       wordSem_state_termdep
     t > 1 /\
     do_app op vals x = Rval (v,s2) ==>
     (?q r.
       evaluate (FST (assign c n l dest op args names_opt),t) =
         (q,r) /\
       (q = SOME wordSem_NotEnoughSpace ==> state_ffi
        r = state_ffi t /\ option_le (state_stack_max r)
          (state_stack_max s2) /\
        (~(data_to_word_config_gc_kind c = None) ==>
          ~(dataSem_state_safe_for_space s2))) /\
       (~(q = SOME wordSem_NotEnoughSpace) ==>
        state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
          NONE)))`)
  CHEAT_TAC;;

let assign_WordToInt = cake_theorem "assign_WordToInt"
  (fun () ->
    `op = closLang_WordOp WordToInt ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
     (~(op_requires_names op = (names_opt = NONE))) /\
     cut_state_opt names_opt s = SOME x /\
     get_vars args (state_locals s) = SOME vals /\
       wordSem_state_termdep
     t > 1 /\
     do_app op vals x = Rval (v,s2) ==>
     (?q r.
       evaluate (FST (assign c n l dest op args names_opt),t) =
         (q,r) /\
       (q = SOME wordSem_NotEnoughSpace ==> state_ffi
        r = state_ffi t /\ option_le (state_stack_max r)
          (state_stack_max s2) /\
        (~(data_to_word_config_gc_kind c = None) ==>
          ~(dataSem_state_safe_for_space s2))) /\
       (~(q = SOME wordSem_NotEnoughSpace) ==>
        state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
          NONE)))`)
  CHEAT_TAC;;

let push_env_tstamps = cake_theorem "push_env_tstamps"
  (fun () ->
    `!x t s. dataSem_state_tstamps (push_env x t s) =
  dataSem_state_tstamps s`)
  CHEAT_TAC;;

let dec_clock_tstamps = cake_theorem "dec_clock_tstamps"
  (fun () ->
    `!s. dataSem_state_tstamps (dec_clock s) = dataSem_state_tstamps s`)
  CHEAT_TAC;;

let FromList1_code_thm = cake_theorem "FromList1_code_thm"
  (fun () ->
    `!k a b r x m1 a1 a2 a3 a4 a5 a6.
        sptree_lookup FromList1_location (state_code r) = SOME
          (6,FromList1_code c) /\
        copy_list c (wordSem_state_store r) k
          (a,x,b,wordSem_state_memory
          (r:('a,'c,'ffi)wordSem_state),wordSem_state_mdomain
          r) = SOME (b1,m1) /\
        shift_length c < dimindex (:'a) /\ good_dimindex (:'a) /\
        get_var a1 r = SOME (Loc l1 l2) /\
        get_var a2 r = SOME (wordLang_Word (b:'a word)) /\
        get_var a3 r = SOME a /\
        get_var a4 r = SOME (wordLang_Word (n2w (4 * k))) /\
        get_var a5 r = SOME ret_val /\
        get_var a6 r = SOME x /\
        4 * k < dimword (:'a) /\
        k < state_clock r ==>
        evaluate (Call NONE (SOME FromList1_location) [a1; a2; a3;
          a4; a5; a6] NONE,r) =
          (SOME (wordSem_Result (wordLang_Loc l1 l2)
            [ret_val]),state_stack_max_fupd (K (OPTION_MAP2 MAX
            (state_stack_max r) (OPTION_MAP2 (+) (stack_size (stack r))
                              (sptree_lookup FromList1_location
                                (wordSem_state_stack_size r)))))
                                (wordSem_state_store_fupd (K
                                (wordSem_state_store r |+
                                (NextFree,wordLang_Word b1)))
                                (state_locals_size_fupd (K (SOME 0))
                                (state_locals_fupd (K LN)
                                (state_clock_fupd (K (state_clock r - k
                                - 1)) (wordSem_state_memory_fupd (K m1)
           r))))))`)
  CHEAT_TAC;;

let FromList_thm = cake_theorem "FromList_thm"
  (fun () ->
    `state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
  ~(encode_header c (4 * tag) 0 = (NONE:('a word) option)) /\
      get_vars [0; 1; 2] (state_locals s) = SOME [v1; v2; Number
        (&(4 * tag))] /\ state_clock
      t = MustTerminate_limit (:'a) - 1 /\
      pop_env s = SOME s1 /\ is_env (HD (stack s)) /\
        state_locals_size
      s = sptree_lookup FromList_location
        (dataSem_state_stack_frame_sizes s) /\
      do_app (closLang_BlockOp (closLang_FromList tag)) [v1; v2] s1
        = Rval (v,s2) /\
      option_le (state_stack_max s) (state_stack_max s2) /\
      size_of_heap (cut_locals (fromList [one; one; one]) s) <=
        size_of_heap_args [v1; v2] s1 ==>
      (?q r new_c.
        evaluate (FromList_code c,t) = (q,r) /\
        (if q = SOME wordSem_NotEnoughSpace then state_ffi
          r = state_ffi t /\
          option_le (state_stack_max r) (state_stack_max s2) /\
          (~(data_to_word_config_gc_kind c = None) /\
            no_thunks_in_refs (state_refs s) ==>
           (match (v1,v2) with
             (Number n,_11) -> ~(small_num (limits_arch_64_bit
               (dataSem_state_limits s)) n) \/
                             ~(num_of_int n < dimword (:'a) DIV 16)
                               \/
                             ~(num_of_int n < 2 EXP
                               data_to_word_config_len_size c) \/
                             (limits_heap_limit
                               (dataSem_state_limits s1) <
                              size_of_heap_args [v1; v2] s1 +
                                num_of_int n + 1))) else
          ?rv. q = SOME (wordSem_Result (wordLang_Loc l1 l2) [rv])
            /\
               state_rel c r1 r2 (stack_fupd (K (stack s))
                 (state_clock_fupd (K new_c) (state_locals_size_fupd (K
                 (SOME 0)) (state_locals_fupd (K LN) s2))))
                  r (SOME [(v,rv)]) locs))`)
  CHEAT_TAC;;

(* ---- helpers used by assign_FromList's NES/Success arms (also reused by
   assign_RefByte etc. below); hoisted above assign_FromList so they are in
   scope here. ---- *)

(* do_app for FromList sets the result stack_max uniformly (stack_consumed is
   the same for the empty and nonempty cases), regardless of tstamps. *)
let do_app_FromList_stack_max =
  cake_theorem "do_app_FromList_stack_max[local]"
  (fun () ->
    `do_app (closLang_BlockOp (closLang_FromList tag)) vals s = Rval
  (v,s') ==> state_stack_max
     s' = OPTION_MAP2 MAX (state_stack_max s)
       (OPTION_MAP2 (+)
          (stack_consumed (dataSem_state_stack_frame_sizes s)
            (dataSem_state_limits s) (closLang_BlockOp
            (closLang_FromList tag)) vals)
          (OPTION_MAP2 (+) (size_of_stack (stack s))
            (state_locals_size s)))`)
  CHEAT_TAC;;

(* do_app for FromList: the result safe_for_space field, uniform over the empty
   and nonempty cases (the empty case lacks the with_fresh_ts/check_lim wrapper,
   but its extra `LENGTH ys < 2 ** length_limit` conjunct is trivially true). The
   add_space_safe_args / the F terms are dataSem overloads; the statement spells
   them out so it parses without the abbreviation. *)
let do_app_FromList_safe = cake_theorem "do_app_FromList_safe[local]"
  (fun () ->
    `v_to_list v2 = SOME ys /\
     do_app (closLang_BlockOp (closLang_FromList tag)) [Number
       (&(LENGTH ys)); v2] (s:('c,'ffi)dataSem_state) = Rval (v,s') ==>
     (dataSem_state_safe_for_space s' <=>
      (((small_num (limits_arch_64_bit (dataSem_state_limits s))
        (&(LENGTH ys)) /\
         LENGTH ys < 2 EXP limits_length_limit
           (dataSem_state_limits s) /\
         LENGTH ys < arch_size (dataSem_state_limits s) DIV 16 /\
         4 * tag < 2 EXP (arch_size (dataSem_state_limits s) -
           (limits_length_limit (dataSem_state_limits s) + 2)) /\
         4 * tag < 2 EXP arch_size (dataSem_state_limits s) DIV 16)
           /\
        (dataSem_state_safe_for_space s /\
         no_thunks_in_refs (state_refs s) /\
         size_of_heap_args [Number (&(LENGTH ys)); v2] s + (LENGTH
           ys + 1) <= limits_heap_limit (dataSem_state_limits s))) /\
       the F (OPTION_MAP ((>) (stack_limit (dataSem_state_limits
         s)))
         (OPTION_MAP2 (+) (OPTION_MAP2 MAX (sptree_lookup
           FromList_location (dataSem_state_stack_frame_sizes s))
                              (sptree_lookup FromList1_location
                                (dataSem_state_stack_frame_sizes s)))
                         (OPTION_MAP2 (+) (size_of_stack (stack
                           s)) (state_locals_size s))))))`)
  CHEAT_TAC;;

(* do_app for FromList: the result value is a Block of the source list, and the
   non-stack/safe/space fields are preserved from the input state (tstamps gains
   a fresh stamp for nonempty lists). Used by assign_FromList's success arm to
   relate s2 (do_app on x) and s2_inner (do_app on s_pop): both share these
   fields because x and s_pop agree on locals/refs/tstamps/.... *)
let do_app_FromList_eq = cake_theorem "do_app_FromList_eq[local]"
  (fun () ->
    `v_to_list v2 = SOME ys /\
     do_app (closLang_BlockOp (closLang_FromList tag)) [Number
       (&(LENGTH ys)); v2] (s:('c,'ffi)dataSem_state) = Rval (v,s') ==>
     (?ts'. v = Block ts' tag ys) /\ dataSem_state_space s' = 0 /\
       state_refs
     s' = state_refs s /\ state_code s' = state_code s /\ state_ffi
       s' = state_ffi s /\ state_handler s' = state_handler s /\
       state_locals
     s' = state_locals s /\ stack s' = stack s /\
       dataSem_state_limits s' = dataSem_state_limits s /\
       dataSem_state_stack_frame_sizes
     s' = dataSem_state_stack_frame_sizes s /\ state_locals_size s'
       = state_locals_size s /\ dataSem_state_global
     s' = dataSem_state_global s /\ compile s' = compile s /\
       compile_oracle s' = compile_oracle s /\ state_clock
     s' = state_clock s /\ dataSem_state_tstamps
     s' = (if ys = [] then dataSem_state_tstamps s else
       OPTION_MAP SUC (dataSem_state_tstamps s))`)
  CHEAT_TAC;;

(* Variant of call_env_push_env_dec_clock_lift that also absorbs a `locals
   := insert k v t.locals` field update inside the dec_clock. *)
let call_env_push_env_dec_clock_lift_locals =
  cake_theorem "call_env_push_env_dec_clock_lift_locals[local]"
  (fun () ->
    `call_env (args:('a word_loc) list) b (push_env (y1,y2) NONE
       (wordSem_dec_clock (wordSem_state_termdep_fupd (K tp)
         (state_clock_fupd (K ck') (state_locals_fupd (K (insert k v
         (state_locals t))) (t:('a,'c,'ffi)wordSem_state)))))) =
         wordSem_state_termdep_fupd (K tp) (state_clock_fupd (K (ck' -
         1))
     (call_env args b (push_env (y1,y2) NONE t)))`)
  CHEAT_TAC;;

let call_env_push_env_dec_clock_stack_max =
  cake_theorem "call_env_push_env_dec_clock_stack_max[local]"
  (fun () ->
    `state_stack_max
       (call_env args ls (push_env env F (dec_clock
         (s:('c,'ffi)dataSem_state)))) =
         OPTION_MAP2 MAX
           (OPTION_MAP2 MAX (state_stack_max s)
              (OPTION_MAP2 (((+)):num->num->num) (state_locals_size
                s) (size_of_stack (stack s))))
           (OPTION_MAP2 (((+)):num->num->num)
              (OPTION_MAP2 (((+)):num->num->num)
                (state_locals_size s) (size_of_stack (stack s))) ls)`)
  CHEAT_TAC;;

let option_le_stackmax_bridge =
  cake_theorem "option_le_stackmax_bridge[local]"
  (fun () ->
    `!(m:num option) (l_size:num option) (s_size:num option)
       (ls_R:num option) (ls_Re:num option).
       option_le
         (OPTION_MAP2 MAX
            (OPTION_MAP2 MAX
               (OPTION_MAP2 MAX m (OPTION_MAP2
                 (((+)):num->num->num) l_size s_size))
               (OPTION_MAP2 (((+)):num->num->num)
                  (OPTION_MAP2 (((+)):num->num->num) l_size s_size)
                    ls_R))
            (OPTION_MAP2 (((+)):num->num->num) (OPTION_MAP2 MAX
              ls_R ls_Re)
               (OPTION_MAP2 (((+)):num->num->num) s_size l_size)))
         (OPTION_MAP2 MAX m
            (OPTION_MAP2 (((+)):num->num->num) (OPTION_MAP2 MAX
              ls_R ls_Re)
               (OPTION_MAP2 (((+)):num->num->num) s_size
                 l_size)))`)
  CHEAT_TAC;;

let assign_FromList = cake_theorem "assign_FromList"
  (fun () ->
    `(?tag. op = closLang_BlockOp (closLang_FromList tag)) ==>
  (state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

(* TODO: move to backendProps? *)
let not_the_F_option_le = cake_theorem "not_the_F_option_le"
  (fun () ->
    `~(the F (OPTION_MAP ((>) n) m)) <=> option_le (SOME n) m`)
  CHEAT_TAC;;

let the_F_not_option_le = cake_theorem "the_F_not_option_le"
  (fun () ->
    `the F (OPTION_MAP ((>) n) m) <=> ~(option_le (SOME n) m)`)
  CHEAT_TAC;;

(* Helper: do_app on RefByte gives a precise equation s' = s with <known-update>
   (args-aware single-cut form). Used to bridge s2_inner field equalities in
   assign_RefByte's Success arm. *)
let do_app_RefByte_eq = cake_theorem "do_app_RefByte_eq[local]"
  (fun () ->
    `do_app (closLang_MemOp (closLang_RefByte fl)) [Number i; Number
  (&(w2n (w:word8)))] (s:('c,'ffi)dataSem_state) = Rval (v,s') ==>
     (?ptr. v = RefPtr T ptr /\ ptr = (LEAST (\p. ~(p IN domain
       (state_refs s)))) /\ (&0) <= i /\
           s' = dataSem_state_peak_heap_length_fupd (K
                    ((\k op_args (s:('c,'ffi)dataSem_state). MAX
                      (dataSem_state_peak_heap_length s)
                      (size_of_heap_args op_args s + k))
                      (space_consumed s (closLang_MemOp
                        (closLang_RefByte fl))
                         [Number i; Number (&(w2n w))])
                      [Number i; Number (&(w2n w))] s))
                        (dataSem_state_safe_for_space_fupd (K
                    (((num_of_int i DIV (arch_size
                      (dataSem_state_limits s) DIV 8) <
                       2 EXP arch_size (dataSem_state_limits s) DIV
                         arch_size (dataSem_state_limits s) /\
                       num_of_int i DIV (arch_size
                         (dataSem_state_limits s) DIV 8) + 1 <
                       2 EXP limits_length_limit
                         (dataSem_state_limits s) /\
                       small_num (limits_arch_64_bit
                         (dataSem_state_limits s)) i) /\
                      no_thunks_in_refs (state_refs s) /\
                      (\k op_args (s:('c,'ffi)dataSem_state).
                     dataSem_state_safe_for_space s /\
                       size_of_heap_args op_args s + k <=
                       limits_heap_limit (dataSem_state_limits s))
                        (space_consumed s (closLang_MemOp
                          (closLang_RefByte fl))
                           [Number i; Number (&(w2n w))])
                        [Number i; Number (&(w2n w))] s) /\
                     the F
                       (OPTION_MAP ((>) (stack_limit
                         (dataSem_state_limits s)))
                          (OPTION_MAP2 (+)
                             (stack_consumed
                               (dataSem_state_stack_frame_sizes s)
                               (dataSem_state_limits s)
                              (closLang_MemOp (closLang_RefByte
                                fl)) [Number i; Number (&(w2n w))])
                             (OPTION_MAP2 (+) (size_of_stack (stack
                               s)) (state_locals_size
                              s)))))) (dataSem_state_space_fupd (K
                                0) (state_refs_fupd (K (insert ptr
                                (ByteArray fl (REPLICATE (num_of_int i)
                                w)) (state_refs s)))
                                (state_stack_max_fupd (K
                    (OPTION_MAP2 MAX (state_stack_max s)
                      (OPTION_MAP2 (+)
                         (stack_consumed
                           (dataSem_state_stack_frame_sizes s)
                           (dataSem_state_limits s)
                            (closLang_MemOp (closLang_RefByte fl))
                              [Number i; Number (&(w2n w))])
                         (OPTION_MAP2 (+) (size_of_stack (stack
                           s)) (state_locals_size s))))) s)))))`)
  CHEAT_TAC;;

(* Helper: lift inner-with on a dec_clock'd state to outer-with on call_env/push_env.
   Used to bridge the post-Call evaluate term to the shape expected by
   evaluate_IMP_domain_union (which has outer-with). *)
let call_env_push_env_dec_clock_lift =
  cake_theorem "call_env_push_env_dec_clock_lift[local]"
  (fun () ->
    `call_env (args:('a word_loc) list) b (push_env (y1,y2) NONE
       (wordSem_dec_clock (wordSem_state_termdep_fupd (K tp)
         (state_clock_fupd (K ck') (t:('a,'c,'ffi)wordSem_state))))) =
         wordSem_state_termdep_fupd (K tp) (state_clock_fupd (K (ck' -
         1))
     (call_env args b (push_env (y1,y2) NONE t)))`)
  CHEAT_TAC;;

let assign_RefByte = cake_theorem "assign_RefByte"
  (fun () ->
    `(?fl. op = closLang_MemOp (closLang_RefByte fl)) ==> (state_rel c
  l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let lookup_set_var = cake_theorem "lookup_set_var"
  (fun () ->
    `sptree_lookup x (state_locals (set_var x y z)) = SOME y`)
  CHEAT_TAC;;

let lookup_2_call_env = cake_theorem "lookup_2_call_env[local]"
  (fun () ->
    `sptree_lookup 0 (state_locals (call_env (x :: ts) a1 a2)) = SOME x
  /\
     sptree_lookup 2 (state_locals (call_env (x :: y :: ts) a1 a2))
       = SOME y /\
     sptree_lookup 4 (state_locals (call_env (x :: y :: z :: ts)
       a1 a2)) = SOME z`)
  CHEAT_TAC;;

(* Binary (two-argument) instance of AllocVar_thm_nary, used by assign_RefArray. *)
let AllocVar_thm_binary = cake_theorem "AllocVar_thm_binary[local]"
  (fun () ->
    `!c l1 l2 s (t:('a,'c,'ffi)wordSem_state) locs a1 a2 x' xa i vv
  limit' q r.
       state_rel c l1 l2 s t NONE locs /\
       dataSem_cut_env (list_insert [a1; a2] x') (state_locals s) =
         SOME xa /\
       get_vars [a1; a2] (state_locals s) = SOME [Number (&i); vv]
         /\
       get_var 1 t = SOME (wordLang_Word (n2w (4 * i))) /\
       4 * i < dimword (:'a) /\
       evaluate (AllocVar c limit' (list_insert [a1; a2] x'),t) =
         (q,r) /\
       limit' < dimword (:'a) DIV 8 ==>
       (q = SOME wordSem_NotEnoughSpace ==> state_ffi
          r = state_ffi s /\ option_le (state_stack_max r)
            (state_stack_max s) /\
          (~(data_to_word_config_gc_kind c = None) /\ i < limit' /\
            no_thunks_in_refs (state_refs s) ==> limits_heap_limit
            (dataSem_state_limits
             s) <
               size_of_heap_args [Number (&i); vv] (cut_locals x'
                 s) + (i + 1))) /\
       (~(q = SOME wordSem_NotEnoughSpace) ==>
          i < limit' /\
          state_rel c l1 l2
            (dataSem_state_space_fupd (K (i + 1))
              (state_locals_fupd (K xa) s)) r NONE locs /\
          FLOOKUP (wordSem_state_store r) (Temp (n2w 29)) = FLOOKUP
            (wordSem_state_store t) (Temp (n2w 29)) /\ state_code
          r = state_code t /\ state_code_buffer r =
            state_code_buffer t /\ wordSem_state_data_buffer
          r = wordSem_state_data_buffer t /\ compile_oracle r =
            compile_oracle t /\
          q = NONE)`)
  CHEAT_TAC;;

let assign_RefArray = cake_theorem "assign_RefArray"
  (fun () ->
    `op = closLang_MemOp closLang_RefArray ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let LENGTH_n2mw_1 = cake_theorem "LENGTH_n2mw_1[local]"
  (fun () ->
    `LENGTH ((n2mw n):('a word) list) = 1 <=> ~(n = 0) /\ n < dimword
  (:'a)`)
  CHEAT_TAC;;

let WordFromInt_DIV_LEMMA = cake_theorem "WordFromInt_DIV_LEMMA[local]"
  (fun () ->
    `kk < B * B /\ 0 < B ==> B * (kk DIV B) <= B * B - B`)
  CHEAT_TAC;;

let explode_less_32 = cake_theorem "explode_less_32[local]"
  (fun () ->
    `(!n. n < 32 ==> P (n:num)) <=>
     P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\ P 6 /\ P 7 /\ P 8 /\
       P 9 /\
     P 10 /\ P 11 /\ P 12 /\ P 13 /\ P 14 /\ P 15 /\ P 16 /\ P 17
       /\ P 18 /\ P 19 /\
     P 20 /\ P 21 /\ P 22 /\ P 23 /\ P 24 /\ P 25 /\ P 26 /\ P 27
       /\ P 28 /\ P 29 /\
     P 30 /\ P 31`)
  CHEAT_TAC;;

let LESS_IMP_NOT_BIT = cake_theorem "LESS_IMP_NOT_BIT[local]"
  (fun () ->
    `!k n. n < 2 EXP k ==> ~(BIT k n)`)
  CHEAT_TAC;;

let smallnum_alt = cake_theorem "Smallnum_alt"
  (fun () ->
    `Smallnum i =
      (if i < (&0) then ((n2w 0) - n2w (num_of_int (--i))) << 2
        else n2w (num_of_int i) << 2)`)
  CHEAT_TAC;;

let BIT_lemma = cake_theorem "BIT_lemma[local]"
  (fun () ->
    `BIT n (2 EXP k - i) <=> (if n < k /\ i < 2 EXP k /\ ~(i = 0) then
  BIT n (2 EXP (MAX n i + 1) - i) else BIT n (2 EXP k - i))`)
  CHEAT_TAC;;

let BIT_Lemma2 = cake_theorem "BIT_Lemma2[local]"
  (fun () ->
    `BIT m (2 EXP k - n) = (if ~(n = 0) /\ n <= 2 EXP m /\ m < k then
  T else BIT m (2 EXP k - n))`)
  CHEAT_TAC;;

let assign_WordFromInt = cake_theorem "assign_WordFromInt"
  (fun () ->
    `op = closLang_WordOp WordFromInt ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_TagEq = cake_theorem "assign_TagEq"
  (fun () ->
    `(?tag. op = closLang_BlockOp (closLang_TagEq tag)) ==> (state_rel c
  l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let all_ones_get_addr = cake_theorem "all_ones_get_addr"
  (fun () ->
    `all_ones (data_to_word_config_len_bits c +
  (data_to_word_config_tag_bits c + 1)) 0 &&
     get_addr c ptr (wordLang_Word (ptr_bits c tag2 len2)) =
     ptr_bits c tag2 len2 || (n2w 1)`)
  CHEAT_TAC;;

let MULT_TWO_EXP_LESS_dimword = cake_theorem "MULT_TWO_EXP_LESS_dimword"
  (fun () ->
    `!b l n.
       b + l <= dimindex (:'a) /\ n < 2 EXP b ==>
       n * 2 EXP l < dimword (:'a)`)
  CHEAT_TAC;;

let maxout_bits_eq = cake_theorem "maxout_bits_eq"
  (fun () ->
    `b + l <= dimindex (:'a) /\ n' < 2 EXP b - 1 ==>
     (maxout_bits n b l = (maxout_bits n' b l:'a word) <=> n =
       n')`)
  CHEAT_TAC;;

let word_or_eq_word_or_split = cake_theorem "word_or_eq_word_or_split"
  (fun () ->
    `w1 && w2 = (n2w 0) /\ v1 && v2 = (n2w 0) /\
     w1 && v2 = (n2w 0) /\ v1 && w2 = (n2w 0) ==>
     ((w1 || w2 = v1 || v2) <=> (w1 = v1 /\ w2 = v2))`)
  CHEAT_TAC;;

let ptr_bits_eq_ptr_bits = cake_theorem "ptr_bits_eq_ptr_bits"
  (fun () ->
    `tag < 2 EXP data_to_word_config_tag_bits c - 1 /\
     len < 2 EXP data_to_word_config_len_bits c - 1 /\
       data_to_word_config_len_bits
     c + data_to_word_config_tag_bits c < dimindex (:'a) ==>
     ((ptr_bits c tag2 len2 || (n2w 1) =
       ptr_bits c tag len || ((n2w 1):'a word)) <=>
      (tag2 = tag /\ len2 = len))`)
  CHEAT_TAC;;

let maxout_bits_0 = cake_theorem "maxout_bits_0"
  (fun () ->
    `maxout_bits 0 b e = (n2w 0)`)
  CHEAT_TAC;;

let ptr_bits_eq_ptr_bits_len_only =
  cake_theorem "ptr_bits_eq_ptr_bits_len_only"
  (fun () ->
    `len < 2 EXP data_to_word_config_len_bits c - 1 /\
  data_to_word_config_len_bits
     c < dimindex (:'a) ==>
     ((ptr_bits c 0 len2 || (n2w 1) =
       ptr_bits c 0 len || ((n2w 1):'a word)) <=>
      (len2 = len))`)
  CHEAT_TAC;;

let assign_TagLenEq = cake_theorem "assign_TagLenEq"
  (fun () ->
    `(?tag len. op = closLang_BlockOp (closLang_TagLenEq tag len)) ==>
  (state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let all_ones_and_1 = cake_theorem "all_ones_and_1"
  (fun () ->
    `~(k = 0) ==> all_ones k 0 && (n2w 1) = (n2w 1)`)
  CHEAT_TAC;;

let all_ones_and_ptr_bits_tag_0 =
  cake_theorem "all_ones_and_ptr_bits_tag_0"
  (fun () ->
    `all_ones (data_to_word_config_len_bits c + 1) 0 && ptr_bits c tag
  len = ptr_bits c 0 len`)
  CHEAT_TAC;;

let assign_LenEq = cake_theorem "assign_LenEq"
  (fun () ->
    `(?len. op = closLang_BlockOp (closLang_LenEq len)) ==> (state_rel c
  l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let state_rel_upd_safe_pkheap = cake_theorem "state_rel_upd_safe_pkheap"
  (fun () ->
    `!c l1 l2 s lcl hpk r locs. state_rel c l1 l2 (state_stack_max_fupd
  (K NONE) (dataSem_state_space_fupd (K 0) (state_locals_fupd (K lcl)
  s)))
                  r NONE locs <=>
     state_rel c l1 l2
                  (dataSem_state_peak_heap_length_fupd (K hpk)
                    (dataSem_state_safe_for_space_fupd (K F)
                    (dataSem_state_space_fupd (K 0)
                    (state_stack_max_fupd (K NONE) (state_locals_fupd (K
                    lcl) s)))))
                  r NONE locs`)
  CHEAT_TAC;;

(* HOL4 data_to_word_assignProofScript.sml:9692-9693: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:9695-9696: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:9698-9699: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:9701-9702: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:9704-9705: ML code, not
   ported *)

let state_rel_ignore_safe_for_space =
  cake_theorem "state_rel_ignore_safe_for_space[simp]"
  (fun () ->
    `state_rel c l1 l2 (dataSem_state_safe_for_space_fupd (K m)
  (dataSem_state_space_fupd (K s) (state_locals_fupd (K l) x))) r t locs
  <=>
     state_rel c l1 l2 (dataSem_state_space_fupd (K s)
       (state_locals_fupd (K l) x)) r t locs`)
  CHEAT_TAC;;

let state_rel_peak_heap_length =
  cake_theorem "state_rel_peak_heap_length[simp]"
  (fun () ->
    `state_rel c l1 l2 (dataSem_state_peak_heap_length_fupd (K m)
  (dataSem_state_space_fupd (K s) (state_locals_fupd (K l) x))) r t locs
  <=>
     state_rel c l1 l2 (dataSem_state_space_fupd (K s)
       (state_locals_fupd (K l) x)) r t locs`)
  CHEAT_TAC;;

let data_to_word_assignProof_opt_map_plus_zero_id =
  cake_theorem "opt_map_plus_zero_id[simp]"
  (fun () ->
    `!n. OPTION_MAP2 (+) (SOME 0) n = (n:num option)`)
  CHEAT_TAC;;

let small_num_small_int = cake_theorem "small_num_small_int[simp]"
  (fun () ->
    `good_dimindex (:'a) ==>
     small_num (dimindex (:'a) = 64) = small_int (:'a)`)
  CHEAT_TAC;;

let memory_rel_small_int = cake_theorem "memory_rel_small_int"
  (fun () ->
    `memory_rel c be ts refs sp st m dm ((Number i,wordLang_Word (w:'a
  word)) :: vars) /\
     word_bit 0 w /\ good_dimindex (:'a) ==>
     ~(small_int (:'a) i)`)
  CHEAT_TAC;;

let small_int_Smallnum_add = cake_theorem "small_int_Smallnum_add"
  (fun () ->
    `good_dimindex (:'a) /\ small_int (:'a) (i1 + i2) ==>
     Smallnum i1 + ((Smallnum i2):'a word) = Smallnum (i1 + i2)`)
  CHEAT_TAC;;

let small_int_INT_MIN_MAX = cake_theorem "small_int_INT_MIN_MAX"
  (fun () ->
    `good_dimindex (:'a) /\ small_int (:'a) i ==>
     (INT_MIN (:'a) <= (&4) * i /\ (&4) * i <= INT_MAX (:'a))`)
  CHEAT_TAC;;

let small_int_w2i_Smallnum_add =
  cake_theorem "small_int_w2i_Smallnum_add"
  (fun () ->
    `good_dimindex (:'a) /\
     small_int (:'a) (i1 + i2) /\
     small_int (:'a) i1 /\
     small_int (:'a) i2 ==>
     w2i (Smallnum i1 + ((Smallnum i2):'a word)) = w2i (Smallnum
       i1:'a word) + w2i (Smallnum i2:'a word)`)
  CHEAT_TAC;;

(* TODO: move? *)
let data_to_word_assignProof_OPTION_MAP2_NONE =
  cake_theorem "OPTION_MAP2_NONE[simp]"
  (fun () ->
    `(OPTION_MAP2 f NONE n = NONE) /\ (OPTION_MAP2 f n NONE = NONE)`)
  CHEAT_TAC;;

let state_rel_IMP_arch_64_bit = cake_theorem "state_rel_IMP_arch_64_bit"
  (fun () ->
    `state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) xs locs ==>
     (limits_arch_64_bit (dataSem_state_limits s) = (dimindex
       (:'a) = 64))`)
  CHEAT_TAC;;

let cut_state_opt_twice = cake_theorem "cut_state_opt_twice"
  (fun () ->
    `dataSem_cut_state_opt names_opt s = SOME x ==>
     dataSem_cut_state_opt names_opt x = SOME x`)
  CHEAT_TAC;;

let cut_state_opt_extra_const = cake_theorem "cut_state_opt_extra_const"
  (fun () ->
    `dataSem_cut_state_opt names_opt s = SOME x ==>
  dataSem_state_stack_frame_sizes
     s = dataSem_state_stack_frame_sizes x /\ state_locals_size
     s = state_locals_size x`)
  CHEAT_TAC;;

let assign_Add = cake_theorem "assign_Add"
  (fun () ->
    `op = closLang_IntOp closLang_Add ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let small_int_Smallnum_sub = cake_theorem "small_int_Smallnum_sub"
  (fun () ->
    `good_dimindex (:'a) /\ small_int (:'a) (i1 - i2) ==>
     Smallnum i1 - ((Smallnum i2):'a word) = Smallnum (i1 - i2)`)
  CHEAT_TAC;;

let small_int_w2i_Smallnum_sub =
  cake_theorem "small_int_w2i_Smallnum_sub"
  (fun () ->
    `good_dimindex (:'a) /\ small_int (:'a) (i1 - i2) /\ small_int (:'a)
  i1 /\ small_int (:'a) i2 ==>
     w2i (Smallnum i1 - ((Smallnum i2):'a word)) = w2i (Smallnum
       i1:'a word) - w2i (Smallnum i2:'a word)`)
  CHEAT_TAC;;

let word_bit_0_sub_lemma = cake_theorem "word_bit_0_sub_lemma[local]"
  (fun () ->
    `!w1 (w2:'a word). ~(word_bit 0 w1) /\ ~(word_bit 0 w2) ==>
  ~(word_bit 0 (w1 + --(n2w 1) * w2))`)
  CHEAT_TAC;;

let assign_Sub = cake_theorem "assign_Sub"
  (fun () ->
    `op = closLang_IntOp closLang_Sub ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let cut_state_opt_IMP_ffi = cake_theorem "cut_state_opt_IMP_ffi"
  (fun () ->
    `dataSem_cut_state_opt names_opt s = SOME x ==> state_ffi x =
  state_ffi s`)
  CHEAT_TAC;;

let quad_times_div_half_double =
  cake_theorem "quad_times_div_half_double"
  (fun () ->
    `(4 * j) DIV 2 = 2 * (j:num)`)
  CHEAT_TAC;;

let w2n_mul_less = cake_theorem "w2n_mul_less"
  (fun () ->
    `!w w'.
       (w2n (w:'a word) * w2n (w':'a word)) < dimword (:'a) EXP 2`)
  CHEAT_TAC;;

let assign_Mult = cake_theorem "assign_Mult"
  (fun () ->
    `op = closLang_IntOp closLang_Mult ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let word_bit_lsr_dimindex_1 = cake_theorem "word_bit_lsr_dimindex_1"
  (fun () ->
    `word_bit 0 ((w1 >>> (dimindex (:'a) - 1)):'a word) <=> word_msb
  w1`)
  CHEAT_TAC;;

let state_rel_Number_IMP = cake_theorem "state_rel_Number_IMP"
  (fun () ->
    `state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      get_var a1 (state_locals s) = SOME (Number i1) /\
      sptree_lookup (adjust_var a1) (state_locals t) = SOME v1 ==>
      (?w1. (v1 = wordLang_Word w1) /\
           (~(word_bit 0 w1) <=> small_int (:'a) i1) /\
           (~(word_msb w1) /\ ~(word_bit 0 w1) ==> (&0) <= i1 /\
             w1 = n2w (4 * num_of_int i1)))`)
  CHEAT_TAC;;

let option_le_add_comm = cake_theorem "option_le_add_comm"
  (fun () ->
    `option_le (OPTION_MAP2 (+) a b) c ==>
       option_le (OPTION_MAP2 (+) b a) c`)
  CHEAT_TAC;;

let IN_adjust_set_IN = cake_theorem "IN_adjust_set_IN"
  (fun () ->
    `y IN domain (adjust_set x) ==> (y - 2) DIV 2 IN domain x`)
  CHEAT_TAC;;

let assign_Div = cake_theorem "assign_Div"
  (fun () ->
    `op = closLang_IntOp closLang_Div ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_Mod = cake_theorem "assign_Mod"
  (fun () ->
    `op = (closLang_IntOp closLang_Mod) ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_LengthByte = cake_theorem "assign_LengthByte"
  (fun () ->
    `op = closLang_MemOp closLang_LengthByte ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_Length = cake_theorem "assign_Length"
  (fun () ->
    `op = closLang_MemOp closLang_Length ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_LengthBlock = cake_theorem "assign_LengthBlock"
  (fun () ->
    `op = closLang_BlockOp closLang_LengthBlock ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_BoundsCheckBlock = cake_theorem "assign_BoundsCheckBlock"
  (fun () ->
    `assign c secn l dest (closLang_BlockOp closLang_BoundsCheckBlock)
  args names =
        (match args with [v1; v2] -> (list_Seq [If Test (adjust_var
          v1) (Imm (n2w 1))
                              (Assign 1 (wordLang_Const (n2w 0)))
                              (Assign 1
                              (let addr' = real_addr c (adjust_var
                                v1) in
                              let header = Load addr' in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c in
                              (\sh e n. Shift sh e (wordLang_Const
                                (n2w n))) Lsr header k));
                              Assign 3 (ShiftVar Ror (adjust_var
                                v2) 2);
                              If asm_Lower 3 (Reg 1)
                              (Assign (adjust_var dest) (Const (n2w
                                18:'a word)))
                              (Assign (adjust_var dest) (Const
                                (n2w 2:'a word)))],l) | _12 ->
                                ((Skip:'a wordLang_prog),l))`)
  CHEAT_TAC;;

let data_to_word_assignProof_assign_BoundsCheckBlock =
  cake_theorem "assign_BoundsCheckBlock[allow_rebind]"
  (fun () ->
    `op = closLang_BlockOp closLang_BoundsCheckBlock ==> (state_rel c l1
  l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
     (~(op_requires_names op = (names_opt = NONE))) /\
     cut_state_opt names_opt s = SOME x /\
     get_vars args (state_locals s) = SOME vals /\
       wordSem_state_termdep
     t > 1 /\
     do_app op vals x = Rval (v,s2) ==>
     (?q r.
       evaluate (FST (assign c n l dest op args names_opt),t) =
         (q,r) /\
       (q = SOME wordSem_NotEnoughSpace ==> state_ffi
        r = state_ffi t /\ option_le (state_stack_max r)
          (state_stack_max s2) /\
        (~(data_to_word_config_gc_kind c = None) ==>
          ~(dataSem_state_safe_for_space s2))) /\
       (~(q = SOME wordSem_NotEnoughSpace) ==>
        state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
          NONE)))`)
  CHEAT_TAC;;

let assign_BoundsCheckArray = cake_theorem "assign_BoundsCheckArray"
  (fun () ->
    `assign c secn l dest (closLang_MemOp closLang_BoundsCheckArray)
  args names =
        (match args with [v1; v2] -> (list_Seq [Assign 1
                              (let addr' = real_addr c (adjust_var
                                v1) in
                              let header = Load addr' in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c in
                              (\sh e n. Shift sh e (wordLang_Const
                                (n2w n))) Lsr header k);
                              Assign 3 (ShiftVar Ror (adjust_var
                                v2) 2);
                              If asm_Lower 3 (Reg 1)
                              (Assign (adjust_var dest) (Const (n2w
                                18:'a word)))
                              (Assign (adjust_var dest) (Const
                                (n2w 2:'a word)))],l) | _13 ->
                                ((Skip:'a wordLang_prog),l))`)
  CHEAT_TAC;;

let data_to_word_assignProof_assign_BoundsCheckArray =
  cake_theorem "assign_BoundsCheckArray[allow_rebind]"
  (fun () ->
    `op = closLang_MemOp closLang_BoundsCheckArray ==> (state_rel c l1
  l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_BoundsCheckByte = cake_theorem "assign_BoundsCheckByte"
  (fun () ->
    `assign c secn l dest (closLang_MemOp (closLang_BoundsCheckByte
  leq)) args names =
        (match args with [v1; v2] -> (list_Seq [Assign 1
                              (let addr' = real_addr c (adjust_var
                                v1) in
                              let header = Load addr' in
                              let extra = (if dimindex (:'a) = 32
                                then 2 else 3) in
                              let k = dimindex (:'a) -
                                data_to_word_config_len_size c - extra
                                in
                              Op Sub [(\sh e n. Shift sh e
                                (wordLang_Const (n2w n))) Lsr header k;
                                Const bytes_in_word]);
                              Assign 3 (ShiftVar Ror (adjust_var
                                v2) 2);
                              (if leq then If asm_NotLower 1 (Reg
                                3) else
                              If asm_Lower 3 (Reg 1))
                              (Assign (adjust_var dest) (Const (n2w
                                18:'a word)))
                              (Assign (adjust_var dest) (Const
                                (n2w 2:'a word)))],l) | _14 ->
                                ((Skip:'a wordLang_prog),l))`)
  CHEAT_TAC;;

let data_to_word_assignProof_assign_BoundsCheckByte =
  cake_theorem "assign_BoundsCheckByte[allow_rebind]"
  (fun () ->
    `(?leq. op = closLang_MemOp (closLang_BoundsCheckByte leq)) ==>
  (state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_LessConstSmall = cake_theorem "assign_LessConstSmall"
  (fun () ->
    `assign c secn l dest (closLang_IntOp (closLang_LessConstSmall i))
  args names =
        (match args with [v1] -> (If Less (adjust_var v1) (Imm (n2w
          (4 * i)))
                    (Assign (adjust_var dest) (Const (n2w 18:'a
                      word)))
                    (Assign (adjust_var dest) (Const (n2w 2:'a
                      word))),l) | _15 -> ((Skip:'a wordLang_prog),l))`)
  CHEAT_TAC;;

let assign_LessSmallConst =
  cake_theorem "assign_LessSmallConst[allow_rebind]"
  (fun () ->
    `(?i. op = closLang_IntOp (closLang_LessConstSmall i)) ==>
  (state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_BoolNot = cake_theorem "assign_BoolNot[allow_rebind]"
  (fun () ->
    `op = closLang_BlockOp closLang_BoolNot ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_BoolTest = cake_theorem "assign_BoolTest[allow_rebind]"
  (fun () ->
    `(?test. op = closLang_BlockOp (closLang_BoolTest test)) ==>
  (state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_WordTest = cake_theorem "assign_WordTest[allow_rebind]"
  (fun () ->
    `(?ws test. op = closLang_WordOp (WordTest ws test)) ==> (state_rel
  c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let compare1_code_thm = cake_theorem "Compare1_code_thm"
  (fun () ->
    `!l a1 a2 dm m res (t:('a,'c,'ffi)wordSem_state).
        word_cmp_loop l a1 a2 dm m = SOME res /\
        dm = wordSem_state_mdomain t /\
        m = wordSem_state_memory t /\
        sptree_lookup Compare1_location (state_code t) = SOME
          (4,Compare1_code) /\
        sptree_lookup Compare1_location (wordSem_state_stack_size
          t) = state_locals_size t /\
        get_var 0 t = SOME (Loc l1 l2) /\
        get_var 2 t = SOME (wordLang_Word l) /\
        get_var 4 t = SOME (wordLang_Word a1) /\
        get_var 6 t = SOME (wordLang_Word a2) /\
        w2n l <= state_clock t ==>
        (?ck smx.
          evaluate (Compare1_code,t) =
            (SOME (wordSem_Result (wordLang_Loc l1 l2)
              [wordLang_Word res]),state_stack_max_fupd (K smx)
              (state_locals_size_fupd (K (SOME 0)) (state_locals_fupd (K
              LN) (state_clock_fupd (K ck)
             t)))) /\
          option_le smx (OPTION_MAP2 MAX (state_stack_max t)
                              (OPTION_MAP2 (+) (stack_size (stack
                                t)) (state_locals_size t))) /\
                                state_clock
          t <= w2n l + ck)`)
  CHEAT_TAC;;

let word_exp_insert = cake_theorem "word_exp_insert"
  (fun () ->
    `(~(m = n) ==>
       (wordSem_word_exp (state_locals_fupd (K (insert n w
         (state_locals t))) t) (real_addr c m) =
        wordSem_word_exp t (real_addr c m))) /\
      (~(m IN {n,n1}) ==>
       (wordSem_word_exp (state_locals_fupd (K (insert n w (insert
         n1 w1 (state_locals t)))) t) (real_addr c m) =
        wordSem_word_exp t (real_addr c m)))`)
  CHEAT_TAC;;

let compare_code_thm = cake_theorem "Compare_code_thm"
  (fun () ->
    `memory_rel c be ts refs sp st m dm
        ((Number i1,wordLang_Word v1) :: (Number i2,wordLang_Word
          v2) :: vars) /\
      dm = wordSem_state_mdomain (t:('a,'c,'ffi)wordSem_state) /\
      m = wordSem_state_memory t /\
      st = wordSem_state_store t /\
      (~(word_bit 0 v1) ==> word_bit 0 v2) /\
      shift_length c < dimindex (:'a) /\
      sptree_lookup Compare1_location (state_code t) = SOME
        (4,Compare1_code) /\
      get_var 0 t = SOME (Loc l1 l2) /\
      get_var 2 t = SOME (wordLang_Word (v1:'a word)) /\
      get_var 4 t = SOME (wordLang_Word (v2:'a word)) /\
      dimword (:'a) < state_clock t /\
        ~(data_to_word_config_len_size
      c = 0) /\ data_to_word_config_len_size
      c < dimindex (:'a) /\
      good_dimindex (:'a) ==>
      (?ck smx.
        evaluate (Compare_code c,t) =
          (SOME (wordSem_Result (wordLang_Loc l1 l2) [wordLang_Word
            (word_cmp_res i1 i2)]),state_stack_max_fupd (K smx)
            (state_locals_size_fupd (K (SOME 0)) (state_locals_fupd (K
            LN) (state_clock_fupd (K ck)
           t)))) /\
          option_le smx (OPTION_MAP2 MAX (state_stack_max
                           t)
                             (OPTION_MAP2 (+) (stack_size (stack
                               t))
                              (sptree_lookup Compare1_location
                                (wordSem_state_stack_size t)))))`)
  CHEAT_TAC;;

let word_cmp_Less_word_cmp_res =
  cake_theorem "word_cmp_Less_word_cmp_res"
  (fun () ->
    `!i i'. good_dimindex (:'a) ==>
             (word_cmp Less (word_cmp_res i i') ((n2w 1):'a word)
               <=> i < i')`)
  CHEAT_TAC;;

let word_cmp_NotLess_word_cmp_res =
  cake_theorem "word_cmp_NotLess_word_cmp_res"
  (fun () ->
    `!i i'. good_dimindex (:'a) ==>
             (word_cmp asm_NotLess ((n2w 1):'a word)
               (word_cmp_res i i') <=> (i <= i'))`)
  CHEAT_TAC;;

let word_cmp_not_NotLess_word_cmp_res =
  cake_theorem "word_cmp_not_NotLess_word_cmp_res"
  (fun () ->
    `!i i'. good_dimindex (:'a) ==>
             (~(word_cmp asm_NotLess ((n2w 1):'a word)
               (word_cmp_res i i')) <=> (i' < i))`)
  CHEAT_TAC;;

let not_word_cmp_Less_word_cmp_res =
  cake_theorem "not_word_cmp_Less_word_cmp_res"
  (fun () ->
    `!i i'. good_dimindex (:'a) ==>
             (~(word_cmp Less (word_cmp_res i i') ((n2w 1):'a
               word)) <=> (i' <= i))`)
  CHEAT_TAC;;

let IMP_spt_eq = cake_theorem "IMP_spt_eq"
  (fun () ->
    `sptree_wf t1 /\ sptree_wf t2 /\ (!n. sptree_lookup n t1 =
  sptree_lookup n t2) ==> (t1 = t2)`)
  CHEAT_TAC;;

let env_to_list_cut_env_IMP = cake_theorem "env_to_list_cut_env_IMP"
  (fun () ->
    `env_to_list x (wordSem_state_permute t) = (l,permute) /\ cut_env y
  s = SOME x ==>
      (fromAList l = x)`)
  CHEAT_TAC;;

let dimword_LESS_MustTerminate_limit =
  cake_theorem "dimword_LESS_MustTerminate_limit"
  (fun () ->
    `good_dimindex (:'a) ==> dimword (:'a) < MustTerminate_limit (:'a)
  - 1`)
  CHEAT_TAC;;

let assign_Less = cake_theorem "assign_Less"
  (fun () ->
    `op = closLang_IntOp closLang_Less ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_LessEq = cake_theorem "assign_LessEq"
  (fun () ->
    `op = closLang_IntOp closLang_LessEq ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let word_exp_set_var_ShiftVar = cake_theorem "word_exp_set_var_ShiftVar"
  (fun () ->
    `wordSem_word_exp (set_var v (wordLang_Word w) t) (ShiftVar sow v n)
  =
      OPTION_MAP wordLang_Word (match sow with Lsl -> SOME (w <<
        n) | Lsr -> SOME (w >>> n) | Asr -> SOME (w >> n) | Ror ->
        SOME (word_ror w n))`)
  CHEAT_TAC;;

let MemEqList_thm = cake_theorem "MemEqList_thm[local]"
  (fun () ->
    `!offset t xs dm m b a.
         word_mem_eq (a + offset) xs dm m = SOME b /\
         get_var 3 t = SOME (wordLang_Word a) /\ dm =
           wordSem_state_mdomain t /\ m = wordSem_state_memory t ==>
         (?x. evaluate (MemEqList offset xs,t) =
               (NONE,state_locals_fupd (K (((if b then insert 1
                 (wordLang_Word (n2w 18)) else I) o
                              (if ~(xs = []) then insert 5 x else
                                I)) (state_locals t))) t))`)
  CHEAT_TAC;;
(* HOL4 data_to_word_assignProofScript.sml:12206-12207: a theorem
   that HOL4 states as the value of an ML expression: MemEqList_thm *)

let assign_EqualConst = cake_theorem "assign_EqualConst"
  (fun () ->
    `(?p. op = closLang_BlockOp (closLang_EqualConst p)) ==> (state_rel
  c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

(* TODO: move to backendProps *)
let option_map_mult_suc = cake_theorem "option_map_mult_suc"
  (fun () ->
    `OPTION_MAP ((*) (SUC n)) m =
     OPTION_MAP2 (+) m (OPTION_MAP ((*) n) m)`)
  CHEAT_TAC;;

let eq_code_stack_max_sub1 = cake_theorem "eq_code_stack_max_sub1"
  (fun () ->
    `~(l = 0) ==>
       eq_code_stack_max l tsz =
       OPTION_MAP2 ((+))
         (OPTION_MAP2 MAX
           (sptree_lookup Equal_location tsz)
           (OPTION_MAP2 MAX
             (sptree_lookup Equal1_location tsz)
             (sptree_lookup Compare1_location tsz)))
         (eq_code_stack_max (l - 1) tsz)`)
  CHEAT_TAC;;

let eq_code_stack_max_le_mono = cake_theorem "eq_code_stack_max_le_mono"
  (fun () ->
    `a <= b ==>
     option_le (eq_code_stack_max a tsz) (eq_code_stack_max b
       tsz)`)
  CHEAT_TAC;;

let sane_locals_size_def = cake_define
  `sane_locals_size t = (state_locals_size t = sptree_lookup
  Equal_location (wordSem_state_stack_size t) \/ state_locals_size
                         t = sptree_lookup Equal1_location
                           (wordSem_state_stack_size t))`;;

let equal_code_lemma = cake_theorem "Equal_code_lemma"
  (fun () ->
    `(!c st dm m l wck v1 v2 t l1 l2 res l' wck'.
        word_eq c st dm m l wck v1 v2 = SOME (res,l',wck') /\
        dm = wordSem_state_mdomain (t:('a,'c,'ffi)wordSem_state) /\
        m = wordSem_state_memory t /\
        st = wordSem_state_store t /\
        l <= state_clock t /\
        shift_length c < dimindex (:'a) /\
        sptree_lookup Equal_location (state_code t) = SOME
          (3,Equal_code c) /\
        sptree_lookup Equal1_location (state_code t) = SOME
          (4,Equal1_code) /\
        sptree_lookup Compare1_location (state_code t) = SOME
          (4,Compare1_code) /\
        get_var 0 t = SOME (Loc l1 l2) /\
        get_var 2 t = SOME (wordLang_Word (v1:'a word)) /\
        get_var 4 t = SOME (wordLang_Word (v2:'a word)) /\
          ~(data_to_word_config_len_size
        c = 0) /\ data_to_word_config_len_size
        c < dimindex (:'a) /\
        sane_locals_size t /\
        good_dimindex (:'a) ==>
        (?ck new_p smx.
          evaluate (Equal_code c,t) =
           (SOME (wordSem_Result (wordLang_Loc l1 l2)
             [wordLang_Word res]),state_stack_max_fupd (K smx)
             (wordSem_state_permute_fupd (K new_p)
             (state_locals_size_fupd (K (SOME 0)) (state_locals_fupd (K
             LN) (state_clock_fupd (K ck)
            t))))) /\
          option_le smx (OPTION_MAP2 MAX (state_stack_max t)
                              (OPTION_MAP2 (+)
                              (stack_size (stack t))
                              (eq_code_stack_max (wck + 1)
                                (wordSem_state_stack_size t)))) /\
          l' <= ck)) /\
      (!c st dm m l wck w a1 a2 t l1 l2 res l' wck'.
        word_eq_list c st dm m l wck w a1 a2 = SOME (res,l',wck')
          /\
        dm = wordSem_state_mdomain (t:('a,'c,'ffi)wordSem_state) /\
        m = wordSem_state_memory t /\
        st = wordSem_state_store t /\
        l <= state_clock t /\
        shift_length c < dimindex (:'a) /\
        sptree_lookup Equal_location (state_code t) = SOME
          (3,Equal_code c) /\
        sptree_lookup Equal1_location (state_code t) = SOME
          (4,Equal1_code) /\
        sptree_lookup Compare1_location (state_code t) = SOME
          (4,Compare1_code) /\
        get_var 0 t = SOME (Loc l1 l2) /\
        get_var 2 t = SOME (wordLang_Word (w:'a word)) /\
        get_var 4 t = SOME (wordLang_Word (a1:'a word)) /\
        get_var 6 t = SOME (wordLang_Word (a2:'a word)) /\
        sane_locals_size t /\ ~(data_to_word_config_len_size
        c = 0) /\ data_to_word_config_len_size
        c < dimindex (:'a) /\
        good_dimindex (:'a) ==>
        (?ck new_p smx.
          evaluate (Equal1_code,t) =
            (SOME (wordSem_Result (wordLang_Loc l1 l2)
              [wordLang_Word res]),state_stack_max_fupd (K smx)
              (wordSem_state_permute_fupd (K new_p)
              (state_locals_size_fupd (K (SOME 0)) (state_locals_fupd (K
              LN) (state_clock_fupd (K ck)
             t))))) /\
          option_le smx (OPTION_MAP2 MAX (state_stack_max t)
                              (OPTION_MAP2 (+)
                              (stack_size (stack t))
                              (eq_code_stack_max (wck + 1)
                                (wordSem_state_stack_size t)))) /\
          l' <= ck))`)
  CHEAT_TAC;;

let equal_code_thm = cake_theorem "Equal_code_thm"
  (fun () ->
    `word_eq c st dm m l wck v1 v2 = SOME (res,l',wck') /\
     dm = wordSem_state_mdomain (t:('a,'c,'ffi)wordSem_state) /\
     m = wordSem_state_memory t /\
     st = wordSem_state_store t /\
     l <= state_clock t /\
     shift_length c < dimindex (:'a) /\ state_locals_size
     t = sptree_lookup Equal_location (wordSem_state_stack_size t)
       /\
     sptree_lookup Equal_location (state_code t) = SOME
       (3,Equal_code c) /\
     sptree_lookup Equal1_location (state_code t) = SOME
       (4,Equal1_code) /\
     sptree_lookup Compare1_location (state_code t) = SOME
       (4,Compare1_code) /\
     get_var 0 t = SOME (Loc l1 l2) /\
     get_var 2 t = SOME (wordLang_Word (v1:'a word)) /\
     get_var 4 t = SOME (wordLang_Word (v2:'a word)) /\
       ~(data_to_word_config_len_size
     c = 0) /\ data_to_word_config_len_size
     c < dimindex (:'a) /\
     good_dimindex (:'a) ==>
     (?ck new_p smx.
       evaluate (Equal_code c,t) =
         (SOME (wordSem_Result (wordLang_Loc l1 l2) [wordLang_Word
           res]),state_stack_max_fupd (K smx)
           (wordSem_state_permute_fupd (K new_p) (state_locals_size_fupd
           (K (SOME 0)) (state_locals_fupd (K LN) (state_clock_fupd (K
           ck)
          t))))) /\
       option_le smx (OPTION_MAP2 MAX (state_stack_max t)
                              (OPTION_MAP2 (+)
                              (stack_size (stack t))
                              (eq_code_stack_max (wck + 1)
                                (wordSem_state_stack_size t)))) /\
       l' <= ck)`)
  CHEAT_TAC;;

let data_to_word_assignProof_MIN_SUB = cake_theorem "MIN_SUB[local]"
  (fun () ->
    `MIN a b - c = MIN (a - c) (b - c)`)
  CHEAT_TAC;;

let assign_Equal = cake_theorem "assign_Equal"
  (fun () ->
    `op = closLang_BlockOp closLang_Equal ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_WordOpW8 = cake_theorem "assign_WordOpW8"
  (fun () ->
    `(?opw. op = closLang_WordOp (WordOpw ast_W8 opw)) ==> (state_rel c
  l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

(* HOL4 data_to_word_assignProofScript.sml:13152-13154: the ML values
   that the definitions below antiquote *)

let mw2n_2_IMP = cake_theorem "mw2n_2_IMP"
  (fun () ->
    `mw2n [w1; w2:'a word] = n ==>
      w2 = n2w (n DIV dimword (:'a)) /\
      w1 = n2w n`)
  CHEAT_TAC;;

let IMP_mw2n_2 = cake_theorem "IMP_mw2n_2"
  (fun () ->
    `Abbrev (x2 = (63 >< 32) (n2w n:word64)) /\
      Abbrev (x1 = (31 >< 0) (n2w n:word64)) /\
      n < dimword (:64) /\ dimindex (:'a) = 32 ==>
      mw2n [x1; x2:'a word] = n`)
  CHEAT_TAC;;

let evaluate_WordOp64_on_32 = cake_theorem "evaluate_WordOp64_on_32"
  (fun () ->
    `!l.
      dimindex (:'a) = 32 ==>
      (?w27 w29.
        evaluate
         (WordOp64_on_32 opw,state_locals_fupd (K
            (insert 23 (wordLang_Word ((31 >< 0) c''))
              (insert 21 (wordLang_Word ((63 >< 32) c''))
                 (insert 13 (wordLang_Word ((31 >< 0) c'))
                    (insert 11 (wordLang_Word ((63 >< 32) c'))
                      l)))))
          (t:('a,'c,'ffi)wordSem_state)) =
       (NONE,state_locals_fupd (K
         (insert 31 (wordLang_Word ((63 >< 32) (opw_lookup opw c'
           c'')))
          (insert 33 (wordLang_Word ((31 >< 0) (opw_lookup opw
            (c':word64) (c'':word64))))
            (insert 27 w27
              (insert 29 w29
                (insert 23 (wordLang_Word ((31 >< 0) c''))
                  (insert 21 (wordLang_Word ((63 >< 32) c''))
                    (insert 13 (wordLang_Word ((31 >< 0) c'))
                      (insert 11 (wordLang_Word ((63 >< 32) c'))
                        l))))))))) t))`)
  CHEAT_TAC;;

let IMP_encode_header_NOT_NONE =
  cake_theorem "IMP_encode_header_NOT_NONE"
  (fun () ->
    `dimindex (:'a) = 32 /\ 1 < data_to_word_config_len_size c /\ 1 <
  30 - data_to_word_config_len_size c ==> ~(encode_header c 3 2 =
  (NONE:('a word) option))`)
  CHEAT_TAC;;

let assign_WordOpW64 = cake_theorem "assign_WordOpW64"
  (fun () ->
    `(?opw. op = closLang_WordOp (WordOpw ast_W64 opw)) ==> (state_rel c
  l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_WordShiftW8 = cake_theorem "assign_WordShiftW8"
  (fun () ->
    `(?sh n. op = closLang_WordOp (WordShift ast_W8 sh n)) ==>
  (state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

(* HOL4 data_to_word_assignProofScript.sml:13734-13736: the ML values
   that the definitions below antiquote *)

let evaluate_WordShift64_on_32 =
  cake_theorem "evaluate_WordShift64_on_32"
  (fun () ->
    `!l.
      dimindex (:'a) = 32 ==>
        evaluate
         (WordShift64_on_32 sh n,state_locals_fupd (K
            (insert 13 (wordLang_Word ((31 >< 0) c'))
            (insert 11 (wordLang_Word ((63 >< 32) c')) l)))
          (t:('a,'c,'ffi)wordSem_state)) =
       (NONE,state_locals_fupd (K
         (insert 31 (wordLang_Word ((63 >< 32) (shift_lookup sh c'
           n)))
          (insert 33 (wordLang_Word ((31 >< 0) (shift_lookup sh
            (c':word64) n)))
            (insert 13 (wordLang_Word ((31 >< 0) c'))
              (insert 11 (wordLang_Word ((63 >< 32) c')) l)))))
                t)`)
  CHEAT_TAC;;

let assign_WordShiftW64 = cake_theorem "assign_WordShiftW64"
  (fun () ->
    `(?sh n. op = closLang_WordOp (WordShift ast_W64 sh n)) ==>
  (state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

(* HOL4 data_to_word_assignProofScript.sml:13990-13992: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:13994-13996: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:13998-14000: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:14002-14004: ML code, not
   ported *)

let w2w_select_id = cake_theorem "w2w_select_id"
  (fun () ->
    `dimindex (:'a) = 64 ==>
      ((w2w:'a word->word64) ((63 >< 0) w)) = w`)
  CHEAT_TAC;;

let extract_append_id = cake_theorem "extract_append_id"
  (fun () ->
    `dimindex (:'a) = 32 ==>
      ((((63 >< 32) w):'a word) @@ (((31 >< 0) w):'a word)) =
        (w:word64)`)
  CHEAT_TAC;;

let word1_cases = cake_theorem "word1_cases"
  (fun () ->
    `!(w:word1). w = (n2w 0) \/ w = (n2w 1)`)
  CHEAT_TAC;;

let w2w_w2w_64 = cake_theorem "w2w_w2w_64"
  (fun () ->
    `!w. dimindex (:'a) = 64 ==> w2w ((w2w w):'a word) = (w:word64)`)
  CHEAT_TAC;;

let fp_greater = cake_theorem "fp_greater[local]"
  (fun () ->
    `fp64_greaterThan a b = fp64_lessThan b a /\
     fp64_greaterEqual a b = fp64_lessEqual b a`)
  CHEAT_TAC;;

let assign_FP_cmp = cake_theorem "assign_FP_cmp"
  (fun () ->
    `(?fpc. op = closLang_WordOp (FP_cmp fpc)) ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_FP_top = cake_theorem "assign_FP_top"
  (fun () ->
    `(?fpt. op = closLang_WordOp (FP_top fpt)) ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_FP_bop = cake_theorem "assign_FP_bop"
  (fun () ->
    `(?fpb. op = closLang_WordOp (FP_bop fpb)) ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_FP_uop = cake_theorem "assign_FP_uop"
  (fun () ->
    `(?fpu. op = closLang_WordOp (FP_uop fpu)) ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_Label = cake_theorem "assign_Label"
  (fun () ->
    `(?lab. op = Label lab) ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let data_to_word_assignProof_do_app_Ref = cake_theorem "do_app_Ref"
  (fun () ->
    `do_app (closLang_MemOp closLang_Ref) vals x =
      (match consume_space (LENGTH vals + 1) x with
        NONE -> Rerr (Rabort Rtype_error) | SOME s1 ->
        Rval
        (RefPtr T (LEAST (\ptr. ~(ptr IN domain (state_refs
          s1)))),state_stack_max_fupd (K (state_stack_max
               (do_stack (closLang_MemOp closLang_Ref) vals
                 (do_lim_safe s1 (closLang_MemOp closLang_Ref) vals))))
                 (dataSem_state_safe_for_space_fupd (K
                 (dataSem_state_safe_for_space (do_stack (closLang_MemOp
                 closLang_Ref) vals (do_lim_safe s1 (closLang_MemOp
                 closLang_Ref) vals)))) (state_refs_fupd (K (insert
                 (LEAST (\ptr. ~(ptr IN domain (state_refs s1))))
                 (ValueArray vals) (state_refs s1)))
           s1))))`)
  CHEAT_TAC;;

let assign_Ref = cake_theorem "assign_Ref"
  (fun () ->
    `op = closLang_MemOp closLang_Ref ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
     (~(op_requires_names op = (names_opt = NONE))) /\
     cut_state_opt names_opt s = SOME x /\
     get_vars args (state_locals s) = SOME vals /\
       wordSem_state_termdep
     t > 1 /\
     do_app op vals x = Rval (v,s2) ==>
     (?q r.
       evaluate (FST (assign c n l dest op args names_opt),t) =
         (q,r) /\
       (q = SOME wordSem_NotEnoughSpace ==> state_ffi
        r = state_ffi t /\ option_le (state_stack_max r)
          (state_stack_max s2) /\
        (~(data_to_word_config_gc_kind c = None) ==>
          ~(dataSem_state_safe_for_space s2))) /\
       (~(q = SOME wordSem_NotEnoughSpace) ==>
        state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
          NONE)))`)
  CHEAT_TAC;;

let assign_Update = cake_theorem "assign_Update"
  (fun () ->
    `op = closLang_MemOp closLang_Update ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
     (~(op_requires_names op = (names_opt = NONE))) /\
     cut_state_opt names_opt s = SOME x /\
     get_vars args (state_locals s) = SOME vals /\
       wordSem_state_termdep
     t > 1 /\
     do_app op vals x = Rval (v,s2) ==>
     (?q r.
       evaluate (FST (assign c n l dest op args names_opt),t) =
         (q,r) /\
       (q = SOME wordSem_NotEnoughSpace ==> state_ffi
        r = state_ffi t /\ option_le (state_stack_max r)
          (state_stack_max s2) /\
        (~(data_to_word_config_gc_kind c = None) ==>
          ~(dataSem_state_safe_for_space s2))) /\
       (~(q = SOME wordSem_NotEnoughSpace) ==>
        state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
          NONE)))`)
  CHEAT_TAC;;

let assign_El = cake_theorem "assign_El"
  (fun () ->
    `op = closLang_MemOp closLang_El ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
     (~(op_requires_names op = (names_opt = NONE))) /\
     cut_state_opt names_opt s = SOME x /\
     get_vars args (state_locals s) = SOME vals /\
       wordSem_state_termdep
     t > 1 /\
     do_app op vals x = Rval (v,s2) ==>
     (?q r.
       evaluate (FST (assign c n l dest op args names_opt),t) =
         (q,r) /\
       (q = SOME wordSem_NotEnoughSpace ==> state_ffi
        r = state_ffi t /\ option_le (state_stack_max r)
          (state_stack_max s2) /\
        (~(data_to_word_config_gc_kind c = None) ==>
          ~(dataSem_state_safe_for_space s2))) /\
       (~(q = SOME wordSem_NotEnoughSpace) ==>
        state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
          NONE)))`)
  CHEAT_TAC;;

let assign_ElemAt = cake_theorem "assign_ElemAt"
  (fun () ->
    `(?n. op = closLang_BlockOp (closLang_ElemAt n)) ==> (state_rel c l1
  l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
     (~(op_requires_names op = (names_opt = NONE))) /\
     cut_state_opt names_opt s = SOME x /\
     get_vars args (state_locals s) = SOME vals /\
       wordSem_state_termdep
     t > 1 /\
     do_app op vals x = Rval (v,s2) ==>
     (?q r.
       evaluate (FST (assign c n l dest op args names_opt),t) =
         (q,r) /\
       (q = SOME wordSem_NotEnoughSpace ==> state_ffi
        r = state_ffi t /\ option_le (state_stack_max r)
          (state_stack_max s2) /\
        (~(data_to_word_config_gc_kind c = None) ==>
          ~(dataSem_state_safe_for_space s2))) /\
       (~(q = SOME wordSem_NotEnoughSpace) ==>
        state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
          NONE)))`)
  CHEAT_TAC;;

let assign_UpdateByte = cake_theorem "assign_UpdateByte"
  (fun () ->
    `op = closLang_MemOp closLang_UpdateByte ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
     (~(op_requires_names op = (names_opt = NONE))) /\
     cut_state_opt names_opt s = SOME x /\
     get_vars args (state_locals s) = SOME vals /\
       wordSem_state_termdep
     t > 1 /\
     do_app op vals x = Rval (v,s2) ==>
     (?q r.
       evaluate (FST (assign c n l dest op args names_opt),t) =
         (q,r) /\
       (q = SOME wordSem_NotEnoughSpace ==> state_ffi
        r = state_ffi t /\ option_le (state_stack_max r)
          (state_stack_max s2) /\
        (~(data_to_word_config_gc_kind c = None) ==>
          ~(dataSem_state_safe_for_space s2))) /\
       (~(q = SOME wordSem_NotEnoughSpace) ==>
        state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
          NONE)))`)
  CHEAT_TAC;;

let assign_DerefByte = cake_theorem "assign_DerefByte"
  (fun () ->
    `op = closLang_MemOp closLang_DerefByte ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
     (~(op_requires_names op = (names_opt = NONE))) /\
     cut_state_opt names_opt s = SOME x /\
     get_vars args (state_locals s) = SOME vals /\
       wordSem_state_termdep
     t > 1 /\
     do_app op vals x = Rval (v,s2) ==>
     (?q r.
       evaluate (FST (assign c n l dest op args names_opt),t) =
         (q,r) /\
       (q = SOME wordSem_NotEnoughSpace ==> state_ffi
        r = state_ffi t /\ option_le (state_stack_max r)
          (state_stack_max s2) /\
        (~(data_to_word_config_gc_kind c = None) ==>
          ~(dataSem_state_safe_for_space s2))) /\
       (~(q = SOME wordSem_NotEnoughSpace) ==>
        state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
          NONE)))`)
  CHEAT_TAC;;

let assign_Const = cake_theorem "assign_Const"
  (fun () ->
    `(?i. op = closLang_IntOp (closLang_Const i)) ==> (state_rel c l1 l2
  s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_GlobalsPtr = cake_theorem "assign_GlobalsPtr"
  (fun () ->
    `op = closLang_GlobOp closLang_GlobalsPtr ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_Global = cake_theorem "assign_Global"
  (fun () ->
    `(?n. op = closLang_GlobOp (closLang_Global n)) ==> (state_rel c l1
  l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_SetGlobal = cake_theorem "assign_SetGlobal"
  (fun () ->
    `(?n. op = closLang_GlobOp (closLang_SetGlobal n)) ==> (state_rel c
  l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_SetGlobalsPtr = cake_theorem "assign_SetGlobalsPtr"
  (fun () ->
    `op = closLang_GlobOp closLang_SetGlobalsPtr ==> (state_rel c l1 l2
  s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let IMP = cake_theorem "IMP"
  (fun () ->
    `b1 \/ b2 <=> ~b1 ==> b2`)
  CHEAT_TAC;;

let memcopy_def = cake_define
  `memcopy k a1 a2 m dm =
     (if k = 0 then SOME m else
       if a1 IN dm /\ a2 IN dm then
         memcopy (k - 1) (a1 + bytes_in_word) (a2 + bytes_in_word)
           ((a2 =+ m a1) m) dm else NONE)`;;

let MemCopy_thm = cake_theorem "MemCopy_thm"
  (fun () ->
    `!ret_val l1 l2 k a1 a2 (s:('a,'c,'ffi)wordSem_state) m dm m1.
        memcopy k a1 a2 m dm = SOME m1 /\ wordSem_state_memory
        s = m /\ wordSem_state_mdomain s = dm /\
        sptree_lookup MemCopy_location (state_code s) = SOME
          (5,MemCopy_code) /\
        k <= state_clock s /\ 4 * k < dimword (:'a) /\
        get_var 0 s = SOME (Loc l1 l2) /\
        get_var 2 s = SOME (wordLang_Word (n2w (4 * k))) /\
        get_var 4 s = SOME (wordLang_Word (a1:'a word)) /\
        get_var 6 s = SOME (wordLang_Word a2) /\
        get_var 8 s = SOME ret_val ==>
        (?smx.
        evaluate (MemCopy_code,s) =
          (SOME (wordSem_Result (wordLang_Loc l1 l2)
            [ret_val]),state_stack_max_fupd (K smx)
            (state_locals_size_fupd (K (SOME 0)) (state_locals_fupd (K
            LN) (wordSem_state_memory_fupd (K m1) (state_clock_fupd (K
            (state_clock s - k))
           s))))) /\
        option_le smx
          (OPTION_MAP2 MAX (state_stack_max s)
            (OPTION_MAP2 (+) (stack_size (stack s))
                            (sptree_lookup MemCopy_location
                              (wordSem_state_stack_size s)))))`)
  CHEAT_TAC;;

(* HOL4 data_to_word_assignProofScript.sml:15317-15319: a theorem
   that HOL4 states as the value of an ML expression:
   assign_ConsExtend_expand *)

let data_to_word_assignProof_get_vars_IMP_domain =
  cake_theorem "get_vars_IMP_domain"
  (fun () ->
    `!xs s y.
        get_vars xs s = SOME y ==>
        EVERY (\x. x IN domain s) xs`)
  CHEAT_TAC;;

let memory_rel_IMP_free_space = cake_theorem "memory_rel_IMP_free_space"
  (fun () ->
    `memory_rel c be ts refs sp st m dm vars ==>
      (?nfree curr other.
        FLOOKUP st NextFree = SOME (wordLang_Word nfree) /\
        FLOOKUP st CurrHeap = SOME (wordLang_Word curr) /\
        (word_list_exists nfree sp * other) (fun2set (m,dm)))`)
  CHEAT_TAC;;

let IMP_store_list_SOME = cake_theorem "IMP_store_list_SOME"
  (fun () ->
    `!ws a n m dm other.
        (word_list_exists a n * other) (fun2set (m,dm)) /\ LENGTH
          ws <= n ==>
        (?m1. data_to_word_memoryProof_store_list a ws m dm = SOME
          m1 /\
             (misc_word_list a ws *
              word_list_exists (a + bytes_in_word * n2w (LENGTH
                ws)) (n - LENGTH ws) *
              other) (fun2set (m1,dm)))`)
  CHEAT_TAC;;

let get_vars_cut_env = cake_theorem "get_vars_cut_env"
  (fun () ->
    `!vs bs.
        dataSem_cut_env nms x1 = SOME x2 /\
        dataSem_get_vars vs x1 = SOME bs /\
        EVERY (\v. v IN domain nms) vs ==>
        dataSem_get_vars vs x2 = SOME bs`)
  CHEAT_TAC;;

let word_exp_real_addr_some_value =
  cake_theorem "word_exp_real_addr_some_value"
  (fun () ->
    `FLOOKUP (wordSem_state_store s3) CurrHeap = SOME (wordLang_Word
  curr) /\
      get_var a s3 = SOME (wordLang_Word ww) /\
      good_dimindex (:'a) /\ shift_length c < dimindex (:'a) ==>
      (?wx. wordSem_word_exp (s3:('a,'c,'ffi)wordSem_state)
        (real_addr c a) = SOME (wordLang_Word wx))`)
  CHEAT_TAC;;

let store_list_APPEND = cake_theorem "store_list_APPEND"
  (fun () ->
    `!xs ys a m.
        data_to_word_memoryProof_store_list a (xs ++ ys) m dm =
        (match data_to_word_memoryProof_store_list a xs m dm with
          NONE -> NONE | SOME m1 ->
          data_to_word_memoryProof_store_list (a + bytes_in_word * n2w
          (LENGTH xs)) ys m1 dm)`)
  CHEAT_TAC;;

let memory_rel_store_list_to_unused =
  cake_theorem "memory_rel_store_list_to_unused"
  (fun () ->
    `!ws2 m dm m1.
        memory_rel c be ts refs n st m dm vars /\
        data_to_word_memoryProof_store_list nfree ws2 m dm = SOME
          m1 /\
        FLOOKUP st NextFree = SOME (wordLang_Word nfree) /\ LENGTH
          ws2 <= n ==>
        memory_rel c be ts refs n st m1 dm vars`)
  CHEAT_TAC;;

let get_vars_delete_lemma = cake_theorem "get_vars_delete_lemma"
  (fun () ->
    `!t7. get_vars (MAP adjust_var t7) (state_locals_fupd (K
                 (insert 9 x9
                   (insert 7 x7
                      (insert 5 x5
                         (insert 1 x1 (state_locals s1)))))) s1) =
        get_vars (MAP adjust_var t7) s1`)
  CHEAT_TAC;;

let INTRO_IS_SOME = cake_theorem "INTRO_IS_SOME"
  (fun () ->
    `(?v. x = SOME v) <=> IS_SOME x`)
  CHEAT_TAC;;

let STAR_fun2set_IMP_SEP_T = cake_theorem "STAR_fun2set_IMP_SEP_T"
  (fun () ->
    `(p * q) (fun2set (m,dm)) ==> (p * SEP_T) (fun2set (m,dm))`)
  CHEAT_TAC;;

let IMP_memcopy_lemma = cake_theorem "IMP_memcopy_lemma"
  (fun () ->
    `memory_rel c (be s1) ts (state_refs x) sp (wordSem_state_store s1)
  m1 (wordSem_state_mdomain s1)
        ((Block ts' n' l',wordLang_Word w_ptr) :: (ZIP ys7 ws1 ++
          vars)) /\
      startptr < LENGTH l' /\ LENGTH ys7 = LENGTH ws1 /\
        good_dimindex (:'a) /\
      sptree_lookup (adjust_var a1) (state_locals s1) = SOME
        (wordLang_Word (w_ptr:'a word)) /\
      wordSem_word_exp s1 (real_addr c (adjust_var a1)) = SOME
        (wordLang_Word wx) ==>
      memory_rel c (be s1) ts (state_refs x) sp
        (wordSem_state_store s1) m1 (wordSem_state_mdomain s1)
        ((Block ts' n' l',wordLang_Word w_ptr) ::
         (ZIP (ys7 ++ [EL startptr l']) (
          ws1 ++ [m1 (wx + bytes_in_word + bytes_in_word * n2w
            startptr)]) ++ vars)) /\
      (wx + bytes_in_word + bytes_in_word * n2w startptr) IN
        wordSem_state_mdomain s1`)
  CHEAT_TAC;;

(* HOL4 data_to_word_assignProofScript.sml:15487-15545: a theorem
   that HOL4 states as the value of an ML expression: IMP_memcopy *)

let data_to_word_assignProof_cut_envs_adjust_sets_insert_ODD =
  cake_theorem "cut_envs_adjust_sets_insert_ODD"
  (fun () ->
    `ODD n ==>
     cut_envs (adjust_sets names) (insert n w t) =
     cut_envs (adjust_sets names) t`)
  CHEAT_TAC;;

let IN_domain_adjust_set_IMP = cake_theorem "IN_domain_adjust_set_IMP"
  (fun () ->
    `x IN domain (adjust_set the_names) ==>
     (?xa. x = adjust_var xa /\ xa IN domain the_names)`)
  CHEAT_TAC;;

let assign_ConsExtend = cake_theorem "assign_ConsExtend"
  (fun () ->
    `(?tag. op = closLang_BlockOp (closLang_ConsExtend tag)) ==>
  (state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

let assign_Cons = cake_theorem "assign_Cons"
  (fun () ->
    `(?tag. op = closLang_BlockOp (closLang_Cons tag)) ==> (state_rel c
  l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
     (~(op_requires_names op = (names_opt = NONE))) /\
     cut_state_opt names_opt s = SOME x /\
     get_vars args (state_locals s) = SOME vals /\
       wordSem_state_termdep
     t > 1 /\
     do_app op vals x = Rval (v,s2) ==>
     (?q r.
       evaluate (FST (assign c n l dest op args names_opt),t) =
         (q,r) /\
       (q = SOME wordSem_NotEnoughSpace ==> state_ffi
        r = state_ffi t /\ option_le (state_stack_max r)
          (state_stack_max s2) /\
        (~(data_to_word_config_gc_kind c = None) ==>
          ~(dataSem_state_safe_for_space s2))) /\
       (~(q = SOME wordSem_NotEnoughSpace) ==>
        state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
          NONE)))`)
  CHEAT_TAC;;

let assign_FFI = cake_theorem "assign_FFI"
  (fun () ->
    `(?n. op = FFI n) ==> (state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
     (~(op_requires_names op = (names_opt = NONE))) /\
     cut_state_opt names_opt s = SOME x /\
     get_vars args (state_locals s) = SOME vals /\
       wordSem_state_termdep
     t > 1 /\
     do_app op vals x = Rval (v,s2) ==>
     (?q r.
       evaluate (FST (assign c n l dest op args names_opt),t) =
         (q,r) /\
       (q = SOME wordSem_NotEnoughSpace ==> state_ffi
        r = state_ffi t /\ option_le (state_stack_max r)
          (state_stack_max s2) /\
        (~(data_to_word_config_gc_kind c = None) ==>
          ~(dataSem_state_safe_for_space s2))) /\
       (~(q = SOME wordSem_NotEnoughSpace) ==>
        state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
          NONE)))`)
  CHEAT_TAC;;

let assign_FFI_final = cake_theorem "assign_FFI_final"
  (fun () ->
    `state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
     (~(op_requires_names (FFI i) = (names_opt = NONE))) /\
     cut_state_opt names_opt s = SOME x /\
     get_vars args (state_locals s) = SOME vals /\
       wordSem_state_termdep
     t > 1 /\
     do_app (FFI i) vals x = Rerr (Rabort (Rffi_error f)) ==>
     (?q r.
       evaluate (FST (assign c n l dest (FFI i) args names_opt),t)
         = (q,r) /\
       option_le (state_stack_max r) (state_stack_max s) /\ ~(q =
         SOME wordSem_NotEnoughSpace) /\ state_ffi r = state_ffi t /\
         q = SOME (wordSem_FinalFFI f))`)
  CHEAT_TAC;;

let getWords_acc = cake_theorem "getWords_acc"
  (fun () ->
    `!ws acc.
       getWords ws acc =
         (let (cs,c) = getWords ws [] in (REVERSE acc ++ cs,c))`)
  CHEAT_TAC;;

let getWords_thm = cake_theorem "getWords_thm"
  (fun () ->
    `!ws cs rest.
       getWords ws [] = (cs,rest) ==>
       ws = MAP (\(b,c). (b,wordLang_Word c)) cs ++ rest`)
  CHEAT_TAC;;

let store_list_word_cond_add_IMP =
  cake_theorem "store_list_word_cond_add_IMP"
  (fun () ->
    `!y2 m a m1 free'.
       data_to_word_memoryProof_store_list free' (MAP
         (word_cond_add c (a:'a word))
         (MAP (\(b,c). (b,wordLang_Word c)) y2)) m dm = SOME m1 ==>
       const_addresses free' y2 dm /\
       const_writes free' (a << (shift_length c -
         backend_common_word_shift (:'a))) y2 m = m1`)
  CHEAT_TAC;;

let evaluate_StoreAnyConsts = cake_theorem "evaluate_StoreAnyConsts"
  (fun () ->
    `!r1 r2 r3 vs w (s:('a,'c,'ffi)wordSem_state) free' m dm m1.
       data_to_word_memoryProof_store_list free' (MAP
         (word_cond_add c (a:'a word)) vs) m dm = SOME m1 /\
       m = wordSem_state_memory s /\ dm = wordSem_state_mdomain s
         /\ ALL_DISTINCT [r1; r2; r3] /\
       EVERY (good_loc (domain (state_code s)) o SND) (w :: vs) /\
       sptree_lookup r2 (state_locals s) = SOME (wordLang_Word
         free') /\
       sptree_lookup r3 (state_locals s) = SOME (wordLang_Word (a
         << (shift_length c - backend_common_word_shift (:'a)))) ==>
       (?ll.
         evaluate (StoreAnyConsts r1 r2 r3 vs w,s) =
           (NONE,wordSem_state_store_fupd (K (wordSem_state_store s
             |+ (NextFree,wordLang_Word
                              (free' + bytes_in_word * n2w (LENGTH
                                vs))))) (state_locals_fupd (K ll)
                                (wordSem_state_memory_fupd (K m1) s)))
                                /\
         sptree_lookup r1 ll = SOME (word_cond_add c a w) /\
         (!n. ~(MEM n [r1; r2; r3]) ==> sptree_lookup n ll =
           sptree_lookup n (state_locals s)))`)
  CHEAT_TAC;;

let do_build_const_IMP_SOME = cake_theorem "do_build_const_IMP_SOME"
  (fun () ->
    `do_build_const parts x (SOME ts) = (v,vs,ts1) ==>
     (?ts2. ts1 = SOME ts2)`)
  CHEAT_TAC;;

let TWO_POW_LEMMA = cake_theorem "TWO_POW_LEMMA[local]"
  (fun () ->
    `(2 EXP n <= 3 ==> n < 2) /\
     (2 EXP n <= 2 ==> n < 2) /\
     (2 EXP n <= 1 ==> n < 1)`)
  CHEAT_TAC;;

let bignum_size = cake_theorem "bignum_size"
  (fun () ->
    `good_dimindex (:'a) ==>
     bignum_size (dimindex (:'a) = 64) i = LENGTH (n2mw
       (num_of_int (abs i)):('a word) list) + 1`)
  CHEAT_TAC;;

let parts_to_words_NONE = cake_theorem "parts_to_words_NONE[local]"
  (fun () ->
    `!parts' (off:'a word) m aa (t:('a,'c,'ffi)wordSem_state)
  (s:('c,'ffi)dataSem_state).
       parts_to_words c m aa parts' off = NONE /\ good_dimindex
         (:'a) /\
       heap_in_memory_store heap a sp sp1 gens c
         (wordSem_state_store t) (wordSem_state_memory t)
         (wordSem_state_mdomain t) limit ==>
       limits_inv (dataSem_state_limits s) (FLOOKUP
         (wordSem_state_store t) HeapLength) (stack_limit t)
         (data_to_word_config_len_size
                  c) (has_fp_ops c)
                    (data_to_word_config_has_fp_tern c) ==>
       EXISTS ((~) o lim_safe_part (dataSem_state_limits s))
         parts'`)
  CHEAT_TAC;;

let assign_Build = cake_theorem "assign_Build"
  (fun () ->
    `(?parts'. op = closLang_BlockOp (closLang_Build parts')) ==>
  (state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
     (~(op_requires_names op = (names_opt = NONE))) /\
     cut_state_opt names_opt s = SOME x /\
     get_vars args (state_locals s) = SOME vals /\
       wordSem_state_termdep
     t > 1 /\
     do_app op vals x = Rval (v,s2) ==>
     (?q r.
       evaluate (FST (assign c n l dest op args names_opt),t) =
         (q,r) /\
       (q = SOME wordSem_NotEnoughSpace ==> state_ffi
        r = state_ffi t /\ option_le (state_stack_max r)
          (state_stack_max s2) /\
        (~(data_to_word_config_gc_kind c = None) ==>
          ~(dataSem_state_safe_for_space s2))) /\
       (~(q = SOME wordSem_NotEnoughSpace) ==>
        state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
          NONE)))`)
  CHEAT_TAC;;


(* HOL4 data_to_word_assignProofScript.sml:16926: ML code, not ported *)

let join_lemma = cake_theorem "join_lemma[local]"
  (fun () ->
    `(b1 ==> x) /\ (b2 ==> x) ==> (b1 \/ b2 ==> x)`)
  CHEAT_TAC;;

(* HOL4 data_to_word_assignProofScript.sml:16931-16933: a theorem
   that HOL4 states as the value of an ML expression: imp_assign *)

let assign_thm = cake_theorem "assign_thm"
  (fun () ->
    `(state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
      (~(op_requires_names op = (names_opt = NONE))) /\
      cut_state_opt names_opt s = SOME x /\
      get_vars args (state_locals s) = SOME vals /\
        wordSem_state_termdep
      t > 1 /\
      do_app op vals x = Rval (v,s2) ==>
      (?q r.
        evaluate (FST (assign c n l dest op args names_opt),t) =
          (q,r) /\
        (q = SOME wordSem_NotEnoughSpace ==> state_ffi
         r = state_ffi t /\ option_le (state_stack_max r)
           (state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = None) ==>
           ~(dataSem_state_safe_for_space s2))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         state_rel c l1 l2 (set_var dest v s2) r NONE locs /\ q =
           NONE)))`)
  CHEAT_TAC;;

cake_hide [];;
