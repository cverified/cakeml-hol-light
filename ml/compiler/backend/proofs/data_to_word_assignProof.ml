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
(* for word_add_carry *)
needs "compiler/backend/bvi_to_data.ml";;
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
needs "lib/integer_word.ml";;
needs "lib/multiword.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "lib/term.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "data_to_word_assignProof"
  ["backendProps"; "backend_common"; "bvi_to_data"; "copying_gc";
   "dataProps"; "dataSem"; "data_to_word"; "data_to_word_bignumProof";
   "data_to_word_gcProof"; "data_to_word_memoryProof"; "gc_shared";
   "gen_gc"; "gen_gc_partial"; "semanticsProps"; "wordLang";
   "wordProps"; "wordSem"; "word_bignum"; "word_bignumProof";
   "word_gcFunctions"];;

let _ = do_list hide_constant ["parts"; "vars"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["code_buffer","code_buffer";
   "data_buffer","data_buffer"];;
(* HOL4 ancestors outside the port: int_bitwise While *)

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
 (`(if b then f x else h y) = (if b then f else h) (if b then x else
  y)`,
  CHEAT_TAC);;

let cut_env_IMP_domain = prove
 (`cut_names x y = SOME t ==> domain t = domain x`,
  CHEAT_TAC);;

let cut_envs_wf = prove
 (`cut_envs kept_names t = SOME (y1,y2) ==> sptree_wf y1 /\ sptree_wf
  y2`,
  CHEAT_TAC);;

let domain_list_insert_thm = prove
 (`!l names.
     domain (list_insert l names) = set_of_list l UNION domain
       names`,
  CHEAT_TAC);;

let cut_env_lookup = prove
 (`wordSem_cut_env names t = SOME y /\
   sptree_lookup n y = SOME a ==>
   sptree_lookup n t = SOME a`,
  CHEAT_TAC);;

let cut_env_get_vars_get_vars = prove
 (`!vs ws ws'.
     wordSem_cut_env kept_names (state_locals t) = SOME y /\
     wordSem_get_vars vs (state_locals_fupd (K y) t) = SOME ws /\
     wordSem_get_vars vs t = SOME ws' ==>
     ws = ws'`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let memory_rel_lookup_var_IMP = prove
 (cake_as_vars (fun () ->
    `memory_rel c be ts refs sp st m dm
       (APPEND (join_env ll
          (toAList (inter (wordSem_state_locals t) (adjust_set
            ll)))) envs) /\
      wordSem_get_vars n ll = SOME x /\
      wordSem_get_vars (MAP adjust_var n)
        (t:('a,'c,'ffi)wordSem_state) = SOME w ==>
      memory_rel c be ts refs sp st m dm
        (APPEND (APPEND (ZIP x w)
         (join_env ll
           (toAList (inter (wordSem_state_locals t) (adjust_set
             ll))))) envs)`),
  CHEAT_TAC);;

let get_real_offset_lemma = prove
 (`wordSem_get_var v t = SOME (wordLang_Word i_w) /\
    good_dimindex (:'a) /\
    get_real_offset i_w = SOME y ==>
    wordSem_word_exp t (real_offset c v) = SOME (wordLang_Word
      (y:'a word))`,
  CHEAT_TAC);;

let state_rel_push_env_loc = prove
 (`data_to_word_gcProof_state_rel c n l s (wordSem_call_env args b
  (wordSem_push_env (y1,y2) NONE t)) ys (CONS (l1,l2) locs) ==>
   sptree_lookup 0 y1 = SOME (wordLang_Loc l1 l2)`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:190-239: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_IMP_domain_union *)

let get_real_byte_offset_lemma = prove
 (`wordSem_get_var v t = SOME (wordLang_Word (w:'a word)) /\
  good_dimindex (:'a) ==>
   wordSem_word_exp t (real_byte_offset v) = SOME (wordLang_Word
     (bytes_in_word + (w >>> 2)))`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let reorder_lemma = prove
 (cake_as_vars (fun () ->
    `memory_rel c be ts (state_refs x) (dataSem_state_space x)
  (wordSem_state_store t) (wordSem_state_memory t)
  (wordSem_state_mdomain t) (CONS x1 (CONS x2 (CONS x3 xs))) ==>
     memory_rel c be ts (state_refs x) (dataSem_state_space x)
       (wordSem_state_store t) (wordSem_state_memory t)
       (wordSem_state_mdomain t) (CONS x3 (CONS x1 (CONS x2 xs)))`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let reorder_2_lemma = prove
 (cake_as_vars (fun () ->
    `memory_rel c be ts (state_refs x) (dataSem_state_space x)
  (wordSem_state_store t) (wordSem_state_memory t)
  (wordSem_state_mdomain t) (CONS x1 (CONS x2 xs)) ==>
     memory_rel c be ts (state_refs x) (dataSem_state_space x)
       (wordSem_state_store t) (wordSem_state_memory t)
       (wordSem_state_mdomain t) (CONS x2 (CONS x1 xs))`),
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:263-289: a theorem that
   HOL4 states as the value of an ML expression: evaluate_StoreEach *)

let get_vars_adjust_var = prove
 (`ODD k ==>
    wordSem_get_vars (MAP adjust_var args) (state_locals_fupd (K
      (sptree_insert k w s)) t) =
    wordSem_get_vars (MAP adjust_var args) (state_locals_fupd (K s)
      t)`,
  CHEAT_TAC);;

let get_vars_with_store = prove
 (`!args. wordSem_get_vars args (wordSem_state_store_fupd (K s)
  (state_locals_fupd (K (state_locals t)) t)) =
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
   sptree_lookup 0 (sptree_union y2 y1) = SOME (wordLang_Loc l1 l2)
     ==>
   ALOOKUP l' 0 = NONE /\ sptree_lookup 0 y1 = SOME (wordLang_Loc
     l1 l2)`,
  CHEAT_TAC);;

let word_exp_real_addr = prove
 (`get_real_addr c (wordSem_state_store t) ptr_w = SOME a /\
    shift_length c < dimindex (:'a) /\ good_dimindex (:'a) /\
    sptree_lookup (adjust_var a1) (wordSem_state_locals
      (t:('a,'c,'ffi)wordSem_state)) = SOME (wordLang_Word ptr_w) ==>
    (!w. wordSem_word_exp (wordSem_state_locals_fupd (K
      (sptree_insert 1 (wordLang_Word (w:'a word)) (wordSem_state_locals
      t))) t)
          (real_addr c (adjust_var a1)) = SOME (wordLang_Word a))`,
  CHEAT_TAC);;

let word_exp_real_addr_2 = prove
 (`get_real_addr c (wordSem_state_store (t:('a,'c,'ffi)wordSem_state))
  ptr_w = SOME a /\
    shift_length c < dimindex (:'a) /\ good_dimindex (:'a) /\
    sptree_lookup (adjust_var a1) (wordSem_state_locals t) = SOME
      (wordLang_Word ptr_w) ==>
    (!w1 w2.
      wordSem_word_exp
        (wordSem_state_locals_fupd (K (sptree_insert 3 (wordLang_Word
          (w1:'a word)) (sptree_insert 1 (wordLang_Word w2)
          (wordSem_state_locals t)))) t)
        (real_addr c (adjust_var a1)) = SOME (wordLang_Word a))`,
  CHEAT_TAC);;

let encode_header_IMP_BIT0 = prove
 (`encode_header c tag l = SOME w ==> FAPPLY w 0`,
  CHEAT_TAC);;

let get_addr_inj = prove
 (`p1 * 2 EXP shift_length c < dimword (:'a) /\
   p2 * 2 EXP shift_length c < dimword (:'a) /\
   get_addr c p1 (wordLang_Word ((n2w 0):'a word)) = get_addr c p2
     (wordLang_Word (n2w 0)) ==> p1 = p2`,
  CHEAT_TAC);;

let Word64Rep_inj = prove
 (`good_dimindex (:'a) ==>
   (Word64Rep (:'a) w1 = Word64Rep (:'a) w2 <=> w1 = w2)`,
  CHEAT_TAC);;

let IMP_read_bytearray_GENLIST = prove
 (`!ls len a.
   len = LENGTH ls /\
   (!i. i < len ==> g (a + n2w i) = SOME (EL i ls)) ==>
     read_bytearray a len g = SOME ls`,
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

(* HOL4 data_to_word_assignProofScript.sml:481-494: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_BignumHalt *)

(* TODO: should probably replace evaluate_GiveUp directly *)
(* HOL4 data_to_word_assignProofScript.sml:497-520: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_GiveUp2 *)

(* HOL4 data_to_word_assignProofScript.sml:522-535: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_BignumHalt2 *)

let state_rel_get_var_Number_IMP_alt = prove
 (`!k i. data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
          wordSem_get_var k (state_locals s) = SOME (dataSem_Number
            i) /\
          wordSem_get_var (2 * k + 2) t = SOME a1 ==>
          (?(w:'a word). a1 = wordLang_Word w /\ FAPPLY w 0 =
            ~(small_int (:'a) i))`,
  CHEAT_TAC);;

(* TODO: move to sptreeTheory *)
(* [local] *)
let EXISTS_NOT_IN_spt_DOMAIN = prove
 (`?x. ~(x IN domain (refs:'a spt))`,
  CHEAT_TAC);;

(* TODO: move to sptreeTheory *)
let LEAST_NOTIN_spt_DOMAIN = prove
 (`!refs. ~((minimal x. ~(x IN domain (refs:'a spt))) IN domain refs)`,
  CHEAT_TAC);;

(*TODO: move to backendProps *)
let option_le_add_indv = prove
 (`option_le (OPTION_MAP2 (+) n m) r ==> option_le n r /\ option_le m
  r`,
  CHEAT_TAC);;

let option_le_add_drop_right = prove
 (`option_le x y ==>
   option_le x (OPTION_MAP2 (+) z y)`,
  CHEAT_TAC);;

let word_exp_SmallLsr = prove
 (`n < dimindex (:'a) ==>
    wordSem_word_exp s (SmallLsr e n) =
       (match wordSem_word_exp s e with SOME (wordLang_Word w) ->
         SOME (wordLang_Word ((w:'a word) >>> n)) | res -> (if n = 0
         then res else NONE))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:604-619: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_MakeBytes *)

let w2w_shift_shift = prove
 (`good_dimindex (:'a) ==> ((w2w (w:word8) << 2 >>> 2):'a word) = w2w
  w`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:629-631: a proof *)

(* HOL4 data_to_word_assignProofScript.sml:633-679: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_WriteLastBytes *)

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
   (size_of lims (CONS (dataSem_Number n) vs) refs seen = size_of
     lims vs refs seen)`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:707-710: a theorem that
   HOL4 states as the value of an ML expression: ADD4DIV4 *)

(* HOL4 data_to_word_assignProofScript.sml:712-715: a theorem that
   HOL4 states as the value of an ML expression: ADD8DIV8 *)

(* HOL4 data_to_word_assignProofScript.sml:717-1233: a theorem whose
   statement HOL Light does not read (tools/unstated.py): RefByte_thm *)

(* TODO: copypaste from costProps *)
let size_of_seen_SUBSET = prove
 (`!lims vs refs seen n1 seen1 refs1.
   (size_of lims vs refs seen = (n1,refs1,seen1)) ==> domain seen
     SUBSET domain seen1`,
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
    size_of lims (CONS (dataSem_Block ts tag l) vs) refs seen =
      size_of lims vs refs seen`,
  CHEAT_TAC);;

let state_rel_IMP_test_zero = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) vs locs /\
    wordSem_get_var i (state_locals s) = SOME (dataSem_Number n) ==>
    (?w. wordSem_get_var (adjust_var i) t = SOME (wordLang_Word w)
      /\ (w = (n2w 0) <=> (n = (&0))))`,
  CHEAT_TAC);;

let state_rel_get_var_Number_IMP = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s t vs locs /\
    wordSem_get_var i (state_locals s) = SOME (dataSem_Number (&n))
      /\ small_int (:'a) (&n) ==>
    (?w. wordSem_get_var (adjust_var i) t = SOME (wordLang_Word
      (Smallnum (&n):'a word)))`,
  CHEAT_TAC);;

let EXP_LEMMA1 = prove
 (`4 * n * (2 EXP k) = n * 2 EXP (k + 2)`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:1341-1356: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_Maxout_bits_code *)

(* HOL4 data_to_word_assignProofScript.sml:1358-1385: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   Make_ptr_bits_thm *)

(* HOL4 data_to_word_assignProofScript.sml:1387-1391: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:1393-1411: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_LoadWord64 *)

(* HOL4 data_to_word_assignProofScript.sml:1413-1467: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_WriteWord64 *)

(* HOL4 data_to_word_assignProofScript.sml:1469-1530: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_WriteWord64_on_32 *)

(* [local] *)
let Num_ABS_AND = prove
 (`num_of_int (abs (&n)) = n /\ num_of_int (abs (--(&n))) = n`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:1538-1612: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_WriteWord64_on_32_num *)

(* HOL4 data_to_word_assignProofScript.sml:1614-1677: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_WriteWord32_bignum *)

(* HOL4 data_to_word_assignProofScript.sml:1679-1742: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_WriteWord64_bignum *)

(* HOL4 data_to_word_assignProofScript.sml:1744-1763: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_LoadBignum *)

(* HOL4 data_to_word_assignProofScript.sml:1765-1778: the ML values
   that the definitions below antiquote *)

(* HOL4 data_to_word_assignProofScript.sml:1780-1781: the ML values
   that the definitions below antiquote *)

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
     MAP (dataSem_Number o (&) o w2n) ns = MAP (dataSem_Number o (&)
       o w2n) ns' <=>
     ns = (ns':word8 list)`,
  CHEAT_TAC);;

(* [local] *)
let MAP_Word64_11 = prove
 (`!ns ns'.
     MAP (dataSem_Word64) ns = MAP (dataSem_Word64) ns' <=>
     ns = ns'`,
  CHEAT_TAC);;

let v_to_list_EQ_SOME_NIL = prove
 (`dataSem_v_to_list hv1 = SOME [] <=> (?ts. hv1 = dataSem_Block ts 0
  [])`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:1845-1962: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   InstallCode_code_thm *)

let w2w_upper_def = new_definition
  `w2w_upper (w:word64) =
     (if dimindex (:'a) = 32 then ((63 >< 32) w):'a word else w2w
       w)`;;

(* HOL4 data_to_word_assignProofScript.sml:1969-2096: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   InstallData_code_thm *)

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
 (`!full_list. MAP FST (MAP (data_to_word_compile_part c) full_list) =
  MAP FST full_list`,
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
 (`consume_space a x = SOME s ==> state_stack_max x = state_stack_max
  s`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:2146-2147: ML code, not
   ported *)

let do_app_aux_safe_for_space_mono = prove
 (`(dataSem_do_app_aux op xs s = Rval (r,s1)) /\
  dataSem_state_safe_for_space s1 ==> dataSem_state_safe_for_space s`,
  CHEAT_TAC);;

let do_app_safe_for_space_allowed_op = prove
 (`dataSem_do_app op xs s = Rval (r,s1) /\ dataSem_state_safe_for_space
   s1 ==>
   allowed_op op (LENGTH xs)`,
  CHEAT_TAC);;

let state_rel_cut_state_opt_SOME = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
   wordSem_get_vars args (state_locals s) = SOME vals /\
   wordSem_cut_state_opt (SOME kept_names) s = SOME x ==>
   (?y ws.
     wordSem_cut_env (adjust_sets kept_names) (state_locals t) = SOME
       y /\
     wordSem_get_vars (MAP adjust_var args) t = SOME ws /\
     LENGTH args = LENGTH vals /\ LENGTH args = LENGTH ws /\
     data_to_word_gcProof_state_rel c l1 l2 x t NONE locs /\
     data_to_word_gcProof_state_rel c l1 l2 x (state_locals_fupd (K
       y) t) NONE locs)`,
  CHEAT_TAC);;

let cut_state_opt_SOME_eq = prove
 (`wordSem_cut_state_opt (SOME names) s = SOME x ==>
   x = state_locals_fupd (K (mk_wf (inter (state_locals s) names)))
     s`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:2210-2212: ML code, not
   ported *)

let state_rel_cut_state_opt_set_var = prove
 (`data_to_word_gcProof_state_rel c l1 l2 (wordSem_set_var dest v s2) r
  NONE locs /\
   wordSem_cut_state_opt (SOME names) s2 = SOME s2_cut ==>
   data_to_word_gcProof_state_rel c l1 l2 (wordSem_set_var dest v
     s2_cut) r NONE locs`,
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
 (`(!k v. sptree_lookup k l1 = SOME v ==> sptree_lookup k l1' = SOME v)
  /\
   (!k v. sptree_lookup k l2 = SOME v ==> sptree_lookup k l2' = SOME
     v) /\
   MEM p (join_env l1 (toAList (inter l2 (adjust_set l1)))) ==>
   MEM p (join_env l1' (toAList (inter l2' (adjust_set l1'))))`,
  CHEAT_TAC);;

(* The three heap-store FLOOKUPs follow directly from state_rel.
   Reusable in any op that needs to inspect t.store.{NextFree,CurrHeap,HeapLength}. *)
let state_rel_FLOOKUP_heap = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s t NONE locs ==>
   (?nf cu hl.
     FLOOKUP (wordSem_state_store t) NextFree = SOME (wordLang_Word
       nf) /\
     FLOOKUP (wordSem_state_store t) CurrHeap = SOME (wordLang_Word
       cu) /\
     FLOOKUP (wordSem_state_store t) HeapLength = SOME
       (wordLang_Word hl))`,
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
     wordSem_cut_env (adjust_sets ns) (state_locals t) = SOME env ==>
     wordSem_evaluate (SilentFFI c 3 (adjust_sets ns),t) =
       (NONE,state_ffi_fupd (K (state_ffi t))
         (wordSem_state_memory_fupd (K (wordSem_state_memory t))
         (fp_regs_fupd (K FEMPTY) (state_locals_fupd (K env) t))))`,
  CHEAT_TAC);;

(* size_of_heap monotonicity helpers *)

let size_of_app_Number = prove
 (`!xs ys lims i refs seen.
     size_of lims (APPEND xs (CONS (dataSem_Number i) ys)) refs seen
       =
     (let (n,refs',seen') = size_of lims (APPEND xs ys) refs seen in
     let k = (if small_num (limits_arch_64_bit lims) i then 0 else
       bignum_size (limits_arch_64_bit lims) i) in
     (n + k,refs',seen'))`,
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
     sptree_lookup k (state_locals s) = SOME (dataSem_Number i) ==>
     size_of_heap (state_locals_fupd (K (sptree_delete k
       (state_locals s))) s) <= size_of_heap s`,
  CHEAT_TAC);;

let wf_FOLDR_delete = prove
 (`!ks (L:'a spt). sptree_wf L ==> sptree_wf (ITLIST sptree_delete ks
  L)`,
  CHEAT_TAC);;

(* lookup_FOLDR_delete *)
let data_to_word_assignProof_lookup_FOLDR_delete = prove
 (`!ks (L:'a spt) h.
     sptree_lookup h (ITLIST sptree_delete ks L) =
     (if MEM h ks then NONE else sptree_lookup h L)`,
  CHEAT_TAC);;

let size_of_heap_FOLDR_delete_Number_LE = prove
 (`!ks L (state:('a,'b)dataSem_state).
     sptree_wf L /\
     (!k. MEM k ks ==> sptree_lookup k L = NONE \/
                       (?i. sptree_lookup k L = SOME (dataSem_Number
                         i))) ==>
     size_of_heap (dataSem_state_locals_fupd (K (ITLIST sptree_delete
       ks L)) state) <=
     size_of_heap (dataSem_state_locals_fupd (K L) state)`,
  CHEAT_TAC);;


(* end size_of_heap monotonicity helpers *)


(* HOL4 data_to_word_assignProofScript.sml:2451-2745: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   assign_Install *)

(* HOL4 data_to_word_assignProofScript.sml:2747-2815: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   assign_MutCons *)

(* HOL4 data_to_word_assignProofScript.sml:2817-2858: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   assign_UpdateCons *)

(* HOL4 data_to_word_assignProofScript.sml:2860-2888: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   assign_FinaliseCons *)

let LENGTH_EQ_5 = prove
 (`(LENGTH xs = 5 <=> (?a1 a2 a3 a4 a5. xs = [a1; a2; a3; a4; a5])) /\
    (5 = LENGTH xs <=> (?a1 a2 a3 a4 a5. xs = [a1; a2; a3; a4;
      a5]))`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let memory_rel_get_num = prove
 (cake_as_vars (fun () ->
    `memory_rel c be ts refs sp st m dm vars /\
      n < dimword (:'a) DIV 8 /\ good_dimindex (:'a) /\
      MEM (dataSem_Number (&n),(a:'a word_loc)) vars ==>
      (?w. a = wordLang_Word w /\ w >>> 2 = n2w n)`),
  CHEAT_TAC);;

let IN_domain_adjust_set_inter = prove
 (`x IN domain (adjust_set (inter s1 s2)) <=>
    x IN domain (adjust_set s1) /\
    x IN domain (adjust_set s2)`,
  CHEAT_TAC);;

let get_var_to_word_exp = prove
 (`wordSem_get_var r s = SOME (wordLang_Word w) ==>
   wordSem_word_exp s (wordLang_Op word_bignum_Add [db_vars_Var r;
     word_depth_Const (n2w 0)]) = SOME (wordLang_Word (w + (n2w 0))) /\
   wordSem_word_exp s (wordLang_Op word_bignum_Add [db_vars_Var r;
     word_depth_Const (n2w 1)]) = SOME (wordLang_Word (w + (n2w 1))) /\
   wordSem_word_exp s (wordLang_Op word_bignum_Add [db_vars_Var r;
     word_depth_Const (n2w 2)]) = SOME (wordLang_Word (w + (n2w 2))) /\
   wordSem_word_exp s (wordLang_Op word_bignum_Add [db_vars_Var r;
     word_depth_Const (n2w 3)]) = SOME (wordLang_Word (w + (n2w 3)))`,
  CHEAT_TAC);;

(* [local] *)
let word_exp_set = prove
 (`(wordSem_word_exp s (wordLang_Op backend_common_Add [wordLang_Var n;
  asm_Const c]) =
   (match wordSem_get_var n s with
     SOME (wordLang_Word w) -> SOME (wordLang_Word (w + c)) | _3 ->
       NONE)) /\
   (wordSem_word_exp s (wordLang_Op backend_common_Sub [wordLang_Var
     n; asm_Const c]) =
   (match wordSem_get_var n s with
     SOME (wordLang_Word w) -> SOME (wordLang_Word (w - c)) | _4 ->
       NONE))`,
  CHEAT_TAC);;

(* [local] *)
let good_dimindex_w2w_byte = prove
 (`good_dimindex (:'a) ==>
   w2w (w2w (w:word8):'a word) = w`,
  CHEAT_TAC);;

(* [local] *)
let set_var_consts = prove
 (`wordSem_state_memory
     (wordSem_set_var r v s) = wordSem_state_memory s /\
       wordSem_state_mdomain
     (wordSem_set_var r v s) = wordSem_state_mdomain s /\ be
     (wordSem_set_var r v s) = be s /\ state_code
     (wordSem_set_var r v s) = state_code s`,
  CHEAT_TAC);;

(* [local] *)
let get_var_consts = prove
 (`wordSem_get_var r (wordSem_state_memory_fupd (K m) s) =
  wordSem_get_var r s`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:2977-3088: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   CopyByteAdd_thm *)

(* HOL4 data_to_word_assignProofScript.sml:3090-3201: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   CopyByteSub_thm *)

let push_env_store = prove
 (`wordSem_state_store
      (wordSem_push_env x y s) = wordSem_state_store s /\
        wordSem_state_memory
       (wordSem_push_env x y s) = wordSem_state_memory s /\
         wordSem_state_mdomain
       (wordSem_push_env x y s) = wordSem_state_mdomain s /\
         state_code
       (wordSem_push_env x y s) = state_code s /\ be
       (wordSem_push_env x y s) = be s`,
  CHEAT_TAC);;

(* [local] *)
let not_less_zero_int_eq = prove
 (`~(i < ((&0):int)) <=> (?n. i = &n)`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:3223-3369: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   assign_WordFromWord *)

let IS_SOME_lookup = prove
 (`IS_SOME (sptree_lookup n l) <=> n IN domain l`,
  CHEAT_TAC);;

let IN_adjust_var_lemma = prove
 (`wordSem_cut_env kept_names s_locals = SOME x /\
   cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
   n IN domain x ==>
   adjust_var n IN domain y2`,
  CHEAT_TAC);;

let cut_env_envs_lookup_lookup = prove
 (`wordSem_cut_env kept_names s_locals = SOME x /\
   cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
   k IN domain (adjust_set x) ==>
   (?v. sptree_lookup k t_locals = SOME v /\
       sptree_lookup k y2 = SOME v)`,
  CHEAT_TAC);;

let env_to_list_domain = prove
 (`env_to_list y2 p = (l,permute) ==>
   domain (fromAList l) = domain y2`,
  CHEAT_TAC);;

let cut_envs_lookup_0 = prove
 (`cut_envs (adjust_sets names) t_locals = SOME (y1,y2) /\
   env_to_list y2 p = (q,r') /\
   sptree_lookup 0 t_locals = SOME (wordLang_Loc l1 l2) ==>
   ALOOKUP q 0 = NONE /\
   sptree_lookup 0 y1 = SOME (wordLang_Loc l1 l2)`,
  CHEAT_TAC);;

let cut_envs_domain_IN = prove
 (`cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
   wordSem_cut_env kept_names s_locals = SOME x /\
   n IN domain x ==>
   adjust_var n IN domain y2`,
  CHEAT_TAC);;

let inter_union_distrib = prove
 (`!x y z. inter (sptree_union x y) z = sptree_union (inter x z)
  (inter y z)`,
  CHEAT_TAC);;

let cut_envs_inter = prove
 (`cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
   wordSem_cut_env kept_names s_locals = SOME x ==>
   inter (fromAList (toAList y1)) (adjust_set x) = LN`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:3469-4092: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   assign_CopyByte *)

(* HOL4 data_to_word_assignProofScript.sml:4094-4151: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_StringCmpLoop *)

(* HOL4 data_to_word_assignProofScript.sml:4153-4164: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_AssignCmp *)

(* HOL4 data_to_word_assignProofScript.sml:4166-4185: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_StringCmpMin *)

(* HOL4 data_to_word_assignProofScript.sml:4187-4563: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   assign_StringCmp *)

(* HOL4 data_to_word_assignProofScript.sml:4565-4630: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_XorLoop *)

(* HOL4 data_to_word_assignProofScript.sml:4632-4825: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   assign_XorByte *)

(* HOL4 data_to_word_assignProofScript.sml:4827-5039: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_AppendMainLoop_code *)

let data_to_word_assignProof_STOP_def = new_definition
  `data_to_word_assignProof_STOP x = x`;;

(* HOL4 data_to_word_assignProofScript.sml:5045-5277: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_AppendMainLoop_code_alt *)
(* HOL4 data_to_word_assignProofScript.sml:5278-5281: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:5283-5369: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_AppendLenLoop_code *)
(* HOL4 data_to_word_assignProofScript.sml:5370-5371: ML code, not
   ported *)

let v_to_list_block_drop = prove
 (`!k v l.
    dataSem_v_to_list v = SOME l /\ k < LENGTH l ==>
      dataSem_v_to_list (THE (block_drop k v)) = SOME (DROP k l)`,
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
 (`!n s x. dataSem_cut_state n s = SOME x ==> state_refs s =
  state_refs x`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:5411-6295: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   assign_ListAppend *)

let do_app_AllocThunk = prove
 (`dataSem_do_app (closLang_ThunkOp (AllocThunk m):closLang_op) [v] x =
    (match consume_space (1 + 1) x with
      NONE -> Rerr (Rabort Rtype_error) | SOME s1 ->
      (if dataSem_bad_thunk_update m v (state_refs s1) then Rerr
        (Rabort Rtype_error) else
      Rval
      (dataSem_RefPtr F (minimal ptr. ~(ptr IN domain (state_refs
        s1))),state_stack_max_fupd (K (state_stack_max (
             do_stack
               (closLang_ThunkOp (AllocThunk m)) [v]
               (do_lim_safe s1 (closLang_ThunkOp (AllocThunk m))
                 [v])))) (dataSem_state_safe_for_space_fupd (K
                 (dataSem_state_safe_for_space (
             do_stack
               (closLang_ThunkOp (AllocThunk m)) [v]
               (do_lim_safe s1 (closLang_ThunkOp (AllocThunk m))
                 [v])))) (state_refs_fupd (K (sptree_insert (minimal
                 ptr. ~(ptr IN domain (state_refs s1))) (bvlSem_Thunk m
                 v) (state_refs s1)))
         s1)))))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:6319-6400: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   assign_AllocThunk *)

(* HOL4 data_to_word_assignProofScript.sml:6402-6469: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   assign_UpdateThunk *)

(* ConfigGC: assign-specific helper + body *)
let configGC_size_of_heap_LE = prove
 (`!ns s x k1 k2 i1 i2 (state:('a,'b)dataSem_state).
     dataSem_cut_state_opt (SOME (sptree_insert k2 one (sptree_insert
       k1 one ns))) s = SOME x /\
     sptree_lookup k1 (state_locals x) = SOME (dataSem_Number i1) /\
     sptree_lookup k2 (state_locals x) = SOME (dataSem_Number i2) /\
       dataSem_state_refs
     state = state_refs s /\ dataSem_state_limits state =
       dataSem_state_limits s /\ dataSem_state_stack
     state = stack s /\ dataSem_state_global state =
       dataSem_state_global s ==>
     size_of_heap (dataSem_state_locals_fupd (K (mk_wf (inter
       (state_locals s) ns))) state) <=
     size_of_heap (dataSem_state_locals_fupd (K (state_locals x))
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
 (`wordSem_cut_state_opt (SOME ns) s = SOME x ==> cut_locals ns s = x`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:6520-6701: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   assign_ConfigGC *)

(* HOL4 data_to_word_assignProofScript.sml:6703-6950: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   assign_WordToInt *)

let push_env_tstamps = prove
 (`!x t s. dataSem_state_tstamps (wordSem_push_env x t s) =
  dataSem_state_tstamps s`,
  CHEAT_TAC);;

let dec_clock_tstamps = prove
 (`!s. dataSem_state_tstamps (word_bignumProof_dec_clock s) =
  dataSem_state_tstamps s`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:6964-7041: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   FromList1_code_thm *)

(* HOL4 data_to_word_assignProofScript.sml:7043-7364: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   FromList_thm *)

(* ---- helpers used by assign_FromList's NES/Success arms (also reused by
   assign_RefByte etc. below); hoisted above assign_FromList so they are in
   scope here. ---- *)

(* do_app for FromList sets the result stack_max uniformly (stack_consumed is
   the same for the empty and nonempty cases), regardless of tstamps. *)
(* [local] *)
let do_app_FromList_stack_max = prove
 (`dataSem_do_app (closLang_BlockOp (closLang_FromList tag)) vals s =
  Rval (v,s') ==> state_stack_max
   s' = OPTION_MAP2 MAX (state_stack_max s)
     (OPTION_MAP2 (+)
        (stack_consumed (dataSem_state_stack_frame_sizes s)
          (dataSem_state_limits s) (closLang_BlockOp (closLang_FromList
          tag)) vals)
        (OPTION_MAP2 (+) (size_of_stack (stack s))
          (state_locals_size s)))`,
  CHEAT_TAC);;

(* do_app for FromList: the result safe_for_space field, uniform over the empty
   and nonempty cases (the empty case lacks the with_fresh_ts/check_lim wrapper,
   but its extra `LENGTH ys < 2 ** length_limit` conjunct is trivially true). The
   add_space_safe_args / the F terms are dataSem overloads; the statement spells
   them out so it parses without the abbreviation. *)
(* [local] *)
let do_app_FromList_safe = prove
 (`dataSem_v_to_list v2 = SOME ys /\
   dataSem_do_app (closLang_BlockOp (closLang_FromList tag))
     [dataSem_Number (&(LENGTH ys)); v2] (s:('c,'ffi)dataSem_state) =
     Rval (v,s') ==>
   (dataSem_state_safe_for_space s' <=>
    (((small_num (limits_arch_64_bit (dataSem_state_limits s))
      (&(LENGTH ys)) /\
       LENGTH ys < 2 EXP limits_length_limit (dataSem_state_limits s)
         /\
       LENGTH ys < arch_size (dataSem_state_limits s) DIV 16 /\
       4 * tag < 2 EXP (arch_size (dataSem_state_limits s) -
         (limits_length_limit (dataSem_state_limits s) + 2)) /\
       4 * tag < 2 EXP arch_size (dataSem_state_limits s) DIV 16) /\
      (dataSem_state_safe_for_space s /\
       no_thunks_in_refs (dataSem_state_refs s) /\
       size_of_heap_args [dataSem_Number (&(LENGTH ys)); v2] s +
         (LENGTH ys + 1) <= limits_heap_limit (dataSem_state_limits s)))
         /\
     the F (OPTION_MAP ((>) (stack_limit (dataSem_state_limits s)))
       (OPTION_MAP2 (+) (OPTION_MAP2 MAX (sptree_lookup
         FromList_location (dataSem_state_stack_frame_sizes s))
                              (sptree_lookup FromList1_location
                                (dataSem_state_stack_frame_sizes s)))
                       (OPTION_MAP2 (+) (size_of_stack
                         (dataSem_state_stack s))
                         (dataSem_state_locals_size s))))))`,
  CHEAT_TAC);;

(* do_app for FromList: the result value is a Block of the source list, and the
   non-stack/safe/space fields are preserved from the input state (tstamps gains
   a fresh stamp for nonempty lists). Used by assign_FromList's success arm to
   relate s2 (do_app on x) and s2_inner (do_app on s_pop): both share these
   fields because x and s_pop agree on locals/refs/tstamps/.... *)
(* [local] *)
let do_app_FromList_eq = prove
 (`dataSem_v_to_list v2 = SOME ys /\
   dataSem_do_app (closLang_BlockOp (closLang_FromList tag))
     [dataSem_Number (&(LENGTH ys)); v2] (s:('c,'ffi)dataSem_state) =
     Rval (v,s') ==>
   (?ts'. v = dataSem_Block ts' tag ys) /\ dataSem_state_space s' = 0
     /\ state_refs
   s' = dataSem_state_refs s /\ state_code s' = dataSem_state_code s
     /\ state_ffi s' = dataSem_state_ffi s /\ state_handler s' =
     dataSem_state_handler s /\ state_locals
   s' = dataSem_state_locals s /\ stack s' = dataSem_state_stack s /\
     dataSem_state_limits s' = dataSem_state_limits s /\
     dataSem_state_stack_frame_sizes
   s' = dataSem_state_stack_frame_sizes s /\ state_locals_size s' =
     dataSem_state_locals_size s /\ dataSem_state_global
   s' = dataSem_state_global s /\ compile s' = dataSem_state_compile
     s /\ compile_oracle s' = dataSem_state_compile_oracle s /\
     state_clock
   s' = dataSem_state_clock s /\ dataSem_state_tstamps
   s' = (if ys = [] then dataSem_state_tstamps s else OPTION_MAP
     SUC (dataSem_state_tstamps s))`,
  CHEAT_TAC);;

(* Variant of call_env_push_env_dec_clock_lift that also absorbs a `locals
   := insert k v t.locals` field update inside the dec_clock. *)
(* [local] *)
let call_env_push_env_dec_clock_lift_locals = prove
 (`wordSem_call_env (args:('a word_loc) list) b (wordSem_push_env
  (y1,y2) NONE
     (wordSem_dec_clock (wordSem_state_termdep_fupd (K tp)
       (wordSem_state_clock_fupd (K ck') (wordSem_state_locals_fupd (K
       (sptree_insert k v (wordSem_state_locals t)))
       (t:('a,'c,'ffi)wordSem_state)))))) = wordSem_state_termdep_fupd
       (K tp) (state_clock_fupd (K (ck' - 1))
   (wordSem_call_env args b (wordSem_push_env (y1,y2) NONE t)))`,
  CHEAT_TAC);;

(* [local] *)
let call_env_push_env_dec_clock_stack_max = prove
 (`state_stack_max
     (wordSem_call_env args ls (wordSem_push_env env F
       (word_bignumProof_dec_clock (s:('c,'ffi)dataSem_state)))) =
       OPTION_MAP2 MAX
         (OPTION_MAP2 MAX (dataSem_state_stack_max s)
            (OPTION_MAP2 (((+)):num->num->num)
              (dataSem_state_locals_size s) (size_of_stack
              (dataSem_state_stack s))))
         (OPTION_MAP2 (((+)):num->num->num)
            (OPTION_MAP2 (((+)):num->num->num)
              (dataSem_state_locals_size s) (size_of_stack
              (dataSem_state_stack s))) ls)`,
  CHEAT_TAC);;

(* [local] *)
let option_le_stackmax_bridge = prove
 (`!(m:num option) (l_size:num option) (s_size:num option)
     (ls_R:num option) (ls_Re:num option).
     option_le
       (OPTION_MAP2 MAX
          (OPTION_MAP2 MAX
             (OPTION_MAP2 MAX m (OPTION_MAP2 (((+)):num->num->num)
               l_size s_size))
             (OPTION_MAP2 (((+)):num->num->num)
                (OPTION_MAP2 (((+)):num->num->num) l_size s_size)
                  ls_R))
          (OPTION_MAP2 (((+)):num->num->num) (OPTION_MAP2 MAX ls_R
            ls_Re)
             (OPTION_MAP2 (((+)):num->num->num) s_size l_size)))
       (OPTION_MAP2 MAX m
          (OPTION_MAP2 (((+)):num->num->num) (OPTION_MAP2 MAX ls_R
            ls_Re)
             (OPTION_MAP2 (((+)):num->num->num) s_size l_size)))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:7491-7810: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   assign_FromList *)

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
 (`dataSem_do_app (closLang_MemOp (closLang_RefByte fl)) [dataSem_Number
  i; dataSem_Number (&(w2n (w:word8)))] (s:('c,'ffi)dataSem_state) =
  Rval (v,s') ==>
   (?ptr. v = dataSem_RefPtr T ptr /\ ptr = (minimal p. ~(p IN domain
     (dataSem_state_refs s))) /\ (&0) <= i /\
         s' = dataSem_state_peak_heap_length_fupd (K
                  ((\k op_args s. MAX (dataSem_state_peak_heap_length
                    s) (size_of_heap_args op_args s + k))
                    (space_consumed s (closLang_MemOp
                      (closLang_RefByte fl))
                       [dataSem_Number i; dataSem_Number (&(w2n w))])
                    [dataSem_Number i; dataSem_Number (&(w2n w))] s))
                      (dataSem_state_safe_for_space_fupd (K
                  (((num_of_int i DIV (arch_size
                    (dataSem_state_limits s) DIV 8) <
                     2 EXP arch_size (dataSem_state_limits s) DIV
                       arch_size (dataSem_state_limits s) /\
                     num_of_int i DIV (arch_size
                       (dataSem_state_limits s) DIV 8) + 1 <
                     2 EXP limits_length_limit (dataSem_state_limits
                       s) /\
                     small_num (limits_arch_64_bit
                       (dataSem_state_limits s)) i) /\
                    no_thunks_in_refs (dataSem_state_refs s) /\
                    (\k op_args s.
                   dataSem_state_safe_for_space s /\
                     size_of_heap_args op_args s + k <=
                     limits_heap_limit (dataSem_state_limits s))
                      (space_consumed s (closLang_MemOp
                        (closLang_RefByte fl))
                         [dataSem_Number i; dataSem_Number (&(w2n
                           w))])
                      [dataSem_Number i; dataSem_Number (&(w2n w))]
                        s) /\
                   the F
                     (OPTION_MAP ((>) (stack_limit
                       (dataSem_state_limits s)))
                        (OPTION_MAP2 (+)
                           (stack_consumed
                             (dataSem_state_stack_frame_sizes s)
                             (dataSem_state_limits s)
                              (closLang_MemOp (closLang_RefByte fl))
                                [dataSem_Number i; dataSem_Number (&(w2n
                                w))])
                           (OPTION_MAP2 (+) (size_of_stack
                             (dataSem_state_stack s))
                             (dataSem_state_locals_size
                              s)))))) (dataSem_state_space_fupd (K 0)
                                (dataSem_state_refs_fupd (K
                                (sptree_insert ptr (bvlSem_ByteArray fl
                                (REPLICATE (num_of_int i) w))
                                (dataSem_state_refs s)))
                                (dataSem_state_stack_max_fupd (K
                  (OPTION_MAP2 MAX (dataSem_state_stack_max s)
                    (OPTION_MAP2 (+)
                       (stack_consumed
                         (dataSem_state_stack_frame_sizes s)
                         (dataSem_state_limits s)
                          (closLang_MemOp (closLang_RefByte fl))
                            [dataSem_Number i; dataSem_Number (&(w2n
                            w))])
                       (OPTION_MAP2 (+) (size_of_stack
                         (dataSem_state_stack s))
                         (dataSem_state_locals_size s))))) s)))))`,
  CHEAT_TAC);;

(* Helper: lift inner-with on a dec_clock'd state to outer-with on call_env/push_env.
   Used to bridge the post-Call evaluate term to the shape expected by
   evaluate_IMP_domain_union (which has outer-with). *)
(* [local] *)
let call_env_push_env_dec_clock_lift = prove
 (`wordSem_call_env (args:('a word_loc) list) b (wordSem_push_env
  (y1,y2) NONE
     (wordSem_dec_clock (wordSem_state_termdep_fupd (K tp)
       (wordSem_state_clock_fupd (K ck')
       (t:('a,'c,'ffi)wordSem_state))))) = wordSem_state_termdep_fupd (K
       tp) (state_clock_fupd (K (ck' - 1))
   (wordSem_call_env args b (wordSem_push_env (y1,y2) NONE t)))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:7889-8149: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   assign_RefByte *)

let lookup_set_var = prove
 (`sptree_lookup x (state_locals (wordSem_set_var x y z)) = SOME y`,
  CHEAT_TAC);;

(* [local] *)
let lookup_2_call_env = prove
 (`sptree_lookup 0 (state_locals (wordSem_call_env (CONS x ts) a1 a2)) =
  SOME x /\
   sptree_lookup 2 (state_locals (wordSem_call_env (CONS x (CONS y
     ts)) a1 a2)) = SOME y /\
   sptree_lookup 4 (state_locals (wordSem_call_env (CONS x (CONS y
     (CONS z ts))) a1 a2)) = SOME z`,
  CHEAT_TAC);;

(* Binary (two-argument) instance of AllocVar_thm_nary, used by assign_RefArray. *)
(* HOL4 data_to_word_assignProofScript.sml:8166-8192: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   AllocVar_thm_binary *)

(* HOL4 data_to_word_assignProofScript.sml:8194-8681: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   assign_RefArray *)

(* [local] *)
let LENGTH_n2mw_1 = prove
 (`LENGTH ((n2mw n):('a word) list) = 1 <=> ~(n = 0) /\ n < dimword
  (:'a)`,
  CHEAT_TAC);;

(* [local] *)
let WordFromInt_DIV_LEMMA = prove
 (`kk < B * B /\ 0 < B ==> B * (kk DIV B) <= B * B - B`,
  CHEAT_TAC);;

(* [local] *)
let explode_less_32 = prove
 (`(!n. n < 32 ==> P (n:num)) <=>
   P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\ P 6 /\ P 7 /\ P 8 /\ P 9
     /\
   P 10 /\ P 11 /\ P 12 /\ P 13 /\ P 14 /\ P 15 /\ P 16 /\ P 17 /\ P
     18 /\ P 19 /\
   P 20 /\ P 21 /\ P 22 /\ P 23 /\ P 24 /\ P 25 /\ P 26 /\ P 27 /\ P
     28 /\ P 29 /\
   P 30 /\ P 31`,
  CHEAT_TAC);;

(* [local] *)
let LESS_IMP_NOT_BIT = prove
 (`!k n. n < 2 EXP k ==> ~(BIT k n)`,
  CHEAT_TAC);;

(* Smallnum_alt *)
let smallnum_alt = prove
 (`Smallnum i =
    (if i < (&0) then ((n2w 0) - n2w (num_of_int (--i))) << 2 else
      n2w (num_of_int i) << 2)`,
  CHEAT_TAC);;

(* [local] *)
let BIT_lemma = prove
 (`BIT n (2 EXP k - i) <=> (if n < k /\ i < 2 EXP k /\ ~(i = 0) then
  BIT n (2 EXP (MAX n i + 1) - i) else BIT n (2 EXP k - i))`,
  CHEAT_TAC);;

(* [local] *)
let BIT_Lemma2 = prove
 (`BIT m (2 EXP k - n) = (if ~(n = 0) /\ n <= 2 EXP m /\ m < k then T
  else BIT m (2 EXP k - n))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:8766-9236: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   assign_WordFromInt *)

(* HOL4 data_to_word_assignProofScript.sml:9238-9304: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   assign_TagEq *)

let all_ones_get_addr = prove
 (`all_ones (data_to_word_config_len_bits c +
  (data_to_word_config_tag_bits c + 1)) 0 &&
   get_addr c ptr (wordLang_Word (ptr_bits c tag2 len2)) =
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
   len < 2 EXP data_to_word_config_len_bits c - 1 /\
     data_to_word_config_len_bits
   c + data_to_word_config_tag_bits c < dimindex (:'a) ==>
   ((ptr_bits c tag2 len2 || (n2w 1) =
     ptr_bits c tag len || ((n2w 1):'a word)) <=>
    (tag2 = tag /\ len2 = len))`,
  CHEAT_TAC);;

let maxout_bits_0 = prove
 (`maxout_bits 0 b e = (n2w 0)`,
  CHEAT_TAC);;

let ptr_bits_eq_ptr_bits_len_only = prove
 (`len < 2 EXP data_to_word_config_len_bits c - 1 /\
  data_to_word_config_len_bits
   c < dimindex (:'a) ==>
   ((ptr_bits c 0 len2 || (n2w 1) =
     ptr_bits c 0 len || ((n2w 1):'a word)) <=>
    (len2 = len))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:9429-9538: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   assign_TagLenEq *)

let all_ones_and_1 = prove
 (`~(k = 0) ==> all_ones k 0 && (n2w 1) = (n2w 1)`,
  CHEAT_TAC);;

let all_ones_and_ptr_bits_tag_0 = prove
 (`all_ones (data_to_word_config_len_bits c + 1) 0 && ptr_bits c tag
  len = ptr_bits c 0 len`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:9555-9677: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   assign_LenEq *)

let state_rel_upd_safe_pkheap = prove
 (`!c l1 l2 s lcl hpk r locs. data_to_word_gcProof_state_rel c l1 l2
  (state_stack_max_fupd (K NONE) (dataSem_state_space_fupd (K 0)
  (state_locals_fupd (K lcl) s)))
                r NONE locs <=>
   data_to_word_gcProof_state_rel c l1 l2
                (dataSem_state_peak_heap_length_fupd (K hpk)
                  (dataSem_state_safe_for_space_fupd (K F)
                  (dataSem_state_space_fupd (K 0) (state_stack_max_fupd
                  (K NONE) (state_locals_fupd (K lcl) s)))))
                r NONE locs`,
  CHEAT_TAC);;

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

(* [simp] *)
let state_rel_ignore_safe_for_space = prove
 (`data_to_word_gcProof_state_rel c l1 l2
  (dataSem_state_safe_for_space_fupd (K m) (dataSem_state_space_fupd (K
  s) (state_locals_fupd (K l) x))) r t locs <=>
   data_to_word_gcProof_state_rel c l1 l2 (dataSem_state_space_fupd
     (K s) (state_locals_fupd (K l) x)) r t locs`,
  CHEAT_TAC);;

(* [simp] *)
let state_rel_peak_heap_length = prove
 (`data_to_word_gcProof_state_rel c l1 l2
  (dataSem_state_peak_heap_length_fupd (K m) (dataSem_state_space_fupd
  (K s) (state_locals_fupd (K l) x))) r t locs <=>
   data_to_word_gcProof_state_rel c l1 l2 (dataSem_state_space_fupd
     (K s) (state_locals_fupd (K l) x)) r t locs`,
  CHEAT_TAC);;

(* opt_map_plus_zero_id[simp] *)
let data_to_word_assignProof_opt_map_plus_zero_id = prove
 (`!n. OPTION_MAP2 (+) (SOME 0) n = (n:num option)`,
  CHEAT_TAC);;

(* [simp] *)
let small_num_small_int = prove
 (`good_dimindex (:'a) ==>
   small_num (dimindex (:'a) = 64) = small_int (:'a)`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let memory_rel_small_int = prove
 (cake_as_vars (fun () ->
    `memory_rel c be ts refs sp st m dm (CONS (dataSem_Number
  i,wordLang_Word (w:'a word)) vars) /\
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
   w2i (Smallnum i1 + ((Smallnum i2):'a word)) = w2i (Smallnum
     i1:'a word) + w2i (Smallnum i2:'a word)`,
  CHEAT_TAC);;

(* TODO: move? *)
(* OPTION_MAP2_NONE[simp] *)
let data_to_word_assignProof_OPTION_MAP2_NONE = prove
 (`(OPTION_MAP2 f NONE n = NONE) /\ (OPTION_MAP2 f n NONE = NONE)`,
  CHEAT_TAC);;

let state_rel_IMP_arch_64_bit = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) xs locs ==>
   (limits_arch_64_bit (dataSem_state_limits s) = (dimindex (:'a) =
     64))`,
  CHEAT_TAC);;

let cut_state_opt_twice = prove
 (`dataSem_cut_state_opt names_opt s = SOME x ==>
   dataSem_cut_state_opt names_opt x = SOME x`,
  CHEAT_TAC);;

let cut_state_opt_extra_const = prove
 (`dataSem_cut_state_opt names_opt s = SOME x ==>
  dataSem_state_stack_frame_sizes
   s = dataSem_state_stack_frame_sizes x /\ state_locals_size
   s = state_locals_size x`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:9812-9964: a theorem whose
   statement HOL Light does not read (tools/unstated.py): assign_Add *)

let small_int_Smallnum_sub = prove
 (`good_dimindex (:'a) /\ small_int (:'a) (i1 - i2) ==>
   Smallnum i1 - ((Smallnum i2):'a word) = Smallnum (i1 - i2)`,
  CHEAT_TAC);;

let small_int_w2i_Smallnum_sub = prove
 (`good_dimindex (:'a) /\ small_int (:'a) (i1 - i2) /\ small_int (:'a)
  i1 /\ small_int (:'a) i2 ==>
   w2i (Smallnum i1 - ((Smallnum i2):'a word)) = w2i (Smallnum
     i1:'a word) - w2i (Smallnum i2:'a word)`,
  CHEAT_TAC);;

(* [local] *)
let word_bit_0_sub_lemma = prove
 (`!w1 (w2:'a word). ~(word_bit 0 w1) /\ ~(word_bit 0 w2) ==>
  ~(word_bit 0 (w1 + --(n2w 1) * w2))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:10003-10158: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_Sub *)

let cut_state_opt_IMP_ffi = prove
 (`dataSem_cut_state_opt names_opt s = SOME x ==> state_ffi x =
  state_ffi s`,
  CHEAT_TAC);;

let quad_times_div_half_double = prove
 (`(4 * j) DIV 2 = 2 * (j:num)`,
  CHEAT_TAC);;

let w2n_mul_less = prove
 (`!w w'.
     (w2n (w:'a word) * w2n (w':'a word)) < dimword (:'a) EXP 2`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:10186-10358: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_Mult *)

let word_bit_lsr_dimindex_1 = prove
 (`word_bit 0 ((w1 >>> (dimindex (:'a) - 1)):'a word) <=> word_msb w1`,
  CHEAT_TAC);;

let state_rel_Number_IMP = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s
  (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    wordSem_get_var a1 (state_locals s) = SOME (dataSem_Number i1) /\
    sptree_lookup (adjust_var a1) (wordSem_state_locals t) = SOME v1
      ==>
    (?w1. (v1 = wordLang_Word w1) /\
         (~(word_bit 0 w1) <=> small_int (:'a) i1) /\
         (~(word_msb w1) /\ ~(word_bit 0 w1) ==> (&0) <= i1 /\ w1 =
           n2w (4 * num_of_int i1)))`,
  CHEAT_TAC);;

let option_le_add_comm = prove
 (`option_le (OPTION_MAP2 (+) a b) c ==>
     option_le (OPTION_MAP2 (+) b a) c`,
  CHEAT_TAC);;

let IN_adjust_set_IN = prove
 (`y IN domain (adjust_set x) ==> (y - 2) DIV 2 IN domain x`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:10403-10709: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_Div *)

(* HOL4 data_to_word_assignProofScript.sml:10711-11022: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_Mod *)

(* HOL4 data_to_word_assignProofScript.sml:11024-11081: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_LengthByte *)

(* HOL4 data_to_word_assignProofScript.sml:11083-11132: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_Length *)

(* HOL4 data_to_word_assignProofScript.sml:11134-11193: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_LengthBlock *)

(* HOL4 data_to_word_assignProofScript.sml:11195-11212: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_BoundsCheckBlock *)

(* HOL4 data_to_word_assignProofScript.sml:11214-11287: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_BoundsCheckBlock *)

(* HOL4 data_to_word_assignProofScript.sml:11289-11304: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_BoundsCheckArray *)

(* HOL4 data_to_word_assignProofScript.sml:11306-11367: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_BoundsCheckArray *)

(* HOL4 data_to_word_assignProofScript.sml:11369-11386: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_BoundsCheckByte *)

(* HOL4 data_to_word_assignProofScript.sml:11388-11451: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_BoundsCheckByte *)

let assign_LessConstSmall = prove
 (`wordSem_assign c secn l dest (closLang_IntOp (closLang_LessConstSmall
  i)) args names =
      (match args with [v1] -> (wordLang_If asm_Less (adjust_var v1)
        (Imm (n2w (4 * i)))
                  (wordLang_Assign (adjust_var dest)
                    (word_depth_Const (n2w 18:'a word)))
                  (wordLang_Assign (adjust_var dest)
                    (word_depth_Const (n2w 2:'a word))),l) | _5 ->
                    ((asm_Skip:'a wordLang_prog),l))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:11464-11503: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_LessSmallConst *)

(* HOL4 data_to_word_assignProofScript.sml:11505-11544: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_BoolNot *)

(* HOL4 data_to_word_assignProofScript.sml:11546-11590: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_BoolTest *)

(* HOL4 data_to_word_assignProofScript.sml:11592-11640: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_WordTest *)

(* HOL4 data_to_word_assignProofScript.sml:11642-11702: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   Compare1_code_thm *)

let word_exp_insert = prove
 (`(~(m = n) ==>
     (wordSem_word_exp (state_locals_fupd (K (sptree_insert n w
       (state_locals t))) t) (real_addr c m) =
      wordSem_word_exp t (real_addr c m))) /\
    (~(m IN {n,n1}) ==>
     (wordSem_word_exp (state_locals_fupd (K (sptree_insert n w
       (sptree_insert n1 w1 (state_locals t)))) t) (real_addr c m) =
      wordSem_word_exp t (real_addr c m)))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:11719-11829: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   Compare_code_thm *)

let word_cmp_Less_word_cmp_res = prove
 (`!i i'. good_dimindex (:'a) ==>
           (wordSem_word_cmp asm_Less (word_cmp_res i i') ((n2w
             1):'a word) <=> i < i')`,
  CHEAT_TAC);;

let word_cmp_NotLess_word_cmp_res = prove
 (`!i i'. good_dimindex (:'a) ==>
           (wordSem_word_cmp asm_NotLess ((n2w 1):'a word)
             (word_cmp_res i i') <=> (i <= i'))`,
  CHEAT_TAC);;

let word_cmp_not_NotLess_word_cmp_res = prove
 (`!i i'. good_dimindex (:'a) ==>
           (~(wordSem_word_cmp asm_NotLess ((n2w 1):'a word)
             (word_cmp_res i i')) <=> (i' < i))`,
  CHEAT_TAC);;

let not_word_cmp_Less_word_cmp_res = prove
 (`!i i'. good_dimindex (:'a) ==>
           (~(wordSem_word_cmp asm_Less (word_cmp_res i i') ((n2w
             1):'a word)) <=> (i' <= i))`,
  CHEAT_TAC);;

let IMP_spt_eq = prove
 (`sptree_wf t1 /\ sptree_wf t2 /\ (!n. sptree_lookup n t1 =
  sptree_lookup n t2) ==> (t1 = t2)`,
  CHEAT_TAC);;

let env_to_list_cut_env_IMP = prove
 (`env_to_list x (wordSem_state_permute t) = (l,permute) /\
  wordSem_cut_env y s = SOME x ==>
    (fromAList l = x)`,
  CHEAT_TAC);;

let dimword_LESS_MustTerminate_limit = prove
 (`good_dimindex (:'a) ==> dimword (:'a) < MustTerminate_limit (:'a) -
  1`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:11897-12030: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_Less *)

(* HOL4 data_to_word_assignProofScript.sml:12032-12166: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_LessEq *)

let word_exp_set_var_ShiftVar = prove
 (`wordSem_word_exp (wordSem_set_var v (wordLang_Word w) t) (ShiftVar
  sow v n) =
    OPTION_MAP wordLang_Word (match sow with Lsl -> SOME (w << n) |
      Lsr -> SOME (w >>> n) | Asr -> SOME (w >> n) | Ror -> SOME
      (word_ror w n))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:12179-12205: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   MemEqList_thm *)
(* HOL4 data_to_word_assignProofScript.sml:12206-12207: a theorem
   that HOL4 states as the value of an ML expression: MemEqList_thm *)

(* HOL4 data_to_word_assignProofScript.sml:12209-12385: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_EqualConst *)

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
  `sane_locals_size t = (state_locals_size t = sptree_lookup
  Equal_location (wordSem_state_stack_size t) \/ state_locals_size
                         t = sptree_lookup Equal1_location
                           (wordSem_state_stack_size t))`;;

(* HOL4 data_to_word_assignProofScript.sml:12421-12764: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   Equal_code_lemma *)

(* HOL4 data_to_word_assignProofScript.sml:12766-12797: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   Equal_code_thm *)

(* MIN_SUB[local] *)
let data_to_word_assignProof_MIN_SUB = prove
 (`MIN a b - c = MIN (a - c) (b - c)`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:12805-12957: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_Equal *)

(* HOL4 data_to_word_assignProofScript.sml:12959-13150: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_WordOpW8 *)

(* HOL4 data_to_word_assignProofScript.sml:13152-13154: the ML values
   that the definitions below antiquote *)

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

(* HOL4 data_to_word_assignProofScript.sml:13182-13315: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   evaluate_WordOp64_on_32 *)

let IMP_encode_header_NOT_NONE = prove
 (`dimindex (:'a) = 32 /\ 1 < data_to_word_config_len_size c /\ 1 < 30
  - data_to_word_config_len_size c ==> ~(encode_header c 3 2 =
  (NONE:('a word) option))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:13324-13463: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_WordOpW64 *)

(* HOL4 data_to_word_assignProofScript.sml:13465-13732: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_WordShiftW8 *)

(* HOL4 data_to_word_assignProofScript.sml:13734-13736: the ML values
   that the definitions below antiquote *)

(* HOL4 data_to_word_assignProofScript.sml:13738-13830: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   evaluate_WordShift64_on_32 *)

(* HOL4 data_to_word_assignProofScript.sml:13832-13988: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_WordShiftW64 *)

(* HOL4 data_to_word_assignProofScript.sml:13990-13992: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:13994-13996: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:13998-14000: ML code, not
   ported *)

(* HOL4 data_to_word_assignProofScript.sml:14002-14004: ML code, not
   ported *)

let w2w_select_id = prove
 (`dimindex (:'a) = 64 ==>
    ((w2w:'a word->word64) ((63 >< 0) w)) = w`,
  CHEAT_TAC);;

let extract_append_id = prove
 (`dimindex (:'a) = 32 ==>
    ((((63 >< 32) w):'a word) @@ (((31 >< 0) w):'a word)) =
      (w:word64)`,
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

(* HOL4 data_to_word_assignProofScript.sml:14057-14157: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_FP_cmp *)

(* HOL4 data_to_word_assignProofScript.sml:14159-14319: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_FP_top *)

(* HOL4 data_to_word_assignProofScript.sml:14321-14465: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_FP_bop *)

(* HOL4 data_to_word_assignProofScript.sml:14467-14590: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_FP_uop *)

(* HOL4 data_to_word_assignProofScript.sml:14592-14615: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_Label *)

(* do_app_Ref *)
let data_to_word_assignProof_do_app_Ref = prove
 (`dataSem_do_app (closLang_MemOp closLang_Ref) vals x =
    (match consume_space (LENGTH vals + 1) x with
      NONE -> Rerr (Rabort Rtype_error) | SOME s1 ->
      Rval
      (dataSem_RefPtr T (minimal ptr. ~(ptr IN domain (state_refs
        s1))),state_stack_max_fupd (K (state_stack_max
             (do_stack (closLang_MemOp closLang_Ref) vals
               (do_lim_safe s1 (closLang_MemOp closLang_Ref) vals))))
               (dataSem_state_safe_for_space_fupd (K
               (dataSem_state_safe_for_space (do_stack (closLang_MemOp
               closLang_Ref) vals (do_lim_safe s1 (closLang_MemOp
               closLang_Ref) vals)))) (state_refs_fupd (K (sptree_insert
               (minimal ptr. ~(ptr IN domain (state_refs s1)))
               (bvlSem_ValueArray vals) (state_refs s1)))
         s1))))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:14634-14694: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_Ref *)

(* HOL4 data_to_word_assignProofScript.sml:14696-14738: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_Update *)

(* HOL4 data_to_word_assignProofScript.sml:14740-14807: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_El *)

(* HOL4 data_to_word_assignProofScript.sml:14809-14872: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_ElemAt *)

(* HOL4 data_to_word_assignProofScript.sml:14874-14982: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_UpdateByte *)

(* HOL4 data_to_word_assignProofScript.sml:14984-15073: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_DerefByte *)

(* HOL4 data_to_word_assignProofScript.sml:15075-15095: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_Const *)

(* HOL4 data_to_word_assignProofScript.sml:15097-15117: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_GlobalsPtr *)

(* HOL4 data_to_word_assignProofScript.sml:15119-15152: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_Global *)

(* HOL4 data_to_word_assignProofScript.sml:15154-15202: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_SetGlobal *)

(* HOL4 data_to_word_assignProofScript.sml:15204-15263: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_SetGlobalsPtr *)

let IMP = prove
 (`b1 \/ b2 <=> ~b1 ==> b2`,
  CHEAT_TAC);;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let memcopy_def,memcopy_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3,x4). (\n. n) x0)`
  [`memcopy k a1 a2 m dm =
     (if k = 0 then SOME m else
       if a1 IN dm /\ a2 IN dm then
         memcopy (k - 1) (a1 + bytes_in_word) (a2 +
           bytes_in_word) ((a2 =+ m a1) m) dm else NONE)`];;

(* HOL4 data_to_word_assignProofScript.sml:15279-15315: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   MemCopy_thm *)

(* HOL4 data_to_word_assignProofScript.sml:15317-15319: a theorem
   that HOL4 states as the value of an ML expression:
   assign_ConsExtend_expand *)

(* get_vars_IMP_domain *)
let data_to_word_assignProof_get_vars_IMP_domain = prove
 (`!xs s y.
      wordSem_get_vars xs s = SOME y ==>
      ALL (\x. x IN domain s) xs`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let memory_rel_IMP_free_space = prove
 (cake_as_vars (fun () ->
    `memory_rel c be ts refs sp st m dm vars ==>
      (?nfree curr other.
        FLOOKUP st NextFree = SOME (wordLang_Word nfree) /\
        FLOOKUP st CurrHeap = SOME (wordLang_Word curr) /\
        (word_list_exists nfree sp * other) (fun2set (m,dm)))`),
  CHEAT_TAC);;

let IMP_store_list_SOME = prove
 (`!ws a n m dm other.
      (word_list_exists a n * other) (fun2set (m,dm)) /\ LENGTH ws <=
        n ==>
      (?m1. data_to_word_memoryProof_store_list a ws m dm = SOME m1
        /\
           (misc_word_list a ws *
            word_list_exists (a + bytes_in_word * n2w (LENGTH ws)) (n
              - LENGTH ws) *
            other) (fun2set (m1,dm)))`,
  CHEAT_TAC);;

let get_vars_cut_env = prove
 (`!vs bs.
      dataSem_cut_env nms x1 = SOME x2 /\
      dataSem_get_vars vs x1 = SOME bs /\
      ALL (\v. v IN domain nms) vs ==>
      dataSem_get_vars vs x2 = SOME bs`,
  CHEAT_TAC);;

let word_exp_real_addr_some_value = prove
 (`FLOOKUP (wordSem_state_store s3) CurrHeap = SOME (wordLang_Word curr)
  /\
    wordSem_get_var a s3 = SOME (wordLang_Word ww) /\
    good_dimindex (:'a) /\ shift_length c < dimindex (:'a) ==>
    (?wx. wordSem_word_exp (s3:('a,'c,'ffi)wordSem_state)
      (real_addr c a) = SOME (wordLang_Word wx))`,
  CHEAT_TAC);;

let store_list_APPEND = prove
 (`!xs ys a m.
      data_to_word_memoryProof_store_list a (APPEND xs ys) m dm =
      (match data_to_word_memoryProof_store_list a xs m dm with
        NONE -> NONE | SOME m1 -> data_to_word_memoryProof_store_list
        (a + bytes_in_word * n2w (LENGTH xs)) ys m1 dm)`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let memory_rel_store_list_to_unused = prove
 (cake_as_vars (fun () ->
    `!ws2 m dm m1.
        memory_rel c be ts refs n st m dm vars /\
        data_to_word_memoryProof_store_list nfree ws2 m dm = SOME
          m1 /\
        FLOOKUP st NextFree = SOME (wordLang_Word nfree) /\ LENGTH
          ws2 <= n ==>
        memory_rel c be ts refs n st m1 dm vars`),
  CHEAT_TAC);;

let get_vars_delete_lemma = prove
 (`!t7. wordSem_get_vars (MAP adjust_var t7) (state_locals_fupd (K
               (sptree_insert 9 x9
                 (sptree_insert 7 x7
                    (sptree_insert 5 x5
                       (sptree_insert 1 x1 (state_locals s1)))))) s1)
                         =
      wordSem_get_vars (MAP adjust_var t7) s1`,
  CHEAT_TAC);;

let INTRO_IS_SOME = prove
 (`(?v. x = SOME v) <=> IS_SOME x`,
  CHEAT_TAC);;

let STAR_fun2set_IMP_SEP_T = prove
 (`(p * q) (fun2set (m,dm)) ==> (p * SEP_T) (fun2set (m,dm))`,
  CHEAT_TAC);;

let IMP_memcopy_lemma = prove
 (`memory_rel c (be s1) ts (state_refs x) sp (wordSem_state_store s1) m1
  (wordSem_state_mdomain s1)
      (CONS (dataSem_Block ts' n' l',wordLang_Word w_ptr) (APPEND
        (ZIP ys7 ws1) vars)) /\
    startptr < LENGTH l' /\ LENGTH ys7 = LENGTH ws1 /\ good_dimindex
      (:'a) /\
    sptree_lookup (adjust_var a1) (state_locals s1) = SOME
      (wordLang_Word (w_ptr:'a word)) /\
    wordSem_word_exp s1 (real_addr c (adjust_var a1)) = SOME
      (wordLang_Word wx) ==>
    memory_rel c (be s1) ts (state_refs x) sp (wordSem_state_store
      s1) m1 (wordSem_state_mdomain s1)
      (CONS (dataSem_Block ts' n' l',wordLang_Word w_ptr)
       (APPEND (ZIP (APPEND ys7 [EL startptr l']) (APPEND ws1 [m1 (wx
         + bytes_in_word + bytes_in_word * n2w startptr)])) vars)) /\
    (wx + bytes_in_word + bytes_in_word * n2w startptr) IN
      wordSem_state_mdomain s1`,
  CHEAT_TAC);;

let IMP_memcopy = prove
 (`!len startptr m1 m2 ws1 ys7 k ts.
         memory_rel c (be s1) ts (state_refs x) sp
           (wordSem_state_store s1) m1 (wordSem_state_mdomain s1)
           (CONS (dataSem_Block ts' n' l',wordLang_Word w_ptr)
             (APPEND (ZIP ys7 ws1) vars)) /\
         (misc_word_list nfree (CONS (wordLang_Word full_header) ws1)
           *
          word_list_exists
            (nfree + bytes_in_word * n2w (SUC (LENGTH ws1))) k *
              other)
              (fun2set (m1,wordSem_state_mdomain s1)) /\ len <= k /\
                good_dimindex (:'a) /\
         sptree_lookup (adjust_var a1) (state_locals s1) = SOME
           (wordLang_Word (w_ptr:'a word)) /\
         wordSem_word_exp s1 (real_addr c (adjust_var a1)) = SOME
           (wordLang_Word wx) /\
         FLOOKUP (wordSem_state_store s1) NextFree = SOME
           (wordLang_Word nfree) /\
         startptr + len <= LENGTH l' /\
         LENGTH ws1 + len < sp /\
         LENGTH ys7 = LENGTH ws1 ==>
         (?m2 ws2.
           memcopy len (wx + bytes_in_word + bytes_in_word * n2w
             startptr)
             (nfree + bytes_in_word * n2w (LENGTH ws1 + 1)) m1
               (wordSem_state_mdomain s1) =
             SOME m2 /\
           (misc_word_list nfree (CONS (wordLang_Word full_header)
             (APPEND ws1 ws2)) * SEP_T)
             (fun2set (m2,wordSem_state_mdomain s1)) /\
           LENGTH ws2 = len /\
           memory_rel c (be s1) ts (state_refs x) sp
             (wordSem_state_store s1) m2 (wordSem_state_mdomain s1)
             (APPEND (ZIP (APPEND ys7 (TAKE len (DROP startptr
               l'))) (APPEND ws1 ws2)) vars))`,
  CHEAT_TAC);;

(* cut_envs_adjust_sets_insert_ODD *)
let data_to_word_assignProof_cut_envs_adjust_sets_insert_ODD = prove
 (`ODD n ==>
   cut_envs (adjust_sets names) (sptree_insert n w t) =
   cut_envs (adjust_sets names) t`,
  CHEAT_TAC);;

let IN_domain_adjust_set_IMP = prove
 (`x IN domain (adjust_set the_names) ==>
   (?xa. x = adjust_var xa /\ xa IN domain the_names)`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:15573-16148: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_ConsExtend *)

(* HOL4 data_to_word_assignProofScript.sml:16150-16244: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_Cons *)

(* HOL4 data_to_word_assignProofScript.sml:16246-16480: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_FFI *)

(* HOL4 data_to_word_assignProofScript.sml:16482-16618: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_FFI_final *)

let getWords_acc = prove
 (`!ws acc.
     getWords ws acc =
       (let (cs,c) = getWords ws [] in (APPEND (REVERSE acc) cs,c))`,
  CHEAT_TAC);;

let getWords_thm = prove
 (`!ws cs rest.
     getWords ws [] = (cs,rest) ==>
     ws = APPEND (MAP (\(b,c). (b,wordLang_Word c)) cs) rest`,
  CHEAT_TAC);;

let store_list_word_cond_add_IMP = prove
 (`!y2 m a m1 free'.
     data_to_word_memoryProof_store_list free' (MAP (word_cond_add c
       (a:'a word))
       (MAP (\(b,c). (b,wordLang_Word c)) y2)) m dm = SOME m1 ==>
     const_addresses free' y2 dm /\
     const_writes free' (a << (shift_length c -
       backend_common_word_shift (:'a))) y2 m = m1`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:16662-16736: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   evaluate_StoreAnyConsts *)

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
   bignum_size (dimindex (:'a) = 64) i = LENGTH (n2mw (num_of_int
     (abs i)):('a word) list) + 1`,
  CHEAT_TAC);;

let _ = do_list hide_constant ["free"];;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let parts_to_words_NONE = prove
 (cake_as_vars (fun () ->
    `!parts' (off:'a word) m aa (t:('a,'c,'ffi)wordSem_state)
  (s:('c,'ffi)dataSem_state).
       parts_to_words c m aa parts' off = NONE /\ good_dimindex
         (:'a) /\
       heap_in_memory_store heap a sp sp1 gens c
         (wordSem_state_store t) (wordSem_state_memory t)
         (wordSem_state_mdomain t) limit ==>
       limits_inv (dataSem_state_limits s) (FLOOKUP
         (wordSem_state_store t) HeapLength) (wordSem_state_stack_limit
         t) (data_to_word_config_len_size
                  c) (data_to_word_config_has_fp_ops c)
                    (data_to_word_config_has_fp_tern c) ==>
       EX ((~) o lim_safe_part (dataSem_state_limits s)) parts'`),
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:16826-16923: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_Build *)


(* HOL4 data_to_word_assignProofScript.sml:16926: ML code, not ported *)

(* [local] *)
let join_lemma = prove
 (`(b1 ==> x) /\ (b2 ==> x) ==> (b1 \/ b2 ==> x)`,
  CHEAT_TAC);;

(* HOL4 data_to_word_assignProofScript.sml:16931-16933: a theorem
   that HOL4 states as the value of an ML expression: imp_assign *)

(* HOL4 data_to_word_assignProofScript.sml:16935-16966: a theorem
   whose statement HOL Light does not read (tools/unstated.py):
   assign_thm *)

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["free";
   "parts";
   "vars"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
