(* ======================================================== *)
(*  stack_removeProof: ported from HOL4's
    compiler/backend/proofs/stack_removeProofScript.sml
    A proof theory about stack_remove.ml, with 23 definitions and
    113 theorems.  Needed by backendProof.ml, lab_to_targetProof.ml
    and stack_to_labProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for stack_remove
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/semantics/stackProps.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_names.ml";;
needs "compiler/backend/stack_remove.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/alignment.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "lib/toto.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/semantics.ml";;

cake_hide ["C"; "gen_gc"; "num_stubs"; "shift"];;

cake_hide_consts
  ["code_buffer","code_buffer";
   "data_buffer","data_buffer"];;

(* HOL4 stack_removeProofScript.sml:16: ML code, not ported *)
(* HOL4 stack_removeProofScript.sml:17: the overload num_stubs, which
   the port expands *)

(* TODO: move *)

let stack_removeProof_word_list_exists_thm =
  cake_theorem "word_list_exists_thm"
  (fun () ->
    `(word_list_exists a 0 = emp) /\
      (word_list_exists a (SUC n) =
       SEP_EXISTS (\w. set_sep_one (a,w) * word_list_exists (a +
         bytes_in_word) n))`)
  CHEAT_TAC;;

let stack_removeProof_word_list_exists_ADD =
  cake_theorem "word_list_exists_ADD"
  (fun () ->
    `!m n a.
        word_list_exists a (m + n) =
        word_list_exists a m *
        word_list_exists (a + bytes_in_word * n2w m) n`)
  CHEAT_TAC;;

let stack_removeProof_word_list_APPEND = cake_theorem "word_list_APPEND"
  (fun () ->
    `!xs ys a.
        misc_word_list a (xs ++ ys) =
        misc_word_list a xs * misc_word_list (a + bytes_in_word *
          n2w (LENGTH xs)) ys`)
  CHEAT_TAC;;

let stack_removeProof_LESS_LENGTH_IMP_APPEND =
  cake_theorem "LESS_LENGTH_IMP_APPEND"
  (fun () ->
    `!xs n. n < LENGTH xs ==> (?ys zs. xs = ys ++ zs /\ LENGTH ys = n)`)
  CHEAT_TAC;;

let stack_removeProof_call_FFI_LENGTH = cake_theorem "call_FFI_LENGTH"
  (fun () ->
    `(call_FFI s i conf xs = FFI_return n ys) ==> (LENGTH ys = LENGTH
  xs)`)
  CHEAT_TAC;;

let stack_removeProof_with_same_clock =
  cake_theorem "with_same_clock[simp]"
  (fun () ->
    `!(x:('a,'c,'ffi)stackSem_state). stackSem_state_clock_fupd (K
  (stackSem_state_clock x))
       x = x`)
  CHEAT_TAC;;

let stack_removeProof_set_var_set_var =
  cake_theorem "set_var_set_var[simp]"
  (fun () ->
    `set_var x y (set_var x z w) = set_var x y w`)
  CHEAT_TAC;;

let get_var_set_var_same = cake_theorem "get_var_set_var_same[simp]"
  (fun () ->
    `get_var x (set_var x y z) = SOME y`)
  CHEAT_TAC;;

let stack_removeProof_get_var_set_var = cake_theorem "get_var_set_var"
  (fun () ->
    `get_var x (set_var x' y z) = (if x = x' then SOME y else get_var
  x z)`)
  CHEAT_TAC;;

let bytes_in_word_word_shift = cake_theorem "bytes_in_word_word_shift"
  (fun () ->
    `good_dimindex (:'a) /\ w2n (bytes_in_word:'a word) * w2n n <
  dimword (:'a) ==>
     ((bytes_in_word:'a word) * n) >>> backend_common_word_shift
       (:'a) = n`)
  CHEAT_TAC;;

let word_offset_eq = cake_theorem "word_offset_eq"
  (fun () ->
    `word_offset n = bytes_in_word * n2w n`)
  CHEAT_TAC;;

let memory_def = cake_define
  `memory m dm = (\s. s = fun2set (m,dm))`;;

let word_list_rev_def = cake_define_list
  [`word_list_rev a [] = emp`;
   `word_list_rev a (x :: xs) =
         set_sep_one (a - bytes_in_word,x) * word_list_rev (a -
           bytes_in_word) xs`];;

let word_store_def = cake_define
  `word_store base store =
     word_list_rev base
       (MAP (\name. match FLOOKUP store name with NONE ->
         wordLang_Word (n2w 0) | SOME x -> x)
         stack_remove_store_list)`;;

let code_rel_def = cake_define
  `stack_removeProof_code_rel jump off k code1 code2 <=>
     (!n prog.
       sptree_lookup n code1 = SOME prog ==>
       reg_bound prog k /\
       sptree_lookup n code2 = SOME (stack_remove_comp jump off k
         prog)) /\
     domain code2 = domain code1 UNION {0,1,2}`;;
hol4_overload "code_rel" "stack_removeProof_code_rel";;
(* exact characterization for Install *)

let is_SOME_Word_def = cake_define
  `is_SOME_Word x1 =
        match x1 with
          SOME (wordLang_Word w) -> T
        | _1 -> F`;;

let the_SOME_Word_def = cake_define
  `(the_SOME_Word (SOME (wordLang_Word w)) = w)`;;

let state_rel_def = cake_define
  `stack_removeProof_state_rel jump off k
  (s1:('a,'c,'ffi)stackSem_state) (s2:('a,'c,'ffi)stackSem_state) <=>
  stackSem_state_use_stack
     s1 /\ stackSem_state_use_store s1 /\
     ~(stackSem_state_use_stack s2) /\ ~(stackSem_state_use_store s2)
       /\
     ~(stackSem_state_use_alloc s2) /\ ~(stackSem_state_use_alloc s1)
       /\ be
     s2 = stackSem_state_be s1 /\ state_gc_fun
     s2 = stackSem_state_gc_fun s1 /\ state_clock
     s2 = stackSem_state_clock s1 /\ state_ffi
     s2 = stackSem_state_ffi s1 /\ stackSem_state_ffi_save_regs
     s2 = stackSem_state_ffi_save_regs s1 /\ fp_regs
     s2 = stackSem_state_fp_regs s1 /\ state_code_buffer
     s2 = stackSem_state_code_buffer s1 /\ state_sh_mdomain
     s2 = stackSem_state_sh_mdomain s1 /\ stackSem_state_compile
     s1 = (\c p. compile s2 c (MAP (prog_comp jump off k) p)) /\
       compile_oracle
     // s2.data_buffer = empty_buffer /\
     s2 = (\n. (I ## MAP (prog_comp jump off k) ## I)
       (stackSem_state_compile_oracle
                              // K []
                              s1 n)) /\
     (!n i p. MEM (i,p) (FST (SND (stackSem_state_compile_oracle s1
       n))) ==> reg_bound p k /\ stack_num_stubs <= i + 1) /\
     good_dimindex (:'a) /\
     (!n.
        n < k ==>
        FLOOKUP (stackSem_state_regs s2) n = FLOOKUP
          (stackSem_state_regs s1) n) /\
     stack_removeProof_code_rel jump off k (stackSem_state_code s1)
       (state_code s2) /\
     sptree_lookup stack_err_lab (state_code s2) = SOME (halt_inst
       (n2w 2)) /\
     FLOOKUP (stackSem_state_regs s2) (k + 2) = FLOOKUP
       (stackSem_state_store s1) CurrHeap /\
     {k,k + 1,k + 2} SUBSET stackSem_state_ffi_save_regs s2 /\
     is_SOME_Word (FLOOKUP (stackSem_state_store s1) BitmapBase) /\
       stackSem_state_stack_space
     s1 <= LENGTH (stackSem_state_stack s1) /\
     (let bp = (the_SOME_Word (FLOOKUP (stackSem_state_store s1)
       BitmapBase) << backend_common_word_shift (:'a)) in
     let all_bitmaps = stackSem_state_bitmaps s1 ++ buffer_buffer
       (stackSem_state_data_buffer s1) in buffer_position
       (stackSem_state_data_buffer
       s1) = bp + bytes_in_word * n2w (LENGTH (stackSem_state_bitmaps
         s1)) /\
     (match FLOOKUP (stackSem_state_regs s2) (k + 1) with SOME
       (wordLang_Word base) ->
       dimindex (:'a) DIV 8 * max_stack_alloc <= w2n base /\
       w2n base + w2n (bytes_in_word:'a word) * LENGTH
         (stackSem_state_stack s1) < dimword (:'a) /\
       FLOOKUP (stackSem_state_regs s2) k =
         SOME (wordLang_Word (base + bytes_in_word * n2w
           (stackSem_state_stack_space s1))) /\
       (memory (stackSem_state_memory s1) (stackSem_state_mdomain s1)
         *
        misc_word_list bp (MAP wordLang_Word all_bitmaps) *
        word_list_exists (bp + bytes_in_word * n2w (LENGTH
          all_bitmaps)) (buffer_space_left (stackSem_state_data_buffer
          s1)) *
        word_store base (stackSem_state_store s1) *
        misc_word_list base (stackSem_state_stack s1))
         (fun2set (state_memory s2,state_mdomain s2)) | _2 -> F))`;;
hol4_overload "state_rel" "stack_removeProof_state_rel";;

let state_rel_get_var = cake_theorem "state_rel_get_var[local]"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t /\ n < k ==> (get_var
  n s = get_var n t)`)
  CHEAT_TAC;;

let state_rel_IMP = cake_theorem "state_rel_IMP[local]"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t1 ==>
       stack_removeProof_state_rel jump off k (dec_clock s)
         (dec_clock t1)`)
  CHEAT_TAC;;

let stack_removeProof_state_rel_with_clock =
  cake_theorem "state_rel_with_clock[local]"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t1 ==>
       stack_removeProof_state_rel jump off k (state_clock_fupd
         (K c) s) (state_clock_fupd (K c) t1)`)
  CHEAT_TAC;;

let stack_removeProof_state_rel_const = cake_theorem "state_rel_const"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t ==> state_code_buffer
     t = state_code_buffer s /\ state_sh_mdomain
     t = state_sh_mdomain s /\
     ~(stackSem_state_use_stack t) /\ stackSem_state_use_stack s /\
       state_ffi t = state_ffi s /\ compile_oracle
     t = (\n. (I ## MAP (prog_comp jump off k) ## I)
       (compile_oracle
                              // K []
                              s n)) /\ compile
     s = (\c p. compile t c (MAP (prog_comp jump off k) p))`)
  CHEAT_TAC;;

let stack_removeProof_find_code_lemma =
  cake_theorem "find_code_lemma[local]"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t1 /\
       (match dest with INL v2 -> T | INR i -> i < k) /\
       find_code dest (stackSem_state_regs s) (state_code s) = SOME
         x ==>
       find_code dest (stackSem_state_regs t1) (state_code t1) =
         SOME (comp jump off k x) /\ reg_bound x k`)
  CHEAT_TAC;;

let find_code_lemma2 = cake_theorem "find_code_lemma2[local]"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t1 /\
       (match dest with INL v2 -> T | INR i -> i < k) /\
       find_code dest (stackSem_state_regs s \\ x1) (state_code s)
         = SOME x ==>
       find_code dest (stackSem_state_regs t1 \\ x1) (state_code
         t1) = SOME (comp jump off k x) /\ reg_bound x k`)
  CHEAT_TAC;;

let state_rel_set_var = cake_theorem "state_rel_set_var[simp]"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t1 /\ v < k ==>
      stack_removeProof_state_rel jump off k (set_var v x s)
        (set_var v x t1)`)
  CHEAT_TAC;;

let word_store_CurrHeap = cake_theorem "word_store_CurrHeap[local]"
  (fun () ->
    `word_store base (state_store s |+ (CurrHeap,x)) = word_store base
  (state_store s)`)
  CHEAT_TAC;;

let memory_fun2set_IMP_read =
  cake_theorem "memory_fun2set_IMP_read[local]"
  (fun () ->
    `(memory m d * p) (fun2set (m1,d1)) /\ a IN d ==>
       a IN d1 /\ m1 a = m a`)
  CHEAT_TAC;;

let state_rel_read = cake_theorem "state_rel_read[local]"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t /\ a IN state_mdomain s
  ==>
       a IN state_mdomain t /\ (state_memory t a = state_memory s
         a)`)
  CHEAT_TAC;;

let mem_load_32_IMP = cake_theorem "mem_load_32_IMP[local]"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t /\
       mem_load_32 (state_memory s) (state_mdomain s) (be s) a =
         SOME x ==>
       mem_load_32 (state_memory t) (state_mdomain t) (be t) a =
         SOME x`)
  CHEAT_TAC;;

let mem_load_byte_aux_IMP = cake_theorem "mem_load_byte_aux_IMP[local]"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t /\
       mem_load_byte_aux (state_memory s) (state_mdomain s) (be s)
         a = SOME x ==>
       mem_load_byte_aux (state_memory t) (state_mdomain t) (be
         t) a = SOME x`)
  CHEAT_TAC;;

let read_bytearray_IMP_read_bytearray =
  cake_theorem "read_bytearray_IMP_read_bytearray[local]"
  (fun () ->
    `!n a k s t x.
         stack_removeProof_state_rel jump off k s t /\
         read_bytearray a n (mem_load_byte_aux (state_memory s)
           (state_mdomain s) (be s)) = SOME x ==>
         read_bytearray a n (mem_load_byte_aux (state_memory t)
           (state_mdomain t) (be t)) = SOME x`)
  CHEAT_TAC;;

let write_bytearray_IGNORE_non_aligned =
  cake_theorem "write_bytearray_IGNORE_non_aligned[local]"
  (fun () ->
    `!new_bytes a.
         (!x. ~(b = byte_align x)) ==>
         write_bytearray a new_bytes m d be b = m b`)
  CHEAT_TAC;;

let write_bytearray_IGNORE =
  cake_theorem "write_bytearray_IGNORE[local]"
  (fun () ->
    `!new_bytes a x xx.
         d1 SUBSET d /\
         read_bytearray a (LENGTH new_bytes) (mem_load_byte_aux m1
           d1 be) = SOME x /\ ~(xx IN d1) ==>
         write_bytearray a new_bytes m d be xx = m xx`)
  CHEAT_TAC;;

let write_bytearray_EQ = cake_theorem "write_bytearray_EQ[local]"
  (fun () ->
    `!new_bytes a m1 m y x.
         d1 SUBSET d /\ (!a. a IN d1 ==> m1 a = m a /\ a IN d) /\
         read_bytearray a (LENGTH new_bytes) (mem_load_byte_aux m1
           d1 be) = SOME y /\ m1 x = m x ==>
         write_bytearray a new_bytes m1 d1 be x =
         write_bytearray a new_bytes m d be x`)
  CHEAT_TAC;;

let write_bytearray_lemma = cake_theorem "write_bytearray_lemma[local]"
  (fun () ->
    `!new_bytes a m1 d1 be' x p m d.
         (memory m1 d1 * p) (fun2set (m,d)) /\
         read_bytearray a (LENGTH new_bytes) (mem_load_byte_aux m1
           d1 be') = SOME x ==>
         (memory (write_bytearray a new_bytes m1 d1 be') d1 * p)
           (fun2set (write_bytearray a new_bytes m d be',d))`)
  CHEAT_TAC;;

let state_rel_get_var_k = cake_theorem "state_rel_get_var_k"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t ==>
     (?(c:'a word).
     get_var (k + 1) t = SOME (wordLang_Word c) /\
     dimindex (:'a) DIV 8 * max_stack_alloc <= w2n c /\
     w2n c + w2n (bytes_in_word:'a word) * LENGTH (stack s) <
       dimword (:'a) /\
     get_var k t = SOME (wordLang_Word (c + bytes_in_word * n2w
       (stackSem_state_stack_space s))) /\
     (memory (state_memory s) (state_mdomain s) *
       misc_word_list
         (the_SOME_Word (FLOOKUP (state_store s) BitmapBase) <<
           backend_common_word_shift (:'a))
         (MAP wordLang_Word (stackSem_state_bitmaps s) ++ MAP
           wordLang_Word (buffer_buffer (state_data_buffer s))) *
       word_list_exists
         (the_SOME_Word (FLOOKUP (state_store s) BitmapBase) <<
           backend_common_word_shift (:'a) +
          bytes_in_word *
          n2w (LENGTH (buffer_buffer (state_data_buffer s)) +
            LENGTH (stackSem_state_bitmaps s))) (buffer_space_left
            (state_data_buffer
         s)) * word_store c (state_store s) *
       misc_word_list c (stack s)) (fun2set (state_memory
         t,state_mdomain t)))`)
  CHEAT_TAC;;

let evaluate_single_stack_alloc =
  cake_theorem "evaluate_single_stack_alloc"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t1 /\
     ((r,s2) = (if stackSem_state_stack_space s < n then (SOME
       (Halt (wordLang_Word (n2w 2))),stackSem_empty_env s) else
       (NONE,stackSem_state_stack_space_fupd (K
       (stackSem_state_stack_space s - n)) s))) /\ ~(n = 0) /\ n <=
       max_stack_alloc ==>
     (?ck t2.
       evaluate (single_stack_alloc jump k n,state_clock_fupd (K
         (state_clock t1 + ck)) t1) = (r,t2) /\
       (if stackSem_state_stack_space s < n then state_ffi t2 =
         state_ffi s2 else stack_removeProof_state_rel jump off k s2
         t2))`)
  CHEAT_TAC;;

let evaluate_stack_alloc = cake_theorem "evaluate_stack_alloc"
  (fun () ->
    `!jump k n r s s2 t1.
     evaluate (stackLang_StackAlloc n,s) = (r,s2) /\ ~(r = SOME
       Error) /\
     stack_removeProof_state_rel jump off k s t1 ==>
     (?ck t2.
       evaluate (stack_alloc jump k n,state_clock_fupd (K (ck +
         state_clock t1)) t1) = (r,t2) /\
       (if !w. ~(r = SOME (Halt w)) then
         stack_removeProof_state_rel jump off k s2 t2 else state_ffi
         t2 = state_ffi s2))`)
  CHEAT_TAC;;

let state_rel_mem_load_imp = cake_theorem "state_rel_mem_load_imp"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t /\
     mem_load x s = SOME w ==>
     mem_load x t = SOME w`)
  CHEAT_TAC;;

let state_rel_word_exp = cake_theorem "state_rel_word_exp"
  (fun () ->
    `!s e w.
     stack_removeProof_state_rel jump off k s t /\
     reg_bound_exp e k /\
     word_exp s e = SOME w ==>
     word_exp t e = SOME w`)
  CHEAT_TAC;;

let memory_write = cake_theorem "memory_write"
  (fun () ->
    `x IN sd /\ x IN dm /\
     (memory sm sd * p) (fun2set (m,dm)) ==>
     (memory ((x =+ y) sm) sd * p) (fun2set ((x =+ y) m,dm))`)
  CHEAT_TAC;;

let state_rel_mem_store = cake_theorem "state_rel_mem_store"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t /\
     mem_store x y s = SOME s' /\
     mem_store x y t = SOME t' ==>
     stack_removeProof_state_rel jump off k s' t'`)
  CHEAT_TAC;;

let state_rel_mem_store_32 = cake_theorem "state_rel_mem_store_32"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t /\ mem_store_32
  (state_memory s) (state_mdomain s) (be s) a b = SOME z ==>
     (?y. mem_store_32 (state_memory t) (state_mdomain t) (be t) a
       b = SOME y /\
         stack_removeProof_state_rel jump off k
           (state_memory_fupd (K z) s) (state_memory_fupd (K y) t))`)
  CHEAT_TAC;;

let state_rel_mem_store_byte_aux =
  cake_theorem "state_rel_mem_store_byte_aux"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t /\ mem_store_byte_aux
  (state_memory s) (state_mdomain s) (be s) a b = SOME z ==>
     (?y. mem_store_byte_aux (state_memory t) (state_mdomain t) (be
       t) a b = SOME y /\
         stack_removeProof_state_rel jump off k
           (state_memory_fupd (K z) s) (state_memory_fupd (K y) t))`)
  CHEAT_TAC;;

let state_rel_get_fp_var = cake_theorem "state_rel_get_fp_var[local]"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t ==>
     get_fp_var n s = get_fp_var n t`)
  CHEAT_TAC;;

let state_rel_set_fp_var = cake_theorem "state_rel_set_fp_var[local]"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t ==>
     stack_removeProof_state_rel jump off k (set_fp_var n v s)
       (set_fp_var n v t)`)
  CHEAT_TAC;;

let state_rel_inst = cake_theorem "state_rel_inst"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t /\
     reg_bound_inst i k /\
     inst i s = SOME s' ==>
     (?t'.
       inst i t = SOME t' /\
       stack_removeProof_state_rel jump off k s' t')`)
  CHEAT_TAC;;

let stack_write = cake_theorem "stack_write"
  (fun () ->
    `!stack' base p m d a v.
     (misc_word_list base stack' * p) (fun2set (m,d)) /\ a < LENGTH
       stack' ==>
     (misc_word_list base (LUPDATE v a stack') * p) (fun2set
       (((base + bytes_in_word * (n2w a)) =+ v) m,d))`)
  CHEAT_TAC;;

let state_rel_stack_store = cake_theorem "state_rel_stack_store"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t /\ st = stack s /\
     FLOOKUP (stackSem_state_regs t) k = SOME (wordLang_Word b) /\
       stackSem_state_stack_space
     s + n < LENGTH st /\
     b + bytes_in_word * n2w n = a ==>
     stack_removeProof_state_rel jump off k (stack_fupd (K (LUPDATE
       x (n + stackSem_state_stack_space s) st)) s)
       (state_memory_fupd (K ((a =+ x) (state_memory t))) t)`)
  CHEAT_TAC;;

let lsl_word_shift = cake_theorem "lsl_word_shift"
  (fun () ->
    `good_dimindex (:'a) ==>
      w << backend_common_word_shift (:'a) = w *
        (bytes_in_word:'a word)`)
  CHEAT_TAC;;

let get_labels_stack_free = cake_theorem "get_labels_stack_free[local]"
  (fun () ->
    `!k n. stackSem_get_labels (stack_remove_stack_free k n) = {}`)
  CHEAT_TAC;;

let get_labels_stack_alloc =
  cake_theorem "get_labels_stack_alloc[local]"
  (fun () ->
    `!jump k n. stackSem_get_labels (stack_alloc jump k n) = {}`)
  CHEAT_TAC;;

let get_labels_upshift = cake_theorem "get_labels_upshift[local]"
  (fun () ->
    `!n n0. stackSem_get_labels (upshift n n0) = {}`)
  CHEAT_TAC;;

let get_labels_downshift = cake_theorem "get_labels_downshift[local]"
  (fun () ->
    `!n n0. stackSem_get_labels (downshift n n0) = {}`)
  CHEAT_TAC;;

let get_labels_comp = cake_theorem "get_labels_comp"
  (fun () ->
    `!jump off k e. stackSem_get_labels (comp jump off k e) =
  stackSem_get_labels e`)
  CHEAT_TAC;;

let code_rel_loc_check = cake_theorem "code_rel_loc_check"
  (fun () ->
    `stack_removeProof_code_rel jump off k c1 c2 /\ loc_check c1
  (l1,l2) ==> loc_check c2 (l1,l2)`)
  CHEAT_TAC;;

let evaluate_single_stack_free =
  cake_theorem "evaluate_single_stack_free"
  (fun () ->
    `stack_removeProof_state_rel jump off k s t1 /\
     ((r,s2) = (NONE,stackSem_state_stack_space_fupd (K
       (stackSem_state_stack_space s + n)) s)) /\
     ~(LENGTH (stack s) < stackSem_state_stack_space s + n) /\ ~(n
       = 0) /\ n <= max_stack_alloc ==>
     (?ck t2.
       evaluate (single_stack_free k n,state_clock_fupd (K
         (state_clock t1 + ck)) t1) = (r,t2) /\
         stack_removeProof_state_rel jump off k s2 t2)`)
  CHEAT_TAC;;

let evaluate_stack_free = cake_theorem "evaluate_stack_free"
  (fun () ->
    `!k n r s s2 t1.
     evaluate (stackLang_StackFree n,s) = (r,s2) /\ ~(r = SOME
       Error) /\
     stack_removeProof_state_rel jump off k s t1 ==>
     (?ck t2.
       evaluate (stack_remove_stack_free k n,state_clock_fupd (K
         (ck + state_clock t1)) t1) = (r,t2) /\
       stack_removeProof_state_rel jump off k s2 t2)`)
  CHEAT_TAC;;

let evaluate_upshift = cake_theorem "evaluate_upshift[local]"
  (fun () ->
    `!r n st w.
     FLOOKUP (stackSem_state_regs st) r = SOME (wordLang_Word w)
       ==>
     evaluate (upshift r n,st) = (NONE,stackSem_state_regs_fupd
       (K (stackSem_state_regs st |+ (r,wordLang_Word (w + word_offset
       n)))) st)`)
  CHEAT_TAC;;

let evaluate_downshift = cake_theorem "evaluate_downshift[local]"
  (fun () ->
    `!r n st w.
     FLOOKUP (stackSem_state_regs st) r = SOME (wordLang_Word w)
       ==>
     evaluate (downshift r n,st) = (NONE,stackSem_state_regs_fupd
       (K (stackSem_state_regs st |+ (r,wordLang_Word (w - word_offset
       n)))) st)`)
  CHEAT_TAC;;

let name_cases = cake_theorem "name_cases[local]"
  (fun () ->
    `!name. ~(name = CurrHeap) ==> MEM name stack_remove_store_list`)
  CHEAT_TAC;;

(* Significantly faster than SEP_R_TAC *)
let mem_load_lemma = cake_theorem "mem_load_lemma[local]"
  (fun () ->
    `MEM name stack_remove_store_list /\
     FLOOKUP (stackSem_state_store (s:('a,'c,'b)stackSem_state))
       name = SOME x /\
     (memory (stackSem_state_memory s) (stackSem_state_mdomain s) *
           misc_word_list
             (the_SOME_Word (FLOOKUP (stackSem_state_store s)
               BitmapBase) << backend_common_word_shift (:'a))
             (MAP wordLang_Word (stackSem_state_bitmaps s) ++ MAP
               wordLang_Word (buffer_buffer (stackSem_state_data_buffer
               s))) *
           word_list_exists
             (the_SOME_Word (FLOOKUP (stackSem_state_store s)
               BitmapBase) <<
              backend_common_word_shift (:'a) +
              bytes_in_word *
              n2w (LENGTH (buffer_buffer
                (stackSem_state_data_buffer s)) + LENGTH
                (stackSem_state_bitmaps s))) (buffer_space_left
                (stackSem_state_data_buffer
             s)) * word_store c (stackSem_state_store s) *
           misc_word_list c (stackSem_state_stack s)) (fun2set
             (stackSem_state_memory t1,stackSem_state_mdomain
             (t1:('a,'c,'b)stackSem_state))) ==>
     mem_load (c + store_offset name) t1 = SOME x`)
  CHEAT_TAC;;

(* basically the same thing, but without the read assumption *)
let mem_load_lemma2 = cake_theorem "mem_load_lemma2[local]"
  (fun () ->
    `MEM name stack_remove_store_list /\
     (memory (state_memory s) (state_mdomain s) *
           misc_word_list
             (the_SOME_Word (FLOOKUP (state_store s) BitmapBase) <<
               backend_common_word_shift (:'a))
             (MAP wordLang_Word (stackSem_state_bitmaps s) ++ MAP
               wordLang_Word (buffer_buffer (state_data_buffer s))) *
           word_list_exists
             (the_SOME_Word (FLOOKUP (state_store s) BitmapBase) <<
              backend_common_word_shift (:'a) +
              bytes_in_word *
              n2w (LENGTH (buffer_buffer (state_data_buffer s)) +
                LENGTH (stackSem_state_bitmaps s))) (buffer_space_left
                (state_data_buffer
             s)) * word_store c (state_store s) *
           misc_word_list c (stack s)) (fun2set
             (stackSem_state_memory t1,stackSem_state_mdomain
             (t1:('a,'c,'b)stackSem_state))) ==>
     c + store_offset name IN stackSem_state_mdomain t1`)
  CHEAT_TAC;;

let assoc_lem = cake_theorem "assoc_lem[local]"
  (fun () ->
    `((A:('a->bool)->bool) * B) * C =
     (B * C) * A`)
  CHEAT_TAC;;

(* HOL4 stack_removeProofScript.sml:1175: ML code, not ported *)

let store_write_lemma = cake_theorem "store_write_lemma[local]"
  (fun () ->
    `MEM name stack_remove_store_list /\
     (memory (state_memory s) (state_mdomain s) *
           misc_word_list
             (the_SOME_Word (FLOOKUP (state_store s) BitmapBase) <<
               backend_common_word_shift (:'a))
             (MAP wordLang_Word (stackSem_state_bitmaps s) ++ MAP
               wordLang_Word (buffer_buffer (state_data_buffer s))) *
           word_list_exists
             (the_SOME_Word (FLOOKUP (state_store s) BitmapBase) <<
              backend_common_word_shift (:'a) +
              bytes_in_word *
              n2w (LENGTH (buffer_buffer (state_data_buffer s)) +
                LENGTH (stackSem_state_bitmaps s))) (buffer_space_left
                (state_data_buffer
             s)) * word_store c (state_store s) *
           misc_word_list c (stack s)) (fun2set (m,d)) ==>
     (memory (state_memory s) (state_mdomain s) *
         misc_word_list
           (the_SOME_Word (FLOOKUP (state_store s) BitmapBase) <<
             backend_common_word_shift (:'a))
           (MAP wordLang_Word (stackSem_state_bitmaps s) ++ MAP
             wordLang_Word (buffer_buffer (state_data_buffer s))) *
         word_list_exists
           (the_SOME_Word (FLOOKUP (state_store s) BitmapBase) <<
             backend_common_word_shift (:'a) +
            bytes_in_word *
            n2w (LENGTH (buffer_buffer (state_data_buffer s)) +
              LENGTH (stackSem_state_bitmaps s))) (buffer_space_left
              (state_data_buffer
           s)) * word_store c (state_store s |+ (name,x)) *
         misc_word_list c (stack s)) (fun2set (((c + store_offset
           name) =+ x) m,d))`)
  CHEAT_TAC;;

let prog_comp_eta = cake_theorem "prog_comp_eta"
  (fun () ->
    `prog_comp = (\jump off k (n,p). (n,comp jump off k p))`)
  CHEAT_TAC;;

let copy_each_thm = cake_theorem "copy_each_thm"
  (fun () ->
    `!pattern i a off bs d m dm i1 a1 m1 x (t:('a,'b,'c)stackSem_state).
       copy_words_for_pattern pattern i a off bs d m = SOME
         (i1,a1,m1) /\
       ALL_DISTINCT [1; 2; 3; t1; t2] /\ dm =
         stackSem_state_mdomain t /\ good_dimindex (:'a) /\
       get_var 1 t = SOME (wordLang_Word pattern) /\ d SUBSET dm /\
       get_var 2 t = SOME (wordLang_Word (a:'a word)) /\
       get_var 3 t = SOME (wordLang_Word off) /\
       get_var t2 t = SOME (wordLang_Word (x + bytes_in_word * n2w
         i)) /\
       (misc_word_list x (MAP wordLang_Word bs) * rest * memory m
         d) (fun2set (stackSem_state_memory t,dm)) ==>
       (?ck y m2.
         evaluate (copy_each t1 t2,stackSem_state_clock_fupd (K
           (stackSem_state_clock t + ck)) t) =
           (NONE,stackSem_state_regs_fupd (K (
                              (if pattern = (n2w 1) then
                                stackSem_state_regs t else
                                stackSem_state_regs t |+
                                (t1,wordLang_Word y)) |+
                                (2,wordLang_Word a1) |+ (1,wordLang_Word
                                (n2w 1)) |+ (t2,wordLang_Word (x +
                                bytes_in_word * n2w i1))))
                                (stackSem_state_memory_fupd (K m2) t))
                                /\
         (misc_word_list x (MAP wordLang_Word bs) * rest * memory
           m1 d) (fun2set (m2,dm)))`)
  CHEAT_TAC;;

let copy_loop_thm = cake_theorem "copy_loop_thm"
  (fun () ->
    `!i a off bs d m dm i1 a1 m1 x (t:('a,'b,'c)stackSem_state).
       copy_words i a off bs d m = SOME (a1,m1) /\
       ALL_DISTINCT [1; 2; 3; t1; t2] /\ dm =
         stackSem_state_mdomain t /\ good_dimindex (:'a) /\
       d SUBSET dm /\
       get_var 2 t = SOME (wordLang_Word (a:'a word)) /\
       get_var 3 t = SOME (wordLang_Word off) /\
       get_var t2 t = SOME (wordLang_Word (x + bytes_in_word * n2w
         i)) /\
       (misc_word_list x (MAP wordLang_Word bs) * rest * memory m
         d) (fun2set (stackSem_state_memory t,dm)) ==>
       (?ck b y y2 m2.
         evaluate (copy_loop t1 t2,stackSem_state_clock_fupd (K
           (stackSem_state_clock t + ck)) t) =
           (NONE,stackSem_state_regs_fupd (K (
                              (if b then stackSem_state_regs t else
                                stackSem_state_regs t |+
                                (t1,wordLang_Word y)) |+
                                (2,wordLang_Word a1) |+ (1,wordLang_Word
                                (n2w 1)) |+ (t2,wordLang_Word y2)))
                                (stackSem_state_memory_fupd (K m2) t))
                                /\
         (misc_word_list x (MAP wordLang_Word bs) * rest * memory
           m1 d) (fun2set (m2,dm)))`)
  CHEAT_TAC;;

let memory_fun2set_SUBSET = cake_theorem "memory_fun2set_SUBSET"
  (fun () ->
    `(memory m1 d1 * rest) (fun2set (m2,d2)) ==> d1 SUBSET d2`)
  CHEAT_TAC;;

let stack_removeProof_comp_correct = cake_theorem "comp_correct[local]"
  (fun () ->
    `!p s1 r s2 t1 k off jump.
        evaluate (p,s1) = (r,s2) /\ ~(r = SOME Error) /\
        stack_removeProof_state_rel jump off k s1 t1 /\ reg_bound p
          k ==>
        (?ck t2. evaluate (comp jump off k p,state_clock_fupd (K
          (ck + state_clock t1)) t1) = (r,t2) /\
                (match r with SOME (Halt _3) -> state_ffi t2 =
                  state_ffi s2 | SOME TimeOut -> state_ffi t2 =
                  state_ffi s2 | SOME (FinalFFI _4) -> state_ffi t2 =
                  state_ffi s2 | _5 -> (stack_removeProof_state_rel
                  jump off k s2 t2)))`)
  CHEAT_TAC;;

let stack_removeProof_compile_semantics =
  cake_theorem "compile_semantics"
  (fun () ->
    `stack_removeProof_state_rel jump off k s1 s2 /\ ~(semantics start
  s1 = ffi_Fail) ==>
     semantics start s2 = semantics start s1`)
  CHEAT_TAC;;

(* init code *)

(* HOL4 stack_removeProofScript.sml:2617-2622: a proof *)

(* HOL4 stack_removeProofScript.sml:2624-2629: a proof *)

let mem_val_def = cake_define_list
  [`mem_val (regs':(num,'a word_loc)fmap) (INL w) = wordLang_Word w`;
   `mem_val (regs':(num,'a word_loc)fmap) (INR n) = FAPPLY regs' n`];;

let store_list_code_thm = cake_theorem "store_list_code_thm"
  (fun () ->
    `!xs s w frame ys m dm.
        (misc_word_list w ys * frame) (fun2set (m,dm)) /\
        m = state_memory s /\ dm = state_mdomain s /\
        (LENGTH ys = LENGTH xs) /\ ~(a = t) /\
        get_var a s = SOME (wordLang_Word w) /\ t IN FDOM
          (stackSem_state_regs s) /\
        EVERY (\x. !n. (INR n = x) ==> ~(n = a) /\ ~(n = t) /\ n IN
          FDOM (stackSem_state_regs s)) xs ==>
        (?r1 m1.
          (misc_word_list w (MAP (mem_val (stackSem_state_regs s))
            xs) * frame) (fun2set (m1,state_mdomain s)) /\
          evaluate (store_list_code a t xs,s) =
            (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs
              s |++
              [(a,wordLang_Word (w + bytes_in_word * n2w (LENGTH
                xs))); (t,r1)])) (state_memory_fupd (K m1) s)))`)
  CHEAT_TAC;;

(* HOL4 stack_removeProofScript.sml:2723-2725: a proof *)

let MOD_EQ_IMP_MULT = cake_theorem "MOD_EQ_IMP_MULT[local]"
  (fun () ->
    `!n d. n MOD d = 0 /\ ~(d = 0) ==> (?k. n = d * k)`)
  CHEAT_TAC;;

let star_move_lemma = cake_theorem "star_move_lemma[local]"
  (fun () ->
    `p0 * p1 * p1' * p2 * p3 * p4 = p2 * (p1 * p1' * STAR p3 (p4 *
  p0))`)
  CHEAT_TAC;;

let read_mem_def = cake_define_list
  [`stack_removeProof_read_mem a m 0 = []`;
   `stack_removeProof_read_mem a m (SUC n) =
         m a :: stack_removeProof_read_mem (a + bytes_in_word)
           m n`];;
hol4_overload "read_mem" "stack_removeProof_read_mem";;

let addresses_def = cake_define_list
  [`addresses a 0 = {}`;
   `addresses a (SUC n) = a INSERT addresses (a + bytes_in_word) n`];;

let LENGTH_read_mem = cake_theorem "LENGTH_read_mem"
  (fun () ->
    `!n a m. LENGTH (stack_removeProof_read_mem a m n) = n`)
  CHEAT_TAC;;

let IN_addresses = cake_theorem "IN_addresses[local]"
  (fun () ->
    `!n a x. x IN addresses a n <=>
               (?i. i < n /\ x = a + n2w i * bytes_in_word)`)
  CHEAT_TAC;;

let addresses_thm = cake_theorem "addresses_thm"
  (fun () ->
    `!n a. addresses a n = {a + n2w i * bytes_in_word' | i < n}`)
  CHEAT_TAC;;

let memory_addresses = cake_theorem "memory_addresses[local]"
  (fun () ->
    `!n (a:'a word) (m:'a word->'a word_loc).
         n * (dimindex (:'a) DIV 8) < dimword (:'a) /\
           good_dimindex (:'a) ==>
         memory m (addresses a n) = misc_word_list a
           (stack_removeProof_read_mem a m n)`)
  CHEAT_TAC;;

let MOD_LESS_EQ_MOD_IMP = cake_theorem "MOD_LESS_EQ_MOD_IMP[local]"
  (fun () ->
    `m MOD k <= n /\ m < k ==> m <= n`)
  CHEAT_TAC;;

let MAP_mem_val_MAP_INL = cake_theorem "MAP_mem_val_MAP_INL[local]"
  (fun () ->
    `!ws f. MAP (mem_val f) (MAP INL ws) = MAP wordLang_Word ws`)
  CHEAT_TAC;;

let word_list_EQ_rev = cake_theorem "word_list_EQ_rev"
  (fun () ->
    `!xs a. misc_word_list a xs =
             word_list_rev (a + n2w (LENGTH xs) * bytes_in_word)
               (REVERSE xs)`)
  CHEAT_TAC;;

let word_list_and_rev_join_lemma =
  cake_theorem "word_list_and_rev_join_lemma[local]"
  (fun () ->
    `(b = a + n2w (LENGTH xs + LENGTH ys) * bytes_in_word) /\
       (p * misc_word_list a (xs ++ REVERSE ys) * q) ss /\ b1 ==>
       (p * misc_word_list a xs * word_list_rev b ys * q) ss /\
         b1`)
  CHEAT_TAC;;

let word_list_IMP_read_mem =
  cake_theorem "word_list_IMP_read_mem[local]"
  (fun () ->
    `!xs a p.
         (p * misc_word_list a xs) (fun2set (m,dm)) ==>
         stack_removeProof_read_mem a m (LENGTH xs) = xs`)
  CHEAT_TAC;;

let INSERT_DELETE_EQ_DELETE =
  cake_theorem "INSERT_DELETE_EQ_DELETE[local]"
  (fun () ->
    `(x INSERT s) DELETE x = s DELETE x`)
  CHEAT_TAC;;

let word_list_exists_addresses =
  cake_theorem "word_list_exists_addresses"
  (fun () ->
    `!n a. (dimindex (:'a) DIV 8) * n < dimword (:'a) /\
            good_dimindex (:'a) ==>
            word_list_exists a n (fun2set (m1,addresses (a:'a
              word) n))`)
  CHEAT_TAC;;

let init_reduce_def = cake_define
  `init_reduce gen_gc' jump off k code bitmaps data_sp coracle
  (s:('a,'c,'ffi)stackSem_state) =
     (let heap_ptr = theWord (FAPPLY (stackSem_state_regs s) (k + 2))
       in
     let bitmap_ptr = theWord (FAPPLY (stackSem_state_regs s) 3) <<
       backend_common_word_shift (:'a) in
     let stack_ptr = theWord (FAPPLY (stackSem_state_regs s) k) in
     let base_ptr = theWord (FAPPLY (stackSem_state_regs s) (k + 1))
       in
     let heap_sp = w2n (base_ptr - heap_ptr) DIV (dimindex (:'a) DIV
       8) - (LENGTH stack_remove_store_list) in
     let stack_sp = w2n (stack_ptr - base_ptr) DIV (dimindex (:'a)
       DIV 8) in stackSem_state_store_fupd (K (FEMPTY |++ (MAP (\n.
       match store_init gen_gc' k n with INL w -> (n,wordLang_Word w) |
       INR i -> (n,FAPPLY (stackSem_state_regs s) i))
                              (CurrHeap ::
                                stack_remove_store_list))))
                                (stackSem_state_stack_fupd (K
                                (stack_removeProof_read_mem base_ptr
                                (stackSem_state_memory s) (stack_sp +
                                1))) (stackSem_state_stack_space_fupd (K
                                stack_sp)
                                (stackSem_state_data_buffer_fupd (K
                                (mk_buffer (bitmap_ptr + bytes_in_word *
                                n2w (LENGTH bitmaps)) [] data_sp))
                                (stackSem_state_compile_oracle_fupd (K
                                coracle) (stackSem_state_compile_fupd (K
                                (\c p. stackSem_state_compile s c (MAP
                                (prog_comp jump off k) p)))
                                (stackSem_state_code_fupd (K code)
                                (stackSem_state_bitmaps_fupd (K bitmaps)
                                (stackSem_state_mdomain_fupd (K
                                (addresses heap_ptr heap_sp))
                                (stackSem_state_use_alloc_fupd (K F)
                                (stackSem_state_use_store_fupd (K T)
                                (stackSem_state_use_stack_fupd (K T)
       s))))))))))))`;;

let init_reduce_stack_space =
  cake_theorem "init_reduce_stack_space[local]"
  (fun () ->
    `stackSem_state_stack_space
       (init_reduce gen_gc jump off k code bitmaps data_sp coracle
         s8) <=
         LENGTH (stack (init_reduce gen_gc jump off k code
           bitmaps data_sp coracle s8))`)
  CHEAT_TAC;;

let stack_heap_limit_ok_def = cake_define
  `stack_heap_limit_ok t (stack_lim,heap_lim) <=>
     FLOOKUP (state_store t) HeapLength = SOME (wordLang_Word (n2w
       heap_lim * (bytes_in_word:'a word))) /\
     heap_lim * (dimindex (:'a) DIV 8) < dimword (:'a) /\
     stack_lim = LENGTH (stack t)`;;

let init_prop_def = cake_define
  `init_prop gen_gc' max_heap data_sp stack_heap_lim
  (s:('a,'c,'ffi)stackSem_state) =
     (?curr other bitmap_base len.
        FLOOKUP (stackSem_state_store s) CurrHeap = SOME
          (wordLang_Word curr) /\
        FLOOKUP (stackSem_state_store s) NextFree = SOME
          (wordLang_Word curr) /\
        FLOOKUP (stackSem_state_store s) TriggerGC = SOME
          (wordLang_Word (if gen_gc' then curr else other)) /\
        FLOOKUP (stackSem_state_store s) EndOfHeap = SOME
          (wordLang_Word other) /\
        FLOOKUP (stackSem_state_store s) OtherHeap = SOME
          (wordLang_Word other) /\
        FLOOKUP (stackSem_state_store s) BitmapBase = SOME
          (wordLang_Word bitmap_base) /\
        FLOOKUP (stackSem_state_store s) HeapLength = SOME
          (wordLang_Word (n2w len * bytes_in_word)) /\
        FLOOKUP (stackSem_state_store s) ProgStart = SOME
          (wordLang_Word (n2w 0)) /\
        FLOOKUP (stackSem_state_store s) AllocSize = SOME
          (wordLang_Word (n2w 0)) /\
        FLOOKUP (stackSem_state_store s) Globals = SOME
          (wordLang_Word (n2w 0)) /\
        FLOOKUP (stackSem_state_store s) GlobReal = SOME
          (wordLang_Word curr) /\
        FLOOKUP (stackSem_state_store s) Handler = SOME
          (wordLang_Word (n2w 0)) /\
        FLOOKUP (stackSem_state_store s) GenStart = SOME
          (wordLang_Word (n2w 0)) /\
        FLOOKUP (stackSem_state_store s) CodeBuffer = SOME
          (wordLang_Word (buffer_position (stackSem_state_code_buffer
          s))) /\
        FLOOKUP (stackSem_state_store s) CodeBufferEnd =
          SOME (wordLang_Word (buffer_position
            (stackSem_state_code_buffer s) + n2w (buffer_space_left
            (stackSem_state_code_buffer s)))) /\
        FLOOKUP (stackSem_state_store s) BitmapBuffer = SOME
          (wordLang_Word (buffer_position (stackSem_state_data_buffer
          s))) /\
        FLOOKUP (stackSem_state_store s) BitmapBufferEnd =
          SOME (wordLang_Word
           (buffer_position (stackSem_state_data_buffer s) +
            bytes_in_word * n2w (buffer_space_left
              (stackSem_state_data_buffer s)))) /\
        stack_heap_limit_ok s stack_heap_lim /\ buffer_buffer
          (stackSem_state_code_buffer
        s) = [] /\ buffer_buffer (stackSem_state_data_buffer s) = []
          /\ stackSem_state_use_stack
        s /\ stackSem_state_use_store s /\
        FLOOKUP (stackSem_state_regs s) 0 = SOME (Loc 1 0) /\
        LENGTH (stackSem_state_bitmaps s) + data_sp + 1 < dimword
          (:'a) /\
        LENGTH (stackSem_state_stack s) < dimword (:'a) /\
        (other = curr + bytes_in_word * n2w len) /\
        byte_aligned curr /\
        LAST (stackSem_state_stack s) = wordLang_Word (n2w 0) /\
        LENGTH (stackSem_state_stack s) = SUC
          (stackSem_state_stack_space s) /\
        LENGTH (stackSem_state_stack s) * (dimindex (:'a) DIV 8) <
          dimword (:'a) /\
        len + len <= max_heap /\
        (word_list_exists curr len * word_list_exists other len)
           (fun2set (stackSem_state_memory
             s,stackSem_state_mdomain s)))`;;

let init_code_pre_def = cake_define
  `init_code_pre k bitmaps data_sp s <=>
     (?ptr2 ptr3 ptr4 bitmap_ptr.
       good_dimindex (:'a) /\ 8 <= k /\ 1 IN domain (state_code s) /\
       {k,k + 1,k + 2} SUBSET stackSem_state_ffi_save_regs s /\
       ~(stackSem_state_use_stack s) /\ ~(stackSem_state_use_store s)
         /\ ~(stackSem_state_use_alloc s) /\
       FLOOKUP (stackSem_state_regs s) 2 = SOME (wordLang_Word
         (ptr2:'a word)) /\
       FLOOKUP (stackSem_state_regs s) 3 = SOME (wordLang_Word ptr3)
         /\
       FLOOKUP (stackSem_state_regs s) 4 = SOME (wordLang_Word ptr4)
         /\ state_memory
       s ptr2 = wordLang_Word bitmap_ptr /\ state_memory
       s (ptr2 + bytes_in_word) =
         wordLang_Word (bitmap_ptr + bytes_in_word * n2w (LENGTH
           bitmaps)) /\ state_memory
       s (ptr2 + (n2w 2) * bytes_in_word) =
         wordLang_Word (bitmap_ptr + bytes_in_word * n2w (LENGTH
           bitmaps) +
                            bytes_in_word * n2w data_sp) /\
                              state_memory
       s (ptr2 + (n2w 3) * bytes_in_word) = wordLang_Word
         (buffer_position (state_code_buffer s)) /\ state_memory
       s (ptr2 + (n2w 4) * bytes_in_word) =
          wordLang_Word (buffer_position (state_code_buffer s) + n2w
            (buffer_space_left (state_code_buffer s))) /\
       ptr2 <=+ ptr4 /\ (n2w 1024) * bytes_in_word <=+ ptr4 - ptr2 /\
       byte_aligned ptr2 /\ byte_aligned ptr4 /\ byte_aligned
         bitmap_ptr /\ buffer_buffer (state_code_buffer
       // NOTE: The last conjunct only needs to hold if
       // the entry checks hold. Probably can make more assumptions
       // about the bitmap_ptr too
       s) = [] /\
       (misc_word_list bitmap_ptr (MAP wordLang_Word bitmaps) *
        word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH
          bitmaps)) data_sp *
        word_list_exists ptr2 (w2n (ptr4 - ptr2) DIV w2n
          (bytes_in_word:'a word)))
         (fun2set (state_memory s,state_mdomain s)))`;;

let byte_aligned_bytes_in_word_MULT =
  cake_theorem "byte_aligned_bytes_in_word_MULT[local]"
  (fun () ->
    `good_dimindex (:'a) ==>
       byte_aligned (bytes_in_word * (w:'a word))`)
  CHEAT_TAC;;

(* The extra b equality makes this work better with SEP_NEQ_TAC *)
let word_list_wrap = cake_theorem "word_list_wrap"
  (fun () ->
    `good_dimindex (:'a) /\
     dimword (:'a) DIV (dimindex (:'a) DIV 8) < LENGTH ls ==>
     (?x xs y ys b.
     misc_word_list (a:'a word) ls = misc_word_list a (x :: xs) *
       misc_word_list b (y :: ys) /\
     b = a)`)
  CHEAT_TAC;;

let sub_rewrite = cake_theorem "sub_rewrite[local]"
  (fun () ->
    `ptr <= ptr' ==>
     --(n2w 1) * n2w ptr + n2w ptr' = n2w (ptr' - ptr)`)
  CHEAT_TAC;;

let div_rewrite = cake_theorem "div_rewrite[local]"
  (fun () ->
    `n <= x /\ 1 < n ==> ~(x DIV n = 0)`)
  CHEAT_TAC;;

let stack_removeProof_push_if = cake_theorem "push_if"
  (fun () ->
    `(if b then f x else f y) = f (if b then x else y) /\
      (if b then f x else g x) = (if b then f else g) x`)
  CHEAT_TAC;;

let fmap_simp_lemma1 = cake_theorem "fmap_simp_lemma1[local]"
  (fun () ->
    `g |+ (0,x) |+ (5,y) |+ (0,z) = g |+ (0,z) |+ (5,y)`)
  CHEAT_TAC;;

let get_stack_heap_limit''_def = cake_define
  `get_stack_heap_limit'' (h2:num) (h3:num) (h4:num) =
     (h4 - h3 - LENGTH stack_remove_store_list,(h3 - h2) DIV 2)`;;

let get_stack_heap_limit'_def = cake_define
  `get_stack_heap_limit' max_heap p2 p3 (p4:'a word) =
     (let ptr2 = w2n p2 in
     let ptr3 = w2n p3 in
     let ptr4 = w2n p4 in
     let d = dimindex (:'a) DIV 8 in
     let max_heap_w = (if max_heap * w2n (bytes_in_word:'a word) <
       dimword (:'a) then
                        bytes_in_word * n2w max_heap else --((n2w
                          1):'a word)) in
     let reg3 = n2w ptr2 +
                (--(n2w 1) * n2w ptr2 +
                 (if max_heap_w <+ --(n2w 1) * n2w ptr2 + n2w ptr3
                   then
                   max_heap_w + (n2w ptr2:'a word) else n2w ptr3))
                     >>> (backend_common_word_shift (:'a) + 1) <<
                     (backend_common_word_shift (:'a) + 1) in
       get_stack_heap_limit'' (ptr2 DIV d) (w2n reg3 DIV d) (ptr4
         DIV d))`;;

let get_stack_heap_limit_def = cake_define
  `get_stack_heap_limit max_heap (ptr2,ptr3,(ptr4:'a word)) =
     (let middle = ptr2 + (--(n2w 1) * ptr2 + ptr4) >>>
       (backend_common_word_shift (:'a) + 1) <<
       backend_common_word_shift (:'a) in
     let adj_ptr2 = ptr2 + bytes_in_word * n2w max_stack_alloc in
     let adj_ptr4 = ptr4 - (bytes_in_word * n2w max_stack_alloc) in
     let adj_ptr3 = (if adj_ptr2 <=+ ptr3 /\ ptr3 <=+ adj_ptr4 then
       ptr3 else middle) in
       get_stack_heap_limit' max_heap ptr2 adj_ptr3 ptr4)`;;

let read_pointers_def = cake_define
  `read_pointers s =
     (theWord (THE (FLOOKUP (stackSem_state_regs s) 2)),
      theWord (THE (FLOOKUP (stackSem_state_regs s) 3)),
      theWord (THE (FLOOKUP (stackSem_state_regs s) 4)))`;;


(* memory *)
(* move *)
let word_list_inj = cake_theorem "word_list_inj"
  (fun () ->
    `!xs a u u'. misc_word_list a xs u /\ misc_word_list a xs u' ==> u
  = u'`)
  CHEAT_TAC;;

(* move? *)
let word_list_set = cake_theorem "word_list_set"
  (fun () ->
    `!xs a. good_dimindex (:'a) /\
            w2n a + LENGTH xs * w2n (bytes_in_word:'a word) <
              dimword (:'a) ==>
            misc_word_list a xs (set_of_list (GENLIST (\i. a +
              n2w i * (bytes_in_word:'a word),EL i xs) (LENGTH xs)))`)
  CHEAT_TAC;;

(* move? *)
let word_list_seteq = cake_theorem "word_list_seteq"
  (fun () ->
    `!xs a. good_dimindex (:'a) /\
            w2n a + LENGTH xs * w2n (bytes_in_word:'a word) <
              dimword (:'a) ==>
            misc_word_list a xs = (\s. s = set_of_list (GENLIST
              (\i. a + n2w i * (bytes_in_word:'a word),EL i xs)
              (LENGTH xs)))`)
  CHEAT_TAC;;

(* move? *)
let word_list_EL_in_memory = cake_theorem "word_list_EL_in_memory"
  (fun () ->
    `good_dimindex (:'a) /\
     w2n a + LENGTH xs * w2n (bytes_in_word:'a word) < dimword
       (:'a) /\
     (r1 * misc_word_list a xs * r2) (fun2set (m,dm)) /\
     i < LENGTH xs ==> m (a + n2w i * (bytes_in_word:'a word)) =
       EL i xs`)
  CHEAT_TAC;;

(* move? *)
let word_list_in_memory = cake_theorem "word_list_in_memory"
  (fun () ->
    `(r1 * misc_word_list a xs * r2) (fun2set (m,dm)) /\
     good_dimindex (:'a) /\
     w2n a + LENGTH xs * w2n (bytes_in_word:'a word) < dimword
       (:'a) ==>
              memory m (addresses a (LENGTH xs)) = misc_word_list
                (a:'a word) xs`)
  CHEAT_TAC;;

let init_code_thm = cake_theorem "init_code_thm"
  (fun () ->
    `init_code_pre k bitmaps data_sp s /\ stack_removeProof_code_rel
  jump off k code (state_code s) /\ compile_oracle
      s = (I ## MAP (prog_comp jump off k) ## I) o coracle /\
      (!n i p. MEM (i,p) (FST (SND (coracle n))) ==> reg_bound p k
        /\ stack_num_stubs <= i + 1) /\
      sptree_lookup stack_err_lab (state_code s) = SOME (halt_inst
        (n2w 2)) /\
      max_stack_alloc <= max_heap ==>
      (match evaluate (stack_remove_init_code gen_gc max_heap k,s)
        with (SOME res,t) -> F | (NONE,t) ->
           (?w2 w3 (w4:'a word).
           FLOOKUP (stackSem_state_regs s) 2 = SOME (wordLang_Word
             w2) /\ byte_aligned w2 /\
           FLOOKUP (stackSem_state_regs t) (k + 2) = SOME
             (wordLang_Word w2) /\
           FLOOKUP (stackSem_state_regs s) 4 = SOME (wordLang_Word
             w4) /\ byte_aligned w4 /\ w2 <+ w4 /\
           FLOOKUP (stackSem_state_regs t) k = SOME (wordLang_Word
             (w4 - bytes_in_word)) /\
           (w2 + n2w max_stack_alloc * bytes_in_word <=+ w3 /\
            w3 <=+ w4 - n2w max_stack_alloc * bytes_in_word /\
            w2n (--(n2w 1) * w2 + w3) <= max_heap * w2n
              (bytes_in_word:'a word) /\
            (w2n (bytes_in_word:'a word)) * max_heap < dimword
              (:'a) ==>
            FLOOKUP (stackSem_state_regs t) (k + 1) =
            SOME (wordLang_Word (
                        ((w3 + --(n2w 1) * w2) >>>
                          (backend_common_word_shift (:'a) + 1) <<
                          (backend_common_word_shift (:'a) + 1)) + w2 +
                          (bytes_in_word:'a word) * (n2w (LENGTH
                          stack_remove_store_list))))) /\
           FLOOKUP (stackSem_state_regs s) 3 = SOME (wordLang_Word
             w3)) /\
           stack_removeProof_state_rel jump off k (init_reduce
             gen_gc jump off k code bitmaps data_sp coracle t) t /\
             state_ffi
           t = state_ffi s /\
           init_prop gen_gc max_heap data_sp (get_stack_heap_limit
             max_heap (read_pointers s))
                     (init_reduce gen_gc jump off k code bitmaps
                       data_sp coracle t) /\ state_mdomain
           s = state_mdomain t /\ state_sh_mdomain
           s = state_sh_mdomain t /\
           (let t0 = init_reduce gen_gc jump off k code bitmaps
             data_sp coracle t in
              fun2set (state_memory s,state_mdomain t0) = fun2set
                (state_memory t,state_mdomain t0)))`)
  CHEAT_TAC;;

let make_init_opt_def = cake_define
  `make_init_opt gen_gc' max_heap bitmaps data_sp coracle jump off k
  code (s:('a,'c,'ffi)stackSem_state) =
     (match evaluate (stack_remove_init_code gen_gc' max_heap k,s)
       with (SOME _6,t) -> NONE | (NONE,t) -> (if init_prop gen_gc'
       max_heap data_sp
                        (get_stack_heap_limit max_heap (read_pointers
                          s))
                        (init_reduce gen_gc' jump off k code
                          bitmaps data_sp coracle t) then SOME
                          (init_reduce gen_gc' jump off k code
                          bitmaps data_sp coracle t) else NONE))`;;

let init_pre_def = cake_define
  `init_pre gen_gc' max_heap bitmaps data_sp k start' s <=>
     sptree_lookup 0 (state_code s) = SOME (Seq
       (stack_remove_init_code gen_gc' max_heap k)
                              (Call NONE (INL start') NONE)) /\
     init_code_pre k bitmaps data_sp s /\ max_stack_alloc <=
       max_heap`;;

let evaluate_init_code = cake_theorem "evaluate_init_code"
  (fun () ->
    `init_pre gen_gc max_heap bitmaps data_sp k start s /\
  stackSem_state_compile_oracle
      s = ((I ## MAP (prog_comp jump off k) ## I) o coracle) /\
      (!n i p. MEM (i,p) (FST (SND (coracle n))) ==> reg_bound p k
        /\ stack_num_stubs <= i + 1) /\
      sptree_lookup stack_err_lab (state_code s) = SOME (halt_inst
        (n2w 2)) /\
      stack_removeProof_code_rel jump off k code (state_code s) ==>
      (match evaluate (stack_remove_init_code gen_gc max_heap k,s)
        with (NONE,t) -> (?r. make_init_opt gen_gc max_heap bitmaps
        data_sp coracle jump off k code s = SOME r /\
                        stack_removeProof_state_rel jump off k r
                          t /\ state_ffi t = state_ffi s) | _7 -> F)`)
  CHEAT_TAC;;

let clock_neutral_store_list_code =
  cake_theorem "clock_neutral_store_list_code"
  (fun () ->
    `!xs n k. clock_neutral (store_list_code n k xs)`)
  CHEAT_TAC;;

let evaluate_init_code_clock =
  cake_theorem "evaluate_init_code_clock[local]"
  (fun () ->
    `evaluate (stack_remove_init_code gen_gc max_heap k,s) = (res,t) ==>
       evaluate (stack_remove_init_code gen_gc max_heap
         k,state_clock_fupd (K c) s) =
         (res,state_clock_fupd (K c) t)`)
  CHEAT_TAC;;

let evaluate_init_code_ffi = cake_theorem "evaluate_init_code_ffi"
  (fun () ->
    `evaluate (stack_remove_init_code gen_gc max_heap
  k,(s:('a,'c,'ffi)stackSem_state)) = (res,t) ==>
      evaluate (stack_remove_init_code gen_gc max_heap
        k,stackSem_state_ffi_fupd (K c) s) =
        (res,((state_ffi_fupd (K c)
          t):('a,'c,'ffi)stackSem_state))`)
  CHEAT_TAC;;

let init_semantics = cake_theorem "init_semantics"
  (fun () ->
    `sptree_lookup stack_err_lab (state_code s) = SOME (halt_inst (n2w
  2)) /\
      stack_removeProof_code_rel jump off k code (state_code s) /\
      init_pre gen_gc max_heap bitmaps data_sp k start s /\
        stackSem_state_compile_oracle
      s = ((I ## MAP (prog_comp jump off k) ## I) o coracle) /\
      (!n i p. MEM (i,p) (FST (SND (coracle n))) ==> reg_bound p k
        /\ stack_num_stubs <= i + 1) ==>
      (match evaluate (stack_remove_init_code gen_gc max_heap k,s)
        with (NONE,t) ->
          (semantics 0 s = semantics start t) /\
          (?r. make_init_opt gen_gc max_heap bitmaps data_sp
            coracle jump off k code s = SOME r /\
              stack_removeProof_state_rel jump off k r t) | _8 ->
                F)`)
  CHEAT_TAC;;

let make_init_opt_SOME_semantics =
  cake_theorem "make_init_opt_SOME_semantics"
  (fun () ->
    `init_pre gen_gc max_heap bitmaps data_sp k start s2 /\
  stackSem_state_compile_oracle
      s2 = ((I ## MAP (prog_comp jump off k) ## I) o coracle) /\
      (!n i p. MEM (i,p) (FST (SND (coracle n))) ==> reg_bound p k
        /\ stack_num_stubs <= i + 1) /\
      stack_removeProof_code_rel jump off k code (state_code s2) /\
      sptree_lookup stack_err_lab (state_code s2) = SOME (halt_inst
        (n2w 2)) ==>
      (?s1.
        make_init_opt gen_gc max_heap bitmaps data_sp coracle jump
          off k code s2 = SOME s1 /\
        (~(semantics start s1 = ffi_Fail) ==>
         semantics 0 s2 = semantics start s1))`)
  CHEAT_TAC;;

let IMP_code_rel = cake_theorem "IMP_code_rel[local]"
  (fun () ->
    `EVERY (\(n,p). reg_bound p k /\ stack_num_stubs <= n + 1) code1 /\
      code2 = fromAList (compile jump off gen_gc max_heap k start
        code1) ==>
      stack_removeProof_code_rel jump off k (fromAList code1)
        code2`)
  CHEAT_TAC;;

let make_init_any_def = cake_define
  `make_init_any gen_gc' max_heap bitmaps data_sp coracle jump off k
  code s =
     (match make_init_opt gen_gc' max_heap bitmaps data_sp coracle
       jump off k code s with SOME t -> t | NONE -> state_store_fupd (K
       (FEMPTY |++ (MAP (\x. (x,wordLang_Word (n2w 0)))
                              (CurrHeap ::
                                stack_remove_store_list))))
                                (state_code_fupd (K code)
                                (state_code_buffer_fupd (K (mk_buffer
                                (n2w 0) [] 0))
                                (state_data_buffer_fupd (K (mk_buffer
                                (n2w 0) [] 0)) (compile_oracle_fupd
                                (K coracle) (compile_fupd (K (\c p.
                                compile s c (MAP (prog_comp jump off
                                k) p)))
                                (stackSem_state_stack_space_fupd (K
                                0) (stack_fupd (K [wordLang_Word (n2w
                                0)]) (stackSem_state_use_alloc_fupd
                                (K F) (stackSem_state_use_store_fupd
                                (K T) (stackSem_state_use_stack_fupd
                                (K T) (stackSem_state_bitmaps_fupd (K
                                [(n2w 4)]) (state_mdomain_fupd (K
                                EMPTY) (fp_regs_fupd (K FEMPTY)
                                (stackSem_state_regs_fupd (K (FEMPTY
                                |+ (0,Loc 1 0))) s)))))))))))))))`;;

let discharge_these_def = cake_define
  `discharge_these jump off gen_gc' max_heap k start' coracle code s2
  <=>
       EVERY (\(n,p). reg_bound p k /\ stack_num_stubs <= n + 1) code
         /\
       (!n i p.
         MEM (i,p) (FST (SND (coracle n))) ==> reg_bound p k /\
           stack_num_stubs <= i + 1) /\ compile_oracle
       s2 = (I ## MAP (prog_comp jump off k) ## I) o coracle /\
         state_code
       s2 = fromAList (compile jump off gen_gc' max_heap k start'
         code) /\
       8 <= k /\ 1 IN domain (state_code s2) /\
       {k,k + 1,k + 2} SUBSET stackSem_state_ffi_save_regs s2 /\
         ~(stackSem_state_use_stack s2) /\
       ~(stackSem_state_use_store s2) /\
         ~(stackSem_state_use_alloc s2) /\ max_stack_alloc <=
         max_heap`;;

let propagate_these_def = cake_define
  `propagate_these s (bitmaps:('a word) list) data_sp <=>
   good_dimindex (:'a) /\
   (?ptr2 ptr3 ptr4 bitmap_ptr.
        FLOOKUP (stackSem_state_regs s) 2 = SOME (wordLang_Word ptr2)
          /\
        FLOOKUP (stackSem_state_regs s) 3 = SOME (wordLang_Word ptr3)
          /\
        FLOOKUP (stackSem_state_regs s) 4 = SOME (wordLang_Word ptr4)
          /\ state_memory
        s ptr2 = wordLang_Word bitmap_ptr /\ state_memory
        s (ptr2 + bytes_in_word) =
            wordLang_Word (bitmap_ptr + bytes_in_word * n2w (LENGTH
              bitmaps)) /\ state_memory
        s (ptr2 + (n2w 2) * bytes_in_word) =
            wordLang_Word (bitmap_ptr + bytes_in_word * n2w (LENGTH
              bitmaps) +
                              bytes_in_word * n2w data_sp) /\
                                state_memory
        s (ptr2 + (n2w 3) * bytes_in_word) =
          wordLang_Word (buffer_position (state_code_buffer s)) /\
            state_memory
        s (ptr2 + (n2w 4) * bytes_in_word) =
          wordLang_Word (buffer_position (state_code_buffer s) + n2w
            (buffer_space_left (state_code_buffer s))) /\ buffer_buffer
            (state_code_buffer
        s) = [] /\
        ptr2 <=+ ptr4 /\
        byte_aligned ptr2 /\ byte_aligned ptr4 /\ byte_aligned
          bitmap_ptr /\
        (n2w 1024) * bytes_in_word <=+ ptr4 - ptr2 /\
        (misc_word_list bitmap_ptr (MAP wordLang_Word bitmaps) *
         word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH
           bitmaps)) data_sp *
         word_list_exists ptr2
             (w2n (--(n2w 1) * ptr2 + ptr4) DIV w2n (bytes_in_word:'a
               word)))
          (fun2set (state_memory s,state_mdomain s)))`;;

let make_init_semantics = cake_theorem "make_init_semantics"
  (fun () ->
    `discharge_these jump off gen_gc max_heap k start coracle code s2 /\
     propagate_these s2 bitmaps data_sp ==>
     (?s1.
       make_init_opt gen_gc max_heap (bitmaps:('a word) list)
         data_sp coracle jump off k (fromAList code) s2 = SOME s1 /\
       (
        ~(semantics start s1 = ffi_Fail) ==>
        semantics 0 s2 = semantics start s1))`)
  CHEAT_TAC;;

let make_init_any_ffi = cake_theorem "make_init_any_ffi"
  (fun () ->
    `state_ffi
        (make_init_any gen_gc max_heap bitmaps data_sp coracle jump
          off k code s) = stackSem_state_ffi
         (s:('a,'c,'ffi)stackSem_state)`)
  CHEAT_TAC;;

let make_init_any_bitmaps = cake_theorem "make_init_any_bitmaps"
  (fun () ->
    `stackSem_state_bitmaps
        (make_init_any gen_gc max_heap bitmaps data_sp coracle jump
          off k code s) =
            (if IS_SOME (make_init_opt gen_gc max_heap bitmaps
              data_sp coracle jump off k code s) then bitmaps else
              [(n2w 4)])`)
  CHEAT_TAC;;

let make_init_any_use_stack = cake_theorem "make_init_any_use_stack"
  (fun () ->
    `stackSem_state_use_stack
        (make_init_any gen_gc max_heap bitmaps data_sp coracle
          jump off k code s)`)
  CHEAT_TAC;;

let make_init_any_use_store = cake_theorem "make_init_any_use_store"
  (fun () ->
    `stackSem_state_use_store
        (make_init_any gen_gc max_heap bitmaps data_sp coracle
          jump off k code s)`)
  CHEAT_TAC;;

let make_init_any_use_alloc = cake_theorem "make_init_any_use_alloc"
  (fun () ->
    `~(stackSem_state_use_alloc (make_init_any gen_gc max_heap bitmaps
  data_sp coracle jump off k code s))`)
  CHEAT_TAC;;

let make_init_any_code = cake_theorem "make_init_any_code"
  (fun () ->
    `state_code
        (make_init_any gen_gc max_heap bitmaps data_sp coracle
          jump off k code s) = code`)
  CHEAT_TAC;;

let make_init_any_stack_limit = cake_theorem "make_init_any_stack_limit"
  (fun () ->
    `LENGTH (stack (make_init_any gen_gc max_heap (bitmaps:('a word)
  list) data_sp coracle jump off k code s)) *
        (dimindex (:'a) DIV 8) < dimword (:'a)`)
  CHEAT_TAC;;

let make_init_any_compile_oracle =
  cake_theorem "make_init_any_compile_oracle"
  (fun () ->
    `compile_oracle
        (make_init_any ggc max_heap bitmaps data_sp coracle jump
          off k code s) = coracle`)
  CHEAT_TAC;;

(* HOL4 stack_removeProofScript.sml:4158-4166: code that the source
   has in a comment *)

(* Syntactic *)

let FST_prog_comp = cake_theorem "FST_prog_comp[simp]"
  (fun () ->
    `FST (prog_comp jump off k pp) = FST pp`)
  CHEAT_TAC;;

let stack_remove_lab_pres = cake_theorem "stack_remove_lab_pres"
  (fun () ->
    `!jump off k p.
       stackProps_extract_labels p = stackProps_extract_labels
         (comp jump off k p)`)
  CHEAT_TAC;;

let stack_remove_comp_stack_asm_name =
  cake_theorem "stack_remove_comp_stack_asm_name"
  (fun () ->
    `!jump off k p.
       stack_asm_name c p /\ stack_asm_remove (c:'a asm_config) p
         /\
       asm_offset_ok 0 (asm_config_addr_offset c) (n2w 0) /\
       good_dimindex (:'a) /\
       (!n. n <= max_stack_alloc ==> asm_config_valid_imm
       c (INL Sub) (n2w (n * (dimindex (:'a) DIV 8))) /\
         asm_config_valid_imm
       c (INL Add) (n2w (n * (dimindex (:'a) DIV 8)))) /\
       (
        // Needed to implement the global store
        !s. asm_offset_ok 0 (asm_config_addr_offset c)
          (store_offset s)) /\
       reg_name (k + 2) c /\
       reg_name (k + 1) c /\
       reg_name k c /\ ~(k = 0) /\
       off = asm_config_addr_offset c ==>
       stack_asm_name c (comp jump off k p)`)
  CHEAT_TAC;;

let stack_remove_stack_asm_name =
  cake_theorem "stack_remove_stack_asm_name"
  (fun () ->
    `EVERY (\(n,p). stack_asm_name c p) prog /\
     EVERY (\(n,p). (stack_asm_remove (c:'a asm_config) p)) prog /\
     asm_offset_ok 0 (asm_config_addr_offset c) (n2w 0) /\
     good_dimindex (:'a) /\
     (!n. n <= max_stack_alloc ==> asm_config_valid_imm
     c (INL Sub) (n2w (n * (dimindex (:'a) DIV 8))) /\
       asm_config_valid_imm
     c (INL Add) (n2w (n * (dimindex (:'a) DIV 8)))) /\
       asm_config_valid_imm
     c (INL Add) (n2w 4) /\ asm_config_valid_imm
     c (INL Add) (n2w 8) /\
     (
      // Needed to implement the global store
      !s. asm_offset_ok 0 (asm_config_addr_offset c) (store_offset
        s)) /\
     reg_name 7 c /\
     reg_name (k + 2) c /\
     reg_name (k + 1) c /\
     reg_name k c /\ ~(k = 0) ==>
     EVERY (\(n,p). stack_asm_name c p)
     (compile jump (asm_config_addr_offset c) gen_gc max_heap k
       start prog)`)
  CHEAT_TAC;;

let upshift_downshift_call_args =
  cake_theorem "upshift_downshift_call_args"
  (fun () ->
    `!n n0.
     call_args (upshift n n0) 1 2 3 4 0 /\
     call_args (downshift n n0) 1 2 3 4 0`)
  CHEAT_TAC;;

let stack_remove_call_args = cake_theorem "stack_remove_call_args"
  (fun () ->
    `compile jump off gen_gc n k pos p = p' /\
      EVERY (\p. call_args p 1 2 3 4 0) (MAP SND p) ==>
      EVERY (\p. call_args p 1 2 3 4 0) (MAP SND p')`)
  CHEAT_TAC;;

cake_hide [];;

cake_hide_consts [];;
