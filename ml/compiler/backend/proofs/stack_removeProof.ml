(* ======================================================== *)
(*  stack_removeProof: ported from HOL4's
    compiler/backend/proofs/stack_removeProofScript.sml  *)
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
needs "lib/byte.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/semanticsProps.ml";;

(* HOL4 ML code, not ported:
val word_shift_def = backend_commonTheory.word_shift_def
*)
(* HOL4 overload (expanded in the port):
     num_stubs = stack_num_stubs *)

(* TODO: move *)

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
     domain code2 = domain code1 UNION ({0,1,2}
   tokens_End
   Definition is_SOME_Word_def:(is_SOME_Word (SOME (wordLang_Word w))
     = T)) /\
   (is_SOME_Word _1 = F)`;;
hol4_overload "code_rel" "stack_removeProof_code_rel";;

let the_SOME_Word_def = cake_define
  `(the_SOME_Word (SOME (wordLang_Word w)) = w)`;;

let state_rel_def = cake_define
  `stack_removeProof_state_rel jump off k
  (s1:('a,'c,'ffi)stackSem_state) s2 <=> stackSem_state_use_stack
     s1 /\ stackSem_state_use_store s1 /\
     ~stackSem_state_use_stack s2 /\ ~stackSem_state_use_store s2 /\
     ~stackSem_state_use_alloc s2 /\ ~stackSem_state_use_alloc s1 /\
       be
     s2 = be s1 /\ state_gc_fun
     s2 = state_gc_fun s1 /\ state_clock
     s2 = state_clock s1 /\ state_ffi
     s2 = state_ffi s1 /\ stackSem_state_ffi_save_regs
     s2 = stackSem_state_ffi_save_regs s1 /\ fp_regs
     s2 = fp_regs s1 /\ state_code_buffer
     s2 = state_code_buffer s1 /\ state_sh_mdomain
     s2 = state_sh_mdomain s1 /\ compile
     s1 = (\c p. compile s2 c (MAP (prog_comp jump off k) p)) /\
       compile_oracle
     s2 = (\n. (I ## MAP (prog_comp jump off k) ## I) (compile_oracle
       s1 n)) /\
     (!n i p. MEM (i,p) (FST (SND (compile_oracle s1 n))) ==>
       reg_bound p k /\ stack_num_stubs <= i + 1) /\
     good_dimindex (:'a) /\
     (!n.
        n < k ==>
        FLOOKUP (stackSem_state_regs s2) n = FLOOKUP
          (stackSem_state_regs s1) n) /\
     stack_removeProof_code_rel jump off k (state_code s1)
       (state_code s2) /\
     sptree_lookup stack_err_lab (state_code s2) = SOME (halt_inst
       (n2w 2)) /\
     FLOOKUP (stackSem_state_regs s2) (k + 2) = FLOOKUP (state_store
       s1) CurrHeap /\
     {k,k + 1,k + 2} SUBSET stackSem_state_ffi_save_regs s2 /\
     is_SOME_Word (FLOOKUP (state_store s1) BitmapBase) /\
       stackSem_state_stack_space
     s1 <= LENGTH (stack s1) /\
     (let bp = (the_SOME_Word (FLOOKUP (state_store s1) BitmapBase)
       << backend_common_word_shift (:'a)) in
     let all_bitmaps = stackSem_state_bitmaps s1 ++ buffer_buffer
       (state_data_buffer s1) in buffer_position (state_data_buffer
       s1) = bp + bytes_in_word * n2w (LENGTH (stackSem_state_bitmaps
         s1)) /\
     (match FLOOKUP (stackSem_state_regs s2) (k + 1) with SOME
       (wordLang_Word base) ->
       dimindex (:'a) DIV 8 * max_stack_alloc <= w2n base /\
       w2n base + w2n (bytes_in_word:'a word) * LENGTH (stack s1) <
         dimword (:'a) /\
       FLOOKUP (stackSem_state_regs s2) k =
         SOME (wordLang_Word (base + bytes_in_word * n2w
           (stackSem_state_stack_space s1))) /\
       (memory (state_memory s1) (state_mdomain s1) *
        misc_word_list bp (MAP wordLang_Word all_bitmaps) *
        word_list_exists (bp + bytes_in_word * n2w (LENGTH
          all_bitmaps)) (buffer_space_left (state_data_buffer s1)) *
        word_store base (state_store s1) *
        misc_word_list base (stack s1))
         (fun2set (state_memory s2,state_mdomain s2)) | _2 -> F))`;;
hol4_overload "state_rel" "stack_removeProof_state_rel";;

(* Significantly faster than SEP_R_TAC *)

(* basically the same thing, but without the read assumption *)

(* HOL4 ML code, not ported:
val write_fun2set2 = write_fun2set |> SIMP_RULE std_ss [GSYM STAR_COMM]
*)

(* init code *)

(* HOL4 ML code, not ported:
val tac = simp
  [list_Seq_def,evaluate_def,inst_def,word_exp_def,get_var_def,
       wordLangTheory.word_op_def,mem_load_def,assign_def,set_var_def,
       FLOOKUP_UPDATE,mem_store_def,dec_clock_def,get_var_imm_def,
       asmTheory.word_cmp_def,
       wordSemTheory.word_cmp_def,GREATER_EQ,GSYM NOT_LESS,FUPDATE_LIST,
       wordLangTheory.word_sh_def,halt_inst_def]
*)

(* HOL4 ML code, not ported:
val tac1 = simp [Once
  list_Seq_def,evaluate_def,inst_def,word_exp_def,get_var_def,
       wordLangTheory.word_op_def,mem_load_def,assign_def,set_var_def,
       FLOOKUP_UPDATE,mem_store_def,dec_clock_def,get_var_imm_def,
       asmTheory.word_cmp_def,
       wordSemTheory.word_cmp_def,GREATER_EQ,GSYM NOT_LESS,FUPDATE_LIST,
       wordLangTheory.word_sh_def,halt_inst_def]
*)

let mem_val_def = cake_define_list
  [`mem_val regs' (INL w) = wordLang_Word w`;
   `mem_val (regs':(num,'a word_loc)fmap) (INR n) = FAPPLY regs' n`];;

(* HOL4 ML code, not ported:
val halt_tac =
  tac \\ fs [good_dimindex_def]
  \\ rw [] \\ fs [dimword_def]
*)

let read_mem_def = cake_define_list
  [`stack_removeProof_read_mem a m 0 = []`;
   `stack_removeProof_read_mem a m (SUC n) =
         m a :: stack_removeProof_read_mem (a + bytes_in_word) m
           n`];;
hol4_overload "read_mem" "stack_removeProof_read_mem";;

let addresses_def = cake_define_list
  [`addresses a 0 = {}`;
   `addresses a (SUC n) = a INSERT addresses (a + bytes_in_word) n`];;

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
       DIV 8) in state_store_fupd (K (FEMPTY |++ (MAP (\n. match
       store_init gen_gc' k n with INL w -> (n,wordLang_Word w) | INR i
       -> (n,FAPPLY (stackSem_state_regs s) i))
                              (CurrHeap ::
                                stack_remove_store_list)))) (stack_fupd
                                (K (stack_removeProof_read_mem base_ptr
                                (state_memory s) (stack_sp + 1)))
                                (stackSem_state_stack_space_fupd (K
                                stack_sp) (state_data_buffer_fupd (K
                                (mk_buffer (bitmap_ptr + bytes_in_word *
                                n2w (LENGTH bitmaps)) [] data_sp))
                                (compile_oracle_fupd (K coracle)
                                (compile_fupd (K (\c p. compile s c (MAP
                                (prog_comp jump off k) p)))
                                (state_code_fupd (K code)
                                (stackSem_state_bitmaps_fupd (K bitmaps)
                                (state_mdomain_fupd (K (addresses
                                heap_ptr heap_sp))
                                (stackSem_state_use_alloc_fupd (K F)
                                (stackSem_state_use_store_fupd (K T)
                                (stackSem_state_use_stack_fupd (K T)
       s))))))))))))`;;

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
        FLOOKUP (state_store s) CurrHeap = SOME (wordLang_Word curr)
          /\
        FLOOKUP (state_store s) NextFree = SOME (wordLang_Word curr)
          /\
        FLOOKUP (state_store s) TriggerGC = SOME (wordLang_Word (if
          gen_gc' then curr else other)) /\
        FLOOKUP (state_store s) EndOfHeap = SOME (wordLang_Word
          other) /\
        FLOOKUP (state_store s) OtherHeap = SOME (wordLang_Word
          other) /\
        FLOOKUP (state_store s) BitmapBase = SOME (wordLang_Word
          bitmap_base) /\
        FLOOKUP (state_store s) HeapLength = SOME (wordLang_Word (n2w
          len * bytes_in_word)) /\
        FLOOKUP (state_store s) ProgStart = SOME (wordLang_Word (n2w
          0)) /\
        FLOOKUP (state_store s) AllocSize = SOME (wordLang_Word (n2w
          0)) /\
        FLOOKUP (state_store s) Globals = SOME (wordLang_Word (n2w
          0)) /\
        FLOOKUP (state_store s) GlobReal = SOME (wordLang_Word curr)
          /\
        FLOOKUP (state_store s) Handler = SOME (wordLang_Word (n2w
          0)) /\
        FLOOKUP (state_store s) GenStart = SOME (wordLang_Word (n2w
          0)) /\
        FLOOKUP (state_store s) CodeBuffer = SOME (wordLang_Word
          (buffer_position (state_code_buffer s))) /\
        FLOOKUP (state_store s) CodeBufferEnd =
          SOME (wordLang_Word (buffer_position (state_code_buffer s)
            + n2w (buffer_space_left (state_code_buffer s)))) /\
        FLOOKUP (state_store s) BitmapBuffer = SOME (wordLang_Word
          (buffer_position (state_data_buffer s))) /\
        FLOOKUP (state_store s) BitmapBufferEnd =
          SOME (wordLang_Word
           (buffer_position (state_data_buffer s) +
            bytes_in_word * n2w (buffer_space_left (state_data_buffer
              s)))) /\
        stack_heap_limit_ok s stack_heap_lim /\ buffer_buffer
          (state_code_buffer
        s) = [] /\ buffer_buffer (state_data_buffer s) = [] /\
          stackSem_state_use_stack
        s /\ stackSem_state_use_store s /\
        FLOOKUP (stackSem_state_regs s) 0 = SOME (Loc 1 0) /\
        LENGTH (stackSem_state_bitmaps s) + data_sp + 1 < dimword
          (:'a) /\
        LENGTH (stack s) < dimword (:'a) /\
        (other = curr + bytes_in_word * n2w len) /\
        byte_aligned curr /\
        LAST (stack s) = wordLang_Word (n2w 0) /\
        LENGTH (stack s) = SUC (stackSem_state_stack_space s) /\
        LENGTH (stack s) * (dimindex (:'ga) DIV 8) < dimword (:'ga)
          /\
        len + len <= max_heap /\
        (word_list_exists curr len * word_list_exists other len)
           (fun2set (state_memory s,state_mdomain s)))`;;

let init_code_pre_def = cake_define
  `init_code_pre k bitmaps data_sp s <=>
     (?ptr2 ptr3 ptr4 bitmap_ptr.
       good_dimindex (:'a) /\ 8 <= k /\ 1 IN domain (state_code s) /\
       {k,k + 1,k + 2} SUBSET stackSem_state_ffi_save_regs s /\
       ~stackSem_state_use_stack s /\ ~stackSem_state_use_store s /\
         ~stackSem_state_use_alloc s /\
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
       s) = [] /\
       (misc_word_list bitmap_ptr (MAP wordLang_Word bitmaps) *
        word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH
          bitmaps)) data_sp *
        word_list_exists ptr2 (w2n (ptr4 - ptr2) DIV w2n
          (bytes_in_word:'a word)))
         (fun2set (state_memory s,state_mdomain s)))`;;

(* The extra b equality makes this work better with SEP_NEQ_TAC *)

let get_stack_heap_limit''_def = cake_define
  `get_stack_heap_limit'' (h2:num) (h3:num) (h4:num) =
     (h4 - h3 - LENGTH stack_remove_store_list,(h3 - h2) DIV 2)`;;

let get_stack_heap_limit'_def = cake_define
  `get_stack_heap_limit' max_heap p2 p3 (p4:'a word) =
     (let ptr2 = w2n p2 in
     let ptr3 = w2n p3 in
     let ptr4 = w2n p4 in
     let d = dimindex (:'a) DIV 8 in
     let max_heap_w = if max_heap * w2n (bytes_in_word:'a word) <
       dimword (:'ga) then
                        bytes_in_word * n2w max_heap else --((n2w
                          1):'a word) in
     let reg3 = n2w ptr2 +
                (--(n2w 1) * n2w ptr2 +
                 (if max_heap_w <+ --(n2w 1) * n2w ptr2 + n2w ptr3
                   then
                   max_heap_w + (n2w ptr2:'a word) else n2w ptr3))
                     >>> (backend_common_word_shift (:'ga) + 1) <<
                     (backend_common_word_shift (:'ga) + 1) in
       get_stack_heap_limit'' (ptr2 DIV d) (w2n reg3 DIV d) (ptr4
         DIV d))`;;

let get_stack_heap_limit_def = cake_define
  `get_stack_heap_limit max_heap (ptr2,ptr3,(ptr4:'a word)) =
     (let middle = ptr2 + (--(n2w 1) * ptr2 + ptr4) >>>
       (backend_common_word_shift (:'ga) + 1) <<
       backend_common_word_shift (:'ga) in
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

(* move? *)

(* move? *)

(* move? *)

(* move? *)

let make_init_opt_def = cake_define
  `make_init_opt gen_gc' max_heap bitmaps data_sp coracle jump off k
  code (s:('a,'c,'ffi)stackSem_state) =
     (match evaluate (stack_remove_init_code gen_gc' max_heap k,s)
       with (SOME _3,t) -> NONE | (NONE,t) -> (if init_prop gen_gc'
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
         ~stackSem_state_use_stack s2 /\
       ~stackSem_state_use_store s2 /\ ~stackSem_state_use_alloc
         s2 /\ max_stack_alloc <= max_heap`;;

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

(*
Theorem make_init_any_data_buffer:
   (make_init_any ggc max_heap bitmaps data_sp coracle jump off k code
     s).data_buffer =
    the correct thing on the success branch (which needs to be set on
      the fail branch too)
Proof
  fs [make_init_any_def,make_init_opt_def,init_reduce_def]
  \\ every_case_tac \\ fs []
QED
*)

(* Syntactic *)
