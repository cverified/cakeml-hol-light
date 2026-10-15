(* ======================================================== *)
(*  wordSem: ported from HOL4's
    compiler/backend/semantics/wordSemScript.sml  *)
(* ======================================================== *)

(*
  The formal semantics of wordLang
*)

needs "basis/pure/mllist.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/encoders/asm/asmSem.ml";;
needs "lib/alignment.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/byte.ml";;
needs "lib/comparison.ml";;
needs "lib/integer_word.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/machine_ieee.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;
(* HOL4 ancestors outside the port: finite_map (* for call_FFI *) (*
   for build_lprefix_lub *) (* for FP *) (* for word_add_carry *) *)

let buffer_FIELDS = define_record "buffer"
  ["position","'a word";
   "buffer","('b word) list";
   "space_left","num"];;

let buffer_flush_def = cake_define
  `buffer_flush cb (w1:'a word) w2 =
     (if buffer_position cb = w1 /\ buffer_position cb + (n2w
       (dimindex (:'b) DIV 8)) * n2w (LENGTH (buffer_buffer cb)) = w2
       then
       SOME ((buffer_buffer cb:('b word) list),buffer_buffer_fupd (K
         []) (buffer_position_fupd (K w2)
             cb)) else NONE)`;;

let buffer_write_def = cake_define
  `buffer_write cb (w:'a word) (b:'b word) =
     (if buffer_position cb + (n2w (dimindex (:'b) DIV 8)) * n2w
       (LENGTH (buffer_buffer cb)) = w /\ 0 < buffer_space_left cb then
       SOME (buffer_space_left_fupd (K (buffer_space_left cb - 1))
         (buffer_buffer_fupd (K (buffer_buffer cb ++ [b])) cb)) else
         NONE)`;;

let is_fwd_ptr_def = cake_define
  `is_fwd_ptr x1 =
        match x1 with
          wordLang_Word w -> ((w && (n2w 3)) = (n2w 0))
        | _1 -> F`;;

let theWord_def = cake_define
  `theWord (wordLang_Word w) = w`;;

let isWord_def = cake_define
  `isWord x1 =
        match x1 with
          wordLang_Word w -> T
        | _2 -> F`;;

let word_cmp_def = cake_define
  `wordSem_word_cmp x1 x2 x3 =
        match (x1,x2,x3) with
          (Equal,wordLang_Word w1,wordLang_Word w2) -> SOME (w1 = w2)
        | (Less,(wordLang_Word w1),(wordLang_Word w2)) -> SOME (w1 <
          w2)
        | (asm_Lower,(wordLang_Word w1),(wordLang_Word w2)) -> SOME
          (w1 <+ w2)
        | (Test,(wordLang_Word w1),(wordLang_Word w2)) -> SOME ((w1
          && w2) = (n2w 0))
        | (Test,(Loc _3 n),(wordLang_Word w2)) -> (if ~(n = 0) then
          NONE else if w2 = (n2w 1) then SOME T else NONE)
        | (asm_NotEqual,(wordLang_Word w1),(wordLang_Word w2)) ->
          SOME (~(w1 = w2))
        | (asm_NotLess,(wordLang_Word w1),(wordLang_Word w2)) -> SOME
          (~(w1 < w2))
        | (asm_NotLower,(wordLang_Word w1),(wordLang_Word w2)) ->
          SOME (~(w1 <+ w2))
        | (asm_NotTest,(wordLang_Word w1),(wordLang_Word w2)) -> SOME
          (~((w1 && w2) = (n2w 0)))
        | (asm_NotTest,(Loc _4 n),(wordLang_Word w2)) -> (if ~(n = 0)
          then NONE else if w2 = (n2w 1) then SOME F else NONE)
        | (_5,_6,_7) -> NONE`;;
hol4_overload "word_cmp" "wordSem_word_cmp";;

let mem_load_32_def = cake_define
  `mem_load_32 m dm be' (w:'a word) =
   (if alignment_aligned 2 w then match m (byte_align w) with Loc _8
     _9 -> NONE | wordLang_Word v ->
            (if byte_align w IN dm then SOME (word_of_bytes be' ((n2w
              0):word32)
              [get_byte w v be'; get_byte (w + (n2w 1)) v be';
               get_byte (w + (n2w 2)) v be'; get_byte (w + (n2w
                 3)) v be']) else NONE) else NONE)`;;

let mem_store_32_def = cake_define
  `mem_store_32 m dm be' (w:'a word) (hw:word32) =
   (if alignment_aligned 2 w then match m (byte_align w) with
     wordLang_Word v ->
            (if byte_align w IN dm then
              let v0 = set_byte w (get_byte ((n2w 0):word32) hw be')
                v be' in
              let v1 = set_byte (w + (n2w 1)) (get_byte (n2w 1) hw
                be') v0 be' in
              let v2 = set_byte (w + (n2w 2)) (get_byte (n2w 2) hw
                be') v1 be' in
              let v3 = set_byte (w + (n2w 3)) (get_byte (n2w 3) hw
                be') v2 be' in
                SOME ((byte_align w =+ wordLang_Word v3) m) else
                  NONE) | _10 -> NONE else NONE)`;;

let mem_load_byte_aux_def = cake_define
  `mem_load_byte_aux m dm be' w =
     (match m (byte_align w) with Loc _11 _12 -> NONE | wordLang_Word
       v ->
         (if byte_align w IN dm then SOME (get_byte w v be') else
           NONE))`;;

let mem_store_byte_aux_def = cake_define
  `mem_store_byte_aux m dm be' w b =
     (match m (byte_align w) with wordLang_Word v ->
         (if byte_align w IN dm then SOME ((byte_align w =+
           wordLang_Word (set_byte w b v be')) m) else NONE) | _13 ->
           NONE)`;;

let write_bytearray_def = cake_define_list
  [`write_bytearray a [] m dm be' = m`;
   `write_bytearray a (b :: bs) m dm be' =
         (match mem_store_byte_aux (write_bytearray (a + (n2w 1))
           bs m dm be') dm be' a b with SOME m -> m | NONE -> m)`];;

let stack_frame_INDUCT,stack_frame_RECURSION = define_datatype
  "stack_frame = StackFrame (num option) ((num#'a word_loc) list) \
   ((num#'a word_loc) list) ((num#num#num) option)";;

(* HOL4 type abbreviation (expanded in the port):
     gc_fun_type = ('a word_loc list) # (('a word) -> ('a word_loc)) #
       ('a word) set #
      (store_name |-> 'a word_loc) ->
      (('a word_loc list) # (('a word) -> ('a word_loc)) #
      (store_name |-> 'a word_loc)) option *)

let gc_bij_ok_def = cake_define
  `gc_bij_ok (seq':num->num->num) = (!n. BIJ (seq' n) UNIV UNIV)`;;

let wordSem_state_FIELDS = define_record "wordSem_state"
  ["locals","('a word_loc) spt";
   "locals_size","num option";
   "fp_regs","(num,word64)fmap";
   "store","(store_name,'a word_loc)fmap";
   "stack","('a stack_frame) list";
   "stack_limit","num";
   "stack_max","num option";
   "stack_size","num spt";
   "memory","'a word->'a word_loc";
   "mdomain","'a word->bool";
   "sh_mdomain","'a word->bool";
   "permute","num->num->num";
   "compile","'c->(num#num#'a wordLang_prog) list->(word8 list#('a \
   word) list#'c) option";
   "compile_oracle","num->'c#(num#num#'a wordLang_prog) list";
   "code_buffer","('a,8)buffer";
   "data_buffer","('a,'a)buffer";
   "gc_fun","('a word_loc) list#('a word->'a word_loc)#('a \
   word->bool)#(store_name,'a word_loc)fmap->(('a word_loc) list#('a \
   word->'a word_loc)#(store_name,'a word_loc)fmap) option";
   "handler","num";
   "clock","num";
   "termdep","num";
   "code","(num#'a wordLang_prog) spt";
   "be","bool";
   "ffi","'ffi ffi_state"];;
hol4_overload "state_locals" "wordSem_state_locals";;
hol4_overload "state_locals_fupd" "wordSem_state_locals_fupd";;
hol4_overload "state_locals_size" "wordSem_state_locals_size";;
hol4_overload "state_locals_size_fupd"
  "wordSem_state_locals_size_fupd";;
hol4_overload "fp_regs" "wordSem_state_fp_regs";;
hol4_overload "fp_regs_fupd" "wordSem_state_fp_regs_fupd";;
hol4_overload "state_store" "wordSem_state_store";;
hol4_overload "state_store_fupd" "wordSem_state_store_fupd";;
hol4_overload "stack" "wordSem_state_stack";;
hol4_overload "stack_fupd" "wordSem_state_stack_fupd";;
hol4_overload "stack_limit" "wordSem_state_stack_limit";;
hol4_overload "stack_limit_fupd" "wordSem_state_stack_limit_fupd";;
hol4_overload "state_stack_max" "wordSem_state_stack_max";;
hol4_overload "state_stack_max_fupd" "wordSem_state_stack_max_fupd";;
hol4_overload "state_memory" "wordSem_state_memory";;
hol4_overload "state_memory_fupd" "wordSem_state_memory_fupd";;
hol4_overload "state_mdomain" "wordSem_state_mdomain";;
hol4_overload "state_mdomain_fupd" "wordSem_state_mdomain_fupd";;
hol4_overload "state_sh_mdomain" "wordSem_state_sh_mdomain";;
hol4_overload "state_sh_mdomain_fupd" "wordSem_state_sh_mdomain_fupd";;
hol4_overload "compile" "wordSem_state_compile";;
hol4_overload "compile_fupd" "wordSem_state_compile_fupd";;
hol4_overload "compile_oracle" "wordSem_state_compile_oracle";;
hol4_overload "compile_oracle_fupd"
  "wordSem_state_compile_oracle_fupd";;
hol4_overload "state_code_buffer" "wordSem_state_code_buffer";;
hol4_overload "state_code_buffer_fupd"
  "wordSem_state_code_buffer_fupd";;
hol4_overload "state_data_buffer" "wordSem_state_data_buffer";;
hol4_overload "state_data_buffer_fupd"
  "wordSem_state_data_buffer_fupd";;
hol4_overload "state_gc_fun" "wordSem_state_gc_fun";;
hol4_overload "state_gc_fun_fupd" "wordSem_state_gc_fun_fupd";;
hol4_overload "state_handler" "wordSem_state_handler";;
hol4_overload "state_handler_fupd" "wordSem_state_handler_fupd";;
hol4_overload "state_clock" "wordSem_state_clock";;
hol4_overload "state_clock_fupd" "wordSem_state_clock_fupd";;
hol4_overload "state_code" "wordSem_state_code";;
hol4_overload "state_code_fupd" "wordSem_state_code_fupd";;
hol4_overload "be" "wordSem_state_be";;
hol4_overload "be_fupd" "wordSem_state_be_fupd";;
hol4_overload "state_ffi" "wordSem_state_ffi";;
hol4_overload "state_ffi_fupd" "wordSem_state_ffi_fupd";;

let stack_size_frame_def = cake_define
  `stack_size_frame x1 =
      match x1 with
        StackFrame n _14 _15 NONE -> n
      | (StackFrame n _16 _17 (SOME _18)) -> OPTION_MAP ((+) 3) n`;;

let stack_size_def = cake_define
  `stack_size = FOLDR (OPTION_MAP2 (+) o stack_size_frame) (SOME 1)`;;

(* HOL4 ML code, not ported:
val state_component_equality = theorem"state_component_equality";
*)

let wordSem_result_INDUCT,wordSem_result_RECURSION = define_datatype
  "wordSem_result = wordSem_Result ('w word_loc) (('w word_loc) list) \
   | wordSem_Exception ('w word_loc) ('w word_loc) | wordSem_Break \
   (num) | wordSem_Continue (num) | wordSem_TimeOut | \
   wordSem_NotEnoughSpace | wordSem_FinalFFI (final_event) | \
   wordSem_Error";;
hol4_overload "Result" "wordSem_Result";;
hol4_overload "Exception" "wordSem_Exception";;
hol4_overload "Break" "wordSem_Break";;
hol4_overload "Continue" "wordSem_Continue";;
hol4_overload "TimeOut" "wordSem_TimeOut";;
hol4_overload "NotEnoughSpace" "wordSem_NotEnoughSpace";;
hol4_overload "FinalFFI" "wordSem_FinalFFI";;
hol4_overload "Error" "wordSem_Error";;

let isResult_def = cake_define
  `wordSem_isResult x1 =
        match x1 with
          wordSem_Result a b -> T
        | _19 -> F`;;
hol4_overload "isResult" "wordSem_isResult";;

let isException_def = cake_define
  `wordSem_isException x1 =
        match x1 with
          wordSem_Exception a b -> T
        | _20 -> F`;;
hol4_overload "isException" "wordSem_isException";;

(* HOL4 ML code, not ported:
val s = ``(s:('a,'c,'ffi) wordSem$state)``
*)

let dec_clock_def = cake_define
  `(\x y. strcat x y)
     dec_clock s = wordSem_state_clock_fupd (K
       (wordSem_state_clock s - 1)) s`;;

let fix_clock_def = cake_define
  `wordSem_fix_clock old_s (res,new_s) =
     (res,wordSem_state_termdep_fupd (K (wordSem_state_termdep
       old_s)) (wordSem_state_clock_fupd (K (if wordSem_state_clock
       old_s < wordSem_state_clock new_s then wordSem_state_clock
       old_s else wordSem_state_clock new_s)) new_s))`;;
hol4_overload "fix_clock" "wordSem_fix_clock";;

let is_word_def = cake_define
  `is_word x1 =
        match x1 with
          wordLang_Word w -> T
        | _21 -> F`;;

let get_word_def = cake_define
  `get_word (wordLang_Word w) = w`;;


let mem_store_def = cake_define
  `(\x y. strcat x y)
     (mem_store (addr:'a word) (w:'a word_loc)) s =
       (if addr IN wordSem_state_mdomain s then
         SOME (wordSem_state_memory_fupd (K ((addr =+ w)
           (wordSem_state_memory s))) s) else NONE)`;;

let mem_load_def = cake_define
  `(\x y. strcat x y)
     (mem_load (addr:'a word)) s =
       (if addr IN wordSem_state_mdomain s then
         SOME (wordSem_state_memory s addr) else NONE)`;;

let the_words_def = cake_define_list
  [`the_words [] = SOME []`;
   `the_words (w :: ws) =
         (match (w,the_words ws) with (SOME (wordLang_Word
           x),SOME xs) -> SOME (x :: xs) | _23 -> NONE)`];;

let get_var_def = cake_define
  `(\x y. strcat x y)
     (get_var v) s = sptree_lookup v (wordSem_state_locals s)`;;

let get_vars_def = cake_define_list
  [`(\x y. strcat x y) (wordSem_get_vars []) s = SOME []`;
   `wordSem_get_vars (v :: vs) s =
         (match get_var v s with NONE -> NONE | SOME x -> (match
           wordSem_get_vars vs s with NONE -> NONE | SOME xs -> SOME
           (x :: xs)))`];;
hol4_overload "get_vars" "wordSem_get_vars";;

let set_var_def = cake_define
  `(\x y. strcat x y)
     (set_var v x) s =
       (wordSem_state_locals_fupd (K (sptree_insert v x
         (wordSem_state_locals s))) s)`;;

let unset_var_def = cake_define
  `(\x y. strcat x y)
     (unset_var v) s = (wordSem_state_locals_fupd (K
       (sptree_delete v (wordSem_state_locals s))) s)`;;

let set_vars_def = cake_define
  `(\x y. strcat x y)
     (set_vars vs xs) s =
       (wordSem_state_locals_fupd (K (alist_insert vs xs
         (wordSem_state_locals s))) s)`;;

let get_store_def = cake_define
  `(\x y. strcat x y)
     (get_store v) s = (FLOOKUP (wordSem_state_store s) v)`;;

let set_store_def = cake_define
  `(\x y. strcat x y)
     (set_store v x) s = (wordSem_state_store_fupd (K
       (wordSem_state_store s |+ (v,x))) s)`;;

let word_exp_def = cake_define_list
  [`(\x y. strcat x y) wordSem_word_exp (s (Const w)) = SOME
  (wordLang_Word w)`;
   `wordSem_word_exp s (wordLang_Var v) = get_var v s`;
   `wordSem_word_exp s (wordLang_Lookup name) = get_store name s`;
   `wordSem_word_exp s (wordLang_Load addr') =
         (match wordSem_word_exp s addr' with SOME (wordLang_Word
           w) -> mem_load w s | _25 -> NONE)`;
   `wordSem_word_exp s (wordLang_Op op wexps) =
         (match the_words (MAP (wordSem_word_exp s) wexps) with
           SOME ws -> (OPTION_MAP wordLang_Word (wordLang_word_op op
           ws)) | _26 -> NONE)`;
   `wordSem_word_exp s (wordLang_Shift sh wexp wexp1) =
         (match (wordSem_word_exp s wexp,wordSem_word_exp s
           wexp1) with (SOME (wordLang_Word w),SOME (wordLang_Word
           w1)) -> OPTION_MAP wordLang_Word (word_sh sh w (w2n w1)) |
           _27 -> NONE)`];;
hol4_overload "word_exp" "wordSem_word_exp";;

(* Flushes the locals and (optionally) the store *)
let flush_state_def = cake_define
  `(\x y. strcat x y)
      (flush_state T) s  =
        match  with
           -> wordSem_state_locals_size_fupd (K (SOME 0))
             (wordSem_state_store_fupd (K FEMPTY)
             (wordSem_state_stack_fupd (K []) (wordSem_state_locals_fupd
             (K LN) s)))
        |  -> wordSem_state_locals_size_fupd (K (SOME 0))
          (wordSem_state_locals_fupd (K LN) s)`;;

let sh_mem_store_def = cake_define
  `(\x y. strcat x y)
     (sh_mem_store (a:'a word) (w:'a word)) s =
       (if a IN wordSem_state_sh_mdomain s then
         match call_FFI (wordSem_state_ffi s) (SharedMem MappedWrite)
           [(n2w 0):word8]
                       (word_to_bytes w F ++ word_to_bytes a F)
                         with FFI_final outcome -> (SOME
                         (wordSem_FinalFFI outcome),flush_state T s)
                         | FFI_return new_ffi new_bytes ->
                         (NONE,(wordSem_state_ffi_fupd (K new_ffi)
                         s)) else (SOME wordSem_Error,s))`;;

let sh_mem_load_def = cake_define
  `(\x y. strcat x y)
     (sh_mem_load (a:'a word)) s =
       (if a IN wordSem_state_sh_mdomain s then
         SOME (call_FFI (wordSem_state_ffi s) (SharedMem MappedRead)
           [(n2w 0):word8]
                       (word_to_bytes a F)) else NONE)`;;

let sh_mem_store_byte_def = cake_define
  `(\x y. strcat x y)
     (sh_mem_store_byte (a:'a word) (w:'a word)) s =
       (if byte_align a IN wordSem_state_sh_mdomain s then
         match call_FFI (wordSem_state_ffi s) (SharedMem MappedWrite)
           [(n2w 1):word8]
                       ([get_byte (n2w 0) w F] ++ word_to_bytes a F)
                         with
           FFI_final outcome -> (SOME (wordSem_FinalFFI
             outcome),flush_state T s) | FFI_return new_ffi new_bytes
             -> (NONE,(wordSem_state_ffi_fupd (K new_ffi) s)) else
             (SOME wordSem_Error,s))`;;

let sh_mem_store16_def = cake_define
  `(\x y. strcat x y)
     (sh_mem_store16 (a:'a word) (w:'a word)) s =
       (if byte_align a IN wordSem_state_sh_mdomain s then
         match call_FFI (wordSem_state_ffi s) (SharedMem MappedWrite)
           [(n2w 2):word8]
                       (TAKE 2 (word_to_bytes w F) ++ word_to_bytes a
                         F) with
           FFI_final outcome -> (SOME (wordSem_FinalFFI
             outcome),flush_state T s) | FFI_return new_ffi new_bytes
             -> (NONE,(wordSem_state_ffi_fupd (K new_ffi) s)) else
             (SOME wordSem_Error,s))`;;

let sh_mem_store32_def = cake_define
  `(\x y. strcat x y)
     (sh_mem_store32 (a:'a word) (w:'a word)) s =
       (if byte_align a IN wordSem_state_sh_mdomain s then
         match call_FFI (wordSem_state_ffi s) (SharedMem MappedWrite)
           [(n2w 4):word8]
                       (TAKE 4 (word_to_bytes w F) ++ word_to_bytes a
                         F) with
           FFI_final outcome -> (SOME (wordSem_FinalFFI
             outcome),flush_state T s) | FFI_return new_ffi new_bytes
             -> (NONE,(wordSem_state_ffi_fupd (K new_ffi) s)) else
             (SOME wordSem_Error,s))`;;

let sh_mem_load_byte_def = cake_define
  `(\x y. strcat x y)
     (sh_mem_load_byte (a:'a word)) s =
       (if byte_align a IN wordSem_state_sh_mdomain s then
         SOME (call_FFI (wordSem_state_ffi s) (SharedMem MappedRead)
           [(n2w 1):word8]
                       (word_to_bytes a F)) else NONE)`;;

let sh_mem_load16_def = cake_define
  `(\x y. strcat x y)
     (sh_mem_load16 (a:'a word)) s =
       (if byte_align a IN wordSem_state_sh_mdomain s then
         SOME (call_FFI (wordSem_state_ffi s) (SharedMem MappedRead)
           [(n2w 2):word8]
                       (word_to_bytes a F)) else NONE)`;;

let sh_mem_load32_def = cake_define
  `(\x y. strcat x y)
     (sh_mem_load32 (a:'a word)) s =
       (if byte_align a IN wordSem_state_sh_mdomain s then
         SOME (call_FFI (wordSem_state_ffi s) (SharedMem MappedRead)
           [(n2w 4):word8]
                       (word_to_bytes a F)) else NONE)`;;

(* set variable given the output from ShareLoad(Byte) *)
let sh_mem_set_var_def = cake_define_list
  [`(\x y. strcat x y) (sh_mem_set_var (SOME (FFI_final outcome))
  _28) s = (SOME (wordSem_FinalFFI outcome),flush_state T s)`;
   `sh_mem_set_var (SOME (FFI_return new_ffi new_bytes)) v s =
  (NONE,set_var v (wordLang_Word (word_of_bytes F (n2w 0) new_bytes))
  (wordSem_state_ffi_fupd (K new_ffi) s))`;
   `sh_mem_set_var _29 _30 s = (SOME wordSem_Error,s)`];;

let share_inst_def = cake_define_list
  [`share_inst Load v ad s = sh_mem_set_var (sh_mem_load ad s) v s`;
   `share_inst asm_Load8 v ad s = sh_mem_set_var (sh_mem_load_byte ad
  s) v s`;
   `share_inst asm_Load16 v ad s = sh_mem_set_var (sh_mem_load16 ad
  s) v s`;
   `share_inst asm_Load32 v ad s = sh_mem_set_var (sh_mem_load32 ad
  s) v s`;
   `share_inst Store v ad s = (match get_var v s with SOME
  (wordLang_Word v) -> sh_mem_store ad v s | _35 -> (SOME
  wordSem_Error,s))`;
   `share_inst asm_Store8 v ad s = (match get_var v s with SOME
  (wordLang_Word v) -> sh_mem_store_byte ad v s | _36 -> (SOME
  wordSem_Error,s))`;
   `share_inst asm_Store16 v ad s = (match get_var v s with SOME
  (wordLang_Word v) -> sh_mem_store16 ad v s | _37 -> (SOME
  wordSem_Error,s))`;
   `share_inst asm_Store32 v ad s = (match get_var v s with SOME
  (wordLang_Word v) -> sh_mem_store32 ad v s | _38 -> (SOME
  wordSem_Error,s))`];;

let call_env_def = cake_define
  `(\x y. strcat x y)
     (call_env args sptree_size) s = wordSem_state_stack_max_fupd (K
       (OPTION_MAP2 MAX (wordSem_state_stack_max s) (OPTION_MAP2 (+)
       (stack_size (wordSem_state_stack s)) sptree_size)))
       (wordSem_state_locals_size_fupd (K sptree_size)
       (wordSem_state_locals_fupd (K (fromList2 args))
       s))`;;

let list_rearrange_def = cake_define
  `list_rearrange mover xs =
     (if (BIJ mover (count (LENGTH xs)) (count (LENGTH xs))) then
       GENLIST (\i. EL (mover i) xs) (LENGTH xs) else
       xs)`;;

(* Compare on keys, if keys match (never), then compare on
   the word_loc vals. Treat Words as < Locs *)
let key_val_compare_def = cake_define
  `key_val_compare x y =
     (let ((a:num),b) = x in
     let ((a':num),b') = y in
       (a > a') \/
       (a = a' /\
         (match b with
           wordLang_Word x -> (match b' with wordLang_Word y -> x
             <= y | _39 -> T) | Loc a b -> (match b' with Loc a' b'
             -> (a > a') \/ (a = a' /\ b >= b') | _40 -> F))))`;;

(*
EVAL ``key_val_compare (1,Loc 3 4) (1,Loc 1 2)``
*)

let env_to_list_def = cake_define
  `env_to_list env (bij_seq:num->num->num) =
     (let mover = bij_seq 0 in
     let permute = (\n. bij_seq (n + 1)) in
     let l = toAList env in
     let l = sort key_val_compare l in
     let l = list_rearrange mover l in
       (l,permute))`;;

let push_env_def = cake_define_list
  [`(\x y. strcat x y) (push_env envs' NONE) s =
        (let l0 = toAList (FST envs') in let
            (l,permute) = env_to_list (SND envs')
              (wordSem_state_permute s) in let
            stack' = StackFrame (wordSem_state_locals_size s) l0 l
              NONE :: wordSem_state_stack s in
              wordSem_state_permute_fupd (K permute)
              (wordSem_state_stack_max_fupd (K (OPTION_MAP2 MAX
              (wordSem_state_stack_max s) (stack_size stack')))
              (wordSem_state_stack_fupd (K stack')
          s)))`;
   `push_env envs' (SOME ((w:num),(h:'a wordLang_prog),l1,l2)) s =
        (let l0 = toAList (FST envs') in let
            (l,permute) = env_to_list (SND envs')
              (wordSem_state_permute s) in let
            handler = SOME (wordSem_state_handler s,l1,l2) in let
            stack' = StackFrame (wordSem_state_locals_size s) l0 l
              handler :: wordSem_state_stack s in
              wordSem_state_handler_fupd (K (LENGTH (wordSem_state_stack
              s))) (wordSem_state_permute_fupd (K permute)
              (wordSem_state_stack_max_fupd (K (OPTION_MAP2 MAX
              (wordSem_state_stack_max s) (stack_size stack')))
              (wordSem_state_stack_fupd (K stack')
          s))))`];;

let pop_env_def = cake_define
  `(\x y. strcat x y)
     pop_env s =
       (match wordSem_state_stack s with (StackFrame m e0 e NONE ::
         xs) ->
            SOME (wordSem_state_locals_size_fupd (K m)
              (wordSem_state_stack_fupd (K xs)
              (wordSem_state_locals_fupd (K (sptree_union (fromAList e)
              (fromAList e0))) s))) | (StackFrame m e0 e (SOME
              (n,_41,_42)) :: xs) ->
            SOME (wordSem_state_handler_fupd (K n)
              (wordSem_state_locals_size_fupd (K m)
              (wordSem_state_stack_fupd (K xs)
              (wordSem_state_locals_fupd (K (sptree_union (fromAList
              e) (fromAList e0))) s)))) | _43 -> NONE)`;;

let jump_exc_def = cake_define
  `(\x y. strcat x y)
     jump_exc s =
       (if wordSem_state_handler s < LENGTH (wordSem_state_stack s)
         then
         match LASTN (wordSem_state_handler s + 1)
           (wordSem_state_stack s) with StackFrame m e0 e (SOME
           (n,l1,l2)) :: xs ->
             SOME (wordSem_state_locals_size_fupd (K m)
               (wordSem_state_stack_fupd (K xs)
               (wordSem_state_locals_fupd (K (sptree_union (fromAList
               e) (fromAList e0))) (wordSem_state_handler_fupd (K n)
               s))),l1,l2) | _44 -> NONE else NONE)`;;

let cut_names_def = cake_define
  `cut_names name_set env =
       (if domain name_set SUBSET domain env then SOME (inter env
         name_set) else NONE)`;;

let cut_envs_def = cake_define
  `cut_envs (name_sets:1 spt#1 spt) env =
     (match (cut_names (FST name_sets) env,cut_names (SND
       name_sets) env) with (SOME e1,SOME e2) -> SOME (e1,e2) | _45
       -> NONE)`;;

let cut_env_def = cake_define
  `wordSem_cut_env (name_sets:1 spt#1 spt) env =
     (match cut_envs name_sets env with SOME (e1,e2) -> SOME
       (sptree_union e2 e1) | _46 -> NONE)`;;
hol4_overload "cut_env" "wordSem_cut_env";;
(* -- *)

let cut_state_def = cake_define
  `(\x y. strcat x y)
     (cut_state names) s =
       (match wordSem_cut_env names (wordSem_state_locals s) with
         NONE -> NONE | SOME env -> SOME (wordSem_state_locals_fupd
         (K env) s))`;;

let cut_state_opt_def = cake_define
  `(\x y. strcat x y)
     (cut_state_opt names) s =
       (match names with NONE -> SOME s | SOME names -> cut_state
         names s)`;;

let find_code_def = cake_define_list
  [`wordSem_find_code (SOME p) args code ssize =
         (match sptree_lookup p code with NONE -> NONE | SOME
           (arity,exp) -> (if LENGTH args = arity then SOME
           (args,exp,sptree_lookup p ssize) else NONE))`;
   `wordSem_find_code NONE args code ssize =
         (if args = [] then NONE else
           match LAST args with Loc loc 0 ->
               (match sptree_lookup loc code with NONE -> NONE |
                 SOME (arity,exp) -> (if LENGTH args = arity + 1 then
                 SOME (FRONT args,exp,sptree_lookup loc ssize) else
                 NONE)) | other -> NONE)`];;
hol4_overload "find_code" "wordSem_find_code";;

let enc_stack_def = cake_define_list
  [`wordSem_enc_stack [] = []`;
   `wordSem_enc_stack (StackFrame n _47 l handler :: st) = MAP SND l
  ++ wordSem_enc_stack st`];;
hol4_overload "enc_stack" "wordSem_enc_stack";;

let dec_stack_def = cake_define
  `wordSem_dec_stack xs x2 =
        match (xs,x2) with
          ([],[]) -> SOME []
        | (xs,((StackFrame n l0 l handler :: st))) ->
        (if LENGTH xs < LENGTH l then NONE else
          match wordSem_dec_stack (DROP (LENGTH l) xs) st with NONE
            -> NONE | SOME s -> SOME (StackFrame n l0
              (ZIP (MAP FST l) (TAKE (LENGTH l) xs)) handler :: s))
        | (_48,_49) -> NONE`;;
hol4_overload "dec_stack" "wordSem_dec_stack";;

let gc_def = cake_define
  `(\x y. strcat x y)
     gc s =
       (let wl_list = wordSem_enc_stack (wordSem_state_stack s) in
         match wordSem_state_gc_fun s (wl_list,wordSem_state_memory
           s,wordSem_state_mdomain s,wordSem_state_store s) with NONE ->
           NONE | SOME (wl,m,st) ->
          (match wordSem_dec_stack wl (wordSem_state_stack s) with
            NONE -> NONE | SOME stack' ->
               SOME (wordSem_state_memory_fupd (K m)
                 (wordSem_state_store_fupd (K st)
                 (wordSem_state_stack_fupd (K stack') s)))))`;;

let has_space_def = cake_define
  `(\x y. strcat x y)
     (has_space wl) s =
       (match (wl,get_store NextFree s,get_store TriggerGC s) with
         (wordLang_Word w,SOME (wordLang_Word n),SOME (wordLang_Word
         l)) -> SOME (w2n w <= w2n (l - n)) | _50 -> NONE)`;;

(* to_ask: should we not update stack size here?  *)
let alloc_def = cake_define
  `(\x y. strcat x y)
     (alloc (w:'a word) names) s =
       (match cut_envs names (wordSem_state_locals s) with NONE ->
         (SOME (wordSem_Error:'a wordSem_result),flush_state T s) | SOME
         envs' ->
        (match gc (push_env envs' (NONE:(num#'a
          wordLang_prog#num#num) option) (set_store AllocSize
          (wordLang_Word w) s)) with NONE -> (SOME
          wordSem_Error,flush_state T s) | SOME s ->
          (match pop_env s with NONE -> (SOME
            wordSem_Error,flush_state T s) | SOME s ->
            (match get_store AllocSize s with NONE -> (SOME
              wordSem_Error,s) | SOME w ->
              (match has_space w s with NONE -> (SOME
                wordSem_Error,s) | SOME T ->
                           (NONE,s) | SOME F ->
                           (SOME
                             wordSem_NotEnoughSpace,flush_state T
                             s))))))`;;

let assign_def = cake_define
  `(\x y. strcat x y)
     (assign reg exp) s =
       (match wordSem_word_exp s exp with NONE -> NONE | SOME w ->
         SOME (set_var reg w s))`;;

let get_fp_var_def = cake_define
  `wordSem_get_fp_var v (s:('a,'c,'ffi)wordSem_state) = FLOOKUP
  (wordSem_state_fp_regs s) v`;;
hol4_overload "get_fp_var" "wordSem_get_fp_var";;

let set_fp_var_def = cake_define
  `wordSem_set_fp_var v x (s:('a,'c,'ffi)wordSem_state) =
     (wordSem_state_fp_regs_fupd (K (wordSem_state_fp_regs s |+
       (v,x))) s)`;;
hol4_overload "set_fp_var" "wordSem_set_fp_var";;

let inst_def = cake_define
  `(\x y. strcat x y)
     (inst i) s =
       (match i with Skip -> SOME s | Const reg w -> assign reg
         (Const w) s | Arith (asm_Binop bop r1 r2 ri) ->
           assign r1
             (wordLang_Op bop [Var r2; match ri with Reg r3 -> Var r3
               | Imm w -> Const w]) s | Arith (Shift sh r1 r2 ri) ->
           assign r1
             (Shift sh (Var r2) (match ri with Reg r3 -> Var r3 | Imm
               w -> Const w)) s | Arith (Div r1 r2 r3) ->
          (let vs = wordSem_get_vars [r3; r2] s in
          match vs with
          SOME [wordLang_Word q; wordLang_Word w2] ->
            (if ~(q = (n2w 0)) then
              SOME (set_var r1 (wordLang_Word (w2 / q)) s) else NONE)
                | _51 -> NONE) | Arith (asm_AddCarry r1 r2 r3 r4) ->
           (let vs = wordSem_get_vars [r2; r3; r4] s in
           match vs with
           SOME [wordLang_Word l; wordLang_Word r; wordLang_Word c]
             ->
             (let (res,co) = word_add_carry l r c in
               SOME (set_var r4 (wordLang_Word co) (set_var r1
                 (wordLang_Word res) s))) | _52 -> NONE) | Arith
                 (asm_AddOverflow r1 r2 r3 r4) ->
           (let vs = wordSem_get_vars [r2; r3] s in
           match vs with
           SOME [wordLang_Word w2; wordLang_Word w3] ->
             SOME (set_var r4 (wordLang_Word (if ~(w2i (w2 + w3) =
               w2i w2 + w2i w3) then (n2w 1) else (n2w 0)))
                    (set_var r1 (wordLang_Word (w2 + w3)) s)) | _53
                      -> NONE) | Arith (asm_SubOverflow r1 r2 r3 r4) ->
           (let vs = wordSem_get_vars [r2; r3] s in
           match vs with
           SOME [wordLang_Word w2; wordLang_Word w3] ->
             SOME (set_var r4 (wordLang_Word (if ~(w2i (w2 - w3) =
               w2i w2 - w2i w3) then (n2w 1) else (n2w 0)))
                    (set_var r1 (wordLang_Word (w2 - w3)) s)) | _54
                      -> NONE) | Arith (asm_LongMul r1 r2 r3 r4) ->
           (let vs = wordSem_get_vars [r3; r4] s in
           match vs with
           SOME [wordLang_Word w3; wordLang_Word w4] ->
            (let r = w2n w3 * w2n w4 in
              SOME (set_var r2 (wordLang_Word (n2w r)) (set_var r1
                (wordLang_Word (n2w (r DIV dimword (:'a)))) s))) | _55
                -> NONE) | Arith (asm_LongDiv r1 r2 r3 r4 r5) ->
          (let vs = wordSem_get_vars [r3; r4; r5] s in
          match vs with
          SOME [wordLang_Word w3; wordLang_Word w4; wordLang_Word w5]
            ->
            (let n = w2n w3 * dimword (:'a) + w2n w4 in
            let d = w2n w5 in
            let q = n DIV d in
            if (~(d = 0) /\ q < dimword (:'a)) then
              SOME (set_var r1 (wordLang_Word (n2w q)) (set_var r2
                (wordLang_Word (n2w (n MOD d))) s)) else NONE) | _56 ->
                NONE) | asm_Mem Load r (Addr a w) ->
          (match wordSem_word_exp s (wordLang_Op Add [Var a; Const
            w]) with SOME (wordLang_Word w) ->
              (match mem_load w s with NONE -> NONE | SOME w -> SOME
                (set_var r w s)) | _57 -> NONE) | asm_Mem asm_Load8 r
                (Addr a w) ->
          (match wordSem_word_exp s (wordLang_Op Add [Var a; Const
            w]) with SOME (wordLang_Word w) ->
              (match mem_load_byte_aux (wordSem_state_memory s)
                (wordSem_state_mdomain s) (wordSem_state_be s) w with
                NONE -> NONE | SOME w -> SOME (set_var r (wordLang_Word
                (w2w w)) s)) | _58 -> NONE) | asm_Mem asm_Load16 _59 _60
                -> NONE | asm_Mem asm_Load32 r (Addr a w) ->
          (match wordSem_word_exp s (wordLang_Op Add [Var a; Const
            w]) with SOME (wordLang_Word w) ->
              (match mem_load_32 (wordSem_state_memory s)
                (wordSem_state_mdomain s) (wordSem_state_be s) w with
                NONE -> NONE | SOME w -> SOME (set_var r (wordLang_Word
                (w2w w)) s)) | _61 -> NONE) | asm_Mem Store r (Addr a w)
                ->
          (match (wordSem_word_exp s (wordLang_Op Add [Var a; Const
            w]),get_var r s) with (SOME (wordLang_Word a),SOME w) ->
               (match mem_store a w s with SOME s1 -> SOME s1 | NONE
                 -> NONE) | _62 -> NONE) | asm_Mem asm_Store8 r (Addr a
                 w) ->
          (match (wordSem_word_exp s (wordLang_Op Add [Var a; Const
            w]),get_var r s) with (SOME (wordLang_Word a),SOME
            (wordLang_Word w)) ->
               (match mem_store_byte_aux (wordSem_state_memory s)
                 (wordSem_state_mdomain s) (wordSem_state_be s) a (w2w
                 w) with SOME new_m -> SOME (wordSem_state_memory_fupd
                 (K new_m) s) | NONE -> NONE) | _63 -> NONE) | asm_Mem
                 asm_Store16 _64 _65 -> NONE | asm_Mem asm_Store32 r
                 (Addr a w) ->
          (match (wordSem_word_exp s (wordLang_Op Add [Var a; Const
            w]),get_var r s) with (SOME (wordLang_Word a),SOME
            (wordLang_Word w)) ->
               (match mem_store_32 (wordSem_state_memory s)
                 (wordSem_state_mdomain s) (wordSem_state_be s) a (w2w
                 w) with SOME new_m -> SOME (wordSem_state_memory_fupd
                 (K new_m) s) | NONE -> NONE) | _66 -> NONE) | asm_FP
                 (FPLess r d1 d2) ->
         (match (wordSem_get_fp_var d1 s,wordSem_get_fp_var d2 s)
           with (SOME f1,SOME f2) ->
           SOME (set_var r
             (wordLang_Word (if fp64_lessThan f1 f2 then (n2w 1) else
               (n2w 0))) s) | _67 -> NONE) | asm_FP (FPLessEqual r d1
               d2) ->
         (match (wordSem_get_fp_var d1 s,wordSem_get_fp_var d2 s)
           with (SOME f1,SOME f2) ->
           SOME (set_var r
             (wordLang_Word (if fp64_lessEqual f1 f2 then (n2w 1)
               else (n2w 0))) s) | _68 -> NONE) | asm_FP (FPEqual r d1
               d2) ->
         (match (wordSem_get_fp_var d1 s,wordSem_get_fp_var d2 s)
           with (SOME f1,SOME f2) ->
           SOME (set_var r
             (wordLang_Word (if fp64_equal f1 f2 then (n2w 1) else
               (n2w 0))) s) | _69 -> NONE) | asm_FP (FPMov d1 d2) ->
         (match wordSem_get_fp_var d2 s with SOME f ->
           SOME (wordSem_set_fp_var d1 f s) | _70 -> NONE) | asm_FP
             (FPAbs d1 d2) ->
         (match wordSem_get_fp_var d2 s with SOME f ->
           SOME (wordSem_set_fp_var d1 (fp64_abs f) s) | _71 -> NONE)
             | asm_FP (FPNeg d1 d2) ->
         (match wordSem_get_fp_var d2 s with SOME f ->
           SOME (wordSem_set_fp_var d1 (fp64_negate f) s) | _72 ->
             NONE) | asm_FP (FPSqrt d1 d2) ->
         (match wordSem_get_fp_var d2 s with SOME f ->
           SOME (wordSem_set_fp_var d1 (fp64_sqrt roundTiesToEven f)
             s) | _73 -> NONE) | asm_FP (FPAdd d1 d2 d3) ->
         (match (wordSem_get_fp_var d2 s,wordSem_get_fp_var d3 s)
           with (SOME f1,SOME f2) ->
           SOME (wordSem_set_fp_var d1 (fp64_add roundTiesToEven f1
             f2) s) | _74 -> NONE) | asm_FP (FPSub d1 d2 d3) ->
         (match (wordSem_get_fp_var d2 s,wordSem_get_fp_var d3 s)
           with (SOME f1,SOME f2) ->
           SOME (wordSem_set_fp_var d1 (fp64_sub roundTiesToEven f1
             f2) s) | _75 -> NONE) | asm_FP (FPMul d1 d2 d3) ->
         (match (wordSem_get_fp_var d2 s,wordSem_get_fp_var d3 s)
           with (SOME f1,SOME f2) ->
           SOME (wordSem_set_fp_var d1 (fp64_mul roundTiesToEven f1
             f2) s) | _76 -> NONE) | asm_FP (FPDiv d1 d2 d3) ->
         (match (wordSem_get_fp_var d2 s,wordSem_get_fp_var d3 s)
           with (SOME f1,SOME f2) ->
           SOME (wordSem_set_fp_var d1 (fp64_div roundTiesToEven f1
             f2) s) | _77 -> NONE) | asm_FP (FPFma d1 d2 d3) ->
         (match (wordSem_get_fp_var d1 s,wordSem_get_fp_var d2
           s,wordSem_get_fp_var d3 s) with (SOME f1,SOME f2,SOME f3) ->
           SOME (wordSem_set_fp_var d1 (fpfma f1 f2 f3) s) | _78 ->
             NONE) | asm_FP (FPMovToReg r1 r2 d) ->
         (match wordSem_get_fp_var d s with SOME v ->
           (if dimindex (:'a) = 64 then
             SOME (set_var r1 (wordLang_Word (w2w v)) s) else
             SOME (set_var r2 (wordLang_Word ((63 >< 32) v)) (set_var
               r1 (wordLang_Word ((31 >< 0) v)) s))) | _79 -> NONE) |
               asm_FP (FPMovFromReg d r1 r2) ->
         (if dimindex (:'a) = 64 then
           match get_var r1 s with
             SOME (wordLang_Word w1) -> SOME (wordSem_set_fp_var d
               (w2w w1) s) | _80 -> NONE else
           match (get_var r1 s,get_var r2 s) with
             (SOME (wordLang_Word w1),SOME (wordLang_Word w2)) ->
               SOME (wordSem_set_fp_var d (w2 @@ w1) s) | _81 -> NONE) |
               asm_FP (FPToInt d1 d2) ->
         (match wordSem_get_fp_var d2 s with
           NONE -> NONE | SOME f ->
         (match fp64_to_int roundTiesToEven f with
           NONE -> NONE | SOME i ->
           (let w = i2w i:word32 in
           if w2i w = i then
             (if dimindex (:'a) = 64 then
                SOME (wordSem_set_fp_var d1 (w2w w) s) else
              match wordSem_get_fp_var (d1 DIV 2) s with
                NONE -> NONE | SOME f ->
                (let (h,l) = if ODD d1 then (63,32) else (31,0) in
                     SOME (wordSem_set_fp_var (d1 DIV 2)
                       (bit_field_insert h l w f) s))) else
             NONE))) | asm_FP (FPFromInt d1 d2) ->
         (if dimindex (:'a) = 64 then
           match wordSem_get_fp_var d2 s with SOME f ->
             (let i = w2i ((31 >< 0) f:word32) in
               SOME (wordSem_set_fp_var d1 (int_to_fp64
                 roundTiesToEven i) s)) | NONE -> NONE else
           match wordSem_get_fp_var (d2 DIV 2) s with SOME v ->
             (let i = w2i (if ODD d2 then (63 >< 32) v else (31 >< 0)
               v:'a word) in
               SOME (wordSem_set_fp_var d1 (int_to_fp64
                 roundTiesToEven i) s)) | NONE -> NONE | _82 ->
                 NONE))`;;

let get_var_imm_def = cake_define_list
  [`(\x y. strcat x y) (wordSem_get_var_imm ((Reg n):'a asm_reg_imm))
  s = get_var n s`;
   `wordSem_get_var_imm (Imm w) s = SOME (wordLang_Word w)`];;
hol4_overload "get_var_imm" "wordSem_get_var_imm";;

let add_ret_loc_def = cake_define_list
  [`add_ret_loc NONE xs = xs`;
   `add_ret_loc (SOME (n,names,ret_handler,l1,l2)) xs = (Loc l1 l2)
  :: xs`];;

(*Avoid case split*)
let bad_dest_args_def = cake_define
  `bad_dest_args dest args <=> dest = NONE /\ args = []`;;

let MustTerminate_limit_def = cake_define
  `MustTerminate_limit (:'a) =
     2 * dimword (:'a) +
     dimword (:'a) * dimword (:'a) +
     dimword (:'a) EXP dimword (:'a) +
     dimword (:'a) EXP dimword (:'a) EXP dimword (:'a)`;;

let const_addresses_def = cake_define_list
  [`const_addresses a [] d = T`;
   `const_addresses a (x :: xs) d =
      (a IN d /\ const_addresses (a + bytes_in_word) xs d)`];;

let const_writes_def = cake_define_list
  [`const_writes a off [] m = m`;
   `const_writes (a:'a word) off ((b,(x:'a word)) :: xs) m =
      const_writes (a + bytes_in_word) off xs
        ((a =+ wordLang_Word (if b then x + off else x)) m)`];;

let STOP_def = cake_define
  `wordSem_STOP x = x`;;
hol4_overload "STOP" "wordSem_STOP";;

let bad_fun_return_def = cake_define
  `wordSem_bad_fun_return x1 =
      match x1 with
        NONE -> T
      | (SOME (Break _83)) -> T
      | (SOME (Continue _84)) -> T
      | _85 -> F`;;
hol4_overload "bad_fun_return" "wordSem_bad_fun_return";;

let cont_loop_def = cake_define
  `wordSem_cont_loop x1 =
      match x1 with
        NONE -> T
      | (SOME (Continue n)) -> (n = 0)
      | _86 -> F`;;
hol4_overload "cont_loop" "wordSem_cont_loop";;

let exit_loop_def = cake_define
  `wordSem_exit_loop res =
      match res with
        SOME (Break n) -> SOME (Break (n - 1))
      | (SOME (Continue n)) -> SOME (Continue (n - 1))
      | res -> res`;;
hol4_overload "exit_loop" "wordSem_exit_loop";;

let evaluate_def = cake_define_list
  [`wordSem_evaluate ((Skip:'a wordLang_prog),s) = (NONE,s)`;
   `wordSem_evaluate (wordLang_Alloc n names,s) =
         (match get_var n s with SOME (wordLang_Word w) -> alloc
           w names s | _90 -> (SOME wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_StoreConsts t1 t2 addr' offset words,s) =
         (match (get_var addr' s,get_var offset s) with (SOME
           (wordLang_Word a),SOME (wordLang_Word off)) ->
            (if ~const_addresses a words (wordSem_state_mdomain s)
              then
               (SOME wordSem_Error,s) else
               let s = wordSem_state_memory_fupd (K (const_writes a
                 off words (wordSem_state_memory s))) s in
               let s = set_var offset (wordLang_Word off) (unset_var
                 t1 (unset_var t2 s)) in
                 (NONE,set_var addr' (wordLang_Word (a +
                   bytes_in_word * n2w (LENGTH words))) s)) | _91 ->
                   (SOME wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_Move pri moves,s) =
         (if ALL_DISTINCT (MAP FST moves) then
           match wordSem_get_vars (MAP SND moves) s with NONE ->
             (SOME wordSem_Error,s) | SOME vs -> (NONE,set_vars (MAP
             FST moves) vs s) else (SOME wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_Inst i,s) =
         (match inst i s with SOME s1 -> (NONE,s1) | NONE ->
           (SOME wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_Assign v exp,s) =
         (match wordSem_word_exp s exp with NONE -> (SOME
           wordSem_Error,s) | SOME w -> (NONE,set_var v w s))`;
   `wordSem_evaluate (wordLang_Get v name,s) =
         (match get_store name s with NONE -> (SOME
           wordSem_Error,s) | SOME x -> (NONE,set_var v x s))`;
   `wordSem_evaluate (wordLang_Set v exp,s) =
         (if v = Handler \/ v = BitmapBase then (SOME
           wordSem_Error,s) else
         match wordSem_word_exp s exp with NONE -> (SOME
           wordSem_Error,s) | SOME w -> (NONE,set_store v w s))`;
   `wordSem_evaluate (wordLang_OpCurrHeap b dst src,s) =
         (match wordSem_word_exp s (wordLang_Op b [Var src;
           wordLang_Lookup CurrHeap]) with NONE -> (SOME
           wordSem_Error,s) | SOME w -> (NONE,set_var dst w s))`;
   `wordSem_evaluate (wordLang_Store exp v,s) =
         (match (wordSem_word_exp s exp,get_var v s) with (SOME
           (wordLang_Word a),SOME w) ->
             (match mem_store a w s with SOME s1 -> (NONE,s1) |
               NONE -> (SOME wordSem_Error,s)) | _92 -> (SOME
               wordSem_Error,s))`;
   `wordSem_evaluate (Tick,s) =
         (if wordSem_state_clock s = 0 then (SOME
           wordSem_TimeOut,flush_state T s) else (NONE,dec_clock s))`;
   `wordSem_evaluate (wordLang_MustTerminate p,s) =
         (if wordSem_state_termdep s = 0 then (SOME wordSem_Error,s)
           else
           let (res,s1) = wordSem_evaluate
             (p,wordSem_state_termdep_fupd (K (wordSem_state_termdep s -
             1)) (wordSem_state_clock_fupd (K (MustTerminate_limit
             (:'a))) s)) in
             if res = SOME wordSem_TimeOut then (SOME
               wordSem_Error,s) else (res,wordSem_state_termdep_fupd
               (K (wordSem_state_termdep s))
               (wordSem_state_clock_fupd (K (wordSem_state_clock s))
               s1)))`;
   `wordSem_evaluate (wordLang_Seq c1 c2,s) =
         (let (res,s1) = wordSem_fix_clock s (wordSem_evaluate
           (c1,s)) in
           if res = NONE then wordSem_evaluate (c2,s1) else
             (res,s1))`;
   `wordSem_evaluate (wordLang_Return n ms,s) =
         (match (get_var n s,wordSem_get_vars ms s) with (SOME
           (Loc l1 l2),SOME ys) -> (SOME (wordSem_Result (Loc l1 l2)
           ys),flush_state F s) | _93 -> (SOME wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_Raise n,s) =
         (match get_var n s with NONE -> (SOME wordSem_Error,s) |
           SOME w ->
           ((match jump_exc s with NONE -> (SOME wordSem_Error,s)
             | SOME (s,l1,l2) -> (SOME (wordSem_Exception (Loc l1 l2)
             w))),s))`;
   `wordSem_evaluate (wordLang_Break k,s) = (SOME (Break k),s)`;
   `wordSem_evaluate (wordLang_Continue k,s) = (SOME (Continue k),s)`;
   `wordSem_evaluate (wordLang_If cmp r1 ri c1 c2,s) =
        (match (get_var r1 s,wordSem_get_var_imm ri s) with (SOME
          x,SOME y) ->
         (match word_cmp cmp x y with SOME T -> wordSem_evaluate
           (c1,s) | SOME F -> wordSem_evaluate (c2,s) | NONE -> (SOME
           wordSem_Error,s)) | _94 -> (SOME wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_Loop names c exit_names,s) =
         (match cut_state (names,LN) s with NONE -> (SOME
           wordSem_Error,s) | SOME s ->
             (let (res,s1) = wordSem_fix_clock s (wordSem_evaluate
               (c,s)) in
               if wordSem_cont_loop res then
                 (if wordSem_state_clock s1 = 0 then (SOME
                   wordSem_TimeOut,flush_state T s1) else
                    wordSem_evaluate (wordSem_STOP (Loop names c
                      exit_names),dec_clock s1)) else if res = SOME
                      (Break 0) then
                 match cut_state (exit_names,LN) s1 with NONE ->
                   (SOME wordSem_Error,s1) | SOME s2 -> (NONE,s2)
                   else (wordSem_exit_loop res,s1)))`;
   `wordSem_evaluate (wordLang_LocValue r l1,s) =
         (if l1 IN domain (wordSem_state_code s) then
           (NONE,set_var r (Loc l1 0) s) else (SOME
             wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_Install ptr len dptr dlen names,s) =
        (match wordSem_cut_env names (wordSem_state_locals s) with
          NONE -> (SOME wordSem_Error,s) | SOME env ->
        (match (get_var ptr s,get_var len s,get_var dptr s,get_var
          dlen s) with (SOME (wordLang_Word w1),SOME (wordLang_Word
          w2),SOME (wordLang_Word w3),SOME (wordLang_Word w4)) ->
           (let (cfg,progs) = wordSem_state_compile_oracle s 0 in
           (match (
                 buffer_flush (wordSem_state_code_buffer s) w1
                   w2,buffer_flush (wordSem_state_data_buffer s) w3 w4)
                   with (
             SOME (bytes,cb),SOME (data,db)) ->
            (let new_oracle = misc_shift_seq 1
              (wordSem_state_compile_oracle s) in
            (match (wordSem_state_compile s cfg progs,progs) with
              (SOME (bytes',data',cfg'),(k,prog) :: _95) ->
                (if bytes = bytes' /\ data = data' /\ FST
                  (new_oracle 0) = cfg' then
                let s' = wordSem_state_stack_size_fupd (K LN)
                  (wordSem_state_stack_max_fupd (K NONE)
                  (wordSem_state_compile_oracle_fupd (K new_oracle)
                  (wordSem_state_fp_regs_fupd (K FEMPTY)
                  (wordSem_state_locals_fupd (K (sptree_insert ptr (Loc
                  k 0) env)) (wordSem_state_code_fupd (K (sptree_union
                  (wordSem_state_code s) (fromAList progs)))
                  (wordSem_state_data_buffer_fupd (K db)
                  (wordSem_state_code_buffer_fupd (K cb)
                    s))))))) in
                  (NONE,s') else (SOME wordSem_Error,s)) | _96 ->
                    (SOME wordSem_Error,s))) | _97 -> (SOME
                    wordSem_Error,s))) | _98 -> (SOME
                    wordSem_Error,s)))`;
   `wordSem_evaluate (wordLang_CodeBufferWrite r1 r2,s) =
        (match (get_var r1 s,get_var r2 s) with (SOME (wordLang_Word
          w1),SOME (wordLang_Word w2)) ->
              (match buffer_write (wordSem_state_code_buffer s) w1
                (w2w w2) with SOME new_cb ->
                (NONE,wordSem_state_code_buffer_fupd (K new_cb)
                  s) | _99 -> (SOME wordSem_Error,s)) | _100 -> (SOME
                  wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_DataBufferWrite r1 r2,s) =
        (match (get_var r1 s,get_var r2 s) with (SOME (wordLang_Word
          w1),SOME (wordLang_Word w2)) ->
              (match buffer_write (wordSem_state_data_buffer s) w1
                w2 with SOME new_db ->
                (NONE,wordSem_state_data_buffer_fupd (K new_db)
                  s) | _101 -> (SOME wordSem_Error,s)) | _102 ->
                  (SOME wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_FFI ffi_index ptr1 len1 ptr2 len2
  names,s) =
        (match (get_var len1 s,get_var ptr1 s,get_var len2 s,get_var
          ptr2 s) with (SOME (wordLang_Word w),SOME (wordLang_Word
          w2),SOME (wordLang_Word w3),SOME (wordLang_Word w4)) ->
          (match wordSem_cut_env names (wordSem_state_locals s) with
            NONE -> (SOME wordSem_Error,s) | SOME env ->
            (match (read_bytearray w2 (w2n w) (mem_load_byte_aux
              (wordSem_state_memory s) (wordSem_state_mdomain s)
              (wordSem_state_be s)),
                   read_bytearray w4 (w2n w3) (mem_load_byte_aux
                     (wordSem_state_memory s) (wordSem_state_mdomain s)
                     (wordSem_state_be s))) with (SOME bytes,SOME
                     bytes2) ->
                 (match call_FFI (wordSem_state_ffi s) (ExtCall
                   ffi_index) bytes bytes2 with FFI_final outcome ->
                   (SOME (wordSem_FinalFFI outcome),flush_state T s) |
                   FFI_return new_ffi new_bytes ->
                    (let new_m = write_bytearray w4 new_bytes
                      (wordSem_state_memory s) (wordSem_state_mdomain s)
                      (wordSem_state_be s) in
                      (NONE,wordSem_state_ffi_fupd (K new_ffi)
                        (wordSem_state_fp_regs_fupd (K FEMPTY)
                        (wordSem_state_locals_fupd (K env)
                        (wordSem_state_memory_fupd (K new_m) s))))))
                        | _103 -> (SOME wordSem_Error,s))) | res ->
                        (SOME wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_ShareInst op v exp,s) =
        (match wordSem_word_exp s exp with SOME (wordLang_Word
          ad) -> share_inst op v ad s | _104 -> (SOME
          wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_Call ret dest args handler,s) =
       (match wordSem_get_vars args s with NONE -> (SOME
         wordSem_Error,s) | SOME xs ->
           (if bad_dest_args dest args then (SOME wordSem_Error,s)
             else
             match wordSem_find_code dest (add_ret_loc ret xs)
               (wordSem_state_code s) (wordSem_state_stack_size s) with
               NONE -> (SOME wordSem_Error,s) | SOME (args1,prog,ss) ->
                 (match ret with NONE ->
                     (if handler = NONE then
                       if wordSem_state_clock s = 0 then (SOME
                         wordSem_TimeOut,flush_state T s) else (match
                         wordSem_evaluate (prog,call_env args1 ss
                         (dec_clock s)) with (res,s) -> (if
                         wordSem_bad_fun_return res then (SOME
                         wordSem_Error,s) else (res,s))) else (SOME
                         wordSem_Error,s)) | SOME
                         (n,names,ret_handler,l1,l2) ->
                     (if domain (FST names) = {} \/ ~ALL_DISTINCT n
                       then (SOME wordSem_Error,s) else
                       (match cut_envs names (wordSem_state_locals
                         s) with NONE -> (SOME wordSem_Error,s) | SOME
                         envs' ->
                            (if wordSem_state_clock s = 0 then
                              (SOME wordSem_TimeOut,
                              flush_state T
                              (wordSem_state_stack_max_fupd (K
                                (wordSem_state_stack_max (call_env args1
                                ss
                              (push_env envs' handler s))))
                                (wordSem_state_stack_fupd (K []) s)))
                                else
                              (match wordSem_fix_clock (call_env
                                args1 ss (push_env envs' handler
                                (dec_clock s)))
                              (wordSem_evaluate (prog,call_env args1
                                ss
                              (push_env envs' handler (dec_clock
                                s)))) with (SOME (wordSem_Result x
                                ys),s2) ->
                              (if ~(x = Loc l1 l2) \/ ~(LENGTH ys =
                                LENGTH n) then (SOME wordSem_Error,s2)
                                else
                              (match pop_env s2 with NONE -> (SOME
                                wordSem_Error,s2) | SOME s1 ->
                              (if domain (wordSem_state_locals s1) =
                                domain (FST envs') UNION domain (SND
                                envs') then wordSem_evaluate
                                (ret_handler,set_vars n ys s1) else
                                (SOME wordSem_Error,s1)))) | (SOME
                                (wordSem_Exception x y),s2) ->
                              (match handler with NONE -> (SOME
                                (wordSem_Exception x y),s2) | SOME
                                (n,h,l1,l2) ->
                              (if ~(x = Loc l1 l2) then (SOME
                                wordSem_Error,s2) else
                              (if domain (wordSem_state_locals
                                s2) = domain (FST envs') UNION domain
                                (SND envs') then wordSem_evaluate
                                (h,set_var n y s2) else (SOME
                                wordSem_Error,s2)))) | (NONE,s) ->
                                (SOME wordSem_Error,s) | (SOME (Break
                                _105),s) -> (SOME wordSem_Error,s) |
                                (SOME (Continue _106),s) -> (SOME
                                wordSem_Error,s) | res -> res)))))))`];;
hol4_overload "evaluate" "wordSem_evaluate";;

(* We prove that the clock never increases and that termdep is constant.
   *)

(* We store the theorems without fix_clock *)

(* observational semantics *)

let semantics_def = cake_define
  `(\x y. strcat x y)
     semantics (s start) =
     (let prog = Call NONE (SOME start) [0] NONE in
     if ?k. match FST (wordSem_evaluate
       (prog,wordSem_state_clock_fupd (K k) s)) with SOME
       (wordSem_Exception _107 _108) -> T | SOME (wordSem_Result ret
       _109) -> ~(ret = Loc 1 0) | SOME wordSem_Error -> T | NONE -> T |
       _110 -> F then ffi_Fail else
       match some (\res.
         ?k t r outcome.
           wordSem_evaluate (prog,wordSem_state_clock_fupd (K k) s) =
             (r,t) /\
           (match r with (SOME (wordSem_FinalFFI e)) -> outcome =
             ffi_FFI_outcome e | (SOME (wordSem_Result _111 _112)) ->
             outcome = ffi_Success | (SOME wordSem_NotEnoughSpace) ->
             outcome = ffi_Resource_limit_hit | _113 -> F) /\
           res = ffi_Terminate outcome (ffi_state_io_events
             (wordSem_state_ffi t))) with SOME res -> res | NONE ->
         ffi_Diverge
            (build_lprefix_lub
              (IMAGE (\k. fromList (ffi_state_io_events
                (wordSem_state_ffi
                 (SND (wordSem_evaluate
                   (prog,wordSem_state_clock_fupd (K k) s))))))
                   UNIV)))`;;

let word_lang_safe_for_space_def = cake_define
  `word_lang_safe_for_space (s:('a,'c,'ffi)wordSem_state) start' =
     (let prog = Call NONE (SOME start') [0] NONE in
       (!k res t. wordSem_evaluate (prog,wordSem_state_clock_fupd (K
         k) s) = (res,t) ==>
         (?max'. wordSem_state_stack_max t = SOME max' /\ max' <=
           wordSem_state_stack_limit t)))`;;

(* clean up *)

(* HOL4 ML code, not ported:
val _ = map delete_binding ["evaluate_AUX_def",
  "evaluate_primitive_def"];
*)
