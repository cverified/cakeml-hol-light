(* ======================================================== *)
(*  wordSem: ported from HOL4's
    compiler/backend/semantics/wordSemScript.sml
    A definition theory, with 77 definitions, 4 datatypes and 16
    theorems.  Needed by 28 files of the port.  *)
(* ======================================================== *)

(*
  The formal semantics of wordLang
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/backend_common.ml";;
(* for word_add_carry *)
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/alignment.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/byte.ml";;
needs "lib/errorMonad.ml";;
needs "lib/integer_word.ml";;
needs "lib/lprefix_lub.ml";;
(* for build_lprefix_lub *)
needs "lib/machine_ieee.ml";;
(* for FP *)
needs "lib/peg.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ffi/ffi.ml";;
(* for call_FFI *)
needs "semantics/fpSem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "wordSem"
  ["asm"; "backend_common"; "ffi"; "fpSem"; "misc"; "mllist";
   "wordLang"];;
(* HOL4 ancestors outside the port: finite_map *)

let buffer_FIELDS = define_record "buffer"
  ["position","'a word";
   "buffer","('b word) list";
   "space_left","num"];;

let buffer_flush_def = new_definition
  `buffer_flush cb (w1:'a word) w2 =
     (if buffer_position cb = w1 /\ buffer_position cb + (n2w
       (dimindex (:'b) DIV 8)) * n2w (LENGTH (buffer_buffer cb)) = w2
       then
       SOME ((buffer_buffer cb:('b word) list),buffer_buffer_fupd (K
         []) (buffer_position_fupd (K w2)
             cb)) else NONE)`;;

let buffer_write_def = new_definition
  `buffer_write cb (w:'a word) (b:'b word) =
     (if buffer_position cb + (n2w (dimindex (:'b) DIV 8)) * n2w
       (LENGTH (buffer_buffer cb)) = w /\ 0 < buffer_space_left cb then
       SOME (buffer_space_left_fupd (K (buffer_space_left cb - 1))
         (buffer_buffer_fupd (K (APPEND (buffer_buffer cb) [b])) cb))
         else NONE)`;;

let is_fwd_ptr_def = new_definition
  `is_fwd_ptr x1 =
        match x1 with
          wordLang_Word w -> ((w && (n2w 3)) = (n2w 0))
        | _1 -> F`;;

let theWord_def = define_general
  [`theWord (wordLang_Word w) = w`];;

let isWord_def = new_definition
  `isWord x1 =
        match x1 with
          wordLang_Word w -> T
        | _2 -> F`;;

let isWord_exists = prove
 (`isWord x <=> (?w. x = wordLang_Word w)`,
  (CASES_ON_TAC `x:(A)word_loc` THEN
   REWRITE_TAC[isWord_def; injectivity "word_loc"; distinctness
     "word_loc"] THEN
   MESON_TAC[]));;

let wordSem_word_cmp_def = new_definition
  `wordSem_word_cmp x1 x2 x3 =
        match (x1,x2,x3) with
          ((asm_Equal:cmp),wordLang_Word w1,wordLang_Word w2) -> SOME
            (w1 = w2)
        | (asm_Less,(wordLang_Word w1),(wordLang_Word w2)) -> SOME
          (w1 < w2)
        | (asm_Lower,(wordLang_Word w1),(wordLang_Word w2)) -> SOME
          (w1 <+ w2)
        | (asm_Test,(wordLang_Word w1),(wordLang_Word w2)) -> SOME
          ((w1 && w2) = (n2w 0))
        | (asm_Test,(wordLang_Loc _3 n),(wordLang_Word w2)) -> (if
          ~(n = 0) then NONE else if w2 = (n2w 1) then SOME T else NONE)
        | (asm_NotEqual,(wordLang_Word w1),(wordLang_Word w2)) ->
          SOME (~(w1 = w2))
        | (asm_NotLess,(wordLang_Word w1),(wordLang_Word w2)) -> SOME
          (~(w1 < w2))
        | (asm_NotLower,(wordLang_Word w1),(wordLang_Word w2)) ->
          SOME (~(w1 <+ w2))
        | (asm_NotTest,(wordLang_Word w1),(wordLang_Word w2)) -> SOME
          (~((w1 && w2) = (n2w 0)))
        | (asm_NotTest,(wordLang_Loc _4 n),(wordLang_Word w2)) -> (if
          ~(n = 0) then NONE else if w2 = (n2w 1) then SOME F else NONE)
        | (_5,_6,_7) -> NONE`;;

let mem_load_32_def = new_definition
  `mem_load_32 m dm be' (w:'a word) =
   (if alignment_aligned 2 w then match m (byte_align w) with
     wordLang_Loc _8 _9 -> NONE | wordLang_Word v ->
            (if byte_align w IN dm then SOME (word_of_bytes be' ((n2w
              0):word32)
              [get_byte w v be'; get_byte (w + (n2w 1)) v be';
               get_byte (w + (n2w 2)) v be'; get_byte (w + (n2w
                 3)) v be']) else NONE) else NONE)`;;

let mem_store_32_def = new_definition
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

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let mem_load_32_alt = prove
 (cake_as_vars (fun () ->
    `mem_load_32 m dm be (w:'a word) =
     (if alignment_aligned 2 w then match m (byte_align w) with
       wordLang_Loc _13 _14 -> NONE | wordLang_Word v ->
              (if byte_align w IN dm then
                let b0 = get_byte w v be in
                let b1 = get_byte (w + (n2w 1)) v be in
                let b2 = get_byte (w + (n2w 2)) v be in
                let b3 = get_byte (w + (n2w 3)) v be in
                  let v' =
                      (if be then
                         (w2w b0) << 24 || (w2w b1) << 16 || (w2w
                           b2) << 8 || (w2w b3) else
                         (w2w b0) || (w2w b1) << 8 || (w2w b2) <<
                           16 || (w2w b3) << 24) in SOME (v':word32)
                           else NONE) else NONE)`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let mem_store_32_alt = prove
 (cake_as_vars (fun () ->
    `mem_store_32 m dm be (w:'a word) (hw:word32) =
     (if alignment_aligned 2 w then match m (byte_align w) with
       wordLang_Word v ->
              (if byte_align w IN dm then
                if be then
                  let v0 = set_byte w (w2w (hw >>> 24)) v be in
                  let v1 = set_byte (w + (n2w 1)) (w2w (hw >>> 16))
                    v0 be in
                  let v2 = set_byte (w + (n2w 2)) (w2w (hw >>> 8))
                    v1 be in
                  let v3 = set_byte (w + (n2w 3)) (w2w hw) v2 be in
                    SOME ((byte_align w =+ wordLang_Word v3) m)
                      else
                  let v0 = set_byte w (w2w hw) v be in
                  let v1 = set_byte (w + (n2w 1)) (w2w (hw >>> 8))
                    v0 be in
                  let v2 = set_byte (w + (n2w 2)) (w2w (hw >>> 16))
                    v1 be in
                  let v3 = set_byte (w + (n2w 3)) (w2w (hw >>> 24))
                    v2 be in
                    SOME ((byte_align w =+ wordLang_Word v3) m)
                      else NONE) | _16 -> NONE else NONE)`),
  CHEAT_TAC);;

let mem_load_byte_aux_def = new_definition
  `mem_load_byte_aux m dm be' w =
     (match m (byte_align w) with wordLang_Loc _17 _18 -> NONE |
       wordLang_Word v ->
         (if byte_align w IN dm then SOME (get_byte w v be') else
           NONE))`;;

let mem_store_byte_aux_def = new_definition
  `mem_store_byte_aux m dm be' w b =
     (match m (byte_align w) with wordLang_Word v ->
         (if byte_align w IN dm then SOME ((byte_align w =+
           wordLang_Word (set_byte w b v be')) m) else NONE) | _19 ->
           NONE)`;;

let write_bytearray_def,write_bytearray_ind = define_guess
  [`write_bytearray a [] m dm be' = m`;
   `write_bytearray a (CONS b bs) m dm be' =
         (match mem_store_byte_aux (write_bytearray (a + (n2w
             1)) bs m dm be') dm be' a b with SOME m -> m | NONE ->
             m)`];;

let stack_frame_INDUCT,stack_frame_RECURSION = define_datatype
  "stack_frame =
     StackFrame (num option) ((num#'a word_loc) list) ((num#'a word_loc)
       list) ((num#num#num) option)
     // non-GCed cutset
     // GCed cutset
  ";;

(* HOL4 wordSemScript.sml:193-197: the type abbreviation gc_fun_type,
   which the port expands *)

let gc_bij_ok_def = new_definition
  `gc_bij_ok (seq':num->num->num) = (!n. BIJ (seq' n) UNIV UNIV)`;;

let wordSem_state_FIELDS = define_record "wordSem_state"
  ["locals","('a word_loc) spt";
   "locals_size","num option";
   (* size of locals when pushed to stack, NONE if unbounded *)
   "fp_regs","(num,word64)fmap";
   (* FP regs are treated "globally" *)
   "store","(store_name,'a word_loc)fmap";
   "stack","('a stack_frame) list";
   "stack_limit","num";
   (* max stack size *)
   "stack_max","num option";
   (* largest stack seen so far, NONE if unbounded *)
   "stack_size","num spt";
   (* stack frame size of function, unbounded if unmapped *)
   "memory","'a word->'a word_loc";
   "mdomain","'a word->bool";
   "sh_mdomain","'a word->bool";
   "permute","num->num->num";
   (* sequence of bijective mappings *)
   "compile","'c->(num#num#'a wordLang_prog) list->(word8 list#('a \
   word) list#'c) option";
   "compile_oracle","num->'c#(num#num#'a wordLang_prog) list";
   "code_buffer","('a,8)buffer";
   "data_buffer","('a,'a)buffer";
   "gc_fun","('a word_loc) list#('a word->'a word_loc)#('a \
   word->bool)#(store_name,'a word_loc)fmap->(('a word_loc) list#('a \
   word->'a word_loc)#(store_name,'a word_loc)fmap) option";
   "handler","num";
   (*position of current handle frame on stack*)
   "clock","num";
   "termdep","num";
   (* count of how many MustTerminates we can still enter *)
   "code","(num#'a wordLang_prog) spt";
   "be","bool";
   (*is big-endian*)
   "ffi","'ffi ffi_state"];;

let stack_size_frame_def = new_definition
  `stack_size_frame x1 =
      match x1 with
        StackFrame n _20 _21 NONE -> n
      | (StackFrame n _22 _23 (SOME _24)) -> OPTION_MAP ((+) 3) n`;;

let stack_size_def = new_definition
  `stack_size = FOLDR (OPTION_MAP2 (+) o stack_size_frame) (SOME 1)`;;

(* HOL4 wordSemScript.sml:239: ML code, not ported *)

let wordSem_result_INDUCT,wordSem_result_RECURSION = define_datatype
  "wordSem_result =
     wordSem_Result ('w word_loc) (('w word_loc) list)
   | wordSem_Exception ('w word_loc) ('w word_loc)
   | wordSem_Break num
   | wordSem_Continue num
   | wordSem_TimeOut
   | wordSem_NotEnoughSpace
   | wordSem_FinalFFI final_event
   | wordSem_Error";;

let isResult_def = new_definition
  `wordSem_isResult x1 =
        match x1 with
          wordSem_Result a b -> T
        | _25 -> F`;;

let isException_def = new_definition
  `wordSem_isException x1 =
        match x1 with
          wordSem_Exception a b -> T
        | _26 -> F`;;

(* HOL4 wordSemScript.sml:260: the ML values that the definitions
   below antiquote *)

let wordSem_dec_clock_def = new_definition
  `wordSem_dec_clock (s:('a,'c,'ffi)wordSem_state) =
  wordSem_state_clock_fupd (K (wordSem_state_clock s - 1)) s`;;

let wordSem_fix_clock_def = new_definition
  `wordSem_fix_clock old_s (res,new_s) =
     (res,wordSem_state_termdep_fupd (K (wordSem_state_termdep
       old_s)) (wordSem_state_clock_fupd (K (if wordSem_state_clock
       old_s < wordSem_state_clock new_s then wordSem_state_clock
       old_s else wordSem_state_clock new_s)) new_s))`;;

let is_word_def = new_definition
  `is_word x1 =
        match x1 with
          wordLang_Word w -> T
        | _27 -> F`;;
add_simp is_word_def;;

let get_word_def = define_general
  [`get_word (wordLang_Word w) = w`];;
add_simp get_word_def;;


let wordSem_mem_store_def = new_definition
  `wordSem_mem_store (addr':'a word) (w:'a word_loc)
  (s:('a,'c,'ffi)wordSem_state) =
     (if addr' IN wordSem_state_mdomain s then
       SOME (wordSem_state_memory_fupd (K ((addr' =+ w)
         (wordSem_state_memory s))) s) else NONE)`;;

let wordSem_mem_load_def = new_definition
  `wordSem_mem_load (addr':'a word) (s:('a,'c,'ffi)wordSem_state) =
     (if addr' IN wordSem_state_mdomain s then
       SOME (wordSem_state_memory s addr') else NONE)`;;

let the_words_def,the_words_ind = define_rec
  [`the_words [] = SOME []`;
   `the_words (CONS w ws) =
         (match (w,the_words ws) with (SOME (wordLang_Word
             x),SOME xs) -> SOME (CONS x xs) | _29 -> NONE)`];;

let wordSem_get_var_def = new_definition
  `wordSem_get_var v (s:('a,'c,'ffi)wordSem_state) = sptree_lookup v
  (wordSem_state_locals s)`;;

let wordSem_get_vars_def,wordSem_get_vars_ind = define_rec
  [`wordSem_get_vars [] (s:('a,'c,'ffi)wordSem_state) = SOME []`;
   `wordSem_get_vars (CONS v vs) (s:('a,'c,'ffi)wordSem_state) =
         (match wordSem_get_var v s with NONE -> NONE | SOME x
             -> (match wordSem_get_vars vs s with NONE -> NONE |
             SOME xs -> SOME (CONS x xs)))`];;

let wordSem_set_var_def = new_definition
  `wordSem_set_var v x (s:('a,'c,'ffi)wordSem_state) =
     (wordSem_state_locals_fupd (K (sptree_insert v x
       (wordSem_state_locals s))) s)`;;

let unset_var_def = new_definition
  `wordSem_unset_var v (s:('a,'c,'ffi)wordSem_state) =
  (wordSem_state_locals_fupd (K (sptree_delete v
  (wordSem_state_locals s))) s)`;;

let wordSem_set_vars_def = new_definition
  `wordSem_set_vars vs xs (s:('a,'c,'ffi)wordSem_state) =
     (wordSem_state_locals_fupd (K (alist_insert vs xs
       (wordSem_state_locals s))) s)`;;

let get_store_def = new_definition
  `wordSem_get_store v (s:('a,'c,'ffi)wordSem_state) = (FLOOKUP
  (wordSem_state_store s) v)`;;

let set_store_def = new_definition
  `wordSem_set_store v x (s:('a,'c,'ffi)wordSem_state) =
  (wordSem_state_store_fupd (K (wordSem_state_store s |+ (v,x))) s)`;;

(* the termination relation that HOL4 gives is
     MEASURE (wordLang_exp_size ARB o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 wordSemScript.sml:357-362: the tactic that proves the
   termination *)
let word_exp_def,word_exp_ind = define_shaped_rec
  "nested"
  [`wordSem_word_exp (s:('a,'c,'ffi)wordSem_state) (wordLang_Const w)
    = SOME (wordLang_Word w)`;
   `wordSem_word_exp (s:('a,'c,'ffi)wordSem_state) (wordLang_Var v) =
    wordSem_get_var v s`;
   `wordSem_word_exp (s:('a,'c,'ffi)wordSem_state) (wordLang_Lookup
    name) = wordSem_get_store name s`;
   `wordSem_word_exp (s:('a,'c,'ffi)wordSem_state) (wordLang_Load addr')
    =
         (match wordSem_word_exp s addr' with SOME (wordLang_Word
             w) -> wordSem_mem_load w s | _33 -> NONE)`;
   `wordSem_word_exp (s:('a,'c,'ffi)wordSem_state) (wordLang_Op op
    wexps) =
         (match the_words (MAP (wordSem_word_exp s) wexps) with
             SOME ws -> (OPTION_MAP wordLang_Word (wordLang_word_op
             op ws)) | _36 -> NONE)`;
   `wordSem_word_exp (s:('a,'c,'ffi)wordSem_state) (wordLang_Shift sh
    wexp wexp1) =
         (match (wordSem_word_exp s wexp,wordSem_word_exp s
             wexp1) with (SOME (wordLang_Word w),SOME
             (wordLang_Word w1)) -> OPTION_MAP wordLang_Word
             (word_sh sh w (w2n w1)) | _39 -> NONE)`];;

(* Flushes the locals and (optionally) the store *)
let wordSem_flush_state_def = define_general
  [`wordSem_flush_state T (s:('a,'c,'ffi)wordSem_state) =
    wordSem_state_locals_size_fupd (K (SOME 0))
    (wordSem_state_store_fupd (K FEMPTY) (wordSem_state_stack_fupd (K
    []) (wordSem_state_locals_fupd (K LN) s)))`;
   `wordSem_flush_state F (s:('a,'c,'ffi)wordSem_state) =
    wordSem_state_locals_size_fupd (K (SOME 0))
    (wordSem_state_locals_fupd (K LN) s)`];;

let sh_mem_store_def = new_definition
  `wordSem_sh_mem_store (a:'a word) (w:'a word)
  (s:('a,'c,'ffi)wordSem_state) =
     (if a IN wordSem_state_sh_mdomain s then
       match call_FFI (wordSem_state_ffi s) (ffi_SharedMem
         MappedWrite) [(n2w 0):word8]
                     (APPEND (word_to_bytes w F) (word_to_bytes a
                       F)) with FFI_final outcome -> (SOME
                       (wordSem_FinalFFI outcome),wordSem_flush_state
                       T s) | FFI_return new_ffi new_bytes ->
                       (NONE,(wordSem_state_ffi_fupd (K new_ffi) s))
                       else (SOME wordSem_Error,s))`;;

let sh_mem_load_def = new_definition
  `wordSem_sh_mem_load (a:'a word) (s:('a,'c,'ffi)wordSem_state) =
     (if a IN wordSem_state_sh_mdomain s then
       SOME (call_FFI (wordSem_state_ffi s) (ffi_SharedMem
         MappedRead) [(n2w 0):word8]
                     (word_to_bytes a F)) else NONE)`;;

let sh_mem_store_byte_def = new_definition
  `wordSem_sh_mem_store_byte (a:'a word) (w:'a word)
  (s:('a,'c,'ffi)wordSem_state) =
     (if byte_align a IN wordSem_state_sh_mdomain s then
       match call_FFI (wordSem_state_ffi s) (ffi_SharedMem
         MappedWrite) [(n2w 1):word8]
                     (APPEND [get_byte (n2w 0) w F] (word_to_bytes a
                       F)) with
         FFI_final outcome -> (SOME (wordSem_FinalFFI
           outcome),wordSem_flush_state T s) | FFI_return new_ffi
           new_bytes -> (NONE,(wordSem_state_ffi_fupd (K new_ffi) s))
           else (SOME wordSem_Error,s))`;;

let sh_mem_store16_def = new_definition
  `wordSem_sh_mem_store16 (a:'a word) (w:'a word)
  (s:('a,'c,'ffi)wordSem_state) =
     (if byte_align a IN wordSem_state_sh_mdomain s then
       match call_FFI (wordSem_state_ffi s) (ffi_SharedMem
         MappedWrite) [(n2w 2):word8]
                     (APPEND (TAKE 2 (word_to_bytes w F))
                       (word_to_bytes a F)) with
         FFI_final outcome -> (SOME (wordSem_FinalFFI
           outcome),wordSem_flush_state T s) | FFI_return new_ffi
           new_bytes -> (NONE,(wordSem_state_ffi_fupd (K new_ffi) s))
           else (SOME wordSem_Error,s))`;;

let sh_mem_store32_def = new_definition
  `wordSem_sh_mem_store32 (a:'a word) (w:'a word)
  (s:('a,'c,'ffi)wordSem_state) =
     (if byte_align a IN wordSem_state_sh_mdomain s then
       match call_FFI (wordSem_state_ffi s) (ffi_SharedMem
         MappedWrite) [(n2w 4):word8]
                     (APPEND (TAKE 4 (word_to_bytes w F))
                       (word_to_bytes a F)) with
         FFI_final outcome -> (SOME (wordSem_FinalFFI
           outcome),wordSem_flush_state T s) | FFI_return new_ffi
           new_bytes -> (NONE,(wordSem_state_ffi_fupd (K new_ffi) s))
           else (SOME wordSem_Error,s))`;;

let sh_mem_load_byte_def = new_definition
  `wordSem_sh_mem_load_byte (a:'a word) (s:('a,'c,'ffi)wordSem_state) =
     (if byte_align a IN wordSem_state_sh_mdomain s then
       SOME (call_FFI (wordSem_state_ffi s) (ffi_SharedMem
         MappedRead) [(n2w 1):word8]
                     (word_to_bytes a F)) else NONE)`;;

let sh_mem_load16_def = new_definition
  `wordSem_sh_mem_load16 (a:'a word) (s:('a,'c,'ffi)wordSem_state) =
     (if byte_align a IN wordSem_state_sh_mdomain s then
       SOME (call_FFI (wordSem_state_ffi s) (ffi_SharedMem
         MappedRead) [(n2w 2):word8]
                     (word_to_bytes a F)) else NONE)`;;

let sh_mem_load32_def = new_definition
  `wordSem_sh_mem_load32 (a:'a word) (s:('a,'c,'ffi)wordSem_state) =
     (if byte_align a IN wordSem_state_sh_mdomain s then
       SOME (call_FFI (wordSem_state_ffi s) (ffi_SharedMem
         MappedRead) [(n2w 4):word8]
                     (word_to_bytes a F)) else NONE)`;;

(* set variable given the output from ShareLoad(Byte) *)
let sh_mem_set_var_def = new_definition
  `sh_mem_set_var x1 v s =
        match (x1,s) with
          (SOME (FFI_final outcome),(s:('a,'c,'ffi)wordSem_state)) ->
            (SOME (wordSem_FinalFFI outcome),wordSem_flush_state T s)
        | ((SOME (FFI_return new_ffi new_bytes)),s) ->
          (NONE,wordSem_set_var v (wordLang_Word (word_of_bytes F (n2w
          0) new_bytes)) (wordSem_state_ffi_fupd (K new_ffi) s))
        | (_40,s) -> (SOME wordSem_Error,s)`;;

let share_inst_def = define_cases
  [`share_inst (asm_Load:memop) v ad s = sh_mem_set_var
    (wordSem_sh_mem_load ad s) v s`;
   `share_inst asm_Load8 v ad s = sh_mem_set_var
    (wordSem_sh_mem_load_byte ad s) v s`;
   `share_inst asm_Load16 v ad s = sh_mem_set_var
    (wordSem_sh_mem_load16 ad s) v s`;
   `share_inst (asm_Load32:memop) v ad s = sh_mem_set_var
    (wordSem_sh_mem_load32 ad s) v s`;
   `share_inst (asm_Store:memop) v ad s = (match wordSem_get_var v s
    with SOME (wordLang_Word v) -> wordSem_sh_mem_store ad v s | _47
    -> (SOME wordSem_Error,s))`;
   `share_inst asm_Store8 v ad s = (match wordSem_get_var v s with
    SOME (wordLang_Word v) -> wordSem_sh_mem_store_byte ad v s | _48
    -> (SOME wordSem_Error,s))`;
   `share_inst asm_Store16 v ad s = (match wordSem_get_var v s with
    SOME (wordLang_Word v) -> wordSem_sh_mem_store16 ad v s | _49 ->
    (SOME wordSem_Error,s))`;
   `share_inst (asm_Store32:memop) v ad s = (match wordSem_get_var
    v s with SOME (wordLang_Word v) -> wordSem_sh_mem_store32 ad v
    s | _52 -> (SOME wordSem_Error,s))`];;

let wordSem_call_env_def = new_definition
  `wordSem_call_env args size' (s:('a,'c,'ffi)wordSem_state) =
  wordSem_state_stack_max_fupd (K (OPTION_MAP2 MAX
  (wordSem_state_stack_max s) (OPTION_MAP2 (+) (stack_size
  (wordSem_state_stack s)) size'))) (wordSem_state_locals_size_fupd (K
  size') (wordSem_state_locals_fupd (K (fromList2 args))
     s))`;;

let list_rearrange_def = new_definition
  `list_rearrange mover xs =
     // if the mover function is actually a permutation,
     // i.e. it bijects (or injects) the keys 0...n-1 to 0...n-1
     // use it
     (if (BIJ mover (count (LENGTH xs)) (count (LENGTH xs))) then
       list_of_seq (\i. EL (mover i) xs) (LENGTH xs) else
       // if it isn't well-formed, just pretend it is I
       xs)`;;

(* Compare on keys, if keys match (never), then compare on
   the word_loc vals. Treat Words as < Locs *)
let key_val_compare_def = new_definition
  `key_val_compare x y =
     (let ((a:num),b) = x in
     let ((a':num),b') = y in
       (a > a') \/
       (a = a' /\
         (match b with
           wordLang_Word x -> (match b' with wordLang_Word y -> x
             <= y | _53 -> T) | wordLang_Loc a b -> (match b' with
             asm_Loc a' b' -> (a > a') \/ (a = a' /\ b >= b') | _54
             -> F))))`;;

(*
EVAL ``key_val_compare (1,Loc 3 4) (1,Loc 1 2)``
*)

let env_to_list_def = new_definition
  `env_to_list env (bij_seq:num->num->num) =
     (let mover = bij_seq 0 in
     let permute = (\n. bij_seq (n + 1)) in
     let l = toAList env in
     let l = sort key_val_compare l in
     let l = list_rearrange mover l in
       (l,permute))`;;

let wordSem_push_env_def = define_cases
  [`wordSem_push_env envs' NONE (s:('a,'c,'ffi)wordSem_state) =
        (let l0 = toAList (FST envs') in let
            (l,permute) = env_to_list (SND envs')
                (wordSem_state_permute s) in let
            stack' = CONS (StackFrame (wordSem_state_locals_size s)
                l0 l NONE) (wordSem_state_stack s) in
                wordSem_state_permute_fupd (K permute)
                (wordSem_state_stack_max_fupd (K (OPTION_MAP2 MAX
                (wordSem_state_stack_max s) (stack_size stack')))
                (wordSem_state_stack_fupd (K stack')
          s)))`;
   `wordSem_push_env envs' (SOME ((w:num),(h:'a wordLang_prog),l1,l2))
    (s:('a,'c,'ffi)wordSem_state) =
        (let l0 = toAList (FST envs') in let
            (l,permute) = env_to_list (SND envs')
                (wordSem_state_permute s) in let
            handler = SOME (wordSem_state_handler s,l1,l2) in let
            stack' = CONS (StackFrame (wordSem_state_locals_size s)
                l0 l handler) (wordSem_state_stack s) in
                wordSem_state_handler_fupd (K (LENGTH
                (wordSem_state_stack s))) (wordSem_state_permute_fupd (K
                permute) (wordSem_state_stack_max_fupd (K (OPTION_MAP2
                MAX (wordSem_state_stack_max s) (stack_size stack')))
                (wordSem_state_stack_fupd (K stack')
          s))))`];;

let wordSem_pop_env_def = new_definition
  `wordSem_pop_env (s:('a,'c,'ffi)wordSem_state) =
     (match wordSem_state_stack s with (CONS (StackFrame m e0 e NONE)
       xs) ->
          SOME (wordSem_state_locals_size_fupd (K m)
            (wordSem_state_stack_fupd (K xs) (wordSem_state_locals_fupd
            (K (sptree_union (fromAList e) (fromAList e0))) s))) | (CONS
            (StackFrame m e0 e (SOME (n,_55,_56))) xs) ->
          SOME (wordSem_state_handler_fupd (K n)
            (wordSem_state_locals_size_fupd (K m)
            (wordSem_state_stack_fupd (K xs)
            (wordSem_state_locals_fupd (K (sptree_union (fromAList e)
            (fromAList e0))) s)))) | _57 -> NONE)`;;

(* push_env_clock[local] *)
let wordSem_push_env_clock = prove
 (`wordSem_state_clock
     (wordSem_push_env env b ((s:('a,'c,'ffi)wordSem_state))) =
       wordSem_state_clock s`,
  CHEAT_TAC);;

(* pop_env_clock[local] *)
let wordSem_pop_env_clock = prove
 (`(wordSem_pop_env ((s:('a,'c,'ffi)wordSem_state)) = SOME s1) ==>
  (wordSem_state_clock s1 = wordSem_state_clock s)`,
  CHEAT_TAC);;

let wordSem_jump_exc_def = new_definition
  `wordSem_jump_exc (s:('a,'c,'ffi)wordSem_state) =
     (if wordSem_state_handler s < LENGTH (wordSem_state_stack s)
       then
       match LASTN (wordSem_state_handler s + 1) (wordSem_state_stack
         s) with CONS (StackFrame m e0 e (SOME (n,l1,l2))) xs ->
           SOME (wordSem_state_locals_size_fupd (K m)
             (wordSem_state_stack_fupd (K xs)
             (wordSem_state_locals_fupd (K (sptree_union (fromAList
             e) (fromAList e0))) (wordSem_state_handler_fupd (K n)
             s))),l1,l2) | _58 -> NONE else NONE)`;;

let cut_names_def = new_definition
  `cut_names name_set env =
       (if domain name_set SUBSET domain env then SOME (inter env
         name_set) else NONE)`;;

let cut_envs_def = new_definition
  `cut_envs (name_sets:1 spt#1 spt) env =
     (match (cut_names (FST name_sets) env,cut_names (SND
       name_sets) env) with (SOME e1,SOME e2) -> SOME (e1,e2) | _59
       -> NONE)`;;

let wordSem_cut_env_def = new_definition
  `wordSem_cut_env (name_sets:1 spt#1 spt) env =
     (match cut_envs name_sets env with SOME (e1,e2) -> SOME
       (sptree_union e2 e1) | _60 -> NONE)`;;
(* -- *)

let wordSem_cut_state_def = new_definition
  `wordSem_cut_state names (s:('a,'c,'ffi)wordSem_state) =
     (match wordSem_cut_env names (wordSem_state_locals s) with
       NONE -> NONE | SOME env -> SOME (wordSem_state_locals_fupd (K
       env) s))`;;

let wordSem_cut_state_opt_def = new_definition
  `wordSem_cut_state_opt names (s:('a,'c,'ffi)wordSem_state) =
     (match names with NONE -> SOME s | SOME names ->
       wordSem_cut_state names s)`;;

let wordSem_find_code_def = define_cases
  [`wordSem_find_code (SOME p) args code ssize =
         (match sptree_lookup p code with NONE -> NONE | SOME
             (arity,exp) -> (if LENGTH args = arity then SOME
             (args,exp,sptree_lookup p ssize) else NONE))`;
   `wordSem_find_code NONE args code ssize =
         (if args = [] then NONE else
           match LAST args with wordLang_Loc loc 0 ->
               (match sptree_lookup loc code with NONE -> NONE
                   | SOME (arity,exp) -> (if LENGTH args = arity +
                   1 then SOME (BUTLAST args,exp,sptree_lookup loc
                   ssize) else NONE)) | other -> NONE)`];;

let _ = size_thms "stack_frame";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let enc_stack_def,enc_stack_ind = define_wf
  `MEASURE (\x0. list_size (stack_frame_size (\x. 0)) x0)`
  [`wordSem_enc_stack [] = []`;
   `wordSem_enc_stack (CONS (StackFrame n _61 l handler) st) =
    APPEND (MAP SND l) (wordSem_enc_stack st)`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let dec_stack_def,dec_stack_ind = define_wf
  `MEASURE (\(x0,x1). list_size (stack_frame_size (\x. 0)) x1)`
  [`wordSem_dec_stack xs x2 =
        match (xs,x2) with
          ([],[]) -> SOME []
        | (xs,CONS (StackFrame n l0 l handler) st) ->
        (if LENGTH xs < LENGTH l then NONE else
          match wordSem_dec_stack (DROP (LENGTH l) xs) st with NONE
            -> NONE | SOME s -> SOME (CONS (StackFrame n l0
              (ZIP (MAP FST l) (TAKE (LENGTH l) xs)) handler) s))
        | (_62,_63) -> NONE`];;

let gc_def = new_definition
  `// gc runs the garbage collector algorithm
   wordSem_gc (s:('a,'c,'ffi)wordSem_state) =
     (let wl_list = wordSem_enc_stack (wordSem_state_stack s) in
       match wordSem_state_gc_fun s (wl_list,wordSem_state_memory
         s,wordSem_state_mdomain s,wordSem_state_store s) with NONE ->
         NONE | SOME (wl,m,st) ->
        (match wordSem_dec_stack wl (wordSem_state_stack s) with NONE
          -> NONE | SOME stack' ->
             SOME (wordSem_state_memory_fupd (K m)
               (wordSem_state_store_fupd (K st)
               (wordSem_state_stack_fupd (K stack') s)))))`;;

let has_space_def = new_definition
  `wordSem_has_space wl (s:('a,'c,'ffi)wordSem_state) =
     (match (wl,wordSem_get_store NextFree s,wordSem_get_store
       TriggerGC s) with (wordLang_Word w,SOME (wordLang_Word n),SOME
       (wordLang_Word l)) -> SOME (w2n w <= w2n (l - n)) | _64 ->
       NONE)`;;

(* to_ask: should we not update stack size here?  *)
let alloc_def = new_definition
  `wordSem_alloc (w:'a word) names (s:('a,'c,'ffi)wordSem_state) =
     // prune local names
     (match cut_envs names (wordSem_state_locals s) with NONE ->
       (SOME (wordSem_Error:'a wordSem_result),wordSem_flush_state T s)
       | SOME envs' ->
      (
       // perform garbage collection
       match wordSem_gc (wordSem_push_env envs' (NONE:(num#'a
         wordLang_prog#num#num) option) (wordSem_set_store AllocSize
         (wordLang_Word w) s)) with NONE -> (SOME
         wordSem_Error,wordSem_flush_state T s) | SOME s ->
        (
         // restore local variables
         match wordSem_pop_env s with
           // Here flush_state is ok because the stack must
           // be empty for pop_env to return NONE
           NONE -> (SOME wordSem_Error,wordSem_flush_state T s) |
             SOME s ->
          (
           // read how much space should be allocated
           match wordSem_get_store AllocSize s with NONE -> (SOME
             wordSem_Error,s) | SOME w ->
            (
             // check how much space there is
             match wordSem_has_space w s with NONE -> (SOME
               wordSem_Error,s) | SOME T ->
                         (
                          // success there is that much space
                          NONE,s) | SOME F ->
                         (
                          // fail, GC didn't free up enough space
                          SOME
                            wordSem_NotEnoughSpace
                            ,wordSem_flush_state T s))))))`;;

let wordSem_assign_def = new_definition
  `wordSem_assign reg exp (s:('a,'c,'ffi)wordSem_state) =
     (match wordSem_word_exp s exp with NONE -> NONE | SOME w ->
       SOME (wordSem_set_var reg w s))`;;

let get_fp_var_def = new_definition
  `wordSem_get_fp_var v (s:('a,'c,'ffi)wordSem_state) = FLOOKUP
  (wordSem_state_fp_regs s) v`;;

let set_fp_var_def = new_definition
  `wordSem_set_fp_var v x (s:('a,'c,'ffi)wordSem_state) =
     (wordSem_state_fp_regs_fupd (K (wordSem_state_fp_regs s |+
       (v,x))) s)`;;

let wordSem_inst_def = new_definition
  `wordSem_inst i (s:('a,'c,'ffi)wordSem_state) =
     (match i with asm_Skip -> SOME s | asm_Const reg w ->
       wordSem_assign reg (wordLang_Const w) s | asm_Arith (asm_Binop
       bop r1 r2 ri) ->
         wordSem_assign r1
           (wordLang_Op bop [wordLang_Var r2; match ri with Reg r3 ->
             wordLang_Var r3 | Imm w -> wordLang_Const w]) s | asm_Arith
             (asm_Shift sh r1 r2 ri) ->
         wordSem_assign r1
           (wordLang_Shift sh (wordLang_Var r2) (match ri with Reg r3
             -> wordLang_Var r3 | Imm w -> wordLang_Const w)) s |
             asm_Arith (asm_Div r1 r2 r3) ->
        (let vs = wordSem_get_vars [r3; r2] s in
        match vs with
        SOME [wordLang_Word q; wordLang_Word w2] ->
          (if ~(q = (n2w 0)) then
            SOME (wordSem_set_var r1 (wordLang_Word (w2 / q)) s) else
              NONE) | _65 -> NONE) | asm_Arith (asm_AddCarry r1 r2 r3
              r4) ->
         (let vs = wordSem_get_vars [r2; r3; r4] s in
         match vs with
         SOME [wordLang_Word l; wordLang_Word r; wordLang_Word c] ->
           (let (res,co) = word_add_carry l r c in
             SOME (wordSem_set_var r4 (wordLang_Word co)
               (wordSem_set_var r1 (wordLang_Word res) s))) | _66 ->
               NONE) | asm_Arith (asm_AddOverflow r1 r2 r3 r4) ->
         (let vs = wordSem_get_vars [r2; r3] s in
         match vs with
         SOME [wordLang_Word w2; wordLang_Word w3] ->
           SOME (wordSem_set_var r4 (wordLang_Word (if ~(w2i (w2 +
             w3) = w2i w2 + w2i w3) then (n2w 1) else (n2w 0)))
                  (wordSem_set_var r1 (wordLang_Word (w2 + w3)) s)) |
                    _67 -> NONE) | asm_Arith (asm_SubOverflow r1 r2 r3
                    r4) ->
         (let vs = wordSem_get_vars [r2; r3] s in
         match vs with
         SOME [wordLang_Word w2; wordLang_Word w3] ->
           SOME (wordSem_set_var r4 (wordLang_Word (if ~(w2i (w2 -
             w3) = w2i w2 - w2i w3) then (n2w 1) else (n2w 0)))
                  (wordSem_set_var r1 (wordLang_Word (w2 - w3)) s)) |
                    _68 -> NONE) | asm_Arith (asm_LongMul r1 r2 r3 r4)
                    ->
         (let vs = wordSem_get_vars [r3; r4] s in
         match vs with
         SOME [wordLang_Word w3; wordLang_Word w4] ->
          (let r = w2n w3 * w2n w4 in
            SOME (wordSem_set_var r2 (wordLang_Word (n2w r))
              (wordSem_set_var r1 (wordLang_Word (n2w (r DIV dimword
              (:'a)))) s))) | _69 -> NONE) | asm_Arith (asm_LongDiv r1
              r2 r3 r4 r5) ->
        (let vs = wordSem_get_vars [r3; r4; r5] s in
        match vs with
        SOME [wordLang_Word w3; wordLang_Word w4; wordLang_Word w5]
          ->
          (let n = w2n w3 * dimword (:'a) + w2n w4 in
          let d = w2n w5 in
          let q = n DIV d in
          if (~(d = 0) /\ q < dimword (:'a)) then
            SOME (wordSem_set_var r1 (wordLang_Word (n2w q))
              (wordSem_set_var r2 (wordLang_Word (n2w (n MOD d))) s))
              else NONE) | _70 -> NONE) | asm_Mem asm_Load r (Addr a w)
              ->
        (match wordSem_word_exp s (wordLang_Op asm_Add [wordLang_Var
          a; wordLang_Const w]) with SOME (wordLang_Word w) ->
            (match wordSem_mem_load w s with NONE -> NONE | SOME w ->
              SOME (wordSem_set_var r w s)) | _71 -> NONE) | asm_Mem
              asm_Load8 r (Addr a w) ->
        (match wordSem_word_exp s (wordLang_Op asm_Add [wordLang_Var
          a; wordLang_Const w]) with SOME (wordLang_Word w) ->
            (match mem_load_byte_aux (wordSem_state_memory s)
              (wordSem_state_mdomain s) (wordSem_state_be s) w with NONE
              -> NONE | SOME w -> SOME (wordSem_set_var r (wordLang_Word
              (w2w w)) s)) | _72 -> NONE) | asm_Mem asm_Load16 _73 _74
              -> NONE | asm_Mem asm_Load32 r (Addr a w) ->
        (match wordSem_word_exp s (wordLang_Op asm_Add [wordLang_Var
          a; wordLang_Const w]) with SOME (wordLang_Word w) ->
            (match mem_load_32 (wordSem_state_memory s)
              (wordSem_state_mdomain s) (wordSem_state_be s) w with NONE
              -> NONE | SOME w -> SOME (wordSem_set_var r (wordLang_Word
              (w2w w)) s)) | _75 -> NONE) | asm_Mem asm_Store r (Addr a
              w) ->
        (match (wordSem_word_exp s (wordLang_Op asm_Add [wordLang_Var
          a; wordLang_Const w]),wordSem_get_var r s) with (SOME
          (wordLang_Word a),SOME w) ->
             (match wordSem_mem_store a w s with SOME s1 -> SOME s1 |
               NONE -> NONE) | _76 -> NONE) | asm_Mem asm_Store8 r (Addr
               a w) ->
        (match (wordSem_word_exp s (wordLang_Op asm_Add [wordLang_Var
          a; wordLang_Const w]),wordSem_get_var r s) with (SOME
          (wordLang_Word a),SOME (wordLang_Word w)) ->
             (match mem_store_byte_aux (wordSem_state_memory s)
               (wordSem_state_mdomain s) (wordSem_state_be s) a (w2w w)
               with SOME new_m -> SOME (wordSem_state_memory_fupd (K
               new_m) s) | NONE -> NONE) | _77 -> NONE) | asm_Mem
               asm_Store16 _78 _79 -> NONE | asm_Mem asm_Store32 r (Addr
               a w) ->
        (match (wordSem_word_exp s (wordLang_Op asm_Add [wordLang_Var
          a; wordLang_Const w]),wordSem_get_var r s) with (SOME
          (wordLang_Word a),SOME (wordLang_Word w)) ->
             (match mem_store_32 (wordSem_state_memory s)
               (wordSem_state_mdomain s) (wordSem_state_be s) a (w2w w)
               with SOME new_m -> SOME (wordSem_state_memory_fupd (K
               new_m) s) | NONE -> NONE) | _80 -> NONE) | asm_FP (FPLess
               r d1 d2) ->
       (match (wordSem_get_fp_var d1 s,wordSem_get_fp_var d2 s) with
         (SOME f1,SOME f2) ->
         SOME (wordSem_set_var r
           (wordLang_Word (if fp64_lessThan f1 f2 then (n2w 1) else
             (n2w 0))) s) | _81 -> NONE) | asm_FP (FPLessEqual r d1 d2)
             ->
       (match (wordSem_get_fp_var d1 s,wordSem_get_fp_var d2 s) with
         (SOME f1,SOME f2) ->
         SOME (wordSem_set_var r
           (wordLang_Word (if fp64_lessEqual f1 f2 then (n2w 1) else
             (n2w 0))) s) | _82 -> NONE) | asm_FP (FPEqual r d1 d2) ->
       (match (wordSem_get_fp_var d1 s,wordSem_get_fp_var d2 s) with
         (SOME f1,SOME f2) ->
         SOME (wordSem_set_var r
           (wordLang_Word (if fp64_equal f1 f2 then (n2w 1) else (n2w
             0))) s) | _83 -> NONE) | asm_FP (FPMov d1 d2) ->
       (match wordSem_get_fp_var d2 s with SOME f ->
         SOME (wordSem_set_fp_var d1 f s) | _84 -> NONE) | asm_FP
           (FPAbs d1 d2) ->
       (match wordSem_get_fp_var d2 s with SOME f ->
         SOME (wordSem_set_fp_var d1 (fp64_abs f) s) | _85 -> NONE) |
           asm_FP (FPNeg d1 d2) ->
       (match wordSem_get_fp_var d2 s with SOME f ->
         SOME (wordSem_set_fp_var d1 (fp64_negate f) s) | _86 ->
           NONE) | asm_FP (FPSqrt d1 d2) ->
       (match wordSem_get_fp_var d2 s with SOME f ->
         SOME (wordSem_set_fp_var d1 (fp64_sqrt roundTiesToEven f) s)
           | _87 -> NONE) | asm_FP (FPAdd d1 d2 d3) ->
       (match (wordSem_get_fp_var d2 s,wordSem_get_fp_var d3 s) with
         (SOME f1,SOME f2) ->
         SOME (wordSem_set_fp_var d1 (fp64_add roundTiesToEven f1 f2)
           s) | _88 -> NONE) | asm_FP (FPSub d1 d2 d3) ->
       (match (wordSem_get_fp_var d2 s,wordSem_get_fp_var d3 s) with
         (SOME f1,SOME f2) ->
         SOME (wordSem_set_fp_var d1 (fp64_sub roundTiesToEven f1 f2)
           s) | _89 -> NONE) | asm_FP (FPMul d1 d2 d3) ->
       (match (wordSem_get_fp_var d2 s,wordSem_get_fp_var d3 s) with
         (SOME f1,SOME f2) ->
         SOME (wordSem_set_fp_var d1 (fp64_mul roundTiesToEven f1 f2)
           s) | _90 -> NONE) | asm_FP (FPDiv d1 d2 d3) ->
       (match (wordSem_get_fp_var d2 s,wordSem_get_fp_var d3 s) with
         (SOME f1,SOME f2) ->
         SOME (wordSem_set_fp_var d1 (fp64_div roundTiesToEven f1 f2)
           s) | _91 -> NONE) | asm_FP (FPFma d1 d2 d3) ->
       (match (wordSem_get_fp_var d1 s,wordSem_get_fp_var d2
         s,wordSem_get_fp_var d3 s) with (SOME f1,SOME f2,SOME f3) ->
         SOME (wordSem_set_fp_var d1 (fpfma f1 f2 f3) s) | _92 ->
           NONE) | asm_FP (FPMovToReg r1 r2 d) ->
       (match wordSem_get_fp_var d s with SOME v ->
         (if dimindex (:'a) = 64 then
           SOME (wordSem_set_var r1 (wordLang_Word (w2w v)) s) else
           SOME (wordSem_set_var r2 (wordLang_Word ((63 >< 32) v))
             (wordSem_set_var r1 (wordLang_Word ((31 >< 0) v)) s))) |
             _93 -> NONE) | asm_FP (FPMovFromReg d r1 r2) ->
       (if dimindex (:'a) = 64 then
         match wordSem_get_var r1 s with
           SOME (wordLang_Word w1) -> SOME (wordSem_set_fp_var d (w2w
             w1) s) | _94 -> NONE else
         match (wordSem_get_var r1 s,wordSem_get_var r2 s) with
           (SOME (wordLang_Word w1),SOME (wordLang_Word w2)) -> SOME
             (wordSem_set_fp_var d (w2 @@ w1) s) | _95 -> NONE) | asm_FP
             (FPToInt d1 d2) ->
       (match wordSem_get_fp_var d2 s with
         NONE -> NONE | SOME f ->
       (match fp64_to_int roundTiesToEven f with
         NONE -> NONE | SOME i ->
         (let w = (i2w i:word32) in
         if w2i w = i then
           (if dimindex (:'a) = 64 then
              SOME (wordSem_set_fp_var d1 (w2w w) s) else
            match wordSem_get_fp_var (d1 DIV 2) s with
              NONE -> NONE | SOME f ->
              (let (h,l) = (if ODD d1 then (63,32) else (31,0)) in
                   SOME (wordSem_set_fp_var (d1 DIV 2)
                     (bit_field_insert h l w f) s))) else
           NONE))) | asm_FP (FPFromInt d1 d2) ->
       (if dimindex (:'a) = 64 then
         match wordSem_get_fp_var d2 s with SOME f ->
           (let i = w2i ((31 >< 0) f:word32) in
             SOME (wordSem_set_fp_var d1 (int_to_fp64 roundTiesToEven
               i) s)) | NONE -> NONE else
         match wordSem_get_fp_var (d2 DIV 2) s with SOME v ->
           (let i = w2i (if ODD d2 then (63 >< 32) v else (31 >< 0)
             v:'a word) in
             SOME (wordSem_set_fp_var d1 (int_to_fp64
               roundTiesToEven i) s)) | NONE -> NONE | _96 -> NONE))`;;

let get_var_imm_def = define_cases
  [`wordSem_get_var_imm ((Reg n):'a asm_reg_imm)
    (s:('a,'c,'ffi)wordSem_state) = wordSem_get_var n s`;
   `wordSem_get_var_imm (Imm w) (s:('a,'c,'ffi)wordSem_state) =
    SOME (wordLang_Word w)`];;

let add_ret_loc_def = define_cases
  [`add_ret_loc NONE xs = xs`;
   `add_ret_loc (SOME (n,names,ret_handler,l1,l2)) xs = CONS
    (wordLang_Loc l1 l2) xs`];;

(*Avoid case split*)
let bad_dest_args_def = new_definition
  `bad_dest_args dest args <=> dest = NONE /\ args = []`;;

(* [local] *)
let termdep_rw = prove
 (`(wordSem_state_termdep (wordSem_call_env p_1 ss
  ((s:('a,'c,'ffi)wordSem_state))) = wordSem_state_termdep s) /\
     (wordSem_state_termdep (wordSem_dec_clock s) =
       wordSem_state_termdep s) /\
     (wordSem_state_termdep (wordSem_set_var n v s) =
       wordSem_state_termdep s)`,
  CHEAT_TAC);;

(* [local] *)
let fix_clock_IMP_LESS_EQ = prove
 (`!x. wordSem_fix_clock ((s:('a,'c,'ffi)wordSem_state)) x = (res,s1)
  ==> wordSem_state_clock s1 <= wordSem_state_clock s /\
  wordSem_state_termdep s1 = wordSem_state_termdep s`,
  CHEAT_TAC);;

let MustTerminate_limit_def = new_definition
  `MustTerminate_limit (:'a) =
     // This is just a number that's large enough for our purposes.
     // It stated in a way that makes proofs easy.
     2 * dimword (:'a) +
     dimword (:'a) * dimword (:'a) +
     dimword (:'a) EXP dimword (:'a) +
     dimword (:'a) EXP dimword (:'a) EXP dimword (:'a)`;;

let const_addresses_def,const_addresses_ind = define_rec
  [`const_addresses a [] d = T`;
   `const_addresses a (CONS x xs) d =
      (a IN d /\ const_addresses (a + bytes_in_word) xs d)`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let const_writes_def,const_writes_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3). list_size (pair_size (\x. 0) (\x. 0)) x2)`
  [`const_writes (a:'a word) off [] m = m`;
   `const_writes (a:'a word) off (CONS (b,(x:'a word)) xs) m =
      const_writes (a + bytes_in_word) off xs
        ((a =+ wordLang_Word (if b then x + off else x)) m)`];;

let STOP_def = new_definition
  `wordSem_STOP x = x`;;

let bad_fun_return_def = new_definition
  `wordSem_bad_fun_return x1 =
      match x1 with
        NONE -> T
      | (SOME (wordSem_Break _97)) -> T
      | (SOME (wordSem_Continue _98)) -> T
      | _99 -> F`;;
add_simp bad_fun_return_def;;

let cont_loop_def = new_definition
  `wordSem_cont_loop x1 =
      match x1 with
        NONE -> T
      | (SOME (wordSem_Continue n)) -> (n = 0)
      | _100 -> F`;;
add_simp cont_loop_def;;

let exit_loop_def = new_definition
  `wordSem_exit_loop res =
      match res with
        SOME (wordSem_Break n) -> SOME (wordSem_Break (n - 1))
      | (SOME (wordSem_Continue n)) -> SOME (wordSem_Continue (n -
        1))
      | res -> res`;;
add_simp exit_loop_def;;

let wordSem_fix_clock_IMP =
  try prove
   (`!s x res s1. wordSem_fix_clock s x = (res,s1)
                  ==> wordSem_state_clock s1 <=
                      wordSem_state_clock s /\
                      wordSem_state_termdep s1 =
                      wordSem_state_termdep s`,
    REWRITE_TAC[FORALL_PAIR_THM; wordSem_fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "wordSem_state") THEN
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "wordSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nwordSem_fix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl wordSem_fix_clock_IMP <> `T` then
  cake_term_facts := wordSem_fix_clock_IMP :: (!cake_term_facts);;

let wordSem_evaluate_def,wordSem_evaluate_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`wordSem_evaluate ((wordLang_Skip:'a
    wordLang_prog),(s:('a,'c,'ffi)wordSem_state)) = (NONE,s)`;
   `wordSem_evaluate (wordLang_Alloc n names,s) =
         (match wordSem_get_var n s with SOME (wordLang_Word w)
             -> wordSem_alloc w names s | _106 -> (SOME
             wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_StoreConsts t1 t2 addr' offset words,s) =
         (match (wordSem_get_var addr' s,wordSem_get_var offset s)
             with (SOME (wordLang_Word a),SOME (wordLang_Word off)) ->
            (if ~(const_addresses a words (wordSem_state_mdomain s))
                then
               (SOME wordSem_Error,s) else
               let s = wordSem_state_memory_fupd (K (const_writes a
                   off words (wordSem_state_memory s))) s in
               let s = wordSem_set_var offset (wordLang_Word off)
                   (wordSem_unset_var t1 (wordSem_unset_var t2 s)) in
                 (NONE,wordSem_set_var addr' (wordLang_Word (a +
                     bytes_in_word * n2w (LENGTH words))) s)) | _109
                     -> (SOME wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_Move pri moves,s) =
         (if ALL_DISTINCT (MAP FST moves) then
           match wordSem_get_vars (MAP SND moves) s with NONE ->
               (SOME wordSem_Error,s) | SOME vs ->
               (NONE,wordSem_set_vars (MAP FST moves) vs s) else
               (SOME wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_Inst i,s) =
         (match wordSem_inst i s with SOME s1 -> (NONE,s1) | NONE
             -> (SOME wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_Assign v exp,s) =
         (match wordSem_word_exp s exp with NONE -> (SOME
             wordSem_Error,s) | SOME w -> (NONE,wordSem_set_var v w
             s))`;
   `wordSem_evaluate (wordLang_Get v name,s) =
         (match wordSem_get_store name s with NONE -> (SOME
             wordSem_Error,s) | SOME x -> (NONE,wordSem_set_var v x
             s))`;
   `wordSem_evaluate (wordLang_Set v exp,s) =
         (if v = Handler \/ v = BitmapBase then (SOME
             wordSem_Error,s) else
         match wordSem_word_exp s exp with NONE -> (SOME
             wordSem_Error,s) | SOME w -> (NONE,wordSem_set_store v w
             s))`;
   `wordSem_evaluate (wordLang_OpCurrHeap b dst src,s) =
         (match wordSem_word_exp s (wordLang_Op b [wordLang_Var
             src; wordLang_Lookup CurrHeap]) with NONE -> (SOME
             wordSem_Error,s) | SOME w -> (NONE,wordSem_set_var dst w
             s))`;
   `wordSem_evaluate (wordLang_Store exp v,s) =
         (match (wordSem_word_exp s exp,wordSem_get_var v s) with
             (SOME (wordLang_Word a),SOME w) ->
             (match wordSem_mem_store a w s with SOME s1 ->
                 (NONE,s1) | NONE -> (SOME wordSem_Error,s)) | _112
                 -> (SOME wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_Tick,s) =
         (if wordSem_state_clock s = 0 then (SOME
             wordSem_TimeOut,wordSem_flush_state T s) else
             (NONE,wordSem_dec_clock s))`;
   `wordSem_evaluate (wordLang_MustTerminate p,s) =
         (if wordSem_state_termdep s = 0 then (SOME wordSem_Error,s)
             else
           let (res,s1) = wordSem_evaluate
               (p,wordSem_state_termdep_fupd (K (wordSem_state_termdep s
               - 1)) (wordSem_state_clock_fupd (K (MustTerminate_limit
               (:'a))) s)) in
             if res = SOME wordSem_TimeOut then (SOME
                 wordSem_Error,s) else
                 (res,wordSem_state_termdep_fupd (K
                 (wordSem_state_termdep s)) (wordSem_state_clock_fupd
                 (K (wordSem_state_clock s)) s1)))`;
   `wordSem_evaluate (wordLang_Seq c1 c2,s) =
         (let (res,s1) = wordSem_fix_clock s (wordSem_evaluate
             (c1,s)) in
           if res = NONE then wordSem_evaluate (c2,s1) else
               (res,s1))`;
   `wordSem_evaluate (wordLang_Return n ms,s) =
         (match (wordSem_get_var n s,wordSem_get_vars ms s) with
             (SOME (wordLang_Loc l1 l2),SOME ys) -> (SOME
             (wordSem_Result (wordLang_Loc l1 l2)
             ys),wordSem_flush_state F s) | _115 -> (SOME
             wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_Raise n,s) =
         (match wordSem_get_var n s with NONE -> (SOME
             wordSem_Error,s) | SOME w ->
           (match wordSem_jump_exc s with NONE -> (SOME
               wordSem_Error,s) | SOME (s,l1,l2) -> (SOME
               (wordSem_Exception (wordLang_Loc l1 l2) w)),s))`;
   `wordSem_evaluate (wordLang_Break k,s) = (SOME (Break k),s)`;
   `wordSem_evaluate (wordLang_Continue k,s) = (SOME (Continue k),s)`;
   `wordSem_evaluate (wordLang_If cmp r1 ri c1 c2,s) =
        (match (wordSem_get_var r1 s,wordSem_get_var_imm ri s) with
            (SOME x,SOME y) ->
         (match wordSem_word_cmp cmp x y with SOME T ->
             wordSem_evaluate (c1,s) | SOME F -> wordSem_evaluate
             (c2,s) | NONE -> (SOME wordSem_Error,s)) | _118 -> (SOME
             wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_Loop names c exit_names,s) =
         (match wordSem_cut_state (names,LN) s with NONE -> (SOME
             wordSem_Error,s) | SOME s ->
             (let (res,s1) = wordSem_fix_clock s (wordSem_evaluate
                 (c,s)) in
               if wordSem_cont_loop res then
                 (if wordSem_state_clock s1 = 0 then (SOME
                     wordSem_TimeOut,wordSem_flush_state T s1) else
                    wordSem_evaluate (wordSem_STOP ((wordLang_Loop
                        names c exit_names:'a
                        wordLang_prog)),wordSem_dec_clock s1)) else if
                        res = SOME (Break 0) then
                 match wordSem_cut_state (exit_names,LN) s1 with
                     NONE -> (SOME wordSem_Error,s1) | SOME s2 ->
                     (NONE,s2) else (wordSem_exit_loop res,s1)))`;
   `wordSem_evaluate (wordLang_LocValue r l1,s) =
         (if l1 IN domain (wordSem_state_code s) then
           (NONE,wordSem_set_var r (wordLang_Loc l1 0) s) else
               (SOME wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_Install ptr len dptr dlen names,s) =
        (match wordSem_cut_env names (wordSem_state_locals s) with
            NONE -> (SOME wordSem_Error,s) | SOME env ->
        (match (wordSem_get_var ptr s,wordSem_get_var len
            s,wordSem_get_var dptr s,wordSem_get_var dlen s) with (SOME
            (wordLang_Word w1),SOME (wordLang_Word w2),SOME
            (wordLang_Word w3),SOME (wordLang_Word w4)) ->
           (let (cfg,progs) = wordSem_state_compile_oracle s 0 in
           (match (
                 buffer_flush (wordSem_state_code_buffer s) w1
                     w2,buffer_flush (wordSem_state_data_buffer s) w3
                     w4) with (
             SOME (bytes,cb),SOME (data,db)) ->
            (let new_oracle = misc_shift_seq 1
                (wordSem_state_compile_oracle s) in
            (match (wordSem_state_compile s cfg progs,progs) with
                (SOME (bytes',data',cfg'),CONS (k,prog) _127) ->
                (if bytes = bytes' /\ data = data' /\ FST
                    (new_oracle 0) = cfg' then
                let s' = wordSem_state_stack_size_fupd (K LN)
                    (wordSem_state_stack_max_fupd (K NONE)
                    (wordSem_state_compile_oracle_fupd (K new_oracle)
                    (wordSem_state_fp_regs_fupd (K FEMPTY)
                    (wordSem_state_locals_fupd (K (sptree_insert ptr
                    (wordLang_Loc k 0) env)) (wordSem_state_code_fupd (K
                    (sptree_union (wordSem_state_code s) (fromAList
                    progs))) (wordSem_state_data_buffer_fupd (K db)
                    (wordSem_state_code_buffer_fupd (K cb)
                    s))))))) in
                  (
                   // For convenience --- stack size of installed code,
                   // or any other code for that matter, doesn't matter
                   // after Install.
                   NONE,s') else (SOME wordSem_Error,s)) | _128
                       -> (SOME wordSem_Error,s))) | _129 -> (SOME
                       wordSem_Error,s))) | _130 -> (SOME
                       wordSem_Error,s)))
    // This order is convenient because it means all of s.code's entries are preserved
    // Install is not safe for space`;
   `wordSem_evaluate (wordLang_CodeBufferWrite r1 r2,s) =
        (match (wordSem_get_var r1 s,wordSem_get_var r2 s) with
            (SOME (wordLang_Word w1),SOME (wordLang_Word w2)) ->
              (match buffer_write (wordSem_state_code_buffer s) w1
                  (w2w w2) with SOME new_cb ->
                (NONE,wordSem_state_code_buffer_fupd (K new_cb)
                    s) | _135 -> (SOME wordSem_Error,s)) | _136 ->
                    (SOME wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_DataBufferWrite r1 r2,s) =
        (match (wordSem_get_var r1 s,wordSem_get_var r2 s) with
            (SOME (wordLang_Word w1),SOME (wordLang_Word w2)) ->
              (match buffer_write (wordSem_state_data_buffer s) w1
                  w2 with SOME new_db ->
                (NONE,wordSem_state_data_buffer_fupd (K new_db)
                    s) | _141 -> (SOME wordSem_Error,s)) | _142 ->
                    (SOME wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_FFI ffi_index ptr1 len1 ptr2 len2
    names,s) =
        (match (wordSem_get_var len1 s,wordSem_get_var ptr1
            s,wordSem_get_var len2 s,wordSem_get_var ptr2 s) with (SOME
            (wordLang_Word w),SOME (wordLang_Word w2),SOME
            (wordLang_Word w3),SOME (wordLang_Word w4)) ->
          (match wordSem_cut_env names (wordSem_state_locals s) with
              NONE -> (SOME wordSem_Error,s) | SOME env ->
            (match (read_bytearray w2 (w2n w) (mem_load_byte_aux
                (wordSem_state_memory s) (wordSem_state_mdomain s)
                (wordSem_state_be s)),
                   read_bytearray w4 (w2n w3) (mem_load_byte_aux
                       (wordSem_state_memory s) (wordSem_state_mdomain
                       s) (wordSem_state_be s))) with (SOME bytes,SOME
                       bytes2) ->
                 (match call_FFI (wordSem_state_ffi s) (ffi_ExtCall
                     ffi_index) bytes bytes2 with FFI_final outcome ->
                     (SOME (wordSem_FinalFFI
                     outcome),wordSem_flush_state T s) | FFI_return
                     new_ffi new_bytes ->
                    (let new_m = write_bytearray w4 new_bytes
                        (wordSem_state_memory s) (wordSem_state_mdomain
                        s) (wordSem_state_be s) in
                      (NONE,wordSem_state_ffi_fupd (K new_ffi)
                          (wordSem_state_fp_regs_fupd (K FEMPTY)
                          (wordSem_state_locals_fupd (K env)
                          (wordSem_state_memory_fupd (K new_m)
                          s)))))) | _145 -> (SOME wordSem_Error,s)))
                          | res -> (SOME wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_ShareInst op v exp,s) =
        (match wordSem_word_exp s exp with SOME (wordLang_Word
            ad) -> share_inst op v ad s | _146 -> (SOME
            wordSem_Error,s))`;
   `wordSem_evaluate (wordLang_Call ret dest args handler,s) =
       (match wordSem_get_vars args s with NONE -> (SOME
           wordSem_Error,s) | SOME xs ->
           (if bad_dest_args dest args then (SOME wordSem_Error,s)
               else
             match wordSem_find_code dest (add_ret_loc ret xs)
                 (wordSem_state_code s) (wordSem_state_stack_size s)
                 with NONE -> (SOME wordSem_Error,s) | SOME
                 (args1,prog,ss) ->
                 (match ret with NONE ->
                     // tail call
                     (if handler = NONE then
                       if wordSem_state_clock s = 0 then (SOME
                           wordSem_TimeOut,wordSem_flush_state T s) else
                           (match wordSem_evaluate
                           (prog,wordSem_call_env args1 ss
                           (wordSem_dec_clock s)) with (res,s) -> (if
                           wordSem_bad_fun_return res then (SOME
                           wordSem_Error,s) else (res,s))) else (SOME
                           wordSem_Error,s)) | SOME
                           (n,names,ret_handler,l1,l2) ->
                     // returning call, returns into var n
                     (if domain (FST names) = {} \/ ~(ALL_DISTINCT
                         n) then (SOME wordSem_Error,s) else
                       (match cut_envs names (wordSem_state_locals
                           s) with NONE -> (SOME wordSem_Error,s) | SOME
                           envs' ->
                            (if wordSem_state_clock s = 0 then
                              (SOME wordSem_TimeOut,
                              wordSem_flush_state T
                              (wordSem_state_stack_max_fupd (K
                                  (wordSem_state_stack_max
                                  (wordSem_call_env args1 ss
                              (wordSem_push_env envs' handler s))))
                                  (wordSem_state_stack_fupd (K []) s)))
                                  else
                              (match wordSem_fix_clock
                                  (wordSem_call_env args1 ss
                                  (wordSem_push_env envs' handler
                                  (wordSem_dec_clock s)))
                              (wordSem_evaluate
                                  (prog,wordSem_call_env args1 ss
                              (wordSem_push_env envs' handler
                                  (wordSem_dec_clock s)))) with (SOME
                                  (wordSem_Result x ys),s2) ->
                              (if ~(x = wordLang_Loc l1 l2) \/
                                  ~(LENGTH ys = LENGTH n) then (SOME
                                  wordSem_Error,s2) else
                              (match wordSem_pop_env s2 with NONE ->
                                  (SOME wordSem_Error,s2) | SOME s1 ->
                              (if domain (wordSem_state_locals s1) =
                                  domain (FST envs') UNION domain (SND
                                  envs') then wordSem_evaluate
                                  (ret_handler,wordSem_set_vars n ys s1)
                                  else (SOME wordSem_Error,s1)))) |
                                  (SOME (wordSem_Exception x y),s2) ->
                              (match handler with
                              // if handler is present, then handle exc
                              NONE -> (SOME (wordSem_Exception x
                                  y),s2) | SOME (n,h,l1,l2) ->
                              (if ~(x = wordLang_Loc l1 l2) then
                                  (SOME wordSem_Error,s2) else
                              (if domain (wordSem_state_locals
                                  s2) = domain (FST envs') UNION
                                  domain (SND envs') then
                                  wordSem_evaluate
                                  (h,wordSem_set_var n y s2) else
                                  (SOME wordSem_Error,s2)))) |
                                  (NONE,s) -> (SOME
                                  wordSem_Error,s) | (SOME (Break
                                  _157),s) -> (SOME
                                  wordSem_Error,s) | (SOME
                                  (Continue _158),s) -> (SOME
                                  wordSem_Error,s) | res ->
                                  res)))))))`];;

(* We prove that the clock never increases and that termdep is constant. *)

let gc_clock = prove
 (`!s1 s2. (wordSem_gc s1 = SOME s2) ==> wordSem_state_clock s2 <=
  wordSem_state_clock s1 /\ wordSem_state_termdep s2 =
  wordSem_state_termdep s1`,
  CHEAT_TAC);;

let alloc_clock = prove
 (`!xs s1 vs s2. (wordSem_alloc x names s1 = (vs,s2)) ==>
  wordSem_state_clock
                  s2 <= wordSem_state_clock s1 /\
                    wordSem_state_termdep s2 = wordSem_state_termdep
                    s1`,
  CHEAT_TAC);;

let sh_mem_set_var_clock = prove
 (`!v s1 v2 s2 res.
     (sh_mem_set_var res v s1 = (v2,s2)) ==> wordSem_state_clock
     s2 <= wordSem_state_clock s1 /\ wordSem_state_termdep s2 =
       wordSem_state_termdep s1`,
  CHEAT_TAC);;

let share_inst_clock = prove
 (`!op v ad s1 v1 s2.
     (share_inst op v ad s1 = (v2,s2)) ==> wordSem_state_clock
     s2 <= wordSem_state_clock s1 /\ wordSem_state_termdep s2 =
       wordSem_state_termdep s1`,
  CHEAT_TAC);;

(* [local] *)
let inst_clock = prove
 (`wordSem_inst i s = SOME s2 ==> wordSem_state_clock s2 <=
  wordSem_state_clock s /\ wordSem_state_termdep s2 =
  wordSem_state_termdep s`,
  CHEAT_TAC);;

(* evaluate_clock *)
let wordSem_evaluate_clock = prove
 (`!xs s1 vs s2. (wordSem_evaluate (xs,s1) = (vs,s2)) ==>
  wordSem_state_clock
   s2 <= wordSem_state_clock s1 /\ wordSem_state_termdep s2 =
     wordSem_state_termdep s1`,
  CHEAT_TAC);;

(* fix_clock_evaluate[local] *)
let wordSem_fix_clock_evaluate = prove
 (`wordSem_fix_clock s (wordSem_evaluate (c1,s)) = wordSem_evaluate
  (c1,s)`,
  CHEAT_TAC);;

(* We store the theorems without fix_clock *)

(* HOL4 wordSemScript.sml:1367-1368: a theorem that HOL4 states as
   the value of an ML expression: evaluate_ind *)
(* HOL4 wordSemScript.sml:1369-1370: a theorem that HOL4 states as
   the value of an ML expression: evaluate_def *)

(* observational semantics *)

let wordSem_semantics_def = new_definition
  `wordSem_semantics (s:('a,'c,'ffi)wordSem_state) start' =
   (let prog = wordLang_Call NONE (SOME start') [0] NONE in
   if ?k. match FST (wordSem_evaluate (prog,wordSem_state_clock_fupd
     (K k) s)) with SOME (wordSem_Exception _159 _160) -> T | SOME
     (wordSem_Result ret _161) -> ~(ret = wordLang_Loc 1 0) | SOME
     wordSem_Error -> T | NONE -> T | _162 -> F then ffi_Fail else
     match some (\res.
       ?k t r outcome.
         wordSem_evaluate (prog,wordSem_state_clock_fupd (K k) s) =
           (r,t) /\
         (match r with (SOME (wordSem_FinalFFI e)) -> outcome =
           ffi_FFI_outcome e | (SOME (wordSem_Result _163 _164)) ->
           outcome = ffi_Success | (SOME wordSem_NotEnoughSpace) ->
           outcome = ffi_Resource_limit_hit | _165 -> F) /\
         res = ffi_Terminate outcome (ffi_state_io_events
           (wordSem_state_ffi t))) with SOME res -> res | NONE ->
       ffi_Diverge
          (build_lprefix_lub
            (IMAGE (\k. fromList (ffi_state_io_events
              (wordSem_state_ffi
               (SND (wordSem_evaluate
                 (prog,wordSem_state_clock_fupd (K k) s)))))) UNIV)))`;;

let word_lang_safe_for_space_def = new_definition
  `word_lang_safe_for_space (s:('a,'c,'ffi)wordSem_state) start' =
     (let prog = wordLang_Call NONE (SOME start') [0] NONE in
       (!k res t. wordSem_evaluate (prog,wordSem_state_clock_fupd (K
         k) s) = (res,t) ==>
         (?max'. wordSem_state_stack_max t = SOME max' /\ max' <=
           wordSem_state_stack_limit t)))`;;

(* clean up *)

(* HOL4 wordSemScript.sml:1412: ML code, not ported *)
