(* ======================================================== *)
(*  stackSem: ported from HOL4's
    compiler/backend/semantics/stackSemScript.sml  *)
(* ======================================================== *)

(*
  The formal semantics of stackLang
*)

needs "compiler/backend/data_live.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/alignment.ml";;
needs "lib/balanced_map.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/byte.ml";;
needs "lib/integer_word.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;
(* HOL4 ancestors outside the port: (* for word_loc and word_cmp *) *)


let stackSem_result_INDUCT,stackSem_result_RECURSION = define_datatype
  "stackSem_result = stackSem_Result ('w word_loc) | \
   stackSem_Exception ('w word_loc) | stackSem_Break (num) | \
   stackSem_Continue (num) | stackSem_Halt ('w word_loc) | \
   stackSem_TimeOut | stackSem_FinalFFI (final_event) | \
   stackSem_Error";;
hol4_overload "Result" "stackSem_Result";;
hol4_overload "Exception" "stackSem_Exception";;
hol4_overload "Break" "stackSem_Break";;
hol4_overload "Continue" "stackSem_Continue";;
hol4_overload "Halt" "stackSem_Halt";;
hol4_overload "TimeOut" "stackSem_TimeOut";;
hol4_overload "FinalFFI" "stackSem_FinalFFI";;
hol4_overload "Error" "stackSem_Error";;

let bit_length_def = cake_define
  `bit_length w = (if w = (n2w 0) then (0:num) else bit_length (w >>>
  1) + 1)`;;

let filter_bitmap_def = cake_define
  `filter_bitmap x1 rs =
        match (x1,rs) with
          ([],rs) -> SOME ([],rs)
        | ((F :: bs),(r :: rs)) -> filter_bitmap bs rs
        | ((T :: bs),(r :: rs)) ->
        (match filter_bitmap bs rs with NONE -> NONE | SOME (ts,rs')
          -> SOME (r :: ts,rs'))
        | (_1,_2) -> NONE`;;

let map_bitmap_def = cake_define
  `map_bitmap x1 ts rs =
        match (x1,ts,rs) with
          ([],ts,rs) -> SOME ([],ts,rs)
        | ((F :: bs),ts,(r :: rs)) ->
        (match map_bitmap bs ts rs with NONE -> NONE | SOME
          (xs,ys,zs) -> SOME (r :: xs,ys,zs))
        | ((T :: bs),(t :: ts),(r :: rs)) ->
        (match map_bitmap bs ts rs with NONE -> NONE | SOME
          (xs,ys,zs) -> SOME (t :: xs,ys,zs))
        | (_3,_4,_5) -> NONE`;;

let read_bitmap_def = cake_define_list
  [`read_bitmap [] = NONE`;
   `read_bitmap ((w:'a word) :: ws) =
         (if word_msb w then
           match read_bitmap ws with NONE -> NONE | SOME bs -> SOME
             (GENLIST (\i. FAPPLY w i) (dimindex (:'a) - 1) ++ bs) else
           SOME (GENLIST (\i. FAPPLY w i) (bit_length w - 1)))`];;

let stackSem_state_FIELDS = define_record "stackSem_state"
  ["regs","(num,'a word_loc)fmap";
   "fp_regs","(num,word64)fmap";
   "store","(store_name,'a word_loc)fmap";
   "stack","('a word_loc) list";
   "stack_space","num";
   "memory","'a word->'a word_loc";
   "mdomain","'a word->bool";
   "sh_mdomain","'a word->bool";
   "bitmaps","('a word) list";
   "compile","'c->(num#'a stackLang_prog) list->(word8 list#'c) option";
   "compile_oracle","num->'c#(num#'a stackLang_prog) list#('a word) \
   list";
   "code_buffer","('a,8)buffer";
   "data_buffer","('a,'a)buffer";
   "gc_fun","('a word_loc) list#('a word->'a word_loc)#('a \
   word->bool)#(store_name,'a word_loc)fmap->(('a word_loc) list#('a \
   word->'a word_loc)#(store_name,'a word_loc)fmap) option";
   "use_stack","bool";
   "use_store","bool";
   "use_alloc","bool";
   "clock","num";
   "code","('a stackLang_prog) spt";
   "ffi","'ffi ffi_state";
   "ffi_save_regs","num->bool";
   "be","bool"];;
hol4_overload "regs" "stackSem_state_regs";;
hol4_overload "regs_fupd" "stackSem_state_regs_fupd";;
hol4_overload "fp_regs" "stackSem_state_fp_regs";;
hol4_overload "fp_regs_fupd" "stackSem_state_fp_regs_fupd";;
hol4_overload "state_store" "stackSem_state_store";;
hol4_overload "state_store_fupd" "stackSem_state_store_fupd";;
hol4_overload "stack" "stackSem_state_stack";;
hol4_overload "stack_fupd" "stackSem_state_stack_fupd";;
hol4_overload "state_memory" "stackSem_state_memory";;
hol4_overload "state_memory_fupd" "stackSem_state_memory_fupd";;
hol4_overload "state_mdomain" "stackSem_state_mdomain";;
hol4_overload "state_mdomain_fupd" "stackSem_state_mdomain_fupd";;
hol4_overload "state_sh_mdomain" "stackSem_state_sh_mdomain";;
hol4_overload "state_sh_mdomain_fupd" "stackSem_state_sh_mdomain_fupd";;
hol4_overload "compile" "stackSem_state_compile";;
hol4_overload "compile_fupd" "stackSem_state_compile_fupd";;
hol4_overload "compile_oracle" "stackSem_state_compile_oracle";;
hol4_overload "compile_oracle_fupd"
  "stackSem_state_compile_oracle_fupd";;
hol4_overload "state_code_buffer" "stackSem_state_code_buffer";;
hol4_overload "state_code_buffer_fupd"
  "stackSem_state_code_buffer_fupd";;
hol4_overload "state_data_buffer" "stackSem_state_data_buffer";;
hol4_overload "state_data_buffer_fupd"
  "stackSem_state_data_buffer_fupd";;
hol4_overload "state_gc_fun" "stackSem_state_gc_fun";;
hol4_overload "state_gc_fun_fupd" "stackSem_state_gc_fun_fupd";;
hol4_overload "state_clock" "stackSem_state_clock";;
hol4_overload "state_clock_fupd" "stackSem_state_clock_fupd";;
hol4_overload "state_code" "stackSem_state_code";;
hol4_overload "state_code_fupd" "stackSem_state_code_fupd";;
hol4_overload "state_ffi" "stackSem_state_ffi";;
hol4_overload "state_ffi_fupd" "stackSem_state_ffi_fupd";;
hol4_overload "be" "stackSem_state_be";;
hol4_overload "be_fupd" "stackSem_state_be_fupd";;

let mem_store_def = cake_define
  `stackSem_mem_store (addr':'a word) (w:'a word_loc)
  (s:('a,'c,'ffi)stackSem_state) =
     (if addr' IN state_mdomain s then
       SOME (state_memory_fupd (K ((addr' =+ w) (state_memory s)))
         s) else NONE)`;;
hol4_overload "mem_store" "stackSem_mem_store";;

let mem_load_def = cake_define
  `stackSem_mem_load (addr':'a word) (s:('a,'c,'ffi)stackSem_state) =
     (if addr' IN state_mdomain s then
       SOME (state_memory s addr') else NONE)`;;
hol4_overload "mem_load" "stackSem_mem_load";;

let dec_clock_def = cake_define
  `stackSem_dec_clock (s:('a,'c,'ffi)stackSem_state) =
  state_clock_fupd (K (state_clock s - 1)) s`;;
hol4_overload "dec_clock" "stackSem_dec_clock";;

let word_exp_def = cake_define_list
  [`stackSem_word_exp s (wordLang_Const w) = SOME w`;
   `stackSem_word_exp s (wordLang_Var v) =
         (match FLOOKUP (stackSem_state_regs s) v with SOME
           (wordLang_Word w) -> SOME w | _12 -> NONE)`;
   `stackSem_word_exp s (wordLang_Lookup name) =
         (match FLOOKUP (state_store s) name with SOME
           (wordLang_Word w) -> SOME w | _13 -> NONE)`;
   `stackSem_word_exp s (wordLang_Load addr') =
         (match stackSem_word_exp s addr' with SOME w -> (match
           mem_load w s with SOME (wordLang_Word w) -> SOME w | _18
           -> NONE) | _19 -> NONE)`;
   `stackSem_word_exp s (wordLang_Op op wexps) =
         (let ws = MAP (stackSem_word_exp s) wexps in
           if EVERY IS_SOME ws then wordLang_word_op op (MAP THE
             ws) else NONE)`;
   `stackSem_word_exp s (wordLang_Shift sh wexp wexp1) =
         (match (stackSem_word_exp s wexp,stackSem_word_exp s
           wexp1) with (SOME w,SOME w1) -> word_sh sh w (w2n w1) |
           _22 -> NONE)`];;
hol4_overload "word_exp" "stackSem_word_exp";;

let get_var_def = cake_define
  `stackSem_get_var v (s:('a,'c,'ffi)stackSem_state) = FLOOKUP
  (stackSem_state_regs s) v`;;
hol4_overload "get_var" "stackSem_get_var";;

let get_vars_def = cake_define_list
  [`stackSem_get_vars [] s = SOME []`;
   `stackSem_get_vars (v :: vs) s =
         (match get_var v s with NONE -> NONE | SOME x ->
           (match stackSem_get_vars vs s with NONE -> NONE | SOME
           xs -> SOME (x :: xs)))`];;
hol4_overload "get_vars" "stackSem_get_vars";;

let get_fp_var_def = cake_define
  `stackSem_get_fp_var v (s:('a,'c,'ffi)stackSem_state) = FLOOKUP
  (fp_regs s) v`;;
hol4_overload "get_fp_var" "stackSem_get_fp_var";;

let set_var_def = cake_define
  `stackSem_set_var v x (s:('a,'c,'ffi)stackSem_state) =
     (stackSem_state_regs_fupd (K (stackSem_state_regs s |+
       (v,x))) s)`;;
hol4_overload "set_var" "stackSem_set_var";;

let set_fp_var_def = cake_define
  `stackSem_set_fp_var v x (s:('a,'c,'ffi)stackSem_state) =
     (fp_regs_fupd (K (fp_regs s |+ (v,x))) s)`;;
hol4_overload "set_fp_var" "stackSem_set_fp_var";;

let set_store_def = cake_define
  `stackSem_set_store v x (s:('a,'c,'ffi)stackSem_state) =
  (state_store_fupd (K (state_store s |+ (v,x))) s)`;;
hol4_overload "set_store" "stackSem_set_store";;

let empty_env_def = cake_define
  `stackSem_empty_env (s:('a,'c,'ffi)stackSem_state) = stack_fupd (K
  []) (stackSem_state_regs_fupd (K FEMPTY) s)`;;
hol4_overload "empty_env" "stackSem_empty_env";;

let sh_mem_store_def = cake_define
  `(stackSem_sh_mem_store r (a:'a word)
  (s:('a,'c,'ffi)stackSem_state):('a stackSem_result)
  option#('a,'c,'ffi)stackSem_state) =
   (match get_var r s with
      SOME (wordLang_Word w) ->
        (if a IN state_sh_mdomain s then
          (match call_FFI (state_ffi s) (SharedMem MappedWrite) [(n2w
            0):word8]
                         (word_to_bytes w F ++ word_to_bytes a F)
                           with
             FFI_final outcome -> (SOME (FinalFFI outcome),s) |
               FFI_return new_ffi new_bytes -> (NONE,state_ffi_fupd
               (K new_ffi) s)) else (SOME Error,s)) | _23 -> (SOME
               Error,s))`;;
hol4_overload "sh_mem_store" "stackSem_sh_mem_store";;

let sh_mem_load_def = cake_define
  `(stackSem_sh_mem_load r (a:'a word)
  (s:('a,'c,'ffi)stackSem_state):('a stackSem_result)
  option#('a,'c,'ffi)stackSem_state) =
   (if a IN state_sh_mdomain s then
     (match call_FFI (state_ffi s) (SharedMem MappedRead) [(n2w
       0):word8]
                    (word_to_bytes a F) with
        FFI_final outcome -> (SOME (FinalFFI outcome),s) | FFI_return
          new_ffi new_bytes ->
          (NONE,state_ffi_fupd (K new_ffi) (stackSem_state_regs_fupd
            (K (stackSem_state_regs s |+ (r,wordLang_Word (word_of_bytes
            F (n2w 0) new_bytes))))
           s))) else (SOME Error,s))`;;
hol4_overload "sh_mem_load" "stackSem_sh_mem_load";;

let sh_mem_store_byte_def = cake_define
  `(stackSem_sh_mem_store_byte r (a:'a word)
  (s:('a,'c,'ffi)stackSem_state):('a stackSem_result)
  option#('a,'c,'ffi)stackSem_state) =
   (match get_var r s with
      SOME (wordLang_Word w) ->
        (if byte_align a IN state_sh_mdomain s then
          (match call_FFI (state_ffi s) (SharedMem MappedWrite) [(n2w
            1):word8]
                         ([get_byte (n2w 0) w F] ++ word_to_bytes a
                           F) with
             FFI_final outcome -> (SOME (FinalFFI outcome),s) |
               FFI_return new_ffi new_bytes -> (NONE,state_ffi_fupd
               (K new_ffi) s)) else (SOME Error,s)) | _24 -> (SOME
               Error,s))`;;
hol4_overload "sh_mem_store_byte" "stackSem_sh_mem_store_byte";;

let sh_mem_store16_def = cake_define
  `(stackSem_sh_mem_store16 r (a:'a word)
  (s:('a,'c,'ffi)stackSem_state):('a stackSem_result)
  option#('a,'c,'ffi)stackSem_state) =
   (match get_var r s with
      SOME (wordLang_Word w) ->
        (if byte_align a IN state_sh_mdomain s then
          (match call_FFI (state_ffi s) (SharedMem MappedWrite) [(n2w
            2):word8]
                         (TAKE 2 (word_to_bytes w F) ++ word_to_bytes
                           a F) with
             FFI_final outcome -> (SOME (FinalFFI outcome),s) |
               FFI_return new_ffi new_bytes -> (NONE,state_ffi_fupd
               (K new_ffi) s)) else (SOME Error,s)) | _25 -> (SOME
               Error,s))`;;
hol4_overload "sh_mem_store16" "stackSem_sh_mem_store16";;

let sh_mem_store32_def = cake_define
  `(stackSem_sh_mem_store32 r (a:'a word)
  (s:('a,'c,'ffi)stackSem_state):('a stackSem_result)
  option#('a,'c,'ffi)stackSem_state) =
   (match get_var r s with
      SOME (wordLang_Word w) ->
        (if byte_align a IN state_sh_mdomain s then
          (match call_FFI (state_ffi s) (SharedMem MappedWrite) [(n2w
            4):word8]
                         (TAKE 4 (word_to_bytes w F) ++ word_to_bytes
                           a F) with
             FFI_final outcome -> (SOME (FinalFFI outcome),s) |
               FFI_return new_ffi new_bytes -> (NONE,state_ffi_fupd
               (K new_ffi) s)) else (SOME Error,s)) | _26 -> (SOME
               Error,s))`;;
hol4_overload "sh_mem_store32" "stackSem_sh_mem_store32";;

let sh_mem_load_byte_def = cake_define
  `(stackSem_sh_mem_load_byte r (a:'a word)
  (s:('a,'c,'ffi)stackSem_state):('a stackSem_result)
  option#('a,'c,'ffi)stackSem_state) =
   (if byte_align a IN state_sh_mdomain s then
     (match call_FFI (state_ffi s) (SharedMem MappedRead) [(n2w
       1):word8] (word_to_bytes a F) with
        FFI_final outcome -> (SOME (FinalFFI outcome),s) | FFI_return
          new_ffi new_bytes ->
          (NONE,state_ffi_fupd (K new_ffi) (stackSem_state_regs_fupd
            (K (stackSem_state_regs s |+ (r,wordLang_Word (word_of_bytes
            F (n2w 0) new_bytes))))
           s))) else (SOME Error,s))`;;
hol4_overload "sh_mem_load_byte" "stackSem_sh_mem_load_byte";;

let sh_mem_load16_def = cake_define
  `(stackSem_sh_mem_load16 r (a:'a word)
  (s:('a,'c,'ffi)stackSem_state):('a stackSem_result)
  option#('a,'c,'ffi)stackSem_state) =
   (if byte_align a IN state_sh_mdomain s then
     (match call_FFI (state_ffi s) (SharedMem MappedRead) [(n2w
       2):word8] (word_to_bytes a F) with
        FFI_final outcome -> (SOME (FinalFFI outcome),s) | FFI_return
          new_ffi new_bytes ->
          (NONE,state_ffi_fupd (K new_ffi) (stackSem_state_regs_fupd
            (K (stackSem_state_regs s |+ (r,wordLang_Word (word_of_bytes
            F (n2w 0) new_bytes))))
           s))) else (SOME Error,s))`;;
hol4_overload "sh_mem_load16" "stackSem_sh_mem_load16";;

let sh_mem_load32_def = cake_define
  `(stackSem_sh_mem_load32 r (a:'a word)
  (s:('a,'c,'ffi)stackSem_state):('a stackSem_result)
  option#('a,'c,'ffi)stackSem_state) =
   (if byte_align a IN state_sh_mdomain s then
     (match call_FFI (state_ffi s) (SharedMem MappedRead) [(n2w
       4):word8] (word_to_bytes a F) with
        FFI_final outcome -> (SOME (FinalFFI outcome),s) | FFI_return
          new_ffi new_bytes ->
          (NONE,state_ffi_fupd (K new_ffi) (stackSem_state_regs_fupd
            (K (stackSem_state_regs s |+ (r,wordLang_Word (word_of_bytes
            F (n2w 0) new_bytes))))
           s))) else (SOME Error,s))`;;
hol4_overload "sh_mem_load32" "stackSem_sh_mem_load32";;

let sh_mem_op_def = cake_define_list
  [`sh_mem_op (Load:memop) r ad (s:('a,'c,'ffi)stackSem_state) =
  sh_mem_load r ad s`;
   `sh_mem_op (Store:memop) r ad s = sh_mem_store r ad s`;
   `sh_mem_op asm_Load8 r ad s = sh_mem_load_byte r ad s`;
   `sh_mem_op asm_Store8 r ad s = sh_mem_store_byte r ad s`;
   `sh_mem_op asm_Load16 r ad s = sh_mem_load16 r ad s`;
   `sh_mem_op asm_Store16 r ad s = sh_mem_store16 r ad s`;
   `sh_mem_op asm_Load32 r ad s = sh_mem_load32 r ad s`;
   `sh_mem_op asm_Store32 r ad s = sh_mem_store32 r ad s`];;

let full_read_bitmap_def = cake_define
  `full_read_bitmap bitmaps x2 =
        match x2 with
          wordLang_Word w ->
        (if w = (n2w 0) then NONE else read_bitmap (DROP (w2n (w -
          (n2w 1))) bitmaps))
        | _27 -> NONE`;;

let enc_stack_def = cake_define_list
  [`stackSem_enc_stack bitmaps [] = NONE`;
   `stackSem_enc_stack bitmaps (w :: ws) =
         (if w = wordLang_Word (n2w 0) then (if ws = [] then SOME []
           else NONE) else
           match full_read_bitmap bitmaps w with NONE -> NONE | SOME
             bs ->
              (match filter_bitmap bs ws with NONE -> NONE | SOME
                (ts,ws') ->
                  (match stackSem_enc_stack bitmaps ws' with
                    NONE -> NONE | SOME rs -> SOME (ts ++ rs))))`];;
hol4_overload "enc_stack" "stackSem_enc_stack";;

let dec_stack_def = cake_define_list
  [`stackSem_dec_stack bitmaps _28 [] = NONE`;
   `stackSem_dec_stack bitmaps ts (w :: ws) =
        (if w = wordLang_Word (n2w 0) then (if ts = [] /\ ws = []
          then SOME [wordLang_Word (n2w 0)] else NONE) else
         match full_read_bitmap bitmaps w with NONE -> NONE | SOME
           bs ->
            (match map_bitmap bs ts ws with NONE -> NONE | SOME
              (hd,ts',ws') ->
               (match stackSem_dec_stack bitmaps ts' ws' with
                 NONE -> NONE | SOME rest -> SOME ([w] ++ hd ++
                 rest))))`];;
hol4_overload "dec_stack" "stackSem_dec_stack";;

let gc_def = cake_define
  `stackSem_gc s =
     (if LENGTH (stack s) < stackSem_state_stack_space s then NONE
       else
       let unused = TAKE (stackSem_state_stack_space s) (stack s) in
       let stack' = DROP (stackSem_state_stack_space s) (stack s) in
         match enc_stack (stackSem_state_bitmaps s) (DROP
           (stackSem_state_stack_space s) (stack s)) with NONE -> NONE |
           SOME wl_list ->
           (match state_gc_fun s (wl_list,state_memory
             s,state_mdomain s,state_store s) with NONE -> NONE | SOME
             (wl,m,st) ->
            (match dec_stack (stackSem_state_bitmaps s) wl stack'
              with NONE -> NONE | SOME stack' ->
                 SOME (state_memory_fupd (K m)
                   (stackSem_state_regs_fupd (K FEMPTY)
                   (state_store_fupd (K st) (stack_fupd (K (unused ++
                   stack')) s)))))))`;;
hol4_overload "gc" "stackSem_gc";;

let has_space_def = cake_define
  `stackSem_has_space wl store =
     (match (wl,FLOOKUP store NextFree,FLOOKUP store TriggerGC)
       with (wordLang_Word w,SOME (wordLang_Word n),SOME
       (wordLang_Word l)) -> SOME (w2n w <= w2n (l - n)) | _29 ->
       NONE)`;;
hol4_overload "has_space" "stackSem_has_space";;

let alloc_def = cake_define
  `stackSem_alloc (w:'a word) (s:('a,'c,'ffi)stackSem_state) =
       (match gc (set_store AllocSize (wordLang_Word w) s) with NONE
         -> (SOME Error,s) | SOME s ->
          (match FLOOKUP (state_store s) AllocSize with NONE -> (SOME
            Error,s) | SOME w ->
            (match has_space w (state_store s) with NONE -> (SOME
              Error,s) | SOME T ->
                         (NONE,s) | SOME F ->
                         (SOME (Halt (wordLang_Word ((n2w 1):'a
                           word))),stackSem_empty_env s))))`;;
hol4_overload "alloc" "stackSem_alloc";;

let assign_def = cake_define
  `stackSem_assign reg exp s =
     (match word_exp s exp with NONE -> NONE | SOME w -> SOME
       (set_var reg (wordLang_Word w) s))`;;
hol4_overload "assign" "stackSem_assign";;

let inst_def = cake_define
  `stackSem_inst i (s:('a,'c,'ffi)stackSem_state) =
     (match i with Skip -> SOME s | Const reg w -> assign reg (Const
       w) s | Arith (asm_Binop bop r1 r2 ri) ->
         (if bop = Or /\ ri = Reg r2 then
           match FLOOKUP (stackSem_state_regs s) r2 with NONE -> NONE
             | SOME w -> SOME (set_var r1 w s) else
           assign r1
             (wordLang_Op bop [Var r2; match ri with Reg r3 -> Var r3
               | Imm w -> Const w]) s) | Arith (Shift sh r1 r2 ri) ->
         assign r1
           (Shift sh (Var r2) (match ri with Reg r3 -> Var r3 | Imm w
             -> Const w)) s | Arith (Div r1 r2 r3) ->
        (let vs = get_vars [r3; r2] s in
        match vs with
        SOME [wordLang_Word q; wordLang_Word w2] ->
          (if ~(q = (n2w 0)) then
            SOME (set_var r1 (wordLang_Word (w2 / q)) s) else NONE) |
              _30 -> NONE) | Arith (asm_AddCarry r1 r2 r3 r4) ->
         (let vs = get_vars [r2; r3; r4] s in
         match vs with
         SOME [wordLang_Word l; wordLang_Word r; wordLang_Word c] ->
           (let res = w2n l + w2n r + (if c = ((n2w 0):'a word) then
             0 else 1) in
             SOME (set_var r4 (wordLang_Word (if dimword (:'a) <= res
               then ((n2w 1):'a word) else (n2w 0)))
                  (set_var r1 (wordLang_Word (n2w res)) s))) | _31 ->
                    NONE) | Arith (asm_AddOverflow r1 r2 r3 r4) ->
         (let vs = get_vars [r2; r3] s in
         match vs with
         SOME [wordLang_Word w2; wordLang_Word w3] ->
           SOME (set_var r4 (wordLang_Word (if ~(w2i (w2 + w3) = w2i
             w2 + w2i w3) then (n2w 1) else (n2w 0)))
                  (set_var r1 (wordLang_Word (w2 + w3)) s)) | _32 ->
                    NONE) | Arith (asm_SubOverflow r1 r2 r3 r4) ->
         (let vs = get_vars [r2; r3] s in
         match vs with
         SOME [wordLang_Word w2; wordLang_Word w3] ->
           SOME (set_var r4 (wordLang_Word (if ~(w2i (w2 - w3) = w2i
             w2 - w2i w3) then (n2w 1) else (n2w 0)))
                  (set_var r1 (wordLang_Word (w2 - w3)) s)) | _33 ->
                    NONE) | Arith (asm_LongMul r1 r2 r3 r4) ->
         (let vs = get_vars [r3; r4] s in
         match vs with
         SOME [wordLang_Word w3; wordLang_Word w4] ->
          (let r = w2n w3 * w2n w4 in
            SOME (set_var r2 (wordLang_Word (n2w r)) (set_var r1
              (wordLang_Word (n2w (r DIV dimword (:'a)))) s))) | _34 ->
              NONE) | Arith (asm_LongDiv r1 r2 r3 r4 r5) ->
        (let vs = get_vars [r3; r4; r5] s in
        match vs with
        SOME [wordLang_Word w3; wordLang_Word w4; wordLang_Word w5]
          ->
          (let n = w2n w3 * dimword (:'a) + w2n w4 in
          let d = w2n w5 in
          let q = n DIV d in
          if (~(d = 0) /\ q < dimword (:'a)) then
            SOME (set_var r1 (wordLang_Word (n2w q)) (set_var r2
              (wordLang_Word (n2w (n MOD d))) s)) else NONE) | _35 ->
              NONE) | asm_Mem Load r (Addr a w) ->
        (match word_exp s (wordLang_Op Add [Var a; Const w]) with
          NONE -> NONE | SOME w ->
             (match mem_load w s with NONE -> NONE | SOME w -> SOME
               (set_var r w s))) | asm_Mem asm_Load8 r (Addr a w) ->
        (match word_exp s (wordLang_Op Add [Var a; Const w]) with
          SOME w ->
            (match mem_load_byte_aux (state_memory s) (state_mdomain
              s) (be s) w with NONE -> NONE | SOME w -> SOME (set_var r
              (wordLang_Word (w2w w)) s)) | _36 -> NONE) | asm_Mem
              asm_Load16 _37 _38 -> NONE | asm_Mem asm_Load32 r (Addr a
              w) ->
        (match word_exp s (wordLang_Op Add [Var a; Const w]) with
          SOME w ->
            (match mem_load_32 (state_memory s) (state_mdomain s) (be
              s) w with NONE -> NONE | SOME w -> SOME (set_var r
              (wordLang_Word (w2w w)) s)) | _39 -> NONE) | asm_Mem Store
              r (Addr a w) ->
        (match (word_exp s (wordLang_Op Add [Var a; Const w]),get_var
          r s) with (SOME a,SOME w) ->
             (match mem_store a w s with SOME s1 -> SOME s1 | NONE ->
               NONE) | _40 -> NONE) | asm_Mem asm_Store8 r (Addr a w) ->
        (match (word_exp s (wordLang_Op Add [Var a; Const w]),get_var
          r s) with (SOME a,SOME (wordLang_Word w)) ->
             (match mem_store_byte_aux (state_memory s)
               (state_mdomain s) (be s) a (w2w w) with SOME new_m ->
               SOME (state_memory_fupd (K new_m) s) | NONE -> NONE) |
               _41 -> NONE) | asm_Mem asm_Store16 _42 _43 -> NONE |
               asm_Mem asm_Store32 r (Addr a w) ->
        (match (word_exp s (wordLang_Op Add [Var a; Const w]),get_var
          r s) with (SOME a,SOME (wordLang_Word w)) ->
             (match mem_store_32 (state_memory s) (state_mdomain s)
               (be s) a (w2w w) with SOME new_m -> SOME
               (state_memory_fupd (K new_m) s) | NONE -> NONE) | _44 ->
               NONE) | asm_FP (FPLess r d1 d2) ->
       (match (get_fp_var d1 s,get_fp_var d2 s) with (SOME f1,SOME
         f2) ->
         SOME (set_var r
           (wordLang_Word (if fp64_lessThan f1 f2 then (n2w 1) else
             (n2w 0))) s) | _45 -> NONE) | asm_FP (FPLessEqual r d1 d2)
             ->
       (match (get_fp_var d1 s,get_fp_var d2 s) with (SOME f1,SOME
         f2) ->
         SOME (set_var r
           (wordLang_Word (if fp64_lessEqual f1 f2 then (n2w 1) else
             (n2w 0))) s) | _46 -> NONE) | asm_FP (FPEqual r d1 d2) ->
       (match (get_fp_var d1 s,get_fp_var d2 s) with (SOME f1,SOME
         f2) ->
         SOME (set_var r
           (wordLang_Word (if fp64_equal f1 f2 then (n2w 1) else (n2w
             0))) s) | _47 -> NONE) | asm_FP (FPMov d1 d2) ->
       (match get_fp_var d2 s with SOME f ->
         SOME (set_fp_var d1 f s) | _48 -> NONE) | asm_FP (FPAbs d1
           d2) ->
       (match get_fp_var d2 s with SOME f ->
         SOME (set_fp_var d1 (fp64_abs f) s) | _49 -> NONE) | asm_FP
           (FPNeg d1 d2) ->
       (match get_fp_var d2 s with SOME f ->
         SOME (set_fp_var d1 (fp64_negate f) s) | _50 -> NONE) |
           asm_FP (FPSqrt d1 d2) ->
       (match get_fp_var d2 s with SOME f ->
         SOME (set_fp_var d1 (fp64_sqrt roundTiesToEven f) s) | _51
           -> NONE) | asm_FP (FPAdd d1 d2 d3) ->
       (match (get_fp_var d2 s,get_fp_var d3 s) with (SOME f1,SOME
         f2) ->
         SOME (set_fp_var d1 (fp64_add roundTiesToEven f1 f2) s) |
           _52 -> NONE) | asm_FP (FPSub d1 d2 d3) ->
       (match (get_fp_var d2 s,get_fp_var d3 s) with (SOME f1,SOME
         f2) ->
         SOME (set_fp_var d1 (fp64_sub roundTiesToEven f1 f2) s) |
           _53 -> NONE) | asm_FP (FPMul d1 d2 d3) ->
       (match (get_fp_var d2 s,get_fp_var d3 s) with (SOME f1,SOME
         f2) ->
         SOME (set_fp_var d1 (fp64_mul roundTiesToEven f1 f2) s) |
           _54 -> NONE) | asm_FP (FPDiv d1 d2 d3) ->
       (match (get_fp_var d2 s,get_fp_var d3 s) with (SOME f1,SOME
         f2) ->
         SOME (set_fp_var d1 (fp64_div roundTiesToEven f1 f2) s) |
           _55 -> NONE) | asm_FP (FPFma d1 d2 d3) ->
       (match (get_fp_var d1 s,get_fp_var d2 s,get_fp_var d3 s) with
         (SOME f1,SOME f2,SOME f3) ->
         SOME (set_fp_var d1 (fpfma f1 f2 f3) s) | _56 -> NONE) |
           asm_FP (FPMovToReg r1 r2 d) ->
       (match get_fp_var d s with SOME v ->
         (if dimindex (:'a) = 64 then
           SOME (set_var r1 (wordLang_Word (w2w v)) s) else
           SOME (set_var r2 (wordLang_Word ((63 >< 32) v)) (set_var
             r1 (wordLang_Word ((31 >< 0) v)) s))) | _57 -> NONE) |
             asm_FP (FPMovFromReg d r1 r2) ->
       (if dimindex (:'a) = 64 then
         match get_var r1 s with
           SOME (wordLang_Word w1) -> SOME (set_fp_var d (w2w w1) s)
             | _58 -> NONE else
         match (get_var r1 s,get_var r2 s) with
           (SOME (wordLang_Word w1),SOME (wordLang_Word w2)) -> SOME
             (set_fp_var d (w2 @@ w1) s) | _59 -> NONE) | asm_FP
             (FPToInt d1 d2) ->
       (match get_fp_var d2 s with
         NONE -> NONE | SOME f ->
       (match fp64_to_int roundTiesToEven f with
         NONE -> NONE | SOME i ->
         (let w = (i2w i:word32) in
         if w2i w = i then
           (if dimindex (:'a) = 64 then
              SOME (set_fp_var d1 (w2w w) s) else
            match get_fp_var (d1 DIV 2) s with
              NONE -> NONE | SOME f ->
              (let (h,l) = (if ODD d1 then (63,32) else (31,0)) in
                   SOME (set_fp_var (d1 DIV 2) (bit_field_insert h l
                     w f) s))) else
           NONE))) | asm_FP (FPFromInt d1 d2) ->
       (if dimindex (:'a) = 64 then
         match get_fp_var d2 s with SOME f ->
           (let i = w2i ((31 >< 0) f:word32) in
             SOME (set_fp_var d1 (int_to_fp64 roundTiesToEven i) s))
               | NONE -> NONE else
         match get_fp_var (d2 DIV 2) s with SOME v ->
           (let i = w2i (if ODD d2 then (63 >< 32) v else (31 >< 0)
             v:'a word) in
             SOME (set_fp_var d1 (int_to_fp64 roundTiesToEven i)
               s)) | NONE -> NONE | _60 -> NONE))`;;
hol4_overload "inst" "stackSem_inst";;

let get_var_imm_def = cake_define_list
  [`stackSem_get_var_imm ((Reg n):'a asm_reg_imm) s = get_var n s`;
   `stackSem_get_var_imm (Imm w) s = SOME (wordLang_Word w)`];;
hol4_overload "get_var_imm" "stackSem_get_var_imm";;

let find_code_def = cake_define_list
  [`stackSem_find_code (INL p) regs' code = sptree_lookup p code`;
   `stackSem_find_code (INR r) regs' code =
         (match FLOOKUP regs' r with
           SOME (Loc loc 0) -> sptree_lookup loc code | other
             -> NONE)`];;
hol4_overload "find_code" "stackSem_find_code";;

let fix_clock_def = cake_define
  `stackSem_fix_clock s (res,s1) = (res,state_clock_fupd (K (MIN
  (state_clock s) (state_clock s1))) s1)`;;
hol4_overload "fix_clock" "stackSem_fix_clock";;

let STOP_def = cake_define
  `stackSem_STOP x = x`;;
hol4_overload "STOP" "stackSem_STOP";;

let get_labels_def = cake_define
  `stackSem_get_labels x1 =
        match x1 with
          stackLang_Seq p1 p2 -> stackSem_get_labels p1 UNION
            stackSem_get_labels p2
        | (If _61 _62 _63 p1 p2) -> stackSem_get_labels p1 UNION
          stackSem_get_labels p2
        | (Loop p) -> stackSem_get_labels p
        | (Call ret _64 handler) ->
        (match ret with NONE -> {} | SOME (r,_65,l1,l2) -> (l1,l2)
          INSERT (stackSem_get_labels r UNION
             (match handler with NONE -> {} | SOME (r,l1,l2) ->
               (l1,l2) INSERT stackSem_get_labels r)))
        | (Halt _66) -> {}
        | _67 -> {}`;;
hol4_overload "get_labels" "stackSem_get_labels";;

let loc_check_def = cake_define
  `loc_check code (l1,l2) <=>
     (l2 = 0 /\ l1 IN domain code) \/
     (?n e. sptree_lookup n code = SOME e /\ (l1,l2) IN
       stackSem_get_labels e)`;;

let copy_words_for_pattern_def = cake_define
  `copy_words_for_pattern (pattern:'a word) (i:num) (a:'a word) (off:'a
  word) bs dm m =
     (if pattern = (n2w 0) then NONE else
     if pattern = (n2w 1) then SOME (i,a,m) else
       if a IN dm /\ i < LENGTH bs then
         let b = FAPPLY pattern 0 in
         let w = EL i bs in
         let m = (a =+ wordLang_Word (if b then w + off else w)) m in
           copy_words_for_pattern
             (pattern >>> 1) (i + 1) (a + bytes_in_word) off bs dm
               m else NONE)`;;

(* HOL4 termination: \\ rw [] \\ imp_res_tac
   copy_words_for_pattern_LESS_EQ \\ fs [] *)
let copy_words_def = cake_define_wf
  `MEASURE (\(i,a,f,bs,dm,m). LENGTH bs - i)`
  `copy_words i a off bs dm m =
     (if LENGTH bs <= i then NONE else
       let pattern = EL i bs in
         match copy_words_for_pattern pattern (i + 1) a off bs dm m
           with NONE -> NONE | SOME (i1,a1,m1) ->
             (if word_msb pattern then copy_words i1 a1 off bs dm m1
               else
               SOME (a1,m1)))`;;

let unset_var_def = cake_define
  `stackSem_unset_var v (s:('a,'c,'ffi)stackSem_state) =
  stackSem_state_regs_fupd (K (stackSem_state_regs s \\ v)) s`;;
hol4_overload "unset_var" "stackSem_unset_var";;

let store_const_sem_def = cake_define
  `store_const_sem t1 t2 (s:('a,'c,'ffi)stackSem_state) =
     (if ~ALL_DISTINCT [0; 1; 2; 3; t1; t2] then (SOME Error,s) else
       match (get_var 1 s,get_var 2 s,get_var 3 s) with (SOME
         (wordLang_Word i),SOME (wordLang_Word a),SOME (wordLang_Word
         off)) ->
           (match copy_words (w2n i) a off (stackSem_state_bitmaps s)
             (state_mdomain s) (state_memory s) with NONE -> (SOME
             Error,s) | SOME (a,m) -> (NONE,
               (if stackSem_state_use_alloc s then unset_var 0 else
                 I)
                 (set_var t1 (wordLang_Word (n2w 1)) (set_var t2
                   (wordLang_Word (n2w 1))
                   (set_var 1 (wordLang_Word (n2w 1)) (set_var 2
                     (wordLang_Word a) (state_memory_fupd (K m)
                     s))))))) | _68 -> (SOME Error,s))`;;

let check_store_consts_opt_def = cake_define_list
  [`check_store_consts_opt t1 t2 NONE _69 = T`;
   `check_store_consts_opt t1 t2 (SOME n) c =
      (sptree_lookup n c = SOME (Seq (StoreConsts t1 t2 NONE)
        (Return 0)))`];;

let dest_Seq_def = cake_define
  `stackSem_dest_Seq x1 =
      match x1 with
        wordLang_Seq p1 p2 -> SOME (p1,(p2:'a stackLang_prog))
      | _70 -> NONE`;;
hol4_overload "dest_Seq" "stackSem_dest_Seq";;

let bad_fun_return_def = cake_define
  `stackSem_bad_fun_return x1 =
      match x1 with
        NONE -> T
      | (SOME (Break _71)) -> T
      | (SOME (Continue _72)) -> T
      | _73 -> F`;;
hol4_overload "bad_fun_return" "stackSem_bad_fun_return";;

let cont_loop_def = cake_define
  `stackSem_cont_loop x1 =
      match x1 with
        NONE -> T
      | (SOME (Continue n)) -> (n = 0)
      | _74 -> F`;;
hol4_overload "cont_loop" "stackSem_cont_loop";;

let exit_loop_def = cake_define
  `stackSem_exit_loop res =
      match res with
        SOME (Break n) -> (if n = 0 then NONE else SOME (Break (n -
          1)))
      | (SOME (Continue n)) -> SOME (Continue (n - 1))
      | res -> res`;;
hol4_overload "exit_loop" "stackSem_exit_loop";;

let evaluate_def = cake_define_list
  [`stackSem_evaluate ((Skip:'a stackLang_prog),s) =
  (NONE,(s:('a,'c,'ffi)stackSem_state))`;
   `stackSem_evaluate (stackSem_Halt v,s) =
         (match get_var v s with SOME w -> (SOME (Halt
           w),stackSem_empty_env s) | NONE -> (SOME Error,s))`;
   `stackSem_evaluate (wordLang_Alloc n,s) =
         (if ~stackSem_state_use_alloc s then (SOME Error,s) else
         match get_var n s with SOME (wordLang_Word w) -> alloc w
           s | _79 -> (SOME Error,s))`;
   `stackSem_evaluate (wordLang_StoreConsts t1 t2 stub_opt,s) =
         (if ~stackSem_state_use_store s then (SOME Error,s) else
         if ~stackSem_state_use_alloc s /\ IS_SOME stub_opt then
           (SOME Error,s) else
         if ~check_store_consts_opt t1 t2 stub_opt (state_code s)
           then (SOME Error,s) else
           store_const_sem t1 t2 s)`;
   `stackSem_evaluate (wordLang_Inst i,s) =
         (match inst i s with SOME s1 -> (NONE,s1) | NONE ->
           (SOME Error,s))`;
   `stackSem_evaluate (wordLang_Get v name,s) =
         (if ~stackSem_state_use_store s then (SOME Error,s) else
         match FLOOKUP (state_store s) name with SOME x ->
           (NONE,set_var v x s) | NONE -> (SOME Error,s))`;
   `stackSem_evaluate (wordLang_Set name v,s) =
         (if ~stackSem_state_use_store s then (SOME Error,s) else
         match get_var v s with SOME w -> (NONE,set_store name w
           s) | NONE -> (SOME Error,s))`;
   `stackSem_evaluate (wordLang_OpCurrHeap binop v src,s) =
         (if ~stackSem_state_use_store s then (SOME Error,s) else
         match word_exp s (wordLang_Op binop [Var src;
           wordLang_Lookup CurrHeap]) with SOME w -> (NONE,set_var v
           (wordLang_Word w) s) | _82 -> (SOME Error,s))`;
   `stackSem_evaluate (wordLang_Tick,s) =
         (if state_clock s = 0 then (SOME
           TimeOut,stackSem_empty_env s) else (NONE,dec_clock s))`;
   `stackSem_evaluate (wordLang_Seq c1 c2,s) =
         (let (res,s1) = fix_clock s (stackSem_evaluate (c1,s)) in
           if res = NONE then stackSem_evaluate (c2,s1) else
             (res,s1))`;
   `stackSem_evaluate (wordLang_Return n,s) =
         (match get_var n s with SOME (Loc l1 l2) -> (SOME
           (Result (Loc l1 l2)),s) | _85 -> (SOME Error,s))`;
   `stackSem_evaluate (wordLang_Raise n,s) =
         (match get_var n s with SOME (Loc l1 l2) -> (SOME
           (Exception (Loc l1 l2)),s) | _88 -> (SOME Error,s))`;
   `stackSem_evaluate (stackSem_Break n,s) = (SOME ((Break n:'w
  stackSem_result)),s)`;
   `stackSem_evaluate (stackSem_Continue n,s) = (SOME ((Continue n:'w
  stackSem_result)),s)`;
   `stackSem_evaluate (wordLang_If cmp r1 ri c1 c2,s) =
        (match (get_var r1 s,get_var_imm ri s) with (SOME x,SOME y)
          ->
         (match wordSem_word_cmp cmp x y with SOME T ->
           stackSem_evaluate (c1,s) | SOME F -> stackSem_evaluate
           (c2,s) | NONE -> (SOME Error,s)) | _91 -> (SOME Error,s))`;
   `stackSem_evaluate (wordLang_Loop c1,s) =
        (let (res,s1) = fix_clock s (stackSem_evaluate (c1,s)) in
           if cont_loop res then
             (if state_clock s1 = 0 then (SOME
               TimeOut,stackSem_empty_env s1) else
                stackSem_evaluate (STOP ((Loop c1:'a
                  stackLang_prog)),dec_clock s1)) else (exit_loop
                  res,s1))`;
   `stackSem_evaluate (stackLang_JumpLower r1 r2 dest,s) =
        (match (get_var r1 s,get_var r2 s) with (SOME (wordLang_Word
          x),SOME (wordLang_Word y)) ->
          (if word_cmp asm_Lower x y then
           (match find_code (INL dest) (stackSem_state_regs s)
             (state_code s) with NONE -> (SOME Error,s) | SOME prog ->
               (if state_clock s = 0 then (SOME
                 TimeOut,stackSem_empty_env s) else
                 (match stackSem_evaluate (prog,dec_clock s) with
                   (res,s) -> (if bad_fun_return res then (SOME
                   Error,s) else (res,s))))) else (NONE,s)) | _92 ->
                   (SOME Error,s))`;
   `stackSem_evaluate (stackLang_RawCall dest,s) =
        (match sptree_lookup dest (state_code s) with NONE -> (SOME
          Error,s) | SOME prog ->
           (match stackSem_dest_Seq prog with SOME (_93,body) ->
               (if state_clock s = 0 then (SOME
                 TimeOut,stackSem_empty_env s) else
                 (match stackSem_evaluate (body,dec_clock s) with
                   (res,s) -> (if bad_fun_return res then (SOME
                   Error,s) else (res,s)))) | _94 -> (SOME Error,s))
                   | _95 -> (SOME Error,s))`;
   `stackSem_evaluate (wordLang_Call ret dest handler,s) =
         (match ret with NONE ->
           (match find_code dest (stackSem_state_regs s) (state_code
             s) with NONE -> (SOME Error,s) | SOME prog ->
               (if ~(handler = NONE) then (SOME Error,s) else
               if state_clock s = 0 then (SOME
                 TimeOut,stackSem_empty_env s) else
                 (match fix_clock (dec_clock s) (stackSem_evaluate
                   (prog,dec_clock s)) with (res,s) -> (if
                   bad_fun_return res then (SOME Error,s) else
                   (res,s))))) | SOME (ret_handler,link_reg',l1,l2) ->
           (match find_code dest (stackSem_state_regs s \\
             link_reg') (state_code s) with NONE -> (SOME Error,s) |
             SOME prog ->
               (if state_clock s = 0 then (SOME
                 TimeOut,stackSem_empty_env s) else
                 (match fix_clock (dec_clock (set_var link_reg' (Loc
                   l1 l2) s))
                 (stackSem_evaluate (prog,dec_clock (set_var
                   link_reg' (Loc l1 l2) s))) with (SOME (Result x),s2)
                   ->
                      (if ~(x = Loc l1 l2) then (SOME Error,s2) else
                        stackSem_evaluate (ret_handler,s2)) | (SOME
                        (Exception x),s2) ->
                      (match handler with NONE -> (SOME (Exception
                        x),s2) | SOME (h,l1,l2) ->
                          (if ~(x = Loc l1 l2) then (SOME Error,s2)
                            else
                            stackSem_evaluate (h,s2))) | (NONE,s)
                              -> (SOME Error,s) | (SOME (Break
                              _106),s) -> (SOME Error,s) | (SOME
                              (Continue _107),s) -> (SOME Error,s) |
                              (res,s) -> (res,s)))))`;
   `stackSem_evaluate (wordLang_Install ptr len dptr dlen ret,s) =
        (match (get_var ptr s,get_var len s,get_var dptr s,get_var
          dlen s) with (SOME (wordLang_Word w1),SOME (wordLang_Word
          w2),SOME (wordLang_Word w3),SOME (wordLang_Word w4)) ->
            (let (cfg,progs,bm) = compile_oracle s 0 in
           (match (buffer_flush (state_code_buffer s) w1 w2,
                  (if stackSem_state_use_stack s then buffer_flush
                    (state_data_buffer s) w3 w4 else SOME
                    (bm,state_data_buffer s))) with (
             SOME (bytes,cb),SOME (data,db)) ->
            (let new_oracle = misc_shift_seq 1 (compile_oracle s) in
            (match (compile s cfg progs,progs) with (SOME
              (bytes',cfg'),(k,prog) :: _116) ->
                (if bytes = bytes' /\ data = bm /\ FST (new_oracle
                  0) = cfg' then
                let s' = compile_oracle_fupd (K new_oracle)
                  (fp_regs_fupd (K FEMPTY) (stackSem_state_regs_fupd (K
                  ((DRESTRICT (stackSem_state_regs s)
                  (stackSem_state_ffi_save_regs s)) |+ (ptr,Loc k 0)))
                  (state_code_fupd (K (sptree_union (state_code s)
                  (fromAList progs))) (state_data_buffer_fupd (K db)
                  (state_code_buffer_fupd (K cb)
                  (stackSem_state_bitmaps_fupd (K
                  (stackSem_state_bitmaps s ++ bm))
                    s)))))) in
                  (NONE,s') else (SOME Error,s)) | _117 -> (SOME
                    Error,s))) | _118 -> (SOME Error,s))) | _119 ->
                    (SOME Error,s))`;
   `stackSem_evaluate (stackLang_ShMemOp op r (Addr a w),s) =
        (match word_exp s (wordLang_Op Add [Var a; Const w]) with
          SOME a ->
             (if state_clock s = 0 then (SOME
               TimeOut,stackSem_empty_env s) else
               sh_mem_op op r a (dec_clock s)) | _120 -> (SOME
                 Error,s))`;
   `stackSem_evaluate (wordLang_CodeBufferWrite r1 r2,s) =
        (match (get_var r1 s,get_var r2 s) with (SOME (wordLang_Word
          w1),SOME (wordLang_Word w2)) ->
              (match buffer_write (state_code_buffer s) w1 (w2w w2)
                with SOME new_cb ->
                (NONE,state_code_buffer_fupd (K new_cb) s) | _125
                  -> (SOME Error,s)) | _126 -> (SOME Error,s))`;
   `stackSem_evaluate (wordLang_DataBufferWrite r1 r2,s) =
        (if ~stackSem_state_use_stack s then (SOME Error,s) else
        (match (get_var r1 s,get_var r2 s) with (SOME (wordLang_Word
          w1),SOME (wordLang_Word w2)) ->
              (match buffer_write (state_data_buffer s) w1 w2 with
                SOME new_db ->
                (NONE,state_data_buffer_fupd (K new_db) s) | _131
                  -> (SOME Error,s)) | _132 -> (SOME Error,s)))`;
   `stackSem_evaluate (wordLang_FFI ffi_index ptr len ptr2 len2 ret,s) =
       (match (get_var len s,get_var ptr s,get_var len2 s,get_var
         ptr2 s) with (SOME (wordLang_Word w),SOME (wordLang_Word
         w2),SOME (wordLang_Word w3),SOME (wordLang_Word w4)) ->
             (match (read_bytearray w2 (w2n w) (mem_load_byte_aux
               (state_memory s) (state_mdomain s) (be s)),
                    read_bytearray w4 (w2n w3) (mem_load_byte_aux
                      (state_memory s) (state_mdomain s) (be s))) with
                      (SOME bytes,SOME bytes2) ->
                 (match call_FFI (state_ffi s) (ExtCall ffi_index)
                   bytes bytes2 with FFI_final outcome -> (SOME
                   (FinalFFI outcome),s) | FFI_return new_ffi new_bytes
                   ->
                      (let new_m = write_bytearray w4 new_bytes
                        (state_memory s) (state_mdomain s) (be s) in
                        (NONE,state_ffi_fupd (K new_ffi)
                          (fp_regs_fupd (K FEMPTY)
                          (stackSem_state_regs_fupd (K (DRESTRICT
                          (stackSem_state_regs s)
                          (stackSem_state_ffi_save_regs s)))
                          (state_memory_fupd (K new_m) s)))))) | _135
                          -> (SOME Error,s)) | res -> (SOME Error,s))`;
   `stackSem_evaluate (wordLang_LocValue r l1 l2,s) =
         (if loc_check (state_code s) (l1,l2) then
           (NONE,set_var r (Loc l1 l2) s) else (SOME Error,s))`;
   `stackSem_evaluate (stackLang_StackAlloc n,s) =
         (if ~stackSem_state_use_stack s then (SOME Error,s) else
         if stackSem_state_stack_space s < n then (SOME (Halt
           (wordLang_Word (n2w 2))),stackSem_empty_env s) else
           (NONE,stackSem_state_stack_space_fupd (K
             (stackSem_state_stack_space s - n)) s))`;
   `stackSem_evaluate (stackLang_StackFree n,s) =
         (if ~stackSem_state_use_stack s then (SOME Error,s) else
         if LENGTH (stack s) < stackSem_state_stack_space s + n then
           (SOME Error,stackSem_empty_env s) else
           (NONE,stackSem_state_stack_space_fupd (K
             (stackSem_state_stack_space s + n)) s))`;
   `stackSem_evaluate (stackLang_StackLoad r n,s) =
         (if ~stackSem_state_use_stack s then (SOME Error,s) else
         if stackSem_state_stack_space s + n < LENGTH (stack s)
           then (NONE,set_var r (EL (stackSem_state_stack_space s +
           n) (stack s)) s) else (SOME Error,stackSem_empty_env s))`;
   `stackSem_evaluate (stackLang_StackLoadAny r rn,s) =
         (if ~stackSem_state_use_stack s then (SOME Error,s) else
           match get_var rn s with SOME (wordLang_Word (w:'a word))
             ->
             (let i = stackSem_state_stack_space s + w2n (w >>>
               backend_common_word_shift (:'a)) in
               if i < LENGTH (stack s) /\
                  ((w >>> backend_common_word_shift (:'a)) <<
                    backend_common_word_shift (:'a) = w) then
                    (NONE,set_var r (EL i (stack s)) s) else (SOME
                    Error,stackSem_empty_env s)) | _136 -> (SOME
                    Error,stackSem_empty_env s))`;
   `stackSem_evaluate (stackLang_StackStore r n,s) =
         (if ~stackSem_state_use_stack s then (SOME Error,s) else
         if LENGTH (stack s) <= stackSem_state_stack_space s + n
           then (SOME Error,stackSem_empty_env s) else
           match get_var r s with NONE -> (SOME
             Error,stackSem_empty_env s) | SOME v -> (NONE,stack_fupd
             (K (LUPDATE v (stackSem_state_stack_space s + n) (stack
             s))) s))`;
   `stackSem_evaluate (stackLang_StackStoreAny r rn,s) =
         (if ~stackSem_state_use_stack s then (SOME Error,s) else
           match (get_var r s,get_var rn s) with (SOME v,SOME
             (wordLang_Word (w:'a word))) ->
             (let i = stackSem_state_stack_space s + w2n (w >>>
               backend_common_word_shift (:'a)) in
               if i < LENGTH (stack s) /\
                  ((w >>> backend_common_word_shift (:'a)) <<
                    backend_common_word_shift (:'a) = w) then
                    (NONE,stack_fupd (K (LUPDATE v i (stack s))) s)
                    else (SOME Error,stackSem_empty_env s)) | _137 ->
                    (SOME Error,stackSem_empty_env s))`;
   `stackSem_evaluate (stackLang_StackGetSize r,s) =
         (if ~stackSem_state_use_stack s then (SOME Error,s) else
         (NONE,set_var r (wordLang_Word (n2w
           (stackSem_state_stack_space s))) s))`;
   `stackSem_evaluate (stackLang_StackSetSize r,s) =
         (if ~stackSem_state_use_stack s then (SOME Error,s) else
         match get_var r s with SOME (wordLang_Word (w:'a word)) ->
             (if LENGTH (stack s) <= w2n w then (SOME
               Error,stackSem_empty_env s) else (NONE,set_var r
               (wordLang_Word (w << backend_common_word_shift (:'a)))
                           (stackSem_state_stack_space_fupd (K
                             (w2n w)) s))) | _138 -> (SOME Error,s))`;
   `stackSem_evaluate (stackLang_BitmapLoad r v,s) =
         (if ~stackSem_state_use_stack s \/ r = v then (SOME
           Error,s) else
         match get_var v s with SOME (wordLang_Word w) ->
             (if LENGTH (stackSem_state_bitmaps s) <= w2n w
               then (SOME Error,s) else (NONE,set_var r
               (wordLang_Word (EL (w2n w) (stackSem_state_bitmaps
               s))) s)) | _139 -> (SOME Error,s))`];;
hol4_overload "evaluate" "stackSem_evaluate";;

(* We prove that the clock never increases. *)

(* observational semantics *)

let semantics_def = cake_define
  `stackSem_semantics start' s =
   (let prog = Call NONE (INL start') NONE in
   if ?k. let res = FST (evaluate (prog,state_clock_fupd (K k) s)) in
     ~(
            res = SOME TimeOut) /\ ~(res = SOME (Result (Loc 1 0)))
              /\
            (!w. ~(res = SOME (Halt (wordLang_Word w)))) /\ (!f.
              ~(res = SOME (FinalFFI f))) then ffi_Fail else
     match some (\res.
       ?k t r outcome.
         evaluate (prog,state_clock_fupd (K k) s) = (SOME r,t) /\
         (match r with FinalFFI e -> outcome = ffi_FFI_outcome e |
           Halt w -> outcome = (if w = wordLang_Word (n2w 0) then
           ffi_Success else ffi_Resource_limit_hit) | Result _140 ->
           outcome = ffi_Success | _141 -> F) /\
         res = ffi_Terminate outcome (ffi_state_io_events (state_ffi
           t))) with SOME res -> res | NONE ->
       ffi_Diverge
          (build_lprefix_lub
            (IMAGE (\k. fromList (ffi_state_io_events (state_ffi
              (SND (evaluate (prog,state_clock_fupd (K k) s))))))
              UNIV)))`;;
hol4_overload "semantics" "stackSem_semantics";;

(* record accessors *)

let read_stack_def = cake_define
  `read_stack s = stack (s:('a,'b,'c)stackSem_state)`;;

let read_stack_space_def = cake_define
  `read_stack_space s = stackSem_state_stack_space
  (s:('a,'b,'c)stackSem_state)`;;

(* clean up *)

(* HOL4 ML code, not ported:
val _ = map delete_binding ["evaluate_AUX_def",
  "evaluate_primitive_def"];
*)
