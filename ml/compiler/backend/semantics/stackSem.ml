(* ======================================================== *)
(*  stackSem: ported from HOL4's
    compiler/backend/semantics/stackSemScript.sml
    A definition theory, with 51 definitions, 2 datatypes and 13
    theorems.  Needed by 7 files of the port.  *)
(* ======================================================== *)

(*
  The formal semantics of stackLang
*)

needs "compiler/backend/semantics/wordSem.ml";;
(* for word_loc and word_cmp *)
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/alignment.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/byte.ml";;
needs "lib/errorMonad.ml";;
needs "lib/integer_word.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/peg.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "stackSem"
  ["stackLang"; "wordSem"];;


let stackSem_result_INDUCT,stackSem_result_RECURSION = define_datatype
  "stackSem_result =
     stackSem_Result ('w word_loc)
   | stackSem_Exception ('w word_loc)
   | stackSem_Break num
   | stackSem_Continue num
   | stackSem_Halt ('w word_loc)
   | stackSem_TimeOut
   | stackSem_FinalFFI final_event
   | stackSem_Error";;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let bit_length_def,bit_length_ind = define_guess_cheat
  [`bit_length w = (if w = (n2w 0) then (0:num) else bit_length (w
  >>> 1) + 1)`];;

let filter_bitmap_def,filter_bitmap_ind = define_guess
  [`filter_bitmap x1 rs =
        match (x1,rs) with
          ([],rs) -> SOME ([],rs)
        | (CONS F bs,CONS r rs) -> filter_bitmap bs rs
        | ((CONS T bs),(CONS r rs)) ->
        (match filter_bitmap bs rs with NONE -> NONE | SOME (ts,rs')
          -> SOME (CONS r ts,rs'))
        | (_1,_2) -> NONE`];;

let map_bitmap_def,map_bitmap_ind = define_guess
  [`map_bitmap x1 ts rs =
        match (x1,ts,rs) with
          ([],ts,rs) -> SOME ([],ts,rs)
        | (CONS F bs,ts,CONS r rs) ->
        (match map_bitmap bs ts rs with NONE -> NONE | SOME
          (xs,ys,zs) -> SOME (CONS r xs,ys,zs))
        | ((CONS T bs),(CONS t ts),(CONS r rs)) ->
        (match map_bitmap bs ts rs with NONE -> NONE | SOME
          (xs,ys,zs) -> SOME (CONS t xs,ys,zs))
        | (_3,_4,_5) -> NONE`];;

let filter_bitmap_LENGTH = prove
 (`!bs xs x y. (filter_bitmap bs xs = SOME (x,y)) ==> LENGTH y <=
  LENGTH xs`,
  CHEAT_TAC);;

let map_bitmap_LENGTH = prove
 (`!t1 t2 t3 x y z. (map_bitmap t1 t2 t3 = SOME (x,y,z)) ==>
                   LENGTH y <= LENGTH t2 /\
                   LENGTH z <= LENGTH t3`,
  CHEAT_TAC);;

let read_bitmap_def,read_bitmap_ind = define_rec
  [`read_bitmap [] = NONE`;
   `read_bitmap (CONS (w:'a word) ws) =
         (if word_msb w then
           // there is a continuation
           match read_bitmap ws with NONE -> NONE | SOME bs -> SOME
               (APPEND (list_of_seq (\i. FAPPLY w i) (dimindex (:'a) -
               1)) bs) else
           // this is the last bitmap word
           SOME (list_of_seq (\i. FAPPLY w i) (bit_length w -
               1)))`];;

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
   "be","bool"
   (* is big-endian *)
  ];;

let stackSem_mem_store_def = new_definition
  `stackSem_mem_store (addr':'a word) (w:'a word_loc)
  (s:('a,'c,'ffi)stackSem_state) =
     (if addr' IN stackSem_state_mdomain s then
       SOME (stackSem_state_memory_fupd (K ((addr' =+ w)
         (stackSem_state_memory s))) s) else NONE)`;;

let stackSem_mem_load_def = new_definition
  `stackSem_mem_load (addr':'a word) (s:('a,'c,'ffi)stackSem_state) =
     (if addr' IN stackSem_state_mdomain s then
       SOME (stackSem_state_memory s addr') else NONE)`;;

let stackSem_dec_clock_def = new_definition
  `stackSem_dec_clock (s:('a,'c,'ffi)stackSem_state) =
  stackSem_state_clock_fupd (K (stackSem_state_clock s - 1)) s`;;

(* the termination relation that HOL4 gives is
     MEASURE (wordLang_exp_size ARB o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 stackSemScript.sml:151-156: the tactic that proves the
   termination *)
let stackSem_word_exp_def,stackSem_word_exp_ind = define_shaped_rec
  "nested"
  [`stackSem_word_exp s (asm_Const w) = SOME w`;
   `stackSem_word_exp s (wordLang_Var v) =
         (match FLOOKUP (stackSem_state_regs s) v with SOME
             (wordLang_Word w) -> SOME w | _12 -> NONE)`;
   `stackSem_word_exp s (wordLang_Lookup name) =
         (match FLOOKUP (stackSem_state_store s) name with SOME
             (wordLang_Word w) -> SOME w | _13 -> NONE)`;
   `stackSem_word_exp s (wordLang_Load addr') =
         (match stackSem_word_exp s addr' with SOME w -> (match
             stackSem_mem_load w s with SOME (wordLang_Word w) ->
             SOME w | _18 -> NONE) | _19 -> NONE)`;
   `stackSem_word_exp s (wordLang_Op op wexps) =
         (let ws = MAP (stackSem_word_exp s) wexps in
           if ALL IS_SOME ws then wordLang_word_op op (MAP THE
               ws) else NONE)`;
   `stackSem_word_exp s (wordLang_Shift sh wexp wexp1) =
         (match (stackSem_word_exp s wexp,stackSem_word_exp s
             wexp1) with (SOME w,SOME w1) -> word_sh sh w (w2n w1)
             | _22 -> NONE)`];;

let stackSem_get_var_def = new_definition
  `stackSem_get_var v (s:('a,'c,'ffi)stackSem_state) = FLOOKUP
  (stackSem_state_regs s) v`;;

let stackSem_get_vars_def,stackSem_get_vars_ind = define_rec
  [`stackSem_get_vars [] s = SOME []`;
   `stackSem_get_vars (CONS v vs) s =
         (match stackSem_get_var v s with NONE -> NONE | SOME x
             -> (match stackSem_get_vars vs s with NONE -> NONE |
             SOME xs -> SOME (CONS x xs)))`];;

let stackSem_get_fp_var_def = new_definition
  `stackSem_get_fp_var v (s:('a,'c,'ffi)stackSem_state) = FLOOKUP
  (stackSem_state_fp_regs s) v`;;

let stackSem_set_var_def = new_definition
  `stackSem_set_var v x (s:('a,'c,'ffi)stackSem_state) =
     (stackSem_state_regs_fupd (K (stackSem_state_regs s |+
       (v,x))) s)`;;

let stackSem_set_fp_var_def = new_definition
  `stackSem_set_fp_var v x (s:('a,'c,'ffi)stackSem_state) =
     (stackSem_state_fp_regs_fupd (K (stackSem_state_fp_regs s |+
       (v,x))) s)`;;

let stackSem_set_store_def = new_definition
  `stackSem_set_store v x (s:('a,'c,'ffi)stackSem_state) =
  (stackSem_state_store_fupd (K (stackSem_state_store s |+ (v,x))) s)`;;

let stackSem_empty_env_def = new_definition
  `stackSem_empty_env (s:('a,'c,'ffi)stackSem_state) =
  stackSem_state_stack_fupd (K []) (stackSem_state_regs_fupd (K
  FEMPTY) s)`;;

let stackSem_sh_mem_store_def = new_definition
  `(stackSem_sh_mem_store r (a:'a word)
  (s:('a,'c,'ffi)stackSem_state):('a stackSem_result)
  option#('a,'c,'ffi)stackSem_state) =
   (match stackSem_get_var r s with
      SOME (wordLang_Word w) ->
        (if a IN stackSem_state_sh_mdomain s then
          (match call_FFI (stackSem_state_ffi s) (ffi_SharedMem
            MappedWrite) [(n2w 0):word8]
                         (APPEND (word_to_bytes w F) (word_to_bytes a
                           F)) with
             FFI_final outcome -> (SOME (stackSem_FinalFFI
               outcome),s) | FFI_return new_ffi new_bytes ->
               (NONE,stackSem_state_ffi_fupd (K new_ffi) s)) else
               (SOME stackSem_Error,s)) | _23 -> (SOME
               stackSem_Error,s))`;;

let stackSem_sh_mem_load_def = new_definition
  `(stackSem_sh_mem_load r (a:'a word)
  (s:('a,'c,'ffi)stackSem_state):('a stackSem_result)
  option#('a,'c,'ffi)stackSem_state) =
   (if a IN stackSem_state_sh_mdomain s then
     (match call_FFI (stackSem_state_ffi s) (ffi_SharedMem
       MappedRead) [(n2w 0):word8]
                    (word_to_bytes a F) with
        FFI_final outcome -> (SOME (stackSem_FinalFFI outcome),s) |
          FFI_return new_ffi new_bytes ->
          (NONE,stackSem_state_ffi_fupd (K new_ffi)
            (stackSem_state_regs_fupd (K (stackSem_state_regs s |+
            (r,wordLang_Word (word_of_bytes F (n2w 0) new_bytes))))
           s))) else (SOME stackSem_Error,s))`;;

let stackSem_sh_mem_store_byte_def = new_definition
  `(stackSem_sh_mem_store_byte r (a:'a word)
  (s:('a,'c,'ffi)stackSem_state):('a stackSem_result)
  option#('a,'c,'ffi)stackSem_state) =
   (match stackSem_get_var r s with
      SOME (wordLang_Word w) ->
        (if byte_align a IN stackSem_state_sh_mdomain s then
          (match call_FFI (stackSem_state_ffi s) (ffi_SharedMem
            MappedWrite) [(n2w 1):word8]
                         (APPEND [get_byte (n2w 0) w F]
                           (word_to_bytes a F)) with
             FFI_final outcome -> (SOME (stackSem_FinalFFI
               outcome),s) | FFI_return new_ffi new_bytes ->
               (NONE,stackSem_state_ffi_fupd (K new_ffi) s)) else
               (SOME stackSem_Error,s)) | _24 -> (SOME
               stackSem_Error,s))`;;

let stackSem_sh_mem_store16_def = new_definition
  `(stackSem_sh_mem_store16 r (a:'a word)
  (s:('a,'c,'ffi)stackSem_state):('a stackSem_result)
  option#('a,'c,'ffi)stackSem_state) =
   (match stackSem_get_var r s with
      SOME (wordLang_Word w) ->
        (if byte_align a IN stackSem_state_sh_mdomain s then
          (match call_FFI (stackSem_state_ffi s) (ffi_SharedMem
            MappedWrite) [(n2w 2):word8]
                         (APPEND (TAKE 2 (word_to_bytes w F))
                           (word_to_bytes a F)) with
             FFI_final outcome -> (SOME (stackSem_FinalFFI
               outcome),s) | FFI_return new_ffi new_bytes ->
               (NONE,stackSem_state_ffi_fupd (K new_ffi) s)) else
               (SOME stackSem_Error,s)) | _25 -> (SOME
               stackSem_Error,s))`;;

let stackSem_sh_mem_store32_def = new_definition
  `(stackSem_sh_mem_store32 r (a:'a word)
  (s:('a,'c,'ffi)stackSem_state):('a stackSem_result)
  option#('a,'c,'ffi)stackSem_state) =
   (match stackSem_get_var r s with
      SOME (wordLang_Word w) ->
        (if byte_align a IN stackSem_state_sh_mdomain s then
          (match call_FFI (stackSem_state_ffi s) (ffi_SharedMem
            MappedWrite) [(n2w 4):word8]
                         (APPEND (TAKE 4 (word_to_bytes w F))
                           (word_to_bytes a F)) with
             FFI_final outcome -> (SOME (stackSem_FinalFFI
               outcome),s) | FFI_return new_ffi new_bytes ->
               (NONE,stackSem_state_ffi_fupd (K new_ffi) s)) else
               (SOME stackSem_Error,s)) | _26 -> (SOME
               stackSem_Error,s))`;;

let stackSem_sh_mem_load_byte_def = new_definition
  `(stackSem_sh_mem_load_byte r (a:'a word)
  (s:('a,'c,'ffi)stackSem_state):('a stackSem_result)
  option#('a,'c,'ffi)stackSem_state) =
   (if byte_align a IN stackSem_state_sh_mdomain s then
     (match call_FFI (stackSem_state_ffi s) (ffi_SharedMem
       MappedRead) [(n2w 1):word8] (word_to_bytes a F) with
        FFI_final outcome -> (SOME (stackSem_FinalFFI outcome),s) |
          FFI_return new_ffi new_bytes ->
          (NONE,stackSem_state_ffi_fupd (K new_ffi)
            (stackSem_state_regs_fupd (K (stackSem_state_regs s |+
            (r,wordLang_Word (word_of_bytes F (n2w 0) new_bytes))))
           s))) else (SOME stackSem_Error,s))`;;

let stackSem_sh_mem_load16_def = new_definition
  `(stackSem_sh_mem_load16 r (a:'a word)
  (s:('a,'c,'ffi)stackSem_state):('a stackSem_result)
  option#('a,'c,'ffi)stackSem_state) =
   (if byte_align a IN stackSem_state_sh_mdomain s then
     (match call_FFI (stackSem_state_ffi s) (ffi_SharedMem
       MappedRead) [(n2w 2):word8] (word_to_bytes a F) with
        FFI_final outcome -> (SOME (stackSem_FinalFFI outcome),s) |
          FFI_return new_ffi new_bytes ->
          (NONE,stackSem_state_ffi_fupd (K new_ffi)
            (stackSem_state_regs_fupd (K (stackSem_state_regs s |+
            (r,wordLang_Word (word_of_bytes F (n2w 0) new_bytes))))
           s))) else (SOME stackSem_Error,s))`;;

let stackSem_sh_mem_load32_def = new_definition
  `(stackSem_sh_mem_load32 r (a:'a word)
  (s:('a,'c,'ffi)stackSem_state):('a stackSem_result)
  option#('a,'c,'ffi)stackSem_state) =
   (if byte_align a IN stackSem_state_sh_mdomain s then
     (match call_FFI (stackSem_state_ffi s) (ffi_SharedMem
       MappedRead) [(n2w 4):word8] (word_to_bytes a F) with
        FFI_final outcome -> (SOME (stackSem_FinalFFI outcome),s) |
          FFI_return new_ffi new_bytes ->
          (NONE,stackSem_state_ffi_fupd (K new_ffi)
            (stackSem_state_regs_fupd (K (stackSem_state_regs s |+
            (r,wordLang_Word (word_of_bytes F (n2w 0) new_bytes))))
           s))) else (SOME stackSem_Error,s))`;;

let sh_mem_op_def = define_cases
  [`sh_mem_op (asm_Load:memop) r ad (s:('a,'c,'ffi)stackSem_state) =
    stackSem_sh_mem_load r ad s`;
   `sh_mem_op (asm_Store:memop) r ad (s:('a,'c,'ffi)stackSem_state) =
    stackSem_sh_mem_store r ad s`;
   `sh_mem_op asm_Load8 r ad (s:('a,'c,'ffi)stackSem_state) =
    stackSem_sh_mem_load_byte r ad s`;
   `sh_mem_op asm_Store8 r ad (s:('a,'c,'ffi)stackSem_state) =
    stackSem_sh_mem_store_byte r ad s`;
   `sh_mem_op asm_Load16 r ad (s:('a,'c,'ffi)stackSem_state) =
    stackSem_sh_mem_load16 r ad s`;
   `sh_mem_op asm_Store16 r ad (s:('a,'c,'ffi)stackSem_state) =
    stackSem_sh_mem_store16 r ad s`;
   `sh_mem_op (asm_Load32:memop) r ad (s:('a,'c,'ffi)stackSem_state)
    = stackSem_sh_mem_load32 r ad s`;
   `sh_mem_op (asm_Store32:memop) r ad
    (s:('a,'c,'ffi)stackSem_state) = stackSem_sh_mem_store32 r ad s`];;

let full_read_bitmap_def = new_definition
  `full_read_bitmap bitmaps x2 =
        match x2 with
          wordLang_Word w ->
        (if w = (n2w 0) then NONE else read_bitmap (DROP (w2n (w -
          (n2w 1))) bitmaps))
        | _27 -> NONE`;;

(* the termination relation that HOL4 gives is
     MEASURE (LENGTH o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 stackSemScript.sml:330-334: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let stackSem_enc_stack_def,stackSem_enc_stack_ind = define_guess_cheat
  [`stackSem_enc_stack bitmaps [] = NONE`;
   `stackSem_enc_stack bitmaps (CONS w ws) =
         (if w = wordLang_Word (n2w 0) then (if ws = [] then SOME []
             else NONE) else
           match full_read_bitmap bitmaps w with NONE -> NONE | SOME
               bs ->
              (match filter_bitmap bs ws with NONE -> NONE | SOME
                  (ts,ws') ->
                  (match stackSem_enc_stack bitmaps ws' with
                      NONE -> NONE | SOME rs -> SOME (APPEND ts
                      rs))))`];;

(* the termination relation that HOL4 gives is
     MEASURE (LENGTH o SND o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 stackSemScript.sml:349-354: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let stackSem_dec_stack_def,stackSem_dec_stack_ind = define_guess_cheat
  [`stackSem_dec_stack bitmaps _28 [] = NONE`;
   `stackSem_dec_stack bitmaps ts (CONS w ws) =
        (if w = wordLang_Word (n2w 0) then (if ts = [] /\ ws = []
            then SOME [wordLang_Word (n2w 0)] else NONE) else
         match full_read_bitmap bitmaps w with NONE -> NONE | SOME
             bs ->
            (match map_bitmap bs ts ws with NONE -> NONE | SOME
                (hd,ts',ws') ->
               (match stackSem_dec_stack bitmaps ts' ws' with
                   NONE -> NONE | SOME rest -> SOME (APPEND (APPEND
                   [w] hd) rest))))`];;

let stackSem_gc_def = new_definition
  `stackSem_gc s =
     (if LENGTH (stackSem_state_stack s) < stackSem_state_stack_space
       s then NONE else
       let unused = TAKE (stackSem_state_stack_space s)
         (stackSem_state_stack s) in
       let stack' = DROP (stackSem_state_stack_space s)
         (stackSem_state_stack s) in
         match stackSem_enc_stack (stackSem_state_bitmaps s) (DROP
           (stackSem_state_stack_space s) (stackSem_state_stack s)) with
           NONE -> NONE | SOME wl_list ->
           (match stackSem_state_gc_fun s
             (wl_list,stackSem_state_memory s,stackSem_state_mdomain
             s,stackSem_state_store s) with NONE -> NONE | SOME
             (wl,m,st) ->
            (match stackSem_dec_stack (stackSem_state_bitmaps s) wl
              stack' with NONE -> NONE | SOME stack' ->
                 SOME (stackSem_state_memory_fupd (K m)
                   (stackSem_state_regs_fupd (K FEMPTY)
                   (stackSem_state_store_fupd (K st)
                   (stackSem_state_stack_fupd (K (APPEND unused
                   stack')) s)))))))`;;

let stackSem_has_space_def = new_definition
  `stackSem_has_space wl store =
     (match (wl,FLOOKUP store NextFree,FLOOKUP store TriggerGC)
       with (wordLang_Word w,SOME (wordLang_Word n),SOME
       (wordLang_Word l)) -> SOME (w2n w <= w2n (l - n)) | _29 ->
       NONE)`;;

let stackSem_alloc_def = new_definition
  `stackSem_alloc (w:'a word) (s:('a,'c,'ffi)stackSem_state) =
       // perform garbage collection
       (match stackSem_gc (stackSem_set_store AllocSize
         (wordLang_Word w) s) with NONE -> (SOME stackSem_Error,s) |
         SOME s ->
          (
           // read how much space should be allocated
           match FLOOKUP (stackSem_state_store s) AllocSize with NONE
             -> (SOME stackSem_Error,s) | SOME w ->
            (
             // check how much space there is
             match stackSem_has_space w (stackSem_state_store s) with
               NONE -> (SOME stackSem_Error,s) | SOME T ->
                         (
                          // success there is that much space
                          NONE,s) | SOME F ->
                         (
                          // fail, GC didn't free up enough space
                          SOME (stackSem_Halt (wordLang_Word ((n2w
                            1):'a word))),stackSem_empty_env s))))`;;

let stackSem_assign_def = new_definition
  `stackSem_assign reg exp s =
     (match stackSem_word_exp s exp with NONE -> NONE | SOME w ->
       SOME (stackSem_set_var reg (wordLang_Word w) s))`;;

let stackSem_inst_def = new_definition
  `stackSem_inst i (s:('a,'c,'ffi)stackSem_state) =
     (match i with asm_Skip -> SOME s | asm_Const reg w ->
       stackSem_assign reg (asm_Const w) s | asm_Arith (asm_Binop bop r1
       r2 ri) ->
         (if bop = asm_Or /\ ri = Reg r2 then
           match FLOOKUP (stackSem_state_regs s) r2 with NONE -> NONE
             | SOME w -> SOME (stackSem_set_var r1 w s) else
           stackSem_assign r1
             (wordLang_Op bop [wordLang_Var r2; match ri with Reg r3
               -> wordLang_Var r3 | Imm w -> asm_Const w]) s) |
               asm_Arith (asm_Shift sh r1 r2 ri) ->
         stackSem_assign r1
           (wordLang_Shift sh (wordLang_Var r2) (match ri with Reg r3
             -> wordLang_Var r3 | Imm w -> asm_Const w)) s | asm_Arith
             (asm_Div r1 r2 r3) ->
        (let vs = stackSem_get_vars [r3; r2] s in
        match vs with
        SOME [wordLang_Word q; wordLang_Word w2] ->
          (if ~(q = (n2w 0)) then
            SOME (stackSem_set_var r1 (wordLang_Word (w2 / q)) s)
              else NONE) | _30 -> NONE) | asm_Arith (asm_AddCarry r1 r2
              r3 r4) ->
         (let vs = stackSem_get_vars [r2; r3; r4] s in
         match vs with
         SOME [wordLang_Word l; wordLang_Word r; wordLang_Word c] ->
           (let res = w2n l + w2n r + (if c = ((n2w 0):'a word) then
             0 else 1) in
             SOME (stackSem_set_var r4 (wordLang_Word (if dimword
               (:'a) <= res then ((n2w 1):'a word) else (n2w 0)))
                  (stackSem_set_var r1 (wordLang_Word (n2w res)) s)))
                    | _31 -> NONE) | asm_Arith (asm_AddOverflow r1 r2 r3
                    r4) ->
         (let vs = stackSem_get_vars [r2; r3] s in
         match vs with
         SOME [wordLang_Word w2; wordLang_Word w3] ->
           SOME (stackSem_set_var r4 (wordLang_Word (if ~(w2i (w2 +
             w3) = w2i w2 + w2i w3) then (n2w 1) else (n2w 0)))
                  (stackSem_set_var r1 (wordLang_Word (w2 + w3)) s))
                    | _32 -> NONE) | asm_Arith (asm_SubOverflow r1 r2 r3
                    r4) ->
         (let vs = stackSem_get_vars [r2; r3] s in
         match vs with
         SOME [wordLang_Word w2; wordLang_Word w3] ->
           SOME (stackSem_set_var r4 (wordLang_Word (if ~(w2i (w2 -
             w3) = w2i w2 - w2i w3) then (n2w 1) else (n2w 0)))
                  (stackSem_set_var r1 (wordLang_Word (w2 - w3)) s))
                    | _33 -> NONE) | asm_Arith (asm_LongMul r1 r2 r3 r4)
                    ->
         (let vs = stackSem_get_vars [r3; r4] s in
         match vs with
         SOME [wordLang_Word w3; wordLang_Word w4] ->
          (let r = w2n w3 * w2n w4 in
            SOME (stackSem_set_var r2 (wordLang_Word (n2w r))
              (stackSem_set_var r1 (wordLang_Word (n2w (r DIV dimword
              (:'a)))) s))) | _34 -> NONE) | asm_Arith (asm_LongDiv r1
              r2 r3 r4 r5) ->
        (let vs = stackSem_get_vars [r3; r4; r5] s in
        match vs with
        SOME [wordLang_Word w3; wordLang_Word w4; wordLang_Word w5]
          ->
          (let n = w2n w3 * dimword (:'a) + w2n w4 in
          let d = w2n w5 in
          let q = n DIV d in
          if (~(d = 0) /\ q < dimword (:'a)) then
            SOME (stackSem_set_var r1 (wordLang_Word (n2w q))
              (stackSem_set_var r2 (wordLang_Word (n2w (n MOD d))) s))
              else NONE) | _35 -> NONE) | asm_Mem asm_Load r (Addr a w)
              ->
        (match stackSem_word_exp s (wordLang_Op asm_Add [wordLang_Var
          a; asm_Const w]) with NONE -> NONE | SOME w ->
             (match stackSem_mem_load w s with NONE -> NONE | SOME w
               -> SOME (stackSem_set_var r w s))) | asm_Mem asm_Load8 r
               (Addr a w) ->
        (match stackSem_word_exp s (wordLang_Op asm_Add [wordLang_Var
          a; asm_Const w]) with SOME w ->
            (match mem_load_byte_aux (stackSem_state_memory s)
              (stackSem_state_mdomain s) (stackSem_state_be s) w with
              NONE -> NONE | SOME w -> SOME (stackSem_set_var r
              (wordLang_Word (w2w w)) s)) | _36 -> NONE) | asm_Mem
              asm_Load16 _37 _38 -> NONE | asm_Mem asm_Load32 r (Addr a
              w) ->
        (match stackSem_word_exp s (wordLang_Op asm_Add [wordLang_Var
          a; asm_Const w]) with SOME w ->
            (match mem_load_32 (stackSem_state_memory s)
              (stackSem_state_mdomain s) (stackSem_state_be s) w with
              NONE -> NONE | SOME w -> SOME (stackSem_set_var r
              (wordLang_Word (w2w w)) s)) | _39 -> NONE) | asm_Mem
              asm_Store r (Addr a w) ->
        (match (stackSem_word_exp s (wordLang_Op asm_Add
          [wordLang_Var a; asm_Const w]),stackSem_get_var r s) with
          (SOME a,SOME w) ->
             (match stackSem_mem_store a w s with SOME s1 -> SOME s1
               | NONE -> NONE) | _40 -> NONE) | asm_Mem asm_Store8 r
               (Addr a w) ->
        (match (stackSem_word_exp s (wordLang_Op asm_Add
          [wordLang_Var a; asm_Const w]),stackSem_get_var r s) with
          (SOME a,SOME (wordLang_Word w)) ->
             (match mem_store_byte_aux (stackSem_state_memory s)
               (stackSem_state_mdomain s) (stackSem_state_be s) a (w2w
               w) with SOME new_m -> SOME (stackSem_state_memory_fupd (K
               new_m) s) | NONE -> NONE) | _41 -> NONE) | asm_Mem
               asm_Store16 _42 _43 -> NONE | asm_Mem asm_Store32 r (Addr
               a w) ->
        (match (stackSem_word_exp s (wordLang_Op asm_Add
          [wordLang_Var a; asm_Const w]),stackSem_get_var r s) with
          (SOME a,SOME (wordLang_Word w)) ->
             (match mem_store_32 (stackSem_state_memory s)
               (stackSem_state_mdomain s) (stackSem_state_be s) a (w2w
               w) with SOME new_m -> SOME (stackSem_state_memory_fupd (K
               new_m) s) | NONE -> NONE) | _44 -> NONE) | asm_FP (FPLess
               r d1 d2) ->
       (match (stackSem_get_fp_var d1 s,stackSem_get_fp_var d2 s)
         with (SOME f1,SOME f2) ->
         SOME (stackSem_set_var r
           (wordLang_Word (if fp64_lessThan f1 f2 then (n2w 1) else
             (n2w 0))) s) | _45 -> NONE) | asm_FP (FPLessEqual r d1 d2)
             ->
       (match (stackSem_get_fp_var d1 s,stackSem_get_fp_var d2 s)
         with (SOME f1,SOME f2) ->
         SOME (stackSem_set_var r
           (wordLang_Word (if fp64_lessEqual f1 f2 then (n2w 1) else
             (n2w 0))) s) | _46 -> NONE) | asm_FP (FPEqual r d1 d2) ->
       (match (stackSem_get_fp_var d1 s,stackSem_get_fp_var d2 s)
         with (SOME f1,SOME f2) ->
         SOME (stackSem_set_var r
           (wordLang_Word (if fp64_equal f1 f2 then (n2w 1) else (n2w
             0))) s) | _47 -> NONE) | asm_FP (FPMov d1 d2) ->
       (match stackSem_get_fp_var d2 s with SOME f ->
         SOME (stackSem_set_fp_var d1 f s) | _48 -> NONE) | asm_FP
           (FPAbs d1 d2) ->
       (match stackSem_get_fp_var d2 s with SOME f ->
         SOME (stackSem_set_fp_var d1 (fp64_abs f) s) | _49 -> NONE)
           | asm_FP (FPNeg d1 d2) ->
       (match stackSem_get_fp_var d2 s with SOME f ->
         SOME (stackSem_set_fp_var d1 (fp64_negate f) s) | _50 ->
           NONE) | asm_FP (FPSqrt d1 d2) ->
       (match stackSem_get_fp_var d2 s with SOME f ->
         SOME (stackSem_set_fp_var d1 (fp64_sqrt roundTiesToEven f)
           s) | _51 -> NONE) | asm_FP (FPAdd d1 d2 d3) ->
       (match (stackSem_get_fp_var d2 s,stackSem_get_fp_var d3 s)
         with (SOME f1,SOME f2) ->
         SOME (stackSem_set_fp_var d1 (fp64_add roundTiesToEven f1
           f2) s) | _52 -> NONE) | asm_FP (FPSub d1 d2 d3) ->
       (match (stackSem_get_fp_var d2 s,stackSem_get_fp_var d3 s)
         with (SOME f1,SOME f2) ->
         SOME (stackSem_set_fp_var d1 (fp64_sub roundTiesToEven f1
           f2) s) | _53 -> NONE) | asm_FP (FPMul d1 d2 d3) ->
       (match (stackSem_get_fp_var d2 s,stackSem_get_fp_var d3 s)
         with (SOME f1,SOME f2) ->
         SOME (stackSem_set_fp_var d1 (fp64_mul roundTiesToEven f1
           f2) s) | _54 -> NONE) | asm_FP (FPDiv d1 d2 d3) ->
       (match (stackSem_get_fp_var d2 s,stackSem_get_fp_var d3 s)
         with (SOME f1,SOME f2) ->
         SOME (stackSem_set_fp_var d1 (fp64_div roundTiesToEven f1
           f2) s) | _55 -> NONE) | asm_FP (FPFma d1 d2 d3) ->
       (match (stackSem_get_fp_var d1 s,stackSem_get_fp_var d2
         s,stackSem_get_fp_var d3 s) with (SOME f1,SOME f2,SOME f3) ->
         SOME (stackSem_set_fp_var d1 (fpfma f1 f2 f3) s) | _56 ->
           NONE) | asm_FP (FPMovToReg r1 r2 d) ->
       (match stackSem_get_fp_var d s with SOME v ->
         (if dimindex (:'a) = 64 then
           SOME (stackSem_set_var r1 (wordLang_Word (w2w v)) s) else
           SOME (stackSem_set_var r2 (wordLang_Word ((63 >< 32) v))
             (stackSem_set_var r1 (wordLang_Word ((31 >< 0) v)) s))) |
             _57 -> NONE) | asm_FP (FPMovFromReg d r1 r2) ->
       (if dimindex (:'a) = 64 then
         match stackSem_get_var r1 s with
           SOME (wordLang_Word w1) -> SOME (stackSem_set_fp_var d
             (w2w w1) s) | _58 -> NONE else
         match (stackSem_get_var r1 s,stackSem_get_var r2 s) with
           (SOME (wordLang_Word w1),SOME (wordLang_Word w2)) -> SOME
             (stackSem_set_fp_var d (w2 @@ w1) s) | _59 -> NONE) |
             asm_FP (FPToInt d1 d2) ->
       (match stackSem_get_fp_var d2 s with
         NONE -> NONE | SOME f ->
       (match fp64_to_int roundTiesToEven f with
         NONE -> NONE | SOME i ->
         (let w = (i2w i:word32) in
         if w2i w = i then
           (if dimindex (:'a) = 64 then
              SOME (stackSem_set_fp_var d1 (w2w w) s) else
            match stackSem_get_fp_var (d1 DIV 2) s with
              NONE -> NONE | SOME f ->
              (let (h,l) = (if ODD d1 then (63,32) else (31,0)) in
                   SOME (stackSem_set_fp_var (d1 DIV 2)
                     (bit_field_insert h l w f) s))) else
           NONE))) | asm_FP (FPFromInt d1 d2) ->
       (if dimindex (:'a) = 64 then
         match stackSem_get_fp_var d2 s with SOME f ->
           (let i = w2i ((31 >< 0) f:word32) in
             SOME (stackSem_set_fp_var d1 (int_to_fp64
               roundTiesToEven i) s)) | NONE -> NONE else
         match stackSem_get_fp_var (d2 DIV 2) s with SOME v ->
           (let i = w2i (if ODD d2 then (63 >< 32) v else (31 >< 0)
             v:'a word) in
             SOME (stackSem_set_fp_var d1 (int_to_fp64
               roundTiesToEven i) s)) | NONE -> NONE | _60 -> NONE))`;;

let stackSem_get_var_imm_def = define_cases
  [`stackSem_get_var_imm ((Reg n):'a asm_reg_imm) s =
    stackSem_get_var n s`;
   `stackSem_get_var_imm (Imm w) s = SOME (wordLang_Word w)`];;

let stackSem_find_code_def = define_cases
  [`stackSem_find_code (INL p) regs' code = sptree_lookup p code`;
   `stackSem_find_code (INR r) regs' code =
         (match FLOOKUP regs' r with
           SOME (wordLang_Loc loc 0) -> sptree_lookup loc code
               | other -> NONE)`];;

let stackSem_fix_clock_def = new_definition
  `stackSem_fix_clock s (res,s1) = (res,stackSem_state_clock_fupd (K
  (MIN (stackSem_state_clock s) (stackSem_state_clock s1))) s1)`;;

(* fix_clock_IMP[local] *)
let stackSem_fix_clock_IMP = prove
 (`stackSem_fix_clock s x = (res,s1) ==> stackSem_state_clock s1 <=
  stackSem_state_clock s`,
  CHEAT_TAC);;

let stackSem_STOP_def = new_definition
  `stackSem_STOP x = x`;;

let _ = size_thms "stackLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let get_labels_def,get_labels_ind = define_wf
  `MEASURE (\x0. stackLang_prog_size (\x. 0) x0)`
  [`stackSem_get_labels x1 =
        match x1 with
          stackLang_Seq p1 p2 -> stackSem_get_labels p1 UNION
            stackSem_get_labels p2
        | (stackLang_If _61 _62 _63 p1 p2) -> stackSem_get_labels p1
          UNION stackSem_get_labels p2
        | (stackLang_Loop p) -> stackSem_get_labels p
        | (stackLang_Call ret _64 handler) ->
        (match ret with NONE -> {} | SOME (r,_65,l1,l2) -> (l1,l2)
          INSERT (stackSem_get_labels r UNION
             (match handler with NONE -> {} | SOME (r,l1,l2) ->
               (l1,l2) INSERT stackSem_get_labels r)))
        | (stackLang_Halt _66) -> {}
        | _67 -> {}`];;

let loc_check_def = new_definition
  `loc_check code (l1,l2) <=>
     (l2 = 0 /\ l1 IN domain code) \/
     (?n e. sptree_lookup n code = SOME e /\ (l1,l2) IN
       stackSem_get_labels e)`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let copy_words_for_pattern_def,copy_words_for_pattern_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3,x4,x5,x6). list_size (\x. 0) x4)`
  [`copy_words_for_pattern (pattern:'a word) (i:num) (a:'a word) (off:'a
  word) bs dm m =
     (if pattern = (n2w 0) then NONE else
     if pattern = (n2w 1) then SOME (i,a,m) else
       if a IN dm /\ i < LENGTH bs then
         let b = FAPPLY pattern 0 in
         let w = EL i bs in
         let m = (a =+ wordLang_Word (if b then w + off else w)) m
           in
           copy_words_for_pattern
             (pattern >>> 1) (i + 1) (a + bytes_in_word) off bs
               dm m else NONE)`];;

let copy_words_for_pattern_LESS_EQ = prove
 (`!p i a f bs dm m j a1.
     copy_words_for_pattern p i a f bs dm m = SOME (j,a1) ==> i <=
       j`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (\(i,a,f,bs,dm,m). LENGTH bs - i)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 stackSemScript.sml:720-723: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let copy_words_def,copy_words_ind = define_guess_cheat
  [`copy_words i a off bs dm m =
     (if LENGTH bs <= i then NONE else
       let pattern = EL i bs in
         match copy_words_for_pattern pattern (i + 1) a off bs dm m
           with NONE -> NONE | SOME (i1,a1,m1) ->
             (if word_msb pattern then copy_words i1 a1 off bs dm m1
               else
               SOME (a1,m1)))`];;

let stackSem_unset_var_def = new_definition
  `stackSem_unset_var v (s:('a,'c,'ffi)stackSem_state) =
  stackSem_state_regs_fupd (K (stackSem_state_regs s \\ v)) s`;;

let store_const_sem_def = new_definition
  `store_const_sem t1 t2 (s:('a,'c,'ffi)stackSem_state) =
     (if ~(ALL_DISTINCT [0; 1; 2; 3; t1; t2]) then (SOME
       stackSem_Error,s) else
       match (stackSem_get_var 1 s,stackSem_get_var 2
         s,stackSem_get_var 3 s) with (SOME (wordLang_Word i),SOME
         (wordLang_Word a),SOME (wordLang_Word off)) ->
           (match copy_words (w2n i) a off (stackSem_state_bitmaps s)
             (stackSem_state_mdomain s) (stackSem_state_memory s) with
             NONE -> (SOME stackSem_Error,s) | SOME (a,m) -> (NONE,
               (if stackSem_state_use_alloc s then stackSem_unset_var
                 0 else I)
                 (stackSem_set_var t1 (wordLang_Word (n2w 1))
                   (stackSem_set_var t2 (wordLang_Word (n2w 1))
                   (stackSem_set_var 1 (wordLang_Word (n2w 1))
                     (stackSem_set_var 2 (wordLang_Word a)
                     (stackSem_state_memory_fupd (K m) s))))))) | _68
                     -> (SOME stackSem_Error,s))`;;

let check_store_consts_opt_def = define_cases
  [`check_store_consts_opt t1 t2 NONE _69 = T`;
   `check_store_consts_opt t1 t2 (SOME n) c =
      (sptree_lookup n c = SOME (stackLang_Seq
          (stackLang_StoreConsts t1 t2 NONE) (stackLang_Return 0)))`];;

let stackSem_dest_Seq_def = new_definition
  `stackSem_dest_Seq x1 =
      match x1 with
        stackLang_Seq p1 p2 -> SOME (p1,(p2:'a stackLang_prog))
      | _70 -> NONE`;;

let stackSem_bad_fun_return_def = new_definition
  `stackSem_bad_fun_return x1 =
      match x1 with
        NONE -> T
      | (SOME (stackSem_Break _71)) -> T
      | (SOME (stackSem_Continue _72)) -> T
      | _73 -> F`;;
add_simp stackSem_bad_fun_return_def;;

let stackSem_cont_loop_def = new_definition
  `stackSem_cont_loop x1 =
      match x1 with
        NONE -> T
      | (SOME (stackSem_Continue n)) -> (n = 0)
      | _74 -> F`;;
add_simp stackSem_cont_loop_def;;

let stackSem_exit_loop_def = new_definition
  `stackSem_exit_loop res =
      match res with
        SOME (stackSem_Break n) -> (if n = 0 then NONE else SOME
          (stackSem_Break (n - 1)))
      | (SOME (stackSem_Continue n)) -> SOME (stackSem_Continue (n -
        1))
      | res -> res`;;
add_simp stackSem_exit_loop_def;;

let stackSem_fix_clock_IMP =
  try prove
   (`!s x res s1. stackSem_fix_clock s x = (res,s1)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; stackSem_fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "stackSem_state") THEN
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "stackSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nstackSem_fix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl stackSem_fix_clock_IMP <> `T` then
  cake_term_facts := stackSem_fix_clock_IMP :: (!cake_term_facts);;

let stackSem_evaluate_def,stackSem_evaluate_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`stackSem_evaluate ((stackLang_Skip:'a stackLang_prog),s) =
    (NONE,(s:('a,'c,'ffi)stackSem_state))`;
   `stackSem_evaluate (stackLang_Halt v,s) =
         (match stackSem_get_var v s with SOME w -> (SOME
             (stackSem_Halt w),stackSem_empty_env s) | NONE -> (SOME
             stackSem_Error,s))`;
   `stackSem_evaluate (stackLang_Alloc n,s) =
         (if ~(stackSem_state_use_alloc s) then (SOME
             stackSem_Error,s) else
         match stackSem_get_var n s with SOME (wordLang_Word w)
             -> stackSem_alloc w s | _79 -> (SOME stackSem_Error,s))`;
   `stackSem_evaluate (stackLang_StoreConsts t1 t2 stub_opt,s) =
         (if ~(stackSem_state_use_store s) then (SOME
             stackSem_Error,s) else
         if ~(stackSem_state_use_alloc s) /\ IS_SOME stub_opt then
             (SOME stackSem_Error,s) else
         if ~(check_store_consts_opt t1 t2 stub_opt
             (stackSem_state_code s)) then (SOME stackSem_Error,s) else
           store_const_sem t1 t2 s)`;
   `stackSem_evaluate (stackLang_Inst i,s) =
         (match stackSem_inst i s with SOME s1 -> (NONE,s1) |
             NONE -> (SOME stackSem_Error,s))`;
   `stackSem_evaluate (stackLang_Get v name,s) =
         (if ~(stackSem_state_use_store s) then (SOME
             stackSem_Error,s) else
         match FLOOKUP (stackSem_state_store s) name with SOME x
             -> (NONE,stackSem_set_var v x s) | NONE -> (SOME
             stackSem_Error,s))`;
   `stackSem_evaluate (stackLang_Set name v,s) =
         (if ~(stackSem_state_use_store s) then (SOME
             stackSem_Error,s) else
         match stackSem_get_var v s with SOME w ->
             (NONE,stackSem_set_store name w s) | NONE -> (SOME
             stackSem_Error,s))`;
   `stackSem_evaluate (stackLang_OpCurrHeap binop v src,s) =
         (if ~(stackSem_state_use_store s) then (SOME
             stackSem_Error,s) else
         match stackSem_word_exp s (wordLang_Op binop
             [wordLang_Var src; wordLang_Lookup CurrHeap]) with SOME
             w -> (NONE,stackSem_set_var v (wordLang_Word w) s) | _82
             -> (SOME stackSem_Error,s))`;
   `stackSem_evaluate (stackLang_Tick,s) =
         (if stackSem_state_clock s = 0 then (SOME
             stackSem_TimeOut,stackSem_empty_env s) else
             (NONE,stackSem_dec_clock s))`;
   `stackSem_evaluate (stackLang_Seq c1 c2,s) =
         (let (res,s1) = stackSem_fix_clock s (stackSem_evaluate
             (c1,s)) in
           if res = NONE then stackSem_evaluate (c2,s1) else
               (res,s1))`;
   `stackSem_evaluate (stackLang_Return n,s) =
         (match stackSem_get_var n s with SOME (wordLang_Loc l1
             l2) -> (SOME (stackSem_Result (wordLang_Loc l1 l2)),s) |
             _85 -> (SOME stackSem_Error,s))`;
   `stackSem_evaluate (stackLang_Raise n,s) =
         (match stackSem_get_var n s with SOME (wordLang_Loc l1
             l2) -> (SOME (stackSem_Exception (wordLang_Loc l1
             l2)),s) | _88 -> (SOME stackSem_Error,s))`;
   `stackSem_evaluate (stackLang_Break n,s) = (SOME (stackLang_Break
    n),s)`;
   `stackSem_evaluate (stackLang_Continue n,s) = (SOME
    (stackLang_Continue n),s)`;
   `stackSem_evaluate (stackLang_If cmp r1 ri c1 c2,s) =
        (match (stackSem_get_var r1 s,stackSem_get_var_imm ri s)
            with (SOME x,SOME y) ->
         (match wordSem_word_cmp cmp x y with SOME T ->
             stackSem_evaluate (c1,s) | SOME F -> stackSem_evaluate
             (c2,s) | NONE -> (SOME stackSem_Error,s)) | _91 -> (SOME
             stackSem_Error,s))`;
   `stackSem_evaluate (stackLang_Loop c1,s) =
        (let (res,s1) = stackSem_fix_clock s (stackSem_evaluate
            (c1,s)) in
           if stackSem_cont_loop res then
             (if stackSem_state_clock s1 = 0 then (SOME
                 stackSem_TimeOut,stackSem_empty_env s1) else
                stackSem_evaluate (stackSem_STOP ((stackLang_Loop
                    c1:'a stackLang_prog)),stackSem_dec_clock s1))
                    else (stackSem_exit_loop res,s1))`;
   `stackSem_evaluate (stackLang_JumpLower r1 r2 dest,s) =
        (match (stackSem_get_var r1 s,stackSem_get_var r2 s) with
            (SOME (wordLang_Word x),SOME (wordLang_Word y)) ->
          (if wordSem_word_cmp asm_Lower x y then
           (match stackSem_find_code (INL dest) (stackSem_state_regs
               s) (stackSem_state_code s) with NONE -> (SOME
               stackSem_Error,s) | SOME prog ->
               (if stackSem_state_clock s = 0 then (SOME
                   stackSem_TimeOut,stackSem_empty_env s) else
                 (match stackSem_evaluate
                     (prog,stackSem_dec_clock s) with (res,s) -> (if
                     stackSem_bad_fun_return res then (SOME
                     stackSem_Error,s) else (res,s))))) else
                     (NONE,s)) | _92 -> (SOME stackSem_Error,s))`;
   `stackSem_evaluate (stackLang_RawCall dest,s) =
        (match sptree_lookup dest (stackSem_state_code s) with NONE
            -> (SOME stackSem_Error,s) | SOME prog ->
           (match stackSem_dest_Seq prog with SOME (_93,body) ->
               (if stackSem_state_clock s = 0 then (SOME
                   stackSem_TimeOut,stackSem_empty_env s) else
                 (match stackSem_evaluate
                     (body,stackSem_dec_clock s) with (res,s) -> (if
                     stackSem_bad_fun_return res then (SOME
                     stackSem_Error,s) else (res,s)))) | _94 -> (SOME
                     stackSem_Error,s)) | _95 -> (SOME
                     stackSem_Error,s))`;
   `stackSem_evaluate (stackLang_Call ret dest handler,s) =
         (match ret with
           // tail call
           NONE ->
           (match stackSem_find_code dest (stackSem_state_regs s)
               (stackSem_state_code s) with NONE -> (SOME
               stackSem_Error,s) | SOME prog ->
               (if ~(handler = NONE) then (SOME stackSem_Error,s)
                   else
               if stackSem_state_clock s = 0 then (SOME
                   stackSem_TimeOut,stackSem_empty_env s) else
                 (match stackSem_fix_clock (stackSem_dec_clock s)
                     (stackSem_evaluate (prog,stackSem_dec_clock s))
                     with (res,s) -> (if stackSem_bad_fun_return res
                     then (SOME stackSem_Error,s) else (res,s))))) |
           // returning call, returns into var n
           SOME (ret_handler,link_reg',l1,l2) ->
           (match stackSem_find_code dest (stackSem_state_regs s \\
               link_reg') (stackSem_state_code s) with NONE -> (SOME
               stackSem_Error,s) | SOME prog ->
               (if stackSem_state_clock s = 0 then (SOME
                   stackSem_TimeOut,stackSem_empty_env s) else
                 (match stackSem_fix_clock (stackSem_dec_clock
                     (stackSem_set_var link_reg' (wordLang_Loc l1 l2)
                     s))
                 (stackSem_evaluate (prog,stackSem_dec_clock
                     (stackSem_set_var link_reg' (wordLang_Loc l1 l2)
                     s))) with (SOME (stackSem_Result x),s2) ->
                      (if ~(x = wordLang_Loc l1 l2) then (SOME
                          stackSem_Error,s2) else stackSem_evaluate
                          (ret_handler,s2)) | (SOME (stackSem_Exception
                          x),s2) ->
                      (match handler with
                         // if handler is present, then handle exc
                         NONE -> (SOME (stackSem_Exception x),s2) |
                             SOME (h,l1,l2) ->
                          (if ~(x = wordLang_Loc l1 l2) then (SOME
                              stackSem_Error,s2) else
                            stackSem_evaluate (h,s2))) | (NONE,s)
                                -> (SOME stackSem_Error,s) | (SOME
                                (stackLang_Break _106),s) -> (SOME
                                stackSem_Error,s) | (SOME
                                (stackLang_Continue _107),s) -> (SOME
                                stackSem_Error,s) | (res,s) ->
                                (res,s)))))`;
   `stackSem_evaluate (stackLang_Install ptr len dptr dlen ret,s) =
        (match (stackSem_get_var ptr s,stackSem_get_var len
            s,stackSem_get_var dptr s,stackSem_get_var dlen s) with
            (SOME (wordLang_Word w1),SOME (wordLang_Word w2),SOME
            (wordLang_Word w3),SOME (wordLang_Word w4)) ->
            (let (cfg,progs,bm) = stackSem_state_compile_oracle s 0
                in
           (match (buffer_flush (stackSem_state_code_buffer s) w1
               w2,
                  (if stackSem_state_use_stack s then buffer_flush
                      (stackSem_state_data_buffer s) w3 w4 else SOME
                      (bm,stackSem_state_data_buffer s))) with (
             SOME (bytes,cb),SOME (data,db)) ->
            (let new_oracle = misc_shift_seq 1
                (stackSem_state_compile_oracle s) in
            (match (stackSem_state_compile s cfg progs,progs) with
                (SOME (bytes',cfg'),CONS (k,prog) _116) ->
                (if bytes = bytes' /\ data = bm /\ FST (new_oracle
                    0) = cfg' then
                let s' = stackSem_state_compile_oracle_fupd (K
                    new_oracle) (stackSem_state_fp_regs_fupd (K FEMPTY)
                    (stackSem_state_regs_fupd (K ((DRESTRICT
                    (stackSem_state_regs s)
                    (stackSem_state_ffi_save_regs s)) |+
                    (ptr,wordLang_Loc k 0))) (stackSem_state_code_fupd
                    (K (sptree_union (stackSem_state_code s) (fromAList
                    progs))) (stackSem_state_data_buffer_fupd (K db)
                    (stackSem_state_code_buffer_fupd (K cb)
                    (stackSem_state_bitmaps_fupd (K (APPEND
                    (stackSem_state_bitmaps s) bm))
                    s)))))) in
                  (NONE,s') else (SOME stackSem_Error,s)) | _117
                      -> (SOME stackSem_Error,s))) | _118 -> (SOME
                      stackSem_Error,s))) | _119 -> (SOME
                      stackSem_Error,s))
    // This order is convenient because it means all of s.code's entries are preserved
    // TODO: this might need to be a new field, cc_save_regs`;
   `stackSem_evaluate (stackLang_ShMemOp op r (Addr a w),s) =
        (match stackSem_word_exp s (wordLang_Op asm_Add
            [wordLang_Var a; wordLang_Const w]) with SOME a ->
             (if stackSem_state_clock s = 0 then (SOME
                 stackSem_TimeOut,stackSem_empty_env s) else
               sh_mem_op op r a (stackSem_dec_clock s)) | _120 ->
                   (SOME stackSem_Error,s))`;
   `stackSem_evaluate (stackLang_CodeBufferWrite r1 r2,s) =
        (match (stackSem_get_var r1 s,stackSem_get_var r2 s) with
            (SOME (wordLang_Word w1),SOME (wordLang_Word w2)) ->
              (match buffer_write (stackSem_state_code_buffer s) w1
                  (w2w w2) with SOME new_cb ->
                (NONE,stackSem_state_code_buffer_fupd (K new_cb)
                    s) | _125 -> (SOME stackSem_Error,s)) | _126 ->
                    (SOME stackSem_Error,s))`;
   `stackSem_evaluate (stackLang_DataBufferWrite r1 r2,s) =
        (if ~(stackSem_state_use_stack s) then (SOME
            stackSem_Error,s) else
        (match (stackSem_get_var r1 s,stackSem_get_var r2 s) with
            (SOME (wordLang_Word w1),SOME (wordLang_Word w2)) ->
              (match buffer_write (stackSem_state_data_buffer s) w1
                  w2 with SOME new_db ->
                (NONE,stackSem_state_data_buffer_fupd (K new_db)
                    s) | _131 -> (SOME stackSem_Error,s)) | _132 ->
                    (SOME stackSem_Error,s)))`;
   `stackSem_evaluate (stackLang_FFI ffi_index ptr len ptr2 len2 ret,s)
    =
       (match (stackSem_get_var len s,stackSem_get_var ptr
           s,stackSem_get_var len2 s,stackSem_get_var ptr2 s) with (SOME
           (wordLang_Word w),SOME (wordLang_Word w2),SOME (wordLang_Word
           w3),SOME (wordLang_Word w4)) ->
             (match (read_bytearray w2 (w2n w) (mem_load_byte_aux
                 (stackSem_state_memory s) (stackSem_state_mdomain s)
                 (stackSem_state_be s)),
                    read_bytearray w4 (w2n w3) (mem_load_byte_aux
                        (stackSem_state_memory s)
                        (stackSem_state_mdomain s) (stackSem_state_be
                        s))) with (SOME bytes,SOME bytes2) ->
                 (match call_FFI (stackSem_state_ffi s) (ffi_ExtCall
                     ffi_index) bytes bytes2 with FFI_final outcome ->
                     (SOME (stackSem_FinalFFI outcome),s) | FFI_return
                     new_ffi new_bytes ->
                      (let new_m = write_bytearray w4 new_bytes
                          (stackSem_state_memory s)
                          (stackSem_state_mdomain s) (stackSem_state_be
                          s) in
                        (NONE,stackSem_state_ffi_fupd (K new_ffi)
                            (stackSem_state_fp_regs_fupd (K FEMPTY)
                            (stackSem_state_regs_fupd (K (DRESTRICT
                            (stackSem_state_regs s)
                            (stackSem_state_ffi_save_regs s)))
                            (stackSem_state_memory_fupd (K new_m)
                            s)))))) | _135 -> (SOME
                            stackSem_Error,s)) | res -> (SOME
                            stackSem_Error,s))`;
   `stackSem_evaluate (stackLang_LocValue r l1 l2,s) =
         (if loc_check (stackSem_state_code s) (l1,l2) then
           (NONE,stackSem_set_var r (wordLang_Loc l1 l2) s) else
               (SOME stackSem_Error,s))`;
   `stackSem_evaluate (stackLang_StackAlloc n,s) =
         (if ~(stackSem_state_use_stack s) then (SOME
             stackSem_Error,s) else
         if stackSem_state_stack_space s < n then (SOME
             (stackSem_Halt (wordLang_Word (n2w 2))),stackSem_empty_env
             s) else
           (NONE,stackSem_state_stack_space_fupd (K
               (stackSem_state_stack_space s - n)) s))`;
   `stackSem_evaluate (stackLang_StackFree n,s) =
         (if ~(stackSem_state_use_stack s) then (SOME
             stackSem_Error,s) else
         if LENGTH (stackSem_state_stack s) <
             stackSem_state_stack_space s + n then (SOME
             stackSem_Error,stackSem_empty_env s) else
           (NONE,stackSem_state_stack_space_fupd (K
               (stackSem_state_stack_space s + n)) s))`;
   `stackSem_evaluate (stackLang_StackLoad r n,s) =
         (if ~(stackSem_state_use_stack s) then (SOME
             stackSem_Error,s) else
         if stackSem_state_stack_space s + n < LENGTH
             (stackSem_state_stack s) then (NONE,stackSem_set_var r
             (EL (stackSem_state_stack_space s + n)
             (stackSem_state_stack s)) s) else (SOME
             stackSem_Error,stackSem_empty_env s))`;
   `stackSem_evaluate (stackLang_StackLoadAny r rn,s) =
         (if ~(stackSem_state_use_stack s) then (SOME
             stackSem_Error,s) else
           match stackSem_get_var rn s with SOME (wordLang_Word
               (w:'a word)) ->
             (let i = stackSem_state_stack_space s + w2n (w >>>
                 asmSem_word_shift (:'a)) in
               if i < LENGTH (stackSem_state_stack s) /\
                  ((w >>> asmSem_word_shift (:'a)) <<
                      asmSem_word_shift (:'a) = w) then
                      (NONE,stackSem_set_var r (EL i
                      (stackSem_state_stack s)) s) else (SOME
                      stackSem_Error,stackSem_empty_env s)) | _136 ->
                      (SOME stackSem_Error,stackSem_empty_env s))`;
   `stackSem_evaluate (stackLang_StackStore r n,s) =
         (if ~(stackSem_state_use_stack s) then (SOME
             stackSem_Error,s) else
         if LENGTH (stackSem_state_stack s) <=
             stackSem_state_stack_space s + n then (SOME
             stackSem_Error,stackSem_empty_env s) else
           match stackSem_get_var r s with NONE -> (SOME
               stackSem_Error,stackSem_empty_env s) | SOME v ->
               (NONE,stackSem_state_stack_fupd (K (LUPDATE v
               (stackSem_state_stack_space s + n)
               (stackSem_state_stack s))) s))`;
   `stackSem_evaluate (stackLang_StackStoreAny r rn,s) =
         (if ~(stackSem_state_use_stack s) then (SOME
             stackSem_Error,s) else
           match (stackSem_get_var r s,stackSem_get_var rn s) with
               (SOME v,SOME (wordLang_Word (w:'a word))) ->
             (let i = stackSem_state_stack_space s + w2n (w >>>
                 asmSem_word_shift (:'a)) in
               if i < LENGTH (stackSem_state_stack s) /\
                  ((w >>> asmSem_word_shift (:'a)) <<
                      asmSem_word_shift (:'a) = w) then
                      (NONE,stackSem_state_stack_fupd (K (LUPDATE v i
                      (stackSem_state_stack s))) s) else (SOME
                      stackSem_Error,stackSem_empty_env s)) | _137 ->
                      (SOME stackSem_Error,stackSem_empty_env s))`;
   `stackSem_evaluate (stackLang_StackGetSize r,s) =
         (if ~(stackSem_state_use_stack s) then (SOME
             stackSem_Error,s) else
         (NONE,stackSem_set_var r (wordLang_Word (n2w
             (stackSem_state_stack_space s))) s))`;
   `stackSem_evaluate (stackLang_StackSetSize r,s) =
         (if ~(stackSem_state_use_stack s) then (SOME
             stackSem_Error,s) else
         match stackSem_get_var r s with SOME (wordLang_Word (w:'a
             word)) ->
             (if LENGTH (stackSem_state_stack s) <= w2n w then (SOME
                 stackSem_Error,stackSem_empty_env s) else
                 (NONE,stackSem_set_var r (wordLang_Word (w <<
                 asmSem_word_shift (:'a)))
                           (stackSem_state_stack_space_fupd (K
                               (w2n w)) s))) | _138 -> (SOME
                               stackSem_Error,s))`;
   `stackSem_evaluate (stackLang_BitmapLoad r v,s) =
         (if ~(stackSem_state_use_stack s) \/ r = v then (SOME
             stackSem_Error,s) else
         match stackSem_get_var v s with SOME (wordLang_Word w) ->
             (if LENGTH (stackSem_state_bitmaps s) <= w2n w
                 then (SOME stackSem_Error,s) else
                 (NONE,stackSem_set_var r (wordLang_Word (EL (w2n
                 w) (stackSem_state_bitmaps s))) s)) | _139 ->
                 (SOME stackSem_Error,s))`];;

(* We prove that the clock never increases. *)

(* gc_clock *)
let stackSem_gc_clock = prove
 (`!s1 s2. (stackSem_gc s1 = SOME s2) ==> stackSem_state_clock s2 <=
  stackSem_state_clock s1`,
  CHEAT_TAC);;

(* alloc_clock *)
let stackSem_alloc_clock = prove
 (`!xs s1 vs s2. (stackSem_alloc x s1 = (vs,s2)) ==>
  stackSem_state_clock s2 <= stackSem_state_clock s1`,
  CHEAT_TAC);;

let store_const_sem_clock = prove
 (`!s1 v s2. (store_const_sem t1 t2 s1 = (v,s2)) ==>
  stackSem_state_clock s2 <= stackSem_state_clock s1`,
  CHEAT_TAC);;

(* inst_clock[local] *)
let stackSem_inst_clock = prove
 (`stackSem_inst i s = SOME s2 ==> stackSem_state_clock s2 <=
  stackSem_state_clock s`,
  CHEAT_TAC);;

(* [local] *)
let sh_mem_op_clock = prove
 (`sh_mem_op op r a s = (res,s') ==> stackSem_state_clock s' <=
  stackSem_state_clock s`,
  CHEAT_TAC);;

(* evaluate_clock *)
let stackSem_evaluate_clock = prove
 (`!xs s1 vs s2. (stackSem_evaluate (xs,s1) = (vs,s2)) ==>
  stackSem_state_clock s2 <= stackSem_state_clock s1`,
  CHEAT_TAC);;

(* fix_clock_evaluate *)
let stackSem_fix_clock_evaluate = prove
 (`stackSem_fix_clock s (stackSem_evaluate (xs,s)) = stackSem_evaluate
  (xs,s)`,
  CHEAT_TAC);;

(* HOL4 stackSemScript.sml:1108-1109: a theorem that HOL4 states as
   the value of an ML expression: evaluate_def *)

(* HOL4 stackSemScript.sml:1111-1112: a theorem that HOL4 states as
   the value of an ML expression: evaluate_ind *)

(* observational semantics *)

let stackSem_semantics_def = new_definition
  `stackSem_semantics start' s =
   (let prog = stackLang_Call NONE (INL start') NONE in
   if ?k. let res = FST (stackSem_evaluate
     (prog,stackSem_state_clock_fupd (K k) s)) in ~(res = SOME
     stackSem_TimeOut) /\ ~(res = SOME (stackSem_Result (wordLang_Loc 1
     0))) /\
            (!w. ~(res = SOME (stackSem_Halt (wordLang_Word w)))) /\
              (!f. ~(res = SOME (stackSem_FinalFFI f))) then ffi_Fail
              else
     match some (\res.
       ?k t r outcome.
         stackSem_evaluate (prog,stackSem_state_clock_fupd (K k) s) =
           (SOME r,t) /\
         (match r with stackSem_FinalFFI e -> outcome =
           ffi_FFI_outcome e | stackSem_Halt w -> outcome = (if w =
           wordLang_Word (n2w 0) then ffi_Success else
           ffi_Resource_limit_hit) | stackSem_Result _140 -> outcome =
           ffi_Success | _141 -> F) /\
         res = ffi_Terminate outcome (ffi_state_io_events
           (stackSem_state_ffi t))) with SOME res -> res | NONE ->
       ffi_Diverge
          (build_lprefix_lub
            (IMAGE (\k. fromList (ffi_state_io_events
              (stackSem_state_ffi (SND (stackSem_evaluate
              (prog,stackSem_state_clock_fupd (K k) s)))))) UNIV)))`;;

(* record accessors *)

let read_stack_def = new_definition
  `read_stack s = stackSem_state_stack (s:('a,'b,'c)stackSem_state)`;;

let read_stack_space_def = new_definition
  `read_stack_space s = stackSem_state_stack_space
  (s:('a,'b,'c)stackSem_state)`;;

(* clean up *)

(* HOL4 stackSemScript.sml:1154: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
