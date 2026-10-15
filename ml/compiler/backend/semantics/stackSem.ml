(* ======================================================== *)
(*  stackSem: ported from HOL4's
    compiler/backend/semantics/stackSemScript.sml  *)
(* ======================================================== *)

(*
  The formal semantics of stackLang
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/export.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/alignment.ml";;
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
        match filter_bitmap bs rs with NONE -> NONE | SOME (ts,rs')
          -> SOME (r :: ts,rs')
        | (_1,_2) -> NONE`;;

let map_bitmap_def = cake_define
  `map_bitmap x1 ts rs =
        match (x1,ts,rs) with
          ([],ts,rs) -> SOME ([],ts,rs)
        | ((F :: bs),ts,(r :: rs)) ->
        match map_bitmap bs ts rs with NONE -> NONE | SOME (xs,ys,zs)
          -> SOME (r :: xs,ys,zs)
        | ((T :: bs),(t :: ts),(r :: rs)) ->
        match map_bitmap bs ts rs with NONE -> NONE | SOME (xs,ys,zs)
          -> SOME (t :: xs,ys,zs)
        | (_3,_4,_5) -> NONE`;;

let read_bitmap_def = cake_define
  `(read_bitmap [] = NONE) /\
   (read_bitmap ((w:'a word) :: ws) =
      (if word_msb w then
        match read_bitmap ws with NONE -> NONE | SOME bs -> SOME
          (GENLIST (\i. FAPPLY w i) (dimindex (:'a) - 1) ++ bs) else
        SOME (GENLIST (\i. FAPPLY w i) (bit_length w - 1))))`;;

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

let mem_store_def = cake_define
  `stackSem_mem_store (addr':'a word) (w:'a word_loc)
  (s:('a,'c,'ffi)stackSem_state) =
     (if addr' IN ?_mdomain s then
       SOME (?_memory_fupd (K ((addr' =+ w) (?_memory s))) s) else
         NONE)`;;
hol4_overload "mem_store" "stackSem_mem_store";;

let mem_load_def = cake_define
  `stackSem_mem_load (addr':'a word) (s:('a,'c,'ffi)stackSem_state) =
     (if addr' IN ?_mdomain s then
       SOME (?_memory s addr') else NONE)`;;
hol4_overload "mem_load" "stackSem_mem_load";;

let dec_clock_def = cake_define
  `stackSem_dec_clock (s:('a,'c,'ffi)stackSem_state) = ?_clock_fupd
  (K (?_clock s - 1)) s`;;
hol4_overload "dec_clock" "stackSem_dec_clock";;

let _ = size_thms "exp";;
(* HOL4 termination: \\ REPEAT STRIP_TAC \\ IMP_RES_TAC
   wordLangTheory.MEM_IMP_exp_size \\ TRY (FIRST_X_ASSUM (ASSUME_TAC
   o Q.SPEC `ARB`)) \\ DECIDE_TAC *)
let word_exp_def = cake_define_wf
  `MEASURE (exp_size ARB o SND)`
  `(stackSem_word_exp s (Const w) = SOME w) /\
   (stackSem_word_exp s (Var v) =
      (match FLOOKUP (stackSem_state_regs s) v with SOME (Word w) ->
        SOME w | _11 -> NONE)) /\
   (stackSem_word_exp s (Lookup name) =
      (match FLOOKUP (?_store s) name with SOME (Word w) -> SOME w |
        _12 -> NONE)) /\
   (stackSem_word_exp s (Load addr') =
      (match stackSem_word_exp s addr' with SOME w -> (match mem_load
        w s with SOME (Word w) -> SOME w | _13 -> NONE) | _14 -> NONE))
        /\
   (stackSem_word_exp s (Op op wexps) =
      (let ws = MAP (stackSem_word_exp s) wexps in
        if EVERY IS_SOME ws then word_op op (MAP THE ws) else NONE))
          /\
   (stackSem_word_exp s (Shift sh wexp wexp1) =
      (match (stackSem_word_exp s wexp,stackSem_word_exp s wexp1)
        with (SOME w,SOME w1) -> word_sh sh w (w2n w1) | _15 ->
        NONE))`;;
hol4_overload "word_exp" "stackSem_word_exp";;

let get_var_def = cake_define
  `stackSem_get_var v (s:('a,'c,'ffi)stackSem_state) = FLOOKUP
  (stackSem_state_regs s) v`;;
hol4_overload "get_var" "stackSem_get_var";;

let get_vars_def = cake_define
  `(stackSem_get_vars [] s = SOME []) /\
   (stackSem_get_vars (v :: vs) s =
      (match get_var v s with NONE -> NONE | SOME x -> (match
        stackSem_get_vars vs s with NONE -> NONE | SOME xs -> SOME (x
        :: xs))))`;;
hol4_overload "get_vars" "stackSem_get_vars";;

let get_fp_var_def = cake_define
  `stackSem_get_fp_var v (s:('a,'c,'ffi)stackSem_state) = FLOOKUP
  (?_fp_regs s) v`;;
hol4_overload "get_fp_var" "stackSem_get_fp_var";;

let set_var_def = cake_define
  `stackSem_set_var v x (s:('a,'c,'ffi)stackSem_state) =
     (stackSem_state_regs_fupd (K (stackSem_state_regs s |+
       (v,x))) s)`;;
hol4_overload "set_var" "stackSem_set_var";;

let set_fp_var_def = cake_define
  `stackSem_set_fp_var v x (s:('a,'c,'ffi)stackSem_state) =
     (?_fp_regs_fupd (K (?_fp_regs s |+ (v,x))) s)`;;
hol4_overload "set_fp_var" "stackSem_set_fp_var";;

let set_store_def = cake_define
  `set_store v x (s:('a,'c,'ffi)stackSem_state) = (?_store_fupd (K
  (?_store s |+ (v,x))) s)`;;

let empty_env_def = cake_define
  `stackSem_empty_env (s:('a,'c,'ffi)stackSem_state) = ?_stack_fupd
  (K []) (stackSem_state_regs_fupd (K FEMPTY) s)`;;
hol4_overload "empty_env" "stackSem_empty_env";;

let sh_mem_store_def = cake_define
  `(sh_mem_store r (a:'a word) (s:('a,'c,'ffi)stackSem_state):('a
  stackSem_result) option#('a,'c,'ffi)stackSem_state) =
   (match get_var r s with
      SOME (Word w) ->
        (if a IN ?_sh_mdomain s then
          (match call_FFI (?_ffi s) (SharedMem MappedWrite) [(n2w
            0):word8]
                         (word_to_bytes w F ++ word_to_bytes a F)
                           with
             FFI_final outcome -> (SOME (FinalFFI outcome),s) |
               FFI_return new_ffi new_bytes -> (NONE,?_ffi_fupd (K
               new_ffi) s)) else (SOME Error,s)) | _16 -> (SOME
               Error,s))`;;

let sh_mem_load_def = cake_define
  `(sh_mem_load r (a:'a word) (s:('a,'c,'ffi)stackSem_state):('a
  stackSem_result) option#('a,'c,'ffi)stackSem_state) =
   (if a IN ?_sh_mdomain s then
     (match call_FFI (?_ffi s) (SharedMem MappedRead) [(n2w 0):word8]
                    (word_to_bytes a F) with
        FFI_final outcome -> (SOME (FinalFFI outcome),s) | FFI_return
          new_ffi new_bytes ->
          (NONE,?_ffi_fupd (K new_ffi) (stackSem_state_regs_fupd (K
            (stackSem_state_regs s |+ (r,Word (word_of_bytes F (n2w 0)
            new_bytes))))
           s))) else (SOME Error,s))`;;

let sh_mem_store_byte_def = cake_define
  `(sh_mem_store_byte r (a:'a word) (s:('a,'c,'ffi)stackSem_state):('a
  stackSem_result) option#('a,'c,'ffi)stackSem_state) =
   (match get_var r s with
      SOME (Word w) ->
        (if byte_align a IN ?_sh_mdomain s then
          (match call_FFI (?_ffi s) (SharedMem MappedWrite) [(n2w
            1):word8]
                         ([get_byte (n2w 0) w F] ++ word_to_bytes a
                           F) with
             FFI_final outcome -> (SOME (FinalFFI outcome),s) |
               FFI_return new_ffi new_bytes -> (NONE,?_ffi_fupd (K
               new_ffi) s)) else (SOME Error,s)) | _17 -> (SOME
               Error,s))`;;

let sh_mem_store16_def = cake_define
  `(sh_mem_store16 r (a:'a word) (s:('a,'c,'ffi)stackSem_state):('a
  stackSem_result) option#('a,'c,'ffi)stackSem_state) =
   (match get_var r s with
      SOME (Word w) ->
        (if byte_align a IN ?_sh_mdomain s then
          (match call_FFI (?_ffi s) (SharedMem MappedWrite) [(n2w
            2):word8]
                         (TAKE 2 (word_to_bytes w F) ++ word_to_bytes
                           a F) with
             FFI_final outcome -> (SOME (FinalFFI outcome),s) |
               FFI_return new_ffi new_bytes -> (NONE,?_ffi_fupd (K
               new_ffi) s)) else (SOME Error,s)) | _18 -> (SOME
               Error,s))`;;

let sh_mem_store32_def = cake_define
  `(sh_mem_store32 r (a:'a word) (s:('a,'c,'ffi)stackSem_state):('a
  stackSem_result) option#('a,'c,'ffi)stackSem_state) =
   (match get_var r s with
      SOME (Word w) ->
        (if byte_align a IN ?_sh_mdomain s then
          (match call_FFI (?_ffi s) (SharedMem MappedWrite) [(n2w
            4):word8]
                         (TAKE 4 (word_to_bytes w F) ++ word_to_bytes
                           a F) with
             FFI_final outcome -> (SOME (FinalFFI outcome),s) |
               FFI_return new_ffi new_bytes -> (NONE,?_ffi_fupd (K
               new_ffi) s)) else (SOME Error,s)) | _19 -> (SOME
               Error,s))`;;

let sh_mem_load_byte_def = cake_define
  `(sh_mem_load_byte r (a:'a word) (s:('a,'c,'ffi)stackSem_state):('a
  stackSem_result) option#('a,'c,'ffi)stackSem_state) =
   (if byte_align a IN ?_sh_mdomain s then
     (match call_FFI (?_ffi s) (SharedMem MappedRead) [(n2w 1):word8]
       (word_to_bytes a F) with
        FFI_final outcome -> (SOME (FinalFFI outcome),s) | FFI_return
          new_ffi new_bytes ->
          (NONE,?_ffi_fupd (K new_ffi) (stackSem_state_regs_fupd (K
            (stackSem_state_regs s |+ (r,Word (word_of_bytes F (n2w 0)
            new_bytes))))
           s))) else (SOME Error,s))`;;

let sh_mem_load16_def = cake_define
  `(sh_mem_load16 r (a:'a word) (s:('a,'c,'ffi)stackSem_state):('a
  stackSem_result) option#('a,'c,'ffi)stackSem_state) =
   (if byte_align a IN ?_sh_mdomain s then
     (match call_FFI (?_ffi s) (SharedMem MappedRead) [(n2w 2):word8]
       (word_to_bytes a F) with
        FFI_final outcome -> (SOME (FinalFFI outcome),s) | FFI_return
          new_ffi new_bytes ->
          (NONE,?_ffi_fupd (K new_ffi) (stackSem_state_regs_fupd (K
            (stackSem_state_regs s |+ (r,Word (word_of_bytes F (n2w 0)
            new_bytes))))
           s))) else (SOME Error,s))`;;

let sh_mem_load32_def = cake_define
  `(sh_mem_load32 r (a:'a word) (s:('a,'c,'ffi)stackSem_state):('a
  stackSem_result) option#('a,'c,'ffi)stackSem_state) =
   (if byte_align a IN ?_sh_mdomain s then
     (match call_FFI (?_ffi s) (SharedMem MappedRead) [(n2w 4):word8]
       (word_to_bytes a F) with
        FFI_final outcome -> (SOME (FinalFFI outcome),s) | FFI_return
          new_ffi new_bytes ->
          (NONE,?_ffi_fupd (K new_ffi) (stackSem_state_regs_fupd (K
            (stackSem_state_regs s |+ (r,Word (word_of_bytes F (n2w 0)
            new_bytes))))
           s))) else (SOME Error,s))`;;

let sh_mem_op_def = cake_define
  `(sh_mem_op Load r ad (s:('a,'c,'ffi)stackSem_state) = sh_mem_load r
  ad s) /\
   (sh_mem_op Store r ad s = sh_mem_store r ad s) /\
   (sh_mem_op Load8 r ad s = sh_mem_load_byte r ad s) /\
   (sh_mem_op Store8 r ad s = sh_mem_store_byte r ad s) /\
   (sh_mem_op Load16 r ad s = sh_mem_load16 r ad s) /\
   (sh_mem_op Store16 r ad s = sh_mem_store16 r ad s) /\
   (sh_mem_op Load32 r ad s = sh_mem_load32 r ad s) /\
   (sh_mem_op Store32 r ad s = sh_mem_store32 r ad s)`;;

let full_read_bitmap_def = cake_define
  `full_read_bitmap bitmaps x2 =
        match x2 with
          (Word w) ->
        if w = (n2w 0) then NONE else read_bitmap (DROP (w2n (w -
          (n2w 1))) bitmaps)
        | _20 -> NONE`;;

(* HOL4 termination: \\ REPEAT STRIP_TAC \\ IMP_RES_TAC
   filter_bitmap_LENGTH \\ fs [] \\ decide_tac *)
let enc_stack_def = cake_define_wf
  `MEASURE (LENGTH o SND)`
  `(stackSem_enc_stack bitmaps [] = NONE) /\
   (stackSem_enc_stack bitmaps (w :: ws) =
      (if w = Word (n2w 0) then (if ws = [] then SOME [] else NONE)
        else
        match full_read_bitmap bitmaps w with NONE -> NONE | SOME bs
          ->
           (match filter_bitmap bs ws with NONE -> NONE | SOME
             (ts,ws') ->
               (match stackSem_enc_stack bitmaps ws' with NONE ->
                 NONE | SOME rs -> SOME (ts ++ rs)))))`;;
hol4_overload "enc_stack" "stackSem_enc_stack";;

(* HOL4 termination: \\ rw [] \\ IMP_RES_TAC map_bitmap_LENGTH \\ fs
   [LENGTH_NIL] \\ rw [] \\ fs [map_bitmap_def] \\ rw [] \\
   decide_tac *)
let dec_stack_def = cake_define_wf
  `MEASURE (LENGTH o SND o SND)`
  `(stackSem_dec_stack bitmaps _21 [] = NONE) /\
   (stackSem_dec_stack bitmaps ts (w :: ws) =
     (if w = Word (n2w 0) then (if ts = [] /\ ws = [] then SOME [Word
       (n2w 0)] else NONE) else
      match full_read_bitmap bitmaps w with NONE -> NONE | SOME bs ->
         (match map_bitmap bs ts ws with NONE -> NONE | SOME
           (hd,ts',ws') ->
            (match stackSem_dec_stack bitmaps ts' ws' with NONE ->
              NONE | SOME rest -> SOME ([w] ++ hd ++ rest)))))`;;
hol4_overload "dec_stack" "stackSem_dec_stack";;

let gc_def = cake_define
  `gc s =
     (if LENGTH (?_stack s) < stackSem_state_stack_space s then NONE
       else
       let unused = TAKE (stackSem_state_stack_space s) (?_stack s)
         in
       let stack = DROP (stackSem_state_stack_space s) (?_stack s) in
         match enc_stack (stackSem_state_bitmaps s) (DROP
           (stackSem_state_stack_space s) (?_stack s)) with NONE -> NONE
           | SOME wl_list ->
           (match ?_gc_fun s (wl_list,?_memory s,?_mdomain s,?_store
             s) with NONE -> NONE | SOME (wl,m,st) ->
            (match dec_stack (stackSem_state_bitmaps s) wl stack with
              NONE -> NONE | SOME stack ->
                 SOME (?_memory_fupd (K m)
                   (stackSem_state_regs_fupd (K FEMPTY) (?_store_fupd
                   (K st) (?_stack_fupd (K (unused ++ stack))
                   s)))))))`;;

let has_space_def = cake_define
  `has_space wl store =
     (match (wl,FLOOKUP store NextFree,FLOOKUP store TriggerGC)
       with (Word w,SOME (Word n),SOME (Word l)) -> SOME (w2n w <=
       w2n (l - n)) | _22 -> NONE)`;;

let alloc_def = cake_define
  `alloc (w:'a word) (s:('a,'c,'ffi)stackSem_state) =
       (match gc (set_store AllocSize (Word w) s) with NONE -> (SOME
         Error,s) | SOME s ->
          (match FLOOKUP (?_store s) AllocSize with NONE -> (SOME
            Error,s) | SOME w ->
            (match has_space w (?_store s) with NONE -> (SOME
              Error,s) | SOME T ->
                         (NONE,s) | SOME F ->
                         (SOME (Halt (Word ((n2w 1):'a
                           word))),empty_env s))))`;;

let assign_def = cake_define
  `stackSem_assign reg exp s =
     (match word_exp s exp with NONE -> NONE | SOME w -> SOME
       (set_var reg (Word w) s))`;;
hol4_overload "assign" "stackSem_assign";;

let inst_def = cake_define
  `stackSem_inst i (s:('a,'c,'ffi)stackSem_state) =
     (match i with Skip -> SOME s | Const reg w -> assign reg (Const
       w) s | Arith (Binop bop r1 r2 ri) ->
         (if bop = Or /\ ri = Reg r2 then
           match FLOOKUP (stackSem_state_regs s) r2 with NONE -> NONE
             | SOME w -> SOME (set_var r1 w s) else
           assign r1
             (Op bop [Var r2; match ri with Reg r3 -> Var r3 | Imm w
               -> Const w]) s) | Arith (Shift sh r1 r2 ri) ->
         assign r1
           (Shift sh (Var r2) (match ri with Reg r3 -> Var r3 | Imm w
             -> Const w)) s | Arith (Div r1 r2 r3) ->
        (let vs = get_vars [r3; r2] s in
        match vs with
        SOME [Word q; Word w2] ->
          (if ~(q = (n2w 0)) then
            SOME (set_var r1 (Word (w2 / q)) s) else NONE) | _23 ->
              NONE) | Arith (AddCarry r1 r2 r3 r4) ->
         (let vs = get_vars [r2; r3; r4] s in
         match vs with
         SOME [Word l; Word r; Word c] ->
           (let res = w2n l + w2n r + (if c = ((n2w 0):'a word) then
             0 else 1) in
             SOME (set_var r4 (Word (if dimword (:'a) <= res then
               ((n2w 1):'a word) else (n2w 0)))
                  (set_var r1 (Word (n2w res)) s))) | _24 -> NONE) |
                    Arith (AddOverflow r1 r2 r3 r4) ->
         (let vs = get_vars [r2; r3] s in
         match vs with
         SOME [Word w2; Word w3] ->
           SOME (set_var r4 (Word (if ~(w2i (w2 + w3) = w2i w2 + w2i
             w3) then (n2w 1) else (n2w 0)))
                  (set_var r1 (Word (w2 + w3)) s)) | _25 -> NONE) |
                    Arith (SubOverflow r1 r2 r3 r4) ->
         (let vs = get_vars [r2; r3] s in
         match vs with
         SOME [Word w2; Word w3] ->
           SOME (set_var r4 (Word (if ~(w2i (w2 - w3) = w2i w2 - w2i
             w3) then (n2w 1) else (n2w 0)))
                  (set_var r1 (Word (w2 - w3)) s)) | _26 -> NONE) |
                    Arith (LongMul r1 r2 r3 r4) ->
         (let vs = get_vars [r3; r4] s in
         match vs with
         SOME [Word w3; Word w4] ->
          (let r = w2n w3 * w2n w4 in
            SOME (set_var r2 (Word (n2w r)) (set_var r1 (Word (n2w (r
              DIV dimword (:'a)))) s))) | _27 -> NONE) | Arith (LongDiv
              r1 r2 r3 r4 r5) ->
        (let vs = get_vars [r3; r4; r5] s in
        match vs with
        SOME [Word w3; Word w4; Word w5] ->
          (let n = w2n w3 * dimword (:'a) + w2n w4 in
          let d = w2n w5 in
          let q = n DIV d in
          if (~(d = 0) /\ q < dimword (:'a)) then
            SOME (set_var r1 (Word (n2w q)) (set_var r2 (Word (n2w (n
              MOD d))) s)) else NONE) | _28 -> NONE) | Mem Load r (Addr
              a w) ->
        (match word_exp s (Op Add [Var a; Const w]) with NONE -> NONE
          | SOME w ->
             (match mem_load w s with NONE -> NONE | SOME w -> SOME
               (set_var r w s))) | Mem Load8 r (Addr a w) ->
        (match word_exp s (Op Add [Var a; Const w]) with SOME w ->
            (match mem_load_byte_aux (?_memory s) (?_mdomain s) (?_be
              s) w with NONE -> NONE | SOME w -> SOME (set_var r (Word
              (w2w w)) s)) | _29 -> NONE) | Mem Load16 _30 _31 -> NONE |
              Mem Load32 r (Addr a w) ->
        (match word_exp s (Op Add [Var a; Const w]) with SOME w ->
            (match mem_load_32 (?_memory s) (?_mdomain s) (?_be s) w
              with NONE -> NONE | SOME w -> SOME (set_var r (Word (w2w
              w)) s)) | _32 -> NONE) | Mem Store r (Addr a w) ->
        (match (word_exp s (Op Add [Var a; Const w]),get_var r s)
          with (SOME a,SOME w) ->
             (match mem_store a w s with SOME s1 -> SOME s1 | NONE ->
               NONE) | _33 -> NONE) | Mem Store8 r (Addr a w) ->
        (match (word_exp s (Op Add [Var a; Const w]),get_var r s)
          with (SOME a,SOME (Word w)) ->
             (match mem_store_byte_aux (?_memory s) (?_mdomain s)
               (?_be s) a (w2w w) with SOME new_m -> SOME (?_memory_fupd
               (K new_m) s) | NONE -> NONE) | _34 -> NONE) | Mem Store16
               _35 _36 -> NONE | Mem Store32 r (Addr a w) ->
        (match (word_exp s (Op Add [Var a; Const w]),get_var r s)
          with (SOME a,SOME (Word w)) ->
             (match mem_store_32 (?_memory s) (?_mdomain s) (?_be s)
               a (w2w w) with SOME new_m -> SOME (?_memory_fupd (K
               new_m) s) | NONE -> NONE) | _37 -> NONE) | FP (FPLess r
               d1 d2) ->
       (match (get_fp_var d1 s,get_fp_var d2 s) with (SOME f1,SOME
         f2) ->
         SOME (set_var r
           (Word (if fp64_lessThan f1 f2 then (n2w 1) else (n2w 0)))
             s) | _38 -> NONE) | FP (FPLessEqual r d1 d2) ->
       (match (get_fp_var d1 s,get_fp_var d2 s) with (SOME f1,SOME
         f2) ->
         SOME (set_var r
           (Word (if fp64_lessEqual f1 f2 then (n2w 1) else (n2w 0)))
             s) | _39 -> NONE) | FP (FPEqual r d1 d2) ->
       (match (get_fp_var d1 s,get_fp_var d2 s) with (SOME f1,SOME
         f2) ->
         SOME (set_var r
           (Word (if fp64_equal f1 f2 then (n2w 1) else (n2w 0))) s)
             | _40 -> NONE) | FP (FPMov d1 d2) ->
       (match get_fp_var d2 s with SOME f ->
         SOME (set_fp_var d1 f s) | _41 -> NONE) | FP (FPAbs d1 d2)
           ->
       (match get_fp_var d2 s with SOME f ->
         SOME (set_fp_var d1 (fp64_abs f) s) | _42 -> NONE) | FP
           (FPNeg d1 d2) ->
       (match get_fp_var d2 s with SOME f ->
         SOME (set_fp_var d1 (fp64_negate f) s) | _43 -> NONE) | FP
           (FPSqrt d1 d2) ->
       (match get_fp_var d2 s with SOME f ->
         SOME (set_fp_var d1 (fp64_sqrt roundTiesToEven f) s) | _44
           -> NONE) | FP (FPAdd d1 d2 d3) ->
       (match (get_fp_var d2 s,get_fp_var d3 s) with (SOME f1,SOME
         f2) ->
         SOME (set_fp_var d1 (fp64_add roundTiesToEven f1 f2) s) |
           _45 -> NONE) | FP (FPSub d1 d2 d3) ->
       (match (get_fp_var d2 s,get_fp_var d3 s) with (SOME f1,SOME
         f2) ->
         SOME (set_fp_var d1 (fp64_sub roundTiesToEven f1 f2) s) |
           _46 -> NONE) | FP (FPMul d1 d2 d3) ->
       (match (get_fp_var d2 s,get_fp_var d3 s) with (SOME f1,SOME
         f2) ->
         SOME (set_fp_var d1 (fp64_mul roundTiesToEven f1 f2) s) |
           _47 -> NONE) | FP (FPDiv d1 d2 d3) ->
       (match (get_fp_var d2 s,get_fp_var d3 s) with (SOME f1,SOME
         f2) ->
         SOME (set_fp_var d1 (fp64_div roundTiesToEven f1 f2) s) |
           _48 -> NONE) | FP (FPFma d1 d2 d3) ->
       (match (get_fp_var d1 s,get_fp_var d2 s,get_fp_var d3 s) with
         (SOME f1,SOME f2,SOME f3) ->
         SOME (set_fp_var d1 (fpfma f1 f2 f3) s) | _49 -> NONE) | FP
           (FPMovToReg r1 r2 d) ->
       (match get_fp_var d s with SOME v ->
         (if dimindex (:'a) = 64 then
           SOME (set_var r1 (Word (w2w v)) s) else
           SOME (set_var r2 (Word ((63 >< 32) v)) (set_var r1 (Word
             ((31 >< 0) v)) s))) | _50 -> NONE) | FP (FPMovFromReg d r1
             r2) ->
       (if dimindex (:'a) = 64 then
         match get_var r1 s with
           SOME (Word w1) -> SOME (set_fp_var d (w2w w1) s) | _51 ->
             NONE else
         match (get_var r1 s,get_var r2 s) with
           (SOME (Word w1),SOME (Word w2)) -> SOME (set_fp_var d (w2
             @@ w1) s) | _52 -> NONE) | FP (FPToInt d1 d2) ->
       (match get_fp_var d2 s with
         NONE -> NONE | SOME f ->
       (match fp64_to_int roundTiesToEven f with
         NONE -> NONE | SOME i ->
         (let w = i2w i:word32 in
         if w2i w = i then
           (if dimindex (:'a) = 64 then
              SOME (set_fp_var d1 (w2w w) s) else
            match get_fp_var (d1 DIV 2) s with
              NONE -> NONE | SOME f ->
              (let (h,l) = if ODD d1 then (63,32) else (31,0) in
                   SOME (set_fp_var (d1 DIV 2) (bit_field_insert h l
                     w f) s))) else
           NONE))) | FP (FPFromInt d1 d2) ->
       (if dimindex (:'a) = 64 then
         match get_fp_var d2 s with SOME f ->
           (let i = w2i ((31 >< 0) f:word32) in
             SOME (set_fp_var d1 (int_to_fp64 roundTiesToEven i) s))
               | NONE -> NONE else
         match get_fp_var (d2 DIV 2) s with SOME v ->
           (let i = w2i (if ODD d2 then (63 >< 32) v else (31 >< 0)
             v:'a word) in
             SOME (set_fp_var d1 (int_to_fp64 roundTiesToEven i)
               s)) | NONE -> NONE | _53 -> NONE))`;;
hol4_overload "inst" "stackSem_inst";;

let get_var_imm_def = cake_define
  `(stackSem_get_var_imm ((Reg n):'a asm_reg_imm) s = get_var n s) /\
   (stackSem_get_var_imm (Imm w) s = SOME (Word w))`;;
hol4_overload "get_var_imm" "stackSem_get_var_imm";;

let find_code_def = cake_define
  `(stackSem_find_code (INL p) regs code = sptree_lookup p code) /\
   (stackSem_find_code (INR r) regs code =
      (match FLOOKUP regs r with
        SOME (Loc loc 0) -> lookup loc code | other -> NONE))`;;
hol4_overload "find_code" "stackSem_find_code";;

let fix_clock_def = cake_define
  `stackSem_fix_clock s (res,s1) = (res,?_clock_fupd (K (MIN (?_clock
  s) (?_clock s1))) s1)`;;
hol4_overload "fix_clock" "stackSem_fix_clock";;

let STOP_def = cake_define
  `stackSem_STOP x = x`;;
hol4_overload "STOP" "stackSem_STOP";;

let get_labels_def = cake_define
  `get_labels x1 =
        match x1 with
          (Seq p1 p2) -> get_labels p1 UNION get_labels p2
        | (If _54 _55 _56 p1 p2) -> get_labels p1 UNION get_labels p2
        | (Loop p) -> get_labels p
        | (Call ret _57 handler) ->
        (match ret with NONE -> {} | SOME (r,_58,l1,l2) -> (l1,l2)
          INSERT (get_labels r UNION
             (match handler with NONE -> {} | SOME (r,l1,l2) ->
               (l1,l2) INSERT get_labels r)))
        | (Halt _59) -> {}
        | _60 -> {}`;;

let loc_check_def = cake_define
  `loc_check code (l1,l2) <=>
     (l2 = 0 /\ l1 IN domain code) \/
     (?n e. lookup n code = SOME e /\ (l1,l2) IN get_labels e)`;;

let copy_words_for_pattern_def = cake_define
  `copy_words_for_pattern (pattern:'a word) (i:num) (a:'a word) (off:'a
  word) bs dm m =
     (if pattern = (n2w 0) then NONE else
     if pattern = (n2w 1) then SOME (i,a,m) else
       if a IN dm /\ i < LENGTH bs then
         let b = FAPPLY pattern 0 in
         let w = EL i bs in
         let m = (a =+ Word (if b then w + off else w)) m in
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
  `unset_var v (s:('a,'c,'ffi)stackSem_state) =
  stackSem_state_regs_fupd (K (stackSem_state_regs s \\ v)) s`;;

let store_const_sem_def = cake_define
  `store_const_sem t1 t2 (s:('a,'c,'ffi)stackSem_state) =
     (if ~ALL_DISTINCT [0; 1; 2; 3; t1; t2] then (SOME Error,s) else
       match (get_var 1 s,get_var 2 s,get_var 3 s) with (SOME (Word
         i),SOME (Word a),SOME (Word off)) ->
           (match copy_words (w2n i) a off (stackSem_state_bitmaps s)
             (?_mdomain s) (?_memory s) with NONE -> (SOME Error,s) |
             SOME (a,m) -> (NONE,
               (if stackSem_state_use_alloc s then unset_var 0 else
                 I)
                 (set_var t1 (Word (n2w 1)) (set_var t2 (Word (n2w
                   1))
                   (set_var 1 (Word (n2w 1)) (set_var 2 (Word a)
                     (?_memory_fupd (K m) s))))))) | _61 -> (SOME
                     Error,s))`;;

let check_store_consts_opt_def = cake_define
  `check_store_consts_opt t1 t2 NONE _62 = T /\
   check_store_consts_opt t1 t2 (SOME n) c =
     (lookup n c = SOME (Seq (StoreConsts t1 t2 NONE) (Return 0)))`;;

let dest_Seq_def = cake_define
  `stackSem_dest_Seq x1 =
      match x1 with
        (Seq p1 p2) -> SOME (p1,(p2:'a stackLang_prog))
      | _63 -> NONE`;;
hol4_overload "dest_Seq" "stackSem_dest_Seq";;

let bad_fun_return_def = cake_define
  `stackSem_bad_fun_return x1 =
      match x1 with
        NONE -> T
      | (SOME (Break _64)) -> T
      | (SOME (Continue _65)) -> T
      | _66 -> F`;;
hol4_overload "bad_fun_return" "stackSem_bad_fun_return";;

let cont_loop_def = cake_define
  `stackSem_cont_loop x1 =
      match x1 with
        NONE -> T
      | (SOME (Continue n)) -> (n = 0)
      | _67 -> F`;;
hol4_overload "cont_loop" "stackSem_cont_loop";;

let exit_loop_def = cake_define
  `stackSem_exit_loop res =
      match res with
        (SOME (Break n)) -> (if n = 0 then NONE else SOME (Break (n -
          1)))
      | (SOME (Continue n)) -> SOME (Continue (n - 1))
      | res -> res`;;
hol4_overload "exit_loop" "stackSem_exit_loop";;

let _ = size_thms "prog";;
(* HOL4 termination: \\ rpt strip_tac \\
   fs[empty_env_def,dec_clock_def,set_var_def,STOP_def] \\
   imp_res_tac fix_clock_IMP \\ fs [] \\ imp_res_tac (GSYM
   fix_clock_IMP) \\ fs [] \\ decide_tac *)
let evaluate_def = cake_define_wf
  `(inv_image (MEASURE I LEX MEASURE (prog_size (K 0)))
                              (\(xs,(s:('a,'c,'ffi)stackSem_state)).
                                (?_clock s,xs)))`
  `(stackSem_evaluate ((Skip:'a stackLang_prog),s) =
  (NONE,(s:('a,'c,'ffi)stackSem_state))) /\
   (stackSem_evaluate (Halt v,s) =
      (match get_var v s with SOME w -> (SOME (Halt w),empty_env s) |
        NONE -> (SOME Error,s))) /\
   (stackSem_evaluate (Alloc n,s) =
      (if ~stackSem_state_use_alloc s then (SOME Error,s) else
      match get_var n s with SOME (Word w) -> alloc w s | _93 ->
        (SOME Error,s))) /\
   (stackSem_evaluate (StoreConsts t1 t2 stub_opt,s) =
      (if ~stackSem_state_use_store s then (SOME Error,s) else
      if ~stackSem_state_use_alloc s /\ IS_SOME stub_opt then (SOME
        Error,s) else
      if ~check_store_consts_opt t1 t2 stub_opt (?_code s) then (SOME
        Error,s) else
        store_const_sem t1 t2 s)) /\
   (stackSem_evaluate (Inst i,s) =
      (match inst i s with SOME s1 -> (NONE,s1) | NONE -> (SOME
        Error,s))) /\
   (stackSem_evaluate (Get v name,s) =
      (if ~stackSem_state_use_store s then (SOME Error,s) else
      match FLOOKUP (?_store s) name with SOME x -> (NONE,set_var v x
        s) | NONE -> (SOME Error,s))) /\
   (stackSem_evaluate (Set name v,s) =
      (if ~stackSem_state_use_store s then (SOME Error,s) else
      match get_var v s with SOME w -> (NONE,set_store name w s) |
        NONE -> (SOME Error,s))) /\
   (stackSem_evaluate (OpCurrHeap binop v src,s) =
      (if ~stackSem_state_use_store s then (SOME Error,s) else
      match word_exp s (Op binop [Var src; Lookup CurrHeap]) with
        SOME w -> (NONE,set_var v (Word w) s) | _94 -> (SOME Error,s)))
        /\
   (stackSem_evaluate (Tick,s) =
      (if ?_clock s = 0 then (SOME TimeOut,empty_env s) else
        (NONE,dec_clock s))) /\
   (stackSem_evaluate (Seq c1 c2,s) =
      (let (res,s1) = fix_clock s (stackSem_evaluate (c1,s)) in
        if res = NONE then stackSem_evaluate (c2,s1) else (res,s1)))
          /\
   (stackSem_evaluate (Return n,s) =
      (match get_var n s with SOME (Loc l1 l2) -> (SOME (Result (Loc
        l1 l2)),s) | _95 -> (SOME Error,s))) /\
   (stackSem_evaluate (Raise n,s) =
      (match get_var n s with SOME (Loc l1 l2) -> (SOME (Exception
        (Loc l1 l2)),s) | _96 -> (SOME Error,s))) /\
   (stackSem_evaluate (Break n,s) = (SOME (Break n),s)) /\
   (stackSem_evaluate (Continue n,s) = (SOME (Continue n),s)) /\
   (stackSem_evaluate (If cmp r1 ri c1 c2,s) =
     (match (get_var r1 s,get_var_imm ri s) with (SOME x,SOME y) ->
      (match wordSem_word_cmp cmp x y with SOME T ->
        stackSem_evaluate (c1,s) | SOME F -> stackSem_evaluate (c2,s) |
        NONE -> (SOME Error,s)) | _97 -> (SOME Error,s))) /\
   (stackSem_evaluate (Loop c1,s) =
     (let (res,s1) = fix_clock s (stackSem_evaluate (c1,s)) in
        if cont_loop res then
          (if ?_clock s1 = 0 then (SOME TimeOut,empty_env s1) else
             stackSem_evaluate (STOP (Loop c1),dec_clock s1)) else
               (exit_loop res,s1))) /\
   (stackSem_evaluate (JumpLower r1 r2 dest,s) =
     (match (get_var r1 s,get_var r2 s) with (SOME (Word x),SOME
       (Word y)) ->
       (if word_cmp Lower x y then
        (match find_code (INL dest) (stackSem_state_regs s) (?_code
          s) with NONE -> (SOME Error,s) | SOME prog ->
            (if ?_clock s = 0 then (SOME TimeOut,empty_env s) else
              (match stackSem_evaluate (prog,dec_clock s) with
                (res,s) -> (if bad_fun_return res then (SOME Error,s)
                else (res,s))))) else (NONE,s)) | _98 -> (SOME
                Error,s))) /\
   (stackSem_evaluate (RawCall dest,s) =
     (match sptree_lookup dest (?_code s) with NONE -> (SOME Error,s)
       | SOME prog ->
        (match dest_Seq prog with SOME (_99,body) ->
            (if ?_clock s = 0 then (SOME TimeOut,empty_env s) else
              (match stackSem_evaluate (body,dec_clock s) with
                (res,s) -> (if bad_fun_return res then (SOME Error,s)
                else (res,s)))) | _100 -> (SOME Error,s)) | _101 ->
                (SOME Error,s))) /\
   (stackSem_evaluate (Call ret dest handler,s) =
      (match ret with NONE ->
        (match find_code dest (stackSem_state_regs s) (?_code s) with
          NONE -> (SOME Error,s) | SOME prog ->
            (if ~(handler = NONE) then (SOME Error,s) else
            if ?_clock s = 0 then (SOME TimeOut,empty_env s) else
              (match fix_clock (dec_clock s) (stackSem_evaluate
                (prog,dec_clock s)) with (res,s) -> (if bad_fun_return
                res then (SOME Error,s) else (res,s))))) | SOME
                (ret_handler,link_reg,l1,l2) ->
        (match find_code dest (stackSem_state_regs s \\ link_reg)
          (?_code s) with NONE -> (SOME Error,s) | SOME prog ->
            (if ?_clock s = 0 then (SOME TimeOut,empty_env s) else
              (match fix_clock (dec_clock (set_var link_reg (Loc l1
                l2) s))
              (stackSem_evaluate (prog,dec_clock (set_var link_reg
                (Loc l1 l2) s))) with (SOME (Result x),s2) ->
                   (if ~(x = Loc l1 l2) then (SOME Error,s2) else
                     stackSem_evaluate (ret_handler,s2)) | (SOME
                     (Exception x),s2) ->
                   (match handler with NONE -> (SOME (Exception
                     x),s2) | SOME (h,l1,l2) ->
                       (if ~(x = Loc l1 l2) then (SOME Error,s2) else
                         stackSem_evaluate (h,s2))) | (NONE,s) ->
                           (SOME Error,s) | (SOME (Break _102),s) ->
                           (SOME Error,s) | (SOME (Continue _103),s) ->
                           (SOME Error,s) | (res,s) -> (res,s)))))) /\
   (stackSem_evaluate (Install ptr len dptr dlen ret,s) =
     (match (get_var ptr s,get_var len s,get_var dptr s,get_var dlen
       s) with (SOME (Word w1),SOME (Word w2),SOME (Word w3),SOME (Word
       w4)) ->
         (let (cfg,progs,bm) = ?_compile_oracle s 0 in
        (match (buffer_flush (?_code_buffer s) w1 w2,
               (if stackSem_state_use_stack s then buffer_flush
                 (?_data_buffer s) w3 w4 else SOME (bm,?_data_buffer
                 s))) with (
          SOME (bytes,cb),SOME (data,db)) ->
         (let new_oracle = shift_seq 1 (?_compile_oracle s) in
         (match (?_compile s cfg progs,progs) with (SOME
           (bytes',cfg'),(k,prog) :: _104) ->
             (if bytes = bytes' /\ data = bm /\ FST (new_oracle 0) =
               cfg' then
             let s' = ?_compile_oracle_fupd (K new_oracle)
               (?_fp_regs_fupd (K FEMPTY) (stackSem_state_regs_fupd (K
               ((DRESTRICT (stackSem_state_regs s)
               (stackSem_state_ffi_save_regs s)) |+ (ptr,Loc k 0)))
               (?_code_fupd (K (union (?_code s) (fromAList progs)))
               (?_data_buffer_fupd (K db) (?_code_buffer_fupd (K cb)
               (stackSem_state_bitmaps_fupd (K (stackSem_state_bitmaps s
               ++ bm))
                 s)))))) in
               (NONE,s') else (SOME Error,s)) | _105 -> (SOME
                 Error,s))) | _106 -> (SOME Error,s))) | _107 -> (SOME
                 Error,s))) /\
   (stackSem_evaluate (ShMemOp op r (Addr a w),s) =
     (match word_exp s (Op Add [Var a; Const w]) with SOME a ->
          (if ?_clock s = 0 then (SOME TimeOut,empty_env s) else
            sh_mem_op op r a (dec_clock s)) | _108 -> (SOME
              Error,s))) /\
   (stackSem_evaluate (CodeBufferWrite r1 r2,s) =
     (match (get_var r1 s,get_var r2 s) with (SOME (Word w1),SOME
       (Word w2)) ->
           (match buffer_write (?_code_buffer s) w1 (w2w w2) with
             SOME new_cb ->
             (NONE,?_code_buffer_fupd (K new_cb) s) | _109 -> (SOME
               Error,s)) | _110 -> (SOME Error,s))) /\
   (stackSem_evaluate (DataBufferWrite r1 r2,s) =
     (if ~stackSem_state_use_stack s then (SOME Error,s) else
     (match (get_var r1 s,get_var r2 s) with (SOME (Word w1),SOME
       (Word w2)) ->
           (match buffer_write (?_data_buffer s) w1 w2 with SOME
             new_db ->
             (NONE,?_data_buffer_fupd (K new_db) s) | _111 -> (SOME
               Error,s)) | _112 -> (SOME Error,s)))) /\
   (stackSem_evaluate (FFI ffi_index ptr len ptr2 len2 ret,s) =
    (match (get_var len s,get_var ptr s,get_var len2 s,get_var ptr2
      s) with (SOME (Word w),SOME (Word w2),SOME (Word w3),SOME (Word
      w4)) ->
          (match (read_bytearray w2 (w2n w) (mem_load_byte_aux
            (?_memory s) (?_mdomain s) (?_be s)),
                 read_bytearray w4 (w2n w3) (mem_load_byte_aux
                   (?_memory s) (?_mdomain s) (?_be s))) with (SOME
                   bytes,SOME bytes2) ->
              (match call_FFI (?_ffi s) (ExtCall ffi_index) bytes
                bytes2 with FFI_final outcome -> (SOME (FinalFFI
                outcome),s) | FFI_return new_ffi new_bytes ->
                   (let new_m = write_bytearray w4 new_bytes
                     (?_memory s) (?_mdomain s) (?_be s) in
                     (NONE,?_ffi_fupd (K new_ffi) (?_fp_regs_fupd (K
                       FEMPTY) (stackSem_state_regs_fupd (K (DRESTRICT
                       (stackSem_state_regs s)
                       (stackSem_state_ffi_save_regs s))) (?_memory_fupd
                       (K new_m) s)))))) | _113 -> (SOME Error,s)) | res
                       -> (SOME Error,s))) /\
   (stackSem_evaluate (LocValue r l1 l2,s) =
      (if loc_check (?_code s) (l1,l2) then
        (NONE,set_var r (Loc l1 l2) s) else (SOME Error,s))) /\
   (stackSem_evaluate (StackAlloc n,s) =
      (if ~stackSem_state_use_stack s then (SOME Error,s) else
      if stackSem_state_stack_space s < n then (SOME (Halt (Word (n2w
        2))),empty_env s) else
        (NONE,stackSem_state_stack_space_fupd (K
          (stackSem_state_stack_space s - n)) s))) /\
   (stackSem_evaluate (StackFree n,s) =
      (if ~stackSem_state_use_stack s then (SOME Error,s) else
      if LENGTH (?_stack s) < stackSem_state_stack_space s + n then
        (SOME Error,empty_env s) else
        (NONE,stackSem_state_stack_space_fupd (K
          (stackSem_state_stack_space s + n)) s))) /\
   (stackSem_evaluate (StackLoad r n,s) =
      (if ~stackSem_state_use_stack s then (SOME Error,s) else
      if stackSem_state_stack_space s + n < LENGTH (?_stack s) then
        (NONE,set_var r (EL (stackSem_state_stack_space s + n) (?_stack
        s)) s) else (SOME Error,empty_env s))) /\
   (stackSem_evaluate (StackLoadAny r rn,s) =
      (if ~stackSem_state_use_stack s then (SOME Error,s) else
        match get_var rn s with SOME (Word (w:'a word)) ->
          (let i = stackSem_state_stack_space s + w2n (w >>>
            word_shift (:'a)) in
            if i < LENGTH (?_stack s) /\
               ((w >>> word_shift (:'a)) << word_shift (:'a) = w)
                 then (NONE,set_var r (EL i (?_stack s)) s) else (SOME
                 Error,empty_env s)) | _114 -> (SOME Error,empty_env
                 s))) /\
   (stackSem_evaluate (StackStore r n,s) =
      (if ~stackSem_state_use_stack s then (SOME Error,s) else
      if LENGTH (?_stack s) <= stackSem_state_stack_space s + n then
        (SOME Error,empty_env s) else
        match get_var r s with NONE -> (SOME Error,empty_env s) |
          SOME v -> (NONE,?_stack_fupd (K (LUPDATE v
          (stackSem_state_stack_space s + n) (?_stack s))) s))) /\
   (stackSem_evaluate (StackStoreAny r rn,s) =
      (if ~stackSem_state_use_stack s then (SOME Error,s) else
        match (get_var r s,get_var rn s) with (SOME v,SOME (Word
          (w:'a word))) ->
          (let i = stackSem_state_stack_space s + w2n (w >>>
            word_shift (:'a)) in
            if i < LENGTH (?_stack s) /\
               ((w >>> word_shift (:'a)) << word_shift (:'a) = w)
                 then (NONE,?_stack_fupd (K (LUPDATE v i (?_stack s)))
                 s) else (SOME Error,empty_env s)) | _115 -> (SOME
                 Error,empty_env s))) /\
   (stackSem_evaluate (StackGetSize r,s) =
      (if ~stackSem_state_use_stack s then (SOME Error,s) else
      (NONE,set_var r (Word (n2w (stackSem_state_stack_space s)))
        s))) /\
   (stackSem_evaluate (StackSetSize r,s) =
      (if ~stackSem_state_use_stack s then (SOME Error,s) else
      match get_var r s with SOME (Word (w:'a word)) ->
          (if LENGTH (?_stack s) <= w2n w then (SOME Error,empty_env
            s) else (NONE,set_var r (Word (w << word_shift (:'a)))
                        (stackSem_state_stack_space_fupd (K (w2n w))
                          s))) | _116 -> (SOME Error,s))) /\
   (stackSem_evaluate (BitmapLoad r v,s) =
      (if ~stackSem_state_use_stack s \/ r = v then (SOME Error,s)
        else
      match get_var v s with SOME (Word w) ->
          (if LENGTH (stackSem_state_bitmaps s) <= w2n w then
            (SOME Error,s) else (NONE,set_var r (Word (EL (w2n w)
            (stackSem_state_bitmaps s))) s)) | _117 -> (SOME
            Error,s)))`;;
hol4_overload "evaluate" "stackSem_evaluate";;

(* We prove that the clock never increases. *)

(* observational semantics *)

let semantics_def = cake_define
  `stackSem_semantics start s =
   (let prog = Call NONE (INL start) NONE in
   if ?k. let res = FST (evaluate (prog,?_clock_fupd (K k) s)) in ~(
            res = SOME TimeOut) /\ ~(res = SOME (Result (Loc 1 0)))
              /\
            (!w. ~(res = SOME (Halt (Word w)))) /\ (!f. ~(res = SOME
              (FinalFFI f))) then Fail else
     match some (\res.
       ?k t r outcome.
         evaluate (prog,?_clock_fupd (K k) s) = (SOME r,t) /\
         (match r with FinalFFI e -> outcome = FFI_outcome e | Halt w
           -> outcome = (if w = Word (n2w 0) then Success else
           Resource_limit_hit) | Result _118 -> outcome = Success | _119
           -> F) /\
         res = Terminate outcome (ffi_state_io_events (?_ffi t)))
           with SOME res -> res | NONE ->
       Diverge
          (build_lprefix_lub
            (IMAGE (\k. fromList (ffi_state_io_events (?_ffi (SND
              (evaluate (prog,?_clock_fupd (K k) s)))))) UNIV)))`;;
hol4_overload "semantics" "stackSem_semantics";;

(* record accessors *)

let read_stack_def = cake_define
  `read_stack s = ?_stack (s:('a,'b,'c)stackSem_state)`;;

let read_stack_space_def = cake_define
  `read_stack_space s = stackSem_state_stack_space
  (s:('a,'b,'c)stackSem_state)`;;

(* clean up *)

(* HOL4 ML code, not ported:
val _ = map delete_binding ["evaluate_AUX_def",
  "evaluate_primitive_def"];
*)
