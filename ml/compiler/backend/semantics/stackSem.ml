(* ======================================================== *)
(*  stackSem: ported from HOL4's
    compiler/backend/semantics/stackSemScript.sml  *)
(* ======================================================== *)

(*
  The formal semantics of stackLang
*)

needs "compiler/backend/data_live.ml";;
needs "compiler/backend/export.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
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
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
(* HOL4 ancestors outside the port: (* for word_loc and word_cmp *) *)


let stackSem_result_INDUCT,stackSem_result_RECURSION = define_datatype
  "stackSem_result = stackSem_Result ('w word_loc) | \
   stackSem_Exception ('w word_loc) | stackSem_Break (num) | \
   stackSem_Continue (num) | stackSem_Halt ('w word_loc) | \
   stackSem_TimeOut | stackSem_FinalFFI (final_event) | \
   stackSem_Error";;

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

let mem_load_def = cake_define
  `stackSem_mem_load (addr':'a word) (s:('a,'c,'ffi)stackSem_state) =
     (if addr' IN ?_mdomain s then
       SOME (?_memory s addr') else NONE)`;;

let dec_clock_def = cake_define
  `stackSem_dec_clock (s:('a,'c,'ffi)stackSem_state) = ?_clock_fupd
  (K (?_clock s - 1)) s`;;

(* HOL4 termination: \\ REPEAT STRIP_TAC \\ IMP_RES_TAC
   wordLangTheory.MEM_IMP_exp_size \\ TRY (FIRST_X_ASSUM (ASSUME_TAC
   o Q.SPEC `ARB`)) \\ DECIDE_TAC *)
let word_exp_def = cake_define_wf
  `MEASURE (exp_size ARB o SND)`
  `(stackSem_word_exp s (wordLang_Const w) = SOME w) /\
   (stackSem_word_exp s (wordLang_Var v) =
      (match FLOOKUP (stackSem_state_regs s) v with SOME
        (wordLang_Word w) -> SOME w | _6 -> NONE)) /\
   (stackSem_word_exp s (wordLang_Lookup name) =
      (match FLOOKUP (?_store s) name with SOME (wordLang_Word w) ->
        SOME w | _7 -> NONE)) /\
   (stackSem_word_exp s (wordLang_Load addr') =
      (match stackSem_word_exp s addr' with SOME w -> (match
        stackSem_mem_load w s with SOME (wordLang_Word w) -> SOME w | _8
        -> NONE) | _9 -> NONE)) /\
   (stackSem_word_exp s (wordLang_Op ast_op wexps) =
      (let ws = MAP (stackSem_word_exp s) wexps in
        if EVERY IS_SOME ws then wordLang_word_op ast_op (MAP THE ws)
          else NONE)) /\
   (stackSem_word_exp s (wordLang_Shift sh wexp wexp1) =
      (match (stackSem_word_exp s wexp,stackSem_word_exp s wexp1)
        with (SOME w,SOME w1) -> word_sh sh w (w2n w1) | _10 ->
        NONE))`;;

let get_var_def = cake_define
  `stackSem_get_var v (s:('a,'c,'ffi)stackSem_state) = FLOOKUP
  (stackSem_state_regs s) v`;;

let get_vars_def = cake_define
  `(stackSem_get_vars [] s = SOME []) /\
   (stackSem_get_vars (v :: vs) s =
      (match stackSem_get_var v s with NONE -> NONE | SOME x ->
        (match stackSem_get_vars vs s with NONE -> NONE | SOME xs ->
        SOME (x :: xs))))`;;

let get_fp_var_def = cake_define
  `stackSem_get_fp_var v (s:('a,'c,'ffi)stackSem_state) = FLOOKUP
  (?_fp_regs s) v`;;

let set_var_def = cake_define
  `stackSem_set_var v x (s:('a,'c,'ffi)stackSem_state) =
     (stackSem_state_regs_fupd (K (stackSem_state_regs s |+
       (v,x))) s)`;;

let set_fp_var_def = cake_define
  `stackSem_set_fp_var v x (s:('a,'c,'ffi)stackSem_state) =
     (?_fp_regs_fupd (K (?_fp_regs s |+ (v,x))) s)`;;

let set_store_def = cake_define
  `set_store v x (s:('a,'c,'ffi)stackSem_state) = (?_store_fupd (K
  (?_store s |+ (v,x))) s)`;;

let empty_env_def = cake_define
  `stackSem_empty_env (s:('a,'c,'ffi)stackSem_state) = ?_stack_fupd
  (K []) (stackSem_state_regs_fupd (K FEMPTY) s)`;;

let sh_mem_store_def = cake_define
  `(sh_mem_store r (a:'a word) (s:('a,'c,'ffi)stackSem_state):('a
  stackSem_result) option#('a,'c,'ffi)stackSem_state) =
   (match stackSem_get_var r s with
      SOME (wordLang_Word w) ->
        (if a IN ?_sh_mdomain s then
          (match call_FFI (?_ffi s) (SharedMem MappedWrite) [(n2w
            0):word8]
                         (word_to_bytes w F ++ word_to_bytes a F)
                           with
             FFI_final outcome -> (SOME (stackSem_FinalFFI
               outcome),s) | FFI_return new_ffi new_bytes ->
               (NONE,?_ffi_fupd (K new_ffi) s)) else (SOME
               stackSem_Error,s)) | _11 -> (SOME stackSem_Error,s))`;;

let sh_mem_load_def = cake_define
  `(sh_mem_load r (a:'a word) (s:('a,'c,'ffi)stackSem_state):('a
  stackSem_result) option#('a,'c,'ffi)stackSem_state) =
   (if a IN ?_sh_mdomain s then
     (match call_FFI (?_ffi s) (SharedMem MappedRead) [(n2w 0):word8]
                    (word_to_bytes a F) with
        FFI_final outcome -> (SOME (stackSem_FinalFFI outcome),s) |
          FFI_return new_ffi new_bytes ->
          (NONE,?_ffi_fupd (K new_ffi) (stackSem_state_regs_fupd (K
            (stackSem_state_regs s |+ (r,wordLang_Word (word_of_bytes F
            (n2w 0) new_bytes))))
           s))) else (SOME stackSem_Error,s))`;;

let sh_mem_store_byte_def = cake_define
  `(sh_mem_store_byte r (a:'a word) (s:('a,'c,'ffi)stackSem_state):('a
  stackSem_result) option#('a,'c,'ffi)stackSem_state) =
   (match stackSem_get_var r s with
      SOME (wordLang_Word w) ->
        (if byte_align a IN ?_sh_mdomain s then
          (match call_FFI (?_ffi s) (SharedMem MappedWrite) [(n2w
            1):word8]
                         ([get_byte (n2w 0) w F] ++ word_to_bytes a
                           F) with
             FFI_final outcome -> (SOME (stackSem_FinalFFI
               outcome),s) | FFI_return new_ffi new_bytes ->
               (NONE,?_ffi_fupd (K new_ffi) s)) else (SOME
               stackSem_Error,s)) | _12 -> (SOME stackSem_Error,s))`;;

let sh_mem_store16_def = cake_define
  `(sh_mem_store16 r (a:'a word) (s:('a,'c,'ffi)stackSem_state):('a
  stackSem_result) option#('a,'c,'ffi)stackSem_state) =
   (match stackSem_get_var r s with
      SOME (wordLang_Word w) ->
        (if byte_align a IN ?_sh_mdomain s then
          (match call_FFI (?_ffi s) (SharedMem MappedWrite) [(n2w
            2):word8]
                         (TAKE 2 (word_to_bytes w F) ++ word_to_bytes
                           a F) with
             FFI_final outcome -> (SOME (stackSem_FinalFFI
               outcome),s) | FFI_return new_ffi new_bytes ->
               (NONE,?_ffi_fupd (K new_ffi) s)) else (SOME
               stackSem_Error,s)) | _13 -> (SOME stackSem_Error,s))`;;

let sh_mem_store32_def = cake_define
  `(sh_mem_store32 r (a:'a word) (s:('a,'c,'ffi)stackSem_state):('a
  stackSem_result) option#('a,'c,'ffi)stackSem_state) =
   (match stackSem_get_var r s with
      SOME (wordLang_Word w) ->
        (if byte_align a IN ?_sh_mdomain s then
          (match call_FFI (?_ffi s) (SharedMem MappedWrite) [(n2w
            4):word8]
                         (TAKE 4 (word_to_bytes w F) ++ word_to_bytes
                           a F) with
             FFI_final outcome -> (SOME (stackSem_FinalFFI
               outcome),s) | FFI_return new_ffi new_bytes ->
               (NONE,?_ffi_fupd (K new_ffi) s)) else (SOME
               stackSem_Error,s)) | _14 -> (SOME stackSem_Error,s))`;;

let sh_mem_load_byte_def = cake_define
  `(sh_mem_load_byte r (a:'a word) (s:('a,'c,'ffi)stackSem_state):('a
  stackSem_result) option#('a,'c,'ffi)stackSem_state) =
   (if byte_align a IN ?_sh_mdomain s then
     (match call_FFI (?_ffi s) (SharedMem MappedRead) [(n2w 1):word8]
       (word_to_bytes a F) with
        FFI_final outcome -> (SOME (stackSem_FinalFFI outcome),s) |
          FFI_return new_ffi new_bytes ->
          (NONE,?_ffi_fupd (K new_ffi) (stackSem_state_regs_fupd (K
            (stackSem_state_regs s |+ (r,wordLang_Word (word_of_bytes F
            (n2w 0) new_bytes))))
           s))) else (SOME stackSem_Error,s))`;;

let sh_mem_load16_def = cake_define
  `(sh_mem_load16 r (a:'a word) (s:('a,'c,'ffi)stackSem_state):('a
  stackSem_result) option#('a,'c,'ffi)stackSem_state) =
   (if byte_align a IN ?_sh_mdomain s then
     (match call_FFI (?_ffi s) (SharedMem MappedRead) [(n2w 2):word8]
       (word_to_bytes a F) with
        FFI_final outcome -> (SOME (stackSem_FinalFFI outcome),s) |
          FFI_return new_ffi new_bytes ->
          (NONE,?_ffi_fupd (K new_ffi) (stackSem_state_regs_fupd (K
            (stackSem_state_regs s |+ (r,wordLang_Word (word_of_bytes F
            (n2w 0) new_bytes))))
           s))) else (SOME stackSem_Error,s))`;;

let sh_mem_load32_def = cake_define
  `(sh_mem_load32 r (a:'a word) (s:('a,'c,'ffi)stackSem_state):('a
  stackSem_result) option#('a,'c,'ffi)stackSem_state) =
   (if byte_align a IN ?_sh_mdomain s then
     (match call_FFI (?_ffi s) (SharedMem MappedRead) [(n2w 4):word8]
       (word_to_bytes a F) with
        FFI_final outcome -> (SOME (stackSem_FinalFFI outcome),s) |
          FFI_return new_ffi new_bytes ->
          (NONE,?_ffi_fupd (K new_ffi) (stackSem_state_regs_fupd (K
            (stackSem_state_regs s |+ (r,wordLang_Word (word_of_bytes F
            (n2w 0) new_bytes))))
           s))) else (SOME stackSem_Error,s))`;;

let sh_mem_op_def = cake_define
  `(sh_mem_op wordLang_Load r ad (s:('a,'c,'ffi)stackSem_state) =
  sh_mem_load r ad s) /\
   (sh_mem_op wordLang_Store r ad s = sh_mem_store r ad s) /\
   (sh_mem_op asm_Load8 r ad s = sh_mem_load_byte r ad s) /\
   (sh_mem_op asm_Store8 r ad s = sh_mem_store_byte r ad s) /\
   (sh_mem_op asm_Load16 r ad s = sh_mem_load16 r ad s) /\
   (sh_mem_op asm_Store16 r ad s = sh_mem_store16 r ad s) /\
   (sh_mem_op asm_Load32 r ad s = sh_mem_load32 r ad s) /\
   (sh_mem_op asm_Store32 r ad s = sh_mem_store32 r ad s)`;;

let full_read_bitmap_def = cake_define
  `full_read_bitmap bitmaps x2 =
        match x2 with
          (wordLang_Word w) ->
        if w = (n2w 0) then NONE else read_bitmap (DROP (w2n (w -
          (n2w 1))) bitmaps)
        | _15 -> NONE`;;

(* HOL4 termination: \\ REPEAT STRIP_TAC \\ IMP_RES_TAC
   filter_bitmap_LENGTH \\ fs [] \\ decide_tac *)
let enc_stack_def = cake_define_wf
  `MEASURE (LENGTH o SND)`
  `(stackSem_enc_stack bitmaps [] = NONE) /\
   (stackSem_enc_stack bitmaps (w :: ws) =
      (if w = wordLang_Word (n2w 0) then (if ws = [] then SOME []
        else NONE) else
        match full_read_bitmap bitmaps w with NONE -> NONE | SOME bs
          ->
           (match filter_bitmap bs ws with NONE -> NONE | SOME
             (ts,ws') ->
               (match stackSem_enc_stack bitmaps ws' with NONE ->
                 NONE | SOME rs -> SOME (ts ++ rs)))))`;;

(* HOL4 termination: \\ rw [] \\ IMP_RES_TAC map_bitmap_LENGTH \\ fs
   [LENGTH_NIL] \\ rw [] \\ fs [map_bitmap_def] \\ rw [] \\
   decide_tac *)
let dec_stack_def = cake_define_wf
  `MEASURE (LENGTH o SND o SND)`
  `(stackSem_dec_stack bitmaps _16 [] = NONE) /\
   (stackSem_dec_stack bitmaps ts (w :: ws) =
     (if w = wordLang_Word (n2w 0) then (if ts = [] /\ ws = [] then
       SOME [wordLang_Word (n2w 0)] else NONE) else
      match full_read_bitmap bitmaps w with NONE -> NONE | SOME bs ->
         (match map_bitmap bs ts ws with NONE -> NONE | SOME
           (hd,ts',ws') ->
            (match stackSem_dec_stack bitmaps ts' ws' with NONE ->
              NONE | SOME rest -> SOME ([w] ++ hd ++ rest)))))`;;

let gc_def = cake_define
  `gc s =
     (if LENGTH (?_stack s) < stackSem_state_stack_space s then NONE
       else
       let unused = TAKE (stackSem_state_stack_space s) (?_stack s)
         in
       let stack = DROP (stackSem_state_stack_space s) (?_stack s) in
         match stackSem_enc_stack (stackSem_state_bitmaps s) (DROP
           (stackSem_state_stack_space s) (?_stack s)) with NONE -> NONE
           | SOME wl_list ->
           (match ?_gc_fun s (wl_list,?_memory s,?_mdomain s,?_store
             s) with NONE -> NONE | SOME (wl,m,st) ->
            (match stackSem_dec_stack (stackSem_state_bitmaps s) wl
              stack with NONE -> NONE | SOME stack ->
                 SOME (?_memory_fupd (K m)
                   (stackSem_state_regs_fupd (K FEMPTY) (?_store_fupd
                   (K st) (?_stack_fupd (K (unused ++ stack))
                   s)))))))`;;

let has_space_def = cake_define
  `has_space wl store =
     (match (wl,FLOOKUP store NextFree,FLOOKUP store TriggerGC)
       with (wordLang_Word w,SOME (wordLang_Word n),SOME
       (wordLang_Word l)) -> SOME (w2n w <= w2n (l - n)) | _17 ->
       NONE)`;;

let alloc_def = cake_define
  `alloc (w:'a word) (s:('a,'c,'ffi)stackSem_state) =
       (match gc (set_store AllocSize (wordLang_Word w) s) with NONE
         -> (SOME stackSem_Error,s) | SOME s ->
          (match FLOOKUP (?_store s) AllocSize with NONE -> (SOME
            stackSem_Error,s) | SOME w ->
            (match has_space w (?_store s) with NONE -> (SOME
              stackSem_Error,s) | SOME T ->
                         (NONE,s) | SOME F ->
                         (SOME (stackSem_Halt (wordLang_Word ((n2w
                           1):'a word))),stackSem_empty_env s))))`;;

let assign_def = cake_define
  `stackSem_assign asm_reg wordLang_exp s =
     (match stackSem_word_exp s wordLang_exp with NONE -> NONE |
       SOME w -> SOME (stackSem_set_var asm_reg (wordLang_Word w) s))`;;

let inst_def = cake_define
  `stackSem_inst i (s:('a,'c,'ffi)stackSem_state) =
     (match i with wordLang_Skip -> SOME s | wordLang_Const asm_reg w
       -> stackSem_assign asm_reg (wordLang_Const w) s | asm_Arith
       (asm_Binop bop r1 r2 ri) ->
         (if bop = asm_Or /\ ri = Reg r2 then
           match FLOOKUP (stackSem_state_regs s) r2 with NONE -> NONE
             | SOME w -> SOME (stackSem_set_var r1 w s) else
           stackSem_assign r1
             (wordLang_Op bop [wordLang_Var r2; match ri with Reg r3
               -> wordLang_Var r3 | Imm w -> wordLang_Const w]) s) |
               asm_Arith (wordLang_Shift sh r1 r2 ri) ->
         stackSem_assign r1
           (wordLang_Shift sh (wordLang_Var r2) (match ri with Reg r3
             -> wordLang_Var r3 | Imm w -> wordLang_Const w)) s |
             asm_Arith (asm_Div r1 r2 r3) ->
        (let vs = stackSem_get_vars [r3; r2] s in
        match vs with
        SOME [wordLang_Word q; wordLang_Word w2] ->
          (if ~(q = (n2w 0)) then
            SOME (stackSem_set_var r1 (wordLang_Word (w2 / q)) s)
              else NONE) | _18 -> NONE) | asm_Arith (asm_AddCarry r1 r2
              r3 r4) ->
         (let vs = stackSem_get_vars [r2; r3; r4] s in
         match vs with
         SOME [wordLang_Word l; wordLang_Word r; wordLang_Word c] ->
           (let res = w2n l + w2n r + (if c = ((n2w 0):'a word) then
             0 else 1) in
             SOME (stackSem_set_var r4 (wordLang_Word (if dimword
               (:'a) <= res then ((n2w 1):'a word) else (n2w 0)))
                  (stackSem_set_var r1 (wordLang_Word (n2w res)) s)))
                    | _19 -> NONE) | asm_Arith (asm_AddOverflow r1 r2 r3
                    r4) ->
         (let vs = stackSem_get_vars [r2; r3] s in
         match vs with
         SOME [wordLang_Word w2; wordLang_Word w3] ->
           SOME (stackSem_set_var r4 (wordLang_Word (if ~(w2i (w2 +
             w3) = w2i w2 + w2i w3) then (n2w 1) else (n2w 0)))
                  (stackSem_set_var r1 (wordLang_Word (w2 + w3)) s))
                    | _20 -> NONE) | asm_Arith (asm_SubOverflow r1 r2 r3
                    r4) ->
         (let vs = stackSem_get_vars [r2; r3] s in
         match vs with
         SOME [wordLang_Word w2; wordLang_Word w3] ->
           SOME (stackSem_set_var r4 (wordLang_Word (if ~(w2i (w2 -
             w3) = w2i w2 - w2i w3) then (n2w 1) else (n2w 0)))
                  (stackSem_set_var r1 (wordLang_Word (w2 - w3)) s))
                    | _21 -> NONE) | asm_Arith (asm_LongMul r1 r2 r3 r4)
                    ->
         (let vs = stackSem_get_vars [r3; r4] s in
         match vs with
         SOME [wordLang_Word w3; wordLang_Word w4] ->
          (let r = w2n w3 * w2n w4 in
            SOME (stackSem_set_var r2 (wordLang_Word (n2w r))
              (stackSem_set_var r1 (wordLang_Word (n2w (r DIV dimword
              (:'a)))) s))) | _22 -> NONE) | asm_Arith (asm_LongDiv r1
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
              else NONE) | _23 -> NONE) | asm_Mem wordLang_Load r (Addr
              a w) ->
        (match stackSem_word_exp s (wordLang_Op asm_Add [wordLang_Var
          a; wordLang_Const w]) with NONE -> NONE | SOME w ->
             (match stackSem_mem_load w s with NONE -> NONE | SOME w
               -> SOME (stackSem_set_var r w s))) | asm_Mem asm_Load8 r
               (Addr a w) ->
        (match stackSem_word_exp s (wordLang_Op asm_Add [wordLang_Var
          a; wordLang_Const w]) with SOME w ->
            (match mem_load_byte_aux (?_memory s) (?_mdomain s) (?_be
              s) w with NONE -> NONE | SOME w -> SOME (stackSem_set_var
              r (wordLang_Word (w2w w)) s)) | _24 -> NONE) | asm_Mem
              asm_Load16 _25 _26 -> NONE | asm_Mem asm_Load32 r (Addr a
              w) ->
        (match stackSem_word_exp s (wordLang_Op asm_Add [wordLang_Var
          a; wordLang_Const w]) with SOME w ->
            (match mem_load_32 (?_memory s) (?_mdomain s) (?_be s) w
              with NONE -> NONE | SOME w -> SOME (stackSem_set_var r
              (wordLang_Word (w2w w)) s)) | _27 -> NONE) | asm_Mem
              wordLang_Store r (Addr a w) ->
        (match (stackSem_word_exp s (wordLang_Op asm_Add
          [wordLang_Var a; wordLang_Const w]),stackSem_get_var r s) with
          (SOME a,SOME w) ->
             (match stackSem_mem_store a w s with SOME s1 -> SOME s1
               | NONE -> NONE) | _28 -> NONE) | asm_Mem asm_Store8 r
               (Addr a w) ->
        (match (stackSem_word_exp s (wordLang_Op asm_Add
          [wordLang_Var a; wordLang_Const w]),stackSem_get_var r s) with
          (SOME a,SOME (wordLang_Word w)) ->
             (match mem_store_byte_aux (?_memory s) (?_mdomain s)
               (?_be s) a (w2w w) with SOME new_m -> SOME (?_memory_fupd
               (K new_m) s) | NONE -> NONE) | _29 -> NONE) | asm_Mem
               asm_Store16 _30 _31 -> NONE | asm_Mem asm_Store32 r (Addr
               a w) ->
        (match (stackSem_word_exp s (wordLang_Op asm_Add
          [wordLang_Var a; wordLang_Const w]),stackSem_get_var r s) with
          (SOME a,SOME (wordLang_Word w)) ->
             (match mem_store_32 (?_memory s) (?_mdomain s) (?_be s)
               a (w2w w) with SOME new_m -> SOME (?_memory_fupd (K
               new_m) s) | NONE -> NONE) | _32 -> NONE) | asm_FP (FPLess
               r d1 d2) ->
       (match (stackSem_get_fp_var d1 s,stackSem_get_fp_var d2 s)
         with (SOME f1,SOME f2) ->
         SOME (stackSem_set_var r
           (wordLang_Word (if fp64_lessThan f1 f2 then (n2w 1) else
             (n2w 0))) s) | _33 -> NONE) | asm_FP (FPLessEqual r d1 d2)
             ->
       (match (stackSem_get_fp_var d1 s,stackSem_get_fp_var d2 s)
         with (SOME f1,SOME f2) ->
         SOME (stackSem_set_var r
           (wordLang_Word (if fp64_lessEqual f1 f2 then (n2w 1) else
             (n2w 0))) s) | _34 -> NONE) | asm_FP (FPEqual r d1 d2) ->
       (match (stackSem_get_fp_var d1 s,stackSem_get_fp_var d2 s)
         with (SOME f1,SOME f2) ->
         SOME (stackSem_set_var r
           (wordLang_Word (if fp64_equal f1 f2 then (n2w 1) else (n2w
             0))) s) | _35 -> NONE) | asm_FP (FPMov d1 d2) ->
       (match stackSem_get_fp_var d2 s with SOME f ->
         SOME (stackSem_set_fp_var d1 f s) | _36 -> NONE) | asm_FP
           (FPAbs d1 d2) ->
       (match stackSem_get_fp_var d2 s with SOME f ->
         SOME (stackSem_set_fp_var d1 (fp64_abs f) s) | _37 -> NONE)
           | asm_FP (FPNeg d1 d2) ->
       (match stackSem_get_fp_var d2 s with SOME f ->
         SOME (stackSem_set_fp_var d1 (fp64_negate f) s) | _38 ->
           NONE) | asm_FP (FPSqrt d1 d2) ->
       (match stackSem_get_fp_var d2 s with SOME f ->
         SOME (stackSem_set_fp_var d1 (fp64_sqrt roundTiesToEven f)
           s) | _39 -> NONE) | asm_FP (FPAdd d1 d2 d3) ->
       (match (stackSem_get_fp_var d2 s,stackSem_get_fp_var d3 s)
         with (SOME f1,SOME f2) ->
         SOME (stackSem_set_fp_var d1 (fp64_add roundTiesToEven f1
           f2) s) | _40 -> NONE) | asm_FP (FPSub d1 d2 d3) ->
       (match (stackSem_get_fp_var d2 s,stackSem_get_fp_var d3 s)
         with (SOME f1,SOME f2) ->
         SOME (stackSem_set_fp_var d1 (fp64_sub roundTiesToEven f1
           f2) s) | _41 -> NONE) | asm_FP (FPMul d1 d2 d3) ->
       (match (stackSem_get_fp_var d2 s,stackSem_get_fp_var d3 s)
         with (SOME f1,SOME f2) ->
         SOME (stackSem_set_fp_var d1 (fp64_mul roundTiesToEven f1
           f2) s) | _42 -> NONE) | asm_FP (FPDiv d1 d2 d3) ->
       (match (stackSem_get_fp_var d2 s,stackSem_get_fp_var d3 s)
         with (SOME f1,SOME f2) ->
         SOME (stackSem_set_fp_var d1 (fp64_div roundTiesToEven f1
           f2) s) | _43 -> NONE) | asm_FP (FPFma d1 d2 d3) ->
       (match (stackSem_get_fp_var d1 s,stackSem_get_fp_var d2
         s,stackSem_get_fp_var d3 s) with (SOME f1,SOME f2,SOME f3) ->
         SOME (stackSem_set_fp_var d1 (fpfma f1 f2 f3) s) | _44 ->
           NONE) | asm_FP (FPMovToReg r1 r2 d) ->
       (match stackSem_get_fp_var d s with SOME v ->
         (if dimindex (:'a) = 64 then
           SOME (stackSem_set_var r1 (wordLang_Word (w2w v)) s) else
           SOME (stackSem_set_var r2 (wordLang_Word ((63 >< 32) v))
             (stackSem_set_var r1 (wordLang_Word ((31 >< 0) v)) s))) |
             _45 -> NONE) | asm_FP (FPMovFromReg d r1 r2) ->
       (if dimindex (:'a) = 64 then
         match stackSem_get_var r1 s with
           SOME (wordLang_Word w1) -> SOME (stackSem_set_fp_var d
             (w2w w1) s) | _46 -> NONE else
         match (stackSem_get_var r1 s,stackSem_get_var r2 s) with
           (SOME (wordLang_Word w1),SOME (wordLang_Word w2)) -> SOME
             (stackSem_set_fp_var d (w2 @@ w1) s) | _47 -> NONE) |
             asm_FP (FPToInt d1 d2) ->
       (match stackSem_get_fp_var d2 s with
         NONE -> NONE | SOME f ->
       (match fp64_to_int roundTiesToEven f with
         NONE -> NONE | SOME i ->
         (let w = i2w i:word32 in
         if w2i w = i then
           (if dimindex (:'a) = 64 then
              SOME (stackSem_set_fp_var d1 (w2w w) s) else
            match stackSem_get_fp_var (d1 DIV 2) s with
              NONE -> NONE | SOME f ->
              (let (h,l) = if ODD d1 then (63,32) else (31,0) in
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
               roundTiesToEven i) s)) | NONE -> NONE | _48 -> NONE))`;;

let get_var_imm_def = cake_define
  `(stackSem_get_var_imm ((Reg n):'a asm_reg_imm) s = stackSem_get_var n
  s) /\
   (stackSem_get_var_imm (Imm w) s = SOME (wordLang_Word w))`;;

let find_code_def = cake_define
  `(stackSem_find_code (INL p) regs code = sptree_lookup p code) /\
   (stackSem_find_code (INR r) regs code =
      (match FLOOKUP regs r with
        SOME (wordLang_Loc loc 0) -> sptree_lookup loc code |
          other -> NONE))`;;

let fix_clock_def = cake_define
  `stackSem_fix_clock s (res,s1) = (res,?_clock_fupd (K (MIN (?_clock
  s) (?_clock s1))) s1)`;;

let STOP_def = cake_define
  `stackSem_STOP x = x`;;

let get_labels_def = cake_define
  `get_labels x1 =
        match x1 with
          (wordLang_Seq p1 p2) -> get_labels p1 UNION get_labels p2
        | (wordLang_If _49 _50 _51 p1 p2) -> get_labels p1 UNION
          get_labels p2
        | (wordLang_Loop p) -> get_labels p
        | (wordLang_Call ret _52 handler) ->
        (match ret with NONE -> {} | SOME (r,_53,l1,l2) -> (l1,l2)
          INSERT (get_labels r UNION
             (match handler with NONE -> {} | SOME (r,l1,l2) ->
               (l1,l2) INSERT get_labels r)))
        | (stackSem_Halt _54) -> {}
        | _55 -> {}`;;

let loc_check_def = cake_define
  `loc_check code (l1,l2) <=>
     (l2 = 0 /\ l1 IN domain code) \/
     (?n e. sptree_lookup n code = SOME e /\ (l1,l2) IN get_labels
       e)`;;

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
  `unset_var v (s:('a,'c,'ffi)stackSem_state) =
  stackSem_state_regs_fupd (K (stackSem_state_regs s \\ v)) s`;;

let store_const_sem_def = cake_define
  `store_const_sem t1 t2 (s:('a,'c,'ffi)stackSem_state) =
     (if ~ALL_DISTINCT [0; 1; 2; 3; t1; t2] then (SOME
       stackSem_Error,s) else
       match (stackSem_get_var 1 s,stackSem_get_var 2
         s,stackSem_get_var 3 s) with (SOME (wordLang_Word i),SOME
         (wordLang_Word a),SOME (wordLang_Word off)) ->
           (match copy_words (w2n i) a off (stackSem_state_bitmaps s)
             (?_mdomain s) (?_memory s) with NONE -> (SOME
             stackSem_Error,s) | SOME (a,m) -> (NONE,
               (if stackSem_state_use_alloc s then unset_var 0 else
                 I)
                 (stackSem_set_var t1 (wordLang_Word (n2w 1))
                   (stackSem_set_var t2 (wordLang_Word (n2w 1))
                   (stackSem_set_var 1 (wordLang_Word (n2w 1))
                     (stackSem_set_var 2 (wordLang_Word a)
                     (?_memory_fupd (K m) s))))))) | _56 -> (SOME
                     stackSem_Error,s))`;;

let check_store_consts_opt_def = cake_define
  `check_store_consts_opt t1 t2 NONE _57 = T /\
   check_store_consts_opt t1 t2 (SOME n) c =
     (sptree_lookup n c = SOME (wordLang_Seq (wordLang_StoreConsts
       t1 t2 NONE) (wordLang_Return 0)))`;;

let dest_Seq_def = cake_define
  `stackSem_dest_Seq x1 =
      match x1 with
        (wordLang_Seq p1 p2) -> SOME (p1,(p2:'a stackLang_prog))
      | _58 -> NONE`;;

let bad_fun_return_def = cake_define
  `stackSem_bad_fun_return x1 =
      match x1 with
        NONE -> T
      | (SOME (stackSem_Break _59)) -> T
      | (SOME (stackSem_Continue _60)) -> T
      | _61 -> F`;;

let cont_loop_def = cake_define
  `stackSem_cont_loop x1 =
      match x1 with
        NONE -> T
      | (SOME (stackSem_Continue n)) -> (n = 0)
      | _62 -> F`;;

let exit_loop_def = cake_define
  `stackSem_exit_loop res =
      match res with
        (SOME (stackSem_Break n)) -> (if n = 0 then NONE else SOME
          (stackSem_Break (n - 1)))
      | (SOME (stackSem_Continue n)) -> SOME (stackSem_Continue (n -
        1))
      | res -> res`;;

(* HOL4 termination: \\ rpt strip_tac \\
   fs[empty_env_def,dec_clock_def,set_var_def,STOP_def] \\
   imp_res_tac fix_clock_IMP \\ fs [] \\ imp_res_tac (GSYM
   fix_clock_IMP) \\ fs [] \\ decide_tac *)
let evaluate_def = cake_define_wf
  `(inv_image (MEASURE I LEX MEASURE (prog_size (K 0)))
                              (\(xs,(s:('a,'c,'ffi)stackSem_state)).
                                (?_clock s,xs)))`
  `(stackSem_evaluate ((wordLang_Skip:'a stackLang_prog),s) =
  (NONE,(s:('a,'c,'ffi)stackSem_state))) /\
   (stackSem_evaluate (stackSem_Halt v,s) =
      (match stackSem_get_var v s with SOME w -> (SOME (stackSem_Halt
        w),stackSem_empty_env s) | NONE -> (SOME stackSem_Error,s))) /\
   (stackSem_evaluate (wordLang_Alloc n,s) =
      (if ~stackSem_state_use_alloc s then (SOME stackSem_Error,s)
        else
      match stackSem_get_var n s with SOME (wordLang_Word w) -> alloc
        w s | _63 -> (SOME stackSem_Error,s))) /\
   (stackSem_evaluate (wordLang_StoreConsts t1 t2 stub_opt,s) =
      (if ~stackSem_state_use_store s then (SOME stackSem_Error,s)
        else
      if ~stackSem_state_use_alloc s /\ IS_SOME stub_opt then (SOME
        stackSem_Error,s) else
      if ~check_store_consts_opt t1 t2 stub_opt (?_code s) then (SOME
        stackSem_Error,s) else
        store_const_sem t1 t2 s)) /\
   (stackSem_evaluate (wordLang_Inst i,s) =
      (match stackSem_inst i s with SOME s1 -> (NONE,s1) | NONE ->
        (SOME stackSem_Error,s))) /\
   (stackSem_evaluate (wordLang_Get v name,s) =
      (if ~stackSem_state_use_store s then (SOME stackSem_Error,s)
        else
      match FLOOKUP (?_store s) name with SOME x ->
        (NONE,stackSem_set_var v x s) | NONE -> (SOME
        stackSem_Error,s))) /\
   (stackSem_evaluate (wordLang_Set name v,s) =
      (if ~stackSem_state_use_store s then (SOME stackSem_Error,s)
        else
      match stackSem_get_var v s with SOME w -> (NONE,set_store name
        w s) | NONE -> (SOME stackSem_Error,s))) /\
   (stackSem_evaluate (wordLang_OpCurrHeap binop v src,s) =
      (if ~stackSem_state_use_store s then (SOME stackSem_Error,s)
        else
      match stackSem_word_exp s (wordLang_Op binop [wordLang_Var src;
        wordLang_Lookup CurrHeap]) with SOME w -> (NONE,stackSem_set_var
        v (wordLang_Word w) s) | _64 -> (SOME stackSem_Error,s))) /\
   (stackSem_evaluate (wordLang_Tick,s) =
      (if ?_clock s = 0 then (SOME
        stackSem_TimeOut,stackSem_empty_env s) else
        (NONE,stackSem_dec_clock s))) /\
   (stackSem_evaluate (wordLang_Seq c1 c2,s) =
      (let (res,s1) = stackSem_fix_clock s (stackSem_evaluate (c1,s))
        in
        if res = NONE then stackSem_evaluate (c2,s1) else (res,s1)))
          /\
   (stackSem_evaluate (wordLang_Return n,s) =
      (match stackSem_get_var n s with SOME (wordLang_Loc l1 l2) ->
        (SOME (stackSem_Result (wordLang_Loc l1 l2)),s) | _65 -> (SOME
        stackSem_Error,s))) /\
   (stackSem_evaluate (wordLang_Raise n,s) =
      (match stackSem_get_var n s with SOME (wordLang_Loc l1 l2) ->
        (SOME (stackSem_Exception (wordLang_Loc l1 l2)),s) | _66 ->
        (SOME stackSem_Error,s))) /\
   (stackSem_evaluate (stackSem_Break n,s) = (SOME (stackSem_Break
     n),s)) /\
   (stackSem_evaluate (stackSem_Continue n,s) = (SOME
     (stackSem_Continue n),s)) /\
   (stackSem_evaluate (wordLang_If cmp r1 ri c1 c2,s) =
     (match (stackSem_get_var r1 s,stackSem_get_var_imm ri s) with
       (SOME x,SOME y) ->
      (match wordSem_word_cmp cmp x y with SOME T ->
        stackSem_evaluate (c1,s) | SOME F -> stackSem_evaluate (c2,s) |
        NONE -> (SOME stackSem_Error,s)) | _67 -> (SOME
        stackSem_Error,s))) /\
   (stackSem_evaluate (wordLang_Loop c1,s) =
     (let (res,s1) = stackSem_fix_clock s (stackSem_evaluate (c1,s))
       in
        if stackSem_cont_loop res then
          (if ?_clock s1 = 0 then (SOME
            stackSem_TimeOut,stackSem_empty_env s1) else
             stackSem_evaluate (stackSem_STOP (wordLang_Loop
               c1),stackSem_dec_clock s1)) else (stackSem_exit_loop
               res,s1))) /\
   (stackSem_evaluate (stackLang_JumpLower r1 r2 dest,s) =
     (match (stackSem_get_var r1 s,stackSem_get_var r2 s) with (SOME
       (wordLang_Word x),SOME (wordLang_Word y)) ->
       (if wordSem_word_cmp asm_Lower x y then
        (match stackSem_find_code (INL dest) (stackSem_state_regs s)
          (?_code s) with NONE -> (SOME stackSem_Error,s) | SOME
          wordLang_prog ->
            (if ?_clock s = 0 then (SOME
              stackSem_TimeOut,stackSem_empty_env s) else
              (match stackSem_evaluate
                (wordLang_prog,stackSem_dec_clock s) with (res,s) -> (if
                stackSem_bad_fun_return res then (SOME stackSem_Error,s)
                else (res,s))))) else (NONE,s)) | _68 -> (SOME
                stackSem_Error,s))) /\
   (stackSem_evaluate (stackLang_RawCall dest,s) =
     (match sptree_lookup dest (?_code s) with NONE -> (SOME
       stackSem_Error,s) | SOME wordLang_prog ->
        (match stackSem_dest_Seq wordLang_prog with SOME (_69,body)
          ->
            (if ?_clock s = 0 then (SOME
              stackSem_TimeOut,stackSem_empty_env s) else
              (match stackSem_evaluate (body,stackSem_dec_clock s)
                with (res,s) -> (if stackSem_bad_fun_return res then
                (SOME stackSem_Error,s) else (res,s)))) | _70 -> (SOME
                stackSem_Error,s)) | _71 -> (SOME stackSem_Error,s))) /\
   (stackSem_evaluate (wordLang_Call ret dest handler,s) =
      (match ret with NONE ->
        (match stackSem_find_code dest (stackSem_state_regs s)
          (?_code s) with NONE -> (SOME stackSem_Error,s) | SOME
          wordLang_prog ->
            (if ~(handler = NONE) then (SOME stackSem_Error,s) else
            if ?_clock s = 0 then (SOME
              stackSem_TimeOut,stackSem_empty_env s) else
              (match stackSem_fix_clock (stackSem_dec_clock s)
                (stackSem_evaluate (wordLang_prog,stackSem_dec_clock s))
                with (res,s) -> (if stackSem_bad_fun_return res then
                (SOME stackSem_Error,s) else (res,s))))) | SOME
                (ret_handler,link_reg,l1,l2) ->
        (match stackSem_find_code dest (stackSem_state_regs s \\
          link_reg) (?_code s) with NONE -> (SOME stackSem_Error,s) |
          SOME wordLang_prog ->
            (if ?_clock s = 0 then (SOME
              stackSem_TimeOut,stackSem_empty_env s) else
              (match stackSem_fix_clock (stackSem_dec_clock
                (stackSem_set_var link_reg (wordLang_Loc l1 l2) s))
              (stackSem_evaluate (wordLang_prog,stackSem_dec_clock
                (stackSem_set_var link_reg (wordLang_Loc l1 l2) s)))
                with (SOME (stackSem_Result x),s2) ->
                   (if ~(x = wordLang_Loc l1 l2) then (SOME
                     stackSem_Error,s2) else stackSem_evaluate
                     (ret_handler,s2)) | (SOME (stackSem_Exception
                     x),s2) ->
                   (match handler with NONE -> (SOME
                     (stackSem_Exception x),s2) | SOME (h,l1,l2) ->
                       (if ~(x = wordLang_Loc l1 l2) then (SOME
                         stackSem_Error,s2) else
                         stackSem_evaluate (h,s2))) | (NONE,s) ->
                           (SOME stackSem_Error,s) | (SOME
                           (stackSem_Break _72),s) -> (SOME
                           stackSem_Error,s) | (SOME (stackSem_Continue
                           _73),s) -> (SOME stackSem_Error,s) | (res,s)
                           -> (res,s)))))) /\
   (stackSem_evaluate (wordLang_Install ptr len dptr dlen ret,s) =
     (match (stackSem_get_var ptr s,stackSem_get_var len
       s,stackSem_get_var dptr s,stackSem_get_var dlen s) with (SOME
       (wordLang_Word w1),SOME (wordLang_Word w2),SOME (wordLang_Word
       w3),SOME (wordLang_Word w4)) ->
         (let (cfg,progs,bm) = ?_compile_oracle s 0 in
        (match (buffer_flush (?_code_buffer s) w1 w2,
               (if stackSem_state_use_stack s then buffer_flush
                 (?_data_buffer s) w3 w4 else SOME (bm,?_data_buffer
                 s))) with (
          SOME (bytes,cb),SOME (data,db)) ->
         (let new_oracle = shift_seq 1 (?_compile_oracle s) in
         (match (?_compile s cfg progs,progs) with (SOME
           (bytes',cfg'),(k,wordLang_prog) :: _74) ->
             (if bytes = bytes' /\ data = bm /\ FST (new_oracle 0) =
               cfg' then
             let s' = ?_compile_oracle_fupd (K new_oracle)
               (?_fp_regs_fupd (K FEMPTY) (stackSem_state_regs_fupd (K
               ((DRESTRICT (stackSem_state_regs s)
               (stackSem_state_ffi_save_regs s)) |+ (ptr,wordLang_Loc k
               0))) (?_code_fupd (K (sptree_union (?_code s) (fromAList
               progs))) (?_data_buffer_fupd (K db) (?_code_buffer_fupd
               (K cb) (stackSem_state_bitmaps_fupd (K
               (stackSem_state_bitmaps s ++ bm))
                 s)))))) in
               (NONE,s') else (SOME stackSem_Error,s)) | _75 -> (SOME
                 stackSem_Error,s))) | _76 -> (SOME stackSem_Error,s)))
                 | _77 -> (SOME stackSem_Error,s))) /\
   (stackSem_evaluate (stackLang_ShMemOp ast_op r (Addr a w),s) =
     (match stackSem_word_exp s (wordLang_Op asm_Add [wordLang_Var a;
       wordLang_Const w]) with SOME a ->
          (if ?_clock s = 0 then (SOME
            stackSem_TimeOut,stackSem_empty_env s) else
            sh_mem_op ast_op r a (stackSem_dec_clock s)) | _78 ->
              (SOME stackSem_Error,s))) /\
   (stackSem_evaluate (wordLang_CodeBufferWrite r1 r2,s) =
     (match (stackSem_get_var r1 s,stackSem_get_var r2 s) with (SOME
       (wordLang_Word w1),SOME (wordLang_Word w2)) ->
           (match buffer_write (?_code_buffer s) w1 (w2w w2) with
             SOME new_cb ->
             (NONE,?_code_buffer_fupd (K new_cb) s) | _79 -> (SOME
               stackSem_Error,s)) | _80 -> (SOME stackSem_Error,s))) /\
   (stackSem_evaluate (wordLang_DataBufferWrite r1 r2,s) =
     (if ~stackSem_state_use_stack s then (SOME stackSem_Error,s)
       else
     (match (stackSem_get_var r1 s,stackSem_get_var r2 s) with (SOME
       (wordLang_Word w1),SOME (wordLang_Word w2)) ->
           (match buffer_write (?_data_buffer s) w1 w2 with SOME
             new_db ->
             (NONE,?_data_buffer_fupd (K new_db) s) | _81 -> (SOME
               stackSem_Error,s)) | _82 -> (SOME stackSem_Error,s)))) /\
   (stackSem_evaluate (wordLang_FFI ffi_index ptr len ptr2 len2
     ret,s) =
    (match (stackSem_get_var len s,stackSem_get_var ptr
      s,stackSem_get_var len2 s,stackSem_get_var ptr2 s) with (SOME
      (wordLang_Word w),SOME (wordLang_Word w2),SOME (wordLang_Word
      w3),SOME (wordLang_Word w4)) ->
          (match (read_bytearray w2 (w2n w) (mem_load_byte_aux
            (?_memory s) (?_mdomain s) (?_be s)),
                 read_bytearray w4 (w2n w3) (mem_load_byte_aux
                   (?_memory s) (?_mdomain s) (?_be s))) with (SOME
                   bytes,SOME bytes2) ->
              (match call_FFI (?_ffi s) (ExtCall ffi_index) bytes
                bytes2 with FFI_final outcome -> (SOME
                (stackSem_FinalFFI outcome),s) | FFI_return new_ffi
                new_bytes ->
                   (let new_m = write_bytearray w4 new_bytes
                     (?_memory s) (?_mdomain s) (?_be s) in
                     (NONE,?_ffi_fupd (K new_ffi) (?_fp_regs_fupd (K
                       FEMPTY) (stackSem_state_regs_fupd (K (DRESTRICT
                       (stackSem_state_regs s)
                       (stackSem_state_ffi_save_regs s))) (?_memory_fupd
                       (K new_m) s)))))) | _83 -> (SOME
                       stackSem_Error,s)) | res -> (SOME
                       stackSem_Error,s))) /\
   (stackSem_evaluate (wordLang_LocValue r l1 l2,s) =
      (if loc_check (?_code s) (l1,l2) then
        (NONE,stackSem_set_var r (wordLang_Loc l1 l2) s) else (SOME
          stackSem_Error,s))) /\
   (stackSem_evaluate (stackLang_StackAlloc n,s) =
      (if ~stackSem_state_use_stack s then (SOME stackSem_Error,s)
        else
      if stackSem_state_stack_space s < n then (SOME (stackSem_Halt
        (wordLang_Word (n2w 2))),stackSem_empty_env s) else
        (NONE,stackSem_state_stack_space_fupd (K
          (stackSem_state_stack_space s - n)) s))) /\
   (stackSem_evaluate (stackLang_StackFree n,s) =
      (if ~stackSem_state_use_stack s then (SOME stackSem_Error,s)
        else
      if LENGTH (?_stack s) < stackSem_state_stack_space s + n then
        (SOME stackSem_Error,stackSem_empty_env s) else
        (NONE,stackSem_state_stack_space_fupd (K
          (stackSem_state_stack_space s + n)) s))) /\
   (stackSem_evaluate (stackLang_StackLoad r n,s) =
      (if ~stackSem_state_use_stack s then (SOME stackSem_Error,s)
        else
      if stackSem_state_stack_space s + n < LENGTH (?_stack s) then
        (NONE,stackSem_set_var r (EL (stackSem_state_stack_space s + n)
        (?_stack s)) s) else (SOME stackSem_Error,stackSem_empty_env
        s))) /\
   (stackSem_evaluate (stackLang_StackLoadAny r rn,s) =
      (if ~stackSem_state_use_stack s then (SOME stackSem_Error,s)
        else
        match stackSem_get_var rn s with SOME (wordLang_Word (w:'a
          word)) ->
          (let i = stackSem_state_stack_space s + w2n (w >>>
            backend_common_word_shift (:'a)) in
            if i < LENGTH (?_stack s) /\
               ((w >>> backend_common_word_shift (:'a)) <<
                 backend_common_word_shift (:'a) = w) then
                 (NONE,stackSem_set_var r (EL i (?_stack s)) s) else
                 (SOME stackSem_Error,stackSem_empty_env s)) | _84 ->
                 (SOME stackSem_Error,stackSem_empty_env s))) /\
   (stackSem_evaluate (stackLang_StackStore r n,s) =
      (if ~stackSem_state_use_stack s then (SOME stackSem_Error,s)
        else
      if LENGTH (?_stack s) <= stackSem_state_stack_space s + n then
        (SOME stackSem_Error,stackSem_empty_env s) else
        match stackSem_get_var r s with NONE -> (SOME
          stackSem_Error,stackSem_empty_env s) | SOME v ->
          (NONE,?_stack_fupd (K (LUPDATE v (stackSem_state_stack_space s
          + n) (?_stack s))) s))) /\
   (stackSem_evaluate (stackLang_StackStoreAny r rn,s) =
      (if ~stackSem_state_use_stack s then (SOME stackSem_Error,s)
        else
        match (stackSem_get_var r s,stackSem_get_var rn s) with (SOME
          v,SOME (wordLang_Word (w:'a word))) ->
          (let i = stackSem_state_stack_space s + w2n (w >>>
            backend_common_word_shift (:'a)) in
            if i < LENGTH (?_stack s) /\
               ((w >>> backend_common_word_shift (:'a)) <<
                 backend_common_word_shift (:'a) = w) then
                 (NONE,?_stack_fupd (K (LUPDATE v i (?_stack s))) s)
                 else (SOME stackSem_Error,stackSem_empty_env s)) | _85
                 -> (SOME stackSem_Error,stackSem_empty_env s))) /\
   (stackSem_evaluate (stackLang_StackGetSize r,s) =
      (if ~stackSem_state_use_stack s then (SOME stackSem_Error,s)
        else
      (NONE,stackSem_set_var r (wordLang_Word (n2w
        (stackSem_state_stack_space s))) s))) /\
   (stackSem_evaluate (stackLang_StackSetSize r,s) =
      (if ~stackSem_state_use_stack s then (SOME stackSem_Error,s)
        else
      match stackSem_get_var r s with SOME (wordLang_Word (w:'a
        word)) ->
          (if LENGTH (?_stack s) <= w2n w then (SOME
            stackSem_Error,stackSem_empty_env s) else
            (NONE,stackSem_set_var r (wordLang_Word (w <<
            backend_common_word_shift (:'a)))
                        (stackSem_state_stack_space_fupd (K (w2n w))
                          s))) | _86 -> (SOME stackSem_Error,s))) /\
   (stackSem_evaluate (stackLang_BitmapLoad r v,s) =
      (if ~stackSem_state_use_stack s \/ r = v then (SOME
        stackSem_Error,s) else
      match stackSem_get_var v s with SOME (wordLang_Word w) ->
          (if LENGTH (stackSem_state_bitmaps s) <= w2n w then
            (SOME stackSem_Error,s) else (NONE,stackSem_set_var r
            (wordLang_Word (EL (w2n w) (stackSem_state_bitmaps s)))
            s)) | _87 -> (SOME stackSem_Error,s)))`;;

(* We prove that the clock never increases. *)

(* observational semantics *)

let semantics_def = cake_define
  `stackSem_semantics start s =
   (let wordLang_prog = wordLang_Call NONE (INL start) NONE in
   if ?k. let res = FST (stackSem_evaluate
     (wordLang_prog,?_clock_fupd (K k) s)) in ~(
            res = SOME stackSem_TimeOut) /\ ~(res = SOME
              (stackSem_Result (wordLang_Loc 1 0))) /\
            (!w. ~(res = SOME (stackSem_Halt (wordLang_Word w)))) /\
              (!f. ~(res = SOME (stackSem_FinalFFI f))) then ffi_Fail
              else
     match some (\res.
       ?k t r outcome.
         stackSem_evaluate (wordLang_prog,?_clock_fupd (K k) s) =
           (SOME r,t) /\
         (match r with stackSem_FinalFFI e -> outcome =
           ffi_FFI_outcome e | stackSem_Halt w -> outcome = (if w =
           wordLang_Word (n2w 0) then ffi_Success else
           ffi_Resource_limit_hit) | stackSem_Result _88 -> outcome =
           ffi_Success | _89 -> F) /\
         res = ffi_Terminate outcome (ffi_state_io_events (?_ffi t)))
           with SOME res -> res | NONE ->
       ffi_Diverge
          (build_lprefix_lub
            (IMAGE (\k. fromList (ffi_state_io_events (?_ffi (SND
              (stackSem_evaluate (wordLang_prog,?_clock_fupd (K k)
              s)))))) UNIV)))`;;

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
