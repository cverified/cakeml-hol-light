(* ======================================================== *)
(*  ag32_memory: ported from HOL4's
    compiler/backend/ag32/ag32_memoryScript.sml
    A definition theory, with 100 definitions and 63 theorems.
    Needed by 6 files of the port.  *)
(* ======================================================== *)

(*
  Define the memory layout for running CakeML programs on Silver, and implement
  the startup code, the FFI jumps, and the CakeML basis's primitive FFI calls
  in Silver machine code. Also define shallow embeddings of the FFI primitives
  and prove theorems summarising their effects.
*)

needs "basis/Marshalling.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/encoders/asm/asmProps.ml";;
needs "compiler/encoders/asm/asmSem.ml";;
needs "compiler/inference/infer.ml";;
needs "lib/alignment.ml";;
needs "lib/bitstring.ml";;
needs "lib/byte.ml";;
needs "misc/misc.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ag32_memory"
  ["Marshalling"; "asmProps"; "asmSem"; "lab_to_target"; "mlstring"];;

let _ = do_list hide_constant ["cf"; "read"; "write"];;
(* HOL4 ancestors outside the port: ag32 ag32_target *)

(* TODO: move *)

let get_mem_word_def = new_definition
  `(get_mem_word (m:word32->word8) (pc':word32):word32) =
   (m (pc' + (n2w 3)) @@
    ((m (pc' + (n2w 2)) @@
      ((m (pc' + (n2w 1)) @@
        m (pc')):word16)):word24))`;;

let set_mem_word_def = new_definition
  `(set_mem_word (a:word32) (w:word32):(word32->word8)->word32->word8) =
     ((a =+ (((7 >< 0) w):word8)) o
     (((a + (n2w 1)) =+ (((15 >< 8) w):word8)) o
     (((a + (n2w 2)) =+ (((23 >< 16) w):word8)) o
     (((a + (n2w 3)) =+ (((31 >< 24) w):word8))))))`;;

let set_mem_word_neq = prove
 (`~(x = k) /\ ~(x + (n2w 1) = k) /\ ~(x + (n2w 2) = k) /\ ~(x + (n2w 3) = k)
  ==>
     set_mem_word x y m k = m k`,
  CHEAT_TAC);;

(* TODO: copied from stack_allocProofTheory *)
let good_dimindex_32 = prove
 (`(byte_aligned (w:word32) <=>
     ((w && (n2w 3)) = (n2w 0)))`,
  CHEAT_TAC);;

let get_mem_word_set_mem_word = prove
 (`byte_aligned a /\ byte_aligned x ==>
   (get_mem_word (set_mem_word a w m) x =
    (if a = x then w else get_mem_word m x))`,
  CHEAT_TAC);;

let get_mem_word_asm_write_bytearray_UNCHANGED_LT = prove
 (`(pc <+ a) /\
   (pc + (n2w 1) <+ a) /\
   (pc + (n2w 2) <+ a) /\
   (pc + (n2w 3) <+ a) /\
   w2n a + LENGTH ls < dimword (:32) ==>
   get_mem_word
   (asm_write_bytearray a ls m) pc =
   get_mem_word m pc`,
  CHEAT_TAC);;

let get_mem_word_UPDATE = prove
 (`~(pc = k) /\ ~(pc + (n2w 1) = k) /\ ~(pc + (n2w 2) = k) /\ ~(pc + (n2w 3) =
  k) ==>
   get_mem_word
     ((k =+ v) m) pc =
   get_mem_word m pc`,
  CHEAT_TAC);;

let get_mem_word_change_mem = prove
 (`(!k. k < 4 ==> (m1 (pc + n2w k) = m2 (pc + n2w k))) ==>
   (get_mem_word m1 pc = get_mem_word m2 pc)`,
  CHEAT_TAC);;

let dfn'Normal_PC = prove
 (`?_PC
      (dfn'Normal x s) = ?_PC s + (n2w 4)`,
  CHEAT_TAC);;

let dfn'Normal_MEM = prove
 (`?_MEM
      (dfn'Normal x s) = ?_MEM s`,
  CHEAT_TAC);;

let dfn'JumpIfZero_PC = prove
 (`(?_PC (dfn'JumpIfZero (fSnd,Reg i,Imm w,Reg r) s) =
      (if ?_R s r = (n2w 0) then ?_PC s + ?_R s i else ?_PC s + (n2w 4))) /\
   (?_PC (dfn'JumpIfZero (fSnd,Imm v,Imm w,Reg r) s) =
      (if ?_R s r = (n2w 0) then ?_PC s + sw2sw v else ?_PC s + (n2w 4))) /\
   (?_PC (dfn'JumpIfZero (fSnd,Imm v,Imm w,Imm x) s) =
      (if sw2sw x = ((n2w 0):word32) then ?_PC s + sw2sw v else ?_PC s +
        (n2w 4)))`,
  CHEAT_TAC);;

let dfn'JumpIfNotZero_PC = prove
 (`(?_PC (dfn'JumpIfNotZero (fSnd,Reg i,Imm w,Reg r) s) =
      (if ~(?_R s r = (n2w 0)) then ?_PC s + ?_R s i else ?_PC s + (n2w 4)))
        /\
   (?_PC (dfn'JumpIfNotZero (fSnd,Imm v,Imm w,Reg r) s) =
      (if ~(?_R s r = (n2w 0)) then ?_PC s + sw2sw v else ?_PC s + (n2w 4)))
        /\
   (?_PC (dfn'JumpIfNotZero (fSnd,Imm v,Imm w,Imm x) s) =
      (if ~(sw2sw x = ((n2w 0):word32)) then ?_PC s + sw2sw v else ?_PC s
        + (n2w 4)))`,
  CHEAT_TAC);;

let dfn'JumpIfNotZero_MEM = prove
 (`?_MEM
      (dfn'JumpIfNotZero x s) = ?_MEM s`,
  CHEAT_TAC);;

let dfn'Interrupt_PC = prove
 (`(?_PC (dfn'Interrupt s) = ?_PC s + (n2w 4))`,
  CHEAT_TAC);;

let dfn'Interrupt_MEM = prove
 (`(?_MEM (dfn'Interrupt s) = ?_MEM s)`,
  CHEAT_TAC);;

let dfn'Jump_MEM = prove
 (`(?_MEM (dfn'Jump x s) = ?_MEM s)`,
  CHEAT_TAC);;

let dfn'LoadMEM_PC = prove
 (`?_PC
      (dfn'LoadMEM x s) = ?_PC s + (n2w 4)`,
  CHEAT_TAC);;

let dfn'LoadMEM_MEM = prove
 (`?_MEM
      (dfn'LoadMEM x s) = ?_MEM s`,
  CHEAT_TAC);;

let dfn'StoreMEMByte_PC = prove
 (`?_PC
      (dfn'StoreMEMByte x s) = ?_PC s + (n2w 4)`,
  CHEAT_TAC);;

let dfn'LoadMEMByte_PC = prove
 (`?_PC
      (dfn'LoadMEMByte x s) = ?_PC s + (n2w 4)`,
  CHEAT_TAC);;

let dfn'LoadMEMByte_MEM = prove
 (`?_MEM
      (dfn'LoadMEMByte x s) = ?_MEM s`,
  CHEAT_TAC);;

let dfn'Shift_PC = prove
 (`?_PC
      (dfn'Shift x s) = ?_PC s + (n2w 4)`,
  CHEAT_TAC);;

let dfn'Shift_MEM = prove
 (`?_MEM
      (dfn'Shift x s) = ?_MEM s`,
  CHEAT_TAC);;

let dfn'LoadConstant_PC = prove
 (`?_PC
      (dfn'LoadConstant x s) = ?_PC s + (n2w 4)`,
  CHEAT_TAC);;

let dfn'LoadConstant_MEM = prove
 (`?_MEM
      (dfn'LoadConstant x s) = ?_MEM s`,
  CHEAT_TAC);;

let dfn'JumpIfZero_MEM = prove
 (`?_MEM
      (dfn'JumpIfZero x s) = ?_MEM s`,
  CHEAT_TAC);;

(* -- *)

let memory_size_def = new_definition
  `memory_size = 128 * 10 EXP 6`;;

let cline_size_def = new_definition
  `cline_size = 2 * 1024`;;

let stdin_size_def = new_definition
  `stdin_size = 5 * 1024 * 1024`;;

let output_buffer_size_def = new_definition
  `output_buffer_size = 2048`;;

let heap_size_def = new_definition
  `heap_size = 80 * 1024 * 1024`;;

let startup_code_size_def = new_definition
  `startup_code_size = 240`;;

(* Memory Layout:

  +-------------------+
  | * CakeML data     |
  +-------------------+  about 23MB left for these
  | * CakeML code     |
  +-------------------+
  | * FFI call jumps  |  <= 176 ((9 + 2) * 16) bytes
  +-------------------+
  | CakeML stack/heap |  heap_size bytes (~100Mb)
  +-------------------+  <- heap_start_offset
  | --- (padding) --- |  (will arrange for this to be 0)
  +-------------------+
  | FFI code          |  (4 * LENGTH ag32_ffi_code) bytes (~640b)
  +-------------------+
  | FFI call id       |  4 bytes (as a word)
  +-------------------+
  | output buffer     |  output_buffer_size bytes (~2Kb)
  +-------------------+
  | output length     |  4 bytes
  +-------------------+
  | output id         |  8 bytes (* ridiculously overpowered... *)
  +-------------------+
  | + stdin           |  stdin_size bytes (~5Mb)
  +-------------------+
  | + stdin length    |  4 bytes
  +-------------------+
  | stdin pointer     |  4 bytes
  +-------------------+
  | + cline args      |  cline_size bytes (~1024b)
  +-------------------+
  | + cline arg count |  4 bytes (as a word)
  +-------------------+  <- startup_code_size
  | ---- padding ---- |
  +-------------------+
  | * startup code    |  (LENGTH startup_code) bytes (~72b, ≤216b (18*12))
  +-------------------+

  The starred items depend on the output of the compiler;
  the other items are boilerplate for every application.
  The plussed items are set by the host before execution.
*)

let FFI_codes_def = new_definition
  `FFI_codes =
     [
     ((implode ""),0); ((implode "get_arg_count"),1); ((implode
       "get_arg_length"),2); ((implode "get_arg"),3); ((implode "read"),4);
       ((implode "write"),5); ((implode "open_in"),6); ((implode
       "open_out"),7); ((implode "close"),8)]
   // ;(«exit», 9n)`;;

let stdin_offset_def = new_definition
  `stdin_offset = startup_code_size + 4 + cline_size`;;

let output_offset_def = new_definition
  `output_offset = stdin_offset + 4 + 4 + stdin_size`;;

let ffi_code_start_offset_def = new_definition
  `ffi_code_start_offset =
     output_offset + 8 + 4 + output_buffer_size + 4`;;

let length_ag32_ffi_code_def = new_definition
  `length_ag32_ffi_code = 1272`;;

let heap_start_offset_def = new_definition
  `heap_start_offset =
     ffi_code_start_offset + length_ag32_ffi_code`;;

let ffi_jumps_offset_def = new_definition
  `ffi_jumps_offset =
     heap_start_offset + heap_size`;;

let ag32_ffi_return_code_def = new_definition
  `ag32_ffi_return_code = [
    Normal (fAdd,(n2w 1),Imm (n2w 0),Imm (n2w 0));
    Normal (fSnd,(n2w 2),Imm (n2w 0),Imm (n2w 0));
    Normal (fSnd,(n2w 3),Imm (n2w 0),Imm (n2w 0));
    Normal (fSnd,(n2w 4),Imm (n2w 0),Imm (n2w 0));
    Normal (fSnd,(n2w 5),Imm (n2w 0),Imm (n2w 0));
    Normal (fSnd,(n2w 6),Imm (n2w 0),Imm (n2w 0));
    Normal (fSnd,(n2w 7),Imm (n2w 0),Imm (n2w 0));
    Normal (fSnd,(n2w 8),Imm (n2w 0),Imm (n2w 0));
    Interrupt;
    lab_Jump (fSnd,(n2w 0),Reg (n2w 0))]`;;

let ag32_ffi_return_def = new_definition
  `ag32_ffi_return s =
   let s = dfn'Normal (fAdd,(n2w 1),Imm (n2w 0),Imm (n2w 0)) s in
   let s = dfn'Normal (fSnd,(n2w 2),Imm (n2w 0),Imm (n2w 0)) s in
   let s = dfn'Normal (fSnd,(n2w 3),Imm (n2w 0),Imm (n2w 0)) s in
   let s = dfn'Normal (fSnd,(n2w 4),Imm (n2w 0),Imm (n2w 0)) s in
   let s = dfn'Normal (fSnd,(n2w 5),Imm (n2w 0),Imm (n2w 0)) s in
   let s = dfn'Normal (fSnd,(n2w 6),Imm (n2w 0),Imm (n2w 0)) s in
   let s = dfn'Normal (fSnd,(n2w 7),Imm (n2w 0),Imm (n2w 0)) s in
   let s = dfn'Normal (fSnd,(n2w 8),Imm (n2w 0),Imm (n2w 0)) s in
   let s = dfn'Interrupt s in
   let s = dfn'Jump (fSnd,(n2w 0),Reg (n2w 0)) s in
   s`;;

let ag32_ffi_return_thm = prove
 (`(ag32_ffi_return s = ffi_state_CarryFlag_fupd (K F)
  (ffi_state_OverflowFlag_fupd (K F) (ffi_state_io_events_fupd (K (SNOC (?_MEM
  s) (ffi_state_io_events s))) (ffi_state_R_fupd (K (((n2w 0) =+ (?_PC s + n2w
  (4 * LENGTH ag32_ffi_return_code)))
                   (((n2w 1) =+ (n2w 0))
                   (((n2w 2) =+ (n2w 0))
                   (((n2w 3) =+ (n2w 0))
                   (((n2w 4) =+ (n2w 0))
                   (((n2w 5) =+ (n2w 0))
                   (((n2w 6) =+ (n2w 0))
                   (((n2w 7) =+ (n2w 0))
                   (((n2w 8) =+ (n2w 0)) (?_R s)))))))))))
                     (ffi_state_PC_fupd (K (?_R s (n2w 0)))
    s)))))`,
  CHEAT_TAC);;

let ag32_ffi_copy_code_def = new_definition
  `ag32_ffi_copy_code = [
      JumpIfZero (fSnd,Reg (n2w 2),Imm (n2w 0),Reg (n2w 1));
      LoadMEMByte ((n2w 8),Reg (n2w 3));
      StoreMEMByte (Reg (n2w 8),Reg (n2w 5));
      Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1));
      Normal (fInc,(n2w 5),Reg (n2w 5),Imm (n2w 1));
      Normal (fDec,(n2w 1),Reg (n2w 1),Imm (n2w 1));
      JumpIfZero (fSnd,Imm ((n2w 4) * --(n2w 6)),Imm (n2w 0),Imm (n2w
        0))]`;;

(* the termination relation that HOL4 gives is
     MEASURE (\s. w2n (?_R s (n2w 1)))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 ag32_memoryScript.sml:461-471: the tactic that proves the
   termination *)
let ag32_ffi_copy_def,ag32_ffi_copy_ind = define_guess
  `ag32_ffi_copy s0 =
   let s = dfn'JumpIfZero (fSnd,Reg (n2w 2),Imm (n2w 0),Reg (n2w 1)) s0 in
   if (?_R s0 (n2w 1) = (n2w 0)) then s else let s = dfn'LoadMEMByte ((n2w
     8),Reg (n2w 3)) s in
   let s = dfn'StoreMEMByte (Reg (n2w 8),Reg (n2w 5)) s in
   let s = dfn'Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1)) s in
   let s = dfn'Normal (fInc,(n2w 5),Reg (n2w 5),Imm (n2w 1)) s in
   let s0 = dfn'Normal (fDec,(n2w 1),Reg (n2w 1),Imm (n2w 1)) s in
   let s = dfn'JumpIfZero (fSnd,Imm ((n2w 4) * --(n2w 6)),Imm (n2w 0),Imm
     (n2w 0)) s0 in
   ag32_ffi_copy s`;;

let ag32_ffi_copy_thm = prove
 (`!s written.
   bytes_in_memory (?_R s (n2w 3)) written (?_MEM s) md /\ (w2n (?_R s (n2w
     1)) = LENGTH written) /\
   DISJOINT md {w | ?_R s (n2w 5) <=+ w /\ w <+ ?_R s (n2w 5) + n2w (LENGTH
     written)} /\
   w2n (?_R s (n2w 5)) + LENGTH written < dimword (:32) /\
   w2n (?_R s (n2w 3)) + LENGTH written < dimword (:32) ==>
   (?r1 r3 r5 r8.
   (ag32_ffi_copy s = ?_MEM_fupd (K (asm_write_bytearray (?_R s (n2w 5))
     written (?_MEM s))) (?_R_fupd (K (((n2w 1) =+ r1)
                   (((n2w 3) =+ r3)
                   (((n2w 5) =+ r5)
                   (((n2w 8) =+ r8) (?_R s)))))) (?_PC_fupd (K (?_PC s + ?_R
                     s (n2w 2)))
    s))))`,
  CHEAT_TAC);;

(* HOL4 ag32_memoryScript.sml:582-617: code that the source has in a comment *)

(* "" ffi
  PC is ffi_code_start_offset
 *)
let ag32_ffi__entrypoint_def = new_definition
  `ag32_ffi__entrypoint = 0`;;

let ag32_ffi__def = new_definition
  `ag32_ffi_ s =
   let s = dfn'Normal (fAdd,(n2w 5),Imm (n2w 0),Imm (n2w 0)) s in
   dfn'Jump (fSnd,(n2w 0),Reg (n2w 0)) s`;;

let ag32_ffi__code_def = new_definition
  `ag32_ffi__code =
     [
     Normal (fAdd,(n2w 5),Imm (n2w 0),Imm (n2w 0));
     lab_Jump (fSnd,(n2w 0),Reg (n2w 0))]`;;

(* get_arg_count
   PC is ffi_code_start_offset
         + 4 * LENGTH ag32_ffi__code
   pointer is in r3 *)

let ag32_ffi_get_arg_count_entrypoint_def = new_definition
  `ag32_ffi_get_arg_count_entrypoint =
   ag32_ffi__entrypoint + 4 * LENGTH ag32_ffi__code`;;

let ag32_ffi_get_arg_count_main_code_def = new_definition
  `ag32_ffi_get_arg_count_main_code =
     [LoadConstant ((n2w 5),F,n2w (ffi_code_start_offset - 1));
      StoreMEMByte (Imm (n2w (THE (ALOOKUP FFI_codes (implode
        "get_arg_count")))),Reg (n2w 5));
      LoadConstant ((n2w 5),F,n2w startup_code_size);
      LoadMEM ((n2w 5),Reg (n2w 5));
      StoreMEMByte (Reg (n2w 5),Reg (n2w 3));
      asm_Shift (shiftLR,(n2w 5),Reg (n2w 5),Imm (n2w 8));
      Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 0));
      StoreMEMByte (Reg (n2w 5),Reg (n2w 3))]`;;

let ag32_ffi_get_arg_count_code_def = new_definition
  `ag32_ffi_get_arg_count_code =
     APPEND ag32_ffi_get_arg_count_main_code ag32_ffi_return_code`;;

let ag32_ffi_get_arg_count_main_def = new_definition
  `ag32_ffi_get_arg_count_main s =
   let s = dfn'LoadConstant ((n2w 5),F,n2w (ffi_code_start_offset - 1)) s in
   let s = dfn'StoreMEMByte (Imm (n2w (THE (ALOOKUP FFI_codes (implode
     "get_arg_count")))),Reg (n2w 5)) s in
   let s = dfn'LoadConstant ((n2w 5),F,n2w startup_code_size) s in
   let s = dfn'LoadMEM ((n2w 5),Reg (n2w 5)) s in
   let s = dfn'StoreMEMByte (Reg (n2w 5),Reg (n2w 3)) s in
   let s = dfn'Shift (shiftLR,(n2w 5),Reg (n2w 5),Imm (n2w 8)) s in
   let s = dfn'Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 0)) s in
   let s = dfn'StoreMEMByte (Reg (n2w 5),Reg (n2w 3)) s in
   s`;;

let ag32_ffi_get_arg_count_main_thm = prove
 (`(get_mem_word (?_MEM s) (n2w startup_code_size) = n2w len) /\ len < 256 *
  256 ==>
   (?r3 r5.
    (ag32_ffi_get_arg_count_main s = ?_R_fupd (K (((n2w 3) =+ r3) (((n2w 5)
      =+ r5) (?_R s)))) (?_MEM_fupd (K
                 (asm_write_bytearray (?_R s (n2w 3)) [n2w len; n2w (len DIV
                   256)]
                   (((n2w (ffi_code_start_offset - 1)) =+ n2w (THE (ALOOKUP
                     FFI_codes (implode "get_arg_count")))) (?_MEM s))))
                     (?_PC_fupd (K (?_PC s + n2w (4 * (LENGTH
                     ag32_ffi_get_arg_count_main_code))))
     s))))`,
  CHEAT_TAC);;

let ag32_ffi_get_arg_count_def = new_definition
  `ag32_ffi_get_arg_count s =
   let s = ag32_ffi_get_arg_count_main s in
   ag32_ffi_return s`;;

(* get_arg_length
   PC is ffi_code_start_offset
         + ag32_ffi_get_arg_count_entrypoint
         + 4 * LENGTH ag32_ffi_get_arg_count_code
   r3 contains pointer to byte array with the arg index: [index % 256, index / 256]
   the array should afterwards contain the length of the arg at index (in the same format) *)

let ag32_ffi_get_arg_length_entrypoint_def = new_definition
  `ag32_ffi_get_arg_length_entrypoint =
   ag32_ffi_get_arg_count_entrypoint + 4 * LENGTH
     ag32_ffi_get_arg_count_code`;;

let ag32_ffi_get_arg_length_setup_code_def = new_definition
  `ag32_ffi_get_arg_length_setup_code =
     [LoadConstant ((n2w 5),F,n2w (ffi_code_start_offset - 1));
      StoreMEMByte (Imm (n2w (THE (ALOOKUP FFI_codes (implode
        "get_arg_length")))),Reg (n2w 5));
      LoadConstant ((n2w 5),F,(n2w (startup_code_size + 4)));
      // r5 contains pointer
      LoadMEMByte ((n2w 6),Reg (n2w 3));
      Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1));
      LoadMEMByte ((n2w 7),Reg (n2w 3));
      asm_Shift (shiftLL,(n2w 7),Reg (n2w 7),Imm (n2w 8));
      Normal (fDec,(n2w 3),Reg (n2w 3),Imm (n2w 1));
      Normal (fInc,(n2w 6),Reg (n2w 6),Imm (n2w 1));
      Normal (fAdd,(n2w 6),Reg (n2w 6),Reg (n2w 7));
      // r6 contains index+1
      LoadConstant ((n2w 7),F,n2w (4 * 8))]`;;

let ag32_ffi_get_arg_length_loop_code_def = new_definition
  `ag32_ffi_get_arg_length_loop_code =
     [
      // decompiler version:
      // [JumpIfZero (fSnd,Imm (4w * 7w),Imm 0w,Imm 0w);
      // Normal (fSnd,4w,Reg 4w,Imm 0w);
      // LoadMEMByte (8w,Reg 5w);
      // Normal (fInc,5w,Reg 5w,Imm 1w);
      // Normal (fInc,4w,Reg 4w,Imm 1w);
      // JumpIfNotZero (fSnd,Imm (4w * -3w),Imm 0w,Reg 8w);
      // Normal (fDec,6w,Reg 6w,Imm 1w);
      // JumpIfNotZero (fSnd,Imm (4w * -6w),Imm 0w,Reg 6w)]
      JumpIfZero (fSnd,Reg (n2w 7),Imm (n2w 0),Reg (n2w 6));
      Normal (fSnd,(n2w 4),Reg (n2w 4),Imm (n2w 0));
      LoadMEMByte ((n2w 8),Reg (n2w 5));
      Normal (fInc,(n2w 5),Reg (n2w 5),Imm (n2w 1));
      Normal (fInc,(n2w 4),Reg (n2w 4),Imm (n2w 1));
      JumpIfNotZero (fSnd,Imm ((n2w 4) * --(n2w 3)),Imm (n2w 0),Reg (n2w
        8));
      Normal (fDec,(n2w 6),Reg (n2w 6),Imm (n2w 1));
      JumpIfZero (fSnd,Imm ((n2w 4) * --(n2w 7)),Imm (n2w 0),Imm (n2w
        0))]`;;

let ag32_ffi_get_arg_length_store_code_def = new_definition
  `ag32_ffi_get_arg_length_store_code =
     [Normal (fDec,(n2w 4),Reg (n2w 4),Imm (n2w 1));
      StoreMEMByte (Reg (n2w 4),Reg (n2w 3));
      asm_Shift (shiftLR,(n2w 4),Reg (n2w 4),Imm (n2w 8));
      Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1));
      StoreMEMByte (Reg (n2w 4),Reg (n2w 3))]`;;

let ag32_ffi_get_arg_length_code_def = new_definition
  `ag32_ffi_get_arg_length_code = APPEND (APPEND (APPEND
  ag32_ffi_get_arg_length_setup_code
     ag32_ffi_get_arg_length_loop_code)
     ag32_ffi_get_arg_length_store_code)
     ag32_ffi_return_code`;;

let ag32_ffi_get_arg_length_setup_def = new_definition
  `ag32_ffi_get_arg_length_setup s =
   let s = dfn'LoadConstant ((n2w 5),F,n2w (ffi_code_start_offset - 1)) s in
   let s = dfn'StoreMEMByte (Imm (n2w (THE (ALOOKUP FFI_codes (implode
     "get_arg_length")))),Reg (n2w 5)) s in
   let s = dfn'LoadConstant ((n2w 5),F,(n2w (startup_code_size + 4))) s in
   let s = dfn'LoadMEMByte ((n2w 6),Reg (n2w 3)) s in
   let s = dfn'Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1)) s in
   let s = dfn'LoadMEMByte ((n2w 7),Reg (n2w 3)) s in
   let s = dfn'Shift (shiftLL,(n2w 7),Reg (n2w 7),Imm (n2w 8)) s in
   let s = dfn'Normal (fDec,(n2w 3),Reg (n2w 3),Imm (n2w 1)) s in
   let s = dfn'Normal (fInc,(n2w 6),Reg (n2w 6),Imm (n2w 1)) s in
   let s = dfn'Normal (fAdd,(n2w 6),Reg (n2w 6),Reg (n2w 7)) s in
   let s = dfn'LoadConstant ((n2w 7),F,n2w (4 * 8)) s in
   s`;;

let ag32_ffi_get_arg_length_setup_thm = prove
 (`bytes_in_memory (?_R s (n2w 3)) [l0; l1] (?_MEM s) md /\ ~(n2w
  (ffi_code_start_offset - 1) IN md) ==>
   (?ov cf.
   (ag32_ffi_get_arg_length_setup s = ?_OverflowFlag_fupd (K ov)
     (?_CarryFlag_fupd (K cf) (?_R_fupd (K (((n2w 5) =+ n2w (startup_code_size
     + 4))
           (((n2w 6) =+ n2w (256 * w2n l1 + w2n l0 + 1))
           (((n2w 7) =+ n2w (4 * 8)) (?_R s))))) (?_PC_fupd (K (?_PC s + n2w
             (4 * LENGTH ag32_ffi_get_arg_length_setup_code))) (?_MEM_fupd (K
             (((n2w (ffi_code_start_offset - 1)) =+ n2w (THE (ALOOKUP FFI_codes
             (implode "get_arg_length")))) (?_MEM s)))
    s))))))`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (\s. minimal n. (?_MEM s (?_R s (n2w 5) + n2w n) = (n2w 0)))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 ag32_memoryScript.sml:848-867: the tactic that proves the
   termination *)
let ag32_ffi_get_arg_length_loop1_def,ag32_ffi_get_arg_length_loop1_ind =
  define_guess
  `ag32_ffi_get_arg_length_loop1 s =
     if (!n. ~(?_MEM s (?_R s (n2w 5) + n2w n) = (n2w 0))) then s else let s
       = dfn'LoadMEMByte ((n2w 8),Reg (n2w 5)) s in
     let s = dfn'Normal (fInc,(n2w 5),Reg (n2w 5),Imm (n2w 1)) s in
     let s0 = dfn'Normal (fInc,(n2w 4),Reg (n2w 4),Imm (n2w 1)) s in
     let s = dfn'JumpIfNotZero (fSnd,Imm ((n2w 4) * --(n2w 3)),Imm (n2w
       0),Reg (n2w 8)) s0 in
     if (?_R s0 (n2w 8) = (n2w 0)) then s else
       ag32_ffi_get_arg_length_loop1 s`;;

let ag32_ffi_get_arg_length_loop1_thm = prove
 (`ag32_ffi_get_arg_length_loop1 s =
   match OLEAST (\n. ?_MEM s (?_R s (n2w 5) + n2w n) = (n2w 0)) with
     NONE -> s
   | SOME n -> ?_R_fupd (K (((n2w 8) =+ (n2w 0))
                    (((n2w 4) =+ (?_R s (n2w 4) + n2w (n + 1)))
                    (((n2w 5) =+ (?_R s (n2w 5) + n2w (n + 1))) (?_R s)))))
                      (?_PC_fupd (K (?_PC s + n2w (4 * 4)))
     s)`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (\s. w2n (?_R s (n2w 6)))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 ag32_memoryScript.sml:940-951: the tactic that proves the
   termination *)
let ag32_ffi_get_arg_length_loop_def,ag32_ffi_get_arg_length_loop_ind =
  define_guess
  `ag32_ffi_get_arg_length_loop s0 =
   let s = dfn'JumpIfZero (fSnd,Reg (n2w 7),Imm (n2w 0),Reg (n2w 6)) s0 in
   if (?_R s0 (n2w 6) = (n2w 0)) then s else let s = dfn'Normal (fSnd,(n2w
     4),Reg (n2w 4),Imm (n2w 0)) s in
   let s = ag32_ffi_get_arg_length_loop1 s in
   let s = dfn'Normal (fDec,(n2w 6),Reg (n2w 6),Imm (n2w 1)) s in
   let s = dfn'JumpIfZero (fSnd,Imm ((n2w 4) * --(n2w 7)),Imm (n2w 0),Imm
     (n2w 0)) s in
   ag32_ffi_get_arg_length_loop s`;;

(* the termination relation that HOL4 gives is
     MEASURE (\(m,a,acc). minimal n. m (a + n2w n) = (n2w 0))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 ag32_memoryScript.sml:957-975: the tactic that proves the
   termination *)
let get_next_mem_arg_def,get_next_mem_arg_ind = define_guess
  `get_next_mem_arg (m:word32->word8) a acc =
     if m a = (n2w 0) \/ (!n. ~(m (a + n2w n) = (n2w 0))) then (a,REVERSE
       acc)
     else get_next_mem_arg m (a + (n2w 1)) (CONS (m a) acc)`;;

(* HOL4 ag32_memoryScript.sml:977: ML code, not ported *)

let get_next_mem_arg_LEAST = prove
 (`!m a acc. get_next_mem_arg m a acc =
    match OLEAST (\n. m (a + n2w n) = (n2w 0)) with NONE -> (a,REVERSE acc)
    | SOME n -> (a + n2w n,APPEND (REVERSE acc) (list_of_seq (\n. m (a +
      n2w n)) n))`,
  CHEAT_TAC);;

let get_mem_arg_def,get_mem_arg_ind = define_guess
  `(get_mem_arg m a 0 = get_next_mem_arg m a []) /\
   (get_mem_arg m a (SUC n) =
       let (a,_) = get_next_mem_arg m a [] in
         get_mem_arg m (a + (n2w 1)) n)`;;

let ag32_ffi_get_arg_length_loop_thm = prove
 (`(?_R s (n2w 6) = n2w (index + 1)) /\ index <= cline_size /\
   (?_R s (n2w 7) = n2w (4 * 8)) /\
   (?n. ?_MEM s (?_R s (n2w 5) + n2w n) = (n2w 0)) ==>
   (?r8 r6 r5.
   (ag32_ffi_get_arg_length_loop s = ?_R_fupd (K (((n2w 8) =+ r8)
                   (((n2w 4) =+ n2w (LENGTH (SND (get_mem_arg (?_MEM s) (?_R
                     s (n2w 5)) index)) + 1))
                   (((n2w 6) =+ r6)
                   (((n2w 5) =+ r5) (?_R s)))))) (?_PC_fupd (K (?_PC s + n2w
                     (4 * LENGTH ag32_ffi_get_arg_length_loop_code)))
    s)))`,
  CHEAT_TAC);;

let ag32_ffi_get_arg_length_store_def = new_definition
  `ag32_ffi_get_arg_length_store s =
   let s = dfn'Normal (fDec,(n2w 4),Reg (n2w 4),Imm (n2w 1)) s in
   let s = dfn'StoreMEMByte (Reg (n2w 4),Reg (n2w 3)) s in
   let s = dfn'Shift (shiftLR,(n2w 4),Reg (n2w 4),Imm (n2w 8)) s in
   let s = dfn'Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1)) s in
   let s = dfn'StoreMEMByte (Reg (n2w 4),Reg (n2w 3)) s in
   s`;;

let ag32_ffi_get_arg_length_store_thm = prove
 (`(?_R s (n2w 4) = n2w (n + 1)) /\
   n < dimword (:32) ==>
   (?r4 r3.
   (ag32_ffi_get_arg_length_store s = ?_MEM_fupd (K (((?_R s (n2w 3)) =+
     (n2w n))
                     (((?_R s (n2w 3) + (n2w 1)) =+ (n2w (n DIV 256)))
                       (?_MEM s)))) (?_R_fupd (K (((n2w 4) =+ r4)
                   (((n2w 3) =+ r3) (?_R s)))) (?_PC_fupd (K (?_PC s + n2w
                     (4 * LENGTH ag32_ffi_get_arg_length_store_code)))
    s))))`,
  CHEAT_TAC);;

let ag32_ffi_get_arg_length_def = new_definition
  `ag32_ffi_get_arg_length s =
     let s = ag32_ffi_get_arg_length_setup s in
     let s = ag32_ffi_get_arg_length_loop s in
     let s = ag32_ffi_get_arg_length_store s in
     ag32_ffi_return s`;;

(* get_arg *)

let ag32_ffi_get_arg_entrypoint_def = new_definition
  `ag32_ffi_get_arg_entrypoint =
   ag32_ffi_get_arg_length_entrypoint + 4 * LENGTH
     ag32_ffi_get_arg_length_code`;;

let ag32_ffi_get_arg_setup_code_def = new_definition
  `ag32_ffi_get_arg_setup_code =
     [LoadConstant ((n2w 5),F,n2w (ffi_code_start_offset - 1));
      StoreMEMByte (Imm (n2w (THE (ALOOKUP FFI_codes (implode
        "get_arg")))),Reg (n2w 5));
      LoadConstant ((n2w 5),F,(n2w (startup_code_size + 4)));
      // r5 contains pointer
      LoadMEMByte ((n2w 6),Reg (n2w 3));
      Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1));
      LoadMEMByte ((n2w 7),Reg (n2w 3));
      asm_Shift (shiftLL,(n2w 7),Reg (n2w 7),Imm (n2w 8));
      Normal (fDec,(n2w 3),Reg (n2w 3),Imm (n2w 1));
      Normal (fAdd,(n2w 6),Reg (n2w 6),Reg (n2w 7))]
   // r6 contains index`;;

let ag32_ffi_get_arg_find_code_def = new_definition
  `ag32_ffi_get_arg_find_code =
     [JumpIfZero (fSnd,Imm ((n2w 4) * (n2w 6)),Imm (n2w 0),Reg (n2w 6));
      LoadMEMByte ((n2w 8),Reg (n2w 5));
      Normal (fInc,(n2w 5),Reg (n2w 5),Imm (n2w 1));
      JumpIfNotZero (fSnd,Imm ((n2w 4) * --(n2w 2)),Imm (n2w 0),Reg (n2w
        8));
      Normal (fDec,(n2w 6),Reg (n2w 6),Imm (n2w 1));
      JumpIfZero (fSnd,Imm ((n2w 4) * --(n2w 5)),Imm (n2w 0),Imm (n2w
        0))]`;;

let ag32_ffi_get_arg_store_code_def = new_definition
  `ag32_ffi_get_arg_store_code =
     [LoadMEMByte ((n2w 8),Reg (n2w 5));
      JumpIfZero (fSnd,Imm ((n2w 4) * (n2w 5)),Imm (n2w 0),Reg (n2w 8));
      StoreMEMByte (Reg (n2w 8),Reg (n2w 3));
      Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1));
      Normal (fInc,(n2w 5),Reg (n2w 5),Imm (n2w 1));
      JumpIfZero (fSnd,Imm ((n2w 4) * --(n2w 5)),Imm (n2w 0),Imm (n2w
        0))]`;;

let ag32_ffi_get_arg_code_def = new_definition
  `ag32_ffi_get_arg_code = APPEND (APPEND (APPEND ag32_ffi_get_arg_setup_code
     ag32_ffi_get_arg_find_code)
     ag32_ffi_get_arg_store_code)
     ag32_ffi_return_code`;;

let ag32_ffi_get_arg_setup_def = new_definition
  `ag32_ffi_get_arg_setup s =
   let s = dfn'LoadConstant ((n2w 5),F,n2w (ffi_code_start_offset - 1)) s in
   let s = dfn'StoreMEMByte (Imm (n2w (THE (ALOOKUP FFI_codes (implode
     "get_arg")))),Reg (n2w 5)) s in
   let s = dfn'LoadConstant ((n2w 5),F,(n2w (startup_code_size + 4))) s in
   let s = dfn'LoadMEMByte ((n2w 6),Reg (n2w 3)) s in
   let s = dfn'Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1)) s in
   let s = dfn'LoadMEMByte ((n2w 7),Reg (n2w 3)) s in
   let s = dfn'Shift (shiftLL,(n2w 7),Reg (n2w 7),Imm (n2w 8)) s in
   let s = dfn'Normal (fDec,(n2w 3),Reg (n2w 3),Imm (n2w 1)) s in
   let s = dfn'Normal (fAdd,(n2w 6),Reg (n2w 6),Reg (n2w 7)) s in
   s`;;

let ag32_ffi_get_arg_setup_thm = prove
 (`bytes_in_memory (?_R s (n2w 3)) [l0; l1] (?_MEM s) md /\ ~(n2w
  (ffi_code_start_offset - 1) IN md) ==>
   (?r7 ov cf.
   (ag32_ffi_get_arg_setup s = ?_OverflowFlag_fupd (K ov) (?_CarryFlag_fupd
     (K cf) (?_R_fupd (K (((n2w 5) =+ n2w (startup_code_size + 4))
           (((n2w 6) =+ n2w (256 * w2n l1 + w2n l0))
           (((n2w 7) =+ r7) (?_R s))))) (?_PC_fupd (K (?_PC s + n2w (4 *
             LENGTH ag32_ffi_get_arg_setup_code))) (?_MEM_fupd (K (((n2w
             (ffi_code_start_offset - 1)) =+ n2w (THE (ALOOKUP FFI_codes
             (implode "get_arg")))) (?_MEM s)))
    s))))))`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (\s. minimal n. (?_MEM s (?_R s (n2w 5) + n2w n) = (n2w 0)))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 ag32_memoryScript.sml:1267-1286: the tactic that proves the
   termination *)
let ag32_ffi_get_arg_find1_def,ag32_ffi_get_arg_find1_ind = define_guess
  `ag32_ffi_get_arg_find1 s =
     if (!n. ~(?_MEM s (?_R s (n2w 5) + n2w n) = (n2w 0))) then s else let s
       = dfn'LoadMEMByte ((n2w 8),Reg (n2w 5)) s in
     let s0 = dfn'Normal (fInc,(n2w 5),Reg (n2w 5),Imm (n2w 1)) s in
     let s = dfn'JumpIfNotZero (fSnd,Imm ((n2w 4) * --(n2w 2)),Imm (n2w
       0),Reg (n2w 8)) s0 in
     if (?_R s0 (n2w 8) = (n2w 0)) then s else ag32_ffi_get_arg_find1 s`;;

let ag32_ffi_get_arg_find1_thm = prove
 (`ag32_ffi_get_arg_find1 s =
   match OLEAST (\n. ?_MEM s (?_R s (n2w 5) + n2w n) = (n2w 0)) with
     NONE -> s
   | SOME n -> ?_R_fupd (K (((n2w 8) =+ (n2w 0))
                    (((n2w 5) =+ (?_R s (n2w 5) + n2w (n + 1))) (?_R s))))
                      (?_PC_fupd (K (?_PC s + n2w (4 * 3)))
     s)`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (\s. w2n (?_R s (n2w 6)))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 ag32_memoryScript.sml:1357-1368: the tactic that proves the
   termination *)
let ag32_ffi_get_arg_find_def,ag32_ffi_get_arg_find_ind = define_guess
  `ag32_ffi_get_arg_find s0 =
   let s = dfn'JumpIfZero (fSnd,Imm ((n2w 4) * (n2w 6)),Imm (n2w 0),Reg (n2w
     6)) s0 in
   if (?_R s0 (n2w 6) = (n2w 0)) then s else let s = ag32_ffi_get_arg_find1
     s in
   let s = dfn'Normal (fDec,(n2w 6),Reg (n2w 6),Imm (n2w 1)) s in
   let s = dfn'JumpIfZero (fSnd,Imm ((n2w 4) * --(n2w 5)),Imm (n2w 0),Imm
     (n2w 0)) s in
   ag32_ffi_get_arg_find s`;;

let ag32_ffi_get_arg_find_thm = prove
 (`(?_R s (n2w 6) = n2w (index)) /\ index <= cline_size /\
   (?n. ?_MEM s (?_R s (n2w 5) + n2w n) = (n2w 0)) ==>
   (?r8 r6.
   (ag32_ffi_get_arg_find s = ?_R_fupd (K (((n2w 8) =+ r8)
                   (((n2w 5) =+ (if 0 < index then FST (get_mem_arg (?_MEM
                     s) (?_R s (n2w 5)) (index - 1)) + (n2w 1) else ?_R s (n2w
                     5)))
                   (((n2w 6) =+ r6) (?_R s))))) (?_PC_fupd (K (?_PC s + n2w
                     (4 * LENGTH ag32_ffi_get_arg_find_code)))
    s)))`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (\s. minimal n. (?_MEM s (?_R s (n2w 5) + n2w n) = (n2w 0)))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 ag32_memoryScript.sml:1453-1496: the tactic that proves the
   termination *)
let ag32_ffi_get_arg_store_def,ag32_ffi_get_arg_store_ind = define_guess
  `ag32_ffi_get_arg_store s =
   if ~(?n. (?_MEM s (?_R s (n2w 5) + n2w n) = (n2w 0)) /\ (!i. i <= n ==>
     ~(?_R s (n2w 3) = ?_R s (n2w 5) + n2w i))) then s else let s0 =
     dfn'LoadMEMByte ((n2w 8),Reg (n2w 5)) s in
   let s = dfn'JumpIfZero (fSnd,Imm ((n2w 4) * (n2w 5)),Imm (n2w 0),Reg (n2w
     8)) s0 in
   if ?_R s0 (n2w 8) = (n2w 0) then s else let s = dfn'StoreMEMByte (Reg
     (n2w 8),Reg (n2w 3)) s in
   let s = dfn'Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1)) s in
   let s = dfn'Normal (fInc,(n2w 5),Reg (n2w 5),Imm (n2w 1)) s in
   let s = dfn'JumpIfZero (fSnd,Imm ((n2w 4) * --(n2w 5)),Imm (n2w 0),Imm
     (n2w 0)) s in
   ag32_ffi_get_arg_store s`;;

let ag32_ffi_get_arg_store_thm = prove
 (`((OLEAST (\n. ?_MEM s (?_R s (n2w 5) + n2w n) = (n2w 0))) = SOME n) /\
   (!i. i <= n ==> ~(?_R s (n2w 5) + n2w i = ?_R s (n2w 3))) /\ Abbrev (w2n
     (?_R s (n2w 3)) + n < dimword (:32)) ==>
   (?r8 r5 r3.
   (ag32_ffi_get_arg_store s = ?_MEM_fupd (K (asm_write_bytearray (?_R s
     (n2w 3)) (list_of_seq (\n. ?_MEM s (?_R s (n2w 5) + n2w n)) n) (?_MEM s)))
     (?_R_fupd (K (((n2w 8) =+ r8)
                   (((n2w 5) =+ r5)
                   (((n2w 3) =+ r3) (?_R s))))) (?_PC_fupd (K (?_PC s + n2w
                     (4 * LENGTH ag32_ffi_get_arg_store_code)))
    s))))`,
  CHEAT_TAC);;

let ag32_ffi_get_arg_def = new_definition
  `ag32_ffi_get_arg s =
     let s = ag32_ffi_get_arg_setup s in
     let s = ag32_ffi_get_arg_find s in
     let s = ag32_ffi_get_arg_store s in
     ag32_ffi_return s`;;

(* read *)

let ag32_ffi_read_entrypoint_def = new_definition
  `ag32_ffi_read_entrypoint =
   ag32_ffi_get_arg_entrypoint + 4 * LENGTH ag32_ffi_get_arg_code`;;

let ag32_ffi_read_set_id_code_def = new_definition
  `ag32_ffi_read_set_id_code =
     [LoadConstant ((n2w 5),F,n2w (ffi_code_start_offset - 1));
      StoreMEMByte (Imm (n2w (THE (ALOOKUP FFI_codes (implode
        "read")))),Reg (n2w 5))]`;;

(* TODO: this would be shorter and maybe simpler using LoadMEM rather than LoadMEMByte *)
let ag32_ffi_read_check_conf_code_def = new_definition
  `ag32_ffi_read_check_conf_code = [
      Normal (fEqual,(n2w 6),Reg (n2w 2),Imm (n2w 8));
      // r6 = (LENGTH conf = 8)
      Normal (fSub,(n2w 4),Reg (n2w 4),Imm (n2w 4));
      // r4 = LENGTH tll
      LoadMEMByte ((n2w 2),Reg (n2w 1));
      // r2 = conf7
      Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0));
      // r7 = conf7 = 0
      Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7));
      // r6 = (LENGTH conf = 8) ∧ conf7 = 0
      Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1));
      // r1 -> conf6::conf5...conf0
      LoadMEMByte ((n2w 2),Reg (n2w 1));
      // r2 = conf6
      Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0));
      // r7 = conf6 = 0
      Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7));
      // r6 = (LENGTH conf = 8) ∧ conf{7..6} = 0
      Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1));
      // r1 -> conf5::conf4...conf0
      LoadMEMByte ((n2w 2),Reg (n2w 1));
      // r2 = conf5
      Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0));
      // r7 = conf5 = 0
      Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7));
      // r6 = (LENGTH conf = 8) ∧ conf{7..5} = 0
      Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1));
      // r1 -> conf4::conf3...conf0
      LoadMEMByte ((n2w 2),Reg (n2w 1));
      // r2 = conf4
      Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0));
      // r7 = conf4 = 0
      Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7));
      // r6 = (LENGTH conf = 8) ∧ conf{7..4} = 0
      Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1));
      // r1 -> conf3::conf2...conf0
      LoadMEMByte ((n2w 2),Reg (n2w 1));
      // r2 = conf3
      Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0));
      // r7 = conf3 = 0
      Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7));
      // r6 = (LENGTH conf = 8) ∧ conf{7..3} = 0
      Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1));
      // r1 -> conf2::conf1::conf0
      LoadMEMByte ((n2w 2),Reg (n2w 1));
      // r2 = conf2
      Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0));
      // r7 = conf2 = 0
      Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7));
      // r6 = (LENGTH conf = 8) ∧ conf{7..2} = 0
      Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1));
      // r1 -> conf1::conf0
      LoadMEMByte ((n2w 2),Reg (n2w 1));
      // r2 = conf1
      Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0));
      // r7 = conf1 = 0
      Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7));
      // r6 = (LENGTH conf = 8) ∧ conf{7..1} = 0
      Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1));
      // r1 -> conf0
      LoadMEMByte ((n2w 2),Reg (n2w 1));
      // r2 = conf0
      Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0));
      // r7 = conf0 = 0
      Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7))]
   // r6 = (LENGTH conf = 8) ∧ w82n conf = 0`;;

let ag32_ffi_read_load_lengths_code_def = new_definition
  `ag32_ffi_read_load_lengths_code = [
      // r3 -> n1::n0::...
      LoadMEMByte ((n2w 1),Reg (n2w 3));
      // r1 = [0w; 0w; 0w; n1]
      asm_Shift (shiftLL,(n2w 1),Reg (n2w 1),Imm (n2w 8));
      // r1 = [0w; 0w; n1; 0w]
      Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1));
      // r3 -> n0::...
      LoadMEMByte ((n2w 8),Reg (n2w 3));
      // r8 = [0w; 0w; 0w; n0]
      Normal (fXor,(n2w 1),Reg (n2w 1),Reg (n2w 8));
      // r1 = [0w; 0w; n1; n0] (= w22n [n1; n0])
      Normal (fDec,(n2w 3),Reg (n2w 3),Imm (n2w 1));
      // r3 -> n1::n0::...
      LoadConstant ((n2w 8),F,n2w (stdin_offset));
      // r8 = stdin_offset
      LoadMEM ((n2w 5),Reg (n2w 8));
      // r5 = off
      Normal (fAdd,(n2w 8),Reg (n2w 8),Imm (n2w 4));
      // r8 = stdin_offset + 4
      LoadMEM ((n2w 7),Reg (n2w 8));
      // r7 = LENGTH content
      Normal (fSub,(n2w 7),Reg (n2w 7),Reg (n2w 5))]
   // r7 = LENGTH content - off`;;

let ag32_ffi_read_check_length_code_def = new_definition
  `ag32_ffi_read_check_length_code = [
      Normal (fLower,(n2w 8),Reg (n2w 4),Reg (n2w 1));
      // r8 = LENGTH tll < w22n [n1; n0]
      Normal (fSub,(n2w 8),Imm (n2w 1),Reg (n2w 8));
      // r8 = ¬(LENGTH tll < w22n [n1; n0]
      Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 8));
      // r6 = (LENGTH conf = 8) ∧ w82n conf < 3 ∧
      // w22n [n1; n0] ≤ LENGTH tll
      LoadConstant ((n2w 4),F,(n2w 4) * (n2w 26));
      JumpIfZero (fAnd,Reg (n2w 4),Reg (n2w 6),Reg (n2w 8))]`;;

let ag32_ffi_read_num_written_code_def = new_definition
  `ag32_ffi_read_num_written_code = [
      StoreMEMByte (Imm (n2w 0),Reg (n2w 3));
      // r3 -> 0w::n0::pad1::pad2::tll
      Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1));
      // r3 -> n0::pad1::pad2::tll
      LoadConstant ((n2w 8),F,n2w (output_buffer_size + 1));
      // r8 = output_buffer_size+1
      JumpIfZero (fLess,Imm (n2w 8),Reg (n2w 8),Reg (n2w 1));
      // skip if ¬(output_buffer_size+1 < w22n [n1; n0])
      Normal (fSnd,(n2w 1),Reg (n2w 1),Reg (n2w 8));
      // r1 = MIN (output_buffer_size+1) n
      JumpIfZero (fLess,Imm (n2w 8),Reg (n2w 7),Reg (n2w 1));
      // skip if ¬(LENGTH content - off < MIN (output_buffer_size+1) n)
      Normal (fSnd,(n2w 1),Reg (n2w 1),Reg (n2w 7));
      // r1 = MIN n (MIN (LENGTH content - off) (output_buffer_size+1))
      asm_Shift (shiftLR,(n2w 8),Reg (n2w 1),Imm (n2w 8));
      // r8 = r1 DIV 256
      StoreMEMByte (Reg (n2w 8),Reg (n2w 3));
      // r3 -> k1::pad1::pad2::tll
      Normal (fInc,(n2w 4),Reg (n2w 3),Imm (n2w 1));
      // r4 -> pad1::pad2::tll
      StoreMEMByte (Reg (n2w 1),Reg (n2w 4));
      // r4 -> k0::pad2::tll
      Normal (fAdd,(n2w 8),Reg (n2w 5),Reg (n2w 1));
      // r8 = off + k
      LoadConstant ((n2w 2),F,n2w stdin_offset);
      // r2 = stdin_offset
      StoreMEM (Reg (n2w 8),Reg (n2w 2));
      // stdin pointer updated
      Normal (fAdd,(n2w 2),Reg (n2w 2),Imm (n2w 8));
      // r2 -> stdin
      Normal (fAdd,(n2w 3),Reg (n2w 2),Reg (n2w 5));
      // r3 -> DROP off stdin
      Normal (fAdd,(n2w 5),Reg (n2w 4),Imm (n2w 2));
      // r5 -> tll
      LoadConstant ((n2w 2),F,(n2w 4) * (n2w 8))]`;;
(* r2 = 4*8 *)

let ag32_ffi_read_code_def = new_definition
  `ag32_ffi_read_code = APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND
  ag32_ffi_read_set_id_code
      ag32_ffi_read_check_conf_code)
      ag32_ffi_read_load_lengths_code)
      ag32_ffi_read_check_length_code)
      ag32_ffi_read_num_written_code)
      ag32_ffi_copy_code)
      [StoreMEMByte (Imm (n2w 1),Reg (n2w 3))])
      ag32_ffi_return_code`;;

let ag32_ffi_read_set_id_def = new_definition
  `ag32_ffi_read_set_id s =
     let s = dfn'LoadConstant ((n2w 5),F,n2w (ffi_code_start_offset - 1)) s
       in
     let s = dfn'StoreMEMByte (Imm (n2w (THE (ALOOKUP FFI_codes (implode
       "read")))),Reg (n2w 5)) s in
     s`;;

let ag32_ffi_read_set_id_thm = prove
 (`(ag32_ffi_read_set_id s = ?_MEM_fupd (K (((n2w (ffi_code_start_offset - 1))
  =+ n2w (THE (ALOOKUP FFI_codes (implode "read")))) (?_MEM s))) (?_R_fupd (K
  (((n2w 5) =+ n2w (ffi_code_start_offset - 1)) (?_R s))) (?_PC_fupd (K (?_PC s
  + (n2w 8)))
    s)))`,
  CHEAT_TAC);;

let ag32_ffi_read_check_conf_def = new_definition
  `ag32_ffi_read_check_conf s =
    let s = dfn'Normal (fEqual,(n2w 6),Reg (n2w 2),Imm (n2w 8)) s in
    let s = dfn'Normal (fSub,(n2w 4),Reg (n2w 4),Imm (n2w 4)) s in
    let s = dfn'LoadMEMByte ((n2w 2),Reg (n2w 1)) s in
    let s = dfn'Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0)) s in
    let s = dfn'Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7)) s in
    let s = dfn'Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1)) s in
    let s = dfn'LoadMEMByte ((n2w 2),Reg (n2w 1)) s in
    let s = dfn'Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0)) s in
    let s = dfn'Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7)) s in
    let s = dfn'Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1)) s in
    let s = dfn'LoadMEMByte ((n2w 2),Reg (n2w 1)) s in
    let s = dfn'Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0)) s in
    let s = dfn'Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7)) s in
    let s = dfn'Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1)) s in
    let s = dfn'LoadMEMByte ((n2w 2),Reg (n2w 1)) s in
    let s = dfn'Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0)) s in
    let s = dfn'Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7)) s in
    let s = dfn'Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1)) s in
    let s = dfn'LoadMEMByte ((n2w 2),Reg (n2w 1)) s in
    let s = dfn'Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0)) s in
    let s = dfn'Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7)) s in
    let s = dfn'Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1)) s in
    let s = dfn'LoadMEMByte ((n2w 2),Reg (n2w 1)) s in
    let s = dfn'Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0)) s in
    let s = dfn'Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7)) s in
    let s = dfn'Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1)) s in
    let s = dfn'LoadMEMByte ((n2w 2),Reg (n2w 1)) s in
    let s = dfn'Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0)) s in
    let s = dfn'Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7)) s in
    let s = dfn'Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1)) s in
    let s = dfn'LoadMEMByte ((n2w 2),Reg (n2w 1)) s in
    let s = dfn'Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0)) s in
    let s = dfn'Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7)) s in s`;;

let ag32_ffi_read_check_conf_thm = prove
 (`bytes_in_memory (?_R s (n2w 1)) conf (?_MEM s) md /\ (w2n (?_R s (n2w 2)) =
  LENGTH conf) ==>
   (?ov cf r1 r2 r7.
   (ag32_ffi_read_check_conf s = ?_CarryFlag_fupd (K cf)
     (?_OverflowFlag_fupd (K ov) (?_PC_fupd (K (?_PC s + n2w (4 * LENGTH
     ag32_ffi_read_check_conf_code))) (?_R_fupd (K (((n2w 6) =+ v2w [(LENGTH
     conf = 8) /\ (w82n conf = 0)])
                   (((n2w 2) =+ (if (LENGTH conf = 8) /\ (w82n conf = 0)
                     then n2w (w82n conf) else r2))
                   (((n2w 4) =+ (?_R s (n2w 4) - (n2w 4)))
                   (((n2w 1) =+ r1)
                   (((n2w 7) =+ r7) (?_R s)))))))
    s)))))`,
  CHEAT_TAC);;

let ag32_ffi_read_load_lengths_def = new_definition
  `ag32_ffi_read_load_lengths s =
   let s = dfn'LoadMEMByte ((n2w 1),Reg (n2w 3)) s in
   let s = dfn'Shift (shiftLL,(n2w 1),Reg (n2w 1),Imm (n2w 8)) s in
   let s = dfn'Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1)) s in
   let s = dfn'LoadMEMByte ((n2w 8),Reg (n2w 3)) s in
   let s = dfn'Normal (fXor,(n2w 1),Reg (n2w 1),Reg (n2w 8)) s in
   let s = dfn'Normal (fDec,(n2w 3),Reg (n2w 3),Imm (n2w 1)) s in
   let s = dfn'LoadConstant ((n2w 8),F,n2w (stdin_offset)) s in
   let s = dfn'LoadMEM ((n2w 5),Reg (n2w 8)) s in
   let s = dfn'Normal (fAdd,(n2w 8),Reg (n2w 8),Imm (n2w 4)) s in
   let s = dfn'LoadMEM ((n2w 7),Reg (n2w 8)) s in
   let s = dfn'Normal (fSub,(n2w 7),Reg (n2w 7),Reg (n2w 5)) s in
   s`;;

let ag32_ffi_read_load_lengths_thm = prove
 (`bytes_in_memory (?_R s (n2w 3)) [n1; n0] (?_MEM s) md /\
   (get_mem_word (?_MEM s) (n2w stdin_offset) = n2w off) /\
   (get_mem_word (?_MEM s) (n2w (stdin_offset + 4)) = n2w len) /\ off <= len
     /\ len <= stdin_size ==>
   (?ov cf r8.
   (ag32_ffi_read_load_lengths s = ?_CarryFlag_fupd (K cf)
     (?_OverflowFlag_fupd (K ov) (?_PC_fupd (K (?_PC s + n2w (4 * LENGTH
     ag32_ffi_read_load_lengths_code))) (?_R_fupd (K (((n2w 8) =+ r8)
                   (((n2w 5) =+ n2w (off))
                   (((n2w 7) =+ n2w (len - off))
                   (((n2w 1) =+ n2w (w22n [n1; n0])) (?_R s))))))
    s)))))`,
  CHEAT_TAC);;

let ag32_ffi_read_check_length_def = new_definition
  `ag32_ffi_read_check_length s =
    let s = dfn'Normal (fLower,(n2w 8),Reg (n2w 4),Reg (n2w 1)) s in
    let s = dfn'Normal (fSub,(n2w 8),Imm (n2w 1),Reg (n2w 8)) s in
    let s = dfn'Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 8)) s in
    let s = dfn'LoadConstant ((n2w 4),F,(n2w 4) * (n2w 26)) s in
    let s = dfn'JumpIfZero (fAnd,Reg (n2w 4),Reg (n2w 6),Reg (n2w 8)) s in
    s`;;

let ag32_ffi_read_check_length_thm = prove
 (`(?_R s (n2w 1) = n2w n) /\ (?_R s (n2w 4) = n2w ltll) /\
   (?_R s (n2w 6) = v2w [cnd]) /\ ltll < dimword (:32) /\ n < dimword (:32)
     ==>
   (?r4 r6 r8 cf ov.
   (ag32_ffi_read_check_length s = ?_OverflowFlag_fupd (K ov)
     (?_CarryFlag_fupd (K cf) (?_R_fupd (K (((n2w 8) =+ r8)
                   (((n2w 6) =+ r6)
                   (((n2w 4) =+ r4) (?_R s))))) (?_PC_fupd (K (if cnd /\ n
                     <= ltll then ?_PC s + n2w (4 * LENGTH
                     ag32_ffi_read_check_length_code)
                    else ?_PC s + n2w (4 * (LENGTH
                      ag32_ffi_read_check_length_code + 25))))
    s)))))`,
  CHEAT_TAC);;

let ag32_ffi_read_num_written_def = new_definition
  `ag32_ffi_read_num_written s =
    let s = dfn'StoreMEMByte (Imm (n2w 0),Reg (n2w 3)) s in
    let s = dfn'Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1)) s in
    let s0 = dfn'LoadConstant ((n2w 8),F,n2w (output_buffer_size + 1)) s in
    let s = dfn'JumpIfZero (fLess,Imm (n2w 8),Reg (n2w 8),Reg (n2w 1)) s0 in
    let s0 = (if ?_PC s = ?_PC s0 + (n2w 4) then dfn'Normal (fSnd,(n2w
      1),Reg (n2w 1),Reg (n2w 8)) s else s) in
    let s = dfn'JumpIfZero (fLess,Imm (n2w 8),Reg (n2w 7),Reg (n2w 1)) s0 in
    let s = (if ?_PC s = ?_PC s0 + (n2w 4) then dfn'Normal (fSnd,(n2w 1),Reg
      (n2w 1),Reg (n2w 7)) s else s) in
    let s = dfn'Shift (shiftLR,(n2w 8),Reg (n2w 1),Imm (n2w 8)) s in
    let s = dfn'StoreMEMByte (Reg (n2w 8),Reg (n2w 3)) s in
    let s = dfn'Normal (fInc,(n2w 4),Reg (n2w 3),Imm (n2w 1)) s in
    let s = dfn'StoreMEMByte (Reg (n2w 1),Reg (n2w 4)) s in
    let s = dfn'Normal (fAdd,(n2w 8),Reg (n2w 5),Reg (n2w 1)) s in
    let s = dfn'LoadConstant ((n2w 2),F,n2w stdin_offset) s in
    let s = dfn'StoreMEM (Reg (n2w 8),Reg (n2w 2)) s in
    let s = dfn'Normal (fAdd,(n2w 2),Reg (n2w 2),Imm (n2w 8)) s in
    let s = dfn'Normal (fAdd,(n2w 3),Reg (n2w 2),Reg (n2w 5)) s in
    let s = dfn'Normal (fAdd,(n2w 5),Reg (n2w 4),Imm (n2w 2)) s in
    let s = dfn'LoadConstant ((n2w 2),F,(n2w 4) * (n2w 8)) s in
    s`;;

let ag32_ffi_read_num_written_thm = prove
 (`bytes_in_memory (?_R s (n2w 3)) (CONS n1 (CONS n0 (CONS pad1 (CONS pad2
  tll)))) (?_MEM s) md /\
   (?_R s (n2w 1) = n2w n) /\
   (?_R s (n2w 5) = n2w off) /\
   (?_R s (n2w 7) = n2w lcmo) /\
   (k = MIN n (MIN lcmo (output_buffer_size + 1))) /\ n < dimword (:31)
     /\ lcmo < dimword (:31) ==>
   (?r8 r4 cf ov.
   (ag32_ffi_read_num_written s = ?_OverflowFlag_fupd (K ov)
     (?_CarryFlag_fupd (K cf) (?_R_fupd (K (((n2w 8) =+ r8)
                   (((n2w 4) =+ r4)
                   (((n2w 3) =+ n2w (stdin_offset + 8 + off))
                   (((n2w 5) =+ (?_R s (n2w 3) + (n2w 4)))
                   (((n2w 2) =+ ((n2w 4) * (n2w 8)))
                   (((n2w 1) =+ n2w k) (?_R s)))))))) (?_MEM_fupd (K
                     (set_mem_word (n2w stdin_offset) (n2w (off + k))
                       (asm_write_bytearray (?_R s (n2w 3)) (CONS (n2w 0)
                         (n2w2 k)) (?_MEM s)))) (?_PC_fupd (K (?_PC s + n2w (4
                         * LENGTH ag32_ffi_read_num_written_code)))
    s))))))`,
  CHEAT_TAC);;

let ag32_ffi_read_def = new_definition
  `ag32_ffi_read s =
   let s = ag32_ffi_read_set_id s in
   let s = ag32_ffi_read_check_conf s in
   let s0 = ag32_ffi_read_load_lengths s in
   let s = ag32_ffi_read_check_length s0 in
   let s =
     (if ?_PC s = ?_PC s0 + n2w (4 * LENGTH ag32_ffi_read_check_length_code)
       then
       let s = ag32_ffi_read_num_written s in
       let s = ag32_ffi_copy s in s
     else dfn'StoreMEMByte (Imm (n2w 1),Reg (n2w 3)) s) in
     ag32_ffi_return s`;;

(* write
   PC is ffi_code_start_offset + ag32_ffi_write_entrypoint
   r1 contains pointer to byte array (conf) with the output id
   r2 contains length of r1 (should be 8)
   r3 contains pointer to byte array n1::n0::off1::off0::tll
   r4 contains LENGTH tll + 4
   postconditions:
     * written (THE (ALOOKUP FFI_codes «write»)) at (n2w (ffi_code_start_offset - 1))
     * if the following conditions hold
         - r2 contains 8
         - w82n conf ≤ 2
         - w22n [off1; off0] ≤ LENGTH tll
         - w22n [n1; n0] ≤ LENGTH tll - w22n [off1; off0]
       then
         - write 0w::n2w2(k) to array pointed by r3
         - write conf ++ [0w;0w;n1;n0] ++ (TAKE k (DROP (w22n [off1; off0]) tll))
           to n2w output_offset
         where k = MIN (w22n [n1; n0]) output_buffer_size
       else
         - write 1w to the first byte pointed by r3
         - do not touch anything else in memory
     * r1,..,r8 are set to 0 and carry and overflow unset
     * exit happens at the end of the code, by jumping to r0
*)

let ag32_ffi_write_entrypoint_def = new_definition
  `ag32_ffi_write_entrypoint =
   ag32_ffi_read_entrypoint + 4 * LENGTH ag32_ffi_read_code`;;

let ag32_ffi_write_set_id_code_def = new_definition
  `ag32_ffi_write_set_id_code =
     [lab_Jump (fAdd,(n2w 5),Imm (n2w 4));
      LoadConstant ((n2w 6),F,n2w (ag32_ffi_write_entrypoint + 4));
      Normal (fSub,(n2w 5),Reg (n2w 5),Reg (n2w 6));
      // r5 = ffi_code_start_offset
      Normal (fDec,(n2w 5),Reg (n2w 5),Imm (n2w 0));
      StoreMEMByte (Imm (n2w (THE (ALOOKUP FFI_codes (implode
        "write")))),Reg (n2w 5))]`;;

let ag32_ffi_write_check_conf_code_def = new_definition
  `ag32_ffi_write_check_conf_code = [
      Normal (fEqual,(n2w 6),Reg (n2w 2),Imm (n2w 8));
      // r6 = (LENGTH conf = 8)
      Normal (fSub,(n2w 4),Reg (n2w 4),Imm (n2w 4));
      // r4 = LENGTH tll
      LoadMEMByte ((n2w 2),Reg (n2w 1));
      // r2 = conf7
      Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0));
      // r7 = conf7 = 0
      Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7));
      // r6 = (LENGTH conf = 8) ∧ conf7 = 0
      Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1));
      // r1 -> conf6::conf5...conf0
      LoadMEMByte ((n2w 2),Reg (n2w 1));
      // r2 = conf6
      Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0));
      // r7 = conf6 = 0
      Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7));
      // r6 = (LENGTH conf = 8) ∧ conf{7..6} = 0
      Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1));
      // r1 -> conf5::conf4...conf0
      LoadMEMByte ((n2w 2),Reg (n2w 1));
      // r2 = conf5
      Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0));
      // r7 = conf5 = 0
      Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7));
      // r6 = (LENGTH conf = 8) ∧ conf{7..5} = 0
      Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1));
      // r1 -> conf4::conf3...conf0
      LoadMEMByte ((n2w 2),Reg (n2w 1));
      // r2 = conf4
      Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0));
      // r7 = conf4 = 0
      Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7));
      // r6 = (LENGTH conf = 8) ∧ conf{7..4} = 0
      Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1));
      // r1 -> conf3::conf2...conf0
      LoadMEMByte ((n2w 2),Reg (n2w 1));
      // r2 = conf3
      Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0));
      // r7 = conf3 = 0
      Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7));
      // r6 = (LENGTH conf = 8) ∧ conf{7..3} = 0
      Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1));
      // r1 -> conf2::conf1::conf0
      LoadMEMByte ((n2w 2),Reg (n2w 1));
      // r2 = conf2
      Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0));
      // r7 = conf2 = 0
      Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7));
      // r6 = (LENGTH conf = 8) ∧ conf{7..2} = 0
      Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1));
      // r1 -> conf1::conf0
      LoadMEMByte ((n2w 2),Reg (n2w 1));
      // r2 = conf1
      Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0));
      // r7 = conf1 = 0
      Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7));
      // r6 = (LENGTH conf = 8) ∧ conf{7..1} = 0
      Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1));
      // r1 -> conf0
      LoadMEMByte ((n2w 2),Reg (n2w 1));
      // r2 = conf0
      Normal (fLess,(n2w 7),Reg (n2w 2),Imm (n2w 3));
      // r7 = conf0 < 3
      Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7));
      // r6 = (LENGTH conf = 8) ∧ w82n conf < 3
      Normal (fLess,(n2w 7),Imm (n2w 0),Reg (n2w 2));
      // r7 = 0 < conf0
      Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7))]
   // r6 = (LENGTH conf = 8) ∧ 0 < w82n conf < 3`;;

let ag32_ffi_write_load_noff_code_def = new_definition
  `ag32_ffi_write_load_noff_code = [
      // r3 -> n1::n0::off1::off0::...
      LoadMEMByte ((n2w 1),Reg (n2w 3));
      // r1 = [0w; 0w; 0w; n1]
      asm_Shift (shiftLL,(n2w 1),Reg (n2w 1),Imm (n2w 8));
      // r1 = [0w; 0w; n1; 0w]
      Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1));
      // r3 -> n0::off1::off0::...
      LoadMEMByte ((n2w 8),Reg (n2w 3));
      // r8 = [0w; 0w; 0w; n0]
      Normal (fXor,(n2w 1),Reg (n2w 1),Reg (n2w 8));
      // r1 = [0w; 0w; n1; n0] (= w22n [n1; n0])
      Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1));
      // r3 -> off1::off0::...
      LoadMEMByte ((n2w 7),Reg (n2w 3));
      // r7 = [0w; 0w; 0w; off1]
      asm_Shift (shiftLL,(n2w 7),Reg (n2w 7),Imm (n2w 8));
      // r7 = [0w; 0w; off1; 0w]
      Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1));
      // r3 -> off0::...
      LoadMEMByte ((n2w 8),Reg (n2w 3));
      // r8 = [0w; 0w; 0w; off0]
      Normal (fXor,(n2w 7),Reg (n2w 7),Reg (n2w 8));
      // r7 = [0w; 0w; off1; off0] (= w22n [off1; off0])
      Normal (fSub,(n2w 3),Reg (n2w 3),Imm (n2w 3))]`;;

let ag32_ffi_write_check_lengths_code_def = new_definition
  `ag32_ffi_write_check_lengths_code = [
      Normal (fLower,(n2w 8),Reg (n2w 4),Reg (n2w 7));
      // r8 = LENGTH tll < w22n [off1; off0]
      Normal (fSub,(n2w 8),Imm (n2w 1),Reg (n2w 8));
      // r8 = ¬(LENGTH tll < w22n [off1; off0]
      Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 8));
      // r6 = (LENGTH conf = 8) ∧ w82n conf < 3 ∧
      // w22n [off1; off0] ≤ LENGTH tll
      Normal (fSub,(n2w 4),Reg (n2w 4),Reg (n2w 7));
      // r4 = LENGTH tll - w22n [off1; off0]
      Normal (fLower,(n2w 8),Reg (n2w 4),Reg (n2w 1));
      // r8 = LENGTH tll - w22n [off1; off0] < w22n [n1; n0]
      Normal (fSub,(n2w 8),Imm (n2w 1),Reg (n2w 8));
      // r8 = ¬(LENGTH tll - w22n [off1; off0] < w22n [n1; n0]
      LoadConstant ((n2w 4),F,n2w ((ffi_code_start_offset - 1) -
        output_offset));
      Normal (fSub,(n2w 5),Reg (n2w 5),Reg (n2w 4));
      // r5 = output_offset
      LoadConstant ((n2w 4),F,(n2w 4) * (n2w 34));
      JumpIfZero (fAnd,Reg (n2w 4),Reg (n2w 6),Reg (n2w 8))]`;;

let ag32_ffi_write_write_header_code_def = new_definition
  `ag32_ffi_write_write_header_code = [
      StoreMEM (Imm (n2w 0),Reg (n2w 5));
      Normal (fAdd,(n2w 5),Reg (n2w 5),Imm (n2w 4));
      // r5 = output_offset + 4
      asm_Shift (shiftLL,(n2w 2),Reg (n2w 2),Imm (n2w 24));
      // r2 = [conf0; 0w; 0w; 0w]
      StoreMEM (Reg (n2w 2),Reg (n2w 5));
      Normal (fAdd,(n2w 5),Reg (n2w 5),Imm (n2w 4));
      // r5 = output_offset + 8
      StoreMEMByte (Imm (n2w 0),Reg (n2w 5));
      Normal (fInc,(n2w 5),Reg (n2w 5),Imm (n2w 1));
      // r5 = output_offset + 9
      StoreMEMByte (Imm (n2w 0),Reg (n2w 5));
      Normal (fInc,(n2w 5),Reg (n2w 5),Imm (n2w 1));
      // r5 = output_offset + 10
      asm_Shift (shiftLR,(n2w 2),Reg (n2w 1),Imm (n2w 8));
      // r2 = [0w; 0w; 0w; n1]
      StoreMEMByte (Reg (n2w 2),Reg (n2w 5));
      Normal (fInc,(n2w 5),Reg (n2w 5),Imm (n2w 1));
      // r5 = output_offset + 11
      StoreMEMByte (Reg (n2w 1),Reg (n2w 5));
      Normal (fInc,(n2w 5),Reg (n2w 5),Imm (n2w 1));
      // r5 = output_offset + 12
      StoreMEMByte (Imm (n2w 0),Reg (n2w 3))]`;;

let ag32_ffi_write_num_written_code_def = new_definition
  `ag32_ffi_write_num_written_code = [
      // calculate k and write to mutable array
      Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1));
      // r3 -> n0::off1::off0::tll
      LoadConstant ((n2w 8),F,n2w output_buffer_size);
      // r8 = output_buffer_size
      JumpIfZero (fLess,Imm (n2w 8),Reg (n2w 8),Reg (n2w 1));
      // skip if ¬(output_buffer_size < w22n [n1; n0])
      Normal (fSnd,(n2w 1),Reg (n2w 1),Reg (n2w 8));
      // r1 = MIN output_buffer_size (w22n [n1; n0])
      asm_Shift (shiftLR,(n2w 8),Reg (n2w 1),Imm (n2w 8));
      // r8 = r1 DIV 256
      StoreMEMByte (Reg (n2w 8),Reg (n2w 3));
      Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1));
      // r3 -> off1::off0::tll
      StoreMEMByte (Reg (n2w 1),Reg (n2w 3));
      Normal (fAdd,(n2w 3),Reg (n2w 3),Imm (n2w 2));
      Normal (fAdd,(n2w 3),Reg (n2w 3),Reg (n2w 7));
      // r3 -> DROP off tll
      LoadConstant ((n2w 2),F,(n2w 4) * (n2w 9))]`;;

let ag32_ffi_write_code_def = new_definition
  `ag32_ffi_write_code = APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND
  (APPEND ag32_ffi_write_set_id_code
      ag32_ffi_write_check_conf_code)
      ag32_ffi_write_load_noff_code)
      ag32_ffi_write_check_lengths_code)
      ag32_ffi_write_write_header_code)
      ag32_ffi_write_num_written_code)
      ag32_ffi_copy_code)
      [
       // error case
       StoreMEMByte (Imm (n2w 1),Reg (n2w 3));
       StoreMEMByte (Imm (n2w 1),Reg (n2w 5))])
      ag32_ffi_return_code`;;

let ag32_ffi_write_set_id_def = new_definition
  `ag32_ffi_write_set_id s =
     let s = dfn'Jump (fAdd,(n2w 5),Imm (n2w 4)) s in
     let s = dfn'LoadConstant ((n2w 6),F,n2w (ag32_ffi_write_entrypoint +
       4)) s in
     let s = dfn'Normal (fSub,(n2w 5),Reg (n2w 5),Reg (n2w 6)) s in
     let s = dfn'Normal (fDec,(n2w 5),Reg (n2w 5),Imm (n2w 0)) s in
     let s = dfn'StoreMEMByte (Imm (n2w (THE (ALOOKUP FFI_codes (implode
       "write")))),Reg (n2w 5)) s in
     s`;;

let ag32_ffi_write_set_id_thm = prove
 (`(?_PC s = n2w (ffi_code_start_offset + ag32_ffi_write_entrypoint)) ==>
    (?cf ov r6.
     (ag32_ffi_write_set_id s = ?_MEM_fupd (K (((n2w (ffi_code_start_offset
       - 1)) =+ n2w (THE (ALOOKUP FFI_codes (implode "write")))) (?_MEM s)))
       (?_OverflowFlag_fupd (K ov) (?_CarryFlag_fupd (K cf) (?_R_fupd (K (((n2w
       6) =+ r6) (((n2w 5) =+ (n2w (ffi_code_start_offset - 1))) (?_R s))))
       (?_PC_fupd (K (?_PC s + n2w (4 * LENGTH ag32_ffi_write_set_id_code)))
      s))))))`,
  CHEAT_TAC);;

let ag32_ffi_write_check_conf_def = new_definition
  `ag32_ffi_write_check_conf s =
    let s = dfn'Normal (fEqual,(n2w 6),Reg (n2w 2),Imm (n2w 8)) s in
    let s = dfn'Normal (fSub,(n2w 4),Reg (n2w 4),Imm (n2w 4)) s in
    let s = dfn'LoadMEMByte ((n2w 2),Reg (n2w 1)) s in
    let s = dfn'Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0)) s in
    let s = dfn'Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7)) s in
    let s = dfn'Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1)) s in
    let s = dfn'LoadMEMByte ((n2w 2),Reg (n2w 1)) s in
    let s = dfn'Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0)) s in
    let s = dfn'Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7)) s in
    let s = dfn'Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1)) s in
    let s = dfn'LoadMEMByte ((n2w 2),Reg (n2w 1)) s in
    let s = dfn'Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0)) s in
    let s = dfn'Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7)) s in
    let s = dfn'Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1)) s in
    let s = dfn'LoadMEMByte ((n2w 2),Reg (n2w 1)) s in
    let s = dfn'Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0)) s in
    let s = dfn'Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7)) s in
    let s = dfn'Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1)) s in
    let s = dfn'LoadMEMByte ((n2w 2),Reg (n2w 1)) s in
    let s = dfn'Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0)) s in
    let s = dfn'Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7)) s in
    let s = dfn'Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1)) s in
    let s = dfn'LoadMEMByte ((n2w 2),Reg (n2w 1)) s in
    let s = dfn'Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0)) s in
    let s = dfn'Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7)) s in
    let s = dfn'Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1)) s in
    let s = dfn'LoadMEMByte ((n2w 2),Reg (n2w 1)) s in
    let s = dfn'Normal (fEqual,(n2w 7),Reg (n2w 2),Imm (n2w 0)) s in
    let s = dfn'Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7)) s in
    let s = dfn'Normal (fInc,(n2w 1),Reg (n2w 1),Imm (n2w 1)) s in
    let s = dfn'LoadMEMByte ((n2w 2),Reg (n2w 1)) s in
    let s = dfn'Normal (fLess,(n2w 7),Reg (n2w 2),Imm (n2w 3)) s in
    let s = dfn'Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7)) s in
    let s = dfn'Normal (fLess,(n2w 7),Imm (n2w 0),Reg (n2w 2)) s in
    let s = dfn'Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 7)) s in
    s`;;

let ag32_ffi_write_check_conf_thm = prove
 (`bytes_in_memory (?_R s (n2w 1)) conf (?_MEM s) md /\ (w2n (?_R s (n2w 2)) =
  LENGTH conf) ==>
   (?ov cf r1 r2 r7.
   (ag32_ffi_write_check_conf s = ?_CarryFlag_fupd (K cf)
     (?_OverflowFlag_fupd (K ov) (?_PC_fupd (K (?_PC s + n2w (4 * LENGTH
     ag32_ffi_write_check_conf_code))) (?_R_fupd (K (((n2w 6) =+ v2w [(LENGTH
     conf = 8) /\ w82n conf < 3 /\ 0 < w82n conf])
                   (((n2w 2) =+ (if (LENGTH conf = 8) /\ w82n conf < 3 /\ 0
                     < w82n conf then n2w (w82n conf) else r2))
                   (((n2w 4) =+ (?_R s (n2w 4) - (n2w 4)))
                   (((n2w 1) =+ r1)
                   (((n2w 7) =+ r7) (?_R s)))))))
    s)))))`,
  CHEAT_TAC);;

let ag32_ffi_write_check_conf_MEM = prove
 (`?_MEM
      (ag32_ffi_write_check_conf s) = ?_MEM s`,
  CHEAT_TAC);;

let ag32_ffi_write_check_conf_PC = prove
 (`?_PC
      (ag32_ffi_write_check_conf s) = ?_PC s + (n2w 140)`,
  CHEAT_TAC);;

let ag32_ffi_write_check_conf_R = prove
 (`(?_R (ag32_ffi_write_check_conf s) (n2w 3) = ?_R s (n2w 3)) /\
   (?_R (ag32_ffi_write_check_conf s) (n2w 5) = ?_R s (n2w 5))`,
  CHEAT_TAC);;

let ag32_ffi_write_load_noff_def = new_definition
  `ag32_ffi_write_load_noff s =
   let s = dfn'LoadMEMByte ((n2w 1),Reg (n2w 3)) s in
   let s = dfn'Shift (shiftLL,(n2w 1),Reg (n2w 1),Imm (n2w 8)) s in
   let s = dfn'Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1)) s in
   let s = dfn'LoadMEMByte ((n2w 8),Reg (n2w 3)) s in
   let s = dfn'Normal (fXor,(n2w 1),Reg (n2w 1),Reg (n2w 8)) s in
   let s = dfn'Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1)) s in
   let s = dfn'LoadMEMByte ((n2w 7),Reg (n2w 3)) s in
   let s = dfn'Shift (shiftLL,(n2w 7),Reg (n2w 7),Imm (n2w 8)) s in
   let s = dfn'Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1)) s in
   let s = dfn'LoadMEMByte ((n2w 8),Reg (n2w 3)) s in
   let s = dfn'Normal (fXor,(n2w 7),Reg (n2w 7),Reg (n2w 8)) s in
   let s = dfn'Normal (fSub,(n2w 3),Reg (n2w 3),Imm (n2w 3)) s in
   s`;;

let ag32_ffi_write_load_noff_thm = prove
 (`bytes_in_memory (?_R s (n2w 3)) (CONS n1 (CONS n0 (CONS off1 (CONS off0
  tll)))) (?_MEM s) md ==>
   (?r8 ov cf.
   (ag32_ffi_write_load_noff s = ?_R_fupd (K (((n2w 8) =+ r8)
                   (((n2w 1) =+ n2w (w22n [n1; n0]))
                   (((n2w 7) =+ n2w (w22n [off1; off0])) (?_R s)))))
                     (?_CarryFlag_fupd (K cf) (?_OverflowFlag_fupd (K ov)
                     (?_PC_fupd (K (?_PC s + n2w (4 * LENGTH
                     ag32_ffi_write_load_noff_code)))
    s)))))`,
  CHEAT_TAC);;

let ag32_ffi_write_load_noff_MEM = prove
 (`?_MEM
      (ag32_ffi_write_load_noff s) = ?_MEM s`,
  CHEAT_TAC);;

let ag32_ffi_write_load_noff_PC = prove
 (`?_PC
      (ag32_ffi_write_load_noff s) = ?_PC s + (n2w 48)`,
  CHEAT_TAC);;

let ag32_ffi_write_load_noff_R = prove
 (`(?_R (ag32_ffi_write_load_noff s) (n2w 3) = ?_R s (n2w 3)) /\
   (?_R (ag32_ffi_write_load_noff s) (n2w 5) = ?_R s (n2w 5))`,
  CHEAT_TAC);;

let ag32_ffi_write_check_lengths_def = new_definition
  `ag32_ffi_write_check_lengths s =
   let s = dfn'Normal (fLower,(n2w 8),Reg (n2w 4),Reg (n2w 7)) s in
   let s = dfn'Normal (fSub,(n2w 8),Imm (n2w 1),Reg (n2w 8)) s in
   let s = dfn'Normal (fAnd,(n2w 6),Reg (n2w 6),Reg (n2w 8)) s in
   let s = dfn'Normal (fSub,(n2w 4),Reg (n2w 4),Reg (n2w 7)) s in
   let s = dfn'Normal (fLower,(n2w 8),Reg (n2w 4),Reg (n2w 1)) s in
   let s = dfn'Normal (fSub,(n2w 8),Imm (n2w 1),Reg (n2w 8)) s in
   let s = dfn'LoadConstant ((n2w 4),F,n2w ((ffi_code_start_offset - 1) -
     output_offset)) s in
   let s = dfn'Normal (fSub,(n2w 5),Reg (n2w 5),Reg (n2w 4)) s in
   let s = dfn'LoadConstant ((n2w 4),F,(n2w 4) * (n2w 34)) s in
   let s = dfn'JumpIfZero (fAnd,Reg (n2w 4),Reg (n2w 6),Reg (n2w 8)) s in
   s`;;

let ag32_ffi_write_check_lengths_thm = prove
 (`(?_R s (n2w 5) = n2w (ffi_code_start_offset - 1)) /\
   (?_R s (n2w 4) = n2w ltll) /\ (?_R s (n2w 7) = n2w off) /\ (?_R s (n2w 1)
     = n2w n) /\ (?_R s (n2w 6) = v2w [cnd]) /\
   off < dimword (:16) /\ n < dimword (:16) /\ ltll < dimword (:32) ==>
   (?r4 r6 r8 cf ov.
   (ag32_ffi_write_check_lengths s = ?_OverflowFlag_fupd (K ov)
     (?_CarryFlag_fupd (K cf) (?_R_fupd (K (((n2w 8) =+ r8)
                   (((n2w 4) =+ r4)
                   (((n2w 5) =+ n2w output_offset)
                   (((n2w 6) =+ r6) (?_R s)))))) (?_PC_fupd (K (if cnd
                     /\ off <= ltll /\ n <= ltll - off then ?_PC s + n2w (4 *
                     LENGTH ag32_ffi_write_check_lengths_code)
                    else ?_PC s + n2w (4 * (LENGTH
                      ag32_ffi_write_check_lengths_code + 33))))
    s)))))`,
  CHEAT_TAC);;

let ag32_ffi_write_check_lengths_MEM = prove
 (`?_MEM
      (ag32_ffi_write_check_lengths s) = ?_MEM s`,
  CHEAT_TAC);;

let ag32_ffi_write_check_lengths_PC = prove
 (`?_PC
      (ag32_ffi_write_check_lengths s) IN
       {?_PC s + n2w (4 * LENGTH ag32_ffi_write_check_lengths_code),?_PC
         s + n2w (4 * (LENGTH ag32_ffi_write_check_lengths_code + 33))}`,
  CHEAT_TAC);;

let ag32_ffi_write_check_lengths_R = prove
 (`(?_R (ag32_ffi_write_check_lengths s) (n2w 3) = ?_R s (n2w 3)) /\
   (?_R (ag32_ffi_write_check_lengths s) (n2w 5) = ?_R s (n2w 5) - n2w
     ((ffi_code_start_offset - 1) - output_offset))`,
  CHEAT_TAC);;

let ag32_ffi_write_write_header_def = new_definition
  `ag32_ffi_write_write_header s =
   let s = dfn'StoreMEM (Imm (n2w 0),Reg (n2w 5)) s in
   let s = dfn'Normal (fAdd,(n2w 5),Reg (n2w 5),Imm (n2w 4)) s in
   let s = dfn'Shift (shiftLL,(n2w 2),Reg (n2w 2),Imm (n2w 24)) s in
   let s = dfn'StoreMEM (Reg (n2w 2),Reg (n2w 5)) s in
   let s = dfn'Normal (fAdd,(n2w 5),Reg (n2w 5),Imm (n2w 4)) s in
   let s = dfn'StoreMEMByte (Imm (n2w 0),Reg (n2w 5)) s in
   let s = dfn'Normal (fInc,(n2w 5),Reg (n2w 5),Imm (n2w 1)) s in
   let s = dfn'StoreMEMByte (Imm (n2w 0),Reg (n2w 5)) s in
   let s = dfn'Normal (fInc,(n2w 5),Reg (n2w 5),Imm (n2w 1)) s in
   let s = dfn'Shift (shiftLR,(n2w 2),Reg (n2w 1),Imm (n2w 8)) s in
   let s = dfn'StoreMEMByte (Reg (n2w 2),Reg (n2w 5)) s in
   let s = dfn'Normal (fInc,(n2w 5),Reg (n2w 5),Imm (n2w 1)) s in
   let s = dfn'StoreMEMByte (Reg (n2w 1),Reg (n2w 5)) s in
   let s = dfn'Normal (fInc,(n2w 5),Reg (n2w 5),Imm (n2w 1)) s in
   let s = dfn'StoreMEMByte (Imm (n2w 0),Reg (n2w 3)) s in
   s`;;

let ag32_ffi_write_write_header_thm = prove
 (`(?_R s (n2w 5) = n2w output_offset) /\
   (LENGTH conf = 8) /\ (w82n conf < 3) /\ (?_R s (n2w 2) = n2w (w82n conf))
     /\
   (?_R s (n2w 1) = n2w (w22n [n1; n0])) /\ (~(?_R s (n2w 3) = n2w
     output_offset)) ==>
   (?r2 ov cf.
   (ag32_ffi_write_write_header s = ?_CarryFlag_fupd (K cf)
     (?_OverflowFlag_fupd (K ov) (?_MEM_fupd (K
                (((?_R s (n2w 3)) =+ (n2w 0))
                 (asm_write_bytearray (n2w output_offset) (APPEND conf [(n2w
                   0); (n2w 0); n1; n0]) (?_MEM s)))) (?_R_fupd (K (((n2w 5) =+
                   n2w (output_offset + 12))
                   (((n2w 2) =+ r2) (?_R s)))) (?_PC_fupd (K (?_PC s + n2w
                     (4 * LENGTH ag32_ffi_write_write_header_code)))
    s))))))`,
  CHEAT_TAC);;

let ag32_ffi_write_write_header_PC = prove
 (`?_PC
      (ag32_ffi_write_write_header s) = ?_PC s + n2w (4 * LENGTH
        ag32_ffi_write_write_header_code)`,
  CHEAT_TAC);;

let ag32_ffi_write_write_header_R = prove
 (`(?_R (ag32_ffi_write_write_header s) (n2w 3) = ?_R s (n2w 3))`,
  CHEAT_TAC);;

let ag32_ffi_write_num_written_def = new_definition
  `ag32_ffi_write_num_written s =
   let s = dfn'Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1)) s in
   let s0 = dfn'LoadConstant ((n2w 8),F,n2w output_buffer_size) s in
   let s = dfn'JumpIfZero (fLess,Imm (n2w 8),Reg (n2w 8),Reg (n2w 1)) s0 in
   let s = (if ?_PC s = ?_PC s0 + (n2w 4) then dfn'Normal (fSnd,(n2w 1),Reg
     (n2w 1),Reg (n2w 8)) s else s) in
   let s = dfn'Shift (shiftLR,(n2w 8),Reg (n2w 1),Imm (n2w 8)) s in
   let s = dfn'StoreMEMByte (Reg (n2w 8),Reg (n2w 3)) s in
   let s = dfn'Normal (fInc,(n2w 3),Reg (n2w 3),Imm (n2w 1)) s in
   let s = dfn'StoreMEMByte (Reg (n2w 1),Reg (n2w 3)) s in
   let s = dfn'Normal (fAdd,(n2w 3),Reg (n2w 3),Imm (n2w 2)) s in
   let s = dfn'Normal (fAdd,(n2w 3),Reg (n2w 3),Reg (n2w 7)) s in
   let s = dfn'LoadConstant ((n2w 2),F,(n2w 4) * (n2w 9)) s in
   s`;;

let ag32_ffi_write_num_written_thm = prove
 (`bytes_in_memory (?_R s (n2w 3)) (CONS (n2w 0) (CONS n0 (CONS off1 (CONS off0
  tll)))) (?_MEM s) md /\
   (?_R s (n2w 1) = n2w n) /\ (k = MIN n output_buffer_size) /\ n < dimword
     (:16) ==>
   (?r8 cf ov.
   (ag32_ffi_write_num_written s = ?_OverflowFlag_fupd (K ov)
     (?_CarryFlag_fupd (K cf) (?_R_fupd (K (((n2w 8) =+ r8)
                   (((n2w 3) =+ (?_R s (n2w 3) + (n2w 4) + ?_R s (n2w 7)))
                   (((n2w 2) =+ ((n2w 4) * (n2w 9)))
                   (((n2w 1) =+ n2w k) (?_R s)))))) (?_MEM_fupd (K
                     (asm_write_bytearray (?_R s (n2w 3)) (CONS (n2w 0) (n2w2
                     k)) (?_MEM s))) (?_PC_fupd (K (?_PC s + n2w (4 * LENGTH
                     ag32_ffi_write_num_written_code)))
    s))))))`,
  CHEAT_TAC);;

let ag32_ffi_write_def = new_definition
  `ag32_ffi_write s =
   let s = ag32_ffi_write_set_id s in
   let s = ag32_ffi_write_check_conf s in
   let s0 = ag32_ffi_write_load_noff s in
   let s = ag32_ffi_write_check_lengths s0 in
   let s =
     (if ?_PC s = ?_PC s0 + n2w (4 * LENGTH
       ag32_ffi_write_check_lengths_code) then
       let s = ag32_ffi_write_write_header s in
       let s = ag32_ffi_write_num_written s in
               ag32_ffi_copy s
     else let s = dfn'StoreMEMByte (Imm (n2w 1),Reg (n2w 3)) s in
               dfn'StoreMEMByte (Imm (n2w 1),Reg (n2w 5)) s) in
                 ag32_ffi_return s`;;

(* returns error code 1 after writing the appropriate ffi *)
let ag32_ffi_fail_def = new_definition
  `ag32_ffi_fail ffiname s =
   let s = dfn'LoadConstant ((n2w 5),F,n2w (ffi_code_start_offset - 1)) s in
   let s = dfn'StoreMEMByte (Imm (n2w (THE (ALOOKUP FFI_codes ffiname))),Reg
     (n2w 5)) s in
   let s = dfn'StoreMEMByte (Imm (n2w 1),Reg (n2w 3)) s in
   s`;;

let ag32_ffi_fail_code_def = new_definition
  `ag32_ffi_fail_code ffiname =
     [LoadConstant ((n2w 5),F,n2w (ffi_code_start_offset - 1));
      StoreMEMByte (Imm (n2w (THE (ALOOKUP FFI_codes ffiname))),Reg (n2w
        5));
      StoreMEMByte (Imm (n2w 1),Reg (n2w 3))]`;;

(* open_in *)
let ag32_ffi_open_in_entrypoint_def = new_definition
  `ag32_ffi_open_in_entrypoint =
   ag32_ffi_write_entrypoint + 4 * LENGTH ag32_ffi_write_code`;;

let ag32_ffi_open_in_def = new_definition
  `ag32_ffi_open_in s =
   let s = ag32_ffi_fail (implode "open_in") s in
   ag32_ffi_return s`;;

let ag32_ffi_open_in_code_def = new_definition
  `ag32_ffi_open_in_code = APPEND (ag32_ffi_fail_code (implode "open_in"))
  ag32_ffi_return_code`;;

(* open_out *)

let ag32_ffi_open_out_entrypoint_def = new_definition
  `ag32_ffi_open_out_entrypoint =
   ag32_ffi_open_in_entrypoint + 4 * LENGTH ag32_ffi_open_in_code`;;

let ag32_ffi_open_out_def = new_definition
  `ag32_ffi_open_out s =
   let s = ag32_ffi_fail (implode "open_out") s in
   ag32_ffi_return s`;;

let ag32_ffi_open_out_code_def = new_definition
  `ag32_ffi_open_out_code = APPEND (ag32_ffi_fail_code (implode "open_out"))
  ag32_ffi_return_code`;;

(* close *)

let ag32_ffi_close_entrypoint_def = new_definition
  `ag32_ffi_close_entrypoint =
   ag32_ffi_open_out_entrypoint + 4 * LENGTH ag32_ffi_open_out_code`;;

let ag32_ffi_close_def = new_definition
  `ag32_ffi_close s =
   let s = ag32_ffi_fail (implode "close") s in
   ag32_ffi_return s`;;

let ag32_ffi_close_code_def = new_definition
  `ag32_ffi_close_code = APPEND (ag32_ffi_fail_code (implode "close"))
  ag32_ffi_return_code`;;

(* FFI jumps
  - get byte array (length,pointer)s in (len_reg,ptr_reg) and (len2_reg,ptr2_reg) (these are r1-r4)
  - get return address in link_reg (r0)
  - PC is ffi_jumps_offset + ffi_offset * index
  conventions on return (see ag32_ffi_interfer_def):
    r0 is the end of this ffi's code (i.e., entrypoint of the next ffi's code)
    r1-r8 are 0w
    overflow and carry are false
*)

let ffi_entrypoints_def = new_definition
  `ffi_entrypoints = [
     ((implode ""),ag32_ffi__entrypoint);
     ((implode "get_arg_count"),ag32_ffi_get_arg_count_entrypoint);
     ((implode "get_arg_length"),ag32_ffi_get_arg_length_entrypoint);
     ((implode "get_arg"),ag32_ffi_get_arg_entrypoint);
     ((implode "read"),ag32_ffi_read_entrypoint);
     ((implode "write"),ag32_ffi_write_entrypoint);
     ((implode "open_in"),ag32_ffi_open_in_entrypoint);
     ((implode "open_out"),ag32_ffi_open_out_entrypoint);
     ((implode "close"),ag32_ffi_close_entrypoint)]
   // («exit», ag32_ffi_exit_entrypoint);`;;

let ffi_exitpcs_def = new_definition
  `ffi_exitpcs = [
     ((implode ""),ffi_code_start_offset +
       ag32_ffi_get_arg_count_entrypoint);
     ((implode "get_arg_count"),ffi_code_start_offset +
       ag32_ffi_get_arg_length_entrypoint);
     ((implode "get_arg_length"),ffi_code_start_offset +
       ag32_ffi_get_arg_entrypoint);
     ((implode "get_arg"),ffi_code_start_offset + ag32_ffi_read_entrypoint);
     ((implode "read"),ffi_code_start_offset + ag32_ffi_write_entrypoint);
     ((implode "write"),ffi_code_start_offset +
       ag32_ffi_open_in_entrypoint);
     ((implode "open_in"),ffi_code_start_offset +
       ag32_ffi_open_out_entrypoint);
     ((implode "open_out"),ffi_code_start_offset +
       ag32_ffi_close_entrypoint);
     ((implode "close"),heap_start_offset)]
   // («exit», ffi_code_start_offset + ag32_ffi_get_arg_count_entrypoint);`;;

let mk_jump_ag32_code_def = new_definition
  `mk_jump_ag32_code ffi_names' name =
     let index = THE (INDEX_OF name ffi_names') in
     let entrypoint = THE (ALOOKUP ffi_entrypoints name) in
     let dist_to_ffi_code = (
       8 + ffi_offset * (LENGTH ffi_names' - 1 - index) +
       heap_size + length_ag32_ffi_code) - entrypoint in
     [Encode (LoadConstant ((n2w 5),F,(22 >< 0) ((n2w
       dist_to_ffi_code):word32)));
      Encode (LoadUpperConstant ((n2w 5),(31 >< 23) ((n2w
        dist_to_ffi_code):word32)));
      Encode (lab_Jump (fSub,(n2w 5),Reg (n2w 5)));
      (n2w 0)]`;;

let EL_FLAT_MAP_mk_jump_ag32_code = prove
 (`!ls index.
   (INDEX_OF nm ls = SOME index) /\ k < 4 ==>
   (EL (4 * index + k) (FLAT (MAP (mk_jump_ag32_code nmns) ls)) =
    EL k (mk_jump_ag32_code nmns nm))`,
  CHEAT_TAC);;

let ccache_jump_ag32_code_def = new_definition
  `ccache_jump_ag32_code = [Encode (lab_Jump (fSnd,(n2w 0),Reg (n2w 0)));
  (n2w 0); (n2w 0); (n2w 0)]`;;

let halt_jump_ag32_code_def = new_definition
  `halt_jump_ag32_code = [Encode (lab_Jump (fAdd,(n2w 0),Imm (n2w 0))); (n2w
  0); (n2w 0); (n2w 0)]`;;

let ag32_ffi_jumps_def = new_definition
  `ag32_ffi_jumps ffi_names' = APPEND (APPEND (FLAT (MAP (mk_jump_ag32_code
  ffi_names') (REVERSE ffi_names'))) ccache_jump_ag32_code)
  halt_jump_ag32_code`;;

(* HOL4 ag32_memoryScript.sml:3588-3593: a theorem that HOL4 states as the
   value of an ML expression: LENGTH_ag32_ffi_jumps *)

let ag32_ffi_code_def = new_definition
  `ag32_ffi_code =
     MAP Encode (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND
       (APPEND ag32_ffi__code
       ag32_ffi_get_arg_count_code)
       ag32_ffi_get_arg_length_code)
       ag32_ffi_get_arg_code)
       ag32_ffi_read_code)
       ag32_ffi_write_code)
       ag32_ffi_open_in_code)
       ag32_ffi_open_out_code)
       ag32_ffi_close_code)
   // ag32_ffi_exit_code ++`;;

let LENGTH_ag32_ffi_code =
  CAKE_EVAL [ag32_ffi_code_def; ag32_ffi__code_def;
  ag32_ffi_get_arg_count_code_def; ag32_ffi_get_arg_length_code_def;
  ag32_ffi_get_arg_code_def; ag32_ffi_read_code_def; ag32_ffi_write_code_def;
  ag32_ffi_open_in_code_def; ag32_ffi_open_out_code_def;
  ag32_ffi_close_code_def; ag32_ffi_fail_code_def; ag32_ffi_return_code_def;
  jump_def; ffi_code_start_offset_def; FFI_codes_def; fsFFI_read_def;
  fsFFI_write_def; labSem_assert_def; error_def;
  camlPtreeConversion_return_def; fsupdate_def; INR_def; bumpFD_def;
  output_offset_def; output_buffer_size_def; stdin_offset_def;
  stdin_size_def; startup_code_size_def; cline_size_def;
  ag32_ffi_write_set_id_code_def; ag32_ffi_write_check_conf_code_def;
  ag32_ffi_write_load_noff_code_def; ag32_ffi_write_check_lengths_code_def;
  ag32_ffi_write_write_header_code_def; ag32_ffi_write_num_written_code_def;
  ag32_ffi_copy_code_def; w22n_def; w82n_def; ag32_ffi_write_entrypoint_def;
  ag32_ffi_read_entrypoint_def; ag32_ffi_get_arg_entrypoint_def;
  ag32_ffi_get_arg_length_entrypoint_def;
  ag32_ffi_get_arg_count_entrypoint_def; ag32_ffi__entrypoint_def;
  ag32_ffi_read_set_id_code_def; ag32_ffi_read_check_conf_code_def;
  ag32_ffi_read_load_lengths_code_def; ag32_ffi_read_check_length_code_def;
  ag32_ffi_read_num_written_code_def; ag32_ffi_get_arg_setup_code_def;
  ag32_ffi_get_arg_find_code_def; ag32_ffi_get_arg_store_code_def;
  ag32_ffi_get_arg_length_setup_code_def;
  ag32_ffi_get_arg_length_loop_code_def;
  ag32_ffi_get_arg_length_store_code_def;
  ag32_ffi_get_arg_count_main_code_def] `LENGTH ag32_ffi_code`;;

let LENGTH_ag32_ffi_code_check = prove
 (`4 * LENGTH ag32_ffi_code = length_ag32_ffi_code`,
  CHEAT_TAC);;

let code_start_offset_def = new_definition
  `code_start_offset num_ffis =
     ffi_jumps_offset +
     ffi_offset *
     (2 +
          // halt and ccache
          num_ffis)`;;

let startup_asm_code_def = new_definition
  `startup_asm_code
     // r1: temp reg
     // r2: heap start reg: should be left with heap start address
     // r3: temp reg - only required because of large immediates
     // r4: heap end reg: should be left with heap end address
     // desired initial words of heap:
     // w0: bitmaps_ptr
     // w1: bitmaps_ptr + bitmaps_length
     // w2: bitmaps_ptr + bitmaps_length + bitmaps_buffer_length
     // w3: code_buffer_ptr
     // w4: code_buffer_ptr + code_buffer_length
     // for now, we simply assume code_buffer_length and bitmaps_buffer_length are 0 (no Install)
     // therefore, in our layout, we want to set things as follows:
     // --------------- <- w1, w2
     // CakeML data
     // --------------- <- w0, w3, w4
     // CakeML code
     // --------------- <- start PC
     num_ffis (code_length:word32) bitmaps_length =
     [
      // r2 <- heap_start_offset
      // r4 <- code_start_offset num_ffis
      // r1 <- code_length
      // r4 <- r4 + r1
      // m[r2+0] <- r4
      // m[r2+3] <- r4
      // m[r2+4] <- r4
      // r1 <- bitmaps_length
      // r4 <- r1 + r4
      // m[r2+1] <- r4
      // m[r2+2] <- r4
      // r1 <- heap_size
      // r4 <- r2 + r1
      // r1 <- code_start_offset num_ffis
      // jump r1
      asm_Inst (asm_Const 2 (n2w heap_start_offset));
      asm_Inst (asm_Const 4 (n2w (code_start_offset num_ffis)));
      asm_Inst (asm_Const 1 code_length);
      asm_Inst (asm_Arith (asm_Binop asm_Add 4 4 (Reg 1)));
      asm_Inst (asm_Mem asm_Store 4 (Addr 2 ((n2w 0) * bytes_in_word)));
      asm_Inst (asm_Mem asm_Store 4 (Addr 2 ((n2w 3) * bytes_in_word)));
      asm_Inst (asm_Mem asm_Store 4 (Addr 2 ((n2w 4) * bytes_in_word)));
      asm_Inst (asm_Const 1 bitmaps_length);
      asm_Inst (asm_Arith (asm_Binop asm_Add 4 1 (Reg 4)));
      asm_Inst (asm_Mem asm_Store 4 (Addr 2 ((n2w 1) * bytes_in_word)));
      asm_Inst (asm_Mem asm_Store 4 (Addr 2 ((n2w 2) * bytes_in_word)));
      asm_Inst (asm_Const 1 (n2w heap_size));
      asm_Inst (asm_Arith (asm_Binop asm_Add 4 2 (Reg 1)));
      asm_Inst (asm_Const 1 (n2w (code_start_offset num_ffis)));
      asm_JumpReg 1]`;;

let LENGTH_startup_asm_code =
  CAKE_EVAL [startup_asm_code_def; heap_start_offset_def;
  code_start_offset_def; heap_size_def; bytes_in_word_def;
  ffi_jumps_offset_def; ffi_offset_def; ffi_code_start_offset_def;
  length_ag32_ffi_code_def; output_offset_def; output_buffer_size_def;
  stdin_offset_def; stdin_size_def; startup_code_size_def; cline_size_def]
  `LENGTH (startup_asm_code n cl bl)`;;

let startup_code_def = new_definition
  `startup_code ffi_len code_len data_len =
     FLAT (MAP ag32_enc (startup_asm_code ffi_len (n2w code_len) (n2w (4
       * data_len))))`;;

let init_memory_words_def = new_definition
  `init_memory_words code data ffis cl stdin' =
   let startup = startup_code (LENGTH ffis) (LENGTH code) (LENGTH data) in
     APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND
     (APPEND (APPEND (APPEND
   // startup code
   (words_of_bytes F startup)
   // pad startup code to size
   (REPLICATE ((startup_code_size - LENGTH startup) DIV 4) (n2w 0)))
   [
    // command line
    n2w (LENGTH cl)])
   (words_of_bytes F (PAD_RIGHT (n2w 0) cline_size (FLAT (MAP (SNOC (n2w 0))
     (MAP (MAP (n2w o ORD) o explode) cl))))))
   [(n2w 0)])
   [
    // stdin
    n2w (LENGTH stdin')])
   (words_of_bytes F (PAD_RIGHT (n2w 0) stdin_size (MAP (n2w o ORD)
     stdin'))))
   // output
   (REPLICATE ((8 + 4 + output_buffer_size + 4) DIV 4) (n2w 0)))
   // ffis
   ag32_ffi_code)
   // heap
   (REPLICATE (heap_size DIV 4) (n2w 0)))
   // FFIs
   (ag32_ffi_jumps ffis))
   (words_of_bytes F code))
   data
   // ++ padding of 0w out to memory_size: not included here`;;

let ag32_memory_init_memory_def = new_definition
  `ag32_memory_init_memory code data ffis (cl,stdin') k =
   get_byte k (EL (w2n (byte_align k) DIV 4) (init_memory_words code data
     ffis cl stdin')) F`;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["cf";
   "read";
   "write"];;

(* and the interface *)
let _ = unhide_overloads ();;
