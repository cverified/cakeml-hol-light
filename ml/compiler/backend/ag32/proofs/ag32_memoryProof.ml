(* ======================================================== *)
(*  ag32_memoryProof: ported from HOL4's
    compiler/backend/ag32/proofs/ag32_memoryProofScript.sml
    A proof theory about ag32_memory.ml, with 1 definition and 24
    theorems.  Needed by ag32BootstrapProof.ml and
    ag32_basis_ffiProof.ml.  *)
(* ======================================================== *)

(*
  Prove some properties about the ag32 memory layout including
  correctness of the startup code and length and lookup theorems for
  other parts of memory.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/ag32/ag32_memory.ml";;
needs "compiler/backend/ag32/proofs/ag32_machine_config.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/backend/proofs/backendProof.ml";;
needs "compiler/backend/proofs/data_to_word_memoryProof.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/encoders/asm/asmSem.ml";;
needs "lib/alignment.ml";;
needs "lib/byte.ml";;
needs "misc/misc.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ag32_memoryProof"
  ["ag32_machine_config"; "ag32_memory"; "asm"; "backendProof";
   "data_to_word_memoryProof"];;

(* TODO: move *)

let get_byte_word_of_bytes = prove
 (`good_dimindex (:'a) ==>
   i < LENGTH ls /\ LENGTH ls <= w2n (bytes_in_word:'a word) ==>
   (get_byte (n2w i) (word_of_bytes be ((n2w 0):'a word) ls) be = EL i ls)`,
  CHEAT_TAC);;

let get_byte_EL_words_of_bytes = prove
 (`!be' ls.
   i < LENGTH ls /\ w2n (bytes_in_word:'a word) * LENGTH ls <= dimword (:'a)
     /\ good_dimindex (:'a) ==>
   (get_byte (n2w i:'a word)
      (EL (w2n (byte_align ((n2w i):'a word)) DIV (w2n (bytes_in_word:'a
        word)))
        (words_of_bytes be' ls)) be' = EL i ls)`,
  CHEAT_TAC);;

let get_mem_word_get_byte_gen = prove
 (`(!x.
      r0 + n2w (4 * (LENGTH ll + k)) <=+ x /\ x <+ r0 + n2w (4 * (LENGTH ll
        + k) + 4) ==> (m x = get_byte x (EL (w2n (byte_align x - r0) DIV 4)
        (APPEND (APPEND ll ls) lr)) F)) /\
   (LENGTH ll = off) /\
   k < LENGTH ls /\ byte_aligned r0 /\ (4 * (off + k)) < dimword (:31) /\
   w2n r0 + (4 * (off + k) + 4) < dimword (:32) ==> (get_mem_word m (r0 +
     n2w (4 * (off + k))) = EL k ls)`,
  CHEAT_TAC);;

let get_mem_word_get_byte =
  SIMP_RULE [CAKE_EVAL [byte_aligned_def; aligned_def; align_def]
  `byte_aligned (n2w 0)`] (CAKE_SPEC `(n2w 0)` (CAKE_GEN `r0`
  get_mem_word_get_byte_gen));;

let ag32_enc_lengths = prove
 (`LENGTH (ag32_enc istr) IN {4,8,12,16}`,
  CHEAT_TAC);;

let bytes_in_memory_get_byte_words = prove
 (`!ls ll a.
   (!k. k IN all_words a (LENGTH ls) ==>
        (m k = get_byte k (EL (w2n (byte_align k) DIV 4) (APPEND (APPEND ll
          (words_of_bytes be ls)) lr)) be)) /\
   (a = n2w (4 * LENGTH ll)) /\
   (all_words a (LENGTH ls) SUBSET md) /\ 4 * (LENGTH ll) < dimword (:31)
     /\ 4 * LENGTH ls <= dimword (:32) ==>
   bytes_in_memory (a:word32) ls m md`,
  CHEAT_TAC);;

(* [local] *)
let get_byte_repl = prove
 (`n + m < dimword (:32) /\
   (m MOD 4 = 0) ==>
   (get_byte ((n2w (n + m)):word32) w F =
   get_byte (n2w n) w F)`,
  CHEAT_TAC);;

(* -- *)

let byte_aligned_code_start_offset = prove
 (`byte_aligned (n2w (code_start_offset num_ffis):word32)`,
  CHEAT_TAC);;

let LENGTH_startup_code = prove
 (`LENGTH (startup_code f c d) <= startup_code_size`,
  CHEAT_TAC);;

let LENGTH_ag32_enc_MOD_4 = prove
 (`LENGTH (ag32_enc i) MOD 4 = 0`,
  CHEAT_TAC);;

let LENGTH_startup_code_MOD_4 = prove
 (`LENGTH (startup_code f c d) MOD 4 = 0`,
  CHEAT_TAC);;

(* HOL4 ag32_memoryProofScript.sml:355: the ML values that the definitions
   below antiquote *)

let LENGTH_init_memory_words = prove
 (`SUM (MAP strlen cl) + LENGTH cl <= cline_size /\ LENGTH inp <= stdin_size
  ==>
   (LENGTH (init_memory_words c d f cl inp) =
   LENGTH d +
   LENGTH (ag32_ffi_jumps f) +
   LENGTH c DIV 4 + MIN 1 (LENGTH c MOD 4) +
   (LENGTH ag32_ffi_code + cline_size DIV 4 + stdin_size DIV 4 + heap_size
     DIV 4 + startup_code_size DIV 4 + (output_buffer_size + 16) DIV 4 + 3))`,
  CHEAT_TAC);;

(* lem[local] *)
let ag32_memoryProof_lem = prove
 (`(m MOD 4 = 0) /\ n < m ==> n DIV 4 < m DIV 4`,
  CHEAT_TAC);;

let init_memory_startup = prove
 (`!code data ffis n.
   n < LENGTH (startup_code (LENGTH ffis) (LENGTH code) (LENGTH data)) ==>
   (ag32_memory_init_memory code data ffis inputs (n2w n) = EL n
     (startup_code (LENGTH ffis) (LENGTH code) (LENGTH data)))`,
  CHEAT_TAC);;

let init_memory_code = prove
 (`!code data ffis n.
   SUM (MAP strlen cl) + LENGTH cl <= cline_size /\ LENGTH inp <= stdin_size
     /\
   code_start_offset (LENGTH ffis) + (LENGTH code) + 4 * LENGTH data <
     memory_size /\
   n < LENGTH code ==>
   (ag32_memory_init_memory code data ffis (cl,inp) (n2w n + n2w
     (code_start_offset (LENGTH ffis))) = EL n code)`,
  CHEAT_TAC);;

(* TODO - clean it up a bit (it repeats a lot) *)
let init_memory_data = prove
 (`SUM (MAP strlen cl) + LENGTH cl <= cline_size /\
   LENGTH inp <= stdin_size /\
   code_start_offset (LENGTH ffis) + (LENGTH code) +
     4 * LENGTH data < memory_size /\
   (low = code_start_offset (LENGTH ffis) + LENGTH code) /\
   k < LENGTH data /\
   byte_aligned (n2w (LENGTH code):word32) ==>
   word_of_bytes F (n2w 0)
     [ag32_memory_init_memory code data ffis (cl,inp) (n2w (4 * (k + low DIV
       4)));
      ag32_memory_init_memory code data ffis (cl,inp) (n2w (4 * (k + low DIV
        4)) + (n2w 1));
      ag32_memory_init_memory code data ffis (cl,inp) (n2w (4 * (k + low DIV
        4)) + (n2w 2));
      ag32_memory_init_memory code data ffis (cl,inp) (n2w (4 * (k + low DIV
        4)) + (n2w 3))] =
    EL k data`,
  CHEAT_TAC);;

let init_memory_halt = prove
 (`(pc = n2w (ffi_jumps_offset + (LENGTH f + 1) * ffi_offset)) /\
   LENGTH f <= LENGTH FFI_codes /\
   SUM (MAP strlen cl) + LENGTH cl <= cline_size /\ LENGTH inp <= stdin_size
     ==>
   (get_mem_word (ag32_memory_init_memory c d f (cl,inp)) pc =
    Encode (asm_Jump (fAdd,(n2w 0),Imm (n2w 0))))`,
  CHEAT_TAC);;

let init_memory_ccache = prove
 (`(pc = n2w (ffi_jumps_offset + (LENGTH f + 0) * ffi_offset)) /\
   LENGTH f <= LENGTH FFI_codes /\
   SUM (MAP strlen cl) + LENGTH cl <= cline_size /\ LENGTH inp <= stdin_size
     ==>
   (get_mem_word (ag32_memory_init_memory c d f (cl,inp)) pc =
    Encode (asm_Jump (fSnd,(n2w 0),Reg (n2w 0))))`,
  CHEAT_TAC);;

let init_memory_startup_bytes_in_memory = prove
 (`i < LENGTH scc /\
   (scc = startup_asm_code (LENGTH ffis) (n2w (LENGTH code)) (n2w (4 *
     (LENGTH data)))) ==>
   bytes_in_memory (n2w (SUM (MAP (LENGTH o ag32_enc) (TAKE i scc))))
     (ag32_enc (EL i scc))
     (ag32_memory_init_memory code data ffis inputs)
       ag32_startup_addresses`,
  CHEAT_TAC);;

let init_asm_state_def = new_definition
  `init_asm_state code data ffis input =
   let im = ag32_memory_init_memory code data ffis in
   let sac = startup_asm_code (LENGTH ffis) (n2w (LENGTH code)) (n2w (4 *
     LENGTH data)) in
     FOLDL (\s i. asmSem_asm i (asm_state_pc s + n2w (LENGTH (ag32_enc i)))
       s)
       (ag32_init_asm_state
         (im input)
         (ag32_startup_addresses))
         sac`;;

(* HOL4 ag32_memoryProofScript.sml:896-898: ML code, not ported *)

(* HOL4 ag32_memoryProofScript.sml:910-918: ML code, not ported *)

(* HOL4 ag32_memoryProofScript.sml:920-923: ML code, not ported *)

(* HOL4 ag32_memoryProofScript.sml:925-935: code that the source has in a
   comment *)

(* HOL4 ag32_memoryProofScript.sml:937-943: a proof *)

(* [local] *)
let bounded_bits = prove
 (`ll < 4294967296 ==>
    ((BIT 0 (ll MOD 256) <=> BIT 0 ll) /\ (BIT 1 (ll MOD 256) <=> BIT 1 ll)
      /\
    (BIT 2 (ll MOD 256) <=> BIT 2 ll) /\ (BIT 3 (ll MOD 256) <=> BIT 3 ll)
      /\
    (BIT 4 (ll MOD 256) <=> BIT 4 ll) /\ (BIT 5 (ll MOD 256) <=> BIT 5 ll)
      /\
    (BIT 6 (ll MOD 256) <=> BIT 6 ll) /\ (BIT 7 (ll MOD 256) <=> BIT 7 ll))
      /\
    ((BIT 0 (BITS 31 8 ll MOD 256) <=> BIT 8 ll) /\
    (BIT 1 (BITS 31 8 ll MOD 256) <=> BIT 9 ll) /\
    (BIT 2 (BITS 31 8 ll MOD 256) <=> BIT 10 ll) /\
    (BIT 3 (BITS 31 8 ll MOD 256) <=> BIT 11 ll) /\
    (BIT 4 (BITS 31 8 ll MOD 256) <=> BIT 12 ll) /\
    (BIT 5 (BITS 31 8 ll MOD 256) <=> BIT 13 ll) /\
    (BIT 6 (BITS 31 8 ll MOD 256) <=> BIT 14 ll) /\
    (BIT 7 (BITS 31 8 ll MOD 256) <=> BIT 15 ll)) /\
    ((BIT 0 (BITS 31 8 (BITS 31 8 ll) MOD 256) <=> BIT 16 ll) /\
    (BIT 1 (BITS 31 8 (BITS 31 8 ll) MOD 256) <=> BIT 17 ll) /\
    (BIT 2 (BITS 31 8 (BITS 31 8 ll) MOD 256) <=> BIT 18 ll) /\
    (BIT 3 (BITS 31 8 (BITS 31 8 ll) MOD 256) <=> BIT 19 ll) /\
    (BIT 4 (BITS 31 8 (BITS 31 8 ll) MOD 256) <=> BIT 20 ll) /\
    (BIT 5 (BITS 31 8 (BITS 31 8 ll) MOD 256) <=> BIT 21 ll) /\
    (BIT 6 (BITS 31 8 (BITS 31 8 ll) MOD 256) <=> BIT 22 ll) /\
    (BIT 7 (BITS 31 8 (BITS 31 8 ll) MOD 256) <=> BIT 23 ll)) /\
    ((BIT 0 (BITS 31 8 (BITS 31 8 (BITS 31 8 ll)) MOD 256) <=> BIT 24 ll) /\
    (BIT 1 (BITS 31 8 (BITS 31 8 (BITS 31 8 ll)) MOD 256) <=> BIT 25 ll) /\
    (BIT 2 (BITS 31 8 (BITS 31 8 (BITS 31 8 ll)) MOD 256) <=> BIT 26 ll) /\
    (BIT 3 (BITS 31 8 (BITS 31 8 (BITS 31 8 ll)) MOD 256) <=> BIT 27 ll) /\
    (BIT 4 (BITS 31 8 (BITS 31 8 (BITS 31 8 ll)) MOD 256) <=> BIT 28 ll) /\
    (BIT 5 (BITS 31 8 (BITS 31 8 (BITS 31 8 ll)) MOD 256) <=> BIT 29 ll) /\
    (BIT 6 (BITS 31 8 (BITS 31 8 (BITS 31 8 ll)) MOD 256) <=> BIT 30 ll) /\
    (BIT 7 (BITS 31 8 (BITS 31 8 (BITS 31 8 ll)) MOD 256) <=> BIT 31 ll))`,
  CHEAT_TAC);;

(* HOL4 ag32_memoryProofScript.sml:997-1012: a proof *)

(* [local] *)
let ag32_const_enc = prove
 (`(?a b c d.
   ag32_enc (asm_Inst (asm_Const r w)) = [a; b; c; d]) \/
   (?a b c d e f g h. ag32_enc (asm_Inst (asm_Const r w)) = [a; b; c; d;
     e; f; g; h])`,
  CHEAT_TAC);;

(* HOL4 ag32_memoryProofScript.sml:1023-1036: a proof *)

(* [local] *)
let FLAT_CONS = prove
 (`FLAT (CONS h t) = APPEND h (FLAT t)`,
  CHEAT_TAC);;

(* HOL4 ag32_memoryProofScript.sml:1044-1047: ML code, not ported *)

(* HOL4 ag32_memoryProofScript.sml:1049-1053: ML code, not ported *)

(* HOL4 ag32_memoryProofScript.sml:1055-1059: code that the source has in a
   comment *)

let init_asm_state_asm_step = prove
 (`!code data ffis cl inp.
   SUM (MAP strlen cl) + LENGTH cl <= cline_size /\
   LENGTH inp <= stdin_size /\
   LENGTH ffis <= LENGTH FFI_codes /\
   code_start_offset (LENGTH ffis) + (LENGTH code) + 4 * LENGTH data <
     memory_size /\
   (im = ag32_memory_init_memory code data ffis) /\
   (asm_state0 =
    ag32_init_asm_state
        (im (cl,inp))
        (ag32_startup_addresses)) /\
   (mc =
    ag32_machine_config ffis (LENGTH code) (LENGTH data)) ==>
   (let tr =
   (steps (\s i. asmSem_asm i (asm_state_pc s + n2w (LENGTH (ag32_enc i)))
     s)
     asm_state0
     (startup_asm_code
       (LENGTH ffis)
       (n2w (LENGTH code))
       (n2w (4 * LENGTH data)))) in
   steps_rel (asm_step (target_config ag32_target)) asm_state0 tr /\
   (let final_st = LAST (CONS asm_state0 (MAP SND tr)) in
   let num_ffis = LENGTH ffis in
    (asm_state_pc final_st = n2w (code_start_offset num_ffis)) /\
    (read_bytearray (asm_state_pc final_st) (LENGTH code)
      (\a. if a IN machine_config_prog_addresses mc then
              SOME (asm_state_mem final_st a) else NONE) = SOME code) /\
    (let hs = n2w heap_start_offset in
    let ds = n2w (code_start_offset num_ffis + LENGTH code) in
    (asm_state_regs final_st 2 = hs) /\
    (asm_state_regs final_st 4 = hs + n2w heap_size) /\
    (word_of_bytes F (n2w 0) (list_of_seq (asm_state_mem final_st o ((+) (hs
      + (n2w 0) * (n2w 4))) o n2w) 4) =
     ds) /\
    (word_of_bytes F (n2w 0) (list_of_seq (asm_state_mem final_st o ((+) (hs
      + (n2w 1) * (n2w 4))) o n2w) 4) =
     ds + n2w (4 * LENGTH data)) /\
    (word_of_bytes F (n2w 0) (list_of_seq (asm_state_mem final_st o ((+) (hs
      + (n2w 2) * (n2w 4))) o n2w) 4) =
     ds + n2w (4 * LENGTH data)) /\
    (word_of_bytes F (n2w 0) (list_of_seq (asm_state_mem final_st o ((+) (hs
      + (n2w 3) * (n2w 4))) o n2w) 4) =
     ds) /\
    (word_of_bytes F (n2w 0) (list_of_seq (asm_state_mem final_st o ((+) (hs
      + (n2w 4) * (n2w 4))) o n2w) 4) =
     ds) /\
    (!k. k < 4 * LENGTH data + 4 ==>
         (asm_state_mem final_st (ds + n2w k) =
          (im (cl,inp)) (ds + n2w k))))))`,
  CHEAT_TAC);;

let init_asm_state_RTC_asm_step = prove
 (`!code data ffis cl inp.
   SUM (MAP strlen cl) + LENGTH cl <= cline_size /\
   LENGTH inp <= stdin_size /\
   LENGTH ffis <= LENGTH FFI_codes /\
   code_start_offset (LENGTH ffis) + (LENGTH code) + 4 * LENGTH data <
     memory_size /\
   (im = ag32_memory_init_memory code data ffis) /\
   (iasmstate = init_asm_state code data ffis (cl,inp)) /\
   (asm_state0 =
    ag32_init_asm_state
        (im (cl,inp))
        (ag32_startup_addresses)) /\
   (mc =
    ag32_machine_config ffis (LENGTH code) (LENGTH data)) ==> RTC
   (\x y. ?i. asm_step ag32_config x i y) asm_state0 iasmstate /\
   (let num_ffis = LENGTH ffis in
   let hs = n2w heap_start_offset in
   let ds = n2w (code_start_offset num_ffis + LENGTH code) in
   (pc iasmstate = n2w (code_start_offset num_ffis)) /\
   (
      read_bytearray (pc iasmstate) (LENGTH code)
      (\a. if a IN machine_config_prog_addresses mc then SOME (mem iasmstate
        a) else NONE) = SOME code) /\
    (regs iasmstate 2 = hs) /\
    (regs iasmstate 4 = hs + n2w heap_size) /\
    (
     word_of_bytes F (n2w 0) (list_of_seq (mem iasmstate o ((+) (hs + (n2w
       0) * (n2w 4))) o n2w) 4) = ds) /\
    (
     word_of_bytes F (n2w 0) (list_of_seq (mem iasmstate o ((+) (hs + (n2w
       1) * (n2w 4))) o n2w) 4) = ds + n2w (4 * LENGTH data)) /\
    (
     word_of_bytes F (n2w 0) (list_of_seq (mem iasmstate o ((+) (hs + (n2w
       2) * (n2w 4))) o n2w) 4) = ds + n2w (4 * LENGTH data)) /\
    (
     word_of_bytes F (n2w 0) (list_of_seq (mem iasmstate o ((+) (hs + (n2w
       3) * (n2w 4))) o n2w) 4) = ds) /\
    (
     word_of_bytes F (n2w 0) (list_of_seq (mem iasmstate o ((+) (hs + (n2w
       4) * (n2w 4))) o n2w) 4) = ds) /\
    (!k. k < 4 * LENGTH data + 4 ==>
      (mem iasmstate (ds + n2w k) =
       im (cl,inp) (ds + n2w k))))`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
