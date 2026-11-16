(* ======================================================== *)
(*  ag32_basis_ffiProof: ported from HOL4's
    compiler/backend/ag32/proofs/ag32_basis_ffiProofScript.sml
    A proof theory, with 10 definitions and 77 theorems.  Needed by
    ag32BootstrapProof.ml.  *)
(* ======================================================== *)

(*
  Verify that the ag32 implementation of the FFI primitives satisfies
  interference_implemented.
*)

needs "basis/CommandLineProof.ml";;
needs "basis/Marshalling.ml";;
needs "basis/TextIOProof.ml";;
needs "basis/basis_ffi.ml";;
needs "basis/clFFI.ml";;
needs "basis/fsFFI.ml";;
needs "basis/fsFFIProps.ml";;
needs "basis/pure/mlstring.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "compiler/backend/ag32/ag32_config.ml";;
needs "compiler/backend/ag32/ag32_memory.ml";;
needs "compiler/backend/ag32/proofs/ag32_ffi_codeProof.ml";;
needs "compiler/backend/ag32/proofs/ag32_machine_config.ml";;
needs "compiler/backend/ag32/proofs/ag32_memoryProof.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/backend/proofs/backendProof.ml";;
needs "compiler/backend/semantics/targetSem.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/encoders/asm/asmProps.ml";;
needs "compiler/encoders/asm/asmSem.ml";;
needs "lib/alignment.ml";;
needs "lib/byte.ml";;
needs "misc/misc.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "translator/ml_prog.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ag32_basis_ffiProof"
  ["ag32_ffi_codeProof"; "ag32_machine_config"; "ag32_memory";
   "ag32_memoryProof"; "basis_ffi"];;

let _ = do_list hide_constant ["context"; "not"];;

(* TODO: move *)

let INDEX_OF_IMP_EL = prove
 (`!xs x index. (INDEX_OF x xs = SOME index) ==> (EL index xs = x)`,
  CHEAT_TAC);;

let INDEX_OF_REVERSE = prove
 (`ALL_DISTINCT ls ==>
   INDEX_OF x (REVERSE ls) = OPTION_MAP (\n. LENGTH ls - 1 - n) (INDEX_OF
     x ls)`,
  CHEAT_TAC);;

let bytes_in_memory_UPDATE_GT = prove
 (`k <+ (pc:word32) /\
   LENGTH ls <= 2 EXP 31 /\
   ~(word_msb pc) /\
   bytes_in_memory pc ls m dm ==>
   bytes_in_memory pc ls ((k =+ v) m) dm`,
  CHEAT_TAC);;

let bytes_in_memory_UPDATE_LT = prove
 (`(w2n pc + (LENGTH ls) <= w2n (k:word32)) /\
   LENGTH ls <= 2 EXP 31 /\
   ~(word_msb pc) /\
   bytes_in_memory pc ls m dm ==>
   bytes_in_memory pc ls ((k =+ v) m) dm`,
  CHEAT_TAC);;

let bytes_in_memory_asm_write_bytearray_LT = prove
 (`(w2n pc + (LENGTH ls) <= w2n (k:word32)) /\
   (w2n k + (LENGTH bs) < dimword (:32)) /\
   LENGTH ls <= 2 EXP 31 /\
   ~(word_msb pc) /\
   bytes_in_memory pc ls m dm ==>
   bytes_in_memory pc ls (asm_write_bytearray k bs m) dm`,
  CHEAT_TAC);;

let asm_write_bytearray_UPDATE = prove
 (`~(x = pc) ==>
     asm_write_bytearray a ls ((pc =+ v) m) x =
     asm_write_bytearray a ls m x`,
  CHEAT_TAC);;

let set_mem_word_asm_write_bytearray_commute_LT = prove
 (`(pc <+ a) /\
   (pc + (n2w 1) <+ a) /\
   (pc + (n2w 2) <+ a) /\
   (pc + (n2w 3) <+ a) /\
   w2n a + LENGTH ls < dimword (:32) ==>
   set_mem_word pc w
   (asm_write_bytearray a ls m) =
   asm_write_bytearray a ls (set_mem_word pc w m)`,
  CHEAT_TAC);;

let asm_write_bytearray_append2 = prove
 (`!a l1 l2 m.
   (asm_write_bytearray (a:word32) (APPEND l1 l2) m =
    asm_write_bytearray a l1 (asm_write_bytearray (a + n2w (LENGTH l1)) l2
      m))`,
  CHEAT_TAC);;

(* HOL4 ag32_basis_ffiProofScript.sml:142: the overload nxt, which the port
   expands *)

let interference_implemented_def = new_definition
  `interference_implemented mc ffi_rel md ms0 <=>
     (?next_interfer ccache_interfer ffi_interfer.
     (!n. machine_config_next_interfer mc n = next_interfer) /\
     (!n. machine_config_ccache_interfer mc n = ccache_interfer) /\
     (!n. machine_config_ffi_interfer mc n = ffi_interfer) /\
     (!ms k0.
       (ms = ITER k0 (target_next (machine_config_target mc)) ms0) /\
       (!x. ~(x IN md) /\ ~(x IN machine_config_prog_addresses mc) ==>
         (target_get_byte (machine_config_target mc) ms x = target_get_byte
         (machine_config_target mc) ms0 x)) ==>
       (
       target_get_pc (machine_config_target mc) ms IN
         machine_config_prog_addresses mc DIFF set_of_list
         (machine_config_ffi_entry_pcs mc) /\
        encoded_bytes_in_mem (target_config (machine_config_target mc))
          (target_get_pc (machine_config_target mc) ms)
          (target_get_byte (machine_config_target mc) ms)
            (machine_config_prog_addresses mc) /\
        (!x. ~(x IN machine_config_prog_addresses mc) ==> (target_get_byte
          (machine_config_target mc) (target_next (machine_config_target mc)
          ms) x = target_get_byte (machine_config_target mc) ms x))
          /\ target_state_ok (machine_config_target
        mc) ms ==>
         (?k. (
              next_interfer (target_next (machine_config_target mc) ms) =
                ITER k (target_next (machine_config_target mc)) (target_next
                (machine_config_target mc) ms)) /\
             (ffi_rel ms = ffi_rel (target_next (machine_config_target mc)
               ms)) /\
             (ffi_rel (target_next (machine_config_target mc) ms) =
              ffi_rel (ITER k (target_next (machine_config_target mc))
                (target_next (machine_config_target mc) ms))) /\
             (!x. ~(x IN md) \/ x IN machine_config_prog_addresses mc DIFF
               set_of_list (machine_config_ffi_entry_pcs mc) ==>
                   (target_get_byte (machine_config_target mc) (ITER k
                     (target_next (machine_config_target mc)) (target_next
                     (machine_config_target mc) ms)) x = target_get_byte
                     (machine_config_target
                    mc) (target_next (machine_config_target mc) ms) x)))) /\
       ((target_get_pc (machine_config_target mc) ms =
         machine_config_ccache_pc mc) ==>
         (?k. (
              ccache_interfer
              (target_get_reg (machine_config_target mc) ms
                (machine_config_ptr_reg mc),target_get_reg
                (machine_config_target
               mc) ms (machine_config_len_reg mc),ms) = ITER k (target_next
                 (machine_config_target mc)) ms) /\
             (ffi_rel ms =
              ffi_rel (ITER k (target_next (machine_config_target mc)) ms))
                /\
             (!x. ~(x IN md) \/ x IN machine_config_prog_addresses mc ==>
               (target_get_byte (machine_config_target mc) (ITER k
                 (target_next (machine_config_target mc)) ms) x =
                 target_get_byte (machine_config_target
                mc) ms x)))) /\
       (!ffi ffi_index bytes bytes2 new_ffi new_bytes.
   (~(target_get_pc (machine_config_target mc) ms IN
     machine_config_prog_addresses mc DIFF set_of_list
     (machine_config_ffi_entry_pcs mc))) /\
           (find_index (target_get_pc (machine_config_target mc) ms)
             (machine_config_ffi_entry_pcs mc) 0 = SOME ffi_index) /\
           (~(target_get_pc (machine_config_target mc) ms =
             machine_config_ccache_pc mc)) /\
           (read_ffi_bytearrays mc ms = (SOME bytes,SOME bytes2)) /\
           (call_FFI ffi (EL ffi_index (machine_config_ffi_names mc)) bytes
             bytes2 =
             FFI_return new_ffi new_bytes) /\
           (ffi_rel ms ffi) ==>
           (?k.
             (ffi_interfer (ffi_index,new_bytes,ms) =
              ITER k (target_next (machine_config_target mc)) ms) /\
             (ffi_rel (ITER k (target_next (machine_config_target mc)) ms)
               new_ffi) /\
             (!x. ~(x IN md) /\ ~(x IN all_words (target_get_reg
               (machine_config_target mc) ms (machine_config_ptr2_reg mc))
               (LENGTH bytes2)) ==>
               (target_get_byte (machine_config_target mc) (ITER k
                 (target_next (machine_config_target mc)) ms) x =
                 target_get_byte (machine_config_target
                mc) ms x))))))`;;

let evaluate_Halt_FUNPOW_next = prove
 (`!mc (ffi:'ffi ffi_state) k ms t ms' ffi'.
   interference_implemented mc ffi_rel md ms /\ ffi_rel ms ffi /\
   ~(MEM (machine_config_ccache_pc mc) (machine_config_ffi_entry_pcs mc)) /\
   ALL (\x. ?s. x = ffi_ExtCall s) (machine_config_ffi_names mc) /\
   LENGTH (machine_config_ffi_entry_pcs mc) <= LENGTH
     (machine_config_ffi_names mc) /\
   (targetSem_evaluate mc ffi k ms = (targetSem_Halt t,ms',ffi')) ==>
     (?k'. (ms' = ITER k' (target_next (machine_config_target mc)) ms) /\
          (ffi_rel ms' ffi') /\
          (!x. ~(x IN md UNION machine_config_prog_addresses mc) ==>
            (target_get_byte (machine_config_target mc) ms' x = target_get_byte
            (machine_config_target mc) ms x)) /\
          ((!x. ~(t = ffi_FFI_outcome x)) ==> (target_get_pc
            (machine_config_target mc) ms' = machine_config_halt_pc mc)) /\
          (
            ((target_get_reg (machine_config_target mc) ms'
              (machine_config_ptr_reg mc) = (n2w 0)) /\ (!x. ~(t =
              ffi_FFI_outcome x))) ==> (t = ffi_Success)))`,
  CHEAT_TAC);;

let machine_sem_Terminate_FUNPOW_next = prove
 (`interference_implemented mc ffi_rel md ms /\
   (ffi_rel ms st) /\
   ~(MEM (machine_config_ccache_pc mc) (machine_config_ffi_entry_pcs mc)) /\
   ALL (\x. ?s. x = ffi_ExtCall s) (machine_config_ffi_names mc) /\
   LENGTH (machine_config_ffi_entry_pcs mc) <= LENGTH
     (machine_config_ffi_names mc) /\
   targetSem_machine_sem mc (st:'ffi ffi_state) ms (ffi_Terminate t
     io_events) ==>
   (?k st'.
     ffi_rel (ITER k (target_next (machine_config_target mc)) ms) st'
       /\ (io_events = ffi_state_io_events st') /\
       (!x. ~(x IN md UNION machine_config_prog_addresses mc) ==>
         (target_get_byte (machine_config_target mc) (ITER k (target_next
         (machine_config_target mc)) ms) x = target_get_byte
         (machine_config_target mc) ms x)) /\
       ((!x. ~(t = ffi_FFI_outcome x)) ==> (target_get_pc
         (machine_config_target mc) (ITER k (target_next (machine_config_target
         mc)) ms) = machine_config_halt_pc mc)) /\
       (
        (target_get_reg (machine_config_target mc) (ITER k (target_next
          (machine_config_target mc)) ms) (machine_config_ptr_reg mc) = (n2w
          0)) /\ (!x. ~(t = ffi_FFI_outcome x)) ==> (t = ffi_Success)))`,
  CHEAT_TAC);;

let word_of_bytes_extract_bytes_le_32 = prove
 (`word_of_bytes F (n2w 0) [(7 >< 0) w; (15 >< 8) w; (23 >< 16) w; (31 >< 24)
  w] = (w:word32)`,
  CHEAT_TAC);;

let bytes_in_mem_bytes_in_memory = prove
 (`!a bs m md k. bytes_in_mem a bs m md k <=> bytes_in_memory a bs m (md DIFF
  k)`,
  CHEAT_TAC);;

let read_bytearray_IMP_bytes_in_memory_WORD_LOWER = prove
 (`!p n m ba m' md.
   (n = LENGTH ba) /\ w2n p + n < dimword (:'a) /\
   (!k. (p <=+ k /\ k <+ p + n2w n) ==> k IN md /\ (m k = SOME (m' k))) /\
   (read_bytearray (p:'a word) n m = SOME ba) ==>
   bytes_in_memory p ba m' md`,
  CHEAT_TAC);;

let bytes_in_memory_IMP_asm_write_bytearray = prove
 (`!bs a m. bytes_in_memory a bs m md ==> (asm_write_bytearray a bs m = m)`,
  CHEAT_TAC);;

let IMP_word_list = prove
 (`8 <= dimindex (:'a) ==>
   (!p ls m.
   (m = IMAGE (\k. (p + n2w k * (bytes_in_word:'a word),EL k ls)) (count
     (LENGTH ls))) /\
   w2n p + LENGTH ls * w2n (bytes_in_word:'a word) < dimword (:'a) ==>
     misc_word_list p ls m)`,
  CHEAT_TAC);;

(* HOL4 ag32_basis_ffiProofScript.sml:481-497: code that the source has in a
   comment *)

let asm_step_target_configured = prove
 (`asm_step c s1 i s2 /\ target_configured s1 mc ==>
   target_configured s2 mc`,
  CHEAT_TAC);;

let RTC_asm_step_target_configured = prove
 (`RTC (\s1 s2. ?i. asm_step c s1 i s2) s1 s2 /\
   target_configured s1 mc ==>
   target_configured s2 mc`,
  CHEAT_TAC);;

let ag32_io_events_unchanged = prove
 (`~(Decode (
   let v:word32 = ((31 >< 2) (?_PC ms):word30) in
     (?_MEM ms (v + (n2w 3)) @@
      ((?_MEM ms (v + (n2w 2)) @@
        ((?_MEM ms (v + (n2w 1)) @@ ?_MEM
          ms (v + (n2w 0))):word16)):word24))) = Interrupt) ==>
   (ffi_state_io_events (Next ms) = ffi_state_io_events ms)`,
  CHEAT_TAC);;

let ag32_enc_not_Interrupt = prove
 (`4 * k < LENGTH (ag32_enc istr) ==>
   (let bs = DROP (4 * k) (ag32_enc istr) in ~(Decode (EL 3 bs @@ ((EL 2
     bs @@ ((EL 1 bs @@ EL 0 bs):word16)):word24)) = Interrupt))`,
  CHEAT_TAC);;

let RTC_asm_step_ag32_target_state_rel_io_events = prove
 (`target_state_rel ag32_target s1 ms /\
   RTC (\s1 s2. ?i. asm_step ag32_config s1 i s2) s1 s2 ==>
   (?n. target_state_rel ag32_target s2 (ITER n Next ms) /\
       (ffi_state_io_events (ITER n Next ms) = ffi_state_io_events ms) /\
       (!x. ~(x IN asm_state_mem_domain s1) ==> (?_MEM (ITER n Next ms) x
         = ?_MEM ms x)))`,
  CHEAT_TAC);;

let read_bytearray_IMP_domain = prove
 (`// replace uses with read_bytearray_IMP_mem_SOME
   !n a xs.
     (read_bytearray a n
       (\a. if a IN md then SOME (m a) else NONE) = SOME xs) ==>
     (!i. i < n ==> a + n2w i IN md)`,
  CHEAT_TAC);;

(* -- *)

let startup_asm_code_small_enough = prove
 (`!i. LENGTH (ag32_enc i) * LENGTH (startup_asm_code n cl bl) <=
  startup_code_size`,
  CHEAT_TAC);;

(* HOL4 ag32_basis_ffiProofScript.sml:725-735: code that the source has in a
   comment *)

let get_output_io_event_def = new_definition
  `get_output_io_event (IO_event CommandLineProof_name conf bs2) =
     if CommandLineProof_name = ffi_ExtCall (implode "write") then
       match MAP FST bs2 with (CONS n1 (CONS n0 (CONS off1 (CONS off0
         tll)))) ->
         let k = MIN (w22n [n1; n0]) output_buffer_size in
         if (SND (HD bs2) = (n2w 0)) then
           let written = TAKE k (DROP (w22n [off1; off0]) tll) in
             SOME (APPEND (APPEND conf [(n2w 0); (n2w 0); n1; n0]) written)
         else SOME []
       | _ -> NONE
     else NONE`;;

let get_ag32_io_event_def = new_definition
  `get_ag32_io_event m =
     let call_id = m (n2w (ffi_code_start_offset - 1)) in
     if call_id = n2w (THE (ALOOKUP FFI_codes (implode "write"))) then
       if m (n2w output_offset) = (n2w 0) then
         let n1 = m (n2w (output_offset + 10)) in
         let n0 = m (n2w (output_offset + 11)) in
         let n = MIN (w22n [n1; n0]) output_buffer_size in
           read_bytearray (n2w output_offset) (8 + 4 + n) (SOME o m)
       else SOME []
     else NONE`;;

(* HOL4 ag32_basis_ffiProofScript.sml:763: ML code, not ported *)

let target_state_rel_ag32_init = prove
 (`is_ag32_init_state m ms ==>
   target_state_rel ag32_target
    (ag32_init_asm_state m md) ms`,
  CHEAT_TAC);;

let stdin_fs_def = new_definition
  `stdin_fs inp =
     mk_IO_fs
        [(UStream (implode "stdout"),""); (UStream (implode "stderr"),"");
          (UStream (implode "stdin"),inp)] []
        [(0,UStream (implode "stdin"),ReadMode,0); (1,UStream (implode
          "stdout"),WriteMode,0); (2,UStream (implode
          "stderr"),WriteMode,0)] (LGENLIST (K output_buffer_size) NONE) 2`;;

let wfFS_stdin_fs = prove
 (`wfFS (stdin_fs inp)`,
  CHEAT_TAC);;

let STD_streams_stdin_fs = prove
 (`STD_streams (stdin_fs inp)`,
  CHEAT_TAC);;

let ag32_fs_ok_def = new_definition
  `ag32_fs_ok fs <=>
    (IO_fs_numchars fs = LGENLIST (K output_buffer_size) NONE) /\
    (!fd. IS_SOME (ALOOKUP (IO_fs_infds fs) fd) <=> fd < 3) /\
    (
     // this needs to change for close
     !fd ino md off.
      (ALOOKUP (IO_fs_infds fs) fd = SOME (ino,md,off)) ==>
      (?cnt. (ALOOKUP (IO_fs_inode_tbl fs) ino = SOME cnt) /\ (fd IN {1,2}
        ==> (off = LENGTH cnt)))) /\
    (!fnm. ALOOKUP (IO_fs_inode_tbl fs) (File fnm) = NONE) /\ IO_fs_maxFD
     // maybe
     fs <= 2 /\
    STD_streams fs`;;

let ag32_stdin_implemented_def = new_definition
  `ag32_stdin_implemented fs m <=>
     (?off inp.
       (ALOOKUP (IO_fs_infds fs) 0 = SOME (UStream (implode
         "stdin"),ReadMode,off)) /\
       (ALOOKUP (IO_fs_inode_tbl fs) (UStream (implode "stdin")) = SOME inp)
         /\
       (get_mem_word m (n2w stdin_offset) = n2w off) /\
       (get_mem_word m (n2w (stdin_offset + 4)) = n2w (LENGTH inp)) /\
       off <= LENGTH inp /\ LENGTH inp <= stdin_size /\
       bytes_in_memory (n2w (stdin_offset + 8)) (MAP (n2w o ORD) inp)
         m (all_words (n2w (stdin_offset + 8)) (LENGTH inp)))`;;

let ag32_cline_implemented_def = new_definition
  `ag32_cline_implemented cl m <=>
     (get_mem_word m (n2w startup_code_size) = n2w (LENGTH cl)) /\
     SUM (MAP strlen cl) + LENGTH cl <= cline_size /\
     ALL validArg cl /\ ~(cl = []) /\
     bytes_in_memory (n2w (startup_code_size + 4))
       (FLAT (MAP (SNOC (n2w 0)) (MAP (MAP (n2w o ORD) o explode) cl)))
       m (all_words (n2w (startup_code_size + 4)) (SUM (MAP strlen cl) +
         LENGTH cl))`;;

let ag32_ffi_rel_def = new_definition
  `ag32_ffi_rel ms ffi <=>
     (MAP get_ag32_io_event (ffi_state_io_events ms) =
      MAP get_output_io_event (ffi_state_io_events ffi)) /\
     (ffi_state_oracle ffi = basis_ffi_oracle no_ext) /\
     (ag32_fs_ok (SND (ffi_state_ffi_state ffi))) /\
     (ag32_stdin_implemented (SND (ffi_state_ffi_state ffi)) (?_MEM ms)) /\
     (ag32_cline_implemented (FST (ffi_state_ffi_state ffi)) (?_MEM ms))`;;

let extract_write_def = new_definition
  `extract_write fd oevent =
     if NULL oevent then NONE else let conf = TAKE 8 oevent in
       if (w82n conf = fd) then
         SOME (DROP (8 + 4) oevent)
       else NONE`;;

let extract_writes_def = new_definition
  `extract_writes fd oevents =
     FLAT (MAP (MAP (CHR o w2n) o THE) (FILTER IS_SOME (MAP (hol4_C
       OPTION_BIND (extract_write fd)) oevents)))`;;

(* [local] *)
let no_ext_apply = prove
 (`no_ext nm st conf bs = Oracle_final FFI_failed`,
  CHEAT_TAC);;
add_simp no_ext_apply;;

(* TODO: why is this proof so slow? make it faster? *)
let extract_fs_extract_writes = prove
 (`!ls fs fs' off off' out rest.
   (extract_fs no_ext (cls,fs) ls = SOME fs') /\
   (IO_fs_numchars
    // can only read/write up to output_buffer_size - this could be made more nuanced
    fs = LGENLIST (K output_buffer_size) NONE) /\
   (
    // UStream of interest exists at the start
    ALOOKUP (IO_fs_infds fs) fd = SOME (UStream nam,WriteMode,LENGTH out))
      /\
   (ALOOKUP (IO_fs_inode_tbl fs) (UStream nam) = SOME out) /\
   (
    // no non-UStream files
    !ino. ALOOKUP (IO_fs_inode_tbl fs) (File ino) = NONE) /\
   (
    // well-formedness invariants for the filesystem
    !fd fnm md off. ~(ALOOKUP (IO_fs_infds fs') fd = SOME (File
      fnm,md,off))) /\
   (!fd1 nm md1 off1 fd2 md2 off2.
     (
      // this one depends on us not being able to open UStreams
      ALOOKUP (IO_fs_infds fs') fd1 = SOME (UStream nm,md1,off1)) /\
     (ALOOKUP (IO_fs_infds fs') fd2 = SOME (UStream nm,md2,off2)) ==> (fd1 =
       fd2)) /\
   (
    // --
    // nothing has changed except the UStream of interest -- is this actually necessary?
    !x. ~(x = fd) ==> (OPTREL (inv_image (=) FST) (ALOOKUP (IO_fs_infds fs')
      x) (ALOOKUP (IO_fs_infds fs) x))) /\
   (!fnm. inFS_fname fs' fnm = inFS_fname fs fnm) /\
   (
    // and it has only changed by appending
    ALOOKUP (IO_fs_infds fs') fd = SOME (UStream nam,WriteMode,LENGTH out +
      LENGTH rest)) /\
   (ALOOKUP (IO_fs_inode_tbl fs') (UStream nam) = SOME (APPEND out rest))
     ==>
   (extract_writes fd (MAP get_output_io_event ls) = rest)`,
  CHEAT_TAC);;


let ag32_ffi_write_thm = prove
 (`bytes_in_memory (?_R s (n2w 1)) conf (?_MEM s) md /\
   bytes_in_memory (?_R s (n2w 3)) bytes (?_MEM s) md /\
   Abbrev (md = ag32_prog_addresses (LENGTH ffi_names) lc ld) /\
   LENGTH ffi_names <= LENGTH FFI_codes /\
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size /\
   (w2n (?_R s (n2w 2)) = LENGTH conf) /\
   (w2n (?_R s (n2w 4)) = LENGTH bytes) /\ w2n (?_R s (n2w 3)) + LENGTH
     bytes < dimword (:32) /\
   (INDEX_OF (implode "write") ffi_names = SOME index) /\
   (ffi_write conf bytes fs = SOME (FFIreturn new_bytes fs')) /\
   ag32_fs_ok fs /\
   (?_PC s = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints
     (implode "write")))) ==>
   (ag32_ffi_write s = ag32_ffi_interfer ffi_names md (index,new_bytes,s))`,
  CHEAT_TAC);;

let ag32_ffi_read_thm = prove
 (`bytes_in_memory (?_R s (n2w 1)) conf (?_MEM s) md /\
   bytes_in_memory (?_R s (n2w 3)) bytes (?_MEM s) md /\
   Abbrev (md = ag32_prog_addresses (LENGTH ffi_names) lc ld) /\
   LENGTH ffi_names <= LENGTH FFI_codes /\
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size /\
   (w2n (?_R s (n2w 2)) = LENGTH conf) /\
   (w2n (?_R s (n2w 4)) = LENGTH bytes) /\ w2n (?_R s (n2w 3)) + LENGTH
     bytes < dimword (:32) /\
   (INDEX_OF (implode "read") ffi_names = SOME index) /\
   (ffi_read conf bytes fs = SOME (FFIreturn new_bytes fs')) /\
   ag32_fs_ok fs /\ ag32_stdin_implemented fs (?_MEM s) /\
   (?_PC s = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints
     (implode "read")))) ==>
   (ag32_ffi_read s = ag32_ffi_interfer ffi_names md (index,new_bytes,s))`,
  CHEAT_TAC);;

let ag32_ffi_get_arg_count_thm = prove
 (`bytes_in_memory (?_R s (n2w 1)) conf (?_MEM s) md /\
   bytes_in_memory (?_R s (n2w 3)) bytes (?_MEM s) md /\
   Abbrev (md = ag32_prog_addresses (LENGTH ffi_names) lc ld) /\
   LENGTH ffi_names <= LENGTH FFI_codes /\
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size /\
   (w2n (?_R s (n2w 2)) = LENGTH conf) /\
   (w2n (?_R s (n2w 4)) = LENGTH bytes) /\ w2n (?_R s (n2w 3)) + LENGTH
     bytes < dimword (:32) /\
   (INDEX_OF (implode "get_arg_count") ffi_names = SOME index) /\
   (ffi_get_arg_count conf bytes (cl:mlstring list) = SOME (FFIreturn
     new_bytes cl')) /\
   ag32_cline_implemented cl (?_MEM s) /\
   (?_PC s = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints
     (implode "get_arg_count")))) ==>
   (ag32_ffi_get_arg_count s = ag32_ffi_interfer ffi_names md
     (index,new_bytes,s))`,
  CHEAT_TAC);;

let get_mem_arg_thm = prove
 (`!cl i a.
   bytes_in_memory a (FLAT (MAP (SNOC (n2w 0)) cl)) m md /\
   i < LENGTH cl /\ ALL (ALL ((\x y. ~(x = y)) (n2w 0))) cl ==>
   get_mem_arg m a i = (a + n2w (SUM (MAP LENGTH (TAKE (i + 1) cl)) + i),
                        EL i cl)`,
  CHEAT_TAC);;

let ag32_ffi_get_arg_length_thm = prove
 (`bytes_in_memory (?_R s (n2w 1)) conf (?_MEM s) md /\
   bytes_in_memory (?_R s (n2w 3)) bytes (?_MEM s) md /\
   Abbrev (md = ag32_prog_addresses (LENGTH ffi_names) lc ld) /\
   LENGTH ffi_names <= LENGTH FFI_codes /\
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size /\
   (w2n (?_R s (n2w 2)) = LENGTH conf) /\
   (w2n (?_R s (n2w 4)) = LENGTH bytes) /\ w2n (?_R s (n2w 3)) + LENGTH
     bytes < dimword (:32) /\
   (INDEX_OF (implode "get_arg_length") ffi_names = SOME index) /\
   (ffi_get_arg_length conf bytes (cl:mlstring list) = SOME (FFIreturn
     new_bytes cl')) /\
   ag32_cline_implemented cl (?_MEM s) /\
   (?_PC s = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints
     (implode "get_arg_length")))) ==>
   (ag32_ffi_get_arg_length s = ag32_ffi_interfer ffi_names md
     (index,new_bytes,s))`,
  CHEAT_TAC);;

let ag32_ffi_get_arg_thm = prove
 (`bytes_in_memory (?_R s (n2w 1)) conf (?_MEM s) md /\
   bytes_in_memory (?_R s (n2w 3)) bytes (?_MEM s) md /\
   Abbrev (md = ag32_prog_addresses (LENGTH ffi_names) lc ld) /\
   LENGTH ffi_names <= LENGTH FFI_codes /\
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size /\
   (w2n (?_R s (n2w 2)) = LENGTH conf) /\
   (w2n (?_R s (n2w 4)) = LENGTH bytes) /\ w2n (?_R s (n2w 3)) + LENGTH
     bytes < dimword (:32) /\
   (INDEX_OF (implode "get_arg") ffi_names = SOME index) /\
   (ffi_get_arg conf bytes (cl:mlstring list) = SOME (FFIreturn new_bytes
     cl')) /\
   ag32_cline_implemented cl (?_MEM s) /\
   (?_PC s = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints
     (implode "get_arg")))) ==>
   (ag32_ffi_get_arg s = ag32_ffi_interfer ffi_names md
     (index,new_bytes,s))`,
  CHEAT_TAC);;

let ag32_ffi_open_in_thm = prove
 (`bytes_in_memory (?_R s (n2w 1)) conf (?_MEM s) md /\
   bytes_in_memory (?_R s (n2w 3)) bytes (?_MEM s) md /\
   Abbrev (md = ag32_prog_addresses (LENGTH ffi_names) lc ld) /\
   LENGTH ffi_names <= LENGTH FFI_codes /\
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size /\
   (w2n (?_R s (n2w 2)) = LENGTH conf) /\
   (w2n (?_R s (n2w 4)) = LENGTH bytes) /\ w2n (?_R s (n2w 3)) + LENGTH
     bytes < dimword (:32) /\
   (INDEX_OF (implode "open_in") ffi_names = SOME index) /\
   (ffi_open_in conf bytes fs = SOME (FFIreturn new_bytes fs')) /\
   ag32_fs_ok fs /\
   (?_PC s = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints
     (implode "open_in")))) ==>
   (ag32_ffi_open_in s = ag32_ffi_interfer ffi_names md
     (index,new_bytes,s))`,
  CHEAT_TAC);;

let ag32_ffi_open_out_thm = prove
 (`bytes_in_memory (?_R s (n2w 1)) conf (?_MEM s) md /\
   bytes_in_memory (?_R s (n2w 3)) bytes (?_MEM s) md /\
   Abbrev (md = ag32_prog_addresses (LENGTH ffi_names) lc ld) /\
   LENGTH ffi_names <= LENGTH FFI_codes /\
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size /\
   (w2n (?_R s (n2w 2)) = LENGTH conf) /\
   (w2n (?_R s (n2w 4)) = LENGTH bytes) /\ w2n (?_R s (n2w 3)) + LENGTH
     bytes < dimword (:32) /\
   (INDEX_OF (implode "open_out") ffi_names = SOME index) /\
   (ffi_open_out conf bytes fs = SOME (FFIreturn new_bytes fs')) /\
   ag32_fs_ok fs /\
   (?_PC s = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints
     (implode "open_out")))) ==>
   (ag32_ffi_open_out s = ag32_ffi_interfer ffi_names md
     (index,new_bytes,s))`,
  CHEAT_TAC);;

let ag32_ffi_close_thm = prove
 (`bytes_in_memory (?_R s (n2w 1)) conf (?_MEM s) md /\
   bytes_in_memory (?_R s (n2w 3)) bytes (?_MEM s) md /\
   Abbrev (md = ag32_prog_addresses (LENGTH ffi_names) lc ld) /\
   LENGTH ffi_names <= LENGTH FFI_codes /\
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size /\
   (w2n (?_R s (n2w 2)) = LENGTH conf) /\
   (w2n (?_R s (n2w 4)) = LENGTH bytes) /\ w2n (?_R s (n2w 3)) + LENGTH
     bytes < dimword (:32) /\
   (INDEX_OF (implode "close") ffi_names = SOME index) /\
   (ffi_close conf bytes fs = SOME (FFIreturn new_bytes fs')) /\
   ag32_fs_ok fs /\
   (?_PC s = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints
     (implode "close")))) ==>
   (ag32_ffi_close s = ag32_ffi_interfer ffi_names md (index,new_bytes,s))`,
  CHEAT_TAC);;

let ag32_ffi__thm = prove
 (`bytes_in_memory (?_R s (n2w 1)) conf (?_MEM s) md /\
   bytes_in_memory (?_R s (n2w 3)) bytes (?_MEM s) md /\
   Abbrev (md = ag32_prog_addresses (LENGTH ffi_names) lc ld) /\
   LENGTH ffi_names <= LENGTH FFI_codes /\
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size /\
   (w2n (?_R s (n2w 2)) = LENGTH conf) /\
   (w2n (?_R s (n2w 4)) = LENGTH bytes) /\ w2n (?_R s (n2w 3)) + LENGTH
     bytes < dimword (:32) /\
   (INDEX_OF (implode "") ffi_names = SOME index) /\
   (?_PC s = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints
     (implode "")))) ==>
   (ag32_ffi_ s = ag32_ffi_interfer ffi_names md (index,bytes,s))`,
  CHEAT_TAC);;

let ag32_fs_ok_stdin_fs = prove
 (`ag32_fs_ok (stdin_fs inp)`,
  CHEAT_TAC);;

let ag32_ffi_rel_write_mem_update = prove
 (`(ffi_write conf bytes fs = SOME (FFIreturn new_bytes fs')) /\
   (m ((n2w (ffi_code_start_offset - 1)):word32) = n2w (THE (ALOOKUP
     FFI_codes (implode "write")))) /\
    ag32_fs_ok fs ==>
   (
    get_ag32_io_event
     (ag32_ffi_mem_update (implode "write") conf bytes new_bytes m) =
       get_output_io_event (IO_event (ffi_ExtCall (implode "write")) conf
       (ZIP bytes new_bytes)))`,
  CHEAT_TAC);;

let ag32_fs_ok_ffi_write = prove
 (`(ffi_write conf bytes fs = SOME (FFIreturn bytes' fs')) /\ ag32_fs_ok fs ==>
   ag32_fs_ok fs'`,
  CHEAT_TAC);;

let ag32_stdin_implemented_ffi_write = prove
 (`STD_streams fs /\
   ag32_stdin_implemented fs m /\
   ffi_write conf bytes fs = SOME (FFIreturn bytes' fs') /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes' < 4294967296 /\
   n2w heap_start_offset <=+ ?_R ms (n2w 3) ==>
   ag32_stdin_implemented fs'
   (ag32_ffi_mem_update (implode "write") conf bytes bytes'
     (asm_write_bytearray (?_R ms (n2w 3)) bytes'
       ((n2w (ffi_code_start_offset - 1) =+
         n2w (THE (ALOOKUP FFI_codes (implode "write")))) m)))`,
  CHEAT_TAC);;

let ag32_cline_implemented_ffi_write = prove
 (`ag32_cline_implemented cl m /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes' < dimword (:32) /\
   n2w heap_start_offset <=+ ?_R ms (n2w 3) /\
   (ffi_write conf bytes fs = SOME (FFIreturn bytes' fs')) ==>
   ag32_cline_implemented cl
     (ag32_ffi_mem_update (implode "write") conf bytes bytes'
       (asm_write_bytearray (?_R ms (n2w 3)) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes (implode "write")))) m)))`,
  CHEAT_TAC);;

let ag32_ffi_rel_read_mem_update = prove
 (`(ffi_read conf bytes fs = SOME (FFIreturn new_bytes fs')) /\
   (m ((n2w (ffi_code_start_offset - 1)):word32) = n2w (THE (ALOOKUP
     FFI_codes (implode "read")))) /\
    ag32_fs_ok fs ==>
   (
    get_ag32_io_event
     (ag32_ffi_mem_update (implode "read") conf bytes new_bytes m) =
       get_output_io_event (IO_event (ffi_ExtCall (implode "read")) conf (ZIP
       bytes new_bytes)))`,
  CHEAT_TAC);;

let ag32_fs_ok_ffi_read = prove
 (`(ffi_read conf bytes fs = SOME (FFIreturn bytes' fs')) /\ ag32_fs_ok fs ==>
   ag32_fs_ok fs'`,
  CHEAT_TAC);;

let ag32_stdin_implemented_ffi_read = prove
 (`ag32_fs_ok fs /\
   ag32_stdin_implemented fs m /\
   ffi_read conf bytes fs = SOME (FFIreturn bytes' fs') /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes' < 4294967296 /\
   n2w heap_start_offset <=+ ?_R ms (n2w 3) ==>
   // you may assume more here from the context where this is used
   ag32_stdin_implemented fs'
     (ag32_ffi_mem_update (implode "read") conf bytes bytes'
       (asm_write_bytearray (?_R ms (n2w 3)) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes (implode "read")))) m)))`,
  CHEAT_TAC);;

let ag32_cline_implemented_ffi_read = prove
 (`ag32_cline_implemented cl m /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes' < dimword (:32) /\
   n2w heap_start_offset <=+ ?_R ms (n2w 3) /\
   (ffi_read conf bytes fs = SOME (FFIreturn bytes' fs')) ==>
   ag32_cline_implemented cl
     (ag32_ffi_mem_update (implode "read") conf bytes bytes'
       (asm_write_bytearray (?_R ms (n2w 3)) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes (implode "read")))) m)))`,
  CHEAT_TAC);;

let ag32_fs_ok_ffi_open_in = prove
 (`(ffi_open_in conf bytes fs = SOME (FFIreturn bytes' fs')) /\ ag32_fs_ok fs
  ==>
   ag32_fs_ok fs'`,
  CHEAT_TAC);;

let ag32_fs_ok_ffi_open_out = prove
 (`(ffi_open_out conf bytes fs = SOME (FFIreturn bytes' fs')) /\ ag32_fs_ok fs
  ==>
   ag32_fs_ok fs'`,
  CHEAT_TAC);;

let ag32_fs_ok_ffi_close = prove
 (`(ffi_close conf bytes fs = SOME (FFIreturn bytes' fs')) /\ ag32_fs_ok fs ==>
   ag32_fs_ok fs'`,
  CHEAT_TAC);;

let ag32_stdin_implemented_ffi_open_in = prove
 (`ag32_fs_ok fs /\
   ag32_stdin_implemented fs m /\
   ffi_open_in conf bytes fs = SOME (FFIreturn bytes' fs') /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes' < 4294967296 /\
   n2w heap_start_offset <=+ ?_R ms (n2w 3) ==>
   ag32_stdin_implemented fs'
     (asm_write_bytearray (?_R ms (n2w 3)) bytes'
       ((n2w (ffi_code_start_offset - 1) =+
         n2w (THE (ALOOKUP FFI_codes (implode "open_in")))) m))`,
  CHEAT_TAC);;

let ag32_cline_implemented_ffi_open_in = prove
 (`ag32_cline_implemented cl m /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes' < dimword (:32) /\
   n2w heap_start_offset <=+ ?_R ms (n2w 3) /\
   (ffi_open_in conf bytes fs = SOME (FFIreturn bytes' fs')) ==>
   ag32_cline_implemented cl
       (asm_write_bytearray (?_R ms (n2w 3)) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes (implode "open_in")))) m))`,
  CHEAT_TAC);;

let ag32_stdin_implemented_ffi_open_out = prove
 (`ag32_fs_ok fs /\
   ag32_stdin_implemented fs m /\
   ffi_open_out conf bytes fs = SOME (FFIreturn bytes' fs') /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes' < 4294967296 /\
   n2w heap_start_offset <=+ ?_R ms (n2w 3) ==>
   ag32_stdin_implemented fs'
     (asm_write_bytearray (?_R ms (n2w 3)) bytes'
       ((n2w (ffi_code_start_offset - 1) =+
         n2w (THE (ALOOKUP FFI_codes (implode "open_out")))) m))`,
  CHEAT_TAC);;

let ag32_cline_implemented_ffi_open_out = prove
 (`ag32_cline_implemented cl m /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes' < dimword (:32) /\
   n2w heap_start_offset <=+ ?_R ms (n2w 3) /\
   (ffi_open_out conf bytes fs = SOME (FFIreturn bytes' fs')) ==>
   ag32_cline_implemented cl
       (asm_write_bytearray (?_R ms (n2w 3)) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes (implode "open_out")))) m))`,
  CHEAT_TAC);;

let ag32_stdin_implemented_ffi_close = prove
 (`ag32_fs_ok fs /\
   ag32_stdin_implemented fs m /\
   ffi_close conf bytes fs = SOME (FFIreturn bytes' fs') /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes' < 4294967296 /\
   n2w heap_start_offset <=+ ?_R ms (n2w 3) ==>
   ag32_stdin_implemented fs'
     (asm_write_bytearray (?_R ms (n2w 3)) bytes'
       ((n2w (ffi_code_start_offset - 1) =+
         n2w (THE (ALOOKUP FFI_codes (implode "close")))) m))`,
  CHEAT_TAC);;

let ag32_cline_implemented_ffi_close = prove
 (`ag32_cline_implemented cl m /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes' < dimword (:32) /\
   n2w heap_start_offset <=+ ?_R ms (n2w 3) /\
   (ffi_close conf bytes fs = SOME (FFIreturn bytes' fs')) ==>
   ag32_cline_implemented cl
       (asm_write_bytearray (?_R ms (n2w 3)) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes (implode "close")))) m))`,
  CHEAT_TAC);;

let ag32_stdin_implemented_ffi_get_arg_count = prove
 (`ag32_stdin_implemented fs m /\
   ffi_get_arg_count conf bytes (cl:mlstring list) = SOME (FFIreturn bytes'
     cl') /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes' < 4294967296 /\
   n2w heap_start_offset <=+ ?_R ms (n2w 3) ==>
   ag32_stdin_implemented fs
     (asm_write_bytearray (?_R ms (n2w 3)) bytes'
       ((n2w (ffi_code_start_offset - 1) =+
         n2w (THE (ALOOKUP FFI_codes (implode "get_arg_count")))) m))`,
  CHEAT_TAC);;

let ag32_cline_implemented_ffi_get_arg_count = prove
 (`ag32_cline_implemented cl m /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes' < dimword (:32) /\
   n2w heap_start_offset <=+ ?_R ms (n2w 3) /\
   (ffi_get_arg_count conf bytes cl = SOME (FFIreturn bytes' cl')) ==>
   ag32_cline_implemented cl'
       (asm_write_bytearray (?_R ms (n2w 3)) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes (implode "get_arg_count")))) m))`,
  CHEAT_TAC);;

let ag32_stdin_implemented_ffi_get_arg_length = prove
 (`ag32_stdin_implemented fs m /\
   ffi_get_arg_length conf bytes (cl:mlstring list) = SOME (FFIreturn bytes'
     cl') /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes' < 4294967296 /\
   n2w heap_start_offset <=+ ?_R ms (n2w 3) ==>
   ag32_stdin_implemented fs
     (asm_write_bytearray (?_R ms (n2w 3)) bytes'
       ((n2w (ffi_code_start_offset - 1) =+
         n2w (THE (ALOOKUP FFI_codes (implode "get_arg_length")))) m))`,
  CHEAT_TAC);;

let ag32_cline_implemented_ffi_get_arg_length = prove
 (`ag32_cline_implemented cl m /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes' < dimword (:32) /\
   n2w heap_start_offset <=+ ?_R ms (n2w 3) /\
   (ffi_get_arg_length conf bytes cl = SOME (FFIreturn bytes' cl')) ==>
   ag32_cline_implemented cl'
       (asm_write_bytearray (?_R ms (n2w 3)) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes (implode "get_arg_length")))) m))`,
  CHEAT_TAC);;

(* TODO: many of these theorems could be deduplicated: the assumptions
         differing between them might not even be necessary *)
let ag32_stdin_implemented_ffi_get_arg = prove
 (`ag32_stdin_implemented fs m /\
   ffi_get_arg conf bytes (cl:mlstring list) = SOME (FFIreturn bytes' cl')
     /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes' < 4294967296 /\
   n2w heap_start_offset <=+ ?_R ms (n2w 3) ==>
   ag32_stdin_implemented fs
     (asm_write_bytearray (?_R ms (n2w 3)) bytes'
       ((n2w (ffi_code_start_offset - 1) =+
         n2w (THE (ALOOKUP FFI_codes (implode "get_arg")))) m))`,
  CHEAT_TAC);;

let ag32_cline_implemented_ffi_get_arg = prove
 (`ag32_cline_implemented cl m /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes' < dimword (:32) /\
   n2w heap_start_offset <=+ ?_R ms (n2w 3) /\
   (ffi_get_arg conf bytes cl = SOME (FFIreturn bytes' cl')) ==>
   ag32_cline_implemented cl'
       (asm_write_bytearray (?_R ms (n2w 3)) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes (implode "get_arg")))) m))`,
  CHEAT_TAC);;

let ag32_ffi_interfer_write = prove
 (`ag32_ffi_rel ms ffi /\
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME
     conf,SOME bytes)) /\
   (call_FFI ffi (ffi_ExtCall (implode "write")) conf bytes = FFI_return
     ffi' bytes') /\
   (INDEX_OF (implode "write") ffi_names = SOME index) /\ ALL_DISTINCT
     ffi_names /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes < dimword (:32) /\
   LENGTH ffi_names <= LENGTH FFI_codes /\
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size /\
   (?_PC ms = n2w (ffi_jumps_offset + (LENGTH ffi_names - 1 - index) *
     ffi_offset)) /\
   (!k. k < LENGTH (ag32_ffi_jumps ffi_names) ==>
        (
         get_mem_word (?_MEM ms) (n2w (ffi_jumps_offset + 4 * k)) = EL k
           (ag32_ffi_jumps ffi_names))) /\
   (!k. k < LENGTH ag32_ffi_write_code ==>
        (
         get_mem_word (?_MEM ms) (n2w (ffi_code_start_offset + THE (ALOOKUP
           ffi_entrypoints (implode "write")) + 4 * k)) = Encode (EL k
           ag32_ffi_write_code))) ==>
   (?k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = ITER k Next ms) /\
      ag32_ffi_rel (ITER k Next ms) ffi' /\
      (!x. ~(x IN ag32_ffi_mem_domain) /\ ~(x IN all_words (?_R ms (n2w 3))
        (LENGTH bytes)) ==>
          (?_MEM (ITER k Next ms) x = ?_MEM ms x)))`,
  CHEAT_TAC);;

let ag32_ffi_interfer_read = prove
 (`ag32_ffi_rel ms ffi /\ (SND (ffi_state_ffi_state ffi) = fs) /\
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME
     conf,SOME bytes)) /\
   (call_FFI ffi (ffi_ExtCall (implode "read")) conf bytes = FFI_return ffi'
     bytes') /\
   (INDEX_OF (implode "read") ffi_names = SOME index) /\ ALL_DISTINCT
     ffi_names /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes < dimword (:32) /\
   LENGTH ffi_names <= LENGTH FFI_codes /\
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size /\
   (?_PC ms = n2w (ffi_jumps_offset + (LENGTH ffi_names - (index + 1)) *
     ffi_offset)) /\
   (!k. k < LENGTH (ag32_ffi_jumps ffi_names) ==>
        (
         get_mem_word (?_MEM ms) (n2w (ffi_jumps_offset + 4 * k)) = EL k
           (ag32_ffi_jumps ffi_names))) /\
   (!k. k < LENGTH ag32_ffi_read_code ==>
        (
         get_mem_word (?_MEM ms) (n2w (ffi_code_start_offset + THE (ALOOKUP
           ffi_entrypoints (implode "read")) + 4 * k)) = Encode (EL k
           ag32_ffi_read_code))) ==>
   (?k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = ITER k Next ms) /\
      ag32_ffi_rel (ITER k Next ms) ffi' /\
      (!x. ~(x IN ag32_ffi_mem_domain) /\ ~(x IN all_words (?_R ms (n2w 3))
        (LENGTH bytes)) ==>
          (?_MEM (ITER k Next ms) x = ?_MEM ms x)))`,
  CHEAT_TAC);;

let ag32_ffi_interfer_open_in = prove
 (`ag32_ffi_rel ms ffi /\ (SND (ffi_state_ffi_state ffi) = fs) /\
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME
     conf,SOME bytes)) /\
   (call_FFI ffi (ffi_ExtCall (implode "open_in")) conf bytes = FFI_return
     ffi' bytes') /\
   (INDEX_OF (implode "open_in") ffi_names = SOME index) /\ ALL_DISTINCT
     ffi_names /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes < dimword (:32) /\
   LENGTH ffi_names <= LENGTH FFI_codes /\
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size /\
   (?_PC ms = n2w (ffi_jumps_offset + (LENGTH ffi_names - (index + 1)) *
     ffi_offset)) /\
   (!k. k < LENGTH (ag32_ffi_jumps ffi_names) ==>
        (
         get_mem_word (?_MEM ms) (n2w (ffi_jumps_offset + 4 * k)) = EL k
           (ag32_ffi_jumps ffi_names))) /\
   (!k. k < LENGTH ag32_ffi_open_in_code ==>
        (
         get_mem_word (?_MEM ms) (n2w (ffi_code_start_offset + THE (ALOOKUP
           ffi_entrypoints (implode "open_in")) + 4 * k)) = Encode (EL k
           ag32_ffi_open_in_code))) ==>
   (?k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = ITER k Next ms) /\
      ag32_ffi_rel (ITER k Next ms) ffi' /\
      (!x. ~(x IN ag32_ffi_mem_domain) /\ ~(x IN all_words (?_R ms (n2w 3))
        (LENGTH bytes)) ==>
          (?_MEM (ITER k Next ms) x = ?_MEM ms x)))`,
  CHEAT_TAC);;

let ag32_ffi_interfer_open_out = prove
 (`ag32_ffi_rel ms ffi /\ (SND (ffi_state_ffi_state ffi) = fs) /\
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME
     conf,SOME bytes)) /\
   (call_FFI ffi (ffi_ExtCall (implode "open_out")) conf bytes = FFI_return
     ffi' bytes') /\
   (INDEX_OF (implode "open_out") ffi_names = SOME index) /\ ALL_DISTINCT
     ffi_names /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes < dimword (:32) /\
   LENGTH ffi_names <= LENGTH FFI_codes /\
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size /\
   (?_PC ms = n2w (ffi_jumps_offset + (LENGTH ffi_names - (index + 1)) *
     ffi_offset)) /\
   (!k. k < LENGTH (ag32_ffi_jumps ffi_names) ==>
        (
         get_mem_word (?_MEM ms) (n2w (ffi_jumps_offset + 4 * k)) = EL k
           (ag32_ffi_jumps ffi_names))) /\
   (!k. k < LENGTH ag32_ffi_open_out_code ==>
        (
         get_mem_word (?_MEM ms) (n2w (ffi_code_start_offset + THE (ALOOKUP
           ffi_entrypoints (implode "open_out")) + 4 * k)) = Encode (EL k
           ag32_ffi_open_out_code))) ==>
   (?k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = ITER k Next ms) /\
      ag32_ffi_rel (ITER k Next ms) ffi' /\
      (!x. ~(x IN ag32_ffi_mem_domain) /\ ~(x IN all_words (?_R ms (n2w 3))
        (LENGTH bytes)) ==>
          (?_MEM (ITER k Next ms) x = ?_MEM ms x)))`,
  CHEAT_TAC);;

let ag32_ffi_interfer_close = prove
 (`ag32_ffi_rel ms ffi /\ (SND (ffi_state_ffi_state ffi) = fs) /\
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME
     conf,SOME bytes)) /\
   (call_FFI ffi (ffi_ExtCall (implode "close")) conf bytes = FFI_return
     ffi' bytes') /\
   (INDEX_OF (implode "close") ffi_names = SOME index) /\ ALL_DISTINCT
     ffi_names /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes < dimword (:32) /\
   LENGTH ffi_names <= LENGTH FFI_codes /\
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size /\
   (?_PC ms = n2w (ffi_jumps_offset + (LENGTH ffi_names - (index + 1)) *
     ffi_offset)) /\
   (!k. k < LENGTH (ag32_ffi_jumps ffi_names) ==>
        (
         get_mem_word (?_MEM ms) (n2w (ffi_jumps_offset + 4 * k)) = EL k
           (ag32_ffi_jumps ffi_names))) /\
   (!k. k < LENGTH ag32_ffi_close_code ==>
        (
         get_mem_word (?_MEM ms) (n2w (ffi_code_start_offset + THE (ALOOKUP
           ffi_entrypoints (implode "close")) + 4 * k)) = Encode (EL k
           ag32_ffi_close_code))) ==>
   (?k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = ITER k Next ms) /\
      ag32_ffi_rel (ITER k Next ms) ffi' /\
      (!x. ~(x IN ag32_ffi_mem_domain) /\ ~(x IN all_words (?_R ms (n2w 3))
        (LENGTH bytes)) ==>
          (?_MEM (ITER k Next ms) x = ?_MEM ms x)))`,
  CHEAT_TAC);;

(* HOL4 ag32_basis_ffiProofScript.sml:5222-5224: the ML values that the
   definitions below antiquote *)

let ag32_ffi_interfer_get_arg_count = prove
 (`ag32_ffi_rel ms ffi /\
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME
     conf,SOME bytes)) /\
   (call_FFI ffi (ffi_ExtCall (implode "get_arg_count")) conf bytes =
     FFI_return ffi' bytes') /\
   (INDEX_OF (implode "get_arg_count") ffi_names = SOME index)
     /\ ALL_DISTINCT ffi_names /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes < dimword (:32) /\
   LENGTH ffi_names <= LENGTH FFI_codes /\
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size /\
   (?_PC ms = n2w (ffi_jumps_offset + (LENGTH ffi_names - (index + 1)) *
     ffi_offset)) /\
   (!k. k < LENGTH (ag32_ffi_jumps ffi_names) ==>
        (
         get_mem_word (?_MEM ms) (n2w (ffi_jumps_offset + 4 * k)) = EL k
           (ag32_ffi_jumps ffi_names))) /\
   (!k. k < LENGTH ag32_ffi_get_arg_count_code ==>
        (
         get_mem_word (?_MEM ms) (n2w (ffi_code_start_offset + THE (ALOOKUP
           ffi_entrypoints (implode "get_arg_count")) + 4 * k)) = Encode (EL k
           ag32_ffi_get_arg_count_code))) ==>
   (?k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = ITER k Next ms) /\
      ag32_ffi_rel (ITER k Next ms) ffi' /\
      (!x. ~(x IN ag32_ffi_mem_domain) /\ ~(x IN all_words (?_R ms (n2w 3))
        (LENGTH bytes)) ==>
          (?_MEM (ITER k Next ms) x = ?_MEM ms x)))`,
  CHEAT_TAC);;

let cline_in_memory_has_n_args = prove
 (`!l cls a.
   bytes_in_memory a (FLAT (MAP (SNOC (n2w 0)) cls)) m md /\
   l <= LENGTH cls /\ ALL (ALL ((\x y. ~(x = y)) (n2w 0))) cls ==>
   has_n_args m a l`,
  CHEAT_TAC);;

let ag32_ffi_interfer_get_arg_length = prove
 (`ag32_ffi_rel ms ffi /\
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME
     conf,SOME bytes)) /\
   (call_FFI ffi (ffi_ExtCall (implode "get_arg_length")) conf bytes =
     FFI_return ffi' bytes') /\
   (INDEX_OF (implode "get_arg_length") ffi_names = SOME index)
     /\ ALL_DISTINCT ffi_names /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes < dimword (:32) /\
   LENGTH ffi_names <= LENGTH FFI_codes /\
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size /\
   (?_PC ms = n2w (ffi_jumps_offset + (LENGTH ffi_names - (index + 1)) *
     ffi_offset)) /\
   (!k. k < LENGTH (ag32_ffi_jumps ffi_names) ==>
        (
         get_mem_word (?_MEM ms) (n2w (ffi_jumps_offset + 4 * k)) = EL k
           (ag32_ffi_jumps ffi_names))) /\
   (!k. k < LENGTH ag32_ffi_get_arg_length_code ==>
        (
         get_mem_word (?_MEM ms) (n2w (ffi_code_start_offset + THE (ALOOKUP
           ffi_entrypoints (implode "get_arg_length")) + 4 * k)) = Encode (EL k
           ag32_ffi_get_arg_length_code))) ==>
   (?k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = ITER k Next ms) /\
      ag32_ffi_rel (ITER k Next ms) ffi' /\
      (!x. ~(x IN ag32_ffi_mem_domain) /\ ~(x IN all_words (?_R ms (n2w 3))
        (LENGTH bytes)) ==>
          (?_MEM (ITER k Next ms) x = ?_MEM ms x)))`,
  CHEAT_TAC);;

let ag32_ffi_interfer_get_arg = prove
 (`ag32_ffi_rel ms ffi /\
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME
     conf,SOME bytes)) /\
   (call_FFI ffi (ffi_ExtCall (implode "get_arg")) conf bytes = FFI_return
     ffi' bytes') /\
   (INDEX_OF (implode "get_arg") ffi_names = SOME index) /\ ALL_DISTINCT
     ffi_names /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes < dimword (:32) /\
   LENGTH ffi_names <= LENGTH FFI_codes /\
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size /\
   (?_PC ms = n2w (ffi_jumps_offset + (LENGTH ffi_names - (index + 1)) *
     ffi_offset)) /\
   (!k. k < LENGTH (ag32_ffi_jumps ffi_names) ==>
        (
         get_mem_word (?_MEM ms) (n2w (ffi_jumps_offset + 4 * k)) = EL k
           (ag32_ffi_jumps ffi_names))) /\
   (!k. k < LENGTH ag32_ffi_get_arg_code ==>
        (
         get_mem_word (?_MEM ms) (n2w (ffi_code_start_offset + THE (ALOOKUP
           ffi_entrypoints (implode "get_arg")) + 4 * k)) = Encode (EL k
           ag32_ffi_get_arg_code))) ==>
   (?k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = ITER k Next ms) /\
      ag32_ffi_rel (ITER k Next ms) ffi' /\
      (!x. ~(x IN ag32_ffi_mem_domain) /\ ~(x IN all_words (?_R ms (n2w 3))
        (LENGTH bytes)) ==>
          (?_MEM (ITER k Next ms) x = ?_MEM ms x)))`,
  CHEAT_TAC);;

let ag32_ffi_interfer_ = prove
 (`ag32_ffi_rel ms ffi /\
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME
     conf,SOME bytes)) /\
   (call_FFI ffi (ffi_ExtCall (implode "")) conf bytes = FFI_return ffi'
     bytes') /\
   (INDEX_OF (implode "") ffi_names = SOME index) /\ ALL_DISTINCT ffi_names
     /\
   w2n (?_R ms (n2w 3)) + LENGTH bytes < dimword (:32) /\
   LENGTH ffi_names <= LENGTH FFI_codes /\
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size /\
   (?_PC ms = n2w (ffi_jumps_offset + (LENGTH ffi_names - (index + 1)) *
     ffi_offset)) /\
   (!k. k < LENGTH (ag32_ffi_jumps ffi_names) ==>
        (
         get_mem_word (?_MEM ms) (n2w (ffi_jumps_offset + 4 * k)) = EL k
           (ag32_ffi_jumps ffi_names))) /\
   (!k. k < LENGTH ag32_ffi__code ==>
        (
         get_mem_word (?_MEM ms) (n2w (ffi_code_start_offset + THE (ALOOKUP
           ffi_entrypoints (implode "")) + 4 * k)) = Encode (EL k
           ag32_ffi__code))) ==>
   (?k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = ITER k Next ms) /\
      ag32_ffi_rel (ITER k Next ms) ffi' /\
      (!x. ~(x IN ag32_ffi_mem_domain) /\ ~(x IN all_words (?_R ms (n2w 3))
        (LENGTH bytes)) ==>
          (?_MEM (ITER k Next ms) x = ?_MEM ms x)))`,
  CHEAT_TAC);;

let SUBSET_ffi_names_IMP_LENGTH_LESS_EQ = prove
 (`set_of_list ffi_names SUBSET set_of_list (MAP FST ffi_exitpcs)
  /\ ALL_DISTINCT ffi_names ==> LENGTH ffi_names <= LENGTH FFI_codes`,
  CHEAT_TAC);;

let ag32_good_init_state = prove
 (`SUM (MAP strlen cl) + LENGTH cl <= cline_size /\
   LENGTH inp <= stdin_size /\
   set_of_list ffi_names SUBSET set_of_list (MAP FST ffi_exitpcs)
     /\ ALL_DISTINCT ffi_names /\
   code_start_offset (LENGTH ffi_names) + LENGTH code + 4 * LENGTH data <
     memory_size /\
   byte_aligned ((n2w (LENGTH code)):word32) /\
   is_ag32_init_state (ag32_memory_init_memory code data ffi_names (cl,inp))
     ms0 /\
   target_state_rel ag32_target (init_asm_state code data ffi_names
     (cl,inp))
     (ITER startup_clock Next ms0) /\
   (!x. ~(x IN ag32_startup_addresses) ==>
      (?_MEM (ITER startup_clock Next ms0) x = ?_MEM ms0 x)) ==>
   good_init_state (ag32_machine_config ffi_names (LENGTH code) (LENGTH
     data))
     (ITER startup_clock Next ms0)
     code 0
     (mem_domain_fupd (K (machine_config_prog_addresses (ag32_machine_config
       ffi_names (LENGTH code) (LENGTH data)))) (init_asm_state code data
       ffi_names (cl,inp)))
     (\k. word_Word
       (word_of_bytes F (n2w 0) (list_of_seq (\i. mem (init_asm_state code
         data ffi_names (cl,inp)) (k + n2w i)) 4)))
       (
        {w | regs (init_asm_state code data ffi_names (cl,inp)) 2 <=+ w /\
             w <+ regs (init_asm_state code data ffi_names (cl,inp)) 4}
               UNION {w | n2w (code_start_offset (LENGTH ffi_names) + LENGTH
               code) <=+ w /\
               w <+ n2w (code_start_offset (LENGTH ffi_names) + LENGTH code
                 + 4 * LENGTH data)})
       {}`,
  CHEAT_TAC);;

(* TODO more things can be pulled out of here *)
let ag32_installed = prove
 (`SUM (MAP strlen cl) + LENGTH cl <= cline_size /\
   LENGTH inp <= stdin_size /\
   set_of_list ffi_names SUBSET set_of_list (MAP FST ffi_exitpcs)
     /\ ALL_DISTINCT ffi_names /\
   code_start_offset (LENGTH ffi_names) + LENGTH code + 4 * LENGTH data <
     memory_size /\
   byte_aligned ((n2w (LENGTH code)):word32) /\
   is_ag32_init_state (ag32_memory_init_memory code data ffi_names (cl,inp))
     ms0 /\
   target_state_rel ag32_target
     (init_asm_state code data ffi_names (cl,inp))
     (ITER startup_clock Next ms0) /\
   (!x. ~(x IN ag32_startup_addresses) ==>
       (?_MEM (ITER startup_clock Next ms0) x = ?_MEM ms0 x)) ==>
   installed code 0 data 0 (SOME (MAP ffi_ExtCall ffi_names))
     (heap_regs (stack_to_lab_config_reg_names (backend_config_stack_conf
       ag32_backend_config)))
     (ag32_machine_config ffi_names (LENGTH code) (LENGTH data)) []
     (ITER startup_clock Next ms0)`,
  CHEAT_TAC);;

let ag32_halted = prove
 (`!ms.
    SUM (MAP strlen cl) + LENGTH cl <= cline_size /\
    LENGTH inp <= stdin_size /\
    LENGTH ffi_names <= LENGTH FFI_codes /\
    (mc = ag32_machine_config ffi_names (LENGTH code) (LENGTH data)) /\
    (?_PC ms = machine_config_halt_pc mc) /\
    (!x. machine_config_halt_pc mc <=+ x /\ x <+ machine_config_halt_pc mc +
      (n2w 16) ==>
         (target_get_byte (machine_config_target mc) ms x =
           (ag32_memory_init_memory code data ffi_names (cl,inp)) x)) ==>
    (!k. (ffi_state_io_events (ITER k Next ms) = ffi_state_io_events ms) /\
        (?_PC (ITER k Next ms) = ?_PC ms) /\
        (?_MEM (ITER k Next ms) = ?_MEM ms) /\
        (!w. ~(w = (n2w 0)) ==> (?_R (ITER k Next ms) w = ?_R ms w)))`,
  CHEAT_TAC);;

(* HOL4 ag32_basis_ffiProofScript.sml:6799-6909: a proof *)

let ag32_interference_implemented = prove
 (`SUM (MAP strlen cl) + LENGTH cl <= cline_size /\
   LENGTH inp <= stdin_size /\
   set_of_list ffi_names SUBSET set_of_list (MAP FST ffi_exitpcs)
     /\ ALL_DISTINCT ffi_names /\
   code_start_offset (LENGTH ffi_names) + LENGTH code + 4 * LENGTH data <
     memory_size /\
   is_ag32_init_state (ag32_memory_init_memory code data ffi_names (cl,inp))
     ms0 /\
   Abbrev (ms = ITER startup_clock Next ms0) /\
   (!x. ~(x IN ag32_startup_addresses) ==> (?_MEM ms x = ?_MEM ms0 x)) ==>
   interference_implemented
    (ag32_machine_config ffi_names (LENGTH code) (LENGTH data))
    (ag32_ffi_rel)
    (ag32_ffi_mem_domain) ms`,
  CHEAT_TAC);;

let ag32_next = prove
 (`SUM (MAP strlen cl) + LENGTH cl <= cline_size /\ wfcl cl /\
   LENGTH inp <= stdin_size /\
   set_of_list ffi_names SUBSET set_of_list (MAP FST ffi_exitpcs)
     /\ ALL_DISTINCT ffi_names /\
   code_start_offset (LENGTH ffi_names) + LENGTH code + 4 * LENGTH data <
     memory_size /\
   is_ag32_init_state (ag32_memory_init_memory code data ffi_names (cl,inp))
     ms0 /\
   Abbrev (ms = ITER startup_clock Next ms0) /\
   (ffi_state_io_events ms = ffi_state_io_events ms0) /\
   (!x. ~(x IN ag32_startup_addresses) ==> (?_MEM ms x = ?_MEM ms0 x)) /\
   targetSem_machine_sem (ag32_machine_config ffi_names (LENGTH code)
     (LENGTH data)) (basis_ffi no_ext cl (stdin_fs inp))
     ms SUBSET extend_with_resource_limit {ffi_Terminate ffi_Success
       io_events} ==>
   (?k1. !k. k1 <= k ==>
     (let ms = ITER k Next ms0 in
     let outs = MAP (get_ag32_io_event) (ffi_state_io_events ms) in
       (?_PC ms = machine_config_halt_pc (ag32_machine_config ffi_names
         (LENGTH code) (LENGTH data))) /\
       (get_mem_word (?_MEM ms) (?_PC ms) = Encode (asm_Jump (fAdd,(n2w
         0),Imm (n2w 0)))) /\
       outs <<= MAP get_output_io_event io_events /\
       ((?_R ms (n2w (machine_config_ptr_reg (ag32_machine_config ffi_names
         (LENGTH code) (LENGTH data)))) = (n2w 0)) ==>
        (outs = MAP get_output_io_event io_events))))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["context";
   "not"];;

(* and the interface *)
let _ = unhide_overloads ();;
