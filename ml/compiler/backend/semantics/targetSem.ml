(* ======================================================== *)
(*  targetSem: ported from HOL4's
    compiler/backend/semantics/targetSemScript.sml  *)
(* ======================================================== *)

(*
  The formal semantics of the target machine language. This semantics
  is parametrised by the target configuration, which includes the next
  state function of the target architecture.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/encoders/asm/asmProps.ml";;
needs "compiler/encoders/asm/asmSem.ml";;
needs "lib/alignment.ml";;
needs "lib/byte.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/evaluateProps.ml";;

(* -- execute target machine with interference from environment -- *)

let machine_result_INDUCT,machine_result_RECURSION = define_datatype
  "machine_result = targetSem_Halt (outcome) | targetSem_Error | \
   targetSem_TimeOut";;
hol4_overload "Halt" "targetSem_Halt";;
hol4_overload "Error" "targetSem_Error";;
hol4_overload "TimeOut" "targetSem_TimeOut";;

let machine_config_FIELDS = define_record "machine_config"
  ["prog_addresses","'a word->bool";
   "shared_addresses","'a word->bool";
   "ffi_entry_pcs","('a word) list";
   "ffi_names","ffiname list";
   "ptr_reg","num";
   "len_reg","num";
   "ptr2_reg","num";
   "len2_reg","num";
   "ffi_interfer","num->num#word8 list#'b->'b";
   "callee_saved_regs","num list";
   "next_interfer","num->'b->'b";
   "halt_pc","'a word";
   "ccache_pc","'a word";
   "ccache_interfer","num->'a word#'a word#'b->'b";
   "target","('a,'b,'c)target";
   "mmio_info","(num#word8#'a asm_addr#num#'a word) list"];;
hol4_overload "ffi_names" "machine_config_ffi_names";;
hol4_overload "ffi_names_fupd" "machine_config_ffi_names_fupd";;
hol4_overload "ptr_reg" "machine_config_ptr_reg";;
hol4_overload "ptr_reg_fupd" "machine_config_ptr_reg_fupd";;
hol4_overload "len_reg" "machine_config_len_reg";;
hol4_overload "len_reg_fupd" "machine_config_len_reg_fupd";;
hol4_overload "ptr2_reg" "machine_config_ptr2_reg";;
hol4_overload "ptr2_reg_fupd" "machine_config_ptr2_reg_fupd";;
hol4_overload "len2_reg" "machine_config_len2_reg";;
hol4_overload "len2_reg_fupd" "machine_config_len2_reg_fupd";;

let apply_oracle_def = cake_define
  `apply_oracle oracle' x =
     (oracle' (0:num) x,misc_shift_seq 1 oracle')`;;

let encoded_bytes_in_mem_def = cake_define
  `encoded_bytes_in_mem c pc' m md <=>
     (?i k. k * (2 EXP asm_config_code_alignment c) < LENGTH
       (asm_config_encode c i) /\
       bytes_in_memory pc'
         (DROP (k * (2 EXP asm_config_code_alignment c))
           (asm_config_encode c i))
         m md)`;;

let read_ffi_bytearray_def = cake_define
  `read_ffi_bytearray mc ptr_reg' len_reg' ms =
     read_bytearray (target_get_reg (machine_config_target mc) ms
       ptr_reg')
       (w2n (target_get_reg (machine_config_target mc) ms len_reg'))
       (\a.
         if a IN machine_config_prog_addresses mc then
           SOME (target_get_byte (machine_config_target mc) ms a)
             else NONE)`;;

let read_ffi_bytearrays_def = cake_define
  `read_ffi_bytearrays mc ms =
     (read_ffi_bytearray mc (machine_config_ptr_reg mc)
       (machine_config_len_reg mc) ms,
      read_ffi_bytearray mc (machine_config_ptr2_reg mc)
        (machine_config_len2_reg mc) ms)`;;

let is_valid_mapped_read_def = cake_define
  `is_valid_mapped_read pc' (nb:word8) (ad:'a asm_addr) r pc' t ms md =
     (if nb = (n2w 1) then
       (bytes_in_memory pc' (asm_config_encode (target_config t)
         (Inst (asm_Mem asm_Load8 r ad)))
         (target_get_byte t ms) md) else if nb = (n2w 0) then
       (bytes_in_memory pc' (asm_config_encode (target_config t)
         (Inst (asm_Mem asm_Load r ad)))
         (target_get_byte t ms) md) else if nb = (n2w 2) then
       (bytes_in_memory pc' (asm_config_encode (target_config t)
         (Inst (asm_Mem asm_Load16 r ad)))
         (target_get_byte t ms) md) else if nb = (n2w 4) then
       (bytes_in_memory pc' (asm_config_encode (target_config t)
         (Inst (asm_Mem asm_Load32 r ad)))
         (target_get_byte t ms) md) else F)`;;

let is_valid_mapped_write_def = cake_define
  `is_valid_mapped_write pc' (nb:word8) (ad:'a asm_addr) r pc' t ms md =
     (if nb = (n2w 1) then
         (bytes_in_memory pc' (asm_config_encode (target_config t)
           (Inst (asm_Mem asm_Store8 r ad)))
           (target_get_byte t ms) md) else if nb = (n2w 0) then
         (bytes_in_memory pc' (asm_config_encode (target_config t)
           (Inst (asm_Mem asm_Store r ad)))
           (target_get_byte t ms) md) else if nb = (n2w 2) then
         (bytes_in_memory pc' (asm_config_encode (target_config t)
           (Inst (asm_Mem asm_Store16 r ad)))
           (target_get_byte t ms) md) else if nb = (n2w 4) then
         (bytes_in_memory pc' (asm_config_encode (target_config t)
           (Inst (asm_Mem asm_Store32 r ad)))
           (target_get_byte t ms) md) else F)`;;

let evaluate_def = cake_define
  `targetSem_evaluate (mc:('b,'a,'c)machine_config) (ffi:'ffi ffi_state)
  k (ms:'a) =
     (if k = 0 then (TimeOut,ms,ffi) else
       if (target_get_pc (machine_config_target mc) ms) IN
         (machine_config_prog_addresses mc DIFF (set_of_list
         (machine_config_ffi_entry_pcs mc))) then
         if encoded_bytes_in_mem (target_config
           (machine_config_target
             mc)) (target_get_pc (machine_config_target mc) ms)
             (target_get_byte (machine_config_target mc) ms)
               (machine_config_prog_addresses mc) then
           let ms1 = target_next (machine_config_target mc) ms in
           let (ms2,new_oracle) = apply_oracle
             (machine_config_next_interfer mc) ms1 in
           let mc = machine_config_next_interfer_fupd (K new_oracle)
             mc in
             if EVERY (target_state_ok (machine_config_target mc))
               [ms; ms1; ms2] /\
                (!x. ~(x IN machine_config_prog_addresses mc) ==>
                  target_get_byte (machine_config_target
                    mc) ms1 x = target_get_byte
                      (machine_config_target
                    mc) ms x) then
               targetSem_evaluate mc ffi (k - 1) ms2 else
               (Error,ms,ffi) else (Error,ms,ffi) else if
                 target_get_pc (machine_config_target mc) ms =
                 machine_config_halt_pc mc then
         ((if target_get_reg (machine_config_target mc) ms
           (machine_config_ptr_reg mc) = (n2w 0) then Halt ffi_Success
           else Halt ffi_Resource_limit_hit),ms,ffi) else if
           target_get_pc (machine_config_target mc) ms =
           machine_config_ccache_pc mc then
         let (ms1,new_oracle) =
           apply_oracle (machine_config_ccache_interfer mc)
             (target_get_reg (machine_config_target mc) ms
               (machine_config_ptr_reg mc),target_get_reg
               (machine_config_target
              mc) ms (machine_config_len_reg mc),
              ms) in
         let mc = machine_config_ccache_interfer_fupd (K new_oracle)
           mc in
           targetSem_evaluate mc ffi (k - 1) ms1 else
         match find_index (target_get_pc (machine_config_target mc)
           ms) (machine_config_ffi_entry_pcs mc) 0 with NONE ->
           (Error,ms,ffi) | SOME ffi_index ->
             (match EL ffi_index (ffi_names mc) with SharedMem op ->
                  (match ALOOKUP (machine_config_mmio_info mc)
                    ffi_index with NONE -> (Error,ms,ffi) | SOME
                    (nb,a,reg,pc') ->
                       (match op with MappedRead ->
                              (match a with Addr r off ->
                              (let ad = target_get_reg
                                (machine_config_target mc) ms r + off in
                              (if (if nb = (n2w 0) then (w2n ad MOD
                                (dimindex (:'b) DIV 8)) = 0 else T) /\
                              (ad IN machine_config_shared_addresses
                                mc) /\
                              is_valid_mapped_read (target_get_pc
                                (machine_config_target mc) ms) nb a reg
                                pc' (machine_config_target
                              mc) ms (machine_config_prog_addresses
                                mc) then
                              (match call_FFI ffi (EL ffi_index
                                (ffi_names mc)) [nb]
                              (word_to_bytes ad F) with FFI_final
                                outcome ->
                              (Halt (ffi_FFI_outcome outcome),ms,ffi)
                                | FFI_return new_ffi new_bytes ->
                              (let (ms1,new_oracle) = apply_oracle
                                (machine_config_ffi_interfer mc)
                              (ffi_index,new_bytes,ms) in
                              let mc =
                                machine_config_ffi_interfer_fupd (K
                                new_oracle) mc in
                              targetSem_evaluate mc new_ffi (k -
                                (1:num)) ms1)) else (Error,ms,ffi)))) |
                                MappedWrite ->
                              (match a with Addr r off ->
                              (let ad = (target_get_reg
                                (machine_config_target mc) ms r) + off
                                in
                              (if (if nb = (n2w 0) then (w2n ad MOD
                                (dimindex (:'b) DIV 8)) = 0 else T) /\
                              (ad IN machine_config_shared_addresses
                                mc) /\
                              is_valid_mapped_write (target_get_pc
                                (machine_config_target mc) ms) nb a reg
                                pc' (machine_config_target
                              mc) ms (machine_config_prog_addresses
                                mc) then
                              (match call_FFI ffi (EL ffi_index
                                (ffi_names mc)) [nb]
                              (
                              (let w = target_get_reg
                                (machine_config_target mc) ms reg in
                              if nb = (n2w 0) then word_to_bytes w F
                                else word_to_bytes_aux (w2n nb) w F) ++
                                (word_to_bytes ad F)) with FFI_final
                                outcome ->
                              (Halt (ffi_FFI_outcome outcome),ms,ffi)
                                | FFI_return new_ffi new_bytes ->
                              (let (ms1,new_oracle) = apply_oracle
                                (machine_config_ffi_interfer mc)
                              (ffi_index,new_bytes,ms) in
                              let mc =
                                machine_config_ffi_interfer_fupd (K
                                new_oracle) mc in
                              targetSem_evaluate mc new_ffi (k -
                                (1:num)) ms1)) else (Error,ms,ffi))))))
                                | ExtCall _1 ->
                  (match ALOOKUP (machine_config_mmio_info mc)
                    ffi_index with SOME _2 -> (Error,ms,ffi) | NONE ->
                       (match read_ffi_bytearrays mc ms with (SOME
                         bytes,SOME bytes2) ->
                            (match call_FFI ffi (EL ffi_index
                              (ffi_names mc)) bytes bytes2 with
                              FFI_final outcome -> (Halt
                              (ffi_FFI_outcome outcome),ms,ffi) |
                              FFI_return new_ffi new_bytes ->
                              (let (ms1,new_oracle) = apply_oracle
                                (machine_config_ffi_interfer mc)
                              (ffi_index,new_bytes,ms) in
                              let mc =
                                machine_config_ffi_interfer_fupd (K
                                new_oracle) mc in
                              targetSem_evaluate mc new_ffi (k -
                                (1:num)) ms1)) | _3 ->
                                (Error,ms,ffi)))))`;;
hol4_overload "evaluate" "targetSem_evaluate";;

let machine_sem_def = cake_define_list
  [`machine_sem mc st ms (ffi_Terminate t io_list) <=>
         (?k ms' st'.
           evaluate mc st k ms = (Halt t,ms',st') /\
             ffi_state_io_events
           st' = io_list)`;
   `machine_sem mc st ms (ffi_Diverge io_trace) <=>
         (!k. ?ms' st'. evaluate mc st k ms = (TimeOut,ms',st')) /\
         lprefix_lub
           (IMAGE
             (\k. fromList (ffi_state_io_events (SND (SND (evaluate
               mc st k ms))))) UNIV)
           io_trace`;
   `machine_sem mc st ms (ffi_Fail:behaviour) <=>
         (?k. FST (evaluate mc st k ms) = Error)`];;

(* define what it means for code to be loaded and ready to run *)

let code_loaded_def = cake_define
  `code_loaded (bytes:word8 list) (mc:('a,'b,'c)machine_config) (ms:'b)
  <=>
     read_bytearray (target_get_pc (machine_config_target mc) ms)
       (LENGTH bytes)
       (\a. if a IN machine_config_prog_addresses mc then SOME
         (target_get_byte (machine_config_target mc) ms a) else NONE)
         = SOME bytes`;;

(* target_configured: target and mc_conf are compatible
   will be proved at the top-level by creating an appropriate t *)
let target_configured_def = cake_define
  `target_configured (t:'a asm_state) mc_conf <=>
     ~asm_state_failed t /\ be
     t = asm_config_big_endian (target_config (machine_config_target
       mc_conf)) /\ asm_state_align
     t = asm_config_code_alignment (target_config
       (machine_config_target mc_conf)) /\ asm_state_mem_domain
     t = machine_config_prog_addresses mc_conf /\
     (match asm_config_link_reg (target_config
       (machine_config_target mc_conf)) with NONE -> T | SOME r ->
       asm_state_lr t = r)`;;

let get_reg_value_def = cake_define_list
  [`get_reg_value NONE w f = w`;
   `get_reg_value (SOME v) _4 f = f v`];;

let mmio_pcs_min_index_def = cake_define
  `mmio_pcs_min_index ffi_names' =
   some (\x.
     ((x <= LENGTH ffi_names') /\
     (!j. j < x ==> (?s.
       EL j ffi_names' = ExtCall s)) /\
     (!j. x <= j /\ j < LENGTH ffi_names' ==>
          (?op. EL j ffi_names' = SharedMem op))))`;;

(* start_pc_ok: machine configuration's saved pcs and initial pc are ok
   *)
let start_pc_ok_def = cake_define
  `start_pc_ok mc_conf pc' <=> ~(machine_config_halt_pc
     mc_conf IN machine_config_prog_addresses mc_conf) /\
       ~(machine_config_ccache_pc
     mc_conf IN machine_config_prog_addresses mc_conf) /\
       ~(machine_config_halt_pc
     mc_conf IN machine_config_shared_addresses mc_conf) /\
       ~(machine_config_ccache_pc
     mc_conf IN machine_config_shared_addresses mc_conf) /\
     pc' - n2w ffi_offset = machine_config_halt_pc mc_conf /\
     pc' - n2w (2 * ffi_offset) = machine_config_ccache_pc mc_conf /\
     ((n2w 1) && pc') = (n2w 0) /\
     (?i. mmio_pcs_min_index (ffi_names mc_conf) = SOME i /\
     (!index.
        index < i ==> ~(
        pc' - n2w ((3 + index) * ffi_offset) IN
          machine_config_prog_addresses
        mc_conf) /\ ~(
        pc' - n2w ((3 + index) * ffi_offset) IN
          machine_config_shared_addresses
        mc_conf) /\ ~(
        pc' - n2w ((3 + index) * ffi_offset) = machine_config_halt_pc
        mc_conf) /\ ~(
        pc' - n2w ((3 + index) * ffi_offset) =
          machine_config_ccache_pc
        mc_conf) /\
        find_index
          (pc' - n2w ((3 + index) * ffi_offset))
            (machine_config_ffi_entry_pcs
          mc_conf) 0 = SOME index) /\
     (!index.
       index < LENGTH (ffi_names mc_conf) /\ i <= index ==>
         ~(machine_config_halt_pc
       mc_conf = (EL index (machine_config_ffi_entry_pcs mc_conf)))
         /\ ~(machine_config_ccache_pc
       mc_conf = (EL index (machine_config_ffi_entry_pcs mc_conf))))
         /\
     LENGTH (ffi_names mc_conf) = LENGTH
       (machine_config_ffi_entry_pcs mc_conf))`;;

(* ffi_interfer_ok: the FFI interference oracle is ok:
   an ExtCall transition must satisfy the per-call promises of the
   calling convention -- the machine invariants hold, control returns
   to the link-register address, the byte array is written and no other
   program memory changes, and callee-saved registers are preserved;
   all other registers (including all FP registers) are unconstrained.
   A SharedMem transition performs the mapped load/store and touches
   nothing else. *)
let ffi_interfer_ok_def = cake_define
  `ffi_interfer_ok pc' mc_conf <=>
     (!ms2 k index new_bytes t1 bytes bytes2 i.
        index < LENGTH (ffi_names mc_conf) /\
        mmio_pcs_min_index (ffi_names mc_conf) = SOME i /\
          machine_config_prog_addresses
        mc_conf = asm_state_mem_domain t1 ==>
          (index < i ==>
            read_ffi_bytearrays mc_conf ms2 = (SOME bytes,SOME
              bytes2) /\
            LENGTH new_bytes = LENGTH bytes2 /\
            (EL index (ffi_names mc_conf) = ExtCall (implode "") ==>
              new_bytes = bytes2) /\
            target_state_rel (machine_config_target mc_conf)
              (asm_state_pc_fupd (K (--n2w ((3 + index) * ffi_offset)
                + pc')) t1) ms2 /\
            alignment_aligned (asm_config_code_alignment
              (target_config (machine_config_target mc_conf)))
             (asm_state_regs t1 (match asm_config_link_reg
               (target_config (machine_config_target mc_conf)) with NONE
               -> 0 | SOME n -> n)) ==>
         (let ms' = machine_config_ffi_interfer mc_conf k
           (index,new_bytes,ms2) in target_state_ok
           (machine_config_target
            mc_conf) ms' /\ target_get_pc (machine_config_target
            mc_conf) ms' = asm_state_regs
              t1 (match asm_config_link_reg (target_config
                (machine_config_target mc_conf)) with NONE -> 0 | SOME n
                -> n) /\
            (!a. a IN asm_state_mem_domain t1 ==> target_get_byte
              (machine_config_target
                 mc_conf) ms' a =
                 asm_write_bytearray (asm_state_regs t1
                   (machine_config_ptr2_reg mc_conf)) new_bytes
                   (asm_state_mem t1) a) /\
            (!r. MEM r (machine_config_callee_saved_regs mc_conf) /\
                 r < asm_config_reg_count (target_config
                   (machine_config_target mc_conf)) /\
                 ~MEM r (asm_config_avoid_regs (target_config
                   (machine_config_target mc_conf))) ==> target_get_reg
                   (machine_config_target
                 mc_conf) ms' r = asm_state_regs t1 r))) /\
          (i <= index /\
            target_state_rel (machine_config_target mc_conf)
             (asm_state_pc_fupd (K (EL index
               (machine_config_ffi_entry_pcs mc_conf))) t1) ms2 ==>
               (?info. ALOOKUP (machine_config_mmio_info mc_conf)
                 index = SOME info /\
                (EL index (ffi_names mc_conf) = SharedMem MappedRead
                  ==>
                (!new_bytes.
                target_state_rel (machine_config_target mc_conf)
                  (asm_state_regs_fupd (K (\n. if n = FST (SND (SND
                    info)) then
                       (word_of_bytes F (n2w 0) new_bytes) else
                         asm_state_regs t1 n)) (asm_state_pc_fupd (K
                         (SND (SND (SND info)))) t1))
                   (machine_config_ffi_interfer mc_conf k
                     (index,new_bytes,ms2)))) /\
                (EL index (ffi_names mc_conf) = SharedMem MappedWrite
                  ==>
                target_state_rel (machine_config_target mc_conf)
                  (asm_state_pc_fupd (K (SND (SND (SND info)))) t1)
                  (machine_config_ffi_interfer mc_conf k
                    (index,new_bytes,ms2))))))`;;

(* ccache_interfer_ok: a cache-clear transition must satisfy the same
   per-call promises, additionally preserving ptr_reg and leaving all
   program memory unchanged *)
let ccache_interfer_ok_def = cake_define
  `ccache_interfer_ok pc' mc_conf <=>
     (!ms2 t1 k a1 a2.
        target_state_rel (machine_config_target mc_conf)
          (asm_state_pc_fupd (K (--n2w (2 * ffi_offset) + pc')) t1)
        ms2 /\
        alignment_aligned (asm_config_code_alignment (target_config
          (machine_config_target mc_conf))) (asm_state_regs t1 (match
          asm_config_link_reg (target_config (machine_config_target
          mc_conf)) with NONE -> 0 | SOME n -> n)) ==>
        (let ms' = machine_config_ccache_interfer mc_conf k
          (a1,a2,ms2) in target_state_ok (machine_config_target
           mc_conf) ms' /\ target_get_pc (machine_config_target
           mc_conf) ms' = asm_state_regs
             t1 (match asm_config_link_reg (target_config
               (machine_config_target mc_conf)) with NONE -> 0 | SOME n
               -> n) /\
           (!a. a IN asm_state_mem_domain t1 ==> target_get_byte
             (machine_config_target
                mc_conf) ms' a = asm_state_mem t1 a) /\
           (!r. (MEM r (machine_config_callee_saved_regs mc_conf) \/
             r = machine_config_ptr_reg mc_conf) /\
                r < asm_config_reg_count (target_config
                  (machine_config_target mc_conf)) /\
                ~MEM r (asm_config_avoid_regs (target_config
                  (machine_config_target mc_conf))) ==> target_get_reg
                  (machine_config_target
                mc_conf) ms' r = asm_state_regs t1 r)))`;;

(* post_ffi_asm / post_ccache_asm: the canonical asm-level successor
   state after an FFI / cache-clear transition -- caller-saved
   registers and all FP registers are taken from the machine state *)
let post_ffi_asm_def = cake_define
  `post_ffi_asm (mc_conf:('a,'state,'b)machine_config) (t1:'a asm_state)
                new_bytes (ms':'state) = asm_state_pc_fupd (K
                  (asm_state_regs t1 (match asm_config_link_reg
                  (target_config (machine_config_target mc_conf)) with
                  NONE -> 0 | SOME n -> n))) (asm_state_mem_fupd (K
                  (asm_write_bytearray (asm_state_regs t1
                  (machine_config_ptr2_reg mc_conf)) new_bytes
                  (asm_state_mem t1))) (fp_regs_fupd (K (\i.
                  target_get_fp_reg (machine_config_target mc_conf) ms'
                  i)) (asm_state_regs_fupd (K (\a. if MEM a
                  (machine_config_callee_saved_regs mc_conf) \/
                         ~(a < asm_config_reg_count (target_config
                           (machine_config_target mc_conf))) \/
                         MEM a (asm_config_avoid_regs (target_config
                           (machine_config_target mc_conf))) then
                           asm_state_regs t1 a else target_get_reg
                           (machine_config_target mc_conf) ms' a))
     t1)))`;;

let post_ccache_asm_def = cake_define
  `post_ccache_asm (mc_conf:('a,'state,'b)machine_config) (t1:'a
  asm_state) (ms':'state) = asm_state_pc_fupd (K (asm_state_regs t1
  (match asm_config_link_reg (target_config (machine_config_target
  mc_conf)) with NONE -> 0 | SOME n -> n))) (fp_regs_fupd (K (\i.
  target_get_fp_reg (machine_config_target mc_conf) ms' i))
  (asm_state_regs_fupd (K (\a. if MEM a
  (machine_config_callee_saved_regs mc_conf) \/
                         a = machine_config_ptr_reg mc_conf \/
                         ~(a < asm_config_reg_count (target_config
                           (machine_config_target mc_conf))) \/
                         MEM a (asm_config_avoid_regs (target_config
                           (machine_config_target mc_conf))) then
                           asm_state_regs t1 a else target_get_reg
                           (machine_config_target mc_conf) ms' a))
     t1))`;;

(*
  good_init_state:
    intermediate invariant describing how
    code (bytes) and ffi is installed in the machine (mc_conf, ms)
    using labLang (m, dm, cbspace) and
    target semantics (t) information as an intermediary
  these are all destined to be assumptions on the top-level correctness
    theorem
*)

let good_init_state_def = cake_define
  `good_init_state (mc_conf:('a,'state,'b)machine_config) ms bytes
     cbspace
     t m dm sdm <=>
     target_state_rel (machine_config_target mc_conf) t ms /\
     target_configured t mc_conf /\ asm_state_pc
     t = target_get_pc (machine_config_target mc_conf) ms /\
     start_pc_ok mc_conf (asm_state_pc t) /\
     (n2w (2 EXP asm_state_align t - 1) && asm_state_pc t) = (n2w 0)
       /\
     interference_ok (machine_config_next_interfer mc_conf)
       (target_proj (machine_config_target mc_conf)
       (machine_config_prog_addresses mc_conf)) /\
     ffi_interfer_ok (asm_state_pc t) mc_conf /\
     ccache_interfer_ok (asm_state_pc t) mc_conf /\
     code_loaded bytes mc_conf ms /\
     bytes_in_mem (asm_state_pc t) bytes (asm_state_mem t)
       (asm_state_mem_domain t) dm /\
     dm SUBSET asm_state_mem_domain t /\
     (!a. byte_align a IN dm ==> a IN dm) /\
     sdm = machine_config_shared_addresses mc_conf /\
     (!a. byte_align a IN sdm ==> a IN sdm) /\
     DISJOINT (machine_config_prog_addresses mc_conf)
       (machine_config_shared_addresses mc_conf) /\
     (!a. ?w. asm_state_mem
       t a = get_byte a w (asm_config_big_endian (target_config
         (machine_config_target mc_conf))) /\
       m (byte_align a) = wordLang_Word w) /\
     (!n. n < cbspace ==>
       n2w (n + LENGTH bytes) + asm_state_pc t IN
         asm_state_mem_domain t /\ ~(
       n2w (n + LENGTH bytes) + asm_state_pc t IN dm)) /\
     cbspace + LENGTH bytes < dimword (:'a)`;;

(* CakeML code, bytes, and code buffer space, cspace, and FFI functions,
   ffi,
   are installed into the machine, mc_conf + ms
   r1 and r2 are the names of registers containing
   the first address of the CakeML heap and the first address past the
     CakeML stack
   i.e., the range of the data memory
*)
let installed_def = cake_define
  `installed bytes cbspace bitmaps data_sp ffi_names' (r1,r2)
  (mc_conf:('a,'state,'b)machine_config) shmem_extra ms <=>
     (?t m bitmap_ptr bitmaps_dm sdm.
       let heap_stack_dm = {w | asm_state_regs t r1 <=+ w /\ w <+
         asm_state_regs t r2} in
       good_init_state mc_conf ms bytes cbspace t m (heap_stack_dm
         UNION bitmaps_dm) sdm /\
       byte_aligned (asm_state_regs t r1) /\
       byte_aligned (asm_state_regs t r2) /\
       byte_aligned bitmap_ptr /\ asm_state_regs
       t r1 <=+ asm_state_regs t r2 /\
       (n2w 1024) * bytes_in_word <=+ asm_state_regs t r2 -
         asm_state_regs t r1 /\
       DISJOINT heap_stack_dm bitmaps_dm /\
       m (asm_state_regs t r1) = wordLang_Word bitmap_ptr /\
       m (asm_state_regs t r1 + bytes_in_word) =
         wordLang_Word (bitmap_ptr + bytes_in_word * n2w (LENGTH
           bitmaps)) /\
       m (asm_state_regs t r1 + (n2w 2) * bytes_in_word) =
         wordLang_Word (bitmap_ptr + bytes_in_word * n2w data_sp +
               bytes_in_word * n2w (LENGTH bitmaps)) /\
       m (asm_state_regs t r1 + (n2w 3) * bytes_in_word) =
         wordLang_Word (target_get_pc (machine_config_target mc_conf)
           ms + n2w (LENGTH bytes)) /\
       m (asm_state_regs t r1 + (n2w 4) * bytes_in_word) =
         wordLang_Word (target_get_pc (machine_config_target mc_conf)
           ms + n2w cbspace + n2w (LENGTH bytes)) /\
       (misc_word_list bitmap_ptr (MAP wordLang_Word bitmaps) *
         word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH
           bitmaps)) data_sp)
        (fun2set (m,byte_aligned INTER bitmaps_dm)) /\
       ffi_names' = SOME (ffi_names mc_conf) /\
    (!i. mmio_pcs_min_index (ffi_names mc_conf) = SOME i ==>
      MAP (\rec. w2n (target_get_pc (machine_config_target mc_conf)
        ms) + shmem_info_num_entry_pc rec) shmem_extra =
        DROP i (MAP w2n (machine_config_ffi_entry_pcs mc_conf)) /\
          machine_config_mmio_info
      mc_conf = ZIP (GENLIST (\index. index + i) (LENGTH
        shmem_extra))
                              (MAP (\rec. (shmem_info_num_nbytes rec,
                              Addr (shmem_info_num_addr_reg rec) (n2w
                                (shmem_info_num_addr_off
                                rec)),shmem_info_num_reg rec,
                              n2w (shmem_info_num_exit_pc rec) +
                                target_get_pc (machine_config_target
                                mc_conf) ms))
                              shmem_extra) /\
     cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword
       (:'a)))`;;
