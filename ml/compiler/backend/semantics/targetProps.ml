(* ======================================================== *)
(*  targetProps: ported from HOL4's
    compiler/backend/semantics/targetPropsScript.sml  *)
(* ======================================================== *)

(*
  Properties about the target semantics
*)

needs "compiler/backend/semantics/targetSem.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/encoders/asm/asmProps.ml";;
needs "compiler/encoders/asm/asmSem.ml";;
needs "lib/byte.ml";;
needs "misc/misc.ml";;
needs "semantics/ffi/ffi.ml";;

let shift_interfer_def = cake_define
  `shift_interfer k s = machine_config_next_interfer_fupd (K
  (misc_shift_seq k (machine_config_next_interfer s)))
     s`;;

let ffi_entry_pcs_disjoint_def = cake_define
  `ffi_entry_pcs_disjoint mc s1 len =
     DISJOINT (set_of_list (machine_config_ffi_entry_pcs mc))
       {asm_state_pc s1 + n2w a | a < len}`;;

(* -- the interference-application trace of a machine run -- *)

let interference_app_INDUCT,interference_app_RECURSION = define_datatype
  "interference_app = FfiApp (num) (word8 list) ('state) ('state) | \
   CcApp ('a word) ('a word) ('state) ('state)";;

let is_ffi_app_def = cake_define_list
  [`is_ffi_app (FfiApp index new_bytes ms_pre ms_post) = T`;
   `is_ffi_app (CcApp a1 a2 ms_pre ms_post) = F`];;

let app_post_def = cake_define_list
  [`app_post (FfiApp index new_bytes ms_pre ms_post) = ms_post`;
   `app_post (CcApp a1 a2 ms_pre ms_post) = ms_post`];;

(* clocked clone of evaluate that stops at the first interference
   application (FFI, shared-memory or cache-clear) and returns its data
   together with the continuation configuration and ffi state *)
let find_next_interference_def = cake_define
  `find_next_interference (mc:('b,'a,'c)machine_config) (ffi:'ffi
  ffi_state) k (ms:'a) =
     (if k = 0 then NONE else
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
               find_next_interference mc ffi (k - 1) ms2 else NONE
                 else NONE else if target_get_pc (machine_config_target
                 mc) ms = machine_config_halt_pc mc then NONE else if
                 target_get_pc (machine_config_target mc) ms =
                 machine_config_ccache_pc mc then
         let (ms1,new_oracle) =
           apply_oracle (machine_config_ccache_interfer mc)
             (target_get_reg (machine_config_target mc) ms
               (machine_config_ptr_reg mc),target_get_reg
               (machine_config_target
              mc) ms (machine_config_len_reg mc),
              ms) in
           SOME (CcApp (target_get_reg (machine_config_target mc) ms
             (machine_config_ptr_reg mc))
                       (target_get_reg (machine_config_target mc) ms
                         (machine_config_len_reg mc)) ms
                         ms1,machine_config_ccache_interfer_fupd (K
                         new_oracle)
                 mc,ffi) else
         match find_index (target_get_pc (machine_config_target mc)
           ms) (machine_config_ffi_entry_pcs mc) 0 with NONE -> NONE |
           SOME ffi_index ->
             (match EL ffi_index (ffi_names mc) with ffi_SharedMem op
               ->
                  (match ALOOKUP (machine_config_mmio_info mc)
                    ffi_index with NONE -> NONE | SOME (nb,a,reg,pc') ->
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
                                outcome -> NONE | FFI_return new_ffi
                                new_bytes ->
                              (let (ms1,new_oracle) = apply_oracle
                                (machine_config_ffi_interfer mc)
                              (ffi_index,new_bytes,ms) in
                              SOME (FfiApp ffi_index new_bytes ms
                                ms1,machine_config_ffi_interfer_fupd (K
                                new_oracle)
                              mc,
                              new_ffi))) else NONE))) | MappedWrite
                                ->
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
                                outcome -> NONE | FFI_return new_ffi
                                new_bytes ->
                              (let (ms1,new_oracle) = apply_oracle
                                (machine_config_ffi_interfer mc)
                              (ffi_index,new_bytes,ms) in
                              SOME (FfiApp ffi_index new_bytes ms
                                ms1,machine_config_ffi_interfer_fupd (K
                                new_oracle)
                              mc,
                              new_ffi))) else NONE))))) | ffi_ExtCall
                                _1 ->
                  (match ALOOKUP (machine_config_mmio_info mc)
                    ffi_index with SOME _2 -> NONE | NONE ->
                       (match read_ffi_bytearrays mc ms with (SOME
                         bytes,SOME bytes2) ->
                            (match call_FFI ffi (EL ffi_index
                              (ffi_names mc)) bytes bytes2 with
                              FFI_final outcome -> NONE | FFI_return
                              new_ffi new_bytes ->
                              (let (ms1,new_oracle) = apply_oracle
                                (machine_config_ffi_interfer mc)
                              (ffi_index,new_bytes,ms) in
                              SOME (FfiApp ffi_index new_bytes ms
                                ms1,machine_config_ffi_interfer_fupd (K
                                new_oracle)
                              mc,
                              new_ffi))) | _3 -> NONE))))`;;

(* the limit of find_next_interference over all clocks *)
let next_interference_def = cake_define
  `next_interference mc ffi ms =
     some (\res. ?k. find_next_interference mc ffi k ms = SOME
       res)`;;

(* the sequence of interference applications of a run *)
let interference_app_seq_def = cake_define_list
  [`interference_app_seq mc ffi ms 0 = next_interference mc ffi ms`;
   `interference_app_seq mc ffi ms (SUC n) =
         (match next_interference mc ffi ms with NONE -> NONE |
           SOME (app,mc',ffi') -> interference_app_seq mc' ffi'
           (app_post app) n)`];;

(* number of applications satisfying P among the first n applications *)
let interference_count_def = cake_define_list
  [`interference_count P mc ffi ms 0 = 0`;
   `interference_count P mc ffi ms (SUC n) =
         interference_count P mc ffi ms n +
         (match interference_app_seq mc ffi ms n with SOME
           (app,mc',ffi') -> (if P app then 1 else 0) | NONE -> 0)`];;

(* position in the application sequence of the k-th application
   satisfying P *)
let interference_pos_def = cake_define
  `interference_pos P mc ffi ms k =
     some (\n. interference_count P mc ffi ms n = k /\
             (?app mc' ffi'.
               interference_app_seq mc ffi ms n = SOME (app,mc',ffi')
                 /\
               P app))`;;

(* the lab-level oracle sequences, constructed from the machine run:
   caller-saved register and FP-register residues are read off each
   application's post state; callee-saved (and avoid / out-of-range)
   registers are marked NONE, i.e. preserved *)
let target_io_regs_def = cake_define
  `target_io_regs mc ffi ms k (name:ffiname) r =
     (match interference_pos is_ffi_app mc ffi ms k with NONE -> NONE
       | SOME n ->
       (match interference_app_seq mc ffi ms n with SOME (FfiApp
         index new_bytes ms_pre ms_post,mc',ffi') ->
            (if MEM r (machine_config_callee_saved_regs mc) \/
                ~(r < asm_config_reg_count (target_config
                  (machine_config_target mc))) \/
                MEM r (asm_config_avoid_regs (target_config
                  (machine_config_target mc))) then NONE else SOME
                  (target_get_reg (machine_config_target mc) ms_post
                  r)) | _4 -> NONE))`;;

let target_io_fp_regs_def = cake_define
  `target_io_fp_regs mc ffi ms k (i:num) =
     (match interference_pos is_ffi_app mc ffi ms k with NONE ->
       ((n2w 0):word64) | SOME n ->
       (match interference_app_seq mc ffi ms n with SOME (FfiApp
         index new_bytes ms_pre ms_post,mc',ffi') -> target_get_fp_reg
         (machine_config_target
            mc) ms_post i | _5 -> (n2w 0)))`;;

let target_cc_regs_def = cake_define
  `target_cc_regs mc ffi ms k r =
     (match interference_pos (\app. ~is_ffi_app app) mc ffi ms k with
       NONE -> NONE | SOME n ->
       (match interference_app_seq mc ffi ms n with SOME (CcApp a1 a2
         ms_pre ms_post,mc',ffi') ->
            (if MEM r (machine_config_callee_saved_regs mc) \/ r =
              machine_config_ptr_reg mc \/
                ~(r < asm_config_reg_count (target_config
                  (machine_config_target mc))) \/
                MEM r (asm_config_avoid_regs (target_config
                  (machine_config_target mc))) then NONE else SOME
                  (target_get_reg (machine_config_target mc) ms_post
                  r)) | _6 -> NONE))`;;

let target_cc_fp_regs_def = cake_define
  `target_cc_fp_regs mc ffi ms k (i:num) =
     (match interference_pos (\app. ~is_ffi_app app) mc ffi ms k with
       NONE -> ((n2w 0):word64) | SOME n ->
       (match interference_app_seq mc ffi ms n with SOME (CcApp a1 a2
         ms_pre ms_post,mc',ffi') -> target_get_fp_reg
         (machine_config_target
            mc) ms_post i | _7 -> (n2w 0)))`;;

(* basic properties *)

(* -- interface lemmas for the interference contracts -- *)
