(* ======================================================== *)
(*  targetProps: ported from HOL4's
    compiler/backend/semantics/targetPropsScript.sml
    A proof theory, with 13 definitions, 1 datatype and 43 theorems.
    Needed by lab_to_targetProof.ml.  *)
(* ======================================================== *)

(*
  Properties about the target semantics
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/backend/semantics/targetSem.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/encoders/asm/asmProps.ml";;
needs "compiler/encoders/asm/asmSem.ml";;
needs "lib/byte.ml";;
needs "misc/misc.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/typeSystem.ml";;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["state_ok","bvl_to_bviProof_state_ok"];;

let shift_interfer_def = cake_define
  `shift_interfer k s = machine_config_next_interfer_fupd (K
  (misc_shift_seq k (machine_config_next_interfer s)))
     s`;;

(* [local] *)
let shift_interfer_intro = prove
 (`shift_interfer k1 (shift_interfer k2 c) =
     shift_interfer (k1 + k2) c`,
  CHEAT_TAC);;

let bytes_in_memory_SUBSET = prove
 (`!p.
   dm SUBSET dm2 /\ bytes_in_memory p xs m dm ==>
   bytes_in_memory p xs m dm2`,
  CHEAT_TAC);;

let bytes_in_memory_DIFF = prove
 (`!p.
       (dm = dm2 DIFF pcs /\ bytes_in_memory p xs m dm2 /\
       DISJOINT pcs {p + n2w i | i | i < LENGTH xs}) ==>
       bytes_in_memory p xs m dm`,
  CHEAT_TAC);;

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
             (match EL ffi_index (machine_config_ffi_names mc) with
               ffi_SharedMem op ->
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
                                (machine_config_ffi_names mc)) [nb]
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
                                (machine_config_ffi_names mc)) [nb]
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
                              (machine_config_ffi_names mc)) bytes
                              bytes2 with FFI_final outcome -> NONE |
                              FFI_return new_ffi new_bytes ->
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
     (match interference_pos (\app. ~(is_ffi_app app)) mc ffi ms k
       with NONE -> NONE | SOME n ->
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
     (match interference_pos (\app. ~(is_ffi_app app)) mc ffi ms k
       with NONE -> ((n2w 0):word64) | SOME n ->
       (match interference_app_seq mc ffi ms n with SOME (CcApp a1 a2
         ms_pre ms_post,mc',ffi') -> target_get_fp_reg
         (machine_config_target
            mc) ms_post i | _7 -> (n2w 0)))`;;

let find_next_interference_mono = prove
 (`!k mc ffi ms res i.
     find_next_interference mc ffi k ms = SOME res ==>
     find_next_interference mc ffi (k + i) ms = SOME res`,
  CHEAT_TAC);;

let find_next_interference_unique = prove
 (`find_next_interference mc ffi k1 ms = SOME res1 /\
   find_next_interference mc ffi k2 ms = SOME res2 ==>
   res1 = res2`,
  CHEAT_TAC);;

let next_interference_intro = prove
 (`find_next_interference mc ffi k ms = SOME res ==>
   next_interference mc ffi ms = SOME res`,
  CHEAT_TAC);;

let next_interference_shift = prove
 (`(!k. find_next_interference mc1 ffi1 (k + l) ms1 =
        find_next_interference mc2 ffi2 k ms2) ==>
   next_interference mc1 ffi1 ms1 = next_interference mc2 ffi2 ms2`,
  CHEAT_TAC);;

let find_next_interference_const = prove
 (`!k mc ffi ms app mc' ffi'.
     find_next_interference mc ffi k ms = SOME (app,mc',ffi') ==>
       machine_config_target
     mc' = machine_config_target mc /\
       machine_config_callee_saved_regs
     mc' = machine_config_callee_saved_regs mc /\
       machine_config_ptr_reg
     mc' = machine_config_ptr_reg mc`,
  CHEAT_TAC);;

let next_interference_const = prove
 (`next_interference mc ffi ms = SOME (app,mc',ffi') ==>
  machine_config_target
   mc' = machine_config_target mc /\ machine_config_callee_saved_regs
   mc' = machine_config_callee_saved_regs mc /\
     machine_config_ptr_reg
   mc' = machine_config_ptr_reg mc`,
  CHEAT_TAC);;

let interference_app_seq_EQ = prove
 (`next_interference mc1 ffi1 ms1 = next_interference mc2 ffi2 ms2 ==>
   (!n. interference_app_seq mc1 ffi1 ms1 n =
       interference_app_seq mc2 ffi2 ms2 n)`,
  CHEAT_TAC);;

let interference_app_seq_tail = prove
 (`next_interference mc ffi ms = SOME (app,mc',ffi') ==>
   (!n. interference_app_seq mc ffi ms (SUC n) =
       interference_app_seq mc' ffi' (app_post app) n)`,
  CHEAT_TAC);;

let interference_count_mono = prove
 (`!i m. interference_count P mc ffi ms m <=
         interference_count P mc ffi ms (m + i)`,
  CHEAT_TAC);;

let interference_count_lt = prove
 (`interference_app_seq mc ffi ms n = SOME (app,mc',ffi') /\ P app /\ n
  < n2 ==>
   interference_count P mc ffi ms n < interference_count P mc ffi
     ms n2`,
  CHEAT_TAC);;

let interference_pos_unique = prove
 (`interference_app_seq mc ffi ms n1 = SOME (app1,mc1',ffi1') /\ P app1
  /\
   interference_app_seq mc ffi ms n2 = SOME (app2,mc2',ffi2') /\ P
     app2 /\
   interference_count P mc ffi ms n1 = interference_count P mc ffi ms
     n2 ==>
   n1 = n2`,
  CHEAT_TAC);;

let interference_count_tail = prove
 (`next_interference mc ffi ms = SOME (app0,mcc,ffic) ==>
   (!n. interference_count P mc ffi ms (SUC n) =
       (if P app0 then 1 else 0) +
       interference_count P mcc ffic (app_post app0) n)`,
  CHEAT_TAC);;

let interference_pos_head = prove
 (`next_interference mc ffi ms = SOME (app0,mcc,ffic) /\ P app0 ==>
   interference_pos P mc ffi ms 0 = SOME 0`,
  CHEAT_TAC);;

let interference_pos_tail_hit = prove
 (`next_interference mc ffi ms = SOME (app0,mcc,ffic) /\ P app0 ==>
   interference_pos P mc ffi ms (SUC k) =
   OPTION_MAP SUC (interference_pos P mcc ffic (app_post app0) k)`,
  CHEAT_TAC);;

let interference_pos_tail_miss = prove
 (`next_interference mc ffi ms = SOME (app0,mcc,ffic) /\ ~(P app0) ==>
   interference_pos P mc ffi ms k =
   OPTION_MAP SUC (interference_pos P mcc ffic (app_post app0) k)`,
  CHEAT_TAC);;

let constructed_oracles_ffi_step = prove
 (`next_interference mc ffi ms =
     SOME (FfiApp index new_bytes ms_pre ms_post,mc',ffi') ==>
   target_io_regs mc ffi ms 0 name r =
     (if MEM r (machine_config_callee_saved_regs mc) \/
         ~(r < asm_config_reg_count (target_config
           (machine_config_target mc))) \/
         MEM r (asm_config_avoid_regs (target_config
           (machine_config_target mc))) then NONE else SOME
           (target_get_reg (machine_config_target mc) ms_post r)) /\
   target_io_fp_regs mc ffi ms 0 i = target_get_fp_reg
     (machine_config_target mc) ms_post i /\
   target_io_regs mc ffi ms (SUC k) name r =
     target_io_regs mc' ffi' ms_post k name r /\
   target_io_fp_regs mc ffi ms (SUC k) i =
     target_io_fp_regs mc' ffi' ms_post k i /\
   target_cc_regs mc ffi ms k r = target_cc_regs mc' ffi' ms_post k r
     /\
   target_cc_fp_regs mc ffi ms k i = target_cc_fp_regs mc' ffi'
     ms_post k i`,
  CHEAT_TAC);;

let constructed_oracles_cc_step = prove
 (`next_interference mc ffi ms =
     SOME (CcApp a1 a2 ms_pre ms_post,mc',ffi') ==>
   target_cc_regs mc ffi ms 0 r =
     (if MEM r (machine_config_callee_saved_regs mc) \/ r =
       machine_config_ptr_reg mc \/
         ~(r < asm_config_reg_count (target_config
           (machine_config_target mc))) \/
         MEM r (asm_config_avoid_regs (target_config
           (machine_config_target mc))) then NONE else SOME
           (target_get_reg (machine_config_target mc) ms_post r)) /\
   target_cc_fp_regs mc ffi ms 0 i = target_get_fp_reg
     (machine_config_target mc) ms_post i /\
   target_cc_regs mc ffi ms (SUC k) r = target_cc_regs mc' ffi'
     ms_post k r /\
   target_cc_fp_regs mc ffi ms (SUC k) i =
     target_cc_fp_regs mc' ffi' ms_post k i /\
   target_io_regs mc ffi ms k name r =
     target_io_regs mc' ffi' ms_post k name r /\
   target_io_fp_regs mc ffi ms k i = target_io_fp_regs mc' ffi'
     ms_post k i`,
  CHEAT_TAC);;

let interference_count_EQ = prove
 (`next_interference mc1 ffi1 ms1 = next_interference mc2 ffi2 ms2 ==>
   (!n. interference_count P mc1 ffi1 ms1 n =
       interference_count P mc2 ffi2 ms2 n)`,
  CHEAT_TAC);;

let constructed_oracles_EQ = prove
 (`next_interference mc1 ffi1 ms1 = next_interference mc2 ffi2 ms2 /\
  machine_config_target
   mc1 = machine_config_target mc2 /\
     machine_config_callee_saved_regs
   mc1 = machine_config_callee_saved_regs mc2 /\
     machine_config_ptr_reg
   mc1 = machine_config_ptr_reg mc2 ==>
   target_io_regs mc1 ffi1 ms1 = target_io_regs mc2 ffi2 ms2 /\
   target_io_fp_regs mc1 ffi1 ms1 = target_io_fp_regs mc2 ffi2 ms2 /\
   target_cc_regs mc1 ffi1 ms1 = target_cc_regs mc2 ffi2 ms2 /\
   target_cc_fp_regs mc1 ffi1 ms1 = target_cc_fp_regs mc2 ffi2 ms2`,
  CHEAT_TAC);;

let target_io_regs_callee_saved = prove
 (`MEM r (machine_config_callee_saved_regs mc) ==> target_io_regs mc
  ffi ms k name r = NONE`,
  CHEAT_TAC);;

let target_cc_regs_callee_saved = prove
 (`MEM r (machine_config_callee_saved_regs mc) ==> target_cc_regs mc
  ffi ms k r = NONE`,
  CHEAT_TAC);;

let next_interference_ExtCall = prove
 (`~(target_get_pc (machine_config_target
     mc) ms IN machine_config_prog_addresses mc DIFF set_of_list
       (machine_config_ffi_entry_pcs mc)) /\ ~(target_get_pc
       (machine_config_target
     mc) ms = machine_config_halt_pc mc) /\ ~(target_get_pc
       (machine_config_target
     mc) ms = machine_config_ccache_pc mc) /\
     find_index (target_get_pc (machine_config_target mc) ms)
       (machine_config_ffi_entry_pcs mc) 0 = SOME index /\
     EL index (ffi_names mc) = ffi_ExtCall name /\
     ALOOKUP (machine_config_mmio_info mc) index = NONE /\
     read_ffi_bytearrays mc ms = (SOME bytes,SOME bytes2) /\
     call_FFI ffi (ffi_ExtCall name) bytes bytes2 = FFI_return
       new_ffi new_bytes ==>
     next_interference mc ffi ms =
       SOME (FfiApp index new_bytes ms (machine_config_ffi_interfer
         mc 0 (index,new_bytes,ms)),machine_config_ffi_interfer_fupd (K
         (misc_shift_seq 1 (machine_config_ffi_interfer mc)))
             mc,
             new_ffi)`,
  CHEAT_TAC);;

let next_interference_ccache = prove
 (`~(target_get_pc (machine_config_target
     mc) ms IN machine_config_prog_addresses mc DIFF set_of_list
       (machine_config_ffi_entry_pcs mc)) /\ ~(target_get_pc
       (machine_config_target
     mc) ms = machine_config_halt_pc mc) /\ target_get_pc
       (machine_config_target
     mc) ms = machine_config_ccache_pc mc ==>
     next_interference mc ffi ms =
       SOME (CcApp (target_get_reg (machine_config_target mc) ms
         (machine_config_ptr_reg mc))
                   (target_get_reg (machine_config_target mc) ms
                     (machine_config_len_reg mc)) ms
                   (machine_config_ccache_interfer mc 0
                      (target_get_reg (machine_config_target mc) ms
                        (machine_config_ptr_reg mc),target_get_reg
                        (machine_config_target
                       mc) ms (machine_config_len_reg
                         mc),ms)),machine_config_ccache_interfer_fupd (K
                         (misc_shift_seq 1
                         (machine_config_ccache_interfer mc)))
             mc,
             ffi)`,
  CHEAT_TAC);;

let next_interference_MappedRead = prove
 (`~(target_get_pc (machine_config_target
     mc) ms IN machine_config_prog_addresses mc DIFF set_of_list
       (machine_config_ffi_entry_pcs mc)) /\ ~(target_get_pc
       (machine_config_target
     mc) ms = machine_config_halt_pc mc) /\ ~(target_get_pc
       (machine_config_target
     mc) ms = machine_config_ccache_pc mc) /\
     find_index (target_get_pc (machine_config_target mc) ms)
       (machine_config_ffi_entry_pcs mc) 0 = SOME index /\
     EL index (machine_config_ffi_names mc) = ffi_SharedMem
       MappedRead /\
     ALOOKUP (machine_config_mmio_info mc) index = SOME (nb,Addr r
       off,reg,pc') /\
     (nb = (n2w 0) ==>
      w2n (target_get_reg (machine_config_target mc) ms r + off) MOD
        (dimindex (:'b) DIV 8) = 0) /\ target_get_reg
        (machine_config_target
     mc) ms r + off IN machine_config_shared_addresses mc /\
     is_valid_mapped_read (target_get_pc (machine_config_target mc)
       ms) nb (Addr r off) reg pc' (machine_config_target
       mc) ms (machine_config_prog_addresses mc) /\
     call_FFI ffi (EL index (machine_config_ffi_names mc)) [nb]
       (word_to_bytes (target_get_reg (machine_config_target mc) ms r
         + off) F) =
       FFI_return new_ffi new_bytes ==>
     next_interference (mc:('b,'a,'c)machine_config) ffi ms =
       SOME (FfiApp index new_bytes ms (machine_config_ffi_interfer
         mc 0 (index,new_bytes,ms)),machine_config_ffi_interfer_fupd (K
         (misc_shift_seq 1 (machine_config_ffi_interfer mc)))
             mc,
             new_ffi)`,
  CHEAT_TAC);;

let next_interference_MappedWrite = prove
 (`~(target_get_pc (machine_config_target
     mc) ms IN machine_config_prog_addresses mc DIFF set_of_list
       (machine_config_ffi_entry_pcs mc)) /\ ~(target_get_pc
       (machine_config_target
     mc) ms = machine_config_halt_pc mc) /\ ~(target_get_pc
       (machine_config_target
     mc) ms = machine_config_ccache_pc mc) /\
     find_index (target_get_pc (machine_config_target mc) ms)
       (machine_config_ffi_entry_pcs mc) 0 = SOME index /\
     EL index (machine_config_ffi_names mc) = ffi_SharedMem
       MappedWrite /\
     ALOOKUP (machine_config_mmio_info mc) index = SOME (nb,Addr r
       off,reg,pc') /\
     (nb = (n2w 0) ==>
      w2n (target_get_reg (machine_config_target mc) ms r + off) MOD
        (dimindex (:'b) DIV 8) = 0) /\ target_get_reg
        (machine_config_target
     mc) ms r + off IN machine_config_shared_addresses mc /\
     is_valid_mapped_write (target_get_pc (machine_config_target mc)
       ms) nb (Addr r off) reg pc' (machine_config_target
       mc) ms (machine_config_prog_addresses mc) /\
     call_FFI ffi (EL index (machine_config_ffi_names mc)) [nb]
       ((let w = target_get_reg (machine_config_target mc) ms reg in
           if nb = (n2w 0) then word_to_bytes w F else
             word_to_bytes_aux (w2n nb) w F) ++
        word_to_bytes (target_get_reg (machine_config_target mc) ms r
          + off) F) =
       FFI_return new_ffi new_bytes ==>
     next_interference (mc:('b,'a,'c)machine_config) ffi ms =
       SOME (FfiApp index new_bytes ms (machine_config_ffi_interfer
         mc 0 (index,new_bytes,ms)),machine_config_ffi_interfer_fupd (K
         (misc_shift_seq 1 (machine_config_ffi_interfer mc)))
             mc,
             new_ffi)`,
  CHEAT_TAC);;

let next_interference_SharedMem = prove
 (`~(target_get_pc (machine_config_target
     mc) ms IN machine_config_prog_addresses mc DIFF set_of_list
       (machine_config_ffi_entry_pcs mc)) /\ ~(target_get_pc
       (machine_config_target
     mc) ms = machine_config_halt_pc mc) /\ ~(target_get_pc
       (machine_config_target
     mc) ms = machine_config_ccache_pc mc) /\
     find_index (target_get_pc (machine_config_target mc) ms)
       (machine_config_ffi_entry_pcs mc) 0 = SOME index /\
     EL index (machine_config_ffi_names mc) = ffi_SharedMem op /\
     ALOOKUP (machine_config_mmio_info mc) index = SOME (nb,Addr r
       off,reg,pc') /\
     (nb = (n2w 0) ==>
      w2n (target_get_reg (machine_config_target mc) ms r + off) MOD
        (dimindex (:'b) DIV 8) = 0) /\ target_get_reg
        (machine_config_target
     mc) ms r + off IN machine_config_shared_addresses mc /\
     (op = MappedRead ==>
        is_valid_mapped_read (target_get_pc (machine_config_target
          mc) ms) nb (Addr r off) reg pc' (machine_config_target
          mc) ms (machine_config_prog_addresses mc) /\
        call_FFI ffi (EL index (machine_config_ffi_names mc)) [nb]
          (word_to_bytes (target_get_reg (machine_config_target mc)
            ms r + off) F) =
          FFI_return new_ffi new_bytes) /\
     (op = MappedWrite ==>
        is_valid_mapped_write (target_get_pc (machine_config_target
          mc) ms) nb (Addr r off) reg pc' (machine_config_target
          mc) ms (machine_config_prog_addresses mc) /\
        call_FFI ffi (EL index (machine_config_ffi_names mc)) [nb]
          ((let w = target_get_reg (machine_config_target mc) ms reg
            in
              if nb = (n2w 0) then word_to_bytes w F else
                word_to_bytes_aux (w2n nb) w F) ++
           word_to_bytes (target_get_reg (machine_config_target mc)
             ms r + off) F) =
          FFI_return new_ffi new_bytes) ==>
     next_interference (mc:('b,'a,'c)machine_config) ffi ms =
       SOME (FfiApp index new_bytes ms (machine_config_ffi_interfer
         mc 0 (index,new_bytes,ms)),machine_config_ffi_interfer_fupd (K
         (misc_shift_seq 1 (machine_config_ffi_interfer mc)))
             mc,
             new_ffi)`,
  CHEAT_TAC);;

let evaluate_EQ_evaluate_lemma = prove
 (`!n ms1 c. target_get_pc (machine_config_target
       c) ms1 IN (machine_config_prog_addresses c DIFF (set_of_list
         (machine_config_ffi_entry_pcs c))) /\ target_state_ok
         (machine_config_target
       c) ms1 /\
       (machine_config_prog_addresses c = dm) /\
       interference_ok (machine_config_next_interfer c) (target_proj
         (machine_config_target c) dm) /\
       (!s ms. target_state_rel (machine_config_target c) s ms ==>
         target_state_ok (machine_config_target c) ms) /\
       (!ms1 ms2. (target_proj (machine_config_target c) dm ms1 =
         target_proj (machine_config_target c) dm ms2) ==>
            (target_state_ok (machine_config_target c) ms1 =
              target_state_ok (machine_config_target c) ms2) /\
            (target_get_pc (machine_config_target c) ms1 =
              target_get_pc (machine_config_target c) ms2) /\
            (!a. a IN dm ==> target_get_byte (machine_config_target
              c) ms1 a = target_get_byte (machine_config_target c) ms2
              a)) /\
       (!env.
          interference_ok env (target_proj (machine_config_target c)
            dm) ==>
          asserts n (\k s. env k (target_next (machine_config_target
            c) s)) ms1
            (\ms'. target_state_ok (machine_config_target c) ms' /\
                   (!pc'. pc' IN all_pcs (LENGTH (asm_config_encode
                     (target_config (machine_config_target c)) i))
                     init_pc 0 ==> target_get_byte
                     (machine_config_target
                    c) ms' pc' = target_get_byte
                      (machine_config_target c) ms1 pc') /\
                      target_get_pc (machine_config_target
                   c) ms' IN
                     all_pcs (LENGTH (asm_config_encode
                       (target_config (machine_config_target c)) i))
                       init_pc (asm_config_code_alignment (target_config
                       (machine_config_target c))))
            (\ms'. target_state_rel (machine_config_target c) s2
              ms')) /\
       (asserts2 (n + 1) (\k. machine_config_next_interfer c ((n + 1)
         - k)) (target_next (machine_config_target c)) ms1
         (\ms1 ms2. !x. ~(x IN dm) ==> target_get_byte
           (machine_config_target c) ms1 x = target_get_byte
           (machine_config_target c) ms2 x)) /\
       (?k. target_get_pc (machine_config_target
         c) ms1 = init_pc + n2w (k * (2 EXP asm_config_code_alignment
           (target_config (machine_config_target c)))) /\
         k * (2 EXP asm_config_code_alignment (target_config
           (machine_config_target c))) < LENGTH (asm_config_encode
           (target_config (machine_config_target c)) i) /\
         bytes_in_memory init_pc (asm_config_encode (target_config
           (machine_config_target c)) i)
           (target_get_byte (machine_config_target c) ms1)
             (machine_config_prog_addresses c DIFF set_of_list
             (machine_config_ffi_entry_pcs c))) ==>
       (?ms2.
         !k. (evaluate c io (k + (n + 1)) ms1 =
              evaluate (shift_interfer (n + 1) c) io k ms2) /\
             (find_next_interference c io (k + (n + 1)) ms1 =
              find_next_interference (shift_interfer (n + 1) c) io k
                ms2) /\
             target_state_rel (machine_config_target c) s2 ms2)`,
  CHEAT_TAC);;

(* [local] *)
let enc_ok_not_empty = prove
 (`enc_ok c /\ asm_ok w c ==> (~(asm_config_encode c w = []))`,
  CHEAT_TAC);;

let asm_step_IMP_evaluate_step_find_next = prove
 (`!c s1 ms1 io i.
       encoder_correct (machine_config_target c) /\
       (machine_config_prog_addresses c = asm_state_mem_domain s1) /\
       ffi_entry_pcs_disjoint c s1 (LENGTH (asm_config_encode
         (target_config (machine_config_target c)) i)) /\
       interference_ok (machine_config_next_interfer c) (target_proj
         (machine_config_target c) (asm_state_mem_domain s1)) /\
       asm_step (target_config (machine_config_target c)) s1 i
         (asmSem_asm i (asm_state_pc s1 + n2w (LENGTH
           (asm_config_encode (target_config (machine_config_target c))
           i))) s1) /\
       target_state_rel (machine_config_target c) (s1:'a asm_state)
         (ms1:'state) ==>
       (?l ms2. !k. (evaluate c io (k + l) ms1 =
                    evaluate (shift_interfer l c) io k ms2) /\
                   (find_next_interference c io (k + l) ms1 =
                    find_next_interference (shift_interfer l c) io k
                      ms2) /\
                   target_state_rel (machine_config_target c)
                     (asmSem_asm i (asm_state_pc s1 + n2w (LENGTH
                       (asm_config_encode (target_config
                       (machine_config_target c)) i))) s1)
                     ms2 /\ ~(l = 0))`,
  CHEAT_TAC);;

let asm_step_IMP_evaluate_step = prove
 (`!c s1 ms1 io i.
       encoder_correct (machine_config_target c) /\
       (machine_config_prog_addresses c = asm_state_mem_domain s1) /\
       ffi_entry_pcs_disjoint c s1 (LENGTH (asm_config_encode
         (target_config (machine_config_target c)) i)) /\
       interference_ok (machine_config_next_interfer c) (target_proj
         (machine_config_target c) (asm_state_mem_domain s1)) /\
       asm_step (target_config (machine_config_target c)) s1 i
         (asmSem_asm i (asm_state_pc s1 + n2w (LENGTH
           (asm_config_encode (target_config (machine_config_target c))
           i))) s1) /\
       target_state_rel (machine_config_target c) (s1:'a asm_state)
         (ms1:'state) ==>
       (?l ms2.
         (!k. evaluate c io (k + l) ms1 =
              evaluate (shift_interfer l c) io k ms2) /\
         target_state_rel (machine_config_target c)
           (asmSem_asm i (asm_state_pc s1 + n2w (LENGTH
             (asm_config_encode (target_config (machine_config_target
             c)) i))) s1) ms2 /\ ~(l = 0))`,
  CHEAT_TAC);;

(* basic properties *)

(* evaluate_add_clock *)
let targetProps_evaluate_add_clock = prove
 (`!mc_conf ffi k ms k1 r ms1 st1.
    evaluate mc_conf ffi k ms = (r,ms1,st1) /\ ~(r = TimeOut) ==>
    evaluate mc_conf ffi (k + k1) ms = (r,ms1,st1)`,
  CHEAT_TAC);;

(* evaluate_io_events_mono *)
let targetProps_evaluate_io_events_mono = prove
 (`!mc_conf ffi k ms. ffi_state_io_events
     ffi <<= ffi_state_io_events (SND (SND (evaluate mc_conf ffi k
       ms)))`,
  CHEAT_TAC);;

(* evaluate_add_clock_io_events_mono *)
let targetProps_evaluate_add_clock_io_events_mono = prove
 (`!mc_conf ffi k ms k'.
   k <= k' ==> ffi_state_io_events
   (SND (SND (evaluate mc_conf ffi k ms))) <<= ffi_state_io_events
   (SND (SND (evaluate mc_conf ffi k' ms)))`,
  CHEAT_TAC);;

let machine_sem_total = prove
 (`?b. machine_sem mc st ms b`,
  CHEAT_TAC);;

let machine_sem_unique = prove
 (`machine_sem mc ffi ms b1 /\ machine_sem mc ffi ms b2 ==> b1 = b2`,
  CHEAT_TAC);;

let read_ffi_bytearray_IMP_SUBSET_prog_addresses = prove
 (`(read_ffi_bytearray mc a l ms = SOME bytes) ==>
    all_words (target_get_reg (machine_config_target mc) ms a)
      (LENGTH bytes) SUBSET machine_config_prog_addresses
      mc`,
  CHEAT_TAC);;

let encoder_correct_asm_step_target_state_rel = prove
 (`encoder_correct t /\
   target_state_rel t s1 ms /\
   asm_step (target_config t) s1 i s2 ==>
   (?n.
   target_state_rel t s2 (FUNPOW (target_next t) n ms) /\
   (!j. j < n ==>
     (!pc'. pc' IN all_pcs (LENGTH (asm_config_encode (target_config
       t) i)) (asm_state_pc s1) 0 ==>
             (target_get_byte t (FUNPOW (target_next t) j ms) pc' =
               target_get_byte t ms pc')) /\
     (target_get_pc t (FUNPOW (target_next t) j ms) IN
       all_pcs (LENGTH (asm_config_encode (target_config t) i))
         (asm_state_pc s1) (asm_config_code_alignment (target_config
         t))) /\
     (target_state_ok t (FUNPOW (target_next t) j ms))) /\
   (!j x. j <= n /\ ~(x IN asm_state_mem_domain s1) ==>
     (target_get_byte t (FUNPOW (target_next t) j ms) x =
     target_get_byte t ms x)))`,
  CHEAT_TAC);;

let encoder_correct_RTC_asm_step_target_state_rel = prove
 (`encoder_correct t /\
   target_state_rel t s1 ms /\
   RTC (\s1 s2. ?i. asm_step (target_config t) s1 i s2) s1 s2 ==>
   (?n. target_state_rel t s2 (FUNPOW (target_next t) n ms))`,
  CHEAT_TAC);;

(* -- interface lemmas for the interference contracts -- *)

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let ffi_interfer_ok_post_ffi_asm = prove
 (cake_as_vars (fun () ->
    `ffi_interfer_ok pc mc_conf /\
     index < LENGTH (machine_config_ffi_names mc_conf) /\
     mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i
       /\
     index < i /\ machine_config_prog_addresses
     mc_conf = asm_state_mem_domain t1 /\
     read_ffi_bytearrays mc_conf ms2 = (SOME bytes,SOME bytes2) /\
     LENGTH new_bytes = LENGTH bytes2 /\
     (EL index (machine_config_ffi_names mc_conf) = ffi_ExtCall
       (implode "") ==> new_bytes = bytes2) /\
     target_state_rel (machine_config_target mc_conf)
       (asm_state_pc_fupd (K (--(n2w ((3 + index) * ffi_offset)) +
         pc)) t1) ms2 /\
     alignment_aligned (asm_config_code_alignment (target_config
       (machine_config_target mc_conf)))
       (asm_state_regs t1 (match asm_config_link_reg (target_config
         (machine_config_target mc_conf)) with NONE -> 0 | SOME n -> n))
         ==>
     target_state_rel (machine_config_target mc_conf)
       (post_ffi_asm mc_conf t1 new_bytes
          (machine_config_ffi_interfer mc_conf k
            (index,new_bytes,ms2)))
       (machine_config_ffi_interfer mc_conf k
         (index,new_bytes,ms2))`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let ccache_interfer_ok_post_ccache_asm = prove
 (cake_as_vars (fun () ->
    `ccache_interfer_ok pc mc_conf /\
     target_state_rel (machine_config_target mc_conf)
       (asm_state_pc_fupd (K (--(n2w (2 * ffi_offset)) + pc)) t1)
         ms2 /\
     alignment_aligned (asm_config_code_alignment (target_config
       (machine_config_target mc_conf)))
       (asm_state_regs t1 (match asm_config_link_reg (target_config
         (machine_config_target mc_conf)) with NONE -> 0 | SOME n -> n))
         ==>
     target_state_rel (machine_config_target mc_conf)
       (post_ccache_asm mc_conf t1 (machine_config_ccache_interfer
         mc_conf k (a1,a2,ms2)))
       (machine_config_ccache_interfer mc_conf k (a1,a2,ms2))`),
  CHEAT_TAC);;

(* and the accessors of those fields are overloaded again *)
let _ = unhide_overloads ();;
