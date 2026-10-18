(* ======================================================== *)
(*  lab_to_targetProof: ported from HOL4's
    compiler/backend/proofs/lab_to_targetProofScript.sml
    A proof theory about lab_to_target.ml, with 63 definitions and
    383 theorems.  Needed by backendProof.ml and compilerProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for lab_to_target
*)

needs "compiler/backend/labLang.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/backend/proofs/lab_filterProof.ml";;
needs "compiler/backend/proofs/stack_removeProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/labProps.ml";;
needs "compiler/backend/semantics/labSem.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/targetProps.ml";;
needs "compiler/backend/semantics/targetSem.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/encoders/asm/asmProps.ml";;
needs "compiler/encoders/asm/asmSem.ml";;
needs "lib/alignment.ml";;
needs "lib/byte.ml";;
needs "lib/pegexec.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/evaluateProps.ml";;

(* HOL4 lab_to_targetProofScript.sml:16: ML code, not ported *)

let sec_loc_to_pc_def = cake_define
  `(sec_loc_to_pc n2 xs =
    (if n2 = 0 then SOME 0 else match xs with [] -> NONE | (z :: zs)
      ->
      (if (?n1 k. z = labLang_Label n1 n2 k) then SOME 0 else if
        is_Label z then sec_loc_to_pc n2 zs else OPTION_MAP SUC
        (sec_loc_to_pc n2 zs))))`;;

(* HOL4 lab_to_targetProofScript.sml:39: ML code, not ported *)

(* HOL4 lab_to_targetProofScript.sml:49: the overload len_no_lab,
   which the port expands *)

(* -- *)

(* -- evaluate-level semantics preservation of compiler -- *)

(* relate asm step to evaluate step *)

let enc_with_nop_def = cake_define
  `enc_with_nop enc (b:'a asm) bytes =
     (let init = enc b in
     let step = enc (asm_Inst asm_Skip) in
       if LENGTH step = 0 then bytes = init else
         let n = (LENGTH bytes - LENGTH init) DIV LENGTH step in
           bytes = init ++ FLAT (REPLICATE n step))`;;

let asm_step_nop_def = cake_define
  `asm_step_nop bytes c s1 i s2 <=>
     bytes_in_memory (pc s1) bytes (mem s1) (mem_domain s1) /\
     enc_with_nop (asm_config_encode c) i bytes /\
     (match link_reg c with NONE -> T | SOME r -> asm_state_lr s1 =
       r) /\
     (be s1 <=> asm_config_big_endian c) /\ asm_state_align s1 =
       asm_config_code_alignment c /\
     asmSem_asm i (pc s1 + n2w (LENGTH bytes)) s1 = s2 /\ ~failed s2
       /\
     asm_ok i c`;;

(* HOL4 lab_to_targetProofScript.sml:125-130: ML code, not ported *)

(* define relation between labSem and targetSem states *)

let lab_lookup_def = cake_define
  `lab_lookup k1 k2 labs =
     (match sptree_lookup k1 labs with NONE -> NONE | SOME f ->
       sptree_lookup k2 f)`;;

let labs_domain_def = cake_define
  `labs_domain labs = {(n1,n2) | ~(lab_lookup n1 n2 labs = NONE)}`;;


(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let has_odd_inst_def = cake_define_list_cheat CHEAT_TAC
  [`has_odd_inst [] = F`;
   `has_odd_inst (Section k [] :: xs) = has_odd_inst xs`;
   `has_odd_inst (Section k (y :: ys) :: xs) <=>
         ~EVEN (line_length y) \/ has_odd_inst ((Section k ys)
           :: xs)`];;

let line_similar_def = cake_define
  `line_similar x1 x2 =
        match (x1,x2) with
          (labLang_Label k1 k2 l,labLang_Label k1' k2' l') -> (k1 =
            k1') /\ (k2 = k2')
        | ((labLang_Asm b bytes l),(labLang_Asm b' bytes' l')) -> (b
          = b')
        | ((labLang_LabAsm a w bytes l),(labLang_LabAsm a' w' bytes'
          l')) -> (a = a')
        | (_1,_2) -> F`;;

(* HOL4 lab_to_targetProofScript.sml:398: ML code, not ported *)

let code_similar_def = cake_define
  `code_similar x1 x2 =
        match (x1,x2) with
          ([],[]) -> T
        | ((Section s1 lines1 :: rest1),(Section s2 lines2 :: rest2))
          ->
        code_similar rest1 rest2 /\
        EVERY2 line_similar lines1 lines2 /\ (s1 = s2)
        | (_3,_4) -> F`;;

(* HOL4 lab_to_targetProofScript.sml:408: ML code, not ported *)

let word_loc_val_def = cake_define_list
  [`word_loc_val p labs (wordLang_Word w) = SOME w`;
   `word_loc_val p labs (wordLang_Loc k1 k2) =
         (match lab_lookup k1 k2 labs with NONE -> NONE | SOME
           q -> SOME (p + n2w q))`];;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let has_io_name_def = cake_define_list_cheat CHEAT_TAC
  [`has_io_name index [] = F`;
   `has_io_name index (Section k [] :: xs) = has_io_name index xs`;
   `has_io_name index (Section k (y :: ys) :: xs) <=>
         has_io_name index ((Section k ys) :: xs) \/
         (match y with labLang_LabAsm (labLang_CallFFI i) _5 _6
           _7 -> (i = index) | _8 -> F)`];;

(* HOL4 lab_to_targetProofScript.sml:532: ML code, not ported *)

let word_loc_val_byte_def = cake_define
  `word_loc_val_byte p labs m a be' =
     (match word_loc_val p labs (m (byte_align a)) with SOME w ->
       SOME (get_byte a w be') | NONE -> NONE)`;;

let line_ok_def = cake_define
  `line_ok c labs ffis pos x5 =
        match (c,x5) with
          ((c:'a asm_config),labLang_Label _11 _12 l) ->
        EVEN pos /\ (l = 0)
        | (c,(labLang_Asm b bytes l)) ->
        enc_with_nop (asm_config_encode c) (cbw_to_asm b) bytes /\
        (LENGTH bytes = l) /\ asm_ok (cbw_to_asm b) c
        | (c,(labLang_LabAsm labLang_Halt w bytes l)) ->
        (let w1 = ((n2w 0):'a word) - n2w (pos + ffi_offset) in
          enc_with_nop (asm_config_encode c) (Jump w1) bytes /\
          (LENGTH bytes = l) /\ asm_ok (Jump w1) c)
        | (c,(labLang_LabAsm Install w bytes l)) ->
        (let w1 = ((n2w 0):'a word) - n2w (pos + 2 * ffi_offset) in
          enc_with_nop (asm_config_encode c) (Jump w1) bytes /\
          (LENGTH bytes = l) /\ asm_ok (Jump w1) c)
        | (c,(labLang_LabAsm (labLang_CallFFI index) w bytes l)) ->
        (let w1 = ((n2w 0):'a word) - n2w (pos + (3 + get_ffi_index
          ffis (ffi_ExtCall index)) * ffi_offset) in
          enc_with_nop (asm_config_encode c) (Jump w1) bytes /\
          (LENGTH bytes = l) /\ asm_ok (Jump w1) c)
        | (c,(labLang_LabAsm (Call v24) w bytes l)) ->
        F
        | (c,(labLang_LabAsm a w bytes l)) ->
        (match get_label a with labLang_Lab l1 l2 ->
        (match lab_lookup l1 l2 labs with
          NONE -> F | SOME t ->
        (let w1 = n2w t - n2w pos in
          enc_with_nop (asm_config_encode c) (lab_inst w1 a) bytes /\
          (LENGTH bytes = l) /\ asm_ok (lab_inst w1 a) c)))`;;

(* HOL4 lab_to_targetProofScript.sml:571: ML code, not ported *)

let lines_ok_def = cake_define_list
  [`lines_ok c labs ffis pos [] = T`;
   `lines_ok c labs ffis pos (y :: ys) <=>
       line_ok c labs ffis pos y /\
       lines_ok c labs ffis (pos + line_length y) ys`];;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let all_enc_ok_def = cake_define_list_cheat CHEAT_TAC
  [`all_enc_ok c labs ffis pos [] = T`;
   `all_enc_ok c labs ffis pos (Section k [] :: xs) <=>
         EVEN pos /\ all_enc_ok c labs ffis pos xs`;
   `all_enc_ok c labs ffis pos (Section k (y :: ys) :: xs) <=>
         line_ok c labs ffis pos y /\
         all_enc_ok c labs ffis (pos + line_length y) ((Section
           k ys) :: xs)`];;

(* HOL4 lab_to_targetProofScript.sml:589: ML code, not ported *)

let pos_val_def = cake_define_list
  [`pos_val i (pos:num) [] = (pos:num)`;
   `pos_val i (pos:num) (Section k [] :: xs) = ((pos_val i pos
  xs):num)`;
   `pos_val i (pos:num) (Section k (y :: ys) :: xs) =
         ((if is_Label y then pos_val i (pos + line_length y)
           ((Section k ys) :: xs) else if i = (0:num) then pos else
           pos_val (i - 1) (pos + line_length y) ((Section k ys) ::
           xs)):num)`];;

(* HOL4 lab_to_targetProofScript.sml:612: ML code, not ported *)

let sec_pos_val_def = cake_define_list
  [`sec_pos_val i pos [] = NONE`;
   `sec_pos_val i pos (y :: ys) =
       (if is_Label y then
         sec_pos_val i (pos + line_length y) ys else if i = 0
           then SOME pos else sec_pos_val (i - 1) (pos +
           line_length y) ys)`];;

let good_code_def = cake_define
  `lab_to_targetProof_good_code c labs code <=>
    EVERY sec_ends_with_label code /\
    EVERY sec_labels_ok code /\
    ALL_DISTINCT (MAP Section_num code) /\
    EVERY (ALL_DISTINCT o extract_labels o Section_lines) code /\
    DISJOINT (domain labs) (set_of_list (MAP Section_num code)) /\
    restrict_nonzero (get_labels code) SUBSET get_code_labels code
      UNION labs_domain labs /\
    (\c ls. EVERY (sec_ok_pre c) ls) c code`;;
hol4_overload "good_code" "lab_to_targetProof_good_code";;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let num_pcs_def = cake_define_list_cheat CHEAT_TAC
  [`num_pcs [] = (0:num)`;
   `num_pcs (Section _13 [] :: rest) = ((num_pcs rest):num)`;
   `num_pcs (Section k (x :: xs) :: rest) = ((if is_Label x then
  num_pcs ((Section k xs) :: rest) else 1 + num_pcs ((Section k xs)
  :: rest)):num)`];;

let share_mem_domain_code_rel_def = cake_define
  `share_mem_domain_code_rel mc_conf p code2 (s1_shared_mem_domain:'a
  word->bool) <=>
     (!pc' op re a inst' len i.
         (asm_fetch_aux pc' code2 = SOME (labLang_Asm (ShareMem op re
           a) inst' len) /\
         mmio_pcs_min_index (ffi_names mc_conf) = SOME i) ==>
         (?index.
           i <= index /\
           find_index (p + n2w (pos_val pc' 0 code2))
             (machine_config_ffi_entry_pcs mc_conf) 0 =
             SOME index /\
           (let (name,nb) = get_memop_info op in
             EL index (ffi_names mc_conf) = ffi_SharedMem name /\
             (
              ALOOKUP (machine_config_mmio_info mc_conf) index = SOME
                (nb,a,re,p + n2w (pos_val pc' 0 code2 + len)))))) /\
     (!pc' line.
       asm_fetch_aux pc' code2 = SOME line /\
       (!op re a inst' len. ~(line = labLang_Asm (ShareMem op re a)
         inst' len)) ==>
       DISJOINT (set_of_list (machine_config_ffi_entry_pcs mc_conf))
         {p + n2w a + n2w (pos_val pc' 0 code2) |
           a < LENGTH (line_bytes line)}) /\
      (!a.
         byte_align a IN s1_shared_mem_domain ==>
         a IN s1_shared_mem_domain) /\
      (machine_config_shared_addresses mc_conf =
        s1_shared_mem_domain)`;;

let share_mem_state_rel_def = cake_define
  `share_mem_state_rel mc_conf
  (s1:('a,lab_to_target_config,'ffi)labSem_state) t1 ms1 <=>
      (!ms2 k index new_bytes t1 nb ad offs re pc' ad' st new_st i.
       mmio_pcs_min_index (ffi_names mc_conf) = SOME i /\
       i <= index /\ index < LENGTH (ffi_names mc_conf) /\ RTC
       call_FFI_rel (state_ffi s1) st /\
       ALOOKUP (machine_config_mmio_info mc_conf) index = SOME
         (nb,Addr ad offs,re,pc') /\
       (machine_config_prog_addresses mc_conf = mem_domain t1) /\
       ad' = target_get_reg (machine_config_target mc_conf) ms2 ad +
         offs /\
       target_state_rel (machine_config_target mc_conf)
         (pc_fupd (K (EL index (machine_config_ffi_entry_pcs
           mc_conf))) t1) ms2 ==>
       (?op. EL index (ffi_names mc_conf) = ffi_SharedMem op /\
          (match op with MappedRead ->
          ((if nb = (n2w 0) then (w2n ad' MOD (dimindex (:'a) DIV 8))
            = 0 else T) /\
          (ad' IN machine_config_shared_addresses mc_conf) /\
          is_valid_mapped_read (target_get_pc (machine_config_target
            mc_conf) ms2) nb (Addr ad offs) re pc'
            (machine_config_target
            mc_conf) ms2 (machine_config_prog_addresses mc_conf) /\
          call_FFI st (ffi_SharedMem MappedRead)
            [nb]
            (word_to_bytes ad' F) =
            FFI_return new_st new_bytes ==>
           target_state_rel (machine_config_target mc_conf)
             (regs_fupd (K (\n. if n = re then
                    (word_of_bytes F (n2w 0) new_bytes) else regs t1
                      n)) (pc_fupd (K pc') t1))
               (machine_config_ffi_interfer mc_conf k
                 (index,new_bytes,ms2))) | MappedWrite ->
          ((if nb = (n2w 0) then (w2n ad' MOD (dimindex (:'a) DIV 8))
            = 0 else T) /\
           (ad' IN machine_config_shared_addresses mc_conf) /\
           is_valid_mapped_write (target_get_pc
             (machine_config_target mc_conf) ms2) nb (Addr ad offs) re
             pc' (machine_config_target
             mc_conf) ms2 (machine_config_prog_addresses mc_conf) /\
          call_FFI st (ffi_SharedMem MappedWrite)
           [nb]
           (
            (let w = target_get_reg (machine_config_target mc_conf)
              ms2 re in
               if nb = (n2w 0) then word_to_bytes w F else
                 word_to_bytes_aux (w2n nb) w F) ++ (word_to_bytes ad'
                 F)) =
           FFI_return new_st new_bytes ==>
           target_state_rel (machine_config_target mc_conf)
             (pc_fupd (K pc') t1)
             (machine_config_ffi_interfer mc_conf k
               (index,new_bytes,ms2)))))) /\
    (!index i. mmio_pcs_min_index (ffi_names mc_conf) = SOME i /\
       index < LENGTH (ffi_names mc_conf) /\ i <= index ==>
         ~(machine_config_halt_pc
       mc_conf = (EL index (machine_config_ffi_entry_pcs mc_conf)))
         /\ ~(machine_config_ccache_pc
       mc_conf = (EL index (machine_config_ffi_entry_pcs
         mc_conf))))`;;

let no_install_or_no_share_mem_def = cake_define
  `no_install_or_no_share_mem code ffi_names' <=>
    (no_share_mem_inst code /\
     EVERY (\x. ?s. x = ffi_ExtCall s) ffi_names') \/
     no_install code`;;

(* The lab-level oracles record the register residues that the machine run
   starting from ms actually leaves behind: the k-th entry of each family is
   read off the k-th interference application of that family.
   This is positional, so it is kept out of state_rel (which is closed under
   shift_interfer) and threaded through compile_correct separately. *)
let oracle_tie_def = cake_define
  `oracle_tie (mc_conf:('a,'state,'b)machine_config) ms
  (s1:('a,'c,'ffi)labSem_state) <=> labSem_state_io_regs
     s1 = target_io_regs mc_conf (state_ffi s1) ms /\
       labSem_state_io_fp_regs
     s1 = target_io_fp_regs mc_conf (state_ffi s1) ms /\
       labSem_state_cc_regs
     s1 = target_cc_regs mc_conf (state_ffi s1) ms /\
       labSem_state_cc_fp_regs
     s1 = target_cc_fp_regs mc_conf (state_ffi s1) ms`;;

(* The code buffer is set-up to immediately follow the current code:
  |---code---|---cb---|
*)
let state_rel_def = cake_define
  `lab_to_targetProof_state_rel (mc_conf,code2,labs,p)
  (s1:('a,lab_to_target_config,'ffi)labSem_state) t1 ms1 <=>
     target_state_rel (machine_config_target mc_conf) t1 ms1 /\
       good_dimindex (:'a) /\
     (machine_config_prog_addresses mc_conf = mem_domain t1) /\
     ~(machine_config_halt_pc mc_conf IN
       machine_config_prog_addresses mc_conf) /\
     ~(machine_config_ccache_pc mc_conf IN
       machine_config_prog_addresses mc_conf) /\
     reg_ok (ptr_reg s1) (target_config (machine_config_target
       mc_conf)) /\ (ptr_reg mc_conf = ptr_reg s1) /\
     reg_ok (len_reg s1) (target_config (machine_config_target
       mc_conf)) /\ (len_reg mc_conf = len_reg s1) /\
     reg_ok (ptr2_reg s1) (target_config (machine_config_target
       mc_conf)) /\ (ptr2_reg mc_conf = ptr2_reg s1) /\
     reg_ok (len2_reg s1) (target_config (machine_config_target
       mc_conf)) /\ (len2_reg mc_conf = len2_reg s1) /\
     reg_ok (link_reg s1) (target_config (machine_config_target
       mc_conf)) /\
     (?i. mmio_pcs_min_index (ffi_names mc_conf) = SOME i /\
          (!index. if i <= index /\ index < LENGTH (ffi_names
            mc_conf) then ?info. ALOOKUP (machine_config_mmio_info
            mc_conf) index = SOME info else ALOOKUP
            (machine_config_mmio_info mc_conf) index = NONE)) /\
     (!ms2 k index new_bytes t1 bytes bytes2 st new_st i.
        mmio_pcs_min_index (ffi_names mc_conf) = SOME i /\
        index < i /\
        read_ffi_bytearrays mc_conf ms2 = (SOME bytes,SOME bytes2) /\
          RTC
        call_FFI_rel (state_ffi s1) st /\
        call_FFI st (EL index (ffi_names mc_conf)) bytes bytes2 =
          FFI_return new_st new_bytes /\
        (machine_config_prog_addresses mc_conf = mem_domain t1) /\
        target_state_rel (machine_config_target mc_conf)
          (pc_fupd (K (p - n2w ((3 + index) * ffi_offset))) t1) ms2
            /\
        alignment_aligned (asm_config_code_alignment (target_config
          (machine_config_target mc_conf))) (regs t1 (link_reg s1)) ==>
        (let ms' = machine_config_ffi_interfer mc_conf k
          (index,new_bytes,ms2) in
           target_state_rel (machine_config_target mc_conf)
             (pc_fupd (K (regs t1 (link_reg s1))) (mem_fupd (K
               (asm_write_bytearray (regs t1 (ptr2_reg s1)) new_bytes
               (mem t1))) (fp_regs_fupd (K (\n. target_get_fp_reg
               (machine_config_target mc_conf) ms' n)) (regs_fupd (K
               (\a. if MEM a (machine_config_callee_saved_regs mc_conf)
               \/
                              ~(a < asm_config_reg_count
                                (target_config (machine_config_target
                                mc_conf))) \/
                              MEM a (asm_config_avoid_regs
                                (target_config (machine_config_target
                                mc_conf))) then regs t1 a else
                                target_get_reg (machine_config_target
                                mc_conf) ms' a)) t1))))
             ms')) /\
     (!ms2 t1 k a1 a2.
       target_state_rel (machine_config_target mc_conf)
         (pc_fupd (K (p - n2w ((2 * ffi_offset)))) t1) ms2 /\
       alignment_aligned (asm_config_code_alignment (target_config
         (machine_config_target mc_conf))) (regs t1 (link_reg s1)) ==>
       (let ms' = machine_config_ccache_interfer mc_conf k
         (a1,a2,ms2) in
          target_state_rel (machine_config_target mc_conf)
            (pc_fupd (K (regs t1 (link_reg s1))) (fp_regs_fupd (K
              (\n. target_get_fp_reg (machine_config_target mc_conf) ms'
              n)) (regs_fupd (K (\a. if MEM a
              (machine_config_callee_saved_regs mc_conf) \/
                              a = ptr_reg s1 \/
                              ~(a < asm_config_reg_count
                                (target_config (machine_config_target
                                mc_conf))) \/
                              MEM a (asm_config_avoid_regs
                                (target_config (machine_config_target
                                mc_conf))) then regs t1 a else
                                target_get_reg (machine_config_target
                                mc_conf) ms' a)) t1)))
            ms')) /\ compile
     s1 = compile_lab (target_config (machine_config_target mc_conf))
       /\
     (no_share_mem_inst code2 ==> (!k. let (cfg,code) =
       compile_oracle s1 k in
             lab_to_targetProof_good_code (target_config
               (machine_config_target mc_conf))
               (lab_to_target_config_labels cfg) code /\
             no_share_mem_inst code /\
             (k = 0 ==> lab_to_target_config_labels
             cfg = labs /\ lab_to_target_config_pos
             cfg = LENGTH (prog_to_bytes code2) /\ ffi_names
             cfg = SOME (ffi_names mc_conf)))) /\
     (!l1 l2 x.
        (lab_lookup l1 l2 labs = SOME x) ==> EVEN x) /\
     (((n2w 1) && p) = (n2w 0)) /\
     (list_subset
       (FILTER (\x. ?s. x = ffi_ExtCall s) (find_ffi_names
         (state_code s1))) (ffi_names
       mc_conf)) /\
     EVEN (LENGTH (prog_to_bytes code2)) /\
     (!name i.
         MEM name (ffi_names mc_conf) /\
         mmio_pcs_min_index (ffi_names mc_conf) = SOME i /\
         get_ffi_index (ffi_names mc_conf) name < i ==>
         (?s. name = ffi_ExtCall s) /\
        ~(p - n2w ((3 + get_ffi_index (ffi_names mc_conf) name) *
          ffi_offset) IN machine_config_prog_addresses mc_conf) /\
        ~(p - n2w ((3 + get_ffi_index (ffi_names mc_conf) name) *
          ffi_offset) = machine_config_halt_pc mc_conf) /\
        ~(p - n2w ((3 + get_ffi_index (ffi_names mc_conf) name) *
          ffi_offset) = machine_config_ccache_pc mc_conf) /\
        (find_index (p - n2w ((3 + get_ffi_index (ffi_names mc_conf)
          name) * ffi_offset)) (machine_config_ffi_entry_pcs
                    mc_conf) 0 = SOME (get_ffi_index (ffi_names
                      mc_conf) name))) /\
     (p - n2w ffi_offset = machine_config_halt_pc mc_conf) /\
     (p - n2w (2 * ffi_offset) = machine_config_ccache_pc mc_conf) /\
     interference_ok (machine_config_next_interfer mc_conf)
       (target_proj (machine_config_target mc_conf) (mem_domain t1)) /\
     (!l1 l2 x2.
        (loc_to_pc l1 l2 (state_code s1) = SOME x2) ==>
        (lab_lookup l1 l2 labs = SOME (pos_val x2 0 code2))) /\
     (!r. fp_regs s1 r = fp_regs t1 r) /\
     (!r. word_loc_val p labs (regs s1 r) = SOME (regs t1 r)) /\
     (!a. byte_align a IN mem_domain s1 ==>
          a IN mem_domain t1 /\ a IN mem_domain s1 /\
          (word_loc_val_byte p labs (mem s1) a (be s1) = SOME (mem t1
            a))) /\
     (!n.
       n < buffer_space_left (state_code_buffer s1) ==>
       (let addr' = buffer_position (state_code_buffer s1) + n2w
         (LENGTH (buffer_buffer (state_code_buffer s1)) + n) in
       addr' IN mem_domain t1 /\ ~(
       addr' IN mem_domain s1))) /\
     bytes_in_mem p (prog_to_bytes code2) (mem
       t1) (mem_domain t1) (mem_domain s1) /\ buffer_position
         (state_code_buffer
     s1) = p + n2w (LENGTH (prog_to_bytes code2)) /\
     bytes_in_mem (buffer_position (state_code_buffer s1))
       (buffer_buffer (state_code_buffer s1)) (mem
       t1) (mem_domain t1) (mem_domain s1) /\
     LENGTH (prog_to_bytes code2) + LENGTH (buffer_buffer
       (state_code_buffer s1)) + buffer_space_left (state_code_buffer
       s1) < dimword (:'a) /\
     (!bn.
       bn < LENGTH (buffer_buffer (state_code_buffer s1)) +
         buffer_space_left (state_code_buffer s1) ==>
       ~MEM (buffer_position (state_code_buffer s1) + n2w bn)
         (machine_config_ffi_entry_pcs mc_conf)) /\
     ~failed s1 /\ ~failed t1 /\ (be s1 = be t1) /\
     (pc t1 = p + n2w (pos_val (pc s1) 0 code2)) /\
     ((p && n2w (2 EXP asm_state_align t1 - 1)) = (n2w 0)) /\
     (match link_reg (target_config (machine_config_target mc_conf))
       with NONE -> T | SOME r -> asm_state_lr t1 = r) /\
     (be t1 <=> asm_config_big_endian (target_config
       (machine_config_target mc_conf))) /\
     (asm_state_align t1 = asm_config_code_alignment (target_config
       (machine_config_target mc_conf))) /\
     (enc_ok (target_config (machine_config_target mc_conf))) /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs
       (TAKE (THE (mmio_pcs_min_index (ffi_names mc_conf)))
         (ffi_names mc_conf)) 0 code2 /\
     EVERY sec_labels_ok code2 /\
     code_similar (state_code s1) code2 /\
     share_mem_state_rel mc_conf s1 t1 ms1 /\
     share_mem_domain_code_rel mc_conf p code2
       (labSem_state_shared_mem_domain s1) /\
     LENGTH (ffi_names mc_conf) = LENGTH
       (machine_config_ffi_entry_pcs mc_conf) /\
     no_install_or_no_share_mem code2 (ffi_names mc_conf)`;;
hol4_overload "state_rel" "lab_to_targetProof_state_rel";;

(* bytes_in_memory lemmas *)

(* HOL4 lab_to_targetProofScript.sml:1210-1212: ML code, not ported *)

(* HOL4 lab_to_targetProofScript.sml:1240: the ML values that the
   definitions below antiquote *)

(* HOL4 lab_to_targetProofScript.sml:1281-1284: the ML values that
   the definitions below antiquote *)

(* read/write bytearrays for FFI *)

(* inst correct *)

(* The lab and asm versions should be in their individual props *)

(* HOL4 lab_to_targetProofScript.sml:2138-2144: a proof *)

(* compile correct *)

(* HOL4 lab_to_targetProofScript.sml:2955-2979: a proof *)

(* HOL4 lab_to_targetProofScript.sml:2981: the ML values that the
   definitions below antiquote *)

(* HOL4 lab_to_targetProofScript.sml:3052: ML code, not ported *)

(* -- syntactic properties of remove_labels -- *)

(* annotated line length *)

let line_len_def = cake_define_list
  [`line_len (labLang_Label _16 _17 l) = l`;
   `line_len (labLang_Asm _18 _19 l) = l`;
   `line_len (labLang_LabAsm _20 _21 _22 l) = l`];;

(* annotated section length *)

(* simple syntactic properties of compiler functions *)

let enc_lines_again_simp_def = cake_define_list
  [`enc_lines_again_simp labs ffis pos enc [] = ([],T)`;
   `enc_lines_again_simp labs ffis pos enc (labLang_LabAsm a w bytes l
  :: xs) =
        (let w1 = get_jump_offset a ffis labs pos in
          if w = w1 then
            let (rest,ok) = enc_lines_again_simp labs ffis (pos + l)
              enc xs in
              (labLang_LabAsm a w bytes l :: rest,ok) else
            let bs = enc (lab_inst w1 a) in
            let l1 = MAX (LENGTH bs) l in
            let (rest,ok) = enc_lines_again_simp labs ffis (pos +
              l1) enc xs in
              (labLang_LabAsm a w1 bs l1 :: rest,(l1 = l /\ ok)))`;
   `enc_lines_again_simp labs ffis pos enc (labLang_Label k1 k2 l :: xs)
  =
        (let (rest,ok) = enc_lines_again_simp labs ffis (pos + l)
          enc xs in
        ((labLang_Label k1 k2 l:'a line) :: rest,ok))`;
   `enc_lines_again_simp labs ffis pos enc (labLang_Asm x1 x2 l :: xs) =
        (let (rest,ok) = enc_lines_again_simp labs ffis (pos + l)
          enc xs in
        (labLang_Asm x1 x2 l :: rest,ok))`];;

(* HOL4 lab_to_targetProofScript.sml:3172: ML code, not ported *)

(* code_similar preservation *)

(* HOL4 lab_to_targetProofScript.sml:3402-3408: a proof *)

(* implications of code_similar *)

(* sec_label_ok preservation *)

(* invariant: lines are encoded and non-label lengths annotated *)

let line_encd0_def = cake_define
  `line_encd0 enc x2 =
        match x2 with
          labLang_Asm b bytes len ->
       enc (cbw_to_asm b) = bytes /\ len = LENGTH bytes
        | (labLang_LabAsm l w bytes len) ->
        enc (lab_inst w l) = bytes /\ LENGTH bytes <= len /\
        (?w'. len = LENGTH (enc (lab_inst w' l)))
        | _23 -> T`;;

let sec_encd0_def = cake_define
  `sec_encd0 enc (Section _24 ls) = EVERY (line_encd0 enc) ls`;;

(* HOL4 lab_to_targetProofScript.sml:3628: the overload all_encd0,
   which the port expands *)

(* establishing encd0 *)

(* encd0 preservation *)

(* invariant: annotated lengths are not too small *)
(* this is a consequence of encd (below) and not treated separately much *)

let line_length_leq_def = cake_define
  `line_length_leq x1 =
        match x1 with
          labLang_LabAsm _25 _26 bytes l ->
       LENGTH bytes <= l
        | (labLang_Asm _27 bytes l) ->
       LENGTH bytes <= l
        | _28 -> T`;;

let sec_length_leq_def = cake_define
  `sec_length_leq (Section _29 ls) = EVERY line_length_leq ls`;;

(* HOL4 lab_to_targetProofScript.sml:3713: the overload
   all_length_leq, which the port expands *)

(* invariant: label annotated lengths are 0 or 1 *)

let label_one_def = cake_define
  `label_one x1 =
        match x1 with
          labLang_Label _32 _33 n -> n <= 1
        | _34 -> T`;;

let sec_label_one_def = cake_define
  `sec_label_one (Section _35 ls) = EVERY label_one ls`;;

(* establishing label_one *)

(* label_one preservation *)

(* simple consequences of label_one *)

(* invariant: lines are encoded and annotated lengths are correct *)

let line_encd_def = cake_define
  `line_encd enc labs ffis pos x5 =
        match x5 with
          labLang_Asm b bytes len ->
       enc (cbw_to_asm b) = bytes /\ len = LENGTH bytes
        | (labLang_LabAsm labLang_Halt _36 bytes len) ->
       enc (Jump (--n2w (pos + ffi_offset))) = bytes /\
       LENGTH bytes <= len
        | (labLang_LabAsm Install _37 bytes len) ->
       enc (Jump (--n2w (pos + 2 * ffi_offset))) = bytes /\
       LENGTH bytes <= len
        | (labLang_LabAsm (labLang_CallFFI s) _38 bytes len) ->
       enc (Jump (--n2w (pos + (get_ffi_index ffis (ffi_ExtCall s) +
         3) * ffi_offset))) = bytes /\
       LENGTH bytes <= len
        | (labLang_LabAsm (Jump l) _39 bytes len) ->
       enc (Jump (n2w (find_pos l labs) + --n2w pos)) = bytes /\
       LENGTH bytes <= len
        | (labLang_LabAsm (JumpCmp a b c l) _40 bytes len) ->
       enc (JumpCmp a b c (n2w (find_pos l labs) + --n2w pos)) =
         bytes /\
       LENGTH bytes <= len
        | (labLang_LabAsm (LocValue k l) _41 bytes len) ->
       enc (Loc k (n2w (find_pos l labs) + --n2w pos)) = bytes /\
       LENGTH bytes <= len
        | (labLang_LabAsm (Call l) _42 bytes len) ->
       enc (Call (n2w (find_pos l labs) + --n2w pos)) = bytes /\
       LENGTH bytes <= len
        | _43 -> T`;;

(* HOL4 lab_to_targetProofScript.sml:3836: ML code, not ported *)

let lines_encd_def = cake_define_list
  [`lines_encd enc labs ffis pos [] <=> T`;
   `lines_encd enc labs ffis pos (l :: ls) <=>
       line_encd enc labs ffis pos l /\
       lines_encd enc labs ffis (pos + line_len l) ls`];;

let all_encd_def = cake_define_list
  [`all_encd enc labs ffis pos [] <=> T`;
   `all_encd enc labs ffis pos (Section k ls :: ss) <=>
       lines_encd enc labs ffis pos ls /\
       all_encd enc labs ffis (pos + SUM (MAP line_len ls)) ss`];;

(* length_leq follows from encd *)

(* establishing encd *)

(* invariant: annotated lengths are correct *)

let line_length_ok_def = cake_define
  `line_length_ok l <=> LENGTH (line_bytes l) = line_len l`;;

let sec_length_ok_def = cake_define
  `sec_length_ok (Section _44 ls) = EVERY line_length_ok ls`;;

(* simple consequences of length_ok *)

(* invariant: all labels annotated with length 0 *)

let label_zero_def = cake_define
  `label_zero x1 =
        match x1 with
          labLang_Label _47 _48 n -> n = 0
        | _49 -> T`;;

let sec_label_zero_def = cake_define
  `sec_label_zero (Section _50 ls) = EVERY label_zero ls`;;

(* label_zero preservation *)

(* simple consequences of label_zero *)

(* invariant: lines aligned *)

let line_aligned_def = cake_define
  `line_aligned m l <=>
     line_len l MOD m = 0 /\
     line_length l MOD m = 0`;;

let sec_aligned_def = cake_define
  `sec_aligned noplen (Section _51 ls) = EVERY (line_aligned noplen)
  ls`;;

(* establishing aligned *)

(* aligned preservation *)

(* invariant: all initial labels have annotated length 0 *)

let label_prefix_zero_def = cake_define
  `label_prefix_zero ls <=>
      (!n. n < LENGTH ls /\ (!m. m <= n ==> is_Label (EL m ls)) ==>
         (!m. m <= n ==> line_len (EL m ls) = 0))`;;

let sec_label_prefix_zero_def = cake_define
  `sec_label_prefix_zero (Section k ls) <=> label_prefix_zero ls`;;

(* establishing label_prefix_zero *)

(* label_prefix_zero preservation *)

(* simple consequences of label_prefix_zero *)

(* invariant: lines encd with nops *)

let line_enc_with_nop_def = cake_define
  `line_enc_with_nop enc labs ffis pos x5 =
        match x5 with
          labLang_Asm b bytes len ->
       enc_with_nop enc (cbw_to_asm b) bytes /\ LENGTH bytes = len
        | (labLang_LabAsm labLang_Halt _52 bytes len) ->
       enc_with_nop enc (Jump (--n2w (pos + ffi_offset))) bytes /\
       LENGTH bytes = len
        | (labLang_LabAsm Install _53 bytes len) ->
       enc_with_nop enc (Jump (--n2w (pos + 2 * ffi_offset))) bytes
         /\
       LENGTH bytes = len
        | (labLang_LabAsm (labLang_CallFFI s) _54 bytes len) ->
       enc_with_nop enc (Jump (--n2w (pos + (get_ffi_index ffis
         (ffi_ExtCall s) + 3) * ffi_offset))) bytes /\
       LENGTH bytes = len
        | (labLang_LabAsm (Jump l) _55 bytes len) ->
       enc_with_nop enc (Jump (n2w (find_pos l labs) + --n2w pos))
         bytes /\
       LENGTH bytes = len
        | (labLang_LabAsm (JumpCmp a b c l) _56 bytes len) ->
       enc_with_nop enc (JumpCmp a b c (n2w (find_pos l labs) + --n2w
         pos)) bytes /\
       LENGTH bytes = len
        | (labLang_LabAsm (LocValue k l) _57 bytes len) ->
       enc_with_nop enc (Loc k (n2w (find_pos l labs) + --n2w pos))
         bytes /\
       LENGTH bytes = len
        | (labLang_LabAsm _58 _59 bytes len) -> LENGTH bytes = len
        | (labLang_Label _60 _61 len) -> len = 0`;;

(* HOL4 lab_to_targetProofScript.sml:4357: ML code, not ported *)

let lines_enc_with_nop_def = cake_define_list
  [`lines_enc_with_nop enc labs ffis pos [] <=> T`;
   `lines_enc_with_nop enc labs ffis pos (l :: ls) <=>
       line_enc_with_nop enc labs ffis pos l /\
       lines_enc_with_nop enc labs ffis (pos + line_length l)
         ls`];;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let all_enc_with_nop_def = cake_define_list_cheat CHEAT_TAC
  [`all_enc_with_nop enc labs ffis pos [] <=> T`;
   `all_enc_with_nop enc labs ffis pos (Section k [] :: xs) <=>
       all_enc_with_nop enc labs ffis pos xs`;
   `all_enc_with_nop enc labs ffis pos (Section k (y :: ys) :: xs) <=>
       line_enc_with_nop enc labs ffis pos y /\
       all_enc_with_nop enc labs ffis (pos + line_length y)
         (Section k ys :: xs)`];;

(* HOL4 lab_to_targetProofScript.sml:4384: ML code, not ported *)

(* enc_with_nop implies length_ok *)

(* enc_with_nop implies label_zero *)

(* line_ok implies enc_with_nop *)

(* establishing enc_with_nop *)

(* invariant: label annotation correctly records alignment *)

let line_lab_len_pos_ok_def = cake_define
  `line_lab_len_pos_ok pos x2 =
        match x2 with
          labLang_Label _64 _65 l ->
        (if EVEN pos then l = 0 else l = 1)
        | _66 -> T`;;

let lab_len_pos_ok_def = cake_define_list
  [`lab_len_pos_ok pos [] <=> T`;
   `lab_len_pos_ok pos (l :: ls) <=>
         line_lab_len_pos_ok pos l /\
         lab_len_pos_ok (pos + line_len l) ls`];;

let all_lab_len_pos_ok_def = cake_define_list
  [`all_lab_len_pos_ok _67 [] <=> T`;
   `all_lab_len_pos_ok pos (Section k ls :: ss) <=>
       lab_len_pos_ok pos ls /\
       all_lab_len_pos_ok (pos + sec_length ls 0) ss`];;

(* HOL4 lab_to_targetProofScript.sml:4714: ML code, not ported *)

(* establishing pos_ok *)

(* pos_ok preservation *)

(* invariant: jump offsets ok *)

let line_offset_ok_def = cake_define
  `line_offset_ok labs ffis pos x4 =
        match x4 with
          labLang_LabAsm a w bytes _68 ->
       w = get_jump_offset a ffis labs pos
        | _69 -> T`;;

let lines_offset_ok_def = cake_define_list
  [`lines_offset_ok labs ffis pos [] <=> T`;
   `lines_offset_ok labs ffis pos (l :: ls) <=>
       line_offset_ok labs ffis pos l /\
       lines_offset_ok labs ffis (pos + line_len l) ls`];;

let offset_ok_def = cake_define_list
  [`lab_to_targetProof_offset_ok labs ffis pos [] <=> T`;
   `lab_to_targetProof_offset_ok labs ffis pos (Section k ls :: ss) <=>
       lines_offset_ok labs ffis pos ls /\
       lab_to_targetProof_offset_ok labs ffis (pos + SUM (MAP
         line_len ls)) ss`];;
hol4_overload "offset_ok" "lab_to_targetProof_offset_ok";;

(* HOL4 lab_to_targetProofScript.sml:4892: ML code, not ported *)

(* establishing offset_ok *)

(* offset_ok preservation *)

(* invariant: referenced labels exist *)

let line_labs_exist_def = cake_define
  `line_labs_exist labs x2 =
        match x2 with
          labLang_LabAsm a _70 _71 _72 ->
       (!n1 n2. (n1,n2) IN labs_of a ==> ~(lab_lookup n1 n2 labs =
         NONE))
        | _73 -> T`;;

(* HOL4 lab_to_targetProofScript.sml:4998: ML code, not ported *)

let sec_labs_exist_def = cake_define
  `sec_labs_exist labs (Section _74 ls) <=> EVERY (line_labs_exist
  labs) ls`;;

(* HOL4 lab_to_targetProofScript.sml:5004: the overload
   all_labs_exist, which the port expands *)

(* Remove tail recursion from zero_labs_acc_exist *)

(* labs_exist preservation *)

(* establishing labs_exist *)

(* invariant: labels aligned at even positions *)

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let even_labels_def = cake_define_list_cheat CHEAT_TAC
  [`even_labels pos [] <=> T`;
   `even_labels pos (Section _75 [] :: ls) <=> even_labels pos ls`;
   `even_labels pos (Section k (y :: ys) :: ls) <=>
       (is_Label y ==> EVEN pos) /\
       even_labels (pos + line_len y) (Section k ys :: ls)`];;

(* HOL4 lab_to_targetProofScript.sml:5229: ML code, not ported *)

let lines_even_labels_def = cake_define_list
  [`lines_even_labels pos [] <=> T`;
   `lines_even_labels pos (y :: ys) <=>
       (is_Label y ==> EVEN pos) /\
       lines_even_labels (pos + line_len y) ys`];;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let even_labels_strong_def = cake_define_list_cheat CHEAT_TAC
  [`even_labels_strong pos [] <=> T`;
   `even_labels_strong pos (Section _76 [] :: ls) <=>
        EVEN pos /\ even_labels_strong pos ls`;
   `even_labels_strong pos (Section k (y :: ys) :: ls) <=>
       (is_Label y ==> EVEN pos) /\
       even_labels_strong (pos + line_len y) (Section k ys ::
         ls)`];;

(* HOL4 lab_to_targetProofScript.sml:5405-5413: code that the source
   has in a comment *)

(* HOL4 lab_to_targetProofScript.sml:5645-5665: code that the source
   has in a comment *)

(* HOL4 lab_to_targetProofScript.sml:5715-5735: code that the source
   has in a comment *)

(** End syntactic stuff **)

(* HOL4 lab_to_targetProofScript.sml:6959-6967: ML code, not ported *)

(* HOL4 lab_to_targetProofScript.sml:6969-6978: a proof *)

(* HOL4 lab_to_targetProofScript.sml:6980-7059: a proof *)

(* HOL4 lab_to_targetProofScript.sml:7061-7157: a proof *)

(* HOL4 lab_to_targetProofScript.sml:7171-7200: a proof *)

(* move *)

(* HOL4 lab_to_targetProofScript.sml:7526: ML code, not ported *)

(* HOL4 lab_to_targetProofScript.sml:7560-7717: a proof *)

(* HOL4 lab_to_targetProofScript.sml:7719: a proof *)
(* CBW *)
(* HOL4 lab_to_targetProofScript.sml:7721-7805: a proof *)
      (* non-overlap of cb with code *)
(* HOL4 lab_to_targetProofScript.sml:7807-7812: a proof *)
      (* non-overlap of cb with itself *)
(* HOL4 lab_to_targetProofScript.sml:7814-7827: a proof *)

(* HOL4 lab_to_targetProofScript.sml:7829: a proof *)
(* share_mem_op *)
(* HOL4 lab_to_targetProofScript.sml:7831-7844: a proof *)

(* HOL4 lab_to_targetProofScript.sml:7846-7849: a proof *)

(* HOL4 lab_to_targetProofScript.sml:7851-7856: a proof *)

(* HOL4 lab_to_targetProofScript.sml:7858-7866: a proof *)


(* HOL4 lab_to_targetProofScript.sml:7927-7945: a proof *)

(* HOL4 lab_to_targetProofScript.sml:7947-7952: a proof *)

(* HOL4 lab_to_targetProofScript.sml:7954: ML code, not ported *)

(* HOL4 lab_to_targetProofScript.sml:7956-7965: a proof *)

(* HOL4 lab_to_targetProofScript.sml:7967: a proof *)
(* Jump *)
(* HOL4 lab_to_targetProofScript.sml:7969-8050: a proof *)

(* HOL4 lab_to_targetProofScript.sml:8052: a proof *)
(* JumpCmp *)
(* HOL4 lab_to_targetProofScript.sml:8054-8065: a proof *)


(* HOL4 lab_to_targetProofScript.sml:8068-8197: a proof *)

(* HOL4 lab_to_targetProofScript.sml:8199: a proof *)
(* Call *)
(* HOL4 lab_to_targetProofScript.sml:8201-8212: a proof *)

(* HOL4 lab_to_targetProofScript.sml:8214: a proof *)
(* LocValue *)
(* HOL4 lab_to_targetProofScript.sml:8216-8290: a proof *)

(* HOL4 lab_to_targetProofScript.sml:8292: a proof *)
(* CallFFI *)
(* HOL4 lab_to_targetProofScript.sml:8294-8407: a proof *)

(* HOL4 lab_to_targetProofScript.sml:8409-8467: a proof *)

(* HOL4 lab_to_targetProofScript.sml:8469-8476: a proof *)
  (* FFI_return *)
(* HOL4 lab_to_targetProofScript.sml:8478-8752: a proof *)

(* HOL4 lab_to_targetProofScript.sml:8754: a proof *)
(* Install *)
(* HOL4 lab_to_targetProofScript.sml:8756-9280: a proof *)

(* HOL4 lab_to_targetProofScript.sml:9282: a proof *)
(* Halt *)
(* HOL4 lab_to_targetProofScript.sml:9284-9351: a proof *)

(* HOL4 lab_to_targetProofScript.sml:9353: a proof *)

(* relating observable semantics *)

let init_ok_def = cake_define
  `init_ok (mc_conf,p) s ms <=>
     (?code2 labs t1.
       state_rel (mc_conf,code2,labs,p) s t1 ms /\
       oracle_tie mc_conf ms s)`;;

(* HOL4 lab_to_targetProofScript.sml:9528-9531: code that the source
   has in a comment *)

(* introducing make_init *)

let set_bytes_def = cake_define_list
  [`set_bytes a be' [] = (n2w 0)`;
   `set_bytes a be' (b :: bs) = set_byte a b (set_bytes (a + (n2w
  1)) be' bs) be'`];;

let make_word_def = cake_define
  `make_word be' m (a:'a word) =
     (if dimindex (:'a) = 32 then
       wordLang_Word (set_bytes a be' [m a; m (a + (n2w 1)); m (a +
         (n2w 2)); m (a + (n2w 3))]) else
       wordLang_Word (set_bytes a be' [m a; m (a + (n2w 1)); m (a +
         (n2w 2)); m (a + (n2w 3));
                             m (a + (n2w 4)); m (a + (n2w 5)); m
                               (a + (n2w 6)); m (a + (n2w 7))]))`;;

let make_init_def = cake_define
  `lab_to_targetProof_make_init mc_conf (ffi:'ffi ffi_state) t m dm sdm
  (ms:'state) code
     comp' cbpos cbspace coracle =
     mk_labSem_state (\k. wordLang_Word ((regs t k):'a word))
       (fp_regs t) m dm sdm 0 (asm_config_big_endian (target_config
       (machine_config_target mc_conf))) ffi (target_io_regs mc_conf
       ffi ms) (target_cc_regs mc_conf ffi ms) (target_io_fp_regs
       mc_conf ffi ms) (target_cc_fp_regs mc_conf ffi ms) code comp'
       coracle (mk_buffer cbpos [] cbspace) 0 F (ptr_reg mc_conf)
       (len_reg mc_conf) (ptr2_reg mc_conf) (len2_reg mc_conf) (match
       link_reg (target_config (machine_config_target mc_conf)) with
       SOME n -> n | _77 -> 0)`;;
hol4_overload "make_init" "lab_to_targetProof_make_init";;

(* HOL4 lab_to_targetProofScript.sml:9586: the ML values that the
   definitions below antiquote *)

let compiler_oracle_ok_def = cake_define
  `compiler_oracle_ok coracle init_labs init_pos c ffis <=>
     (!(k:num). let (cfg,code) = coracle k in
       lab_to_targetProof_good_code c (lab_to_target_config_labels cfg)
       code /\
       no_share_mem_inst code) /\
     (let (cfg,code) = coracle 0 in lab_to_target_config_labels
         cfg = init_labs /\ lab_to_target_config_pos
         cfg = init_pos /\ ffi_names
         cfg = SOME ffis)`;;

(* mc_conf_ok: conditions on the machine configuration
   which will be discharged for the particular configuration of each target
*)
let mc_conf_ok_def = cake_define
  `mc_conf_ok (mc_conf:('a,'b,'c)machine_config) <=>
     good_dimindex (:'a) /\
     encoder_correct (machine_config_target mc_conf) /\
     reg_ok (ptr_reg mc_conf) (target_config (machine_config_target
       mc_conf)) /\
     reg_ok (len_reg mc_conf) (target_config (machine_config_target
       mc_conf)) /\
     reg_ok (ptr2_reg mc_conf) (target_config (machine_config_target
       mc_conf)) /\
     reg_ok (len2_reg mc_conf) (target_config (machine_config_target
       mc_conf)) /\
     reg_ok (match link_reg (target_config (machine_config_target
       mc_conf)) with NONE -> 0 | SOME n -> n) (target_config
       (machine_config_target
       mc_conf)) /\
     enc_ok (target_config (machine_config_target mc_conf))`;;

let line_to_info_def = cake_define
  `line_to_info (secs:('a sec) list) p x = (match SND x with
     SOME (labLang_Asm (ShareMem m r ad) bytes l) ->
       (let (name,nb) = get_memop_info m in
       [(ffi_SharedMem name,
        mk_shmem_info_num (pos_val (FST x) p secs) nb (match ad
          with Addr r off -> r) (match ad with Addr r off -> w2n off)
          r (pos_val (FST x) p secs + LENGTH bytes))]) | _78 -> [])`;;

(* This is set up for the very first compile call *)

(* HOL4 lab_to_targetProofScript.sml:10204-10222: a proof *)

(* HOL4 lab_to_targetProofScript.sml:10224-10234: a proof *)

(* HOL4 lab_to_targetProofScript.sml:10236-10242: a proof *)

(* HOL4 lab_to_targetProofScript.sml:10244-10252: a proof *)

(* HOL4 lab_to_targetProofScript.sml:10254-10256: a proof *)

(* HOL4 lab_to_targetProofScript.sml:10258-10260: a proof *)

(* HOL4 lab_to_targetProofScript.sml:10262-10264: a proof *)

(* HOL4 lab_to_targetProofScript.sml:10266-10272: a proof *)

(* HOL4 lab_to_targetProofScript.sml:10274-10277: a proof *)

(* HOL4 lab_to_targetProofScript.sml:10279-10281: a proof *)

(* HOL4 lab_to_targetProofScript.sml:10283-10285: a proof *)

(* HOL4 lab_to_targetProofScript.sml:10287-10328: a proof *)

(* HOL4 lab_to_targetProofScript.sml:10330-10332: a proof *)

(* HOL4 lab_to_targetProofScript.sml:10334-10336: a proof *)

(* HOL4 lab_to_targetProofScript.sml:10338-10349: a proof *)

(* HOL4 lab_to_targetProofScript.sml:10351-10446: a proof *)
    (* TAKE case: asm_fetch_NOT_ffi_entry_pcs *)
(* HOL4 lab_to_targetProofScript.sml:10448-10450: a proof *)
    (* Get MEM in DROP via TAKE_DROP *)
(* HOL4 lab_to_targetProofScript.sml:10452-10459: a proof *)
    (* Get w2n version in DROP *)
(* HOL4 lab_to_targetProofScript.sml:10461-10464: a proof *)
    (* w2n x >= w2n(get_pc ms) from new_shmem_info structure *)
(* HOL4 lab_to_targetProofScript.sml:10466-10474: a proof *)
    (* a + pos_val < LENGTH prog *)
(* HOL4 lab_to_targetProofScript.sml:10476-10481: a proof *)
    (* Apply DISJOINT to get contradiction *)
(* HOL4 lab_to_targetProofScript.sml:10483-10489: a proof *)
    (* Prove w2n equality: w2n(n2w a + n2w(pos_val) + get_pc ms) = a + (w2n(pc) + pos_val) *)
(* HOL4 lab_to_targetProofScript.sml:10491-10493: a proof *)
    (* Show no overflow: a + pos_val + w2n(pc) < dimword *)
(* HOL4 lab_to_targetProofScript.sml:10495-10508: a proof *)

(* HOL4 lab_to_targetProofScript.sml:10510-10512: a proof *)

(* HOL4 lab_to_targetProofScript.sml:10514: a proof *)

(* TODO: move *)
(* HOL4 lab_to_targetProofScript.sml:10827-10848: code that the
   source has in a comment *)
(* HOL4 lab_to_targetProofScript.sml:10866-10941: code that the
   source has in a comment *)

(* HOL4 lab_to_targetProofScript.sml:10953-11010: code that the
   source has in a comment *)

(* try to show the condition of semantics_compile is not vacuous *)
(* HOL4 lab_to_targetProofScript.sml:11174-11199: code that the
   source has in a comment *)
(* HOL4 lab_to_targetProofScript.sml:11200-11245: code that the
   source has in a comment *)
