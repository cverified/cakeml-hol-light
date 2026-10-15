(* ======================================================== *)
(*  lab_to_targetProof: ported from HOL4's
    compiler/backend/proofs/lab_to_targetProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for lab_to_target
*)

needs "compiler/backend/export.ml";;
needs "compiler/backend/labLang.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
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
needs "compiler/backend/wordLang.ml";;
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

(* HOL4 ML code, not ported:
fun say0 pfx s g = (print (pfx ^ ": " ^ s ^ "\n"); ALL_TAC g)
*)

let sec_loc_to_pc_def = cake_define
  `(sec_loc_to_pc n2 xs =
    (if n2 = 0 then SOME 0 else match xs with [] -> NONE | (z :: zs)
      ->
      (if (?n1 k. z = Label n1 n2 k) then SOME 0 else if is_Label
        z then sec_loc_to_pc n2 zs else OPTION_MAP SUC (sec_loc_to_pc
        n2 zs))))`;;

(* HOL4 ML code, not ported:
val sec_loc_to_pc_ind = theorem"sec_loc_to_pc_ind"
*)

(* HOL4 overload (expanded in the port):
     len_no_lab = λxs. LENGTH (FILTER ($~ o is_Label) xs) *)

(* -- *)

(* -- evaluate-level semantics preservation of compiler -- *)

(* relate asm step to evaluate step *)

let enc_with_nop_def = cake_define
  `enc_with_nop enc (b:'a asm) bytes =
     (let init = enc b in
     let step = enc (asm_Inst Skip) in
       if LENGTH step = 0 then bytes = init else
         let n = (LENGTH bytes - LENGTH init) DIV LENGTH step in
           bytes = init ++ FLAT (REPLICATE n step))`;;

let asm_step_nop_def = cake_define
  `asm_step_nop bytes c s1 i s2 <=>
     bytes_in_memory (?_pc s1) bytes (?_mem s1) (?_mem_domain s1) /\
     enc_with_nop (asm_config_encode c) i bytes /\
     (match ?_link_reg c with NONE -> T | SOME r -> asm_state_lr s1 =
       r) /\
     (?_be s1 <=> asm_config_big_endian c) /\ asm_state_align s1 =
       asm_config_code_alignment c /\
     asm i (?_pc s1 + n2w (LENGTH bytes)) s1 = s2 /\ ~?_failed s2 /\
     asm_ok i c`;;

(* HOL4 ML code, not ported:
val evaluate_nop_step =
  asm_step_IMP_evaluate_step_find_next
    |> SIMP_RULE std_ss [asm_step_def]
    |> SPEC_ALL |> Q.INST [`i`|->`Inst Skip`]
    |> SIMP_RULE (srw_ss()) [asm_def,inst_def,asm_ok_def,inst_ok_def,
         Once upd_pc_def,GSYM CONJ_ASSOC]
*)

(* define relation between labSem and targetSem states *)

let lab_lookup_def = cake_define
  `lab_lookup k1 k2 labs =
     (match lookup k1 labs with NONE -> NONE | SOME f -> lookup k2
       f)`;;

let labs_domain_def = cake_define
  `labs_domain labs = {(n1,n2) | ~(lab_lookup n1 n2 labs = NONE)}`;;


let has_odd_inst_def = cake_define
  `(has_odd_inst [] = F) /\
   (has_odd_inst ((Section k []) :: xs) = has_odd_inst xs) /\
   (has_odd_inst ((Section k (y :: ys)) :: xs) <=>
      ~EVEN (line_length y) \/ has_odd_inst ((Section k ys) ::
        xs))`;;

let line_similar_def = cake_define
  `line_similar x1 x2 =
        match (x1,x2) with
          ((Label k1 k2 l),(Label k1' k2' l')) -> (k1 = k1') /\ (k2 =
            k2')
        | ((Asm b bytes l),(Asm b' bytes' l')) -> (b = b')
        | ((LabAsm a w bytes l),(LabAsm a' w' bytes' l')) -> (a = a')
        | (_1,_2) -> F`;;

(* HOL4 ML code, not ported:
val line_similar_ind = theorem"line_similar_ind";
*)

let code_similar_def = cake_define
  `code_similar x1 x2 =
        match (x1,x2) with
          ([],[]) -> T
        | (((Section s1 lines1) :: rest1),((Section s2 lines2) ::
          rest2)) ->
        code_similar rest1 rest2 /\
        EVERY2 line_similar lines1 lines2 /\ (s1 = s2)
        | (_3,_4) -> F`;;

(* HOL4 ML code, not ported:
val code_similar_ind = theorem "code_similar_ind";
*)

let word_loc_val_def = cake_define
  `(word_loc_val p labs (Word w) = SOME w) /\
   (word_loc_val p labs (Loc k1 k2) =
      (match lab_lookup k1 k2 labs with NONE -> NONE | SOME q ->
        SOME (p + n2w q)))`;;

let has_io_name_def = cake_define
  `(has_io_name index [] = F) /\
   (has_io_name index ((Section k []) :: xs) = has_io_name index xs)
     /\
   (has_io_name index ((Section k (y :: ys)) :: xs) <=>
      has_io_name index ((Section k ys) :: xs) \/
      (match y with LabAsm (CallFFI i) _5 _6 _7 -> (i = index) |
        _8 -> F))`;;

(* HOL4 ML code, not ported:
val has_io_name_ind = theorem"has_io_name_ind"
*)

let word_loc_val_byte_def = cake_define
  `word_loc_val_byte p labs m a be =
     (match word_loc_val p labs (m (byte_align a)) with SOME w ->
       SOME (get_byte a w be) | NONE -> NONE)`;;

let line_ok_def = cake_define
  `line_ok c labs ffis pos x5 =
        match (c,x5) with
          ((c:'a asm_config),(Label _9 _10 l)) ->
        EVEN pos /\ (l = 0)
        | (c,(Asm b bytes l)) ->
        enc_with_nop (asm_config_encode c) (cbw_to_asm b) bytes /\
        (LENGTH bytes = l) /\ asm_ok (cbw_to_asm b) c
        | (c,(LabAsm Halt w bytes l)) ->
        let w1 = ((n2w 0):'a word) - n2w (pos + ffi_offset) in
          enc_with_nop (asm_config_encode c) (Jump w1) bytes /\
          (LENGTH bytes = l) /\ asm_ok (Jump w1) c
        | (c,(LabAsm Install w bytes l)) ->
        let w1 = ((n2w 0):'a word) - n2w (pos + 2 * ffi_offset) in
          enc_with_nop (asm_config_encode c) (Jump w1) bytes /\
          (LENGTH bytes = l) /\ asm_ok (Jump w1) c
        | (c,(LabAsm (CallFFI index) w bytes l)) ->
        let w1 = ((n2w 0):'a word) - n2w (pos + (3 + get_ffi_index
          ffis (ExtCall index)) * ffi_offset) in
          enc_with_nop (asm_config_encode c) (Jump w1) bytes /\
          (LENGTH bytes = l) /\ asm_ok (Jump w1) c
        | (c,(LabAsm (Call v24) w bytes l)) ->
        F
        | (c,(LabAsm a w bytes l)) ->
        match get_label a with Lab l1 l2 ->
        (match lab_lookup l1 l2 labs with
          NONE -> F | SOME t ->
        (let w1 = n2w t - n2w pos in
          enc_with_nop (asm_config_encode c) (lab_inst w1 a) bytes /\
          (LENGTH bytes = l) /\ asm_ok (lab_inst w1 a) c))`;;

(* HOL4 ML code, not ported:
val line_ok_ind = theorem"line_ok_ind";
*)

let lines_ok_def = cake_define
  `(lines_ok c labs ffis pos [] = T) /\
   (lines_ok c labs ffis pos (y :: ys) <=>
    line_ok c labs ffis pos y /\
    lines_ok c labs ffis (pos + line_length y) ys)`;;

let all_enc_ok_def = cake_define
  `(all_enc_ok c labs ffis pos [] = T) /\
   (all_enc_ok c labs ffis pos ((Section k []) :: xs) <=>
      EVEN pos /\ all_enc_ok c labs ffis pos xs) /\
   (all_enc_ok c labs ffis pos ((Section k (y :: ys)) :: xs) <=>
      line_ok c labs ffis pos y /\
      all_enc_ok c labs ffis (pos + line_length y) ((Section k ys)
        :: xs))`;;

(* HOL4 ML code, not ported:
val all_enc_ok_ind = theorem"all_enc_ok_ind";
*)

let pos_val_def = cake_define
  `(pos_val i pos [] = (pos:num)) /\
   (pos_val i pos ((Section k []) :: xs) = pos_val i pos xs) /\
   (pos_val i pos ((Section k (y :: ys)) :: xs) =
      (if is_Label y then pos_val i (pos + line_length y)
        ((Section k ys) :: xs) else if i = (0:num) then pos else
        pos_val (i - 1) (pos + line_length y) ((Section k ys) ::
        xs)))`;;

(* HOL4 ML code, not ported:
val pos_val_ind = theorem"pos_val_ind";
*)

let sec_pos_val_def = cake_define
  `(sec_pos_val i pos [] = NONE) /\
   (sec_pos_val i pos (y :: ys) =
    (if is_Label y then
      sec_pos_val i (pos + line_length y) ys else if i = 0 then
        SOME pos else sec_pos_val (i - 1) (pos + line_length y) ys))`;;

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

let num_pcs_def = cake_define
  `num_pcs [] = (0:num) /\
   num_pcs ((Section _11 []) :: rest) = num_pcs rest /\
   num_pcs ((Section k (x :: xs)) :: rest) = (if is_Label x then
     num_pcs ((Section k xs) :: rest) else 1 + num_pcs ((Section k
     xs) :: rest))`;;

let share_mem_domain_code_rel_def = cake_define
  `share_mem_domain_code_rel mc_conf p code2 (s1_shared_mem_domain:'a
  word->bool) <=>
     (!pc op re a inst' len i.
         (asm_fetch_aux pc code2 = SOME (Asm (ShareMem op re a) inst'
           len) /\
         mmio_pcs_min_index (?_ffi_names mc_conf) = SOME i) ==>
         (?index.
           i <= index /\
           find_index (p + n2w (pos_val pc 0 code2))
             (machine_config_ffi_entry_pcs mc_conf) 0 =
             SOME index /\
           (let (name,nb) = get_memop_info op in
             EL index (?_ffi_names mc_conf) = SharedMem name /\
             (
              ALOOKUP (machine_config_mmio_info mc_conf) index = SOME
                (nb,a,re,p + n2w (pos_val pc 0 code2 + len)))))) /\
     (!pc line.
       asm_fetch_aux pc code2 = SOME line /\
       (!op re a inst' len. ~(line = Asm (ShareMem op re a) inst'
         len)) ==>
       DISJOINT (set_of_list (machine_config_ffi_entry_pcs mc_conf))
         {p + n2w a + n2w (pos_val pc 0 code2) |
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
       mmio_pcs_min_index (?_ffi_names mc_conf) = SOME i /\
       i <= index /\ index < LENGTH (?_ffi_names mc_conf) /\ RTC
       call_FFI_rel (?_ffi s1) st /\
       ALOOKUP (machine_config_mmio_info mc_conf) index = SOME
         (nb,Addr ad offs,re,pc') /\
       (machine_config_prog_addresses mc_conf = ?_mem_domain t1) /\
       ad' = target_get_reg (machine_config_target mc_conf) ms2 ad +
         offs /\
       target_state_rel (machine_config_target mc_conf)
         (?_pc_fupd (K (EL index (machine_config_ffi_entry_pcs
           mc_conf))) t1) ms2 ==>
       (?op. EL index (?_ffi_names mc_conf) = SharedMem op /\
          (match op with MappedRead ->
          ((if nb = (n2w 0) then (w2n ad' MOD (dimindex (:'a) DIV 8))
            = 0 else T) /\
          (ad' IN machine_config_shared_addresses mc_conf) /\
          is_valid_mapped_read (target_get_pc (machine_config_target
            mc_conf) ms2) nb (Addr ad offs) re pc'
            (machine_config_target
            mc_conf) ms2 (machine_config_prog_addresses mc_conf) /\
          call_FFI st (SharedMem MappedRead)
            [nb]
            (word_to_bytes ad' F) =
            FFI_return new_st new_bytes ==>
           target_state_rel (machine_config_target mc_conf)
             (?_regs_fupd (K (\n. if n = re then
                    (word_of_bytes F (n2w 0) new_bytes) else ?_regs
                      t1 n)) (?_pc_fupd (K pc') t1))
               (machine_config_ffi_interfer mc_conf k
                 (index,new_bytes,ms2))) | MappedWrite ->
          ((if nb = (n2w 0) then (w2n ad' MOD (dimindex (:'a) DIV 8))
            = 0 else T) /\
           (ad' IN machine_config_shared_addresses mc_conf) /\
           is_valid_mapped_write (target_get_pc
             (machine_config_target mc_conf) ms2) nb (Addr ad offs) re
             pc' (machine_config_target
             mc_conf) ms2 (machine_config_prog_addresses mc_conf) /\
          call_FFI st (SharedMem MappedWrite)
           [nb]
           (
            (let w = target_get_reg (machine_config_target mc_conf)
              ms2 re in
               if nb = (n2w 0) then word_to_bytes w F else
                 word_to_bytes_aux (w2n nb) w F) ++ (word_to_bytes ad'
                 F)) =
           FFI_return new_st new_bytes ==>
           target_state_rel (machine_config_target mc_conf)
             (?_pc_fupd (K pc') t1)
             (machine_config_ffi_interfer mc_conf k
               (index,new_bytes,ms2)))))) /\
    (!index i. mmio_pcs_min_index (?_ffi_names mc_conf) = SOME i /\
       index < LENGTH (?_ffi_names mc_conf) /\ i <= index ==>
         ~(machine_config_halt_pc
       mc_conf = (EL index (machine_config_ffi_entry_pcs mc_conf)))
         /\ ~(machine_config_ccache_pc
       mc_conf = (EL index (machine_config_ffi_entry_pcs
         mc_conf))))`;;

let no_install_or_no_share_mem_def = cake_define
  `no_install_or_no_share_mem code ffi_names <=>
    (no_share_mem_inst code /\
     EVERY (\x. ?s. x = ExtCall s) ffi_names) \/
     no_install code`;;

(* The lab-level oracles record the register residues that the machine
   run
   starting from ms actually leaves behind: the k-th entry of each
     family is
   read off the k-th interference application of that family.
   This is positional, so it is kept out of state_rel (which is closed
     under
   shift_interfer) and threaded through compile_correct separately. *)
let oracle_tie_def = cake_define
  `oracle_tie (mc_conf:('a,'state,'b)machine_config) ms
              (s1:('a,'c,'ffi)labSem_state) <=> labSem_state_io_regs
     s1 = target_io_regs mc_conf (?_ffi s1) ms /\
       labSem_state_io_fp_regs
     s1 = target_io_fp_regs mc_conf (?_ffi s1) ms /\
       labSem_state_cc_regs
     s1 = target_cc_regs mc_conf (?_ffi s1) ms /\
       labSem_state_cc_fp_regs
     s1 = target_cc_fp_regs mc_conf (?_ffi s1) ms`;;

(* The code buffer is set-up to immediately follow the current code:
  |---code---|---cb---|
*)
let state_rel_def = cake_define
  `lab_to_targetProof_state_rel (mc_conf,code2,labs,p)
  (s1:('a,lab_to_target_config,'ffi)labSem_state) t1 ms1 <=>
     target_state_rel (machine_config_target mc_conf) t1 ms1 /\
       good_dimindex (:'a) /\
     (machine_config_prog_addresses mc_conf = ?_mem_domain t1) /\
     ~(machine_config_halt_pc mc_conf IN
       machine_config_prog_addresses mc_conf) /\
     ~(machine_config_ccache_pc mc_conf IN
       machine_config_prog_addresses mc_conf) /\
     reg_ok (?_ptr_reg s1) (target_config (machine_config_target
       mc_conf)) /\ (?_ptr_reg mc_conf = ?_ptr_reg s1) /\
     reg_ok (?_len_reg s1) (target_config (machine_config_target
       mc_conf)) /\ (?_len_reg mc_conf = ?_len_reg s1) /\
     reg_ok (?_ptr2_reg s1) (target_config (machine_config_target
       mc_conf)) /\ (?_ptr2_reg mc_conf = ?_ptr2_reg s1) /\
     reg_ok (?_len2_reg s1) (target_config (machine_config_target
       mc_conf)) /\ (?_len2_reg mc_conf = ?_len2_reg s1) /\
     reg_ok (?_link_reg s1) (target_config (machine_config_target
       mc_conf)) /\
     (?i. mmio_pcs_min_index (?_ffi_names mc_conf) = SOME i /\
          (!index. if i <= index /\ index < LENGTH (?_ffi_names
            mc_conf) then ?info. ALOOKUP (machine_config_mmio_info
            mc_conf) index = SOME info else ALOOKUP
            (machine_config_mmio_info mc_conf) index = NONE)) /\
     (!ms2 k index new_bytes t1 bytes bytes2 st new_st i.
        mmio_pcs_min_index (?_ffi_names mc_conf) = SOME i /\
        index < i /\
        read_ffi_bytearrays mc_conf ms2 = (SOME bytes,SOME bytes2) /\
          RTC
        call_FFI_rel (?_ffi s1) st /\
        call_FFI st (EL index (?_ffi_names mc_conf)) bytes bytes2 =
          FFI_return new_st new_bytes /\
        (machine_config_prog_addresses mc_conf = ?_mem_domain t1) /\
        target_state_rel (machine_config_target mc_conf)
          (?_pc_fupd (K (p - n2w ((3 + index) * ffi_offset))) t1) ms2
            /\
        alignment_aligned (asm_config_code_alignment (target_config
          (machine_config_target mc_conf))) (?_regs t1 (?_link_reg s1))
          ==>
        (let ms' = machine_config_ffi_interfer mc_conf k
          (index,new_bytes,ms2) in
           target_state_rel (machine_config_target mc_conf)
             (?_pc_fupd (K (?_regs t1 (?_link_reg s1))) (?_mem_fupd
               (K (asm_write_bytearray (?_regs t1 (?_ptr2_reg s1))
               new_bytes (?_mem t1))) (?_fp_regs_fupd (K (\n.
               target_get_fp_reg (machine_config_target mc_conf) ms' n))
               (?_regs_fupd (K (\a. if MEM a
               (machine_config_callee_saved_regs mc_conf) \/
                              ~(a < asm_config_reg_count
                                (target_config (machine_config_target
                                mc_conf))) \/
                              MEM a (asm_config_avoid_regs
                                (target_config (machine_config_target
                                mc_conf))) then ?_regs t1 a else
                                target_get_reg (machine_config_target
                                mc_conf) ms' a)) t1))))
             ms')) /\
     (!ms2 t1 k a1 a2.
       target_state_rel (machine_config_target mc_conf)
         (?_pc_fupd (K (p - n2w ((2 * ffi_offset)))) t1) ms2 /\
       alignment_aligned (asm_config_code_alignment (target_config
         (machine_config_target mc_conf))) (?_regs t1 (?_link_reg s1))
         ==>
       (let ms' = machine_config_ccache_interfer mc_conf k
         (a1,a2,ms2) in
          target_state_rel (machine_config_target mc_conf)
            (?_pc_fupd (K (?_regs t1 (?_link_reg s1)))
              (?_fp_regs_fupd (K (\n. target_get_fp_reg
              (machine_config_target mc_conf) ms' n)) (?_regs_fupd (K
              (\a. if MEM a (machine_config_callee_saved_regs mc_conf)
              \/
                              a = ?_ptr_reg s1 \/
                              ~(a < asm_config_reg_count
                                (target_config (machine_config_target
                                mc_conf))) \/
                              MEM a (asm_config_avoid_regs
                                (target_config (machine_config_target
                                mc_conf))) then ?_regs t1 a else
                                target_get_reg (machine_config_target
                                mc_conf) ms' a)) t1)))
            ms')) /\ ?_compile
     s1 = compile_lab (target_config (machine_config_target mc_conf))
       /\
     (no_share_mem_inst code2 ==> (!k. let (cfg,code) =
       ?_compile_oracle s1 k in
             good_code (target_config (machine_config_target
               mc_conf)) (lab_to_target_config_labels cfg) code /\
             no_share_mem_inst code /\
             (k = 0 ==> lab_to_target_config_labels
             cfg = labs /\ lab_to_target_config_pos
             cfg = LENGTH (prog_to_bytes code2) /\ ?_ffi_names
             cfg = SOME (?_ffi_names mc_conf)))) /\
     (!l1 l2 x.
        (lab_lookup l1 l2 labs = SOME x) ==> EVEN x) /\
     (((n2w 1) && p) = (n2w 0)) /\
     (list_subset
       (FILTER (\x. ?s. x = ExtCall s) (find_ffi_names (?_code s1)))
         (?_ffi_names
       mc_conf)) /\
     EVEN (LENGTH (prog_to_bytes code2)) /\
     (!name i.
         MEM name (?_ffi_names mc_conf) /\
         mmio_pcs_min_index (?_ffi_names mc_conf) = SOME i /\
         get_ffi_index (?_ffi_names mc_conf) name < i ==>
         (?s. name = ExtCall s) /\
        ~(p - n2w ((3 + get_ffi_index (?_ffi_names mc_conf) name) *
          ffi_offset) IN machine_config_prog_addresses mc_conf) /\
        ~(p - n2w ((3 + get_ffi_index (?_ffi_names mc_conf) name) *
          ffi_offset) = machine_config_halt_pc mc_conf) /\
        ~(p - n2w ((3 + get_ffi_index (?_ffi_names mc_conf) name) *
          ffi_offset) = machine_config_ccache_pc mc_conf) /\
        (find_index (p - n2w ((3 + get_ffi_index (?_ffi_names
          mc_conf) name) * ffi_offset)) (machine_config_ffi_entry_pcs
                    mc_conf) 0 = SOME (get_ffi_index (?_ffi_names
                      mc_conf) name))) /\
     (p - n2w ffi_offset = machine_config_halt_pc mc_conf) /\
     (p - n2w (2 * ffi_offset) = machine_config_ccache_pc mc_conf) /\
     interference_ok (machine_config_next_interfer mc_conf)
       (target_proj (machine_config_target mc_conf) (?_mem_domain t1))
       /\
     (!l1 l2 x2.
        (loc_to_pc l1 l2 (?_code s1) = SOME x2) ==>
        (lab_lookup l1 l2 labs = SOME (pos_val x2 0 code2))) /\
     (!r. ?_fp_regs s1 r = ?_fp_regs t1 r) /\
     (!r. word_loc_val p labs (?_regs s1 r) = SOME (?_regs t1 r)) /\
     (!a. byte_align a IN ?_mem_domain s1 ==>
          a IN ?_mem_domain t1 /\ a IN ?_mem_domain s1 /\
          (word_loc_val_byte p labs (?_mem s1) a (?_be s1) = SOME
            (?_mem t1 a))) /\
     (!n.
       n < buffer_space_left (?_code_buffer s1) ==>
       (let addr' = buffer_position (?_code_buffer s1) + n2w (LENGTH
         (buffer_buffer (?_code_buffer s1)) + n) in
       addr' IN ?_mem_domain t1 /\ ~(
       addr' IN ?_mem_domain s1))) /\
     bytes_in_mem p (prog_to_bytes code2) (?_mem
       t1) (?_mem_domain t1) (?_mem_domain s1) /\ buffer_position
         (?_code_buffer
     s1) = p + n2w (LENGTH (prog_to_bytes code2)) /\
     bytes_in_mem (buffer_position (?_code_buffer s1)) (buffer_buffer
       (?_code_buffer s1)) (?_mem
       t1) (?_mem_domain t1) (?_mem_domain s1) /\
     LENGTH (prog_to_bytes code2) + LENGTH (buffer_buffer
       (?_code_buffer s1)) + buffer_space_left (?_code_buffer s1) <
       dimword (:'a) /\
     (!bn.
       bn < LENGTH (buffer_buffer (?_code_buffer s1)) +
         buffer_space_left (?_code_buffer s1) ==>
       ~MEM (buffer_position (?_code_buffer s1) + n2w bn)
         (machine_config_ffi_entry_pcs mc_conf)) /\
     ~?_failed s1 /\ ~?_failed t1 /\ (?_be s1 = ?_be t1) /\
     (?_pc t1 = p + n2w (pos_val (?_pc s1) 0 code2)) /\
     ((p && n2w (2 EXP asm_state_align t1 - 1)) = (n2w 0)) /\
     (match ?_link_reg (target_config (machine_config_target
       mc_conf)) with NONE -> T | SOME r -> asm_state_lr t1 = r) /\
     (?_be t1 <=> asm_config_big_endian (target_config
       (machine_config_target mc_conf))) /\
     (asm_state_align t1 = asm_config_code_alignment (target_config
       (machine_config_target mc_conf))) /\
     (enc_ok (target_config (machine_config_target mc_conf))) /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs
       (TAKE (THE (mmio_pcs_min_index (?_ffi_names mc_conf)))
         (?_ffi_names mc_conf)) 0 code2 /\
     EVERY sec_labels_ok code2 /\
     code_similar (?_code s1) code2 /\
     share_mem_state_rel mc_conf s1 t1 ms1 /\
     share_mem_domain_code_rel mc_conf p code2
       (labSem_state_shared_mem_domain s1) /\
     LENGTH (?_ffi_names mc_conf) = LENGTH
       (machine_config_ffi_entry_pcs mc_conf) /\
     no_install_or_no_share_mem code2 (?_ffi_names mc_conf)`;;
hol4_overload "state_rel" "lab_to_targetProof_state_rel";;

(* bytes_in_memory lemmas *)

(* HOL4 ML code, not ported:
val prog_to_bytes_lemma = prog_to_bytes_lemma
  |> Q.SPECL [`code2`,`code1`,`pc`,`i`,`0`]
  |> SIMP_RULE std_ss [];
*)

(* HOL4 ML code, not ported:
val s1 = ``s1:('a,lab_to_target$config,'ffi) labSem$state``;
*)

(* HOL4 ML code, not ported:
val case_eq_thms0 = map TypeBase.case_eq_of [``:lab``, ``:'a option``]
val bool_case_eq_thms = map (fn th =>
  let val v = th |> concl |> lhs |> rhs
  in th |> GEN v |> Q.ISPEC`T` |> SIMP_RULE bool_ss [] end)
    case_eq_thms0
*)

(* read/write bytearrays for FFI *)

(* inst correct *)

(* The lab and asm versions should be in their individual props *)

(* HOL4 ML code, not ported:
val share_mem_state_rel_tac =
  rw[] >>
  gvs[IMP_CONJ_THM, AND_IMP_INTRO]
  >- (first_x_assum $ ho_match_mp_tac o cj 1 >> fs[] >> metis_tac[])
  >- (first_x_assum $ ho_match_mp_tac o cj 2 >> fs[] >> metis_tac[])
  >- (first_x_assum $ ho_match_mp_tac o cj 1 >> fs[] >> metis_tac[])
  >- (first_x_assum $ ho_match_mp_tac o cj 2 >> fs[] >> metis_tac[])
*)

(* compile correct *)

(* HOL4 ML code, not ported:
val pos_val_MOD_0 = Q.prove(
  `!x pos code2.
      encoder_correct mc_conf.target /\
      (has_odd_inst code2 ==> (mc_conf.target.config.code_alignment =
        0)) /\
      (~EVEN pos ==> (mc_conf.target.config.code_alignment = 0)) /\
      (pos MOD 2 ** mc_conf.target.config.code_alignment = 0) /\
      all_enc_ok mc_conf.target.config labs ffi_names pos code2 ==>
      (pos_val x pos code2 MOD 2 ** mc_conf.target.config.code_alignment
        = 0)`,
  reverse (Cases_on `encoder_correct mc_conf.target`)
  \\ asm_simp_tac pure_ss [] THEN1 full_simp_tac(srw_ss())[]
  \\ HO_MATCH_MP_TAC pos_val_ind
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[pos_val_def] \\
    full_simp_tac(srw_ss())[all_enc_ok_def]
  THEN1 (srw_tac[][] \\
    full_simp_tac(srw_ss())[PULL_FORALL,AND_IMP_INTRO,has_odd_inst_def])
  \\ Cases_on `is_Label y` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `x = 0` \\ full_simp_tac(srw_ss())[]
  \\ FIRST_X_ASSUM MATCH_MP_TAC \\ full_simp_tac(srw_ss())[] \\
    srw_tac[][]
  \\ full_simp_tac(srw_ss())[has_odd_inst_def]
  \\ Cases_on `EVEN pos` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[EVEN_ADD]
  \\ `0:num < 2 ** mc_conf.target.config.code_alignment` by
    full_simp_tac(srw_ss())[]
  \\ once_rewrite_tac [GSYM MOD_PLUS]
  \\ imp_res_tac line_length_MOD_0 \\ full_simp_tac(srw_ss())[])
  |> Q.SPECL [`x`,`0`,`y`] |> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
  |> SIMP_RULE std_ss [pos_val_MOD_0_lemma]
  |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC];
*)

(* HOL4 ML code, not ported:
val IMP_IMP2 = METIS_PROVE [] ``a /\ (a /\ b ==> c) ==> ((a ==> b) ==>
  c)``
*)

(* HOL4 ML code, not ported:
val list_add_if_fresh_simp = Q.SPECL [`n`,`s`] list_add_if_fresh_simp
*)

(* -- syntactic properties of remove_labels -- *)

(* annotated line length *)

let line_len_def = cake_define
  `(line_len (Label _12 _13 l) = l) /\
   (line_len (Asm _14 _15 l) = l) /\
   (line_len (LabAsm _16 _17 _18 l) = l)`;;

(* annotated section length *)

(* simple syntactic properties of compiler functions *)

let enc_lines_again_simp_def = cake_define
  `(enc_lines_again_simp labs ffis pos enc [] = ([],T)) /\
   (enc_lines_again_simp labs ffis pos enc (LabAsm a w bytes l :: xs)
     =
     (let w1 = get_jump_offset a ffis labs pos in
       if w = w1 then
         let (rest,ok) = enc_lines_again_simp labs ffis (pos + l) enc
           xs in
           (LabAsm a w bytes l :: rest,ok) else
         let bs = enc (lab_inst w1 a) in
         let l1 = MAX (LENGTH bs) l in
         let (rest,ok) = enc_lines_again_simp labs ffis (pos + l1)
           enc xs in
           (LabAsm a w1 bs l1 :: rest,(l1 = l /\ ok)))) /\
   (enc_lines_again_simp labs ffis pos enc (Label k1 k2 l :: xs) =
     (let (rest,ok) = enc_lines_again_simp labs ffis (pos + l) enc xs
       in
     (Label k1 k2 l :: rest,ok))) /\
   (enc_lines_again_simp labs ffis pos enc (Asm x1 x2 l :: xs) =
     (let (rest,ok) = enc_lines_again_simp labs ffis (pos + l) enc xs
       in
     (Asm x1 x2 l :: rest,ok)))`;;

(* HOL4 ML code, not ported:
val enc_lines_again_simp_ind = theorem"enc_lines_again_simp_ind";
*)

(* code_similar preservation *)

(* HOL4 ML code, not ported:
val lines_upd_lab_len_AUX = Q.prove(
  `!l aux pos.
      REVERSE aux ++ FST (lines_upd_lab_len pos l []) =
      FST (lines_upd_lab_len pos l aux)`,
  Induct \\ fs [lines_upd_lab_len_def]
  \\ Cases \\ simp_tac std_ss [lines_upd_lab_len_def,LET_DEF]
  \\ pop_assum (fn th => once_rewrite_tac [GSYM th]) \\ fs []) |> GSYM
*)

(* implications of code_similar *)

(* sec_label_ok preservation *)

(* invariant: lines are encoded and non-label lengths annotated *)

let line_encd0_def = cake_define
  `line_encd0 enc x2 =
        match x2 with
          (Asm b bytes len) ->
       enc (cbw_to_asm b) = bytes /\ len = LENGTH bytes
        | (LabAsm l w bytes len) ->
        enc (lab_inst w l) = bytes /\ LENGTH bytes <= len /\
        (?w'. len = LENGTH (enc (lab_inst w' l)))
        | _19 -> T`;;

let sec_encd0_def = cake_define
  `sec_encd0 enc (Section _20 ls) = EVERY (line_encd0 enc) ls`;;

(* HOL4 overload (expanded in the port):
     all_encd0 = λenc l. EVERY (sec_encd0 enc) l *)

(* establishing encd0 *)

(* encd0 preservation *)

(* invariant: annotated lengths are not too small *)
(* this is a consequence of encd (below) and not treated separately much
   *)

let line_length_leq_def = cake_define
  `line_length_leq x1 =
        match x1 with
          (LabAsm _21 _22 bytes l) ->
       LENGTH bytes <= l
        | (Asm _23 bytes l) ->
       LENGTH bytes <= l
        | _24 -> T`;;

let sec_length_leq_def = cake_define
  `sec_length_leq (Section _25 ls) = EVERY line_length_leq ls`;;

(* HOL4 overload (expanded in the port):
     all_length_leq = λl. EVERY sec_length_leq l *)

(* invariant: label annotated lengths are 0 or 1 *)

let label_one_def = cake_define
  `label_one x1 =
        match x1 with
          (Label _26 _27 n) -> n <= 1
        | _28 -> T`;;

let sec_label_one_def = cake_define
  `sec_label_one (Section _29 ls) = EVERY label_one ls`;;

(* establishing label_one *)

(* label_one preservation *)

(* simple consequences of label_one *)

(* invariant: lines are encoded and annotated lengths are correct *)

let line_encd_def = cake_define
  `line_encd enc labs ffis pos x5 =
        match x5 with
          (Asm b bytes len) ->
       enc (cbw_to_asm b) = bytes /\ len = LENGTH bytes
        | (LabAsm Halt _30 bytes len) ->
       enc (Jump (--n2w (pos + ffi_offset))) = bytes /\
       LENGTH bytes <= len
        | (LabAsm Install _31 bytes len) ->
       enc (Jump (--n2w (pos + 2 * ffi_offset))) = bytes /\
       LENGTH bytes <= len
        | (LabAsm (CallFFI s) _32 bytes len) ->
       enc (Jump (--n2w (pos + (get_ffi_index ffis (ExtCall s) + 3) *
         ffi_offset))) = bytes /\
       LENGTH bytes <= len
        | (LabAsm (Jump l) _33 bytes len) ->
       enc (Jump (n2w (find_pos l labs) + --n2w pos)) = bytes /\
       LENGTH bytes <= len
        | (LabAsm (JumpCmp a b c l) _34 bytes len) ->
       enc (JumpCmp a b c (n2w (find_pos l labs) + --n2w pos)) =
         bytes /\
       LENGTH bytes <= len
        | (LabAsm (LocValue k l) _35 bytes len) ->
       enc (Loc k (n2w (find_pos l labs) + --n2w pos)) = bytes /\
       LENGTH bytes <= len
        | (LabAsm (Call l) _36 bytes len) ->
       enc (Call (n2w (find_pos l labs) + --n2w pos)) = bytes /\
       LENGTH bytes <= len
        | _37 -> T`;;

(* HOL4 ML code, not ported:
val line_encd_ind = theorem"line_encd_ind";
*)

let lines_encd_def = cake_define
  `(lines_encd enc labs ffis pos [] <=> T) /\
   (lines_encd enc labs ffis pos (l :: ls) <=>
    line_encd enc labs ffis pos l /\
    lines_encd enc labs ffis (pos + line_len l) ls)`;;

let all_encd_def = cake_define
  `(all_encd enc labs ffis pos [] <=> T) /\
   (all_encd enc labs ffis pos (Section k ls :: ss) <=>
    lines_encd enc labs ffis pos ls /\
    all_encd enc labs ffis (pos + SUM (MAP line_len ls)) ss)`;;

(* length_leq follows from encd *)

(* establishing encd *)

(* invariant: annotated lengths are correct *)

let line_length_ok_def = cake_define
  `line_length_ok l <=> LENGTH (line_bytes l) = line_len l`;;

let sec_length_ok_def = cake_define
  `sec_length_ok (Section _38 ls) = EVERY line_length_ok ls`;;

(* simple consequences of length_ok *)

(* invariant: all labels annotated with length 0 *)

let label_zero_def = cake_define
  `label_zero x1 =
        match x1 with
          (Label _39 _40 n) -> n = 0
        | _41 -> T`;;

let sec_label_zero_def = cake_define
  `sec_label_zero (Section _42 ls) = EVERY label_zero ls`;;

(* label_zero preservation *)

(* simple consequences of label_zero *)

(* invariant: lines aligned *)

let line_aligned_def = cake_define
  `line_aligned m l <=>
     line_len l MOD m = 0 /\
     line_length l MOD m = 0`;;

let sec_aligned_def = cake_define
  `sec_aligned noplen (Section _43 ls) = EVERY (line_aligned noplen)
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
          (Asm b bytes len) ->
       enc_with_nop enc (cbw_to_asm b) bytes /\ LENGTH bytes = len
        | (LabAsm Halt _44 bytes len) ->
       enc_with_nop enc (Jump (--n2w (pos + ffi_offset))) bytes /\
       LENGTH bytes = len
        | (LabAsm Install _45 bytes len) ->
       enc_with_nop enc (Jump (--n2w (pos + 2 * ffi_offset))) bytes
         /\
       LENGTH bytes = len
        | (LabAsm (CallFFI s) _46 bytes len) ->
       enc_with_nop enc (Jump (--n2w (pos + (get_ffi_index ffis
         (ExtCall s) + 3) * ffi_offset))) bytes /\
       LENGTH bytes = len
        | (LabAsm (Jump l) _47 bytes len) ->
       enc_with_nop enc (Jump (n2w (find_pos l labs) + --n2w pos))
         bytes /\
       LENGTH bytes = len
        | (LabAsm (JumpCmp a b c l) _48 bytes len) ->
       enc_with_nop enc (JumpCmp a b c (n2w (find_pos l labs) + --n2w
         pos)) bytes /\
       LENGTH bytes = len
        | (LabAsm (LocValue k l) _49 bytes len) ->
       enc_with_nop enc (Loc k (n2w (find_pos l labs) + --n2w pos))
         bytes /\
       LENGTH bytes = len
        | (LabAsm _50 _51 bytes len) -> LENGTH bytes = len
        | (Label _52 _53 len) -> len = 0`;;

(* HOL4 ML code, not ported:
val line_enc_with_nop_ind = theorem"line_enc_with_nop_ind";
*)

let lines_enc_with_nop_def = cake_define
  `(lines_enc_with_nop enc labs ffis pos [] <=> T) /\
   (lines_enc_with_nop enc labs ffis pos (l :: ls) <=>
    line_enc_with_nop enc labs ffis pos l /\
    lines_enc_with_nop enc labs ffis (pos + line_length l) ls)`;;

let all_enc_with_nop_def = cake_define
  `(all_enc_with_nop enc labs ffis pos [] <=> T) /\
   (all_enc_with_nop enc labs ffis pos (Section k [] :: xs) <=>
    all_enc_with_nop enc labs ffis pos xs) /\
   (all_enc_with_nop enc labs ffis pos (Section k (y :: ys) :: xs)
     <=>
    line_enc_with_nop enc labs ffis pos y /\
    all_enc_with_nop enc labs ffis (pos + line_length y) (Section
      k ys :: xs))`;;

(* HOL4 ML code, not ported:
val all_enc_with_nop_ind = theorem"all_enc_with_nop_ind";
*)

(* enc_with_nop implies length_ok *)

(* enc_with_nop implies label_zero *)

(* line_ok implies enc_with_nop *)

(* establishing enc_with_nop *)

(* invariant: label annotation correctly records alignment *)

let line_lab_len_pos_ok_def = cake_define
  `line_lab_len_pos_ok pos x2 =
        match x2 with
          (Label _54 _55 l) ->
        if EVEN pos then l = 0 else l = 1
        | _56 -> T`;;

let lab_len_pos_ok_def = cake_define
  `(lab_len_pos_ok pos [] <=> T) /\
   (lab_len_pos_ok pos (l :: ls) <=>
      line_lab_len_pos_ok pos l /\
      lab_len_pos_ok (pos + line_len l) ls)`;;

let all_lab_len_pos_ok_def = cake_define
  `(all_lab_len_pos_ok _57 [] <=> T) /\
   (all_lab_len_pos_ok pos (Section k ls :: ss) <=>
    lab_len_pos_ok pos ls /\
    all_lab_len_pos_ok (pos + sec_length ls 0) ss)`;;

(* HOL4 ML code, not ported:
val all_lab_len_pos_ok_ind = theorem"all_lab_len_pos_ok_ind";
*)

(* establishing pos_ok *)

(* pos_ok preservation *)

(* invariant: jump offsets ok *)

let line_offset_ok_def = cake_define
  `line_offset_ok labs ffis pos x4 =
        match x4 with
          (LabAsm a w bytes _58) ->
       w = get_jump_offset a ffis labs pos
        | _59 -> T`;;

let lines_offset_ok_def = cake_define
  `(lines_offset_ok labs ffis pos [] <=> T) /\
   (lines_offset_ok labs ffis pos (l :: ls) <=>
    line_offset_ok labs ffis pos l /\
    lines_offset_ok labs ffis (pos + line_len l) ls)`;;

let offset_ok_def = cake_define
  `lab_to_targetProof_offset_ok labs ffis pos x4 =
        match x4 with
          [] -> T
        | (Section k ls :: ss) ->
      lines_offset_ok labs ffis pos ls /\
      lab_to_targetProof_offset_ok labs ffis (pos + SUM (MAP
        line_len ls)) ss`;;
hol4_overload "offset_ok" "lab_to_targetProof_offset_ok";;

(* HOL4 ML code, not ported:
val offset_ok_ind = theorem"offset_ok_ind";
*)

(* establishing offset_ok *)

(* offset_ok preservation *)

(* invariant: referenced labels exist *)

let line_labs_exist_def = cake_define
  `line_labs_exist labs x2 =
        match x2 with
          (LabAsm a _60 _61 _62) ->
       !n1 n2. (n1,n2) IN labs_of a ==> ~(lab_lookup n1 n2 labs =
         NONE)
        | _63 -> T`;;

(* HOL4 ML code, not ported:
val line_labs_exist_ind = theorem "line_labs_exist_ind";
*)

let sec_labs_exist_def = cake_define
  `sec_labs_exist labs (Section _64 ls) <=> EVERY (line_labs_exist
  labs) ls`;;

(* HOL4 overload (expanded in the port):
     all_labs_exist = λlabs code. EVERY (sec_labs_exist labs) code *)

(* Remove tail recursion from zero_labs_acc_exist *)

(* labs_exist preservation *)

(* establishing labs_exist *)

(* invariant: labels aligned at even positions *)

let even_labels_def = cake_define
  `(even_labels pos [] <=> T) /\
   (even_labels pos (Section _65 [] :: ls) <=> even_labels pos ls) /\
   (even_labels pos (Section k (y :: ys) :: ls) <=>
    (is_Label y ==> EVEN pos) /\
    even_labels (pos + line_len y) (Section k ys :: ls))`;;

(* HOL4 ML code, not ported:
val even_labels_ind = theorem"even_labels_ind";
*)

let lines_even_labels_def = cake_define
  `(lines_even_labels pos [] <=> T) /\
   (lines_even_labels pos (y :: ys) <=>
    (is_Label y ==> EVEN pos) /\
    lines_even_labels (pos + line_len y) ys)`;;

let even_labels_strong_def = cake_define
  `(even_labels_strong pos [] <=> T) /\
   (even_labels_strong pos (Section _66 [] :: ls) <=>
     EVEN pos /\ even_labels_strong pos ls) /\
   (even_labels_strong pos (Section k (y :: ys) :: ls) <=>
    (is_Label y ==> EVEN pos) /\
    even_labels_strong (pos + line_len y) (Section k ys :: ls))`;;

(*
val tm = ``[Label 0 1 0; Label 0 2 1; Label 0 3 0; Label 0 4 1]``;
val tm = ``[Label 0 1 0; Label 0 2 1; Label 0 3 0; Label 0 4 1; Asm a
  [b] 1]``;
val tm = ``[Asm a [b] 1; Label 0 1 0; Label 0 2 1; Label 0 3 0; Label 0
  4 1]``;
val th = EVAL ``pad_section nop ^tm  []``
val tm2 = th |> concl |> rhs
EVAL ``SUM (MAP line_length ^tm)``
EVAL ``SUM (MAP line_length ^tm2)``
*)

(*
  val code = ``[Label a1 b1 0; Label a2 b2 0; Asm x3 [b3] 1; Label a4 b4
    1; Label a5 b5 0]``
  EVAL ``lab_len_pos_ok 0 ^code``
  EVAL ``(pad_section nop ^code [])``
  EVAL ``lab_len_pos_ok 0 (pad_section nop ^code [])``

  [Label a1 b1 0; Label a2 b2 0; Asm x3 [b3] 1; Label a4 b4 1; Label a5
    b5 0]
  []

  [Label a2 b2 0; Asm x3 [b3] 1; Label a4 b4 1; Label a5 b5 0]
  [Label a1 b1 0]

  [Asm x3 [b3] 1; Label a4 b4 1; Label a5 b5 0]
  [Label a2 b2 0; Label a1 b1 0]

  [Label a4 b4 1; Label a5 b5 0]
  [Asm x3 [b3] 1; Label a2 b2 0; Label a1 b1 0]

  [Label a5 b5 0]
  [Label a4 b4 0; Asm x3 [b3;nop] 2; Label a2 b2 0; Label a1 b1 0]
*)

(*
  val code = ``[Label 1 1 0; Label 1 2 0; Asm x3 [b3] 1; Label 1 3 1;
    Label 1 4 0]``
  EVAL ``section_labels 0 ^code LN``
  EVAL ``(pad_section nop ^code [])``
  EVAL ``section_labels 0 (pad_section nop ^code []) LN``

  [Label 1 1 0; Label 1 2 0; Asm x3 [b3] 1; Label 1 3 1; Label 1 4 0]
  []

  [Label 1 2 0; Asm x3 [b3] 1; Label 1 3 1; Label 1 4 0]
  [Label 1 1 0]

  [Asm x3 [b3] 1; Label 1 3 1; Label 1 4 0]
  [Label 1 2 0; Label 1 1 0]

  [Label 1 3 1; Label 1 4 0]
  [Asm x3 [b3] 1; Label 1 2 0; Label 1 1 0]

  [Label 1 4 0]
  [Label 1 3 0; Asm x3 [b3;nop] 2; Label 1 2 0; Label 1 1 0]
*)

(** End syntactic stuff **)

(* HOL4 ML code, not ported:
fun map_first_cj t =
  let
    fun gen_list n =
      case total (cj n) t of
        NONE => []
      | SOME t' => t'::gen_list (n+1)
  in
  MAP_FIRST ho_match_mp_tac $ gen_list 1
end
*)

(* HOL4 ML code, not ported:
val enc_is_valid_mapped_access_tac =
    fs[is_valid_mapped_read_def,is_valid_mapped_write_def]
    \\ fs[enc_with_nop_thm]
    \\ rfs[]
    \\ drule_then assume_tac $
        cj 1 $ cj 1 $ PURE_REWRITE_RULE [EQ_IMP_THM]
          bytes_in_memory_APPEND
    \\ drule_then assume_tac bytes_in_memory_in_domain
    \\ irule bytes_in_memory_change_mem
    \\ qexists `t1.mem`
    \\ simp[];
*)

(* HOL4 ML code, not ported:
fun share_mem_load_compile_correct_tac ffi_name new_t1 nb new_ffi =
  qpat_assum `!i. _ ==> mc_conf.target.get_reg ms1 i = t1.regs i` $
    qspec_then `n''` drule_all
  \\ strip_tac
  \\ fs[call_FFI_def]
  \\ last_x_assum irule
  \\ simp[]
  \\ conj_tac
  >- (rpt gen_tac
      \\ strip_tac
      \\ first_x_assum $ qspecl_then [`ms2`, `t1'`, `k`, `a1`, `a2`]
        mp_tac
      \\ simp[] )
  \\ conj_tac
  >- (rpt gen_tac
    \\ simp[apply_oracle_def,shift_interfer_def,shift_seq_def]
    \\ fs[IMP_CONJ_THM, AND_IMP_INTRO]
    \\ conj_tac
    \\ strip_tac
    \\ first_x_assum map_first_cj
    \\ fs[]
    \\ qexistsl [`st`, `new_st`]
    \\ simp[]
    \\ irule $ cj 2 RTC_RULES
    \\ qexists new_ffi
    \\ simp[evaluatePropsTheory.call_FFI_rel_def]
    \\ qexists ffi_name
    \\ simp[call_FFI_def, AllCaseEqs()]
    \\ metis_tac[] )
  >- (
    rpt gen_tac
    \\ simp[apply_oracle_def,shift_interfer_def,shift_seq_def]
    \\ conj_tac
    >- (
      rpt gen_tac
      \\ strip_tac
      \\ first_x_assum $ qspecl_then
        [`ms2`,`k+1`,`index'`,`new_bytes`,`t1'`,`bytes'`,`bytes2`,`st`
          ,`new_st`]
        assume_tac
      \\ first_x_assum ho_match_mp_tac
      \\ fs[]
      \\ irule $ cj 2 RTC_RULES
      \\ qexists new_ffi
      \\ simp[evaluatePropsTheory.call_FFI_rel_def]
      \\ qexists ffi_name
      \\ simp[call_FFI_def, AllCaseEqs()]
      \\ metis_tac[] )
    >- (
      simp[apply_oracle_def,shift_interfer_def,shift_seq_def]
      \\ first_x_assum $ qspecl_then
        [`ms1`, `0`,`index`,`v4`, `t1`, nb,`n''`,`c`,`n'`,
          `p + n2w (LENGTH bytes + pos_val s1.pc 0 code2)`,`s1.ffi`,
          new_ffi] mp_tac
      \\ simp[]
      \\ impl_tac
      >- (
        simp[target_state_rel_def]
        \\ old_drule find_index_LESS_LENGTH
        \\ simp[]
        \\ disch_then kall_tac
        \\ fs[find_index_INDEX_OF, INDEX_OF_eq_SOME] )
      \\ impl_tac
      >- (
        gvs[is_valid_mapped_write_def,is_valid_mapped_read_def
          ,good_dimindex_def]
        \\ gvs[enc_with_nop_thm]
        \\ old_drule $ cj 1 $ cj 1 $ PURE_REWRITE_RULE [EQ_IMP_THM]
          bytes_in_memory_APPEND
        \\ strip_tac
        \\ drule_all bytes_in_memory_eq_mem
        \\ simp[]
      )
      \\ rpt strip_tac
      \\ fs[target_state_rel_def]
      \\ first_x_assum $ irule_at (Pat `all_enc_ok`)
      \\ qexists new_t1
      \\ rw[]
      >- (first_x_assum irule >> metis_tac[])
      \\ simp[APPLY_UPDATE_THM]
      \\ IF_CASES_TAC
      \\ fs[word_loc_val_def]
    )
  );
*)

(* HOL4 ML code, not ported:
fun share_mem_store_compile_correct_tac ffi_name new_t1 (nb: term frag
  list) new_ffi =
  let
    val (wnb: term frag list) = `n2w (` @ nb @ `)`
  in
  qpat_assum `!i. _ ==> mc_conf.target.get_reg ms1 i = t1.regs i` $
    qspec_then `n''` drule_all
  \\ rpt strip_tac
  \\ `mc_conf.target.get_reg ms1 n' = t1.regs n'` by (
        qpat_x_assum `!i. _ ==> mc_conf.target.get_reg ms1 i = t1.regs
          i` $
          qspec_then `n'` irule
        \\ simp[] )
  \\ `(dimindex (:α) DIV 8) MOD 256 = dimindex (:α) DIV 8` by
    fs[good_dimindex_def]
  \\ gvs[call_FFI_def,LENGTH_APPEND,inc_pc_def,dec_clock_def]
  \\ last_x_assum irule
  \\ simp[]
  \\ conj_tac
  >- (rpt gen_tac
      \\ strip_tac
      \\ first_x_assum $ qspecl_then [`ms2`, `t1'`, `k`, `a1`, `a2`]
        mp_tac
      \\ simp[] )
  \\ conj_tac
  >- (rpt gen_tac
    \\ simp[apply_oracle_def,shift_interfer_def,shift_seq_def]
    \\ fs[IMP_CONJ_THM, AND_IMP_INTRO]
    \\ conj_tac
    \\ strip_tac
    \\ first_x_assum map_first_cj
    \\ fs[]
    \\ qexistsl [`st`, `new_st`]
    \\ simp[]
    \\ irule $ cj 2 RTC_RULES
    \\ qexists new_ffi
    \\ simp[evaluatePropsTheory.call_FFI_rel_def]
    \\ qexists ffi_name
    \\ simp[call_FFI_def, AllCaseEqs()]
    \\ qexistsl [
      `[` @ wnb @ `]`,
      `w2wlist_le (t1.regs n') (`  @ nb @ `) ++ addr2w8list (c + t1.regs
        n'')`,
      `v4`, `ffi'`]
    \\ gvs[LENGTH_APPEND] )
  >- (
    rpt gen_tac
    \\ simp[apply_oracle_def,shift_interfer_def,shift_seq_def]
    \\ conj_tac
    >- (
      rpt gen_tac
      \\ strip_tac
      \\ first_x_assum $ qspecl_then
        [`ms2`,`k+1`,`index'`,`new_bytes`,`t1'`,`bytes'`,`bytes2`,`st`
          ,`new_st`]
        assume_tac
      \\ first_x_assum ho_match_mp_tac
      \\ fs[]
      \\ irule $ cj 2 RTC_RULES
      \\ qexists new_ffi
      \\ simp[evaluatePropsTheory.call_FFI_rel_def]
      \\ qexists ffi_name
      \\ simp[call_FFI_def, AllCaseEqs()]
      \\ qexistsl [
        `[` @ wnb @ `]`,
        `w2wlist_le (t1.regs n') (`  @ nb @ `) ++ addr2w8list (c +
          t1.regs n'')`,
        `v4`, `ffi'`]
      \\ fs[LENGTH_APPEND] )
    >- (
      simp[apply_oracle_def,shift_interfer_def,shift_seq_def]
      \\ first_x_assum $ qspecl_then
        [`ms1`, `0`,`index`,`v4`, `t1`, wnb,`n''`,`c`,`n'`,
          `p + n2w (LENGTH bytes + pos_val s1.pc 0 code2)`,`s1.ffi`,
          new_ffi] mp_tac
      \\ simp[]
      \\ impl_tac
      >- (
        simp[target_state_rel_def]
        \\ old_drule find_index_LESS_LENGTH
        \\ simp[]
        \\ disch_then kall_tac
        \\ fs[find_index_INDEX_OF, INDEX_OF_eq_SOME] )
      \\ impl_tac
      >- (
        gvs[is_valid_mapped_write_def,is_valid_mapped_read_def
          ,good_dimindex_def]
        \\ gvs[enc_with_nop_thm]
        \\ old_drule $ cj 1 $ cj 1 $ PURE_REWRITE_RULE [EQ_IMP_THM]
          bytes_in_memory_APPEND
        \\ strip_tac
        \\ drule_all bytes_in_memory_eq_mem
        \\ simp[]
      )
      \\ rpt strip_tac
      \\ fs[target_state_rel_def]
      \\ first_x_assum $ irule_at (Pat `all_enc_ok`)
      \\ qexists new_t1
      \\ rw[]
      >- (first_x_assum irule >> metis_tac[])
      \\ simp[APPLY_UPDATE_THM]
      \\ IF_CASES_TAC
      \\ fs[word_loc_val_def]
    )
  )
end
*)

(* HOL4 ML code, not ported:
val share_mem_eval_expand_tac =
  fs[share_mem_op_def,share_mem_load_def,share_mem_store_def,AllCaseEqs
    (),call_FFI_def]
  \\ simp[Once targetSemTheory.evaluate_def]
  \\ fs[state_rel_def,share_mem_domain_code_rel_def,asm_fetch_def,
    ELIM_UNCURRY,get_memop_info_def]
  \\ drule_all $ GEN_ALL IMP_bytes_in_memory_ShareMem
  \\ strip_tac
  \\ qpat_assum `!pc op re a inst len i. asm_fetch_aux _ _ = SOME _ /\
      mmio_pcs_min_index _ = SOME _ ==> _` drule_all
  \\ strip_tac
  \\ old_drule find_index_is_MEM
  \\ fs[target_state_rel_def]
  \\ disch_then kall_tac
  \\ fs[share_mem_state_rel_def]
  \\ qpat_assum `!index' i'. mmio_pcs_min_index _ = SOME i' /\ index' <
    _ /\
      _ ==> _` $ qspec_then `index` old_drule
  \\ (
    impl_tac >- (old_drule find_index_LESS_LENGTH >> fs[])
    \\ disch_then assume_tac
    \\ `mc_conf.target.get_pc ms1 <> mc_conf.ccache_pc /\
        mc_conf.target.get_pc ms1 <> mc_conf.halt_pc` by (
          irule ffi_entry_pcs_NOT_ccache_OR_halt_pc >> gvs[])
    \\ rfs[get_memop_info_def]
    \\ TOP_CASE_TAC
    \\ fs[labSemTheory.addr_def,AllCaseEqs()]
    \\ rw[GSYM PULL_EXISTS]
    \\ `(dimindex (:'a) DIV 8) MOD 256 <> 1` by (
      rfs[good_dimindex_def] >> fs[])
    \\ fs[asm_ok_def,inst_ok_def,reg_ok_def]
  );
*)

(* move *)

(* HOL4 ML code, not ported:
val say = say0 "compile_correct";
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Asm]:
  fs[case_eq_thms]>>rw[]
  THEN1 (* Asm Inst *) (
     say "Asm Inst"
     \\ qmatch_assum_rename_tac `asm_fetch s1 = SOME (Asm (Asmi(Inst i))
       bytes len)`
     \\ qabbrev_tac `ffi_names = TAKE (THE (mmio_pcs_min_index
       mc_conf.ffi_names)) mc_conf.ffi_names`
     \\ mp_tac IMP_bytes_in_memory_Inst
     \\ full_simp_tac(srw_ss())[]
     \\ impl_tac
     THEN1 (full_simp_tac(srw_ss())[state_rel_def])
     \\ rpt strip_tac \\ pop_assum mp_tac \\ pop_assum mp_tac
     \\ qpat_abbrev_tac `jj = asm$Inst i` \\ rpt strip_tac
     \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]MP_TAC
          asm_step_IMP_evaluate_step_nop) \\ full_simp_tac(srw_ss())[]
     \\ disch_then (mp_tac o Q.SPEC `bytes'`)
     \\ impl_tac>-
      (imp_res_tac Inst_lemma \\ pop_assum (K all_tac)
       \\ full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF] \\
         unabbrev_all_tac \\ full_simp_tac(srw_ss())[]
       \\ full_simp_tac(srw_ss())[asm_step_nop_def,asm_def,LET_DEF]
       \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def,upd_reg_def]
       \\ conj_tac
       >- (fs[asm_fetch_def] >>
        `!op re a. Asmi (Inst i) <> ShareMem op re a` by simp[] >>
        drule_all $ GEN_ALL IMP_ffi_entry_pcs_disjoint_Asm >>
        simp[])
       \\ qpat_x_assum `bytes_in_mem ww bytes' t1.mem
             t1.mem_domain s1.mem_domain` mp_tac
       \\ match_mp_tac bytes_in_mem_IMP_memory \\
         full_simp_tac(srw_ss())[])
     \\ rpt strip_tac \\ full_simp_tac(srw_ss())[]
     \\ rfs[] \\ fs[]
     \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l mc_conf`,
          `code2`,`labs`,
          `(asm jj (t1.pc + n2w (LENGTH (bytes':word8 list)))
            t1)`,`ms2`])
     \\ impl_tac THEN1
      (conj_tac
       >- (irule oracle_tie_step
           \\ qpat_assum `oracle_tie _ _ _` (irule_at Any)
           \\ simp[labSemTheory.inc_pc_def,labSemTheory.dec_clock_def,
                   labSemTheory.upd_pc_def,asm_inst_consts]
           \\ metis_tac[])
       \\ unabbrev_all_tac \\ rpt strip_tac \\
         full_simp_tac(srw_ss())[asm_def]
       THEN1 (full_simp_tac(srw_ss())[shift_interfer_def])
       \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
       \\ match_mp_tac state_rel_shift_interfer
       \\ old_drule Inst_lemma \\ fs[])
     \\ rpt strip_tac \\
       full_simp_tac(srw_ss())[inc_pc_def,dec_clock_def
       ,labSemTheory.upd_reg_def]
     \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock - 1 + k` mp_tac)
     \\ rpt strip_tac
     \\ Q.EXISTS_TAC `k + l - 1` \\ full_simp_tac(srw_ss())[]
     \\ `^s1.clock - 1 + k + l = ^s1.clock + (k + l - 1)` by decide_tac
     \\ fs[asm_inst_consts])
  THEN1 (* Asm JumpReg *) (
    say "Asm JumpReg"
    \\ qmatch_assum_rename_tac `read_reg r1 s1 = Loc l1 l2`
    \\ Cases_on `loc_to_pc l1 l2 s1.code` \\ full_simp_tac(srw_ss())[]
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`, `s1.ffi`, `JumpReg
      r1`]MP_TAC
         asm_step_IMP_evaluate_step_find_next) \\
           full_simp_tac(srw_ss())[]
    \\ impl_tac >-
     (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF]
      \\ conj_tac
      >- (fs[asm_fetch_def]
        \\ drule_all $ GEN_ALL IMP_bytes_in_memory
        \\ strip_tac
        \\ fs[]
        \\ `!op re a. Asmi (JumpReg r1) <> ShareMem op re a` by simp[]
        \\ drule_all $ GEN_ALL IMP_ffi_entry_pcs_disjoint_Asm
        \\ `LENGTH ((mc_conf.target.config.encode (JumpReg r1))) <=
          LENGTH (line_bytes j)`
          suffices_by metis_tac[ffi_entry_pcs_disjoint_LENGTH_shorter]
        \\ Cases_on `j`
        \\ fs[line_similar_def,line_ok_def]
        \\ fs[enc_with_nop_thm,line_length_def]
        \\ Cases_on `a` >> fs[]
        \\ metis_tac[LENGTH_APPEND,LESS_EQ_ADD])
      \\ full_simp_tac(srw_ss())[asm_step_def,asm_def,LET_DEF]
      \\ imp_res_tac bytes_in_mem_IMP
      \\ full_simp_tac(srw_ss())[IMP_bytes_in_memory_JumpReg
        ,asmSemTheory.upd_pc_def,
             asmSemTheory.assert_def]
      \\ imp_res_tac IMP_bytes_in_memory_JumpReg \\
        full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[asmSemTheory.read_reg_def]
      \\ full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def]
      \\ FIRST_X_ASSUM (kall_tac o Q.SPEC `r1:num`)
      \\ qpat_x_assum `!n. n<s1.code_buffer.space_left ==> _` kall_tac
      \\ qpat_x_assum `!r. word_loc_val _ _ (read_reg r _) = _` (MP_TAC
        o Q.SPEC `r1:num`)
      \\ strip_tac \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[word_loc_val_def]
      \\ Cases_on `lab_lookup l1 l2 labs` \\ full_simp_tac(srw_ss())[]
      \\ Q.PAT_X_ASSUM `xx = t1.regs r1` (fn th =>
        full_simp_tac(srw_ss())[GSYM th])
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l1`,`l2`]) \\
        full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ (alignmentTheory.aligned_add_sub_cor
          |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> irule)
      \\ conj_tac >- fs[alignmentTheory.aligned_bitwise_and]
      \\ simp[aligned_w2n]
      \\ qmatch_goalsub_abbrev_tac`pv MOD dw MOD _`
      \\ `pv MOD dw = pv` by (
        simp[Abbr`pv`,Abbr`dw`]
        \\ irule LESS_EQ_LESS_TRANS
        \\ qexists_tac`LENGTH (prog_to_bytes code2)`
        \\ simp[]
        \\ old_drule pos_val_bound
        \\ disch_then(qspec_then`0`mp_tac o CONV_RULE SWAP_FORALL_CONV)
        \\ simp[] )
      \\ simp[]
      \\ qunabbrev_tac`pv`
      \\ qabbrev_tac `ffi_names = TAKE (THE (mmio_pcs_min_index
        mc_conf.ffi_names)) mc_conf.ffi_names`
      \\ match_mp_tac pos_val_MOD_0 \\ gvs[]
      \\ metis_tac[has_odd_inst_alignment] )
    \\ rpt strip_tac
    \\ rfs[] \\ fs[] \\ rfs[]
    \\ FIRST_X_ASSUM (qspecl_then [`shift_interfer l' mc_conf`,
         `code2`,`labs`,`(asm (JumpReg r1)
            (t1.pc + n2w (LENGTH (mc_conf.target.config.encode (JumpReg
              r1)))) t1)`,`ms2`] mp_tac)
    \\ impl_tac >-
     (conj_tac
       >- (irule oracle_tie_step
           \\ qpat_assum `oracle_tie _ _ _` (irule_at Any)
           \\ simp[labSemTheory.upd_pc_def,labSemTheory.dec_clock_def]
           \\ metis_tac[])
      \\ full_simp_tac(srw_ss())[shift_interfer_def,state_rel_def
        ,asm_def,LET_DEF] \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[asmSemTheory.upd_pc_def
        ,asmSemTheory.assert_def,
             asmSemTheory.read_reg_def,dec_clock_def
               ,labSemTheory.upd_pc_def,
             labSemTheory.assert_def]
      \\ full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def]
      \\ FIRST_X_ASSUM (K ALL_TAC o Q.SPEC `r1:num`)
      \\ FIRST_X_ASSUM (K ALL_TAC o Q.SPEC `r1:num`)
      \\ FIRST_X_ASSUM (K ALL_TAC o Q.SPEC `r1:num`)
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `r1:num`)
      \\ strip_tac \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[word_loc_val_def]
      \\ Cases_on `lab_lookup l1 l2 labs` \\ full_simp_tac(srw_ss())[]
      \\ Q.PAT_X_ASSUM `xx = t1.regs r1` (fn th =>
        full_simp_tac(srw_ss())[GSYM th])
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l1`,`l2`]) \\
        full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ RES_TAC \\ full_simp_tac(srw_ss())[] \\ rpt strip_tac \\
        res_tac \\ srw_tac[][]
      >- ((alignmentTheory.aligned_add_sub_cor
          |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> irule)
        \\ conj_tac >- fs[alignmentTheory.aligned_bitwise_and]
        \\ simp[aligned_w2n]
        \\ qmatch_goalsub_abbrev_tac`pv MOD dw MOD _`
        \\ `pv MOD dw = pv` by (
          simp[Abbr`pv`,Abbr`dw`]
          \\ irule LESS_EQ_LESS_TRANS
          \\ qexists_tac`LENGTH (prog_to_bytes code2)`
          \\ simp[]
          \\ old_drule pos_val_bound
          \\ disch_then(qspec_then`0`mp_tac o CONV_RULE
            SWAP_FORALL_CONV)
          \\ simp[] )
        \\ simp[]
        \\ qunabbrev_tac`pv`
        \\ match_mp_tac $ Q.GEN `ffi_names` pos_val_MOD_0 \\ fs[]
        \\ metis_tac[has_odd_inst_alignment])
      >- (fs[share_mem_state_rel_def] >> share_mem_state_rel_tac)
      >- fs[share_mem_domain_code_rel_def] )
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock - 1 + k`MP_TAC) \\
      srw_tac[][]
    \\ `s1.clock - 1 + k + l' = s1.clock + (k + l' - 1)` by DECIDE_TAC
    \\ Q.EXISTS_TAC `k + l' - 1` \\ full_simp_tac(srw_ss())[]
    \\ Q.EXISTS_TAC `ms2'` \\ fs[state_rel_def,shift_interfer_def] )
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[CBW]:
*)
(* CBW *)
(* HOL4 ML code, not ported:
  say "CBW" >>
  fs[case_eq_thms]>>
  fs[dec_clock_def]>>
  qmatch_asmsub_rename_tac `Asm (Cbw r1 r2) bytes len`>>
  qabbrev_tac `ffi_names = TAKE (THE (mmio_pcs_min_index
    mc_conf.ffi_names)) mc_conf.ffi_names` >>
  mp_tac IMP_bytes_in_memory_Cbw>> impl_tac>-
    fs[state_rel_def]>>
  strip_tac>>
  `t1.regs r1 = w1 ∧ t1.regs r2 = w2` by
    (fs[state_rel_def]>>
    qpat_assum`!r. word_loc_val _ _ _ = SOME _` (qspec_then`r1`
      mp_tac)>>
    qpat_x_assum`!r. word_loc_val _ _ _ = SOME _` (qspec_then`r2`
      mp_tac)>>
    simp[word_loc_val_def])>>
  qpat_x_assum`buffer_write _ _ _ = _ `mp_tac>>
  simp[buffer_write_def]>>
  strip_tac>>
  qmatch_asmsub_abbrev_tac`Inst jj`>>
  (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`Inst jj`]MP_TAC
          asm_step_IMP_evaluate_step_nop) \\ full_simp_tac(srw_ss())[]
  \\ disch_then (mp_tac o Q.SPEC `bytes'`)
  \\ fs[asm_def] >>
  `inst jj t1 = t1 with mem := ((w1 =+ w2w w2) t1.mem)` by
    (unabbrev_all_tac >>
    simp[inst_def,mem_op_def,mem_store_def,alignmentTheory.aligned_0]>>
    EVAL_TAC>> simp[asm_state_component_equality]>>
    fs[state_rel_def]>>rw[]>>
    first_x_assum old_drule>>simp[])
  \\ impl_tac>-
    (fs[state_rel_def]>>
    conj_tac >- (
      fs[asm_fetch_def]
      \\ drule_all $ GEN_ALL IMP_bytes_in_memory
      \\ strip_tac
      \\ fs[]
      \\ `!op re a. Cbw r1 r2 <> ShareMem op re a` by simp[]
      \\ drule_all $ GEN_ALL IMP_ffi_entry_pcs_disjoint_Asm
      \\ `LENGTH bytes' <= LENGTH (line_bytes j)` suffices_by
        metis_tac[ffi_entry_pcs_disjoint_LENGTH_shorter]
      \\ Cases_on `j`
      \\ fs[line_similar_def,line_ok_def]) >>
    conj_tac>-
      (match_mp_tac (GEN_ALL bytes_in_mem_IMP)>>
      qexists_tac`s1.mem_domain`>>
      match_mp_tac bytes_in_mem_UPDATE>>
      rw[]>>
      PURE_REWRITE_TAC [GSYM WORD_ADD_ASSOC]>>
      `LENGTH bytes' + pos_val s1.pc 0 code2 <= LENGTH (prog_to_bytes
        code2)` by
        (qpat_x_assum`pos_val _ _ _ = _` sym_sub_tac>>
        old_drule pos_val_bound>>
        disch_then(qspecl_then [`s1.pc+1`,`0`] assume_tac)>>
        fs[])>>
      rw[]>>
      simp[word_add_n2w])>>
    simp[asm_step_nop_def,asm_def]) >>
  strip_tac>>
  first_x_assum (qspecl_then [`shift_interfer l mc_conf`,
        `code2`,`labs`,
        `(asm (Inst jj) (t1.pc + n2w (LENGTH (bytes':word8 list)))
          t1)`,`ms2`] mp_tac)>>
  impl_tac>-
    (conj_tac
      >- (irule oracle_tie_step
          \\ qpat_assum `oracle_tie _ _ _` (irule_at Any)
          \\ simp[labSemTheory.inc_pc_def,labSemTheory.dec_clock_def,
                  labSemTheory.upd_pc_def,labSemTheory.upd_reg_def
                    ,asm_inst_consts]
          \\ metis_tac[])
     \\ unabbrev_all_tac \\ rpt strip_tac \\
       full_simp_tac(srw_ss())[asm_def]
    >-
      (full_simp_tac(srw_ss())[shift_interfer_def])
    >>
    qpat_x_assum`_ = new_cb` sym_sub_tac >> fs[]>>
    match_mp_tac state_rel_shift_interfer>>
    fs[state_rel_def]>>
    rfs[]>>fs[]>>
    conj_tac>- metis_tac[]>>
    conj_tac>- metis_tac[]>>
    conj_tac>-
      (rw[APPLY_UPDATE_THM]>>
      first_x_assum old_drule>>
      fs[])
    \\ conj_tac>-
      (strip_tac>>
      qpat_x_assum`!n. n <s1.code_buffer.space_left ⇒ _`
        (qspec_then`n+1` assume_tac)>>
      fs[])
    \\ conj_tac >-
*)
      (* non-overlap of cb with code *)
(* HOL4 ML code, not ported:
      (match_mp_tac bytes_in_mem_UPDATE>>rw[]>>
      PURE_REWRITE_TAC [GSYM WORD_ADD_ASSOC]>>
      simp[word_add_n2w])
    \\ conj_tac >-
      (simp[bytes_in_mem_APPEND]
    \\ conj_tac >-
*)
      (* non-overlap of cb with itself *)
(* HOL4 ML code, not ported:
      (match_mp_tac bytes_in_mem_UPDATE>>
        rw[])
    \\ simp[bytes_in_mem_def,APPLY_UPDATE_THM]>>
       first_x_assum old_drule>>fs[])
    \\ simp[GSYM word_add_n2w]
     >> fs[upd_pc_def, inc_pc_def, share_mem_state_rel_def] >>
      share_mem_state_rel_tac)
  \\ rpt strip_tac \\
    full_simp_tac(srw_ss())[inc_pc_def,dec_clock_def
    ,labSemTheory.upd_reg_def]
  \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock - 1 + k` mp_tac)
  \\ rpt strip_tac
  \\ Q.EXISTS_TAC `k + l - 1` \\ full_simp_tac(srw_ss())[]
  \\ `^s1.clock - 1 + k + l = ^s1.clock + (k + l - 1)` by decide_tac
  \\ fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[ShareMemOp]:
*)
(* share_mem_op *)
(* HOL4 ML code, not ported:
  say "share_mem_op"
  \\ Cases_on `m` >>
  fs[share_mem_op_def,share_mem_load_def,share_mem_store_def]>>
  gvs[pair_case_eq,option_case_eq,
    ffi_result_case_eq,CaseEq"word_loc"]>>
  fs[asm_fetch_def,state_rel_def]>>
  drule_all IMP_bytes_in_memory_ShareMem>>strip_tac>>
  fs[share_mem_domain_code_rel_def]>>
  qpat_assum `!pc op re a inst len i. asm_fetch_aux _ _ = SOME _ /\
  mmio_pcs_min_index _ = SOME _ ==> _` drule_all>>strip_tac>>
  fs[get_memop_info_def]>>
  old_drule find_index_is_MEM>>strip_tac>>
  simp[Once targetSemTheory.evaluate_def]>>
  qpat_x_assum ‘target_state_rel _ _ _’ assume_tac>>
  fs[target_state_rel_def]>>
*)

(* HOL4 ML code, not ported:
  qpat_assum ‘share_mem_state_rel _ _ _ _ ’ assume_tac>>
  fs[share_mem_state_rel_def]>>
  qpat_assum `!index' i'. mmio_pcs_min_index _ = SOME i' /\ index' < _
    /\
  _ ==> _` $ qspecl_then [`index`, `i`] old_drule>>
*)

(* HOL4 ML code, not ported:
  (impl_tac>-(old_drule find_index_LESS_LENGTH >> fs[]))>>
  strip_tac>>
  `mc_conf.target.get_pc ms1 <> mc_conf.ccache_pc /\
  mc_conf.target.get_pc ms1 <> mc_conf.halt_pc` by (
    irule ffi_entry_pcs_NOT_ccache_OR_halt_pc >> gvs[])>>
  fs[]>>
*)

(* HOL4 ML code, not ported:
  Cases_on ‘a'’>>
  fs[labSemTheory.addr_def,CaseEq"word_loc"]>>
  qpat_assum ‘∀r. word_loc_val _ _ _ = SOME _’ $ qspec_then ‘n''’
    assume_tac>>
  TRY (qpat_assum ‘∀r. word_loc_val _ _ _ = SOME _’ $ qspec_then ‘n'’
    assume_tac)>>
  fs[option_case_eq,CaseEq"word_loc"]>>
  qpat_x_assum ‘read_reg n'' _ = _ ’ $ assume_tac>>
  TRY (qpat_x_assum ‘read_reg n' _ = _ ’ $ assume_tac)>>
  fs[word_loc_val_def]>>
  qpat_x_assum ‘_ = v'’ $ assume_tac o GSYM>>
*)


(* HOL4 ML code, not ported:
  fs[apply_oracle_def,shift_seq_def]>>
  qpat_x_assum ‘_ = ms1'’ $ assume_tac o GSYM>>fs[]>>
  qpat_x_assum ‘∀a b c d e f g h i j k l. _ ⇒ _’ mp_tac>>
  disch_then $ old_drule>>fs[]>>
  old_drule find_index_LESS_LENGTH>>strip_tac>>
  strip_tac>>
  (conj_tac >-
    (pop_assum mp_tac>>
     simp[target_state_rel_def]>>strip_tac>>
     pop_assum $ irule o cj 1>>
     fs[find_index_INDEX_OF, INDEX_OF_eq_SOME]>>
     rpt (last_x_assum $ irule_at Any)>>fs[]))>>
  (conj_tac >-
    (qpat_x_assum `_ = new_oracle` (SUBST_ALL_TAC o SYM)
     \\ irule (REWRITE_RULE [shift_seq_def] oracle_tie_ffi_next)
     \\ qpat_assum `oracle_tie _ _ _` (irule_at Any)
     \\ simp[]
     \\ irule_at Any (REWRITE_RULE [shift_seq_def]
       next_interference_SharedMem)
     \\ gvs[]))>>
*)

(* HOL4 ML code, not ported:
  qabbrev_tac ‘pc = p + n2w (LENGTH bytes + pos_val s1.pc 0n code2)’>>
  qmatch_asmsub_abbrev_tac ‘call_FFI _ _ [nb] _ = _’>>
  last_x_assum $ qspecl_then [‘ms1’, ‘0’, ‘new_bytes’, ‘t1’, ‘s1.ffi’,
    ‘new_ffi’] mp_tac>>
  (impl_tac>-
    fs[target_state_rel_def,find_index_INDEX_OF, INDEX_OF_eq_SOME])>>
  strip_tac>>rfs[Abbr ‘nb’]>>
*)

(* HOL4 ML code, not ported:
  qmatch_asmsub_abbrev_tac ‘target_state_rel mc_conf.target t1_new’>>
*)

(* HOL4 ML code, not ported:
  qexistsl [‘code2’, ‘labs’, ‘t1_new’] >> fs[]>>
  fs[Abbr ‘t1_new’]>>
  qpat_x_assum ‘∀a b c d e f. _ ⇒ _’ mp_tac>>
  ‘call_FFI_rel꙳ s1.ffi s1.ffi’ by fs[cj 1 RTC_RULES]>>
  rpt (disch_then $ drule_at Any)>>
  fs[find_index_INDEX_OF, INDEX_OF_eq_SOME]>>
  fs[target_state_rel_def,UPDATE_def]>>
  rw[word_loc_val_def]>>
  metis_tac[word_loc_val_def]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Jump]:
*)
(* Jump *)
(* HOL4 ML code, not ported:
  say "Jump"
  \\ qmatch_assum_rename_tac
       `asm_fetch s1 = SOME (LabAsm (Jump jtarget) l1 l2 l3)`
  \\ qmatch_assum_rename_tac
       `asm_fetch s1 = SOME (LabAsm (Jump jtarget) l bytes n)`
  \\ Cases_on `get_pc_value jtarget s1` \\ full_simp_tac(srw_ss())[]
  \\ qabbrev_tac `ffi_names = TAKE (THE (mmio_pcs_min_index
    mc_conf.ffi_names)) mc_conf.ffi_names`
  \\ mp_tac IMP_bytes_in_memory_Jump \\ full_simp_tac(srw_ss())[]
  \\ match_mp_tac IMP_IMP \\ strip_tac
  THEN1 (full_simp_tac(srw_ss())[state_rel_def] \\ imp_res_tac
    bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[])
  \\ rpt strip_tac \\ pop_assum mp_tac
  \\ qpat_abbrev_tac `jj = asm$Jump lll` \\ rpt strip_tac
  \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]MP_TAC
       asm_step_IMP_evaluate_step_find_next) \\
         full_simp_tac(srw_ss())[]
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF]
    \\ full_simp_tac(srw_ss())[asm_step_def,asm_def,LET_DEF]
    \\ imp_res_tac bytes_in_mem_IMP
    \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def
      ,asmSemTheory.upd_pc_def]
    \\ rev_full_simp_tac(srw_ss())[] \\ unabbrev_all_tac
    \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def
      ,asmSemTheory.upd_pc_def,asm_def]
    \\ fs[asm_fetch_def]
    \\ drule_all $ GEN_ALL IMP_bytes_in_memory
    \\ strip_tac
    \\ fs[]
    \\ drule_all $ GEN_ALL IMP_ffi_entry_pcs_disjoint_LabAsm
    \\ `LENGTH
          ((mc_conf.target.config.encode
            (Jump
               (n2w (find_pos jtarget labs) +
                -n2w (pos_val s1.pc 0 code2)))))
        <= LENGTH (line_bytes j)` suffices_by
      metis_tac[ffi_entry_pcs_disjoint_LENGTH_shorter]
    \\ Cases_on `j`
    \\ gvs[line_similar_def,line_ok_def,line_length_def,line_bytes_def]
    \\ fs[get_label_def]
    \\ Cases_on `jtarget`
    \\ fs[]
    \\ Cases_on `lab_lookup n'' n0 labs`
    \\ gvs[lab_inst_def,enc_with_nop_thm, LENGTH_APPEND]
    \\ old_drule lab_lookup_IMP
    \\ fs[]
  )
  \\ rpt strip_tac
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l' mc_conf`,
       `code2`,`labs`,
       `(asm jj (t1.pc + n2w (LENGTH (mc_conf.target.config.encode jj)))
         t1)`,`ms2`])
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (conj_tac
     >- (irule oracle_tie_step
         \\ qpat_assum `oracle_tie _ _ _` (irule_at Any)
         \\ simp[labSemTheory.inc_pc_def,labSemTheory.dec_clock_def,
                 labSemTheory.upd_pc_def,labSemTheory.upd_reg_def
                   ,asm_inst_consts]
         \\ metis_tac[])
    \\ unabbrev_all_tac
    \\ full_simp_tac(srw_ss())[shift_interfer_def,state_rel_def,asm_def
      ,LET_DEF] \\ rev_full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[asmSemTheory.upd_pc_def
      ,asmSemTheory.assert_def,
           asmSemTheory.read_reg_def,
             dec_clock_def,labSemTheory.upd_pc_def,
           labSemTheory.assert_def,asm_def,
           jump_to_offset_def]
    \\ full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def
      ,read_reg_def]
    \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
          WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[get_pc_value_def]
    \\ Cases_on `jtarget` \\ full_simp_tac(srw_ss())[]
    \\ qmatch_assum_rename_tac `loc_to_pc l1 l2 s1.code = SOME x`
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l1`,`l2`]) \\
      full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ imp_res_tac lab_lookup_IMP \\ full_simp_tac(srw_ss())[]
    >- metis_tac[]
    >- metis_tac[]
    >- (fs[share_mem_state_rel_def] >> share_mem_state_rel_tac)
    >- fs[share_mem_domain_code_rel_def] )
  \\ rpt strip_tac>>
  irule_at Any EQ_TRANS>>
  first_x_assum $ irule_at Any>>
  irule_at Any EQ_TRANS>>
  `!k. evaluate mc_conf s1.ffi (k + l') ms1 =
       evaluate (shift_interfer l' mc_conf) s1.ffi k ms2` by
         metis_tac[]>>
  first_x_assum $ irule_at (Pos last)>>
  `l' <> 0` by metis_tac[]>>
  `s1.clock - 1 + k + l' = s1.clock + (k + l' - 1)` by DECIDE_TAC>>
  metis_tac[]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[JumpCmp]:
*)
(* JumpCmp *)
(* HOL4 ML code, not ported:
  say "JumpCmp"
  \\ qmatch_assum_rename_tac
       `asm_fetch s1 = SOME (LabAsm (JumpCmp cmp rr ri jtarget) l1 l2
         l3)`
  \\ qmatch_assum_rename_tac
       `asm_fetch s1 = SOME (LabAsm (JumpCmp cmp rr ri jtarget) l bytes
         n)`
  \\ `word_cmp cmp (read_reg rr s1) (labSem$reg_imm ri s1) =
      SOME (asm$word_cmp cmp (read_reg rr t1) (reg_imm ri t1))` by
   (Cases_on `word_cmp cmp (read_reg rr s1) (reg_imm ri s1)` \\
     full_simp_tac(srw_ss())[]
    \\ imp_res_tac word_cmp_lemma \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[]
  \\ qabbrev_tac `ffi_names = TAKE (THE (mmio_pcs_min_index
    mc_conf.ffi_names)) mc_conf.ffi_names`
  \\ Cases_on `word_cmp cmp (read_reg rr t1) (reg_imm ri t1)` \\
    full_simp_tac(srw_ss())[]
*)


(* HOL4 ML code, not ported:
  THEN1
   (Cases_on `get_pc_value jtarget s1` \\ full_simp_tac(srw_ss())[]
    \\ mp_tac IMP_bytes_in_memory_JumpCmp \\ full_simp_tac(srw_ss())[]
    \\ match_mp_tac IMP_IMP \\ strip_tac
    THEN1 (full_simp_tac(srw_ss())[state_rel_def] \\ imp_res_tac
      bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[])
    \\ rpt strip_tac \\ pop_assum mp_tac
    \\ qpat_abbrev_tac `jj = asm$JumpCmp cmp rr ri lll` \\ rpt strip_tac
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
         asm_step_IMP_evaluate_step_find_next) \\
           full_simp_tac(srw_ss())[]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF]
      \\ unabbrev_all_tac \\
        full_simp_tac(srw_ss())[asm_step_def,asm_def,LET_DEF]
      \\ imp_res_tac bytes_in_mem_IMP
      \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def
        ,asmSemTheory.upd_pc_def]
      \\ rev_full_simp_tac(srw_ss())[] \\ unabbrev_all_tac
      \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def
        ,asmSemTheory.upd_pc_def,asm_def]
      \\ fs[asm_fetch_def]
      \\ drule_all $ GEN_ALL IMP_bytes_in_memory
      \\ strip_tac
      \\ fs[]
      \\ drule_all $ GEN_ALL IMP_ffi_entry_pcs_disjoint_LabAsm
      \\ ho_match_mp_tac (
        PURE_REWRITE_RULE [satTheory.AND_IMP] o
        PURE_REWRITE_RULE [Once CONJ_SYM] $
        GEN_ALL ffi_entry_pcs_disjoint_LENGTH_shorter )
      \\ Cases_on `j`
      \\ gvs[line_similar_def,line_ok_def,line_length_def
        ,line_bytes_def]
      \\ fs[get_label_def]
      \\ Cases_on `jtarget`
      \\ fs[]
      \\ Cases_on `lab_lookup n'' n0 labs`
      \\ gvs[lab_inst_def,enc_with_nop_thm, LENGTH_APPEND]
      \\ old_drule lab_lookup_IMP
      \\ fs[]
    )
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l' mc_conf`,
         `code2`,`labs`,
         `(asm jj (t1.pc + n2w (LENGTH (mc_conf.target.config.encode
           jj))) t1)`,`ms2`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (conj_tac
       >- (irule oracle_tie_step
           \\ qpat_assum `oracle_tie _ _ _` (irule_at Any)
           \\ simp[labSemTheory.inc_pc_def,labSemTheory.dec_clock_def,
                   labSemTheory.upd_pc_def,labSemTheory.upd_reg_def
                     ,asm_inst_consts]
           \\ metis_tac[])
      \\ unabbrev_all_tac
      \\ full_simp_tac(srw_ss())[shift_interfer_def,state_rel_def
        ,asm_def,LET_DEF] \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[asmSemTheory.upd_pc_def
        ,asmSemTheory.assert_def,
             asmSemTheory.read_reg_def,
               dec_clock_def,labSemTheory.upd_pc_def,
             labSemTheory.assert_def,asm_def,
             jump_to_offset_def]
      \\ full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def
        ,read_reg_def]
      \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
            WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[get_pc_value_def]
      \\ Cases_on `jtarget` \\ full_simp_tac(srw_ss())[]
      \\ qmatch_assum_rename_tac `loc_to_pc l1 l2 s1.code = SOME x`
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l1`,`l2`]) \\
        full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ imp_res_tac lab_lookup_IMP \\ full_simp_tac(srw_ss())[]
      >- metis_tac []
      >- metis_tac []
      >- (fs[share_mem_state_rel_def] >> share_mem_state_rel_tac)
      >- fs[share_mem_domain_code_rel_def] )
    \\ rpt strip_tac>>
    irule_at Any EQ_TRANS>>
    first_x_assum $ irule_at Any>>
    irule_at Any EQ_TRANS>>
    `!k. evaluate mc_conf s1.ffi (k + l') ms1 =
         evaluate (shift_interfer l' mc_conf) s1.ffi k ms2` by
           metis_tac[]>>
    first_x_assum $ irule_at (Pos last)>>
    `l' <> 0` by metis_tac[]>>
    `s1.clock - 1 + k + l' = s1.clock + (k + l' - 1)` by DECIDE_TAC>>
    metis_tac[])
  \\ mp_tac (IMP_bytes_in_memory_JumpCmp_1) \\ full_simp_tac(srw_ss())[]
  \\ match_mp_tac IMP_IMP \\ strip_tac
  THEN1 (full_simp_tac(srw_ss())[state_rel_def] \\ imp_res_tac
    bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[])
  \\ rpt strip_tac \\ pop_assum mp_tac \\ pop_assum mp_tac
  \\ qpat_abbrev_tac `jj = asm$JumpCmp cmp rr ri lll` \\ rpt strip_tac
  \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
       asm_step_IMP_evaluate_step_nop) \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ pop_assum (mp_tac o Q.SPEC `bytes'`)
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF] \\
     unabbrev_all_tac \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[asm_step_nop_def,asm_def,LET_DEF]
    \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def,upd_reg_def]
    \\ fs[asm_fetch_def]
    \\ drule_all $ GEN_ALL IMP_bytes_in_memory
    \\ strip_tac
    \\ fs[]
    \\ drule_all $ GEN_ALL IMP_ffi_entry_pcs_disjoint_LabAsm
    \\ ho_match_mp_tac (
      PURE_REWRITE_RULE [satTheory.AND_IMP] o
      PURE_REWRITE_RULE [Once CONJ_SYM] $
      GEN_ALL ffi_entry_pcs_disjoint_LENGTH_shorter )
    \\ Cases_on `j`
    \\ gvs[line_similar_def,line_ok_def,line_length_def,line_bytes_def]
      )
  \\ rpt strip_tac
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l' mc_conf`,
       `code2`,`labs`,
       `(asm jj (t1.pc + n2w (LENGTH (bytes':word8 list))) t1)`,`ms2`])
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (conj_tac
     >- (irule oracle_tie_step
         \\ qpat_assum `oracle_tie _ _ _` (irule_at Any)
         \\ simp[labSemTheory.inc_pc_def,labSemTheory.dec_clock_def,
                 labSemTheory.upd_pc_def,labSemTheory.upd_reg_def
                   ,asm_inst_consts]
         \\ metis_tac[])
    \\ unabbrev_all_tac
    \\ full_simp_tac(srw_ss())[shift_interfer_def,state_rel_def,asm_def
      ,LET_DEF] \\ rev_full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[asmSemTheory.upd_pc_def
      ,asmSemTheory.assert_def,
           asmSemTheory.read_reg_def,
             dec_clock_def,labSemTheory.upd_pc_def,
           labSemTheory.assert_def,asm_def,
           jump_to_offset_def,inc_pc_def,asmSemTheory.upd_reg_def,
           labSemTheory.upd_reg_def]
    \\ full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def
      ,read_reg_def]
    \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
          WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[get_pc_value_def]
    \\ rpt strip_tac \\ res_tac \\ full_simp_tac(srw_ss())[]
    >- (fs[share_mem_state_rel_def] >> share_mem_state_rel_tac)
    >- fs[share_mem_domain_code_rel_def] )
  \\ rpt strip_tac \\
    full_simp_tac(srw_ss())[inc_pc_def,dec_clock_def
    ,labSemTheory.upd_reg_def]
  \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock - 1 + k`mp_tac)
  \\ rpt strip_tac>>
  irule_at Any EQ_TRANS>>
  first_x_assum $ irule_at Any>>
  irule_at Any EQ_TRANS>>
  first_x_assum $ irule_at (Pos last)>>
  `s1.clock - 1 + k + l' = s1.clock + (k + l' - 1)` by DECIDE_TAC>>
  metis_tac[]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Call]:
*)
(* Call *)
(* HOL4 ML code, not ported:
  say "Call"
  \\ qmatch_assum_rename_tac
       `asm_fetch s1 = SOME (LabAsm (Call lab) x1 x2 x3)`
  \\ Cases_on `lab`
  \\ qmatch_assum_rename_tac
       `asm_fetch s1 = SOME (LabAsm (Call (Lab l1 l2)) l bytes len)`
  \\ qabbrev_tac `ffi_names = TAKE (THE (mmio_pcs_min_index
    mc_conf.ffi_names)) mc_conf.ffi_names`
  \\ (Q.SPECL_THEN [`Lab l1 l2`,`len`]mp_tac
          (Q.GENL[`ww`,`n`]IMP_bytes_in_memory_Call))
  \\ match_mp_tac IMP_IMP \\ strip_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[state_rel_def] \\ imp_res_tac
    bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[LocValue]:
*)
(* LocValue *)
(* HOL4 ML code, not ported:
  say "LocValue"
  \\ qmatch_assum_rename_tac
       `asm_fetch s1 = SOME (LabAsm (LocValue reg lab) x1 x2 x3)`
  \\ Cases_on `lab`
  \\ qmatch_assum_rename_tac
       `asm_fetch s1 = SOME (LabAsm (LocValue reg (Lab l1 l2)) ww bytes
         len)`
  \\ full_simp_tac(srw_ss())[lab_to_loc_def]
  \\ qabbrev_tac `ffi_names = TAKE (THE (mmio_pcs_min_index
    mc_conf.ffi_names)) mc_conf.ffi_names`
  \\ mp_tac (Q.INST [`l`|->`ww`,`n`|->`len`]
             IMP_bytes_in_memory_LocValue) \\ full_simp_tac(srw_ss())[]
  \\ match_mp_tac IMP_IMP \\ strip_tac
  THEN1 (full_simp_tac(srw_ss())[state_rel_def]
         \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[])
  \\ rpt strip_tac \\ pop_assum mp_tac
  \\ Cases_on `get_pc_value (Lab l1 l2) s1` \\ fs []
  \\ qpat_abbrev_tac `jj = asm$Loc reg lll` \\ rpt strip_tac
  \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
       asm_step_IMP_evaluate_step_nop) \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ pop_assum (mp_tac o Q.SPEC `bytes'`)
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF]
    \\ unabbrev_all_tac \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[asm_step_nop_def,asm_def,LET_DEF]
    \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def,upd_reg_def]
    \\ fs[asm_fetch_def]
    \\ drule_all $ GEN_ALL IMP_bytes_in_memory
    \\ strip_tac
    \\ fs[]
    \\ drule_all $ GEN_ALL IMP_ffi_entry_pcs_disjoint_LabAsm
    \\ ho_match_mp_tac (
      PURE_REWRITE_RULE [satTheory.AND_IMP] o
      PURE_REWRITE_RULE [Once CONJ_SYM] $
      GEN_ALL ffi_entry_pcs_disjoint_LENGTH_shorter )
    \\ Cases_on `j`
    \\ gvs[line_similar_def,line_ok_def,line_length_def,line_bytes_def]
      )
  \\ rpt strip_tac
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l mc_conf`,
       `code2`,`labs`,
       `(asm jj (t1.pc + n2w (LENGTH (bytes':word8 list))) t1)`,`ms2`])
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (conj_tac
     >- (irule oracle_tie_step
         \\ qpat_assum `oracle_tie _ _ _` (irule_at Any)
         \\ simp[labSemTheory.inc_pc_def,labSemTheory.dec_clock_def,
                 labSemTheory.upd_pc_def,labSemTheory.upd_reg_def
                   ,asm_inst_consts]
         \\ metis_tac[])
    \\ unabbrev_all_tac
    \\ full_simp_tac(srw_ss())[shift_interfer_def,state_rel_def,asm_def
      ,LET_DEF]
    \\ rev_full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[asmSemTheory.upd_pc_def
      ,asmSemTheory.assert_def,
           asmSemTheory.read_reg_def,
             dec_clock_def,labSemTheory.upd_pc_def,
           labSemTheory.assert_def,asm_def,
           jump_to_offset_def,inc_pc_def,asmSemTheory.upd_reg_def,
           labSemTheory.upd_reg_def]
    \\ full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def
      ,read_reg_def]
    \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
          WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[get_pc_value_def]
    \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM] \\
      srw_tac[][word_loc_val_def]
    \\ res_tac \\ full_simp_tac(srw_ss())[]
    >- (
      Cases_on `lab_lookup l1 l2 labs` \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac lab_lookup_IMP \\ srw_tac[][] )
    >- (fs[share_mem_state_rel_def] >> share_mem_state_rel_tac)
    >- fs[share_mem_domain_code_rel_def] )
  \\ rpt strip_tac>>
  gvs[inc_pc_def,dec_clock_def,labSemTheory.upd_reg_def]>>
  irule_at Any EQ_TRANS>>
  first_x_assum $ irule_at Any>>
  first_x_assum $ qspec_then ‘k + s1.clock - 1’ assume_tac>>
  fs[]>>
  qpat_x_assum ‘evaluate _ _ _ _ = evaluate _ _ _ _’ mp_tac>>
  `k + s1.clock - 1 + l = k + l - 1 + s1.clock` by DECIDE_TAC>>
  pop_assum (fn h => rewrite_tac[h])>>strip_tac>>
  first_assum $ irule_at Any
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[CallFFI]:
*)
(* CallFFI *)
(* HOL4 ML code, not ported:
  say "CallFFI"
  \\ qmatch_assum_rename_tac `asm_fetch s1 = SOME (LabAsm (CallFFI s) l1
    l2 l3)`
  \\ qmatch_assum_rename_tac
       `asm_fetch s1 = SOME (LabAsm (CallFFI s) l bytes n)`
  \\ Cases_on `s1.regs s1.len_reg` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `s1.regs s1.len2_reg` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `s1.regs s1.link_reg` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `s1.regs s1.ptr_reg` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `s1.regs s1.ptr2_reg` \\ full_simp_tac(srw_ss())[]
  \\ qmatch_assum_rename_tac `read_reg _.len2_reg _ = Word c2`
  \\ qmatch_assum_rename_tac `read_reg _.ptr2_reg _ = Word c2'`
  \\ qmatch_assum_rename_tac `read_reg _.ptr_reg _ = Word c'`
  \\ Cases_on `read_bytearray c' (w2n c) (mem_load_byte_aux s1.mem
    s1.mem_domain s1.be)`
  \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `read_bytearray c2' (w2n c2) (mem_load_byte_aux s1.mem
    s1.mem_domain s1.be)`
  \\ full_simp_tac(srw_ss())[]
  \\ qmatch_assum_rename_tac `s1.regs s1.link_reg = Loc n1 n2`
  \\ qmatch_asmsub_abbrev_tac `loc_to_pc a1 a2 a3`
  \\ Cases_on `loc_to_pc a1 a2 a3` >- fs[]
  \\ unabbrev_all_tac \\ fs[]
  \\ qabbrev_tac `ffi_names = TAKE (THE (mmio_pcs_min_index
    mc_conf.ffi_names)) mc_conf.ffi_names`
  \\ mp_tac (Q.GEN `name` IMP_bytes_in_memory_CallFFI) \\
    full_simp_tac(srw_ss())[]
  \\ match_mp_tac IMP_IMP \\ strip_tac
  THEN1 (
    full_simp_tac(srw_ss())[state_rel_def]
    \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[]
  )
  \\ rpt strip_tac \\ pop_assum mp_tac
  \\ qpat_abbrev_tac `jj = asm$Jump lll` \\ rpt strip_tac
  \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
       asm_step_IMP_evaluate_step_find_next) \\
         full_simp_tac(srw_ss())[]
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (
    full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF]
    \\ full_simp_tac(srw_ss())[asm_step_def,asm_def,LET_DEF]
    \\ imp_res_tac bytes_in_mem_IMP
    \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,
         asmSemTheory.upd_pc_def]
    \\ rev_full_simp_tac(srw_ss())[] \\ unabbrev_all_tac
    \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,
         asmSemTheory.upd_pc_def,asm_def]
    \\ fs[asm_fetch_def]
    \\ drule_all $ GEN_ALL IMP_bytes_in_memory
    \\ strip_tac
    \\ fs[]
    \\ drule_all $ GEN_ALL IMP_ffi_entry_pcs_disjoint_LabAsm
    \\ ho_match_mp_tac (
      PURE_REWRITE_RULE [satTheory.AND_IMP] o
      PURE_REWRITE_RULE [Once CONJ_SYM] $
      GEN_ALL ffi_entry_pcs_disjoint_LENGTH_shorter )
    \\ Cases_on `j`
    \\ gvs[line_similar_def,line_ok_def,line_length_def,line_bytes_def]
    \\ gvs[lab_inst_def,enc_with_nop_thm, LENGTH_APPEND]
  )
  \\ rpt strip_tac
  \\ Cases_on `loc_to_pc n1 n2 s1.code` \\ full_simp_tac(srw_ss())[]
  \\ qmatch_assum_rename_tac `loc_to_pc n1 n2 s1.code = SOME new_pc`
  \\ `mc_conf.target.get_pc ms2 = p - n2w ((3 + get_ffi_index ffi_names
    (ExtCall s)) * ffi_offset)` by
   (full_simp_tac(srw_ss())[GSYM PULL_FORALL]
    \\ full_simp_tac(srw_ss())[state_rel_def] \\
      rev_full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())
         [encoder_correct_def,target_ok_def,target_state_rel_def]
    \\ unabbrev_all_tac
    \\ full_simp_tac(srw_ss())[asm_def,asmSemTheory.jump_to_offset_def,
         asmSemTheory.upd_pc_def]
    \\ rewrite_tac [GSYM word_sub_def,WORD_SUB_PLUS,
         GSYM word_add_n2w,WORD_ADD_SUB]) \\ full_simp_tac(srw_ss())[]
  \\ `has_io_name s s1.code` by
        (imp_res_tac IMP_has_io_name \\ NO_TAC)
  \\ `MEM (ExtCall s) mc_conf.ffi_names` by (
    imp_res_tac has_io_name_find_index>>
    imp_res_tac find_index_is_MEM>>
    gvs[list_subset_def,state_rel_def,EVERY_MEM,Abbr`ffi_names`]>>
    drule_all mmio_pcs_min_index_is_SOME >>
    strip_tac >>
    gvs[MEM_FILTER] >>
    `MEM s mc_conf.ffi_names` by (
      first_x_assum irule >> gvs[]) >>
    gvs[MEM_EL] >>
    `n'' < i` by (
      spose_not_then assume_tac >>
      `i <= n''` by decide_tac >>
      first_x_assum drule_all >>
      gvs[]
    ) >>
    qexists `n''` >>
    gvs[] >>
    irule $ GSYM EL_TAKE >>
    simp[]
  )
  \\ `~(mc_conf.target.get_pc ms2 IN mc_conf.prog_addresses) /\
      ~(mc_conf.target.get_pc ms2 = mc_conf.halt_pc) /\
      ~(mc_conf.target.get_pc ms2 = mc_conf.ccache_pc) /\
      (find_index (mc_conf.target.get_pc ms2) mc_conf.ffi_entry_pcs 0 =
         SOME (get_ffi_index mc_conf.ffi_names (ExtCall s))) /\
      get_ffi_index mc_conf.ffi_names (ExtCall s) = get_ffi_index
        ffi_names (ExtCall s)` by (
     full_simp_tac(srw_ss())[state_rel_def]>>
     first_x_assum $ qspecl_then [`ExtCall s`, `i`] old_drule >>
     gvs[] >>
     impl_keep_tac
     >- (irule ffi_name_NOT_Mapped >> fs[]) >>
     `get_ffi_index mc_conf.ffi_names (ExtCall s) = get_ffi_index
       ffi_names (ExtCall s)`
       suffices_by gvs[] >>
     gvs[get_ffi_index_def,backendPropsTheory.the_eqn] >>
     gvs[Abbr`ffi_names`] >>
     imp_res_tac find_index_MEM >>
     first_x_assum $ qspec_then `0` assume_tac >>fs[]>>
     fs[CaseEq"option"]>>irule OR_INTRO_THM2>>
     Cases_on ‘i ≤ LENGTH mc_conf.ffi_names’>>fs[]>-
      (
      old_drule LENGTH_TAKE>>strip_tac>>
      irule find_index_APPEND1>>fs[]>>
      qexists_tac `DROP i mc_conf.ffi_names` >>
      fs[TAKE_DROP])>>
     fs[NOT_LESS_EQUAL,TAKE_LENGTH_TOO_LONG])
*)

(* HOL4 ML code, not ported:
  \\ `EL (get_ffi_index mc_conf.ffi_names (ExtCall s)) mc_conf.ffi_names
    = (ExtCall s)` by (
    irule EL_get_ffi_index_MEM >> simp[]
  )
  \\ sg `(mc_conf.target.get_reg ms2 mc_conf.ptr_reg = t1.regs
    mc_conf.ptr_reg) /\
      (mc_conf.target.get_reg ms2 mc_conf.len_reg = t1.regs
        mc_conf.len_reg) /\
      (mc_conf.target.get_reg ms2 mc_conf.ptr2_reg = t1.regs
        mc_conf.ptr2_reg) /\
      (mc_conf.target.get_reg ms2 mc_conf.len2_reg = t1.regs
        mc_conf.len2_reg) /\
      !a. a IN mc_conf.prog_addresses ==>
          (mc_conf.target.get_byte ms2 a = t1.mem a)`
  >- (
    qpat_x_assum `!k. _` (strip_assume_tac o SPEC_ALL)
    \\ gvs[asmPropsTheory.target_state_rel_def,asm_def
      ,jump_to_offset_def,
           asmSemTheory.upd_pc_def]
    \\ unabbrev_all_tac \\
      full_simp_tac(srw_ss())[state_rel_def,asm_def,
         jump_to_offset_def,asmSemTheory.upd_pc_def,AND_IMP_INTRO]
    \\ rpt strip_tac \\ first_x_assum match_mp_tac
    \\ full_simp_tac(srw_ss())[reg_ok_def]
  )
  \\ full_simp_tac(srw_ss())[]
  \\ `(t1.regs mc_conf.ptr_reg = c') /\
      (t1.regs mc_conf.len_reg = c) /\
      (t1.regs mc_conf.ptr2_reg = c2') /\
      (t1.regs mc_conf.len2_reg = c2)` by
   (full_simp_tac(srw_ss())[state_rel_def]
    \\ Q.PAT_X_ASSUM `!r. word_loc_val p labs (s1.regs r) = SOME
      (t1.regs r)`
         (fn th =>
        MP_TAC (Q.SPEC `(mc_conf: ('a,'state,'b)
          machine_config).ptr_reg` th)
        \\ MP_TAC (Q.SPEC `(mc_conf: ('a,'state,'b)
          machine_config).len_reg` th)
        \\ MP_TAC (Q.SPEC `(mc_conf: ('a,'state,'b)
          machine_config).ptr2_reg` th)
        \\ MP_TAC (Q.SPEC `(mc_conf: ('a,'state,'b)
          machine_config).len2_reg` th))
    \\ Q.PAT_X_ASSUM `xx = s1.ptr_reg` (ASSUME_TAC o GSYM)
    \\ Q.PAT_X_ASSUM `xx = s1.len_reg` (ASSUME_TAC o GSYM)
    \\ Q.PAT_X_ASSUM `xx = s1.ptr2_reg` (ASSUME_TAC o GSYM)
    \\ Q.PAT_X_ASSUM `xx = s1.len2_reg` (ASSUME_TAC o GSYM)
    \\ full_simp_tac(srw_ss())[word_loc_val_def] \\ NO_TAC)
  \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac read_bytearray_state_rel \\ full_simp_tac(srw_ss())[]
  \\ reverse(Cases_on `call_FFI s1.ffi (ExtCall s) x x'`) THEN1
   ((* FFI_final *)
   FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock`mp_tac) \\ rpt strip_tac
   \\ fs[] \\ rveq \\ fs[]
   \\ Q.EXISTS_TAC `l'` \\ full_simp_tac(srw_ss())[ADD_ASSOC]
   \\ once_rewrite_tac [targetSemTheory.evaluate_def]
   \\ PURE_TOP_CASE_TAC >- (fs[shift_interfer_def])
   \\ simp[]
   \\ PURE_TOP_CASE_TAC >- (fs[shift_interfer_def])
   \\ simp[]
   \\ PURE_TOP_CASE_TAC >- (fs[shift_interfer_def])
   \\ simp[]
   \\ PURE_TOP_CASE_TAC >- (fs[shift_interfer_def])
   \\ simp[]
   \\ PURE_TOP_CASE_TAC >- (fs[shift_interfer_def])
   \\ simp[]
   >> ‘EL x'' (shift_interfer l' mc_conf).ffi_names = ExtCall s’
     by gvs[shift_interfer_def]>>
   first_assum (fn h => simp[h])
   \\ rpt (PURE_TOP_CASE_TAC \\ simp[])>>
   TRY
     (fs[shift_interfer_def,read_ffi_bytearrays_def
     ,read_ffi_bytearray_def]>>
        gvs[]>>NO_TAC)>>
*)

(* HOL4 ML code, not ported:
   fs[shift_interfer_def]>>
   fs[state_rel_def]>>
   old_drule mmio_pcs_min_index_is_SOME>>
   strip_tac>>fs[]>>
   last_x_assum $ qspec_then ‘x''’ assume_tac>>fs[]>>
   Cases_on ‘x'' < i’>>fs[NOT_LESS]>>
   old_drule find_index_LESS_LENGTH>>strip_tac>>fs[]>>
   first_x_assum $ qspec_then ‘x''’ assume_tac>>gvs[])
*)
  (* FFI_return *)
(* HOL4 ML code, not ported:
  \\ full_simp_tac(srw_ss())[]
  \\ qmatch_assum_rename_tac
       `call_FFI s1.ffi (ExtCall s) x x' = FFI_return new_ffi new_bytes`
  \\ FIRST_X_ASSUM (Q.SPECL_THEN [
       `shift_interfer l' mc_conf with
        ffi_interfer := shift_seq 1 mc_conf.ffi_interfer`,
       `code2`,`labs`,
       `t1 with <| pc := p + n2w (pos_val new_pc 0 (code2:'a sec list))
         ;
                   mem := asm_write_bytearray c2' new_bytes t1.mem ;
                   regs := \a. get_reg_value (s1.io_regs 0 (ExtCall s)
                     a) (t1.regs a) I ;
                   fp_regs := \n. s1.io_fp_regs 0 n |>`,
       `mc_conf.ffi_interfer 0 (get_ffi_index mc_conf.ffi_names (ExtCall
         s),new_bytes,ms2)`]mp_tac)
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (
    (conj_tac
      >- (
        sg `oracle_tie (shift_interfer l' mc_conf) ms2 s1`
        >- (
          irule oracle_tie_shift_interfer
          \\ qexists_tac `ms1`
          \\ conj_tac
          >- (gen_tac
              \\ qpat_x_assum `!k. _ /\ _ /\ _ /\ _` (qspec_then `k`
                strip_assume_tac)
              \\ first_assum ACCEPT_TAC)
          \\ first_assum ACCEPT_TAC
        )
        \\ `(shift_interfer l' mc_conf).ffi_interfer =
          mc_conf.ffi_interfer` by
             simp[shift_interfer_def]
        \\ sg `next_interference (shift_interfer l' mc_conf) s1.ffi ms2
          =
            SOME (FfiApp (get_ffi_index mc_conf.ffi_names (ExtCall s))
              new_bytes ms2
                    (mc_conf.ffi_interfer 0
                       (get_ffi_index mc_conf.ffi_names (ExtCall
                         s),new_bytes,ms2)),
                  shift_interfer l' mc_conf with
                    ffi_interfer := shift_seq 1 mc_conf.ffi_interfer,
                      new_ffi)`
        >- (
          qpat_x_assum `(shift_interfer l' mc_conf).ffi_interfer =
            mc_conf.ffi_interfer`
            (fn th => rewrite_tac[GSYM th])
          \\ irule next_interference_ExtCall
          \\ full_simp_tac(srw_ss())[shift_interfer_def,state_rel_def,
               read_ffi_bytearrays_def,read_ffi_bytearray_def]
          \\ rpt conj_tac
          >- (
            qpat_x_assum `mc_conf.target.get_pc ms2 = _` (fn th =>
              rewrite_tac[GSYM th])
            \\ first_assum ACCEPT_TAC
          )
          >- (
            qpat_x_assum `mc_conf.target.get_pc ms2 = _` (fn th =>
              rewrite_tac[GSYM th])
            \\ first_assum ACCEPT_TAC
          )
          >- (
            disj1_tac
            \\ qpat_x_assum `mc_conf.target.get_pc ms2 = _` (fn th =>
              rewrite_tac[GSYM th])
            \\ qpat_x_assum `mc_conf.prog_addresses = _` (fn th =>
              rewrite_tac[GSYM th])
            \\ first_assum ACCEPT_TAC
          )
          >- (
            qpat_x_assum `mc_conf.target.get_pc ms2 = _` (fn th =>
              rewrite_tac[GSYM th])
            \\ first_assum ACCEPT_TAC
          )
          >- (
            `get_ffi_index ffi_names (ExtCall s) < i` by
               (qpat_x_assum `get_ffi_index mc_conf.ffi_names _ = _`
                  (fn th => rewrite_tac[GSYM th])
                \\ irule ffi_name_NOT_Mapped
                \\ simp[]
                \\ first_assum ACCEPT_TAC)
            \\ qpat_x_assum `!index. if _ then _ else _`
                 (qspec_then `get_ffi_index ffi_names (ExtCall s)`
                   mp_tac)
            \\ rw[]
          )
          >- (
            qexists_tac `x` \\ qexists_tac `x'` \\ qexists_tac `s`
            \\ full_simp_tac(srw_ss())[]
            \\ rev_full_simp_tac(srw_ss())[]
          )
        )
        >- (
          irule oracle_tie_ffi_next
          \\ qpat_assum `next_interference (shift_interfer l' mc_conf) _
            _ = _`
               (irule_at Any)
          \\ simp[]
          \\ first_assum ACCEPT_TAC
        )
      )
     \\ rpt strip_tac
     THEN1
       (full_simp_tac(srw_ss())[encoder_correct_def,shift_interfer_def]
            \\ metis_tac [])
     >- (
       unabbrev_all_tac
       \\ imp_res_tac bytes_in_mem_asm_write_bytearray
       \\ full_simp_tac(srw_ss())[state_rel_def,shift_interfer_def,
              asm_def,jump_to_offset_def,
              asmSemTheory.upd_pc_def] \\ rev_full_simp_tac(srw_ss())[]
       \\ rewrite_tac [GSYM word_add_n2w,GSYM
         word_sub_def,WORD_SUB_PLUS,
             WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[get_pc_value_def]
       \\ full_simp_tac bool_ss [GSYM word_add_n2w,GSYM
         word_sub_def,WORD_SUB_PLUS,
             WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[get_pc_value_def]
       \\ `interference_ok (shift_seq l' mc_conf.next_interfer)
             (mc_conf.target.proj t1.mem_domain)` by
                (full_simp_tac(srw_ss())[interference_ok_def
                  ,shift_seq_def]
                 \\ NO_TAC) \\ full_simp_tac(srw_ss())[]
       \\ `p + n2w (pos_val new_pc 0 code2) = t1.regs s1.link_reg` by
        (Q.PAT_X_ASSUM `!r. word_loc_val p labs (s1.regs r) = SOME
          (t1.regs r)`
            (Q.SPEC_THEN `s1.link_reg`mp_tac)
         \\ full_simp_tac(srw_ss())[word_loc_val_def]
         \\ Cases_on `lab_lookup n1 n2 labs` \\
           full_simp_tac(srw_ss())[]
         \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ full_simp_tac(srw_ss())[]
         \\ res_tac \\ full_simp_tac(srw_ss())[]) \\
           full_simp_tac(srw_ss())[]
       \\ `w2n c2 = LENGTH new_bytes` by
        (imp_res_tac read_bytearray_LENGTH
         \\ imp_res_tac evaluatePropsTheory.call_FFI_LENGTH \\
           full_simp_tac(srw_ss())[])
       \\ qmatch_goalsub_abbrev_tac`mc_conf.ffi_interfer _ (index,_,_)`
       \\ `index < i` by (
         imp_res_tac mmio_pcs_min_index_is_SOME>>gvs[]>>
         simp[get_ffi_index_def,backendPropsTheory.the_eqn] >>
        imp_res_tac find_index_MEM >>
         first_x_assum $ qspec_then `0` assume_tac >>fs[]>>
         Cases_on ‘i' < i’>>fs[NOT_LESS]>>
         first_x_assum $ qspec_then `i'` assume_tac >>gvs[]
       )
       \\ `index < LENGTH mc_conf.ffi_names` by (
         old_drule mmio_pcs_min_index_is_SOME >> gvs[]
         )
       \\ qunabbrev_tac`index`
       \\ conj_tac >- (
         `read_ffi_bytearrays mc_conf ms2 = (SOME x, SOME x')` by
            full_simp_tac(srw_ss())[read_ffi_bytearrays_def
              ,read_ffi_bytearray_def]
         \\ qspecl_then [`mc_conf`,`ms1`,`s1`,`ms2`,`l'`,
                         `get_ffi_index (TAKE i mc_conf.ffi_names)
                           (ExtCall s)`,`s`,
                         `x`,`x'`,`new_ffi`,`new_bytes`,`t1`] mp_tac
              oracle_tie_ExtCall_residues
         \\ impl_tac
         >- (
           qpat_assum `mc_conf.target.get_pc ms2 = _` $ rewrite_tac o
             single
           \\ rpt conj_tac
           >- first_assum ACCEPT_TAC
           >- (gen_tac
               \\ qpat_x_assum `!k. _ /\ _ /\ _ /\ _` (qspec_then `k`
                 strip_assume_tac)
               \\ first_assum ACCEPT_TAC)
           >- (qpat_x_assum `mc_conf.prog_addresses = _` $ rewrite_tac o
             single
               \\ rewrite_tac[pred_setTheory.IN_DIFF]
               \\ qpat_x_assum `p + -n2w _ NOTIN t1.mem_domain` $
                 rewrite_tac o single)
           >- first_assum ACCEPT_TAC
           >- first_assum ACCEPT_TAC
           >- first_assum ACCEPT_TAC
           >- first_assum ACCEPT_TAC
           >- (qpat_x_assum `!index. if _ then _ else _`
                 (qspec_then `get_ffi_index (TAKE i mc_conf.ffi_names)
                   (ExtCall s)` mp_tac)
               \\ qpat_x_assum `get_ffi_index (TAKE i mc_conf.ffi_names)
                 (ExtCall s) < i` mp_tac
               \\ rw[])
           >- first_assum ACCEPT_TAC
           \\ first_assum ACCEPT_TAC
         )
         >- (
           strip_tac
           \\ pop_assum $ rewrite_tac o single
           \\ pop_assum $ rewrite_tac o single
           \\ qpat_x_assum `!ms2' k index new_bytes' t1' bytes' bytes2
             st new_st. _`
                (qspecl_then [`ms2`,`0`,
                              `get_ffi_index (TAKE i mc_conf.ffi_names)
                                (ExtCall s)`,
                              `new_bytes`,`t1`,`x`,`x'`,`s1.ffi`
                                ,`new_ffi`] mp_tac)
           \\ impl_tac
           >- (
             rpt conj_tac
             >- first_assum ACCEPT_TAC
             >- first_assum ACCEPT_TAC
             >- MATCH_ACCEPT_TAC relationTheory.RTC_REFL
             >- (qpat_x_assum `mc_conf.ffi_names❲_❳ = ExtCall s` $
               rewrite_tac o single
                 \\ first_assum ACCEPT_TAC)
             >- rewrite_tac[]
             >- (qpat_x_assum `!k. _ /\ _ /\ _ /\ _` (qspec_then `0`
               strip_assume_tac)
                 \\ first_assum ACCEPT_TAC)
             \\ `aligned mc_conf.target.config.code_alignment p` by
                  fs [alignmentTheory.aligned_bitwise_and]
             \\ qpat_x_assum `_ = t1.regs s1.link_reg` (fn th =>
               rewrite_tac [GSYM th])
             \\ simp [ONCE_REWRITE_RULE [WORD_ADD_COMM]
               alignmentTheory.aligned_add_sub]
             \\ old_drule all_enc_ok_aligned_pos_val \\ simp []
             \\ disch_then (qspec_then `new_pc` mp_tac)
             \\ impl_tac >- metis_tac[has_odd_inst_alignment]
             \\ rw[]
           )
           >- (
             qpat_x_assum `t1.regs s1.ptr2_reg = c2'` (fn th =>
               rewrite_tac[GSYM th])
             \\ qpat_x_assum `new_pc = x''` (fn th => rewrite_tac[GSYM
               th])
             \\ qpat_x_assum `p + n2w (pos_val new_pc 0 code2) = t1.regs
               s1.link_reg`
                  $ rewrite_tac o single
             \\ rewrite_tac[LET_THM]
             \\ BETA_TAC
             \\ disch_then ACCEPT_TAC
           )
         )
       )
       \\ conj_tac >- (
         rpt gen_tac \\ strip_tac
         \\ qpat_x_assum `!ms2'' k' index' new_bytes'' t1'' bytes''
           bytes2' st' new_st'. _`
              (qspecl_then
                [`ms2'`,`k+1`,`index`,`new_bytes'`,`t1'`,`bytes'`
                ,`bytes2`,
                            `st`,`new_st`] mp_tac)
         \\ impl_tac
         >- (
           rpt conj_tac
           >- first_assum ACCEPT_TAC
           >- first_assum ACCEPT_TAC
           >- (once_rewrite_tac[RTC_CASES1]
               \\ disj2_tac
               \\ qexists_tac `new_ffi`
               \\ conj_tac
               >- (rewrite_tac[evaluatePropsTheory.call_FFI_rel_def]
                   \\ goal_assum (first_assum o mp_then Any mp_tac))
               \\ first_assum ACCEPT_TAC)
           \\ first_assum ACCEPT_TAC
         )
         >- (
           rewrite_tac[shift_seq_def, LET_THM]
           \\ BETA_TAC
           \\ disch_then ACCEPT_TAC
         )
       )
       \\ conj_tac THEN1 metis_tac[]
       \\ conj_tac THEN1
        (Cases_on `s1.io_regs 0 (ExtCall s) r`
         \\ full_simp_tac(srw_ss())[get_reg_value_def,word_loc_val_def])
       \\ conj_tac THEN1
        (rpt strip_tac \\ qpat_x_assum `!a.
            byte_align a IN s1.mem_domain ==> bbb` (MP_TAC o Q.SPEC `a`)
         \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
         \\ match_mp_tac (SIMP_RULE std_ss [] (Q.INST [`x` |-> `x'`]
           CallFFI_bytearray_lemma))
         \\ full_simp_tac(srw_ss())[])
       \\ rw[]
       >- (
         match_mp_tac (MP_CANON (Q.INST [`x`|->`x'`]
           bytes_in_mem_asm_write_bytearray))
         \\ simp[] \\ fs[])
       >- (
         match_mp_tac (MP_CANON (Q.INST [`x`|->`x'`]
           bytes_in_mem_asm_write_bytearray))
         \\ simp[] \\ fs[])
       >- (
           fs[share_mem_state_rel_def] >>
           gvs[]>>
           rpt gen_tac>>strip_tac>>fs[]>>
           gvs[IMP_CONJ_THM,AND_IMP_INTRO,shift_seq_def] >>
           first_assum $ irule_at Any>>
           fs[]>>
           irule $ cj 2 RTC_RULES >>
           qexists `new_ffi` >>
           gvs[evaluatePropsTheory.call_FFI_rel_def] >>
           metis_tac[]
       )
       >- fs[share_mem_domain_code_rel_def]
     ))
  )
  \\ rpt strip_tac
  \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock + k`mp_tac) \\ rpt strip_tac
  \\ Q.EXISTS_TAC `k + l'` \\ full_simp_tac(srw_ss())[ADD_ASSOC]
  \\ Q.LIST_EXISTS_TAC [`ms2'`] \\ full_simp_tac(srw_ss())[]
  \\ fs[]
  \\ simp_tac std_ss [Once evaluate_def]
  \\ full_simp_tac(srw_ss())[shift_interfer_def]
  \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC,AC MULT_COMM
    MULT_ASSOC]
  \\ rev_full_simp_tac(srw_ss())[LET_DEF]
  \\ rewrite_tac[read_ffi_bytearrays_def, read_ffi_bytearray_def]
  \\ TOP_CASE_TAC>>fs[]
  \\ TRY (TOP_CASE_TAC>>fs[])
  \\ TRY (TOP_CASE_TAC>>fs[])
  >- (pairarg_tac>>fs[]>>
      irule EQ_TRANS>>
      first_x_assum $ irule_at (Pos last)>>
      simp[]>>
      fs[apply_oracle_def])>>
  qabbrev_tac ‘j = get_ffi_index ffi_names (ExtCall s)’>>
  fs[state_rel_def]>>
  old_drule mmio_pcs_min_index_is_SOME>>
  strip_tac>>fs[]>>
  last_x_assum $ qspec_then ‘j’ assume_tac>>fs[]>>
  Cases_on ‘j < i’>>fs[NOT_LESS]>>
  old_drule find_index_LESS_LENGTH>>strip_tac>>fs[]>>
  first_x_assum $ qspec_then ‘j’ assume_tac>>gvs[]
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Install]:
*)
(* Install *)
(* HOL4 ML code, not ported:
  say "Install" >>
  qpat_x_assum`_ =(res,s2)` mp_tac >>
  ntac 6 (TOP_CASE_TAC >> fs[])>>
  pairarg_tac \\ fs[] \\
  ntac 5 (TOP_CASE_TAC \\ fs[]) >>
  strip_tac >> rfs[]>>
  qabbrev_tac `ffi_names = TAKE (THE (mmio_pcs_min_index
    mc_conf.ffi_names)) mc_conf.ffi_names` >>
  mp_tac IMP_bytes_in_memory_Install>>
  fs[]>>impl_tac>-
    fs[state_rel_def]>>
  strip_tac>>
  pop_assum mp_tac >>
  qpat_abbrev_tac `jj = asm$Jump lll` \\ rpt strip_tac>>
  (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
       asm_step_IMP_evaluate_step_find_next) \\
         full_simp_tac(srw_ss())[]>>
  impl_tac>-
    (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF]
    \\ full_simp_tac(srw_ss())[asm_step_def,asm_def,LET_DEF]
    \\ imp_res_tac bytes_in_mem_IMP
    \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,
          asmSemTheory.upd_pc_def]
    \\ rev_full_simp_tac(srw_ss())[] \\ unabbrev_all_tac
    \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,
          asmSemTheory.upd_pc_def,asm_def]
    \\ fs[asm_fetch_def]
    \\ drule_all $ GEN_ALL IMP_bytes_in_memory
    \\ strip_tac
    \\ fs[]
    \\ drule_all $ GEN_ALL IMP_ffi_entry_pcs_disjoint_LabAsm
    \\ ho_match_mp_tac (
      PURE_REWRITE_RULE [satTheory.AND_IMP] o
      PURE_REWRITE_RULE [Once CONJ_SYM] $
      GEN_ALL ffi_entry_pcs_disjoint_LENGTH_shorter )
    \\ Cases_on `j`
    \\ gvs[line_similar_def,line_ok_def,line_length_def,line_bytes_def]
    \\ gvs[enc_with_nop_thm,LENGTH_APPEND] )>>
  strip_tac
  \\ `mc_conf.target.get_pc ms2 = mc_conf.ccache_pc` by
   (
    fs[Abbr`jj`,asm_def]>>
    fs[encoder_correct_def,target_ok_def,target_state_rel_def]>>
    fs[jump_to_offset_def,state_rel_def]>>
    metis_tac[GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
         WORD_ADD_SUB])
  \\ `~(mc_conf.target.get_pc ms2 IN t1.mem_domain)` by
    (fs[state_rel_def]>>rfs[])
  \\ `(t1.regs mc_conf.ptr_reg = c') /\
      (t1.regs mc_conf.len_reg = c'')` by
    (fs[state_rel_def]>>
    Q.PAT_X_ASSUM `!r. word_loc_val p labs (s1.regs r) = SOME (t1.regs
      r)`
         (fn th =>
        MP_TAC (Q.SPEC `(mc_conf: ('a,'state,'b)
          machine_config).ptr_reg` th)
        \\ MP_TAC (Q.SPEC `(mc_conf: ('a,'state,'b)
          machine_config).len_reg` th))
    \\ Q.PAT_X_ASSUM `xx = s1.ptr_reg` (ASSUME_TAC o GSYM)
    \\ Q.PAT_X_ASSUM `xx = s1.len_reg` (ASSUME_TAC o GSYM)
    \\ full_simp_tac(srw_ss())[word_loc_val_def])
  \\ rfs[]
  \\ qmatch_asmsub_abbrev_tac`evaluate mc_conf2 s1.ffi _ ms2`
  \\ qmatch_assum_rename_tac`s1.compile cfg _ = SOME (bytes,new_cfg)`
  \\ fs[asm_def,Abbr`jj`,jump_to_offset_def,upd_pc_def,FORALL_AND_THM]
  \\ sg `target_state_rel mc_conf.target
      (t1 with  <| regs := (s1.ptr_reg =+ t1.regs s1.ptr_reg)
                            (λa. get_reg_value (s1.cc_regs 0 a) (t1.regs
                              a) I);
                    fp_regs := (λn. s1.cc_fp_regs 0 n);
                    pc := t1.regs s1.link_reg |>)
      (mc_conf.ccache_interfer 0 (t1.regs s1.ptr_reg, t1.regs
        s1.len_reg, ms2))`
  >- (
    qspecl_then [`mc_conf`,`mc_conf2`,`ms1`,`s1`,`ms2`,`l''`,`t1`]
      mp_tac
       oracle_tie_ccache_residues
    \\ impl_tac
    >- (
      fs[Abbr`mc_conf2`,shift_interfer_def]
      \\ rpt conj_tac
      >- (disj1_tac \\ fs[state_rel_def])
      \\ fs[state_rel_def]
      \\ qpat_x_assum `p + -n2w (2 * ffi_offset) = _` (fn th =>
        rewrite_tac[GSYM th])
      \\ qpat_x_assum `p + -n2w ffi_offset = _` (fn th =>
        rewrite_tac[GSYM th])
      \\ rfs[good_dimindex_def,ffi_offset_def]
      \\ EVAL_TAC
      \\ simp[dimword_def]
    )
    >- (
      sg `mc_conf.target.get_reg ms2 mc_conf.ptr_reg = t1.regs
        s1.ptr_reg ∧
          mc_conf.target.get_reg ms2 mc_conf.len_reg = t1.regs
            s1.len_reg ∧
          mc_conf.ptr_reg = s1.ptr_reg`
      >- (
        fs[state_rel_def,asmPropsTheory.target_state_rel_def,reg_ok_def]
        \\ rfs[]
      )
      >- (
        qpat_x_assum `mc_conf.target.get_reg ms2 mc_conf.ptr_reg = _`
          $ rewrite_tac o single
        \\ qpat_x_assum `mc_conf.target.get_reg ms2 mc_conf.len_reg = _`
          $ rewrite_tac o single
        \\ qpat_x_assum `mc_conf.ptr_reg = s1.ptr_reg` $ rewrite_tac o
          single
        \\ strip_tac
        \\ pop_assum $ rewrite_tac o single
        \\ pop_assum $ rewrite_tac o single
        \\ `!(f:num -> 'a word).
              (λa. if MEM a mc_conf.callee_saved_regs ∨ a = s1.ptr_reg ∨
                      ¬(a < mc_conf.target.config.reg_count) ∨
                      MEM a mc_conf.target.config.avoid_regs
                   then t1.regs a else f a)⦇ s1.ptr_reg ↦ t1.regs
                     s1.ptr_reg ⦈ =
              (λa. if MEM a mc_conf.callee_saved_regs ∨ a = s1.ptr_reg ∨
                      ¬(a < mc_conf.target.config.reg_count) ∨
                      MEM a mc_conf.target.config.avoid_regs
                   then t1.regs a else f a)` by
             (gen_tac \\ simp[FUN_EQ_THM,APPLY_UPDATE_THM] \\ rw[])
        \\ pop_assum $ rewrite_tac o single
        \\ fs[state_rel_def]
        \\ first_x_assum irule
        \\ conj_tac
        >- (
          qpat_x_assum `∀r. word_loc_val p labs (read_reg r s1) = SOME
            (t1.regs r)`
                (qspec_then `s1.link_reg` mp_tac) \\ simp [] \\
                  strip_tac
          \\ rename [`word_loc_val p labs (Loc l1 l2) = SOME (t1.regs
            r1)`]
          \\ full_simp_tac(srw_ss())[word_loc_val_def]
          \\ Cases_on `lab_lookup l1 l2 labs` \\
            full_simp_tac(srw_ss())[]
          \\ first_x_assum (qspecl_then [`l1`,`l2`] mp_tac) \\ fs [] \\
            rw []
          \\ `aligned mc_conf.target.config.code_alignment p` by
                 fs [alignmentTheory.aligned_bitwise_and]
          \\ qpat_x_assum `_ = t1.regs r1` (fn th => rewrite_tac [GSYM
            th])
          \\ simp [ONCE_REWRITE_RULE [WORD_ADD_COMM]
            alignmentTheory.aligned_add_sub]
          \\ old_drule all_enc_ok_aligned_pos_val \\ simp []
          \\ disch_then match_mp_tac \\ fs []
          \\ metis_tac[has_odd_inst_alignment]
        )
        >- (
          sg `t1.pc + -n2w (2 * ffi_offset + pos_val s1.pc 0 code2) =
              p + -n2w (2 * ffi_offset)`
          >- (
            `t1.pc = p + n2w (pos_val s1.pc 0 code2)` by
              fs[state_rel_def]
            \\ pop_assum $ rewrite_tac o single
            \\ simp[GSYM word_add_n2w, WORD_NEG_ADD]
            \\ qpat_x_assum `p + -n2w (2 * ffi_offset) =
              mc_conf.ccache_pc`
                 (fn th => rewrite_tac[GSYM th])
            \\ CONV_TAC wordsLib.WORD_ARITH_CONV
            \\ rewrite_tac[WORD_ADD_RINV]
          )
          \\ pop_assum (fn th => rewrite_tac[GSYM th])
          \\ first_assum ACCEPT_TAC
        )
      )
    )
  )
  \\ qmatch_assum_abbrev_tac`target_state_rel _ t2 ms12`
  \\ qpat_assum`s1.compile _ _ = _`mp_tac
  \\ `s1.compile = compile_lab mc_conf.target.config` by
    fs[state_rel_def]
  \\ pop_assum SUBST1_TAC
  \\ simp[compile_lab_def]
  \\ pairarg_tac \\ simp[]
  \\ qmatch_assum_abbrev_tac`s1.compile cfg new_code = _`
  \\ TOP_CASE_TAC
  \\ split_pair_case_tac \\ fs[]
  \\ strip_tac
  \\ first_x_assum(qspecl_then
      [`mc_conf2 with ccache_interfer := shift_seq 1
        mc_conf.ccache_interfer`,
       `code2 ++ sec_list`,
       `new_cfg.labels`,`t2`,`ms12`]mp_tac)
  \\ impl_tac
  >- (
     conj_tac >- (
       sg `oracle_tie mc_conf2 ms2 s1`
       >- (
         qspecl_then [`mc_conf`,`mc_conf2`,`ms1`,`s1`,`ms2`,`l''`]
           mp_tac
           oracle_tie_shift_gen
         \\ impl_tac
         >- (rpt conj_tac
             >- first_assum ACCEPT_TAC
             >- first_assum ACCEPT_TAC
             \\ simp[Abbr`mc_conf2`,shift_interfer_def])
         \\ disch_then ACCEPT_TAC
       )
       \\ sg `next_interference mc_conf2 s1.ffi ms2 =
              SOME (CcApp (mc_conf2.target.get_reg ms2 mc_conf2.ptr_reg)
                          (mc_conf2.target.get_reg ms2 mc_conf2.len_reg)
                            ms2
                      (mc_conf2.ccache_interfer 0
                         (mc_conf2.target.get_reg ms2 mc_conf2.ptr_reg,
                          mc_conf2.target.get_reg ms2 mc_conf2.len_reg,
                            ms2)),
                    mc_conf2 with ccache_interfer := shift_seq 1
                      mc_conf2.ccache_interfer,
                    s1.ffi)`
       >- (
         irule next_interference_ccache
         \\ simp[Abbr`mc_conf2`,shift_interfer_def]
         \\ conj_tac
         >- (fs[state_rel_def]
             \\ qpat_x_assum `p + -n2w (2 * ffi_offset) = _`
                  (fn th => rewrite_tac[GSYM th])
             \\ qpat_x_assum `p + -n2w ffi_offset = _` (fn th =>
               rewrite_tac[GSYM th])
             \\ rfs[good_dimindex_def,ffi_offset_def]
             \\ EVAL_TAC
             \\ simp[dimword_def])
         \\ disj1_tac \\ fs[state_rel_def]
       )
       >- (
         `mc_conf2.ccache_interfer = mc_conf.ccache_interfer` by
            simp[Abbr`mc_conf2`,shift_interfer_def]
         \\ sg `mc_conf2.target.get_reg ms2 mc_conf2.ptr_reg = t1.regs
           s1.ptr_reg ∧
                mc_conf2.target.get_reg ms2 mc_conf2.len_reg = t1.regs
                  s1.len_reg`
         >- (
           simp[Abbr`mc_conf2`,shift_interfer_def]
           \\ fs[state_rel_def,asmPropsTheory.target_state_rel_def
             ,reg_ok_def]
           \\ rfs[]
         )
         >- (
           qpat_x_assum `next_interference mc_conf2 _ _ = _` mp_tac
           \\ qpat_x_assum `mc_conf2.target.get_reg ms2 mc_conf2.ptr_reg
             = _`
                $ rewrite_tac o single
           \\ qpat_x_assum `mc_conf2.target.get_reg ms2 mc_conf2.len_reg
             = _`
                $ rewrite_tac o single
           \\ qpat_x_assum `mc_conf2.ccache_interfer = _` $ rewrite_tac
             o single
           \\ strip_tac
           \\ simp[Abbr`ms12`]
           \\ irule oracle_tie_ccache_next
           \\ qpat_assum `next_interference mc_conf2 _ _ = _` (irule_at
             Any)
           \\ simp[]
           \\ first_assum ACCEPT_TAC
         )
       )
     )
     \\ fs[Abbr`mc_conf2`,shift_interfer_def,ELIM_UNCURRY]
     \\ pop_assum $ assume_tac o GSYM
     \\ fs[state_rel_def,Abbr`t2`,Abbr`ms12`]
     \\ reverse $ rfs[no_install_or_no_share_mem_def]
     >- (
       fs[no_install_def,asm_fetch_def] >>
       old_drule code_similar_IMP_asm_fetch_aux_line_similar >>
       disch_then $ qspec_then `s1.pc` assume_tac >>
       gvs[DefnBase.one_line_ify NONE line_similar_def,OPTREL_def] >>
       pop_assum mp_tac >>
       TOP_CASE_TAC >>
       strip_tac >>
       gvs[]) >>
     qpat_assum `_ ==> !k. _ (s1.compile_oracle k)`
       (drule_then $ qspec_then`0` mp_tac)>>
     qpat_assum`s1.compile_oracle 0 = _` SUBST1_TAC>>
     SIMP_TAC (srw_ss()) [] >>
     strip_tac>>
     old_drule remove_labels_thm >> impl_tac>-
       (fs[good_code_def]>>
       rw[]>>fs[]>>
       Cases_on`lab_lookup l1' l2 cfg.labels`>>
       fs[]>>
       metis_tac[])>>
    strip_tac >>
    fs[]>>rfs[] >>
    drule_all code_similar_IMP_both_no_share_mem >>
    strip_tac >>
    `no_share_mem_inst (code2 ++ sec_list)` by (
      irule no_share_mem_APPEND >>
      simp[]) >>
    simp[] >>
    `~(no_install (code2 ++ sec_list))` by (
      irule $ SRULE[Once $ DECIDE ``(B ==> A) <=> (~A ==> ~B)``] $
        cj 1 no_install_APPEND_IMP >>
      simp[no_install_def] >>
      rev_drule code_similar_IMP_asm_fetch_aux_line_similar >>
      disch_then $ qspec_then `s1.pc` (assume_tac o
        SRULE[DefnBase.one_line_ify NONE OPTREL_def,
          DefnBase.one_line_ify NONE line_similar_def]) >>
      gvs[asm_fetch_def] >>
      pop_assum mp_tac >>
      TOP_CASE_TAC >>
      strip_tac >>
      var_eq_tac >>
      metis_tac[])
    \\ conj_tac >- (
      fs[read_ffi_bytearrays_def, read_ffi_bytearray_def, shift_seq_def]
      \\ rw[] \\ first_x_assum irule
      \\ rw[] \\ asm_exists_tac \\ rw[]
      \\ fs[]
    )
    \\ conj_tac >- (
      fs[shift_seq_def]
    )
    \\ conj_tac
    >- (
      fs[shift_seq_def]
      \\ rw[]
      \\ pairarg_tac \\ fs[]
      \\ conj_tac
      >- (
        rpt(first_x_assum(qspec_then`k+1`mp_tac))
        \\ simp[] ) \\
      conj_tac
      >- (
        rpt(first_x_assum(qspec_then`k+1`mp_tac))
        \\ simp[] ) \\
      strip_tac \\
      rpt(first_x_assum(qspec_then`0` assume_tac))>>
      rfs[]>>
      fs[]>>
      simp[prog_to_bytes_MAP,no_share_mem_IMP_get_shmem_info]
    )
    \\ conj_tac >- (
      rw[]>>
      metis_tac[])
    \\ conj_tac >-(
      fs[find_ffi_names_append,list_subset_def]>>
      fs[EVERY_FILTER,EVERY_MEM])
    \\ conj_tac >- (
      fs[prog_to_bytes_APPEND,EVEN_ADD]>>
      metis_tac[all_enc_ok_prog_to_bytes_EVEN])
    \\ conj_tac >- ( fs[interference_ok_def,shift_seq_def] )
    \\ conj_asm2_tac >- (
      `EVERY sec_labels_ok (s1.code++new_code)` by
        (fs[good_code_def]>>
        metis_tac[code_similar_sym,code_similar_sec_labels_ok])>>
      `EVERY sec_label_zero sec_list` by
        metis_tac[all_enc_ok_imp_sec_label_zero]>>
      simp[loc_to_pc_append]>>
      ntac 3 strip_tac>>
      reverse (TOP_CASE_TAC >> fs[])
      >-
        (rw[]>> first_x_assum old_drule>>
        strip_tac>>
        first_x_assum old_drule>>
        simp[pos_val_append]>>
        rw[]>>
        metis_tac[code_similar_loc_to_pc,loc_to_pc_bound])
      >>
        TOP_CASE_TAC>>fs[]>>
        first_x_assum old_drule>>rw[]>>
        simp[pos_val_append]>>
        rw[]
        >-
          (imp_res_tac code_similar_len_no_lab>>
          fs[]>>
          `x''=0` by fs[]>>
          simp[]>>
          simp[pos_val_acc]>>
          imp_res_tac pos_val_0>>
          simp[]>>
          metis_tac[LENGTH_prog_to_bytes2])
        >>
          imp_res_tac code_similar_len_no_lab>>
          simp[]>>
          metis_tac[LENGTH_prog_to_bytes2])
    \\ conj_tac >- (
      rw[]
      \\ reverse(rw[APPLY_UPDATE_THM])
      \\ rfs[]
      >- (
        qmatch_goalsub_rename_tac`s1.cc_regs 0 reg`
        \\ Cases_on`s1.cc_regs 0 reg`
        >- (
          simp[get_reg_value_def]
          \\ first_assum(qspec_then`reg`(CHANGED_TAC o SUBST1_TAC o
            SYM))
          \\ Cases_on`read_reg reg s1` \\ simp[word_loc_val_def]
          \\ match_mp_tac EQ_SYM
          \\ TOP_CASE_TAC
          >- (
            rpt(first_x_assum(qspec_then`reg`mp_tac))
            \\ simp[word_loc_val_def] )
          \\ first_x_assum old_drule
          \\ simp[])
        \\ simp[get_reg_value_def]
        \\ simp[word_loc_val_def] )
      \\ simp[word_loc_val_def]
      \\ fs[Abbr`new_code`]
      \\ first_x_assum (qspecl_then [`n''`,`0`,`0`] mp_tac)
      \\ simp[Once loc_to_pc_def]
      \\ imp_res_tac pos_val_0
      \\ rw[]
      \\ qhdtm_x_assum`buffer_flush`mp_tac
      \\ simp[buffer_flush_def]
      \\ strip_tac
      \\ rfs[])
    \\ conj_tac >- (
      rw[]
      \\ res_tac
      \\ fs[word_loc_val_byte_def]
      \\ ntac 2 (pop_assum mp_tac)
      \\ TOP_CASE_TAC \\ simp[]
      \\ strip_tac
      \\ qmatch_asmsub_abbrev_tac`word_loc_val p labs w = _`
      \\ Cases_on`w` \\ fs[word_loc_val_def]
      \\ ntac 4 (pop_assum mp_tac)
      \\ TOP_CASE_TAC \\ simp[]
      \\ ntac 4 strip_tac
      \\ first_x_assum old_drule \\ simp[])
    \\ conj_tac >- (
      strip_tac \\
      qhdtm_x_assum`buffer_flush`mp_tac \\
      simp[buffer_flush_def] \\ ntac 2 strip_tac \\
      qpat_x_assum `∀n. n < _ ⇒ _`(qspec_then`n'''` mp_tac)>>
      rw[]>>rfs[] >> fs[GSYM word_add_n2w])
    \\ conj_tac >- (
      simp[prog_to_bytes_APPEND]
      \\ fs[bytes_in_mem_APPEND]
      \\ qhdtm_x_assum`buffer_flush`mp_tac
      \\ simp[buffer_flush_def]
      \\ rw[]
      \\ fs[])
    \\ conj_tac >- (
      simp[prog_to_bytes_APPEND]
      \\ fs[buffer_flush_def] \\ rw[]
      \\ qpat_x_assum`_ = t1.regs s1.len_reg` sym_sub_tac
      \\ simp[GSYM word_add_n2w])
    \\ conj_tac >- (
      fs[buffer_flush_def]>>rw[]>>
      simp[bytes_in_mem_def])
    \\ conj_tac >-
      (fs[buffer_flush_def] \\ rw[] >>
      fs[LENGTH_prog_to_bytes2,prog_to_bytes_APPEND])
    \\ conj_tac >- (
       gvs[buffer_flush_def] >>
       rw[] >>
       qpat_x_assum `!bn. bn < _ + _ ==> ~(MEM _ _)` $
         qspec_then `bn + LENGTH (prog_to_bytes sec_list)` mp_tac >>
       gvs[GSYM word_add_n2w] >>
       metis_tac[WORD_ADD_ASSOC]
    )
    \\ conj_tac>- (
      `EVERY sec_label_zero sec_list` by
        metis_tac[all_enc_ok_imp_sec_label_zero]>>
      qmatch_assum_rename_tac `loc_to_pc ll1 ll2 s1.code = SOME xx`>>
      rfs[]>>fs[]>>
      `pos_val xx 0 (code2 ++ sec_list) = pos_val xx 0 code2` by
        (simp[pos_val_append]>>
        metis_tac[loc_to_pc_bound,code_similar_sec_labels_ok
          ,code_similar_loc_to_pc])>>
      simp[]>>
      last_x_assum(qspecl_then[`ll1`,`ll2`,`xx`] assume_tac)>>
      last_x_assum(qspecl_then[`ll1`,`ll2`,`xx`] assume_tac)>>
      rfs[]>>
      fs[]>>
      qpat_x_assum`!r. word_loc_val _ _ _ = _` (qspec_then`s1.link_reg`
        assume_tac)>>
      rfs[word_loc_val_def])
    \\ conj_tac>-
      (match_mp_tac all_enc_ok_append>>
      rw[]>>fs[]>>
      match_mp_tac all_enc_ok_labs_mono
      >- metis_tac[] >>
      qexists `l1` >>
      gvs[asm_fetch_def] >>
      rev_drule code_similar_IMP_asm_fetch_aux_line_similar >>
      simp[OPTREL_def,DefnBase.one_line_ify NONE
        line_similar_def,AllCaseEqs()] >>
      disch_then $ qspec_then `s1.pc` assume_tac >>
      gvs[] >>
      first_x_assum mp_tac >>
      TOP_CASE_TAC >>
      strip_tac >>
      var_eq_tac >>
      old_drule $ GEN_ALL no_share_mem_lemma >>
      rpt strip_tac >>
      gvs[Abbr`ffi_names`] >>
      pop_assum old_drule >>
      impl_tac >-
      simp[no_install_or_no_share_mem_def] >>
      metis_tac[TAKE_LENGTH_ID] )
    \\ conj_tac>-
      (fs[good_code_def]>>
      metis_tac[code_similar_sec_labels_ok])
    \\ conj_tac >- metis_tac[code_similar_append]
    \\ conj_tac >-
      (gvs[share_mem_state_rel_def] >>
       share_mem_state_rel_tac)
    \\ gvs[share_mem_domain_code_rel_def] >>
       conj_tac >- gvs[no_share_mem_inst_def] >>
       rw[IN_DISJOINT] >>
       spose_not_then assume_tac >>
       gvs[asm_fetch_def] >>
       Cases_on `pc < num_pcs code2`
       >- (
         gvs[asm_fetch_aux_APPEND1,pos_val_APPEND1] >>
         first_x_assum drule_all >>
         gvs[IN_DISJOINT] >>
         metis_tac[]
       ) >>
       `?pc'. pc = num_pcs code2 + pc'` by (
         irule LESS_EQUAL_ADD >>
         decide_tac
       ) >>
       gvs[asm_fetch_aux_APPEND2] >>
       rev_drule_then (qspecl_then [`sec_list`,`pc'`] assume_tac)
         pos_val_APPEND2 >>
       gvs[] >>
       pop_assum kall_tac >>
       drule_then old_drule $ GEN_ALL no_share_mem_lemma >>
       impl_tac >- (
         irule code_similar_IMP_both_no_install_or_no_share_mem >>
         irule_at (Pos hd) code_similar_sym >>
         first_x_assum $ irule_at (Pos hd) >>
         simp[no_install_or_no_share_mem_def]) >>
       strip_tac >>
       gvs[buffer_flush_def] >>
       drule_all $ GEN_ALL asm_fetch_aux_pos_val_SUC >>
       disch_then $ qspec_then `0` assume_tac >>
       drule_then (qspecl_then [`pc'+1`,`0`] (assume_tac o
         SIMP_RULE(srw_ss())[]))
         pos_val_bound >>
       qpat_x_assum `!bn. bn < _ + _ ==> ~(MEM _ _)` mp_tac >>
       simp[] >>
       qexists `a + pos_val pc' 0 sec_list` >>
       simp[GSYM word_add_n2w] >>
       metis_tac[word_add_n2w,WORD_ADD_ASSOC,WORD_ADD_COMM]
  )
  >- (
    disch_then(qx_choose_then`k`strip_assume_tac)
    \\ qpat_x_assum `!k'. evaluate mc_conf _ _ _ = _`
         (qspec_then `s1.clock+k` assume_tac)
    \\ qmatch_asmsub_rename_tac`s1.clock + k + k0`
    \\ qexists_tac`k + k0` \\ fs[]
    \\ simp[Abbr`mc_conf2`,Abbr`ms12`]
    \\ simp[Once evaluate_def]
    \\ fs[shift_interfer_def]
    \\ IF_CASES_TAC >- (
      fs[state_rel_def]
    )
    \\ IF_CASES_TAC
    >- (
      fs[state_rel_def]
      \\ `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[]
      \\ rfs[good_dimindex_def,ffi_offset_def]
      \\ rpt(qpat_x_assum`_ = _.halt_pc`(mp_tac o SYM))
      \\ simp[]
      \\ EVAL_TAC
      \\ simp[dimword_def]
    )
    >- (
      rfs[apply_oracle_def,target_state_rel_def,state_rel_def
        ,reg_ok_def]
    )
  )
QED
*)

(* HOL4 ML code, not ported:
Resume compile_correct[Halt]:
*)
(* Halt *)
(* HOL4 ML code, not ported:
  say "Halt"
  \\ srw_tac[][]
  \\ qmatch_assum_rename_tac `asm_fetch s1 = SOME (LabAsm Halt l1 l2
    l3)`
  \\ qmatch_assum_rename_tac `asm_fetch s1 = SOME (LabAsm Halt l bytes
    n)`
  \\ qabbrev_tac `ffi_names = TAKE (THE (mmio_pcs_min_index
    mc_conf.ffi_names)) mc_conf.ffi_names`
  \\ mp_tac IMP_bytes_in_memory_Halt \\ full_simp_tac(srw_ss())[]
  \\ match_mp_tac IMP_IMP \\ strip_tac
  THEN1 (full_simp_tac(srw_ss())[state_rel_def]
         \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[])
  \\ rpt strip_tac \\ pop_assum mp_tac
  \\ qpat_abbrev_tac `jj = asm$Jump lll` \\ rpt strip_tac
  \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
       asm_step_IMP_evaluate_step_find_next) \\
         full_simp_tac(srw_ss())[]
  \\ MATCH_MP_TAC IMP_IMP2 \\ STRIP_TAC THEN1
   (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF]
    \\ full_simp_tac(srw_ss())[asm_step_def,asm_def,LET_DEF]
    \\ imp_res_tac bytes_in_mem_IMP
    \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,
          asmSemTheory.upd_pc_def]
    \\ rev_full_simp_tac(srw_ss())[] \\ unabbrev_all_tac
    \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,
          asmSemTheory.upd_pc_def,asm_def]
    \\ fs[asm_fetch_def]
    \\ drule_all $ GEN_ALL IMP_bytes_in_memory
    \\ strip_tac
    \\ fs[]
    \\ drule_all $ GEN_ALL IMP_ffi_entry_pcs_disjoint_LabAsm
    \\ ho_match_mp_tac (
      PURE_REWRITE_RULE [satTheory.AND_IMP] o
      PURE_REWRITE_RULE [Once CONJ_SYM] $
      GEN_ALL ffi_entry_pcs_disjoint_LENGTH_shorter )
    \\ Cases_on `j`
    \\ gvs[line_similar_def,line_ok_def,line_length_def,line_bytes_def]
    \\ gvs[enc_with_nop_thm,LENGTH_APPEND]
  )
  \\ rpt strip_tac
  \\ unabbrev_all_tac \\ full_simp_tac(srw_ss())[asm_def]
  \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock`mp_tac) \\ srw_tac[][]
  \\ Q.EXISTS_TAC `l'` \\ full_simp_tac(srw_ss())[]
  \\ once_rewrite_tac [evaluate_def] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[shift_interfer_def]
  \\ `mc_conf.target.get_pc ms2 = mc_conf.halt_pc` by
   (full_simp_tac(srw_ss())
      [encoder_correct_def,target_ok_def,target_state_rel_def]
    \\ res_tac
    \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[jump_to_offset_def
      ,asmSemTheory.upd_pc_def]
    \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
         WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[])
  \\ `~(mc_conf.target.get_pc ms2 IN t1.mem_domain)` by
          full_simp_tac(srw_ss())[state_rel_def]
  \\ full_simp_tac(srw_ss())[state_rel_def,jump_to_offset_def,
        asmSemTheory.upd_pc_def]
  \\ Cases_on `s1.regs s1.ptr_reg` \\ full_simp_tac(srw_ss())[]
  \\ `word_loc_val p labs (s1.regs s1.ptr_reg) =
       SOME (t1.regs s1.ptr_reg)` by full_simp_tac(srw_ss())[]
  \\ Cases_on `s1.regs s1.ptr_reg`
  \\ full_simp_tac(srw_ss())[word_loc_val_def] \\ srw_tac[][]
  \\ `s1 = s2` by (Cases_on `t1.regs s1.ptr_reg = 0w`
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]) \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())
       [encoder_correct_def,target_ok_def,target_state_rel_def]
  \\ first_x_assum (qspec_then `s1.ptr_reg` mp_tac)
  \\ first_x_assum (qspec_then `s1.ptr_reg` mp_tac)
  \\ full_simp_tac(srw_ss())[reg_ok_def]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
QED
*)

(* HOL4 ML code, not ported:
Finalise compile_correct;
*)

(* relating observable semantics *)

let init_ok_def = cake_define
  `init_ok (mc_conf,p) s ms <=>
     (?code2 labs t1.
       state_rel (mc_conf,code2,labs,p) s t1 ms /\
       oracle_tie mc_conf ms s)`;;

(*
val () = PolyML.SaveState.saveState "lab_to_target_syntactic";
val () = PolyML.SaveState.loadState "lab_to_target_syntactic";
*)

(* introducing make_init *)

let set_bytes_def = cake_define
  `(set_bytes a be [] = (n2w 0)) /\
   (set_bytes a be (b :: bs) = set_byte a b (set_bytes (a + (n2w
     1)) be bs) be)`;;

let make_word_def = cake_define
  `make_word be m (a:'a word) =
     (if dimindex (:'a) = 32 then
       Word (set_bytes a be [m a; m (a + (n2w 1)); m (a + (n2w 2)); m
         (a + (n2w 3))]) else
       Word (set_bytes a be [m a; m (a + (n2w 1)); m (a + (n2w 2)); m
         (a + (n2w 3));
                             m (a + (n2w 4)); m (a + (n2w 5)); m
                               (a + (n2w 6)); m (a + (n2w 7))]))`;;

let make_init_def = cake_define
  `lab_to_targetProof_make_init mc_conf (ffi:'ffi ffi_state) t m dm sdm
  (ms:'state) code
     comp' cbpos cbspace coracle =
     mk_? (\k. Word ((?_regs t k):'a word)) (?_fp_regs t) m dm sdm
       0 (asm_config_big_endian (target_config (machine_config_target
       mc_conf))) ffi (target_io_regs mc_conf ffi ms)
       (target_io_fp_regs mc_conf ffi ms) (target_cc_regs mc_conf ffi
       ms) (target_cc_fp_regs mc_conf ffi ms) code 0 F (?_ptr_reg
       mc_conf) (?_len_reg mc_conf) (?_ptr2_reg mc_conf) (?_len2_reg
       mc_conf) (match ?_link_reg (target_config
       (machine_config_target mc_conf)) with SOME n -> n | _67 -> 0)
       comp' (mk_buffer cbpos [] cbspace) coracle`;;
hol4_overload "make_init" "lab_to_targetProof_make_init";;

(* HOL4 ML code, not ported:
val IMP_LEMMA = METIS_PROVE [] ``(a ==> b) ==> (b ==> c) ==> (a ==> c)``
*)

let compiler_oracle_ok_def = cake_define
  `compiler_oracle_ok coracle init_labs init_pos c ffis <=>
     (!(k:num). let (cfg,code) = coracle k in good_code c
       (lab_to_target_config_labels cfg) code /\
       no_share_mem_inst code) /\
     (let (cfg,code) = coracle 0 in lab_to_target_config_labels
         cfg = init_labs /\ lab_to_target_config_pos
         cfg = init_pos /\ ?_ffi_names
         cfg = SOME ffis)`;;

(* mc_conf_ok: conditions on the machine configuration
   which will be discharged for the particular configuration of each
     target
*)
let mc_conf_ok_def = cake_define
  `mc_conf_ok (mc_conf:('a,'b,'c)machine_config) <=>
     good_dimindex (:'a) /\
     encoder_correct (machine_config_target mc_conf) /\
     reg_ok (?_ptr_reg mc_conf) (target_config (machine_config_target
       mc_conf)) /\
     reg_ok (?_len_reg mc_conf) (target_config (machine_config_target
       mc_conf)) /\
     reg_ok (?_ptr2_reg mc_conf) (target_config
       (machine_config_target mc_conf)) /\
     reg_ok (?_len2_reg mc_conf) (target_config
       (machine_config_target mc_conf)) /\
     reg_ok (match ?_link_reg (target_config (machine_config_target
       mc_conf)) with NONE -> 0 | SOME n -> n) (target_config
       (machine_config_target
       mc_conf)) /\
     enc_ok (target_config (machine_config_target mc_conf))`;;

let line_to_info_def = cake_define
  `line_to_info (secs:('a sec) list) p x = (match SND x with
     SOME (Asm (ShareMem m r ad) bytes l) ->
       (let (name,nb) = get_memop_info m in
       [(SharedMem name,
        mk_shmem_info_num (pos_val (FST x) p secs) nb (match ad
          with Addr r off -> r) (match ad with Addr r off -> w2n off)
          r (pos_val (FST x) p secs + LENGTH bytes))]) | _68 -> [])`;;

(* This is set up for the very first compile call *)

(* HOL4 ML code, not ported:
Resume IMP_state_rel_make_init[ISR1]:
  fs[Abbr ‘new_shmem_info’]>>
  fs[MAP_MAP_o,o_DEF]>>
  qmatch_goalsub_abbrev_tac ‘ZIP (l1,MAP ff _)’>>
  ‘LENGTH l1 = LENGTH (MAP ff shmem_info)’ by fs[Abbr
    ‘l1’,LENGTH_GENLIST]>>
  fs[ALOOKUP_ZIP_MAP_SND]>>
  `LENGTH shmem_info = LENGTH (DROP i (MAP w2n mc_conf.ffi_entry_pcs))`
    by (qpat_assum `MAP _ shmem_info = DROP _ _` (fn h => assume_tac
      (Q.AP_TERM `LENGTH` h))>>
        gvs[LENGTH_MAP,LENGTH_DROP])>>
  rw[Abbr ‘l1’]
  >- (‘shmem_info ≠ []’ by (strip_tac>>fs[])>>
      irule_at Any ALOOKUP_ALL_DISTINCT_MEM>>
      simp[MEM_ZIP,MAP_ZIP,ALL_DISTINCT_GENLIST,EL_GENLIST]>>
      qexists_tac ‘index - i’>>
      reverse conj_asm1_tac>-
        fs[EL_GENLIST]>>fs[LENGTH_MAP,LENGTH_DROP])>>
  rewrite_tac[ALOOKUP_FAILS]>>
  rpt strip_tac>>
  gvs[NOT_LESS,NOT_LESS_EQUAL,MEM_ZIP]
QED
*)

(* HOL4 ML code, not ported:
Resume IMP_state_rel_make_init[ISR2]:
  rpt strip_tac
  \\ irule (REWRITE_RULE [post_ffi_asm_def]
    ffi_interfer_ok_post_ffi_asm)
  \\ rpt conj_tac \\ fs[]
  >- (old_drule mmio_pcs_min_index_is_SOME \\ gvs[])
  >- (conj_tac
      >- (imp_res_tac evaluatePropsTheory.call_FFI_LENGTH \\ simp[])
      \\ strip_tac \\ gvs[call_FFI_def, AllCaseEqs()])
  \\ qexists_tac `mc_conf.target.get_pc ms`
  \\ simp[]
QED
*)

(* HOL4 ML code, not ported:
Resume IMP_state_rel_make_init[ISR3]:
  rpt strip_tac
  \\ irule (REWRITE_RULE [post_ccache_asm_def]
    ccache_interfer_ok_post_ccache_asm)
  \\ simp[]
  \\ qexists_tac `mc_conf.target.get_pc ms`
  \\ simp[]
QED
*)

(* HOL4 ML code, not ported:
Resume IMP_state_rel_make_init[ISR4]:
  ntac 2 strip_tac >>
  pairarg_tac >> fs[]>>
  drule_then assume_tac code_similar_sym >>
  drule_all_then assume_tac code_similar_IMP_both_no_share_mem >>
  fs[] >>
  qpat_x_assum`!k. _ (coracle k)`(qspec_then`k` assume_tac)>>rfs[]>>
  strip_tac>>fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume IMP_state_rel_make_init[ISR5]:
  metis_tac[EVEN,all_enc_ok_prog_to_bytes_EVEN]
QED
*)

(* HOL4 ML code, not ported:
Resume IMP_state_rel_make_init[ISR6]:
  metis_tac[list_subset_TAKE,list_subset_trans]
QED
*)

(* HOL4 ML code, not ported:
Resume IMP_state_rel_make_init[ISR7]:
  metis_tac[EVEN,all_enc_ok_prog_to_bytes_EVEN]
QED
*)

(* HOL4 ML code, not ported:
Resume IMP_state_rel_make_init[ISR8]:
  imp_res_tac mmio_pcs_min_index_is_SOME>>
  rpt strip_tac>>fs[]>>
  fs[get_ffi_index_def,backendPropsTheory.the_eqn]>>
  imp_res_tac find_index_MEM>>
  first_x_assum $ qspecl_then [‘0’] assume_tac>>gvs[]
QED
*)

(* HOL4 ML code, not ported:
Resume IMP_state_rel_make_init[ISR9]:
  simp[word_loc_val_byte_def,case_eq_thms]
  \\ metis_tac[SUBSET_DEF,word_loc_val_def]
QED
*)

(* HOL4 ML code, not ported:
Resume IMP_state_rel_make_init[ISR10]:
  metis_tac[word_add_n2w]
QED
*)

(* HOL4 ML code, not ported:
Resume IMP_state_rel_make_init[ISR11]:
  simp[bytes_in_mem_def]
QED
*)

(* HOL4 ML code, not ported:
Resume IMP_state_rel_make_init[ISR12]:
  rpt strip_tac >>
  `MAP (\rec. n2w rec.entry_pc) new_shmem_info = DROP i
    (mc_conf.ffi_entry_pcs : 'a word list)` by (
    qpat_x_assum `MAP _ new_shmem_info = DROP i (MAP w2n _)` (fn h =>
      mp_tac (AP_TERM ``MAP (n2w:num -> 'a word)`` h)) >>
    simp[MAP_MAP_o, o_DEF, n2w_w2n, MAP_DROP]) >>
  qpat_x_assum `!bn. bn < cbspace ==> _` $ imp_res_tac >>
  gvs[MEM_EL] >>
  drule_then assume_tac $ cj 1 mmio_pcs_min_index_is_SOME>>
  gvs[LENGTH_TAKE] >>
  first_x_assum $ qspec_then`n` assume_tac >>
  Cases_on `n < i`
  >- gvs[EL_TAKE] >>
  `i <= n` by decide_tac >>
  gvs[] >>
  old_drule get_shmem_info_thm >>
  disch_then $ qspecl_then [`0`,`[]`,`[]`] assume_tac >>
  gvs[UNZIP_MAP,MAP_GENLIST,combinTheory.o_DEF,ZIP_MAP_FST_SND_EQ
    ,MAP_MAP_o,
    Abbr`new_shmem_info`,EL_MAP] >>
  qspecl_then [`n - i`, `i`,`mc_conf.ffi_entry_pcs`]
    assume_tac $ GSYM EL_DROP >>
  gvs[] >>
  pop_assum kall_tac >>
  qpat_x_assum `_ = DROP i mc_conf.ffi_entry_pcs` $ assume_tac o GSYM >>
  fs[GSYM word_add_n2w]>>
  qmatch_assum_abbrev_tac `DROP i mc_conf.ffi_entry_pcs = MAP
    offset_func flatten_genlist` >>
  gvs[] >>
  `n - i < LENGTH (MAP offset_func flatten_genlist)` by (
    qpat_x_assum `DROP i mc_conf.ffi_entry_pcs = _` $ assume_tac o GSYM
      >>
    asm_rewrite_tac[LENGTH_DROP] >>
    simp[]
  ) >>
  gvs[EL_MAP,Abbr`offset_func`] >>
  drule_all genlist_line_to_info_entry_pc_max >>
  strip_tac >>
  drule_then (qspec_then `n-i` assume_tac) $ iffLR EVERY_EL >>
  gvs[Abbr`flatten_genlist`] >>
  qmatch_asmsub_abbrev_tac `entry_pc' < pos_val _ _ _` >>
  drule_then (fn t =>
    gvs[t,addressTheory.word_arith_lemma1]) $
    GEN_ALL pos_val_num_pcs
QED
*)

(* HOL4 ML code, not ported:
Resume IMP_state_rel_make_init[ISR13]:
  drule pos_val_0 \\ simp[]
QED
*)

(* HOL4 ML code, not ported:
Resume IMP_state_rel_make_init[ISR14]:
  metis_tac[code_similar_sec_labels_ok]
QED
*)

(* HOL4 ML code, not ported:
Resume IMP_state_rel_make_init[ISR15]:
  fs[ffi_interfer_ok_def]
  \\ gvs[share_mem_state_rel_def]
  \\ rpt strip_tac
  \\ gvs[IMP_CONJ_THM, AND_IMP_INTRO]
  \\ first_x_assum $ qspecl_then [`ms2`, `k`, `index`, `new_bytes`,
    `t1`, `B`, `C`] mp_tac
  \\ gvs[] >> strip_tac>>fs[]>>
  old_drule mmio_pcs_min_index_is_SOME>>
  strip_tac>>fs[]>>
  first_x_assum $ qspec_then ‘index’ assume_tac>>gvs[]>>
  TOP_CASE_TAC>>fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume IMP_state_rel_make_init[ISR16]:
  simp[share_mem_domain_code_rel_def]
  \\ fs[MAP_MAP_o,o_DEF,ELIM_UNCURRY]
  \\ old_drule $ GEN_ALL get_shmem_info_ok_lemma
  \\ disch_then $ qspecl_then [
      `w2n (mc_conf.target.get_pc
        ms)`,`new_shmem_info`,`mc_conf.ffi_names`,
      `TAKE i mc_conf.ffi_names`] mp_tac
  \\ gvs[]
  \\ impl_tac
  >- (
    old_drule mmio_pcs_min_index_is_SOME >>
    strip_tac >>
    reverse $ rw[EVERY_EL]
   >- (
      qpat_abbrev_tac `info = get_shmem_info _ _ _ _` >>
      first_x_assum $ assume_tac o GSYM o
        ONCE_REWRITE_RULE[markerTheory.Abbrev_def] >>
      Cases_on `info` >>
      old_drule $ GEN_ALL get_shmem_info_PREPEND >>
      gvs[] >>
      strip_tac >>
      old_drule $ GEN_ALL get_shmem_info_init_pc_offset >>
      disch_then $ qspec_then `w2n (mc_conf.target.get_pc ms)` mp_tac >>
      strip_tac >>
      gvs[markerTheory.Abbrev_def] >>
      metis_tac[TAKE_DROP] ) >>
    first_x_assum $ mp_tac o GSYM >>
    spose_not_then assume_tac >>fs[]>>
    qpat_x_assum`∀s. EL _ (TAKE i mc_conf.ffi_names) ≠ _` $ mp_tac >>
    fs[EL_TAKE]
  )
  \\ rw[]
  >- (
    qpat_x_assum `!pc op re a inst len. asm_fetch_aux _ _ = _ ==> ?i._`
      $ imp_res_tac
    \\ qexists `index + i`
    \\ old_drule find_index_LESS_LENGTH
    \\ fs[GSYM word_add_n2w]
    \\ `LENGTH (MAP (\rec. (n2w rec.entry_pc):'a word) new_shmem_info) =
        LENGTH mc_conf.ffi_entry_pcs - i`
          by (qpat_x_assum `MAP _ new_shmem_info = DROP _ _` (fn h =>
                assume_tac (Q.AP_TERM `LENGTH` h)) >>
              gvs[LENGTH_MAP,LENGTH_DROP])
    \\ fs[LENGTH_MAP,LESS_SUB_ADD_LESS,EL_MAP,LENGTH_TAKE]
    \\ strip_tac
    \\ `find_index (n2w (pos_val pc 0 code2) + mc_conf.target.get_pc ms)
          (DROP i mc_conf.ffi_entry_pcs) 0 = SOME index` by (
      ONCE_REWRITE_TAC[GSYM find_index_MAP_w2n] >>
      simp[MAP_DROP] >>
      `w2n (mc_conf.target.get_pc ms) + pos_val pc 0 code2 <
        dimword(:'a)` by (
        drule find_index_is_MEM >> strip_tac >>
        imp_res_tac MEM_DROP_IMP >>
        fs[MEM_MAP] >> metis_tac[w2n_lt]) >>
      ONCE_REWRITE_TAC[GSYM n2w_w2n |> Q.ISPEC `mc_conf.target.get_pc
        ms`] >>
      rewrite_tac[word_add_n2w, w2n_n2w] >>
      `pos_val pc 0 code2 < dimword(:'a)` by fs[] >>
      simp[] >>
      ONCE_REWRITE_TAC[ADD_COMM] >>
      first_x_assum ACCEPT_TAC)
    \\ old_drule find_index_shift >> fs[]
    \\ disch_then $ qspec_then `i` assume_tac
    \\ `~MEM (n2w (pos_val pc 0 code2) + mc_conf.target.get_pc ms)
          (TAKE i mc_conf.ffi_entry_pcs)` by (
      `LENGTH (prog_to_bytes code2) < dimword(:'a)` by gvs[] >>
      old_drule $ GEN_ALL asm_fetch_NOT_ffi_entry_pcs >>
      rpt $ disch_then $ drule_at Any >>
      disch_then $ qspec_then `0` mp_tac >>
      simp[line_bytes_def, line_length_def] >>
      impl_tac >- (
        old_drule $ GEN_ALL enc_ok_LENGTH_GT_0 >>
        drule_all $ GEN_ALL all_enc_ok_asm_fetch_aux_IMP_line_ok >>
        gvs[line_ok_def,line_length_def,enc_with_nop_thm] >>
        rpt strip_tac >> gvs[] >>
        first_x_assum $ qspec_then `Inst (Mem op re a)` assume_tac >>
          gvs[]) >>
      metis_tac[WORD_ADD_COMM, WORD_ADD_ASSOC])
    \\ `find_index (n2w (pos_val pc 0 code2) + mc_conf.target.get_pc ms)
          (TAKE i mc_conf.ffi_entry_pcs) 0 = NONE` by
      fs[GSYM find_index_NOT_MEM]
    \\ qspecl_then [
        `TAKE i (mc_conf: ('a,'state,'b) machine_config).ffi_entry_pcs`,
        `DROP i (mc_conf: ('a,'state,'b) machine_config).ffi_entry_pcs`,
        `n2w (pos_val pc 0 code2) + (mc_conf.target.get_pc ms: 'a
          word)`,
        `0`] assume_tac find_index_APPEND
    \\ gvs[AllCaseEqs()]
    \\ gvs[ELIM_UNCURRY,shmem_info_num_component_equality]>>
    irule ALOOKUP_ALL_DISTINCT_MEM>>
    qmatch_goalsub_abbrev_tac `ZIP (l1, l2)`>>
    `LENGTH l1 = LENGTH l2` by
      (unabbrev_all_tac>>fs[LENGTH_GENLIST,LENGTH_MAP])>>
    fs[MAP_ZIP,MEM_ZIP]>>unabbrev_all_tac>>fs[]>>
    fs[ALL_DISTINCT_GENLIST]>>fs[MAP_MAP_o,o_DEF]>>gvs[]>>simp[EL_MAP]>>
    qexists_tac `index`>>fs[EL_MAP]>>
    fs[EL_GENLIST]>>
    Cases_on `a` >> simp[n2w_w2n] >>
    rewrite_tac[GSYM word_add_n2w] >> simp[n2w_w2n])
  >- (
    qpat_x_assum `!pc line. asm_fetch_aux _ _ = _ /\ _ ==> _`
      imp_res_tac
    \\ simp[IN_DISJOINT] >> rpt strip_tac >> spose_not_then assume_tac
      >> gvs[]
    \\ `LENGTH (prog_to_bytes code2) < dimword(:'a)` by gvs[]
*)
    (* TAKE case: asm_fetch_NOT_ffi_entry_pcs *)
(* HOL4 ML code, not ported:
    \\ `~MEM (mc_conf.target.get_pc ms + n2w a + n2w (pos_val pc 0
      code2))
         (TAKE i mc_conf.ffi_entry_pcs)` by (
      irule asm_fetch_NOT_ffi_entry_pcs >> gvs[] >> metis_tac[])
*)
    (* Get MEM in DROP via TAKE_DROP *)
(* HOL4 ML code, not ported:
    \\ `MEM (mc_conf.target.get_pc ms + n2w a + n2w (pos_val pc 0
      code2))
         (DROP i mc_conf.ffi_entry_pcs)` by (
      ONCE_REWRITE_TAC[WORD_ADD_COMM] >>
      qpat_x_assum `MEM _ _` mp_tac >>
      `mc_conf.ffi_entry_pcs = TAKE i mc_conf.ffi_entry_pcs ++ DROP i
        mc_conf.ffi_entry_pcs`
        by simp[TAKE_DROP] >>
      pop_assum (fn h => ONCE_REWRITE_TAC[h]) >>
      rewrite_tac[MEM_APPEND] >> strip_tac >> gvs[])
*)
    (* Get w2n version in DROP *)
(* HOL4 ML code, not ported:
    \\ `MEM (w2n (mc_conf.target.get_pc ms + n2w a + n2w (pos_val pc 0
      code2)))
         (DROP i (MAP w2n mc_conf.ffi_entry_pcs))` by (
      rewrite_tac[GSYM MAP_DROP] >>
      irule MEM_MAP_f >> first_x_assum ACCEPT_TAC)
*)
    (* w2n x >= w2n(get_pc ms) from new_shmem_info structure *)
(* HOL4 ML code, not ported:
    \\ `w2n (mc_conf.target.get_pc ms) <=
       w2n (mc_conf.target.get_pc ms + n2w a + n2w (pos_val pc 0
         code2))` by (
      qpat_x_assum `MEM _ (DROP i (MAP w2n _))` mp_tac >>
      qpat_x_assum `MAP _ new_shmem_info = DROP i _` (SUBST1_TAC o GSYM)
        >>
      qpat_x_assum `Abbrev (new_shmem_info = _)` mp_tac >>
      simp[markerTheory.Abbrev_def] >> strip_tac >>
      ASM_REWRITE_TAC[] >>
      simp[MAP_MAP_o, o_DEF, MEM_MAP] >>
      strip_tac >> simp[])
*)
    (* a + pos_val < LENGTH prog *)
(* HOL4 ML code, not ported:
    \\ `a + pos_val pc 0 code2 < LENGTH (prog_to_bytes code2)` by (
      imp_res_tac asm_fetch_aux_pos_val_SUC >>
      pop_assum $ qspec_then `0` assume_tac >>
      old_drule pos_val_bound >>
      disch_then $ qspecl_then [`pc+1`,`0`] assume_tac >>
      gvs[])
*)
    (* Apply DISJOINT to get contradiction *)
(* HOL4 ML code, not ported:
    \\ qpat_x_assum `DISJOINT _ _` (mp_tac o REWRITE_RULE[DISJOINT_ALT])
    \\ disch_then $ qspec_then `w2n (mc_conf.target.get_pc ms + n2w a +
      n2w (pos_val pc 0 code2))` mp_tac
    \\ impl_tac >- (
      rewrite_tac[GSYM MAP_DROP] >>
      irule MEM_MAP_f >> first_x_assum ACCEPT_TAC)
    \\ strip_tac >> pop_assum mp_tac >> simp[]
    \\ qexists_tac `a` >> simp[]
*)
    (* Prove w2n equality: w2n(n2w a + n2w(pos_val) + get_pc ms) = a +
       (w2n(pc) + pos_val) *)
(* HOL4 ML code, not ported:
    \\ ONCE_REWRITE_TAC[WORD_ADD_COMM] >> rewrite_tac[word_add_n2w]
    \\ `a + pos_val pc 0 code2 < dimword(:'a)` by fs[]
    \\ DEP_REWRITE_TAC[w2n_add_2] >> simp[w2n_n2w]
*)
    (* Show no overflow: a + pos_val + w2n(pc) < dimword *)
(* HOL4 ML code, not ported:
    \\ spose_not_then assume_tac >> gvs[NOT_LESS]
    \\ qpat_x_assum `w2n _ <= _` mp_tac >> simp[NOT_LESS_EQUAL]
    \\ ONCE_REWRITE_TAC[WORD_ADD_COMM] >> rewrite_tac[word_add_n2w]
    \\ simp[word_add_def, w2n_n2w]
    \\ `w2n (mc_conf.target.get_pc ms) < dimword(:'a)` by simp[w2n_lt]
    \\ `a + (w2n (mc_conf.target.get_pc ms) + pos_val pc 0 code2) < 2 *
      dimword(:'a)` by fs[]
    \\ `(a + (w2n (mc_conf.target.get_pc ms) + pos_val pc 0 code2)) MOD
      dimword(:'a) =
       a + (w2n (mc_conf.target.get_pc ms) + pos_val pc 0 code2) -
         dimword(:'a)` by (
      `0 < dimword(:'a)` by simp[] >>
      drule_all SUB_MOD >> strip_tac >>
      `a + (w2n (mc_conf.target.get_pc ms) + pos_val pc 0 code2) -
        dimword(:'a) < dimword(:'a)` by fs[] >>
      imp_res_tac LESS_MOD >> fs[])
    \\ simp[] >> fs[])
QED
*)

(* HOL4 ML code, not ported:
Resume IMP_state_rel_make_init[ISR17]:
  drule_then (drule_then irule) $ GEN_ALL
    code_similar_IMP_both_no_install_or_no_share_mem
QED
*)

(* HOL4 ML code, not ported:
Finalise IMP_state_rel_make_init;
*)

(* TODO: move *)
(*
Theorem no_share_mem_inst_APPEND_IMP:
  no_share_mem_inst (l ++ sec_list) ==>
  no_share_mem_inst l /\ no_share_mem_inst sec_list
Proof
  simp[no_share_mem_inst_def] >>
  rw[] >>
  spose_not_then assume_tac >>
  last_x_assum mp_tac >>
  simp[] >>
  irule_at (Pos hd) EQ_TRANS >>
  first_assum $ irule_at (Pos last) >>
  irule_at (Pos hd) EQ_TRANS
  >- (
    irule_at (Pos last) asm_fetch_aux_APPEND1 >>
    old_drule asm_fetch_SOME_IMP_LESS_num_pcs >>
    metis_tac[]
  ) >>
  irule_at (Pos last) asm_fetch_aux_APPEND2 >>
  metis_tac[]
QED
*)
(*
Theorem no_share_mem_inst_EVERY:
  no_share_mem_inst sec_list =
  EVERY (
    (EVERY (\x. !op re a inst len.
       x <> (Asm (ShareMem op re a)) inst len)) o
    Section_lines) sec_list
Proof
  Induct_on `sec_list`
  >- (
    fs[no_share_mem_inst_def] >>
    simp[DefnBase.one_line_ify NONE asm_fetch_aux_def]) >>
  rw[] >>
  eq_tac
  >- (
    strip_tac >>
    pop_assum $ assume_tac o
      PURE_REWRITE_RULE[Once $
        Q.prove (`(x::y) = [x] ++ y`,simp[])] >>
    reverse conj_tac
    >- (
      old_drule no_share_mem_inst_APPEND_IMP >>
      simp[]) >>
    dxrule $ cj 1 no_share_mem_inst_APPEND_IMP >>
    pop_assum kall_tac >>
    simp[no_share_mem_inst_def] >>
    simp[DefnBase.one_line_ify NONE labLangTheory.Section_lines_def] >>
    TOP_CASE_TAC >>
    strip_tac >>
    spose_not_then assume_tac >>
    last_x_assum mp_tac >>
    fs[NOT_EVERY,o_DEF,EXISTS_MEM] >>
    simp[Once $ DefnBase.one_line_ify NONE asm_fetch_aux_def] >>
    TOP_CASE_TAC >>
    gvs[is_Label_def]
    >- (qexists `0` >>simp[]) >>
    TOP_CASE_TAC >>
    old_drule asm_fetch_aux_MEM >>
    simp[is_Label_def] >>
    strip_tac >>
    irule_at (Pos hd) EQ_TRANS >>
    first_assum $ irule_at (Pos last)
    >- metis_tac[] >>
    qexists `p + 1` >> simp[]
  ) >>
  rw[] >>
  PURE_REWRITE_TAC[Once $ Q.prove(`(x::y) = [x] ++ y`,simp[])] >>
  irule no_share_mem_APPEND >>
  reverse conj_tac >- metis_tac[] >>
  pop_assum kall_tac >>
  last_x_assum kall_tac >>
  first_x_assum mp_tac >>
  fs[DefnBase.one_line_ify NONE labLangTheory.Section_lines_def] >>
  TOP_CASE_TAC >>
  rw[no_share_mem_inst_def] >>
  spose_not_then assume_tac >>
  last_x_assum mp_tac >>
  simp[o_DEF,EXISTS_MEM] >>
  pop_assum mp_tac >>
  qid_spec_tac `p` >>
  Induct_on `l`
  >- simp[asm_fetch_aux_def] >>
  rw[] >>
  pop_assum mp_tac >>
  simp[asm_fetch_aux_def] >>
  TOP_CASE_TAC
  >- (
    strip_tac >>
    gvs[] >>
    metis_tac[]
  ) >>
  TOP_CASE_TAC >>
  metis_tac[]
QED

*)

(*
Theorem compile_lab_ffi_names_SOME:
  compile_lab c sec_list = SOME (bytes,c') /\
  c.ffi_names = SOME ffis /\
  EVERY (\x. x <> "MappedRead" /\ x <> "MappedWrite") ffis ==>
  ?ffi_names. c'.ffi_names = SOME ffi_names /\
  mmio_pcs_min_index ffi_names = SOME $ LENGTH ffis
Proof
  simp[compile_lab_def] >>
  pairarg_tac >>
  fs[] >>
  pop_assum $ mp_tac o SRULE[AllCaseEqs()] >>
  rpt TOP_CASE_TAC >>
  pairarg_tac >>
  rw[] >>
  gvs[] >>
  pop_assum mp_tac >>
  simp[GSYM FILTER_EQ_ID] >>
  disch_then assume_tac >>
  first_assum (fn thm => CONV_TAC (LHS_CONV $ REWRITE_CONV[Once $ GSYM
    thm])) >>
  first_assum (fn thm => CONV_TAC (RHS_CONV $ REWRITE_CONV[Once $ GSYM
    thm])) >>
  irule FILTER_mmio_pcs_min_index >>
  old_drule get_shmem_info_MappedRead_or_MappedWrite >>
  simp[]
QED

Theorem compile_lab_no_share_mem_ffi_names_SOME:
  compile_lab c sec_list = SOME (bytes,c') /\
  no_share_mem_inst sec_list /\
  c.ffi_names = SOME ffi_names /\
  (EVERY $ \x. x <> "MappedRead" /\ x <> "MappedWrite") ffi_names ==>
  c'.ffi_names = SOME ffi_names /\
  mmio_pcs_min_index ffi_names = SOME $ LENGTH ffi_names
Proof
  strip_tac >>
  drule_all_then assume_tac compile_lab_ffi_names_SOME >>
  fs[] >>
  conj_asm1_tac >- (
    rpt (pop_assum mp_tac) >>
    simp[compile_lab_def] >>
    pairarg_tac >>
    fs[] >>
    pop_assum $ mp_tac o SRULE[AllCaseEqs()] >>
    rpt TOP_CASE_TAC >>
    pairarg_tac >>
    rw[] >>
    gvs[remove_labels_def] >>
    drule_then assume_tac remove_labels_loop_no_share_mem_inst >>
    pop_assum mp_tac >>
    impl_tac
    >- drule_then irule enc_sec_list_no_share_mem_inst >>
    strip_tac >>
    drule_all no_share_mem_IMP_get_shmem_info >>
    strip_tac >>
    gvs[]) >>
  metis_tac[]
QED
*)

(* try to show the condition of semantics_compile is not vacuous *)
(* prove that mmio_min_min_index actually exists,
  and LENGTH ffi_names = LENGTH ffi_entry_pcs,
  which are stated in start_pc_ok
Theorem get_shmem_info_FST_eq:
!q p names info p' info'.
  FST (get_shmem_info q p names info) = FST (get_shmem_info q p' names
    info')
Proof
  ho_match_mp_tac get_shmem_info_ind >>
  rpt strip_tac >>
  gvs[get_shmem_info_def] >>
  pairarg_tac >>
  gvs[get_shmem_info_def]
QED

Theorem get_shmem_info_FST_SND_LENGTH_eq:
!q p names info.
  LENGTH (FST (get_shmem_info q p names info)) + LENGTH info =
  LENGTH (SND (get_shmem_info q p names info)) + LENGTH names
Proof
  ho_match_mp_tac get_shmem_info_ind >>
  rpt strip_tac >>
  gvs[get_shmem_info_def] >>
  pairarg_tac >>
  gvs[get_shmem_info_def]
QED
*)
(*
Theorem start_pc_ok_not_vacuous_lemma:
  LENGTH  <= LENGTH mc_conf.ffi_entry_pcs /\
  compile c (code: 'a sec list) = SOME (bytes,c') ∧
  c'.ffi_names = SOME mc_conf.ffi_names /\
  MAP (\rec. rec.entry_pc + mc_conf.target.get_pc ms) c'.shmem_extra =
    DROP (LENGTH old_ffi_names) mc_conf.ffi_entry_pcs /\
  (!ffis. c.ffi_names = SOME ffis ==>
    ~MEM "MappedRead" ffis /\ ~MEM "MappedWrite" ffis )
  ==>
  ?i. mmio_pcs_min_index mc_conf.ffi_names = SOME i /\
  LENGTH mc_conf.ffi_names = LENGTH mc_conf.ffi_entry_pcs
Proof
  fs[compile_def,compile_lab_def]>>
  pairarg_tac \\ fs[] >>
  CASE_TAC>>fs[]>>
  CASE_TAC>>fs[]>>
  rw[]>>
  `compile =  (λc p. compile_lab c (filter_skip p)) ` by
    fs[FUN_EQ_THM,compile_def]>>
  pop_assum SUBST_ALL_TAC>>
  fs[find_ffi_names_filter_skip,GSYM PULL_EXISTS,MAP_MAP_o,o_DEF]>>
  SIMP_TAC (bool_ss) [Once WORD_ADD_COMM]>>
  qabbrev_tac `info=get_shmem_info q 0 [] []` >>
  first_x_assum $ assume_tac o GSYM o
    ONCE_REWRITE_RULE[markerTheory.Abbrev_def] >>
  Cases_on `info` >>
  gvs[] >>
  `FST(get_shmem_info q c.pos [] []) = FST(get_shmem_info q 0 [] [])`
    by metis_tac[get_shmem_info_FST_eq] >>
  simp[] >>
  conj_tac >- (
    qexists_tac `LENGTH ffis` >>
    irule mmio_pcs_min_index_APPEND_thm >>
    gvs[] >>
    drule_then assume_tac get_shmem_info_MappedRead_or_MappedWrite >>
    gvs[] >>
    Cases_on `c.ffi_names` >>
    gvs[FILTER_NOT_MEM_Mapped]
  ) >>
  qspecl_then [`q`,`c.pos`,`[]`,`[]`] assume_tac
    get_shmem_info_FST_SND_LENGTH_eq >>
  gvs[] >>
  qpat_x_assum `MAP _ _ = DROP _ _` $
    assume_tac o Q.AP_TERM `LENGTH` >>
  gvs[LENGTH_MAP,LENGTH_DROP]
QED
*)
