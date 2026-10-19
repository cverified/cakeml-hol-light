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
needs "compiler/backend/lab_filter.ml";;
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
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/semantics.ml";;

cake_hide ["contain"; "invariant"; "not"];;

cake_hide_consts
  ["failed","pegexec_failed"];;

(* HOL4 lab_to_targetProofScript.sml:16: ML code, not ported *)

let evaluate_ignore_clocks =
  cake_theorem "evaluate_ignore_clocks[local]"
  (fun () ->
    `evaluate mc_conf ffi k ms = (r1,ms1,st1) /\ ~(r1 = TimeOut) /\
       evaluate mc_conf ffi k' ms = (r2,ms2,st2) /\ ~(r2 = TimeOut)
         ==>
       (r1,ms1,st1) = (r2,ms2,st2)`)
  CHEAT_TAC;;

let sec_loc_to_pc_def = cake_define
  `(sec_loc_to_pc n2 xs =
    (if n2 = 0 then SOME 0 else match xs with [] -> NONE | (z :: zs)
      ->
      (if (?n1 k. z = labLang_Label n1 n2 k) then SOME 0 else if
        is_Label z then sec_loc_to_pc n2 zs else OPTION_MAP SUC
        (sec_loc_to_pc n2 zs))))`;;

(* HOL4 lab_to_targetProofScript.sml:39: ML code, not ported *)

let sec_loc_to_pc_cons = cake_theorem "sec_loc_to_pc_cons"
  (fun () ->
    `sec_loc_to_pc n2 (l :: lines) =
     (if n2 = 0 \/ (?n1 k. l = labLang_Label n1 n2 k) then SOME 0
       else OPTION_MAP (if is_Label l then I else SUC) (sec_loc_to_pc
       n2 lines))`)
  CHEAT_TAC;;

(* HOL4 lab_to_targetProofScript.sml:49: the overload len_no_lab,
   which the port expands *)

let loc_to_pc_thm = cake_theorem "loc_to_pc_thm"
  (fun () ->
    `!n1 n2 ls.
       EVERY sec_labels_ok ls ==>
       loc_to_pc n1 n2 ls =
         (match ls with [] -> NONE | (Section k xs :: ys) ->
           (if n1 = k then
             match sec_loc_to_pc n2 xs with NONE -> OPTION_MAP
               ((+) (LENGTH (FILTER ((~) o is_Label) xs))) (loc_to_pc
               n1 n2 ys) | x -> x else OPTION_MAP ((+) (LENGTH (FILTER
               ((~) o is_Label) xs))) (loc_to_pc n1 n2 ys)))`)
  CHEAT_TAC;;

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

let enc_with_nop_thm = cake_theorem "enc_with_nop_thm[local]"
  (fun () ->
    `enc_with_nop enc (b:'a asm) bytes =
         (?n. bytes = enc b ++ FLAT (REPLICATE n (enc (asm_Inst
           asm_Skip))))`)
  CHEAT_TAC;;

let asm_step_nop_def = cake_define
  `asm_step_nop bytes c s1 i s2 <=>
     bytes_in_memory (asm_state_pc s1) bytes (asm_state_mem s1)
       (asm_state_mem_domain s1) /\
     enc_with_nop (asm_config_encode c) i bytes /\
     (match link_reg c with NONE -> T | SOME r -> asm_state_lr s1 =
       r) /\
     (asm_state_be s1 <=> asm_config_big_endian c) /\ asm_state_align
       s1 = asm_config_code_alignment c /\
     asmSem_asm i (asm_state_pc s1 + n2w (LENGTH bytes)) s1 = s2 /\
       ~(failed s2) /\
     asm_ok i c`;;

(* HOL4 lab_to_targetProofScript.sml:125-130: ML code, not ported *)

let shift_interfer_0 = cake_theorem "shift_interfer_0[local]"
  (fun () ->
    `shift_interfer 0 = I`)
  CHEAT_TAC;;

let upd_pc_with_pc = cake_theorem "upd_pc_with_pc[local]"
  (fun () ->
    `upd_pc (asm_state_pc s1) s1 = (s1:'a asm_state)`)
  CHEAT_TAC;;

let shift_interfer_twice = cake_theorem "shift_interfer_twice[simp]"
  (fun () ->
    `shift_interfer l' (shift_interfer l c) =
      shift_interfer (l + l') c`)
  CHEAT_TAC;;

let evaluate_nop_steps = cake_theorem "evaluate_nop_steps[local]"
  (fun () ->
    `!n s1 ms1 c.
         encoder_correct (machine_config_target c) /\
           machine_config_prog_addresses
         c = asm_state_mem_domain s1 /\
         ffi_entry_pcs_disjoint c s1
           (n * LENGTH (asm_config_encode (target_config
             (machine_config_target c)) (Inst asm_Skip))) /\
         interference_ok (machine_config_next_interfer c)
           (target_proj (machine_config_target c) (asm_state_mem_domain
           s1)) /\
         bytes_in_memory (asm_state_pc s1)
           (FLAT (REPLICATE n (asm_config_encode (target_config
             (machine_config_target c)) (Inst asm_Skip))))
             (asm_state_mem s1) (asm_state_mem_domain
           s1) /\
         (match link_reg (target_config (machine_config_target c))
           with NONE -> T | SOME r -> asm_state_lr s1 = r) /\
         (asm_state_be s1 <=> asm_config_big_endian (target_config
           (machine_config_target c))) /\ asm_state_align
         s1 = asm_config_code_alignment (target_config
           (machine_config_target c)) /\ ~(asm_state_failed s1) /\
         target_state_rel (machine_config_target c) (s1:'a
           asm_state) (ms1:'state) ==>
         (?l ms2.
           !k.
             (evaluate c io (k + l) ms1 =
              evaluate (shift_interfer l c) io k ms2) /\
             (find_next_interference c io (k + l) ms1 =
              find_next_interference (shift_interfer l c) io k ms2)
                /\
             target_state_rel (machine_config_target c)
               (upd_pc
                 (asm_state_pc s1 +
                  n2w (n * LENGTH (asm_config_encode (target_config
                    (machine_config_target c)) (Inst asm_Skip)))) s1)
               ms2)`)
  CHEAT_TAC;;

let ffi_entry_pcs_disjoint_LENGTH_shorter =
  cake_theorem "ffi_entry_pcs_disjoint_LENGTH_shorter"
  (fun () ->
    `!l1 l2.
       ffi_entry_pcs_disjoint c s1 l1 /\
       l2 <= l1 ==>
       ffi_entry_pcs_disjoint c s1 l2`)
  CHEAT_TAC;;

let asm_step_IMP_evaluate_step_nop =
  cake_theorem "asm_step_IMP_evaluate_step_nop"
  (fun () ->
    `!c s1 ms1 io i s2 bytes.
        encoder_correct (machine_config_target c) /\
          machine_config_prog_addresses
        c = asm_state_mem_domain s1 /\
        ffi_entry_pcs_disjoint c s1 (LENGTH bytes) /\
        interference_ok (machine_config_next_interfer c)
          (target_proj (machine_config_target c) (asm_state_mem_domain
          s1)) /\
        bytes_in_memory (asm_state_pc s1) bytes (mem s2)
          (asm_state_mem_domain s1) /\
        asm_step_nop bytes (target_config (machine_config_target
          c)) s1 i s2 /\
        s2 = asmSem_asm i (asm_state_pc s1 + n2w (LENGTH bytes)) s1
          /\
        target_state_rel (machine_config_target c) (s1:'a
          asm_state) (ms1:'state) /\
        (!x. ~(i = Call x)) ==>
        (?l ms2.
          !k.
            (evaluate c io (k + l) ms1 =
             evaluate (shift_interfer l c) io k ms2) /\
            (find_next_interference c io (k + l) ms1 =
             find_next_interference (shift_interfer l c) io k ms2)
               /\
            target_state_rel (machine_config_target c) s2 ms2 /\
              ~(l = 0))`)
  CHEAT_TAC;;

(* define relation between labSem and targetSem states *)

let lab_lookup_def = cake_define
  `lab_lookup k1 k2 labs =
     (match sptree_lookup k1 labs with NONE -> NONE | SOME f ->
       sptree_lookup k2 f)`;;

let lab_lookup_IMP = cake_theorem "lab_lookup_IMP[local]"
  (fun () ->
    `(lab_lookup l1 l2 labs = SOME x) ==>
       (find_pos (labLang_Lab l1 l2) labs = x)`)
  CHEAT_TAC;;

let labs_domain_def = cake_define
  `labs_domain labs = {(n1,n2) | ~(lab_lookup n1 n2 labs = NONE)}`;;

let labs_domain_LN = cake_theorem "labs_domain_LN[simp]"
  (fun () ->
    `labs_domain LN = {}`)
  CHEAT_TAC;;

let labs_domain_insert = cake_theorem "labs_domain_insert"
  (fun () ->
    `~(k IN domain labs) ==>
        labs_domain (sptree_insert k s labs) = IMAGE (\n2.
          (k,n2)) (domain s) UNION labs_domain labs`)
  CHEAT_TAC;;


(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let has_odd_inst_def = cake_define_list_cheat CHEAT_TAC
  [`has_odd_inst [] = F`;
   `has_odd_inst (Section k [] :: xs) = has_odd_inst xs`;
   `has_odd_inst (Section k (y :: ys) :: xs) <=>
         ~(EVEN (line_length y)) \/ has_odd_inst ((Section k
           ys) :: xs)`];;

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

let line_similar_sym = cake_theorem "line_similar_sym"
  (fun () ->
    `line_similar l1 l2 ==> line_similar l2 l1`)
  CHEAT_TAC;;

let code_similar_sym = cake_theorem "code_similar_sym"
  (fun () ->
    `!code1 code2. code_similar code1 code2 ==> code_similar code2
  code1`)
  CHEAT_TAC;;

let line_similar_refl = cake_theorem "line_similar_refl[simp]"
  (fun () ->
    `!l. line_similar l l`)
  CHEAT_TAC;;

let code_similar_refl = cake_theorem "code_similar_refl[simp]"
  (fun () ->
    `!code. code_similar code code`)
  CHEAT_TAC;;

let line_similar_trans = cake_theorem "line_similar_trans[local]"
  (fun () ->
    `line_similar x y /\ line_similar y z ==> line_similar x z`)
  CHEAT_TAC;;

let code_similar_trans = cake_theorem "code_similar_trans"
  (fun () ->
    `!c1 c2 c3. code_similar c1 c2 /\ code_similar c2 c3 ==>
  code_similar c1 c3`)
  CHEAT_TAC;;

let code_similar_nil = cake_theorem "code_similar_nil"
  (fun () ->
    `(code_similar [] l <=> l = []) /\
     (code_similar l [] <=> l = [])`)
  CHEAT_TAC;;

let code_similar_append = cake_theorem "code_similar_append"
  (fun () ->
    `!l1 l2 r1 r2.
       code_similar l1 l2 /\
       code_similar r1 r2 ==>
       code_similar (l1 ++ r1) (l2 ++ r2)`)
  CHEAT_TAC;;

let line_similar_sec_label_ok = cake_theorem "line_similar_sec_label_ok"
  (fun () ->
    `!l1 l2.
     EVERY (sec_label_ok s) l1 /\
     LIST_REL line_similar l1 l2 ==>
     EVERY (sec_label_ok s) l2`)
  CHEAT_TAC;;

let code_similar_sec_labels_ok =
  cake_theorem "code_similar_sec_labels_ok"
  (fun () ->
    `!c1 c2.
     EVERY sec_labels_ok c1 /\
     code_similar c1 c2 ==>
     EVERY sec_labels_ok c2`)
  CHEAT_TAC;;

let line_similar_len_no_lab = cake_theorem "line_similar_len_no_lab"
  (fun () ->
    `!l1 l2.
     LIST_REL line_similar l1 l2 ==>
     (\xs. LENGTH (FILTER ((~) o is_Label) xs)) l1 = (\xs. LENGTH
       (FILTER ((~) o is_Label) xs)) l2`)
  CHEAT_TAC;;

let code_similar_len_no_lab = cake_theorem "code_similar_len_no_lab"
  (fun () ->
    `!(c1:('a sec) list) (c2:('a sec) list).
     code_similar c1 c2 ==>
     MAP ((\xs. LENGTH (FILTER ((~) o is_Label) xs)) o
       Section_lines) c1 =
     MAP ((\xs. LENGTH (FILTER ((~) o is_Label) xs)) o
       Section_lines) c2`)
  CHEAT_TAC;;

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
        // Call not yet supported
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

let all_enc_ok_cons = cake_theorem "all_enc_ok_cons"
  (fun () ->
    `!ls pos.
     all_enc_ok c labs ffis pos (Section k ls :: xs) <=>
     all_enc_ok c labs ffis (pos + SUM (MAP line_length ls)) xs /\
     EVEN (pos + SUM (MAP line_length ls)) /\
     lines_ok c labs ffis pos ls`)
  CHEAT_TAC;;

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

let pos_val_0 = cake_theorem "pos_val_0"
  (fun () ->
    `!xs c enc labs ffis pos.
        all_enc_ok c labs ffis pos xs ==> (pos_val 0 pos xs =
          pos)`)
  CHEAT_TAC;;

let sec_pos_val_def = cake_define_list
  [`sec_pos_val i pos [] = NONE`;
   `sec_pos_val i pos (y :: ys) =
       (if is_Label y then
         sec_pos_val i (pos + line_length y) ys else if i = 0
           then SOME pos else sec_pos_val (i - 1) (pos +
           line_length y) ys)`];;

let sec_pos_val_too_big = cake_theorem "sec_pos_val_too_big"
  (fun () ->
    `!i pos lines.
      LENGTH (FILTER ((~) o is_Label) lines) <= i ==> sec_pos_val
        i pos lines = NONE`)
  CHEAT_TAC;;

let EVERY_is_Label_sec_pos_val =
  cake_theorem "EVERY_is_Label_sec_pos_val"
  (fun () ->
    `!n pos lines. EVERY is_Label lines ==> sec_pos_val n pos lines =
  NONE`)
  CHEAT_TAC;;

let pos_val_thm0 = cake_theorem "pos_val_thm0[local]"
  (fun () ->
    `!i pos acc.
       pos_val i pos acc =
         (match acc with [] -> pos | Section k s :: ss ->
           (match sec_pos_val i pos s with NONE ->
           pos_val (i - LENGTH (FILTER ((~) o is_Label) s)) (pos
             + SUM (MAP line_length s)) ss | SOME x -> x))`)
  CHEAT_TAC;;

let pos_val_thm = cake_theorem "pos_val_thm"
  (fun () ->
    `(pos_val i pos [] = pos) /\
     (pos_val i pos (Section k s :: ss) =
      (match sec_pos_val i pos s with NONE ->
        pos_val (i - LENGTH (FILTER ((~) o is_Label) s)) (pos +
          SUM (MAP line_length s)) ss | SOME x -> x))`)
  CHEAT_TAC;;

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
     (
      // whenever the pc is accessing share mem, the pc is in ffi_entry_pcs
      // * after mmio_pcs_min_index and the mmio_info for it is correct
      !pc' op re a inst' len i.
         (asm_fetch_aux pc' code2 = SOME (labLang_Asm (ShareMem op re
           a) inst' len) /\
         mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME
           i) ==>
         (?index.
           i <= index /\
           find_index (p + n2w (pos_val pc' 0 code2))
             (machine_config_ffi_entry_pcs mc_conf) 0 =
             SOME index /\
           (let (name,nb) = get_memop_info op in
             EL index (machine_config_ffi_names mc_conf) =
               ffi_SharedMem name /\
             (
              ALOOKUP (machine_config_mmio_info mc_conf) index = SOME
                (nb,a,re,p + n2w (pos_val pc' 0 code2 + len)))))) /\
     (
      // if the bytes of the instruction intersect with the ffi_entry_pcs,
      // * it must be fetching ShareMem instruction
      !pc' line.
       asm_fetch_aux pc' code2 = SOME line /\
       (!op re a inst' len. ~(line = labLang_Asm (ShareMem op re a)
         inst' len)) ==>
       DISJOINT (set_of_list (machine_config_ffi_entry_pcs mc_conf))
         {p + n2w a + n2w (pos_val pc' 0 code2) |
           a < LENGTH (line_bytes line)}) /\
      (
       // restriction for shared memory domain
       !a.
         byte_align a IN s1_shared_mem_domain ==>
         a IN s1_shared_mem_domain) /\
      (machine_config_shared_addresses mc_conf =
        s1_shared_mem_domain)`;;

let share_mem_state_rel_def = cake_define
  `share_mem_state_rel mc_conf
  (s1:('a,lab_to_target_config,'ffi)labSem_state) t1 ms1 <=>
      (
       // ffi interfers for mapped read/write are ok
       !ms2 k index new_bytes t1 nb ad offs re pc' ad' st new_st i.
       mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i
         /\
       i <= index /\ index < LENGTH (machine_config_ffi_names
         mc_conf) /\ RTC
       call_FFI_rel (labSem_state_ffi s1) st /\
       ALOOKUP (machine_config_mmio_info mc_conf) index = SOME
         (nb,Addr ad offs,re,pc') /\
       (machine_config_prog_addresses mc_conf = asm_state_mem_domain
         t1) /\
       ad' = target_get_reg (machine_config_target mc_conf) ms2 ad +
         offs /\
       // eval the address value
       target_state_rel (machine_config_target mc_conf)
         (asm_state_pc_fupd (K (EL index
           (machine_config_ffi_entry_pcs mc_conf))) t1) ms2 ==>
       (?op. EL index (machine_config_ffi_names mc_conf) =
         ffi_SharedMem op /\
          (match op with MappedRead ->
          ((
            // If we are doing mapped read, and addresses are fine
            if nb = (n2w 0) then (w2n ad' MOD (dimindex (:'a) DIV 8))
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
             (asm_state_regs_fupd (K (\n. if n = re then
                    (word_of_bytes F (n2w 0) new_bytes) else
                      asm_state_regs t1 n)) (asm_state_pc_fupd (K pc')
                      t1))
               (machine_config_ffi_interfer mc_conf k
                 (index,new_bytes,ms2))) | MappedWrite ->
          ((
            // If we are doing mapped write, and the addresses are fine
            if nb = (n2w 0) then (w2n ad' MOD (dimindex (:'a) DIV 8))
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
             (asm_state_pc_fupd (K pc') t1)
             (machine_config_ffi_interfer mc_conf k
               (index,new_bytes,ms2)))))) /\
    (
     // requirements for location of share memory access pcs
     !index i. mmio_pcs_min_index (machine_config_ffi_names mc_conf)
       = SOME i /\
       index < LENGTH (machine_config_ffi_names mc_conf) /\ i <=
         index ==> ~(machine_config_halt_pc
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
     s1 = target_io_regs mc_conf (labSem_state_ffi s1) ms /\
       labSem_state_io_fp_regs
     s1 = target_io_fp_regs mc_conf (labSem_state_ffi s1) ms /\
       labSem_state_cc_regs
     s1 = target_cc_regs mc_conf (labSem_state_ffi s1) ms /\
       labSem_state_cc_fp_regs
     s1 = target_cc_fp_regs mc_conf (labSem_state_ffi s1) ms`;;

let oracle_tie_shift_interfer = cake_theorem "oracle_tie_shift_interfer"
  (fun () ->
    `oracle_tie mc_conf ms1 s1 /\
     (!k. find_next_interference mc_conf (labSem_state_ffi s1) (k +
       l) ms1 =
          find_next_interference (shift_interfer l mc_conf)
            (labSem_state_ffi s1) k ms2) ==>
     oracle_tie (shift_interfer l mc_conf) ms2 s1`)
  CHEAT_TAC;;

let oracle_tie_step = cake_theorem "oracle_tie_step"
  (fun () ->
    `oracle_tie mc_conf ms1 (s1:('a,'c,'ffi)labSem_state) /\
     (!k. find_next_interference mc_conf (labSem_state_ffi s1) (k +
       l) ms1 =
          find_next_interference (shift_interfer l mc_conf)
            (labSem_state_ffi s1) k ms2) /\ labSem_state_io_regs
     (s2:('a,'c,'ffi)labSem_state) = labSem_state_io_regs s1 /\
       labSem_state_io_fp_regs
     s2 = labSem_state_io_fp_regs s1 /\ labSem_state_cc_regs
     s2 = labSem_state_cc_regs s1 /\ labSem_state_cc_fp_regs s2 =
       labSem_state_cc_fp_regs s1 /\ labSem_state_ffi
     s2 = labSem_state_ffi s1 ==>
     oracle_tie (shift_interfer l mc_conf) ms2 s2`)
  CHEAT_TAC;;

let oracle_tie_ffi_step = cake_theorem "oracle_tie_ffi_step"
  (fun () ->
    `oracle_tie mc_conf ms1 s1 /\
     next_interference mc_conf (labSem_state_ffi s1) ms1 =
       SOME (FfiApp index new_bytes ms_pre ms_post,mc',ffi') ==>
     (!name r. labSem_state_io_regs
        s1 0 name r =
          (if MEM r (machine_config_callee_saved_regs mc_conf) \/
             ~(r < asm_config_reg_count (target_config
               (machine_config_target mc_conf))) \/
             MEM r (asm_config_avoid_regs (target_config
               (machine_config_target mc_conf))) then NONE else SOME
               (target_get_reg (machine_config_target mc_conf) ms_post
               r))) /\
     (!i. labSem_state_io_fp_regs s1 0 i = target_get_fp_reg
       (machine_config_target mc_conf) ms_post i) /\
     target_io_regs mc' ffi' ms_post = misc_shift_seq 1
       (labSem_state_io_regs s1) /\
     target_io_fp_regs mc' ffi' ms_post = misc_shift_seq 1
       (labSem_state_io_fp_regs s1) /\
     target_cc_regs mc' ffi' ms_post = labSem_state_cc_regs s1 /\
     target_cc_fp_regs mc' ffi' ms_post = labSem_state_cc_fp_regs
       s1`)
  CHEAT_TAC;;

let oracle_tie_ccache_step = cake_theorem "oracle_tie_ccache_step"
  (fun () ->
    `oracle_tie mc_conf ms1 s1 /\
     next_interference mc_conf (labSem_state_ffi s1) ms1 =
       SOME (CcApp a1 a2 ms_pre ms_post,mc',ffi') ==>
     (!r. labSem_state_cc_regs
        s1 0 r =
          (if MEM r (machine_config_callee_saved_regs mc_conf) \/ r
            = machine_config_ptr_reg mc_conf \/
             ~(r < asm_config_reg_count (target_config
               (machine_config_target mc_conf))) \/
             MEM r (asm_config_avoid_regs (target_config
               (machine_config_target mc_conf))) then NONE else SOME
               (target_get_reg (machine_config_target mc_conf) ms_post
               r))) /\
     (!i. labSem_state_cc_fp_regs s1 0 i = target_get_fp_reg
       (machine_config_target mc_conf) ms_post i) /\
     target_cc_regs mc' ffi' ms_post = misc_shift_seq 1
       (labSem_state_cc_regs s1) /\
     target_cc_fp_regs mc' ffi' ms_post = misc_shift_seq 1
       (labSem_state_cc_fp_regs s1) /\
     target_io_regs mc' ffi' ms_post = labSem_state_io_regs s1 /\
     target_io_fp_regs mc' ffi' ms_post = labSem_state_io_fp_regs
       s1`)
  CHEAT_TAC;;

let oracle_tie_ffi_next = cake_theorem "oracle_tie_ffi_next"
  (fun () ->
    `oracle_tie mc_conf ms1 (s1:('a,'c,'ffi)labSem_state) /\
     next_interference mc_conf (labSem_state_ffi s1) ms1 =
       SOME (FfiApp index new_bytes ms_pre ms_post,mc',ffi') /\
         labSem_state_io_regs
     (s2:('a,'c,'ffi)labSem_state) = misc_shift_seq 1
       (labSem_state_io_regs s1) /\ labSem_state_io_fp_regs
     s2 = misc_shift_seq 1 (labSem_state_io_fp_regs s1) /\
       labSem_state_cc_regs
     s2 = labSem_state_cc_regs s1 /\ labSem_state_cc_fp_regs s2 =
       labSem_state_cc_fp_regs s1 /\ labSem_state_ffi
     s2 = ffi' ==>
     oracle_tie mc' ms_post s2`)
  CHEAT_TAC;;

let oracle_tie_ccache_next = cake_theorem "oracle_tie_ccache_next"
  (fun () ->
    `oracle_tie mc_conf ms1 (s1:('a,'c,'ffi)labSem_state) /\
     next_interference mc_conf (labSem_state_ffi s1) ms1 =
       SOME (CcApp a1 a2 ms_pre ms_post,mc',ffi') /\
         labSem_state_cc_regs
     (s2:('a,'c,'ffi)labSem_state) = misc_shift_seq 1
       (labSem_state_cc_regs s1) /\ labSem_state_cc_fp_regs
     s2 = misc_shift_seq 1 (labSem_state_cc_fp_regs s1) /\
       labSem_state_io_regs
     s2 = labSem_state_io_regs s1 /\ labSem_state_io_fp_regs s2 =
       labSem_state_io_fp_regs s1 /\ labSem_state_ffi
     s2 = ffi' ==>
     oracle_tie mc' ms_post s2`)
  CHEAT_TAC;;

let oracle_tie_ExtCall_residues =
  cake_theorem "oracle_tie_ExtCall_residues"
  (fun () ->
    `!mc_conf ms1 s1 ms2 l index name bytes bytes2 new_ffi new_bytes t1.
     oracle_tie mc_conf ms1 (s1:('a,'c,'ffi)labSem_state) /\
     (!k. find_next_interference mc_conf (labSem_state_ffi s1) (k +
       l) ms1 =
          find_next_interference
            (machine_config_next_interfer_fupd (K (misc_shift_seq l
              (machine_config_next_interfer mc_conf))) mc_conf)
              (labSem_state_ffi
            s1) k ms2) /\ ~(target_get_pc (machine_config_target
     mc_conf) ms2 IN machine_config_prog_addresses mc_conf DIFF
       set_of_list (machine_config_ffi_entry_pcs mc_conf)) /\
       ~(target_get_pc (machine_config_target
     mc_conf) ms2 = machine_config_halt_pc mc_conf) /\
       ~(target_get_pc (machine_config_target
     mc_conf) ms2 = machine_config_ccache_pc mc_conf) /\
     find_index (target_get_pc (machine_config_target mc_conf) ms2)
       (machine_config_ffi_entry_pcs mc_conf) 0 = SOME index /\
     EL index (machine_config_ffi_names mc_conf) = ffi_ExtCall name
       /\
     ALOOKUP (machine_config_mmio_info mc_conf) index = NONE /\
     read_ffi_bytearrays mc_conf ms2 = (SOME bytes,SOME bytes2) /\
     call_FFI (labSem_state_ffi s1) (ffi_ExtCall name) bytes bytes2
       = FFI_return new_ffi new_bytes ==>
     (\a. get_reg_value (labSem_state_io_regs s1 0 (ffi_ExtCall
       name) a) (asm_state_regs t1 a) I) =
       (\a. if MEM a (machine_config_callee_saved_regs mc_conf) \/
               ~(a < asm_config_reg_count (target_config
                 (machine_config_target mc_conf))) \/
               MEM a (asm_config_avoid_regs (target_config
                 (machine_config_target mc_conf))) then asm_state_regs
                 t1 a else target_get_reg (machine_config_target
                 mc_conf)
                   (machine_config_ffi_interfer mc_conf 0
                     (index,new_bytes,ms2)) a) /\
     (\n. labSem_state_io_fp_regs s1 0 n) =
       (\n. target_get_fp_reg (machine_config_target mc_conf)
              (machine_config_ffi_interfer mc_conf 0
                (index,new_bytes,ms2)) n)`)
  CHEAT_TAC;;

(* The code buffer is set-up to immediately follow the current code:
  |---code---|---cb---|
*)
let state_rel_def = cake_define
  `lab_to_targetProof_state_rel (mc_conf,code2,labs,p)
  (s1:('a,lab_to_target_config,'ffi)labSem_state) t1 ms1 <=>
     target_state_rel (machine_config_target mc_conf) t1 ms1 /\
       good_dimindex (:'a) /\
     (machine_config_prog_addresses mc_conf = asm_state_mem_domain
       t1) /\
     ~(machine_config_halt_pc mc_conf IN
       machine_config_prog_addresses mc_conf) /\
     ~(machine_config_ccache_pc mc_conf IN
       machine_config_prog_addresses mc_conf) /\
     reg_ok (labSem_state_ptr_reg s1) (target_config
       (machine_config_target mc_conf)) /\ (machine_config_ptr_reg
       mc_conf = labSem_state_ptr_reg s1) /\
     reg_ok (labSem_state_len_reg s1) (target_config
       (machine_config_target mc_conf)) /\ (machine_config_len_reg
       mc_conf = labSem_state_len_reg s1) /\
     reg_ok (labSem_state_ptr2_reg s1) (target_config
       (machine_config_target mc_conf)) /\ (machine_config_ptr2_reg
       mc_conf = labSem_state_ptr2_reg s1) /\
     reg_ok (labSem_state_len2_reg s1) (target_config
       (machine_config_target mc_conf)) /\ (machine_config_len2_reg
       mc_conf = labSem_state_len2_reg s1) /\
     reg_ok (labSem_state_link_reg s1) (target_config
       (machine_config_target mc_conf)) /\
     (
      // FFI behaves correctly
      ?i. mmio_pcs_min_index (machine_config_ffi_names mc_conf) =
        SOME i /\
          (!index. if i <= index /\ index < LENGTH
            (machine_config_ffi_names mc_conf) then ?info. ALOOKUP
            (machine_config_mmio_info mc_conf) index = SOME info else
            ALOOKUP (machine_config_mmio_info mc_conf) index = NONE)) /\
     (!ms2 k index new_bytes t1 bytes bytes2 st new_st i.
        // for normal ffis
        mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME
          i /\
        index < i /\
        read_ffi_bytearrays mc_conf ms2 = (SOME bytes,SOME bytes2) /\
          RTC
        call_FFI_rel (labSem_state_ffi s1) st /\
        call_FFI st (EL index (machine_config_ffi_names mc_conf))
          bytes bytes2 = FFI_return new_st new_bytes /\
        (machine_config_prog_addresses mc_conf = asm_state_mem_domain
          t1) /\
        target_state_rel (machine_config_target mc_conf)
          (asm_state_pc_fupd (K (p - n2w ((3 + index) * ffi_offset)))
            t1) ms2 /\
        alignment_aligned (asm_config_code_alignment (target_config
          (machine_config_target mc_conf))) (asm_state_regs t1
          (labSem_state_link_reg s1)) ==>
        (let ms' = machine_config_ffi_interfer mc_conf k
          (index,new_bytes,ms2) in
           target_state_rel (machine_config_target mc_conf)
             (asm_state_pc_fupd (K (asm_state_regs t1
               (labSem_state_link_reg s1))) (asm_state_mem_fupd (K
               (asm_write_bytearray (asm_state_regs t1
               (labSem_state_ptr2_reg s1)) new_bytes (asm_state_mem
               t1))) (asm_state_fp_regs_fupd (K (\n. target_get_fp_reg
               (machine_config_target mc_conf) ms' n))
               (asm_state_regs_fupd (K (\a. if MEM a
               (machine_config_callee_saved_regs mc_conf) \/
                              ~(a < asm_config_reg_count
                                (target_config (machine_config_target
                                mc_conf))) \/
                              MEM a (asm_config_avoid_regs
                                (target_config (machine_config_target
                                mc_conf))) then asm_state_regs t1 a else
                                target_get_reg (machine_config_target
                                mc_conf) ms' a)) t1))))
             ms')) /\
     (
      // clear cache behaves correctly
      !ms2 t1 k a1 a2.
       target_state_rel (machine_config_target mc_conf)
         (asm_state_pc_fupd (K (p - n2w ((2 * ffi_offset)))) t1) ms2
           /\
       alignment_aligned (asm_config_code_alignment (target_config
         (machine_config_target mc_conf))) (asm_state_regs t1
         (labSem_state_link_reg s1)) ==>
       (let ms' = machine_config_ccache_interfer mc_conf k
         (a1,a2,ms2) in
          target_state_rel (machine_config_target mc_conf)
            (asm_state_pc_fupd (K (asm_state_regs t1
              (labSem_state_link_reg s1))) (asm_state_fp_regs_fupd (K
              (\n. target_get_fp_reg (machine_config_target mc_conf) ms'
              n)) (asm_state_regs_fupd (K (\a. if MEM a
              (machine_config_callee_saved_regs mc_conf) \/
                              a = labSem_state_ptr_reg s1 \/
                              ~(a < asm_config_reg_count
                                (target_config (machine_config_target
                                mc_conf))) \/
                              MEM a (asm_config_avoid_regs
                                (target_config (machine_config_target
                                mc_conf))) then asm_state_regs t1 a else
                                target_get_reg (machine_config_target
                                mc_conf) ms' a)) t1)))
            ms')) /\ labSem_state_compile
     s1 = compile_lab (target_config (machine_config_target mc_conf))
       /\
     (no_share_mem_inst code2 ==> (!k. let (cfg,code) =
       labSem_state_compile_oracle s1 k in
             lab_to_targetProof_good_code (target_config
               (machine_config_target mc_conf))
               (lab_to_target_config_labels cfg) code /\
             no_share_mem_inst code /\
             (
              // Initial configuration for oracle
              // Note: this should not be stated as a record cfg = <|...|>
              // because some parts of it can be freely chosen (e.g. the clock)
              k = 0 ==> lab_to_target_config_labels
             cfg = labs /\ lab_to_target_config_pos
             cfg = LENGTH (prog_to_bytes code2) /\ ffi_names
             cfg = SOME (machine_config_ffi_names mc_conf)))) /\
     (!l1 l2 x.
        (lab_lookup l1 l2 labs = SOME x) ==> EVEN x) /\
     (((n2w 1) && p) = (n2w 0)) /\
     (list_subset
       (FILTER (\x. ?s. x = ffi_ExtCall s) (find_ffi_names
         (labSem_state_code s1))) (machine_config_ffi_names
       mc_conf)) /\
     // this is possibly already implied
     EVEN (LENGTH (prog_to_bytes code2)) /\
     (
      // FFIs are located at the right positions
      !name i.
         MEM name (machine_config_ffi_names mc_conf) /\
         mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME
           i /\
         get_ffi_index (machine_config_ffi_names mc_conf) name < i
           ==>
         (?s. name = ffi_ExtCall s) /\
        ~(p - n2w ((3 + get_ffi_index (machine_config_ffi_names
          mc_conf) name) * ffi_offset) IN machine_config_prog_addresses
          mc_conf) /\
        ~(p - n2w ((3 + get_ffi_index (machine_config_ffi_names
          mc_conf) name) * ffi_offset) = machine_config_halt_pc mc_conf)
          /\
        ~(p - n2w ((3 + get_ffi_index (machine_config_ffi_names
          mc_conf) name) * ffi_offset) = machine_config_ccache_pc
          mc_conf) /\
        (find_index (p - n2w ((3 + get_ffi_index
          (machine_config_ffi_names mc_conf) name) * ffi_offset))
          (machine_config_ffi_entry_pcs
                    mc_conf) 0 = SOME (get_ffi_index
                      (machine_config_ffi_names mc_conf) name))) /\
     (
      // Halt/ClearCache are at the right positions
      p - n2w ffi_offset = machine_config_halt_pc mc_conf) /\
     (p - n2w (2 * ffi_offset) = machine_config_ccache_pc mc_conf) /\
     // Small interference oracle is okay
     interference_ok (machine_config_next_interfer mc_conf)
       (target_proj (machine_config_target mc_conf)
       (asm_state_mem_domain t1)) /\
     (!l1 l2 x2.
        (loc_to_pc l1 l2 (labSem_state_code s1) = SOME x2) ==>
        (lab_lookup l1 l2 labs = SOME (pos_val x2 0 code2))) /\
     (
      // Relating register
      !r. labSem_state_fp_regs s1 r = asm_state_fp_regs t1 r) /\
     (!r. word_loc_val p labs (labSem_state_regs s1 r) = SOME
       (asm_state_regs t1 r)) /\
     (
      // Relating (data) memories
      !a. byte_align a IN labSem_state_mem_domain s1 ==>
          a IN asm_state_mem_domain t1 /\ a IN
            labSem_state_mem_domain s1 /\
          (word_loc_val_byte p labs (labSem_state_mem s1) a
            (labSem_state_be s1) = SOME (asm_state_mem t1 a))) /\
     (
      // Remaining space for code buffer exists
      !n.
       n < buffer_space_left (labSem_state_code_buffer s1) ==>
       (let addr' = buffer_position (labSem_state_code_buffer s1) +
         n2w (LENGTH (buffer_buffer (labSem_state_code_buffer s1)) + n)
         in
       addr' IN asm_state_mem_domain t1 /\ ~(addr' IN
         labSem_state_mem_domain s1))) /\
     // Position of code memory
     bytes_in_mem p (prog_to_bytes code2) (asm_state_mem
       t1) (asm_state_mem_domain t1) (labSem_state_mem_domain s1) /\
         buffer_position (labSem_state_code_buffer
     // Position of code buffer pointer
     s1) = p + n2w (LENGTH (prog_to_bytes code2)) /\
     // Code buffer's bytes are in the right position
     bytes_in_mem (buffer_position (labSem_state_code_buffer s1))
       (buffer_buffer (labSem_state_code_buffer s1)) (asm_state_mem
       t1) (asm_state_mem_domain t1) (labSem_state_mem_domain s1) /\
     // Code buffer writes do not overwrite memory
     LENGTH (prog_to_bytes code2) + LENGTH (buffer_buffer
       (labSem_state_code_buffer s1)) + buffer_space_left
       (labSem_state_code_buffer s1) < dimword (:'a) /\
     (
      // code buffer does not intersect with ffi_entry_pcs
      !bn.
       bn < LENGTH (buffer_buffer (labSem_state_code_buffer s1)) +
         buffer_space_left (labSem_state_code_buffer s1) ==>
       ~(MEM (buffer_position (labSem_state_code_buffer s1) + n2w bn)
         (machine_config_ffi_entry_pcs mc_conf))) /\
     ~(labSem_state_failed s1) /\ ~(asm_state_failed t1) /\
       (labSem_state_be s1 = asm_state_be t1) /\
     (asm_state_pc t1 = p + n2w (pos_val (labSem_state_pc s1) 0
       code2)) /\
     ((p && n2w (2 EXP asm_state_align t1 - 1)) = (n2w 0)) /\
     (match link_reg (target_config (machine_config_target mc_conf))
       with NONE -> T | SOME r -> asm_state_lr t1 = r) /\
     (asm_state_be t1 <=> asm_config_big_endian (target_config
       (machine_config_target mc_conf))) /\
     (asm_state_align t1 = asm_config_code_alignment (target_config
       (machine_config_target mc_conf))) /\
     (enc_ok (target_config (machine_config_target mc_conf))) /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs
       (TAKE (THE (mmio_pcs_min_index (machine_config_ffi_names
         mc_conf))) (machine_config_ffi_names mc_conf)) 0 code2 /\
     EVERY sec_labels_ok code2 /\
     code_similar (labSem_state_code s1) code2 /\
     share_mem_state_rel mc_conf s1 t1 ms1 /\
     share_mem_domain_code_rel mc_conf p code2
       (labSem_state_shared_mem_domain s1) /\
     LENGTH (machine_config_ffi_names mc_conf) = LENGTH
       (machine_config_ffi_entry_pcs mc_conf) /\
     no_install_or_no_share_mem code2 (machine_config_ffi_names
       mc_conf)`;;
hol4_overload "state_rel" "lab_to_targetProof_state_rel";;

let oracle_tie_clock = cake_theorem "oracle_tie_clock"
  (fun () ->
    `oracle_tie mc_conf ms s1 ==>
     oracle_tie mc_conf ms (labSem_state_clock_fupd (K k) s1)`)
  CHEAT_TAC;;

let lab_to_targetProof_state_rel_clock = cake_theorem "state_rel_clock"
  (fun () ->
    `state_rel x s1 t1 ms ==>
       state_rel x (labSem_state_clock_fupd (K k) s1) (t1) ms`)
  CHEAT_TAC;;

let share_mem_state_rel_shift_interfer =
  cake_theorem "share_mem_state_rel_shift_interfer"
  (fun () ->
    `share_mem_state_rel mc_conf s1 t1 x ==>
       share_mem_state_rel (machine_config_next_interfer_fupd (K
         (\i. machine_config_next_interfer mc_conf (i + l))) mc_conf)
         s1 t1 x`)
  CHEAT_TAC;;

let share_mem_domain_code_rel_shift_interfer =
  cake_theorem "share_mem_domain_code_rel_shift_interfer"
  (fun () ->
    `share_mem_domain_code_rel mc_conf p code2
  (labSem_state_shared_mem_domain s1) ==>
     share_mem_domain_code_rel
       (machine_config_next_interfer_fupd (K (\i.
         machine_config_next_interfer mc_conf (i + l))) mc_conf)
       p code2 (labSem_state_shared_mem_domain s1)`)
  CHEAT_TAC;;

let state_rel_shift_interfer = cake_theorem "state_rel_shift_interfer"
  (fun () ->
    `state_rel (mc_conf,code2,labs,p) s1 t1 x ==>
       state_rel (shift_interfer l mc_conf,code2,labs,p) s1 t1 x`)
  CHEAT_TAC;;

(* bytes_in_memory lemmas *)
let prog_to_bytes_lemma = cake_theorem "prog_to_bytes_lemma[local]"
  (fun () ->
    `!code2 code1 pc' i pos.
         code_similar code1 code2 /\
         all_enc_ok (target_config (machine_config_target
           (mc_conf:('a,'state,'b)machine_config)))
           labs ffi_names pos code2 /\
         (asm_fetch_aux pc' code1 = SOME i) ==>
         (?bs j bs2.
           (prog_to_bytes code2 = bs ++ line_bytes j ++ bs2) /\
           (LENGTH bs + pos = pos_val pc' pos code2) /\
           (LENGTH bs + pos + LENGTH (line_bytes j) = pos_val (pc'
             + 1) pos code2) /\
           line_similar i j /\
           line_ok (target_config (machine_config_target
             mc_conf)) labs ffi_names (pos_val pc' pos code2) j)`)
  CHEAT_TAC;;

(* HOL4 lab_to_targetProofScript.sml:1210-1212: ML code, not ported *)

let bytes_in_mem_APPEND = cake_theorem "bytes_in_mem_APPEND[local]"
  (fun () ->
    `!xs ys a m md md1.
         bytes_in_mem a (xs ++ ys) m md md1 <=>
         bytes_in_mem a xs m md md1 /\
         bytes_in_mem (a + n2w (LENGTH xs)) ys m md md1`)
  CHEAT_TAC;;

let bytes_in_mem_UPDATE = cake_theorem "bytes_in_mem_UPDATE"
  (fun () ->
    `!ls a m md md2 w1 w2.
     (!n. n < LENGTH ls ==> ~(a + n2w n = w1)) /\
     bytes_in_mem a ls m md md2 ==>
     bytes_in_mem a ls ((w1 =+ w2) m) md md2`)
  CHEAT_TAC;;

(* HOL4 lab_to_targetProofScript.sml:1240: the ML values that the
   definitions below antiquote *)

let IMP_bytes_in_memory = cake_theorem "IMP_bytes_in_memory[local]"
  (fun () ->
    `code_similar code1 code2 /\
       all_enc_ok (target_config (machine_config_target mc_conf))
         labs ffi_names 0 code2 /\
       (asm_fetch_aux pc code1 = SOME i) /\
       bytes_in_mem p (prog_to_bytes code2) m (dm:'a word->bool)
         dm1 ==>
       (?j.
         bytes_in_mem (p + n2w (pos_val pc 0 code2)) (line_bytes j)
           m dm dm1 /\
         line_ok (target_config (machine_config_target
           (mc_conf:('a,'state,'b)machine_config)))
           labs ffi_names (pos_val pc 0 code2) j /\
         (pos_val (pc + 1) 0 code2 = pos_val pc 0 code2 + LENGTH
           (line_bytes j)) /\
         line_similar i j)`)
  CHEAT_TAC;;

let IMP_bytes_in_memory_JumpReg =
  cake_theorem "IMP_bytes_in_memory_JumpReg[local]"
  (fun () ->
    `code_similar (labSem_state_code s1) code2 /\
       all_enc_ok (target_config (machine_config_target mc_conf))
         labs ffi_names 0 code2 /\
       bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1)
         (asm_state_mem_domain t1) (labSem_state_mem_domain s1) /\
       (asm_fetch s1 = SOME (labLang_Asm (Asmi (asm_JumpReg r1)) l
         n)) ==>
       bytes_in_memory ((p:'a word) + n2w (pos_val (labSem_state_pc
         s1) 0 code2))
         (asm_config_encode (target_config (machine_config_target
           mc_conf)) (asm_JumpReg r1)) (asm_state_mem t1)
           (asm_state_mem_domain t1) /\
       asm_ok (asm_JumpReg r1) (target_config
         (machine_config_target
         (mc_conf:('a,'state,'b)machine_config)))`)
  CHEAT_TAC;;

(* HOL4 lab_to_targetProofScript.sml:1281-1284: ML code, not ported *)

let IMP_bytes_in_memory_Jump =
  cake_theorem "IMP_bytes_in_memory_Jump[local]"
  (fun () ->
    `code_similar (labSem_state_code
  (s1:('a,lab_to_target_config,'ffi)labSem_state)) code2 /\
       all_enc_ok (target_config (machine_config_target mc_conf))
         labs ffi_names 0 code2 /\
       bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1)
         (asm_state_mem_domain t1) (labSem_state_mem_domain s1) /\
       (asm_fetch s1 = SOME (labLang_LabAsm (Jump jtarget) l bytes
         n)) ==>
       (?tt enc.
         (tt = n2w (find_pos jtarget labs) -
               n2w (pos_val (labSem_state_pc s1) 0 code2)) /\
         (enc = asm_config_encode (target_config
           (machine_config_target mc_conf)) (Jump tt)) /\
         bytes_in_memory ((p:'a word) + n2w (pos_val
           (labSem_state_pc s1) 0 code2))
           enc (asm_state_mem t1) (asm_state_mem_domain t1) /\
         asm_ok (Jump tt) (target_config (machine_config_target
           (mc_conf:('a,'state,'b)machine_config))))`)
  CHEAT_TAC;;

let IMP_bytes_in_memory_JumpCmp =
  cake_theorem "IMP_bytes_in_memory_JumpCmp[local]"
  (fun () ->
    `code_similar (labSem_state_code
  (s1:('a,lab_to_target_config,'ffi)labSem_state)) code2 /\
       all_enc_ok (target_config (machine_config_target mc_conf))
         labs ffi_names 0 code2 /\
       bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1)
         (asm_state_mem_domain t1) (labSem_state_mem_domain s1) /\
       (asm_fetch s1 = SOME (labLang_LabAsm (JumpCmp cmp rr ri
         jtarget) l bytes n)) ==>
       (?tt enc.
         (tt = n2w (find_pos jtarget labs) -
               n2w (pos_val (labSem_state_pc s1) 0 code2)) /\
         (enc = asm_config_encode (target_config
           (machine_config_target mc_conf)) (JumpCmp cmp rr ri tt)) /\
         bytes_in_memory ((p:'a word) + n2w (pos_val
           (labSem_state_pc s1) 0 code2))
           enc (asm_state_mem t1) (asm_state_mem_domain t1) /\
         asm_ok (JumpCmp cmp rr ri tt) (target_config
           (machine_config_target
           (mc_conf:('a,'state,'b)machine_config))))`)
  CHEAT_TAC;;

let IMP_bytes_in_memory_JumpCmp_1 =
  cake_theorem "IMP_bytes_in_memory_JumpCmp_1[local]"
  (fun () ->
    `code_similar (labSem_state_code
  (s1:('a,lab_to_target_config,'ffi)labSem_state)) code2 /\
       all_enc_ok (target_config (machine_config_target mc_conf))
         labs ffi_names 0 code2 /\
       bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1)
         (asm_state_mem_domain t1) (labSem_state_mem_domain s1) /\
       (asm_fetch s1 = SOME (labLang_LabAsm (JumpCmp cmp rr ri
         jtarget) l bytes n)) ==>
       (?tt bytes.
         (tt = n2w (find_pos jtarget labs) -
               n2w (pos_val (labSem_state_pc s1) 0 code2)) /\
         enc_with_nop (asm_config_encode (target_config
           (machine_config_target mc_conf))) (JumpCmp cmp rr ri tt)
           bytes /\
         bytes_in_memory ((p:'a word) + n2w (pos_val
           (labSem_state_pc s1) 0 code2))
           bytes (asm_state_mem t1) (asm_state_mem_domain t1) /\
         (pos_val (labSem_state_pc s1 + 1) 0 code2 = pos_val
           (labSem_state_pc s1) 0 code2 + LENGTH bytes) /\
         asm_ok (JumpCmp cmp rr ri tt) (target_config
           (machine_config_target
           (mc_conf:('a,'state,'b)machine_config))))`)
  CHEAT_TAC;;

let IMP_bytes_in_memory_Call =
  cake_theorem "IMP_bytes_in_memory_Call[local]"
  (fun () ->
    `code_similar (labSem_state_code
  (s1:('a,lab_to_target_config,'ffi)labSem_state)) code2 /\
       all_enc_ok (target_config (machine_config_target
         (mc_conf:('a,'state,'b)machine_config))) labs ffi_names 0
           code2 /\
       bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1)
         (asm_state_mem_domain
         (t1:'a asm_state)) (labSem_state_mem_domain s1) /\
       (asm_fetch s1 = SOME (labLang_LabAsm (Call ww) l bytes n))
         ==>
       F`)
  CHEAT_TAC;;

let IMP_bytes_in_memory_LocValue =
  cake_theorem "IMP_bytes_in_memory_LocValue[local]"
  (fun () ->
    `code_similar (labSem_state_code
  (s1:('a,lab_to_target_config,'ffi)labSem_state)) code2 /\
       all_enc_ok (target_config (machine_config_target mc_conf))
         labs ffi_names 0 code2 /\
       bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1)
         (asm_state_mem_domain t1) (labSem_state_mem_domain s1) /\
       (asm_fetch s1 = SOME (labLang_LabAsm (LocValue reg
         (labLang_Lab l1 l2)) l bytes n)) ==>
       (?tt bytes.
         (tt = n2w (find_pos (labLang_Lab l1 l2) labs) -
               n2w (pos_val (labSem_state_pc s1) 0 code2)) /\
         enc_with_nop (asm_config_encode (target_config
           (machine_config_target mc_conf))) (Loc reg tt) bytes /\
         bytes_in_memory ((p:'a word) + n2w (pos_val
           (labSem_state_pc s1) 0 code2))
           bytes (asm_state_mem t1) (asm_state_mem_domain t1) /\
         (pos_val (labSem_state_pc s1 + 1) 0 code2 = pos_val
           (labSem_state_pc s1) 0 code2 + LENGTH bytes) /\
         asm_ok (Loc reg tt) (target_config
           (machine_config_target
           (mc_conf:('a,'state,'b)machine_config))))`)
  CHEAT_TAC;;

let IMP_bytes_in_memory_Inst =
  cake_theorem "IMP_bytes_in_memory_Inst[local]"
  (fun () ->
    `code_similar (labSem_state_code
  (s1:('a,lab_to_target_config,'ffi)labSem_state)) code2 /\
       all_enc_ok (target_config (machine_config_target mc_conf))
         labs ffi_names 0 code2 /\
       bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1)
         (asm_state_mem_domain t1) (labSem_state_mem_domain s1) /\
       (asm_fetch s1 = SOME (labLang_Asm (Asmi (asm_Inst i)) bytes
         len)) ==>
       (?bytes.
         enc_with_nop (asm_config_encode (target_config
           (machine_config_target mc_conf))) (Inst i) bytes /\
         bytes_in_memory ((p:'a word) + n2w (pos_val
           (labSem_state_pc s1) 0 code2))
           bytes (asm_state_mem t1) (asm_state_mem_domain t1) /\
         bytes_in_mem ((p:'a word) + n2w (pos_val (labSem_state_pc
           s1) 0 code2))
           bytes (asm_state_mem t1) (asm_state_mem_domain t1)
             (labSem_state_mem_domain s1) /\
         (pos_val (labSem_state_pc s1 + 1) 0 code2 = pos_val
           (labSem_state_pc s1) 0 code2 + LENGTH bytes) /\
         asm_ok (Inst i) (target_config (machine_config_target
           (mc_conf:('a,'state,'b)machine_config))))`)
  CHEAT_TAC;;

let IMP_bytes_in_memory_Cbw =
  cake_theorem "IMP_bytes_in_memory_Cbw[local]"
  (fun () ->
    `code_similar (labSem_state_code
  (s1:('a,lab_to_target_config,'ffi)labSem_state)) code2 /\
       all_enc_ok (target_config (machine_config_target mc_conf))
         labs ffi_names 0 code2 /\
       bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1)
         (asm_state_mem_domain t1) (labSem_state_mem_domain s1) /\
       (asm_fetch s1 = SOME (labLang_Asm (Cbw r1 r2) bytes len))
         ==>
       (?bytes.
         enc_with_nop (asm_config_encode (target_config
           (machine_config_target mc_conf))) (Inst (asm_Mem asm_Store8
           r2 (Addr r1 (n2w 0)))) bytes /\
         bytes_in_memory ((p:'a word) + n2w (pos_val
           (labSem_state_pc s1) 0 code2))
           bytes (asm_state_mem t1) (asm_state_mem_domain t1) /\
         bytes_in_mem ((p:'a word) + n2w (pos_val (labSem_state_pc
           s1) 0 code2))
           bytes (asm_state_mem t1) (asm_state_mem_domain t1)
             (labSem_state_mem_domain s1) /\
         (pos_val (labSem_state_pc s1 + 1) 0 code2 = pos_val
           (labSem_state_pc s1) 0 code2 + LENGTH bytes) /\
         asm_ok (Inst (asm_Mem asm_Store8 r2 (Addr r1 (n2w 0))))
           (target_config (machine_config_target
           (mc_conf:('a,'state,'b)machine_config))))`)
  CHEAT_TAC;;

let IMP_bytes_in_memory_CallFFI =
  cake_theorem "IMP_bytes_in_memory_CallFFI[local]"
  (fun () ->
    `code_similar (labSem_state_code
  (s1:('a,lab_to_target_config,'ffi)labSem_state)) code2 /\
       all_enc_ok (target_config (machine_config_target mc_conf))
         labs ffi_names 0 code2 /\
       bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1)
         (asm_state_mem_domain t1) (labSem_state_mem_domain s1) /\
       (asm_fetch s1 = SOME (labLang_LabAsm (labLang_CallFFI name)
         l bytes n)) ==>
       (?tt enc.
         (tt = (n2w 0) - n2w (pos_val (labSem_state_pc s1) 0 code2
           + (3 + get_ffi_index ffi_names (ffi_ExtCall name)) *
           ffi_offset)) /\
         (enc = asm_config_encode (target_config
           (machine_config_target mc_conf)) (Jump tt)) /\
         bytes_in_memory ((p:'a word) + n2w (pos_val
           (labSem_state_pc s1) 0 code2))
           enc (asm_state_mem t1) (asm_state_mem_domain t1) /\
         asm_ok (Jump tt) (target_config (machine_config_target
           (mc_conf:('a,'state,'b)machine_config))))`)
  CHEAT_TAC;;

let IMP_bytes_in_memory_Halt =
  cake_theorem "IMP_bytes_in_memory_Halt[local]"
  (fun () ->
    `code_similar (labSem_state_code
  (s1:('a,lab_to_target_config,'ffi)labSem_state)) code2 /\
       all_enc_ok (target_config (machine_config_target mc_conf))
         labs ffi_names 0 code2 /\
       bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1)
         (asm_state_mem_domain t1) (labSem_state_mem_domain s1) /\
       (asm_fetch s1 = SOME (labLang_LabAsm labLang_Halt l bytes
         n)) ==>
       (?tt enc.
         (tt = (n2w 0) - n2w (pos_val (labSem_state_pc s1) 0 code2
           + ffi_offset)) /\
         (enc = asm_config_encode (target_config
           (machine_config_target mc_conf)) (Jump tt)) /\
         bytes_in_memory ((p:'a word) + n2w (pos_val
           (labSem_state_pc s1) 0 code2))
           enc (asm_state_mem t1) (asm_state_mem_domain t1) /\
         asm_ok (Jump tt) (target_config (machine_config_target
           (mc_conf:('a,'state,'b)machine_config))))`)
  CHEAT_TAC;;

let IMP_bytes_in_memory_Install =
  cake_theorem "IMP_bytes_in_memory_Install[local]"
  (fun () ->
    `code_similar (labSem_state_code
  (s1:('a,lab_to_target_config,'ffi)labSem_state)) code2 /\
       all_enc_ok (target_config (machine_config_target mc_conf))
         labs ffi_names 0 code2 /\
       bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1)
         (asm_state_mem_domain t1) (labSem_state_mem_domain s1) /\
       (asm_fetch s1 = SOME (labLang_LabAsm Install c l n)) ==>
       (?tt enc.
         (tt = (n2w 0) - n2w (pos_val (labSem_state_pc s1) 0 code2
           + 2 * ffi_offset)) /\
         (enc = asm_config_encode (target_config
           (machine_config_target mc_conf)) (Jump tt)) /\
         bytes_in_memory ((p:'a word) + n2w (pos_val
           (labSem_state_pc s1) 0 code2))
           enc (asm_state_mem t1) (asm_state_mem_domain t1) /\
         asm_ok (Jump tt) (target_config (machine_config_target
           (mc_conf:('a,'state,'b)machine_config))))`)
  CHEAT_TAC;;

let all_enc_ok_asm_fetch_aux_IMP_line_ok =
  cake_theorem "all_enc_ok_asm_fetch_aux_IMP_line_ok"
  (fun () ->
    `!pc' n code2.
       all_enc_ok c labs ffis n code2 /\
       asm_fetch_aux pc' code2 = SOME line ==>
       line_ok c labs ffis (pos_val pc' n code2) line`)
  CHEAT_TAC;;

let code_similar_IMP_asm_fetch_aux_line_similar =
  cake_theorem "code_similar_IMP_asm_fetch_aux_line_similar"
  (fun () ->
    `!pc' code1 code2.
       code_similar code1 code2 ==>
       OPTREL line_similar (asm_fetch_aux pc' code1)
         (asm_fetch_aux pc' code2)`)
  CHEAT_TAC;;

let asm_fetch_aux_pos_val_LENGTH_EQ =
  cake_theorem "asm_fetch_aux_pos_val_LENGTH_EQ"
  (fun () ->
    `!pc' n code2 line.
       asm_fetch_aux pc' code2 = SOME line /\
       all_enc_ok conf labs ffi_names n code2 /\
       pos_val (pc' + 1) n code2 = LENGTH bytes' + pos_val pc' n
         code2 ==>
       LENGTH (line_bytes line) = LENGTH (bytes':word8 list)`)
  CHEAT_TAC;;

let IMP_bytes_in_memory_ShareMem =
  cake_theorem "IMP_bytes_in_memory_ShareMem"
  (fun () ->
    `(asm_fetch_aux (labSem_state_pc s1) (labSem_state_code s1) = SOME
  (labLang_Asm (ShareMem mop r ad) l n)) /\
     code_similar (labSem_state_code
       (s1:('a,lab_to_target_config,'ffi)labSem_state)) code2 /\
     all_enc_ok (target_config (machine_config_target mc_conf))
       labs ffi_names 0 code2 /\
     bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1)
       (asm_state_mem_domain t1) (labSem_state_mem_domain s1) ==>
     (?bytes.
       asm_fetch_aux (labSem_state_pc s1) code2 = SOME (labLang_Asm
         (ShareMem mop r ad)
         bytes (LENGTH bytes)) /\
       enc_with_nop (asm_config_encode (target_config
         (machine_config_target mc_conf))) (Inst (asm_Mem mop r ad))
         bytes /\
       bytes_in_memory ((p:'a word) + n2w (pos_val (labSem_state_pc
         s1) 0 code2))
         bytes (asm_state_mem t1) (asm_state_mem_domain t1) /\
       bytes_in_mem ((p:'a word) + n2w (pos_val (labSem_state_pc
         s1) 0 code2))
         bytes (asm_state_mem t1) (asm_state_mem_domain t1)
           (labSem_state_mem_domain s1) /\
       (pos_val (labSem_state_pc s1 + 1) 0 code2 = pos_val
         (labSem_state_pc s1) 0 code2 + LENGTH bytes) /\
       asm_ok (Inst (asm_Mem mop r ad)) (target_config
         (machine_config_target
         (mc_conf:('a,'state,'b)machine_config))))`)
  CHEAT_TAC;;

let bytes_in_mem_IMP_memory =
  cake_theorem "bytes_in_mem_IMP_memory[local]"
  (fun () ->
    `!xs a.
         (!a. ~(a IN dm1) ==> m a = m1 a) ==>
         bytes_in_mem a xs m dm dm1 ==>
         bytes_in_memory a xs m1 dm`)
  CHEAT_TAC;;

(* read/write bytearrays for FFI *)

let read_bytearray_state_rel =
  cake_theorem "read_bytearray_state_rel[local]"
  (fun () ->
    `!n a x.
         state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
         (read_bytearray a n (mem_load_byte_aux (labSem_state_mem
           s1) (labSem_state_mem_domain s1) (labSem_state_be s1)) = SOME
           x) ==>
         (read_bytearray a n
           (\a. if a IN machine_config_prog_addresses mc_conf then
             SOME (asm_state_mem t1 a) else NONE) =
          SOME x)`)
  CHEAT_TAC;;

let IMP_has_io_name = cake_theorem "IMP_has_io_name[local]"
  (fun () ->
    `(asm_fetch s1 = SOME (labLang_LabAsm (labLang_CallFFI index) l
  bytes n)) ==>
       has_io_name index (labSem_state_code s1)`)
  CHEAT_TAC;;

let bytes_in_mem_asm_write_bytearray_lemma =
  cake_theorem "bytes_in_mem_asm_write_bytearray_lemma[local]"
  (fun () ->
    `!xs p.
         (!a. ~(a IN k) ==> (m1 a = m2 a)) ==>
         bytes_in_mem p xs m1 d k ==>
         bytes_in_mem p xs m2 d k`)
  CHEAT_TAC;;

let bytes_in_mem_asm_write_bytearray =
  cake_theorem "bytes_in_mem_asm_write_bytearray[local]"
  (fun () ->
    `(!a. byte_align a IN labSem_state_mem_domain s1 ==> a IN
  labSem_state_mem_domain s1) /\
       (read_bytearray c1 (LENGTH new_bytes) (mem_load_byte_aux
         (labSem_state_mem s1) (labSem_state_mem_domain s1)
         (labSem_state_be s1)) = SOME x) ==>
       bytes_in_mem p xs (asm_state_mem t1) (asm_state_mem_domain
         t1) (labSem_state_mem_domain s1) ==>
       bytes_in_mem p xs
         (asm_write_bytearray c1 new_bytes (asm_state_mem t1))
           (asm_state_mem_domain t1) (labSem_state_mem_domain s1)`)
  CHEAT_TAC;;

let write_bytearray_NOT_Loc =
  cake_theorem "write_bytearray_NOT_Loc[local]"
  (fun () ->
    `!xs c1 s1 a c.
         (labSem_state_mem s1 a = wordLang_Word c) ==>
           ~((write_bytearray c1 xs (labSem_state_mem s1)
           (labSem_state_mem_domain s1) (labSem_state_be s1)) a = Loc
           n n0)`)
  CHEAT_TAC;;

let CallFFI_bytearray_lemma =
  cake_theorem "CallFFI_bytearray_lemma[local]"
  (fun () ->
    `byte_align (a:'a word) IN labSem_state_mem_domain s1 /\
  good_dimindex (:'a) /\
       a IN asm_state_mem_domain t1 /\
       a IN labSem_state_mem_domain s1 /\
       (labSem_state_be s1 = asm_config_big_endian (target_config
         (machine_config_target mc_conf))) /\
       (read_bytearray c1 (LENGTH new_bytes) (mem_load_byte_aux
         (labSem_state_mem s1) (labSem_state_mem_domain s1)
         (labSem_state_be s1)) = SOME x) /\
       (word_loc_val_byte p labs (labSem_state_mem s1) a
         (asm_config_big_endian (target_config (machine_config_target
         mc_conf))) =
          SOME (asm_state_mem t1 a)) ==>
       (word_loc_val_byte p labs (write_bytearray c1 new_bytes
         (labSem_state_mem s1) (labSem_state_mem_domain s1)
         (labSem_state_be s1)) a (asm_config_big_endian (target_config
         (machine_config_target
          mc_conf))) =
        SOME (asm_write_bytearray c1 new_bytes (asm_state_mem t1)
          a))`)
  CHEAT_TAC;;

(* inst correct *)

let MULT_ADD_LESS_MULT = cake_theorem "MULT_ADD_LESS_MULT[local]"
  (fun () ->
    `!m n k l j. m < l /\ n < k /\ j <= k ==> m * j + n < l * (k:num)`)
  CHEAT_TAC;;

let aligned_IMP_ADD_LESS_dimword =
  cake_theorem "aligned_IMP_ADD_LESS_dimword[local]"
  (fun () ->
    `alignment_aligned k (x:'a word) /\ k <= dimindex (:'a) ==>
       w2n x + (2 EXP k - 1) < dimword (:'a)`)
  CHEAT_TAC;;

let aligned_2_imp = cake_theorem "aligned_2_imp"
  (fun () ->
    `alignment_aligned 2 (x:'a word) /\ dimindex (:'a) = 32 ==>
      byte_align x = x /\
      byte_align (x + (n2w 1)) = x /\
      byte_align (x + (n2w 2)) = x /\
      byte_align (x + (n2w 3)) = x`)
  CHEAT_TAC;;

let aligned_2_not_eq = cake_theorem "aligned_2_not_eq"
  (fun () ->
    `alignment_aligned 2 (x:'a word) /\ dimindex (:'a) = 32 /\ ~(x =
  byte_align a) ==> ~(x = a) /\ ~(x + (n2w 1) = a) /\ ~(x + (n2w 2) =
  a) /\ ~(x + (n2w 3) = a)`)
  CHEAT_TAC;;

let aligned_3_imp = cake_theorem "aligned_3_imp"
  (fun () ->
    `alignment_aligned 3 (x:'a word) /\ dimindex (:'a) = 64 ==>
      byte_align x = x /\
      byte_align (x + (n2w 1)) = x /\
      byte_align (x + (n2w 2)) = x /\
      byte_align (x + (n2w 3)) = x /\
      byte_align (x + (n2w 4)) = x /\
      byte_align (x + (n2w 5)) = x /\
      byte_align (x + (n2w 6)) = x /\
      byte_align (x + (n2w 7)) = x`)
  CHEAT_TAC;;

let aligned_3_not_eq = cake_theorem "aligned_3_not_eq"
  (fun () ->
    `alignment_aligned 3 (x:'a word) /\ dimindex (:'a) = 64 /\ ~(x =
  byte_align a) ==> ~(x = a) /\ ~(x + (n2w 1) = a) /\ ~(x + (n2w 2) =
  a) /\ ~(x + (n2w 3) = a) /\ ~(x + (n2w 4) = a) /\ ~(x + (n2w 5) = a)
  /\ ~(x + (n2w 6) = a) /\ ~(x + (n2w 7) = a)`)
  CHEAT_TAC;;

let dimword_eq_32_imp_or_bytes =
  cake_theorem "dimword_eq_32_imp_or_bytes[local]"
  (fun () ->
    `dimindex (:'a) = 32 ==>
       (w2w ((w2w (x:'a word)):word8) ||
        w2w ((w2w (x >>> 8)):word8) << 8 ||
        w2w ((w2w (x >>> 16)):word8) << 16 ||
        w2w ((w2w (x >>> 24)):word8) << 24) = x`)
  CHEAT_TAC;;

let dimword_eq_64_imp_or_bytes =
  cake_theorem "dimword_eq_64_imp_or_bytes[local]"
  (fun () ->
    `dimindex (:'a) = 64 ==>
       (w2w ((w2w (x:'a word)):word8) ||
        w2w ((w2w (x >>> 8)):word8) << 8 ||
        w2w ((w2w (x >>> 16)):word8) << 16 ||
        w2w ((w2w (x >>> 24)):word8) << 24 ||
        w2w ((w2w (x >>> 32)):word8) << 32 ||
        w2w ((w2w (x >>> 40)):word8) << 40 ||
        w2w ((w2w (x >>> 48)):word8) << 48 ||
        w2w ((w2w (x >>> 56)):word8) << 56) = x`)
  CHEAT_TAC;;

let byte_align_32_eq = cake_theorem "byte_align_32_eq[local]"
  (fun () ->
    `dimindex (:'a) = 32 ==>
     byte_align (a:'a word) + n2w (w2n a MOD 4) = a`)
  CHEAT_TAC;;

let byte_align_64_eq = cake_theorem "byte_align_64_eq[local]"
  (fun () ->
    `dimindex (:'a) = 64 ==>
     byte_align (a:'a word) + n2w (w2n a MOD 8) = a`)
  CHEAT_TAC;;

let byte_align_32_IMP = cake_theorem "byte_align_32_IMP[local]"
  (fun () ->
    `dimindex (:'a) = 32 ==>
     (byte_align a = a ==> w2n a MOD 4 = 0) /\
     (byte_align a + ((n2w 1):'a word) = a ==> w2n a MOD 4 = 1) /\
     (byte_align a + ((n2w 2):'a word) = a ==> w2n a MOD 4 = 2) /\
     (byte_align a + ((n2w 3):'a word) = a ==> w2n a MOD 4 = 3)`)
  CHEAT_TAC;;

let MOD4_CASES = cake_theorem "MOD4_CASES[local]"
  (fun () ->
    `!n. n MOD 4 = 0 \/ n MOD 4 = 1 \/ n MOD 4 = 2 \/ n MOD 4 = 3`)
  CHEAT_TAC;;

let byte_align_32_CASES = cake_theorem "byte_align_32_CASES[local]"
  (fun () ->
    `dimindex (:'a) = 32 ==>
     byte_align a + ((n2w 3):'a word) = a \/
     byte_align a + ((n2w 2):'a word) = a \/
     byte_align a + ((n2w 1):'a word) = a \/
     byte_align a = a`)
  CHEAT_TAC;;

let MOD8_CASES = cake_theorem "MOD8_CASES[local]"
  (fun () ->
    `!n. n MOD 8 = 0 \/ n MOD 8 = 1 \/ n MOD 8 = 2 \/ n MOD 8 = 3 \/
         n MOD 8 = 4 \/ n MOD 8 = 5 \/ n MOD 8 = 6 \/ n MOD 8 = 7`)
  CHEAT_TAC;;

let byte_align_64_CASES = cake_theorem "byte_align_64_CASES[local]"
  (fun () ->
    `dimindex (:'a) = 64 ==>
     byte_align a + ((n2w 7):'a word) = a \/
     byte_align a + ((n2w 6):'a word) = a \/
     byte_align a + ((n2w 5):'a word) = a \/
     byte_align a + ((n2w 4):'a word) = a \/
     byte_align a + ((n2w 3):'a word) = a \/
     byte_align a + ((n2w 2):'a word) = a \/
     byte_align a + ((n2w 1):'a word) = a \/
     byte_align a = a`)
  CHEAT_TAC;;

let byte_align_64_IMP = cake_theorem "byte_align_64_IMP[local]"
  (fun () ->
    `dimindex (:'a) = 64 ==>
     (byte_align a + ((n2w 7):'a word) = a ==> w2n a MOD 8 = 7) /\
     (byte_align a + ((n2w 6):'a word) = a ==> w2n a MOD 8 = 6) /\
     (byte_align a + ((n2w 5):'a word) = a ==> w2n a MOD 8 = 5) /\
     (byte_align a + ((n2w 4):'a word) = a ==> w2n a MOD 8 = 4) /\
     (byte_align a + ((n2w 3):'a word) = a ==> w2n a MOD 8 = 3) /\
     (byte_align a + ((n2w 2):'a word) = a ==> w2n a MOD 8 = 2) /\
     (byte_align a + ((n2w 1):'a word) = a ==> w2n a MOD 8 = 1) /\
     (byte_align a = a ==> w2n a MOD 8 = 0)`)
  CHEAT_TAC;;

let arith_upd_lemma = cake_theorem "arith_upd_lemma[local]"
  (fun () ->
    `(!r. word_loc_val p labs (labSem_state_regs s1 r) = SOME
  (asm_state_regs t1 r)) /\ ~(failed (arith_upd a s1)) ==>
      (!r. word_loc_val p labs (regs (arith_upd a s1) r) =
          SOME (regs (arith_upd a t1) r))`)
  CHEAT_TAC;;

(* The lab and asm versions should be in their individual props *)
let arith_upd_fp_regs = cake_theorem "arith_upd_fp_regs[simp]"
  (fun () ->
    `(fp_regs (arith_upd a s) = fp_regs s /\ fp_regs
     (arith_upd a (t:'a asm_state)) = asm_state_fp_regs t)`)
  CHEAT_TAC;;

let fp_upd_lemma = cake_theorem "fp_upd_lemma[local]"
  (fun () ->
    `(!r. word_loc_val p labs (labSem_state_regs s1 r) = SOME
  (asm_state_regs t1 r)) /\
     (!r. labSem_state_fp_regs s1 r = asm_state_fp_regs t1 r) /\
      ~(failed (fp_upd f s1)) ==>
     (!r. fp_regs (fp_upd f s1) r = fp_regs (fp_upd f t1) r) /\
     (!r.
       word_loc_val p labs (regs (fp_upd f s1) r) =
       SOME (regs (fp_upd f t1) r))`)
  CHEAT_TAC;;

let inst_share_mem_pc_update_helper =
  cake_theorem "Inst_share_mem_pc_update_helper"
  (fun () ->
    `share_mem_state_rel mc_conf s1 t1 ms1 /\
     target_state_rel (machine_config_target mc_conf)
       (asm_state_pc_fupd (K pc') t1) ms2 ==>
     share_mem_state_rel mc_conf (labSem_state_clock_fupd (K
       (labSem_state_clock s1 - 1)) (labSem_state_pc_fupd (K
       (labSem_state_pc s1 + 1)) s1))
       (asm_state_pc_fupd (K pc') t1) ms2`)
  CHEAT_TAC;;

let inst_share_mem_reg_update_helper =
  cake_theorem "Inst_share_mem_reg_update_helper"
  (fun () ->
    `share_mem_state_rel mc_conf s1 t1 ms1 /\
     target_state_rel (machine_config_target mc_conf)
       (asm_state_pc_fupd (K pc') (asm_state_regs_fupd (K ((n =+ c)
         (asm_state_regs t1))) t1)) ms2 ==>
     share_mem_state_rel mc_conf (labSem_state_clock_fupd (K
       (labSem_state_clock s1 - 1)) (labSem_state_pc_fupd (K
       (labSem_state_pc s1 + 1)) (labSem_state_regs_fupd (K ((n =+
       wordLang_Word c) (labSem_state_regs s1))) s1)))
       (asm_state_pc_fupd (K pc') (asm_state_regs_fupd (K ((n =+
         c) (asm_state_regs t1))) t1)) ms2`)
  CHEAT_TAC;;

let arith_upd_share_mem_domain_unchange =
  cake_theorem "arith_upd_share_mem_domain_unchange"
  (fun () ->
    `labSem_state_shared_mem_domain
       (arith_upd a s1) = labSem_state_shared_mem_domain s1`)
  CHEAT_TAC;;

let fp_upd_share_mem_domain_unchange =
  cake_theorem "fp_upd_share_mem_domain_unchange"
  (fun () ->
    `labSem_state_shared_mem_domain
       (fp_upd f s1) = labSem_state_shared_mem_domain s1`)
  CHEAT_TAC;;

(* HOL4 lab_to_targetProofScript.sml:2138-2144: a proof *)

let align2_not_align3_4w = cake_theorem "align2_not_align3_4w"
  (fun () ->
    `~(alignment_aligned 3 x) /\ alignment_aligned 2 (x:'a word) /\
  dimindex (:'a) = 64 ==>
     x = byte_align x + (n2w 4) /\
     x + (n2w 1) = byte_align x + (n2w 5) /\
     x + (n2w 2) = byte_align x + (n2w 6) /\
     x + (n2w 3) = byte_align x + (n2w 7)`)
  CHEAT_TAC;;

let inst_lemma = cake_theorem "Inst_lemma"
  (fun () ->
    `~(failed (asm_inst i s1)) /\
      state_rel
        ((mc_conf:('a,'state,'b)machine_config),code2,labs,p) s1 t1 ms1
        /\
      (pos_val (labSem_state_pc s1 + 1) 0 code2 = pos_val
        (labSem_state_pc s1) 0 code2 + LENGTH bytes') ==>
      ~(failed (inst i t1)) /\
       (!a. ~(a IN labSem_state_mem_domain s1) ==> mem (inst i t1)
         a = asm_state_mem t1 a) /\
      (target_state_rel (machine_config_target mc_conf)
         (upd_pc (asm_state_pc t1 + n2w (LENGTH bytes')) (inst i
           t1)) ms2 ==>
       state_rel (mc_conf,code2,labs,p)
         (inc_pc (dec_clock (asm_inst i s1)))
         (upd_pc (asm_state_pc t1 + n2w (LENGTH (bytes':word8
           list))) (inst i t1)) ms2)`)
  CHEAT_TAC;;

(* compile correct *)

let line_length_MOD_0 = cake_theorem "line_length_MOD_0[local]"
  (fun () ->
    `encoder_correct (machine_config_target mc_conf) /\
       (~(EVEN p) ==> (asm_config_code_alignment (target_config
         (machine_config_target mc_conf)) = 0)) /\
       line_ok (target_config (machine_config_target mc_conf)) labs
         ffi_names p h ==>
       (line_length h MOD 2 EXP asm_config_code_alignment
         (target_config (machine_config_target mc_conf)) = 0)`)
  CHEAT_TAC;;

let pos_val_MOD_0_lemma = cake_theorem "pos_val_MOD_0_lemma[local]"
  (fun () ->
    `(0 MOD 2 EXP asm_config_code_alignment (target_config
  (machine_config_target mc_conf)) = 0)`)
  CHEAT_TAC;;

(* HOL4 lab_to_targetProofScript.sml:2955-2979: a theorem that HOL4
   states as the value of an ML expression: pos_val_MOD_0 *)

(* HOL4 lab_to_targetProofScript.sml:2981: the ML values that the
   definitions below antiquote *)

let EVEN_add_AND = cake_theorem "EVEN_add_AND"
  (fun () ->
    `((n2w 1) && p) = (n2w 0) /\
     EVEN x ==>
     ((n2w 1) && (p + n2w x)) = (n2w 0)`)
  CHEAT_TAC;;

let word_cmp_lemma = cake_theorem "word_cmp_lemma[local]"
  (fun () ->
    `state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
       (word_cmp cmp (labSem_state_regs s1 rr) (reg_imm ri s1) =
         SOME x) ==>
       (x = word_cmp cmp (asm_state_regs t1 rr) (reg_imm ri t1))`)
  CHEAT_TAC;;

let list_add_if_fresh_simp =
  cake_theorem "list_add_if_fresh_simp[local]"
  (fun () ->
    `!n s. list_add_if_fresh s l =
       (if find_index s l n = NONE then
         APPEND l [s] else l)`)
  CHEAT_TAC;;

let list_add_if_fresh_thm = cake_theorem "list_add_if_fresh_thm"
  (fun () ->
    `list_add_if_fresh s l =
      (if MEM s l then l else l ++ [s])`)
  CHEAT_TAC;;

(* HOL4 lab_to_targetProofScript.sml:3052: ML code, not ported *)

let find_index_append = cake_theorem "find_index_append[local]"
  (fun () ->
    `!n. find_index s (l ++ l') n =
     (match find_index s l n with NONE -> find_index s l' (n +
       LENGTH l) | SOME i -> SOME i)`)
  CHEAT_TAC;;

let has_io_name_find_index =
  cake_theorem "has_io_name_find_index[local]"
  (fun () ->
    `!l s.
     has_io_name s l ==> (?y. find_index (ffi_ExtCall s)
       (find_ffi_names l) 0 = SOME y)`)
  CHEAT_TAC;;

let find_index_in_range = cake_theorem "find_index_in_range[local]"
  (fun () ->
    `!n. find_index s l n = SOME x ==> x < n + LENGTH l /\ x >= n`)
  CHEAT_TAC;;

let find_index_in_range0 = cake_theorem "find_index_in_range0[local]"
  (fun () ->
    `find_index s l 0 = SOME x ==> x < LENGTH l /\ x >= 0`)
  CHEAT_TAC;;

let EL_get_ffi_index_MEM = cake_theorem "EL_get_ffi_index_MEM"
  (fun () ->
    `MEM s ls ==> EL (get_ffi_index ls s) ls = s`)
  CHEAT_TAC;;

let has_io_name_EXISTS = cake_theorem "has_io_name_EXISTS"
  (fun () ->
    `!name ls. has_io_name name ls <=>
      EXISTS (\x. match x with labLang_LabAsm (labLang_CallFFI i)
        _14 _15 _16 -> i = name | _17 -> F)
      (FLAT (MAP Section_lines ls))`)
  CHEAT_TAC;;

(* -- syntactic properties of remove_labels -- *)

(* annotated line length *)

let line_len_def = cake_define_list
  [`line_len (labLang_Label _20 _21 l) = l`;
   `line_len (labLang_Asm _22 _23 l) = l`;
   `line_len (labLang_LabAsm _24 _25 _26 l) = l`];;

(* annotated section length *)

let sec_length_add = cake_theorem "sec_length_add"
  (fun () ->
    `!ls n m. sec_length ls (n + m) = sec_length ls n + m`)
  CHEAT_TAC;;

let sec_length_sum_line_len = cake_theorem "sec_length_sum_line_len"
  (fun () ->
    `!ls n.
      sec_length ls n = SUM (MAP line_len ls) + n`)
  CHEAT_TAC;;

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

let enc_lines_again_simp_EQ =
  cake_theorem "enc_lines_again_simp_EQ[local]"
  (fun () ->
    `!labs ffis pos enc ls acc b.
     let (ls',flag) = enc_lines_again_simp labs ffis pos enc ls in
     enc_lines_again labs ffis pos enc ls (acc,b) = (REVERSE acc
       ++ ls',sec_length ls' pos,(b /\ flag))`)
  CHEAT_TAC;;

let enc_lines_again_simp_len = cake_theorem "enc_lines_again_simp_len"
  (fun () ->
    `!labs ffis pos enc lines res.
      enc_lines_again_simp labs ffis pos enc lines = (res,T) ==>
      MAP line_len res = MAP line_len lines`)
  CHEAT_TAC;;

let LENGTH_pad_bytes = cake_theorem "LENGTH_pad_bytes"
  (fun () ->
    `0 < LENGTH nop /\ LENGTH bytes <= l ==>
      LENGTH (pad_bytes bytes l nop) = l`)
  CHEAT_TAC;;

let section_labels_sec_length = cake_theorem "section_labels_sec_length"
  (fun () ->
    `!pos lines acc.
      FST (section_labels pos lines acc) = sec_length lines pos`)
  CHEAT_TAC;;

let section_labels_append = cake_theorem "section_labels_append"
  (fun () ->
    `!pos l1 labs l2.
      section_labels pos (l1 ++ l2) labs =
      section_labels (pos + (SUM (MAP line_len l1))) l2 (SND
        (section_labels pos l1 labs))`)
  CHEAT_TAC;;

let line_length_add_nop1 = cake_theorem "line_length_add_nop1"
  (fun () ->
    `!nop ls.
     ~(EVERY is_Label ls) ==>
     SUM (MAP line_length (add_nop nop ls)) =
     SUM (MAP line_length ls) + LENGTH nop`)
  CHEAT_TAC;;

let line_length_add_nop = cake_theorem "line_length_add_nop"
  (fun () ->
    `!nop ls.
     EVERY is_Label ls ==>
     SUM (MAP line_length (add_nop nop ls)) =
     SUM (MAP line_length ls)`)
  CHEAT_TAC;;

let line_len_add_nop1 = cake_theorem "line_len_add_nop1"
  (fun () ->
    `!nop ls. ~(EVERY is_Label ls) ==>
      SUM (MAP line_len (add_nop nop ls)) =
      SUM (MAP line_len ls) + 1`)
  CHEAT_TAC;;

let line_len_add_nop = cake_theorem "line_len_add_nop"
  (fun () ->
    `!nop ls. EVERY is_Label ls ==>
      SUM (MAP line_len (add_nop nop ls)) =
      SUM (MAP line_len ls)`)
  CHEAT_TAC;;

let add_nop_append = cake_theorem "add_nop_append"
  (fun () ->
    `!nop l1 l2.
      add_nop nop (l1 ++ l2) = (if EVERY is_Label l1 then l1 ++
        add_nop nop l2 else add_nop nop l1 ++ l2)`)
  CHEAT_TAC;;

let EXISTS_not_Label_add_nop =
  cake_theorem "EXISTS_not_Label_add_nop[simp]"
  (fun () ->
    `!nop acc.
       EXISTS ((~) o is_Label) (add_nop nop acc) <=> EXISTS ((~)
         o is_Label) acc`)
  CHEAT_TAC;;

let EVERY_is_Label_add_nop_preserved =
  cake_theorem "EVERY_is_Label_add_nop_preserved[simp]"
  (fun () ->
    `!nop acc.
       EVERY is_Label (add_nop nop acc) <=> EVERY is_Label acc`)
  CHEAT_TAC;;

let EVERY_is_Label_add_nop = cake_theorem "EVERY_is_Label_add_nop"
  (fun () ->
    `!nop ls. EVERY is_Label ls ==> add_nop nop ls = ls`)
  CHEAT_TAC;;

let SND_lines_upd_lab_len = cake_theorem "SND_lines_upd_lab_len"
  (fun () ->
    `!pos lines acc.
       SND (lines_upd_lab_len pos lines acc) = (
       pos + SUM (MAP line_len (FST (lines_upd_lab_len pos lines
         acc)))) - SUM (MAP line_len acc)`)
  CHEAT_TAC;;

(* code_similar preservation *)

let line_similar_add_nop = cake_theorem "line_similar_add_nop[local]"
  (fun () ->
    `!ls ls' h.
     LIST_REL line_similar ls ls' ==>
     LIST_REL line_similar ls (add_nop h ls')`)
  CHEAT_TAC;;

let line_similar_pad_section = cake_theorem "line_similar_pad_section"
  (fun () ->
    `!nop l2 aux l1.
       LIST_REL line_similar l1 (REVERSE aux ++ l2) ==>
       LIST_REL line_similar l1 (pad_section nop l2 aux)`)
  CHEAT_TAC;;

let code_similar_pad_code = cake_theorem "code_similar_pad_code"
  (fun () ->
    `!code1 code2.
     code_similar code1 code2 ==>
     code_similar code1 (pad_code nop code2)`)
  CHEAT_TAC;;

let LIST_REL_enc_line = cake_theorem "LIST_REL_enc_line[local]"
  (fun () ->
    `!ls ls'.
     LIST_REL line_similar ls ls' <=>
     LIST_REL line_similar (MAP (enc_line enc len) ls) ls'`)
  CHEAT_TAC;;

let code_similar_enc_sec_list =
  cake_theorem "code_similar_enc_sec_list[simp]"
  (fun () ->
    `!code1 code2 n.
       code_similar (enc_sec_list n code1) code2 <=>
       code_similar code1 code2`)
  CHEAT_TAC;;

let enc_lines_again_IMP_similar =
  cake_theorem "enc_lines_again_IMP_similar[local]"
  (fun () ->
    `!labs ffis pos enc lines acc ok lines' ok' curr.
     enc_lines_again labs ffis pos enc lines (acc,ok) =
       (lines',ok') ==>
     LIST_REL line_similar curr (REVERSE acc) ==>
     LIST_REL line_similar (curr ++ lines) lines'`)
  CHEAT_TAC;;

let enc_secs_again_IMP_similar =
  cake_theorem "enc_secs_again_IMP_similar"
  (fun () ->
    `!pos labs ffis enc code code1 ok.
     enc_secs_again pos labs ffis enc code = (code1,ok) ==>
       code_similar code code1`)
  CHEAT_TAC;;

(* HOL4 lab_to_targetProofScript.sml:3402-3408: a theorem that HOL4
   states as the value of an ML expression: lines_upd_lab_len_AUX *)

let line_similar_lines_upd_lab_len =
  cake_theorem "line_similar_lines_upd_lab_len[local]"
  (fun () ->
    `!l aux pos l1.
         LIST_REL line_similar (FST (lines_upd_lab_len pos l []))
           l1 =
         LIST_REL line_similar l l1`)
  CHEAT_TAC;;

let code_similar_upd_lab_len = cake_theorem "code_similar_upd_lab_len"
  (fun () ->
    `!code pos code1.
        code_similar (upd_lab_len pos code) code1 = code_similar
          code code1`)
  CHEAT_TAC;;

let lines_upd_lab_len_similar = cake_theorem "lines_upd_lab_len_similar"
  (fun () ->
    `!pos lines aux.
      LIST_REL line_similar (FST (lines_upd_lab_len pos lines
        aux)) (REVERSE aux ++ lines)`)
  CHEAT_TAC;;

(* implications of code_similar *)

let code_similar_MAP_Section_num =
  cake_theorem "code_similar_MAP_Section_num"
  (fun () ->
    `!c1 c2.
     code_similar c1 c2 ==>
     MAP Section_num c1 = MAP Section_num c2`)
  CHEAT_TAC;;

let code_similar_extract_labels =
  cake_theorem "code_similar_extract_labels"
  (fun () ->
    `!code1 code2. code_similar code1 code2 ==>
     MAP (extract_labels o Section_lines) code1 =
     MAP (extract_labels o Section_lines) code2`)
  CHEAT_TAC;;

let code_similar_loc_to_pc = cake_theorem "code_similar_loc_to_pc"
  (fun () ->
    `!l1 l2 c1 c2. code_similar c1 c2 ==>
       loc_to_pc l1 l2 c1 = loc_to_pc l1 l2 c2`)
  CHEAT_TAC;;

(* sec_label_ok preservation *)

let enc_sec_list_sec_labels_ok =
  cake_theorem "enc_sec_list_sec_labels_ok"
  (fun () ->
    `!enc code.
     EVERY sec_labels_ok code ==> EVERY sec_labels_ok
       (enc_sec_list enc code)`)
  CHEAT_TAC;;

let enc_lines_again_sec_labels_ok =
  cake_theorem "enc_lines_again_sec_labels_ok[local]"
  (fun () ->
    `!labs ffis pos enc lines acc ok res ok' k.
       enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok')
         /\
       EVERY (sec_label_ok k) acc /\
       EVERY (sec_label_ok k) lines ==>
       EVERY (sec_label_ok k) res`)
  CHEAT_TAC;;

let enc_secs_again_sec_labels_ok =
  cake_theorem "enc_secs_again_sec_labels_ok"
  (fun () ->
    `!pos ffis labs enc ls res ok k.
      enc_secs_again pos ffis labs enc ls = (res,ok) /\ EVERY
        sec_labels_ok ls ==>
      EVERY sec_labels_ok res`)
  CHEAT_TAC;;

let lines_upd_lab_len_sec_label_ok =
  cake_theorem "lines_upd_lab_len_sec_label_ok[local]"
  (fun () ->
    `!pos lines acc k.
        EVERY (sec_label_ok k) lines /\
        EVERY (sec_label_ok k) acc ==>
        EVERY (sec_label_ok k) (FST (lines_upd_lab_len pos lines
          acc))`)
  CHEAT_TAC;;

let upd_lab_len_sec_labels_ok = cake_theorem "upd_lab_len_sec_labels_ok"
  (fun () ->
    `!n ls. EVERY sec_labels_ok ls ==> EVERY sec_labels_ok
  (upd_lab_len n ls)`)
  CHEAT_TAC;;

let add_nop_sec_label_ok = cake_theorem "add_nop_sec_label_ok[local]"
  (fun () ->
    `!nop aux.
       EVERY (sec_label_ok k) aux ==>
       EVERY (sec_label_ok k) (add_nop nop aux)`)
  CHEAT_TAC;;

let pad_section_sec_label_ok =
  cake_theorem "pad_section_sec_label_ok[local]"
  (fun () ->
    `!nop xs acc k.
       EVERY (sec_label_ok k) xs /\
       EVERY (sec_label_ok k) acc ==>
       EVERY (sec_label_ok k) (pad_section nop xs acc)`)
  CHEAT_TAC;;

let pad_code_sec_labels_ok = cake_theorem "pad_code_sec_labels_ok"
  (fun () ->
    `!nop code.
      EVERY sec_labels_ok code ==>
      EVERY sec_labels_ok (pad_code nop code)`)
  CHEAT_TAC;;

let sec_labels_ok_filter_skip =
  cake_theorem "sec_labels_ok_filter_skip[simp]"
  (fun () ->
    `!code. EVERY sec_labels_ok (filter_skip code) <=> EVERY
  sec_labels_ok code`)
  CHEAT_TAC;;

(* invariant: lines are encoded and non-label lengths annotated *)

let line_encd0_def = cake_define
  `line_encd0 enc x2 =
        match x2 with
          labLang_Asm b bytes len ->
       enc (cbw_to_asm b) = bytes /\ len = LENGTH bytes
        | (labLang_LabAsm l w bytes len) ->
        enc (lab_inst w l) = bytes /\ LENGTH bytes <= len /\
        (?w'. len = LENGTH (enc (lab_inst w' l)))
        | _27 -> T`;;

let sec_encd0_def = cake_define
  `sec_encd0 enc (Section _28 ls) = EVERY (line_encd0 enc) ls`;;

(* HOL4 lab_to_targetProofScript.sml:3628: the overload all_encd0,
   which the port expands *)

(* establishing encd0 *)

let enc_sec_list_encd0 = cake_theorem "enc_sec_list_encd0"
  (fun () ->
    `!ls. (\enc l. EVERY (sec_encd0 enc) l) enc (enc_sec_list enc ls)`)
  CHEAT_TAC;;

(* encd0 preservation *)

let enc_lines_again_encd0 = cake_theorem "enc_lines_again_encd0"
  (fun () ->
    `!labs ffis pos enc lines acc ok res ok'.
      enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok')
        /\
      EVERY (line_encd0 enc) lines /\
      EVERY (line_encd0 enc) acc ==>
      EVERY (line_encd0 enc) res`)
  CHEAT_TAC;;

let enc_secs_again_encd0 = cake_theorem "enc_secs_again_encd0"
  (fun () ->
    `!pos labs ffis enc ls res ok.
      enc_secs_again pos labs ffis enc ls = (res,ok) /\
      (\enc l. EVERY (sec_encd0 enc) l) enc ls ==>
      (\enc l. EVERY (sec_encd0 enc) l) enc res`)
  CHEAT_TAC;;

let lines_upd_lab_len_encd0 = cake_theorem "lines_upd_lab_len_encd0"
  (fun () ->
    `!pos ls acc.
      EVERY (line_encd0 enc) ls /\
      EVERY (line_encd0 enc) acc ==>
      EVERY (line_encd0 enc) (FST (lines_upd_lab_len pos ls acc))`)
  CHEAT_TAC;;

let upd_lab_len_encd0 = cake_theorem "upd_lab_len_encd0"
  (fun () ->
    `!pos ss. (\enc l. EVERY (sec_encd0 enc) l) enc ss ==> (\enc l.
  EVERY (sec_encd0 enc) l) enc (upd_lab_len pos ss)`)
  CHEAT_TAC;;

(* invariant: annotated lengths are not too small *)
(* this is a consequence of encd (below) and not treated separately much *)

let line_length_leq_def = cake_define
  `line_length_leq x1 =
        match x1 with
          labLang_LabAsm _29 _30 bytes l ->
       LENGTH bytes <= l
        | (labLang_Asm _31 bytes l) ->
       LENGTH bytes <= l
        | _32 -> T`;;

let sec_length_leq_def = cake_define
  `sec_length_leq (Section _33 ls) = EVERY line_length_leq ls`;;

(* HOL4 lab_to_targetProofScript.sml:3713: the overload
   all_length_leq, which the port expands *)

(* invariant: label annotated lengths are 0 or 1 *)

let label_one_def = cake_define
  `label_one x1 =
        match x1 with
          labLang_Label _36 _37 n -> n <= 1
        | _38 -> T`;;

let sec_label_one_def = cake_define
  `sec_label_one (Section _39 ls) = EVERY label_one ls`;;

(* establishing label_one *)

let lines_upd_lab_len_label_one =
  cake_theorem "lines_upd_lab_len_label_one"
  (fun () ->
    `!pos ls acc.
      EVERY label_one acc ==>
      EVERY label_one (FST (lines_upd_lab_len pos ls acc))`)
  CHEAT_TAC;;

let upd_lab_len_label_one = cake_theorem "upd_lab_len_label_one"
  (fun () ->
    `!pos ss. EVERY sec_label_one (upd_lab_len pos ss)`)
  CHEAT_TAC;;

(* label_one preservation *)

let enc_lines_again_simp_label_one =
  cake_theorem "enc_lines_again_simp_label_one"
  (fun () ->
    `!labs ffis pos enc ls res ok.
      enc_lines_again_simp labs ffis pos enc ls = (res,ok) /\
      EVERY label_one ls ==>
      EVERY label_one res`)
  CHEAT_TAC;;

let enc_secs_again_label_one = cake_theorem "enc_secs_again_label_one"
  (fun () ->
    `!pos labs ffis enc lines res ok.
      enc_secs_again pos labs ffis enc lines = (res,ok) /\
      EVERY sec_label_one lines ==>
      EVERY sec_label_one res`)
  CHEAT_TAC;;

(* simple consequences of label_one *)

let line_length_pad_section1 = cake_theorem "line_length_pad_section1"
  (fun () ->
    `!nop ls acc.
     LENGTH nop = 1 /\
     EVERY label_one ls /\
     EVERY line_length_leq ls /\
     ~(EVERY is_Label acc) /\
     SUM (MAP line_length acc) = SUM (MAP line_len acc) ==>
     SUM (MAP line_length (pad_section nop ls acc)) =
     SUM (MAP line_len ls) + SUM (MAP line_len acc)`)
  CHEAT_TAC;;

let line_len_pad_section1 = cake_theorem "line_len_pad_section1"
  (fun () ->
    `!nop xs aux.
     LENGTH nop = 1 /\
     EVERY label_one xs /\
     ~(EVERY is_Label aux) ==>
     SUM (MAP line_len (pad_section nop xs aux)) =
     SUM (MAP line_len xs) + SUM (MAP line_len aux)`)
  CHEAT_TAC;;

(* invariant: lines are encoded and annotated lengths are correct *)

let line_encd_def = cake_define
  `line_encd enc labs ffis pos x5 =
        match x5 with
          labLang_Asm b bytes len ->
       enc (cbw_to_asm b) = bytes /\ len = LENGTH bytes
        | (labLang_LabAsm labLang_Halt _40 bytes len) ->
       enc (Jump (--(n2w (pos + ffi_offset)))) = bytes /\
       LENGTH bytes <= len
        | (labLang_LabAsm Install _41 bytes len) ->
       enc (Jump (--(n2w (pos + 2 * ffi_offset)))) = bytes /\
       LENGTH bytes <= len
        | (labLang_LabAsm (labLang_CallFFI s) _42 bytes len) ->
       enc (Jump (--(n2w (pos + (get_ffi_index ffis (ffi_ExtCall s) +
         3) * ffi_offset)))) = bytes /\
       LENGTH bytes <= len
        | (labLang_LabAsm (Jump l) _43 bytes len) ->
       enc (Jump (n2w (find_pos l labs) + --(n2w pos))) = bytes /\
       LENGTH bytes <= len
        | (labLang_LabAsm (JumpCmp a b c l) _44 bytes len) ->
       enc (JumpCmp a b c (n2w (find_pos l labs) + --(n2w pos))) =
         bytes /\
       LENGTH bytes <= len
        | (labLang_LabAsm (LocValue k l) _45 bytes len) ->
       enc (Loc k (n2w (find_pos l labs) + --(n2w pos))) = bytes /\
       LENGTH bytes <= len
        | (labLang_LabAsm (Call l) _46 bytes len) ->
       enc (Call (n2w (find_pos l labs) + --(n2w pos))) = bytes /\
       LENGTH bytes <= len
        | _47 -> T`;;

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

let line_encd_length_leq = cake_theorem "line_encd_length_leq"
  (fun () ->
    `!enc labs ffis pos l. line_encd enc labs ffis pos l ==>
  line_length_leq l`)
  CHEAT_TAC;;

let lines_encd_length_leq = cake_theorem "lines_encd_length_leq"
  (fun () ->
    `!enc labs ffis pos ls. lines_encd enc labs ffis pos ls ==> EVERY
  line_length_leq ls`)
  CHEAT_TAC;;

let all_encd_length_leq = cake_theorem "all_encd_length_leq"
  (fun () ->
    `!enc labs ffis pos ls. all_encd enc labs ffis pos ls ==> (\l.
  EVERY sec_length_leq l) ls`)
  CHEAT_TAC;;

(* establishing encd *)

let enc_lines_again_simp_encd = cake_theorem "enc_lines_again_simp_encd"
  (fun () ->
    `!labs ffis pos enc lines res.
      enc_lines_again_simp labs ffis pos enc lines = (res,T) /\
      EVERY label_one lines /\
      EVERY (line_encd0 enc) lines ==>
      lines_encd enc labs ffis pos res`)
  CHEAT_TAC;;

let enc_secs_again_encd = cake_theorem "enc_secs_again_encd"
  (fun () ->
    `!pos labs ffis enc ls res.
      enc_secs_again pos labs ffis enc ls = (res,T) /\
      EVERY sec_label_one ls /\
      EVERY (sec_encd0 enc) ls ==>
      all_encd enc labs ffis pos res`)
  CHEAT_TAC;;

(* invariant: annotated lengths are correct *)

let line_length_ok_def = cake_define
  `line_length_ok l <=> LENGTH (line_bytes l) = line_len l`;;

let sec_length_ok_def = cake_define
  `sec_length_ok (Section _48 ls) = EVERY line_length_ok ls`;;

(* simple consequences of length_ok *)

let sec_length_sum_line_length =
  cake_theorem "sec_length_sum_line_length"
  (fun () ->
    `!ls n.
      EVERY line_length_ok ls ==>
      (sec_length ls n = SUM (MAP line_length ls) + n)`)
  CHEAT_TAC;;

(* invariant: all labels annotated with length 0 *)

let label_zero_def = cake_define
  `label_zero x1 =
        match x1 with
          labLang_Label _51 _52 n -> n = 0
        | _53 -> T`;;

let sec_label_zero_def = cake_define
  `sec_label_zero (Section _54 ls) = EVERY label_zero ls`;;

(* label_zero preservation *)

let EVERY_label_zero_add_nop =
  cake_theorem "EVERY_label_zero_add_nop[local]"
  (fun () ->
    `!xs. EVERY label_zero (add_nop nop xs) = EVERY label_zero xs`)
  CHEAT_TAC;;

let EVERY_label_zero_pad_section =
  cake_theorem "EVERY_label_zero_pad_section[simp]"
  (fun () ->
    `!nop xs aux.
       EVERY label_zero aux ==>
       EVERY label_zero (pad_section nop xs aux)`)
  CHEAT_TAC;;

let EVERY_sec_label_zero_pad_code =
  cake_theorem "EVERY_sec_label_zero_pad_code[simp]"
  (fun () ->
    `!nop ls. EVERY sec_label_zero (pad_code nop ls)`)
  CHEAT_TAC;;

let enc_lines_again_simp_label_zero =
  cake_theorem "enc_lines_again_simp_label_zero"
  (fun () ->
    `!labs ffis pos enc ls res ok.
      enc_lines_again_simp labs ffis pos enc ls = (res,ok) /\
      EVERY label_zero ls ==>
      EVERY label_zero res`)
  CHEAT_TAC;;

let enc_secs_again_label_zero = cake_theorem "enc_secs_again_label_zero"
  (fun () ->
    `!pos labs ffis enc lines res ok.
      enc_secs_again pos labs ffis enc lines = (res,ok) /\
      EVERY sec_label_zero lines ==>
      EVERY sec_label_zero res`)
  CHEAT_TAC;;

let lines_upd_lab_len_encd0_label_zero =
  cake_theorem "lines_upd_lab_len_encd0_label_zero"
  (fun () ->
    `!pos lines aux.
      enc_ok c /\ enc = asm_config_encode c /\
        ~(asm_config_code_alignment c = 0) /\
      EVERY (line_encd0 enc) lines /\ EVEN pos /\
      EVERY label_zero aux ==>
      EVERY label_zero (FST (lines_upd_lab_len pos lines aux))`)
  CHEAT_TAC;;

let EVEN_sec_length_lines_upd_lab_len =
  cake_theorem "EVEN_sec_length_lines_upd_lab_len"
  (fun () ->
    `!pos lines acc.
      (if NULL lines then
       EVEN pos /\ EVEN (SUM (MAP line_len acc)) else is_Label
         (LAST lines) /\
           EVEN (pos + (SUM (MAP line_len acc)))) ==>
      EVEN (SUM (MAP line_len (FST (lines_upd_lab_len pos lines
        acc))))`)
  CHEAT_TAC;;

let upd_lab_len_encd0_label_zero =
  cake_theorem "upd_lab_len_encd0_label_zero"
  (fun () ->
    `!pos code.
      enc_ok c /\ enc = asm_config_encode c /\
        ~(asm_config_code_alignment c = 0) /\
      (\enc l. EVERY (sec_encd0 enc) l) enc code /\ EVEN pos /\
        EVERY sec_ends_with_label code ==>
      EVERY sec_label_zero (upd_lab_len pos code)`)
  CHEAT_TAC;;

(* simple consequences of label_zero *)

let sec_pos_val_0 = cake_theorem "sec_pos_val_0"
  (fun () ->
    `!pos lines. ~(EVERY is_Label lines) /\ EVERY label_zero lines ==>
  sec_pos_val 0 pos lines = SOME pos`)
  CHEAT_TAC;;

let line_len_pad_section0 = cake_theorem "line_len_pad_section0"
  (fun () ->
    `!nop ls aux.
     EVERY label_zero ls ==>
     SUM (MAP line_len (pad_section nop ls aux)) =
     SUM (MAP line_len ls) + SUM (MAP line_len aux)`)
  CHEAT_TAC;;

let sec_label_zero_pos_val_0 = cake_theorem "sec_label_zero_pos_val_0"
  (fun () ->
    `!xs pos.
     EVERY sec_label_zero xs ==>
     pos_val 0 pos xs = pos`)
  CHEAT_TAC;;

let all_enc_ok_imp_sec_label_zero =
  cake_theorem "all_enc_ok_imp_sec_label_zero"
  (fun () ->
    `!conf labs ffis n code.
     all_enc_ok conf labs ffis n code ==>
     EVERY sec_label_zero code`)
  CHEAT_TAC;;

(* invariant: lines aligned *)

let line_aligned_def = cake_define
  `line_aligned m l <=>
     line_len l MOD m = 0 /\
     line_length l MOD m = 0`;;

let sec_aligned_def = cake_define
  `sec_aligned noplen (Section _55 ls) = EVERY (line_aligned noplen)
  ls`;;

(* establishing aligned *)

let all_encd0_aligned = cake_theorem "all_encd0_aligned"
  (fun () ->
    `!c enc code.
     enc_ok c /\ enc = asm_config_encode c /\
     (\enc l. EVERY (sec_encd0 enc) l) enc code /\
     EVERY sec_label_zero code ==>
     EVERY (sec_aligned (LENGTH (enc (Inst asm_Skip)))) code`)
  CHEAT_TAC;;

(* aligned preservation *)

let enc_lines_again_simp_aligned =
  cake_theorem "enc_lines_again_simp_aligned"
  (fun () ->
    `!labs ffis pos enc ls res ok.
      (!a. LENGTH (enc a) MOD len = 0) /\
      enc_lines_again_simp labs ffis pos enc ls = (res,ok) /\
      EVERY (line_aligned len) ls ==>
      EVERY (line_aligned len) res`)
  CHEAT_TAC;;

let enc_secs_again_aligned = cake_theorem "enc_secs_again_aligned"
  (fun () ->
    `!pos labs ffis enc lines res ok.
      (!a. LENGTH (enc a) MOD len = 0) /\
      enc_secs_again pos labs ffis enc lines = (res,ok) /\
      EVERY (sec_aligned len) lines ==>
      EVERY (sec_aligned len) res`)
  CHEAT_TAC;;

(* invariant: all initial labels have annotated length 0 *)

let label_prefix_zero_def = cake_define
  `label_prefix_zero ls <=>
      (!n. n < LENGTH ls /\ (!m. m <= n ==> is_Label (EL m ls)) ==>
         (!m. m <= n ==> line_len (EL m ls) = 0))`;;

let sec_label_prefix_zero_def = cake_define
  `sec_label_prefix_zero (Section k ls) <=> label_prefix_zero ls`;;

let label_prefix_zero_cons = cake_theorem "label_prefix_zero_cons"
  (fun () ->
    `(label_prefix_zero (labLang_Label l1 l2 len :: ls) <=> ((len = 0)
  /\ label_prefix_zero ls)) /\
     (label_prefix_zero (labLang_Asm a b c :: ls) <=> T) /\
     (label_prefix_zero (labLang_LabAsm d e f g :: ls) <=> T)`)
  CHEAT_TAC;;

(* establishing label_prefix_zero *)

let label_prefix_zero_append_suff =
  cake_theorem "label_prefix_zero_append_suff"
  (fun () ->
    `!l1 l2.
     label_prefix_zero l1 /\ label_prefix_zero l2 ==>
     label_prefix_zero (l1 ++ l2)`)
  CHEAT_TAC;;

let label_prefix_zero_append_suff2 =
  cake_theorem "label_prefix_zero_append_suff2"
  (fun () ->
    `!l1 l2.
     label_prefix_zero l1 /\ EXISTS ((~) o is_Label) l1 ==>
     label_prefix_zero (l1 ++ l2)`)
  CHEAT_TAC;;

let lines_upd_lab_len_label_prefix_zero =
  cake_theorem "lines_upd_lab_len_label_prefix_zero"
  (fun () ->
    `!pos ls acc.
      (EVERY is_Label acc ==> EVEN pos) /\ label_prefix_zero
        (REVERSE acc) ==>
      label_prefix_zero (FST (lines_upd_lab_len pos ls acc))`)
  CHEAT_TAC;;

let upd_lab_len_label_prefix_zero =
  cake_theorem "upd_lab_len_label_prefix_zero"
  (fun () ->
    `!pos ss.
      EVEN pos /\ EVERY sec_ends_with_label ss ==>
      EVERY sec_label_prefix_zero (upd_lab_len pos ss)`)
  CHEAT_TAC;;

(* label_prefix_zero preservation *)

let enc_lines_again_simp_label_prefix_zero =
  cake_theorem "enc_lines_again_simp_label_prefix_zero"
  (fun () ->
    `!labs ffis pos enc ls res ok.
      enc_lines_again_simp labs ffis pos enc ls = (res,ok) /\
      label_prefix_zero ls ==>
      label_prefix_zero res`)
  CHEAT_TAC;;

let enc_secs_again_label_prefix_zero =
  cake_theorem "enc_secs_again_label_prefix_zero"
  (fun () ->
    `!pos labs ffis enc lines res ok.
      enc_secs_again pos labs ffis enc lines = (res,ok) /\
      EVERY sec_label_prefix_zero lines ==>
      EVERY sec_label_prefix_zero res`)
  CHEAT_TAC;;

(* simple consequences of label_prefix_zero *)

let line_length_pad_section = cake_theorem "line_length_pad_section"
  (fun () ->
    `!nop ls acc.
     LENGTH nop = 1 /\
     EVERY label_one ls /\
     EVERY line_length_leq ls /\
     SUM (MAP line_length acc) = SUM (MAP line_len acc) /\
     EVERY is_Label acc /\ label_prefix_zero ls ==>
     SUM (MAP line_length (pad_section nop ls acc)) =
     SUM (MAP line_len ls) + SUM (MAP line_len acc)`)
  CHEAT_TAC;;

let label_zero_line_length_pad_section =
  cake_theorem "label_zero_line_length_pad_section"
  (fun () ->
    `!nop ls acc.
     0 < LENGTH nop /\
     EVERY label_zero ls /\
     MAP line_length acc = MAP line_len acc /\
     EVERY line_length_leq ls ==>
     MAP line_length (pad_section nop ls acc) =
     MAP line_len (REVERSE acc ++ ls)`)
  CHEAT_TAC;;

(* invariant: lines encd with nops *)

let line_enc_with_nop_def = cake_define
  `line_enc_with_nop enc labs ffis pos x5 =
        match x5 with
          labLang_Asm b bytes len ->
       enc_with_nop enc (cbw_to_asm b) bytes /\ LENGTH bytes = len
        | (labLang_LabAsm labLang_Halt _56 bytes len) ->
       enc_with_nop enc (Jump (--(n2w (pos + ffi_offset)))) bytes /\
       LENGTH bytes = len
        | (labLang_LabAsm Install _57 bytes len) ->
       enc_with_nop enc (Jump (--(n2w (pos + 2 * ffi_offset)))) bytes
         /\
       LENGTH bytes = len
        | (labLang_LabAsm (labLang_CallFFI s) _58 bytes len) ->
       enc_with_nop enc (Jump (--(n2w (pos + (get_ffi_index ffis
         (ffi_ExtCall s) + 3) * ffi_offset)))) bytes /\
       LENGTH bytes = len
        | (labLang_LabAsm (Jump l) _59 bytes len) ->
       enc_with_nop enc (Jump (n2w (find_pos l labs) + --(n2w pos)))
         bytes /\
       LENGTH bytes = len
        | (labLang_LabAsm (JumpCmp a b c l) _60 bytes len) ->
       enc_with_nop enc (JumpCmp a b c (n2w (find_pos l labs) +
         --(n2w pos))) bytes /\
       LENGTH bytes = len
        | (labLang_LabAsm (LocValue k l) _61 bytes len) ->
       enc_with_nop enc (Loc k (n2w (find_pos l labs) + --(n2w pos)))
         bytes /\
       LENGTH bytes = len
        | (labLang_LabAsm _62 _63 bytes len) -> LENGTH bytes = len
        | (labLang_Label _64 _65 len) -> len = 0`;;

(* HOL4 lab_to_targetProofScript.sml:4357: ML code, not ported *)

let lines_enc_with_nop_def = cake_define_list
  [`lines_enc_with_nop enc labs ffis pos [] <=> T`;
   `lines_enc_with_nop enc labs ffis pos (l :: ls) <=>
       line_enc_with_nop enc labs ffis pos l /\
       lines_enc_with_nop enc labs ffis (pos + line_length l)
         ls`];;

let lines_enc_with_nop_append = cake_theorem "lines_enc_with_nop_append"
  (fun () ->
    `!enc labs ffis pos l1 l2.
     lines_enc_with_nop enc labs ffis pos (l1 ++ l2) <=>
     lines_enc_with_nop enc labs ffis pos l1 /\
     lines_enc_with_nop enc labs ffis (pos + SUM (MAP line_length
       l1)) l2`)
  CHEAT_TAC;;

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

let all_enc_with_nop_alt = cake_theorem "all_enc_with_nop_alt"
  (fun () ->
    `(all_enc_with_nop enc labs ffis pos [] <=> T) /\
     (all_enc_with_nop enc labs ffis pos (Section k ls :: ss) <=>
      lines_enc_with_nop enc labs ffis pos ls /\
      all_enc_with_nop enc labs ffis (pos + SUM (MAP line_length
        ls)) ss)`)
  CHEAT_TAC;;

(* enc_with_nop implies length_ok *)

let line_enc_with_nop_length_ok =
  cake_theorem "line_enc_with_nop_length_ok"
  (fun () ->
    `!enc labs ffis pos line.
      line_enc_with_nop enc labs ffis pos line ==> line_length_ok
        line`)
  CHEAT_TAC;;

let lines_enc_with_nop_length_ok =
  cake_theorem "lines_enc_with_nop_length_ok"
  (fun () ->
    `!enc labs ffis pos ls. lines_enc_with_nop enc labs ffis pos ls
  ==> EVERY line_length_ok ls`)
  CHEAT_TAC;;

(* enc_with_nop implies label_zero *)

let line_enc_with_nop_label_zero =
  cake_theorem "line_enc_with_nop_label_zero"
  (fun () ->
    `!enc labs ffis pos line.
      line_enc_with_nop enc labs ffis pos line ==> label_zero
        line`)
  CHEAT_TAC;;

let lines_enc_with_nop_label_zero =
  cake_theorem "lines_enc_with_nop_label_zero"
  (fun () ->
    `!enc labs ffis pos lines.
       lines_enc_with_nop enc labs ffis pos lines ==> EVERY
         label_zero lines`)
  CHEAT_TAC;;

let all_enc_with_nop_label_zero =
  cake_theorem "all_enc_with_nop_label_zero"
  (fun () ->
    `!enc labs ffis pos ls.
      all_enc_with_nop enc labs ffis pos ls ==>
      EVERY sec_label_zero ls`)
  CHEAT_TAC;;

(* line_ok implies enc_with_nop *)

let line_ok_line_enc_with_nop = cake_theorem "line_ok_line_enc_with_nop"
  (fun () ->
    `!c labs ffis pos line.
      line_ok c labs ffis pos line ==>
      line_enc_with_nop (asm_config_encode c) labs ffis pos line`)
  CHEAT_TAC;;

let lines_ok_lines_enc_with_nop =
  cake_theorem "lines_ok_lines_enc_with_nop"
  (fun () ->
    `!c labs ffis pos lines.
      lines_ok c labs ffis pos lines ==>
      lines_enc_with_nop (asm_config_encode c) labs ffis pos
        lines`)
  CHEAT_TAC;;

(* establishing enc_with_nop *)

let enc_with_nop_pad_bytes_length =
  cake_theorem "enc_with_nop_pad_bytes_length"
  (fun () ->
    `enc_with_nop enc x (pad_bytes (enc x) (LENGTH (enc x)) (enc (Inst
  asm_Skip)))`)
  CHEAT_TAC;;

let enc_with_nop_pad_bytes = cake_theorem "enc_with_nop_pad_bytes"
  (fun () ->
    `nop = enc (Inst asm_Skip) /\ LENGTH (enc x) <= len /\
     LENGTH (enc x) MOD (LENGTH nop) = 0 /\
     len MOD (LENGTH nop) = 0 /\
     0 < LENGTH nop ==> enc_with_nop enc x (pad_bytes (enc x) len
       nop)`)
  CHEAT_TAC;;

let lines_enc_with_nop_add_nop =
  cake_theorem "lines_enc_with_nop_add_nop"
  (fun () ->
    `!enc labs ffis pos ls.
      LENGTH (enc (Inst asm_Skip)) = 1 /\
      lines_enc_with_nop enc labs ffis pos (REVERSE ls) ==>
      lines_enc_with_nop enc labs ffis pos
        (REVERSE (add_nop (enc (Inst asm_Skip)) ls))`)
  CHEAT_TAC;;

let lines_enc_with_nop_pad_section1 =
  cake_theorem "lines_enc_with_nop_pad_section1"
  (fun () ->
    `!nop code aux pos.
      nop = enc (Inst asm_Skip) /\ LENGTH nop = 1 /\
      lines_encd enc labs ffis (pos + (SUM (MAP line_len aux)))
        code /\
      lines_enc_with_nop enc labs ffis pos (REVERSE aux) /\
      ~(EVERY is_Label aux) /\
      EVERY label_one code ==>
      lines_enc_with_nop enc labs ffis pos (pad_section nop code
        aux)`)
  CHEAT_TAC;;

let lines_enc_with_nop_pad_section01 =
  cake_theorem "lines_enc_with_nop_pad_section01"
  (fun () ->
    `!nop code aux pos.
      nop = enc (Inst asm_Skip) /\ 0 < LENGTH nop /\
      EVERY (line_aligned (LENGTH nop)) code /\
      lines_encd enc labs ffis (pos + SUM (MAP line_len aux)) code
        /\
      lines_enc_with_nop enc labs ffis pos (REVERSE aux) /\
      ~(EVERY is_Label aux) /\ EVERY label_zero code ==>
      lines_enc_with_nop enc labs ffis pos (pad_section nop code
        aux)`)
  CHEAT_TAC;;

let lines_enc_with_nop_pad_section0 =
  cake_theorem "lines_enc_with_nop_pad_section0"
  (fun () ->
    `!nop code aux pos.
      nop = enc (Inst asm_Skip) /\ 0 < LENGTH nop /\
      EVERY (line_aligned (LENGTH nop)) code /\
      lines_encd enc labs ffis (pos + SUM (MAP line_len aux)) code
        /\
      lines_enc_with_nop enc labs ffis pos (REVERSE aux) /\
      EVERY is_Label aux /\ EVERY label_zero code ==>
      lines_enc_with_nop enc labs ffis pos (pad_section nop code
        aux)`)
  CHEAT_TAC;;

let lines_enc_with_nop_pad_section =
  cake_theorem "lines_enc_with_nop_pad_section"
  (fun () ->
    `!nop code aux pos.
      nop = enc (Inst asm_Skip) /\ LENGTH nop = 1 /\
      lines_encd enc labs ffis (pos + SUM (MAP line_len aux)) code
        /\
      lines_enc_with_nop enc labs ffis pos (REVERSE aux) /\
      EVERY is_Label aux /\ EVERY label_one code /\
        label_prefix_zero code ==>
      lines_enc_with_nop enc labs ffis pos (pad_section nop code
        aux)`)
  CHEAT_TAC;;

let all_enc_with_nop_pad_code = cake_theorem "all_enc_with_nop_pad_code"
  (fun () ->
    `!nop code pos.
     0 < LENGTH nop /\ nop = enc (Inst asm_Skip) /\
     (~(LENGTH nop = 1) ==> EVERY (sec_aligned (LENGTH nop)) code
       /\ EVERY sec_label_zero code) /\
     EVERY sec_label_one code /\
     EVERY sec_length_leq code /\
     EVERY sec_label_prefix_zero code /\
     all_encd enc labs ffis pos code ==>
     all_enc_with_nop enc labs ffis pos (pad_code nop code)`)
  CHEAT_TAC;;

(* invariant: label annotation correctly records alignment *)

let line_lab_len_pos_ok_def = cake_define
  `line_lab_len_pos_ok pos x2 =
        match x2 with
          labLang_Label _68 _69 l ->
        (if EVEN pos then l = 0 else l = 1)
        | _70 -> T`;;

let lab_len_pos_ok_def = cake_define_list
  [`lab_len_pos_ok pos [] <=> T`;
   `lab_len_pos_ok pos (l :: ls) <=>
         line_lab_len_pos_ok pos l /\
         lab_len_pos_ok (pos + line_len l) ls`];;

let lab_len_pos_ok_append = cake_theorem "lab_len_pos_ok_append"
  (fun () ->
    `!l1 pos l2.
     lab_len_pos_ok pos (l1 ++ l2) <=>
     lab_len_pos_ok pos l1 /\
     lab_len_pos_ok (pos + SUM (MAP line_len l1)) l2`)
  CHEAT_TAC;;

let all_lab_len_pos_ok_def = cake_define_list
  [`all_lab_len_pos_ok _71 [] <=> T`;
   `all_lab_len_pos_ok pos (Section k ls :: ss) <=>
       lab_len_pos_ok pos ls /\
       all_lab_len_pos_ok (pos + sec_length ls 0) ss`];;

(* HOL4 lab_to_targetProofScript.sml:4714: ML code, not ported *)

(* establishing pos_ok *)

let lines_upd_lab_len_pos_ok = cake_theorem "lines_upd_lab_len_pos_ok"
  (fun () ->
    `!pos lines.
      lab_len_pos_ok pos (FST (lines_upd_lab_len pos lines []))`)
  CHEAT_TAC;;

let upd_lab_len_pos_ok = cake_theorem "upd_lab_len_pos_ok"
  (fun () ->
    `!pos code.
      all_lab_len_pos_ok pos (upd_lab_len pos code)`)
  CHEAT_TAC;;

(* pos_ok preservation *)

let enc_lines_again_simp_pos_ok =
  cake_theorem "enc_lines_again_simp_pos_ok"
  (fun () ->
    `!labs ffis pos enc lines res.
      enc_lines_again_simp labs ffis pos enc lines = (res,T) /\
      lab_len_pos_ok pos lines ==>
      lab_len_pos_ok pos res`)
  CHEAT_TAC;;

let enc_secs_again_pos_ok = cake_theorem "enc_secs_again_pos_ok"
  (fun () ->
    `!pos labs ffis enc code res.
      enc_secs_again pos labs ffis enc code = (res,T) /\
      all_lab_len_pos_ok pos code ==>
      all_lab_len_pos_ok pos res`)
  CHEAT_TAC;;

let lab_len_pos_ok_even_prefix_zero =
  cake_theorem "lab_len_pos_ok_even_prefix_zero"
  (fun () ->
    `!pos ls.
      EVEN pos /\
      lab_len_pos_ok pos ls ==>
      label_prefix_zero ls`)
  CHEAT_TAC;;

let pad_section_pos_ok = cake_theorem "pad_section_pos_ok"
  (fun () ->
    `!nop lines aux pos.
      lab_len_pos_ok (pos + SUM (MAP line_len aux)) lines /\
      lab_len_pos_ok pos (REVERSE aux) /\
      EVERY label_zero aux /\
      ((NULL aux \/ is_Label (HD aux)) ==> label_prefix_zero lines)
        ==>
      lab_len_pos_ok pos (pad_section nop lines aux)`)
  CHEAT_TAC;;

let line_len_pad_section = cake_theorem "line_len_pad_section"
  (fun () ->
    `!nop xs aux.
      LENGTH nop = 1 /\
      EVERY label_one xs /\
      (EVERY is_Label aux ==> label_prefix_zero xs) ==>
      SUM (MAP line_len (pad_section nop xs aux)) =
      SUM (MAP line_len xs) + SUM (MAP line_len aux)`)
  CHEAT_TAC;;

let all_lab_len_pos_ok_pad_code =
  cake_theorem "all_lab_len_pos_ok_pad_code"
  (fun () ->
    `!nop code pos.
      all_lab_len_pos_ok pos code /\
      (~(LENGTH nop = 1) ==> EVERY sec_label_zero code) /\
      EVERY sec_label_one code /\
      EVERY sec_label_prefix_zero code ==>
      all_lab_len_pos_ok pos (pad_code nop code)`)
  CHEAT_TAC;;

(* invariant: jump offsets ok *)

let line_offset_ok_def = cake_define
  `line_offset_ok labs ffis pos x4 =
        match x4 with
          labLang_LabAsm a w bytes _72 ->
       w = get_jump_offset a ffis labs pos
        | _73 -> T`;;

let lines_offset_ok_def = cake_define_list
  [`lines_offset_ok labs ffis pos [] <=> T`;
   `lines_offset_ok labs ffis pos (l :: ls) <=>
       line_offset_ok labs ffis pos l /\
       lines_offset_ok labs ffis (pos + line_len l) ls`];;

let lines_offset_ok_append = cake_theorem "lines_offset_ok_append"
  (fun () ->
    `!labs ffis pos l1 l2.
      lines_offset_ok labs ffis pos (l1 ++ l2) <=>
      lines_offset_ok labs ffis pos l1 /\
      lines_offset_ok labs ffis (pos + SUM (MAP line_len l1)) l2`)
  CHEAT_TAC;;

let offset_ok_def = cake_define_list
  [`lab_to_targetProof_offset_ok labs ffis pos [] <=> T`;
   `lab_to_targetProof_offset_ok labs ffis pos (Section k ls :: ss) <=>
       lines_offset_ok labs ffis pos ls /\
       lab_to_targetProof_offset_ok labs ffis (pos + SUM (MAP
         line_len ls)) ss`];;
hol4_overload "offset_ok" "lab_to_targetProof_offset_ok";;

(* HOL4 lab_to_targetProofScript.sml:4892: ML code, not ported *)

(* establishing offset_ok *)

let enc_lines_again_simp_offset_ok =
  cake_theorem "enc_lines_again_simp_offset_ok"
  (fun () ->
    `!labs ffis pos enc lines res ok.
      enc_lines_again_simp labs ffis pos enc lines = (res,ok) ==>
      lines_offset_ok labs ffis pos res`)
  CHEAT_TAC;;

let enc_secs_again_offset_ok = cake_theorem "enc_secs_again_offset_ok"
  (fun () ->
    `!pos labs ffis enc ls res ok.
      enc_secs_again pos labs ffis enc ls = (res,ok) ==>
      offset_ok labs ffis pos res`)
  CHEAT_TAC;;

(* offset_ok preservation *)

let lines_offset_ok_pad_section =
  cake_theorem "lines_offset_ok_pad_section"
  (fun () ->
    `!nop lines aux labs ffis pos.
      lab_len_pos_ok (pos + SUM (MAP line_len aux)) lines /\
      lab_len_pos_ok pos (REVERSE aux) /\ EVERY label_zero aux /\
      (~(NULL lines) /\ is_Label (HD lines) /\ line_len (HD lines)
        = 1 ==>
       ~(NULL aux) /\ ~(is_Label (HD aux))) /\
      lines_offset_ok labs ffis pos (REVERSE aux ++ lines) ==>
      lines_offset_ok labs ffis pos (pad_section nop lines aux)`)
  CHEAT_TAC;;

let offset_ok_pad_code = cake_theorem "offset_ok_pad_code"
  (fun () ->
    `!labs ffis pos code.
      (~(LENGTH nop = 1) ==> EVERY sec_label_zero code) /\
      EVERY sec_label_one code /\
      EVERY sec_label_prefix_zero code /\
      all_lab_len_pos_ok pos code /\
      offset_ok labs ffis pos code ==>
      offset_ok labs ffis pos (pad_code nop code)`)
  CHEAT_TAC;;

(* invariant: referenced labels exist *)

let line_labs_exist_def = cake_define
  `line_labs_exist labs x2 =
        match x2 with
          labLang_LabAsm a _74 _75 _76 ->
       (!n1 n2. (n1,n2) IN labs_of a ==> ~(lab_lookup n1 n2 labs =
         NONE))
        | _77 -> T`;;

(* HOL4 lab_to_targetProofScript.sml:4998: ML code, not ported *)

let sec_labs_exist_def = cake_define
  `sec_labs_exist labs (Section _78 ls) <=> EVERY (line_labs_exist
  labs) ls`;;

(* HOL4 lab_to_targetProofScript.sml:5004: the overload
   all_labs_exist, which the port expands *)

(* Remove tail recursion from zero_labs_acc_exist *)
let zero_labs_acc_of_eq_zero_labs_of =
  cake_theorem "zero_labs_acc_of_eq_zero_labs_of[local]"
  (fun () ->
    `domain (zero_labs_acc_of l acc) =
     IMAGE FST (restrict_zero (labs_of l)) UNION domain acc`)
  CHEAT_TAC;;

let line_get_zero_labs_acc_eq_line_get_zero_labels =
  cake_theorem "line_get_zero_labs_acc_eq_line_get_zero_labels[local]"
  (fun () ->
    `domain (line_get_zero_labs_acc l acc) =
     IMAGE FST (restrict_zero (line_get_labels l)) UNION domain
       acc`)
  CHEAT_TAC;;

let sec_get_zero_labs_acc_eq_sec_get_zero_labels =
  cake_theorem "sec_get_zero_labs_acc_eq_sec_get_zero_labels[local]"
  (fun () ->
    `domain (sec_get_zero_labs_acc sec acc) =
     IMAGE FST (restrict_zero (sec_get_labels sec)) UNION domain
       acc`)
  CHEAT_TAC;;

let get_zero_labs_acc_eq_get_zero_labels =
  cake_theorem "get_zero_labs_acc_eq_get_zero_labels[local]"
  (fun () ->
    `domain (ITLIST sec_get_zero_labs_acc code acc) =
     IMAGE FST (restrict_zero (get_labels code)) UNION domain acc`)
  CHEAT_TAC;;

let zero_labs_acc_exist_eq = cake_theorem "zero_labs_acc_exist_eq"
  (fun () ->
    `zero_labs_acc_exist labs code <=>
     restrict_zero (get_labels code) SUBSET labs_domain labs`)
  CHEAT_TAC;;

(* labs_exist preservation *)
let line_similar_line_labs_exist =
  cake_theorem "line_similar_line_labs_exist"
  (fun () ->
    `!l1 l2. line_similar l1 l2 ==> (line_labs_exist labs l1 <=>
  line_labs_exist labs l2)`)
  CHEAT_TAC;;

let code_similar_all_labs_exist =
  cake_theorem "code_similar_all_labs_exist"
  (fun () ->
    `!c1 c2. code_similar c1 c2 ==> ((\labs code. EVERY
  (sec_labs_exist labs) code) labs c1 <=> (\labs code. EVERY
  (sec_labs_exist labs) code) labs c2)`)
  CHEAT_TAC;;

let all_labs_exist_pad_code =
  cake_theorem "all_labs_exist_pad_code[simp]"
  (fun () ->
    `!nop code. (\labs code. EVERY (sec_labs_exist labs) code) labs
  (pad_code nop code) <=> (\labs code. EVERY (sec_labs_exist labs)
  code) labs code`)
  CHEAT_TAC;;

let enc_lines_again_line_labs_exist =
  cake_theorem "enc_lines_again_line_labs_exist"
  (fun () ->
    `!labs ffis pos enc lines acc ok res ok' k.
     enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok')
       /\
     EVERY (line_labs_exist labs') acc /\
     EVERY (line_labs_exist labs') lines ==>
     EVERY (line_labs_exist labs') res`)
  CHEAT_TAC;;

let enc_secs_again_all_labs_exist =
  cake_theorem "enc_secs_again_all_labs_exist"
  (fun () ->
    `!pos ffis labs enc ls res ok k.
      enc_secs_again pos ffis labs enc ls = (res,ok) /\ (\labs
        code. EVERY (sec_labs_exist labs) code) labs' ls ==>
      (\labs code. EVERY (sec_labs_exist labs) code) labs' res`)
  CHEAT_TAC;;

let upd_lab_len_all_labs_exist =
  cake_theorem "upd_lab_len_all_labs_exist"
  (fun () ->
    `!pos code. (\labs code. EVERY (sec_labs_exist labs) code) labs
  (upd_lab_len pos code) <=> (\labs code. EVERY (sec_labs_exist labs)
  code) labs code`)
  CHEAT_TAC;;

(* establishing labs_exist *)

let line_similar_line_get_code_labels =
  cake_theorem "line_similar_line_get_code_labels"
  (fun () ->
    `!l1 l2. line_similar l1 l2 ==> line_get_code_labels l1 =
  line_get_code_labels l2`)
  CHEAT_TAC;;

let code_similar_get_code_labels =
  cake_theorem "code_similar_get_code_labels"
  (fun () ->
    `!c1 c2. code_similar c1 c2 ==> get_code_labels c1 =
  get_code_labels c2`)
  CHEAT_TAC;;

let line_labs_exist_get_labels =
  cake_theorem "line_labs_exist_get_labels"
  (fun () ->
    `!labs line. line_labs_exist labs line <=> line_get_labels line
  SUBSET labs_domain labs`)
  CHEAT_TAC;;

let sec_labs_exist_get_labels = cake_theorem "sec_labs_exist_get_labels"
  (fun () ->
    `!labs sec. sec_labs_exist labs sec <=> sec_get_labels sec SUBSET
  labs_domain labs`)
  CHEAT_TAC;;

let all_labs_exist_get_labels = cake_theorem "all_labs_exist_get_labels"
  (fun () ->
    `(\labs code. EVERY (sec_labs_exist labs) code) labs code <=>
  get_labels code SUBSET labs_domain labs`)
  CHEAT_TAC;;

let line_similar_line_get_labels =
  cake_theorem "line_similar_line_get_labels"
  (fun () ->
    `!l1 l2. line_similar l1 l2 ==> (line_get_labels l1 =
  line_get_labels l2)`)
  CHEAT_TAC;;

let code_similar_get_labels = cake_theorem "code_similar_get_labels"
  (fun () ->
    `!c1 c2. code_similar c1 c2 ==> get_labels c1 = get_labels c2`)
  CHEAT_TAC;;

let get_labels_upd_lab_len = cake_theorem "get_labels_upd_lab_len[simp]"
  (fun () ->
    `get_labels (upd_lab_len pos code) = get_labels code`)
  CHEAT_TAC;;

let section_labels_line_get_code_labels =
  cake_theorem "section_labels_line_get_code_labels"
  (fun () ->
    `!pos lines aux new_pos labs. section_labels pos lines aux =
  (new_pos,labs) ==>
     0 INSERT set_of_list (MAP FST labs) = 0 INSERT (set_of_list
       (MAP FST aux) UNION BIGUNION (IMAGE line_get_code_labels
       (set_of_list lines)))`)
  CHEAT_TAC;;

let labs_domain_compute_labels_alt =
  cake_theorem "labs_domain_compute_labels_alt"
  (fun () ->
    `!pos code labs.
       ALL_DISTINCT (MAP Section_num code) /\
       DISJOINT (domain labs) (set_of_list (MAP Section_num code))
         ==>
       labs_domain (compute_labels_alt pos code labs) =
       get_code_labels code UNION labs_domain labs`)
  CHEAT_TAC;;

(* invariant: labels aligned at even positions *)

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let even_labels_def = cake_define_list_cheat CHEAT_TAC
  [`even_labels pos [] <=> T`;
   `even_labels pos (Section _79 [] :: ls) <=> even_labels pos ls`;
   `even_labels pos (Section k (y :: ys) :: ls) <=>
       (is_Label y ==> EVEN pos) /\
       even_labels (pos + line_len y) (Section k ys :: ls)`];;

(* HOL4 lab_to_targetProofScript.sml:5229: ML code, not ported *)

let lines_even_labels_def = cake_define_list
  [`lines_even_labels pos [] <=> T`;
   `lines_even_labels pos (y :: ys) <=>
       (is_Label y ==> EVEN pos) /\
       lines_even_labels (pos + line_len y) ys`];;

let even_labels_alt = cake_theorem "even_labels_alt"
  (fun () ->
    `(even_labels pos [] <=> T) /\
     (even_labels pos (Section _80 ls :: ss) <=>
      lines_even_labels pos ls /\
      even_labels (pos + SUM (MAP line_len ls)) ss)`)
  CHEAT_TAC;;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let even_labels_strong_def = cake_define_list_cheat CHEAT_TAC
  [`even_labels_strong pos [] <=> T`;
   `even_labels_strong pos (Section _81 [] :: ls) <=>
        EVEN pos /\ even_labels_strong pos ls`;
   `even_labels_strong pos (Section k (y :: ys) :: ls) <=>
       (is_Label y ==> EVEN pos) /\
       even_labels_strong (pos + line_len y) (Section k ys ::
         ls)`];;

let even_labels_ends_imp_strong =
  cake_theorem "even_labels_ends_imp_strong"
  (fun () ->
    `!pos code.
      even_labels pos code /\
      EVERY sec_ends_with_label code /\
      EVERY sec_label_zero code ==>
      even_labels_strong pos code`)
  CHEAT_TAC;;

let ALOOKUP_section_labels_ignore =
  cake_theorem "ALOOKUP_section_labels_ignore"
  (fun () ->
    `!pos lines acc.
     ~(MEM n2 (MAP SND (extract_labels lines))) ==>
     ALOOKUP (SND (section_labels pos lines acc)) n2 =
     ALOOKUP acc n2`)
  CHEAT_TAC;;

let lines_ok_section_lab_lookup_even =
  cake_theorem "lines_ok_section_lab_lookup_even"
  (fun () ->
    `!pos lines acc.
     lines_ok c labs ffis pos lines /\
     (!l2 x. ALOOKUP acc l2 = SOME x ==> EVEN x) /\
     ALOOKUP (SND (section_labels pos lines acc)) l2 = SOME x ==>
     EVEN x`)
  CHEAT_TAC;;

let all_enc_ok_split = cake_theorem "all_enc_ok_split[local]"
  (fun () ->
    `!c labs ffis pos k lines xs.
     all_enc_ok c labs ffis pos (Section k lines :: xs) ==>
     all_enc_ok c labs ffis pos [Section k lines] /\
     all_enc_ok c labs ffis (pos + sec_length lines 0) xs`)
  CHEAT_TAC;;

let all_enc_ok_even = cake_theorem "all_enc_ok_even[local]"
  (fun () ->
    `!lines pos.
     all_enc_ok c labs ffis pos [Section k lines] ==>
     EVEN (sec_length lines pos)`)
  CHEAT_TAC;;

let all_enc_ok_lab_lookup_even =
  cake_theorem "all_enc_ok_lab_lookup_even[local]"
  (fun () ->
    `!c labs ffis pos sec_list l1 l2 acc x.
         all_enc_ok c labs ffis pos sec_list /\
         lab_lookup l1 l2 (compute_labels_alt pos sec_list acc) =
           SOME x /\
         (!x. lab_lookup l1 l2 acc = SOME x ==> EVEN x) /\
         EVEN pos ==>
         EVEN x`)
  CHEAT_TAC;;

let line_ok_pre_light_imp_line_ok =
  cake_theorem "line_ok_pre_light_imp_line_ok"
  (fun () ->
    `!c labs ffis pos line.
       line_ok_pre c line /\
       line_enc_with_nop (asm_config_encode c) labs ffis pos line
         /\
       line_offset_ok labs ffis pos line /\
       line_labs_exist labs line /\
       line_ok_light c line /\ (is_Label line ==> EVEN pos) ==>
       line_ok c labs ffis pos line`)
  CHEAT_TAC;;

let all_enc_ok_pre_light_imp_all_enc_ok =
  cake_theorem "all_enc_ok_pre_light_imp_all_enc_ok"
  (fun () ->
    `!c labs ffis pos code.
      all_enc_with_nop (asm_config_encode c) labs ffis pos code /\
      (\c ls. EVERY (sec_ok_pre c) ls) c code /\
      (\c ls. EVERY (sec_ok_light c) ls) c code /\
      even_labels_strong pos code /\
      (\labs code. EVERY (sec_labs_exist labs) code) labs code /\
      offset_ok labs ffis pos code ==>
      all_enc_ok c labs ffis pos code`)
  CHEAT_TAC;;

(* HOL4 lab_to_targetProofScript.sml:5405-5413: code that the source
   has in a comment *)

let upd_lab_len_ends_with_label =
  cake_theorem "upd_lab_len_ends_with_label"
  (fun () ->
    `!pos ss.
      EVERY sec_ends_with_label ss ==>
      EVERY sec_ends_with_label (upd_lab_len pos ss)`)
  CHEAT_TAC;;

let lab_lookup_compute_labels_alt_ignore =
  cake_theorem "lab_lookup_compute_labels_alt_ignore"
  (fun () ->
    `!pos secs acc.
     ~(MEM n1 (MAP Section_num secs)) ==>
     lab_lookup n1 n2 (compute_labels_alt pos secs acc) =
       lab_lookup n1 n2 acc`)
  CHEAT_TAC;;

let ALOOKUP_section_labels = cake_theorem "ALOOKUP_section_labels"
  (fun () ->
    `!pos lines acc pc'.
     EVERY (sec_label_ok n1) lines /\
     EVERY line_length_ok lines /\
     EVERY label_zero lines /\
     ALL_DISTINCT (extract_labels lines) /\
     sec_loc_to_pc n2 lines = SOME pc' /\ ~(n2 = 0) ==>
     (?i.
       ALOOKUP (SND (section_labels pos lines acc)) n2 = SOME i /\
       ((sec_pos_val pc' pos lines = NONE /\
         i = pos + SUM (MAP line_length lines) /\
         pc' = LENGTH (FILTER ((~) o is_Label) lines)) \/
        sec_pos_val pc' pos lines = SOME i))`)
  CHEAT_TAC;;

let lab_lookup_compute_labels_test =
  cake_theorem "lab_lookup_compute_labels_test[local]"
  (fun () ->
    `!pos sec_list acc l1 l2 x2 c labs ffis nop.
         EVERY sec_labels_ok sec_list /\
         ALL_DISTINCT (MAP Section_num sec_list) /\
         EVERY (ALL_DISTINCT o extract_labels o Section_lines)
           sec_list /\
         EVERY sec_label_zero sec_list /\
         all_enc_ok c labs ffis pos sec_list /\
         loc_to_pc l1 l2 sec_list = SOME x2 ==>
         lab_lookup l1 l2 (compute_labels_alt pos sec_list acc) =
         SOME (pos_val x2 pos sec_list)`)
  CHEAT_TAC;;

let enc_lines_again_simp_ends_with_label =
  cake_theorem "enc_lines_again_simp_ends_with_label"
  (fun () ->
    `!labs ffis pos enc ls res ok.
      enc_lines_again_simp labs ffis pos enc ls = (res,ok) /\
      ~(NULL ls) /\ is_Label (LAST ls) ==>
      ~(NULL res) /\ is_Label (LAST res)`)
  CHEAT_TAC;;

let enc_secs_again_ends_with_label =
  cake_theorem "enc_secs_again_ends_with_label"
  (fun () ->
    `!pos labs ffis enc lines res ok.
      enc_secs_again pos labs ffis enc lines = (res,ok) /\
      EVERY sec_ends_with_label lines ==>
      EVERY sec_ends_with_label res`)
  CHEAT_TAC;;

let enc_sec_list_ends_with_label =
  cake_theorem "enc_sec_list_ends_with_label"
  (fun () ->
    `!enc code.
     EVERY sec_ends_with_label code ==>
     EVERY sec_ends_with_label (enc_sec_list enc code)`)
  CHEAT_TAC;;

let lines_even_labels_append = cake_theorem "lines_even_labels_append"
  (fun () ->
    `!l1 l2 pos.
      lines_even_labels pos (l1 ++ l2) <=>
      lines_even_labels pos l1 /\
      lines_even_labels (pos + SUM (MAP line_len l1)) l2`)
  CHEAT_TAC;;

let label_zero_pos_ok_lines_even_labels =
  cake_theorem "label_zero_pos_ok_lines_even_labels"
  (fun () ->
    `!pos ls.
      EVERY label_zero ls /\
      lab_len_pos_ok pos ls ==>
      lines_even_labels pos ls`)
  CHEAT_TAC;;

let label_zero_pos_ok_even_labels =
  cake_theorem "label_zero_pos_ok_even_labels"
  (fun () ->
    `!pos code.
     EVERY sec_label_zero code /\
     all_lab_len_pos_ok pos code ==>
     even_labels pos code`)
  CHEAT_TAC;;

(*
  val code = ``[Label a1 b1 0; Label a2 b2 0; Asm x3 [b3] 1; Label a4 b4 1; Label a5 b5 0]``
  EVAL ``lab_len_pos_ok 0 ^code``
  EVAL ``(pad_section nop ^code [])``
  EVAL ``lab_len_pos_ok 0 (pad_section nop ^code [])``

  [Label a1 b1 0; Label a2 b2 0; Asm x3 [b3] 1; Label a4 b4 1; Label a5 b5 0]
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

let pad_code_ends_with_label = cake_theorem "pad_code_ends_with_label"
  (fun () ->
    `!nop ls.
      EVERY sec_ends_with_label ls ==>
      EVERY sec_ends_with_label (pad_code nop ls)`)
  CHEAT_TAC;;

let enc_lines_again_section_labels =
  cake_theorem "enc_lines_again_section_labels"
  (fun () ->
    `!labs ffis pos enc lines res acc.
      enc_lines_again_simp labs ffis pos enc lines = (res,T) ==>
      section_labels pos lines acc = section_labels pos res acc`)
  CHEAT_TAC;;

let enc_secs_again_compute_labels =
  cake_theorem "enc_secs_again_compute_labels"
  (fun () ->
    `!pos labs ffis enc secs res acc.
     enc_secs_again pos labs ffis enc secs = (res,T) ==>
     compute_labels_alt pos res acc =
     compute_labels_alt pos secs acc`)
  CHEAT_TAC;;

(*
  val code = ``[Label 1 1 0; Label 1 2 0; Asm x3 [b3] 1; Label 1 3 1; Label 1 4 0]``
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

let pad_section_labels = cake_theorem "pad_section_labels"
  (fun () ->
    `!nop lines aux pos labs.
      lab_len_pos_ok (pos + SUM (MAP line_len aux)) lines /\
      lab_len_pos_ok pos (REVERSE aux) /\ EVERY label_zero aux /\
      (~(NULL lines) /\ is_Label (HD lines) /\ line_len (HD lines)
        = 1 ==>
       ~(NULL aux) /\ ~(is_Label (HD aux))) ==>
      section_labels pos (pad_section nop lines aux) labs =
      section_labels pos (REVERSE aux ++ lines) labs`)
  CHEAT_TAC;;

let pad_code_compute_labels = cake_theorem "pad_code_compute_labels"
  (fun () ->
    `!pos code acc.
      EVERY sec_label_one code /\
      (~(LENGTH nop = 1) ==> EVERY sec_label_zero code) /\
      EVERY sec_label_prefix_zero code /\
      all_lab_len_pos_ok pos code ==>
      compute_labels_alt pos (pad_code nop code) acc =
      compute_labels_alt pos code acc`)
  CHEAT_TAC;;

let enc_lines_again_all_enc_ok_pre =
  cake_theorem "enc_lines_again_all_enc_ok_pre[local]"
  (fun () ->
    `!labs ffis pos enc lines acc ok res ok' c.
     enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok')
       /\
     EVERY (line_ok_pre c) lines /\ EVERY (line_ok_pre c) acc ==>
     EVERY (line_ok_pre c) res`)
  CHEAT_TAC;;

let enc_secs_again_all_enc_ok_pre =
  cake_theorem "enc_secs_again_all_enc_ok_pre[local]"
  (fun () ->
    `!pos labs ffis enc ls res ok c.
     enc_secs_again pos labs ffis enc ls = (res,ok) /\ (\c ls.
       EVERY (sec_ok_pre c) ls) c ls ==>
     (\c ls. EVERY (sec_ok_pre c) ls) c res`)
  CHEAT_TAC;;

let line_ok_pre_add_nop = cake_theorem "line_ok_pre_add_nop[local]"
  (fun () ->
    `EVERY (line_ok_pre c) xs ==>
     EVERY (line_ok_pre c) (add_nop nop xs)`)
  CHEAT_TAC;;

let line_ok_pre_pad_section =
  cake_theorem "line_ok_pre_pad_section[local]"
  (fun () ->
    `!nop xs acc c.
     EVERY (line_ok_pre c) xs /\ EVERY (line_ok_pre c) acc ==>
     EVERY (line_ok_pre c) (pad_section nop xs acc)`)
  CHEAT_TAC;;

let all_enc_ok_pre_pad_code =
  cake_theorem "all_enc_ok_pre_pad_code[local]"
  (fun () ->
    `!nop code c.
     (\c ls. EVERY (sec_ok_pre c) ls) c code ==>
     (\c ls. EVERY (sec_ok_pre c) ls) c (pad_code nop code)`)
  CHEAT_TAC;;

let all_enc_ok_pre_lines_upd_lab_len =
  cake_theorem "all_enc_ok_pre_lines_upd_lab_len[local]"
  (fun () ->
    `!n lines acc.
     EVERY (line_ok_pre c) lines /\
     EVERY (line_ok_pre c) acc ==>
     EVERY (line_ok_pre c) (FST (lines_upd_lab_len n lines acc))`)
  CHEAT_TAC;;

let all_enc_ok_pre_upd_lab_len =
  cake_theorem "all_enc_ok_pre_upd_lab_len[local]"
  (fun () ->
    `!n code.
     (\c ls. EVERY (sec_ok_pre c) ls) c code ==>
     (\c ls. EVERY (sec_ok_pre c) ls) c (upd_lab_len n code)`)
  CHEAT_TAC;;

let EXP_IMP_ZERO_LT = cake_theorem "EXP_IMP_ZERO_LT[local]"
  (fun () ->
    `(2 EXP y = x) ==> 0 < x`)
  CHEAT_TAC;;

let line_ok_alignment = cake_theorem "line_ok_alignment"
  (fun () ->
    `!c labs ffis pos line.
     enc_ok c /\
     line_ok c labs ffis pos line /\ ODD (line_length line) ==>
       asm_config_code_alignment c = 0`)
  CHEAT_TAC;;

let has_odd_inst_alignment = cake_theorem "has_odd_inst_alignment"
  (fun () ->
    `!c labs ffis pos code.
     enc_ok c /\
     all_enc_ok c labs ffis pos code /\ has_odd_inst code ==>
       asm_config_code_alignment c = 0`)
  CHEAT_TAC;;

let remove_labels_loop_thm =
  cake_theorem "remove_labels_loop_thm[local]"
  (fun () ->
    `!n c init_pos init_labs ffis code code2 labs.
       remove_labels_loop n c init_pos init_labs ffis code = SOME
         (code2,labs) /\
       EVERY sec_ends_with_label code /\
       EVERY sec_labels_ok code /\
       ALL_DISTINCT (MAP Section_num code) /\
       EVERY (ALL_DISTINCT o extract_labels o Section_lines) code
         /\
       DISJOINT (domain init_labs) (set_of_list (MAP Section_num
         code)) /\
       // TODO this is stronger:
       // get_labels code ⊆ get_code_labels code ∪ labs_domain init_labs ∧
       restrict_nonzero (get_labels code) SUBSET get_code_labels
         code UNION labs_domain init_labs /\
       (\c ls. EVERY (sec_ok_pre c) ls) c code /\
       // new loop invariant
       (\enc l. EVERY (sec_encd0 enc) l) (asm_config_encode c) code
         /\
       enc_ok c /\
       EVEN init_pos /\
       (!l1 l2. OPTION_ALL EVEN (lab_lookup l1 l2 init_labs)) ==>
       (\c ls. EVERY (sec_ok_pre c) ls) c code2 /\
       EVERY sec_labels_ok code2 /\
       all_enc_ok c labs ffis init_pos code2 /\
       code_similar code code2 /\
       (has_odd_inst code2 ==> asm_config_code_alignment c = 0) /\
       (!l1 l2 x. lab_lookup l1 l2 labs = SOME x ==> EVEN x) /\
       (!l1 l2 x. lab_lookup l1 l2 init_labs = SOME x ==>
                  lab_lookup l1 l2 labs = SOME x) /\
       (!l1 l2 x2.
         loc_to_pc l1 l2 code = SOME x2 ==>
         lab_lookup l1 l2 labs = SOME (pos_val x2 init_pos
           code2))`)
  CHEAT_TAC;;

let loc_to_pc_enc_sec_list = cake_theorem "loc_to_pc_enc_sec_list[simp]"
  (fun () ->
    `!l1 l2 code.
       loc_to_pc l1 l2 (enc_sec_list e code) = loc_to_pc l1 l2
         code`)
  CHEAT_TAC;;

let all_enc_ok_pre_enc_sec_list =
  cake_theorem "all_enc_ok_pre_enc_sec_list[local]"
  (fun () ->
    `!code enc c.
     (\c ls. EVERY (sec_ok_pre c) ls) c code ==>
     (\c ls. EVERY (sec_ok_pre c) ls) c (enc_sec_list enc code)`)
  CHEAT_TAC;;

let remove_labels_thm = cake_theorem "remove_labels_thm"
  (fun () ->
    `remove_labels clock conf init_pos init_labs ffi_names code = SOME
  (code2,labs) /\
     enc_ok conf /\
     EVERY sec_ends_with_label code /\
     EVERY sec_labels_ok code /\
     ALL_DISTINCT (MAP Section_num code) /\
     EVERY (ALL_DISTINCT o extract_labels o Section_lines) code /\
     DISJOINT (domain init_labs) (set_of_list (MAP Section_num
       code)) /\
     restrict_nonzero (get_labels code) SUBSET get_code_labels code
       UNION labs_domain init_labs /\
     (\c ls. EVERY (sec_ok_pre c) ls) conf code /\
     EVEN init_pos /\
     (!l1 l2. OPTION_ALL EVEN (lab_lookup l1 l2 init_labs)) ==>
     all_enc_ok conf labs ffi_names init_pos code2 /\
     code_similar code code2 /\
     (has_odd_inst code2 ==> asm_config_code_alignment conf = 0) /\
     (!l1 l2 x. lab_lookup l1 l2 labs = SOME x ==> EVEN x) /\
     (!l1 l2 x. lab_lookup l1 l2 init_labs = SOME x ==>
                lab_lookup l1 l2 labs = SOME x) /\
     (!l1 l2 x2.
       loc_to_pc l1 l2 code = SOME x2 ==>
       lab_lookup l1 l2 labs = SOME (pos_val x2 init_pos code2))`)
  CHEAT_TAC;;

let compute_labels_alt_domain_labs =
  cake_theorem "compute_labels_alt_domain_labs"
  (fun () ->
    `!pos code labs.
       domain (compute_labels_alt pos code labs) =
       IMAGE FST (get_code_labels code) UNION domain labs`)
  CHEAT_TAC;;

let remove_labels_loop_domain_labs =
  cake_theorem "remove_labels_loop_domain_labs"
  (fun () ->
    `!a b c d e f g h. remove_labels_loop a b c d e f = SOME (g,h) ==>
     domain h = IMAGE FST (get_code_labels f) UNION domain d`)
  CHEAT_TAC;;

let remove_labels_domain_labs = cake_theorem "remove_labels_domain_labs"
  (fun () ->
    `remove_labels c t k init_labs f p = SOME (q,labs) ==>
     domain labs = IMAGE FST (get_code_labels p) UNION domain
       init_labs`)
  CHEAT_TAC;;

(** End syntactic stuff **)

let LENGTH_prog_to_bytes = cake_theorem "LENGTH_prog_to_bytes"
  (fun () ->
    `!code n c labs ffi pos.
     all_enc_ok c labs ffi pos code ==>
     FOLDL (\pos sec. sec_length (Section_lines sec) pos) n code =
     LENGTH (prog_to_bytes code) + n`)
  CHEAT_TAC;;

let LENGTH_prog_to_bytes2 = cake_theorem "LENGTH_prog_to_bytes2"
  (fun () ->
    `!code n c labs ffi pos.
     all_enc_ok c labs ffi pos code ==>
     SUM (MAP (SUM o MAP line_length o Section_lines) code) =
     LENGTH (prog_to_bytes code)`)
  CHEAT_TAC;;

let prog_to_bytes_APPEND = cake_theorem "prog_to_bytes_APPEND"
  (fun () ->
    `prog_to_bytes (c1 ++ c2) = prog_to_bytes c1 ++ prog_to_bytes c2`)
  CHEAT_TAC;;

let line_ok_line_byte_length = cake_theorem "line_ok_line_byte_length"
  (fun () ->
    `line_ok c labs ffi n l ==>
     LENGTH (line_bytes l) = line_length l`)
  CHEAT_TAC;;

let lines_ok_MAP_line_byte_length =
  cake_theorem "lines_ok_MAP_line_byte_length"
  (fun () ->
    `!ls c labs ffi n.
     lines_ok c labs ffi n ls ==>
     MAP LENGTH (MAP line_bytes ls) = MAP line_length ls`)
  CHEAT_TAC;;

let all_enc_ok_prog_to_bytes_EVEN =
  cake_theorem "all_enc_ok_prog_to_bytes_EVEN[local]"
  (fun () ->
    `!code n c labs ffi pos.
      EVEN pos /\
      all_enc_ok c labs ffi pos code ==>
      EVEN (LENGTH (prog_to_bytes code))`)
  CHEAT_TAC;;

let loc_to_pc_append = cake_theorem "loc_to_pc_append[local]"
  (fun () ->
    `!l1 l2 c1 c2 conf labs ffis pos.
     EVERY sec_labels_ok (c1 ++ c2) ==>
     loc_to_pc l1 l2 (c1 ++ c2) =
     (match loc_to_pc l1 l2 c1 with
       SOME x -> SOME x | NONE ->
       (match loc_to_pc l1 l2 c2 with
         SOME x -> SOME (x + SUM (MAP ((\xs. LENGTH (FILTER ((~)
           o is_Label) xs)) o Section_lines) c1)) | NONE -> NONE))`)
  CHEAT_TAC;;

let all_enc_ok_append = cake_theorem "all_enc_ok_append"
  (fun () ->
    `!conf labs ffi n c1 c2.
     all_enc_ok conf labs ffi n c1 /\
     all_enc_ok conf labs ffi (n + LENGTH (prog_to_bytes c1)) c2
       ==>
     all_enc_ok conf labs ffi n (c1 ++ c2)`)
  CHEAT_TAC;;

let extract_labels_loc_to_pc = cake_theorem "extract_labels_loc_to_pc"
  (fun () ->
    `!l1 l2 code.
     EVERY sec_labels_ok code /\
     MEM (l1,l2) (FLAT (MAP (extract_labels o Section_lines) code))
       ==>
     (?y. loc_to_pc l1 l2 code = SOME y)`)
  CHEAT_TAC;;

let all_enc_ok_labs_mono = cake_theorem "all_enc_ok_labs_mono"
  (fun () ->
    `!conf labs ffi n c labs2.
     (!l1 l2 x.
     lab_lookup l1 l2 labs = SOME x ==>
     lab_lookup l1 l2 labs2 = SOME x) /\
     all_enc_ok conf labs ffi n c ==>
     all_enc_ok conf labs2 ffi n c`)
  CHEAT_TAC;;

let pos_val_append = cake_theorem "pos_val_append"
  (fun () ->
    `!c1 i pos c2.
     EVERY sec_label_zero c2 ==>
     pos_val i pos (c1 ++ c2) =
     (if i <= (SUM (MAP ((\xs. LENGTH (FILTER ((~) o is_Label) xs))
       o Section_lines) c1)) then
     pos_val i pos c1 else
      pos_val (i - (SUM (MAP ((\xs. LENGTH (FILTER ((~) o
        is_Label) xs)) o Section_lines) c1))) (pos + (SUM (MAP (SUM o
        MAP line_length o Section_lines) c1))) c2)`)
  CHEAT_TAC;;

let sec_pos_val_acc = cake_theorem "sec_pos_val_acc"
  (fun () ->
    `!l n i.
     (\xs. LENGTH (FILTER ((~) o is_Label) xs)) l <= i ==>
     sec_pos_val i n l = NONE`)
  CHEAT_TAC;;

let pos_val_acc = cake_theorem "pos_val_acc"
  (fun () ->
    `!ls n.
     pos_val (SUM (MAP ((\xs. LENGTH (FILTER ((~) o is_Label) xs))
       o Section_lines) ls)) n ls =
     n + SUM (MAP (SUM o (MAP line_length) o Section_lines) ls)`)
  CHEAT_TAC;;

let pos_val_bound = cake_theorem "pos_val_bound"
  (fun () ->
    `!i pos code conf labs ffi n.
     all_enc_ok conf labs ffi n code ==>
     pos_val i pos code <= pos + LENGTH (prog_to_bytes code)`)
  CHEAT_TAC;;

let sec_loc_to_pc_bound = cake_theorem "sec_loc_to_pc_bound"
  (fun () ->
    `!n xs x.
     sec_loc_to_pc n xs = SOME x ==>
     x <= (\xs. LENGTH (FILTER ((~) o is_Label) xs)) xs`)
  CHEAT_TAC;;

let loc_to_pc_bound = cake_theorem "loc_to_pc_bound"
  (fun () ->
    `!code l1 l2 x.
     EVERY sec_labels_ok code /\
     loc_to_pc l1 l2 code = SOME x ==>
     x <= SUM (MAP ((\xs. LENGTH (FILTER ((~) o is_Label) xs)) o
       Section_lines) code)`)
  CHEAT_TAC;;

let find_ffi_names_append = cake_theorem "find_ffi_names_append[local]"
  (fun () ->
    `!l1 l2.
     find_ffi_names (l1 ++ l2) =
     (find_ffi_names l2) ++
     FILTER (\n. ~(MEM n (find_ffi_names l2))) (find_ffi_names
       l1)`)
  CHEAT_TAC;;

let all_enc_ok_aligned_pos_val =
  cake_theorem "all_enc_ok_aligned_pos_val"
  (fun () ->
    `!(mc_conf:('a,'b,'c)machine_config) labs code2 pc' ffi_names'.
      all_enc_ok (target_config (machine_config_target mc_conf))
        labs ffi_names' 0 code2 /\
      (has_odd_inst code2 ==> asm_config_code_alignment
        (target_config (machine_config_target mc_conf)) = 0) /\
      encoder_correct (machine_config_target mc_conf) ==>
      alignment_aligned (asm_config_code_alignment (target_config
        (machine_config_target mc_conf))) (n2w (pos_val pc' 0
        code2):'a word)`)
  CHEAT_TAC;;

let read_ffi_bytearrays_with_next_interfer =
  cake_theorem "read_ffi_bytearrays_with_next_interfer[simp]"
  (fun () ->
    `read_ffi_bytearrays (machine_config_next_interfer_fupd (K foo) mc)
  =
     read_ffi_bytearrays mc`)
  CHEAT_TAC;;

let read_ffi_bytearrays_shift_interfer =
  cake_theorem "read_ffi_bytearrays_shift_interfer[simp]"
  (fun () ->
    `read_ffi_bytearrays (shift_interfer x y) = read_ffi_bytearrays y`)
  CHEAT_TAC;;

let read_ffi_bytearrays_ffi_interfer =
  cake_theorem "read_ffi_bytearrays_ffi_interfer[simp]"
  (fun () ->
    `read_ffi_bytearrays (machine_config_ffi_interfer_fupd (K ffi) mc)
  = read_ffi_bytearrays mc`)
  CHEAT_TAC;;

let IMP_ffi_entry_pcs_disjoint_Asm =
  cake_theorem "IMP_ffi_entry_pcs_disjoint_Asm"
  (fun () ->
    `!(s1:('a,lab_to_target_config,'ffi)labSem_state)
  (mc_conf:('a,'state,'b)machine_config).
       code_similar (labSem_state_code s1) code2 /\
       all_enc_ok (target_config (machine_config_target mc_conf))
         labs ffi_names 0 code2 /\
       asm_fetch_aux (labSem_state_pc s1) (labSem_state_code s1) =
         SOME (labLang_Asm instr _bytes _len) /\
       (!op re a. ~(instr = ShareMem op re a)) /\
       share_mem_domain_code_rel mc_conf p code2
         (labSem_state_shared_mem_domain s1) /\
       bytes_in_mem (p + n2w (pos_val (labSem_state_pc s1) 0
         code2)) bytes' (asm_state_mem t1) (asm_state_mem_domain
         t1) (labSem_state_mem_domain s1) /\
       pos_val (labSem_state_pc s1 + 1) 0 code2 = LENGTH bytes' +
         pos_val (labSem_state_pc s1) 0 code2 /\ asm_state_pc
       t1 = p + n2w (pos_val (labSem_state_pc s1) 0 code2) ==>
       ffi_entry_pcs_disjoint
         (mc_conf:('a,'state,'b)machine_config) t1 (LENGTH bytes')`)
  CHEAT_TAC;;

let IMP_ffi_entry_pcs_disjoint_LabAsm =
  cake_theorem "IMP_ffi_entry_pcs_disjoint_LabAsm"
  (fun () ->
    `!(s1:('a,lab_to_target_config,'ffi)labSem_state)
  (mc_conf:('a,'state,'b)machine_config).
       code_similar (labSem_state_code s1) code2 /\
       all_enc_ok (target_config (machine_config_target mc_conf))
         labs ffi_names 0 code2 /\
       asm_fetch_aux (labSem_state_pc s1) (labSem_state_code s1) =
         SOME (labLang_LabAsm instr _pos _bytes _len) /\
       share_mem_domain_code_rel mc_conf p code2
         (labSem_state_shared_mem_domain s1) /\
       bytes_in_mem (p + n2w (pos_val (labSem_state_pc s1) 0
         code2)) bytes' (asm_state_mem t1) (asm_state_mem_domain
         t1) (labSem_state_mem_domain s1) /\
       pos_val (labSem_state_pc s1 + 1) 0 code2 = LENGTH bytes' +
         pos_val (labSem_state_pc s1) 0 code2 /\ asm_state_pc
       t1 = p + n2w (pos_val (labSem_state_pc s1) 0 code2) ==>
       ffi_entry_pcs_disjoint
         (mc_conf:('a,'state,'b)machine_config) t1 (LENGTH bytes')`)
  CHEAT_TAC;;

let asm_fetch_SOME_IMP_LESS_num_pcs =
  cake_theorem "asm_fetch_SOME_IMP_LESS_num_pcs"
  (fun () ->
    `!pc' secs x.
       asm_fetch_aux pc' secs = SOME x ==>
       pc' < num_pcs secs`)
  CHEAT_TAC;;

let GENLIST_asm_fetch_aux_next =
  cake_theorem "GENLIST_asm_fetch_aux_next"
  (fun () ->
    `~(is_Label x) ==>
     GENLIST (\i.
       (i,asm_fetch_aux i (Section k (x :: xs) :: rest)))
       (n + 1) =
     (0,SOME x) :: (
       GENLIST (\i.
         (i + 1,asm_fetch_aux i (Section k xs :: rest))) n)`)
  CHEAT_TAC;;

let pos_val_acc_sum = cake_theorem "pos_val_acc_sum"
  (fun () ->
    `!i pos secs x y.
       x + y = pos ==>
       x + pos_val i y secs = pos_val i pos secs`)
  CHEAT_TAC;;

let pos_val_acc_0 = cake_theorem "pos_val_acc_0"
  (fun () ->
    `!i pos secs.
     pos + pos_val i 0 secs = pos_val i pos secs`)
  CHEAT_TAC;;

let FILTER_mmio_pcs_min_index = cake_theorem "FILTER_mmio_pcs_min_index"
  (fun () ->
    `EVERY (\x. ?op. x = ffi_SharedMem op) l ==>
     mmio_pcs_min_index
       (FILTER (\x. ?s. x = ffi_ExtCall s) ffis ++ l) =
     SOME (LENGTH
       (FILTER (\x. ?s. x = ffi_ExtCall s) ffis))`)
  CHEAT_TAC;;

let pos_val_GE_pc = cake_theorem "pos_val_GE_pc"
  (fun () ->
    `!i p code2.
       p <= pos_val i p code2`)
  CHEAT_TAC;;

let enc_ok_LENGTH_GT_0 = cake_theorem "enc_ok_LENGTH_GT_0"
  (fun () ->
    `enc_ok c ==>
     0 < LENGTH (asm_config_encode c l)`)
  CHEAT_TAC;;

let pos_val_mono = cake_theorem "pos_val_mono"
  (fun () ->
    `!i p code2 j p'.
       i < j /\
       j <= num_pcs code2 /\
       all_enc_ok c labs ffis p' code2 /\
       enc_ok c ==>
       pos_val i p code2 < pos_val j p code2`)
  CHEAT_TAC;;

let pos_val_mono_inv = cake_theorem "pos_val_mono_inv"
  (fun () ->
    `!i p code2 j.
       pos_val i p code2 < pos_val j p code2 /\
       i <= num_pcs code2 /\
       all_enc_ok c labs ffis p' code2 /\
       enc_ok c ==>
       i < j`)
  CHEAT_TAC;;

let pos_val_inj = cake_theorem "pos_val_inj"
  (fun () ->
    `!p code2 j.
       pos_val i p code2 = pos_val j p code2 /\
       i <= num_pcs code2 /\ j <= num_pcs code2 /\
       all_enc_ok c labs ffis p' code2 /\
       enc_ok c ==>
       i = j`)
  CHEAT_TAC;;

let pos_val_num_pcs = cake_theorem "pos_val_num_pcs"
  (fun () ->
    `!c labs ffis p' code2.
       all_enc_ok c labs ffis p' code2 ==>
       pos_val (num_pcs code2) p code2 = p + LENGTH
         (prog_to_bytes code2)`)
  CHEAT_TAC;;

let pos_val_GE_num_pcs = cake_theorem "pos_val_GE_num_pcs"
  (fun () ->
    `!pc' p code2.
       num_pcs code2 <= pc' ==>
       pos_val (num_pcs code2) p code2 = pos_val pc' p code2`)
  CHEAT_TAC;;

let pos_val_0_aux = cake_theorem "pos_val_0_aux"
  (fun () ->
    `!c labs ffis p xs pos.
       all_enc_ok c labs ffis p xs ==> (pos_val 0 pos xs = pos)`)
  CHEAT_TAC;;

let asm_fetch_aux_pos_val_SUC = cake_theorem "asm_fetch_aux_pos_val_SUC"
  (fun () ->
    `!pc' p code2 p'.
       all_enc_ok c labs ffi p' code2 /\
       asm_fetch_aux pc' (code2:('a sec) list) = SOME line ==>
       LENGTH (line_bytes line) + pos_val pc' p code2 = pos_val
         (pc' + 1) p code2`)
  CHEAT_TAC;;

let pos_val_asm_fetch_aux_distinct =
  cake_theorem "pos_val_asm_fetch_aux_distinct"
  (fun () ->
    `all_enc_ok c labs ffis p' (code2:('a sec) list) /\
     enc_ok c /\
     asm_fetch_aux pc code2 = SOME line /\
     a < LENGTH (line_bytes line) /\
     LENGTH (prog_to_bytes code2) < dimword (:'a) /\ ~(pc' = pc)
       ==> ~(a + pos_val pc p code2 = pos_val pc' p code2)`)
  CHEAT_TAC;;

let bytes_in_memory_eq_mem = cake_theorem "bytes_in_memory_eq_mem"
  (fun () ->
    `!pc' bytes.
       (!a. a IN asm_state_mem_domain t1 ==> target_get_byte
         (machine_config_target mc_conf) ms1 a = asm_state_mem t1 a) /\
       bytes_in_memory pc' bytes (asm_state_mem t1)
         (asm_state_mem_domain t1) ==>
       bytes_in_memory pc' bytes (target_get_byte
         (machine_config_target mc_conf) ms1) (asm_state_mem_domain
         t1)`)
  CHEAT_TAC;;

(* HOL4 lab_to_targetProofScript.sml:6959-6967: ML code, not ported *)

(* HOL4 lab_to_targetProofScript.sml:6969-6978: a proof *)

(* HOL4 lab_to_targetProofScript.sml:6980-7059: a proof *)

(* HOL4 lab_to_targetProofScript.sml:7061-7157: a proof *)

let ffi_entry_pcs_NOT_ccache_OR_halt_pc =
  cake_theorem "ffi_entry_pcs_NOT_ccache_OR_halt_pc"
  (fun () ->
    `find_index pc (machine_config_ffi_entry_pcs mc_conf) 0 =
        SOME index /\ ~(machine_config_halt_pc
     mc_conf = EL index (machine_config_ffi_entry_pcs mc_conf)) /\
       ~(machine_config_ccache_pc
     mc_conf = EL index (machine_config_ffi_entry_pcs mc_conf))
       ==> ~(pc = machine_config_ccache_pc mc_conf) /\ ~(pc =
       machine_config_halt_pc mc_conf)`)
  CHEAT_TAC;;

(* HOL4 lab_to_targetProofScript.sml:7171-7200: a proof *)

let ffi_name_NOT_Mapped = cake_theorem "ffi_name_NOT_Mapped"
  (fun () ->
    `mmio_pcs_min_index ffi_names = SOME i /\ (?str. s = ffi_ExtCall
  str) /\
     MEM s ffi_names ==>
     get_ffi_index ffi_names s < i`)
  CHEAT_TAC;;

let mmio_pcs_min_index_is_SOME =
  cake_theorem "mmio_pcs_min_index_is_SOME"
  (fun () ->
    `!ffi_names'.
       mmio_pcs_min_index ffi_names' = SOME i ==>
       i <= LENGTH ffi_names' /\
       (!j. j < i ==>
         (?s. EL j ffi_names' = ffi_ExtCall s)) /\
        (!j. i <= j /\ j < LENGTH ffi_names' ==>
          (?op. EL j ffi_names' = ffi_SharedMem op))`)
  CHEAT_TAC;;

let no_share_mem_lemma = cake_theorem "no_share_mem_lemma"
  (fun () ->
    `mmio_pcs_min_index ffi_names = SOME i /\
     asm_fetch_aux pc code = SOME (labLang_LabAsm Install c l n) /\
     no_install_or_no_share_mem code ffi_names ==>
     i = LENGTH ffi_names`)
  CHEAT_TAC;;

let asm_fetch_aux_APPEND1 = cake_theorem "asm_fetch_aux_APPEND1"
  (fun () ->
    `!pc' code.
       pc' < num_pcs code ==>
       asm_fetch_aux pc' (code ++ sec_list) = asm_fetch_aux pc'
         code`)
  CHEAT_TAC;;

let pos_val_APPEND1 = cake_theorem "pos_val_APPEND1"
  (fun () ->
    `!pc' code.
       pc' < num_pcs code ==>
       pos_val pc' 0 (code ++ sec_list) = pos_val pc' 0 code`)
  CHEAT_TAC;;

let asm_fetch_aux_APPEND2 = cake_theorem "asm_fetch_aux_APPEND2"
  (fun () ->
    `!code.
       asm_fetch_aux (pc + num_pcs code) (code ++ sec_list) =
         asm_fetch_aux pc sec_list`)
  CHEAT_TAC;;

let pos_val_APPEND2 = cake_theorem "pos_val_APPEND2"
  (fun () ->
    `!c labs ffis p code.
       all_enc_ok c labs ffis p code ==>
       pos_val (pc + num_pcs code) 0 (code ++ sec_list) =
         LENGTH (prog_to_bytes code) + pos_val pc 0 sec_list`)
  CHEAT_TAC;;

let get_shmem_info_MappedRead_or_MappedWrite =
  cake_theorem "get_shmem_info_MappedRead_or_MappedWrite"
  (fun () ->
    `!sec pos ffi_names' info new_ffi_names new_info.
       get_shmem_info sec pos ffi_names' info =
         (new_ffi_names,new_info) ==>
       (?l. new_ffi_names = ffi_names' ++ l /\
         EVERY (\x. ?op. x = ffi_SharedMem op) l)`)
  CHEAT_TAC;;

let no_share_mem_APPEND = cake_theorem "no_share_mem_APPEND"
  (fun () ->
    `no_share_mem_inst code /\
     no_share_mem_inst secs ==>
     no_share_mem_inst (code ++ secs)`)
  CHEAT_TAC;;

let no_install_APPEND_IMP = cake_theorem "no_install_APPEND_IMP"
  (fun () ->
    `no_install (code ++ secs) ==>
     no_install code /\ no_install secs`)
  CHEAT_TAC;;

let code_similar_IMP_both_no_share_mem =
  cake_theorem "code_similar_IMP_both_no_share_mem"
  (fun () ->
    `code_similar code sec_list /\
     no_share_mem_inst code ==>
     no_share_mem_inst sec_list`)
  CHEAT_TAC;;

let code_similar_IMP_both_no_install_or_no_share_mem =
  cake_theorem "code_similar_IMP_both_no_install_or_no_share_mem"
  (fun () ->
    `code_similar code sec_list /\
     no_install_or_no_share_mem code ffi_names ==>
     no_install_or_no_share_mem sec_list ffi_names`)
  CHEAT_TAC;;

let no_share_mem_IMP_get_shmem_info =
  cake_theorem "no_share_mem_IMP_get_shmem_info"
  (fun () ->
    `!code p ffi_names' shmem_info.
       no_share_mem_inst code ==>
       get_shmem_info code p ffi_names' shmem_info =
         (ffi_names',shmem_info)`)
  CHEAT_TAC;;

(* move *)
let Sh_not_Ext = cake_theorem "Sh_not_Ext"
  (fun () ->
    `(?s. x = ffi_SharedMem s) <=> (!s. ~(x = ffi_ExtCall s))`)
  CHEAT_TAC;;

let not_Sh_Ext = cake_theorem "not_Sh_Ext"
  (fun () ->
    `(!s. ~(x = ffi_SharedMem s)) <=> (?s. x = ffi_ExtCall s)`)
  CHEAT_TAC;;

let oracle_tie_shift_gen = cake_theorem "oracle_tie_shift_gen"
  (fun () ->
    `!mc_conf mc2 ms1 s1 ms2 l.
     oracle_tie mc_conf ms1 (s1:('a,'c,'ffi)labSem_state) /\
     (!k. find_next_interference mc_conf (labSem_state_ffi s1) (k +
       l) ms1 =
          find_next_interference mc2 (labSem_state_ffi s1) k ms2)
            /\ machine_config_target
     mc2 = machine_config_target mc_conf /\
       machine_config_callee_saved_regs
     mc2 = machine_config_callee_saved_regs mc_conf /\ ptr_reg
     mc2 = machine_config_ptr_reg mc_conf ==>
     oracle_tie mc2 ms2 s1`)
  CHEAT_TAC;;

let oracle_tie_ccache_residues =
  cake_theorem "oracle_tie_ccache_residues"
  (fun () ->
    `!mc_conf mc2 ms1 s1 ms2 l t1.
     oracle_tie mc_conf ms1 (s1:('a,'c,'ffi)labSem_state) /\
     (!k. find_next_interference mc_conf (labSem_state_ffi s1) (k +
       l) ms1 =
          find_next_interference mc2 (labSem_state_ffi s1) k ms2)
            /\ machine_config_target
     mc2 = machine_config_target mc_conf /\ ptr_reg
     mc2 = machine_config_ptr_reg mc_conf /\ len_reg
     mc2 = machine_config_len_reg mc_conf /\
       machine_config_ccache_interfer
     mc2 = machine_config_ccache_interfer mc_conf /\
       ~(target_get_pc (machine_config_target
     mc2) ms2 IN machine_config_prog_addresses mc2 DIFF set_of_list
       (machine_config_ffi_entry_pcs mc2)) /\ ~(target_get_pc
       (machine_config_target
     mc2) ms2 = machine_config_halt_pc mc2) /\ target_get_pc
       (machine_config_target
     mc2) ms2 = machine_config_ccache_pc mc2 ==>
     (\a. get_reg_value (labSem_state_cc_regs s1 0 a)
       (asm_state_regs t1 a) I) =
       (\a. if MEM a (machine_config_callee_saved_regs mc_conf) \/
         a = machine_config_ptr_reg mc_conf \/
               ~(a < asm_config_reg_count (target_config
                 (machine_config_target mc_conf))) \/
               MEM a (asm_config_avoid_regs (target_config
                 (machine_config_target mc_conf))) then asm_state_regs
                 t1 a else target_get_reg (machine_config_target
                 mc_conf)
                   (machine_config_ccache_interfer mc_conf 0
                      (target_get_reg (machine_config_target
                        mc_conf) ms2 (machine_config_ptr_reg
                        mc_conf),target_get_reg (machine_config_target
                       mc_conf) ms2 (machine_config_len_reg
                         mc_conf),ms2)) a) /\
     (\n. labSem_state_cc_fp_regs s1 0 n) =
       (\n. target_get_fp_reg (machine_config_target mc_conf)
              (machine_config_ccache_interfer mc_conf 0
                 (target_get_reg (machine_config_target mc_conf)
                   ms2 (machine_config_ptr_reg mc_conf),target_get_reg
                   (machine_config_target
                  mc_conf) ms2 (machine_config_len_reg
                    mc_conf),ms2)) n)`)
  CHEAT_TAC;;

(* HOL4 lab_to_targetProofScript.sml:7526: ML code, not ported *)

let lab_to_targetProof_compile_correct = cake_theorem "compile_correct"
  (fun () ->
    `!(s1:('a,lab_to_target_config,'ffi)labSem_state) res
  (mc_conf:('a,'state,'b)machine_config) s2 code2 labs t1 ms1.
        oracle_tie mc_conf ms1 s1 /\
        (evaluate s1 = (res,s2)) /\ (~(res = Error)) /\
        encoder_correct (machine_config_target mc_conf) /\
        state_rel (mc_conf,code2,labs,p) s1 t1 ms1 ==>
        (?k t2 ms2.
          (evaluate mc_conf (labSem_state_ffi s1)
            (labSem_state_clock s1 + k) ms1 =
             (res,
              ms2,state_ffi s2)))`)
  CHEAT_TAC;;

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

let machine_sem_EQ_sem = cake_theorem "machine_sem_EQ_sem"
  (fun () ->
    `!mc_conf p (ms:'state)
  (s1:('a,lab_to_target_config,'ffi)labSem_state).
       encoder_correct (machine_config_target mc_conf) /\
       init_ok (mc_conf,p) s1 ms /\ ~(semantics s1 = ffi_Fail) ==>
       machine_sem mc_conf (labSem_state_ffi s1) ms = {semantics
         s1}`)
  CHEAT_TAC;;

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
       (machine_config_target mc_conf))) ffi (target_io_regs mc_conf ffi
       ms) (target_cc_regs mc_conf ffi ms) (target_io_fp_regs mc_conf
       ffi ms) (target_cc_fp_regs mc_conf ffi ms) code comp' coracle
       (mk_buffer cbpos [] cbspace) 0 F (machine_config_ptr_reg mc_conf)
       (machine_config_len_reg mc_conf) (machine_config_ptr2_reg
       mc_conf) (machine_config_len2_reg mc_conf) (match link_reg
       (target_config (machine_config_target mc_conf)) with SOME n -> n
       | _82 -> 0)
   // Initialize with code buffer empty`;;
hol4_overload "make_init" "lab_to_targetProof_make_init";;

let oracle_tie_make_init = cake_theorem "oracle_tie_make_init"
  (fun () ->
    `oracle_tie mc_conf ms
       (lab_to_targetProof_make_init mc_conf ffi t m dm sdm ms
         code cmp cbpos cbspace coracle)`)
  CHEAT_TAC;;

(* HOL4 lab_to_targetProofScript.sml:9586: the ML values that the
   definitions below antiquote *)

let compiler_oracle_ok_def = cake_define
  `compiler_oracle_ok coracle init_labs init_pos c ffis <=>
     (
      // Assumptions about initial compile oracle
      !(k:num). let (cfg,code) = coracle k in
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
     reg_ok (machine_config_ptr_reg mc_conf) (target_config
       (machine_config_target mc_conf)) /\
     reg_ok (machine_config_len_reg mc_conf) (target_config
       (machine_config_target mc_conf)) /\
     reg_ok (machine_config_ptr2_reg mc_conf) (target_config
       (machine_config_target mc_conf)) /\
     reg_ok (machine_config_len2_reg mc_conf) (target_config
       (machine_config_target mc_conf)) /\
     reg_ok (match link_reg (target_config (machine_config_target
       mc_conf)) with NONE -> 0 | SOME n -> n) (target_config
       (machine_config_target
       mc_conf)) /\
     enc_ok (target_config (machine_config_target mc_conf))`;;

let get_shmem_info_APPEND = cake_theorem "get_shmem_info_APPEND"
  (fun () ->
    `!secs pos ffi_names' shmem_info ffis1 ffis2 info1 info2
  new_ffi_names new_shmem_info.
       get_shmem_info secs pos ffi_names'
         (shmem_info:shmem_info_num list) =
         (new_ffi_names,new_shmem_info) /\
       ffi_names' = ffis1 ++ ffis2 /\
       shmem_info = info1 ++ info2 ==>
       new_ffi_names = ffis1 ++ (FST (get_shmem_info secs pos ffis2
         info2)) /\
       new_shmem_info = info1 ++ (SND (get_shmem_info secs pos
         ffis2 info2))`)
  CHEAT_TAC;;

let get_shmem_info_PREPEND = cake_theorem "get_shmem_info_PREPEND"
  (fun () ->
    `get_shmem_info secs pos ffi_names (shmem_info:shmem_info_num list)
  =
       (new_ffi_names,new_shmem_info) ==>
     new_ffi_names = ffi_names ++ (FST (get_shmem_info secs pos []
       [])) /\
     new_shmem_info = shmem_info ++ (SND (get_shmem_info secs pos
       [] []))`)
  CHEAT_TAC;;

let line_to_info_def = cake_define
  `line_to_info (secs:('a sec) list) p x = (match SND x with
     SOME (labLang_Asm (ShareMem m r ad) bytes l) ->
       (let (name,nb) = get_memop_info m in
       [(ffi_SharedMem name,
        mk_shmem_info_num (pos_val (FST x) p secs) nb (match ad
          with Addr r off -> r) (match ad with Addr r off -> w2n off)
          r (pos_val (FST x) p secs + LENGTH bytes))]) | _83 -> [])`;;

let line_to_info_next = cake_theorem "line_to_info_next"
  (fun () ->
    `line_to_info (Section k1 (labLang_LabAsm a b bytes1 len1 :: xs1) ::
  rest1) p1 (i1 + 1,l1) = line_to_info ((Section k1 xs1) :: rest1) (p1 +
  LENGTH bytes1) (i1,l1) /\
     line_to_info (Section k2 (labLang_Asm c2 bytes2 len2 :: xs2)
       :: rest2) p2 (i2 + 1,l2) = line_to_info ((Section k2 xs2) ::
       rest2) (p2 + LENGTH bytes2) (i2,l2)`)
  CHEAT_TAC;;

let line_to_info_hd_empty = cake_theorem "line_to_info_hd_empty"
  (fun () ->
    `line_to_info (Section k [] :: rest) p t =
       line_to_info rest p t`)
  CHEAT_TAC;;

let line_to_info_hd_Label = cake_theorem "line_to_info_hd_Label"
  (fun () ->
    `line_to_info (Section k ((labLang_Label a b 0) :: xs) :: rest)
       p t = line_to_info (Section k xs :: rest) p t`)
  CHEAT_TAC;;

let get_shmem_info_thm = cake_theorem "get_shmem_info_thm"
  (fun () ->
    `!secs p ffi_names' shmem_info p'.
     all_enc_ok c labs ffis p' secs ==>
     get_shmem_info secs p ffi_names' shmem_info =
       (let (new_ffis,new_info) =
         UNZIP (FLAT (
         MAP (line_to_info secs p) (
         GENLIST (\i. (i,asm_fetch_aux i secs))
         (num_pcs secs)))) in (ffi_names' ++ new_ffis,shmem_info
           ++ new_info))`)
  CHEAT_TAC;;

let FILTER_NOT_MEM_Mapped = cake_theorem "FILTER_NOT_MEM_Mapped[local]"
  (fun () ->
    `~(MEM "MappedRead" (FILTER (\x. ~(x = "MappedRead") /\ ~(x =
  "MappedWrite")) l)) /\
     ~(MEM "MappedWrite" (FILTER (\x. ~(x = "MappedRead") /\ ~(x
       = "MappedWrite")) l))`)
  CHEAT_TAC;;

let mmio_pcs_min_index_APPEND_thm =
  cake_theorem "mmio_pcs_min_index_APPEND_thm"
  (fun () ->
    `EVERY (\x. !s. ~(x = ffi_ExtCall s)) l /\
     EVERY (\x. ?s. x = ffi_ExtCall s) ffis ==>
     mmio_pcs_min_index (ffis ++ l) = SOME (LENGTH ffis)`)
  CHEAT_TAC;;

let MEM_get_shmem_info = cake_theorem "MEM_get_shmem_info"
  (fun () ->
    `all_enc_ok c labs ffis p' (code2:('a sec) list) /\
     asm_fetch_aux pc code2 = SOME (labLang_Asm (ShareMem op re a)
       inst' len) /\
     get_memop_info op = (q,(r:word8)) ==>
     MEM
       (ffi_SharedMem q,
       mk_shmem_info_num (pos_val pc p code2) r (match a with Addr
         r off -> r) (match a with Addr r off -> w2n off) re (pos_val pc
         (p + LENGTH inst') code2))
       (UNCURRY ZIP (get_shmem_info code2 p [] []))`)
  CHEAT_TAC;;

let get_shmem_info_ALL_DISTINCT =
  cake_theorem "get_shmem_info_ALL_DISTINCT"
  (fun () ->
    `LENGTH (prog_to_bytes code2) < dimword (:'a) /\
     enc_ok c /\
     all_enc_ok c labs ffis p' (code2:('a sec) list) ==>
     ALL_DISTINCT (MAP (\rec. shmem_info_num_entry_pc rec) (SND
       (get_shmem_info code2 p [] [])))`)
  CHEAT_TAC;;

let get_shmem_info_EMPTY_LENGTH_EQ =
  cake_theorem "get_shmem_info_EMPTY_LENGTH_EQ"
  (fun () ->
    `all_enc_ok c labs ffis p' (code2:('a sec) list) ==>
     LENGTH (FST (get_shmem_info code2 p [] [])) =
       LENGTH (SND (get_shmem_info code2 p [] []))`)
  CHEAT_TAC;;

let line_to_info_offset_FST_eq =
  cake_theorem "line_to_info_offset_FST_eq"
  (fun () ->
    `MAP FST (line_to_info code p accum) = MAP FST (line_to_info code
  0 accum)`)
  CHEAT_TAC;;

let line_to_info_offset_SND_eq =
  cake_theorem "line_to_info_offset_SND_eq"
  (fun () ->
    `MAP SND (line_to_info code p accum) = MAP (\x.
  shmem_info_num_exit_pc_fupd (K (p + shmem_info_num_exit_pc (SND x)))
  (shmem_info_num_entry_pc_fupd (K (p + shmem_info_num_entry_pc (SND
  x))) (SND x)))
       (line_to_info code 0 accum)`)
  CHEAT_TAC;;

let get_shmem_info_init_pc_offset =
  cake_theorem "get_shmem_info_init_pc_offset"
  (fun () ->
    `all_enc_ok c labs ffis p' code ==>
     FST (get_shmem_info code 0 [] []) = FST (get_shmem_info code p
       [] []) /\
     MAP (\rec. shmem_info_num_exit_pc_fupd (K (p +
       shmem_info_num_exit_pc rec)) (shmem_info_num_entry_pc_fupd (K (p
       + shmem_info_num_entry_pc rec)) rec)) (SND (get_shmem_info code 0
       [] [])) =
     SND (get_shmem_info code p [] [])`)
  CHEAT_TAC;;

let mmio_pcs_min_index_get_shmem_info_ok =
  cake_theorem "mmio_pcs_min_index_get_shmem_info_ok"
  (fun () ->
    `all_enc_ok c labs ffis' p' (code2:('a sec) list) /\
     enc_ok c /\ EVERY (\x. ?s. x = ffi_ExtCall s) ffis /\
     get_shmem_info code2 p ffis [] =
       (new_ffi_names,new_shmem_info) ==>
     mmio_pcs_min_index new_ffi_names = SOME (LENGTH ffis)`)
  CHEAT_TAC;;

let get_shmem_info_ok_lemma = cake_theorem "get_shmem_info_ok_lemma"
  (fun () ->
    `all_enc_ok c labs ffis' p' (code2:('a sec) list) /\
     enc_ok c /\
     LENGTH (prog_to_bytes code2) < dimword (:'a) /\
     EVERY (\x. ?s. x = ffi_ExtCall s) ffis /\
     get_shmem_info code2 p ffis [] =
       (new_ffi_names,new_shmem_info) ==>
     (!pc' op re a inst' len i.
       (asm_fetch_aux pc' code2 = SOME (labLang_Asm (ShareMem op re
         a) inst' len) /\
       mmio_pcs_min_index new_ffi_names = SOME i) ==>
       (?index.
         find_index (p + (pos_val pc' 0 code2)) (MAP (\rec.
           shmem_info_num_entry_pc rec) new_shmem_info) 0 =
           SOME index /\
         (let (name,nb) = get_memop_info op in
           EL (index + i) new_ffi_names = ffi_SharedMem name /\
           EL index new_shmem_info =
             mk_shmem_info_num (shmem_info_num_entry_pc (EL index
               new_shmem_info)) nb (match a with Addr r off -> r) (match
               a with Addr r off -> w2n off) re (p + (pos_val pc' 0
               code2 + len))))) /\
     (!pc' line.
         asm_fetch_aux pc' code2 = SOME line /\
         (!op re a inst' len. ~(line = labLang_Asm (ShareMem op re
           a) inst' len)) ==>
         DISJOINT (set_of_list (MAP (\rec. shmem_info_num_entry_pc
           rec) new_shmem_info))
           {p + a + (pos_val pc' 0 code2) |
             a < LENGTH (line_bytes line)})`)
  CHEAT_TAC;;

let asm_fetch_NOT_ffi_entry_pcs =
  cake_theorem "asm_fetch_NOT_ffi_entry_pcs"
  (fun () ->
    `LENGTH (prog_to_bytes code2) < dimword (:'a) /\
     mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i
       /\
     LENGTH (machine_config_ffi_names mc_conf) = LENGTH
       (machine_config_ffi_entry_pcs mc_conf) /\
     all_enc_ok (target_config (machine_config_target mc_conf))
       labs ffi_names 0 (code2:('a sec) list) /\
     enc_ok (target_config (machine_config_target mc_conf)) /\
     (!index.
       index < i ==> ~(--(n2w (ffi_offset * (index + 3))) +
         target_get_pc (machine_config_target mc_conf) (ms:'state) IN
         machine_config_prog_addresses
       mc_conf) /\ ~(--(n2w (ffi_offset * (index + 3))) +
         target_get_pc (machine_config_target mc_conf) ms IN
         machine_config_shared_addresses
       mc_conf) /\ ~(--(n2w (ffi_offset * (index + 3))) +
         target_get_pc (machine_config_target mc_conf) ms =
         machine_config_halt_pc
       mc_conf) /\ ~(--(n2w (ffi_offset * (index + 3))) +
         target_get_pc (machine_config_target mc_conf) ms =
         machine_config_ccache_pc
       mc_conf) /\
       find_index
         (--(n2w (ffi_offset * (index + 3))) + target_get_pc
           (machine_config_target mc_conf) ms)
           (machine_config_ffi_entry_pcs
         mc_conf) 0 = SOME index) /\
     bytes_in_mem (target_get_pc (machine_config_target mc_conf)
       ms) (prog_to_bytes code2) (asm_state_mem t)
       (machine_config_prog_addresses
        (mc_conf:('a,'state,'b)machine_config)) dm /\
     asm_fetch_aux pos code2 = SOME line /\
     a < LENGTH (line_bytes line) ==>
     ~(MEM (target_get_pc (machine_config_target mc_conf) ms + n2w
       a + (n2w (pos_val pos 0 code2)))
       (TAKE i (machine_config_ffi_entry_pcs mc_conf)))`)
  CHEAT_TAC;;

let list_subset_refl = cake_theorem "list_subset_refl"
  (fun () ->
    `!xs.
       list_subset xs xs`)
  CHEAT_TAC;;

let list_subset_TAKE = cake_theorem "list_subset_TAKE"
  (fun () ->
    `!i xs.
       list_subset (TAKE i xs) xs`)
  CHEAT_TAC;;

let list_subset_trans = cake_theorem "list_subset_trans"
  (fun () ->
    `list_subset a b /\ list_subset b c ==>
     list_subset a c`)
  CHEAT_TAC;;

let genlist_line_to_info_entry_pc_max =
  cake_theorem "genlist_line_to_info_entry_pc_max"
  (fun () ->
    `all_enc_ok c labs ffis p' code2 /\ enc_ok c ==>
     EVERY (\x. shmem_info_num_entry_pc (SND x) < pos_val (num_pcs
       code2) 0 code2)
       (FLAT (GENLIST
         (\i. line_to_info code2 0 (i,asm_fetch_aux i code2))
         (num_pcs code2)))`)
  CHEAT_TAC;;

let find_index_MAP_w2n = cake_theorem "find_index_MAP_w2n[local]"
  (fun () ->
    `!l (x:'a word) n. find_index (w2n x) (MAP w2n l) n = find_index x
  l n`)
  CHEAT_TAC;;

(* This is set up for the very first compile call *)
let IMP_state_rel_make_init =
  cake_theorem "IMP_state_rel_make_init[local]"
  (fun () ->
    `lab_to_targetProof_good_code (target_config (machine_config_target
  mc_conf)) LN (code:('a sec) list) /\
      mc_conf_ok mc_conf /\
      (no_share_mem_inst code ==>
        compiler_oracle_ok coracle labs (LENGTH (prog_to_bytes
          code2)) (target_config (machine_config_target mc_conf))
          (machine_config_ffi_names mc_conf)) /\
      list_subset (FILTER (\x. ?s. x = ffi_ExtCall s)
         (find_ffi_names code)) (TAKE i (machine_config_ffi_names
           mc_conf)) /\
      remove_labels clock (target_config (machine_config_target
        mc_conf)) 0 LN (TAKE i (machine_config_ffi_names mc_conf)) code
        =
         SOME (code2,labs) /\
      good_init_state mc_conf ms (prog_to_bytes code2)
         cbspace t m dm sdm /\
      get_shmem_info code2 0 [] [] = (new_ffi_names,shmem_info) /\
      new_shmem_info = MAP (\rec. shmem_info_num_exit_pc_fupd (K
        (w2n (target_get_pc (machine_config_target mc_conf) ms) +
        shmem_info_num_exit_pc rec)) (shmem_info_num_entry_pc_fupd (K
        (w2n (target_get_pc (machine_config_target mc_conf) ms) +
        shmem_info_num_entry_pc rec)) rec)) shmem_info /\
      DROP i (machine_config_ffi_names mc_conf) = new_ffi_names /\
      mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME
        i /\
      MAP (\rec. shmem_info_num_entry_pc rec) new_shmem_info = DROP
        i (MAP w2n (machine_config_ffi_entry_pcs mc_conf)) /\
      (machine_config_mmio_info mc_conf = ZIP (GENLIST (\index.
        index + i) (LENGTH new_shmem_info))
                              (MAP (\rec. (shmem_info_num_nbytes
                                rec,
                              Addr (shmem_info_num_addr_reg rec)
                                (n2w (shmem_info_num_addr_off
                                rec)),shmem_info_num_reg
                              rec,n2w (shmem_info_num_exit_pc
                                rec))) new_shmem_info)) /\
      no_install_or_no_share_mem code (machine_config_ffi_names
        mc_conf) /\
      (!bn. bn < cbspace ==>
         ~(MEM (n2w bn + n2w (LENGTH (prog_to_bytes code2)) +
           target_get_pc (machine_config_target
                mc_conf) ms) (TAKE i (machine_config_ffi_entry_pcs
                  mc_conf)))) ==>
      state_rel
        ((mc_conf:('a,'state,'b)machine_config),code2,labs,target_get_pc
        (machine_config_target
          mc_conf) ms)
        (lab_to_targetProof_make_init mc_conf (ffi:'ffi ffi_state)
          t m dm sdm ms code
         (compile_lab (target_config (machine_config_target
           mc_conf)))
         (target_get_pc (machine_config_target mc_conf) ms + n2w
           (LENGTH (prog_to_bytes code2))) cbspace coracle) t ms`)
  CHEAT_TAC;;

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

let make_init_simp = cake_theorem "make_init_simp[simp]"
  (fun () ->
    `state_ffi
       (lab_to_targetProof_make_init a b f g h i j k l m n p) = b
         /\ pc
       (lab_to_targetProof_make_init a b f g h i j k l m n p) = 0
         /\ state_code
       (lab_to_targetProof_make_init a b f g h i j k l m n p) = k`)
  CHEAT_TAC;;

(* HOL4 lab_to_targetProofScript.sml:10524-10538: a theorem that HOL4
   states as the value of an ML expression: semantics_make_init *)

let make_init_filter_skip = cake_theorem "make_init_filter_skip"
  (fun () ->
    `semantics (lab_to_targetProof_make_init mc_conf ffi t m dm sdm ms
  (filter_skip code)
         (compile_lab (target_config (machine_config_target
           mc_conf))) cbpos cbspace ((\(a,b). (a,filter_skip b)) o
           coracle)) =
     semantics
      (lab_to_targetProof_make_init mc_conf ffi t m dm sdm ms code
        (\c p. (compile_lab (target_config (machine_config_target
          mc_conf))) c (filter_skip p)) cbpos cbspace coracle)`)
  CHEAT_TAC;;

(* TODO: move *)
let find_ffi_names_filter_skip =
  cake_theorem "find_ffi_names_filter_skip"
  (fun () ->
    `!code. find_ffi_names (filter_skip code) = find_ffi_names code`)
  CHEAT_TAC;;

let all_enc_ok_pre_filter_skip =
  cake_theorem "all_enc_ok_pre_filter_skip[local]"
  (fun () ->
    `!code c.
     (\c ls. EVERY (sec_ok_pre c) ls) c code ==>
     (\c ls. EVERY (sec_ok_pre c) ls) c (filter_skip code)`)
  CHEAT_TAC;;

let MAP_Section_num_filter_skip =
  cake_theorem "MAP_Section_num_filter_skip[simp]"
  (fun () ->
    `!code. MAP Section_num (filter_skip code) = MAP Section_num code`)
  CHEAT_TAC;;

let filter_skip_extract_labels =
  cake_theorem "filter_skip_extract_labels[simp]"
  (fun () ->
    `!code. MAP (extract_labels o Section_lines) (filter_skip code) =
     MAP (extract_labels o Section_lines) code`)
  CHEAT_TAC;;

let get_code_labels_filter_skip =
  cake_theorem "get_code_labels_filter_skip[simp]"
  (fun () ->
    `!code. get_code_labels (filter_skip code) = get_code_labels code`)
  CHEAT_TAC;;

let get_labels_filter_skip = cake_theorem "get_labels_filter_skip[simp]"
  (fun () ->
    `!code. get_labels (filter_skip code) = get_labels code`)
  CHEAT_TAC;;

let implements_intro_gen = cake_theorem "implements_intro_gen"
  (fun () ->
    `(b /\ ~(x = ffi_Fail) ==> y = {x}) ==> b ==> implements' T y {x}`)
  CHEAT_TAC;;

let find_ffi_names_ALL_DISTINCT =
  cake_theorem "find_ffi_names_ALL_DISTINCT"
  (fun () ->
    `!code. ALL_DISTINCT (find_ffi_names code)`)
  CHEAT_TAC;;

let not_not_skip_IMP_Skip = cake_theorem "not_not_skip_IMP_Skip[local]"
  (fun () ->
    `~(not_skip inst') ==> (?l n. inst' = labLang_Asm (Asmi (asm_Inst
  asm_Skip)) l n)`)
  CHEAT_TAC;;

let asm_fetch_aux_filter_skip = cake_theorem "asm_fetch_aux_filter_skip"
  (fun () ->
    `!code p.
       asm_fetch_aux p (filter_skip code) = SOME inst' /\
       not_skip inst' ==>
       (?p'. asm_fetch_aux p' code = SOME inst')`)
  CHEAT_TAC;;

let IMP_asm_fetch_aux_filter_skip =
  cake_theorem "IMP_asm_fetch_aux_filter_skip"
  (fun () ->
    `!p code i.
       asm_fetch_aux p code = SOME i /\ not_skip i ==>
       (?p'. asm_fetch_aux p' (filter_skip code) = SOME i)`)
  CHEAT_TAC;;

let no_share_mem_filter_skip = cake_theorem "no_share_mem_filter_skip"
  (fun () ->
    `no_share_mem_inst (filter_skip code) <=> no_share_mem_inst code`)
  CHEAT_TAC;;


let all_pc_adjust_pc = cake_theorem "all_pc_adjust_pc"
  (fun () ->
    `!code p.
       p < num_pcs (filter_skip code) ==>
       (?k. adjust_pc k code = p)`)
  CHEAT_TAC;;

let no_install_or_no_share_mem_filter_skip =
  cake_theorem "no_install_or_no_share_mem_filter_skip"
  (fun () ->
    `no_install_or_no_share_mem code ffi_names ==>
     no_install_or_no_share_mem (filter_skip code) ffi_names`)
  CHEAT_TAC;;
(* HOL4 lab_to_targetProofScript.sml:10827-10848: code that the
   source has in a comment *)
let asm_fetch_aux_MEM = cake_theorem "asm_fetch_aux_MEM"
  (fun () ->
    `MEM x l /\ ~(is_Label x) ==>
     (?p. asm_fetch_aux p [Section n l] = SOME x)`)
  CHEAT_TAC;;
(* HOL4 lab_to_targetProofScript.sml:10866-10941: code that the
   source has in a comment *)
let find_ffi_names_EVERY = cake_theorem "find_ffi_names_EVERY"
  (fun () ->
    `!code ls. find_ffi_names code = ls ==> EVERY (\x. ?s. x =
  ffi_ExtCall s) ls`)
  CHEAT_TAC;;

(* HOL4 lab_to_targetProofScript.sml:10953-11010: code that the
   source has in a comment *)

let semantics_compile_lemma' =
  cake_theorem "semantics_compile_lemma'[local]"
  (fun () ->
    `mc_conf_ok mc_conf /\
     (no_share_mem_inst code ==>
       compiler_oracle_ok coracle (lab_to_target_config_labels c')
         (LENGTH bytes) (asm_conf:'a asm_config)
         (machine_config_ffi_names mc_conf)) /\
     // Assumptions on input code
     lab_to_targetProof_good_code (target_config
       (machine_config_target mc_conf)) LN code /\
     // Config state
     asm_conf = target_config (machine_config_target mc_conf) /\
       lab_to_target_config_labels
     c = LN /\ lab_to_target_config_pos c = 0 /\
     lab_to_target_compile asm_conf (c:lab_to_target_config) code =
       SOME (bytes,c') /\ ffi_names
     // FFI is either given or computed
     c' = SOME (machine_config_ffi_names mc_conf) /\
     good_init_state mc_conf ms bytes cbspace t m dm sdm /\
     // set up mmio_info and ffi_entry_pcs for mmio
     MAP (\rec. w2n (target_get_pc (machine_config_target mc_conf)
       ms) + shmem_info_num_entry_pc rec)
       (lab_to_target_config_shmem_extra c') =
       DROP i (MAP w2n (machine_config_ffi_entry_pcs mc_conf)) /\
         machine_config_mmio_info
     mc_conf = ZIP (GENLIST (\index. index + i) (LENGTH
       (lab_to_target_config_shmem_extra c')))
                              (MAP (\rec. (shmem_info_num_nbytes
                                rec,Addr (shmem_info_num_addr_reg rec)
                                (n2w (shmem_info_num_addr_off
                                rec)),shmem_info_num_reg
                              rec,n2w (shmem_info_num_exit_pc rec)
                                + target_get_pc (machine_config_target
                                mc_conf) ms))
                                (lab_to_target_config_shmem_extra
                              c')) /\
     no_install_or_no_share_mem code (machine_config_ffi_names
       mc_conf) /\
     (mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME
       i) /\
     // to avoid the ffi_entry_pc wraps around and overlaps with the program or code buffer
     cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword (:'a)
       /\
     (
      // the original ffi names provided does not contain MappedRead or MappedWrite
      !ffis. lab_to_target_config_ffi_names c = SOME ffis ==> EVERY
        (\x. ?s. x = ffi_ExtCall s) ffis) /\ ~(semantics
        (lab_to_targetProof_make_init mc_conf ffi t m dm sdm ms code
       (lab_to_target_compile asm_conf) (target_get_pc
         (machine_config_target mc_conf) ms + n2w (LENGTH bytes))
         cbspace
       coracle) = ffi_Fail) ==>
     machine_sem mc_conf ffi ms =
     {semantics (lab_to_targetProof_make_init mc_conf ffi t m dm
       sdm ms code
       (lab_to_target_compile asm_conf) (target_get_pc
         (machine_config_target mc_conf) ms + n2w (LENGTH bytes))
         cbspace
       coracle)}`)
  CHEAT_TAC;;

(* HOL4 lab_to_targetProofScript.sml:11167-11171: a theorem that HOL4
   states as the value of an ML expression: semantics_compile_lemma *)

(* try to show the condition of semantics_compile is not vacuous *)
(* HOL4 lab_to_targetProofScript.sml:11174-11199: code that the
   source has in a comment *)
(* HOL4 lab_to_targetProofScript.sml:11200-11245: code that the
   source has in a comment *)

let lab_to_targetProof_semantics_compile =
  cake_theorem "semantics_compile"
  (fun () ->
    `mc_conf_ok mc_conf /\
     (no_share_mem_inst code ==>
       compiler_oracle_ok coracle (lab_to_target_config_labels c')
         (LENGTH bytes) asm_conf (machine_config_ffi_names mc_conf)) /\
     lab_to_targetProof_good_code asm_conf
       (lab_to_target_config_labels c) code /\
     asm_conf = target_config (machine_config_target mc_conf) /\
       lab_to_target_config_labels
     c = LN /\ lab_to_target_config_pos c = 0 /\
     compile asm_conf c (code:('a sec) list) = SOME (bytes,c') /\
       ffi_names
     c' = SOME (machine_config_ffi_names mc_conf) /\
     good_init_state mc_conf ms bytes cbspace t m dm sdm /\
     mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i
       /\
     MAP (\rec. w2n (target_get_pc (machine_config_target mc_conf)
       ms) + shmem_info_num_entry_pc rec)
       (lab_to_target_config_shmem_extra c') =
      DROP i (MAP w2n (machine_config_ffi_entry_pcs mc_conf)) /\
        machine_config_mmio_info
     mc_conf = ZIP (GENLIST (\index. index + i) (LENGTH
       (lab_to_target_config_shmem_extra c')))
                              (MAP (\rec. (shmem_info_num_nbytes
                                rec,Addr (shmem_info_num_addr_reg rec)
                                (n2w (shmem_info_num_addr_off
                                rec)),shmem_info_num_reg
                              rec,n2w (shmem_info_num_exit_pc rec)
                                + target_get_pc (machine_config_target
                                mc_conf) ms))
                                (lab_to_target_config_shmem_extra
                              c')) /\
     no_install_or_no_share_mem code (machine_config_ffi_names
       mc_conf) /\
     // to avoid the ffi_entry_pc wraps around and overlaps with the program or code buffer
     cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword (:'a)
       /\
     (
      // the original ffi names provided does not contain MappedRead or MappedWrite
      !ffis. ffi_names c = SOME ffis ==> EVERY (\x. ?s. x =
        ffi_ExtCall s) ffis) ==>
      implements' T (machine_sem mc_conf ffi ms)
        {semantics
           (lab_to_targetProof_make_init mc_conf ffi t m (dm INTER
             byte_aligned) (sdm INTER byte_aligned) ms code
              (compile asm_conf) (target_get_pc
                (machine_config_target mc_conf) ms + n2w (LENGTH bytes))
              cbspace coracle)}`)
  CHEAT_TAC;;

cake_hide [];;

cake_hide_consts [];;
