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
needs "compiler/backend/semantics/targetProps.ml";;
needs "compiler/backend/semantics/targetSem.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
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
needs "semantics/proofs/semanticsProps.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "lab_to_targetProof"
  ["asm"; "asmProps"; "asmSem"; "ffi"; "labProps"; "labSem";
   "lab_filterProof"; "lab_to_target"; "stack_removeProof";
   "targetProps"; "targetSem"; "wordSem"];;

let _ = do_list hide_constant ["contain"; "invariant"; "not"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["failed","pegexec_failed"];;

(* HOL4 lab_to_targetProofScript.sml:16: ML code, not ported *)

(* [local] *)
let evaluate_ignore_clocks = prove
 (`labSem_evaluate mc_conf ffi k ms = (r1,ms1,st1) /\ ~(r1 =
  targetSem_TimeOut) /\
     labSem_evaluate mc_conf ffi k' ms = (r2,ms2,st2) /\ ~(r2 =
       targetSem_TimeOut) ==>
     (r1,ms1,st1) = (r2,ms2,st2)`,
  CHEAT_TAC);;

let _ = size_thms "line";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let sec_loc_to_pc_def,sec_loc_to_pc_ind = define_wf
  `MEASURE (\(x0,x1). list_size (line_size (\x. 0)) x1)`
  [`(sec_loc_to_pc n2 xs =
    (if n2 = 0 then SOME 0 else match xs with [] -> NONE | (CONS z
      zs) ->
      (if (?n1 k. z = labLang_Label n1 n2 k) then SOME 0 else if
        is_Label z then sec_loc_to_pc n2 zs else OPTION_MAP SUC
        (sec_loc_to_pc n2 zs))))`];;

(* HOL4 lab_to_targetProofScript.sml:39: ML code, not ported *)

let sec_loc_to_pc_cons = prove
 (`sec_loc_to_pc n2 (CONS l lines) =
   (if n2 = 0 \/ (?n1 k. l = labLang_Label n1 n2 k) then SOME 0
     else OPTION_MAP (if is_Label l then I else SUC) (sec_loc_to_pc n2
     lines))`,
  CHEAT_TAC);;

(* HOL4 lab_to_targetProofScript.sml:49: the overload len_no_lab,
   which the port expands *)

let loc_to_pc_thm = prove
 (`!n1 n2 ls.
     ALL sec_labels_ok ls ==>
     loc_to_pc n1 n2 ls =
       (match ls with [] -> NONE | (CONS (Section k xs) ys) ->
         (if n1 = k then
           match sec_loc_to_pc n2 xs with NONE -> OPTION_MAP ((+)
             (LENGTH (FILTER ((~) o is_Label) xs))) (loc_to_pc n1 n2
             ys) | x -> x else OPTION_MAP ((+) (LENGTH (FILTER ((~) o
             is_Label) xs))) (loc_to_pc n1 n2 ys)))`,
  CHEAT_TAC);;

(* -- *)

(* -- evaluate-level semantics preservation of compiler -- *)

(* relate asm step to evaluate step *)

let enc_with_nop_def = new_definition
  `enc_with_nop enc (b:'a asm) bytes =
     (let init = enc b in
     let step = enc (asm_Inst asm_Skip) in
       if LENGTH step = 0 then bytes = init else
         let n = (LENGTH bytes - LENGTH init) DIV LENGTH step in
           bytes = APPEND init (FLAT (REPLICATE n step)))`;;

(* [local] *)
let enc_with_nop_thm = prove
 (`enc_with_nop enc (b:'a asm) bytes =
       (?n. bytes = APPEND (enc b) (FLAT (REPLICATE n (enc
         (asm_Inst asm_Skip)))))`,
  CHEAT_TAC);;

let asm_step_nop_def = new_definition
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

(* [local] *)
let shift_interfer_0 = prove
 (`shift_interfer 0 = I`,
  CHEAT_TAC);;

(* [local] *)
let upd_pc_with_pc = prove
 (`labSem_upd_pc (asm_state_pc s1) s1 = (s1:'a asm_state)`,
  CHEAT_TAC);;

(* [simp] *)
let shift_interfer_twice = prove
 (`shift_interfer l' (shift_interfer l c) =
    shift_interfer (l + l') c`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_nop_steps = prove
 (`!n s1 ms1 c.
       encoder_correct (machine_config_target c) /\
         machine_config_prog_addresses
       c = asm_state_mem_domain s1 /\
       ffi_entry_pcs_disjoint c s1
         (n * LENGTH (asm_config_encode (target_config
           (machine_config_target c)) (asm_Inst asm_Skip))) /\
       interference_ok (machine_config_next_interfer c) (target_proj
         (machine_config_target c) (asm_state_mem_domain s1)) /\
       bytes_in_memory (asm_state_pc s1)
         (FLAT (REPLICATE n (asm_config_encode (target_config
           (machine_config_target c)) (asm_Inst asm_Skip))))
           (asm_state_mem s1) (asm_state_mem_domain
         s1) /\
       (match link_reg (target_config (machine_config_target c)) with
         NONE -> T | SOME r -> asm_state_lr s1 = r) /\
       (asm_state_be s1 <=> asm_config_big_endian (target_config
         (machine_config_target c))) /\ asm_state_align
       s1 = asm_config_code_alignment (target_config
         (machine_config_target c)) /\ ~(asm_state_failed s1) /\
       target_state_rel (machine_config_target c) (s1:'a asm_state)
         (ms1:'state) ==>
       (?l ms2.
         !k.
           (labSem_evaluate c io (k + l) ms1 =
            labSem_evaluate (shift_interfer l c) io k ms2) /\
           (find_next_interference c io (k + l) ms1 =
            find_next_interference (shift_interfer l c) io k ms2) /\
           target_state_rel (machine_config_target c)
             (labSem_upd_pc
               (asm_state_pc s1 +
                n2w (n * LENGTH (asm_config_encode (target_config
                  (machine_config_target c)) (asm_Inst asm_Skip)))) s1)
             ms2)`,
  CHEAT_TAC);;

let ffi_entry_pcs_disjoint_LENGTH_shorter = prove
 (`!l1 l2.
     ffi_entry_pcs_disjoint c s1 l1 /\
     l2 <= l1 ==>
     ffi_entry_pcs_disjoint c s1 l2`,
  CHEAT_TAC);;

let asm_step_IMP_evaluate_step_nop = prove
 (`!c s1 ms1 io i s2 bytes.
      encoder_correct (machine_config_target c) /\
        machine_config_prog_addresses
      c = asm_state_mem_domain s1 /\
      ffi_entry_pcs_disjoint c s1 (LENGTH bytes) /\
      interference_ok (machine_config_next_interfer c) (target_proj
        (machine_config_target c) (asm_state_mem_domain s1)) /\
      bytes_in_memory (asm_state_pc s1) bytes (mem s2)
        (asm_state_mem_domain s1) /\
      asm_step_nop bytes (target_config (machine_config_target c)) s1
        i s2 /\
      s2 = asmSem_asm i (asm_state_pc s1 + n2w (LENGTH bytes)) s1 /\
      target_state_rel (machine_config_target c) (s1:'a asm_state)
        (ms1:'state) /\
      (!x. ~(i = asm_Call x)) ==>
      (?l ms2.
        !k.
          (labSem_evaluate c io (k + l) ms1 =
           labSem_evaluate (shift_interfer l c) io k ms2) /\
          (find_next_interference c io (k + l) ms1 =
           find_next_interference (shift_interfer l c) io k ms2) /\
          target_state_rel (machine_config_target c) s2 ms2 /\ ~(l
            = 0))`,
  CHEAT_TAC);;

(* define relation between labSem and targetSem states *)

let lab_lookup_def = new_definition
  `lab_lookup k1 k2 labs =
     (match sptree_lookup k1 labs with NONE -> NONE | SOME f ->
       sptree_lookup k2 f)`;;

(* [local] *)
let lab_lookup_IMP = prove
 (`(lab_lookup l1 l2 labs = SOME x) ==>
     (find_pos (labLang_Lab l1 l2) labs = x)`,
  CHEAT_TAC);;

let labs_domain_def = new_definition
  `labs_domain labs = {(n1,n2) | ~(lab_lookup n1 n2 labs = NONE)}`;;

(* [simp] *)
let labs_domain_LN = prove
 (`labs_domain LN = {}`,
  CHEAT_TAC);;

let labs_domain_insert = prove
 (`~(k IN domain labs) ==>
      labs_domain (sptree_insert k s labs) = IMAGE (\n2. (k,n2))
        (domain s) UNION labs_domain labs`,
  CHEAT_TAC);;


(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let has_odd_inst_def,has_odd_inst_ind = define_guess_cheat
  [`has_odd_inst [] = F`;
   `has_odd_inst (CONS (Section k []) xs) = has_odd_inst xs`;
   `has_odd_inst (CONS (Section k (CONS y ys)) xs) <=>
         ~(EVEN (line_length y)) \/ has_odd_inst (CONS (Section
           k ys) xs)`];;

let line_similar_def = new_definition
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

let _ = size_thms "sec";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let code_similar_def,code_similar_ind = define_wf
  `MEASURE (\(x0,x1). list_size (sec_size (\x. 0)) x0 + list_size
  (sec_size (\x. 0)) x1)`
  [`code_similar x1 x2 =
        match (x1,x2) with
          ([],[]) -> T
        | (CONS (Section s1 lines1) rest1,CONS (Section s2 lines2)
          rest2) ->
        code_similar rest1 rest2 /\
        ALL2 line_similar lines1 lines2 /\ (s1 = s2)
        | (_3,_4) -> F`];;

(* HOL4 lab_to_targetProofScript.sml:408: ML code, not ported *)

let line_similar_sym = prove
 (`line_similar l1 l2 ==> line_similar l2 l1`,
  CHEAT_TAC);;

let code_similar_sym = prove
 (`!code1 code2. code_similar code1 code2 ==> code_similar code2 code1`,
  CHEAT_TAC);;

(* [simp] *)
let line_similar_refl = prove
 (`!l. line_similar l l`,
  CHEAT_TAC);;

(* [simp] *)
let code_similar_refl = prove
 (`!code. code_similar code code`,
  CHEAT_TAC);;

(* [local] *)
let line_similar_trans = prove
 (`line_similar x y /\ line_similar y z ==> line_similar x z`,
  CHEAT_TAC);;

let code_similar_trans = prove
 (`!c1 c2 c3. code_similar c1 c2 /\ code_similar c2 c3 ==>
  code_similar c1 c3`,
  CHEAT_TAC);;

let code_similar_nil = prove
 (`(code_similar [] l <=> l = []) /\
   (code_similar l [] <=> l = [])`,
  CHEAT_TAC);;

let code_similar_append = prove
 (`!l1 l2 r1 r2.
     code_similar l1 l2 /\
     code_similar r1 r2 ==>
     code_similar (APPEND l1 r1) (APPEND l2 r2)`,
  CHEAT_TAC);;

let line_similar_sec_label_ok = prove
 (`!l1 l2.
   ALL (sec_label_ok s) l1 /\
   ALL2 line_similar l1 l2 ==>
   ALL (sec_label_ok s) l2`,
  CHEAT_TAC);;

let code_similar_sec_labels_ok = prove
 (`!c1 c2.
   ALL sec_labels_ok c1 /\
   code_similar c1 c2 ==>
   ALL sec_labels_ok c2`,
  CHEAT_TAC);;

let line_similar_len_no_lab = prove
 (`!l1 l2.
   ALL2 line_similar l1 l2 ==>
   (\xs. LENGTH (FILTER ((~) o is_Label) xs)) l1 = (\xs. LENGTH
     (FILTER ((~) o is_Label) xs)) l2`,
  CHEAT_TAC);;

let code_similar_len_no_lab = prove
 (`!(c1:('a sec) list) (c2:('a sec) list).
   code_similar c1 c2 ==>
   MAP ((\xs. LENGTH (FILTER ((~) o is_Label) xs)) o Section_lines)
     c1 =
   MAP ((\xs. LENGTH (FILTER ((~) o is_Label) xs)) o Section_lines)
     c2`,
  CHEAT_TAC);;

let word_loc_val_def = define_cases
  [`word_loc_val p labs (wordLang_Word w) = SOME w`;
   `word_loc_val p labs (wordLang_Loc k1 k2) =
         (match lab_lookup k1 k2 labs with NONE -> NONE | SOME
           q -> SOME (p + n2w q))`];;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let has_io_name_def,has_io_name_ind = define_guess_cheat
  [`has_io_name index [] = F`;
   `has_io_name index (CONS (Section k []) xs) = has_io_name index xs`;
   `has_io_name index (CONS (Section k (CONS y ys)) xs) <=>
         has_io_name index (CONS (Section k ys) xs) \/
         (match y with labLang_LabAsm (labLang_CallFFI i) _5 _6
           _7 -> (i = index) | _8 -> F)`];;

(* HOL4 lab_to_targetProofScript.sml:532: ML code, not ported *)

let word_loc_val_byte_def = new_definition
  `word_loc_val_byte p labs m a be' =
     (match word_loc_val p labs (m (byte_align a)) with SOME w ->
       SOME (get_byte a w be') | NONE -> NONE)`;;

let line_ok_def = new_definition
  `line_ok c labs ffis pos x5 =
        match (c,x5) with
          ((c:'a asm_config),labLang_Label _11 _12 l) ->
        EVEN pos /\ (l = 0)
        | (c,(labLang_Asm b bytes l)) ->
        enc_with_nop (asm_config_encode c) (cbw_to_asm b) bytes /\
        (LENGTH bytes = l) /\ asm_ok (cbw_to_asm b) c
        | (c,(labLang_LabAsm labLang_Halt w bytes l)) ->
        (let w1 = ((n2w 0):'a word) - n2w (pos + ffi_offset) in
          enc_with_nop (asm_config_encode c) (labLang_Jump w1) bytes
            /\
          (LENGTH bytes = l) /\ asm_ok (labLang_Jump w1) c)
        | (c,(labLang_LabAsm labLang_Install w bytes l)) ->
        (let w1 = ((n2w 0):'a word) - n2w (pos + 2 * ffi_offset) in
          enc_with_nop (asm_config_encode c) (labLang_Jump w1) bytes
            /\
          (LENGTH bytes = l) /\ asm_ok (labLang_Jump w1) c)
        | (c,(labLang_LabAsm (labLang_CallFFI index) w bytes l)) ->
        (let w1 = ((n2w 0):'a word) - n2w (pos + (3 + get_ffi_index
          ffis (ffi_ExtCall index)) * ffi_offset) in
          enc_with_nop (asm_config_encode c) (labLang_Jump w1) bytes
            /\
          (LENGTH bytes = l) /\ asm_ok (labLang_Jump w1) c)
        | (c,(labLang_LabAsm (labLang_Call v24) w bytes l)) ->
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

let lines_ok_def,lines_ok_ind = define_rec
  [`lines_ok c labs ffis pos [] = T`;
   `lines_ok c labs ffis pos (CONS y ys) <=>
       line_ok c labs ffis pos y /\
       lines_ok c labs ffis (pos + line_length y) ys`];;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let all_enc_ok_def,all_enc_ok_ind = define_guess_cheat
  [`all_enc_ok c labs ffis pos [] = T`;
   `all_enc_ok c labs ffis pos (CONS (Section k []) xs) <=>
         EVEN pos /\ all_enc_ok c labs ffis pos xs`;
   `all_enc_ok c labs ffis pos (CONS (Section k (CONS y ys)) xs) <=>
         line_ok c labs ffis pos y /\
         all_enc_ok c labs ffis (pos + line_length y) (CONS
           (Section k ys) xs)`];;

(* HOL4 lab_to_targetProofScript.sml:589: ML code, not ported *)

let all_enc_ok_cons = prove
 (`!ls pos.
   all_enc_ok c labs ffis pos (CONS (Section k ls) xs) <=>
   all_enc_ok c labs ffis (pos + SUM (MAP line_length ls)) xs /\
   EVEN (pos + SUM (MAP line_length ls)) /\
   lines_ok c labs ffis pos ls`,
  CHEAT_TAC);;

let _ = size_thms "sec";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let pos_val_def,pos_val_ind = define_wf
  `MEASURE (\(x0,x1,x2). list_size (sec_size (\x. 0)) x2)`
  [`pos_val i (pos:num) [] = (pos:num)`;
   `pos_val i (pos:num) (CONS (Section k []) xs) = ((pos_val i pos
  xs):num)`;
   `pos_val i (pos:num) (CONS (Section k (CONS y ys)) xs) =
         ((if is_Label y then pos_val i (pos + line_length y)
           (CONS (Section k ys) xs) else if i = (0:num) then pos
           else pos_val (i - 1) (pos + line_length y) (CONS
           (Section k ys) xs)):num)`];;

(* HOL4 lab_to_targetProofScript.sml:612: ML code, not ported *)

let pos_val_0 = prove
 (`!xs c enc labs ffis pos.
      all_enc_ok c labs ffis pos xs ==> (pos_val 0 pos xs = pos)`,
  CHEAT_TAC);;

let sec_pos_val_def,sec_pos_val_ind = define_rec
  [`sec_pos_val i pos [] = NONE`;
   `sec_pos_val i pos (CONS y ys) =
       (if is_Label y then
         sec_pos_val i (pos + line_length y) ys else if i = 0
           then SOME pos else sec_pos_val (i - 1) (pos +
           line_length y) ys)`];;

let sec_pos_val_too_big = prove
 (`!i pos lines.
    LENGTH (FILTER ((~) o is_Label) lines) <= i ==> sec_pos_val i
      pos lines = NONE`,
  CHEAT_TAC);;

let EVERY_is_Label_sec_pos_val = prove
 (`!n pos lines. ALL is_Label lines ==> sec_pos_val n pos lines = NONE`,
  CHEAT_TAC);;

(* [local] *)
let pos_val_thm0 = prove
 (`!i pos acc.
     pos_val i pos acc =
       (match acc with [] -> pos | CONS (Section k s) ss ->
         (match sec_pos_val i pos s with NONE ->
         pos_val (i - LENGTH (FILTER ((~) o is_Label) s)) (pos +
           SUM (MAP line_length s)) ss | SOME x -> x))`,
  CHEAT_TAC);;

let pos_val_thm = prove
 (`(pos_val i pos [] = pos) /\
   (pos_val i pos (CONS (Section k s) ss) =
    (match sec_pos_val i pos s with NONE ->
      pos_val (i - LENGTH (FILTER ((~) o is_Label) s)) (pos + SUM
        (MAP line_length s)) ss | SOME x -> x))`,
  CHEAT_TAC);;

let lab_to_targetProof_good_code_def = new_definition
  `lab_to_targetProof_good_code c labs code <=>
    ALL sec_ends_with_label code /\
    ALL sec_labels_ok code /\
    ALL_DISTINCT (MAP Section_num code) /\
    ALL (ALL_DISTINCT o labProps_extract_labels o Section_lines) code
      /\
    DISJOINT (domain labs) (set_of_list (MAP Section_num code)) /\
    restrict_nonzero (labProps_get_labels code) SUBSET
      labProps_get_code_labels code UNION labs_domain labs /\
    (\c ls. ALL (sec_ok_pre c) ls) c code`;;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let num_pcs_def,num_pcs_ind = define_guess_cheat
  [`num_pcs [] = (0:num)`;
   `num_pcs (CONS (Section _13 []) rest) = ((num_pcs rest):num)`;
   `num_pcs (CONS (Section k (CONS x xs)) rest) = ((if is_Label x
  then num_pcs (CONS (Section k xs) rest) else 1 + num_pcs (CONS
  (Section k xs) rest)):num)`];;

let share_mem_domain_code_rel_def = new_definition
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

let share_mem_state_rel_def = new_definition
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
            APPEND (let w = target_get_reg (machine_config_target
              mc_conf) ms2 re in
               if nb = (n2w 0) then word_to_bytes w F else
                 word_to_bytes_aux (w2n nb) w F) (word_to_bytes ad' F))
                 =
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

let no_install_or_no_share_mem_def = new_definition
  `no_install_or_no_share_mem code ffi_names' <=>
    (no_share_mem_inst code /\
     ALL (\x. ?s. x = ffi_ExtCall s) ffi_names') \/
     labProps_no_install code`;;

(* The lab-level oracles record the register residues that the machine run
   starting from ms actually leaves behind: the k-th entry of each family is
   read off the k-th interference application of that family.
   This is positional, so it is kept out of state_rel (which is closed under
   shift_interfer) and threaded through compile_correct separately. *)
let oracle_tie_def = new_definition
  `oracle_tie (mc_conf:('a,'state,'b)machine_config) ms
  (s1:('a,'c,'ffi)labSem_state) <=> labSem_state_io_regs
     s1 = target_io_regs mc_conf (labSem_state_ffi s1) ms /\
       labSem_state_io_fp_regs
     s1 = target_io_fp_regs mc_conf (labSem_state_ffi s1) ms /\
       labSem_state_cc_regs
     s1 = target_cc_regs mc_conf (labSem_state_ffi s1) ms /\
       labSem_state_cc_fp_regs
     s1 = target_cc_fp_regs mc_conf (labSem_state_ffi s1) ms`;;

let oracle_tie_shift_interfer = prove
 (`oracle_tie mc_conf ms1 s1 /\
   (!k. find_next_interference mc_conf (labSem_state_ffi s1) (k + l)
     ms1 =
        find_next_interference (shift_interfer l mc_conf)
          (labSem_state_ffi s1) k ms2) ==>
   oracle_tie (shift_interfer l mc_conf) ms2 s1`,
  CHEAT_TAC);;

let oracle_tie_step = prove
 (`oracle_tie mc_conf ms1 (s1:('a,'c,'ffi)labSem_state) /\
   (!k. find_next_interference mc_conf (labSem_state_ffi s1) (k + l)
     ms1 =
        find_next_interference (shift_interfer l mc_conf)
          (labSem_state_ffi s1) k ms2) /\ labSem_state_io_regs
   (s2:('a,'c,'ffi)labSem_state) = labSem_state_io_regs s1 /\
     labSem_state_io_fp_regs
   s2 = labSem_state_io_fp_regs s1 /\ labSem_state_cc_regs
   s2 = labSem_state_cc_regs s1 /\ labSem_state_cc_fp_regs s2 =
     labSem_state_cc_fp_regs s1 /\ labSem_state_ffi
   s2 = labSem_state_ffi s1 ==>
   oracle_tie (shift_interfer l mc_conf) ms2 s2`,
  CHEAT_TAC);;

let oracle_tie_ffi_step = prove
 (`oracle_tie mc_conf ms1 s1 /\
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
   target_cc_fp_regs mc' ffi' ms_post = labSem_state_cc_fp_regs s1`,
  CHEAT_TAC);;

let oracle_tie_ccache_step = prove
 (`oracle_tie mc_conf ms1 s1 /\
   next_interference mc_conf (labSem_state_ffi s1) ms1 =
     SOME (CcApp a1 a2 ms_pre ms_post,mc',ffi') ==>
   (!r. labSem_state_cc_regs
      s1 0 r =
        (if MEM r (machine_config_callee_saved_regs mc_conf) \/ r =
          machine_config_ptr_reg mc_conf \/
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
   target_io_fp_regs mc' ffi' ms_post = labSem_state_io_fp_regs s1`,
  CHEAT_TAC);;

let oracle_tie_ffi_next = prove
 (`oracle_tie mc_conf ms1 (s1:('a,'c,'ffi)labSem_state) /\
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
   oracle_tie mc' ms_post s2`,
  CHEAT_TAC);;

let oracle_tie_ccache_next = prove
 (`oracle_tie mc_conf ms1 (s1:('a,'c,'ffi)labSem_state) /\
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
   oracle_tie mc' ms_post s2`,
  CHEAT_TAC);;

let oracle_tie_ExtCall_residues = prove
 (`!mc_conf ms1 s1 ms2 l index name bytes bytes2 new_ffi new_bytes t1.
   oracle_tie mc_conf ms1 (s1:('a,'c,'ffi)labSem_state) /\
   (!k. find_next_interference mc_conf (labSem_state_ffi s1) (k + l)
     ms1 =
        find_next_interference
          (machine_config_next_interfer_fupd (K (misc_shift_seq l
            (machine_config_next_interfer mc_conf))) mc_conf)
            (labSem_state_ffi
          s1) k ms2) /\ ~(target_get_pc (machine_config_target
   mc_conf) ms2 IN machine_config_prog_addresses mc_conf DIFF
     set_of_list (machine_config_ffi_entry_pcs mc_conf)) /\
     ~(target_get_pc (machine_config_target
   mc_conf) ms2 = machine_config_halt_pc mc_conf) /\ ~(target_get_pc
     (machine_config_target
   mc_conf) ms2 = machine_config_ccache_pc mc_conf) /\
   find_index (target_get_pc (machine_config_target mc_conf) ms2)
     (machine_config_ffi_entry_pcs mc_conf) 0 = SOME index /\
   EL index (machine_config_ffi_names mc_conf) = ffi_ExtCall name /\
   ALOOKUP (machine_config_mmio_info mc_conf) index = NONE /\
   read_ffi_bytearrays mc_conf ms2 = (SOME bytes,SOME bytes2) /\
   call_FFI (labSem_state_ffi s1) (ffi_ExtCall name) bytes bytes2 =
     FFI_return new_ffi new_bytes ==>
   (\a. get_reg_value (labSem_state_io_regs s1 0 (ffi_ExtCall name)
     a) (asm_state_regs t1 a) I) =
     (\a. if MEM a (machine_config_callee_saved_regs mc_conf) \/
             ~(a < asm_config_reg_count (target_config
               (machine_config_target mc_conf))) \/
             MEM a (asm_config_avoid_regs (target_config
               (machine_config_target mc_conf))) then asm_state_regs t1
               a else target_get_reg (machine_config_target mc_conf)
                 (machine_config_ffi_interfer mc_conf 0
                   (index,new_bytes,ms2)) a) /\
   (\n. labSem_state_io_fp_regs s1 0 n) =
     (\n. target_get_fp_reg (machine_config_target mc_conf)
            (machine_config_ffi_interfer mc_conf 0
              (index,new_bytes,ms2)) n)`,
  CHEAT_TAC);;

(* The code buffer is set-up to immediately follow the current code:
  |---code---|---cb---|
*)
let lab_to_targetProof_state_rel_def = new_definition
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
     ALL sec_labels_ok code2 /\
     code_similar (labSem_state_code s1) code2 /\
     share_mem_state_rel mc_conf s1 t1 ms1 /\
     share_mem_domain_code_rel mc_conf p code2
       (labSem_state_shared_mem_domain s1) /\
     LENGTH (machine_config_ffi_names mc_conf) = LENGTH
       (machine_config_ffi_entry_pcs mc_conf) /\
     no_install_or_no_share_mem code2 (machine_config_ffi_names
       mc_conf)`;;

let oracle_tie_clock = prove
 (`oracle_tie mc_conf ms s1 ==>
   oracle_tie mc_conf ms (labSem_state_clock_fupd (K k) s1)`,
  CHEAT_TAC);;

(* state_rel_clock *)
let lab_to_targetProof_state_rel_clock = prove
 (`lab_to_targetProof_state_rel x s1 t1 ms ==>
     lab_to_targetProof_state_rel x (labSem_state_clock_fupd (K k)
       s1) (t1) ms`,
  CHEAT_TAC);;

let share_mem_state_rel_shift_interfer = prove
 (`share_mem_state_rel mc_conf s1 t1 x ==>
     share_mem_state_rel (machine_config_next_interfer_fupd (K (\i.
       machine_config_next_interfer mc_conf (i + l))) mc_conf)
       s1 t1 x`,
  CHEAT_TAC);;

let share_mem_domain_code_rel_shift_interfer = prove
 (`share_mem_domain_code_rel mc_conf p code2
  (labSem_state_shared_mem_domain s1) ==>
   share_mem_domain_code_rel
     (machine_config_next_interfer_fupd (K (\i.
       machine_config_next_interfer mc_conf (i + l))) mc_conf)
     p code2 (labSem_state_shared_mem_domain s1)`,
  CHEAT_TAC);;

let state_rel_shift_interfer = prove
 (`lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 x ==>
     lab_to_targetProof_state_rel (shift_interfer l
       mc_conf,code2,labs,p) s1 t1 x`,
  CHEAT_TAC);;

(* bytes_in_memory lemmas *)
(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let prog_to_bytes_lemma = prove
 (cake_as_vars (fun () ->
    `!code2 code1 pc' i pos.
         code_similar code1 code2 /\
         all_enc_ok (target_config (machine_config_target
           (mc_conf:('a,'state,'b)machine_config)))
           labs ffi_names pos code2 /\
         (asm_fetch_aux pc' code1 = SOME i) ==>
         (?bs j bs2.
           (prog_to_bytes code2 = APPEND (APPEND bs (line_bytes j))
             bs2) /\
           (LENGTH bs + pos = pos_val pc' pos code2) /\
           (LENGTH bs + pos + LENGTH (line_bytes j) = pos_val (pc'
             + 1) pos code2) /\
           line_similar i j /\
           line_ok (target_config (machine_config_target
             mc_conf)) labs ffi_names (pos_val pc' pos code2) j)`),
  CHEAT_TAC);;

(* HOL4 lab_to_targetProofScript.sml:1210-1212: ML code, not ported *)

(* [local] *)
let bytes_in_mem_APPEND = prove
 (`!xs ys a m md md1.
       bytes_in_mem a (APPEND xs ys) m md md1 <=>
       bytes_in_mem a xs m md md1 /\
       bytes_in_mem (a + n2w (LENGTH xs)) ys m md md1`,
  CHEAT_TAC);;

let bytes_in_mem_UPDATE = prove
 (`!ls a m md md2 w1 w2.
   (!n. n < LENGTH ls ==> ~(a + n2w n = w1)) /\
   bytes_in_mem a ls m md md2 ==>
   bytes_in_mem a ls ((w1 =+ w2) m) md md2`,
  CHEAT_TAC);;

(* HOL4 lab_to_targetProofScript.sml:1240: the ML values that the
   definitions below antiquote *)

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let IMP_bytes_in_memory = prove
 (cake_as_vars (fun () ->
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
         line_similar i j)`),
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let IMP_bytes_in_memory_JumpReg = prove
 (cake_as_vars (fun () ->
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
         (mc_conf:('a,'state,'b)machine_config)))`),
  CHEAT_TAC);;

(* HOL4 lab_to_targetProofScript.sml:1281-1284: ML code, not ported *)

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let IMP_bytes_in_memory_Jump = prove
 (cake_as_vars (fun () ->
    `code_similar (labSem_state_code
  (s1:('a,lab_to_target_config,'ffi)labSem_state)) code2 /\
       all_enc_ok (target_config (machine_config_target mc_conf))
         labs ffi_names 0 code2 /\
       bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1)
         (asm_state_mem_domain t1) (labSem_state_mem_domain s1) /\
       (asm_fetch s1 = SOME (labLang_LabAsm (asm_Jump jtarget) l
         bytes n)) ==>
       (?tt enc.
         (tt = n2w (find_pos jtarget labs) -
               n2w (pos_val (labSem_state_pc s1) 0 code2)) /\
         (enc = asm_config_encode (target_config
           (machine_config_target mc_conf)) (asm_Jump tt)) /\
         bytes_in_memory ((p:'a word) + n2w (pos_val
           (labSem_state_pc s1) 0 code2))
           enc (asm_state_mem t1) (asm_state_mem_domain t1) /\
         asm_ok (asm_Jump tt) (target_config
           (machine_config_target
           (mc_conf:('a,'state,'b)machine_config))))`),
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let IMP_bytes_in_memory_JumpCmp = prove
 (cake_as_vars (fun () ->
    `code_similar (labSem_state_code
  (s1:('a,lab_to_target_config,'ffi)labSem_state)) code2 /\
       all_enc_ok (target_config (machine_config_target mc_conf))
         labs ffi_names 0 code2 /\
       bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1)
         (asm_state_mem_domain t1) (labSem_state_mem_domain s1) /\
       (asm_fetch s1 = SOME (labLang_LabAsm (asm_JumpCmp cmp rr ri
         jtarget) l bytes n)) ==>
       (?tt enc.
         (tt = n2w (find_pos jtarget labs) -
               n2w (pos_val (labSem_state_pc s1) 0 code2)) /\
         (enc = asm_config_encode (target_config
           (machine_config_target mc_conf)) (asm_JumpCmp cmp rr ri tt))
           /\
         bytes_in_memory ((p:'a word) + n2w (pos_val
           (labSem_state_pc s1) 0 code2))
           enc (asm_state_mem t1) (asm_state_mem_domain t1) /\
         asm_ok (asm_JumpCmp cmp rr ri tt) (target_config
           (machine_config_target
           (mc_conf:('a,'state,'b)machine_config))))`),
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let IMP_bytes_in_memory_JumpCmp_1 = prove
 (cake_as_vars (fun () ->
    `code_similar (labSem_state_code
  (s1:('a,lab_to_target_config,'ffi)labSem_state)) code2 /\
       all_enc_ok (target_config (machine_config_target mc_conf))
         labs ffi_names 0 code2 /\
       bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1)
         (asm_state_mem_domain t1) (labSem_state_mem_domain s1) /\
       (asm_fetch s1 = SOME (labLang_LabAsm (asm_JumpCmp cmp rr ri
         jtarget) l bytes n)) ==>
       (?tt bytes.
         (tt = n2w (find_pos jtarget labs) -
               n2w (pos_val (labSem_state_pc s1) 0 code2)) /\
         enc_with_nop (asm_config_encode (target_config
           (machine_config_target mc_conf))) (asm_JumpCmp cmp rr ri tt)
           bytes /\
         bytes_in_memory ((p:'a word) + n2w (pos_val
           (labSem_state_pc s1) 0 code2))
           bytes (asm_state_mem t1) (asm_state_mem_domain t1) /\
         (pos_val (labSem_state_pc s1 + 1) 0 code2 = pos_val
           (labSem_state_pc s1) 0 code2 + LENGTH bytes) /\
         asm_ok (asm_JumpCmp cmp rr ri tt) (target_config
           (machine_config_target
           (mc_conf:('a,'state,'b)machine_config))))`),
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let IMP_bytes_in_memory_Call = prove
 (cake_as_vars (fun () ->
    `code_similar (labSem_state_code
  (s1:('a,lab_to_target_config,'ffi)labSem_state)) code2 /\
       all_enc_ok (target_config (machine_config_target
         (mc_conf:('a,'state,'b)machine_config))) labs ffi_names 0
           code2 /\
       bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1)
         (asm_state_mem_domain
         (t1:'a asm_state)) (labSem_state_mem_domain s1) /\
       (asm_fetch s1 = SOME (labLang_LabAsm (asm_Call ww) l bytes
         n)) ==>
       F`),
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let IMP_bytes_in_memory_LocValue = prove
 (cake_as_vars (fun () ->
    `code_similar (labSem_state_code
  (s1:('a,lab_to_target_config,'ffi)labSem_state)) code2 /\
       all_enc_ok (target_config (machine_config_target mc_conf))
         labs ffi_names 0 code2 /\
       bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1)
         (asm_state_mem_domain t1) (labSem_state_mem_domain s1) /\
       (asm_fetch s1 = SOME (labLang_LabAsm (labLang_LocValue reg
         (labLang_Lab l1 l2)) l bytes n)) ==>
       (?tt bytes.
         (tt = n2w (find_pos (labLang_Lab l1 l2) labs) -
               n2w (pos_val (labSem_state_pc s1) 0 code2)) /\
         enc_with_nop (asm_config_encode (target_config
           (machine_config_target mc_conf))) (asm_Loc reg tt) bytes /\
         bytes_in_memory ((p:'a word) + n2w (pos_val
           (labSem_state_pc s1) 0 code2))
           bytes (asm_state_mem t1) (asm_state_mem_domain t1) /\
         (pos_val (labSem_state_pc s1 + 1) 0 code2 = pos_val
           (labSem_state_pc s1) 0 code2 + LENGTH bytes) /\
         asm_ok (asm_Loc reg tt) (target_config
           (machine_config_target
           (mc_conf:('a,'state,'b)machine_config))))`),
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let IMP_bytes_in_memory_Inst = prove
 (cake_as_vars (fun () ->
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
           (machine_config_target mc_conf))) (asm_Inst i) bytes /\
         bytes_in_memory ((p:'a word) + n2w (pos_val
           (labSem_state_pc s1) 0 code2))
           bytes (asm_state_mem t1) (asm_state_mem_domain t1) /\
         bytes_in_mem ((p:'a word) + n2w (pos_val (labSem_state_pc
           s1) 0 code2))
           bytes (asm_state_mem t1) (asm_state_mem_domain t1)
             (labSem_state_mem_domain s1) /\
         (pos_val (labSem_state_pc s1 + 1) 0 code2 = pos_val
           (labSem_state_pc s1) 0 code2 + LENGTH bytes) /\
         asm_ok (asm_Inst i) (target_config
           (machine_config_target
           (mc_conf:('a,'state,'b)machine_config))))`),
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let IMP_bytes_in_memory_Cbw = prove
 (cake_as_vars (fun () ->
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
           (machine_config_target mc_conf))) (asm_Inst (asm_Mem
           asm_Store8 r2 (Addr r1 (n2w 0)))) bytes /\
         bytes_in_memory ((p:'a word) + n2w (pos_val
           (labSem_state_pc s1) 0 code2))
           bytes (asm_state_mem t1) (asm_state_mem_domain t1) /\
         bytes_in_mem ((p:'a word) + n2w (pos_val (labSem_state_pc
           s1) 0 code2))
           bytes (asm_state_mem t1) (asm_state_mem_domain t1)
             (labSem_state_mem_domain s1) /\
         (pos_val (labSem_state_pc s1 + 1) 0 code2 = pos_val
           (labSem_state_pc s1) 0 code2 + LENGTH bytes) /\
         asm_ok (asm_Inst (asm_Mem asm_Store8 r2 (Addr r1 (n2w
           0)))) (target_config (machine_config_target
           (mc_conf:('a,'state,'b)machine_config))))`),
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let IMP_bytes_in_memory_CallFFI = prove
 (cake_as_vars (fun () ->
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
           (machine_config_target mc_conf)) (asm_Jump tt)) /\
         bytes_in_memory ((p:'a word) + n2w (pos_val
           (labSem_state_pc s1) 0 code2))
           enc (asm_state_mem t1) (asm_state_mem_domain t1) /\
         asm_ok (asm_Jump tt) (target_config
           (machine_config_target
           (mc_conf:('a,'state,'b)machine_config))))`),
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let IMP_bytes_in_memory_Halt = prove
 (cake_as_vars (fun () ->
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
           (machine_config_target mc_conf)) (asm_Jump tt)) /\
         bytes_in_memory ((p:'a word) + n2w (pos_val
           (labSem_state_pc s1) 0 code2))
           enc (asm_state_mem t1) (asm_state_mem_domain t1) /\
         asm_ok (asm_Jump tt) (target_config
           (machine_config_target
           (mc_conf:('a,'state,'b)machine_config))))`),
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let IMP_bytes_in_memory_Install = prove
 (cake_as_vars (fun () ->
    `code_similar (labSem_state_code
  (s1:('a,lab_to_target_config,'ffi)labSem_state)) code2 /\
       all_enc_ok (target_config (machine_config_target mc_conf))
         labs ffi_names 0 code2 /\
       bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1)
         (asm_state_mem_domain t1) (labSem_state_mem_domain s1) /\
       (asm_fetch s1 = SOME (labLang_LabAsm labLang_Install c l n))
         ==>
       (?tt enc.
         (tt = (n2w 0) - n2w (pos_val (labSem_state_pc s1) 0 code2
           + 2 * ffi_offset)) /\
         (enc = asm_config_encode (target_config
           (machine_config_target mc_conf)) (asm_Jump tt)) /\
         bytes_in_memory ((p:'a word) + n2w (pos_val
           (labSem_state_pc s1) 0 code2))
           enc (asm_state_mem t1) (asm_state_mem_domain t1) /\
         asm_ok (asm_Jump tt) (target_config
           (machine_config_target
           (mc_conf:('a,'state,'b)machine_config))))`),
  CHEAT_TAC);;

let all_enc_ok_asm_fetch_aux_IMP_line_ok = prove
 (`!pc' n code2.
     all_enc_ok c labs ffis n code2 /\
     asm_fetch_aux pc' code2 = SOME line ==>
     line_ok c labs ffis (pos_val pc' n code2) line`,
  CHEAT_TAC);;

let code_similar_IMP_asm_fetch_aux_line_similar = prove
 (`!pc' code1 code2.
     code_similar code1 code2 ==>
     OPTREL line_similar (asm_fetch_aux pc' code1) (asm_fetch_aux
       pc' code2)`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let asm_fetch_aux_pos_val_LENGTH_EQ = prove
 (cake_as_vars (fun () ->
    `!pc' n code2 line.
       asm_fetch_aux pc' code2 = SOME line /\
       all_enc_ok conf labs ffi_names n code2 /\
       pos_val (pc' + 1) n code2 = LENGTH bytes' + pos_val pc' n
         code2 ==>
       LENGTH (line_bytes line) = LENGTH (bytes':word8 list)`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let IMP_bytes_in_memory_ShareMem = prove
 (cake_as_vars (fun () ->
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
         (machine_config_target mc_conf))) (asm_Inst (asm_Mem mop r ad))
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
       asm_ok (asm_Inst (asm_Mem mop r ad)) (target_config
         (machine_config_target
         (mc_conf:('a,'state,'b)machine_config))))`),
  CHEAT_TAC);;

(* [local] *)
let bytes_in_mem_IMP_memory = prove
 (`!xs a.
       (!a. ~(a IN dm1) ==> m a = m1 a) ==>
       bytes_in_mem a xs m dm dm1 ==>
       bytes_in_memory a xs m1 dm`,
  CHEAT_TAC);;

(* read/write bytearrays for FFI *)

(* [local] *)
let read_bytearray_state_rel = prove
 (`!n a x.
       lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1
         /\
       (read_bytearray a n (mem_load_byte_aux (labSem_state_mem s1)
         (labSem_state_mem_domain s1) (labSem_state_be s1)) = SOME x)
         ==>
       (read_bytearray a n
         (\a. if a IN machine_config_prog_addresses mc_conf then SOME
           (asm_state_mem t1 a) else NONE) =
        SOME x)`,
  CHEAT_TAC);;

(* [local] *)
let IMP_has_io_name = prove
 (`(asm_fetch s1 = SOME (labLang_LabAsm (labLang_CallFFI index) l bytes
  n)) ==>
     has_io_name index (labSem_state_code s1)`,
  CHEAT_TAC);;

(* [local] *)
let bytes_in_mem_asm_write_bytearray_lemma = prove
 (`!xs p.
       (!a. ~(a IN k) ==> (m1 a = m2 a)) ==>
       bytes_in_mem p xs m1 d k ==>
       bytes_in_mem p xs m2 d k`,
  CHEAT_TAC);;

(* [local] *)
let bytes_in_mem_asm_write_bytearray = prove
 (`(!a. byte_align a IN labSem_state_mem_domain s1 ==> a IN
  labSem_state_mem_domain s1) /\
     (read_bytearray c1 (LENGTH new_bytes) (mem_load_byte_aux
       (labSem_state_mem s1) (labSem_state_mem_domain s1)
       (labSem_state_be s1)) = SOME x) ==>
     bytes_in_mem p xs (asm_state_mem t1) (asm_state_mem_domain t1)
       (labSem_state_mem_domain s1) ==>
     bytes_in_mem p xs
       (asm_write_bytearray c1 new_bytes (asm_state_mem t1))
         (asm_state_mem_domain t1) (labSem_state_mem_domain s1)`,
  CHEAT_TAC);;

(* [local] *)
let write_bytearray_NOT_Loc = prove
 (`!xs c1 s1 a c.
       (labSem_state_mem s1 a = wordLang_Word c) ==>
         ~((write_bytearray c1 xs (labSem_state_mem s1)
         (labSem_state_mem_domain s1) (labSem_state_be s1)) a =
         asm_Loc n n0)`,
  CHEAT_TAC);;

(* [local] *)
let CallFFI_bytearray_lemma = prove
 (`byte_align (a:'a word) IN labSem_state_mem_domain s1 /\ good_dimindex
  (:'a) /\
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
      SOME (asm_write_bytearray c1 new_bytes (asm_state_mem t1) a))`,
  CHEAT_TAC);;

(* inst correct *)

(* [local] *)
let MULT_ADD_LESS_MULT = prove
 (`!m n k l j. m < l /\ n < k /\ j <= k ==> m * j + n < l * (k:num)`,
  CHEAT_TAC);;

(* [local] *)
let aligned_IMP_ADD_LESS_dimword = prove
 (`alignment_aligned k (x:'a word) /\ k <= dimindex (:'a) ==>
     w2n x + (2 EXP k - 1) < dimword (:'a)`,
  CHEAT_TAC);;

let aligned_2_imp = prove
 (`alignment_aligned 2 (x:'a word) /\ dimindex (:'a) = 32 ==>
    byte_align x = x /\
    byte_align (x + (n2w 1)) = x /\
    byte_align (x + (n2w 2)) = x /\
    byte_align (x + (n2w 3)) = x`,
  CHEAT_TAC);;

let aligned_2_not_eq = prove
 (`alignment_aligned 2 (x:'a word) /\ dimindex (:'a) = 32 /\ ~(x =
  byte_align a) ==> ~(x = a) /\ ~(x + (n2w 1) = a) /\ ~(x + (n2w 2) =
  a) /\ ~(x + (n2w 3) = a)`,
  CHEAT_TAC);;

let aligned_3_imp = prove
 (`alignment_aligned 3 (x:'a word) /\ dimindex (:'a) = 64 ==>
    byte_align x = x /\
    byte_align (x + (n2w 1)) = x /\
    byte_align (x + (n2w 2)) = x /\
    byte_align (x + (n2w 3)) = x /\
    byte_align (x + (n2w 4)) = x /\
    byte_align (x + (n2w 5)) = x /\
    byte_align (x + (n2w 6)) = x /\
    byte_align (x + (n2w 7)) = x`,
  CHEAT_TAC);;

let aligned_3_not_eq = prove
 (`alignment_aligned 3 (x:'a word) /\ dimindex (:'a) = 64 /\ ~(x =
  byte_align a) ==> ~(x = a) /\ ~(x + (n2w 1) = a) /\ ~(x + (n2w 2) =
  a) /\ ~(x + (n2w 3) = a) /\ ~(x + (n2w 4) = a) /\ ~(x + (n2w 5) = a)
  /\ ~(x + (n2w 6) = a) /\ ~(x + (n2w 7) = a)`,
  CHEAT_TAC);;

(* [local] *)
let dimword_eq_32_imp_or_bytes = prove
 (`dimindex (:'a) = 32 ==>
     (w2w ((w2w (x:'a word)):word8) ||
      w2w ((w2w (x >>> 8)):word8) << 8 ||
      w2w ((w2w (x >>> 16)):word8) << 16 ||
      w2w ((w2w (x >>> 24)):word8) << 24) = x`,
  CHEAT_TAC);;

(* [local] *)
let dimword_eq_64_imp_or_bytes = prove
 (`dimindex (:'a) = 64 ==>
     (w2w ((w2w (x:'a word)):word8) ||
      w2w ((w2w (x >>> 8)):word8) << 8 ||
      w2w ((w2w (x >>> 16)):word8) << 16 ||
      w2w ((w2w (x >>> 24)):word8) << 24 ||
      w2w ((w2w (x >>> 32)):word8) << 32 ||
      w2w ((w2w (x >>> 40)):word8) << 40 ||
      w2w ((w2w (x >>> 48)):word8) << 48 ||
      w2w ((w2w (x >>> 56)):word8) << 56) = x`,
  CHEAT_TAC);;

(* [local] *)
let byte_align_32_eq = prove
 (`dimindex (:'a) = 32 ==>
   byte_align (a:'a word) + n2w (w2n a MOD 4) = a`,
  CHEAT_TAC);;

(* [local] *)
let byte_align_64_eq = prove
 (`dimindex (:'a) = 64 ==>
   byte_align (a:'a word) + n2w (w2n a MOD 8) = a`,
  CHEAT_TAC);;

(* [local] *)
let byte_align_32_IMP = prove
 (`dimindex (:'a) = 32 ==>
   (byte_align a = a ==> w2n a MOD 4 = 0) /\
   (byte_align a + ((n2w 1):'a word) = a ==> w2n a MOD 4 = 1) /\
   (byte_align a + ((n2w 2):'a word) = a ==> w2n a MOD 4 = 2) /\
   (byte_align a + ((n2w 3):'a word) = a ==> w2n a MOD 4 = 3)`,
  CHEAT_TAC);;

(* [local] *)
let MOD4_CASES = prove
 (`!n. n MOD 4 = 0 \/ n MOD 4 = 1 \/ n MOD 4 = 2 \/ n MOD 4 = 3`,
  CHEAT_TAC);;

(* [local] *)
let byte_align_32_CASES = prove
 (`dimindex (:'a) = 32 ==>
   byte_align a + ((n2w 3):'a word) = a \/
   byte_align a + ((n2w 2):'a word) = a \/
   byte_align a + ((n2w 1):'a word) = a \/
   byte_align a = a`,
  CHEAT_TAC);;

(* [local] *)
let MOD8_CASES = prove
 (`!n. n MOD 8 = 0 \/ n MOD 8 = 1 \/ n MOD 8 = 2 \/ n MOD 8 = 3 \/
       n MOD 8 = 4 \/ n MOD 8 = 5 \/ n MOD 8 = 6 \/ n MOD 8 = 7`,
  CHEAT_TAC);;

(* [local] *)
let byte_align_64_CASES = prove
 (`dimindex (:'a) = 64 ==>
   byte_align a + ((n2w 7):'a word) = a \/
   byte_align a + ((n2w 6):'a word) = a \/
   byte_align a + ((n2w 5):'a word) = a \/
   byte_align a + ((n2w 4):'a word) = a \/
   byte_align a + ((n2w 3):'a word) = a \/
   byte_align a + ((n2w 2):'a word) = a \/
   byte_align a + ((n2w 1):'a word) = a \/
   byte_align a = a`,
  CHEAT_TAC);;

(* [local] *)
let byte_align_64_IMP = prove
 (`dimindex (:'a) = 64 ==>
   (byte_align a + ((n2w 7):'a word) = a ==> w2n a MOD 8 = 7) /\
   (byte_align a + ((n2w 6):'a word) = a ==> w2n a MOD 8 = 6) /\
   (byte_align a + ((n2w 5):'a word) = a ==> w2n a MOD 8 = 5) /\
   (byte_align a + ((n2w 4):'a word) = a ==> w2n a MOD 8 = 4) /\
   (byte_align a + ((n2w 3):'a word) = a ==> w2n a MOD 8 = 3) /\
   (byte_align a + ((n2w 2):'a word) = a ==> w2n a MOD 8 = 2) /\
   (byte_align a + ((n2w 1):'a word) = a ==> w2n a MOD 8 = 1) /\
   (byte_align a = a ==> w2n a MOD 8 = 0)`,
  CHEAT_TAC);;

(* HOL4 lab_to_targetProofScript.sml:2005-2055: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   arith_upd_lemma *)

(* The lab and asm versions should be in their individual props *)
(* [simp] *)
let arith_upd_fp_regs = prove
 (`(fp_regs (labSem_arith_upd a s) = fp_regs s /\ fp_regs
   (labSem_arith_upd a (t:'a asm_state)) = asm_state_fp_regs t)`,
  CHEAT_TAC);;

(* HOL4 lab_to_targetProofScript.sml:2068-2096: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   fp_upd_lemma *)

(* Inst_share_mem_pc_update_helper *)
let inst_share_mem_pc_update_helper = prove
 (`share_mem_state_rel mc_conf s1 t1 ms1 /\
   target_state_rel (machine_config_target mc_conf)
     (asm_state_pc_fupd (K pc') t1) ms2 ==>
   share_mem_state_rel mc_conf (labSem_state_clock_fupd (K
     (labSem_state_clock s1 - 1)) (labSem_state_pc_fupd (K
     (labSem_state_pc s1 + 1)) s1))
     (asm_state_pc_fupd (K pc') t1) ms2`,
  CHEAT_TAC);;

(* Inst_share_mem_reg_update_helper *)
let inst_share_mem_reg_update_helper = prove
 (`share_mem_state_rel mc_conf s1 t1 ms1 /\
   target_state_rel (machine_config_target mc_conf)
     (asm_state_pc_fupd (K pc') (asm_state_regs_fupd (K ((n =+ c)
       (asm_state_regs t1))) t1)) ms2 ==>
   share_mem_state_rel mc_conf (labSem_state_clock_fupd (K
     (labSem_state_clock s1 - 1)) (labSem_state_pc_fupd (K
     (labSem_state_pc s1 + 1)) (labSem_state_regs_fupd (K ((n =+
     wordLang_Word c) (labSem_state_regs s1))) s1)))
     (asm_state_pc_fupd (K pc') (asm_state_regs_fupd (K ((n =+ c)
       (asm_state_regs t1))) t1)) ms2`,
  CHEAT_TAC);;

(* HOL4 lab_to_targetProofScript.sml:2120-2128: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   arith_upd_share_mem_domain_unchange *)

(* HOL4 lab_to_targetProofScript.sml:2130-2136: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   fp_upd_share_mem_domain_unchange *)

(* HOL4 lab_to_targetProofScript.sml:2138-2144: a proof *)

let align2_not_align3_4w = prove
 (`~(alignment_aligned 3 x) /\ alignment_aligned 2 (x:'a word) /\
  dimindex (:'a) = 64 ==>
   x = byte_align x + (n2w 4) /\
   x + (n2w 1) = byte_align x + (n2w 5) /\
   x + (n2w 2) = byte_align x + (n2w 6) /\
   x + (n2w 3) = byte_align x + (n2w 7)`,
  CHEAT_TAC);;

(* HOL4 lab_to_targetProofScript.sml:2170-2930: a theorem whose
   statement HOL Light does not read (tools/unstated.py): Inst_lemma *)

(* compile correct *)

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let line_length_MOD_0 = prove
 (cake_as_vars (fun () ->
    `encoder_correct (machine_config_target mc_conf) /\
       (~(EVEN p) ==> (asm_config_code_alignment (target_config
         (machine_config_target mc_conf)) = 0)) /\
       line_ok (target_config (machine_config_target mc_conf)) labs
         ffi_names p h ==>
       (line_length h MOD 2 EXP asm_config_code_alignment
         (target_config (machine_config_target mc_conf)) = 0)`),
  CHEAT_TAC);;

(* [local] *)
let pos_val_MOD_0_lemma = prove
 (`(0 MOD 2 EXP asm_config_code_alignment (target_config
  (machine_config_target mc_conf)) = 0)`,
  CHEAT_TAC);;

(* HOL4 lab_to_targetProofScript.sml:2955-2979: a theorem that HOL4
   states as the value of an ML expression: pos_val_MOD_0 *)

(* HOL4 lab_to_targetProofScript.sml:2981: the ML values that the
   definitions below antiquote *)

let EVEN_add_AND = prove
 (`((n2w 1) && p) = (n2w 0) /\
   EVEN x ==>
   ((n2w 1) && (p + n2w x)) = (n2w 0)`,
  CHEAT_TAC);;

(* [local] *)
let word_cmp_lemma = prove
 (`lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     (wordSem_word_cmp cmp (labSem_state_regs s1 rr) (labSem_reg_imm
       ri s1) = SOME x) ==>
     (x = wordSem_word_cmp cmp (asm_state_regs t1 rr)
       (labSem_reg_imm ri t1))`,
  CHEAT_TAC);;

(* [local] *)
let list_add_if_fresh_simp = prove
 (`!n s. list_add_if_fresh s l =
     (if find_index s l n = NONE then
       APPEND l [s] else l)`,
  CHEAT_TAC);;

let list_add_if_fresh_thm = prove
 (`list_add_if_fresh s l =
    (if MEM s l then l else APPEND l [s])`,
  CHEAT_TAC);;

(* HOL4 lab_to_targetProofScript.sml:3052: ML code, not ported *)

(* [local] *)
let find_index_append = prove
 (`!n. find_index s (APPEND l l') n =
   (match find_index s l n with NONE -> find_index s l' (n + LENGTH
     l) | SOME i -> SOME i)`,
  CHEAT_TAC);;

(* [local] *)
let has_io_name_find_index = prove
 (`!l s.
   has_io_name s l ==> (?y. find_index (ffi_ExtCall s)
     (find_ffi_names l) 0 = SOME y)`,
  CHEAT_TAC);;

(* [local] *)
let find_index_in_range = prove
 (`!n. find_index s l n = SOME x ==> x < n + LENGTH l /\ x >= n`,
  CHEAT_TAC);;

(* [local] *)
let find_index_in_range0 = prove
 (`find_index s l 0 = SOME x ==> x < LENGTH l /\ x >= 0`,
  CHEAT_TAC);;

let EL_get_ffi_index_MEM = prove
 (`MEM s ls ==> EL (get_ffi_index ls s) ls = s`,
  CHEAT_TAC);;

let has_io_name_EXISTS = prove
 (`!name ls. has_io_name name ls <=>
    EX (\x. match x with labLang_LabAsm (labLang_CallFFI i) _14 _15
      _16 -> i = name | _17 -> F)
    (FLAT (MAP Section_lines ls))`,
  CHEAT_TAC);;

(* -- syntactic properties of remove_labels -- *)

(* annotated line length *)

let line_len_def = define_cases
  [`line_len (labLang_Label _20 _21 l) = l`;
   `line_len (labLang_Asm _22 _23 l) = l`;
   `line_len (labLang_LabAsm _24 _25 _26 l) = l`];;

(* annotated section length *)

let sec_length_add = prove
 (`!ls n m. sec_length ls (n + m) = sec_length ls n + m`,
  CHEAT_TAC);;

let sec_length_sum_line_len = prove
 (`!ls n.
    sec_length ls n = SUM (MAP line_len ls) + n`,
  CHEAT_TAC);;

(* simple syntactic properties of compiler functions *)

let _ = size_thms "line";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let enc_lines_again_simp_def,enc_lines_again_simp_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3,x4). list_size (line_size (\x. 0)) x4)`
  [`enc_lines_again_simp labs ffis pos enc [] = ([],T)`;
   `enc_lines_again_simp labs ffis pos enc (CONS (labLang_LabAsm a w
  bytes l) xs) =
        (let w1 = get_jump_offset a ffis labs pos in
          if w = w1 then
            let (rest,ok) = enc_lines_again_simp labs ffis (pos + l)
              enc xs in
              (CONS (labLang_LabAsm a w bytes l) rest,ok) else
            let bs = enc (lab_inst w1 a) in
            let l1 = MAX (LENGTH bs) l in
            let (rest,ok) = enc_lines_again_simp labs ffis (pos +
              l1) enc xs in
              (CONS (labLang_LabAsm a w1 bs l1) rest,(l1 = l /\
                ok)))`;
   `enc_lines_again_simp labs ffis pos enc (CONS (labLang_Label k1 k2 l)
  xs) =
        (let (rest,ok) = enc_lines_again_simp labs ffis (pos + l)
          enc xs in
        (CONS (labLang_Label k1 k2 l:'a line) rest,ok))`;
   `enc_lines_again_simp labs ffis pos enc (CONS (labLang_Asm x1 x2 l)
  xs) =
        (let (rest,ok) = enc_lines_again_simp labs ffis (pos + l)
          enc xs in
        (CONS (labLang_Asm x1 x2 l) rest,ok))`];;

(* HOL4 lab_to_targetProofScript.sml:3172: ML code, not ported *)

(* [local] *)
let enc_lines_again_simp_EQ = prove
 (`!labs ffis pos enc ls acc b.
   let (ls',flag) = enc_lines_again_simp labs ffis pos enc ls in
   enc_lines_again labs ffis pos enc ls (acc,b) = (APPEND (REVERSE
     acc) ls',sec_length ls' pos,(b /\ flag))`,
  CHEAT_TAC);;

let enc_lines_again_simp_len = prove
 (`!labs ffis pos enc lines res.
    enc_lines_again_simp labs ffis pos enc lines = (res,T) ==>
    MAP line_len res = MAP line_len lines`,
  CHEAT_TAC);;

let LENGTH_pad_bytes = prove
 (`0 < LENGTH nop /\ LENGTH bytes <= l ==>
    LENGTH (pad_bytes bytes l nop) = l`,
  CHEAT_TAC);;

let section_labels_sec_length = prove
 (`!pos lines acc.
    FST (section_labels pos lines acc) = sec_length lines pos`,
  CHEAT_TAC);;

let section_labels_append = prove
 (`!pos l1 labs l2.
    section_labels pos (APPEND l1 l2) labs =
    section_labels (pos + (SUM (MAP line_len l1))) l2 (SND
      (section_labels pos l1 labs))`,
  CHEAT_TAC);;

let line_length_add_nop1 = prove
 (`!nop ls.
   ~(ALL is_Label ls) ==>
   SUM (MAP line_length (add_nop nop ls)) =
   SUM (MAP line_length ls) + LENGTH nop`,
  CHEAT_TAC);;

let line_length_add_nop = prove
 (`!nop ls.
   ALL is_Label ls ==>
   SUM (MAP line_length (add_nop nop ls)) =
   SUM (MAP line_length ls)`,
  CHEAT_TAC);;

let line_len_add_nop1 = prove
 (`!nop ls. ~(ALL is_Label ls) ==>
    SUM (MAP line_len (add_nop nop ls)) =
    SUM (MAP line_len ls) + 1`,
  CHEAT_TAC);;

let line_len_add_nop = prove
 (`!nop ls. ALL is_Label ls ==>
    SUM (MAP line_len (add_nop nop ls)) =
    SUM (MAP line_len ls)`,
  CHEAT_TAC);;

let add_nop_append = prove
 (`!nop l1 l2.
    add_nop nop (APPEND l1 l2) = (if ALL is_Label l1 then APPEND l1
      (add_nop nop l2) else APPEND (add_nop nop l1) l2)`,
  CHEAT_TAC);;

(* [simp] *)
let EXISTS_not_Label_add_nop = prove
 (`!nop acc.
     EX ((~) o is_Label) (add_nop nop acc) <=> EX ((~) o is_Label)
       acc`,
  CHEAT_TAC);;

(* [simp] *)
let EVERY_is_Label_add_nop_preserved = prove
 (`!nop acc.
     ALL is_Label (add_nop nop acc) <=> ALL is_Label acc`,
  CHEAT_TAC);;

let EVERY_is_Label_add_nop = prove
 (`!nop ls. ALL is_Label ls ==> add_nop nop ls = ls`,
  CHEAT_TAC);;

let SND_lines_upd_lab_len = prove
 (`!pos lines acc.
     SND (lines_upd_lab_len pos lines acc) = (
     pos + SUM (MAP line_len (FST (lines_upd_lab_len pos lines
       acc)))) - SUM (MAP line_len acc)`,
  CHEAT_TAC);;

(* code_similar preservation *)

(* [local] *)
let line_similar_add_nop = prove
 (`!ls ls' h.
   ALL2 line_similar ls ls' ==>
   ALL2 line_similar ls (add_nop h ls')`,
  CHEAT_TAC);;

let line_similar_pad_section = prove
 (`!nop l2 aux l1.
     ALL2 line_similar l1 (APPEND (REVERSE aux) l2) ==>
     ALL2 line_similar l1 (pad_section nop l2 aux)`,
  CHEAT_TAC);;

let code_similar_pad_code = prove
 (`!code1 code2.
   code_similar code1 code2 ==>
   code_similar code1 (pad_code nop code2)`,
  CHEAT_TAC);;

(* [local] *)
let LIST_REL_enc_line = prove
 (`!ls ls'.
   ALL2 line_similar ls ls' <=>
   ALL2 line_similar (MAP (enc_line enc len) ls) ls'`,
  CHEAT_TAC);;

(* [simp] *)
let code_similar_enc_sec_list = prove
 (`!code1 code2 n.
     code_similar (enc_sec_list n code1) code2 <=>
     code_similar code1 code2`,
  CHEAT_TAC);;

(* [local] *)
let enc_lines_again_IMP_similar = prove
 (`!labs ffis pos enc lines acc ok lines' ok' curr.
   enc_lines_again labs ffis pos enc lines (acc,ok) = (lines',ok')
     ==>
   ALL2 line_similar curr (REVERSE acc) ==>
   ALL2 line_similar (APPEND curr lines) lines'`,
  CHEAT_TAC);;

let enc_secs_again_IMP_similar = prove
 (`!pos labs ffis enc code code1 ok.
   enc_secs_again pos labs ffis enc code = (code1,ok) ==>
     code_similar code code1`,
  CHEAT_TAC);;

(* HOL4 lab_to_targetProofScript.sml:3402-3408: a theorem that HOL4
   states as the value of an ML expression: lines_upd_lab_len_AUX *)

(* [local] *)
let line_similar_lines_upd_lab_len = prove
 (`!l aux pos l1.
       ALL2 line_similar (FST (lines_upd_lab_len pos l [])) l1 =
       ALL2 line_similar l l1`,
  CHEAT_TAC);;

let code_similar_upd_lab_len = prove
 (`!code pos code1.
      code_similar (upd_lab_len pos code) code1 = code_similar code
        code1`,
  CHEAT_TAC);;

let lines_upd_lab_len_similar = prove
 (`!pos lines aux.
    ALL2 line_similar (FST (lines_upd_lab_len pos lines aux))
      (APPEND (REVERSE aux) lines)`,
  CHEAT_TAC);;

(* implications of code_similar *)

let code_similar_MAP_Section_num = prove
 (`!c1 c2.
   code_similar c1 c2 ==>
   MAP Section_num c1 = MAP Section_num c2`,
  CHEAT_TAC);;

let code_similar_extract_labels = prove
 (`!code1 code2. code_similar code1 code2 ==>
   MAP (labProps_extract_labels o Section_lines) code1 =
   MAP (labProps_extract_labels o Section_lines) code2`,
  CHEAT_TAC);;

let code_similar_loc_to_pc = prove
 (`!l1 l2 c1 c2. code_similar c1 c2 ==>
     loc_to_pc l1 l2 c1 = loc_to_pc l1 l2 c2`,
  CHEAT_TAC);;

(* sec_label_ok preservation *)

let enc_sec_list_sec_labels_ok = prove
 (`!enc code.
   ALL sec_labels_ok code ==> ALL sec_labels_ok (enc_sec_list enc
     code)`,
  CHEAT_TAC);;

(* [local] *)
let enc_lines_again_sec_labels_ok = prove
 (`!labs ffis pos enc lines acc ok res ok' k.
     enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok') /\
     ALL (sec_label_ok k) acc /\
     ALL (sec_label_ok k) lines ==>
     ALL (sec_label_ok k) res`,
  CHEAT_TAC);;

let enc_secs_again_sec_labels_ok = prove
 (`!pos ffis labs enc ls res ok k.
    enc_secs_again pos ffis labs enc ls = (res,ok) /\ ALL
      sec_labels_ok ls ==>
    ALL sec_labels_ok res`,
  CHEAT_TAC);;

(* [local] *)
let lines_upd_lab_len_sec_label_ok = prove
 (`!pos lines acc k.
      ALL (sec_label_ok k) lines /\
      ALL (sec_label_ok k) acc ==>
      ALL (sec_label_ok k) (FST (lines_upd_lab_len pos lines acc))`,
  CHEAT_TAC);;

let upd_lab_len_sec_labels_ok = prove
 (`!n ls. ALL sec_labels_ok ls ==> ALL sec_labels_ok (upd_lab_len n
  ls)`,
  CHEAT_TAC);;

(* [local] *)
let add_nop_sec_label_ok = prove
 (`!nop aux.
     ALL (sec_label_ok k) aux ==>
     ALL (sec_label_ok k) (add_nop nop aux)`,
  CHEAT_TAC);;

(* [local] *)
let pad_section_sec_label_ok = prove
 (`!nop xs acc k.
     ALL (sec_label_ok k) xs /\
     ALL (sec_label_ok k) acc ==>
     ALL (sec_label_ok k) (pad_section nop xs acc)`,
  CHEAT_TAC);;

let pad_code_sec_labels_ok = prove
 (`!nop code.
    ALL sec_labels_ok code ==>
    ALL sec_labels_ok (pad_code nop code)`,
  CHEAT_TAC);;

(* [simp] *)
let sec_labels_ok_filter_skip = prove
 (`!code. ALL sec_labels_ok (filter_skip code) <=> ALL sec_labels_ok
  code`,
  CHEAT_TAC);;

(* invariant: lines are encoded and non-label lengths annotated *)

let line_encd0_def = new_definition
  `line_encd0 enc x2 =
        match x2 with
          labLang_Asm b bytes len ->
       enc (cbw_to_asm b) = bytes /\ len = LENGTH bytes
        | (labLang_LabAsm l w bytes len) ->
        enc (lab_inst w l) = bytes /\ LENGTH bytes <= len /\
        (?w'. len = LENGTH (enc (lab_inst w' l)))
        | _27 -> T`;;

let sec_encd0_def = define_general
  [`sec_encd0 enc (Section _28 ls) = ALL (line_encd0 enc) ls`];;

(* HOL4 lab_to_targetProofScript.sml:3628: the overload all_encd0,
   which the port expands *)

(* establishing encd0 *)

let enc_sec_list_encd0 = prove
 (`!ls. (\enc l. ALL (sec_encd0 enc) l) enc (enc_sec_list enc ls)`,
  CHEAT_TAC);;

(* encd0 preservation *)

let enc_lines_again_encd0 = prove
 (`!labs ffis pos enc lines acc ok res ok'.
    enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok') /\
    ALL (line_encd0 enc) lines /\
    ALL (line_encd0 enc) acc ==>
    ALL (line_encd0 enc) res`,
  CHEAT_TAC);;

let enc_secs_again_encd0 = prove
 (`!pos labs ffis enc ls res ok.
    enc_secs_again pos labs ffis enc ls = (res,ok) /\
    (\enc l. ALL (sec_encd0 enc) l) enc ls ==>
    (\enc l. ALL (sec_encd0 enc) l) enc res`,
  CHEAT_TAC);;

let lines_upd_lab_len_encd0 = prove
 (`!pos ls acc.
    ALL (line_encd0 enc) ls /\
    ALL (line_encd0 enc) acc ==>
    ALL (line_encd0 enc) (FST (lines_upd_lab_len pos ls acc))`,
  CHEAT_TAC);;

let upd_lab_len_encd0 = prove
 (`!pos ss. (\enc l. ALL (sec_encd0 enc) l) enc ss ==> (\enc l. ALL
  (sec_encd0 enc) l) enc (upd_lab_len pos ss)`,
  CHEAT_TAC);;

(* invariant: annotated lengths are not too small *)
(* this is a consequence of encd (below) and not treated separately much *)

let line_length_leq_def = new_definition
  `line_length_leq x1 =
        match x1 with
          labLang_LabAsm _29 _30 bytes l ->
       LENGTH bytes <= l
        | (labLang_Asm _31 bytes l) ->
       LENGTH bytes <= l
        | _32 -> T`;;

let sec_length_leq_def = define_general
  [`sec_length_leq (Section _33 ls) = ALL line_length_leq ls`];;

(* HOL4 lab_to_targetProofScript.sml:3713: the overload
   all_length_leq, which the port expands *)

(* invariant: label annotated lengths are 0 or 1 *)

let label_one_def = new_definition
  `label_one x1 =
        match x1 with
          labLang_Label _36 _37 n -> n <= 1
        | _38 -> T`;;

let sec_label_one_def = define_general
  [`sec_label_one (Section _39 ls) = ALL label_one ls`];;

(* establishing label_one *)

let lines_upd_lab_len_label_one = prove
 (`!pos ls acc.
    ALL label_one acc ==>
    ALL label_one (FST (lines_upd_lab_len pos ls acc))`,
  CHEAT_TAC);;

let upd_lab_len_label_one = prove
 (`!pos ss. ALL sec_label_one (upd_lab_len pos ss)`,
  CHEAT_TAC);;

(* label_one preservation *)

let enc_lines_again_simp_label_one = prove
 (`!labs ffis pos enc ls res ok.
    enc_lines_again_simp labs ffis pos enc ls = (res,ok) /\
    ALL label_one ls ==>
    ALL label_one res`,
  CHEAT_TAC);;

let enc_secs_again_label_one = prove
 (`!pos labs ffis enc lines res ok.
    enc_secs_again pos labs ffis enc lines = (res,ok) /\
    ALL sec_label_one lines ==>
    ALL sec_label_one res`,
  CHEAT_TAC);;

(* simple consequences of label_one *)

let line_length_pad_section1 = prove
 (`!nop ls acc.
   LENGTH nop = 1 /\
   ALL label_one ls /\
   ALL line_length_leq ls /\
   ~(ALL is_Label acc) /\
   SUM (MAP line_length acc) = SUM (MAP line_len acc) ==>
   SUM (MAP line_length (pad_section nop ls acc)) =
   SUM (MAP line_len ls) + SUM (MAP line_len acc)`,
  CHEAT_TAC);;

let line_len_pad_section1 = prove
 (`!nop xs aux.
   LENGTH nop = 1 /\
   ALL label_one xs /\
   ~(ALL is_Label aux) ==>
   SUM (MAP line_len (pad_section nop xs aux)) =
   SUM (MAP line_len xs) + SUM (MAP line_len aux)`,
  CHEAT_TAC);;

(* invariant: lines are encoded and annotated lengths are correct *)

let line_encd_def = new_definition
  `line_encd enc labs ffis pos x5 =
        match x5 with
          labLang_Asm b bytes len ->
       enc (cbw_to_asm b) = bytes /\ len = LENGTH bytes
        | (labLang_LabAsm labLang_Halt _40 bytes len) ->
       enc (labLang_Jump (--(n2w (pos + ffi_offset)))) = bytes /\
       LENGTH bytes <= len
        | (labLang_LabAsm labLang_Install _41 bytes len) ->
       enc (labLang_Jump (--(n2w (pos + 2 * ffi_offset)))) = bytes /\
       LENGTH bytes <= len
        | (labLang_LabAsm (labLang_CallFFI s) _42 bytes len) ->
       enc (labLang_Jump (--(n2w (pos + (get_ffi_index ffis
         (ffi_ExtCall s) + 3) * ffi_offset)))) = bytes /\
       LENGTH bytes <= len
        | (labLang_LabAsm (labLang_Jump l) _43 bytes len) ->
       enc (labLang_Jump (n2w (find_pos l labs) + --(n2w pos))) =
         bytes /\
       LENGTH bytes <= len
        | (labLang_LabAsm (labLang_JumpCmp a b c l) _44 bytes len) ->
       enc (labLang_JumpCmp a b c (n2w (find_pos l labs) + --(n2w
         pos))) = bytes /\
       LENGTH bytes <= len
        | (labLang_LabAsm (labLang_LocValue k l) _45 bytes len) ->
       enc (asm_Loc k (n2w (find_pos l labs) + --(n2w pos))) = bytes
         /\
       LENGTH bytes <= len
        | (labLang_LabAsm (labLang_Call l) _46 bytes len) ->
       enc (labLang_Call (n2w (find_pos l labs) + --(n2w pos))) =
         bytes /\
       LENGTH bytes <= len
        | _47 -> T`;;

(* HOL4 lab_to_targetProofScript.sml:3836: ML code, not ported *)

let lines_encd_def,lines_encd_ind = define_rec
  [`lines_encd enc labs ffis pos [] <=> T`;
   `lines_encd enc labs ffis pos (CONS l ls) <=>
       line_encd enc labs ffis pos l /\
       lines_encd enc labs ffis (pos + line_len l) ls`];;

let _ = size_thms "sec";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let all_encd_def,all_encd_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3,x4). list_size (sec_size (\x. 0)) x4)`
  [`all_encd enc labs ffis pos [] <=> T`;
   `all_encd enc labs ffis pos (CONS (Section k ls) ss) <=>
       lines_encd enc labs ffis pos ls /\
       all_encd enc labs ffis (pos + SUM (MAP line_len ls)) ss`];;

(* length_leq follows from encd *)

let line_encd_length_leq = prove
 (`!enc labs ffis pos l. line_encd enc labs ffis pos l ==>
  line_length_leq l`,
  CHEAT_TAC);;

let lines_encd_length_leq = prove
 (`!enc labs ffis pos ls. lines_encd enc labs ffis pos ls ==> ALL
  line_length_leq ls`,
  CHEAT_TAC);;

let all_encd_length_leq = prove
 (`!enc labs ffis pos ls. all_encd enc labs ffis pos ls ==> (\l. ALL
  sec_length_leq l) ls`,
  CHEAT_TAC);;

(* establishing encd *)

let enc_lines_again_simp_encd = prove
 (`!labs ffis pos enc lines res.
    enc_lines_again_simp labs ffis pos enc lines = (res,T) /\
    ALL label_one lines /\
    ALL (line_encd0 enc) lines ==>
    lines_encd enc labs ffis pos res`,
  CHEAT_TAC);;

let enc_secs_again_encd = prove
 (`!pos labs ffis enc ls res.
    enc_secs_again pos labs ffis enc ls = (res,T) /\
    ALL sec_label_one ls /\
    ALL (sec_encd0 enc) ls ==>
    all_encd enc labs ffis pos res`,
  CHEAT_TAC);;

(* invariant: annotated lengths are correct *)

let line_length_ok_def = new_definition
  `line_length_ok l <=> LENGTH (line_bytes l) = line_len l`;;

let sec_length_ok_def = define_general
  [`sec_length_ok (Section _48 ls) = ALL line_length_ok ls`];;

(* simple consequences of length_ok *)

let sec_length_sum_line_length = prove
 (`!ls n.
    ALL line_length_ok ls ==>
    (sec_length ls n = SUM (MAP line_length ls) + n)`,
  CHEAT_TAC);;

(* invariant: all labels annotated with length 0 *)

let label_zero_def = new_definition
  `label_zero x1 =
        match x1 with
          labLang_Label _51 _52 n -> n = 0
        | _53 -> T`;;

let sec_label_zero_def = define_general
  [`sec_label_zero (Section _54 ls) = ALL label_zero ls`];;

(* label_zero preservation *)

(* [local] *)
let EVERY_label_zero_add_nop = prove
 (`!xs. ALL label_zero (add_nop nop xs) = ALL label_zero xs`,
  CHEAT_TAC);;

(* [simp] *)
let EVERY_label_zero_pad_section = prove
 (`!nop xs aux.
     ALL label_zero aux ==>
     ALL label_zero (pad_section nop xs aux)`,
  CHEAT_TAC);;

(* [simp] *)
let EVERY_sec_label_zero_pad_code = prove
 (`!nop ls. ALL sec_label_zero (pad_code nop ls)`,
  CHEAT_TAC);;

let enc_lines_again_simp_label_zero = prove
 (`!labs ffis pos enc ls res ok.
    enc_lines_again_simp labs ffis pos enc ls = (res,ok) /\
    ALL label_zero ls ==>
    ALL label_zero res`,
  CHEAT_TAC);;

let enc_secs_again_label_zero = prove
 (`!pos labs ffis enc lines res ok.
    enc_secs_again pos labs ffis enc lines = (res,ok) /\
    ALL sec_label_zero lines ==>
    ALL sec_label_zero res`,
  CHEAT_TAC);;

let lines_upd_lab_len_encd0_label_zero = prove
 (`!pos lines aux.
    enc_ok c /\ enc = asm_config_encode c /\
      ~(asm_config_code_alignment c = 0) /\
    ALL (line_encd0 enc) lines /\ EVEN pos /\
    ALL label_zero aux ==>
    ALL label_zero (FST (lines_upd_lab_len pos lines aux))`,
  CHEAT_TAC);;

let EVEN_sec_length_lines_upd_lab_len = prove
 (`!pos lines acc.
    (if NULL lines then
     EVEN pos /\ EVEN (SUM (MAP line_len acc)) else is_Label (LAST
       lines) /\
         EVEN (pos + (SUM (MAP line_len acc)))) ==>
    EVEN (SUM (MAP line_len (FST (lines_upd_lab_len pos lines
      acc))))`,
  CHEAT_TAC);;

let upd_lab_len_encd0_label_zero = prove
 (`!pos code.
    enc_ok c /\ enc = asm_config_encode c /\
      ~(asm_config_code_alignment c = 0) /\
    (\enc l. ALL (sec_encd0 enc) l) enc code /\ EVEN pos /\ ALL
      sec_ends_with_label code ==>
    ALL sec_label_zero (upd_lab_len pos code)`,
  CHEAT_TAC);;

(* simple consequences of label_zero *)

let sec_pos_val_0 = prove
 (`!pos lines. ~(ALL is_Label lines) /\ ALL label_zero lines ==>
  sec_pos_val 0 pos lines = SOME pos`,
  CHEAT_TAC);;

let line_len_pad_section0 = prove
 (`!nop ls aux.
   ALL label_zero ls ==>
   SUM (MAP line_len (pad_section nop ls aux)) =
   SUM (MAP line_len ls) + SUM (MAP line_len aux)`,
  CHEAT_TAC);;

let sec_label_zero_pos_val_0 = prove
 (`!xs pos.
   ALL sec_label_zero xs ==>
   pos_val 0 pos xs = pos`,
  CHEAT_TAC);;

let all_enc_ok_imp_sec_label_zero = prove
 (`!conf labs ffis n code.
   all_enc_ok conf labs ffis n code ==>
   ALL sec_label_zero code`,
  CHEAT_TAC);;

(* invariant: lines aligned *)

let line_aligned_def = new_definition
  `line_aligned m l <=>
     line_len l MOD m = 0 /\
     line_length l MOD m = 0`;;

let sec_aligned_def = define_general
  [`sec_aligned noplen (Section _55 ls) = ALL (line_aligned noplen)
  ls`];;

(* establishing aligned *)

let all_encd0_aligned = prove
 (`!c enc code.
   enc_ok c /\ enc = asm_config_encode c /\
   (\enc l. ALL (sec_encd0 enc) l) enc code /\
   ALL sec_label_zero code ==>
   ALL (sec_aligned (LENGTH (enc (asm_Inst asm_Skip)))) code`,
  CHEAT_TAC);;

(* aligned preservation *)

let enc_lines_again_simp_aligned = prove
 (`!labs ffis pos enc ls res ok.
    (!a. LENGTH (enc a) MOD len = 0) /\
    enc_lines_again_simp labs ffis pos enc ls = (res,ok) /\
    ALL (line_aligned len) ls ==>
    ALL (line_aligned len) res`,
  CHEAT_TAC);;

let enc_secs_again_aligned = prove
 (`!pos labs ffis enc lines res ok.
    (!a. LENGTH (enc a) MOD len = 0) /\
    enc_secs_again pos labs ffis enc lines = (res,ok) /\
    ALL (sec_aligned len) lines ==>
    ALL (sec_aligned len) res`,
  CHEAT_TAC);;

(* invariant: all initial labels have annotated length 0 *)

let label_prefix_zero_def = new_definition
  `label_prefix_zero ls <=>
      (!n. n < LENGTH ls /\ (!m. m <= n ==> is_Label (EL m ls)) ==>
         (!m. m <= n ==> line_len (EL m ls) = 0))`;;

let sec_label_prefix_zero_def = define_general
  [`sec_label_prefix_zero (Section k ls) <=> label_prefix_zero ls`];;

let label_prefix_zero_cons = prove
 (`(label_prefix_zero (CONS (labLang_Label l1 l2 len) ls) <=> ((len = 0)
  /\ label_prefix_zero ls)) /\
   (label_prefix_zero (CONS (labLang_Asm a b c) ls) <=> T) /\
   (label_prefix_zero (CONS (labLang_LabAsm d e f g) ls) <=> T)`,
  CHEAT_TAC);;

(* establishing label_prefix_zero *)

let label_prefix_zero_append_suff = prove
 (`!l1 l2.
   label_prefix_zero l1 /\ label_prefix_zero l2 ==>
   label_prefix_zero (APPEND l1 l2)`,
  CHEAT_TAC);;

let label_prefix_zero_append_suff2 = prove
 (`!l1 l2.
   label_prefix_zero l1 /\ EX ((~) o is_Label) l1 ==>
   label_prefix_zero (APPEND l1 l2)`,
  CHEAT_TAC);;

let lines_upd_lab_len_label_prefix_zero = prove
 (`!pos ls acc.
    (ALL is_Label acc ==> EVEN pos) /\ label_prefix_zero (REVERSE
      acc) ==>
    label_prefix_zero (FST (lines_upd_lab_len pos ls acc))`,
  CHEAT_TAC);;

let upd_lab_len_label_prefix_zero = prove
 (`!pos ss.
    EVEN pos /\ ALL sec_ends_with_label ss ==>
    ALL sec_label_prefix_zero (upd_lab_len pos ss)`,
  CHEAT_TAC);;

(* label_prefix_zero preservation *)

let enc_lines_again_simp_label_prefix_zero = prove
 (`!labs ffis pos enc ls res ok.
    enc_lines_again_simp labs ffis pos enc ls = (res,ok) /\
    label_prefix_zero ls ==>
    label_prefix_zero res`,
  CHEAT_TAC);;

let enc_secs_again_label_prefix_zero = prove
 (`!pos labs ffis enc lines res ok.
    enc_secs_again pos labs ffis enc lines = (res,ok) /\
    ALL sec_label_prefix_zero lines ==>
    ALL sec_label_prefix_zero res`,
  CHEAT_TAC);;

(* simple consequences of label_prefix_zero *)

let line_length_pad_section = prove
 (`!nop ls acc.
   LENGTH nop = 1 /\
   ALL label_one ls /\
   ALL line_length_leq ls /\
   SUM (MAP line_length acc) = SUM (MAP line_len acc) /\
   ALL is_Label acc /\ label_prefix_zero ls ==>
   SUM (MAP line_length (pad_section nop ls acc)) =
   SUM (MAP line_len ls) + SUM (MAP line_len acc)`,
  CHEAT_TAC);;

let label_zero_line_length_pad_section = prove
 (`!nop ls acc.
   0 < LENGTH nop /\
   ALL label_zero ls /\
   MAP line_length acc = MAP line_len acc /\
   ALL line_length_leq ls ==>
   MAP line_length (pad_section nop ls acc) =
   MAP line_len (APPEND (REVERSE acc) ls)`,
  CHEAT_TAC);;

(* invariant: lines encd with nops *)

let line_enc_with_nop_def = new_definition
  `line_enc_with_nop enc labs ffis pos x5 =
        match x5 with
          labLang_Asm b bytes len ->
       enc_with_nop enc (cbw_to_asm b) bytes /\ LENGTH bytes = len
        | (labLang_LabAsm labLang_Halt _56 bytes len) ->
       enc_with_nop enc (labLang_Jump (--(n2w (pos + ffi_offset))))
         bytes /\
       LENGTH bytes = len
        | (labLang_LabAsm labLang_Install _57 bytes len) ->
       enc_with_nop enc (labLang_Jump (--(n2w (pos + 2 *
         ffi_offset)))) bytes /\
       LENGTH bytes = len
        | (labLang_LabAsm (labLang_CallFFI s) _58 bytes len) ->
       enc_with_nop enc (labLang_Jump (--(n2w (pos + (get_ffi_index
         ffis (ffi_ExtCall s) + 3) * ffi_offset)))) bytes /\
       LENGTH bytes = len
        | (labLang_LabAsm (labLang_Jump l) _59 bytes len) ->
       enc_with_nop enc (labLang_Jump (n2w (find_pos l labs) + --(n2w
         pos))) bytes /\
       LENGTH bytes = len
        | (labLang_LabAsm (labLang_JumpCmp a b c l) _60 bytes len) ->
       enc_with_nop enc (labLang_JumpCmp a b c (n2w (find_pos l labs)
         + --(n2w pos))) bytes /\
       LENGTH bytes = len
        | (labLang_LabAsm (labLang_LocValue k l) _61 bytes len) ->
       enc_with_nop enc (asm_Loc k (n2w (find_pos l labs) + --(n2w
         pos))) bytes /\
       LENGTH bytes = len
        | (labLang_LabAsm _62 _63 bytes len) -> LENGTH bytes = len
        | (labLang_Label _64 _65 len) -> len = 0`;;

(* HOL4 lab_to_targetProofScript.sml:4357: ML code, not ported *)

let lines_enc_with_nop_def,lines_enc_with_nop_ind = define_rec
  [`lines_enc_with_nop enc labs ffis pos [] <=> T`;
   `lines_enc_with_nop enc labs ffis pos (CONS l ls) <=>
       line_enc_with_nop enc labs ffis pos l /\
       lines_enc_with_nop enc labs ffis (pos + line_length l)
         ls`];;

let lines_enc_with_nop_append = prove
 (`!enc labs ffis pos l1 l2.
   lines_enc_with_nop enc labs ffis pos (APPEND l1 l2) <=>
   lines_enc_with_nop enc labs ffis pos l1 /\
   lines_enc_with_nop enc labs ffis (pos + SUM (MAP line_length
     l1)) l2`,
  CHEAT_TAC);;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let all_enc_with_nop_def,all_enc_with_nop_ind = define_guess_cheat
  [`all_enc_with_nop enc labs ffis pos [] <=> T`;
   `all_enc_with_nop enc labs ffis pos (CONS (Section k []) xs) <=>
       all_enc_with_nop enc labs ffis pos xs`;
   `all_enc_with_nop enc labs ffis pos (CONS (Section k (CONS y ys)) xs)
  <=>
       line_enc_with_nop enc labs ffis pos y /\
       all_enc_with_nop enc labs ffis (pos + line_length y)
         (CONS (Section k ys) xs)`];;

(* HOL4 lab_to_targetProofScript.sml:4384: ML code, not ported *)

let all_enc_with_nop_alt = prove
 (`(all_enc_with_nop enc labs ffis pos [] <=> T) /\
   (all_enc_with_nop enc labs ffis pos (CONS (Section k ls) ss) <=>
    lines_enc_with_nop enc labs ffis pos ls /\
    all_enc_with_nop enc labs ffis (pos + SUM (MAP line_length ls))
      ss)`,
  CHEAT_TAC);;

(* enc_with_nop implies length_ok *)

let line_enc_with_nop_length_ok = prove
 (`!enc labs ffis pos line.
    line_enc_with_nop enc labs ffis pos line ==> line_length_ok
      line`,
  CHEAT_TAC);;

let lines_enc_with_nop_length_ok = prove
 (`!enc labs ffis pos ls. lines_enc_with_nop enc labs ffis pos ls ==>
  ALL line_length_ok ls`,
  CHEAT_TAC);;

(* enc_with_nop implies label_zero *)

let line_enc_with_nop_label_zero = prove
 (`!enc labs ffis pos line.
    line_enc_with_nop enc labs ffis pos line ==> label_zero line`,
  CHEAT_TAC);;

let lines_enc_with_nop_label_zero = prove
 (`!enc labs ffis pos lines.
     lines_enc_with_nop enc labs ffis pos lines ==> ALL label_zero
       lines`,
  CHEAT_TAC);;

let all_enc_with_nop_label_zero = prove
 (`!enc labs ffis pos ls.
    all_enc_with_nop enc labs ffis pos ls ==>
    ALL sec_label_zero ls`,
  CHEAT_TAC);;

(* line_ok implies enc_with_nop *)

let line_ok_line_enc_with_nop = prove
 (`!c labs ffis pos line.
    line_ok c labs ffis pos line ==>
    line_enc_with_nop (asm_config_encode c) labs ffis pos line`,
  CHEAT_TAC);;

let lines_ok_lines_enc_with_nop = prove
 (`!c labs ffis pos lines.
    lines_ok c labs ffis pos lines ==>
    lines_enc_with_nop (asm_config_encode c) labs ffis pos lines`,
  CHEAT_TAC);;

(* establishing enc_with_nop *)

let enc_with_nop_pad_bytes_length = prove
 (`enc_with_nop enc x (pad_bytes (enc x) (LENGTH (enc x)) (enc
  (asm_Inst asm_Skip)))`,
  CHEAT_TAC);;

let enc_with_nop_pad_bytes = prove
 (`nop = enc (asm_Inst asm_Skip) /\ LENGTH (enc x) <= len /\
   LENGTH (enc x) MOD (LENGTH nop) = 0 /\
   len MOD (LENGTH nop) = 0 /\
   0 < LENGTH nop ==> enc_with_nop enc x (pad_bytes (enc x) len
     nop)`,
  CHEAT_TAC);;

let lines_enc_with_nop_add_nop = prove
 (`!enc labs ffis pos ls.
    LENGTH (enc (asm_Inst asm_Skip)) = 1 /\
    lines_enc_with_nop enc labs ffis pos (REVERSE ls) ==>
    lines_enc_with_nop enc labs ffis pos
      (REVERSE (add_nop (enc (asm_Inst asm_Skip)) ls))`,
  CHEAT_TAC);;

let lines_enc_with_nop_pad_section1 = prove
 (`!nop code aux pos.
    nop = enc (asm_Inst asm_Skip) /\ LENGTH nop = 1 /\
    lines_encd enc labs ffis (pos + (SUM (MAP line_len aux))) code /\
    lines_enc_with_nop enc labs ffis pos (REVERSE aux) /\
    ~(ALL is_Label aux) /\
    ALL label_one code ==>
    lines_enc_with_nop enc labs ffis pos (pad_section nop code aux)`,
  CHEAT_TAC);;

let lines_enc_with_nop_pad_section01 = prove
 (`!nop code aux pos.
    nop = enc (asm_Inst asm_Skip) /\ 0 < LENGTH nop /\
    ALL (line_aligned (LENGTH nop)) code /\
    lines_encd enc labs ffis (pos + SUM (MAP line_len aux)) code /\
    lines_enc_with_nop enc labs ffis pos (REVERSE aux) /\
    ~(ALL is_Label aux) /\ ALL label_zero code ==>
    lines_enc_with_nop enc labs ffis pos (pad_section nop code aux)`,
  CHEAT_TAC);;

let lines_enc_with_nop_pad_section0 = prove
 (`!nop code aux pos.
    nop = enc (asm_Inst asm_Skip) /\ 0 < LENGTH nop /\
    ALL (line_aligned (LENGTH nop)) code /\
    lines_encd enc labs ffis (pos + SUM (MAP line_len aux)) code /\
    lines_enc_with_nop enc labs ffis pos (REVERSE aux) /\
    ALL is_Label aux /\ ALL label_zero code ==>
    lines_enc_with_nop enc labs ffis pos (pad_section nop code aux)`,
  CHEAT_TAC);;

let lines_enc_with_nop_pad_section = prove
 (`!nop code aux pos.
    nop = enc (asm_Inst asm_Skip) /\ LENGTH nop = 1 /\
    lines_encd enc labs ffis (pos + SUM (MAP line_len aux)) code /\
    lines_enc_with_nop enc labs ffis pos (REVERSE aux) /\
    ALL is_Label aux /\ ALL label_one code /\ label_prefix_zero code
      ==>
    lines_enc_with_nop enc labs ffis pos (pad_section nop code aux)`,
  CHEAT_TAC);;

let all_enc_with_nop_pad_code = prove
 (`!nop code pos.
   0 < LENGTH nop /\ nop = enc (asm_Inst asm_Skip) /\
   (~(LENGTH nop = 1) ==> ALL (sec_aligned (LENGTH nop)) code /\ ALL
     sec_label_zero code) /\
   ALL sec_label_one code /\
   ALL sec_length_leq code /\
   ALL sec_label_prefix_zero code /\
   all_encd enc labs ffis pos code ==>
   all_enc_with_nop enc labs ffis pos (pad_code nop code)`,
  CHEAT_TAC);;

(* invariant: label annotation correctly records alignment *)

let line_lab_len_pos_ok_def = new_definition
  `line_lab_len_pos_ok pos x2 =
        match x2 with
          labLang_Label _68 _69 l ->
        (if EVEN pos then l = 0 else l = 1)
        | _70 -> T`;;

let lab_len_pos_ok_def,lab_len_pos_ok_ind = define_rec
  [`lab_len_pos_ok pos [] <=> T`;
   `lab_len_pos_ok pos (CONS l ls) <=>
         line_lab_len_pos_ok pos l /\
         lab_len_pos_ok (pos + line_len l) ls`];;

let lab_len_pos_ok_append = prove
 (`!l1 pos l2.
   lab_len_pos_ok pos (APPEND l1 l2) <=>
   lab_len_pos_ok pos l1 /\
   lab_len_pos_ok (pos + SUM (MAP line_len l1)) l2`,
  CHEAT_TAC);;

let _ = size_thms "sec";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let all_lab_len_pos_ok_def,all_lab_len_pos_ok_ind = define_wf
  `MEASURE (\(x0,x1). list_size (sec_size (\x. 0)) x1)`
  [`all_lab_len_pos_ok _71 [] <=> T`;
   `all_lab_len_pos_ok pos (CONS (Section k ls) ss) <=>
       lab_len_pos_ok pos ls /\
       all_lab_len_pos_ok (pos + sec_length ls 0) ss`];;

(* HOL4 lab_to_targetProofScript.sml:4714: ML code, not ported *)

(* establishing pos_ok *)

let lines_upd_lab_len_pos_ok = prove
 (`!pos lines.
    lab_len_pos_ok pos (FST (lines_upd_lab_len pos lines []))`,
  CHEAT_TAC);;

let upd_lab_len_pos_ok = prove
 (`!pos code.
    all_lab_len_pos_ok pos (upd_lab_len pos code)`,
  CHEAT_TAC);;

(* pos_ok preservation *)

let enc_lines_again_simp_pos_ok = prove
 (`!labs ffis pos enc lines res.
    enc_lines_again_simp labs ffis pos enc lines = (res,T) /\
    lab_len_pos_ok pos lines ==>
    lab_len_pos_ok pos res`,
  CHEAT_TAC);;

let enc_secs_again_pos_ok = prove
 (`!pos labs ffis enc code res.
    enc_secs_again pos labs ffis enc code = (res,T) /\
    all_lab_len_pos_ok pos code ==>
    all_lab_len_pos_ok pos res`,
  CHEAT_TAC);;

let lab_len_pos_ok_even_prefix_zero = prove
 (`!pos ls.
    EVEN pos /\
    lab_len_pos_ok pos ls ==>
    label_prefix_zero ls`,
  CHEAT_TAC);;

let pad_section_pos_ok = prove
 (`!nop lines aux pos.
    lab_len_pos_ok (pos + SUM (MAP line_len aux)) lines /\
    lab_len_pos_ok pos (REVERSE aux) /\
    ALL label_zero aux /\
    ((NULL aux \/ is_Label (HD aux)) ==> label_prefix_zero lines) ==>
    lab_len_pos_ok pos (pad_section nop lines aux)`,
  CHEAT_TAC);;

let line_len_pad_section = prove
 (`!nop xs aux.
    LENGTH nop = 1 /\
    ALL label_one xs /\
    (ALL is_Label aux ==> label_prefix_zero xs) ==>
    SUM (MAP line_len (pad_section nop xs aux)) =
    SUM (MAP line_len xs) + SUM (MAP line_len aux)`,
  CHEAT_TAC);;

let all_lab_len_pos_ok_pad_code = prove
 (`!nop code pos.
    all_lab_len_pos_ok pos code /\
    (~(LENGTH nop = 1) ==> ALL sec_label_zero code) /\
    ALL sec_label_one code /\
    ALL sec_label_prefix_zero code ==>
    all_lab_len_pos_ok pos (pad_code nop code)`,
  CHEAT_TAC);;

(* invariant: jump offsets ok *)

let line_offset_ok_def = new_definition
  `line_offset_ok labs ffis pos x4 =
        match x4 with
          labLang_LabAsm a w bytes _72 ->
       w = get_jump_offset a ffis labs pos
        | _73 -> T`;;

let lines_offset_ok_def,lines_offset_ok_ind = define_rec
  [`lines_offset_ok labs ffis pos [] <=> T`;
   `lines_offset_ok labs ffis pos (CONS l ls) <=>
       line_offset_ok labs ffis pos l /\
       lines_offset_ok labs ffis (pos + line_len l) ls`];;

let lines_offset_ok_append = prove
 (`!labs ffis pos l1 l2.
    lines_offset_ok labs ffis pos (APPEND l1 l2) <=>
    lines_offset_ok labs ffis pos l1 /\
    lines_offset_ok labs ffis (pos + SUM (MAP line_len l1)) l2`,
  CHEAT_TAC);;

let _ = size_thms "sec";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let lab_to_targetProof_offset_ok_def,lab_to_targetProof_offset_ok_ind =
  define_wf
  `MEASURE (\(x0,x1,x2,x3). list_size (sec_size (\x. 0)) x3)`
  [`lab_to_targetProof_offset_ok labs ffis pos [] <=> T`;
   `lab_to_targetProof_offset_ok labs ffis pos (CONS (Section k ls) ss)
  <=>
       lines_offset_ok labs ffis pos ls /\
       lab_to_targetProof_offset_ok labs ffis (pos + SUM (MAP
         line_len ls)) ss`];;

(* HOL4 lab_to_targetProofScript.sml:4892: ML code, not ported *)

(* establishing offset_ok *)

let enc_lines_again_simp_offset_ok = prove
 (`!labs ffis pos enc lines res ok.
    enc_lines_again_simp labs ffis pos enc lines = (res,ok) ==>
    lines_offset_ok labs ffis pos res`,
  CHEAT_TAC);;

let enc_secs_again_offset_ok = prove
 (`!pos labs ffis enc ls res ok.
    enc_secs_again pos labs ffis enc ls = (res,ok) ==>
    lab_to_targetProof_offset_ok labs ffis pos res`,
  CHEAT_TAC);;

(* offset_ok preservation *)

let lines_offset_ok_pad_section = prove
 (`!nop lines aux labs ffis pos.
    lab_len_pos_ok (pos + SUM (MAP line_len aux)) lines /\
    lab_len_pos_ok pos (REVERSE aux) /\ ALL label_zero aux /\
    (~(NULL lines) /\ is_Label (HD lines) /\ line_len (HD lines) = 1
      ==>
     ~(NULL aux) /\ ~(is_Label (HD aux))) /\
    lines_offset_ok labs ffis pos (APPEND (REVERSE aux) lines) ==>
    lines_offset_ok labs ffis pos (pad_section nop lines aux)`,
  CHEAT_TAC);;

let offset_ok_pad_code = prove
 (`!labs ffis pos code.
    (~(LENGTH nop = 1) ==> ALL sec_label_zero code) /\
    ALL sec_label_one code /\
    ALL sec_label_prefix_zero code /\
    all_lab_len_pos_ok pos code /\
    lab_to_targetProof_offset_ok labs ffis pos code ==>
    lab_to_targetProof_offset_ok labs ffis pos (pad_code nop code)`,
  CHEAT_TAC);;

(* invariant: referenced labels exist *)

let line_labs_exist_def = new_definition
  `line_labs_exist labs x2 =
        match x2 with
          labLang_LabAsm a _74 _75 _76 ->
       (!n1 n2. (n1,n2) IN labs_of a ==> ~(lab_lookup n1 n2 labs =
         NONE))
        | _77 -> T`;;

(* HOL4 lab_to_targetProofScript.sml:4998: ML code, not ported *)

let sec_labs_exist_def = define_general
  [`sec_labs_exist labs (Section _78 ls) <=> ALL (line_labs_exist
  labs) ls`];;

(* HOL4 lab_to_targetProofScript.sml:5004: the overload
   all_labs_exist, which the port expands *)

(* Remove tail recursion from zero_labs_acc_exist *)
(* [local] *)
let zero_labs_acc_of_eq_zero_labs_of = prove
 (`domain (zero_labs_acc_of l acc) =
   IMAGE FST (restrict_zero (labs_of l)) UNION domain acc`,
  CHEAT_TAC);;

(* [local] *)
let line_get_zero_labs_acc_eq_line_get_zero_labels = prove
 (`domain (line_get_zero_labs_acc l acc) =
   IMAGE FST (restrict_zero (line_get_labels l)) UNION domain acc`,
  CHEAT_TAC);;

(* [local] *)
let sec_get_zero_labs_acc_eq_sec_get_zero_labels = prove
 (`domain (sec_get_zero_labs_acc sec acc) =
   IMAGE FST (restrict_zero (sec_get_labels sec)) UNION domain acc`,
  CHEAT_TAC);;

(* [local] *)
let get_zero_labs_acc_eq_get_zero_labels = prove
 (`domain (ITLIST sec_get_zero_labs_acc code acc) =
   IMAGE FST (restrict_zero (labProps_get_labels code)) UNION
     domain acc`,
  CHEAT_TAC);;

let zero_labs_acc_exist_eq = prove
 (`zero_labs_acc_exist labs code <=>
   restrict_zero (labProps_get_labels code) SUBSET labs_domain labs`,
  CHEAT_TAC);;

(* labs_exist preservation *)
let line_similar_line_labs_exist = prove
 (`!l1 l2. line_similar l1 l2 ==> (line_labs_exist labs l1 <=>
  line_labs_exist labs l2)`,
  CHEAT_TAC);;

let code_similar_all_labs_exist = prove
 (`!c1 c2. code_similar c1 c2 ==> ((\labs code. ALL (sec_labs_exist
  labs) code) labs c1 <=> (\labs code. ALL (sec_labs_exist labs) code)
  labs c2)`,
  CHEAT_TAC);;

(* [simp] *)
let all_labs_exist_pad_code = prove
 (`!nop code. (\labs code. ALL (sec_labs_exist labs) code) labs
  (pad_code nop code) <=> (\labs code. ALL (sec_labs_exist labs) code)
  labs code`,
  CHEAT_TAC);;

let enc_lines_again_line_labs_exist = prove
 (`!labs ffis pos enc lines acc ok res ok' k.
   enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok') /\
   ALL (line_labs_exist labs') acc /\
   ALL (line_labs_exist labs') lines ==>
   ALL (line_labs_exist labs') res`,
  CHEAT_TAC);;

let enc_secs_again_all_labs_exist = prove
 (`!pos ffis labs enc ls res ok k.
    enc_secs_again pos ffis labs enc ls = (res,ok) /\ (\labs code.
      ALL (sec_labs_exist labs) code) labs' ls ==>
    (\labs code. ALL (sec_labs_exist labs) code) labs' res`,
  CHEAT_TAC);;

let upd_lab_len_all_labs_exist = prove
 (`!pos code. (\labs code. ALL (sec_labs_exist labs) code) labs
  (upd_lab_len pos code) <=> (\labs code. ALL (sec_labs_exist labs)
  code) labs code`,
  CHEAT_TAC);;

(* establishing labs_exist *)

let line_similar_line_get_code_labels = prove
 (`!l1 l2. line_similar l1 l2 ==> line_get_code_labels l1 =
  line_get_code_labels l2`,
  CHEAT_TAC);;

let code_similar_get_code_labels = prove
 (`!c1 c2. code_similar c1 c2 ==> labProps_get_code_labels c1 =
  labProps_get_code_labels c2`,
  CHEAT_TAC);;

let line_labs_exist_get_labels = prove
 (`!labs line. line_labs_exist labs line <=> line_get_labels line
  SUBSET labs_domain labs`,
  CHEAT_TAC);;

let sec_labs_exist_get_labels = prove
 (`!labs sec. sec_labs_exist labs sec <=> sec_get_labels sec SUBSET
  labs_domain labs`,
  CHEAT_TAC);;

let all_labs_exist_get_labels = prove
 (`(\labs code. ALL (sec_labs_exist labs) code) labs code <=>
  labProps_get_labels code SUBSET labs_domain labs`,
  CHEAT_TAC);;

let line_similar_line_get_labels = prove
 (`!l1 l2. line_similar l1 l2 ==> (line_get_labels l1 =
  line_get_labels l2)`,
  CHEAT_TAC);;

let code_similar_get_labels = prove
 (`!c1 c2. code_similar c1 c2 ==> labProps_get_labels c1 =
  labProps_get_labels c2`,
  CHEAT_TAC);;

(* [simp] *)
let get_labels_upd_lab_len = prove
 (`labProps_get_labels (upd_lab_len pos code) = labProps_get_labels
  code`,
  CHEAT_TAC);;

let section_labels_line_get_code_labels = prove
 (`!pos lines aux new_pos labs. section_labels pos lines aux =
  (new_pos,labs) ==>
   0 INSERT set_of_list (MAP FST labs) = 0 INSERT (set_of_list (MAP
     FST aux) UNION UNIONS (IMAGE line_get_code_labels (set_of_list
     lines)))`,
  CHEAT_TAC);;

let labs_domain_compute_labels_alt = prove
 (`!pos code labs.
     ALL_DISTINCT (MAP Section_num code) /\
     DISJOINT (domain labs) (set_of_list (MAP Section_num code)) ==>
     labs_domain (compute_labels_alt pos code labs) =
     labProps_get_code_labels code UNION labs_domain labs`,
  CHEAT_TAC);;

(* invariant: labels aligned at even positions *)

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let even_labels_def,even_labels_ind = define_guess_cheat
  [`even_labels pos [] <=> T`;
   `even_labels pos (CONS (Section _79 []) ls) <=> even_labels pos ls`;
   `even_labels pos (CONS (Section k (CONS y ys)) ls) <=>
       (is_Label y ==> EVEN pos) /\
       even_labels (pos + line_len y) (CONS (Section k ys) ls)`];;

(* HOL4 lab_to_targetProofScript.sml:5229: ML code, not ported *)

let lines_even_labels_def,lines_even_labels_ind = define_rec
  [`lines_even_labels pos [] <=> T`;
   `lines_even_labels pos (CONS y ys) <=>
       (is_Label y ==> EVEN pos) /\
       lines_even_labels (pos + line_len y) ys`];;

let even_labels_alt = prove
 (`(even_labels pos [] <=> T) /\
   (even_labels pos (CONS (Section _80 ls) ss) <=>
    lines_even_labels pos ls /\
    even_labels (pos + SUM (MAP line_len ls)) ss)`,
  CHEAT_TAC);;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let even_labels_strong_def,even_labels_strong_ind = define_guess_cheat
  [`even_labels_strong pos [] <=> T`;
   `even_labels_strong pos (CONS (Section _81 []) ls) <=>
        EVEN pos /\ even_labels_strong pos ls`;
   `even_labels_strong pos (CONS (Section k (CONS y ys)) ls) <=>
       (is_Label y ==> EVEN pos) /\
       even_labels_strong (pos + line_len y) (CONS (Section k
         ys) ls)`];;

let even_labels_ends_imp_strong = prove
 (`!pos code.
    even_labels pos code /\
    ALL sec_ends_with_label code /\
    ALL sec_label_zero code ==>
    even_labels_strong pos code`,
  CHEAT_TAC);;

let ALOOKUP_section_labels_ignore = prove
 (`!pos lines acc.
   ~(MEM n2 (MAP SND (labProps_extract_labels lines))) ==>
   ALOOKUP (SND (section_labels pos lines acc)) n2 =
   ALOOKUP acc n2`,
  CHEAT_TAC);;

let lines_ok_section_lab_lookup_even = prove
 (`!pos lines acc.
   lines_ok c labs ffis pos lines /\
   (!l2 x. ALOOKUP acc l2 = SOME x ==> EVEN x) /\
   ALOOKUP (SND (section_labels pos lines acc)) l2 = SOME x ==>
   EVEN x`,
  CHEAT_TAC);;

(* [local] *)
let all_enc_ok_split = prove
 (`!c labs ffis pos k lines xs.
   all_enc_ok c labs ffis pos (CONS (Section k lines) xs) ==>
   all_enc_ok c labs ffis pos [Section k lines] /\
   all_enc_ok c labs ffis (pos + sec_length lines 0) xs`,
  CHEAT_TAC);;

(* [local] *)
let all_enc_ok_even = prove
 (`!lines pos.
   all_enc_ok c labs ffis pos [Section k lines] ==>
   EVEN (sec_length lines pos)`,
  CHEAT_TAC);;

(* [local] *)
let all_enc_ok_lab_lookup_even = prove
 (`!c labs ffis pos sec_list l1 l2 acc x.
       all_enc_ok c labs ffis pos sec_list /\
       lab_lookup l1 l2 (compute_labels_alt pos sec_list acc) = SOME
         x /\
       (!x. lab_lookup l1 l2 acc = SOME x ==> EVEN x) /\
       EVEN pos ==>
       EVEN x`,
  CHEAT_TAC);;

let line_ok_pre_light_imp_line_ok = prove
 (`!c labs ffis pos line.
     line_ok_pre c line /\
     line_enc_with_nop (asm_config_encode c) labs ffis pos line /\
     line_offset_ok labs ffis pos line /\
     line_labs_exist labs line /\
     line_ok_light c line /\ (is_Label line ==> EVEN pos) ==>
     line_ok c labs ffis pos line`,
  CHEAT_TAC);;

let all_enc_ok_pre_light_imp_all_enc_ok = prove
 (`!c labs ffis pos code.
    all_enc_with_nop (asm_config_encode c) labs ffis pos code /\
    (\c ls. ALL (sec_ok_pre c) ls) c code /\
    (\c ls. ALL (sec_ok_light c) ls) c code /\
    even_labels_strong pos code /\
    (\labs code. ALL (sec_labs_exist labs) code) labs code /\
    lab_to_targetProof_offset_ok labs ffis pos code ==>
    all_enc_ok c labs ffis pos code`,
  CHEAT_TAC);;

(* HOL4 lab_to_targetProofScript.sml:5405-5413: code that the source
   has in a comment *)

let upd_lab_len_ends_with_label = prove
 (`!pos ss.
    ALL sec_ends_with_label ss ==>
    ALL sec_ends_with_label (upd_lab_len pos ss)`,
  CHEAT_TAC);;

let lab_lookup_compute_labels_alt_ignore = prove
 (`!pos secs acc.
   ~(MEM n1 (MAP Section_num secs)) ==>
   lab_lookup n1 n2 (compute_labels_alt pos secs acc) = lab_lookup
     n1 n2 acc`,
  CHEAT_TAC);;

let ALOOKUP_section_labels = prove
 (`!pos lines acc pc'.
   ALL (sec_label_ok n1) lines /\
   ALL line_length_ok lines /\
   ALL label_zero lines /\
   ALL_DISTINCT (labProps_extract_labels lines) /\
   sec_loc_to_pc n2 lines = SOME pc' /\ ~(n2 = 0) ==>
   (?i.
     ALOOKUP (SND (section_labels pos lines acc)) n2 = SOME i /\
     ((sec_pos_val pc' pos lines = NONE /\
       i = pos + SUM (MAP line_length lines) /\
       pc' = LENGTH (FILTER ((~) o is_Label) lines)) \/
      sec_pos_val pc' pos lines = SOME i))`,
  CHEAT_TAC);;

(* [local] *)
let lab_lookup_compute_labels_test = prove
 (`!pos sec_list acc l1 l2 x2 c labs ffis nop.
       ALL sec_labels_ok sec_list /\
       ALL_DISTINCT (MAP Section_num sec_list) /\
       ALL (ALL_DISTINCT o labProps_extract_labels o Section_lines)
         sec_list /\
       ALL sec_label_zero sec_list /\
       all_enc_ok c labs ffis pos sec_list /\
       loc_to_pc l1 l2 sec_list = SOME x2 ==>
       lab_lookup l1 l2 (compute_labels_alt pos sec_list acc) =
       SOME (pos_val x2 pos sec_list)`,
  CHEAT_TAC);;

let enc_lines_again_simp_ends_with_label = prove
 (`!labs ffis pos enc ls res ok.
    enc_lines_again_simp labs ffis pos enc ls = (res,ok) /\
    ~(NULL ls) /\ is_Label (LAST ls) ==>
    ~(NULL res) /\ is_Label (LAST res)`,
  CHEAT_TAC);;

let enc_secs_again_ends_with_label = prove
 (`!pos labs ffis enc lines res ok.
    enc_secs_again pos labs ffis enc lines = (res,ok) /\
    ALL sec_ends_with_label lines ==>
    ALL sec_ends_with_label res`,
  CHEAT_TAC);;

let enc_sec_list_ends_with_label = prove
 (`!enc code.
   ALL sec_ends_with_label code ==>
   ALL sec_ends_with_label (enc_sec_list enc code)`,
  CHEAT_TAC);;

let lines_even_labels_append = prove
 (`!l1 l2 pos.
    lines_even_labels pos (APPEND l1 l2) <=>
    lines_even_labels pos l1 /\
    lines_even_labels (pos + SUM (MAP line_len l1)) l2`,
  CHEAT_TAC);;

let label_zero_pos_ok_lines_even_labels = prove
 (`!pos ls.
    ALL label_zero ls /\
    lab_len_pos_ok pos ls ==>
    lines_even_labels pos ls`,
  CHEAT_TAC);;

let label_zero_pos_ok_even_labels = prove
 (`!pos code.
   ALL sec_label_zero code /\
   all_lab_len_pos_ok pos code ==>
   even_labels pos code`,
  CHEAT_TAC);;

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

let pad_code_ends_with_label = prove
 (`!nop ls.
    ALL sec_ends_with_label ls ==>
    ALL sec_ends_with_label (pad_code nop ls)`,
  CHEAT_TAC);;

let enc_lines_again_section_labels = prove
 (`!labs ffis pos enc lines res acc.
    enc_lines_again_simp labs ffis pos enc lines = (res,T) ==>
    section_labels pos lines acc = section_labels pos res acc`,
  CHEAT_TAC);;

let enc_secs_again_compute_labels = prove
 (`!pos labs ffis enc secs res acc.
   enc_secs_again pos labs ffis enc secs = (res,T) ==>
   compute_labels_alt pos res acc =
   compute_labels_alt pos secs acc`,
  CHEAT_TAC);;

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

let pad_section_labels = prove
 (`!nop lines aux pos labs.
    lab_len_pos_ok (pos + SUM (MAP line_len aux)) lines /\
    lab_len_pos_ok pos (REVERSE aux) /\ ALL label_zero aux /\
    (~(NULL lines) /\ is_Label (HD lines) /\ line_len (HD lines) = 1
      ==>
     ~(NULL aux) /\ ~(is_Label (HD aux))) ==>
    section_labels pos (pad_section nop lines aux) labs =
    section_labels pos (APPEND (REVERSE aux) lines) labs`,
  CHEAT_TAC);;

let pad_code_compute_labels = prove
 (`!pos code acc.
    ALL sec_label_one code /\
    (~(LENGTH nop = 1) ==> ALL sec_label_zero code) /\
    ALL sec_label_prefix_zero code /\
    all_lab_len_pos_ok pos code ==>
    compute_labels_alt pos (pad_code nop code) acc =
    compute_labels_alt pos code acc`,
  CHEAT_TAC);;

(* [local] *)
let enc_lines_again_all_enc_ok_pre = prove
 (`!labs ffis pos enc lines acc ok res ok' c.
   enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok') /\
   ALL (line_ok_pre c) lines /\ ALL (line_ok_pre c) acc ==>
   ALL (line_ok_pre c) res`,
  CHEAT_TAC);;

(* [local] *)
let enc_secs_again_all_enc_ok_pre = prove
 (`!pos labs ffis enc ls res ok c.
   enc_secs_again pos labs ffis enc ls = (res,ok) /\ (\c ls. ALL
     (sec_ok_pre c) ls) c ls ==>
   (\c ls. ALL (sec_ok_pre c) ls) c res`,
  CHEAT_TAC);;

(* [local] *)
let line_ok_pre_add_nop = prove
 (`ALL (line_ok_pre c) xs ==>
   ALL (line_ok_pre c) (add_nop nop xs)`,
  CHEAT_TAC);;

(* [local] *)
let line_ok_pre_pad_section = prove
 (`!nop xs acc c.
   ALL (line_ok_pre c) xs /\ ALL (line_ok_pre c) acc ==>
   ALL (line_ok_pre c) (pad_section nop xs acc)`,
  CHEAT_TAC);;

(* [local] *)
let all_enc_ok_pre_pad_code = prove
 (`!nop code c.
   (\c ls. ALL (sec_ok_pre c) ls) c code ==>
   (\c ls. ALL (sec_ok_pre c) ls) c (pad_code nop code)`,
  CHEAT_TAC);;

(* [local] *)
let all_enc_ok_pre_lines_upd_lab_len = prove
 (`!n lines acc.
   ALL (line_ok_pre c) lines /\
   ALL (line_ok_pre c) acc ==>
   ALL (line_ok_pre c) (FST (lines_upd_lab_len n lines acc))`,
  CHEAT_TAC);;

(* [local] *)
let all_enc_ok_pre_upd_lab_len = prove
 (`!n code.
   (\c ls. ALL (sec_ok_pre c) ls) c code ==>
   (\c ls. ALL (sec_ok_pre c) ls) c (upd_lab_len n code)`,
  CHEAT_TAC);;

(* [local] *)
let EXP_IMP_ZERO_LT = prove
 (`(2 EXP y = x) ==> 0 < x`,
  CHEAT_TAC);;

let line_ok_alignment = prove
 (`!c labs ffis pos line.
   enc_ok c /\
   line_ok c labs ffis pos line /\ ODD (line_length line) ==>
     asm_config_code_alignment c = 0`,
  CHEAT_TAC);;

let has_odd_inst_alignment = prove
 (`!c labs ffis pos code.
   enc_ok c /\
   all_enc_ok c labs ffis pos code /\ has_odd_inst code ==>
     asm_config_code_alignment c = 0`,
  CHEAT_TAC);;

(* [local] *)
let remove_labels_loop_thm = prove
 (`!n c init_pos init_labs ffis code code2 labs.
     remove_labels_loop n c init_pos init_labs ffis code = SOME
       (code2,labs) /\
     ALL sec_ends_with_label code /\
     ALL sec_labels_ok code /\
     ALL_DISTINCT (MAP Section_num code) /\
     ALL (ALL_DISTINCT o labProps_extract_labels o Section_lines)
       code /\
     DISJOINT (domain init_labs) (set_of_list (MAP Section_num code))
       /\
     // TODO this is stronger:
     // get_labels code ⊆ get_code_labels code ∪ labs_domain init_labs ∧
     restrict_nonzero (labProps_get_labels code) SUBSET
       labProps_get_code_labels code UNION labs_domain init_labs /\
     (\c ls. ALL (sec_ok_pre c) ls) c code /\
     // new loop invariant
     (\enc l. ALL (sec_encd0 enc) l) (asm_config_encode c) code /\
     enc_ok c /\
     EVEN init_pos /\
     (!l1 l2. OPTION_ALL EVEN (lab_lookup l1 l2 init_labs)) ==>
     (\c ls. ALL (sec_ok_pre c) ls) c code2 /\
     ALL sec_labels_ok code2 /\
     all_enc_ok c labs ffis init_pos code2 /\
     code_similar code code2 /\
     (has_odd_inst code2 ==> asm_config_code_alignment c = 0) /\
     (!l1 l2 x. lab_lookup l1 l2 labs = SOME x ==> EVEN x) /\
     (!l1 l2 x. lab_lookup l1 l2 init_labs = SOME x ==>
                lab_lookup l1 l2 labs = SOME x) /\
     (!l1 l2 x2.
       loc_to_pc l1 l2 code = SOME x2 ==>
       lab_lookup l1 l2 labs = SOME (pos_val x2 init_pos code2))`,
  CHEAT_TAC);;

(* [simp] *)
let loc_to_pc_enc_sec_list = prove
 (`!l1 l2 code.
     loc_to_pc l1 l2 (enc_sec_list e code) = loc_to_pc l1 l2 code`,
  CHEAT_TAC);;

(* [local] *)
let all_enc_ok_pre_enc_sec_list = prove
 (`!code enc c.
   (\c ls. ALL (sec_ok_pre c) ls) c code ==>
   (\c ls. ALL (sec_ok_pre c) ls) c (enc_sec_list enc code)`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let remove_labels_thm = prove
 (cake_as_vars (fun () ->
    `remove_labels clock conf init_pos init_labs ffi_names code = SOME
  (code2,labs) /\
     enc_ok conf /\
     ALL sec_ends_with_label code /\
     ALL sec_labels_ok code /\
     ALL_DISTINCT (MAP Section_num code) /\
     ALL (ALL_DISTINCT o labProps_extract_labels o Section_lines)
       code /\
     DISJOINT (domain init_labs) (set_of_list (MAP Section_num
       code)) /\
     restrict_nonzero (labProps_get_labels code) SUBSET
       labProps_get_code_labels code UNION labs_domain init_labs /\
     (\c ls. ALL (sec_ok_pre c) ls) conf code /\
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
       lab_lookup l1 l2 labs = SOME (pos_val x2 init_pos code2))`),
  CHEAT_TAC);;

let compute_labels_alt_domain_labs = prove
 (`!pos code labs.
     domain (compute_labels_alt pos code labs) =
     IMAGE FST (labProps_get_code_labels code) UNION domain labs`,
  CHEAT_TAC);;

let remove_labels_loop_domain_labs = prove
 (`!a b c d e f g h. remove_labels_loop a b c d e f = SOME (g,h) ==>
   domain h = IMAGE FST (labProps_get_code_labels f) UNION domain d`,
  CHEAT_TAC);;

let remove_labels_domain_labs = prove
 (`remove_labels c t k init_labs f p = SOME (q,labs) ==>
   domain labs = IMAGE FST (labProps_get_code_labels p) UNION
     domain init_labs`,
  CHEAT_TAC);;

(** End syntactic stuff **)

let LENGTH_prog_to_bytes = prove
 (`!code n c labs ffi pos.
   all_enc_ok c labs ffi pos code ==>
   FOLDL (\pos sec. sec_length (Section_lines sec) pos) n code =
   LENGTH (prog_to_bytes code) + n`,
  CHEAT_TAC);;

let LENGTH_prog_to_bytes2 = prove
 (`!code n c labs ffi pos.
   all_enc_ok c labs ffi pos code ==>
   SUM (MAP (SUM o MAP line_length o Section_lines) code) =
   LENGTH (prog_to_bytes code)`,
  CHEAT_TAC);;

let prog_to_bytes_APPEND = prove
 (`prog_to_bytes (APPEND c1 c2) = APPEND (prog_to_bytes c1)
  (prog_to_bytes c2)`,
  CHEAT_TAC);;

let line_ok_line_byte_length = prove
 (`line_ok c labs ffi n l ==>
   LENGTH (line_bytes l) = line_length l`,
  CHEAT_TAC);;

let lines_ok_MAP_line_byte_length = prove
 (`!ls c labs ffi n.
   lines_ok c labs ffi n ls ==>
   MAP LENGTH (MAP line_bytes ls) = MAP line_length ls`,
  CHEAT_TAC);;

(* [local] *)
let all_enc_ok_prog_to_bytes_EVEN = prove
 (`!code n c labs ffi pos.
    EVEN pos /\
    all_enc_ok c labs ffi pos code ==>
    EVEN (LENGTH (prog_to_bytes code))`,
  CHEAT_TAC);;

(* [local] *)
let loc_to_pc_append = prove
 (`!l1 l2 c1 c2 conf labs ffis pos.
   ALL sec_labels_ok (APPEND c1 c2) ==>
   loc_to_pc l1 l2 (APPEND c1 c2) =
   (match loc_to_pc l1 l2 c1 with
     SOME x -> SOME x | NONE ->
     (match loc_to_pc l1 l2 c2 with
       SOME x -> SOME (x + SUM (MAP ((\xs. LENGTH (FILTER ((~) o
         is_Label) xs)) o Section_lines) c1)) | NONE -> NONE))`,
  CHEAT_TAC);;

let all_enc_ok_append = prove
 (`!conf labs ffi n c1 c2.
   all_enc_ok conf labs ffi n c1 /\
   all_enc_ok conf labs ffi (n + LENGTH (prog_to_bytes c1)) c2 ==>
   all_enc_ok conf labs ffi n (APPEND c1 c2)`,
  CHEAT_TAC);;

let extract_labels_loc_to_pc = prove
 (`!l1 l2 code.
   ALL sec_labels_ok code /\
   MEM (l1,l2) (FLAT (MAP (labProps_extract_labels o Section_lines)
     code)) ==>
   (?y. loc_to_pc l1 l2 code = SOME y)`,
  CHEAT_TAC);;

let all_enc_ok_labs_mono = prove
 (`!conf labs ffi n c labs2.
   (!l1 l2 x.
   lab_lookup l1 l2 labs = SOME x ==>
   lab_lookup l1 l2 labs2 = SOME x) /\
   all_enc_ok conf labs ffi n c ==>
   all_enc_ok conf labs2 ffi n c`,
  CHEAT_TAC);;

let pos_val_append = prove
 (`!c1 i pos c2.
   ALL sec_label_zero c2 ==>
   pos_val i pos (APPEND c1 c2) =
   (if i <= (SUM (MAP ((\xs. LENGTH (FILTER ((~) o is_Label) xs)) o
     Section_lines) c1)) then
   pos_val i pos c1 else
    pos_val (i - (SUM (MAP ((\xs. LENGTH (FILTER ((~) o is_Label)
      xs)) o Section_lines) c1))) (pos + (SUM (MAP (SUM o MAP
      line_length o Section_lines) c1))) c2)`,
  CHEAT_TAC);;

let sec_pos_val_acc = prove
 (`!l n i.
   (\xs. LENGTH (FILTER ((~) o is_Label) xs)) l <= i ==>
   sec_pos_val i n l = NONE`,
  CHEAT_TAC);;

let pos_val_acc = prove
 (`!ls n.
   pos_val (SUM (MAP ((\xs. LENGTH (FILTER ((~) o is_Label) xs)) o
     Section_lines) ls)) n ls =
   n + SUM (MAP (SUM o (MAP line_length) o Section_lines) ls)`,
  CHEAT_TAC);;

let pos_val_bound = prove
 (`!i pos code conf labs ffi n.
   all_enc_ok conf labs ffi n code ==>
   pos_val i pos code <= pos + LENGTH (prog_to_bytes code)`,
  CHEAT_TAC);;

let sec_loc_to_pc_bound = prove
 (`!n xs x.
   sec_loc_to_pc n xs = SOME x ==>
   x <= (\xs. LENGTH (FILTER ((~) o is_Label) xs)) xs`,
  CHEAT_TAC);;

let loc_to_pc_bound = prove
 (`!code l1 l2 x.
   ALL sec_labels_ok code /\
   loc_to_pc l1 l2 code = SOME x ==>
   x <= SUM (MAP ((\xs. LENGTH (FILTER ((~) o is_Label) xs)) o
     Section_lines) code)`,
  CHEAT_TAC);;

(* [local] *)
let find_ffi_names_append = prove
 (`!l1 l2.
   find_ffi_names (APPEND l1 l2) = APPEND (find_ffi_names l2)
   (FILTER (\n. ~(MEM n (find_ffi_names l2))) (find_ffi_names l1))`,
  CHEAT_TAC);;

let all_enc_ok_aligned_pos_val = prove
 (`!(mc_conf:('a,'b,'c)machine_config) labs code2 pc' ffi_names'.
    all_enc_ok (target_config (machine_config_target mc_conf)) labs
      ffi_names' 0 code2 /\
    (has_odd_inst code2 ==> asm_config_code_alignment (target_config
      (machine_config_target mc_conf)) = 0) /\
    encoder_correct (machine_config_target mc_conf) ==>
    alignment_aligned (asm_config_code_alignment (target_config
      (machine_config_target mc_conf))) (n2w (pos_val pc' 0 code2):'a
      word)`,
  CHEAT_TAC);;

(* [simp] *)
let read_ffi_bytearrays_with_next_interfer = prove
 (`read_ffi_bytearrays (machine_config_next_interfer_fupd (K foo) mc) =
   read_ffi_bytearrays mc`,
  CHEAT_TAC);;

(* [simp] *)
let read_ffi_bytearrays_shift_interfer = prove
 (`read_ffi_bytearrays (shift_interfer x y) = read_ffi_bytearrays y`,
  CHEAT_TAC);;

(* [simp] *)
let read_ffi_bytearrays_ffi_interfer = prove
 (`read_ffi_bytearrays (machine_config_ffi_interfer_fupd (K ffi) mc) =
  read_ffi_bytearrays mc`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let IMP_ffi_entry_pcs_disjoint_Asm = prove
 (cake_as_vars (fun () ->
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
         (mc_conf:('a,'state,'b)machine_config) t1 (LENGTH bytes')`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let IMP_ffi_entry_pcs_disjoint_LabAsm = prove
 (cake_as_vars (fun () ->
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
         (mc_conf:('a,'state,'b)machine_config) t1 (LENGTH bytes')`),
  CHEAT_TAC);;

let asm_fetch_SOME_IMP_LESS_num_pcs = prove
 (`!pc' secs x.
     asm_fetch_aux pc' secs = SOME x ==>
     pc' < num_pcs secs`,
  CHEAT_TAC);;

let GENLIST_asm_fetch_aux_next = prove
 (`~(is_Label x) ==>
   list_of_seq (\i.
     (i,asm_fetch_aux i (CONS (Section k (CONS x xs)) rest)))
     (n + 1) = CONS (0,SOME x) (
     list_of_seq (\i.
       (i + 1,asm_fetch_aux i (CONS (Section k xs) rest))) n)`,
  CHEAT_TAC);;

let pos_val_acc_sum = prove
 (`!i pos secs x y.
     x + y = pos ==>
     x + pos_val i y secs = pos_val i pos secs`,
  CHEAT_TAC);;

let pos_val_acc_0 = prove
 (`!i pos secs.
   pos + pos_val i 0 secs = pos_val i pos secs`,
  CHEAT_TAC);;

let FILTER_mmio_pcs_min_index = prove
 (`ALL (\x. ?op. x = ffi_SharedMem op) l ==>
   mmio_pcs_min_index
     (APPEND (FILTER (\x. ?s. x = ffi_ExtCall s) ffis) l) =
   SOME (LENGTH
     (FILTER (\x. ?s. x = ffi_ExtCall s) ffis))`,
  CHEAT_TAC);;

let pos_val_GE_pc = prove
 (`!i p code2.
     p <= pos_val i p code2`,
  CHEAT_TAC);;

let enc_ok_LENGTH_GT_0 = prove
 (`enc_ok c ==>
   0 < LENGTH (asm_config_encode c l)`,
  CHEAT_TAC);;

let pos_val_mono = prove
 (`!i p code2 j p'.
     i < j /\
     j <= num_pcs code2 /\
     all_enc_ok c labs ffis p' code2 /\
     enc_ok c ==>
     pos_val i p code2 < pos_val j p code2`,
  CHEAT_TAC);;

let pos_val_mono_inv = prove
 (`!i p code2 j.
     pos_val i p code2 < pos_val j p code2 /\
     i <= num_pcs code2 /\
     all_enc_ok c labs ffis p' code2 /\
     enc_ok c ==>
     i < j`,
  CHEAT_TAC);;

let pos_val_inj = prove
 (`!p code2 j.
     pos_val i p code2 = pos_val j p code2 /\
     i <= num_pcs code2 /\ j <= num_pcs code2 /\
     all_enc_ok c labs ffis p' code2 /\
     enc_ok c ==>
     i = j`,
  CHEAT_TAC);;

let pos_val_num_pcs = prove
 (`!c labs ffis p' code2.
     all_enc_ok c labs ffis p' code2 ==>
     pos_val (num_pcs code2) p code2 = p + LENGTH (prog_to_bytes
       code2)`,
  CHEAT_TAC);;

let pos_val_GE_num_pcs = prove
 (`!pc' p code2.
     num_pcs code2 <= pc' ==>
     pos_val (num_pcs code2) p code2 = pos_val pc' p code2`,
  CHEAT_TAC);;

let pos_val_0_aux = prove
 (`!c labs ffis p xs pos.
     all_enc_ok c labs ffis p xs ==> (pos_val 0 pos xs = pos)`,
  CHEAT_TAC);;

let asm_fetch_aux_pos_val_SUC = prove
 (`!pc' p code2 p'.
     all_enc_ok c labs ffi p' code2 /\
     asm_fetch_aux pc' (code2:('a sec) list) = SOME line ==>
     LENGTH (line_bytes line) + pos_val pc' p code2 = pos_val (pc'
       + 1) p code2`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let pos_val_asm_fetch_aux_distinct = prove
 (cake_as_vars (fun () ->
    `all_enc_ok c labs ffis p' (code2:('a sec) list) /\
     enc_ok c /\
     asm_fetch_aux pc code2 = SOME line /\
     a < LENGTH (line_bytes line) /\
     LENGTH (prog_to_bytes code2) < dimword (:'a) /\ ~(pc' = pc)
       ==> ~(a + pos_val pc p code2 = pos_val pc' p code2)`),
  CHEAT_TAC);;

let bytes_in_memory_eq_mem = prove
 (`!pc' bytes.
     (!a. a IN asm_state_mem_domain t1 ==> target_get_byte
       (machine_config_target mc_conf) ms1 a = asm_state_mem t1 a) /\
     bytes_in_memory pc' bytes (asm_state_mem t1)
       (asm_state_mem_domain t1) ==>
     bytes_in_memory pc' bytes (target_get_byte
       (machine_config_target mc_conf) ms1) (asm_state_mem_domain t1)`,
  CHEAT_TAC);;

(* HOL4 lab_to_targetProofScript.sml:6959-6967: ML code, not ported *)

(* HOL4 lab_to_targetProofScript.sml:6969-6978: a proof *)

(* HOL4 lab_to_targetProofScript.sml:6980-7059: a proof *)

(* HOL4 lab_to_targetProofScript.sml:7061-7157: a proof *)

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let ffi_entry_pcs_NOT_ccache_OR_halt_pc = prove
 (cake_as_vars (fun () ->
    `find_index pc (machine_config_ffi_entry_pcs mc_conf) 0 =
        SOME index /\ ~(machine_config_halt_pc
     mc_conf = EL index (machine_config_ffi_entry_pcs mc_conf)) /\
       ~(machine_config_ccache_pc
     mc_conf = EL index (machine_config_ffi_entry_pcs mc_conf))
       ==> ~(pc = machine_config_ccache_pc mc_conf) /\ ~(pc =
       machine_config_halt_pc mc_conf)`),
  CHEAT_TAC);;

(* HOL4 lab_to_targetProofScript.sml:7171-7200: a proof *)

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let ffi_name_NOT_Mapped = prove
 (cake_as_vars (fun () ->
    `mmio_pcs_min_index ffi_names = SOME i /\ (?str. s = ffi_ExtCall
  str) /\
     MEM s ffi_names ==>
     get_ffi_index ffi_names s < i`),
  CHEAT_TAC);;

let mmio_pcs_min_index_is_SOME = prove
 (`!ffi_names'.
     mmio_pcs_min_index ffi_names' = SOME i ==>
     i <= LENGTH ffi_names' /\
     (!j. j < i ==>
       (?s. EL j ffi_names' = ffi_ExtCall s)) /\
      (!j. i <= j /\ j < LENGTH ffi_names' ==>
        (?op. EL j ffi_names' = ffi_SharedMem op))`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let no_share_mem_lemma = prove
 (cake_as_vars (fun () ->
    `mmio_pcs_min_index ffi_names = SOME i /\
     asm_fetch_aux pc code = SOME (labLang_LabAsm labLang_Install c
       l n) /\
     no_install_or_no_share_mem code ffi_names ==>
     i = LENGTH ffi_names`),
  CHEAT_TAC);;

let asm_fetch_aux_APPEND1 = prove
 (`!pc' code.
     pc' < num_pcs code ==>
     asm_fetch_aux pc' (APPEND code sec_list) = asm_fetch_aux pc'
       code`,
  CHEAT_TAC);;

let pos_val_APPEND1 = prove
 (`!pc' code.
     pc' < num_pcs code ==>
     pos_val pc' 0 (APPEND code sec_list) = pos_val pc' 0 code`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let asm_fetch_aux_APPEND2 = prove
 (cake_as_vars (fun () ->
    `!code.
       asm_fetch_aux (pc + num_pcs code) (APPEND code sec_list) =
         asm_fetch_aux pc sec_list`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let pos_val_APPEND2 = prove
 (cake_as_vars (fun () ->
    `!c labs ffis p code.
       all_enc_ok c labs ffis p code ==>
       pos_val (pc + num_pcs code) 0 (APPEND code sec_list) =
         LENGTH (prog_to_bytes code) + pos_val pc 0 sec_list`),
  CHEAT_TAC);;

let get_shmem_info_MappedRead_or_MappedWrite = prove
 (`!sec pos ffi_names' info new_ffi_names new_info.
     get_shmem_info sec pos ffi_names' info =
       (new_ffi_names,new_info) ==>
     (?l. new_ffi_names = APPEND ffi_names' l /\
       ALL (\x. ?op. x = ffi_SharedMem op) l)`,
  CHEAT_TAC);;

let no_share_mem_APPEND = prove
 (`no_share_mem_inst code /\
   no_share_mem_inst secs ==>
   no_share_mem_inst (APPEND code secs)`,
  CHEAT_TAC);;

let no_install_APPEND_IMP = prove
 (`labProps_no_install (APPEND code secs) ==>
   labProps_no_install code /\ labProps_no_install secs`,
  CHEAT_TAC);;

let code_similar_IMP_both_no_share_mem = prove
 (`code_similar code sec_list /\
   no_share_mem_inst code ==>
   no_share_mem_inst sec_list`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let code_similar_IMP_both_no_install_or_no_share_mem = prove
 (cake_as_vars (fun () ->
    `code_similar code sec_list /\
     no_install_or_no_share_mem code ffi_names ==>
     no_install_or_no_share_mem sec_list ffi_names`),
  CHEAT_TAC);;

let no_share_mem_IMP_get_shmem_info = prove
 (`!code p ffi_names' shmem_info.
     no_share_mem_inst code ==>
     get_shmem_info code p ffi_names' shmem_info =
       (ffi_names',shmem_info)`,
  CHEAT_TAC);;

(* move *)
let Sh_not_Ext = prove
 (`(?s. x = ffi_SharedMem s) <=> (!s. ~(x = ffi_ExtCall s))`,
  CHEAT_TAC);;

let not_Sh_Ext = prove
 (`(!s. ~(x = ffi_SharedMem s)) <=> (?s. x = ffi_ExtCall s)`,
  CHEAT_TAC);;

let oracle_tie_shift_gen = prove
 (`!mc_conf mc2 ms1 s1 ms2 l.
   oracle_tie mc_conf ms1 (s1:('a,'c,'ffi)labSem_state) /\
   (!k. find_next_interference mc_conf (labSem_state_ffi s1) (k + l)
     ms1 =
        find_next_interference mc2 (labSem_state_ffi s1) k ms2) /\
          machine_config_target
   mc2 = machine_config_target mc_conf /\
     machine_config_callee_saved_regs
   mc2 = machine_config_callee_saved_regs mc_conf /\ ptr_reg
   mc2 = machine_config_ptr_reg mc_conf ==>
   oracle_tie mc2 ms2 s1`,
  CHEAT_TAC);;

let oracle_tie_ccache_residues = prove
 (`!mc_conf mc2 ms1 s1 ms2 l t1.
   oracle_tie mc_conf ms1 (s1:('a,'c,'ffi)labSem_state) /\
   (!k. find_next_interference mc_conf (labSem_state_ffi s1) (k + l)
     ms1 =
        find_next_interference mc2 (labSem_state_ffi s1) k ms2) /\
          machine_config_target
   mc2 = machine_config_target mc_conf /\ ptr_reg
   mc2 = machine_config_ptr_reg mc_conf /\ len_reg
   mc2 = machine_config_len_reg mc_conf /\
     machine_config_ccache_interfer
   mc2 = machine_config_ccache_interfer mc_conf /\ ~(target_get_pc
     (machine_config_target
   mc2) ms2 IN machine_config_prog_addresses mc2 DIFF set_of_list
     (machine_config_ffi_entry_pcs mc2)) /\ ~(target_get_pc
     (machine_config_target
   mc2) ms2 = machine_config_halt_pc mc2) /\ target_get_pc
     (machine_config_target
   mc2) ms2 = machine_config_ccache_pc mc2 ==>
   (\a. get_reg_value (labSem_state_cc_regs s1 0 a) (asm_state_regs
     t1 a) I) =
     (\a. if MEM a (machine_config_callee_saved_regs mc_conf) \/ a =
       machine_config_ptr_reg mc_conf \/
             ~(a < asm_config_reg_count (target_config
               (machine_config_target mc_conf))) \/
             MEM a (asm_config_avoid_regs (target_config
               (machine_config_target mc_conf))) then asm_state_regs t1
               a else target_get_reg (machine_config_target mc_conf)
                 (machine_config_ccache_interfer mc_conf 0
                    (target_get_reg (machine_config_target mc_conf)
                      ms2 (machine_config_ptr_reg
                      mc_conf),target_get_reg (machine_config_target
                     mc_conf) ms2 (machine_config_len_reg
                       mc_conf),ms2)) a) /\
   (\n. labSem_state_cc_fp_regs s1 0 n) =
     (\n. target_get_fp_reg (machine_config_target mc_conf)
            (machine_config_ccache_interfer mc_conf 0
               (target_get_reg (machine_config_target mc_conf) ms2
                 (machine_config_ptr_reg mc_conf),target_get_reg
                 (machine_config_target
                mc_conf) ms2 (machine_config_len_reg mc_conf),ms2))
                  n)`,
  CHEAT_TAC);;

(* HOL4 lab_to_targetProofScript.sml:7526: ML code, not ported *)

(* HOL4 lab_to_targetProofScript.sml:7528-7558: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   compile_correct *)

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

let init_ok_def = new_definition
  `init_ok (mc_conf,p) s ms <=>
     (?code2 labs t1.
       lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s t1 ms /\
       oracle_tie mc_conf ms s)`;;

(* HOL4 lab_to_targetProofScript.sml:9364-9526: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   machine_sem_EQ_sem *)

(* HOL4 lab_to_targetProofScript.sml:9528-9531: code that the source
   has in a comment *)

(* introducing make_init *)

let set_bytes_def,set_bytes_ind = define_rec
  [`set_bytes a be' [] = (n2w 0)`;
   `set_bytes a be' (CONS b bs) = set_byte a b (set_bytes (a + (n2w
  1)) be' bs) be'`];;

let make_word_def = new_definition
  `make_word be' m (a:'a word) =
     (if dimindex (:'a) = 32 then
       wordLang_Word (set_bytes a be' [m a; m (a + (n2w 1)); m (a +
         (n2w 2)); m (a + (n2w 3))]) else
       wordLang_Word (set_bytes a be' [m a; m (a + (n2w 1)); m (a +
         (n2w 2)); m (a + (n2w 3));
                             m (a + (n2w 4)); m (a + (n2w 5)); m
                               (a + (n2w 6)); m (a + (n2w 7))]))`;;

let make_init_def = new_definition
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

let oracle_tie_make_init = prove
 (`oracle_tie mc_conf ms
     (lab_to_targetProof_make_init mc_conf ffi t m dm sdm ms code
       cmp cbpos cbspace coracle)`,
  CHEAT_TAC);;

(* HOL4 lab_to_targetProofScript.sml:9586: the ML values that the
   definitions below antiquote *)

let compiler_oracle_ok_def = new_definition
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
let mc_conf_ok_def = new_definition
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

let get_shmem_info_APPEND = prove
 (`!secs pos ffi_names' shmem_info ffis1 ffis2 info1 info2 new_ffi_names
  new_shmem_info.
     get_shmem_info secs pos ffi_names' (shmem_info:shmem_info_num
       list) =
       (new_ffi_names,new_shmem_info) /\
     ffi_names' = APPEND ffis1 ffis2 /\
     shmem_info = APPEND info1 info2 ==>
     new_ffi_names = APPEND ffis1 (FST (get_shmem_info secs pos ffis2
       info2)) /\
     new_shmem_info = APPEND info1 (SND (get_shmem_info secs pos
       ffis2 info2))`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let get_shmem_info_PREPEND = prove
 (cake_as_vars (fun () ->
    `get_shmem_info secs pos ffi_names (shmem_info:shmem_info_num list)
  =
       (new_ffi_names,new_shmem_info) ==>
     new_ffi_names = APPEND ffi_names (FST (get_shmem_info secs pos
       [] [])) /\
     new_shmem_info = APPEND shmem_info (SND (get_shmem_info secs
       pos [] []))`),
  CHEAT_TAC);;

let line_to_info_def = new_definition
  `line_to_info (secs:('a sec) list) p x = (match SND x with
     SOME (labLang_Asm (ShareMem m r ad) bytes l) ->
       (let (name,nb) = get_memop_info m in
       [(ffi_SharedMem name,
        mk_shmem_info_num (pos_val (FST x) p secs) nb (match ad
          with Addr r off -> r) (match ad with Addr r off -> w2n off)
          r (pos_val (FST x) p secs + LENGTH bytes))]) | _83 -> [])`;;

let line_to_info_next = prove
 (`line_to_info (CONS (Section k1 (CONS (labLang_LabAsm a b bytes1 len1)
  xs1)) rest1) p1 (i1 + 1,l1) = line_to_info (CONS (Section k1 xs1)
  rest1) (p1 + LENGTH bytes1) (i1,l1) /\
   line_to_info (CONS (Section k2 (CONS (labLang_Asm c2 bytes2
     len2) xs2)) rest2) p2 (i2 + 1,l2) = line_to_info (CONS (Section
     k2 xs2) rest2) (p2 + LENGTH bytes2) (i2,l2)`,
  CHEAT_TAC);;

let line_to_info_hd_empty = prove
 (`line_to_info (CONS (Section k []) rest) p t =
     line_to_info rest p t`,
  CHEAT_TAC);;

let line_to_info_hd_Label = prove
 (`line_to_info (CONS (Section k (CONS (labLang_Label a b 0) xs)) rest)
     p t = line_to_info (CONS (Section k xs) rest) p t`,
  CHEAT_TAC);;

let get_shmem_info_thm = prove
 (`!secs p ffi_names' shmem_info p'.
   all_enc_ok c labs ffis p' secs ==>
   get_shmem_info secs p ffi_names' shmem_info =
     (let (new_ffis,new_info) =
       UNZIP (FLAT (
       MAP (line_to_info secs p) (
       list_of_seq (\i. (i,asm_fetch_aux i secs))
       (num_pcs secs)))) in (APPEND ffi_names' new_ffis,APPEND
         shmem_info new_info))`,
  CHEAT_TAC);;

(* [local] *)
let FILTER_NOT_MEM_Mapped = prove
 (`~(MEM "MappedRead" (FILTER (\x. ~(x = "MappedRead") /\ ~(x =
  "MappedWrite")) l)) /\
   ~(MEM "MappedWrite" (FILTER (\x. ~(x = "MappedRead") /\ ~(x =
     "MappedWrite")) l))`,
  CHEAT_TAC);;

let mmio_pcs_min_index_APPEND_thm = prove
 (`ALL (\x. !s. ~(x = ffi_ExtCall s)) l /\
   ALL (\x. ?s. x = ffi_ExtCall s) ffis ==>
   mmio_pcs_min_index (APPEND ffis l) = SOME (LENGTH ffis)`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let MEM_get_shmem_info = prove
 (cake_as_vars (fun () ->
    `all_enc_ok c labs ffis p' (code2:('a sec) list) /\
     asm_fetch_aux pc code2 = SOME (labLang_Asm (ShareMem op re a)
       inst' len) /\
     get_memop_info op = (q,(r:word8)) ==>
     MEM
       (ffi_SharedMem q,
       mk_shmem_info_num (pos_val pc p code2) r (match a with Addr
         r off -> r) (match a with Addr r off -> w2n off) re (pos_val pc
         (p + LENGTH inst') code2))
       (UNCURRY ZIP (get_shmem_info code2 p [] []))`),
  CHEAT_TAC);;

let get_shmem_info_ALL_DISTINCT = prove
 (`LENGTH (prog_to_bytes code2) < dimword (:'a) /\
   enc_ok c /\
   all_enc_ok c labs ffis p' (code2:('a sec) list) ==>
   ALL_DISTINCT (MAP (\rec. shmem_info_num_entry_pc rec) (SND
     (get_shmem_info code2 p [] [])))`,
  CHEAT_TAC);;

let get_shmem_info_EMPTY_LENGTH_EQ = prove
 (`all_enc_ok c labs ffis p' (code2:('a sec) list) ==>
   LENGTH (FST (get_shmem_info code2 p [] [])) =
     LENGTH (SND (get_shmem_info code2 p [] []))`,
  CHEAT_TAC);;

let line_to_info_offset_FST_eq = prove
 (`MAP FST (line_to_info code p accum) = MAP FST (line_to_info code 0
  accum)`,
  CHEAT_TAC);;

let line_to_info_offset_SND_eq = prove
 (`MAP SND (line_to_info code p accum) = MAP (\x.
  shmem_info_num_exit_pc_fupd (K (p + shmem_info_num_exit_pc (SND x)))
  (shmem_info_num_entry_pc_fupd (K (p + shmem_info_num_entry_pc (SND
  x))) (SND x)))
     (line_to_info code 0 accum)`,
  CHEAT_TAC);;

let get_shmem_info_init_pc_offset = prove
 (`all_enc_ok c labs ffis p' code ==>
   FST (get_shmem_info code 0 [] []) = FST (get_shmem_info code p []
     []) /\
   MAP (\rec. shmem_info_num_exit_pc_fupd (K (p +
     shmem_info_num_exit_pc rec)) (shmem_info_num_entry_pc_fupd (K (p +
     shmem_info_num_entry_pc rec)) rec)) (SND (get_shmem_info code 0 []
     [])) =
   SND (get_shmem_info code p [] [])`,
  CHEAT_TAC);;

let mmio_pcs_min_index_get_shmem_info_ok = prove
 (`all_enc_ok c labs ffis' p' (code2:('a sec) list) /\
   enc_ok c /\ ALL (\x. ?s. x = ffi_ExtCall s) ffis /\
   get_shmem_info code2 p ffis [] = (new_ffi_names,new_shmem_info)
     ==>
   mmio_pcs_min_index new_ffi_names = SOME (LENGTH ffis)`,
  CHEAT_TAC);;

let get_shmem_info_ok_lemma = prove
 (`all_enc_ok c labs ffis' p' (code2:('a sec) list) /\
   enc_ok c /\
   LENGTH (prog_to_bytes code2) < dimword (:'a) /\
   ALL (\x. ?s. x = ffi_ExtCall s) ffis /\
   get_shmem_info code2 p ffis [] = (new_ffi_names,new_shmem_info)
     ==>
   (!pc' op re a inst' len i.
     (asm_fetch_aux pc' code2 = SOME (labLang_Asm (ShareMem op re a)
       inst' len) /\
     mmio_pcs_min_index new_ffi_names = SOME i) ==>
     (?index.
       find_index (p + (pos_val pc' 0 code2)) (MAP (\rec.
         shmem_info_num_entry_pc rec) new_shmem_info) 0 =
         SOME index /\
       (let (name,nb) = get_memop_info op in
         EL (index + i) new_ffi_names = ffi_SharedMem name /\
         EL index new_shmem_info =
           mk_shmem_info_num (shmem_info_num_entry_pc (EL index
             new_shmem_info)) nb (match a with Addr r off -> r) (match a
             with Addr r off -> w2n off) re (p + (pos_val pc' 0 code2 +
             len))))) /\
   (!pc' line.
       asm_fetch_aux pc' code2 = SOME line /\
       (!op re a inst' len. ~(line = labLang_Asm (ShareMem op re a)
         inst' len)) ==>
       DISJOINT (set_of_list (MAP (\rec. shmem_info_num_entry_pc rec)
         new_shmem_info))
         {p + a + (pos_val pc' 0 code2) |
           a < LENGTH (line_bytes line)})`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let asm_fetch_NOT_ffi_entry_pcs = prove
 (cake_as_vars (fun () ->
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
       (TAKE i (machine_config_ffi_entry_pcs mc_conf)))`),
  CHEAT_TAC);;

let list_subset_refl = prove
 (`!xs.
     list_subset xs xs`,
  CHEAT_TAC);;

let list_subset_TAKE = prove
 (`!i xs.
     list_subset (TAKE i xs) xs`,
  CHEAT_TAC);;

let list_subset_trans = prove
 (`list_subset a b /\ list_subset b c ==>
   list_subset a c`,
  CHEAT_TAC);;

let genlist_line_to_info_entry_pc_max = prove
 (`all_enc_ok c labs ffis p' code2 /\ enc_ok c ==>
   ALL (\x. shmem_info_num_entry_pc (SND x) < pos_val (num_pcs code2)
     0 code2)
     (FLAT (list_of_seq
       (\i. line_to_info code2 0 (i,asm_fetch_aux i code2))
       (num_pcs code2)))`,
  CHEAT_TAC);;

(* [local] *)
let find_index_MAP_w2n = prove
 (`!l (x:'a word) n. find_index (w2n x) (MAP w2n l) n = find_index x l
  n`,
  CHEAT_TAC);;

(* This is set up for the very first compile call *)
(* [local] *)
let IMP_state_rel_make_init = prove
 (`lab_to_targetProof_good_code (target_config (machine_config_target
  mc_conf)) LN (code:('a sec) list) /\
    mc_conf_ok mc_conf /\
    (no_share_mem_inst code ==>
      compiler_oracle_ok coracle labs (LENGTH (prog_to_bytes code2))
        (target_config (machine_config_target mc_conf))
        (machine_config_ffi_names mc_conf)) /\
    list_subset (FILTER (\x. ?s. x = ffi_ExtCall s)
       (find_ffi_names code)) (TAKE i (machine_config_ffi_names
         mc_conf)) /\
    remove_labels clock (target_config (machine_config_target
      mc_conf)) 0 LN (TAKE i (machine_config_ffi_names mc_conf)) code =
       SOME (code2,labs) /\
    good_init_state mc_conf ms (prog_to_bytes code2)
       cbspace t m dm sdm /\
    get_shmem_info code2 0 [] [] = (new_ffi_names,shmem_info) /\
    new_shmem_info = MAP (\rec. shmem_info_num_exit_pc_fupd (K (w2n
      (target_get_pc (machine_config_target mc_conf) ms) +
      shmem_info_num_exit_pc rec)) (shmem_info_num_entry_pc_fupd (K (w2n
      (target_get_pc (machine_config_target mc_conf) ms) +
      shmem_info_num_entry_pc rec)) rec)) shmem_info /\
    DROP i (machine_config_ffi_names mc_conf) = new_ffi_names /\
    mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i /\
    MAP (\rec. shmem_info_num_entry_pc rec) new_shmem_info = DROP i
      (MAP w2n (machine_config_ffi_entry_pcs mc_conf)) /\
    (machine_config_mmio_info mc_conf = ZIP (list_of_seq (\index.
      index + i) (LENGTH new_shmem_info))
                              (MAP (\rec. (shmem_info_num_nbytes rec,
                              Addr (shmem_info_num_addr_reg rec) (n2w
                                (shmem_info_num_addr_off
                                rec)),shmem_info_num_reg
                              rec,n2w (shmem_info_num_exit_pc rec)))
                                new_shmem_info)) /\
    no_install_or_no_share_mem code (machine_config_ffi_names
      mc_conf) /\
    (!bn. bn < cbspace ==>
       ~(MEM (n2w bn + n2w (LENGTH (prog_to_bytes code2)) +
         target_get_pc (machine_config_target
              mc_conf) ms) (TAKE i (machine_config_ffi_entry_pcs
                mc_conf)))) ==>
    lab_to_targetProof_state_rel
      ((mc_conf:('a,'state,'b)machine_config),code2,labs,target_get_pc
      (machine_config_target
        mc_conf) ms)
      (lab_to_targetProof_make_init mc_conf (ffi:'ffi ffi_state) t m
        dm sdm ms code
       (compile_lab (target_config (machine_config_target mc_conf)))
       (target_get_pc (machine_config_target mc_conf) ms + n2w
         (LENGTH (prog_to_bytes code2))) cbspace coracle) t ms`,
  CHEAT_TAC);;

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

(* [simp] *)
let make_init_simp = prove
 (`state_ffi
     (lab_to_targetProof_make_init a b f g h i j k l m n p) = b /\ pc
     (lab_to_targetProof_make_init a b f g h i j k l m n p) = 0 /\
       state_code
     (lab_to_targetProof_make_init a b f g h i j k l m n p) = k`,
  CHEAT_TAC);;

(* HOL4 lab_to_targetProofScript.sml:10524-10538: a theorem that HOL4
   states as the value of an ML expression: semantics_make_init *)

(* HOL4 lab_to_targetProofScript.sml:10540-10552: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   make_init_filter_skip *)

(* TODO: move *)
let find_ffi_names_filter_skip = prove
 (`!code. find_ffi_names (filter_skip code) = find_ffi_names code`,
  CHEAT_TAC);;

(* [local] *)
let all_enc_ok_pre_filter_skip = prove
 (`!code c.
   (\c ls. ALL (sec_ok_pre c) ls) c code ==>
   (\c ls. ALL (sec_ok_pre c) ls) c (filter_skip code)`,
  CHEAT_TAC);;

(* [simp] *)
let MAP_Section_num_filter_skip = prove
 (`!code. MAP Section_num (filter_skip code) = MAP Section_num code`,
  CHEAT_TAC);;

(* [simp] *)
let filter_skip_extract_labels = prove
 (`!code. MAP (labProps_extract_labels o Section_lines) (filter_skip
  code) =
   MAP (labProps_extract_labels o Section_lines) code`,
  CHEAT_TAC);;

(* [simp] *)
let get_code_labels_filter_skip = prove
 (`!code. labProps_get_code_labels (filter_skip code) =
  labProps_get_code_labels code`,
  CHEAT_TAC);;

(* [simp] *)
let get_labels_filter_skip = prove
 (`!code. labProps_get_labels (filter_skip code) = labProps_get_labels
  code`,
  CHEAT_TAC);;

let implements_intro_gen = prove
 (`(b /\ ~(x = ffi_Fail) ==> y = {x}) ==> b ==> implements' T y {x}`,
  CHEAT_TAC);;

let find_ffi_names_ALL_DISTINCT = prove
 (`!code. ALL_DISTINCT (find_ffi_names code)`,
  CHEAT_TAC);;

(* [local] *)
let not_not_skip_IMP_Skip = prove
 (`~(not_skip inst') ==> (?l n. inst' = labLang_Asm (Asmi (asm_Inst
  asm_Skip)) l n)`,
  CHEAT_TAC);;

let asm_fetch_aux_filter_skip = prove
 (`!code p.
     asm_fetch_aux p (filter_skip code) = SOME inst' /\
     not_skip inst' ==>
     (?p'. asm_fetch_aux p' code = SOME inst')`,
  CHEAT_TAC);;

let IMP_asm_fetch_aux_filter_skip = prove
 (`!p code i.
     asm_fetch_aux p code = SOME i /\ not_skip i ==>
     (?p'. asm_fetch_aux p' (filter_skip code) = SOME i)`,
  CHEAT_TAC);;

let no_share_mem_filter_skip = prove
 (`no_share_mem_inst (filter_skip code) <=> no_share_mem_inst code`,
  CHEAT_TAC);;


let all_pc_adjust_pc = prove
 (`!code p.
     p < num_pcs (filter_skip code) ==>
     (?k. adjust_pc k code = p)`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let no_install_or_no_share_mem_filter_skip = prove
 (cake_as_vars (fun () ->
    `no_install_or_no_share_mem code ffi_names ==>
     no_install_or_no_share_mem (filter_skip code) ffi_names`),
  CHEAT_TAC);;
(* HOL4 lab_to_targetProofScript.sml:10827-10848: code that the
   source has in a comment *)
let asm_fetch_aux_MEM = prove
 (`MEM x l /\ ~(is_Label x) ==>
   (?p. asm_fetch_aux p [Section n l] = SOME x)`,
  CHEAT_TAC);;
(* HOL4 lab_to_targetProofScript.sml:10866-10941: code that the
   source has in a comment *)
let find_ffi_names_EVERY = prove
 (`!code ls. find_ffi_names code = ls ==> ALL (\x. ?s. x = ffi_ExtCall
  s) ls`,
  CHEAT_TAC);;

(* HOL4 lab_to_targetProofScript.sml:10953-11010: code that the
   source has in a comment *)

(* HOL4 lab_to_targetProofScript.sml:11012-11165: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   semantics_compile_lemma' *)

(* HOL4 lab_to_targetProofScript.sml:11167-11171: a theorem that HOL4
   states as the value of an ML expression: semantics_compile_lemma *)

(* try to show the condition of semantics_compile is not vacuous *)
(* HOL4 lab_to_targetProofScript.sml:11174-11199: code that the
   source has in a comment *)
(* HOL4 lab_to_targetProofScript.sml:11200-11245: code that the
   source has in a comment *)

(* HOL4 lab_to_targetProofScript.sml:11247-11303: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   semantics_compile *)

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["contain";
   "invariant";
   "not"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
