(* ======================================================== *)
(*  stack_to_labProof: ported from HOL4's
    compiler/backend/proofs/stack_to_labProofScript.sml
    A proof theory about stack_to_lab.ml, with 17 definitions, 1
    datatype and 169 theorems.  Needed by backendProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for stack_to_lab
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvl_jump.ml";;
needs "compiler/backend/bvl_to_bvi.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/labLang.ml";;
needs "compiler/backend/proofs/data_to_word_gcProof.ml";;
needs "compiler/backend/proofs/stack_allocProof.ml";;
needs "compiler/backend/proofs/stack_namesProof.ml";;
needs "compiler/backend/proofs/stack_rawcallProof.ml";;
needs "compiler/backend/proofs/stack_removeProof.ml";;
needs "compiler/backend/proofs/word_to_stackProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/labProps.ml";;
needs "compiler/backend/semantics/labSem.ml";;
needs "compiler/backend/semantics/stackProps.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_alloc.ml";;
needs "compiler/backend/stack_rawcall.ml";;
needs "compiler/backend/stack_remove.ml";;
needs "compiler/backend/stack_to_lab.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_to_stack.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/encoders/asm/asmSem.ml";;
needs "lib/alignment.ml";;
needs "lib/byte.ml";;
needs "lib/multiword.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "lib/toto.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticsProps.ml";;

cake_hide_consts
  ["code_buffer","code_buffer";
   "data_buffer","data_buffer";
   "failed","pegexec_failed"];;

(* HOL4 stack_to_labProofScript.sml:23-24: ML code, not ported *)

(* HOL4 stack_to_labProofScript.sml:26: code that the source has in a
   comment *)

(* HOL4 stack_to_labProofScript.sml:28: the overload Loc, which the
   port expands *)

(* TODO: move *)

let word_sh_word_shift = cake_theorem "word_sh_word_shift"
  (fun () ->
    `word_sh a (b:'a word) c = SOME z ==> c < dimindex (:'a) /\ z =
  word_shift a b c`)
  CHEAT_TAC;;

let assert_T = cake_theorem "assert_T[simp]"
  (fun () ->
    `assert T s = s`)
  CHEAT_TAC;;

let asm_fetch_aux_no_label = cake_theorem "asm_fetch_aux_no_label"
  (fun () ->
    `!pc' code.
     asm_fetch_aux pc' code = SOME (Label l1 l2 x) ==> F`)
  CHEAT_TAC;;

let dest_to_loc_def = cake_define
  `dest_to_loc regs' dest =
     (match dest with INL p -> p | INR r -> (match FAPPLY regs' r
       with wordLang_Loc loc _1 -> loc))`;;

let dest_to_loc'_def = cake_define
  `dest_to_loc' regs' dest =
     (match dest with INL p -> p | INR r -> (match regs' r with
       wordLang_Loc loc _2 -> loc))`;;

let find_code_lookup = cake_theorem "find_code_lookup"
  (fun () ->
    `find_code dest regs code = SOME p ==>
      lookup (dest_to_loc regs dest) code = SOME p /\
      (!r. dest = INR r ==> r IN FDOM regs)`)
  CHEAT_TAC;;

let not_is_Label_compile_jump =
  cake_theorem "not_is_Label_compile_jump[simp]"
  (fun () ->
    `is_Label (compile_jump dest) <=> F`)
  CHEAT_TAC;;

let word_cmp_not_NONE = cake_theorem "word_cmp_not_NONE[simp]"
  (fun () ->
    `~(word_cmp cmp (wordLang_Word w1) (wordLang_Word w2) = NONE)`)
  CHEAT_TAC;;

let word_cmp_negate_alt = cake_theorem "word_cmp_negate_alt[simp]"
  (fun () ->
    `asm_word_cmp (negate cmp) w1 w2 <=> ~(word_cmp cmp w1 w2)`)
  CHEAT_TAC;;

let word_cmp_negate = cake_theorem "word_cmp_negate[simp]"
  (fun () ->
    `wordSem_word_cmp (negate cmp) w1 w2 =
     OPTION_MAP (~) (wordSem_word_cmp cmp (w1) (w2))`)
  CHEAT_TAC;;

(* -- Lemmas about code_installed, loc_to_pc and asm_fetch_aux -- *)

let code_installed_def = cake_define_list
  [`stack_to_labProof_code_installed n [] code = T`;
   `stack_to_labProof_code_installed n (x :: xs) code <=>
       (if is_Label x then
         (match x with Label l1 l2 _4 -> loc_to_pc l1 l2 code = SOME
           n) /\
         stack_to_labProof_code_installed n xs code else
         asm_fetch_aux n code = SOME x /\
         stack_to_labProof_code_installed (n + 1) xs code)`];;
hol4_overload "code_installed" "stack_to_labProof_code_installed";;

let code_installed_append_imp = cake_theorem "code_installed_append_imp"
  (fun () ->
    `!l1 pc' l2 code. stack_to_labProof_code_installed pc' (l1 ++ l2)
  code ==>
     stack_to_labProof_code_installed pc' l1 code /\
     stack_to_labProof_code_installed (pc' + LENGTH (FILTER ((~)
       o is_Label) l1)) l2 code`)
  CHEAT_TAC;;

let code_installed_get_labels_IMP =
  cake_theorem "code_installed_get_labels_IMP[local]"
  (fun () ->
    `!top e n q cs bs pc'.
         stack_to_labProof_code_installed pc' (append (FST
           (stack_to_lab_flatten top e n q cs bs))) c /\
         (l1,l2) IN get_labels e ==>
         (?v. loc_to_pc l1 l2 c = SOME v)`)
  CHEAT_TAC;;

(* TODO: these may already be proved in lab_filter or lab_to_target,
         they ought to move into labProps
*)
let asm_fetch_aux_SOME_append =
  cake_theorem "asm_fetch_aux_SOME_append[local]"
  (fun () ->
    `!pc' code l code2.
     asm_fetch_aux pc' code = SOME l ==>
     asm_fetch_aux pc' (code ++ code2) = SOME l`)
  CHEAT_TAC;;

let asm_fetch_aux_SOME_isPREFIX =
  cake_theorem "asm_fetch_aux_SOME_isPREFIX[local]"
  (fun () ->
    `!pc' code l code2.
     asm_fetch_aux pc' code = SOME l /\
     code <<= code2 ==>
     asm_fetch_aux pc' code2 = SOME l`)
  CHEAT_TAC;;

let loc_to_pc_APPEND = cake_theorem "loc_to_pc_APPEND"
  (fun () ->
    `!n m code pc' code2.
     loc_to_pc n m code = SOME pc' ==>
     loc_to_pc n m (code ++ code2) = SOME pc'`)
  CHEAT_TAC;;

let code_installed_APPEND = cake_theorem "code_installed_APPEND"
  (fun () ->
    `!ls pc' code code2.
     stack_to_labProof_code_installed pc' ls code ==>
     stack_to_labProof_code_installed pc' ls (code ++ code2)`)
  CHEAT_TAC;;

let code_installed_isPREFIX = cake_theorem "code_installed_isPREFIX"
  (fun () ->
    `!ls pc' code code2.
     stack_to_labProof_code_installed pc' ls code /\
     code <<= code2 ==>
     stack_to_labProof_code_installed pc' ls code2`)
  CHEAT_TAC;;

let loc_to_pc_isPREFIX = cake_theorem "loc_to_pc_isPREFIX"
  (fun () ->
    `!n m code pc' code2.
     loc_to_pc n m code = SOME pc' /\
     code <<= code2 ==>
     loc_to_pc n m code2 = SOME pc'`)
  CHEAT_TAC;;

let MAP_prog_to_section_FST =
  cake_theorem "MAP_prog_to_section_FST[local]"
  (fun () ->
    `MAP (\s. match s with Section n v -> n) (MAP prog_to_section prog)
  =
     MAP FST prog`)
  CHEAT_TAC;;

let MAP_prog_to_section_Section_num =
  cake_theorem "MAP_prog_to_section_Section_num"
  (fun () ->
    `MAP Section_num (MAP prog_to_section prog) =
     MAP FST prog`)
  CHEAT_TAC;;

(* Appending on the other side *)
let asm_fetch_aux_SOME_append2 =
  cake_theorem "asm_fetch_aux_SOME_append2"
  (fun () ->
    `!pc' code l code2.
     asm_fetch_aux pc' code2 = SOME l ==>
     asm_fetch_aux
     (LENGTH (FLAT (MAP (FILTER ((~) o is_Label) o Section_lines)
       code)) + pc') (code ++ code2) = SOME l`)
  CHEAT_TAC;;

(* loc_to_pc on the other side *)
let loc_to_pc_append2 = cake_theorem "loc_to_pc_append2"
  (fun () ->
    `!k ll code code2 pc'.
     ~(MEM k (MAP Section_num code)) /\
     EVERY sec_labels_ok code /\
     loc_to_pc k ll code2 = SOME pc' ==>
     loc_to_pc k ll (code ++ code2) =
     SOME (pc' + (LENGTH (FLAT (MAP (FILTER ((~) o is_Label) o
       Section_lines) code))))`)
  CHEAT_TAC;;

let code_installed_append2 = cake_theorem "code_installed_append2"
  (fun () ->
    `!lines pc' c1 c2 k.
     ~(MEM k (MAP Section_num c1)) /\
     EVERY sec_labels_ok c1 /\
     EVERY (sec_label_ok k) lines /\
     stack_to_labProof_code_installed pc' lines c2 ==>
     stack_to_labProof_code_installed
     (LENGTH (FLAT (MAP (FILTER ((~) o is_Label) o Section_lines)
       c1)) + pc')
     lines (c1 ++ c2)`)
  CHEAT_TAC;;

let ALOOKUP_PARTITION = cake_theorem "ALOOKUP_PARTITION"
  (fun () ->
    `!ls n v.
     ALOOKUP ls n = SOME v ==>
     (?ls1 ls2.
     ls = ls1 ++ [(n,v)] ++ ls2 /\
     ~(MEM n (MAP FST ls1)))`)
  CHEAT_TAC;;

let code_installed'_def = cake_define_list
  [`code_installed' n [] code <=> T`;
   `code_installed' n (x :: xs) code <=>
         (if is_Label x then code_installed' n xs code else
           asm_fetch_aux n code = SOME x /\ code_installed' (n + 1)
           xs code)`];;

let code_installed'_cons_label =
  cake_theorem "code_installed'_cons_label"
  (fun () ->
    `!lines pos.
        is_Label h ==>
        code_installed' pos lines (Section n (h :: xs) :: other) =
        code_installed' pos lines (Section n xs :: other)`)
  CHEAT_TAC;;

(* HOL4 stack_to_labProofScript.sml:342-349: a theorem that HOL4
   states as the value of an ML expression:
   code_installed'_cons_non_label *)

let code_installed'_simp = cake_theorem "code_installed'_simp"
  (fun () ->
    `!lines. code_installed' 0 lines (Section n (lines ++ rest) ::
  other)`)
  CHEAT_TAC;;

let loc_to_pc_skip_section = cake_theorem "loc_to_pc_skip_section"
  (fun () ->
    `!lines. ~(n = p) ==>
        loc_to_pc n 0 (Section p lines :: xs) =
        (match loc_to_pc n 0 xs with NONE -> NONE | SOME k ->
          SOME (k + LENGTH (FILTER (\x. ~(is_Label x)) lines)))`)
  CHEAT_TAC;;

let asm_fetch_aux_add = cake_theorem "asm_fetch_aux_add"
  (fun () ->
    `!ys pc' rest.
        asm_fetch_aux (pc' + LENGTH (FILTER (\x. ~(is_Label x))
          ys)) (Section pos ys :: rest) = asm_fetch_aux pc' rest`)
  CHEAT_TAC;;

let labs_correct_def = cake_define_list
  [`labs_correct n [] code <=> T`;
   `labs_correct n (x :: xs) code <=>
         (if is_Label x then labs_correct n xs code /\
           (match x with Label l1 l2 v2 -> loc_to_pc l1 l2 code
             = SOME n | _6 -> T) else labs_correct (n + 1) xs code)`];;

(* HOL4 stack_to_labProofScript.sml:391: ML code, not ported *)

let code_installed_eq = cake_theorem "code_installed_eq"
  (fun () ->
    `!pc' xs code.
        stack_to_labProof_code_installed pc' xs code <=>
        code_installed' pc' xs code /\ labs_correct pc' xs code`)
  CHEAT_TAC;;

let stack_to_labProof_code_installed_cons =
  cake_theorem "code_installed_cons"
  (fun () ->
    `!xs ys pos pc'.
        code_installed' pc' xs rest ==>
        code_installed' (pc' + LENGTH (FILTER (\x. ~(is_Label x))
          ys)) xs
          (Section pos ys :: rest)`)
  CHEAT_TAC;;

let code_installed_prog_to_section_lemma =
  cake_theorem "code_installed_prog_to_section_lemma[local]"
  (fun () ->
    `!prog4 n prog3.
         ALOOKUP prog4 n = SOME prog3 ==>
         (?pc'.
           code_installed' pc' (append (FST (stack_to_lab_flatten T
             prog3 n (next_lab prog3 2) [] [])))
             (MAP prog_to_section prog4) /\
           loc_to_pc n 0 (MAP prog_to_section prog4) = SOME pc')`)
  CHEAT_TAC;;

(* HOL4 stack_to_labProofScript.sml:434-435: ML code, not ported *)

let labs_correct_hd = cake_theorem "labs_correct_hd"
  (fun () ->
    `!extra l.
     ALL_DISTINCT (extract_labels (extra ++ l)) /\
     EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0)) (extract_labels (extra
       ++ l)) ==>
     labs_correct (LENGTH (FILTER (\x. ~(is_Label x)) extra)) l
       (Section n (extra ++ l) :: code)`)
  CHEAT_TAC;;

let labels_ok_def = cake_define
  `labels_ok code <=>
   ALL_DISTINCT (MAP (\s. match s with Section n _7 -> n) code) /\
   EVERY (\s. match s with Section n lines ->
     (let labs = extract_labels lines in
     EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0)) labs /\
     ALL_DISTINCT labs)) code`;;

let labels_ok_imp = cake_theorem "labels_ok_imp"
  (fun () ->
    `!code.
     labels_ok code ==>
     EVERY sec_labels_ok code /\
     ALL_DISTINCT (MAP Section_num code) /\
     EVERY (ALL_DISTINCT o extract_labels o Section_lines) code`)
  CHEAT_TAC;;

let labels_ok_labs_correct = cake_theorem "labels_ok_labs_correct"
  (fun () ->
    `!code.
     labels_ok code ==>
     EVERY (\s. match s with Section n lines ->
       (match loc_to_pc n 0 code with
        SOME pc' -> labs_correct pc' lines code | _8 -> T)) code`)
  CHEAT_TAC;;

let labs_correct_append = cake_theorem "labs_correct_append"
  (fun () ->
    `!ls pc'.
     labs_correct pc' (ls ++ rest) code ==>
     labs_correct pc' ls code`)
  CHEAT_TAC;;

let code_installed_prog_to_section =
  cake_theorem "code_installed_prog_to_section"
  (fun () ->
    `!prog4 n prog3.
        labels_ok (MAP prog_to_section prog4) /\
        ALOOKUP prog4 n = SOME prog3 ==>
        (?pc'.
          stack_to_labProof_code_installed pc' (append (FST
            (stack_to_lab_flatten T prog3 n (next_lab prog3 2) [] [])))
            (MAP prog_to_section prog4) /\
          loc_to_pc n 0 (MAP prog_to_section prog4) = SOME pc')`)
  CHEAT_TAC;;

(* -- End code_installed lemmas  -- *)

let state_rel_def = cake_define
  `stack_to_labProof_state_rel (s:('a,'c,'ffi)stackSem_state)
  (t:('a,'c,'ffi)labSem_state) <=>
     (!n v. FLOOKUP (stackSem_state_regs s) n = SOME v ==>
       labSem_state_regs t n = v) /\
     (!n v. FLOOKUP (stackSem_state_fp_regs s) n = SOME v ==>
       labSem_state_fp_regs t n = v) /\ labSem_state_mem
     t = stackSem_state_memory s /\ labSem_state_mem_domain
     t = stackSem_state_mdomain s /\ labSem_state_shared_mem_domain
     t = stackSem_state_sh_mdomain s /\ labSem_state_be
     t = stackSem_state_be s /\ labSem_state_ffi
     t = stackSem_state_ffi s /\ labSem_state_clock
     t = stackSem_state_clock s /\
     (!n prog. lookup n (stackSem_state_code s) = SOME prog ==>
       call_args prog (labSem_state_ptr_reg t) (labSem_state_len_reg
         t) (labSem_state_ptr2_reg t) (labSem_state_len2_reg t)
         (labSem_state_link_reg t) /\
       (?pc'. stack_to_labProof_code_installed pc'
              (append (FST (stack_to_lab_flatten T prog n (next_lab
                prog 2) [] []))) (labSem_state_code t) /\
            loc_to_pc n 0 (labSem_state_code t) = SOME pc')) /\
     domain (stackSem_state_code s) = set_of_list (MAP Section_num
       (labSem_state_code t)) /\
     EVERY sec_labels_ok (labSem_state_code t) /\
     ~(labSem_state_failed t) /\ ~(labSem_state_link_reg
     t = labSem_state_len_reg t) /\ ~(labSem_state_link_reg t =
       labSem_state_ptr_reg t) /\ ~(labSem_state_link_reg
     t = labSem_state_len2_reg t) /\ ~(labSem_state_link_reg t =
       labSem_state_ptr2_reg t) /\
     ~(labSem_state_link_reg t IN stackSem_state_ffi_save_regs s) /\
     (!k i n. k IN stackSem_state_ffi_save_regs s ==>
       labSem_state_io_regs t n i k = NONE) /\
     (!k n. k IN stackSem_state_ffi_save_regs s ==>
       labSem_state_cc_regs t n k = NONE) /\
     (!x. x IN stackSem_state_mdomain s ==> w2n x MOD (dimindex (:'a)
       DIV 8) = 0) /\
     (!x. x IN stackSem_state_sh_mdomain s ==> w2n x MOD (dimindex
       (:'a) DIV 8) = 0) /\ stackSem_state_code_buffer
     s = labSem_state_code_buffer t /\ stackSem_state_compile
     s = (\c p. labSem_state_compile t c (MAP prog_to_section p)) /\
     (labSem_state_compile_oracle t = (\n. let (c,p,_9) =
       stackSem_state_compile_oracle s n in
                            (c,MAP prog_to_section p))) /\
     (!k. let (c,ps,_10) = stackSem_state_compile_oracle s k in
       EVERY (\(n,p).
         call_args p (labSem_state_ptr_reg t) (labSem_state_len_reg
           t) (labSem_state_ptr2_reg t) (labSem_state_len2_reg t)
           (labSem_state_link_reg t) /\
         EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
           (extract_labels p) /\
         ALL_DISTINCT (extract_labels p)) ps /\
         ALL_DISTINCT (MAP FST ps)) /\
     ~(stackSem_state_use_stack s) /\
     ~(stackSem_state_use_store s) /\
     ~(stackSem_state_use_alloc s) /\
     good_dimindex (:'a)`;;
hol4_overload "state_rel" "stack_to_labProof_state_rel";;

let loc_check_IMP_loc_to_pc = cake_theorem "loc_check_IMP_loc_to_pc"
  (fun () ->
    `loc_check (stackSem_state_code s) (l1,l2) /\ state_rel s t1 ==>
      (?v. loc_to_pc l1 l2 (labSem_state_code t1) = SOME v)`)
  CHEAT_TAC;;

let stack_to_labProof_state_rel_dec_clock =
  cake_theorem "state_rel_dec_clock"
  (fun () ->
    `state_rel s t ==> state_rel (dec_clock s) (dec_clock t)`)
  CHEAT_TAC;;

let state_rel_with_pc = cake_theorem "state_rel_with_pc"
  (fun () ->
    `state_rel s t ==> state_rel s (upd_pc pc t)`)
  CHEAT_TAC;;

let stack_to_labProof_state_rel_with_clock =
  cake_theorem "state_rel_with_clock"
  (fun () ->
    `state_rel s t ==> state_rel (stackSem_state_clock_fupd (K k) s)
  (labSem_state_clock_fupd (K k) t)`)
  CHEAT_TAC;;

let set_var_upd_reg = cake_theorem "set_var_upd_reg"
  (fun () ->
    `state_rel s t ==>
     state_rel (set_var a b s) (upd_reg a b t)`)
  CHEAT_TAC;;

let set_var_Word_upd_reg = cake_theorem "set_var_Word_upd_reg[simp]"
  (fun () ->
    `state_rel s t ==>
     state_rel (set_var a (wordLang_Word b) s) (upd_reg a
       (wordLang_Word b) t)`)
  CHEAT_TAC;;

let set_fp_var_upd_fp_reg = cake_theorem "set_fp_var_upd_fp_reg"
  (fun () ->
    `state_rel s t ==>
     state_rel (set_fp_var a b s) (upd_fp_reg a b t)`)
  CHEAT_TAC;;

let mem_store_upd_mem = cake_theorem "mem_store_upd_mem"
  (fun () ->
    `state_rel s t /\ mem_store x y s = SOME s1 ==>
     state_rel s1 (upd_mem x y t)`)
  CHEAT_TAC;;

let state_rel_read_reg_FLOOKUP_regs =
  cake_theorem "state_rel_read_reg_FLOOKUP_regs"
  (fun () ->
    `state_rel s t /\
     FLOOKUP (stackSem_state_regs s) x = SOME y ==>
     y = labSem_state_regs t x`)
  CHEAT_TAC;;

let state_rel_read_fp_reg_FLOOKUP_fp_regs =
  cake_theorem "state_rel_read_fp_reg_FLOOKUP_fp_regs"
  (fun () ->
    `state_rel s t /\
     get_fp_var n s = SOME x ==>
     x = read_fp_reg n t`)
  CHEAT_TAC;;

let state_rel_get_var_imm = cake_theorem "state_rel_get_var_imm"
  (fun () ->
    `state_rel s t /\
     get_var_imm r s = SOME x ==>
     reg_imm r t = x`)
  CHEAT_TAC;;

let stack_to_labProof_inst_correct = cake_theorem "inst_correct"
  (fun () ->
    `inst i s1 = SOME s2 /\
     state_rel s1 t1 ==>
     state_rel s2 (asm_inst i t1)`)
  CHEAT_TAC;;

let flatten_leq = cake_theorem "flatten_leq"
  (fun () ->
    `!t x y z cs bs. z <= SND (SND (stack_to_lab_flatten t x y z cs
  bs))`)
  CHEAT_TAC;;

let NOT_bad_fun_return_IMP_SOME =
  cake_theorem "NOT_bad_fun_return_IMP_SOME[local]"
  (fun () ->
    `~(bad_fun_return q) ==> (?n. q = SOME n)`)
  CHEAT_TAC;;

let no_ret_correct = cake_theorem "no_ret_correct"
  (fun () ->
    `!t p y z cs bs. FST (SND (stack_to_lab_flatten t p y z cs bs))
  ==> (!s. IS_SOME (FST (evaluate (p,s))))`)
  CHEAT_TAC;;

(* HOL4 stack_to_labProofScript.sml:926: the ML values that the
   definitions below antiquote *)

let compile_jump_correct = cake_theorem "compile_jump_correct"
  (fun () ->
    `asm_fetch_aux pc code = SOME (compile_jump dest) /\
     loc_to_pc (dest_to_loc' regs dest) 0 code = SOME pc' /\
     (!r. dest = INR r ==> (?p. labSem_state_regs s r =
       wordLang_Loc p 0)) /\ labSem_state_pc
     (s:('a,'c,'ffi)labSem_state) = pc /\ labSem_state_code s =
       code /\ labSem_state_regs s = regs /\ ~(labSem_state_clock s = 0)
       ==>
     evaluate s = evaluate (upd_pc pc' (dec_clock s))`)
  CHEAT_TAC;;

let result_view_INDUCT,result_view_RECURSION = define_datatype
  "result_view = Vloc (num) (num) | Vcont (num) (num) | Vtimeout | \
   Verr";;

let result_view_def = cake_define
  `result_view x1 l cs bs =
        match x1 with
          stackSem_Result (wordLang_Loc n1 n2) -> Vloc n1 n2
        | (Exception (wordLang_Loc n1 n2)) -> Vloc n1 n2
        | TimeOut -> Vtimeout
        | (Continue n) -> Vcont l (find_lab n cs)
        | (Break n) -> Vloc l (find_lab n bs)
        | _11 -> Verr`;;

let halt_word_view_def = cake_define
  `halt_word_view x1 =
        match x1 with
          wordLang_Word (n2w 0) -> Halt ffi_Success
        | (wordLang_Word _12) -> Halt ffi_Resource_limit_hit
        | _13 -> Error`;;

let halt_view_def = cake_define
  `halt_view x1 =
        match x1 with
          SOME (Halt w) -> SOME (halt_word_view w)
        | (SOME (FinalFFI outcome)) -> SOME (Halt (ffi_FFI_outcome
          outcome))
        | _14 -> NONE`;;

(* HOL4 stack_to_labProofScript.sml:966-1017: a proof *)

(* Proving that stack_to_lab generates labels_ok *)
(* HOL4 stack_to_labProofScript.sml:1020: ML code, not ported *)

let next_lab_non_zero = cake_theorem "next_lab_non_zero"
  (fun () ->
    `!p. 2 <= next_lab p 2`)
  CHEAT_TAC;;

let stack_to_lab_lab_pres = cake_theorem "stack_to_lab_lab_pres"
  (fun () ->
    `!t p n nl cs bs.
       EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
         (extract_labels p) /\
       ALL_DISTINCT (extract_labels p) /\ ~t /\
       next_lab p 2 <= nl ==>
       (let (cp,nr,nl') = stack_to_lab_flatten t p n nl cs bs in
         EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
           (extract_labels (append cp)) /\
         ALL_DISTINCT (extract_labels (append cp)) /\
         (!lab. MEM lab (extract_labels (append cp)) ==> MEM lab
           (extract_labels p) \/
                              (nl <= SND lab /\ SND lab < nl')) /\
         nl <= nl')`)
  CHEAT_TAC;;

let stack_to_lab_lab_pres_T = cake_theorem "stack_to_lab_lab_pres_T"
  (fun () ->
    `!t p n nl cs bs.
     EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
       (extract_labels p) /\
     ALL_DISTINCT (extract_labels p) /\ t /\
     next_lab p 2 <= nl ==>
     (let (cp,nr,nl') = stack_to_lab_flatten t p n nl cs bs in
     EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0)) (extract_labels (append
       cp)) /\
     ALL_DISTINCT (extract_labels (append cp)) /\
     (!lab. MEM lab (extract_labels (append cp)) ==>
          MEM lab (extract_labels p) \/ SND lab < nl') /\
     nl <= nl')`)
  CHEAT_TAC;;

let flatten_T_F = cake_theorem "flatten_T_F"
  (fun () ->
    `~(is_Seq p_2) ==>
     stack_to_lab_flatten T p_2 p_1 m cs bs =
       stack_to_lab_flatten F p_2 p_1 m cs bs`)
  CHEAT_TAC;;

let prog_to_section_labels_ok = cake_theorem "prog_to_section_labels_ok"
  (fun () ->
    `EVERY (\(n,p).
              let labs = extract_labels p in
                EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
                  labs /\
                ALL_DISTINCT labs) prog /\
     ALL_DISTINCT (MAP FST prog) ==>
     labels_ok (MAP prog_to_section prog)`)
  CHEAT_TAC;;

let NOT_MEM_find_lab_IMP = cake_theorem "NOT_MEM_find_lab_IMP"
  (fun () ->
    `!bs n. ~(MEM (find_lab n bs) bs) ==> find_lab n bs = 0`)
  CHEAT_TAC;;

let is_some_loc_to_pc_prefix = cake_theorem "is_some_loc_to_pc_prefix"
  (fun () ->
    `IS_SOME (loc_to_pc n k c1) /\ c1 <<= c2 ==>
     IS_SOME (loc_to_pc n k c2)`)
  CHEAT_TAC;;

let every_is_some_loc_to_pc_prefix =
  cake_theorem "every_is_some_loc_to_pc_prefix"
  (fun () ->
    `EVERY (\k. IS_SOME (loc_to_pc n k c1)) cs /\ c1 <<= c2 ==>
     EVERY (\k. IS_SOME (loc_to_pc n k c2)) cs`)
  CHEAT_TAC;;

let flatten_correct = cake_theorem "flatten_correct"
  (fun () ->
    `!prog s1 t r s2 n l cs bs (t1:('a,'c,'ffi)labSem_state).
       evaluate (prog,s1) = (r,s2) /\ ~(r = SOME Error) /\
       state_rel s1 t1 /\
       call_args prog (labSem_state_ptr_reg t1)
         (labSem_state_len_reg t1) (labSem_state_ptr2_reg t1)
         (labSem_state_len2_reg t1) (labSem_state_link_reg t1) /\
       stack_to_labProof_code_installed (labSem_state_pc t1)
         (append (FST (stack_to_lab_flatten t prog n l cs bs)))
         (labSem_state_code t1) /\
       EVERY (\k. IS_SOME (loc_to_pc n k (labSem_state_code t1)))
         (cs ++ bs ++ [0]) ==>
       (?ck t2.
       match halt_view r with SOME res ->
         evaluate (labSem_state_clock_fupd (K (labSem_state_clock
           t1 + ck)) t1) =
           (res,t2) /\ labSem_state_ffi t2 = state_ffi s2 | NONE ->
         (!ck1. evaluate (labSem_state_clock_fupd (K
           (labSem_state_clock t1 + ck + ck1)) t1) =
           evaluate (labSem_state_clock_fupd (K (labSem_state_clock
             t2 + ck1)) t2)) /\ labSem_state_len_reg
         t2 = labSem_state_len_reg t1 /\ labSem_state_ptr_reg
         t2 = labSem_state_ptr_reg t1 /\ labSem_state_len2_reg
         t2 = labSem_state_len2_reg t1 /\ labSem_state_ptr2_reg
         t2 = labSem_state_ptr2_reg t1 /\ labSem_state_link_reg
         t2 = labSem_state_link_reg t1 /\ labSem_state_code
         t1 <<= labSem_state_code t2 /\
         (match OPTION_MAP (\w. result_view w n cs bs) r with NONE
           -> labSem_state_pc
           t2 = labSem_state_pc t1 + LENGTH (FILTER ((~) o
             is_Label)
                             (append (FST (stack_to_lab_flatten t
                               prog n l cs bs)))) /\
           state_rel s2 t2 | SOME (Vloc n1 n2) ->
             (!n. IS_SOME (lookup n (state_code s2)) ==> IS_SOME
               (loc_to_pc n 0 (labSem_state_code t2))) /\
             (!w. loc_to_pc n1 n2 (labSem_state_code t2) = SOME w
               ==>
                 w = labSem_state_pc t2 /\
                 state_rel s2 t2) | SOME (Vcont n1 n2) ->
             state_rel s2 t2 /\
             stack_to_labProof_code_installed (labSem_state_pc
               t2) [labLang_LabAsm (Jump (labLang_Lab n1 n2)) (n2w 0)
               [] 0] (labSem_state_code t2) | SOME Vtimeout ->
               labSem_state_ffi t2 = state_ffi s2 /\
               labSem_state_clock t2 = 0 | _15 -> F))`)
  CHEAT_TAC;;

let flatten_call_correct = cake_theorem "flatten_call_correct"
  (fun () ->
    `evaluate (Call NONE (INL start) NONE,s1) = (res,s2) /\
     state_rel (s1:('a,'c,'ffi)stackSem_state) t1 /\
     loc_to_pc start 0 (labSem_state_code t1) = SOME
       (labSem_state_pc t1) /\ ~(res = SOME Error) /\
     (~(res = SOME TimeOut) ==>
       (?w. res = SOME (Halt (wordLang_Word w))) \/
       (?f. res = SOME (FinalFFI f)) \/
       (?n. res = SOME (Result (wordLang_Loc n 0)) /\
         (!(s:('a,'c,'ffi)stackSem_state). subspt
           (stackSem_state_code s1) (stackSem_state_code s) /\
           ~(stackSem_state_clock s = 0) ==>
             (?t. evaluate (Call NONE (INL n) NONE,s) = (SOME (Halt
               (wordLang_Word (n2w 0))),t) /\ stackSem_state_ffi
                 t = stackSem_state_ffi s /\ stackSem_state_clock t
                   = stackSem_state_clock s - 1)))) ==>
     (?ck r2 t2.
       evaluate (labSem_state_clock_fupd (K (labSem_state_clock t1
         - 1 + ck)) (t1:('a,'c,'ffi)labSem_state)) = (r2,t2) /\
       (!f. res = SOME (FinalFFI f) ==> r2 = Halt (ffi_FFI_outcome
         f)) /\
       (!w. res = SOME (Halt w) ==> r2 =
        (match w with wordLang_Word (n2w 0) -> Halt ffi_Success |
          wordLang_Word _16 -> Halt ffi_Resource_limit_hit | _17 ->
          Error)) /\
       (!n. res = SOME (Result (wordLang_Loc n 0)) ==> r2 = Halt
         ffi_Success) /\ labSem_state_ffi
       t2 = state_ffi s2 /\ ~(r2 = Error) /\ (res = SOME TimeOut
         ==> r2 = TimeOut))`)
  CHEAT_TAC;;

let halt_assum_def = cake_define
  `halt_assum (:'ffi#'c) code <=>
    (!(s:('a,'c,'ffi)stackSem_state).
      subspt code (stackSem_state_code s) /\ ~(stackSem_state_clock s
        = 0) ==>
      (?t. evaluate (Call NONE (INL 1) NONE,s) = (SOME (Halt
        (wordLang_Word (n2w 0))),t) /\ stackSem_state_ffi
          t = stackSem_state_ffi s /\ stackSem_state_clock t =
            stackSem_state_clock s - 1))`;;

let flatten_semantics = cake_theorem "flatten_semantics"
  (fun () ->
    `halt_assum (:'ffi#'c) (stackSem_state_code
  (s1:('a,'c,'ffi)stackSem_state)) /\
     state_rel s1 (s2:('a,'c,'ffi)labSem_state) /\
     loc_to_pc start 0 (labSem_state_code s2) = SOME
       (labSem_state_pc s2) /\ ~(semantics start s1 = Fail) ==>
     semantics s2 = semantics start s1`)
  CHEAT_TAC;;

let make_init_def = cake_define
  `stack_to_labProof_make_init code coracle regs' save_regs
  (s:('a,'c,'ffi)labSem_state) =
     (mk_stackSem_state (FEMPTY |++ (MAP (\r. r,(\r s.
       labSem_state_regs s r) r s) regs')) FEMPTY ARB ARB ARB
       (labSem_state_mem s) (labSem_state_mem_domain s)
       (labSem_state_shared_mem_domain s) ARB (\c p.
       labSem_state_compile s c (MAP prog_to_section p)) coracle
       (labSem_state_code_buffer s) ARB ARB F F F (labSem_state_clock
       s) code (labSem_state_ffi s) save_regs (labSem_state_be
       s):('a,'c,'ffi)stackSem_state)`;;
hol4_overload "make_init" "stack_to_labProof_make_init";;

(* HOL4 stack_to_labProofScript.sml:3047-3049: ML code, not ported *)

(* HOL4 stack_to_labProofScript.sml:3051: the overload
   stack_to_lab_compile, which the port expands *)
(* HOL4 stack_to_labProofScript.sml:3052: the overload
   stack_names_compile, which the port expands *)
(* HOL4 stack_to_labProofScript.sml:3053: the overload
   stack_alloc_compile, which the port expands *)
(* HOL4 stack_to_labProofScript.sml:3054: the overload
   stack_remove_compile, which the port expands *)

let full_make_init_def = cake_define
  `full_make_init stack_conf data_conf max_heap sp offset bitmaps code
  s4 save_regs data_sp coracle =
   (let ggc = is_gen_gc (data_to_word_config_gc_kind data_conf) in
   let jump = stack_to_lab_config_jump stack_conf in
   let code1 = stack_alloc_compile data_conf (stack_rawcall_compile
     code) in
   let code2 = compile jump offset ggc max_heap sp
     InitGlobals_location code1 in
   let code3 = fromAList (compile (stack_to_lab_config_reg_names
     stack_conf) code2) in
   let coracle1 = (I ## MAP prog_comp ## I) o coracle in
   let coracle2 = (I ## MAP (prog_comp jump offset sp) ## I) o
     coracle1 in
   let coracle3 = (I ## compile (stack_to_lab_config_reg_names
     stack_conf) ## I) o coracle2 in
   let s3 = make_init code3 coracle3 (MAP (tlookup
     (stack_to_lab_config_reg_names stack_conf)) [2; 3; 4]) save_regs s4
     in
   let s2 = make_init (stack_to_lab_config_reg_names stack_conf)
     (fromAList code2) coracle2 s3 in
   let s1 = make_init_any ggc max_heap bitmaps data_sp coracle1 jump
     offset sp (fromAList code1) s2 in
     (make_init data_conf (fromAList code) coracle s1,
      make_init_opt ggc max_heap bitmaps data_sp coracle1 jump
        offset sp (fromAList code1) s2))`;;

let full_make_init_buffer = cake_theorem "full_make_init_buffer"
  (fun () ->
    `buffer_buffer (state_code_buffer
         (FST (full_make_init a b c d e f g h i j k))) = [] /\
           buffer_buffer (state_data_buffer
       (FST (full_make_init a b c d e f g h i j k))) = []`)
  CHEAT_TAC;;

let full_make_init_ffi = cake_theorem "full_make_init_ffi"
  (fun () ->
    `state_ffi
         (FST (full_make_init a b c d e f g h i j k)) = state_ffi
           h`)
  CHEAT_TAC;;

let full_make_init_compile = cake_theorem "full_make_init_compile"
  (fun () ->
    `compile
        (FST (full_make_init a b c d e f g h i j k)) =
        (\c. (\p. compile h c (MAP prog_to_section (MAP
          (prog_comp (stack_to_lab_config_reg_names a)) (MAP
          (prog_comp (stack_to_lab_config_jump a) e d) p)))) o MAP
          prog_comp)`)
  CHEAT_TAC;;

let memory_assumption_def = cake_define
  `memory_assumption rnames (bitmaps:('a word) list) data_sp t =
     (?ptr2 ptr3 ptr4 bitmap_ptr.
       (\r s. labSem_state_regs s r) (tlookup rnames 2) t =
         wordLang_Word ptr2 /\
       (\r s. labSem_state_regs s r) (tlookup rnames 3) t =
         wordLang_Word ptr3 /\
       (\r s. labSem_state_regs s r) (tlookup rnames 4) t =
         wordLang_Word ptr4 /\ labSem_state_mem
       t ptr2 = wordLang_Word bitmap_ptr /\ labSem_state_mem
       t (ptr2 + bytes_in_word) =
           wordLang_Word (bitmap_ptr + bytes_in_word * n2w (LENGTH
             bitmaps)) /\ labSem_state_mem
       t (ptr2 + (n2w 2) * bytes_in_word) =
           wordLang_Word (bitmap_ptr + bytes_in_word * n2w data_sp +
                 bytes_in_word * n2w (LENGTH bitmaps)) /\
                   labSem_state_mem
       t (ptr2 + (n2w 3) * bytes_in_word) = wordLang_Word
         (buffer_position (labSem_state_code_buffer t)) /\
         labSem_state_mem
       t (ptr2 + (n2w 4) * bytes_in_word) =
           wordLang_Word (buffer_position (labSem_state_code_buffer
             t) + n2w (buffer_space_left (labSem_state_code_buffer t)))
             /\ buffer_buffer (labSem_state_code_buffer
       t) = [] /\
       ptr2 <=+ ptr4 /\ byte_aligned ptr2 /\
       byte_aligned ptr4 /\ byte_aligned bitmap_ptr /\
       (n2w 1024) * bytes_in_word <=+ ptr4 - ptr2 /\
      (word_list bitmap_ptr (MAP wordLang_Word bitmaps) *
       word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH
         bitmaps)) data_sp *
       word_list_exists ptr2
         (w2n (--(n2w 1) * ptr2 + ptr4) DIV w2n (bytes_in_word:'a
           word)))
        (fun2set (labSem_state_mem t,labSem_state_mem_domain t)))`;;

let halt_assum_lemma = cake_theorem "halt_assum_lemma[local]"
  (fun () ->
    `halt_assum (:'ffi#'c)
        (fromAList (stack_names_compile f
          (compile jump off gen max_heap k l code)))`)
  CHEAT_TAC;;

let FLOOKUP_regs = cake_theorem "FLOOKUP_regs[local]"
  (fun () ->
    `!regs' n v f s.
         FLOOKUP (FEMPTY |++ MAP (\r. (r,labSem_state_regs s r))
           regs') n = SOME v ==> labSem_state_regs s n = v`)
  CHEAT_TAC;;

let state_rel_make_init = cake_theorem "state_rel_make_init"
  (fun () ->
    `state_rel (make_init code coracle regs save_regs s)
  (s:('a,'c,'ffi)labSem_state) <=>
      (!n prog.
       lookup n code = SOME (prog) ==>
       call_args prog (labSem_state_ptr_reg s)
         (labSem_state_len_reg s) (labSem_state_ptr2_reg s)
         (labSem_state_len2_reg s) (labSem_state_link_reg s) /\
       (?pc'.
         stack_to_labProof_code_installed pc' (append (FST
           (stack_to_lab_flatten T prog n (next_lab prog 2) [] [])))
           (labSem_state_code s) /\
         loc_to_pc n 0 (labSem_state_code s) = SOME pc')) /\
           ~(labSem_state_failed s) /\ labSem_state_compile_oracle
      s = (\n. (\(c,p,_18). (c,MAP prog_to_section p)) (coracle n))
        /\
      (!k.
        (\(c,ps,_19).
           EVERY
             (\(n,p).
                call_args p (labSem_state_ptr_reg s)
                  (labSem_state_len_reg s) (labSem_state_ptr2_reg s)
                  (labSem_state_len2_reg s) (labSem_state_link_reg s) /\
                EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
                  (extract_labels p) /\
                ALL_DISTINCT (extract_labels p)) ps /\
           ALL_DISTINCT (MAP FST ps)) (coracle k)) /\
             ~(labSem_state_link_reg
      s = labSem_state_len_reg s) /\ ~(labSem_state_link_reg s =
        labSem_state_ptr_reg s) /\ ~(labSem_state_link_reg
      s = labSem_state_len2_reg s) /\ ~(labSem_state_link_reg s =
        labSem_state_ptr2_reg s) /\ ~(labSem_state_link_reg
      s IN save_regs) /\
      domain code = set_of_list (MAP Section_num (labSem_state_code
        s)) /\
      EVERY sec_labels_ok (labSem_state_code s) /\
      (!k i n. k IN save_regs ==> labSem_state_io_regs s n i k =
        NONE) /\
      (!k n. k IN save_regs ==> labSem_state_cc_regs s n k = NONE)
        /\
      (!x. x IN labSem_state_mem_domain s ==> w2n x MOD (dimindex
        (:'a) DIV 8) = 0) /\
      (!x. x IN labSem_state_shared_mem_domain s ==> w2n x MOD
        (dimindex (:'a) DIV 8) = 0) /\
      good_dimindex (:'a)`)
  CHEAT_TAC;;

let MAP_FST_compile_compile =
  cake_theorem "MAP_FST_compile_compile[local]"
  (fun () ->
    `MAP FST (compile jump off gen max_heap k InitGlobals_location
                 (stack_alloc_compile c
                    (stack_rawcall_compile code))) =
       0 :: 1 :: 2 :: gc_stub_location :: MAP FST code`)
  CHEAT_TAC;;

(* HOL4 stack_to_labProofScript.sml:3209: ML code, not ported *)

let stack_to_labProof_next_lab_non_zero =
  cake_theorem "next_lab_non_zero[allow_rebind]"
  (fun () ->
    `!p. 1 <= next_lab p 1 /\
         2 <= next_lab p 2`)
  CHEAT_TAC;;

(* HOL4 stack_to_labProofScript.sml:3218-3270: code that the source
   has in a comment *)

let stack_to_labProof_MAP_prog_to_section_FST =
  cake_theorem "MAP_prog_to_section_FST[local]"
  (fun () ->
    `MAP (\s. match s with Section n v -> n) (MAP prog_to_section prog)
  =
     MAP FST prog`)
  CHEAT_TAC;;

let extract_label_store_list_code =
  cake_theorem "extract_label_store_list_code[local]"
  (fun () ->
    `!a t ls.
     extract_labels (store_list_code a t ls) = []`)
  CHEAT_TAC;;

let stack_to_lab_compile_lab_pres =
  cake_theorem "stack_to_lab_compile_lab_pres"
  (fun () ->
    `EVERY (\n. ~(n = 0) /\ ~(n = 1) /\ ~(n = 2) /\ ~(n =
  gc_stub_location)) (MAP FST prog) /\
     EVERY (\(n,p).
              let labs = extract_labels p in
                EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
                  labs /\
                ALL_DISTINCT labs) prog /\
     ALL_DISTINCT (MAP FST prog) ==>
     labels_ok (compile c c2 c3 sp offset prog)`)
  CHEAT_TAC;;

let good_code_def = cake_define
  `stack_to_labProof_good_code sp code <=>
    ALL_DISTINCT (MAP FST code) /\
    EVERY (\(k,prog). stack_num_stubs <= k /\ alloc_arg prog) code /\
    EVERY (\p. call_args p 1 2 3 4 0) (MAP SND code) /\
    EVERY (\p. reg_bound p sp) (MAP SND code) /\
    EVERY
    (\(n,p).
       EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
         (extract_labels p) /\
       ALL_DISTINCT (extract_labels p)) code`;;
hol4_overload "good_code" "stack_to_labProof_good_code";;

let contain_def = cake_define
  `contain b = Abbrev b`;;

let full_make_init_semantics = cake_theorem "full_make_init_semantics"
  (fun () ->
    `full_make_init stack_conf data_conf max_heap sp offset
      (bitmaps:('a word) list) code t save_regs data_sp coracle =
        (s,opt) /\
     good_dimindex (:'a) /\ labSem_state_code
     t = stack_to_lab_compile stack_conf data_conf max_heap sp
       offset code /\ labSem_state_compile_oracle
     t = (\n.
       let (c,p,b) = coracle n in
         (c,compile_no_stubs (stack_to_lab_config_reg_names
           stack_conf) (stack_to_lab_config_jump stack_conf) offset sp
           p)) /\
     ~(labSem_state_failed t) /\
     memory_assumption (stack_to_lab_config_reg_names stack_conf)
       bitmaps data_sp t /\
     max_stack_alloc <= max_heap /\ ~(labSem_state_link_reg
     t IN save_regs) /\ labSem_state_pc t = 0 /\
     (!k i n. k IN save_regs ==> labSem_state_io_regs t n i k =
       NONE) /\
     (!k n. k IN save_regs ==> labSem_state_cc_regs t n k = NONE)
       /\
     (!x. x IN labSem_state_mem_domain t ==> w2n x MOD (dimindex
       (:'a) DIV 8) = 0) /\
     (!x. x IN labSem_state_shared_mem_domain t ==> w2n x MOD
       (dimindex (:'a) DIV 8) = 0) /\
     good_code sp code /\
     (!n. good_code sp (FST (SND (coracle n)))) /\
     10 <= sp /\
     EVERY (\r. (tlookup (stack_to_lab_config_reg_names stack_conf)
       ((r + sp) - 2)) IN save_regs) [2; 3; 4] /\
     tlookup (stack_to_lab_config_reg_names stack_conf) 4 =
       labSem_state_len2_reg t /\
     tlookup (stack_to_lab_config_reg_names stack_conf) 3 =
       labSem_state_ptr2_reg t /\
     tlookup (stack_to_lab_config_reg_names stack_conf) 2 =
       labSem_state_len_reg t /\
     tlookup (stack_to_lab_config_reg_names stack_conf) 1 =
       labSem_state_ptr_reg t /\
     tlookup (stack_to_lab_config_reg_names stack_conf) 0 =
       labSem_state_link_reg t /\
     BIJ (tlookup (stack_to_lab_config_reg_names stack_conf)) UNIV
       UNIV ==>
     Abbrev (~(opt = NONE) /\ (~(semantics InitGlobals_location s =
       Fail) ==>
     semantics t = semantics InitGlobals_location s))`)
  CHEAT_TAC;;

(* HOL4 stack_to_labProofScript.sml:3617-3618: a theorem that HOL4
   states as the value of an ML expression: full_make_init_semantics *)

let EVERY_sec_ends_with_label_MAP_prog_to_section =
  cake_theorem "EVERY_sec_ends_with_label_MAP_prog_to_section[simp]"
  (fun () ->
    `!prog. EVERY sec_ends_with_label (MAP prog_to_section prog)`)
  CHEAT_TAC;;

(* HOL4 stack_to_labProofScript.sml:3627: ML code, not ported *)

let flatten_line_ok_pre = cake_theorem "flatten_line_ok_pre[local]"
  (fun () ->
    `!t p n m cs bs ls a b c.
     asm_offset_ok 0 (asm_config_byte_offset c) (n2w 0) /\
     stack_asm_ok c p /\
     stack_to_lab_flatten t p n m cs bs = (ls,a,b) ==>
     EVERY (line_ok_pre c) (append ls)`)
  CHEAT_TAC;;

let compile_all_enc_ok_pre = cake_theorem "compile_all_enc_ok_pre"
  (fun () ->
    `asm_offset_ok 0 (asm_config_byte_offset c) (n2w 0) /\
     EVERY (\(n,p). stack_asm_ok c p) prog ==>
     (\c ls. EVERY (sec_ok_pre c) ls) c (MAP prog_to_section
       prog)`)
  CHEAT_TAC;;

(* stack_name renames registers to obey non-clashing names
  It should be sufficient that the incoming nregs < reg_count - avoid_regs,
  and that the mapping target for these avoids bad regs
*)

let stack_to_lab_compile_all_enc_ok =
  cake_theorem "stack_to_lab_compile_all_enc_ok"
  (fun () ->
    `EVERY (\(n,p). stack_asm_name c p) prog /\
     EVERY (\(n,p). stack_asm_remove c p) prog /\
     stack_names_names_ok (stack_to_lab_config_reg_names c1)
       (asm_config_reg_count (c:'a asm_config)) (asm_config_avoid_regs
       c) /\
     fixed_names (stack_to_lab_config_reg_names c1) c /\
     asm_offset_ok 0 (asm_config_addr_offset c) (n2w 0) /\
       good_dimindex (:'a) /\
     asm_offset_ok 0 (asm_config_byte_offset c) (n2w 0) /\
     (!n. n <= max_stack_alloc ==> asm_config_valid_imm
     c (INL Sub) (n2w (n * (dimindex (:'a) DIV 8))) /\
       asm_config_valid_imm
     c (INL Add) (n2w (n * (dimindex (:'a) DIV 8)))) /\
       asm_config_valid_imm
     c (INL Add) (n2w 1) /\ asm_config_valid_imm c (INL Sub) (n2w
       1) /\ asm_config_valid_imm
     c (INL Add) (n2w 4) /\ asm_config_valid_imm c (INL Add) (n2w
       8) /\
     (!s. asm_offset_ok 0 (asm_config_addr_offset c) (store_offset
       s)) /\ reg_name 10 c /\
     reg_name (sp + 2) c /\ reg_name (sp + 1) c /\ reg_name sp c /\
     conf_ok (:'a) c2 /\ ~(sp = 0) ==>
     (\c ls. EVERY (sec_ok_pre c) ls) c (compile c1 c2 c3 sp
       (asm_config_addr_offset c) prog)`)
  CHEAT_TAC;;

let IMP_init_store_ok = cake_theorem "IMP_init_store_ok"
  (fun () ->
    `max_heap = 2 * max_heap_limit (:'a) c1 - 1 /\
     (fmis,xxx) = full_make_init stack_conf c1 max_heap sp offset
       (bitmaps:('a word) list) code s save_regs data_sp coracle ==>
      init_store_ok c1
        (state_store fmis \\ Handler) (state_memory
         fmis) (state_mdomain
         fmis) (state_code_buffer
        fmis) (state_data_buffer
        fmis)`)
  CHEAT_TAC;;

let IMP_init_state_ok = cake_theorem "IMP_init_state_ok"
  (fun () ->
    `4 < kkk /\
     (bitmaps:('a word) list) = (n2w 4) :: t /\
     good_dimindex (:'a) /\
     (!n.
       (\((bm0,cfg),progs).
        EVERY
          (post_alloc_conventions kkk o SND o SND) progs /\
        EVERY (flat_exp_conventions o SND o SND) progs /\
        EVERY ((\y. ~(raise_stub_location = y)) o FST) progs /\
        EVERY ((\y. ~(store_consts_stub_location = y)) o FST) progs
          /\
        (n = 0 ==> bm0 = LENGTH bitmaps)) (word_oracle n)) /\
     stack_oracle =
     (\n.
      (\((bm0,cfg),progs).
         (\(progs,fs,bm). (cfg,progs,append (FST bm)))
           (compile_word_to_stack
              ac F kkk progs
              (misc_Nil,bm0))) (word_oracle n)) /\
       (full_make_init scc dc max_heap stk stoff bitmaps p6 lab_st
         save_regs data_sp stack_oracle = (fmis,SOME xxx)) ==>
       init_state_ok ac kkk fmis word_oracle`)
  CHEAT_TAC;;

let full_make_init_has_fp_ops =
  cake_theorem "full_make_init_has_fp_ops[simp]"
  (fun () ->
    `full_make_init stack_conf (data_to_word_config_has_fp_tern_fupd (K
  b2) (has_fp_ops_fupd (K b1) dconf))
         mheap sp offset bitmaps code s save_regs dsp cor =
       full_make_init stack_conf dconf
         mheap sp offset bitmaps code s save_regs dsp cor`)
  CHEAT_TAC;;

let complex_get_code_labels_def = cake_define
  `complex_get_code_labels x1 =
        match x1 with
          stackLang_Seq p1 p2 -> complex_get_code_labels p1 UNION
            complex_get_code_labels p2
        | (If _20 _21 _22 p1 p2) -> complex_get_code_labels p1 UNION
          complex_get_code_labels p2
        | (Call ret dest handler) ->
        (match dest with INL x -> {(x,0)} | _23 -> {}) UNION
        (match ret with NONE -> {} | SOME (r,_24,l1,l2) -> (l1,l2)
          INSERT (complex_get_code_labels r UNION
             (match handler with NONE -> {} | SOME (r,l1,l2) ->
               (l1,l2) INSERT complex_get_code_labels r)))
        | (Loop p) -> complex_get_code_labels p
        | (LocValue i l1 l2) -> {(l1,l2)}
        | (stackLang_RawCall l) -> {(l,1)}
        | (stackLang_JumpLower n m l) -> {(l,0)}
        | _25 -> {}`;;

let complex_flatten_labels =
  cake_theorem "complex_flatten_labels[local]"
  (fun () ->
    `!t p n m cs bs.
     let pp = set_of_list (append (FST (stack_to_lab_flatten t p n
       m cs bs))) in
     BIGUNION (IMAGE line_get_labels pp) SUBSET
     (n,0) INSERT
     (n,(if t /\ (?p1 p2. p = Seq p1 p2) then 1 else 0)) INSERT (
     set_of_list (MAP (\l. (n,l)) (cs ++ bs)) UNION
     IMAGE (\n2. (n,n2)) (BIGUNION (IMAGE line_get_code_labels pp))
       UNION
     complex_get_code_labels p)`)
  CHEAT_TAC;;

let flatten_labels = cake_theorem "flatten_labels[local]"
  (fun () ->
    `!t m n p cs bs l x y.
       stack_to_lab_flatten t m n p cs bs = (l,x,y) /\
       EVERY (sec_label_ok n) (append l) ==>
       BIGUNION (IMAGE line_get_labels (set_of_list (append l)))
         SUBSET
       set_of_list (MAP (\l. (n,l)) (cs ++ bs)) UNION
       sec_get_code_labels (Section n (append l)) UNION
       get_code_labels m`)
  CHEAT_TAC;;

let get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma =
  cake_theorem "get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma"
  (fun () ->
    `!p. EVERY sec_labels_ok (MAP prog_to_section p) ==>
      get_labels (MAP prog_to_section p) SUBSET
      get_code_labels (MAP prog_to_section p) UNION
      BIGUNION (IMAGE get_code_labels (set_of_list (MAP SND p)))`)
  CHEAT_TAC;;

let prog_to_section_preserves_MAP_FST =
  cake_theorem "prog_to_section_preserves_MAP_FST[local]"
  (fun () ->
    `!p.
       IMAGE (\n. n,0) (set_of_list (MAP FST p)) SUBSET
       get_code_labels (MAP prog_to_section p)`)
  CHEAT_TAC;;

let prog_to_section_labels = cake_theorem "prog_to_section_labels"
  (fun () ->
    `prog_to_section (n,p) = pp ==>
     sec_get_labels pp SUBSET
     sec_get_code_labels pp UNION complex_get_code_labels p`)
  CHEAT_TAC;;

let flatten_preserves_handler_labels =
  cake_theorem "flatten_preserves_handler_labels"
  (fun () ->
    `!t m n p cs bs l x y.
     stack_to_lab_flatten t m n p cs bs = (l,x,y) ==>
     stack_get_handler_labels n m SUBSET
       sec_get_code_labels (Section n (append l))`)
  CHEAT_TAC;;

let MAP_prog_to_section_preserves_handler_labels =
  cake_theorem "MAP_prog_to_section_preserves_handler_labels"
  (fun () ->
    `!p.
      BIGUNION (set_of_list (MAP (\(n,pp). stack_get_handler_labels
        n pp) p)) SUBSET
      get_code_labels (MAP prog_to_section p)`)
  CHEAT_TAC;;

let one_prog_section = cake_theorem "one_prog_section"
  (fun () ->
    `IMAGE (\n. (n,1)) (set_of_list (MAP FST p)) SUBSET
     get_code_labels (MAP prog_to_section p)`)
  CHEAT_TAC;;

let get_labels_MAP_prog_to_section_SUBSET_code_labels =
  cake_theorem "get_labels_MAP_prog_to_section_SUBSET_code_labels"
  (fun () ->
    `!p.
       EVERY sec_labels_ok (MAP prog_to_section p) /\
        stack_good_code_labels p elabs ==>
        get_labels (MAP prog_to_section p) SUBSET
        get_code_labels (MAP prog_to_section p) UNION
        IMAGE (\n. n,0) elabs UNION
        IMAGE (\n. n,1) elabs`)
  CHEAT_TAC;;

(* TODO: move these when the actual needed theorem is clearer...
  - e.g.: do we need a LIST_REL on the labels before/after each code
    table entry? or just a weaker BIGUNION?
    (I think the latter may be sufficient)
 *)
(* stack_names *)
let get_code_labels_comp = cake_theorem "get_code_labels_comp[local]"
  (fun () ->
    `!f p. complex_get_code_labels (stack_names_comp f p) =
  complex_get_code_labels p`)
  CHEAT_TAC;;

let stack_names_get_code_labels =
  cake_theorem "stack_names_get_code_labels"
  (fun () ->
    `LIST_REL (\cp p. complex_get_code_labels cp =
  complex_get_code_labels p)
     (MAP SND (stack_names_compile f prog)) (MAP SND prog)`)
  CHEAT_TAC;;

(* stack_remove *)
let stack_to_labProof_get_code_labels_comp =
  cake_theorem "get_code_labels_comp[local]"
  (fun () ->
    `!a b c p. get_code_labels (comp a b c p) SUBSET (stack_err_lab,0)
  INSERT get_code_labels p`)
  CHEAT_TAC;;

let init_stubs_labels = cake_theorem "init_stubs_labels[local]"
  (fun () ->
    `EVERY (\p. get_code_labels p SUBSET (set_of_list [(1,0);
  (start,0)])) (MAP SND (init_stubs ggc mh k start))`)
  CHEAT_TAC;;

(* ---- stack_names  ----*)
let stack_names_get_code_labels_comp =
  cake_theorem "stack_names_get_code_labels_comp[local]"
  (fun () ->
    `!f p. get_code_labels (stack_names_comp f p) = get_code_labels p`)
  CHEAT_TAC;;

let stack_names_stack_get_handler_labels_comp =
  cake_theorem "stack_names_stack_get_handler_labels_comp[local]"
  (fun () ->
    `!f p n.
     stack_get_handler_labels n (stack_names_comp f p) =
     stack_get_handler_labels n p`)
  CHEAT_TAC;;

let UNCURRY_PAIR_ETA = cake_theorem "UNCURRY_PAIR_ETA[local]"
  (fun () ->
    `UNCURRY f = (\(p1,p2). f p1 p2)`)
  CHEAT_TAC;;

(* TODO: Exported for now -- maybe using in backendProof *)
let stack_names_stack_good_code_labels =
  cake_theorem "stack_names_stack_good_code_labels"
  (fun () ->
    `!prog f. stack_good_code_labels prog elabs ==>
     stack_good_code_labels (stack_names_compile f prog) elabs`)
  CHEAT_TAC;;

(* ---- stack_remove ---- *)
let stack_remove_get_code_labels_comp =
  cake_theorem "stack_remove_get_code_labels_comp[local]"
  (fun () ->
    `!a b c p.
     get_code_labels (comp a b c p) SUBSET (stack_err_lab,0)
       INSERT get_code_labels p`)
  CHEAT_TAC;;

let stack_remove_stack_get_handler_labels_comp =
  cake_theorem "stack_remove_stack_get_handler_labels_comp[local]"
  (fun () ->
    `!a b c p m.
     stack_get_handler_labels m (comp a b c p) =
     stack_get_handler_labels m p`)
  CHEAT_TAC;;

let stack_remove_init_code_labels =
  cake_theorem "stack_remove_init_code_labels[local]"
  (fun () ->
    `x IN get_code_labels (init_code ggc mh sp) ==> x = (1,0)`)
  CHEAT_TAC;;

let stack_remove_stack_good_code_labels =
  cake_theorem "stack_remove_stack_good_code_labels"
  (fun () ->
    `!prog.
     MEM loc (MAP FST prog) /\
     stack_good_code_labels prog elabs ==>
     stack_good_code_labels (stack_remove_compile jump off ggc mh
       sp loc prog) elabs`)
  CHEAT_TAC;;

(*
  The same theorem, but for the incremental version
  The jump label (2) is now assumed to be in there
*)
let stack_remove_stack_good_code_labels_incr =
  cake_theorem "stack_remove_stack_good_code_labels_incr"
  (fun () ->
    `!prog.
     stack_err_lab IN elabs /\
     stack_good_code_labels prog elabs ==>
     stack_good_code_labels (MAP (prog_comp jump offset sp) prog)
       elabs`)
  CHEAT_TAC;;

(* --- stack_alloc ---- *)
let stack_alloc_get_code_labels_comp =
  cake_theorem "stack_alloc_get_code_labels_comp[local]"
  (fun () ->
    `!n m p pp mm.
     get_code_labels (FST (comp n m p)) SUBSET
       (gc_stub_location,0) INSERT get_code_labels p`)
  CHEAT_TAC;;

let stack_alloc_stack_get_handler_labels_comp =
  cake_theorem "stack_alloc_stack_get_handler_labels_comp[local]"
  (fun () ->
    `!n m p pp mm.
     stack_get_handler_labels i (FST (comp n m p)) =
       stack_get_handler_labels i p`)
  CHEAT_TAC;;

let stack_alloc_init_code_labels =
  cake_theorem "stack_alloc_init_code_labels[local]"
  (fun () ->
    `get_code_labels (word_gc_code c) = {}`)
  CHEAT_TAC;;

let stack_alloc_stack_good_code_labels =
  cake_theorem "stack_alloc_stack_good_code_labels"
  (fun () ->
    `!prog c.
     stack_good_code_labels prog elabs ==>
     stack_good_code_labels (stack_alloc_compile c prog) elabs`)
  CHEAT_TAC;;

(*
  The same theorem, but for the incremental version
  The jump label (2) is now assumed to be in there
*)
let stack_alloc_stack_good_code_labels_incr =
  cake_theorem "stack_alloc_stack_good_code_labels_incr"
  (fun () ->
    `!prog.
     gc_stub_location IN elabs /\
     stack_good_code_labels prog elabs ==>
     stack_good_code_labels (MAP prog_comp prog) elabs`)
  CHEAT_TAC;;

let IN_get_code_labels_comp_top_lemma =
  cake_theorem "IN_get_code_labels_comp_top_lemma"
  (fun () ->
    `!i q p_1 p_2.
       ((p_1,p_2) IN get_code_labels (stack_rawcall_comp i q) ==>
        (?k. (p_1,k) IN get_code_labels q /\
            (~(p_2 = k) ==> p_2 = 1 /\ k = 0 /\ p_1 IN domain i)))
              /\
       ((p_1,p_2) IN get_code_labels (comp_top i q) ==>
        (?k. (p_1,k) IN get_code_labels q /\
            (~(p_2 = k) ==> p_2 = 1 /\ k = 0 /\ p_1 IN domain
              i)))`)
  CHEAT_TAC;;

let IN_domain_collect_info = cake_theorem "IN_domain_collect_info"
  (fun () ->
    `!prog f p_1.
       p_1 IN domain (collect_info prog f) ==>
       MEM p_1 (MAP FST prog) \/ p_1 IN domain f`)
  CHEAT_TAC;;

let IN_get_code_labels_comp_top =
  cake_theorem "IN_get_code_labels_comp_top"
  (fun () ->
    `(p_1,p_2) IN get_code_labels (comp_top (collect_info prog LN) q)
  ==>
     (?k. (p_1,k) IN get_code_labels q /\
         (~(p_2 = k) ==> p_2 = 1 /\ k = 0 /\ MEM p_1 (MAP FST
           prog)))`)
  CHEAT_TAC;;

let stack_rawcall_stack_good_code_labels =
  cake_theorem "stack_rawcall_stack_good_code_labels"
  (fun () ->
    `stack_good_code_labels prog elabs ==>
     stack_good_code_labels (stack_rawcall_compile prog) elabs`)
  CHEAT_TAC;;

(* stack_to_lab *)
let stack_to_lab_stack_good_code_labels =
  cake_theorem "stack_to_lab_stack_good_code_labels"
  (fun () ->
    `compile stack_conf data_conf max_heap sp offset prog = prog' /\
     MEM InitGlobals_location (MAP FST prog) /\
     stack_good_code_labels prog elabs /\
     EVERY sec_labels_ok prog' ==>
     get_labels prog' SUBSET get_code_labels prog' UNION IMAGE
       (\n. n,0) elabs UNION IMAGE (\n. n,1) elabs`)
  CHEAT_TAC;;

let stack_to_lab_stack_good_code_labels_incr =
  cake_theorem "stack_to_lab_stack_good_code_labels_incr"
  (fun () ->
    `stack_err_lab IN elabs /\
     gc_stub_location IN elabs /\
     compile_no_stubs f jump offset sp prog = prog' /\
     stack_good_code_labels prog elabs /\
     EVERY sec_labels_ok prog' ==>
     get_labels prog' SUBSET get_code_labels prog' UNION IMAGE
       (\n. n,0) elabs UNION IMAGE (\n. n,1) elabs`)
  CHEAT_TAC;;

(* nonzero restricted code labels *)
let nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels =
  cake_theorem
    "nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels"
  (fun () ->
    `!p.
        EVERY sec_labels_ok (MAP prog_to_section p) /\
        stack_good_handler_labels p ==>
        restrict_nonzero (get_labels (MAP prog_to_section p))
          SUBSET
        get_code_labels (MAP prog_to_section p)`)
  CHEAT_TAC;;

let stack_names_stack_good_handler_labels =
  cake_theorem "stack_names_stack_good_handler_labels"
  (fun () ->
    `!prog f. stack_good_handler_labels prog ==>
     stack_good_handler_labels (stack_names_compile f prog)`)
  CHEAT_TAC;;

let restrict_nonzero_union = cake_theorem "restrict_nonzero_union"
  (fun () ->
    `restrict_nonzero (A UNION B) = restrict_nonzero A UNION
  restrict_nonzero B`)
  CHEAT_TAC;;

let restrict_nonzero_IN = cake_theorem "restrict_nonzero_IN"
  (fun () ->
    `x IN restrict_nonzero s <=> x IN s /\ ~(SND x = 0)`)
  CHEAT_TAC;;

let stack_good_handler_labels_append =
  cake_theorem "stack_good_handler_labels_append"
  (fun () ->
    `stack_good_handler_labels xs /\
     stack_good_handler_labels ys ==>
     stack_good_handler_labels (xs ++ ys)`)
  CHEAT_TAC;;

let stack_remove_stack_good_handler_labels_incr =
  cake_theorem "stack_remove_stack_good_handler_labels_incr"
  (fun () ->
    `!prog.
     stack_good_handler_labels prog ==>
     stack_good_handler_labels (MAP (prog_comp jump offset sp)
       prog)`)
  CHEAT_TAC;;

let stack_remove_stack_good_handler_labels =
  cake_theorem "stack_remove_stack_good_handler_labels"
  (fun () ->
    `!prog.
     stack_good_handler_labels prog ==>
     stack_good_handler_labels (stack_remove_compile jump off ggc
       mh sp loc prog)`)
  CHEAT_TAC;;

let stack_alloc_stack_good_handler_labels_incr =
  cake_theorem "stack_alloc_stack_good_handler_labels_incr"
  (fun () ->
    `!prog.
     stack_good_handler_labels prog ==>
     stack_good_handler_labels (MAP prog_comp prog)`)
  CHEAT_TAC;;

let stack_alloc_stack_good_handler_labels =
  cake_theorem "stack_alloc_stack_good_handler_labels"
  (fun () ->
    `!prog c.
     stack_good_handler_labels prog ==>
     stack_good_handler_labels (stack_alloc_compile c prog)`)
  CHEAT_TAC;;

let stack_rawcall_stack_good_handler_labels =
  cake_theorem "stack_rawcall_stack_good_handler_labels"
  (fun () ->
    `stack_good_handler_labels prog ==>
     stack_good_handler_labels (stack_rawcall_compile prog)`)
  CHEAT_TAC;;

let stack_to_lab_stack_good_handler_labels =
  cake_theorem "stack_to_lab_stack_good_handler_labels"
  (fun () ->
    `compile stack_conf data_conf max_heap sp offset prog = prog' /\
     stack_good_handler_labels prog /\
     EVERY sec_labels_ok prog' ==>
     restrict_nonzero (get_labels prog') SUBSET get_code_labels
       prog'`)
  CHEAT_TAC;;

let stack_to_lab_stack_good_handler_labels_incr =
  cake_theorem "stack_to_lab_stack_good_handler_labels_incr"
  (fun () ->
    `compile_no_stubs f jump offset sp prog = prog' /\
     stack_good_handler_labels prog /\
     EVERY sec_labels_ok prog' ==>
     restrict_nonzero (get_labels prog') SUBSET get_code_labels
       prog'`)
  CHEAT_TAC;;

(*** no_shmemop ***)

let stack_rawcall_comp_no_shmemop =
  cake_theorem "stack_rawcall_comp_no_shmemop"
  (fun () ->
    `!i p. no_shmemop p ==> no_shmemop (comp i p)`)
  CHEAT_TAC;;

let stack_rawcall_comp_top_no_shmemop =
  cake_theorem "stack_rawcall_comp_top_no_shmemop"
  (fun () ->
    `!p. no_shmemop p ==> no_shmemop (comp_top i p)`)
  CHEAT_TAC;;

let stack_rawcall_compile_no_shmemop =
  cake_theorem "stack_rawcall_compile_no_shmemop"
  (fun () ->
    `!prog. EVERY (\(a,p). no_shmemop p) prog ==>
         EVERY (\(a,p). no_shmemop p) (compile prog)`)
  CHEAT_TAC;;

let stack_alloc_comp_no_shmemop =
  cake_theorem "stack_alloc_comp_no_shmemop"
  (fun () ->
    `!n m p. no_shmemop p ==> no_shmemop (FST (comp n m p))`)
  CHEAT_TAC;;

let stack_alloc_prog_comp_no_shmemop =
  cake_theorem "stack_alloc_prog_comp_no_shmemop"
  (fun () ->
    `!prog.
     EVERY (\(a,p). no_shmemop p) prog ==>
     EVERY (\(a,p). no_shmemop p) (MAP prog_comp prog)`)
  CHEAT_TAC;;

let stack_alloc_compile_no_shmemop =
  cake_theorem "stack_alloc_compile_no_shmemop"
  (fun () ->
    `EVERY (\(a,p). no_shmemop p) prog ==>
     EVERY (\(a,p). no_shmemop p) (stack_alloc_compile data prog)`)
  CHEAT_TAC;;

let upshift_no_shmemop = cake_theorem "upshift_no_shmemop[simp]"
  (fun () ->
    `!k n. no_shmemop (upshift k n)`)
  CHEAT_TAC;;

let downshift_no_shmemop = cake_theorem "downshift_no_shmemop[simp]"
  (fun () ->
    `!k n. no_shmemop (downshift k n)`)
  CHEAT_TAC;;

let stack_free_no_shmemop = cake_theorem "stack_free_no_shmemop[simp]"
  (fun () ->
    `!k n. no_shmemop (stack_free k n)`)
  CHEAT_TAC;;

let stack_alloc_no_shmemop = cake_theorem "stack_alloc_no_shmemop[simp]"
  (fun () ->
    `!jump k n. no_shmemop (stack_alloc jump k n)`)
  CHEAT_TAC;;

let stack_remove_comp_no_shmemop =
  cake_theorem "stack_remove_comp_no_shmemop"
  (fun () ->
    `!jump off k p. no_shmemop p ==> no_shmemop (comp jump off k p)`)
  CHEAT_TAC;;

let stack_remove_prog_comp_no_shmemop =
  cake_theorem "stack_remove_prog_comp_no_shmemop"
  (fun () ->
    `!p. no_shmemop p ==> no_shmemop (SND (prog_comp jump off k
  (n,p)))`)
  CHEAT_TAC;;

let stack_remove_compile_no_shmemop =
  cake_theorem "stack_remove_compile_no_shmemop"
  (fun () ->
    `EVERY (\(a,p). no_shmemop p) prog ==>
     EVERY (\(a,p). no_shmemop p) (stack_remove_compile jump
       offset gckind mh sp loc prog)`)
  CHEAT_TAC;;

let stack_names_comp_no_shmemop =
  cake_theorem "stack_names_comp_no_shmemop"
  (fun () ->
    `!f p. no_shmemop p ==> no_shmemop (stack_names_comp f p)`)
  CHEAT_TAC;;

let stack_names_prog_comp_no_shmemop =
  cake_theorem "stack_names_prog_comp_no_shmemop"
  (fun () ->
    `!prog.
     EVERY (\(a,p). no_shmemop p) prog ==>
     EVERY (\(a,p). no_shmemop p) (MAP (prog_comp f) prog)`)
  CHEAT_TAC;;

let stack_names_compile_no_shmemop =
  cake_theorem "stack_names_compile_no_shmemop"
  (fun () ->
    `EVERY (\(a,p). no_shmemop p) prog ==>
     EVERY (\(a,p). no_shmemop p) (stack_names_compile names
       prog)`)
  CHEAT_TAC;;

let flatten_no_share_mem_inst = cake_theorem "flatten_no_share_mem_inst"
  (fun () ->
    `!t p n m cs bs.
         no_shmemop p ==>
         EVERY (\ln. !op re a inst' len. ~(ln = labLang_Asm
           (ShareMem op re a) inst' len))
               (append (FST (stack_to_lab_flatten t p n m cs
                 bs)))`)
  CHEAT_TAC;;

let asm_fetch_aux_no_share_mem_inst_CONS =
  cake_theorem "asm_fetch_aux_no_share_mem_inst_CONS"
  (fun () ->
    `!xs.
     EVERY (\ln. !op re a inst' len. ~(ln = labLang_Asm (ShareMem
       op re a) inst' len)) xs /\
     no_share_mem_inst ls ==>
     no_share_mem_inst (Section k xs :: ls)`)
  CHEAT_TAC;;

let prog_to_section_no_share_mem_inst =
  cake_theorem "prog_to_section_no_share_mem_inst"
  (fun () ->
    `!prog. EVERY (\(a,p). no_shmemop p) prog ==>
            no_share_mem_inst (MAP prog_to_section prog)`)
  CHEAT_TAC;;

let compile_no_share_mem_inst = cake_theorem "compile_no_share_mem_inst"
  (fun () ->
    `!prog prog'.
     EVERY (\(a,p). no_shmemop p) prog /\
     compile stack_conf data_conf max_heap sp offset prog = prog'
       ==>
     no_share_mem_inst prog'`)
  CHEAT_TAC;;

let stack_remove_prog_comp_no_shmemop_MAP =
  cake_theorem "stack_remove_prog_comp_no_shmemop_MAP"
  (fun () ->
    `EVERY (\(a,p). no_shmemop p) prog ==>
     EVERY (\(a,p). no_shmemop p) (MAP (prog_comp jump offset sp)
       prog)`)
  CHEAT_TAC;;

let compile_no_stubs_no_share_mem_inst =
  cake_theorem "compile_no_stubs_no_share_mem_inst"
  (fun () ->
    `EVERY (\(a,p). no_shmemop p) prog /\
     compile_no_stubs f jump offset sp prog = prog' ==>
     no_share_mem_inst prog'`)
  CHEAT_TAC;;

(*** no_install ***)

let stack_rawcall_comp_no_install =
  cake_theorem "stack_rawcall_comp_no_install"
  (fun () ->
    `!i p. no_install p ==> no_install (comp i p)`)
  CHEAT_TAC;;

let stack_rawcall_comp_top_no_install =
  cake_theorem "stack_rawcall_comp_top_no_install"
  (fun () ->
    `!p. no_install p ==> no_install (comp_top i p)`)
  CHEAT_TAC;;

let stack_rawcall_compile_no_install =
  cake_theorem "stack_rawcall_compile_no_install"
  (fun () ->
    `!prog. EVERY (\(a,p). no_install p) prog ==>
         EVERY (\(a,p). no_install p) (compile prog)`)
  CHEAT_TAC;;

let stack_alloc_comp_no_install =
  cake_theorem "stack_alloc_comp_no_install"
  (fun () ->
    `!n m p. no_install p ==> no_install (FST (comp n m p))`)
  CHEAT_TAC;;

let stack_alloc_prog_comp_no_install =
  cake_theorem "stack_alloc_prog_comp_no_install"
  (fun () ->
    `!prog.
     EVERY (\(a,p). no_install p) prog ==>
     EVERY (\(a,p). no_install p) (MAP prog_comp prog)`)
  CHEAT_TAC;;

let stack_alloc_compile_no_install =
  cake_theorem "stack_alloc_compile_no_install"
  (fun () ->
    `EVERY (\(a,p). no_install p) prog ==>
     EVERY (\(a,p). no_install p) (stack_alloc_compile data prog)`)
  CHEAT_TAC;;

let upshift_no_install = cake_theorem "upshift_no_install[simp]"
  (fun () ->
    `!k n. no_install (upshift k n)`)
  CHEAT_TAC;;

let downshift_no_install = cake_theorem "downshift_no_install[simp]"
  (fun () ->
    `!k n. no_install (downshift k n)`)
  CHEAT_TAC;;

let stack_free_no_install = cake_theorem "stack_free_no_install[simp]"
  (fun () ->
    `!k n. no_install (stack_free k n)`)
  CHEAT_TAC;;

let stack_alloc_no_install = cake_theorem "stack_alloc_no_install[simp]"
  (fun () ->
    `!jump k n. no_install (stack_alloc jump k n)`)
  CHEAT_TAC;;

let stack_remove_comp_no_install =
  cake_theorem "stack_remove_comp_no_install"
  (fun () ->
    `!jump off k p. no_install p ==> no_install (comp jump off k p)`)
  CHEAT_TAC;;

let stack_remove_prog_comp_no_install =
  cake_theorem "stack_remove_prog_comp_no_install"
  (fun () ->
    `!p. no_install p ==> no_install (SND (prog_comp jump off k
  (n,p)))`)
  CHEAT_TAC;;

let stack_remove_compile_no_install =
  cake_theorem "stack_remove_compile_no_install"
  (fun () ->
    `EVERY (\(a,p). no_install p) prog ==>
     EVERY (\(a,p). no_install p) (stack_remove_compile jump
       offset gckind mh sp loc prog)`)
  CHEAT_TAC;;

let stack_names_comp_no_install =
  cake_theorem "stack_names_comp_no_install"
  (fun () ->
    `!f p. no_install p ==> no_install (stack_names_comp f p)`)
  CHEAT_TAC;;

let stack_names_prog_comp_no_install =
  cake_theorem "stack_names_prog_comp_no_install"
  (fun () ->
    `!prog.
     EVERY (\(a,p). no_install p) prog ==>
     EVERY (\(a,p). no_install p) (MAP (prog_comp f) prog)`)
  CHEAT_TAC;;

let stack_names_compile_no_install =
  cake_theorem "stack_names_compile_no_install"
  (fun () ->
    `EVERY (\(a,p). no_install p) prog ==>
     EVERY (\(a,p). no_install p) (stack_names_compile names
       prog)`)
  CHEAT_TAC;;

let flatten_no_install = cake_theorem "flatten_no_install"
  (fun () ->
    `!t p n m cs bs.
         no_install p ==>
         EVERY (\ln. !w bytes l. ~(ln = labLang_LabAsm Install w
           bytes l))
               (append (FST (stack_to_lab_flatten t p n m cs
                 bs)))`)
  CHEAT_TAC;;

let asm_fetch_aux_no_install_CONS =
  cake_theorem "asm_fetch_aux_no_install_CONS"
  (fun () ->
    `!xs.
     EVERY (\ln. !w bytes l. ~(ln = labLang_LabAsm Install w bytes
       l)) xs /\
     no_install ls ==>
     no_install (Section k xs :: ls)`)
  CHEAT_TAC;;

let prog_to_section_no_install =
  cake_theorem "prog_to_section_no_install"
  (fun () ->
    `!prog. EVERY (\(a,p). no_install p) prog ==>
            no_install (MAP prog_to_section prog)`)
  CHEAT_TAC;;

let stack_to_lab_compile_no_install =
  cake_theorem "stack_to_lab_compile_no_install"
  (fun () ->
    `!prog prog'.
     EVERY (\(a,p). no_install p) prog /\
     compile stack_conf data_conf max_heap sp offset prog = prog'
       ==>
     labProps_no_install prog'`)
  CHEAT_TAC;;

cake_hide_consts [];;
