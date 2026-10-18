(* ======================================================== *)
(*  wordConvsProof: ported from HOL4's
    compiler/backend/proofs/wordConvsProofScript.sml
    A proof theory about wordConvs.ml, with no definitions and 201
    theorems.  Needed by data_to_wordProof.ml and
    word_to_wordProof.ml.  *)
(* ======================================================== *)

(*
  Syntactic properties proofs for wordConvs.
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_alloc.ml";;
needs "compiler/backend/word_copy.ml";;
needs "compiler/backend/word_cse.ml";;
needs "compiler/backend/word_elim.ml";;
needs "compiler/backend/word_inst.ml";;
needs "compiler/backend/word_remove.ml";;
needs "compiler/backend/word_simp.ml";;
needs "compiler/backend/word_to_word.ml";;
needs "compiler/backend/word_unreach.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

cake_hide ["C"; "dummy"];;

(***
  This theory should serve also as documentation for
  the syntactic properties of wordLang that gets preserved
  across wordLang passes.
  It must NOT depend on the semantics or word_Xproof files.

  word_simp$compile_exp
  ===
    preserves label_rel: extract_labels_compile_exp
    preserves every_inst: compile_exp_no_inst

    preserves subprogs (no export): compile_exp_not_created_subprogs
    preserves code_labels (no export):   word_get_code_labels_word_simp
    preserves good_handlers (no export): word_good_handlers_word_simp

  inst_select
  ===
    preserves label_rel: inst_select_lab_pres (equality on labels)
    creates flat_exp_conventions: inst_select_flat_exp_conventions
    creates full_inst_ok_less (uses every_inst): inst_select_full_inst_ok_less

    preserves subprogs (no export): inst_select_not_created_subprogs
    preserves code_labels (no export):   word_get_code_labels_inst_select
    preserves good_handlers (no export): word_good_handlers_inst_select

  full_ssa_cc_trans
  ===
    preserves label_rel: full_ssa_cc_trans_lab_pres (equality on labels)

    preserves flat_exp_conventions: full_ssa_cc_trans_flat_exp_conventions
    creates wf_cutsets: full_ssa_cc_trans_wf_cutsets

    TODO: move these out of word_allocProof somehow
      preserves full_inst_ok_less: full_ssa_cc_trans_full_inst_ok_less
      creates pre_alloc_conventions: full_ssa_cc_trans_pre_alloc_conventions
      creates distinct_tar_reg: full_ssa_cc_trans_distinct_tar_reg
    TODO ends here

    preserves subprogs (no export): full_ssa_cc_trans_not_created_subprogs
    preserves code_labels (no_export):   word_get_code_labels_full_ssa_cc_trans
    preserves good_handlers (no_export): word_good_handlers_full_ssa_cc_trans

  remove_dead_prog (note this is ran again after remove_unreach)
  ===
    preserves label_rel: remove_dead_prog_conventions (equality on labels)

    preserves flat_exp_conventions: remove_dead_prog_conventions
    preserves full_inst_ok_less: remove_dead_prog_conventions
    preserves pre_alloc_conventions: remove_dead_prog_conventions
    preserves every_inst: remove_dead_prog_conventions
    preserves wf_cutsets: remove_dead_prog_conventions

    preserves subprogs (no export): remove_dead_prog_not_created_subprogs
    preserves code_labels (no export): word_get_code_labels_remove_dead_prog
    preserves good_handlers (no export): word_good_handlers_remove_dead_prog

  word_common_subexp_elim
  ===
    preserves label_rel: extract_labels_word_common_subexp_elim (equality on labels)

    preserves flat_exp_conventions: flat_exp_conventions_word_common_subexp_elim
    preserves wf_cutsets: wf_cutsets_word_common_subexp_elim

    TODO: move these out of word_cseProof somehow
      preserves full_inst_ok_less: full_inst_ok_less_word_common_subexp_elim
      preserves pre_alloc_conventions: pre_alloc_conventions_word_common_subexp_elim
      preserves every_inst_distinct_tar_reg: every_inst_distinct_tar_reg_word_common_subexp_elim
      preserves every_inst_two_reg_inst (unused): word_cse_conventions (unused)
    TODO ends here

    preserves subprogs (no export): word_common_subexp_elim_not_created_subprogs
    preserves code_labels (no export):   word_get_code_labels_word_common_subexp_elim
    preserves good_handlers (no export): word_good_handlers_word_common_subexp_elim

  copy_prop
  ===
    preserves label_rel: extract_labels_copy_prop (equality on labels)

    preserves flat_exp_conventions: flat_exp_conventions_copy_prop
    preserves full_inst_ok_less: full_inst_ok_less_copy_prop
    preserves pre_alloc_conventions: pre_alloc_conventions_copy_prop
    preserves every_inst_distinct_tar_reg: every_inst_distinct_tar_reg_copy_prop
    preserves wf_cutsets: wf_cutsets_copy_prop

    preserves subprogs (no export): copy_prop_not_created_subprogs
    preserves code_labels (no export):   word_get_code_labels_copy_prop
    preserves good_handlers (no export): word_good_handlers_copy_prop

  three_to_two_reg_prog
  ===
    preserves label_rel: three_to_two_reg_prog_lab_pres (equality on labels)

    preserves flat_exp_conventions: three_to_two_reg_prog_flat_exp_conventions
    preserves full_inst_ok_less :three_to_two_reg_prog_full_inst_ok_less:
    preserves pre_alloc_conventions: three_to_two_reg_prog_pre_alloc_conventions
    creates two_reg_inst (from distinct_tar_reg): three_to_two_reg_prog_two_reg_inst
    preserves wf_cutsets: three_to_two_reg_prog_wf_cutsets

    preserves subprogs (no export): three_to_two_reg_prog_not_created_subprogs
    preserves code_labels (no export): word_get_code_labels_three_to_two_reg_prog
    preserves good_handlers (no export): word_good_handlers_three_to_two_reg_prog

  remove_unreach
  ===
    preserves labels_rel: labels_rel_remove_unreach

    preserves flat_exp_conventions: flat_exp_conventions_remove_unreach
    preserves full_inst_ok_less: full_inst_ok_less_remove_unreach
    preserves pre_alloc_conventions: pre_alloc_conventions_remove_unreach
    preserves every_inst: every_inst_remove_unreach
    preserves wf_cutsets: wf_cutsets_remove_unreach

    preserves subprogs (no export): remove_unreach_not_created_subprogs
    preserves code_labels (no export):   word_get_code_labels_remove_unreach
    preserves good_handlers (no export): word_good_handlers_remove_unreach

  word_alloc
  ===
    preserves label_rel: word_alloc_lab_pres (equality on labels)

    preserves flat_exp_conventions: word_alloc_flat_exp_conventions
    preserves two_reg_inst: word_alloc_two_reg_inst

    TODO: move these out of word_allocProof somehow
      preserves full_inst_ok_less: word_alloc_full_inst_ok_less
      creates post_alloc_conventions (from pre_alloc_conventions): pre_post_conventions_word_alloc
    TODO ends here

    preserves subprogs (no export): word_alloc_not_created_subprogs
    preserves code_labels (no export): word_get_code_labels_word_alloc
    preserves good_handlers (no export): word_good_handlers_word_alloc

  remove_must_terminate
  ===
    preserves label_rel: remove_must_terminate_conventions (equality on labels)

    preserves flat_exp_conventions: remove_must_terminate_conventions
    preserves full_inst_ok_less: remove_must_terminate_conventions
    preserves post_alloc_conventions: remove_must_terminate_conventions
    preserves every_inst: remove_must_terminate_conventions

    (subprogs is dealt with separately)
    preserves code_labels (no export): word_get_code_labels_remove_must_terminate
    preserves good_handlers (no export): word_good_handlers_remove_must_terminate

  word_to_word (compile_single and full_compile_single thms)
  ===
    preserves subprogs: compile_single_not_created_subprogs
    preserves good_handlers: word_good_handlers_word_to_word, word_good_handlers_word_to_word_incr
    preserves good_code_labels: word_good_code_labels_word_to_word_incr, word_good_code_labels_word_to_word
***)

(*** word_simp$compile_exp ***)

(* labels_rel *)
let extract_labels_SmartSeq =
  cake_theorem "extract_labels_SmartSeq[local]"
  (fun () ->
    `wordConvs_extract_labels (SmartSeq p1 p2) =
  wordConvs_extract_labels (Seq p1 p2)`)
  CHEAT_TAC;;

let extract_labels_Seq_assoc_lemma =
  cake_theorem "extract_labels_Seq_assoc_lemma[local]"
  (fun () ->
    `!p1 p2. wordConvs_extract_labels (Seq_assoc p1 p2) =
              wordConvs_extract_labels p1 ++
                wordConvs_extract_labels p2`)
  CHEAT_TAC;;

let extract_labels_Seq_assoc =
  cake_theorem "extract_labels_Seq_assoc[local]"
  (fun () ->
    `wordConvs_extract_labels (Seq_assoc Skip p) =
  wordConvs_extract_labels p`)
  CHEAT_TAC;;

let extract_labels_drop_consts_1 =
  cake_theorem "extract_labels_drop_consts_1[local]"
  (fun () ->
    `wordConvs_extract_labels (drop_consts cs ls) = []`)
  CHEAT_TAC;;

let extract_labels_drop_consts =
  cake_theorem "extract_labels_drop_consts[local,simp]"
  (fun () ->
    `wordConvs_extract_labels (SmartSeq (drop_consts cs ls) p) =
  wordConvs_extract_labels p`)
  CHEAT_TAC;;

let extract_labels_const_fp_loop =
  cake_theorem "extract_labels_const_fp_loop[local]"
  (fun () ->
    `!p cs p1 cs1.
     const_fp_loop p cs = (p1,cs1) ==>
     labels_rel (wordConvs_extract_labels p)
       (wordConvs_extract_labels p1)`)
  CHEAT_TAC;;

let extract_labels_const_fp =
  cake_theorem "extract_labels_const_fp[local]"
  (fun () ->
    `labels_rel (wordConvs_extract_labels p) (wordConvs_extract_labels
  (const_fp p))`)
  CHEAT_TAC;;

let labels_rel_append_imp = cake_theorem "labels_rel_append_imp[local]"
  (fun () ->
    `labels_rel (Y ++ X) Z ==> labels_rel (X ++ Y) Z`)
  CHEAT_TAC;;

(* HOL4 wordConvsProofScript.sml:252: ML code, not ported *)

(* HOL4 wordConvsProofScript.sml:254-260: ML code, not ported *)

(* HOL4 wordConvsProofScript.sml:262-265: a theorem that HOL4 states
   as the value of an ML expression: const_fp_loop_Seq *)

(* The tricky part: to prove this syntactic property (and only for this) we
   have to show that the strategy actually works, and that any program which
   the hoist mechanism hoists will simplify (via const_fp) back to a program
   in which nothing is duplicated. *)
let const_fp_loop_dummy_cases =
  cake_theorem "const_fp_loop_dummy_cases[local]"
  (fun () ->
    `const_fp_loop (If cmp lhs rhs (Raise 1) (Raise 2)) cs = (p2,cs2)
  ==>
     (dest_Raise_num p2 = 1 /\
     (!br1 br2. const_fp_loop (If cmp lhs rhs br1 br2) cs =
       const_fp_loop br1 cs)) \/
     (dest_Raise_num p2 = 2 /\
     (!br1 br2. const_fp_loop (If cmp lhs rhs br1 br2) cs =
       const_fp_loop br2 cs)) \/
     (dest_Raise_num p2 = 0)`)
  CHEAT_TAC;;

let wordConvsProof_dest_If_thm = cake_theorem "dest_If_thm[local]"
  (fun () ->
    `dest_If x2 = SOME (g1,g2,g3,g4,g5) <=> x2 = If g1 g2 g3 g4 g5`)
  CHEAT_TAC;;

let labels_rel_hoist2 = cake_theorem "labels_rel_hoist2[local]"
  (fun () ->
    `!N p1 interm dummy' p2 s.
     try_if_hoist2 N p1 interm dummy' p2 = SOME p3 ==>
     dest_If p2 = SOME (cmp,lhs,rhs,br1,br2) ==>
     dummy' = If cmp lhs rhs (Raise 1) (Raise 2) ==>
     wordConvs_extract_labels interm = [] ==>
     labels_rel (wordConvs_extract_labels p1 ++
       wordConvs_extract_labels p2)
       (wordConvs_extract_labels p3)`)
  CHEAT_TAC;;

let labels_rel_simp_duplicate_if =
  cake_theorem "labels_rel_simp_duplicate_if[local]"
  (fun () ->
    `!p. labels_rel (wordConvs_extract_labels p)
  (wordConvs_extract_labels (simp_duplicate_if p))`)
  CHEAT_TAC;;

let labels_rel_push_out_if =
  cake_theorem "labels_rel_push_out_if[local]"
  (fun () ->
    `!p. labels_rel (wordConvs_extract_labels p)
  (wordConvs_extract_labels (push_out_if p))`)
  CHEAT_TAC;;

let extract_labels_compile_exp =
  cake_theorem "extract_labels_compile_exp"
  (fun () ->
    `!p. labels_rel (wordConvs_extract_labels p)
                    (wordConvs_extract_labels
                      (word_simp_compile_exp p))`)
  CHEAT_TAC;;

(* inst_ok_less *)
let dest_Seq_no_inst = cake_theorem "dest_Seq_no_inst[local]"
  (fun () ->
    `!prog.
     every_inst P prog ==>
     every_inst P (FST (word_simp_dest_Seq prog)) /\
     every_inst P (SND (word_simp_dest_Seq prog))`)
  CHEAT_TAC;;

let seq_assoc_no_inst = cake_theorem "Seq_assoc_no_inst[local]"
  (fun () ->
    `!p1 p2.
     every_inst P p1 /\ every_inst P p2 ==>
     every_inst P (Seq_assoc p1 p2)`)
  CHEAT_TAC;;

let every_inst_SmartSeq = cake_theorem "every_inst_SmartSeq[local]"
  (fun () ->
    `every_inst P (SmartSeq p q) =
     (every_inst P p /\ every_inst P q)`)
  CHEAT_TAC;;

let every_inst_drop_consts =
  cake_theorem "every_inst_drop_consts[local,simp]"
  (fun () ->
    `every_inst P (SmartSeq (drop_consts cs ls) p) =
     every_inst P p`)
  CHEAT_TAC;;

let every_inst_const_fp = cake_theorem "every_inst_const_fp[local]"
  (fun () ->
    `!prog.
      every_inst P prog ==>
      every_inst P (const_fp prog)`)
  CHEAT_TAC;;

let try_if_hoist2_no_inst = cake_theorem "try_if_hoist2_no_inst[local]"
  (fun () ->
    `!N p1 interm dummy' p2 s.
     try_if_hoist2 N p1 interm dummy' p2 = SOME p3 ==>
     every_inst P p1 ==>
     every_inst P interm ==>
     every_inst P p2 ==>
     every_inst P p3`)
  CHEAT_TAC;;

let simp_duplicate_if_no_inst =
  cake_theorem "simp_duplicate_if_no_inst[local]"
  (fun () ->
    `!p. every_inst P p ==> every_inst P (simp_duplicate_if p)`)
  CHEAT_TAC;;

let simp_push_out_if_no_inst =
  cake_theorem "simp_push_out_if_no_inst[local]"
  (fun () ->
    `!p. every_inst P p ==> every_inst P (push_out_if p)`)
  CHEAT_TAC;;

let compile_exp_no_inst = cake_theorem "compile_exp_no_inst"
  (fun () ->
    `!prog.
       every_inst P prog ==>
       every_inst P (word_simp_compile_exp prog)`)
  CHEAT_TAC;;

let not_created_subprogs_SmartSeq =
  cake_theorem "not_created_subprogs_SmartSeq[local]"
  (fun () ->
    `not_created_subprogs P (SmartSeq p1 p2) =
     (not_created_subprogs P p1 /\ not_created_subprogs P p2)`)
  CHEAT_TAC;;

let not_created_subprogs_Seq_assoc =
  cake_theorem "not_created_subprogs_Seq_assoc[local]"
  (fun () ->
    `!p1 p2. not_created_subprogs P (Seq_assoc p1 p2) =
     (not_created_subprogs P p1 /\ not_created_subprogs P p2)`)
  CHEAT_TAC;;

let not_created_subprogs_drop_consts =
  cake_theorem "not_created_subprogs_drop_consts[local,simp]"
  (fun () ->
    `not_created_subprogs P (SmartSeq (drop_consts cs ls) p) =
     not_created_subprogs P p`)
  CHEAT_TAC;;

let not_created_subprogs_const_fp_loop =
  cake_theorem "not_created_subprogs_const_fp_loop[local]"
  (fun () ->
    `!p cs p1 cs1.
     const_fp_loop p cs = (p1,cs1) ==>
     not_created_subprogs P p ==>
     not_created_subprogs P p1`)
  CHEAT_TAC;;

let not_created_subprogs_const_fp =
  cake_theorem "not_created_subprogs_const_fp[local]"
  (fun () ->
    `not_created_subprogs P p ==>
     not_created_subprogs P (const_fp p)`)
  CHEAT_TAC;;

let not_created_subprogs_hoist2 =
  cake_theorem "not_created_subprogs_hoist2[local]"
  (fun () ->
    `!N p1 interm dummy' p2.
     try_if_hoist2 N p1 interm dummy' p2 = SOME p3 ==>
     not_created_subprogs P p1 ==> not_created_subprogs P interm
       ==>
     not_created_subprogs P p2 ==>
     not_created_subprogs P p3`)
  CHEAT_TAC;;

let not_created_subprogs_simp_duplicate_if =
  cake_theorem "not_created_subprogs_simp_duplicate_if[local]"
  (fun () ->
    `!p. not_created_subprogs P p ==>
     not_created_subprogs P (simp_duplicate_if p)`)
  CHEAT_TAC;;

let not_created_subprogs_push_out_if =
  cake_theorem "not_created_subprogs_push_out_if[local]"
  (fun () ->
    `!p.
     not_created_subprogs P (push_out_if p) =
     not_created_subprogs P p`)
  CHEAT_TAC;;

let compile_exp_not_created_subprogs =
  cake_theorem "compile_exp_not_created_subprogs[local]"
  (fun () ->
    `not_created_subprogs P p ==>
     not_created_subprogs P (word_simp_compile_exp p)`)
  CHEAT_TAC;;

let word_get_code_labels_SmartSeq =
  cake_theorem "word_get_code_labels_SmartSeq[local,simp]"
  (fun () ->
    `wordConvs_get_code_labels (SmartSeq p q) =
     wordConvs_get_code_labels p UNION wordConvs_get_code_labels
       q`)
  CHEAT_TAC;;

let word_get_code_labels_drop_consts =
  cake_theorem "word_get_code_labels_drop_consts[local,simp]"
  (fun () ->
    `!args.
     wordConvs_get_code_labels (drop_consts l args) = {}`)
  CHEAT_TAC;;

let word_get_code_labels_const_fp_loop =
  cake_theorem "word_get_code_labels_const_fp_loop[local]"
  (fun () ->
    `!p l.
     wordConvs_get_code_labels (FST (const_fp_loop p l)) SUBSET
       wordConvs_get_code_labels p`)
  CHEAT_TAC;;

let word_good_handlers_SmartSeq =
  cake_theorem "word_good_handlers_SmartSeq[local,simp]"
  (fun () ->
    `good_handlers n (SmartSeq p q) <=>
     good_handlers n p /\
     good_handlers n q`)
  CHEAT_TAC;;

let word_good_handlers_drop_consts =
  cake_theorem "word_good_handlers_drop_consts[local,simp]"
  (fun () ->
    `!args.
     good_handlers n (drop_consts l args)`)
  CHEAT_TAC;;

let word_good_handlers_const_fp_loop =
  cake_theorem "word_good_handlers_const_fp_loop[local]"
  (fun () ->
    `!p l.
     good_handlers n p ==>
     good_handlers n (FST (const_fp_loop p l))`)
  CHEAT_TAC;;

let word_get_code_labels_Seq_assoc =
  cake_theorem "word_get_code_labels_Seq_assoc[local]"
  (fun () ->
    `!p1 p2.
     wordConvs_get_code_labels (Seq_assoc p1 p2) =
       wordConvs_get_code_labels p1 UNION wordConvs_get_code_labels p2`)
  CHEAT_TAC;;

let word_good_handlers_Seq_assoc =
  cake_theorem "word_good_handlers_Seq_assoc[local]"
  (fun () ->
    `!p1 p2.
     good_handlers n (Seq_assoc p1 p2) <=>
     good_handlers n p1 /\ good_handlers n p2`)
  CHEAT_TAC;;

let word_good_handlers_try_if_hoist2 =
  cake_theorem "word_good_handlers_try_if_hoist2[local]"
  (fun () ->
    `!N p1 interm dummy' p2 s.
     try_if_hoist2 N p1 interm dummy' p2 = SOME p3 ==>
     good_handlers n p1 /\ good_handlers n p2 /\ good_handlers n
       interm ==>
     good_handlers n p3`)
  CHEAT_TAC;;

let word_good_handlers_simp_duplicate_if =
  cake_theorem "word_good_handlers_simp_duplicate_if[local]"
  (fun () ->
    `!p. good_handlers n p ==> good_handlers n (simp_duplicate_if p)`)
  CHEAT_TAC;;

let word_good_handlers_simp_push_out_if =
  cake_theorem "word_good_handlers_simp_push_out_if[local]"
  (fun () ->
    `!p. good_handlers n p ==> good_handlers n (push_out_if p)`)
  CHEAT_TAC;;

let word_good_handlers_word_simp =
  cake_theorem "word_good_handlers_word_simp[local]"
  (fun () ->
    `!ps.
     good_handlers n ps ==>
     good_handlers n (word_simp_compile_exp ps)`)
  CHEAT_TAC;;

let word_get_code_labels_try_if_hoist2 =
  cake_theorem "word_get_code_labels_try_if_hoist2[local]"
  (fun () ->
    `!N p1 interm dummy' p2 s.
     try_if_hoist2 N p1 interm dummy' p2 = SOME p3 ==>
     wordConvs_get_code_labels p3 SUBSET
     (wordConvs_get_code_labels p1 UNION
       wordConvs_get_code_labels interm UNION
       wordConvs_get_code_labels p2)`)
  CHEAT_TAC;;

let word_get_code_labels_simp_duplicate_if =
  cake_theorem "word_get_code_labels_simp_duplicate_if[local]"
  (fun () ->
    `!p. wordConvs_get_code_labels (simp_duplicate_if p) SUBSET
  wordConvs_get_code_labels p`)
  CHEAT_TAC;;

let word_get_code_labels_push_out_if =
  cake_theorem "word_get_code_labels_push_out_if[local]"
  (fun () ->
    `!p. wordConvs_get_code_labels (push_out_if p) SUBSET
  wordConvs_get_code_labels p`)
  CHEAT_TAC;;

let word_get_code_labels_word_simp =
  cake_theorem "word_get_code_labels_word_simp[local]"
  (fun () ->
    `!ps.
     wordConvs_get_code_labels (word_simp_compile_exp ps) SUBSET
     wordConvs_get_code_labels ps`)
  CHEAT_TAC;;


(*** inst_select ***)

(* label preservation stuff *)
let inst_select_exp_no_lab =
  cake_theorem "inst_select_exp_no_lab[local]"
  (fun () ->
    `!c temp temp' exp.
     wordConvs_extract_labels (inst_select_exp c temp temp' exp)
       = []`)
  CHEAT_TAC;;

let inst_select_lab_pres = cake_theorem "inst_select_lab_pres"
  (fun () ->
    `!c temp prog.
       wordConvs_extract_labels prog = wordConvs_extract_labels
         (inst_select c temp prog)`)
  CHEAT_TAC;;

(* inst_select syntax *)
let inst_select_exp_flat_exp_conventions =
  cake_theorem "inst_select_exp_flat_exp_conventions[local]"
  (fun () ->
    `!c tar temp exp.
     flat_exp_conventions (inst_select_exp c tar temp exp)`)
  CHEAT_TAC;;

let inst_select_flat_exp_conventions =
  cake_theorem "inst_select_flat_exp_conventions"
  (fun () ->
    `!c temp prog.
       flat_exp_conventions (inst_select c temp prog)`)
  CHEAT_TAC;;

let inst_select_exp_not_created_subprogs =
  cake_theorem "inst_select_exp_not_created_subprogs[local]"
  (fun () ->
    `not_created_subprogs P (inst_select_exp c c' n exp)`)
  CHEAT_TAC;;

let inst_select_not_created_subprogs =
  cake_theorem "inst_select_not_created_subprogs[local]"
  (fun () ->
    `not_created_subprogs P prog ==>
     not_created_subprogs P (inst_select c n prog)`)
  CHEAT_TAC;;

(*Less restrictive version of inst_ok guaranteed by inst_select*)
let inst_select_exp_full_inst_ok_less =
  cake_theorem "inst_select_exp_full_inst_ok_less[local]"
  (fun () ->
    `!c tar temp exp.
     (\c. asm_offset_ok 0 (asm_config_addr_offset c)) c (n2w 0) ==>
     full_inst_ok_less c (inst_select_exp c tar temp exp)`)
  CHEAT_TAC;;

let inst_select_full_inst_ok_less =
  cake_theorem "inst_select_full_inst_ok_less"
  (fun () ->
    `!c temp prog.
       (\c. asm_offset_ok 0 (asm_config_addr_offset c)) c (n2w 0)
         /\
       (\c. asm_offset_ok 0 (asm_config_hw_offset c)) c (n2w 0) /\
       (\c. asm_offset_ok 0 (asm_config_byte_offset c)) c (n2w 0)
         /\
       every_inst (inst_ok_less c) prog ==>
       full_inst_ok_less c (inst_select c temp prog)`)
  CHEAT_TAC;;

let word_get_code_labels_inst_select_exp =
  cake_theorem "word_get_code_labels_inst_select_exp[local]"
  (fun () ->
    `!a b c exp.
     wordConvs_get_code_labels (inst_select_exp a b c exp) = {}`)
  CHEAT_TAC;;

let word_get_code_labels_inst_select =
  cake_theorem "word_get_code_labels_inst_select[local]"
  (fun () ->
    `!ac v ps.
     wordConvs_get_code_labels (inst_select ac v ps) =
     wordConvs_get_code_labels ps`)
  CHEAT_TAC;;

let word_good_handlers_inst_select_exp =
  cake_theorem "word_good_handlers_inst_select_exp[local]"
  (fun () ->
    `!a b c exp.
     good_handlers n (inst_select_exp a b c exp)`)
  CHEAT_TAC;;

let word_good_handlers_inst_select =
  cake_theorem "word_good_handlers_inst_select[local]"
  (fun () ->
    `!ac v ps.
     good_handlers n (inst_select ac v ps) <=>
     good_handlers n ps`)
  CHEAT_TAC;;

(*** full_ssa_cc_trans ***)
let fake_moves_no_labs = cake_theorem "fake_moves_no_labs[local]"
  (fun () ->
    `!ls a b c d e f g h.
     fake_moves prio ls a b c = (d,e,f,g,h) ==>
     wordConvs_extract_labels d = [] /\ wordConvs_extract_labels
       e = []`)
  CHEAT_TAC;;

let fake_seq_no_labs = cake_theorem "fake_seq_no_labs[local]"
  (fun () ->
    `!ls. wordConvs_extract_labels (ITLIST Seq (MAP (\r. fake_move r)
  ls) Skip) = []`)
  CHEAT_TAC;;

let fake_seq_get_code_labels =
  cake_theorem "fake_seq_get_code_labels[local]"
  (fun () ->
    `!ls. wordConvs_get_code_labels (ITLIST Seq (MAP (\r. fake_move r)
  ls) Skip) = {}`)
  CHEAT_TAC;;

let fake_seq_good_handlers =
  cake_theorem "fake_seq_good_handlers[local]"
  (fun () ->
    `!ls. good_handlers n (ITLIST Seq (MAP (\r. fake_move r) ls) Skip)`)
  CHEAT_TAC;;

let fake_seq_flat_exp_conventions =
  cake_theorem "fake_seq_flat_exp_conventions[local]"
  (fun () ->
    `!ls. flat_exp_conventions (ITLIST Seq (MAP (\r. fake_move r) ls)
  Skip)`)
  CHEAT_TAC;;

let fake_seq_wf_cutsets = cake_theorem "fake_seq_wf_cutsets[local]"
  (fun () ->
    `!ls. wf_cutsets (ITLIST Seq (MAP (\r. fake_move r) ls) Skip)`)
  CHEAT_TAC;;

let ssa_reconcile_no_labs = cake_theorem "ssa_reconcile_no_labs[local]"
  (fun () ->
    `wordConvs_extract_labels (ssa_reconcile cur_ssa tgt_ssa ns) = []`)
  CHEAT_TAC;;

let ssa_reconcile_get_code_labels =
  cake_theorem "ssa_reconcile_get_code_labels[local]"
  (fun () ->
    `wordConvs_get_code_labels (ssa_reconcile cur_ssa tgt_ssa ns) = {}`)
  CHEAT_TAC;;

let ssa_reconcile_good_handlers =
  cake_theorem "ssa_reconcile_good_handlers[local]"
  (fun () ->
    `good_handlers n (ssa_reconcile cur_ssa tgt_ssa ns)`)
  CHEAT_TAC;;

let ssa_reconcile_flat_exp_conventions =
  cake_theorem "ssa_reconcile_flat_exp_conventions[local]"
  (fun () ->
    `flat_exp_conventions (ssa_reconcile cur_ssa tgt_ssa ns)`)
  CHEAT_TAC;;

let ssa_reconcile_wf_cutsets =
  cake_theorem "ssa_reconcile_wf_cutsets[local]"
  (fun () ->
    `wf_cutsets (ssa_reconcile cur_ssa tgt_ssa ns)`)
  CHEAT_TAC;;

let loop_setup_no_labs = cake_theorem "loop_setup_no_labs[local]"
  (fun () ->
    `loop_setup names exit_names ssa na = (setup_prog,ssa',na') ==>
     wordConvs_extract_labels setup_prog = []`)
  CHEAT_TAC;;

let loop_setup_get_code_labels =
  cake_theorem "loop_setup_get_code_labels[local]"
  (fun () ->
    `loop_setup names exit_names ssa na = (setup_prog,ssa',na') ==>
     wordConvs_get_code_labels setup_prog = {}`)
  CHEAT_TAC;;

let loop_setup_good_handlers =
  cake_theorem "loop_setup_good_handlers[local]"
  (fun () ->
    `loop_setup names exit_names ssa na = (setup_prog,ssa',na') ==>
     good_handlers n setup_prog`)
  CHEAT_TAC;;

let loop_setup_flat_exp_conventions =
  cake_theorem "loop_setup_flat_exp_conventions[local]"
  (fun () ->
    `loop_setup names exit_names ssa na = (setup_prog,ssa',na') ==>
     flat_exp_conventions setup_prog`)
  CHEAT_TAC;;

let loop_setup_wf_cutsets = cake_theorem "loop_setup_wf_cutsets[local]"
  (fun () ->
    `loop_setup names exit_names ssa na = (setup_prog,ssa',na') ==>
     wf_cutsets setup_prog`)
  CHEAT_TAC;;

let full_ssa_cc_trans_lab_pres =
  cake_theorem "full_ssa_cc_trans_lab_pres"
  (fun () ->
    `!prog n.
     wordConvs_extract_labels prog =
     wordConvs_extract_labels (full_ssa_cc_trans n prog)`)
  CHEAT_TAC;;

let ssa_cc_trans_inst_not_created_subprogs =
  cake_theorem "ssa_cc_trans_inst_not_created_subprogs[local]"
  (fun () ->
    `ssa_cc_trans_inst i ssa na = (i',ssa',na') ==>
     not_created_subprogs P i'`)
  CHEAT_TAC;;

let fake_moves_not_created_subprogs =
  cake_theorem "fake_moves_not_created_subprogs[local]"
  (fun () ->
    `fake_moves prio ls nL nR n = (prog1,prog2,n',ssa,ssa') ==>
     not_created_subprogs P prog1 /\ not_created_subprogs P prog2`)
  CHEAT_TAC;;

let fake_seq_not_created_subprogs =
  cake_theorem "fake_seq_not_created_subprogs[local]"
  (fun () ->
    `!ls. not_created_subprogs P (ITLIST Seq (MAP (\r. fake_move r)
  ls) Skip)`)
  CHEAT_TAC;;

let loop_setup_not_created_subprogs =
  cake_theorem "loop_setup_not_created_subprogs[local]"
  (fun () ->
    `loop_setup names exit_names ssa na = (setup_prog,ssa',na') ==>
     not_created_subprogs P setup_prog`)
  CHEAT_TAC;;

let ssa_cc_trans_not_created_subprogs =
  cake_theorem "ssa_cc_trans_not_created_subprogs[local]"
  (fun () ->
    `not_created_subprogs P prog /\
     ssa_cc_trans prog ssa n lt = (prog',ssa',na) ==>
     not_created_subprogs P prog'`)
  CHEAT_TAC;;

let setup_ssa_not_created_subprogs =
  cake_theorem "setup_ssa_not_created_subprogs[local]"
  (fun () ->
    `not_created_subprogs P prog /\
     setup_ssa n v prog = (mov,ssa,na) ==>
     not_created_subprogs P mov`)
  CHEAT_TAC;;

let full_ssa_cc_trans_not_created_subprogs =
  cake_theorem "full_ssa_cc_trans_not_created_subprogs[local]"
  (fun () ->
    `not_created_subprogs P prog ==>
     not_created_subprogs P (full_ssa_cc_trans n prog)`)
  CHEAT_TAC;;

let word_get_code_labels_fake_moves =
  cake_theorem "word_get_code_labels_fake_moves[local]"
  (fun () ->
    `!a b c d e f g h i.
     fake_moves prio a b c d = (e,f,g,h,i) ==>
     wordConvs_get_code_labels e = {} /\
     wordConvs_get_code_labels f = {}`)
  CHEAT_TAC;;

let word_get_code_labels_ssa_cc_trans =
  cake_theorem "word_get_code_labels_ssa_cc_trans[local]"
  (fun () ->
    `!x y z lt a b c.
     ssa_cc_trans x y z lt = (a,b,c) ==>
     wordConvs_get_code_labels a = wordConvs_get_code_labels x`)
  CHEAT_TAC;;

let word_get_code_labels_full_ssa_cc_trans =
  cake_theorem "word_get_code_labels_full_ssa_cc_trans[local]"
  (fun () ->
    `!m p.
     wordConvs_get_code_labels (full_ssa_cc_trans m p) =
     wordConvs_get_code_labels p`)
  CHEAT_TAC;;

let word_good_handlers_fake_moves =
  cake_theorem "word_good_handlers_fake_moves[local]"
  (fun () ->
    `!a b c d e f g h i.
     fake_moves prio a b c d = (e,f,g,h,i) ==>
     good_handlers n e /\
     good_handlers n f`)
  CHEAT_TAC;;

let word_good_handlers_ssa_cc_trans =
  cake_theorem "word_good_handlers_ssa_cc_trans[local]"
  (fun () ->
    `!x y z lt a b c.
     ssa_cc_trans x y z lt = (a,b,c) ==>
     good_handlers n a = good_handlers n x`)
  CHEAT_TAC;;

let word_good_handlers_full_ssa_cc_trans =
  cake_theorem "word_good_handlers_full_ssa_cc_trans[local]"
  (fun () ->
    `!m p.
     good_handlers n (full_ssa_cc_trans m p) <=>
     good_handlers n p`)
  CHEAT_TAC;;

let flat_exp_conventions_ShareInst =
  cake_theorem "flat_exp_conventions_ShareInst[local]"
  (fun () ->
    `flat_exp_conventions (wordLang_ShareInst op v exp) <=>
       ((?v c. exp = wordLang_Op asm_Add [Var v; Const c]) \/
         (?v. exp = Var v))`)
  CHEAT_TAC;;

let flat_exp_conventions_fake_moves =
  cake_theorem "flat_exp_conventions_fake_moves[local]"
  (fun () ->
    `!ls ssal ssar na l r a b c conf.
     fake_moves prio ls ssal ssar na = (l,r,a,b,c) ==>
     flat_exp_conventions l /\
     flat_exp_conventions r`)
  CHEAT_TAC;;

let ssa_cc_trans_flat_exp_conventions =
  cake_theorem "ssa_cc_trans_flat_exp_conventions[local]"
  (fun () ->
    `!prog ssa na lt.
     flat_exp_conventions prog ==>
     flat_exp_conventions (FST (ssa_cc_trans prog ssa na lt))`)
  CHEAT_TAC;;

let full_ssa_cc_trans_flat_exp_conventions =
  cake_theorem "full_ssa_cc_trans_flat_exp_conventions"
  (fun () ->
    `!prog n.
     flat_exp_conventions prog ==>
     flat_exp_conventions (full_ssa_cc_trans n prog)`)
  CHEAT_TAC;;

let fake_moves_wf_cutsets = cake_theorem "fake_moves_wf_cutsets[local]"
  (fun () ->
    `!ls A B C' L R D E G.
     fake_moves prio ls A B C' = (L,R,D,E,G) ==>
     wf_cutsets L /\ wf_cutsets R`)
  CHEAT_TAC;;
let ssa_cc_trans_wf_cutsets =
  cake_theorem "ssa_cc_trans_wf_cutsets[local]"
  (fun () ->
    `!prog ssa na lt.
     let (prog',ssa',na') = ssa_cc_trans prog ssa na lt in
     wf_cutsets prog'`)
  CHEAT_TAC;;

let full_ssa_cc_trans_wf_cutsets =
  cake_theorem "full_ssa_cc_trans_wf_cutsets"
  (fun () ->
    `!n prog.
     wf_cutsets (full_ssa_cc_trans n prog)`)
  CHEAT_TAC;;

(*** remove_dead_prog ***)
(* HOL4 wordConvsProofScript.sml:1519: ML code, not ported *)

let remove_dead_not_created_subprogs =
  cake_theorem "remove_dead_not_created_subprogs[local]"
  (fun () ->
    `!prog q r lt.
     not_created_subprogs P prog ==>
     not_created_subprogs P (FST (remove_dead prog q r lt))`)
  CHEAT_TAC;;

let remove_dead_prog_not_created_subprogs =
  cake_theorem "remove_dead_prog_not_created_subprogs[local]"
  (fun () ->
    `not_created_subprogs P prog ==>
     not_created_subprogs P (remove_dead_prog prog)`)
  CHEAT_TAC;;

let remove_dead_conventions =
  cake_theorem "remove_dead_conventions[local]"
  (fun () ->
    `!p live nlive lt c k.
       let comp' = FST (remove_dead p live nlive lt) in
       (flat_exp_conventions p ==> flat_exp_conventions comp') /\
       (full_inst_ok_less c p ==> full_inst_ok_less c comp') /\
       (pre_alloc_conventions p ==> pre_alloc_conventions comp') /\
       (every_inst P p ==> every_inst P comp') /\
       (wf_cutsets p ==> wf_cutsets comp') /\
       (wordConvs_extract_labels p = wordConvs_extract_labels
         comp')`)
  CHEAT_TAC;;

(* HOL4 wordConvsProofScript.sml:1563-1565: a theorem that HOL4
   states as the value of an ML expression:
   remove_dead_prog_conventions *)

let word_get_code_labels_remove_dead =
  cake_theorem "word_get_code_labels_remove_dead[local]"
  (fun () ->
    `!ps live nlive lt.
     wordConvs_get_code_labels (FST (remove_dead ps live nlive lt))
       SUBSET
     wordConvs_get_code_labels ps`)
  CHEAT_TAC;;

let word_get_code_labels_remove_dead_prog =
  cake_theorem "word_get_code_labels_remove_dead_prog[local]"
  (fun () ->
    `wordConvs_get_code_labels (remove_dead_prog ps) SUBSET
     wordConvs_get_code_labels ps`)
  CHEAT_TAC;;

let word_good_handlers_remove_dead =
  cake_theorem "word_good_handlers_remove_dead[local]"
  (fun () ->
    `!ps live nlive lt.
     good_handlers n (FST (remove_dead ps live nlive lt)) <=>
     good_handlers n ps`)
  CHEAT_TAC;;

let word_good_handlers_remove_dead_prog =
  cake_theorem "word_good_handlers_remove_dead_prog[local]"
  (fun () ->
    `good_handlers n (remove_dead_prog ps) <=>
     good_handlers n ps`)
  CHEAT_TAC;;

(*** word_common_subexp_elim ***)
let word_cse_extract_labels =
  cake_theorem "word_cse_extract_labels[local]"
  (fun () ->
    `!p d d1 p1.
     word_cse d p = (d1,p1) ==>
     wordConvs_extract_labels p1 = wordConvs_extract_labels p`)
  CHEAT_TAC;;

let extract_labels_word_common_subexp_elim =
  cake_theorem "extract_labels_word_common_subexp_elim"
  (fun () ->
    `wordConvs_extract_labels (word_common_subexp_elim p) =
  wordConvs_extract_labels p`)
  CHEAT_TAC;;

let word_cseInst_not_created_subprogs =
  cake_theorem "word_cseInst_not_created_subprogs[local]"
  (fun () ->
    `!env i. not_created_subprogs P (SND (word_cseInst env i))`)
  CHEAT_TAC;;

let word_cse_not_created_subprogs =
  cake_theorem "word_cse_not_created_subprogs[local]"
  (fun () ->
    `!p env. not_created_subprogs P p ==>
     not_created_subprogs P (SND (word_cse env p))`)
  CHEAT_TAC;;

let word_common_subexp_elim_not_created_subprogs =
  cake_theorem "word_common_subexp_elim_not_created_subprogs[local]"
  (fun () ->
    `not_created_subprogs P prog ==>
     not_created_subprogs P (word_common_subexp_elim prog)`)
  CHEAT_TAC;;

let word_good_handlers_word_common_subexp_elim =
  cake_theorem "word_good_handlers_word_common_subexp_elim[local]"
  (fun () ->
    `good_handlers q (word_common_subexp_elim p) <=>
     good_handlers q p`)
  CHEAT_TAC;;

(* word_cse can only drop code-label references (LocValue-CSE replaces a
   second LocValue for the same label by a Move), so this is a ⊆, not an
   equality. *)
let word_cse_get_code_labels =
  cake_theorem "word_cse_get_code_labels[local]"
  (fun () ->
    `!p data data' (q:'a wordLang_prog).
       word_cse data p = (data',q) ==>
       wordConvs_get_code_labels q SUBSET
         wordConvs_get_code_labels p`)
  CHEAT_TAC;;

let word_get_code_labels_word_common_subexp_elim =
  cake_theorem "word_get_code_labels_word_common_subexp_elim[local]"
  (fun () ->
    `wordConvs_get_code_labels (word_common_subexp_elim p) SUBSET
     wordConvs_get_code_labels p`)
  CHEAT_TAC;;

let word_cse_flat_exp_conventions =
  cake_theorem "word_cse_flat_exp_conventions[local]"
  (fun () ->
    `!p data data' (q:'a wordLang_prog).
       flat_exp_conventions p /\ word_cse data p = (data',q) ==>
       flat_exp_conventions q`)
  CHEAT_TAC;;

let flat_exp_conventions_word_common_subexp_elim =
  cake_theorem "flat_exp_conventions_word_common_subexp_elim"
  (fun () ->
    `flat_exp_conventions p ==>
     flat_exp_conventions (word_common_subexp_elim p)`)
  CHEAT_TAC;;

let word_cse_wf_cutsets = cake_theorem "word_cse_wf_cutsets[local]"
  (fun () ->
    `!p data data' (q:'a wordLang_prog).
       wf_cutsets p /\ word_cse data p = (data',q) ==>
       wf_cutsets q`)
  CHEAT_TAC;;

let wf_cutsets_word_common_subexp_elim =
  cake_theorem "wf_cutsets_word_common_subexp_elim"
  (fun () ->
    `wf_cutsets p ==> wf_cutsets (word_common_subexp_elim p)`)
  CHEAT_TAC;;


(*** copy_prop ***)

(* may not prove goal fully *)
(* HOL4 wordConvsProofScript.sml:1855-1871: a proof *)

let wf_cutsets_copy_prop_aux =
  cake_theorem "wf_cutsets_copy_prop_aux[local]"
  (fun () ->
    `!p cs. wf_cutsets p ==>
       wf_cutsets (FST (copy_prop_prog p cs))`)
  CHEAT_TAC;;

let wf_cutsets_copy_prop = cake_theorem "wf_cutsets_copy_prop"
  (fun () ->
    `wf_cutsets p ==> wf_cutsets (copy_prop p)`)
  CHEAT_TAC;;

let every_inst_distinct_tar_reg_copy_prop_aux =
  cake_theorem "every_inst_distinct_tar_reg_copy_prop_aux[local]"
  (fun () ->
    `!p cs.
     every_inst distinct_tar_reg p ==>
     every_inst distinct_tar_reg (FST (copy_prop_prog p cs))`)
  CHEAT_TAC;;

let every_inst_distinct_tar_reg_copy_prop =
  cake_theorem "every_inst_distinct_tar_reg_copy_prop"
  (fun () ->
    `every_inst distinct_tar_reg p ==>
     every_inst distinct_tar_reg (copy_prop p)`)
  CHEAT_TAC;;

let extract_labels_copy_prop_aux =
  cake_theorem "extract_labels_copy_prop_aux[local]"
  (fun () ->
    `!p cs.
     wordConvs_extract_labels (FST (copy_prop_prog p cs)) =
     wordConvs_extract_labels p`)
  CHEAT_TAC;;

let extract_labels_copy_prop = cake_theorem "extract_labels_copy_prop"
  (fun () ->
    `wordConvs_extract_labels (copy_prop p) =
     wordConvs_extract_labels p`)
  CHEAT_TAC;;

let flat_exp_conventions_copy_prop_aux =
  cake_theorem "flat_exp_conventions_copy_prop_aux[local]"
  (fun () ->
    `!p cs.
     flat_exp_conventions p ==>
     flat_exp_conventions (FST (copy_prop_prog p cs))`)
  CHEAT_TAC;;

let flat_exp_conventions_copy_prop =
  cake_theorem "flat_exp_conventions_copy_prop"
  (fun () ->
    `flat_exp_conventions p ==>
     flat_exp_conventions (copy_prop p)`)
  CHEAT_TAC;;

let copy_prop_prog_not_alloc_var_aux1 =
  cake_theorem "copy_prop_prog_not_alloc_var_aux1[local]"
  (fun () ->
    `(!x. ~(is_alloc_var x) ==> lookup x (copy_state_to_eq cs) = NONE)
  ==>
     ~(is_alloc_var x) ==>
     lookup x (copy_state_to_eq (remove_eq cs y)) = NONE`)
  CHEAT_TAC;;

let copy_prop_prog_not_alloc_var_aux2 =
  cake_theorem "copy_prop_prog_not_alloc_var_aux2[local]"
  (fun () ->
    `!cs.
     (!x. ~(is_alloc_var x) ==> lookup x (copy_state_to_eq cs) =
       NONE) ==>
     ~(is_alloc_var x) ==>
     lookup x (copy_state_to_eq (remove_eqs cs yy)) = NONE`)
  CHEAT_TAC;;

(* trivial and tedious *)
let copy_prop_prog_not_alloc_var =
  cake_theorem "copy_prop_prog_not_alloc_var[local]"
  (fun () ->
    `!p cs.
     (!x. ~(is_alloc_var x) ==> lookup x (copy_state_to_eq cs) =
       NONE) ==>
     (!x. ~(is_alloc_var x) ==> lookup x (copy_state_to_eq (SND
       (copy_prop_prog p cs))) = NONE)`)
  CHEAT_TAC;;

let pre_alloc_conventions_copy_prop_aux =
  cake_theorem "pre_alloc_conventions_copy_prop_aux[local]"
  (fun () ->
    `!p cs.
     (!x. ~(is_alloc_var x) ==> lookup x (copy_state_to_eq cs) =
       NONE) ==>
     pre_alloc_conventions p ==>
     pre_alloc_conventions (FST (copy_prop_prog p cs))`)
  CHEAT_TAC;;

let pre_alloc_conventions_copy_prop =
  cake_theorem "pre_alloc_conventions_copy_prop"
  (fun () ->
    `pre_alloc_conventions p ==>
     pre_alloc_conventions (copy_prop p)`)
  CHEAT_TAC;;

let full_inst_ok_less_copy_prop_aux =
  cake_theorem "full_inst_ok_less_copy_prop_aux[local]"
  (fun () ->
    `!p cs.
     full_inst_ok_less ac p ==>
     full_inst_ok_less ac (FST (copy_prop_prog p cs))`)
  CHEAT_TAC;;

let full_inst_ok_less_copy_prop =
  cake_theorem "full_inst_ok_less_copy_prop"
  (fun () ->
    `full_inst_ok_less ac p ==>
     full_inst_ok_less ac (copy_prop p)`)
  CHEAT_TAC;;

let word_get_code_labels_copy_prop =
  cake_theorem "word_get_code_labels_copy_prop[local]"
  (fun () ->
    `wordConvs_get_code_labels (copy_prop ps) =
     wordConvs_get_code_labels ps`)
  CHEAT_TAC;;

let word_good_handlers_copy_prop =
  cake_theorem "word_good_handlers_copy_prop[local]"
  (fun () ->
    `good_handlers n (copy_prop ps) <=>
     good_handlers n ps`)
  CHEAT_TAC;;

let copy_prop_not_created_subprogs =
  cake_theorem "copy_prop_not_created_subprogs[local]"
  (fun () ->
    `not_created_subprogs P prog ==>
     not_created_subprogs P (copy_prop prog)`)
  CHEAT_TAC;;

(*** three_to_to_reg_prog ***)
let three_to_two_reg_prog_lab_pres =
  cake_theorem "three_to_two_reg_prog_lab_pres"
  (fun () ->
    `!prog.
     wordConvs_extract_labels prog = wordConvs_extract_labels
       (three_to_two_reg_prog b prog)`)
  CHEAT_TAC;;

let three_to_two_reg_prog_not_created_subprogs =
  cake_theorem "three_to_two_reg_prog_not_created_subprogs[local]"
  (fun () ->
    `!prog.
     not_created_subprogs P prog ==>
     not_created_subprogs P (three_to_two_reg_prog b prog)`)
  CHEAT_TAC;;

let three_to_two_reg_prog_two_reg_inst =
  cake_theorem "three_to_two_reg_prog_two_reg_inst"
  (fun () ->
    `!prog.
     b ==>
     every_inst two_reg_inst (three_to_two_reg_prog b prog)`)
  CHEAT_TAC;;

let three_to_two_reg_prog_wf_cutsets =
  cake_theorem "three_to_two_reg_prog_wf_cutsets"
  (fun () ->
    `!prog.
     wf_cutsets prog ==> wf_cutsets (three_to_two_reg_prog b
       prog)`)
  CHEAT_TAC;;

let three_to_two_reg_prog_pre_alloc_conventions =
  cake_theorem "three_to_two_reg_prog_pre_alloc_conventions"
  (fun () ->
    `!prog.
     pre_alloc_conventions prog ==>
     pre_alloc_conventions (three_to_two_reg_prog b prog)`)
  CHEAT_TAC;;

let three_to_two_reg_prog_flat_exp_conventions =
  cake_theorem "three_to_two_reg_prog_flat_exp_conventions"
  (fun () ->
    `!prog.
     flat_exp_conventions prog ==>
     flat_exp_conventions (three_to_two_reg_prog b prog)`)
  CHEAT_TAC;;

let three_to_two_reg_prog_full_inst_ok_less =
  cake_theorem "three_to_two_reg_prog_full_inst_ok_less"
  (fun () ->
    `!prog. full_inst_ok_less c prog ==>
            full_inst_ok_less c (three_to_two_reg_prog b prog)`)
  CHEAT_TAC;;

let word_get_code_labels_three_to_two_reg_prog =
  cake_theorem "word_get_code_labels_three_to_two_reg_prog[local]"
  (fun () ->
    `!ps.
     wordConvs_get_code_labels (three_to_two_reg_prog b ps) =
     wordConvs_get_code_labels ps`)
  CHEAT_TAC;;

let word_good_handlers_three_to_two_reg_prog =
  cake_theorem "word_good_handlers_three_to_two_reg_prog[local]"
  (fun () ->
    `!ps.
     good_handlers n (three_to_two_reg_prog b ps) <=>
     good_handlers n ps`)
  CHEAT_TAC;;

(*** remove_unreach ***)
let word_get_code_labels_dest_Seq_Move =
  cake_theorem "word_get_code_labels_dest_Seq_Move[local]"
  (fun () ->
    `!p.
     dest_Seq_Move p = SOME (x,y,z) ==>
     wordConvs_get_code_labels z = wordConvs_get_code_labels p`)
  CHEAT_TAC;;

let word_get_code_labels_SimpSeq =
  cake_theorem "word_get_code_labels_SimpSeq[local]"
  (fun () ->
    `wordConvs_get_code_labels (SimpSeq p q) SUBSET
     wordConvs_get_code_labels p UNION wordConvs_get_code_labels
       q`)
  CHEAT_TAC;;

let word_get_code_labels_Seq_assoc_right =
  cake_theorem "word_get_code_labels_Seq_assoc_right[local]"
  (fun () ->
    `!ps qs.
     wordConvs_get_code_labels (Seq_assoc_right ps qs) SUBSET
     wordConvs_get_code_labels ps UNION wordConvs_get_code_labels
       qs`)
  CHEAT_TAC;;

let word_get_code_labels_remove_unreach =
  cake_theorem "word_get_code_labels_remove_unreach[local]"
  (fun () ->
    `wordConvs_get_code_labels (remove_unreach ps) SUBSET
     wordConvs_get_code_labels ps`)
  CHEAT_TAC;;

let word_good_handlers_SimpSeq =
  cake_theorem "word_good_handlers_SimpSeq[local]"
  (fun () ->
    `good_handlers n ps /\ good_handlers n qs ==>
     good_handlers n (SimpSeq ps qs)`)
  CHEAT_TAC;;

let word_good_handlers_Seq_assoc_right =
  cake_theorem "word_good_handlers_Seq_assoc_right[local]"
  (fun () ->
    `good_handlers n ps /\ good_handlers n qs ==>
     good_handlers n (Seq_assoc_right ps qs)`)
  CHEAT_TAC;;

let word_good_handlers_remove_unreach =
  cake_theorem "word_good_handlers_remove_unreach[local]"
  (fun () ->
    `good_handlers n ps ==>
     good_handlers n (remove_unreach ps)`)
  CHEAT_TAC;;

let SimpSeq_not_created_subprogs =
  cake_theorem "SimpSeq_not_created_subprogs[local]"
  (fun () ->
    `not_created_subprogs P ps /\ not_created_subprogs P qs ==>
     not_created_subprogs P (SimpSeq ps qs)`)
  CHEAT_TAC;;

let seq_assoc_right_not_created_subprogs =
  cake_theorem "Seq_assoc_right_not_created_subprogs[local]"
  (fun () ->
    `not_created_subprogs P ps /\ not_created_subprogs P qs ==>
     not_created_subprogs P (Seq_assoc_right ps qs)`)
  CHEAT_TAC;;

let remove_unreach_not_created_subprogs =
  cake_theorem "remove_unreach_not_created_subprogs[local]"
  (fun () ->
    `not_created_subprogs P prog ==>
     not_created_subprogs P (remove_unreach prog)`)
  CHEAT_TAC;;

let extract_labels_SimpSeq =
  cake_theorem "extract_labels_SimpSeq[local]"
  (fun () ->
    `set_of_list (wordConvs_extract_labels (SimpSeq p1 p2)) SUBSET
  set_of_list (wordConvs_extract_labels (Seq p1 p2))`)
  CHEAT_TAC;;

let extract_labels_Seq_assoc_right_lemma =
  cake_theorem "extract_labels_Seq_assoc_right_lemma[local]"
  (fun () ->
    `!p1 p2. set_of_list (wordConvs_extract_labels (Seq_assoc_right p1
  p2)) SUBSET
             set_of_list (wordConvs_extract_labels p1) UNION
               set_of_list (wordConvs_extract_labels p2)`)
  CHEAT_TAC;;

let extract_labels_remove_unreach =
  cake_theorem "extract_labels_remove_unreach[local]"
  (fun () ->
    `set_of_list (wordConvs_extract_labels (remove_unreach p)) SUBSET
  set_of_list (wordConvs_extract_labels p)`)
  CHEAT_TAC;;

let MEM_extract_labels_Seq_assoc_right_lemma =
  cake_theorem "MEM_extract_labels_Seq_assoc_right_lemma[local]"
  (fun () ->
    `!p1 p2 x.
       MEM x (wordConvs_extract_labels (Seq_assoc_right p1 p2)) ==>
       MEM x (wordConvs_extract_labels p1) \/ MEM x
         (wordConvs_extract_labels p2)`)
  CHEAT_TAC;;

(* HOL4 wordConvsProofScript.sml:2491-2492: a theorem that HOL4
   states as the value of an ML expression: helper *)

let ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma =
  cake_theorem
    "ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma[local]"
  (fun () ->
    `!p1 p2. ALL_DISTINCT ((wordConvs_extract_labels p1) ++
  (wordConvs_extract_labels p2)) ==>
             ALL_DISTINCT (wordConvs_extract_labels
               (Seq_assoc_right p1 p2))`)
  CHEAT_TAC;;

let ALL_DISTINCT_extract_labels_remove_unreach =
  cake_theorem "ALL_DISTINCT_extract_labels_remove_unreach[local]"
  (fun () ->
    `ALL_DISTINCT (wordConvs_extract_labels p) ==>
     ALL_DISTINCT (wordConvs_extract_labels (remove_unreach p))`)
  CHEAT_TAC;;

let labels_rel_remove_unreach = cake_theorem "labels_rel_remove_unreach"
  (fun () ->
    `labels_rel (wordConvs_extract_labels q) (wordConvs_extract_labels
  (remove_unreach q))`)
  CHEAT_TAC;;

let call_arg_convention_Seq_assoc_right_lemma =
  cake_theorem "call_arg_convention_Seq_assoc_right_lemma[local]"
  (fun () ->
    `!p1 p2. call_arg_convention p1 /\ call_arg_convention p2 ==>
             call_arg_convention (Seq_assoc_right p1 p2)`)
  CHEAT_TAC;;

let call_arg_convention_remove_unreach =
  cake_theorem "call_arg_convention_remove_unreach[local]"
  (fun () ->
    `call_arg_convention p ==>
     call_arg_convention (remove_unreach p)`)
  CHEAT_TAC;;

let every_stack_var_is_stack_var_Seq_assoc_right_lemma =
  cake_theorem
    "every_stack_var_is_stack_var_Seq_assoc_right_lemma[local]"
  (fun () ->
    `!p1 p2. every_stack_var is_stack_var p1 /\
             every_stack_var is_stack_var p2 ==>
             every_stack_var is_stack_var (Seq_assoc_right p1 p2)`)
  CHEAT_TAC;;

let every_stack_var_is_stack_var_remove_unreach =
  cake_theorem "every_stack_var_is_stack_var_remove_unreach[local]"
  (fun () ->
    `every_stack_var is_stack_var p ==>
     every_stack_var is_stack_var (remove_unreach p)`)
  CHEAT_TAC;;

let pre_alloc_conventions_remove_unreach =
  cake_theorem "pre_alloc_conventions_remove_unreach"
  (fun () ->
    `pre_alloc_conventions p ==>
     pre_alloc_conventions (remove_unreach p)`)
  CHEAT_TAC;;

let full_inst_ok_less_Seq_assoc_right_lemma =
  cake_theorem "full_inst_ok_less_Seq_assoc_right_lemma[local]"
  (fun () ->
    `!p1 p2. full_inst_ok_less ac p1 /\ full_inst_ok_less ac p2 ==>
             full_inst_ok_less ac (Seq_assoc_right p1 p2)`)
  CHEAT_TAC;;

let full_inst_ok_less_remove_unreach =
  cake_theorem "full_inst_ok_less_remove_unreach"
  (fun () ->
    `full_inst_ok_less ac p ==>
     full_inst_ok_less ac (remove_unreach p)`)
  CHEAT_TAC;;

let wf_cutsets_SimpSeq = cake_theorem "wf_cutsets_SimpSeq[local]"
  (fun () ->
    `wf_cutsets p1 /\ wf_cutsets p2 ==>
     wf_cutsets (SimpSeq p1 p2)`)
  CHEAT_TAC;;

let wf_cutsets_Seq_assoc_right_lemma =
  cake_theorem "wf_cutsets_Seq_assoc_right_lemma[local]"
  (fun () ->
    `!p1 p2.
     wf_cutsets p1 /\ wf_cutsets p2 ==>
     wf_cutsets (Seq_assoc_right p1 p2)`)
  CHEAT_TAC;;

let wf_cutsets_remove_unreach = cake_theorem "wf_cutsets_remove_unreach"
  (fun () ->
    `wf_cutsets p ==> wf_cutsets (remove_unreach p)`)
  CHEAT_TAC;;

let every_inst_SimpSeq = cake_theorem "every_inst_SimpSeq[local]"
  (fun () ->
    `every_inst P p1 /\ every_inst P p2 ==>
     every_inst P (SimpSeq p1 p2)`)
  CHEAT_TAC;;

let every_inst_Seq_assoc_right_lemma =
  cake_theorem "every_inst_Seq_assoc_right_lemma[local]"
  (fun () ->
    `!p1 p2.
     every_inst P p1 /\ every_inst P p2 ==>
     every_inst P (Seq_assoc_right p1 p2)`)
  CHEAT_TAC;;

let every_inst_remove_unreach = cake_theorem "every_inst_remove_unreach"
  (fun () ->
    `every_inst P p ==>
     every_inst P (remove_unreach p)`)
  CHEAT_TAC;;

let flat_exp_conventions_SimpSeq =
  cake_theorem "flat_exp_conventions_SimpSeq[local]"
  (fun () ->
    `flat_exp_conventions p1 /\ flat_exp_conventions p2 ==>
     flat_exp_conventions (SimpSeq p1 p2)`)
  CHEAT_TAC;;

let flat_exp_conventions_Seq_assoc_right_lemma =
  cake_theorem "flat_exp_conventions_Seq_assoc_right_lemma[local]"
  (fun () ->
    `!p1 p2.
     flat_exp_conventions p1 /\ flat_exp_conventions p2 ==>
     flat_exp_conventions (Seq_assoc_right p1 p2)`)
  CHEAT_TAC;;

let flat_exp_conventions_remove_unreach =
  cake_theorem "flat_exp_conventions_remove_unreach"
  (fun () ->
    `flat_exp_conventions p ==>
     flat_exp_conventions (remove_unreach p)`)
  CHEAT_TAC;;

(*** word_alloc ***)
let apply_colour_lab_pres = cake_theorem "apply_colour_lab_pres[local]"
  (fun () ->
    `!col prog.
     wordConvs_extract_labels prog = wordConvs_extract_labels
       (apply_colour col prog)`)
  CHEAT_TAC;;

let word_alloc_lab_pres = cake_theorem "word_alloc_lab_pres"
  (fun () ->
    `wordConvs_extract_labels prog = wordConvs_extract_labels
  (word_alloc fc c alg k prog col_opt)`)
  CHEAT_TAC;;

let word_alloc_flat_exp_conventions_lem =
  cake_theorem "word_alloc_flat_exp_conventions_lem[local]"
  (fun () ->
    `!f prog.
     flat_exp_conventions prog ==>
     flat_exp_conventions (apply_colour f prog)`)
  CHEAT_TAC;;

let word_alloc_flat_exp_conventions =
  cake_theorem "word_alloc_flat_exp_conventions"
  (fun () ->
    `!fc c alg k prog col_opt.
     flat_exp_conventions prog ==>
     flat_exp_conventions (word_alloc fc c alg k prog col_opt)`)
  CHEAT_TAC;;

let word_alloc_two_reg_inst_lem =
  cake_theorem "word_alloc_two_reg_inst_lem[local]"
  (fun () ->
    `!f prog.
     every_inst two_reg_inst prog ==>
     every_inst two_reg_inst (apply_colour f prog)`)
  CHEAT_TAC;;

let word_alloc_two_reg_inst = cake_theorem "word_alloc_two_reg_inst"
  (fun () ->
    `!fc c alg k prog col_opt.
     every_inst two_reg_inst prog ==>
     every_inst two_reg_inst (word_alloc fc c alg k prog col_opt)`)
  CHEAT_TAC;;

let apply_colour_not_created_subprogs =
  cake_theorem "apply_colour_not_created_subprogs[local]"
  (fun () ->
    `not_created_subprogs P prog ==>
     not_created_subprogs P (apply_colour f prog)`)
  CHEAT_TAC;;

let word_alloc_not_created_subprogs =
  cake_theorem "word_alloc_not_created_subprogs[local]"
  (fun () ->
    `not_created_subprogs P prog ==>
     not_created_subprogs P (word_alloc n c a r prog cl)`)
  CHEAT_TAC;;

let word_get_code_labels_apply_colour =
  cake_theorem "word_get_code_labels_apply_colour[local]"
  (fun () ->
    `!col ps.
     wordConvs_get_code_labels (apply_colour col ps) =
     wordConvs_get_code_labels ps`)
  CHEAT_TAC;;

let word_good_handlers_apply_colour =
  cake_theorem "word_good_handlers_apply_colour[local]"
  (fun () ->
    `!col ps.
     good_handlers n (apply_colour col ps) <=>
     good_handlers n ps`)
  CHEAT_TAC;;

let word_get_code_labels_word_alloc =
  cake_theorem "word_get_code_labels_word_alloc[local]"
  (fun () ->
    `wordConvs_get_code_labels (word_alloc fc c alg k prog col_opt) =
     wordConvs_get_code_labels prog`)
  CHEAT_TAC;;

let word_good_handlers_word_alloc =
  cake_theorem "word_good_handlers_word_alloc[local]"
  (fun () ->
    `good_handlers n (word_alloc fc c alg k prog col_opt) <=>
     good_handlers n prog`)
  CHEAT_TAC;;

(*** remove_must_terminate ***)

(* HOL4 wordConvsProofScript.sml:2924-2927: ML code, not ported *)

let remove_must_terminate_conventions =
  cake_theorem "remove_must_terminate_conventions"
  (fun () ->
    `!p c k.
     let comp' = remove_must_terminate p in
     (flat_exp_conventions p ==> flat_exp_conventions comp') /\
     (full_inst_ok_less c p ==> full_inst_ok_less c comp') /\
     (post_alloc_conventions k p ==> post_alloc_conventions k
       comp') /\
     (every_inst P p ==> every_inst P comp') /\
     (wordConvs_extract_labels p = wordConvs_extract_labels
       comp')`)
  CHEAT_TAC;;

let word_get_code_labels_remove_must_terminate =
  cake_theorem "word_get_code_labels_remove_must_terminate[local]"
  (fun () ->
    `!ps.
     wordConvs_get_code_labels (remove_must_terminate ps) =
     wordConvs_get_code_labels ps`)
  CHEAT_TAC;;

let word_good_handlers_remove_must_terminate =
  cake_theorem "word_good_handlers_remove_must_terminate[local]"
  (fun () ->
    `!ps.
     good_handlers n (remove_must_terminate ps) <=>
     good_handlers n ps`)
  CHEAT_TAC;;

(*** word_to_word ***)
let compile_single_not_created_subprogs =
  cake_theorem "compile_single_not_created_subprogs"
  (fun () ->
    `not_created_subprogs P (SND (SND (FST prog_opt))) ==>
     not_created_subprogs P (SND (SND
       (word_to_word_compile_single two_reg_arith reg_count alg c
         prog_opt)))`)
  CHEAT_TAC;;

let word_good_handlers_word_to_word_incr_helper =
  cake_theorem "word_good_handlers_word_to_word_incr_helper[local]"
  (fun () ->
    `!oracles.
     LENGTH progs = LENGTH oracles ==>
     EVERY (\(n,m,pp). good_handlers n pp) progs ==>
     EVERY (\(n,m,pp). good_handlers n pp)
     (MAP (full_compile_single tra reg_count1
           ralg asm_c) (ZIP progs oracles))`)
  CHEAT_TAC;;

let word_good_handlers_word_to_word_incr =
  cake_theorem "word_good_handlers_word_to_word_incr"
  (fun () ->
    `EVERY (\(n,m,pp). good_handlers n pp) progs ==>
     EVERY (\(n,m,pp). good_handlers n pp)
       (MAP (\p. full_compile_single tra reg_count1 ralg asm_c
         (p,NONE)) progs)`)
  CHEAT_TAC;;

let word_good_handlers_word_to_word =
  cake_theorem "word_good_handlers_word_to_word"
  (fun () ->
    `EVERY (\(n,m,pp). good_handlers n pp) progs ==>
     EVERY (\(n,m,pp). good_handlers n pp) (SND
       (word_to_word_compile wc ac progs))`)
  CHEAT_TAC;;

let word_good_code_labels_word_to_word_incr_helper =
  cake_theorem "word_good_code_labels_word_to_word_incr_helper[local]"
  (fun () ->
    `!oracles.
     LENGTH progs = LENGTH oracles ==>
     wordConvs_good_code_labels progs elabs ==>
     wordConvs_good_code_labels
     (MAP (full_compile_single tra reg_count1
           ralg asm_c) (ZIP progs oracles)) elabs`)
  CHEAT_TAC;;

(* The actual incremental theorem to use in the backend *)
let word_good_code_labels_word_to_word_incr =
  cake_theorem "word_good_code_labels_word_to_word_incr"
  (fun () ->
    `wordConvs_good_code_labels progs elabs ==>
     wordConvs_good_code_labels
       (MAP (\p. full_compile_single tra reg_count1 ralg asm_c
         (p,NONE)) progs) elabs`)
  CHEAT_TAC;;

let word_good_code_labels_word_to_word =
  cake_theorem "word_good_code_labels_word_to_word"
  (fun () ->
    `wordConvs_good_code_labels progs elabs ==>
     wordConvs_good_code_labels (SND (word_to_word_compile wc ac
       progs)) elabs`)
  CHEAT_TAC;;

cake_hide [];;
