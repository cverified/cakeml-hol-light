(* ======================================================== *)
(*  wordConvsProof: ported from HOL4's
    compiler/backend/proofs/wordConvsProofScript.sml  *)
(* ======================================================== *)

(*
  Syntactic properties proofs for wordConvs.
*)

needs "compiler/backend/semantics/wordConvs.ml";;
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
    creates full_inst_ok_less (uses every_inst):
      inst_select_full_inst_ok_less

    preserves subprogs (no export): inst_select_not_created_subprogs
    preserves code_labels (no export):
      word_get_code_labels_inst_select
    preserves good_handlers (no export): word_good_handlers_inst_select

  full_ssa_cc_trans
  ===
    preserves label_rel: full_ssa_cc_trans_lab_pres (equality on labels)

    preserves flat_exp_conventions:
      full_ssa_cc_trans_flat_exp_conventions
    creates wf_cutsets: full_ssa_cc_trans_wf_cutsets

    TODO: move these out of word_allocProof somehow
      preserves full_inst_ok_less: full_ssa_cc_trans_full_inst_ok_less
      creates pre_alloc_conventions:
        full_ssa_cc_trans_pre_alloc_conventions
      creates distinct_tar_reg: full_ssa_cc_trans_distinct_tar_reg
    TODO ends here

    preserves subprogs (no export):
      full_ssa_cc_trans_not_created_subprogs
    preserves code_labels (no_export):
      word_get_code_labels_full_ssa_cc_trans
    preserves good_handlers (no_export):
      word_good_handlers_full_ssa_cc_trans

  remove_dead_prog (note this is ran again after remove_unreach)
  ===
    preserves label_rel: remove_dead_prog_conventions (equality on
      labels)

    preserves flat_exp_conventions: remove_dead_prog_conventions
    preserves full_inst_ok_less: remove_dead_prog_conventions
    preserves pre_alloc_conventions: remove_dead_prog_conventions
    preserves every_inst: remove_dead_prog_conventions
    preserves wf_cutsets: remove_dead_prog_conventions

    preserves subprogs (no export):
      remove_dead_prog_not_created_subprogs
    preserves code_labels (no export):
      word_get_code_labels_remove_dead_prog
    preserves good_handlers (no export):
      word_good_handlers_remove_dead_prog

  word_common_subexp_elim
  ===
    preserves label_rel: extract_labels_word_common_subexp_elim
      (equality on labels)

    preserves flat_exp_conventions:
      flat_exp_conventions_word_common_subexp_elim
    preserves wf_cutsets: wf_cutsets_word_common_subexp_elim

    TODO: move these out of word_cseProof somehow
      preserves full_inst_ok_less:
        full_inst_ok_less_word_common_subexp_elim
      preserves pre_alloc_conventions:
        pre_alloc_conventions_word_common_subexp_elim
      preserves every_inst_distinct_tar_reg:
        every_inst_distinct_tar_reg_word_common_subexp_elim
      preserves every_inst_two_reg_inst (unused): word_cse_conventions
        (unused)
    TODO ends here

    preserves subprogs (no export):
      word_common_subexp_elim_not_created_subprogs
    preserves code_labels (no export):
      word_get_code_labels_word_common_subexp_elim
    preserves good_handlers (no export):
      word_good_handlers_word_common_subexp_elim

  copy_prop
  ===
    preserves label_rel: extract_labels_copy_prop (equality on labels)

    preserves flat_exp_conventions: flat_exp_conventions_copy_prop
    preserves full_inst_ok_less: full_inst_ok_less_copy_prop
    preserves pre_alloc_conventions: pre_alloc_conventions_copy_prop
    preserves every_inst_distinct_tar_reg:
      every_inst_distinct_tar_reg_copy_prop
    preserves wf_cutsets: wf_cutsets_copy_prop

    preserves subprogs (no export): copy_prop_not_created_subprogs
    preserves code_labels (no export):   word_get_code_labels_copy_prop
    preserves good_handlers (no export): word_good_handlers_copy_prop

  three_to_two_reg_prog
  ===
    preserves label_rel: three_to_two_reg_prog_lab_pres (equality on
      labels)

    preserves flat_exp_conventions:
      three_to_two_reg_prog_flat_exp_conventions
    preserves full_inst_ok_less
      :three_to_two_reg_prog_full_inst_ok_less:
    preserves pre_alloc_conventions:
      three_to_two_reg_prog_pre_alloc_conventions
    creates two_reg_inst (from distinct_tar_reg):
      three_to_two_reg_prog_two_reg_inst
    preserves wf_cutsets: three_to_two_reg_prog_wf_cutsets

    preserves subprogs (no export):
      three_to_two_reg_prog_not_created_subprogs
    preserves code_labels (no export):
      word_get_code_labels_three_to_two_reg_prog
    preserves good_handlers (no export):
      word_good_handlers_three_to_two_reg_prog

  remove_unreach
  ===
    preserves labels_rel: labels_rel_remove_unreach

    preserves flat_exp_conventions: flat_exp_conventions_remove_unreach
    preserves full_inst_ok_less: full_inst_ok_less_remove_unreach
    preserves pre_alloc_conventions:
      pre_alloc_conventions_remove_unreach
    preserves every_inst: every_inst_remove_unreach
    preserves wf_cutsets: wf_cutsets_remove_unreach

    preserves subprogs (no export): remove_unreach_not_created_subprogs
    preserves code_labels (no export):
      word_get_code_labels_remove_unreach
    preserves good_handlers (no export):
      word_good_handlers_remove_unreach

  word_alloc
  ===
    preserves label_rel: word_alloc_lab_pres (equality on labels)

    preserves flat_exp_conventions: word_alloc_flat_exp_conventions
    preserves two_reg_inst: word_alloc_two_reg_inst

    TODO: move these out of word_allocProof somehow
      preserves full_inst_ok_less: word_alloc_full_inst_ok_less
      creates post_alloc_conventions (from pre_alloc_conventions):
        pre_post_conventions_word_alloc
    TODO ends here

    preserves subprogs (no export): word_alloc_not_created_subprogs
    preserves code_labels (no export): word_get_code_labels_word_alloc
    preserves good_handlers (no export): word_good_handlers_word_alloc

  remove_must_terminate
  ===
    preserves label_rel: remove_must_terminate_conventions (equality on
      labels)

    preserves flat_exp_conventions: remove_must_terminate_conventions
    preserves full_inst_ok_less: remove_must_terminate_conventions
    preserves post_alloc_conventions: remove_must_terminate_conventions
    preserves every_inst: remove_must_terminate_conventions

    (subprogs is dealt with separately)
    preserves code_labels (no export):
      word_get_code_labels_remove_must_terminate
    preserves good_handlers (no export):
      word_good_handlers_remove_must_terminate

  word_to_word (compile_single and full_compile_single thms)
  ===
    preserves subprogs: compile_single_not_created_subprogs
    preserves good_handlers: word_good_handlers_word_to_word,
      word_good_handlers_word_to_word_incr
    preserves good_code_labels: word_good_code_labels_word_to_word_incr,
      word_good_code_labels_word_to_word
***)

(*** word_simp$compile_exp ***)

(* labels_rel *)

(* HOL4 wordConvsProofScript.sml:252: ML code, not ported *)

(* HOL4 wordConvsProofScript.sml:254-260: ML code, not ported *)

(* The tricky part: to prove this syntactic property (and only for this)
   we
   have to show that the strategy actually works, and that any program
     which
   the hoist mechanism hoists will simplify (via const_fp) back to a
     program
   in which nothing is duplicated. *)

(* inst_ok_less *)


(*** inst_select ***)

(* label preservation stuff *)

(* inst_select syntax *)

(*Less restrictive version of inst_ok guaranteed by inst_select*)

(*** full_ssa_cc_trans ***)

(*** remove_dead_prog ***)
(* HOL4 wordConvsProofScript.sml:1519: ML code, not ported *)

(*** word_common_subexp_elim ***)

(* word_cse can only drop code-label references (LocValue-CSE replaces a
   second LocValue for the same label by a Move), so this is a ⊆, not an
   equality. *)


(*** copy_prop ***)

(* may not prove goal fully *)
(* HOL4 wordConvsProofScript.sml:1855-1871: a proof *)

(* trivial and tedious *)

(*** three_to_to_reg_prog ***)

(*** remove_unreach ***)

(*** word_alloc ***)

(*** remove_must_terminate ***)

(* HOL4 wordConvsProofScript.sml:2924-2927: ML code, not ported *)

(*** word_to_word ***)

(* The actual incremental theorem to use in the backend *)
