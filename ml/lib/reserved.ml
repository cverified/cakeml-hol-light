(* ================================================================== *)
(*  The names that the port gives constants of its own and that   *)
(*  the library must not invent for a size function.  The size    *)
(*  function of a datatype is made where the type is, before the  *)
(*  theory's own constants are there, and balanced_map's size and *)
(*  the size field of panLang's struct_info are names of the      *)
(*  theory (ml/lib/define.ml, cake_reserved).                     *)
(*                                                                *)
(*  tools/portall.py writes this file.                            *)
(* ================================================================== *)

cake_reserved :=
  ["alloc_size";
   "arch_size";
   "balanced_map_size";
   "bignum_size";
   "cb_size";
   "check_size";
   "closSem_exp1_alt_size";
   "closSem_exp2_alt_size";
   "closSem_exp3_alt_size";
   "closSem_exp_alt_size";
   "clos_known_config_inline_max_body_size";
   "clos_known_get_size";
   "dataSem_state_locals_size";
   "data_space_num_size";
   "data_to_word_config_len_size";
   "dec_alt_size";
   "default_max_body_size";
   "exp4_alt_size";
   "exp5_alt_size";
   "exp6_alt_size";
   "flatSem_exp1_alt_size";
   "flatSem_exp2_alt_size";
   "flatSem_exp3_alt_size";
   "flatSem_exp_alt_size";
   "get_gen_size";
   "get_next_size";
   "handle_size";
   "handle_size1";
   "lab_to_target_config_hash_size";
   "mlsexp_get_size";
   "nontrivial_size";
   "same_stack_size";
   "sane_locals_size";
   "sptree_size";
   "stack_size";
   "string_size";
   "struct_info_size";
   "structure_size";
   "vb_eq_size";
   "vb_size";
   "wordSem_state_locals_size";
   "wordSem_state_stack_size";
   "word_size";
   "word_to_stack_config_stack_frame_size"];;
