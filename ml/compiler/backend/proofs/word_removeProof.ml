(* ======================================================== *)
(*  word_removeProof: ported from HOL4's
    compiler/backend/proofs/word_removeProofScript.sml
    A proof theory about word_remove.ml, with 1 definition and 32
    theorems.  Needed by word_to_wordProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for word_remove
*)

needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/word_remove.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "word_removeProof"
  ["wordConvs"; "wordProps"; "wordSem"; "word_remove"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["code_buffer","code_buffer";
   "compile","backend_compile";
   "compile","bvi_let_compile";
   "compile","bvi_to_data_compile";
   "compile","bvl_const_compile";
   "compile","bvl_handle_compile";
   "compile","bvl_to_bvi_compile";
   "compile","clos_annotate_compile";
   "compile","clos_call_compile";
   "compile","clos_fvs_compile";
   "compile","clos_known_compile";
   "compile","clos_mti_compile";
   "compile","clos_to_bvl_compile";
   "compile","compiler_compile";
   "compile","data_live_compile";
   "compile","data_space_compile";
   "compile","data_to_word_compile";
   "compile","flat_to_clos_compile";
   "compile","lab_to_target_compile";
   "compile","source_to_flat_compile";
   "compile","source_to_source_compile";
   "compile","stack_alloc_compile";
   "compile","stack_names_compile";
   "compile","stack_rawcall_compile";
   "compile","stack_remove_compile";
   "compile","stack_to_lab_compile";
   "compile","word_bignum_compile";
   "compile","word_to_stack_compile";
   "compile","word_to_word_compile";
   "data_buffer","data_buffer"];;

let compile_state_def = new_definition
  `compile_state clk c s = wordSem_state_compile_fupd (K c)
  (wordSem_state_compile_oracle_fupd (K ((I ## (MAP (I ## I ##
  remove_must_terminate))) o wordSem_state_compile_oracle s))
  (wordSem_state_code_fupd (K (sptree_map (I ## remove_must_terminate)
  (wordSem_state_code s))) (wordSem_state_termdep_fupd (K 0)
  (state_clock_fupd (K (state_clock s + clk))
     s))))`;;

let compile_state_const = prove
 (`wordSem_state_locals
      (compile_state clk c s) = wordSem_state_locals s /\
        wordSem_state_permute
      (compile_state clk c s) = wordSem_state_permute s /\ state_ffi
      (compile_state clk c s) = state_ffi s /\
        wordSem_state_code_buffer
      (compile_state clk c s) = wordSem_state_code_buffer s /\
        wordSem_state_data_buffer
      (compile_state clk c s) = wordSem_state_data_buffer s /\
        wordSem_state_code
      (compile_state clk c s) = sptree_map (I ##
        remove_must_terminate) (wordSem_state_code s) /\ state_clock
      (compile_state clk c s) = state_clock s + clk /\
        wordSem_state_termdep
      (compile_state clk c s) = 0 /\ wordSem_state_compile_oracle
      (compile_state clk c s) = (I ## (MAP (I ## I ##
        remove_must_terminate))) o wordSem_state_compile_oracle s /\
        wordSem_state_compile
      (compile_state clk c s) = c /\ stack
      (compile_state clk c s) = stack s /\ wordSem_state_store
      (compile_state clk c s) = wordSem_state_store s /\
        wordSem_state_fp_regs
      (compile_state clk c s) = wordSem_state_fp_regs s /\
        wordSem_state_memory
      (compile_state clk c s) = wordSem_state_memory s /\
        wordSem_state_mdomain
      (compile_state clk c s) = wordSem_state_mdomain s /\
        wordSem_state_sh_mdomain
      (compile_state clk c s) = wordSem_state_sh_mdomain s /\
        wordSem_state_be
      (compile_state clk c s) = wordSem_state_be s /\
        wordSem_state_gc_fun
      (compile_state clk c s) = wordSem_state_gc_fun s /\
        wordSem_state_handler
      (compile_state clk c s) = wordSem_state_handler s /\
        wordSem_state_locals_size
      (compile_state clk c s) = wordSem_state_locals_size s /\
        wordSem_state_stack_size
      (compile_state clk c s) = wordSem_state_stack_size s /\
        wordSem_state_stack_max
      (compile_state clk c s) = wordSem_state_stack_max s /\
        wordSem_state_stack_limit
      (compile_state clk c s) = wordSem_state_stack_limit s`,
  CHEAT_TAC);;
add_simp compile_state_const;;

let find_code_map_I = prove
 (`wordSem_find_code d l (sptree_map (I ## f) t) lsz = OPTION_MAP (I
  ## f ## I) (wordSem_find_code d l t lsz)`,
  CHEAT_TAC);;
add_simp find_code_map_I;;


let compile_state_update = prove
 (`stack_fupd (K f1)
      (compile_state clk c s) = compile_state clk c (stack_fupd (K
        f1) s) /\ wordSem_state_permute_fupd (K f2)
      (compile_state clk c s) = compile_state clk c
        (wordSem_state_permute_fupd (K f2) s) /\ state_ffi_fupd (K f10)
      (compile_state clk c s) = compile_state clk c (state_ffi_fupd
        (K f10) s) /\ wordSem_state_data_buffer_fupd (K f9)
      (compile_state clk c s) = compile_state clk c
        (wordSem_state_data_buffer_fupd (K f9) s) /\
        wordSem_state_code_buffer_fupd (K f8)
      (compile_state clk c s) = compile_state clk c
        (wordSem_state_code_buffer_fupd (K f8) s) /\
        wordSem_state_memory_fupd (K f7)
      (compile_state clk c s) = compile_state clk c
        (wordSem_state_memory_fupd (K f7) s) /\
        wordSem_state_locals_fupd (K f6)
      (compile_state clk c s) = compile_state clk c
        (wordSem_state_locals_fupd (K f6) s) /\
        wordSem_state_memory_fupd (K f5)
      (compile_state clk c s) = compile_state clk c
        (wordSem_state_memory_fupd (K f5) s) /\ wordSem_state_store_fupd
        (K f4)
      (compile_state clk c s) = compile_state clk c
        (wordSem_state_store_fupd (K f4) s) /\
        wordSem_state_fp_regs_fupd (K f11)
      (compile_state clk c s) = compile_state clk c
        (wordSem_state_fp_regs_fupd (K f11) s) /\
        wordSem_state_handler_fupd (K f3)
      (compile_state clk c s) = compile_state clk c
        (wordSem_state_handler_fupd (K f3) s) /\
        wordSem_state_locals_size_fupd (K f12)
      (compile_state clk c s) = compile_state clk c
        (wordSem_state_locals_size_fupd (K f12) s) /\
        wordSem_state_stack_size_fupd (K f13)
      (compile_state clk c s) = compile_state clk c
        (wordSem_state_stack_size_fupd (K f13) s) /\
        wordSem_state_stack_max_fupd (K f14)
      (compile_state clk c s) = compile_state clk c
        (wordSem_state_stack_max_fupd (K f14) s) /\
        wordSem_state_stack_limit_fupd (K f15)
      (compile_state clk c s) = compile_state clk c
        (wordSem_state_stack_limit_fupd (K f15) s)`,
  CHEAT_TAC);;
add_simp compile_state_update;;

let get_var_compile_state = prove
 (`wordSem_get_var x (compile_state clk c s) = wordSem_get_var x s`,
  CHEAT_TAC);;
add_simp get_var_compile_state;;

let get_fp_var_compile_state = prove
 (`wordSem_get_fp_var x (compile_state clk c s) = wordSem_get_fp_var x
  s`,
  CHEAT_TAC);;
add_simp get_fp_var_compile_state;;

let get_vars_compile_state = prove
 (`wordSem_get_vars xs (compile_state clk c s) = wordSem_get_vars xs s`,
  CHEAT_TAC);;
add_simp get_vars_compile_state;;

let set_var_compile_state = prove
 (`wordSem_set_var x y (compile_state clk c s) = compile_state clk c
  (wordSem_set_var x y s)`,
  CHEAT_TAC);;
add_simp set_var_compile_state;;

let unset_var_compile_state = prove
 (`wordSem_unset_var x (compile_state clk c s) = compile_state clk c
  (wordSem_unset_var x s)`,
  CHEAT_TAC);;
add_simp unset_var_compile_state;;

let set_fp_var_compile_state = prove
 (`wordSem_set_fp_var x y (compile_state clk c s) = compile_state clk
  c (wordSem_set_fp_var x y s)`,
  CHEAT_TAC);;
add_simp set_fp_var_compile_state;;

let set_vars_compile_state = prove
 (`wordSem_set_vars xs ys (compile_state clk c s) = compile_state clk
  c (wordSem_set_vars xs ys s)`,
  CHEAT_TAC);;
add_simp set_vars_compile_state;;

let get_store_compile_state = prove
 (`wordSem_get_store x (compile_state clk c s) = (wordSem_get_store x
  s)`,
  CHEAT_TAC);;
add_simp get_store_compile_state;;

let set_store_compile_state = prove
 (`wordSem_set_store x y (compile_state clk c s) = compile_state clk c
  (wordSem_set_store x y s)`,
  CHEAT_TAC);;
add_simp set_store_compile_state;;

let push_env_compile_state = prove
 (`wordSem_push_env env h (compile_state clk c s) = compile_state clk
  c (wordSem_push_env env h s)`,
  CHEAT_TAC);;
add_simp push_env_compile_state;;

let pop_env_compile_state = prove
 (`wordSem_pop_env (compile_state clk c s) = OPTION_MAP (compile_state
  clk c) (wordSem_pop_env s)`,
  CHEAT_TAC);;
add_simp pop_env_compile_state;;

let call_env_compile_state = prove
 (`wordSem_call_env x lsz (compile_state clk c z) = compile_state clk
  c (wordSem_call_env x lsz z)`,
  CHEAT_TAC);;
add_simp call_env_compile_state;;

let flush_state_compile_state = prove
 (`wordSem_flush_state x (compile_state clk c z) = compile_state clk c
  (wordSem_flush_state x z)`,
  CHEAT_TAC);;
add_simp flush_state_compile_state;;

let has_space_compile_state = prove
 (`wordSem_has_space n (compile_state clk c s) = wordSem_has_space n s`,
  CHEAT_TAC);;
add_simp has_space_compile_state;;

let gc_compile_state = prove
 (`wordSem_gc (compile_state clk c s) = OPTION_MAP (compile_state clk
  c) (wordSem_gc s)`,
  CHEAT_TAC);;
add_simp gc_compile_state;;

let alloc_compile_state = prove
 (`wordSem_alloc w names (compile_state clk c s) = (I ## compile_state
  clk c) (wordSem_alloc w names s)`,
  CHEAT_TAC);;
add_simp alloc_compile_state;;

let mem_load_compile_state = prove
 (`wordSem_mem_load w (compile_state clk c s) = wordSem_mem_load w s`,
  CHEAT_TAC);;
add_simp mem_load_compile_state;;

let mem_store_compile_state = prove
 (`wordSem_mem_store x y (compile_state clk c s) = OPTION_MAP
  (compile_state clk c) (wordSem_mem_store x y s)`,
  CHEAT_TAC);;
add_simp mem_store_compile_state;;

let word_exp_compile_state = prove
 (`!s y. wordSem_word_exp (compile_state clk c s) y = wordSem_word_exp
  s y`,
  CHEAT_TAC);;
add_simp word_exp_compile_state;;

let assign_compile_state = prove
 (`wordSem_assign x y (compile_state clk c s) = OPTION_MAP
  (compile_state clk c) (wordSem_assign x y s)`,
  CHEAT_TAC);;
add_simp assign_compile_state;;

let inst_compile_state = prove
 (`wordSem_inst i (compile_state clk c s) = OPTION_MAP (compile_state
  clk c) (wordSem_inst i s)`,
  CHEAT_TAC);;
add_simp inst_compile_state;;

let cut_state_compile_state = prove
 (`wordSem_cut_state names (compile_state clk c s) =
   OPTION_MAP (compile_state clk c) (wordSem_cut_state names s)`,
  CHEAT_TAC);;
add_simp cut_state_compile_state;;

(* [local] *)
let evaluate_add_clock_compile_state = prove
 (`wordSem_evaluate (p,compile_state clk c s) = (res,compile_state 0 c
  s') /\ ~(res = SOME wordSem_TimeOut) ==>
   (!extra. wordSem_evaluate (p,compile_state (clk + extra) c s) =
           (res,compile_state extra c s'))`,
  CHEAT_TAC);;

let compile_state_dec_clock = prove
 (`~(state_clock
      s = 0) ==> (compile_state clk c (wordSem_dec_clock s) =
        wordSem_dec_clock (compile_state clk c s))`,
  CHEAT_TAC);;
add_simp compile_state_dec_clock;;

let jump_exc_compile_state = prove
 (`wordSem_jump_exc (compile_state clk c s) = OPTION_MAP
  (compile_state clk c ## I) (wordSem_jump_exc s)`,
  CHEAT_TAC);;
add_simp jump_exc_compile_state;;

let get_var_imm_compile_state = prove
 (`wordSem_get_var_imm x (compile_state clk c s) = wordSem_get_var_imm
  x s`,
  CHEAT_TAC);;
add_simp get_var_imm_compile_state;;

let push_env_case_handler = prove
 (`wordSem_push_env x (match handler with NONE -> NONE | SOME
  (v,prog,l1,l2) -> SOME (v,f prog,l1,l2)) = wordSem_push_env x
  handler`,
  CHEAT_TAC);;
add_simp push_env_case_handler;;

(* [local] *)
let pair_map_I = prove
 (`(\(k,v). (k,f v)) = (I ## f) /\
   (\(k,v). (f k,v)) = (f ## I)`,
  CHEAT_TAC);;

let word_remove_correct = prove
 (`!prog st res rst.
   wordSem_evaluate (prog,st) = (res,rst) /\ wordSem_state_compile
   st = (\cfg. c cfg o (MAP (I ## I ## remove_must_terminate))) /\
     ~(res = SOME wordSem_Error) ==>
   (?clk.
      wordSem_evaluate (remove_must_terminate prog,compile_state clk
        c st) =
      (res,compile_state 0 c rst))`,
  CHEAT_TAC);;

(* HOL4 word_removeProofScript.sml:401-428: a proof *)

(* HOL4 word_removeProofScript.sml:430: a proof *)

(* and the interface *)
let _ = unhide_overloads ();;
