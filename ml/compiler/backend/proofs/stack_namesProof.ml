(* ======================================================== *)
(*  stack_namesProof: ported from HOL4's
    compiler/backend/proofs/stack_namesProofScript.sml
    A proof theory about stack_names.ml, with 2 definitions and 38
    theorems.  Needed by stack_to_labProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for stack_names
*)

needs "compiler/backend/semantics/stackProps.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/stack_names.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;

let rename_state_def = cake_define
  `rename_state compile_rest f s = stackSem_state_ffi_save_regs_fupd (K
  (IMAGE (tlookup f) (stackSem_state_ffi_save_regs s)))
  (compile_oracle_fupd (K ((I ## stack_names_compile f ## I) o
  compile_oracle s)) (compile_fupd (K compile_rest) (state_code_fupd (K
  (fromAList (stack_names_compile f (toAList (state_code s)))))
  (stackSem_state_regs_fupd (K (MAP_KEYS (tlookup f)
  (stackSem_state_regs s)))
    s))))`;;

let make_init_def = cake_define
  `stack_namesProof_make_init f code oracle'
  (s:('a,'c,'ffi)stackSem_state) = stackSem_state_ffi_save_regs_fupd (K
  (IMAGE (LINV (tlookup f) UNIV) (stackSem_state_ffi_save_regs s)))
  (compile_oracle_fupd (K oracle') (compile_fupd (K (\cfg. compile s cfg
  o (stack_names_compile f))) (stackSem_state_regs_fupd (K (MAP_KEYS
  (LINV (tlookup f) UNIV) (stackSem_state_regs s))) (state_code_fupd (K
  code)
     s))))`;;
hol4_overload "make_init" "stack_namesProof_make_init";;
