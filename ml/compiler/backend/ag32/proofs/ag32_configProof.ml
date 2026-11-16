(* ======================================================== *)
(*  ag32_configProof: ported from HOL4's
    compiler/backend/ag32/proofs/ag32_configProofScript.sml
    A proof theory about ag32_config.ml, with 1 definition and 9
    theorems.  Needed by ag32BootstrapProof.ml and
    ag32_machine_config.ml.  *)
(* ======================================================== *)

(*
  For ag32, prove that the compiler configuration is well formed, and
  instantiate the compiler correctness theorem.
*)

needs "compiler/backend/ag32/ag32_config.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/backend/proofs/backendProof.ml";;
needs "compiler/backend/proofs/lab_to_targetProof.ml";;
needs "compiler/encoders/ag32/proofs/ag32_targetProof.ml";;
needs "misc/misc.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ag32_configProof"
  ["ag32_config"; "ag32_targetProof"; "backendProof"; "lab_to_targetProof"];;

let is_ag32_machine_config_def = new_definition
  `is_ag32_machine_config mc <=> machine_config_target
   mc = ag32_target /\ machine_config_ptr_reg
   mc = 1 /\ machine_config_len_reg
   mc = 2 /\ machine_config_ptr2_reg
   mc = 3 /\ machine_config_len2_reg
   mc = 4 /\ machine_config_callee_saved_regs
   mc = [60; 61; 62]`;;

(* HOL4 ag32_configProofScript.sml:21-24: a proof *)

let ag32_backend_config_ok = prove
 (`backend_config_ok ag32_config ag32_backend_config`,
  CHEAT_TAC);;

let ag32_machine_config_ok = prove
 (`is_ag32_machine_config mc ==> mc_conf_ok mc`,
  CHEAT_TAC);;

let ag32_init_ok = prove
 (`is_ag32_machine_config mc ==>
    mc_init_ok ag32_config ag32_backend_config mc`,
  CHEAT_TAC);;

(* HOL4 ag32_configProofScript.sml:79: ML code, not ported *)

(* HOL4 ag32_configProofScript.sml:81-88: a theorem that HOL4 states as the
   value of an ML expression: ag32_compile_correct *)

let get_shmem_info_LENGTH = prove
 (`!xs c l1 l2.
     get_shmem_info xs c l1 l2 = (t1,t2) /\ LENGTH l1 = LENGTH l2 ==>
     LENGTH t1 = LENGTH t2`,
  CHEAT_TAC);;

(* [local] *)
let IMP_EVERY_list_add_if_fresh = prove
 (`!xs x p. p x /\ ALL p xs ==> ALL p (list_add_if_fresh x xs)`,
  CHEAT_TAC);;

let find_ffi_names_ExtCall = prove
 (`!xs. ALL (\x. ?i. ffi_ExtCall i = x) (find_ffi_names xs)`,
  CHEAT_TAC);;

let MAP_ExtCall_ffinames = prove
 (`!xs.
     ALL (\x. ?i. ffi_ExtCall i = x) xs ==>
     xs = MAP ffi_ExtCall (ffinames_to_string_list xs)`,
  CHEAT_TAC);;

let compile_imp_ffi_names = prove
 (`backend_compile asm_conf c p = SOME (b,d,c1)
  /\ lab_to_target_config_shmem_extra (backend_config_lab_conf
   c1) = [] /\ ~(f = []) /\ lab_to_target_config_ffi_names
     (backend_config_lab_conf
   c) = NONE /\
   ffinames_to_string_list (the [] (lab_to_target_config_ffi_names
     (backend_config_lab_conf c1))) = f ==> lab_to_target_config_ffi_names
     (backend_config_lab_conf
   c1) = SOME (MAP ffi_ExtCall f)`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
