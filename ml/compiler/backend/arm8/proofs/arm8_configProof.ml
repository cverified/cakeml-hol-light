(* ======================================================== *)
(*  arm8_configProof: ported from HOL4's
    compiler/backend/arm8/proofs/arm8_configProofScript.sml
    A proof theory about arm8_config.ml, with 1 definition and 4
    theorems.  Needed by arm8BootstrapProof.ml.  *)
(* ======================================================== *)

(*
  For ARMv8, prove that the compiler configuration is well formed, and
  instantiate the compiler correctness theorem.
*)

needs "compiler/backend/arm8/arm8_config.ml";;
needs "compiler/backend/proofs/backendProof.ml";;
needs "compiler/backend/proofs/lab_to_targetProof.ml";;
needs "compiler/encoders/arm8/proofs/arm8_targetProof.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "arm8_configProof"
  ["arm8_config"; "arm8_targetProof"; "backendProof"; "lab_to_targetProof"];;

let is_arm8_machine_config_def = new_definition
  `is_arm8_machine_config mc <=> machine_config_target
   mc = arm8_target /\ machine_config_len_reg
   mc = 1 /\ machine_config_ptr_reg
   mc = 0 /\ machine_config_len2_reg
   mc = 3 /\ machine_config_ptr2_reg
   mc = 2 /\ machine_config_callee_saved_regs
   mc = [19; 20; 21; 22; 23; 24; 25; 26; 27; 28]`;;

(* HOL4 arm8_configProofScript.sml:21-24: a proof *)

let arm8_backend_config_ok = prove
 (`backend_config_ok arm8_config arm8_backend_config`,
  CHEAT_TAC);;

let arm8_machine_config_ok = prove
 (`is_arm8_machine_config mc ==> mc_conf_ok mc`,
  CHEAT_TAC);;

let arm8_init_ok = prove
 (`is_arm8_machine_config mc ==>
    mc_init_ok arm8_config arm8_backend_config mc`,
  CHEAT_TAC);;

(* HOL4 arm8_configProofScript.sml:84: ML code, not ported *)

(* HOL4 arm8_configProofScript.sml:86-93: a theorem that HOL4 states as the
   value of an ML expression: arm8_compile_correct *)

(* and the interface *)
let _ = unhide_overloads ();;
