(* ======================================================== *)
(*  x64_configProof: ported from HOL4's
    compiler/backend/x64/proofs/x64_configProofScript.sml
    A proof theory about x64_config.ml, with 1 definition and 4
    theorems.  Needed by replProof.ml, x64BootstrapProof.ml and
    x64_32BootstrapProof.ml.  *)
(* ======================================================== *)

(*
  For x64, prove that the compiler configuration is well formed, and
  instantiate the compiler correctness theorem.
*)

needs "compiler/backend/proofs/backendProof.ml";;
needs "compiler/backend/proofs/lab_to_targetProof.ml";;
needs "compiler/backend/x64/x64_config.ml";;
needs "compiler/encoders/x64/proofs/x64_targetProof.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "x64_configProof"
  ["backendProof"; "lab_to_targetProof"; "x64_config"; "x64_targetProof"];;

let is_x64_machine_config_def = new_definition
  `is_x64_machine_config mc <=> machine_config_target
     mc = x64_target /\ machine_config_len_reg
     mc = 6 /\ machine_config_ptr_reg
     mc = 7 /\ machine_config_len2_reg
     mc = 1 /\ machine_config_ptr2_reg
     mc = 2 /\ machine_config_callee_saved_regs
     mc = [12; 13; 14]`;;

(* HOL4 x64_configProofScript.sml:21-24: a proof *)

let x64_backend_config_ok = prove
 (`backend_config_ok x64_config x64_backend_config`,
  CHEAT_TAC);;

let x64_machine_config_ok = prove
 (`is_x64_machine_config mc ==> mc_conf_ok mc`,
  CHEAT_TAC);;

let x64_init_ok = prove
 (`is_x64_machine_config mc ==>
    mc_init_ok x64_config x64_backend_config mc`,
  CHEAT_TAC);;

(* HOL4 x64_configProofScript.sml:76: ML code, not ported *)

(* HOL4 x64_configProofScript.sml:78-85: a theorem that HOL4 states as the
   value of an ML expression: x64_compile_correct *)

(* and the interface *)
let _ = unhide_overloads ();;
