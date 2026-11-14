(* ======================================================== *)
(*  bvl_jumpProof: ported from HOL4's
    compiler/backend/proofs/bvl_jumpProofScript.sml
    A proof theory about bvl_jump.ml, with no definitions and 3
    theorems.  Needed by clos_to_bvlProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for bvl_jump
*)

needs "compiler/backend/bvl_jump.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "bvl_jumpProof"
  ["bvlProps"; "bvlSem"; "bvl_jump"];;

(* [local] *)
let evaluate_JumpList = prove
 (`!n xs k.
       k < LENGTH xs ==>
       (bvlSem_evaluate ([JumpList n xs],CONS (bvlSem_Number (&(n +
         k))) env,s) =
        bvlSem_evaluate ([EL k xs],CONS (bvlSem_Number (&(n + k)))
          env,s))`,
  CHEAT_TAC);;

let evaluate_Jump = prove
 (`(bvlSem_evaluate ([x],env,s) = (Rval [bvlSem_Number (&n)],t)) /\
    n < LENGTH xs ==>
    (bvlSem_evaluate ([bvl_jump_Jump x xs],env,s) =
     bvlSem_evaluate ([EL n xs],CONS (bvlSem_Number (&n)) env,t))`,
  CHEAT_TAC);;

let bvl_get_code_labels_JumpList = prove
 (`!n xs. bvlProps_get_code_labels (JumpList n xs) = UNIONS
  (set_of_list (MAP bvlProps_get_code_labels xs))`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
