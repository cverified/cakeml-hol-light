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
needs "compiler/backend/semantics/closSem.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

(* [local] *)
let evaluate_JumpList = prove
 (`!n xs k.
       k < LENGTH xs ==>
       (evaluate ([JumpList n xs],Number (&(n + k)) :: env,s) =
        evaluate ([EL k xs],Number (&(n + k)) :: env,s))`,
  CHEAT_TAC);;

let evaluate_Jump = prove
 (`(evaluate ([x],env,s) = (Rval [Number (&n)],t)) /\
    n < LENGTH xs ==>
    (evaluate ([bvl_jump_Jump x xs],env,s) =
     evaluate ([EL n xs],Number (&n) :: env,t))`,
  CHEAT_TAC);;

let bvl_get_code_labels_JumpList = prove
 (`!n xs. bvlProps_get_code_labels (JumpList n xs) = BIGUNION
  (set_of_list (MAP bvlProps_get_code_labels xs))`,
  CHEAT_TAC);;
