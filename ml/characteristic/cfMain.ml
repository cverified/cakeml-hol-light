(* ======================================================== *)
(*  cfMain: ported from HOL4's
    characteristic/cfMainScript.sml
    A definition theory, with 1 definition and 9 theorems.  Needed
    by CommandLineProof.ml, RuntimeProof.ml and TextIOProof.ml.  *)
(* ======================================================== *)

(*
  The following section culminates in call_main_thm2 which takes a
  spec and some aspects of the current state, and proves a
  Semantics_prog statement.

  It also proves call_FFI_rel^* between the initial state, and the
  state after creating the prog and then calling the main function -
  this is useful for theorizing about the output of the program.
*)

needs "characteristic/cf.ml";;
needs "characteristic/cfHeaps.ml";;
needs "lib/set_sep.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/evaluate_dec.ml";;
needs "translator/ml_prog.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "cfMain"
  ["cf"; "cfHeaps"; "cfTactics"; "evaluate"; "evaluateProps"; "evaluate_dec";
   "ml_prog"; "ml_translator"; "semanticPrimitives"];;

let _ = do_list hide_constant ["fv"; "prog"];;

(* HOL4 cfMainScript.sml:18: ML code, not ported *)
(* TODO: don't use the parser so much here? *)
(* HOL4 cfMainScript.sml:20-22: the ML values that the definitions below
   antiquote *)

(* HOL4 cfMainScript.sml:24-66: a theorem whose statement the port cannot
   state yet: call_main_thm1 *)

(* [local] *)
let prog_to_semantics_dec_list = prove
 (`!init_env' inp prog st c r env2 s2.
      Decls init_env' inp prog env2 s2 ==>
      (semantics_dec_list inp init_env' prog (ffi_Terminate ffi_Success
        (ffi_state_io_events (semanticPrimitives_state_ffi s2))))`,
  CHEAT_TAC);;

(* [local] *)
let clock_eq_lemma = prove
 (`!c. semanticPrimitives_state_clock_fupd (K a) st =
  semanticPrimitives_state_clock_fupd (K b) st2 ==>
  semanticPrimitives_state_clock_fupd (K c)
       st = semanticPrimitives_state_clock_fupd (K c) st2`,
  CHEAT_TAC);;

(* [local] *)
let state_eq_semantics_dec_list = prove
 (`semanticPrimitives_state_clock_fupd (K a)
     st = semanticPrimitives_state_clock_fupd (K b) st2 ==>
      semantics_dec_list st env prog r = semantics_dec_list st2 env prog r`,
  CHEAT_TAC);;

(* [local] *)
let prog_SNOC_semantics_dec_list = prove
 (`!prog1 init_env' decl st1 c outcome events env2 st2.
     Decls init_env' st1 prog1 env2 st2 /\
     semantics_dec_list st2 (merge_env env2 init_env') [decl] (ffi_Terminate
       outcome events) ==>
     semantics_dec_list st1 init_env' (SNOC decl prog1) (ffi_Terminate
       outcome events)`,
  CHEAT_TAC);;

let FFI_part_hprop_def = new_definition
  `FFI_part_hprop Q =
    (!h. Q h ==> (?s u ns us. cfHeapsBase_FFI_part s u ns us IN h))`;;

let FFI_part_hprop_STAR = prove
 (`FFI_part_hprop P \/ FFI_part_hprop Q ==> FFI_part_hprop (P * Q)`,
  CHEAT_TAC);;

let FFI_part_hprop_SEP_EXISTS = prove
 (`(!x. FFI_part_hprop (P x)) ==> FFI_part_hprop (SEP_EXISTS (\x. P x))`,
  CHEAT_TAC);;

(* HOL4 cfMainScript.sml:135-161: a theorem whose statement the port cannot
   state yet: call_main_thm2 *)

(* HOL4 cfMainScript.sml:163-219: a theorem whose statement the port cannot
   state yet: call_main_thm2_ffidiv *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["fv";
   "prog"];;

(* and the interface *)
let _ = unhide_overloads ();;
