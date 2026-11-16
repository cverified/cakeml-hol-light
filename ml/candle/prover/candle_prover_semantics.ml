(* ======================================================== *)
(*  candle_prover_semantics: ported from HOL4's
    candle/prover/candle_prover_semanticsScript.sml
    A definition theory, with 2 definitions and 18 theorems.  Needed
    by x64BootstrapProof.ml.  *)
(* ======================================================== *)

(*
  Top-level soundness theorem for the Candle theorem prover.
 *)

needs "basis/basisProg.ml";;
needs "candle/prover/ast_extras.ml";;
needs "candle/prover/candle_basis_evaluate.ml";;
needs "candle/prover/candle_kernelProg.ml";;
needs "candle/prover/candle_kernel_funs.ml";;
needs "candle/prover/candle_kernel_vals.ml";;
needs "candle/prover/candle_prover_evaluate.ml";;
needs "candle/prover/candle_prover_inv.ml";;
needs "candle/prover/perms.ml";;
needs "candle/standard/ml_kernel/ml_hol_kernel_funsProg.ml";;
needs "candle/standard/monadic/holKernelProof.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "compiler/backend/dataLang.ml";;
needs "lib/balanced_map.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/semantics.ml";;
needs "translator/ml_prog.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "candle_prover_semantics"
  ["ast_extras"; "basisProg"; "candle_basis_evaluate"; "candle_kernelProg";
   "candle_kernel_funs"; "candle_kernel_vals"; "candle_prover_evaluate";
   "candle_prover_inv"; "evaluate"; "evaluateProps"; "holKernelProof";
   "misc"; "ml_hol_kernel_funsProg"; "ml_prog"; "ml_translator";
   "namespaceProps"; "perms"; "semanticPrimitives";
   "semanticPrimitivesProps"; "semantics"];;

let _ = do_list hide_constant ["prog"];;


(* HOL4 candle_prover_semanticsScript.sml:16: ML code, not ported *)

let LPREFIX_LNTH = prove
 (`!n xs l ll.
     LPREFIX xs l /\
     LNTH n xs = NONE /\
     LTAKE n l = SOME ll ==>
       LPREFIX xs (sptree_fromList ll)`,
  CHEAT_TAC);;

(* -------------------------------------------------------------------------
 * - The basis program:
 *   basis, basis_env, basis_state
 * - The candle program (includes the former):
 *   candle_code, candle_init_env, candle_init_state
 * ------------------------------------------------------------------------- *)

(* HOL4 candle_prover_semanticsScript.sml:36: the overload basis_env, which
   the port expands *)

(* HOL4 candle_prover_semanticsScript.sml:38: the overload basis_state,
   which the port expands *)

(* -------------------------------------------------------------------------
 * Show that the basis program satisfies post_state_ok, simple_dec and
 * safe_dec. Use this to show basis_env is env_ok.
 * ------------------------------------------------------------------------- *)

let post_state_ok_basis_state = prove
 (`post_state_ok (basis_state ffi)`,
  CHEAT_TAC);;

let basis_decs_ok = prove
 (`ALL simple_dec basis /\
   ALL safe_dec basis`,
  CHEAT_TAC);;

let env_ok_basis_env = prove
 (`candle_prover_inv_env_ok ctxt basis_env`,
  CHEAT_TAC);;

(* --------------------------------------------------------------------------
 * Show that the candle_init_state is state_ok.
 * ------------------------------------------------------------------------- *)

(* TODO Move this to standard/ml_kernel; a copy of this is used by the
 *      OpenTheory reader.
 *)

let init_refs_def = new_definition
  `init_refs = mk_hol_refs init_type_constants init_term_constants
  init_axioms init_context`;;

let STATE_init_refs = prove
 (`STATE init_context init_refs`,
  CHEAT_TAC);;

let candle_init_state_stamp = prove
 (`n IN kernel_types ==> n < semanticPrimitives_state_next_type_stamp
  (candle_init_state ffi)`,
  CHEAT_TAC);;

(* [local] *)
let kernel_refs_distinct = prove
 (`~(the_type_constants = the_term_constants) /\ ~(the_type_constants =
  the_axioms) /\ ~(the_type_constants = the_context) /\ ~(the_term_constants
  = the_axioms) /\ ~(the_term_constants = the_context) /\ ~(the_axioms =
  the_context)`,
  CHEAT_TAC);;
add_simp kernel_refs_distinct;;

(* [local] *)
let LLOOKUPs = prove
 (`(semanticPrimitives_Loc T loc = the_type_constants ==>
      (\l n. oEL n l) (semanticPrimitives_state_refs (candle_init_state
        ffi)) loc =
      SOME (semanticPrimitives_Refv init_type_constants_v)) /\
   (semanticPrimitives_Loc T loc = the_term_constants ==>
      (\l n. oEL n l) (semanticPrimitives_state_refs (candle_init_state
        ffi)) loc =
      SOME (semanticPrimitives_Refv init_term_constants_v)) /\
   (semanticPrimitives_Loc T loc = the_axioms ==>
      (\l n. oEL n l) (semanticPrimitives_state_refs (candle_init_state
        ffi)) loc =
      SOME (semanticPrimitives_Refv init_axioms_v)) /\
   (semanticPrimitives_Loc T loc = the_context ==>
      (\l n. oEL n l) (semanticPrimitives_state_refs (candle_init_state
        ffi)) loc =
      SOME (semanticPrimitives_Refv init_context_v))`,
  CHEAT_TAC);;

let candle_init_state_refs = prove
 (`loc IN kernel_locs ==>
     kernel_loc_ok init_refs loc (semanticPrimitives_state_refs
       (candle_init_state ffi))`,
  CHEAT_TAC);;

let candle_init_state_eval = prove
 (`eval_state_ok (semanticPrimitives_state_eval_state (candle_init_state
  ffi))`,
  CHEAT_TAC);;
add_simp candle_init_state_eval;;

let candle_init_state_ffi = prove
 (`semanticPrimitives_state_ffi
     (candle_init_state ffi) = ffi`,
  CHEAT_TAC);;
add_simp candle_init_state_ffi;;

let candle_init_state_state_ok = prove
 (`ffi_state_io_events
     ffi = [] ==>
     candle_prover_inv_state_ok init_context (candle_init_state ffi)`,
  CHEAT_TAC);;

(* --------------------------------------------------------------------------
 * First prove that all kernel values are v_ok (this follows from the
 * definition of v_ok but it's nice to have in one theorem.)
 * ------------------------------------------------------------------------- *)

(* HOL4 candle_prover_semanticsScript.sml:197-204: a proof *)

(* HOL4 candle_prover_semanticsScript.sml:206-210: a theorem that HOL4
   states as the value of an ML expression: v_ok_kernel_funs *)

(* --------------------------------------------------------------------------
 * Now prove that candle_init_env is env_ok.
 * ------------------------------------------------------------------------- *)

(* Prove env_ok and cache intermediate results. This code is very brittle.
 *)

(* HOL4 candle_prover_semanticsScript.sml:219: ML code, not ported *)

(* HOL4 candle_prover_semanticsScript.sml:221: ML code, not ported *)
  (* Constants (can these be found in a syntax file?) *)
(* HOL4 candle_prover_semanticsScript.sml:223-235: ML code, not ported *)
  (* Types *)
(* HOL4 candle_prover_semanticsScript.sml:237-238: the ML values that the
   definitions below antiquote *)
  (* Dealing with env_ok terms *)
(* HOL4 candle_prover_semanticsScript.sml:240-251: ML code, not ported *)
  (* Cache of previously proven theorems *)
(* HOL4 candle_prover_semanticsScript.sml:253-263: ML code, not ported *)
  (* 'Prove' v_ok for kernel values by looking them up in the kernel funs
   * theorem from above. *)
(* HOL4 candle_prover_semanticsScript.sml:266-272: ML code, not ported *)
  (* Theorems *)
(* HOL4 candle_prover_semanticsScript.sml:274-281: ML code, not ported *)
  (* Conversion *)
(* HOL4 candle_prover_semanticsScript.sml:283-354: the ML values that the
   definitions below antiquote *)
    (* FIXME This can succeed if it's given a term with TypeStamp *)
(* HOL4 candle_prover_semanticsScript.sml:356-397: ML code, not ported *)

let env_ok_candle_init_env = prove
 (`candle_prover_inv_env_ok init_context candle_init_env`,
  CHEAT_TAC);;

(* --------------------------------------------------------------------------
 * Top-level semantics theorem.
 * ------------------------------------------------------------------------- *)

(* TODO Print context updates on FFI
    -- Magnus: actually, we might want to print the entire context
               for each theorem to make soundness statement simple
   TODO: Use 'ffi
 *)

(* TODO why do these both exist? *)

(* [local] *)
let init_context_init_ctxt = prove
 (`init_ctxt = init_context`,
  CHEAT_TAC);;
add_simp init_context_init_ctxt;;

let semantics_thm = prove
 (`semantics_prog (semanticPrimitives_state_eval_state_fupd (K es)
  (ml_prog_init_state ffi))
                  init_env (APPEND candle_code prog) res /\
   eval_state_ok es /\
   prog_syntax_ok candle_code /\
   ALL safe_dec prog /\ ffi_state_io_events
   ffi = [] /\ ~(res = ffi_Fail) ==>
     (!outcome io_list.
        res = ffi_Terminate outcome io_list ==>
          ALL ok_event io_list) /\
     (!io_trace.
        res = ffi_Diverge io_trace ==>
          every ok_event io_trace)`,
  CHEAT_TAC);;

let events_of_def = define_cases
  `(events_of (ffi_Terminate _ io_list) = set_of_list io_list) /\
   (events_of (ffi_Diverge io_llist) = LSET io_llist) /\
   (events_of ffi_Fail = (UNIV:io_event->bool))`;;

let events_of_semantics = prove
 (`semantics_prog (ml_prog_init_state ffi) init_env (APPEND candle_code prog)
  res /\
   prog_syntax_ok candle_code /\
   ALL safe_dec prog /\ ffi_state_io_events ffi = [] /\ ~(res = ffi_Fail)
     ==>
   (!e. e IN events_of res ==> ok_event e)`,
  CHEAT_TAC);;

let events_of_semantics_with_eval_state = prove
 (`semantics_prog (semanticPrimitives_state_eval_state_fupd (K ev)
  (ml_prog_init_state ffi))
     init_env (APPEND candle_code prog) res /\ eval_state_ok ev /\
   prog_syntax_ok candle_code /\
   ALL safe_dec prog /\ ffi_state_io_events ffi = [] /\ ~(res = ffi_Fail)
     ==>
   (!e. e IN events_of res ==> ok_event e)`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["prog"];;

(* and the interface *)
let _ = unhide_overloads ();;
