(* ======================================================== *)
(*  candle_prover_evaluate: ported from HOL4's
    candle/prover/candle_prover_evaluateScript.sml
    A definition theory, with no definitions and 7 theorems.  Needed
    by candle_basis_evaluate.ml and candle_prover_semantics.ml.  *)
(* ======================================================== *)

(*
  Proving that Candle prover maintains its invariants (i.e. v_ok)
 *)

needs "candle/prover/ast_extras.ml";;
needs "candle/prover/candle_kernelProg.ml";;
needs "candle/prover/candle_kernel_funs.ml";;
needs "candle/prover/candle_kernel_vals.ml";;
needs "candle/prover/candle_prover_inv.ml";;
needs "candle/prover/perms.ml";;
needs "candle/standard/ml_kernel/ml_hol_kernel_funsProg.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "candle_prover_evaluate"
  ["ast_extras"; "candle_kernelProg"; "candle_kernel_funs";
   "candle_kernel_vals"; "candle_prover_inv"; "evaluate"; "evaluateProps";
   "misc"; "ml_hol_kernel_funsProg"; "ml_prog"; "namespaceProps"; "perms";
   "semanticPrimitives"; "semanticPrimitivesProps"];;

let pmatch_v_ok = prove
 (`(!envC s p v ws env.
     semanticPrimitives_pmatch envC s p v ws = Match env /\
     candle_prover_inv_v_ok ctxt v /\
     (!n len tag m.
       nsLookup envC n = SOME (len,TypeStamp tag m) /\
       m IN kernel_types ==>
         id_to_n n IN kernel_ctors) /\
     (!loc r. ~(loc IN kernel_locs) /\ (\l n. oEL n l) s loc = SOME r ==>
       candle_prover_inv_ref_ok ctxt r) /\
     ALL (candle_prover_inv_v_ok ctxt) (MAP SND ws) ==>
       ALL (candle_prover_inv_v_ok ctxt) (MAP SND env)) /\
   (!envC s ps vs ws env.
     semanticPrimitives_pmatch_list envC s ps vs ws = Match env /\
     ALL (candle_prover_inv_v_ok ctxt) vs /\
     (!n len tag m.
       nsLookup envC n = SOME (len,TypeStamp tag m) /\
       m IN kernel_types ==>
         id_to_n n IN kernel_ctors) /\
     (!loc r. ~(loc IN kernel_locs) /\ (\l n. oEL n l) s loc = SOME r ==>
       candle_prover_inv_ref_ok ctxt r) /\
     ALL (candle_prover_inv_v_ok ctxt) (MAP SND ws) ==>
       ALL (candle_prover_inv_v_ok ctxt) (MAP SND env))`,
  CHEAT_TAC);;

(* HOL4 candle_prover_evaluateScript.sml:61-116: ML code, not ported *)

(* HOL4 candle_prover_evaluateScript.sml:118-152: a theorem whose statement
   the port cannot state yet: evaluate_v_ok *)

(* HOL4 candle_prover_evaluateScript.sml:154-157: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:159-170: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:172-176: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:178-182: a proof *)

(* EXISTS_IMP[local] *)
let candle_prover_evaluate_EXISTS_IMP = prove
 (`?b. !x. P a x ==> P b x`,
  CHEAT_TAC);;
add_simp candle_prover_evaluate_EXISTS_IMP;;

(* HOL4 candle_prover_evaluateScript.sml:190-200: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:202-216: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:218-225: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:227-232: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:234-241: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:243-269: a proof *)

let v_ok_v_to_list = prove
 (`!v vs.
     semanticPrimitives_v_to_list v = SOME vs /\
     candle_prover_inv_v_ok ctxt v ==>
       ALL (candle_prover_inv_v_ok ctxt) vs`,
  CHEAT_TAC);;

let do_app_ok = prove
 (`semanticPrimitives_do_app (refs,ffi) op vs = SOME ((refs1,ffi1),res) /\ ~(op
  = ast_Opapp) /\ ~(op = ast_Eval) /\
   ALL (candle_prover_inv_v_ok ctxt) vs /\
   (!loc r. ~(loc IN kernel_locs) /\ (\l n. oEL n l) refs loc = SOME r ==>
     candle_prover_inv_ref_ok ctxt r) /\
   ALL ok_event (ffi_state_io_events ffi) /\ ~(op = ast_FFI kernel_ffi) /\
   STATE ctxt st /\
   (!loc. loc IN kernel_locs ==> kernel_loc_ok st loc refs) ==>
     (?st1.
       STATE ctxt st1 /\
       (!loc. loc IN kernel_locs ==> kernel_loc_ok st1 loc refs1) /\
       (!loc r. ~(loc IN kernel_locs) /\ (\l n. oEL n l) refs1 loc = SOME r
         ==> candle_prover_inv_ref_ok ctxt r) /\
       ALL ok_event (ffi_state_io_events ffi1) /\
       (match list_result res with
         Rval vs -> ALL (candle_prover_inv_v_ok ctxt) vs
         | Rerr (Rraise v) -> candle_prover_inv_v_ok ctxt v
         | _ -> T))`,
  CHEAT_TAC);;

let state_ok_dest_thunk = prove
 (`candle_prover_inv_state_ok ctxt s /\
   ALL (candle_prover_inv_v_ok ctxt) vs /\
   semanticPrimitives_dest_thunk (REVERSE vs)
     (semanticPrimitives_state_refs s) = semanticPrimitives_IsThunk m v ==>
     candle_prover_inv_v_ok ctxt v`,
  CHEAT_TAC);;

let state_ok_update_thunk = prove
 (`candle_prover_inv_state_ok ctxt s /\
   ALL (candle_prover_inv_v_ok ctxt) vs /\
   ALL (candle_prover_inv_v_ok ctxt) vs2 /\
   semanticPrimitives_update_thunk (REVERSE vs)
     (semanticPrimitives_state_refs s) vs2 = SOME refs ==>
     candle_prover_inv_state_ok ctxt (semanticPrimitives_state_refs_fupd
       (K refs) s)`,
  CHEAT_TAC);;

(* HOL4 candle_prover_evaluateScript.sml:682-794: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:796-858: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:860-876: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:878-894: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:896-911: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:913-929: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:931-950: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:952-954: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:956-958: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:960-963: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:965-984: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:986-989: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:991-1007: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:1009-1025: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:1027-1040: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:1042-1070: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:1072-1076: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:1078-1088: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:1090-1097: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:1099-1114: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:1116-1128: a proof *)

(* HOL4 candle_prover_evaluateScript.sml:1130: a proof *)

(* and the interface *)
let _ = unhide_overloads ();;
