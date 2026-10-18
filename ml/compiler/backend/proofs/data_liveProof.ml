(* ======================================================== *)
(*  data_liveProof: ported from HOL4's
    compiler/backend/proofs/data_liveProofScript.sml
    A proof theory about data_live.ml, with 1 definition and 14
    theorems.  Needed by bvi_to_dataProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for data_live
*)

needs "compiler/backend/data_live.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "lib/sptree.ml";;

let state_rel_def = cake_define
  `data_liveProof_state_rel (s1:('a,'ffi)dataSem_state)
  (t1:('a,'ffi)dataSem_state) (live:1 spt) <=> state_code
     s1 = state_code t1 /\ state_clock s1 = state_clock t1 /\
       dataSem_state_space s1 = dataSem_state_space t1 /\ state_ffi
     s1 = state_ffi t1 /\ state_refs s1 = state_refs t1 /\
       dataSem_state_global s1 = dataSem_state_global t1 /\
       dataSem_state_handler
     s1 = dataSem_state_handler t1 /\ (LENGTH (stack s1) = LENGTH
       (stack t1)) /\ compile
     s1 = compile t1 /\ compile_oracle s1 = compile_oracle t1 /\
       dataSem_state_tstamps
     s1 = dataSem_state_tstamps t1 /\ dataSem_state_limits
     s1 = dataSem_state_limits t1 /\ dataSem_state_stack_frame_sizes
     s1 = dataSem_state_stack_frame_sizes t1 /\
     (!x. x IN domain live ==> (lookup x (dataSem_state_locals s1)
       = lookup x (dataSem_state_locals t1)))`;;
hol4_overload "state_rel" "data_liveProof_state_rel";;

(* HOL4 data_liveProofScript.sml:53-54: ML code, not ported *)

(* HOL4 data_liveProofScript.sml:212-214: a proof *)

(* HOL4 data_liveProofScript.sml:216-220: a proof *)

(* HOL4 data_liveProofScript.sml:222-289: a proof *)

(* HOL4 data_liveProofScript.sml:291-295: a proof *)

(* HOL4 data_liveProofScript.sml:297-305: a proof *)

(* HOL4 data_liveProofScript.sml:307-315: a proof *)

(* HOL4 data_liveProofScript.sml:317-322: a proof *)

(* HOL4 data_liveProofScript.sml:324-348: a proof *)

(* HOL4 data_liveProofScript.sml:350-372: a proof *)

(* HOL4 data_liveProofScript.sml:374-378: a proof *)

(* HOL4 data_liveProofScript.sml:380-456: a proof *)

(* HOL4 data_liveProofScript.sml:458-472: a proof *)

(* HOL4 data_liveProofScript.sml:474-488: a proof *)

(* HOL4 data_liveProofScript.sml:490-492: a proof *)

(* HOL4 data_liveProofScript.sml:494-538: a proof *)

(* HOL4 data_liveProofScript.sml:540-593: a proof *)

(* HOL4 data_liveProofScript.sml:595-616: a proof *)

(* HOL4 data_liveProofScript.sml:618: a proof *)
  (* Call from here onwards *)
(* HOL4 data_liveProofScript.sml:620-621: a proof *)
  (* Call with SOME ret *)
(* HOL4 data_liveProofScript.sml:623-628: a proof *)

(* HOL4 data_liveProofScript.sml:630-705: a proof *)

(* HOL4 data_liveProofScript.sml:707-847: a proof *)

(* HOL4 data_liveProofScript.sml:849-1002: a proof *)

(* HOL4 data_liveProofScript.sml:1004: a proof *)
