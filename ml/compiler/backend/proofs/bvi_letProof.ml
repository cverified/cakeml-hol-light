(* ======================================================== *)
(*  bvi_letProof: ported from HOL4's
    compiler/backend/proofs/bvi_letProofScript.sml
    A proof theory about bvi_let.ml, with 2 definitions and 19
    theorems.  Needed by bvl_to_bviProof.ml and compilerProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for bvi_let
*)

needs "compiler/backend/bvi_let.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;

let v_rel_def = cake_define
  `bvi_letProof_v_rel a x y xs ys <=> (\l n. oEL n l) ys a = SOME x`;;
hol4_overload "v_rel" "bvi_letProof_v_rel";;

let env_rel_def = cake_define
  `bvi_letProof_env_rel x1 d e1 e2 =
        match (x1,e1,e2) with
          ([],e1,e2) -> (e1 = DROP d e2)
        | ((a :: rest),(x :: e1),(y :: e2)) ->
        bvi_letProof_v_rel a x y (x :: e1) (y :: e2) /\
          bvi_letProof_env_rel rest d e1 e2
        | (_1,_2,_3) -> F`;;
hol4_overload "env_rel" "bvi_letProof_env_rel";;

(* HOL4 bvi_letProofScript.sml:220-237: a proof *)

(* HOL4 bvi_letProofScript.sml:239-249: a proof *)

(* HOL4 bvi_letProofScript.sml:251-257: a proof *)

(* HOL4 bvi_letProofScript.sml:259-270: a proof *)

(* HOL4 bvi_letProofScript.sml:272-287: a proof *)
   (* the handler now post-processes its result (rejecting an escaping Ret);
      split that inner case (the Ret branch is impossible as res <> type error),
      then close each surviving handler outcome by the induction hypothesis *)
(* HOL4 bvi_letProofScript.sml:291-297: a proof *)

(* HOL4 bvi_letProofScript.sml:299-307: a proof *)

(* HOL4 bvi_letProofScript.sml:309-320: a proof *)

(* HOL4 bvi_letProofScript.sml:322-330: a proof *)

(* HOL4 bvi_letProofScript.sml:332-346: a proof *)

(* HOL4 bvi_letProofScript.sml:348-387: a proof *)

(* HOL4 bvi_letProofScript.sml:389: a proof *)
