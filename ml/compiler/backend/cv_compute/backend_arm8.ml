(* ======================================================== *)
(*  backend_arm8: ported from HOL4's
    compiler/backend/cv_compute/backend_arm8Script.sml
    A definition theory, with no definitions and no theorems.
    Needed by backend_arm8_cv.ml.  *)
(* ======================================================== *)

(*
  Define arm8 specialised backend functions.
*)

(* this file needs nothing of the port *)

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "backend_arm8"
  ["asmProps"; "asmSem"; "backend_asm"];;
(* HOL4 ancestors outside the port: arm8_target *)


(* HOL4 backend_arm8Script.sml:11: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
