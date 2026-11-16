(* ======================================================== *)
(*  backend_ag32: ported from HOL4's
    compiler/backend/cv_compute/backend_ag32Script.sml
    A definition theory, with no definitions and no theorems.
    Needed by backend_ag32_cv.ml.  *)
(* ======================================================== *)

(*
  Define ag32 specialised backend functions.
*)

(* this file needs nothing of the port *)

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "backend_ag32"
  ["asmProps"; "asmSem"; "backend_asm"];;
(* HOL4 ancestors outside the port: ag32_target *)


(* HOL4 backend_ag32Script.sml:11: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
