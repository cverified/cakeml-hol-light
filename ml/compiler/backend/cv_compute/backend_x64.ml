(* ======================================================== *)
(*  backend_x64: ported from HOL4's
    compiler/backend/cv_compute/backend_x64Script.sml
    A definition theory, with no definitions and no theorems.
    Needed by backend_x64_cv.ml.  *)
(* ======================================================== *)

(*
  Define x64 specialised backend functions.
*)

(* this file needs nothing of the port *)

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "backend_x64"
  ["asmProps"; "asmSem"; "backend_asm"];;
(* HOL4 ancestors outside the port: x64_target *)


(* HOL4 backend_x64Script.sml:11: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
