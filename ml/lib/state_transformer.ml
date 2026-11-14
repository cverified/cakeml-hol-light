(* ======================================================== *)
(*  state_transformer: ported from HOL4's
    src/monad/more_monads/state_transformerScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by linear_scan.ml, reg_alloc.ml and
    reg_allocProof.ml.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: pair combin list *)
