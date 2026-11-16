(* ======================================================== *)
(*  int_arith: ported from HOL4's
    src/integer/int_arithScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by TextIOProof.ml.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: integer divides arithmetic gcd *)
