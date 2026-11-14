(* ======================================================== *)
(*  integer_word: ported from HOL4's
    src/integer/integer_wordScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 17 files of the port.  *)
(* ======================================================== *)

needs "lib/ASCIInumbers.ml";;

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: arithmetic bit words integer *)
