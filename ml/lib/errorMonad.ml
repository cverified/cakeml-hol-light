(* ======================================================== *)
(*  errorMonad: ported from HOL4's
    src/monad/more_monads/errorMonadScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 14 files of the port.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;

let errorMonad_error_INDUCT,errorMonad_error_RECURSION = define_datatype
  "errorMonad_error =
     errorMonad_return ('a)
   | errorMonad_error ('e)";;
