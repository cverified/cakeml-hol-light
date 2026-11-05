(* ======================================================== *)
(*  errorMonad: ported from HOL4's
    src/monad/more_monads/errorMonadScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 14 files of the port.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;

let errorMonad_error_INDUCT,errorMonad_error_RECURSION = define_datatype
  "errorMonad_error = errorMonad_return ('a) | errorMonad_error ('e)";;
hol4_overload "return" "errorMonad_return";;
hol4_overload "error" "errorMonad_error";;
