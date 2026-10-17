(* ======================================================== *)
(*  errorMonad: ported from HOL4's
    src/monad/more_monads/errorMonadScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

let errorMonad_error_INDUCT,errorMonad_error_RECURSION = define_datatype
  "errorMonad_error = errorMonad_return ('a) | errorMonad_error ('e)";;
hol4_overload "return" "errorMonad_return";;
hol4_overload "error" "errorMonad_error";;
