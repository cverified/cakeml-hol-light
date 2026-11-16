(* ======================================================== *)
(*  errorLogMonad: ported from HOL4's
    src/monad/more_monads/errorLogMonadScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by panStatic.ml.  *)
(* ======================================================== *)

needs "lib/errorMonad.ml";;

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;

(* HOL4 errorLogMonadScript.sml:5: the type abbreviation M, which the port
   expands *)

(* HOL4 errorLogMonadScript.sml:8: the overload emret, which the port
   expands *)

let return_def = new_definition
  `(errorLogMonad_return (v:'a):('a,'e)errorMonad_error#'w list) =
  (errorMonad_return v,[])`;;

let log_def = new_definition
  `(errorLogMonad_log (m:'l):(1,'e)errorMonad_error#'l list) =
  (errorMonad_return one,[m])`;;

let error_def = new_definition
  `(errorLogMonad_error (e:'e):('a,'e)errorMonad_error#'l list) =
  (errorMonad_error e,[])`;;
