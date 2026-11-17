(* ======================================================== *)
(*  lprefix_lub: ported from HOL4's
    examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 19 files of the port.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: list rich_list llist pred_set option *)

(* HOL4 lprefix_lubScript.sml:171-174: the definition *)

let lprefix_chain_nth_def = new_definition
  `lprefix_chain_nth n ls =
     some (\x. ?l. l IN ls /\ LNTH n l = SOME x)`;;

(* HOL4 lprefix_lubScript.sml:306-310: the definition *)

let build_lprefix_lub_f_def = new_definition
  `build_lprefix_lub_f ls n =
     OPTION_MAP (\x. (n + 1,x)) (lprefix_chain_nth n ls)`;;

let build_lprefix_lub_def = new_definition
  `build_lprefix_lub ls =
     LUNFOLD (build_lprefix_lub_f ls) 0`;;
