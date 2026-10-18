(* ======================================================== *)
(*  NTproperties: ported from HOL4's
    examples/formal-languages/context-free/NTpropertiesScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by cmlNTProps.ml, gramProps.ml and
    pegComplete.ml.  *)
(* ======================================================== *)

needs "lib/grammar.ml";;
(* HOL4 ancestors outside the port: list pred_set *)

let firstSet_def = cake_define
  `firstSet G sf = {t | ?rest. (\G. RTC (derive G)) G sf (grammar_TOK
  t :: rest)}`;;
