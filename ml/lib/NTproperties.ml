(* ======================================================== *)
(*  NTproperties: ported from HOL4's
    examples/formal-languages/context-free/NTpropertiesScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

needs "lib/grammar.ml";;
(* HOL4 ancestors outside the port: list pred_set *)

let firstSet_def = cake_define
  `firstSet G sf = {t | ?rest. (\G. RTC (derive G)) G sf (grammar_TOK
  t :: rest)}`;;
