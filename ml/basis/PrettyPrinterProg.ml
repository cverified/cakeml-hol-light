(* ======================================================== *)
(*  PrettyPrinterProg: ported from HOL4's
    basis/PrettyPrinterProgScript.sml
    A definition theory, with 5 definitions and 1 theorem.  Needed
    by RatProg.ml and basisProg.ml.  *)
(* ======================================================== *)

(*
  Module providing pretty-printer implementation, and setup
  of the global builtin pretty-printer functions.
*)

needs "basis/IntProg.ml";;
needs "basis/pure/mlprettyprinter.ml";;
needs "basis/pure/mlstring.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "PrettyPrinterProg"
  ["IntProg"; "ml_prog"; "ml_translator"; "mlprettyprinter"];;

(* HOL4 PrettyPrinterProgScript.sml:13: ML code, not ported *)

(* HOL4 PrettyPrinterProgScript.sml:15-16: ML code, not ported *)

(* HOL4 PrettyPrinterProgScript.sml:18: ML code, not ported *)

(* HOL4 PrettyPrinterProgScript.sml:20-22: ML code, not ported *)

(* HOL4 PrettyPrinterProgScript.sml:24-27: ML code, not ported *)

(* HOL4 PrettyPrinterProgScript.sml:29: ML code, not ported *)

(* HOL4 PrettyPrinterProgScript.sml:31-33: ML code, not ported *)

(* HOL4 PrettyPrinterProgScript.sml:35: ML code, not ported *)

(* [local] *)
let escape_str_app_list_side = prove
 (`!i s. escape_str_app_list_side i s <=> i <= strlen s`,
  CHEAT_TAC);;

(* HOL4 PrettyPrinterProgScript.sml:49: ML code, not ported *)

(* HOL4 PrettyPrinterProgScript.sml:51: ML code, not ported *)

(* HOL4 PrettyPrinterProgScript.sml:53-63: ML code, not ported *)

(* HOL4 PrettyPrinterProgScript.sml:65-66: ML code, not ported *)

(* HOL4 PrettyPrinterProgScript.sml:68-69: ML code, not ported *)

(* HOL4 PrettyPrinterProgScript.sml:71-72: ML code, not ported *)

(* HOL4 PrettyPrinterProgScript.sml:74: ML code, not ported *)

(* HOL4 PrettyPrinterProgScript.sml:76: ML code, not ported *)

(* HOL4 PrettyPrinterProgScript.sml:78: ML code, not ported *)

(* pretty-printers for global (builtin) types, at global scope *)

(* HOL4 PrettyPrinterProgScript.sml:82-84: ML code, not ported *)

(* add global names for some printers, esp. those used in pp_pp_data *)
let rename_pp_list_def = new_definition
  `rename_pp_list = pp_list`;;
(* HOL4 PrettyPrinterProgScript.sml:90: ML code, not ported *)

let rename_pp_bool_def = new_definition
  `rename_pp_bool = pp_bool`;;
(* HOL4 PrettyPrinterProgScript.sml:95: ML code, not ported *)

let rename_pp_char_def = new_definition
  `rename_pp_char = pp_char`;;
(* HOL4 PrettyPrinterProgScript.sml:100: ML code, not ported *)

let rename_pp_string_def = new_definition
  `rename_pp_string = pp_string`;;
(* HOL4 PrettyPrinterProgScript.sml:105: ML code, not ported *)

let rename_pp_app_list_def = new_definition
  `rename_pp_app_list = pp_app_list`;;
(* HOL4 PrettyPrinterProgScript.sml:110: ML code, not ported *)

(* useless pretty-printers for impure types.
   should be replaced later in the basis *)
(* HOL4 PrettyPrinterProgScript.sml:114-116: ML code, not ported *)

(* candle needs constants in the basis to be defined as literals, no funcalls *)
(* HOL4 PrettyPrinterProgScript.sml:119: ML code, not ported *)

(* pretty printers for numeric types *)
(* HOL4 PrettyPrinterProgScript.sml:122-124: ML code, not ported *)

(* setup pretty-printers for previously existing global types *)
(* HOL4 PrettyPrinterProgScript.sml:127: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
