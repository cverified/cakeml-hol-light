(* ======================================================== *)
(*  tokenUtils: ported from HOL4's
    semantics/tokenUtilsScript.sml
    A definition theory, with 22 definitions and 3 theorems.  Needed
    by cmlPEG.ml and cmlPtreeConversion.ml.  *)
(* ======================================================== *)

(*
  Utility functions over tokens.
  TODO: perhaps should just appear in tokensTheory.
*)

needs "lib/grammar.ml";;
needs "semantics/tokens.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "tokenUtils"
  ["tokens"];;


let isInt_def = new_definition
  `isInt x1 =
   match x1 with
     tokens_IntT i -> T
   | _ -> F`;;
add_simp isInt_def;;

let isString_def = new_definition
  `isString x1 =
   match x1 with
     tokens_StringT _ -> T
   | _ -> F`;;
add_simp isString_def;;

let isAlphaT_def = new_definition
  `isAlphaT x1 =
   match x1 with
     tokens_AlphaT s -> T
   | _ -> F`;;
add_simp isAlphaT_def;;

let isSymbolT_def = new_definition
  `isSymbolT x1 =
   match x1 with
     tokens_SymbolT s -> T
   | _ -> F`;;
add_simp isSymbolT_def;;

let isAlphaSym_def = new_definition
  `isAlphaSym x1 =
   match x1 with
     tokens_AlphaT _ -> T
   | tokens_SymbolT _ -> T
   | _ -> F`;;
add_simp isAlphaSym_def;;

let isTyvarT_def = new_definition
  `isTyvarT x1 =
   match x1 with
     tokens_TyvarT _ -> T
   | _ -> F`;;
add_simp isTyvarT_def;;

let isWhitespaceT_def = new_definition
  `isWhitespaceT x1 =
     match x1 with
       tokens_WhitespaceT _ -> T
     | _ -> F`;;
add_simp isWhitespaceT_def;;

let isCharT_def = new_definition
  `isCharT x1 =
     match x1 with
       tokens_CharT _ -> T
     | _ -> F`;;
add_simp isCharT_def;;

let isWordT_def = new_definition
  `isWordT x1 =
     match x1 with
       tokens_WordT _ -> T
     | _ -> F`;;
add_simp isWordT_def;;

let isLongidT_def = new_definition
  `isLongidT x1 =
     match x1 with
       tokens_LongidT _ _ -> T
     | _ -> F`;;
add_simp isLongidT_def;;

let destLongidT_def = new_definition
  `destLongidT x1 =
     match x1 with
       tokens_LongidT str s -> SOME (str,s)
     | _ -> NONE`;;
add_simp destLongidT_def;;

let destLongidT_EQ_SOME = prove
 (`destLongidT t = SOME strs <=> (?str s. t = tokens_LongidT str s /\ strs =
  (str,s))`,
  CHEAT_TAC);;
add_simp destLongidT_EQ_SOME;;

let destTyvarPT_def = new_definition
  `destTyvarPT x1 =
     match x1 with
       Lf (grammar_TOK (tokens_TyvarT s),_) -> SOME s
     | _ -> NONE`;;
add_simp destTyvarPT_def;;

let destLf_def = new_definition
  `destLf x1 =
     match x1 with
       Lf (x,_) -> SOME x
     | _ -> NONE`;;
add_simp destLf_def;;

let tokenUtils_destTOK_def = new_definition
  `tokenUtils_destTOK x1 =
     match x1 with
       grammar_TOK t -> SOME t
     | _ -> NONE`;;
add_simp tokenUtils_destTOK_def;;

let destAlphaT_def = new_definition
  `destAlphaT x1 =
     match x1 with
       tokens_AlphaT s -> SOME s
     | _ -> NONE`;;
add_simp destAlphaT_def;;

let destAlphaT_EQ_SOME = prove
 (`destAlphaT t = SOME s <=> t = tokens_AlphaT s`,
  CHEAT_TAC);;
add_simp destAlphaT_EQ_SOME;;

let destSymbolT_def = new_definition
  `destSymbolT x1 =
     match x1 with
       tokens_SymbolT s -> SOME s
     | _ -> NONE`;;
add_simp destSymbolT_def;;

let destSymbolT_EQ_SOME = prove
 (`destSymbolT t = SOME s <=> t = tokens_SymbolT s`,
  CHEAT_TAC);;
add_simp destSymbolT_EQ_SOME;;

let destIntT_def = new_definition
  `destIntT x1 =
     match x1 with
       tokens_IntT i -> SOME i
     | _ -> NONE`;;
add_simp destIntT_def;;

let destCharT_def = new_definition
  `destCharT x1 =
     match x1 with
       tokens_CharT c -> SOME c
     | _ -> NONE`;;
add_simp destCharT_def;;

let destStringT_def = new_definition
  `destStringT x1 =
     match x1 with
       tokens_StringT s -> SOME s
     | _ -> NONE`;;
add_simp destStringT_def;;

let destWordT_def = new_definition
  `destWordT x1 =
     match x1 with
       tokens_WordT w -> SOME w
     | _ -> NONE`;;
add_simp destWordT_def;;

let destFFIT_def = new_definition
  `destFFIT x1 =
     match x1 with
       tokens_FFIT s -> SOME s
     | _ -> NONE`;;
add_simp destFFIT_def;;

let destREPLIDT_def = new_definition
  `destREPLIDT x1 =
     match x1 with
       tokens_REPLIDT s -> SOME s
     | _ -> NONE`;;
add_simp destREPLIDT_def;;

(* and the interface *)
let _ = unhide_overloads ();;
