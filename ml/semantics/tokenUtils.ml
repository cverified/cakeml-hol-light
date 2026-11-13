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

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "tokenUtils"
  ["tokens"];;


let isInt_def = new_definition
  `isInt x1 =
      match x1 with
        (tokens_IntT i:tokens_token) -> T
      | _1 -> F`;;

let isString_def = new_definition
  `isString x1 =
      match x1 with
        tokens_StringT _2 -> T
      | _3 -> F`;;

let isAlphaT_def = new_definition
  `isAlphaT x1 =
      match x1 with
        tokens_AlphaT s -> T
      | _4 -> F`;;

let isSymbolT_def = new_definition
  `isSymbolT x1 =
      match x1 with
        tokens_SymbolT s -> T
      | _5 -> F`;;

let isAlphaSym_def = new_definition
  `isAlphaSym x1 =
      match x1 with
        tokens_AlphaT _6 -> T
      | (tokens_SymbolT _7) -> T
      | _8 -> F`;;

let isTyvarT_def = new_definition
  `isTyvarT x1 =
      match x1 with
        tokens_TyvarT _9 -> T
      | _10 -> F`;;

let isWhitespaceT_def = new_definition
  `isWhitespaceT x1 =
        match x1 with
          tokens_WhitespaceT _11 -> T
        | _12 -> F`;;

let isCharT_def = new_definition
  `isCharT x1 =
        match x1 with
          (tokens_CharT _14:tokens_token) -> T
        | _15 -> F`;;

let isWordT_def = new_definition
  `isWordT x1 =
        match x1 with
          (tokens_WordT _17:tokens_token) -> T
        | _18 -> F`;;

let isLongidT_def = new_definition
  `isLongidT x1 =
        match x1 with
          tokens_LongidT _19 _20 -> T
        | _21 -> F`;;

let destLongidT_def = new_definition
  `destLongidT x1 =
        match x1 with
          tokens_LongidT str s -> SOME (str,s)
        | _22 -> NONE`;;

(* [simp] *)
let destLongidT_EQ_SOME = prove
 (`destLongidT t = SOME strs <=> (?str s. t = tokens_LongidT str s /\
  strs = (str,s))`,
  CHEAT_TAC);;

let destTyvarPT_def = new_definition
  `destTyvarPT x1 =
        match x1 with
          Lf (grammar_TOK (tokens_TyvarT s),_23) -> SOME s
        | _24 -> NONE`;;

let destLf_def = new_definition
  `destLf x1 =
        match x1 with
          Lf (x,_25) -> SOME x
        | _26 -> NONE`;;

let tokenUtils_destTOK_def = new_definition
  `tokenUtils_destTOK x1 =
        match x1 with
          grammar_TOK t -> SOME t
        | _27 -> NONE`;;
hol4_overload "destTOK" "tokenUtils_destTOK";;

let destAlphaT_def = new_definition
  `destAlphaT x1 =
        match x1 with
          tokens_AlphaT s -> SOME s
        | _28 -> NONE`;;

(* [simp] *)
let destAlphaT_EQ_SOME = prove
 (`destAlphaT t = SOME s <=> t = tokens_AlphaT s`,
  CHEAT_TAC);;

let destSymbolT_def = new_definition
  `destSymbolT x1 =
        match x1 with
          tokens_SymbolT s -> SOME s
        | _29 -> NONE`;;

(* [simp] *)
let destSymbolT_EQ_SOME = prove
 (`destSymbolT t = SOME s <=> t = tokens_SymbolT s`,
  CHEAT_TAC);;

let destIntT_def = new_definition
  `destIntT x1 =
        match x1 with
          (tokens_IntT i:tokens_token) -> SOME i
        | _30 -> NONE`;;

let destCharT_def = new_definition
  `destCharT x1 =
        match x1 with
          (tokens_CharT c:tokens_token) -> SOME c
        | _31 -> NONE`;;

let destStringT_def = new_definition
  `destStringT x1 =
        match x1 with
          tokens_StringT s -> SOME s
        | _32 -> NONE`;;

let destWordT_def = new_definition
  `destWordT x1 =
        match x1 with
          (tokens_WordT w:tokens_token) -> SOME w
        | _33 -> NONE`;;

let destFFIT_def = new_definition
  `destFFIT x1 =
        match x1 with
          tokens_FFIT s -> SOME s
        | _34 -> NONE`;;

let destREPLIDT_def = new_definition
  `destREPLIDT x1 =
        match x1 with
          tokens_REPLIDT s -> SOME s
        | _35 -> NONE`;;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
