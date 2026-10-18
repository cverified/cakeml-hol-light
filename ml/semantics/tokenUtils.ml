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


let isInt_def = cake_define
  `isInt x1 =
      match x1 with
        (tokens_IntT i:tokens_token) -> T
      | _1 -> F`;;

let isString_def = cake_define
  `isString x1 =
      match x1 with
        tokens_StringT _2 -> T
      | _3 -> F`;;

let isAlphaT_def = cake_define
  `isAlphaT x1 =
      match x1 with
        tokens_AlphaT s -> T
      | _4 -> F`;;

let isSymbolT_def = cake_define
  `isSymbolT x1 =
      match x1 with
        tokens_SymbolT s -> T
      | _5 -> F`;;

let isAlphaSym_def = cake_define
  `isAlphaSym x1 =
      match x1 with
        tokens_AlphaT _6 -> T
      | (tokens_SymbolT _7) -> T
      | _8 -> F`;;

let isTyvarT_def = cake_define
  `isTyvarT x1 =
      match x1 with
        tokens_TyvarT _9 -> T
      | _10 -> F`;;

let isWhitespaceT_def = cake_define
  `isWhitespaceT x1 =
        match x1 with
          tokens_WhitespaceT _11 -> T
        | _12 -> F`;;

let isCharT_def = cake_define
  `isCharT x1 =
        match x1 with
          (tokens_CharT _14:tokens_token) -> T
        | _15 -> F`;;

let isWordT_def = cake_define
  `isWordT x1 =
        match x1 with
          (tokens_WordT _17:tokens_token) -> T
        | _18 -> F`;;

let isLongidT_def = cake_define
  `isLongidT x1 =
        match x1 with
          tokens_LongidT _19 _20 -> T
        | _21 -> F`;;

let destLongidT_def = cake_define
  `destLongidT x1 =
        match x1 with
          tokens_LongidT str s -> SOME (str,s)
        | _22 -> NONE`;;

let destTyvarPT_def = cake_define
  `destTyvarPT x1 =
        match x1 with
          Lf (grammar_TOK (tokens_TyvarT s),_23) -> SOME s
        | _24 -> NONE`;;

let destLf_def = cake_define
  `destLf x1 =
        match x1 with
          Lf (x,_25) -> SOME x
        | _26 -> NONE`;;

let destTOK_def = cake_define
  `tokenUtils_destTOK x1 =
        match x1 with
          grammar_TOK t -> SOME t
        | _27 -> NONE`;;
hol4_overload "destTOK" "tokenUtils_destTOK";;

let destAlphaT_def = cake_define
  `destAlphaT x1 =
        match x1 with
          tokens_AlphaT s -> SOME s
        | _28 -> NONE`;;

let destSymbolT_def = cake_define
  `destSymbolT x1 =
        match x1 with
          tokens_SymbolT s -> SOME s
        | _29 -> NONE`;;

let destIntT_def = cake_define
  `destIntT x1 =
        match x1 with
          (tokens_IntT i:tokens_token) -> SOME i
        | _30 -> NONE`;;

let destCharT_def = cake_define
  `destCharT x1 =
        match x1 with
          (tokens_CharT c:tokens_token) -> SOME c
        | _31 -> NONE`;;

let destStringT_def = cake_define
  `destStringT x1 =
        match x1 with
          tokens_StringT s -> SOME s
        | _32 -> NONE`;;

let destWordT_def = cake_define
  `destWordT x1 =
        match x1 with
          (tokens_WordT w:tokens_token) -> SOME w
        | _33 -> NONE`;;

let destFFIT_def = cake_define
  `destFFIT x1 =
        match x1 with
          tokens_FFIT s -> SOME s
        | _34 -> NONE`;;

let destREPLIDT_def = cake_define
  `destREPLIDT x1 =
        match x1 with
          tokens_REPLIDT s -> SOME s
        | _35 -> NONE`;;
