(* ======================================================== *)
(*  tokenUtils: ported from HOL4's
    semantics/tokenUtilsScript.sml  *)
(* ======================================================== *)

(*
  Utility functions over tokens.
  TODO: perhaps should just appear in tokensTheory.
*)

needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "lib/grammar.ml";;
needs "semantics/tokens.ml";;
needs "semantics/typeSystem.ml";;


let isInt_def = cake_define
  `isInt x1 =
      match x1 with
        IntT i -> T
      | _1 -> F`;;

let isString_def = cake_define
  `isString x1 =
      match x1 with
        StringT _2 -> T
      | _3 -> F`;;

let isAlphaT_def = cake_define
  `isAlphaT x1 =
      match x1 with
        AlphaT s -> T
      | _4 -> F`;;

let isSymbolT_def = cake_define
  `isSymbolT x1 =
      match x1 with
        SymbolT s -> T
      | _5 -> F`;;

let isAlphaSym_def = cake_define
  `isAlphaSym x1 =
      match x1 with
        AlphaT _6 -> T
      | (SymbolT _7) -> T
      | _8 -> F`;;

let isTyvarT_def = cake_define
  `isTyvarT x1 =
      match x1 with
        TyvarT _9 -> T
      | _10 -> F`;;

let isWhitespaceT_def = cake_define
  `isWhitespaceT x1 =
        match x1 with
          WhitespaceT _11 -> T
        | _12 -> F`;;

let isCharT_def = cake_define
  `isCharT x1 =
        match x1 with
          CharT _13 -> T
        | _14 -> F`;;

let isWordT_def = cake_define
  `isWordT x1 =
        match x1 with
          WordT _15 -> T
        | _16 -> F`;;

let isLongidT_def = cake_define
  `isLongidT x1 =
        match x1 with
          LongidT _17 _18 -> T
        | _19 -> F`;;

let destLongidT_def = cake_define
  `destLongidT x1 =
        match x1 with
          LongidT str s -> SOME (str,s)
        | _20 -> NONE`;;

let destTyvarPT_def = cake_define
  `destTyvarPT x1 =
        match x1 with
          Lf (TOK (TyvarT s),_21) -> SOME s
        | _22 -> NONE`;;

let destLf_def = cake_define
  `destLf x1 =
        match x1 with
          Lf (x,_23) -> SOME x
        | _24 -> NONE`;;

let destTOK_def = cake_define
  `tokenUtils_destTOK x1 =
        match x1 with
          TOK t -> SOME t
        | _25 -> NONE`;;
hol4_overload "destTOK" "tokenUtils_destTOK";;

let destAlphaT_def = cake_define
  `destAlphaT x1 =
        match x1 with
          AlphaT s -> SOME s
        | _26 -> NONE`;;

let destSymbolT_def = cake_define
  `destSymbolT x1 =
        match x1 with
          SymbolT s -> SOME s
        | _27 -> NONE`;;

let destIntT_def = cake_define
  `destIntT x1 =
        match x1 with
          IntT i -> SOME i
        | _28 -> NONE`;;

let destCharT_def = cake_define
  `destCharT x1 =
        match x1 with
          CharT c -> SOME c
        | _29 -> NONE`;;

let destStringT_def = cake_define
  `destStringT x1 =
        match x1 with
          StringT s -> SOME s
        | _30 -> NONE`;;

let destWordT_def = cake_define
  `destWordT x1 =
        match x1 with
          WordT w -> SOME w
        | _31 -> NONE`;;

let destFFIT_def = cake_define
  `destFFIT x1 =
        match x1 with
          FFIT s -> SOME s
        | _32 -> NONE`;;

let destREPLIDT_def = cake_define
  `destREPLIDT x1 =
        match x1 with
          REPLIDT s -> SOME s
        | _33 -> NONE`;;
