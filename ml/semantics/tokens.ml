(* ======================================================== *)
(*  tokens: ported from HOL4's
    semantics/tokensScript.sml
    A definition theory, with no definitions, 2 datatypes and no
    theorems.  Needed by gram.ml, lexer_fun.ml, lexer_impl.ml and
    tokenUtils.ml.  *)
(* ======================================================== *)

(*
  The tokens CakeML concrete syntax.
  Some tokens are from Standard ML and not used in CakeML.
*)

needs "basis/pure/mlstring.ml";;
(* HOL4 ancestors outside the port: integer *)

let tokens_path_INDUCT,tokens_path_RECURSION = define_datatype
  "tokens_path = tokens_Mod (mlstring) (tokens_path) | tokens_End";;
hol4_overload "Mod" "tokens_Mod";;
hol4_overload "End" "tokens_End";;

let tokens_token_INDUCT,tokens_token_RECURSION = define_datatype
  "tokens_token = tokens_WhitespaceT (num) | tokens_NewlineT | \
   tokens_LexErrorT | tokens_HashT | tokens_LparT | tokens_RparT | \
   tokens_StarT | tokens_CommaT | tokens_ArrowT | tokens_DotsT | \
   tokens_ColonT | tokens_SealT | tokens_SemicolonT | tokens_EqualsT \
   | tokens_DarrowT | tokens_LbrackT | tokens_RbrackT | \
   tokens_UnderbarT | tokens_LbraceT | tokens_BarT | tokens_RbraceT | \
   tokens_AndT | tokens_AndalsoT | tokens_AsT | tokens_CaseT | \
   tokens_DatatypeT | tokens_ElseT | tokens_EndT | tokens_EqtypeT | \
   tokens_ExceptionT | tokens_FnT | tokens_FunT | tokens_HandleT | \
   tokens_IfT | tokens_InT | tokens_IncludeT | tokens_LetT | \
   tokens_LocalT | tokens_OfT | tokens_OpT | tokens_OpenT | \
   tokens_OrelseT | tokens_RaiseT | tokens_RecT | tokens_SharingT | \
   tokens_SigT | tokens_SignatureT | tokens_StructT | \
   tokens_StructureT | tokens_ThenT | tokens_TypeT | tokens_ValT | \
   tokens_WhereT | tokens_WhileT | tokens_WithT | tokens_WithtypeT | \
   tokens_IntT (int) | tokens_HexintT (mlstring) | tokens_WordT (num) \
   | tokens_RealT (mlstring) | tokens_StringT (mlstring) | \
   tokens_CharT (char) | tokens_TyvarT (mlstring) | tokens_AlphaT \
   (mlstring) | tokens_SymbolT (mlstring) | tokens_LongidT \
   (tokens_path) (mlstring) | tokens_FFIT (mlstring) | tokens_REPLIDT \
   (mlstring)";;
hol4_overload "WhitespaceT" "tokens_WhitespaceT";;
hol4_overload "NewlineT" "tokens_NewlineT";;
hol4_overload "LexErrorT" "tokens_LexErrorT";;
hol4_overload "HashT" "tokens_HashT";;
hol4_overload "LparT" "tokens_LparT";;
hol4_overload "RparT" "tokens_RparT";;
hol4_overload "StarT" "tokens_StarT";;
hol4_overload "CommaT" "tokens_CommaT";;
hol4_overload "ArrowT" "tokens_ArrowT";;
hol4_overload "DotsT" "tokens_DotsT";;
hol4_overload "ColonT" "tokens_ColonT";;
hol4_overload "SealT" "tokens_SealT";;
hol4_overload "SemicolonT" "tokens_SemicolonT";;
hol4_overload "EqualsT" "tokens_EqualsT";;
hol4_overload "DarrowT" "tokens_DarrowT";;
hol4_overload "LbrackT" "tokens_LbrackT";;
hol4_overload "RbrackT" "tokens_RbrackT";;
hol4_overload "UnderbarT" "tokens_UnderbarT";;
hol4_overload "LbraceT" "tokens_LbraceT";;
hol4_overload "BarT" "tokens_BarT";;
hol4_overload "RbraceT" "tokens_RbraceT";;
hol4_overload "AndT" "tokens_AndT";;
hol4_overload "AndalsoT" "tokens_AndalsoT";;
hol4_overload "AsT" "tokens_AsT";;
hol4_overload "CaseT" "tokens_CaseT";;
hol4_overload "DatatypeT" "tokens_DatatypeT";;
hol4_overload "ElseT" "tokens_ElseT";;
hol4_overload "EndT" "tokens_EndT";;
hol4_overload "EqtypeT" "tokens_EqtypeT";;
hol4_overload "ExceptionT" "tokens_ExceptionT";;
hol4_overload "FnT" "tokens_FnT";;
hol4_overload "FunT" "tokens_FunT";;
hol4_overload "HandleT" "tokens_HandleT";;
hol4_overload "IfT" "tokens_IfT";;
hol4_overload "InT" "tokens_InT";;
hol4_overload "IncludeT" "tokens_IncludeT";;
hol4_overload "LetT" "tokens_LetT";;
hol4_overload "LocalT" "tokens_LocalT";;
hol4_overload "OfT" "tokens_OfT";;
hol4_overload "OpT" "tokens_OpT";;
hol4_overload "OpenT" "tokens_OpenT";;
hol4_overload "OrelseT" "tokens_OrelseT";;
hol4_overload "RaiseT" "tokens_RaiseT";;
hol4_overload "RecT" "tokens_RecT";;
hol4_overload "SharingT" "tokens_SharingT";;
hol4_overload "SigT" "tokens_SigT";;
hol4_overload "SignatureT" "tokens_SignatureT";;
hol4_overload "StructT" "tokens_StructT";;
hol4_overload "StructureT" "tokens_StructureT";;
hol4_overload "ThenT" "tokens_ThenT";;
hol4_overload "TypeT" "tokens_TypeT";;
hol4_overload "ValT" "tokens_ValT";;
hol4_overload "WhereT" "tokens_WhereT";;
hol4_overload "WhileT" "tokens_WhileT";;
hol4_overload "WithT" "tokens_WithT";;
hol4_overload "WithtypeT" "tokens_WithtypeT";;
hol4_overload "IntT" "tokens_IntT";;
hol4_overload "HexintT" "tokens_HexintT";;
hol4_overload "WordT" "tokens_WordT";;
hol4_overload "RealT" "tokens_RealT";;
hol4_overload "StringT" "tokens_StringT";;
hol4_overload "CharT" "tokens_CharT";;
hol4_overload "TyvarT" "tokens_TyvarT";;
hol4_overload "AlphaT" "tokens_AlphaT";;
hol4_overload "SymbolT" "tokens_SymbolT";;
hol4_overload "LongidT" "tokens_LongidT";;
hol4_overload "FFIT" "tokens_FFIT";;
hol4_overload "REPLIDT" "tokens_REPLIDT";;
