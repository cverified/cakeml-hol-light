(* ======================================================== *)
(*  tokens: ported from HOL4's
    semantics/tokensScript.sml  *)
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
hol4_overload "IntT" "tokens_IntT";;
hol4_overload "WordT" "tokens_WordT";;
hol4_overload "CharT" "tokens_CharT";;
