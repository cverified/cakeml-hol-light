(* ======================================================== *)
(*  cmlNTProps: ported from HOL4's
    compiler/parsing/proofs/cmlNTPropsScript.sml
    A proof theory, with no definitions and 84 theorems.  Needed by
    pegComplete.ml.  *)
(* ======================================================== *)

(*
  Properties (first sets etc) for non-terminals in the CakeML grammar
*)

needs "basis/pure/mlstring.ml";;
needs "lib/NTproperties.ml";;
needs "semantics/gram.ml";;
needs "semantics/proofs/gramProps.ml";;
needs "semantics/typeSystem.ml";;

let disjImpI = cake_theorem "disjImpI[local]"
  (fun () ->
    `~p \/ q <=> p ==> q`)
  CHEAT_TAC;;

let firstSet_nUQTyOp = cake_theorem "firstSet_nUQTyOp[simp]"
  (fun () ->
    `firstSet cmlG ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nUQTyOp :: rest) =
     {tokens_AlphaT s | T} UNION {tokens_SymbolT s | T}`)
  CHEAT_TAC;;

let firstSet_nTyOp = cake_theorem "firstSet_nTyOp[simp]"
  (fun () ->
    `firstSet cmlG ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nTyOp :: rest) =
     {tokens_AlphaT s | T} UNION {tokens_SymbolT s | T} UNION
       {tokens_LongidT s1 s2 | T}`)
  CHEAT_TAC;;

let firstSet_nPTbase = cake_theorem "firstSet_nPTbase[simp]"
  (fun () ->
    `firstSet cmlG ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nPTbase :: rest) =
     firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nt')) nTyOp] UNION {tokens_LparT} UNION {tokens_TyvarT s | T}`)
  CHEAT_TAC;;

let firstSet_nTbaseList = cake_theorem "firstSet_nTbaseList[simp]"
  (fun () ->
    `firstSet cmlG ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nTbaseList :: rest) =
     firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nt')) nPTbase] UNION firstSet cmlG rest`)
  CHEAT_TAC;;

let firstSet_nTyVarList = cake_theorem "firstSet_nTyVarList[simp]"
  (fun () ->
    `firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nTyVarList)] = {tokens_TyvarT s | T}`)
  CHEAT_TAC;;
(* HOL4 cmlNTPropsScript.sml:57-59: ML code, not ported *)

let firstSet_nLetDec = cake_theorem "firstSet_nLetDec[simp]"
  (fun () ->
    `firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nLetDec)] =
  {tokens_ValT,tokens_FunT}`)
  CHEAT_TAC;;

let firstSet_nLetDecs = cake_theorem "firstSet_nLetDecs[simp]"
  (fun () ->
    `firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nLetDecs)]
  = {tokens_ValT,tokens_FunT,tokens_SemicolonT}`)
  CHEAT_TAC;;

let firstSet_nTypeDec = cake_theorem "firstSet_nTypeDec[simp]"
  (fun () ->
    `firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nTypeDec)]
  = {tokens_DatatypeT}`)
  CHEAT_TAC;;

let firstSet_nTypeAbbrevDec =
  cake_theorem "firstSet_nTypeAbbrevDec[simp]"
  (fun () ->
    `firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nTypeAbbrevDec)] = {tokens_TypeT}`)
  CHEAT_TAC;;

let firstSet_nStructure = cake_theorem "firstSet_nStructure[simp]"
  (fun () ->
    `firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nStructure)] = {tokens_StructureT}`)
  CHEAT_TAC;;

let firstSet_nDecl = cake_theorem "firstSet_nDecl[simp]"
  (fun () ->
    `firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nDecl)] =
     {tokens_ValT,tokens_FunT,tokens_DatatypeT,tokens_ExceptionT
       ,tokens_TypeT,tokens_LocalT,tokens_StructureT}`)
  CHEAT_TAC;;

let firstSet_nDecls = cake_theorem "firstSet_nDecls[simp]"
  (fun () ->
    `firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nDecls] =
     {tokens_ValT,tokens_DatatypeT,tokens_FunT,tokens_SemicolonT
       ,tokens_ExceptionT,tokens_TypeT,tokens_LocalT
       ,tokens_StructureT}`)
  CHEAT_TAC;;

let IMAGE_GSPEC1 = cake_theorem "IMAGE_GSPEC1[local]"
  (fun () ->
    `IMAGE f (hol4_GSPEC (\a. (g a,P a))) = hol4_GSPEC (\a. (f (g a),P
  a))`)
  CHEAT_TAC;;

let BIGUNION_singletons = cake_theorem "BIGUNION_singletons[local,simp]"
  (fun () ->
    `BIGUNION (hol4_GSPEC (\a. {f a},P a)) = hol4_GSPEC (\a. f a,P a)`)
  CHEAT_TAC;;

let firstSet_nMultOps = cake_theorem "firstSet_nMultOps[simp]"
  (fun () ->
    `firstSet cmlG (grammar_NT ((INL:MMLnonT->MMLnonT+num) nMultOps) ::
  rest) =
     {tokens_AlphaT (implode "div"),tokens_AlphaT (implode
       "mod"),tokens_StarT} UNION {tokens_SymbolT s | validMultSym
       (explode s)}`)
  CHEAT_TAC;;

let firstSet_nRelOps = cake_theorem "firstSet_nRelOps[simp]"
  (fun () ->
    `firstSet cmlG (grammar_NT ((INL:MMLnonT->MMLnonT+num) nRelOps) ::
  rest) =
     tokens_EqualsT INSERT {tokens_SymbolT s | validRelSym
       (explode s)}`)
  CHEAT_TAC;;

let firstSet_nAddOps = cake_theorem "firstSet_nAddOps[simp]"
  (fun () ->
    `firstSet cmlG (grammar_NT ((INL:MMLnonT->MMLnonT+num) nAddOps) ::
  rest) = {tokens_SymbolT s | validAddSym (explode s)}`)
  CHEAT_TAC;;

let firstSet_nCompOps = cake_theorem "firstSet_nCompOps[simp]"
  (fun () ->
    `firstSet cmlG (grammar_NT ((INL:MMLnonT->MMLnonT+num) nCompOps)
  :: rest) = {tokens_AlphaT (implode "o"),tokens_SymbolT (implode
  ":=")}`)
  CHEAT_TAC;;

let firstSet_nListOps = cake_theorem "firstSet_nListOps[simp]"
  (fun () ->
    `firstSet cmlG (grammar_NT ((INL:MMLnonT->MMLnonT+num) nListOps)
  :: rest) = {tokens_SymbolT s | validListSym (explode s)}`)
  CHEAT_TAC;;

let firstSet_nSpecLine = cake_theorem "firstSet_nSpecLine[simp]"
  (fun () ->
    `firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nSpecLine)] =
     {tokens_ValT,tokens_DatatypeT,tokens_TypeT
       ,tokens_ExceptionT}`)
  CHEAT_TAC;;

let firstSet_nSpecLineList = cake_theorem "firstSet_nSpecLineList[simp]"
  (fun () ->
    `firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nSpecLineList)] =
     {tokens_ValT,tokens_DatatypeT,tokens_TypeT,tokens_SemicolonT
       ,tokens_ExceptionT}`)
  CHEAT_TAC;;

let firstSet_nV = cake_theorem "firstSet_nV"
  (fun () ->
    `firstSet cmlG ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nV :: rest) =
     {tokens_AlphaT s | ~(s = (implode "")) /\ ~(isUpper (strsub s
       0)) /\ ~(s = (implode "before")) /\ ~(s = (implode "div")) /\ ~(s
       = (implode "mod")) /\ ~(s = (implode "o"))} UNION
                              {tokens_SymbolT s | validPrefixSym
                                (explode s)}`)
  CHEAT_TAC;;

let firstSet_nFQV = cake_theorem "firstSet_nFQV"
  (fun () ->
    `firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nFQV)] =
     firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nV)]
       UNION
              {tokens_LongidT m i | (m,i) | ~(i = (implode ""))
                /\ (isAlpha (strsub i 0) ==> ~(isUpper (strsub i 0)))}`)
  CHEAT_TAC;;

let firstSet_nUQConstructorName =
  cake_theorem "firstSet_nUQConstructorName"
  (fun () ->
    `firstSet cmlG ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nUQConstructorName :: rest) =
     {tokens_AlphaT s | ~(s = (implode "")) /\ isUpper (strsub s
       0)}`)
  CHEAT_TAC;;

let firstSet_nConstructorName = cake_theorem "firstSet_nConstructorName"
  (fun () ->
    `firstSet cmlG ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nConstructorName :: rest) =
     {tokens_LongidT str s | (str,s) | ~(s = (implode "")) /\
       isAlpha (strsub s 0) /\ isUpper (strsub s 0)} UNION
                              {tokens_AlphaT s | ~(s = (implode
                                "")) /\ isUpper (strsub s 0)}`)
  CHEAT_TAC;;

let firstSetML_nConstructorName =
  cake_theorem "firstSetML_nConstructorName[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) ==>
       (firstSetML cmlG sn ((\nt'. grammar_NT
         ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName :: rest) =
        firstSet cmlG [(\nt'. grammar_NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName])`)
  CHEAT_TAC;;

let firstSetML_nV = cake_theorem "firstSetML_nV[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nV IN sn) ==>
       (firstSetML cmlG sn ((\nt'. grammar_NT
         ((INL:MMLnonT->MMLnonT+num) nt')) nV :: rest) = firstSet cmlG
         [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nV])`)
  CHEAT_TAC;;

let firstSetML_nFQV = cake_theorem "firstSetML_nFQV[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) ==>
       (firstSetML cmlG sn ((\nt'. grammar_NT
         ((INL:MMLnonT->MMLnonT+num) nt')) nFQV :: rest) = firstSet
         cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
         nFQV])`)
  CHEAT_TAC;;

let firstSet_nEtuple = cake_theorem "firstSet_nEtuple[simp]"
  (fun () ->
    `firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEtuple)] =
  {tokens_LparT}`)
  CHEAT_TAC;;

let firstSet_nEliteral = cake_theorem "firstSet_nEliteral[simp]"
  (fun () ->
    `firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEliteral)] =
     {tokens_IntT i | T} UNION {tokens_StringT s | T} UNION
       {tokens_CharT c | T} UNION {tokens_WordT w | T} UNION
                  {tokens_FFIT s | T}`)
  CHEAT_TAC;;

let firstSetML_nEliteral = cake_theorem "firstSetML_nEliteral[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nEliteral IN sn) ==>
       firstSetML cmlG sn (grammar_NT ((INL:MMLnonT->MMLnonT+num)
         nEliteral) :: rest) =
       firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
         nEliteral)]`)
  CHEAT_TAC;;

let firstSet_nEbase = cake_theorem "firstSet_nEbase[simp]"
  (fun () ->
    `firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEbase)] =
     {tokens_LetT,tokens_LparT,tokens_LbrackT,tokens_OpT} UNION
       firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nFQV)]
       UNION
                              firstSet cmlG [grammar_NT
                                ((INL:MMLnonT->MMLnonT+num) nEliteral)]
                                UNION
                              firstSet cmlG [grammar_NT
                                ((INL:MMLnonT->MMLnonT+num)
                                nConstructorName)]`)
  CHEAT_TAC;;

let firstSetML_nEbase = cake_theorem "firstSetML_nEbase[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nEliteral IN sn) ==>
       firstSetML cmlG sn (grammar_NT ((INL:MMLnonT->MMLnonT+num)
         nEbase) :: rest) =
       firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
         nEbase)]`)
  CHEAT_TAC;;

let firstSet_nEapp = cake_theorem "firstSet_nEapp[simp]"
  (fun () ->
    `firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEapp)] =
  firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEbase)]`)
  CHEAT_TAC;;

let firstSetML_nEapp = cake_theorem "firstSetML_nEapp[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nEapp IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nEliteral IN sn) ==>
     firstSetML cmlG sn (grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nEapp) :: rest) =
     firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nEbase)]`)
  CHEAT_TAC;;

let firstSet_nEmult = cake_theorem "firstSet_nEmult[simp]"
  (fun () ->
    `firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEmult)] =
  firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEbase)]`)
  CHEAT_TAC;;

let firstSetML_nEmult = cake_theorem "firstSetML_nEmult[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nEapp IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nEmult IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEliteral IN sn) ==>
     firstSetML cmlG sn (grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nEmult) :: rest) =
     firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nEbase)]`)
  CHEAT_TAC;;

let firstSet_nEadd = cake_theorem "firstSet_nEadd[simp]"
  (fun () ->
    `firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEadd)] =
  firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEbase)]`)
  CHEAT_TAC;;

let firstSetML_nEadd = cake_theorem "firstSetML_nEadd[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nEapp IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nEmult IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEadd IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEliteral IN sn) ==>
       firstSetML cmlG sn (grammar_NT ((INL:MMLnonT->MMLnonT+num)
         nEadd) :: rest) =
       firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
         nEbase)]`)
  CHEAT_TAC;;

let firstSet_nElistop = cake_theorem "firstSet_nElistop[simp]"
  (fun () ->
    `firstSet cmlG (grammar_NT ((INL:MMLnonT->MMLnonT+num) nElistop) ::
  rest) =
     firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nEbase)]`)
  CHEAT_TAC;;

let firstSetML_nElistop = cake_theorem "firstSetML_nElistop[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nEapp IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nEmult IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEadd IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nElistop IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEliteral IN sn) ==>
     firstSetML cmlG sn (grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nElistop) :: rest) =
     firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nEbase)]`)
  CHEAT_TAC;;

let firstSet_nErel = cake_theorem "firstSet_nErel[simp]"
  (fun () ->
    `firstSet cmlG (grammar_NT ((INL:MMLnonT->MMLnonT+num) nErel) ::
  rest) = firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nEbase)]`)
  CHEAT_TAC;;

let firstSetML_nErel = cake_theorem "firstSetML_nErel[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nEapp IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nEmult IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEadd IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nErel IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nElistop IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEliteral IN sn) ==>
     firstSetML cmlG sn (grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nErel) :: rest) = firstSet cmlG [(\nt'. grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nt')) nEbase]`)
  CHEAT_TAC;;

let firstSet_nEcomp = cake_theorem "firstSet_nEcomp[simp]"
  (fun () ->
    `firstSet cmlG (grammar_NT ((INL:MMLnonT->MMLnonT+num) nEcomp) ::
  rest) = firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nEbase)]`)
  CHEAT_TAC;;

let firstSetML_nEcomp = cake_theorem "firstSetML_nEcomp[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nEapp IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nEmult IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEadd IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nErel IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEcomp IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nElistop IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEliteral IN sn) ==>
       firstSetML cmlG sn (grammar_NT ((INL:MMLnonT->MMLnonT+num)
         nEcomp) :: rest) = firstSet cmlG [(\nt'. grammar_NT
         ((INL:MMLnonT->MMLnonT+num) nt')) nEbase]`)
  CHEAT_TAC;;

let firstSet_nEbefore = cake_theorem "firstSet_nEbefore[simp]"
  (fun () ->
    `firstSet cmlG (grammar_NT ((INL:MMLnonT->MMLnonT+num) nEbefore) ::
  rest) =
     firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nEbase)]`)
  CHEAT_TAC;;

let firstSetML_nEbefore = cake_theorem "firstSetML_nEbefore[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nEapp IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nEmult IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEadd IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nErel IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEcomp IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbefore IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nElistop IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEliteral IN sn) ==>
       firstSetML cmlG sn (grammar_NT ((INL:MMLnonT->MMLnonT+num)
         nEbefore) :: rest) = firstSet cmlG [(\nt'. grammar_NT
         ((INL:MMLnonT->MMLnonT+num) nt')) nEbase]`)
  CHEAT_TAC;;

let firstSet_nEtyped = cake_theorem "firstSet_nEtyped[simp]"
  (fun () ->
    `firstSet cmlG (grammar_NT ((INL:MMLnonT->MMLnonT+num) nEtyped) ::
  rest) = firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nEbase)]`)
  CHEAT_TAC;;

let firstSetML_nEtyped = cake_theorem "firstSetML_nEtyped[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nEapp IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nEmult IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEadd IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nErel IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEcomp IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbefore IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEtyped IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nElistop IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEliteral IN sn) ==>
     firstSetML cmlG sn (grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nEtyped) :: rest) = firstSet cmlG [(\nt'. grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nt')) nEbase]`)
  CHEAT_TAC;;

let firstSet_nElogicAND = cake_theorem "firstSet_nElogicAND[simp]"
  (fun () ->
    `firstSet cmlG (grammar_NT ((INL:MMLnonT->MMLnonT+num) nElogicAND)
  :: rest) = firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nEbase)]`)
  CHEAT_TAC;;

let firstSetML_nElogicAND = cake_theorem "firstSetML_nElogicAND[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nEapp IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nEmult IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEadd IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nErel IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEcomp IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbefore IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEtyped IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nElogicAND IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nElistop IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEliteral IN sn) ==>
     firstSetML cmlG sn (grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nElogicAND) :: rest) =
     firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nt')) nEbase]`)
  CHEAT_TAC;;

let firstSet_nElogicOR = cake_theorem "firstSet_nElogicOR[simp]"
  (fun () ->
    `firstSet cmlG (grammar_NT ((INL:MMLnonT->MMLnonT+num) nElogicOR)
  :: rest) = firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nEbase)]`)
  CHEAT_TAC;;

let firstSetML_nElogicOR = cake_theorem "firstSetML_nElogicOR[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nEapp IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nEmult IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEadd IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nErel IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEcomp IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbefore IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEtyped IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nElogicAND IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nElogicOR IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nElistop IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEliteral IN sn) ==>
     firstSetML cmlG sn (grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nElogicOR) :: rest) =
     firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nt')) nEbase]`)
  CHEAT_TAC;;

let firstSet_nEhandle = cake_theorem "firstSet_nEhandle[simp]"
  (fun () ->
    `firstSet cmlG (grammar_NT ((INL:MMLnonT->MMLnonT+num) nEhandle)
  :: rest) = firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nEbase)]`)
  CHEAT_TAC;;

let firstSetML_nEhandle = cake_theorem "firstSetML_nEhandle[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nEapp IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nEmult IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEadd IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nErel IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEcomp IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbefore IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEtyped IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nElogicAND IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nElogicOR IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEhandle IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nElistop IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEliteral IN sn) ==>
     firstSetML cmlG sn (grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nEhandle) :: rest) =
     firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nt')) nEbase]`)
  CHEAT_TAC;;

let firstSet_nE = cake_theorem "firstSet_nE"
  (fun () ->
    `firstSet cmlG (grammar_NT ((INL:MMLnonT->MMLnonT+num) nE) :: rest)
  =
     firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nEbase)] UNION
       {tokens_IfT,tokens_CaseT,tokens_FnT,tokens_RaiseT}`)
  CHEAT_TAC;;

let firstSet_nTopLevelDecs = cake_theorem "firstSet_nTopLevelDecs[simp]"
  (fun () ->
    `firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nTopLevelDecs] =
     {tokens_ValT,tokens_FunT,tokens_SemicolonT,tokens_DatatypeT
       ,tokens_StructureT,tokens_ExceptionT,tokens_TypeT,
      tokens_LocalT} UNION
              firstSet cmlG [grammar_NT
                ((INL:MMLnonT->MMLnonT+num) nE)]`)
  CHEAT_TAC;;

let firstSet_nNonETopLevelDecs =
  cake_theorem "firstSet_nNonETopLevelDecs[simp]"
  (fun () ->
    `firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nNonETopLevelDecs] =
     {tokens_ValT,tokens_FunT,tokens_SemicolonT,tokens_DatatypeT
       ,tokens_StructureT,tokens_ExceptionT,tokens_TypeT,
      tokens_LocalT}`)
  CHEAT_TAC;;

let firstSet_nEseq = cake_theorem "firstSet_nEseq[simp]"
  (fun () ->
    `firstSet cmlG ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nEseq :: rest) = firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nE]`)
  CHEAT_TAC;;

let NOTIN_firstSet_nE = cake_theorem "NOTIN_firstSet_nE[simp]"
  (fun () ->
    `~(tokens_ValT IN firstSet cmlG (grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nE) :: rest)) /\ ~(tokens_StructureT IN
  firstSet cmlG (grammar_NT ((INL:MMLnonT->MMLnonT+num) nE) :: rest))
  /\ ~(tokens_FunT IN firstSet cmlG (grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nE) :: rest)) /\ ~(tokens_DatatypeT IN
  firstSet cmlG (grammar_NT ((INL:MMLnonT->MMLnonT+num) nE) :: rest))
  /\ ~(tokens_ExceptionT IN firstSet cmlG (grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nE) :: rest)) /\ ~(tokens_SemicolonT IN
  firstSet cmlG (grammar_NT ((INL:MMLnonT->MMLnonT+num) nE) :: rest))
  /\ ~(tokens_RparT IN firstSet cmlG ((\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nE :: rest)) /\ ~(tokens_RbrackT
  IN firstSet cmlG ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nE :: rest)) /\ ~(tokens_TypeT IN firstSet cmlG ((\nt'.
  grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nE :: rest))`)
  CHEAT_TAC;;

let firstSetML_nE = cake_theorem "firstSetML_nE[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nEapp IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nEmult IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEadd IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nErel IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEcomp IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbefore IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEtyped IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nElogicAND IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nElogicOR IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEhandle IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nE IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nElistop IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nEliteral IN sn) ==>
       firstSetML cmlG sn (grammar_NT ((INL:MMLnonT->MMLnonT+num)
         nE) :: rest) = firstSet cmlG [(\nt'. grammar_NT
         ((INL:MMLnonT->MMLnonT+num) nt')) nE]`)
  CHEAT_TAC;;

let firstSet_nElist1 = cake_theorem "firstSet_nElist1[simp]"
  (fun () ->
    `firstSet cmlG (grammar_NT ((INL:MMLnonT->MMLnonT+num) nElist1) ::
  rest) = firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nE)]`)
  CHEAT_TAC;;

let firstSet_nElist2 = cake_theorem "firstSet_nElist2[simp]"
  (fun () ->
    `firstSet cmlG (grammar_NT ((INL:MMLnonT->MMLnonT+num) nElist2) ::
  rest) = firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nE)]`)
  CHEAT_TAC;;

let firstSetML_nPtuple = cake_theorem "firstSetML_nPtuple[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nPtuple IN sn) ==> (firstSetML cmlG
  sn ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nPtuple ::
  rest) = {tokens_LparT})`)
  CHEAT_TAC;;

let firstSet_nPtuple = cake_theorem "firstSet_nPtuple[simp]"
  (fun () ->
    `firstSet cmlG ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nPtuple :: rest) = {tokens_LparT}`)
  CHEAT_TAC;;

let firstSet_nPbase = cake_theorem "firstSet_nPbase[simp]"
  (fun () ->
    `firstSet cmlG ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nPbase :: rest) =
     {tokens_LparT,tokens_UnderbarT,tokens_LbrackT,tokens_OpT}
       UNION {tokens_IntT i | T} UNION {tokens_StringT s | T} UNION
                              {tokens_CharT c | T} UNION
                              firstSet cmlG [(\nt'. grammar_NT
                                ((INL:MMLnonT->MMLnonT+num) nt'))
                                nConstructorName] UNION firstSet cmlG
                                [(\nt'. grammar_NT
                                ((INL:MMLnonT->MMLnonT+num) nt')) nV]`)
  CHEAT_TAC;;

let firstSetML_nPbase = cake_theorem "firstSetML_nPbase[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nPbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nConstructorName IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nUQConstructorName IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nPtuple IN
  sn) ==>
       firstSetML cmlG sn ((\nt'. grammar_NT
         ((INL:MMLnonT->MMLnonT+num) nt')) nPbase :: rest) = firstSet
         cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
         nPbase]`)
  CHEAT_TAC;;

let firstSet_nPConApp = cake_theorem "firstSet_nPConApp[simp]"
  (fun () ->
    `firstSet cmlG ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nPConApp :: rest) =
     firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nt')) nConstructorName]`)
  CHEAT_TAC;;

let firstSetML_nPConApp = cake_theorem "firstSetML_nPConApp[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nPConApp IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) ==>
       firstSetML cmlG sn ((\nt'. grammar_NT
         ((INL:MMLnonT->MMLnonT+num) nt')) nPConApp :: rest) =
       firstSet cmlG [(\nt'. grammar_NT
         ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]`)
  CHEAT_TAC;;

let firstSet_nPapp = cake_theorem "firstSet_nPapp[simp]"
  (fun () ->
    `firstSet cmlG ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nPapp :: rest) = firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nPbase]`)
  CHEAT_TAC;;

let firstSetML_nPapp = cake_theorem "firstSetML_nPapp[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nPbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nConstructorName IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nUQConstructorName IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nPtuple IN
  sn) /\ ~((INL:MMLnonT->MMLnonT+num) nPapp IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nPConApp IN sn) ==>
       firstSetML cmlG sn ((\nt'. grammar_NT
         ((INL:MMLnonT->MMLnonT+num) nt')) nPapp :: rest) = firstSet
         cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
         nPbase]`)
  CHEAT_TAC;;

let firstSet_nPcons = cake_theorem "firstSet_nPcons[simp]"
  (fun () ->
    `firstSet cmlG ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nPcons :: rest) = firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nPbase]`)
  CHEAT_TAC;;

let firstSetML_nPcons = cake_theorem "firstSetML_nPcons[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nPbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nConstructorName IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nUQConstructorName IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nPtuple IN
  sn) /\ ~((INL:MMLnonT->MMLnonT+num) nPapp IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nPcons IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nPConApp IN sn) ==>
       firstSetML cmlG sn ((\nt'. grammar_NT
         ((INL:MMLnonT->MMLnonT+num) nt')) nPcons :: rest) = firstSet
         cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
         nPbase]`)
  CHEAT_TAC;;

let firstSet_nPas = cake_theorem "firstSet_nPas[simp]"
  (fun () ->
    `firstSet cmlG ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nPas :: rest) = firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nPbase]`)
  CHEAT_TAC;;

let firstSetML_nPas = cake_theorem "firstSetML_nPas[simp]"
  (fun () ->
    `~((INL:MMLnonT->MMLnonT+num) nPbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nConstructorName IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nUQConstructorName IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nPtuple IN
  sn) /\ ~((INL:MMLnonT->MMLnonT+num) nPapp IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nPcons IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nPConApp IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nPas IN sn) ==>
       firstSetML cmlG sn ((\nt'. grammar_NT
         ((INL:MMLnonT->MMLnonT+num) nt')) nPas :: rest) = firstSet
         cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
         nPbase]`)
  CHEAT_TAC;;

let firstSet_nPattern = cake_theorem "firstSet_nPattern[simp]"
  (fun () ->
    `firstSet cmlG ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nPattern :: rest) = firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nPbase]`)
  CHEAT_TAC;;

let firstSet_nPatternList = cake_theorem "firstSet_nPatternList[simp]"
  (fun () ->
    `firstSet cmlG ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nPatternList :: rest) = firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nPattern]`)
  CHEAT_TAC;;

let firstSet_nPbaseList1 = cake_theorem "firstSet_nPbaseList1[simp]"
  (fun () ->
    `firstSet cmlG ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nPbaseList1 :: rest) = firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nPbase]`)
  CHEAT_TAC;;

let firstSet_nPEsfx = cake_theorem "firstSet_nPEsfx[simp]"
  (fun () ->
    `firstSet cmlG ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nPEsfx :: rest) =
     tokens_BarT INSERT tokens_HandleT INSERT firstSet cmlG rest`)
  CHEAT_TAC;;

let NOTIN_firstSet_nV = cake_theorem "NOTIN_firstSet_nV[simp]"
  (fun () ->
    `~(tokens_CommaT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\ ~(tokens_LparT IN firstSet
  cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\
  ~(tokens_RparT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\ ~(tokens_UnderbarT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nV]) /\ ~(tokens_BarT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\ ~(tokens_OpT IN firstSet
  cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\
  ~(tokens_FnT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\ ~(tokens_IfT IN firstSet
  cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\
  ~(tokens_EqualsT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\ ~(tokens_DarrowT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nV]) /\ ~(tokens_ValT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\ ~(tokens_ExceptionT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nV]) /\ ~(tokens_EndT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\ ~(tokens_AndT IN firstSet
  cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\
  ~(tokens_FFIT s IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\ ~(tokens_FunT IN firstSet
  cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\
  ~(tokens_LbrackT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\ ~(tokens_LocalT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nV]) /\ ~(tokens_RbrackT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\ ~(tokens_InT IN firstSet
  cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\
  ~(tokens_IntT i IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\ ~(tokens_StringT s IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nV]) /\ ~(tokens_CharT c IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\ ~(tokens_ThenT IN firstSet
  cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\
  ~(tokens_ElseT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\ ~(tokens_CaseT IN firstSet
  cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\
  ~(tokens_LetT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\ ~(tokens_OfT IN firstSet
  cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\
  ~(tokens_RaiseT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\ ~(tokens_DatatypeT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nV]) /\ ~(tokens_TypeT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\ ~(tokens_SemicolonT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nV]) /\ ~(tokens_ColonT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\ ~(tokens_StructureT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nV]) /\ ~(tokens_WordT w IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\ ~(tokens_SymbolT (implode
  "::") IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nV]) /\ ~(tokens_HandleT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nV])`)
  CHEAT_TAC;;

let NOTIN_firstSet_nFQV = cake_theorem "NOTIN_firstSet_nFQV[simp]"
  (fun () ->
    `~(tokens_AndT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\ ~(tokens_BarT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nFQV]) /\ ~(tokens_CaseT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\ ~(tokens_CharT c IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nFQV]) /\ ~(tokens_ColonT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\ ~(tokens_CommaT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nFQV]) /\ ~(tokens_DarrowT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\ ~(tokens_DatatypeT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nFQV]) /\ ~(tokens_ElseT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\ ~(tokens_EndT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nFQV]) /\ ~(tokens_EqualsT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\ ~(tokens_ExceptionT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nFQV]) /\ ~(tokens_FFIT s IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\ ~(tokens_FnT IN firstSet
  cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\
  ~(tokens_FunT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\ ~(tokens_IfT IN firstSet
  cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\
  ~(tokens_InT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\ ~(tokens_IntT i IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nFQV]) /\ ~(tokens_LbrackT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\ ~(tokens_LetT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nFQV]) /\ ~(tokens_LocalT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\ ~(tokens_LparT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nFQV]) /\ ~(tokens_OfT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\ ~(tokens_OpT IN firstSet
  cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\
  ~(tokens_RaiseT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\ ~(tokens_RbrackT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nFQV]) /\ ~(tokens_RparT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\ ~(tokens_SemicolonT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nFQV]) /\ ~(tokens_StringT s IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\ ~(tokens_StructureT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nFQV]) /\ ~(tokens_ThenT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\ ~(tokens_TypeT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nFQV]) /\ ~(tokens_UnderbarT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\ ~(tokens_ValT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nFQV]) /\ ~(tokens_WordT w IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nFQV]) /\ ~(tokens_HandleT IN
  firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nV])`)
  CHEAT_TAC;;

let NOTIN_firstSet_nConstructorName =
  cake_theorem "NOTIN_firstSet_nConstructorName[simp]"
  (fun () ->
    `~(tokens_AndT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_BarT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_ColonT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_CaseT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_CharT c IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_CommaT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_DarrowT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_DatatypeT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_ElseT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_EndT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_EqualsT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_ExceptionT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_FFIT s IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\ ~(tokens_FnT
  IN firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nConstructorName]) /\ ~(tokens_FunT IN firstSet cmlG [(\nt'.
  grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_IfT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\ ~(tokens_InT
  IN firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nConstructorName]) /\ ~(tokens_IntT i IN firstSet cmlG [(\nt'.
  grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_LbrackT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_LetT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_LocalT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_LparT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\ ~(tokens_OfT
  IN firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nConstructorName]) /\ ~(tokens_OpT IN firstSet cmlG [(\nt'.
  grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_RaiseT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_RbrackT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_RparT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_SemicolonT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_StringT s IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_StructureT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_SymbolT (implode "::") IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_SymbolT (implode "ref") IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_ThenT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_TypeT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_UnderbarT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_ValT IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName]) /\
  ~(tokens_WordT w IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName])`)
  CHEAT_TAC;;

let firstSets_nV_nConstructorName =
  cake_theorem "firstSets_nV_nConstructorName"
  (fun () ->
    `~(t IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName] /\ t IN firstSet
  cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nV])`)
  CHEAT_TAC;;
