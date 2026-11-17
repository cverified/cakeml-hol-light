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
needs "lib/peg.ml";;
needs "semantics/gram.ml";;
needs "semantics/proofs/gramProps.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "cmlNTProps"
  ["gram"; "gramProps"];;

(* [local] *)
let disjImpI = prove
 (`~p \/ q <=> p ==> q`,
  CHEAT_TAC);;

let firstSet_nUQTyOp = prove
 (`firstSet cmlG (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nUQTyOp) rest) =
   {tokens_AlphaT s | T} UNION {tokens_SymbolT s | T}`,
  CHEAT_TAC);;
add_simp firstSet_nUQTyOp;;

let firstSet_nTyOp = prove
 (`firstSet cmlG (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nTyOp) rest) =
   {tokens_AlphaT s | T} UNION {tokens_SymbolT s | T} UNION
     {tokens_LongidT s1 s2 | T}`,
  CHEAT_TAC);;
add_simp firstSet_nTyOp;;

let firstSet_nPTbase = prove
 (`firstSet cmlG (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nPTbase) rest) =
   firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
     gram_nTyOp] UNION {tokens_LparT} UNION {tokens_TyvarT s | T}`,
  CHEAT_TAC);;
add_simp firstSet_nPTbase;;

let firstSet_nTbaseList = prove
 (`firstSet cmlG (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nTbaseList) rest) =
   firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
     gram_nPTbase] UNION firstSet cmlG rest`,
  CHEAT_TAC);;
add_simp firstSet_nTbaseList;;

let firstSet_nTyVarList = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nTyVarList)] =
  {tokens_TyvarT s | T}`,
  CHEAT_TAC);;
add_simp firstSet_nTyVarList;;
(* HOL4 cmlNTPropsScript.sml:57-59: ML code, not ported *)

let firstSet_nLetDec = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nLetDec)] =
  {tokens_ValT,tokens_FunT}`,
  CHEAT_TAC);;
add_simp firstSet_nLetDec;;

let firstSet_nLetDecs = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nLetDecs)] =
  {tokens_ValT,tokens_FunT,tokens_SemicolonT}`,
  CHEAT_TAC);;
add_simp firstSet_nLetDecs;;

let firstSet_nTypeDec = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nTypeDec)] =
  {tokens_DatatypeT}`,
  CHEAT_TAC);;
add_simp firstSet_nTypeDec;;

let firstSet_nTypeAbbrevDec = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
  gram_nTypeAbbrevDec)] = {tokens_TypeT}`,
  CHEAT_TAC);;
add_simp firstSet_nTypeAbbrevDec;;

let firstSet_nStructure = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nStructure)] =
  {tokens_StructureT}`,
  CHEAT_TAC);;
add_simp firstSet_nStructure;;

let firstSet_nDecl = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nDecl)] =
   {tokens_ValT,tokens_FunT,tokens_DatatypeT,tokens_ExceptionT
     ,tokens_TypeT,tokens_LocalT,tokens_StructureT}`,
  CHEAT_TAC);;
add_simp firstSet_nDecl;;

let firstSet_nDecls = prove
 (`firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nDecls] =
   {tokens_ValT,tokens_DatatypeT,tokens_FunT,tokens_SemicolonT
     ,tokens_ExceptionT,tokens_TypeT,tokens_LocalT,tokens_StructureT}`,
  CHEAT_TAC);;
add_simp firstSet_nDecls;;

(* [local] *)
let IMAGE_GSPEC1 = prove
 (`IMAGE f {g a | P a} = {f (g a) | P a}`,
  CHEAT_TAC);;

(* [local] *)
let BIGUNION_singletons = prove
 (`UNIONS {{f a} | P a} = {f a | P a}`,
  CHEAT_TAC);;
add_simp BIGUNION_singletons;;

let firstSet_nMultOps = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nMultOps))
  rest) =
   {tokens_AlphaT (implode "div"),tokens_AlphaT (implode
     "mod"),tokens_StarT} UNION {tokens_SymbolT s | validMultSym (explode s)}`,
  CHEAT_TAC);;
add_simp firstSet_nMultOps;;

let firstSet_nRelOps = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nRelOps))
  rest) =
   tokens_EqualsT INSERT {tokens_SymbolT s | validRelSym (explode s)}`,
  CHEAT_TAC);;
add_simp firstSet_nRelOps;;

let firstSet_nAddOps = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nAddOps))
  rest) = {tokens_SymbolT s | validAddSym (explode s)}`,
  CHEAT_TAC);;
add_simp firstSet_nAddOps;;

let firstSet_nCompOps = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
  gram_nCompOps)) rest) = {tokens_AlphaT (implode "o"),tokens_SymbolT
  (implode ":=")}`,
  CHEAT_TAC);;
add_simp firstSet_nCompOps;;

let firstSet_nListOps = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
  gram_nListOps)) rest) = {tokens_SymbolT s | validListSym (explode s)}`,
  CHEAT_TAC);;
add_simp firstSet_nListOps;;

let firstSet_nSpecLine = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nSpecLine)] =
   {tokens_ValT,tokens_DatatypeT,tokens_TypeT,tokens_ExceptionT}`,
  CHEAT_TAC);;
add_simp firstSet_nSpecLine;;

let firstSet_nSpecLineList = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nSpecLineList)] =
   {tokens_ValT,tokens_DatatypeT,tokens_TypeT,tokens_SemicolonT
     ,tokens_ExceptionT}`,
  CHEAT_TAC);;
add_simp firstSet_nSpecLineList;;

let firstSet_nV = prove
 (`firstSet cmlG (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nV) rest) =
   {tokens_AlphaT s | ~(s = (implode "")) /\ ~(isUpper (strsub s 0)) /\ ~(s
     = (implode "before")) /\ ~(s = (implode "div")) /\ ~(s = (implode "mod"))
     /\ ~(s = (implode "o"))} UNION
                              {tokens_SymbolT s | gram_validPrefixSym
                                (explode s)}`,
  CHEAT_TAC);;

let firstSet_nFQV = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nFQV)] =
   firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nV)] UNION
            {tokens_LongidT m i | (m,i) | ~(i = (implode "")) /\ (isAlpha
              (strsub i 0) ==> ~(isUpper (strsub i 0)))}`,
  CHEAT_TAC);;

let firstSet_nUQConstructorName = prove
 (`firstSet cmlG (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nUQConstructorName) rest) =
   {tokens_AlphaT s | ~(s = (implode "")) /\ isUpper (strsub s 0)}`,
  CHEAT_TAC);;

let firstSet_nConstructorName = prove
 (`firstSet cmlG (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nConstructorName) rest) =
   {tokens_LongidT str s | (str,s) | ~(s = (implode "")) /\ isAlpha (strsub
     s 0) /\ isUpper (strsub s 0)} UNION
                              {tokens_AlphaT s | ~(s = (implode ""))
                                /\ isUpper (strsub s 0)}`,
  CHEAT_TAC);;

let firstSetML_nConstructorName = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nUQConstructorName IN sn) ==>
     (firstSetML cmlG sn (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nt)) gram_nConstructorName) rest) =
      firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
        gram_nConstructorName])`,
  CHEAT_TAC);;
add_simp firstSetML_nConstructorName;;

let firstSetML_nV = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nV IN sn) ==>
     (firstSetML cmlG sn (CONS ((\nt. grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV) rest) = firstSet cmlG [(\nt.
       grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])`,
  CHEAT_TAC);;
add_simp firstSetML_nV;;

let firstSetML_nFQV = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nFQV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nV IN sn) ==>
     (firstSetML cmlG sn (CONS ((\nt. grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV) rest) = firstSet cmlG
       [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV])`,
  CHEAT_TAC);;
add_simp firstSetML_nFQV;;

let firstSet_nEtuple = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEtuple)] =
  {tokens_LparT}`,
  CHEAT_TAC);;
add_simp firstSet_nEtuple;;

let firstSet_nEliteral = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEliteral)] =
   {tokens_IntT i | T} UNION {tokens_StringT s | T} UNION {tokens_CharT c |
     T} UNION {tokens_WordT w | T} UNION
                {tokens_FFIT s | T}`,
  CHEAT_TAC);;
add_simp firstSet_nEliteral;;

let firstSetML_nEliteral = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nEliteral IN sn) ==>
     firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
       gram_nEliteral)) rest) =
     firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
       gram_nEliteral)]`,
  CHEAT_TAC);;
add_simp firstSetML_nEliteral;;

let firstSet_nEbase = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEbase)] =
   {tokens_LetT,tokens_LparT,tokens_LbrackT,tokens_OpT} UNION firstSet cmlG
     [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nFQV)] UNION
                              firstSet cmlG [grammar_NT
                                ((INL:MMLnonT->MMLnonT+num) gram_nEliteral)]
                                UNION
                              firstSet cmlG [grammar_NT
                                ((INL:MMLnonT->MMLnonT+num)
                                gram_nConstructorName)]`,
  CHEAT_TAC);;
add_simp firstSet_nEbase;;

let firstSetML_nEbase = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nUQConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEbase IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nFQV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEliteral IN sn) ==>
     firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
       gram_nEbase)) rest) =
     firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEbase)]`,
  CHEAT_TAC);;
add_simp firstSetML_nEbase;;

let firstSet_nEapp = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEapp)] =
  firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nEapp;;

let firstSetML_nEapp = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nUQConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEbase IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nFQV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEapp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEliteral IN sn) ==>
   firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
     gram_nEapp)) rest) =
   firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEbase)]`,
  CHEAT_TAC);;
add_simp firstSetML_nEapp;;

let firstSet_nEmult = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEmult)] =
  firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nEmult;;

let firstSetML_nEmult = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nUQConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEbase IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nFQV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEapp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEmult IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEliteral IN sn) ==>
   firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
     gram_nEmult)) rest) =
   firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEbase)]`,
  CHEAT_TAC);;
add_simp firstSetML_nEmult;;

let firstSet_nEadd = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEadd)] =
  firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nEadd;;

let firstSetML_nEadd = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nUQConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEbase IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nFQV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEapp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEmult IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEadd IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEliteral IN sn) ==>
     firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
       gram_nEadd)) rest) =
     firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEbase)]`,
  CHEAT_TAC);;
add_simp firstSetML_nEadd;;

let firstSet_nElistop = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nElistop))
  rest) =
   firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nElistop;;

let firstSetML_nElistop = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nUQConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEbase IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nFQV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEapp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEmult IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEadd IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nElistop IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEliteral IN sn) ==>
   firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
     gram_nElistop)) rest) =
   firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEbase)]`,
  CHEAT_TAC);;
add_simp firstSetML_nElistop;;

let firstSet_nErel = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nErel))
  rest) = firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nErel;;

let firstSetML_nErel = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nUQConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEbase IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nFQV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEapp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEmult IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEadd IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nErel IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nElistop IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEliteral IN sn) ==>
   firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
     gram_nErel)) rest) = firstSet cmlG [(\nt. grammar_NT
     ((INL:MMLnonT->MMLnonT+num) nt)) gram_nEbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nErel;;

let firstSet_nEcomp = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEcomp))
  rest) = firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nEcomp;;

let firstSetML_nEcomp = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nUQConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEbase IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nFQV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEapp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEmult IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEadd IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nErel IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEcomp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nElistop IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEliteral IN sn) ==>
     firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
       gram_nEcomp)) rest) = firstSet cmlG [(\nt. grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nt)) gram_nEbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nEcomp;;

let firstSet_nEbefore = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEbefore))
  rest) =
   firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nEbefore;;

let firstSetML_nEbefore = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nUQConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEbase IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nFQV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEapp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEmult IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEadd IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nErel IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEcomp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEbefore IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nElistop IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEliteral IN sn) ==>
     firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
       gram_nEbefore)) rest) = firstSet cmlG [(\nt. grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nt)) gram_nEbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nEbefore;;

let firstSet_nEtyped = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEtyped))
  rest) = firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nEtyped;;

let firstSetML_nEtyped = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nUQConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEbase IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nFQV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEapp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEmult IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEadd IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nErel IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEcomp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEbefore IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEtyped IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nElistop IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEliteral IN sn) ==>
   firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
     gram_nEtyped)) rest) = firstSet cmlG [(\nt. grammar_NT
     ((INL:MMLnonT->MMLnonT+num) nt)) gram_nEbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nEtyped;;

let firstSet_nElogicAND = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
  gram_nElogicAND)) rest) = firstSet cmlG [grammar_NT
  ((INL:MMLnonT->MMLnonT+num) gram_nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nElogicAND;;

let firstSetML_nElogicAND = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nUQConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEbase IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nFQV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEapp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEmult IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEadd IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nErel IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEcomp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEbefore IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEtyped IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nElogicAND IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nElistop IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEliteral IN sn) ==>
   firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
     gram_nElogicAND)) rest) =
   firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
     gram_nEbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nElogicAND;;

let firstSet_nElogicOR = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
  gram_nElogicOR)) rest) = firstSet cmlG [grammar_NT
  ((INL:MMLnonT->MMLnonT+num) gram_nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nElogicOR;;

let firstSetML_nElogicOR = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nUQConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEbase IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nFQV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEapp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEmult IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEadd IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nErel IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEcomp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEbefore IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEtyped IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nElogicAND IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nElogicOR IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nElistop IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEliteral IN sn) ==>
   firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
     gram_nElogicOR)) rest) =
   firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
     gram_nEbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nElogicOR;;

let firstSet_nEhandle = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
  gram_nEhandle)) rest) = firstSet cmlG [grammar_NT
  ((INL:MMLnonT->MMLnonT+num) gram_nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nEhandle;;

let firstSetML_nEhandle = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nUQConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEbase IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nFQV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEapp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEmult IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEadd IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nErel IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEcomp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEbefore IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEtyped IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nElogicAND IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nElogicOR IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEhandle IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nElistop IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEliteral IN sn) ==>
   firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
     gram_nEhandle)) rest) =
   firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
     gram_nEbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nEhandle;;

let firstSet_nE = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nE)) rest)
  =
   firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nEbase)]
     UNION {tokens_IfT,tokens_CaseT,tokens_FnT,tokens_RaiseT}`,
  CHEAT_TAC);;

let firstSet_nTopLevelDecs = prove
 (`firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nTopLevelDecs] =
   {tokens_ValT,tokens_FunT,tokens_SemicolonT,tokens_DatatypeT
     ,tokens_StructureT,tokens_ExceptionT,tokens_TypeT,
    tokens_LocalT} UNION
            firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
              gram_nE)]`,
  CHEAT_TAC);;
add_simp firstSet_nTopLevelDecs;;

let firstSet_nNonETopLevelDecs = prove
 (`firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nNonETopLevelDecs] =
   {tokens_ValT,tokens_FunT,tokens_SemicolonT,tokens_DatatypeT
     ,tokens_StructureT,tokens_ExceptionT,tokens_TypeT,
    tokens_LocalT}`,
  CHEAT_TAC);;
add_simp firstSet_nNonETopLevelDecs;;

let firstSet_nEseq = prove
 (`firstSet cmlG (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nEseq) rest) = firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nE]`,
  CHEAT_TAC);;
add_simp firstSet_nEseq;;

let NOTIN_firstSet_nE = prove
 (`~(tokens_ValT IN firstSet cmlG (CONS (grammar_NT
  ((INL:MMLnonT->MMLnonT+num) gram_nE)) rest)) /\ ~(tokens_StructureT IN
  firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nE))
  rest)) /\ ~(tokens_FunT IN firstSet cmlG (CONS (grammar_NT
  ((INL:MMLnonT->MMLnonT+num) gram_nE)) rest)) /\ ~(tokens_DatatypeT IN
  firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nE))
  rest)) /\ ~(tokens_ExceptionT IN firstSet cmlG (CONS (grammar_NT
  ((INL:MMLnonT->MMLnonT+num) gram_nE)) rest)) /\ ~(tokens_SemicolonT IN
  firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nE))
  rest)) /\ ~(tokens_RparT IN firstSet cmlG (CONS ((\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nE) rest)) /\ ~(tokens_RbrackT IN
  firstSet cmlG (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nE) rest)) /\ ~(tokens_TypeT IN firstSet cmlG (CONS ((\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nE) rest))`,
  CHEAT_TAC);;
add_simp NOTIN_firstSet_nE;;

let firstSetML_nE = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nUQConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEbase IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nFQV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEapp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEmult IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEadd IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nErel IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEcomp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEbefore IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEtyped IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nElogicAND IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nElogicOR IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEhandle IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nE IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nElistop IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nEliteral IN sn) ==>
     firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
       gram_nE)) rest) = firstSet cmlG [(\nt. grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nt)) gram_nE]`,
  CHEAT_TAC);;
add_simp firstSetML_nE;;

let firstSet_nElist1 = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nElist1))
  rest) = firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nE)]`,
  CHEAT_TAC);;
add_simp firstSet_nElist1;;

let firstSet_nElist2 = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nElist2))
  rest) = firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nE)]`,
  CHEAT_TAC);;
add_simp firstSet_nElist2;;

let firstSetML_nPtuple = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nPtuple IN sn) ==> (firstSetML cmlG sn
  (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nPtuple)
  rest) = {tokens_LparT})`,
  CHEAT_TAC);;
add_simp firstSetML_nPtuple;;

let firstSet_nPtuple = prove
 (`firstSet cmlG (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nPtuple) rest) = {tokens_LparT}`,
  CHEAT_TAC);;
add_simp firstSet_nPtuple;;

let firstSet_nPbase = prove
 (`firstSet cmlG (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nPbase) rest) =
   {tokens_LparT,tokens_UnderbarT,tokens_LbrackT,tokens_OpT} UNION
     {tokens_IntT i | T} UNION {tokens_StringT s | T} UNION
                              {tokens_CharT c | T} UNION
                              firstSet cmlG [(\nt. grammar_NT
                                ((INL:MMLnonT->MMLnonT+num) nt))
                                gram_nConstructorName] UNION firstSet cmlG
                                [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num)
                                nt)) gram_nV]`,
  CHEAT_TAC);;
add_simp firstSet_nPbase;;

let firstSetML_nPbase = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nPbase IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nUQConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nPtuple IN sn) ==>
     firstSetML cmlG sn (CONS ((\nt. grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nt)) gram_nPbase) rest) = firstSet cmlG
       [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nPbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nPbase;;

let firstSet_nPConApp = prove
 (`firstSet cmlG (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nPConApp) rest) =
   firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
     gram_nConstructorName]`,
  CHEAT_TAC);;
add_simp firstSet_nPConApp;;

let firstSetML_nPConApp = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nPConApp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nUQConstructorName IN sn) ==>
     firstSetML cmlG sn (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nt)) gram_nPConApp) rest) =
     firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
       gram_nConstructorName]`,
  CHEAT_TAC);;
add_simp firstSetML_nPConApp;;

let firstSet_nPapp = prove
 (`firstSet cmlG (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nPapp) rest) = firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nPbase]`,
  CHEAT_TAC);;
add_simp firstSet_nPapp;;

let firstSetML_nPapp = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nPbase IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nUQConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nPtuple IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nPapp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nPConApp IN sn) ==>
     firstSetML cmlG sn (CONS ((\nt. grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nt)) gram_nPapp) rest) = firstSet cmlG
       [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nPbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nPapp;;

let firstSet_nPcons = prove
 (`firstSet cmlG (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nPcons) rest) = firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nPbase]`,
  CHEAT_TAC);;
add_simp firstSet_nPcons;;

let firstSetML_nPcons = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nPbase IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nUQConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nPtuple IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nPapp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nPcons IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nPConApp IN sn) ==>
     firstSetML cmlG sn (CONS ((\nt. grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nt)) gram_nPcons) rest) = firstSet cmlG
       [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nPbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nPcons;;

let firstSet_nPas = prove
 (`firstSet cmlG (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nPas) rest) = firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nPbase]`,
  CHEAT_TAC);;
add_simp firstSet_nPas;;

let firstSetML_nPas = prove
 (`~((INL:MMLnonT->MMLnonT+num) gram_nPbase IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nV IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nUQConstructorName IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nPtuple IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nPapp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nPcons IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nPConApp IN sn)
  /\ ~((INL:MMLnonT->MMLnonT+num) gram_nPas IN sn) ==>
     firstSetML cmlG sn (CONS ((\nt. grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nt)) gram_nPas) rest) = firstSet cmlG
       [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nPbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nPas;;

let firstSet_nPattern = prove
 (`firstSet cmlG (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nPattern) rest) = firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nPbase]`,
  CHEAT_TAC);;
add_simp firstSet_nPattern;;

let firstSet_nPatternList = prove
 (`firstSet cmlG (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nPatternList) rest) = firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nPattern]`,
  CHEAT_TAC);;
add_simp firstSet_nPatternList;;

let firstSet_nPbaseList1 = prove
 (`firstSet cmlG (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nPbaseList1) rest) = firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nPbase]`,
  CHEAT_TAC);;
add_simp firstSet_nPbaseList1;;

let firstSet_nPEsfx = prove
 (`firstSet cmlG (CONS ((\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nPEsfx) rest) =
   tokens_BarT INSERT tokens_HandleT INSERT firstSet cmlG rest`,
  CHEAT_TAC);;
add_simp firstSet_nPEsfx;;

let NOTIN_firstSet_nV = prove
 (`~(tokens_CommaT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV]) /\ ~(tokens_LparT IN firstSet
  cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])
  /\ ~(tokens_RparT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV]) /\ ~(tokens_UnderbarT IN
  firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])
  /\ ~(tokens_BarT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV]) /\ ~(tokens_OpT IN firstSet cmlG
  [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])
  /\ ~(tokens_FnT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV]) /\ ~(tokens_IfT IN firstSet cmlG
  [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])
  /\ ~(tokens_EqualsT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV]) /\ ~(tokens_DarrowT IN firstSet
  cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])
  /\ ~(tokens_ValT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV]) /\ ~(tokens_ExceptionT IN
  firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])
  /\ ~(tokens_EndT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV]) /\ ~(tokens_AndT IN firstSet
  cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])
  /\ ~(tokens_FFIT s IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV]) /\ ~(tokens_FunT IN firstSet
  cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])
  /\ ~(tokens_LbrackT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV]) /\ ~(tokens_LocalT IN firstSet
  cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])
  /\ ~(tokens_RbrackT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV]) /\ ~(tokens_InT IN firstSet cmlG
  [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])
  /\ ~(tokens_IntT i IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV]) /\ ~(tokens_StringT s IN
  firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])
  /\ ~(tokens_CharT c IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV]) /\ ~(tokens_ThenT IN firstSet
  cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])
  /\ ~(tokens_ElseT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV]) /\ ~(tokens_CaseT IN firstSet
  cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])
  /\ ~(tokens_LetT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV]) /\ ~(tokens_OfT IN firstSet cmlG
  [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])
  /\ ~(tokens_RaiseT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV]) /\ ~(tokens_DatatypeT IN
  firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])
  /\ ~(tokens_TypeT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV]) /\ ~(tokens_SemicolonT IN
  firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])
  /\ ~(tokens_ColonT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV]) /\ ~(tokens_StructureT IN
  firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])
  /\ ~(tokens_WordT w IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV]) /\ ~(tokens_SymbolT (implode
  "::") IN firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nV]) /\ ~(tokens_HandleT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])`,
  CHEAT_TAC);;
add_simp NOTIN_firstSet_nV;;

let NOTIN_firstSet_nFQV = prove
 (`~(tokens_AndT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV]) /\ ~(tokens_BarT IN firstSet
  cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV])
  /\ ~(tokens_CaseT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV]) /\ ~(tokens_CharT c IN
  firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nFQV]) /\ ~(tokens_ColonT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV]) /\ ~(tokens_CommaT IN firstSet
  cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV])
  /\ ~(tokens_DarrowT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV]) /\ ~(tokens_DatatypeT IN
  firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nFQV]) /\ ~(tokens_ElseT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV]) /\ ~(tokens_EndT IN firstSet
  cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV])
  /\ ~(tokens_EqualsT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV]) /\ ~(tokens_ExceptionT IN
  firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nFQV]) /\ ~(tokens_FFIT s IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV]) /\ ~(tokens_FnT IN firstSet
  cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV])
  /\ ~(tokens_FunT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV]) /\ ~(tokens_IfT IN firstSet
  cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV])
  /\ ~(tokens_InT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV]) /\ ~(tokens_IntT i IN firstSet
  cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV])
  /\ ~(tokens_LbrackT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV]) /\ ~(tokens_LetT IN firstSet
  cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV])
  /\ ~(tokens_LocalT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV]) /\ ~(tokens_LparT IN firstSet
  cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV])
  /\ ~(tokens_OfT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV]) /\ ~(tokens_OpT IN firstSet
  cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV])
  /\ ~(tokens_RaiseT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV]) /\ ~(tokens_RbrackT IN
  firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nFQV]) /\ ~(tokens_RparT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV]) /\ ~(tokens_SemicolonT IN
  firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nFQV]) /\ ~(tokens_StringT s IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV]) /\ ~(tokens_StructureT IN
  firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nFQV]) /\ ~(tokens_ThenT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV]) /\ ~(tokens_TypeT IN firstSet
  cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV])
  /\ ~(tokens_UnderbarT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV]) /\ ~(tokens_ValT IN firstSet
  cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV])
  /\ ~(tokens_WordT w IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nFQV]) /\ ~(tokens_HandleT IN
  firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])`,
  CHEAT_TAC);;
add_simp NOTIN_firstSet_nFQV;;

let NOTIN_firstSet_nConstructorName = prove
 (`~(tokens_AndT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName]) /\ ~(tokens_BarT
  IN firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nConstructorName]) /\ ~(tokens_ColonT IN firstSet cmlG [(\nt.
  grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName])
  /\ ~(tokens_CaseT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName]) /\ ~(tokens_CharT
  c IN firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nConstructorName]) /\ ~(tokens_CommaT IN firstSet cmlG [(\nt.
  grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName])
  /\ ~(tokens_DarrowT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName])
  /\ ~(tokens_DatatypeT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName]) /\ ~(tokens_ElseT
  IN firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nConstructorName]) /\ ~(tokens_EndT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName])
  /\ ~(tokens_EqualsT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName])
  /\ ~(tokens_ExceptionT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName]) /\ ~(tokens_FFIT s
  IN firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nConstructorName]) /\ ~(tokens_FnT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName]) /\ ~(tokens_FunT
  IN firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nConstructorName]) /\ ~(tokens_IfT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName]) /\ ~(tokens_InT IN
  firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nConstructorName]) /\ ~(tokens_IntT i IN firstSet cmlG [(\nt.
  grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName])
  /\ ~(tokens_LbrackT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName]) /\ ~(tokens_LetT
  IN firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nConstructorName]) /\ ~(tokens_LocalT IN firstSet cmlG [(\nt.
  grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName])
  /\ ~(tokens_LparT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName]) /\ ~(tokens_OfT IN
  firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nConstructorName]) /\ ~(tokens_OpT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName]) /\ ~(tokens_RaiseT
  IN firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nConstructorName]) /\ ~(tokens_RbrackT IN firstSet cmlG [(\nt.
  grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName])
  /\ ~(tokens_RparT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName])
  /\ ~(tokens_SemicolonT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName])
  /\ ~(tokens_StringT s IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName])
  /\ ~(tokens_StructureT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName])
  /\ ~(tokens_SymbolT (implode "::") IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName])
  /\ ~(tokens_SymbolT (implode "ref") IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName]) /\ ~(tokens_ThenT
  IN firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nConstructorName]) /\ ~(tokens_TypeT IN firstSet cmlG [(\nt.
  grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName])
  /\ ~(tokens_UnderbarT IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName]) /\ ~(tokens_ValT
  IN firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nConstructorName]) /\ ~(tokens_WordT w IN firstSet cmlG [(\nt.
  grammar_NT ((INL:MMLnonT->MMLnonT+num) nt)) gram_nConstructorName])`,
  CHEAT_TAC);;
add_simp NOTIN_firstSet_nConstructorName;;

let firstSets_nV_nConstructorName = prove
 (`~(t IN firstSet cmlG [(\nt. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt))
  gram_nConstructorName] /\ t IN firstSet cmlG [(\nt. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt)) gram_nV])`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
