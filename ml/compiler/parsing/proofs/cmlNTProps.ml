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

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "cmlNTProps"
  ["gram"; "gramProps"];;

(* [local] *)
let disjImpI = prove
 (`~p \/ q <=> p ==> q`,
  (REPEAT GEN_TAC THEN CONV_TAC TAUT));;

let firstSet_nUQTyOp = prove
 (`firstSet cmlG (CONS ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nUQTyOp) rest) =
   {tokens_AlphaT s | T} UNION {tokens_SymbolT s | T}`,
  CHEAT_TAC);;
add_simp firstSet_nUQTyOp;;

let firstSet_nTyOp = prove
 (`firstSet cmlG (CONS ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nTyOp) rest) =
   {tokens_AlphaT s | T} UNION {tokens_SymbolT s | T} UNION
     {tokens_LongidT s1 s2 | T}`,
  CHEAT_TAC);;
add_simp firstSet_nTyOp;;

let firstSet_nPTbase = prove
 (`firstSet cmlG (CONS ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nPTbase) rest) =
   firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
     nt')) nTyOp] UNION {tokens_LparT} UNION {tokens_TyvarT s | T}`,
  CHEAT_TAC);;
add_simp firstSet_nPTbase;;

let firstSet_nTbaseList = prove
 (`firstSet cmlG (CONS ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nTbaseList) rest) =
   firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
     nt')) nPTbase] UNION firstSet cmlG rest`,
  CHEAT_TAC);;
add_simp firstSet_nTbaseList;;

let firstSet_nTyVarList = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nTyVarList)]
  = {tokens_TyvarT s | T}`,
  CHEAT_TAC);;
add_simp firstSet_nTyVarList;;
(* HOL4 cmlNTPropsScript.sml:57-59: ML code, not ported *)

let firstSet_nLetDec = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nLetDec)] =
  {tokens_ValT,tokens_FunT}`,
  CHEAT_TAC);;
add_simp firstSet_nLetDec;;

let firstSet_nLetDecs = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nLetDecs)] =
  {tokens_ValT,tokens_FunT,tokens_SemicolonT}`,
  CHEAT_TAC);;
add_simp firstSet_nLetDecs;;

let firstSet_nTypeDec = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nTypeDec)] =
  {tokens_DatatypeT}`,
  CHEAT_TAC);;
add_simp firstSet_nTypeDec;;

let firstSet_nTypeAbbrevDec = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nTypeAbbrevDec)] = {tokens_TypeT}`,
  CHEAT_TAC);;
add_simp firstSet_nTypeAbbrevDec;;

let firstSet_nStructure = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nStructure)]
  = {tokens_StructureT}`,
  CHEAT_TAC);;
add_simp firstSet_nStructure;;

let firstSet_nDecl = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nDecl)] =
   {tokens_ValT,tokens_FunT,tokens_DatatypeT,tokens_ExceptionT
     ,tokens_TypeT,tokens_LocalT,tokens_StructureT}`,
  CHEAT_TAC);;
add_simp firstSet_nDecl;;

let firstSet_nDecls = prove
 (`firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nDecls] =
   {tokens_ValT,tokens_DatatypeT,tokens_FunT,tokens_SemicolonT
     ,tokens_ExceptionT,tokens_TypeT,tokens_LocalT,tokens_StructureT}`,
  CHEAT_TAC);;
add_simp firstSet_nDecls;;

(* [local] *)
let IMAGE_GSPEC1 = prove
 (`IMAGE f (hol4_GSPEC (\a. (g a,P a))) = hol4_GSPEC (\a. (f (g a),P
  a))`,
  (REWRITE_TAC[hol4_GSPEC] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
   REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; PAIR_EQ] THEN
   MESON_TAC[]));;

(* [local] *)
let BIGUNION_singletons = prove
 (`UNIONS (hol4_GSPEC (\a. {f a},P a)) = hol4_GSPEC (\a. f a,P a)`,
  (REWRITE_TAC[hol4_GSPEC] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
   REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; PAIR_EQ] THEN
   MESON_TAC[IN_SING]));;
add_simp BIGUNION_singletons;;

let firstSet_nMultOps = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nMultOps)) rest) =
   {tokens_AlphaT (implode "div"),tokens_AlphaT (implode
     "mod"),tokens_StarT} UNION {tokens_SymbolT s | validMultSym
     (explode s)}`,
  CHEAT_TAC);;
add_simp firstSet_nMultOps;;

let firstSet_nRelOps = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num) nRelOps))
  rest) =
   tokens_EqualsT INSERT {tokens_SymbolT s | validRelSym (explode
     s)}`,
  CHEAT_TAC);;
add_simp firstSet_nRelOps;;

let firstSet_nAddOps = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nAddOps)) rest) = {tokens_SymbolT s | validAddSym (explode s)}`,
  CHEAT_TAC);;
add_simp firstSet_nAddOps;;

let firstSet_nCompOps = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nCompOps)) rest) = {tokens_AlphaT (implode "o"),tokens_SymbolT
  (implode ":=")}`,
  CHEAT_TAC);;
add_simp firstSet_nCompOps;;

let firstSet_nListOps = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nListOps)) rest) = {tokens_SymbolT s | validListSym (explode s)}`,
  CHEAT_TAC);;
add_simp firstSet_nListOps;;

let firstSet_nSpecLine = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nSpecLine)] =
   {tokens_ValT,tokens_DatatypeT,tokens_TypeT,tokens_ExceptionT}`,
  CHEAT_TAC);;
add_simp firstSet_nSpecLine;;

let firstSet_nSpecLineList = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nSpecLineList)]
  =
   {tokens_ValT,tokens_DatatypeT,tokens_TypeT,tokens_SemicolonT
     ,tokens_ExceptionT}`,
  CHEAT_TAC);;
add_simp firstSet_nSpecLineList;;

let firstSet_nV = prove
 (`firstSet cmlG (CONS ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nV) rest) =
   {tokens_AlphaT s | ~(s = (implode "")) /\ ~(isUpper (strsub s 0))
     /\ ~(s = (implode "before")) /\ ~(s = (implode "div")) /\ ~(s =
     (implode "mod")) /\ ~(s = (implode "o"))} UNION
                              {tokens_SymbolT s | validPrefixSym
                                (explode s)}`,
  CHEAT_TAC);;

let firstSet_nFQV = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nFQV)] =
   firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nV)] UNION
            {tokens_LongidT m i | (m,i) | ~(i = (implode "")) /\
              (isAlpha (strsub i 0) ==> ~(isUpper (strsub i 0)))}`,
  CHEAT_TAC);;

let firstSet_nUQConstructorName = prove
 (`firstSet cmlG (CONS ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nUQConstructorName) rest) =
   {tokens_AlphaT s | ~(s = (implode "")) /\ isUpper (strsub s 0)}`,
  CHEAT_TAC);;

let firstSet_nConstructorName = prove
 (`firstSet cmlG (CONS ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nConstructorName) rest) =
   {tokens_LongidT str s | (str,s) | ~(s = (implode "")) /\ isAlpha
     (strsub s 0) /\ isUpper (strsub s 0)} UNION
                              {tokens_AlphaT s | ~(s = (implode
                                "")) /\ isUpper (strsub s 0)}`,
  CHEAT_TAC);;

let firstSetML_nConstructorName = prove
 (`~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) ==>
     (firstSetML cmlG sn (CONS ((\nt'. grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName) rest) =
      firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
        nt')) nConstructorName])`,
  CHEAT_TAC);;
add_simp firstSetML_nConstructorName;;

let firstSetML_nV = prove
 (`~((INL:MMLnonT->MMLnonT+num) nV IN sn) ==>
     (firstSetML cmlG sn (CONS ((\nt'. grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nt')) nV) rest) = firstSet cmlG
       [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nV])`,
  CHEAT_TAC);;
add_simp firstSetML_nV;;

let firstSetML_nFQV = prove
 (`~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) ==>
     (firstSetML cmlG sn (CONS ((\nt'. grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nt')) nFQV) rest) = firstSet cmlG
       [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nFQV])`,
  CHEAT_TAC);;
add_simp firstSetML_nFQV;;

let firstSet_nEtuple = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEtuple)] =
  {tokens_LparT}`,
  CHEAT_TAC);;
add_simp firstSet_nEtuple;;

let firstSet_nEliteral = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEliteral)] =
   {tokens_IntT i | T} UNION {tokens_StringT s | T} UNION
     {tokens_CharT c | T} UNION {tokens_WordT w | T} UNION
                {tokens_FFIT s | T}`,
  CHEAT_TAC);;
add_simp firstSet_nEliteral;;

let firstSetML_nEliteral = prove
 (`~((INL:MMLnonT->MMLnonT+num) nEliteral IN sn) ==>
     firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nEliteral)) rest) =
     firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nEliteral)]`,
  CHEAT_TAC);;
add_simp firstSetML_nEliteral;;

let firstSet_nEbase = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEbase)] =
   {tokens_LetT,tokens_LparT,tokens_LbrackT,tokens_OpT} UNION
     firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nFQV)] UNION
                              firstSet cmlG [grammar_NT
                                ((INL:MMLnonT->MMLnonT+num) nEliteral)]
                                UNION
                              firstSet cmlG [grammar_NT
                                ((INL:MMLnonT->MMLnonT+num)
                                nConstructorName)]`,
  CHEAT_TAC);;
add_simp firstSet_nEbase;;

let firstSetML_nEbase = prove
 (`~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nEliteral IN sn) ==>
     firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nEbase)) rest) =
     firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEbase)]`,
  CHEAT_TAC);;
add_simp firstSetML_nEbase;;

let firstSet_nEapp = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEapp)] =
  firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nEapp;;

let firstSetML_nEapp = prove
 (`~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nEapp IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nEliteral IN sn) ==>
   firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
     nEapp)) rest) =
   firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEbase)]`,
  CHEAT_TAC);;
add_simp firstSetML_nEapp;;

let firstSet_nEmult = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEmult)] =
  firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nEmult;;

let firstSetML_nEmult = prove
 (`~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nEapp IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nEmult IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEliteral IN sn) ==>
   firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
     nEmult)) rest) =
   firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEbase)]`,
  CHEAT_TAC);;
add_simp firstSetML_nEmult;;

let firstSet_nEadd = prove
 (`firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEadd)] =
  firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nEadd;;

let firstSetML_nEadd = prove
 (`~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nEapp IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nEmult IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEadd IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEliteral IN sn) ==>
     firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nEadd)) rest) =
     firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEbase)]`,
  CHEAT_TAC);;
add_simp firstSetML_nEadd;;

let firstSet_nElistop = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nElistop)) rest) =
   firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nElistop;;

let firstSetML_nElistop = prove
 (`~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nEapp IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nEmult IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEadd IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nElistop IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEliteral IN sn) ==>
   firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
     nElistop)) rest) =
   firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEbase)]`,
  CHEAT_TAC);;
add_simp firstSetML_nElistop;;

let firstSet_nErel = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num) nErel))
  rest) = firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nErel;;

let firstSetML_nErel = prove
 (`~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nFQV IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nEapp IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nEmult IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEadd IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nErel IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nElistop IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nEliteral IN sn) ==>
   firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
     nErel)) rest) = firstSet cmlG [(\nt'. grammar_NT
     ((INL:MMLnonT->MMLnonT+num) nt')) nEbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nErel;;

let firstSet_nEcomp = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nEcomp)) rest) = firstSet cmlG [grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nEcomp;;

let firstSetML_nEcomp = prove
 (`~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
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
     firstSetML cmlG sn (CONS (grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nEcomp)) rest) = firstSet cmlG
       [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nEbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nEcomp;;

let firstSet_nEbefore = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nEbefore)) rest) =
   firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nEbefore;;

let firstSetML_nEbefore = prove
 (`~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
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
     firstSetML cmlG sn (CONS (grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nEbefore)) rest) = firstSet cmlG
       [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nEbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nEbefore;;

let firstSet_nEtyped = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nEtyped)) rest) = firstSet cmlG [grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nEtyped;;

let firstSetML_nEtyped = prove
 (`~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
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
   firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
     nEtyped)) rest) = firstSet cmlG [(\nt'. grammar_NT
     ((INL:MMLnonT->MMLnonT+num) nt')) nEbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nEtyped;;

let firstSet_nElogicAND = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nElogicAND)) rest) = firstSet cmlG [grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nElogicAND;;

let firstSetML_nElogicAND = prove
 (`~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
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
   firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
     nElogicAND)) rest) =
   firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
     nt')) nEbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nElogicAND;;

let firstSet_nElogicOR = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nElogicOR)) rest) = firstSet cmlG [grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nElogicOR;;

let firstSetML_nElogicOR = prove
 (`~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
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
   firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
     nElogicOR)) rest) =
   firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
     nt')) nEbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nElogicOR;;

let firstSet_nEhandle = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nEhandle)) rest) = firstSet cmlG [grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nEbase)]`,
  CHEAT_TAC);;
add_simp firstSet_nEhandle;;

let firstSetML_nEhandle = prove
 (`~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
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
   firstSetML cmlG sn (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
     nEhandle)) rest) =
   firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
     nt')) nEbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nEhandle;;

let firstSet_nE = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num) nE))
  rest) =
   firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nEbase)]
     UNION {tokens_IfT,tokens_CaseT,tokens_FnT,tokens_RaiseT}`,
  CHEAT_TAC);;

let firstSet_nTopLevelDecs = prove
 (`firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nTopLevelDecs] =
   {tokens_ValT,tokens_FunT,tokens_SemicolonT,tokens_DatatypeT
     ,tokens_StructureT,tokens_ExceptionT,tokens_TypeT,
    tokens_LocalT} UNION
            firstSet cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num)
              nE)]`,
  CHEAT_TAC);;
add_simp firstSet_nTopLevelDecs;;

let firstSet_nNonETopLevelDecs = prove
 (`firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  nNonETopLevelDecs] =
   {tokens_ValT,tokens_FunT,tokens_SemicolonT,tokens_DatatypeT
     ,tokens_StructureT,tokens_ExceptionT,tokens_TypeT,
    tokens_LocalT}`,
  CHEAT_TAC);;
add_simp firstSet_nNonETopLevelDecs;;

let firstSet_nEseq = prove
 (`firstSet cmlG (CONS ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nEseq) rest) = firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nE]`,
  CHEAT_TAC);;
add_simp firstSet_nEseq;;

let NOTIN_firstSet_nE = prove
 (`~(tokens_ValT IN firstSet cmlG (CONS (grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nE)) rest)) /\ ~(tokens_StructureT IN
  firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num) nE))
  rest)) /\ ~(tokens_FunT IN firstSet cmlG (CONS (grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nE)) rest)) /\ ~(tokens_DatatypeT IN
  firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num) nE))
  rest)) /\ ~(tokens_ExceptionT IN firstSet cmlG (CONS (grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nE)) rest)) /\ ~(tokens_SemicolonT IN
  firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num) nE))
  rest)) /\ ~(tokens_RparT IN firstSet cmlG (CONS ((\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nE) rest)) /\ ~(tokens_RbrackT IN
  firstSet cmlG (CONS ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nE) rest)) /\ ~(tokens_TypeT IN firstSet cmlG (CONS ((\nt'.
  grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nE) rest))`,
  CHEAT_TAC);;
add_simp NOTIN_firstSet_nE;;

let firstSetML_nE = prove
 (`~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
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
     firstSetML cmlG sn (CONS (grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nE)) rest) = firstSet cmlG [(\nt'.
       grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nE]`,
  CHEAT_TAC);;
add_simp firstSetML_nE;;

let firstSet_nElist1 = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nElist1)) rest) = firstSet cmlG [grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nE)]`,
  CHEAT_TAC);;
add_simp firstSet_nElist1;;

let firstSet_nElist2 = prove
 (`firstSet cmlG (CONS (grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nElist2)) rest) = firstSet cmlG [grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nE)]`,
  CHEAT_TAC);;
add_simp firstSet_nElist2;;

let firstSetML_nPtuple = prove
 (`~((INL:MMLnonT->MMLnonT+num) nPtuple IN sn) ==> (firstSetML cmlG sn
  (CONS ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nPtuple)
  rest) = {tokens_LparT})`,
  CHEAT_TAC);;
add_simp firstSetML_nPtuple;;

let firstSet_nPtuple = prove
 (`firstSet cmlG (CONS ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nPtuple) rest) = {tokens_LparT}`,
  CHEAT_TAC);;
add_simp firstSet_nPtuple;;

let firstSet_nPbase = prove
 (`firstSet cmlG (CONS ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nPbase) rest) =
   {tokens_LparT,tokens_UnderbarT,tokens_LbrackT,tokens_OpT} UNION
     {tokens_IntT i | T} UNION {tokens_StringT s | T} UNION
                              {tokens_CharT c | T} UNION
                              firstSet cmlG [(\nt'. grammar_NT
                                ((INL:MMLnonT->MMLnonT+num) nt'))
                                nConstructorName] UNION firstSet cmlG
                                [(\nt'. grammar_NT
                                ((INL:MMLnonT->MMLnonT+num) nt')) nV]`,
  CHEAT_TAC);;
add_simp firstSet_nPbase;;

let firstSetML_nPbase = prove
 (`~((INL:MMLnonT->MMLnonT+num) nPbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nConstructorName IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nUQConstructorName IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nPtuple IN
  sn) ==>
     firstSetML cmlG sn (CONS ((\nt'. grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nt')) nPbase) rest) = firstSet cmlG
       [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nPbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nPbase;;

let firstSet_nPConApp = prove
 (`firstSet cmlG (CONS ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nPConApp) rest) =
   firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
     nt')) nConstructorName]`,
  CHEAT_TAC);;
add_simp firstSet_nPConApp;;

let firstSetML_nPConApp = prove
 (`~((INL:MMLnonT->MMLnonT+num) nConstructorName IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nPConApp IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nUQConstructorName IN sn) ==>
     firstSetML cmlG sn (CONS ((\nt'. grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nt')) nPConApp) rest) =
     firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nt')) nConstructorName]`,
  CHEAT_TAC);;
add_simp firstSetML_nPConApp;;

let firstSet_nPapp = prove
 (`firstSet cmlG (CONS ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nPapp) rest) = firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nPbase]`,
  CHEAT_TAC);;
add_simp firstSet_nPapp;;

let firstSetML_nPapp = prove
 (`~((INL:MMLnonT->MMLnonT+num) nPbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nConstructorName IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nUQConstructorName IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nPtuple IN
  sn) /\ ~((INL:MMLnonT->MMLnonT+num) nPapp IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nPConApp IN sn) ==>
     firstSetML cmlG sn (CONS ((\nt'. grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nt')) nPapp) rest) = firstSet cmlG
       [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nPbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nPapp;;

let firstSet_nPcons = prove
 (`firstSet cmlG (CONS ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nPcons) rest) = firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nPbase]`,
  CHEAT_TAC);;
add_simp firstSet_nPcons;;

let firstSetML_nPcons = prove
 (`~((INL:MMLnonT->MMLnonT+num) nPbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nConstructorName IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nUQConstructorName IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nPtuple IN
  sn) /\ ~((INL:MMLnonT->MMLnonT+num) nPapp IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nPcons IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nPConApp IN sn) ==>
     firstSetML cmlG sn (CONS ((\nt'. grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nt')) nPcons) rest) = firstSet cmlG
       [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nPbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nPcons;;

let firstSet_nPas = prove
 (`firstSet cmlG (CONS ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nPas) rest) = firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nPbase]`,
  CHEAT_TAC);;
add_simp firstSet_nPas;;

let firstSetML_nPas = prove
 (`~((INL:MMLnonT->MMLnonT+num) nPbase IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nV IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nConstructorName IN sn) /\ ~((INL:MMLnonT->MMLnonT+num)
  nUQConstructorName IN sn) /\ ~((INL:MMLnonT->MMLnonT+num) nPtuple IN
  sn) /\ ~((INL:MMLnonT->MMLnonT+num) nPapp IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nPcons IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nPConApp IN sn) /\
  ~((INL:MMLnonT->MMLnonT+num) nPas IN sn) ==>
     firstSetML cmlG sn (CONS ((\nt'. grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nt')) nPas) rest) = firstSet cmlG
       [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nPbase]`,
  CHEAT_TAC);;
add_simp firstSetML_nPas;;

let firstSet_nPattern = prove
 (`firstSet cmlG (CONS ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nPattern) rest) = firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nPbase]`,
  CHEAT_TAC);;
add_simp firstSet_nPattern;;

let firstSet_nPatternList = prove
 (`firstSet cmlG (CONS ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nPatternList) rest) = firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nPattern]`,
  CHEAT_TAC);;
add_simp firstSet_nPatternList;;

let firstSet_nPbaseList1 = prove
 (`firstSet cmlG (CONS ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nPbaseList1) rest) = firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nPbase]`,
  CHEAT_TAC);;
add_simp firstSet_nPbaseList1;;

let firstSet_nPEsfx = prove
 (`firstSet cmlG (CONS ((\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nPEsfx) rest) =
   tokens_BarT INSERT tokens_HandleT INSERT firstSet cmlG rest`,
  CHEAT_TAC);;
add_simp firstSet_nPEsfx;;

let NOTIN_firstSet_nV = prove
 (`~(tokens_CommaT IN firstSet cmlG [(\nt'. grammar_NT
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
  nV])`,
  CHEAT_TAC);;
add_simp NOTIN_firstSet_nV;;

let NOTIN_firstSet_nFQV = prove
 (`~(tokens_AndT IN firstSet cmlG [(\nt'. grammar_NT
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
  nV])`,
  CHEAT_TAC);;
add_simp NOTIN_firstSet_nFQV;;

let NOTIN_firstSet_nConstructorName = prove
 (`~(tokens_AndT IN firstSet cmlG [(\nt'. grammar_NT
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
  ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName])`,
  CHEAT_TAC);;
add_simp NOTIN_firstSet_nConstructorName;;

let firstSets_nV_nConstructorName = prove
 (`~(t IN firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
  nt')) nConstructorName] /\ t IN firstSet cmlG [(\nt'. grammar_NT
  ((INL:MMLnonT->MMLnonT+num) nt')) nV])`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
