(* ======================================================== *)
(*  gram: ported from HOL4's
    semantics/gramScript.sml  *)
(* ======================================================== *)

(*
  Definition of CakeML's Context-Free Grammar.
  The grammar specifies how token lists should be converted to syntax
    trees.
*)

needs "basis/pure/mlstring.ml";;
needs "lib/grammar.ml";;
needs "lib/location.ml";;
needs "semantics/tokens.ml";;


(* HOL4 ML code, not ported:
val tokmap0 =
    List.foldl (fn ((s,t), acc) => Binarymap.insert(acc,s,t))
               (Binarymap.mkDict String.compare)
               [("(", ``LparT``), (")", ``RparT``), (",", ``CommaT``),
                ("[", ``LbrackT``),
                ("]", ``RbrackT``),
                (";", ``SemicolonT``), (":=", ``SymbolT «:=»``),
                (":>", ``SealT``),
                ("->", ``ArrowT``), ("=>", ``DarrowT``),
                ("*", ``StarT``),
                ("::", “SymbolT «::»”),
                ("|", ``BarT``), ("=", ``EqualsT``), (":", ``ColonT``),
                ("_", ``UnderbarT``),
                ("and", ``AndT``),
                ("andalso", ``AndalsoT``),
                ("as", ``AsT``),
                ("before", ``AlphaT «before»``),
                ("Bind", ``AlphaT «Bind»``),
                ("case", ``CaseT``),
                ("datatype", ``DatatypeT``),
                ("Div", ``AlphaT «Div»``),
                ("else", ``ElseT``),
                ("end", ``EndT``),
                ("exception", ``ExceptionT``),
                ("fn", ``FnT``),
                ("fun", ``FunT``),
                ("handle", ``HandleT``),
                ("if", ``IfT``),
                ("in", ``InT``),
                ("IntError", ``AlphaT «IntError»``),
                ("let", ``LetT``),
                ("local", ``LocalT``),
                ("o", ``AlphaT «o»``),
                ("of", ``OfT``),
                ("op", ``OpT``),
                ("orelse", ``OrelseT``),
                ("raise", ``RaiseT``),
                ("sig", ``SigT``),
                ("struct", ``StructT``),
                ("structure", ``StructureT``),
                ("then", ``ThenT``),
                ("type", ``TypeT``),
                ("val", ``ValT``)]
fun tokmap s =
    case Binarymap.peek(tokmap0, s) of
        NONE => raise Fail ("No token binding for "^s)
      | SOME t => t
*)

(* HOL4 ML code, not ported:
val ginfo = { tokmap = tokmap,
              tokty = ``:token``, nt_tyname = "MMLnonT",
              start = "TopLevelDecs",
              gname = "cmlG", mkntname = (fn s => "n" ^ s) }
*)

let validMultSym_def = cake_define
  `validMultSym s <=> "/" <<= s \/ "*" <<= s \/ "%" <<= s \/ "&" <<=
  s`;;

let validAddSym_def = cake_define
  `validAddSym s <=> ~(s = "") /\ HD s IN {(CHR 43),(CHR 45),(CHR 94)}
  \/
                   2 <= LENGTH s /\ HD s = (CHR 124)`;;

let validRelSym_def = cake_define
  `validRelSym s <=> "<" <<= s \/ ">" <<= s \/ (2 <= LENGTH s /\ ("="
  <<= s \/ "~" <<= s))`;;

let validListSym_def = cake_define
  `validListSym s <=> "@" <<= s \/ (":" <<= s /\ 2 <= LENGTH s /\ ~(s
  = ":="))`;;

let validPrefixSym_def = cake_define
  `validPrefixSym s <=> s = "~" \/ "!" <<= s \/ "?" <<= s`;;

(* HOL4 makes the datatype of the nonterminals and the
   grammar itself with the ML code of grammarLib
   (mk_grammar_def); the port writes out what it makes *)

let MMLnonT_INDUCT,MMLnonT_RECURSION = define_datatype
  "MMLnonT = nV | nUQTyOp | nUQConstructorName | nTyvarN | nTypeName \
   | nTypeList2 | nTypeList1 | nTypeDec | nTypeAbbrevDec | nType | \
   nTyVarList | nTyOp | nTopLevelDecs | nTbaseList | nTbase | \
   nStructure | nStructName | nSpecLineList | nSpecLine | \
   nSignatureValue | nRelOps | nPtuple | nPcons | nPbaseList1 | \
   nPbase | nPatternList | nPattern | nPas | nPapp | nPType | nPTbase \
   | nPEsfx | nPEs | nPE | nPConApp | nOptionalSignatureAscription | \
   nOptTypEqn | nOpID | nNonETopLevelDecs | nMultOps | nListOps | \
   nLetDecs | nLetDec | nFQV | nFDecl | nEtyped | nEtuple | nEseq | \
   nErel | nEmult | nElogicOR | nElogicAND | nEliteral | nElistop | \
   nElist2 | nElist1 | nEhandle | nEcomp | nEbefore | nEbase | nEapp \
   | nEadd | nE | nDtypeDecls | nDtypeDecl | nDtypeCons | nDecls | \
   nDecl | nDconstructor | nDType | nConstructorName | nCompOps | \
   nAndFDecls | nAddOps";;

let cmlG_def = cake_define
  `cmlG = mk_grammar (INL nTopLevelDecs) (FEMPTY |+ (INL
  nUQTyOp,({[grammar_TOK (tokens_AlphaT m)] | m | T} UNION {[grammar_TOK
  (tokens_SymbolT m)] | m | T})) |+ (INL nTyvarN,{[grammar_TOK
  (tokens_TyvarT m)] | m | T}) |+ (INL nTyOp,({[grammar_NT (INL
  nUQTyOp)]} UNION {[grammar_TOK (tokens_LongidT p m)] | p,m | T})) |+
  (INL nTypeList1,({[grammar_NT (INL nType)]} UNION {[grammar_NT (INL
  nType); grammar_TOK (tokens_CommaT); grammar_NT (INL nTypeList1)]}))
  |+ (INL nTypeList2,{[grammar_NT (INL nType); grammar_TOK
  (tokens_CommaT); grammar_NT (INL nTypeList1)]}) |+ (INL
  nTbase,((({[grammar_TOK (tokens_TyvarT m)] | m | T} UNION {[grammar_NT
  (INL nTyOp)]}) UNION {[grammar_TOK (tokens_LparT); grammar_NT (INL
  nTypeList2); grammar_TOK (tokens_RparT); grammar_NT (INL nTyOp)]})
  UNION {[grammar_TOK (tokens_LparT); grammar_NT (INL nType);
  grammar_TOK (tokens_RparT)]})) |+ (INL nDType,({[grammar_NT (INL
  nDType); grammar_NT (INL nTyOp)]} UNION {[grammar_NT (INL nTbase)]}))
  |+ (INL nPType,({[grammar_NT (INL nDType); grammar_TOK (tokens_StarT);
  grammar_NT (INL nPType)]} UNION {[grammar_NT (INL nDType)]})) |+ (INL
  nType,({[grammar_NT (INL nPType)]} UNION {[grammar_NT (INL nPType);
  grammar_TOK (tokens_ArrowT); grammar_NT (INL nType)]})) |+ (INL
  nTbaseList,({[]} UNION {[grammar_NT (INL nPTbase); grammar_NT (INL
  nTbaseList)]})) |+ (INL nPTbase,(({[grammar_TOK (tokens_TyvarT m)] | m
  | T} UNION {[grammar_NT (INL nTyOp)]}) UNION {[grammar_TOK
  (tokens_LparT); grammar_NT (INL nType); grammar_TOK (tokens_RparT)]}))
  |+ (INL nTypeName,(({[grammar_NT (INL nUQTyOp)]} UNION {[grammar_TOK
  (tokens_LparT); grammar_NT (INL nTyVarList); grammar_TOK
  (tokens_RparT); grammar_NT (INL nUQTyOp)]}) UNION {[grammar_TOK
  (tokens_TyvarT m); grammar_NT (INL nUQTyOp)] | m | T})) |+ (INL
  nTyVarList,({[grammar_NT (INL nTyvarN)]} UNION {[grammar_NT (INL
  nTyVarList); grammar_TOK (tokens_CommaT); grammar_NT (INL nTyvarN)]}))
  |+ (INL nDconstructor,{[grammar_NT (INL nUQConstructorName);
  grammar_NT (INL nTbaseList)]}) |+ (INL nDtypeCons,({[grammar_NT (INL
  nDconstructor)]} UNION {[grammar_NT (INL nDtypeCons); grammar_TOK
  (tokens_BarT); grammar_NT (INL nDconstructor)]})) |+ (INL
  nDtypeDecl,{[grammar_NT (INL nTypeName); grammar_TOK (tokens_EqualsT);
  grammar_NT (INL nDtypeCons)]}) |+ (INL nDtypeDecls,({[grammar_NT (INL
  nDtypeDecl)]} UNION {[grammar_NT (INL nDtypeDecls); grammar_TOK
  (tokens_AndT); grammar_NT (INL nDtypeDecl)]})) |+ (INL
  nTypeDec,{[grammar_TOK (tokens_DatatypeT); grammar_NT (INL
  nDtypeDecls)]}) |+ (INL nTypeAbbrevDec,{[grammar_TOK (tokens_TypeT);
  grammar_NT (INL nTypeName); grammar_TOK (tokens_EqualsT); grammar_NT
  (INL nType)]}) |+ (INL nUQConstructorName,{[grammar_TOK (tokens_AlphaT
  s)] | ~(s = (implode "")) /\ isUpper (strsub s 0)}) |+ (INL
  nConstructorName,({[grammar_NT (INL nUQConstructorName)]} UNION
  {[grammar_TOK (tokens_LongidT str s)] | str,s | ~(s = (implode "")) /\
  isAlpha (strsub s 0) /\ isUpper (strsub s 0)})) |+ (INL
  nV,({[grammar_TOK (tokens_AlphaT s)] | ~(s IN {(implode
  "before"),(implode "div"),(implode "mod"),(implode "o")}) /\ ~(
                          s = (implode "")) /\ ~isUpper (strsub s 0)}
                            UNION {[grammar_TOK (tokens_SymbolT s)] |
                            validPrefixSym (explode s)})) |+ (INL
                            nFQV,({[grammar_NT (INL nV)]} UNION
                            {[grammar_TOK (tokens_LongidT str s)] |
                            str,s | ~(
                 s = (implode "")) /\ (isAlpha (strsub s 0) ==>
                   ~isUpper (strsub s 0))})) |+ (INL
                   nOpID,(((({[grammar_TOK (tokens_LongidT str s)] |
                   str,s | ~(s = (implode ""))} UNION {[grammar_TOK
                   (tokens_AlphaT s)] | ~(s = (implode ""))}) UNION
                   {[grammar_TOK (tokens_SymbolT s)] | ~(s = (implode
                   ""))}) UNION {[grammar_TOK (tokens_StarT)]}) UNION
                   {[grammar_TOK (tokens_EqualsT)]})) |+ (INL
                   nEliteral,(((({[grammar_TOK (tokens_IntT i)] | i |
                   T} UNION {[grammar_TOK (tokens_CharT c)] | c | T})
                   UNION {[grammar_TOK (tokens_StringT m)] | m | T})
                   UNION {[grammar_TOK (tokens_WordT n)] | n | T})
                   UNION {[grammar_TOK (tokens_FFIT m)] | m | T})) |+
                   (INL nEbase,((((((((({[grammar_TOK (tokens_LparT);
                   grammar_NT (INL nEseq); grammar_TOK
                   (tokens_RparT)]} UNION {[grammar_NT (INL
                   nEtuple)]}) UNION {[grammar_TOK (tokens_LparT);
                   grammar_TOK (tokens_RparT)]}) UNION {[grammar_NT
                   (INL nFQV)]}) UNION {[grammar_NT (INL
                   nConstructorName)]}) UNION {[grammar_NT (INL
                   nEliteral)]}) UNION {[grammar_TOK (tokens_LetT);
                   grammar_NT (INL nLetDecs); grammar_TOK
                   (tokens_InT); grammar_NT (INL nEseq); grammar_TOK
                   (tokens_EndT)]}) UNION {[grammar_TOK
                   (tokens_LbrackT); grammar_TOK (tokens_RbrackT)]})
                   UNION {[grammar_TOK (tokens_LbrackT); grammar_NT
                   (INL nElist1); grammar_TOK (tokens_RbrackT)]})
                   UNION {[grammar_TOK (tokens_OpT); grammar_NT (INL
                   nOpID)]})) |+ (INL nEseq,({[grammar_NT (INL nE);
                   grammar_TOK (tokens_SemicolonT); grammar_NT (INL
                   nEseq)]} UNION {[grammar_NT (INL nE)]})) |+ (INL
                   nEtuple,{[grammar_TOK (tokens_LparT); grammar_NT
                   (INL nElist2); grammar_TOK (tokens_RparT)]}) |+
                   (INL nElist2,{[grammar_NT (INL nE); grammar_TOK
                   (tokens_CommaT); grammar_NT (INL nElist1)]}) |+
                   (INL nElist1,({[grammar_NT (INL nE)]} UNION
                   {[grammar_NT (INL nE); grammar_TOK
                   (tokens_CommaT); grammar_NT (INL nElist1)]})) |+
                   (INL nEapp,({[grammar_NT (INL nEapp); grammar_NT
                   (INL nEbase)]} UNION {[grammar_NT (INL nEbase)]}))
                   |+ (INL nMultOps,({[grammar_TOK (tokens_AlphaT
                   (implode "div"))]; [grammar_TOK (tokens_AlphaT
                   (implode "mod"))]; [grammar_TOK (tokens_StarT)]}
                   UNION {[grammar_TOK (tokens_SymbolT s)] |
                   validMultSym (explode s)})) |+ (INL
                   nAddOps,{[grammar_TOK (tokens_SymbolT s)] |
                   validAddSym (explode s)}) |+ (INL
                   nRelOps,({[grammar_TOK (tokens_SymbolT s)] |
                   validRelSym (explode s)} UNION {[grammar_TOK
                   (tokens_EqualsT)]})) |+ (INL
                   nCompOps,({[grammar_TOK (tokens_AlphaT (implode
                   "o"))]} UNION {[grammar_TOK (tokens_SymbolT
                   (implode ":="))]})) |+ (INL nListOps,{[grammar_TOK
                   (tokens_SymbolT s)] | validListSym (explode s)})
                   |+ (INL nEmult,({[grammar_NT (INL nEmult);
                   grammar_NT (INL nMultOps); grammar_NT (INL
                   nEapp)]} UNION {[grammar_NT (INL nEapp)]})) |+
                   (INL nEadd,({[grammar_NT (INL nEadd); grammar_NT
                   (INL nAddOps); grammar_NT (INL nEmult)]} UNION
                   {[grammar_NT (INL nEmult)]})) |+ (INL
                   nElistop,({[grammar_NT (INL nEadd); grammar_NT
                   (INL nListOps); grammar_NT (INL nElistop)]} UNION
                   {[grammar_NT (INL nEadd)]})) |+ (INL
                   nErel,({[grammar_NT (INL nErel); grammar_NT (INL
                   nRelOps); grammar_NT (INL nElistop)]} UNION
                   {[grammar_NT (INL nElistop)]})) |+ (INL
                   nEcomp,({[grammar_NT (INL nEcomp); grammar_NT (INL
                   nCompOps); grammar_NT (INL nErel)]} UNION
                   {[grammar_NT (INL nErel)]})) |+ (INL
                   nEbefore,({[grammar_NT (INL nEbefore); grammar_TOK
                   (tokens_AlphaT (implode "before")); grammar_NT
                   (INL nEcomp)]} UNION {[grammar_NT (INL nEcomp)]}))
                   |+ (INL nEtyped,({[grammar_NT (INL nEbefore)]}
                   UNION {[grammar_NT (INL nEbefore); grammar_TOK
                   (tokens_ColonT); grammar_NT (INL nType)]})) |+
                   (INL nElogicAND,({[grammar_NT (INL nElogicAND);
                   grammar_TOK (tokens_AndalsoT); grammar_NT (INL
                   nEtyped)]} UNION {[grammar_NT (INL nEtyped)]})) |+
                   (INL nElogicOR,({[grammar_NT (INL nElogicOR);
                   grammar_TOK (tokens_OrelseT); grammar_NT (INL
                   nElogicAND)]} UNION {[grammar_NT (INL
                   nElogicAND)]})) |+ (INL nEhandle,({[grammar_NT
                   (INL nElogicOR)]} UNION {[grammar_NT (INL
                   nElogicOR); grammar_TOK (tokens_HandleT);
                   grammar_NT (INL nPEs)]})) |+ (INL
                   nE,(((({[grammar_TOK (tokens_IfT); grammar_NT (INL
                   nE); grammar_TOK (tokens_ThenT); grammar_NT (INL
                   nE); grammar_TOK (tokens_ElseT); grammar_NT (INL
                   nE)]} UNION {[grammar_TOK (tokens_CaseT);
                   grammar_NT (INL nE); grammar_TOK (tokens_OfT);
                   grammar_NT (INL nPEs)]}) UNION {[grammar_TOK
                   (tokens_FnT); grammar_NT (INL nPattern);
                   grammar_TOK (tokens_DarrowT); grammar_NT (INL
                   nE)]}) UNION {[grammar_TOK (tokens_RaiseT);
                   grammar_NT (INL nE)]}) UNION {[grammar_NT (INL
                   nEhandle)]})) |+ (INL nFDecl,{[grammar_NT (INL
                   nV); grammar_NT (INL nPbaseList1); grammar_TOK
                   (tokens_EqualsT); grammar_NT (INL nE)]}) |+ (INL
                   nAndFDecls,({[grammar_NT (INL nFDecl)]} UNION
                   {[grammar_NT (INL nAndFDecls); grammar_TOK
                   (tokens_AndT); grammar_NT (INL nFDecl)]})) |+ (INL
                   nLetDec,({[grammar_TOK (tokens_ValT); grammar_NT
                   (INL nPattern); grammar_TOK (tokens_EqualsT);
                   grammar_NT (INL nE)]} UNION {[grammar_TOK
                   (tokens_FunT); grammar_NT (INL nAndFDecls)]})) |+
                   (INL nLetDecs,(({[grammar_NT (INL nLetDec);
                   grammar_NT (INL nLetDecs)]} UNION {[grammar_TOK
                   (tokens_SemicolonT); grammar_NT (INL nLetDecs)]})
                   UNION {[]})) |+ (INL nPbase,((((((((({[grammar_NT
                   (INL nV)]} UNION {[grammar_NT (INL
                   nConstructorName)]}) UNION {[grammar_TOK
                   (tokens_IntT i)] | i | T}) UNION {[grammar_TOK
                   (tokens_StringT m)] | m | T}) UNION {[grammar_TOK
                   (tokens_CharT c)] | c | T}) UNION {[grammar_NT
                   (INL nPtuple)]}) UNION {[grammar_TOK
                   (tokens_UnderbarT)]}) UNION {[grammar_TOK
                   (tokens_LbrackT); grammar_TOK (tokens_RbrackT)]})
                   UNION {[grammar_TOK (tokens_LbrackT); grammar_NT
                   (INL nPatternList); grammar_TOK
                   (tokens_RbrackT)]}) UNION {[grammar_TOK
                   (tokens_OpT); grammar_NT (INL nOpID)]})) |+ (INL
                   nPConApp,({[grammar_NT (INL nConstructorName)]}
                   UNION {[grammar_NT (INL nPConApp); grammar_NT (INL
                   nPbase)]})) |+ (INL nPapp,({[grammar_NT (INL
                   nPConApp); grammar_NT (INL nPbase)]} UNION
                   {[grammar_NT (INL nPbase)]})) |+ (INL
                   nPcons,({[grammar_NT (INL nPapp); grammar_TOK
                   (tokens_SymbolT (implode "::")); grammar_NT (INL
                   nPcons)]} UNION {[grammar_NT (INL nPapp)]})) |+
                   (INL nPas,({[grammar_NT (INL nV); grammar_TOK
                   (tokens_AsT); grammar_NT (INL nPcons)]} UNION
                   {[grammar_NT (INL nPcons)]})) |+ (INL
                   nPattern,({[grammar_NT (INL nPas)]} UNION
                   {[grammar_NT (INL nPas); grammar_TOK
                   (tokens_ColonT); grammar_NT (INL nType)]})) |+
                   (INL nPtuple,({[grammar_TOK (tokens_LparT);
                   grammar_TOK (tokens_RparT)]} UNION {[grammar_TOK
                   (tokens_LparT); grammar_NT (INL nPatternList);
                   grammar_TOK (tokens_RparT)]})) |+ (INL
                   nPatternList,({[grammar_NT (INL nPattern)]} UNION
                   {[grammar_NT (INL nPattern); grammar_TOK
                   (tokens_CommaT); grammar_NT (INL nPatternList)]}))
                   |+ (INL nPbaseList1,({[grammar_NT (INL nPbase)]}
                   UNION {[grammar_NT (INL nPbase); grammar_NT (INL
                   nPbaseList1)]})) |+ (INL nPE,(((({[grammar_TOK
                   (tokens_CaseT); grammar_NT (INL nE); grammar_TOK
                   (tokens_OfT); grammar_NT (INL nPEs)]} UNION
                   {[grammar_TOK (tokens_IfT); grammar_NT (INL nE);
                   grammar_TOK (tokens_ThenT); grammar_NT (INL nE);
                   grammar_TOK (tokens_ElseT); grammar_NT (INL
                   nPE)]}) UNION {[grammar_TOK (tokens_FnT);
                   grammar_NT (INL nPattern); grammar_TOK
                   (tokens_DarrowT); grammar_NT (INL nE)]}) UNION
                   {[grammar_TOK (tokens_RaiseT); grammar_NT (INL
                   nPE)]}) UNION {[grammar_NT (INL nElogicOR);
                   grammar_NT (INL nPEsfx)]})) |+ (INL nPEsfx,(({[]}
                   UNION {[grammar_TOK (tokens_HandleT); grammar_NT
                   (INL nPEs)]}) UNION {[grammar_TOK (tokens_BarT);
                   grammar_NT (INL nPEs)]})) |+ (INL
                   nPEs,{[grammar_NT (INL nPattern); grammar_TOK
                   (tokens_DarrowT); grammar_NT (INL nPE)]}) |+ (INL
                   nStructName,{[grammar_TOK (tokens_AlphaT s)] | ~(s
                   = (implode ""))}) |+ (INL
                   nSpecLine,((({[grammar_TOK (tokens_ValT);
                   grammar_NT (INL nV); grammar_TOK (tokens_ColonT);
                   grammar_NT (INL nType)]} UNION {[grammar_TOK
                   (tokens_TypeT); grammar_NT (INL nTypeName);
                   grammar_NT (INL nOptTypEqn)]}) UNION {[grammar_TOK
                   (tokens_ExceptionT); grammar_NT (INL
                   nDconstructor)]}) UNION {[grammar_NT (INL
                   nTypeDec)]})) |+ (INL nOptTypEqn,({[grammar_TOK
                   (tokens_EqualsT); grammar_NT (INL nType)]} UNION
                   {[]})) |+ (INL nSpecLineList,(({[grammar_NT (INL
                   nSpecLine); grammar_NT (INL nSpecLineList)]} UNION
                   {[grammar_TOK (tokens_SemicolonT); grammar_NT (INL
                   nSpecLineList)]}) UNION {[]})) |+ (INL
                   nSignatureValue,{[grammar_TOK (tokens_SigT);
                   grammar_NT (INL nSpecLineList); grammar_TOK
                   (tokens_EndT)]}) |+ (INL
                   nOptionalSignatureAscription,({[grammar_TOK
                   (tokens_SealT); grammar_NT (INL nSignatureValue)]}
                   UNION {[]})) |+ (INL nDecl,(((((({[grammar_TOK
                   (tokens_ValT); grammar_NT (INL nPattern);
                   grammar_TOK (tokens_EqualsT); grammar_NT (INL
                   nE)]} UNION {[grammar_TOK (tokens_FunT);
                   grammar_NT (INL nAndFDecls)]}) UNION {[grammar_NT
                   (INL nTypeDec)]}) UNION {[grammar_TOK
                   (tokens_ExceptionT); grammar_NT (INL
                   nDconstructor)]}) UNION {[grammar_NT (INL
                   nTypeAbbrevDec)]}) UNION {[grammar_TOK
                   (tokens_LocalT); grammar_NT (INL nDecls);
                   grammar_TOK (tokens_InT); grammar_NT (INL nDecls);
                   grammar_TOK (tokens_EndT)]}) UNION {[grammar_NT
                   (INL nStructure)]})) |+ (INL nDecls,(({[grammar_NT
                   (INL nDecl); grammar_NT (INL nDecls)]} UNION
                   {[grammar_TOK (tokens_SemicolonT); grammar_NT (INL
                   nDecls)]}) UNION {[]})) |+ (INL
                   nStructure,{[grammar_TOK (tokens_StructureT);
                   grammar_NT (INL nStructName); grammar_NT (INL
                   nOptionalSignatureAscription); grammar_TOK
                   (tokens_EqualsT); grammar_TOK (tokens_StructT);
                   grammar_NT (INL nDecls); grammar_TOK
                   (tokens_EndT)]}) |+ (INL
                   nTopLevelDecs,((({[grammar_NT (INL nE);
                   grammar_TOK (tokens_SemicolonT); grammar_NT (INL
                   nTopLevelDecs)]} UNION {[grammar_NT (INL nDecl);
                   grammar_NT (INL nNonETopLevelDecs)]}) UNION
                   {[grammar_TOK (tokens_SemicolonT); grammar_NT (INL
                   nTopLevelDecs)]}) UNION {[]})) |+ (INL
                   nNonETopLevelDecs,(({[grammar_NT (INL nDecl);
                   grammar_NT (INL nNonETopLevelDecs)]} UNION
                   {[grammar_TOK (tokens_SemicolonT); grammar_NT (INL
                   nTopLevelDecs)]}) UNION {[]})))`;;

new_type_abbrev("gram_NT",`: MMLnonT+num`);;

(* HOL4 overload (expanded in the port):
     mkNT = INL : MMLnonT -> NT *)
(* HOL4 overload (expanded in the port):
     NN = \nt. NT (mkNT nt) *)
(* HOL4 overload (expanded in the port):
     TK = TOK : token -> (token,MMLnonT)symbol *)

new_type_abbrev("mlptree",`: (tokens_token,MMLnonT,locs)parsetree`);;

(* HOL4 ML code, not ported:
val nt_distinct_ths = let
  val ntlist = TypeBase.constructors_of ``:MMLnonT``
  fun recurse [] = []
    | recurse (t::ts) = let
      val eqns = map (fn t' => mk_eq(t,t')) ts
      val ths0 = map (SIMP_CONV (srw_ss()) []) eqns
      val ths1 = map (CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ))) ths0
    in
      ths0 @ ths1 @ recurse ts
    end
in
  save_thm("nt_distinct_ths",  LIST_CONJ (recurse ntlist))
end
*)

let ndl_def = cake_define
  `(Ndl n l = Nd (n,unknown_loc) l)`;;

let lfl_def = cake_define
  `(Lfl t = Lf (t,unknown_loc))`;;

(* HOL4 ML code, not ported:
val ast =
  ``let mkI = λn. Ndl (mkNT nEbase) [Ndl (mkNT nEliteral) [Lfl (TK (IntT
    n))]]
    in
      Ndl (mkNT nEmult) [
              Ndl (mkNT nEmult) [
                Ndl (mkNT nEmult) [Ndl (mkNT nEapp) [mkI 3]];
                Ndl (mkNT nMultOps) [Lfl (TK StarT)];
                Ndl (mkNT nEapp) [mkI 4]
              ];
              Ndl (mkNT nMultOps) [Lfl (TK (SymbolT «/»))];
              Ndl (mkNT nEapp) [mkI 5]
            ]``
*)

(* HOL4 ML code, not ported:
val check_results =
    time (SIMP_CONV (srw_ss())
              [valid_ptree_def, cmlG_def,DISJ_IMP_THM, FORALL_AND_THM,
               finite_mapTheory.FAPPLY_FUPDATE_THM,
                 LET_THM,Ndl_def,Lfl_def,
               validMultSym_def])
 ``valid_ptree cmlG ^ast``
*)

(* HOL4 ML code, not ported:
val _ = if aconv (rhs (concl check_results)) T then print
  "valid_ptree: OK\n"
        else raise Fail "valid_ptree: failed"
*)
