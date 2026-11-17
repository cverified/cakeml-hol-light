(* ======================================================== *)
(*  camlPEG: ported from HOL4's
    compiler/parsing/ocaml/camlPEGScript.sml
    A definition theory, with 30 definitions, 1 datatype and 17
    theorems.  Needed by camlPtreeConversion.ml, caml_parser.ml and
    caml_parserProg.ml.  *)
(* ======================================================== *)

(*
  Definition of a PEG for (a subset of) OCaml.
 *)

needs "basis/pure/mlstring.ml";;
needs "compiler/encoders/asm/asmSem.ml";;
needs "compiler/parsing/ocaml/caml_lex.ml";;
needs "lib/grammar.ml";;
needs "lib/peg.ml";;
needs "lib/pegexec.ml";;
needs "semantics/ast.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "camlPEG"
  ["caml_lex"; "mlstring"];;

(* Some definitions taken from cmlPEG:
 *)

let camlPEG_sumID_def = define_cases
  `(camlPEG_sumID (INL x) = x) /\
   (camlPEG_sumID (INR y) = y)`;;

let camlPEG_mktokLf_def = new_definition
  `camlPEG_mktokLf t = [Lf (grammar_TOK (FST t),SND t)]`;;

let camlPEG_mkNd_def = new_definition
  `camlPEG_mkNd ntnm l = Nd (ntnm,ptree_list_loc l) l`;;

let camlPEG_bindNT0_def = new_definition
  `camlPEG_bindNT0 ntnm l = Nd (INL ntnm,ptree_list_loc l) l`;;

let camlPEG_bindNT_def = new_definition
  `camlPEG_bindNT ntnm l = [camlPEG_bindNT0 ntnm l]`;;

let camlPEG_mk_linfix_def,camlPEG_mk_linfix_ind = define_guess
  `(camlPEG_mk_linfix tgt acc [] = acc) /\
   (camlPEG_mk_linfix tgt acc [t] = acc) /\
   (camlPEG_mk_linfix tgt acc (CONS opt (CONS t rest)) =
      camlPEG_mk_linfix tgt (camlPEG_mkNd tgt [acc; opt; t]) rest)`;;

let camlPEG_peg_linfix_def = new_definition
  `camlPEG_peg_linfix tgtnt rptsym opsym =
     peg_seq rptsym (peg_rpt (peg_seq opsym rptsym APPEND) FLAT)
         (\a b. match a with
                    [] -> []
                   | CONS h _ -> [camlPEG_mk_linfix tgtnt (camlPEG_mkNd
                     tgtnt [h]) b])`;;

let camlPEG_choicel_def,camlPEG_choicel_ind = define_guess
  `(camlPEG_choicel [] = peg_not (peg_empty []) []) /\
   (camlPEG_choicel (CONS h t) = peg_choice h (camlPEG_choicel t)
    camlPEG_sumID)`;;

let camlPEG_pegf_def = new_definition
  `camlPEG_pegf sym f = peg_seq sym (peg_empty []) (\l1 l2. f l1)`;;

let camlPEG_seql_def = new_definition
  `camlPEG_seql l f = camlPEG_pegf (ITLIST (\p acc. peg_seq p acc APPEND) l
  (peg_empty [])) f`;;

let camlPEG_try_def = new_definition
  `camlPEG_try sym = camlPEG_choicel [sym; peg_empty []]`;;

let camlPEG_tokeq_def = new_definition
  `camlPEG_tokeq t = peg_tok ((=) t) camlPEG_mktokLf`;;

let camlPEG_tokSymP_def = new_definition
  `camlPEG_tokSymP P =
     peg_tok (\t. (OPTION_BIND (destSymbol t) (\s. assert (P s))) = SOME
       one) camlPEG_mktokLf`;;

let tokIdP_def = new_definition
  `tokIdP P =
     peg_tok (\t. (OPTION_BIND (destIdent t) (\s. assert (P s))) = SOME
       one) camlPEG_mktokLf`;;

let tokPragma_def = new_definition
  `tokPragma =
     peg_tok (\t. (OPTION_BIND (destPragma t) (\s. SOME one)) = SOME one)
       camlPEG_mktokLf`;;

let camlPEG_pnt_def = new_definition
  `camlPEG_pnt ntsym = peg_nt (INL ntsym) I`;;

(* -------------------------------------------------------------------------
 * Non-terminals
 * ------------------------------------------------------------------------- *)

let validCoreOpChar_def = new_definition
  `validCoreOpChar c = MEM c "$&*+-/=>@^|"`;;

(* HOL4 camlPEGScript.sml:101-103: the definition *)

let camlPEG_validPrefixSym_def = new_definition
  `camlPEG_validPrefixSym s <=> ~(s = "") /\
     (HD s = (CHR 33) \/ HD s = (CHR 63) \/ HD s = (CHR 126) /\ 2 <= LENGTH
       s) /\
     ALL validOpChar (TL s)`;;

let validInfixSym_def = new_definition
  `validInfixSym s <=> ~(s = "") /\
     (validCoreOpChar (HD s) \/ HD s = (CHR 37) \/ HD s = (CHR 60) \/
      HD s = (CHR 35) /\ 2 <= LENGTH s) /\
     ALL validOpChar (TL s)`;;

let validMultOp_def = new_definition
  `validMultOp s <=> ~(s = "") /\
     (s = "%" \/
      s = "/" \/
      ((HD s = (CHR 42) \/ HD s = (CHR 37) \/ HD s = (CHR 47)) /\
         2 <= LENGTH s /\ ALL validOpChar (TL s)))`;;

let validAddOp_def = new_definition
  `validAddOp s <=> ~(s = "") /\
     (HD s = (CHR 43) \/ HD s = (CHR 45)) /\
     2 <= LENGTH s /\
     ALL validOpChar (TL s)`;;

let validRelOp_def = new_definition
  `validRelOp s <=> ~(s = "") /\
     (HD s = (CHR 61) \/ HD s = (CHR 60) \/ HD s = (CHR 62) \/ HD s = (CHR
       124) \/
      HD s = (CHR 38) \/ HD s = (CHR 36)) /\
     2 <= LENGTH s /\
     ALL validOpChar (TL s)`;;

(* HOL4 camlPEGScript.sml:146-150: the definition *)

let validCatOp_def = new_definition
  `validCatOp s <=> ~(s = "") /\
     (HD s = (CHR 64) \/ HD s = CHR 94) /\
     ALL validOpChar (TL s)`;;

let idChar_def = new_definition
  `idChar P = ALL (\c. P c \/ c = (CHR 95) \/ c = (CHR 39) \/ isDigit c)`;;

(* Modules and type constructors according to HOL light are words that start
 * with a capital letter and then only lowercase letters, digits or ticks.
 * There has to be at least one character in the tail of the string, and at
 * least one of those need to be lowercase.
 *)

(* HOL4 camlPEGScript.sml:169-175: the definition *)

(* Names of values according to HOL light are all combinations of identifier
 * characters (alphanumerics, underscore and tick) _except_ those that are
 * module names or type constructors. In particular, if there are letters in
 * the tail of the string, then at least one of those letters must be
 * uppercase.
 *)

let identMixed_def = new_definition
  `identMixed s <=> ~(s = "") /\
     idChar isAlpha (TL s) /\
     ((isLower (HD s) \/ HD s = (CHR 95)) \/
      (isUpper (HD s) /\
       (EX isAlpha (TL s) ==> EX isUpper (TL s))))`;;

(* Names of types start with a lowercase letter or underscore.
 *)

let identLower_def = new_definition
  `identLower s <=> ~(s = "") /\
     (isLower (HD s) \/ HD s = (CHR 95)) /\
     idChar isAlpha (TL s)`;;

let camlNT_INDUCT,camlNT_RECURSION = define_datatype
  "camlNT =
     // hol-light specific operators
     camlPEG_nEHolInfix
   | camlPEG_nHolInfixOp
     // different sorts of names
   | camlPEG_nValuePath
   | camlPEG_nValueName
   | camlPEG_nConstr
   | camlPEG_nConstrName
   | camlPEG_nTypeConstr
   | camlPEG_nTypeConstrName
   | camlPEG_nModulePath
   | camlPEG_nModuleName
   | camlPEG_nModTypePath
   | camlPEG_nModTypeName
   | camlPEG_nFieldName
   | camlPEG_nOperatorName
     // expressions
   | camlPEG_nLiteral
   | camlPEG_nIdent
   | camlPEG_nEBase
   | camlPEG_nEList
   | camlPEG_nEApp
   | camlPEG_nEConstr
   | camlPEG_nEFunapp
   | camlPEG_nEAssert
   | camlPEG_nELazy
   | camlPEG_nEPrefix
   | camlPEG_nEIndex
   | camlPEG_nENeg
   | camlPEG_nEShift
   | camlPEG_nEMult
   | camlPEG_nERecProj
   | camlPEG_nERecUpdate
   | camlPEG_nERecCons
   | camlPEG_nEAdd
   | camlPEG_nECons
   | camlPEG_nECat
   | camlPEG_nERel
   | camlPEG_nEAnd
   | camlPEG_nEOr
   | camlPEG_nEProd
   | camlPEG_nEAssign
   | camlPEG_nEIf
   | camlPEG_nESeq
   | camlPEG_nEMatch
   | camlPEG_nETry
   | camlPEG_nEFun
   | camlPEG_nEFunction
   | camlPEG_nELet
   | camlPEG_nELetRec
   | camlPEG_nEWhile
   | camlPEG_nEFor
   | camlPEG_nExpr
   | camlPEG_nEUnclosed
     // expressions that bind everything to the right
     // indexing
   | camlPEG_nArrIdx
   | camlPEG_nStrIdx
     // record updates
   | camlPEG_nUpdate
   | camlPEG_nUpdates
   | camlPEG_nFieldDec
   | camlPEG_nFieldDecs
     // pattern matches
   | camlPEG_nLetBinding
   | camlPEG_nLetBindings
   | camlPEG_nLetRecBinding
   | camlPEG_nLetRecBindings
   | camlPEG_nPatternMatch
   | camlPEG_nPatternMatches
     // type definitions
   | camlPEG_nTypeDefinition
   | camlPEG_nTypeDef
   | camlPEG_nTypeDefs
   | camlPEG_nTypeParams
   | camlPEG_nTypeInfo
   | camlPEG_nTypeRepr
   | camlPEG_nTypeReprs
   | camlPEG_nConstrDecl
   | camlPEG_nConstrArgs
   | camlPEG_nRecord
   | camlPEG_nExcDefinition
     // patterns
   | camlPEG_nPAny
   | camlPEG_nPList
   | camlPEG_nPPar
   | camlPEG_nPBase
   | camlPEG_nPRecFields
   | camlPEG_nPCons
   | camlPEG_nPAs
   | camlPEG_nPOps
   | camlPEG_nPattern
   | camlPEG_nPatterns
     // types
   | camlPEG_nTypeList
   | camlPEG_nTypeLists
   | camlPEG_nTVar
   | camlPEG_nTBase
   | camlPEG_nTConstr
   | camlPEG_nTProd
   | camlPEG_nTFun
   | camlPEG_nType
     // module types
   | camlPEG_nSigSpec
   | camlPEG_nSigItems
   | camlPEG_nSigItem
   | camlPEG_nModTypeAssign
   | camlPEG_nModTypeAsc
   | camlPEG_nModAscApp
   | camlPEG_nModAscApps
   | camlPEG_nValType
   | camlPEG_nExcType
   | camlPEG_nModuleTypeDef
   | camlPEG_nIncludeMod
   | camlPEG_nOpenMod
     // definitions
   | camlPEG_nDefinition
   | camlPEG_nTopLet
   | camlPEG_nTopLetRec
   | camlPEG_nModuleItem
   | camlPEG_nModuleItems
   | camlPEG_nOpen
   | camlPEG_nModExpr
   | camlPEG_nModuleDef
   | camlPEG_nModuleType
   | camlPEG_nSemis
   | camlPEG_nExprItem
   | camlPEG_nExprItems
   | camlPEG_nDefItem
     // misc
   | camlPEG_nShiftOp
   | camlPEG_nMultOp
   | camlPEG_nAddOp
   | camlPEG_nRelOp
   | camlPEG_nAndOp
   | camlPEG_nOrOp
   | camlPEG_nCatOp
   | camlPEG_nPrefixOp
   | camlPEG_nAssignOp
   | camlPEG_nPatLiteral
   | camlPEG_nStart
     // Declarations through CakeML pragmas
   | camlPEG_nCakeMLPragma";;

(* Definition of the OCaml PEG.
 *)

let camlPEG_def = new_definition
  `camlPEG = mk_peg (camlPEG_pnt camlPEG_nStart) "Unexpected end-of-file"
  "Unexpected token" "Expected token, found end-of-file"
  "Not combinator failed" (FEMPTY |++ [
       (
        // -- CakeML code pragmas --------------------------------------------
        INL camlPEG_nCakeMLPragma,
        camlPEG_pegf (tokPragma) (camlPEG_bindNT camlPEG_nCakeMLPragma));
       (
        // -- HOL Light specific ops -----------------------------------------
        INL camlPEG_nHolInfixOp,
        camlPEG_pegf (camlPEG_choicel [camlPEG_tokeq caml_lex_FuncompT;
          camlPEG_tokeq caml_lex_F_FT; camlPEG_tokeq caml_lex_THEN_T;
          camlPEG_tokeq caml_lex_THENC_T;
                       camlPEG_tokeq caml_lex_THENL_T; camlPEG_tokeq
                         caml_lex_THEN_TCL_T; camlPEG_tokeq caml_lex_ORELSE_T;
                       camlPEG_tokeq caml_lex_ORELSEC_T; camlPEG_tokeq
                         caml_lex_ORELSE_TCL_T])
             (camlPEG_bindNT camlPEG_nHolInfixOp));
       (
        // -- Names and paths ------------------------------------------------
        INL camlPEG_nValueName,
        camlPEG_choicel [camlPEG_pegf (tokIdP (identMixed o explode))
          (camlPEG_bindNT camlPEG_nValueName);
                 camlPEG_seql [camlPEG_tokeq caml_lex_LparT; camlPEG_pnt
                   camlPEG_nOperatorName; camlPEG_tokeq caml_lex_RparT]
                      (camlPEG_bindNT camlPEG_nValueName)]);
       (INL camlPEG_nOperatorName,
        camlPEG_pegf (camlPEG_choicel [camlPEG_pnt camlPEG_nShiftOp;
                       camlPEG_pnt camlPEG_nMultOp;
                       camlPEG_pnt camlPEG_nAddOp;
                       camlPEG_pnt camlPEG_nRelOp;
                       camlPEG_pnt camlPEG_nAndOp;
                       camlPEG_pnt camlPEG_nOrOp;
                       camlPEG_pnt camlPEG_nHolInfixOp;
                       camlPEG_pnt camlPEG_nCatOp;
                       camlPEG_pnt camlPEG_nPrefixOp;
                       camlPEG_pnt camlPEG_nAssignOp])
             (camlPEG_bindNT camlPEG_nOperatorName));
       (INL camlPEG_nConstrName,
        camlPEG_pegf (tokIdP (identUpperLower o explode)) (camlPEG_bindNT
          camlPEG_nConstrName));
       (INL camlPEG_nTypeConstrName,
        camlPEG_pegf (tokIdP (identLower o explode)) (camlPEG_bindNT
          camlPEG_nTypeConstrName));
       (INL camlPEG_nModuleName,
        camlPEG_pegf (tokIdP (identUpperLower o explode)) (camlPEG_bindNT
          camlPEG_nModuleName));
       (INL camlPEG_nFieldName,
        camlPEG_pegf (tokIdP (identLower o explode)) (camlPEG_bindNT
          camlPEG_nFieldName));
       (INL camlPEG_nValuePath,
        camlPEG_seql [camlPEG_try (camlPEG_seql [camlPEG_pnt
          camlPEG_nModulePath; camlPEG_tokeq caml_lex_DotT] I); camlPEG_pnt
          camlPEG_nValueName]
             (camlPEG_bindNT camlPEG_nValuePath));
       (
        // Can't use nModulePath in nConstr, because it would parse the
        // nConstrName as a nModuleName (because they're the same). But we can
        // do this:
        // constr ::= mod-name "." constr / constr-name
        INL camlPEG_nConstr,
        camlPEG_pegf (camlPEG_choicel [camlPEG_seql [camlPEG_pnt
          camlPEG_nModuleName; camlPEG_tokeq caml_lex_DotT; camlPEG_pnt
          camlPEG_nConstr] I;
                       camlPEG_pnt camlPEG_nConstrName])
             (camlPEG_bindNT camlPEG_nConstr));
       (INL camlPEG_nTypeConstr,
        camlPEG_seql [camlPEG_try (camlPEG_seql [camlPEG_pnt
          camlPEG_nModulePath; camlPEG_tokeq caml_lex_DotT] I); camlPEG_pnt
          camlPEG_nTypeConstrName]
             (camlPEG_bindNT camlPEG_nTypeConstr));
       (INL camlPEG_nModulePath,
        camlPEG_seql [camlPEG_pnt camlPEG_nModuleName; camlPEG_try
          (camlPEG_seql [camlPEG_tokeq caml_lex_DotT; camlPEG_pnt
          camlPEG_nModulePath] I)]
             (camlPEG_bindNT camlPEG_nModulePath));
       (INL camlPEG_nModTypeName,
        camlPEG_pegf (tokIdP (\x. T)) (camlPEG_bindNT
          camlPEG_nModTypeName));
       (
        // Can't use nModulePath in nModTypePath because of similar reasons to
        // nConstr (there's some ambiguity).
        INL camlPEG_nModTypePath,
        camlPEG_pegf (camlPEG_choicel [camlPEG_seql [camlPEG_pnt
          camlPEG_nModuleName; camlPEG_tokeq caml_lex_DotT; camlPEG_pnt
          camlPEG_nModTypePath] I;
                       camlPEG_pnt camlPEG_nModTypeName])
             (camlPEG_bindNT camlPEG_nModTypePath));
       (
        // -- Definitions (module items) -------------------------------------
        INL camlPEG_nSemis,
        camlPEG_seql [camlPEG_tokeq caml_lex_SemisT; camlPEG_try
          (camlPEG_pnt camlPEG_nSemis)]
             (camlPEG_bindNT camlPEG_nSemis));
       (INL camlPEG_nExprItems,
        camlPEG_seql [camlPEG_try (camlPEG_pnt camlPEG_nSemis); camlPEG_pnt
          camlPEG_nExpr]
             (camlPEG_bindNT camlPEG_nExprItems));
       (INL camlPEG_nExprItem,
        camlPEG_seql [camlPEG_pnt camlPEG_nSemis; camlPEG_pnt camlPEG_nExpr]
             (camlPEG_bindNT camlPEG_nExprItem));
       (INL camlPEG_nDefItem,
        camlPEG_seql [camlPEG_try (camlPEG_pnt camlPEG_nSemis); camlPEG_pnt
          camlPEG_nDefinition]
             (camlPEG_bindNT camlPEG_nDefItem));
       (INL camlPEG_nModuleItems,
        camlPEG_seql [camlPEG_choicel [camlPEG_pnt camlPEG_nExprItems;
          camlPEG_pnt camlPEG_nDefItem];
              camlPEG_try (camlPEG_pnt camlPEG_nModuleItem);
              camlPEG_try (camlPEG_pnt camlPEG_nSemis)]
             (camlPEG_bindNT camlPEG_nModuleItems));
       (INL camlPEG_nModuleItem,
        camlPEG_seql [camlPEG_choicel [camlPEG_pnt camlPEG_nExprItem;
          camlPEG_pnt camlPEG_nDefItem];
              camlPEG_try (camlPEG_pnt camlPEG_nModuleItem)]
             (camlPEG_bindNT camlPEG_nModuleItem));
       (INL camlPEG_nTopLet,
        camlPEG_seql [camlPEG_tokeq caml_lex_LetT; camlPEG_pnt
          camlPEG_nLetBindings]
             (camlPEG_bindNT camlPEG_nTopLet));
       (INL camlPEG_nTopLetRec,
        camlPEG_seql [camlPEG_tokeq caml_lex_LetT; camlPEG_tokeq
          caml_lex_RecT; camlPEG_pnt camlPEG_nLetRecBindings]
             (camlPEG_bindNT camlPEG_nTopLetRec));
       (INL camlPEG_nOpen,
        camlPEG_seql [camlPEG_tokeq caml_lex_OpenT; camlPEG_pnt
          camlPEG_nModulePath]
             (camlPEG_bindNT camlPEG_nOpen));
       (INL camlPEG_nModExpr,
        camlPEG_pegf (camlPEG_choicel [camlPEG_pnt camlPEG_nModulePath;
                       camlPEG_seql [camlPEG_tokeq caml_lex_StructT;
                         camlPEG_try (camlPEG_pnt camlPEG_nModuleItems);
                         camlPEG_tokeq caml_lex_EndT] I])
             (camlPEG_bindNT camlPEG_nModExpr));
       (INL camlPEG_nModuleDef,
        camlPEG_seql [camlPEG_tokeq caml_lex_ModuleT; camlPEG_pnt
          camlPEG_nModuleName;
              camlPEG_try (camlPEG_seql [camlPEG_tokeq caml_lex_ColonT;
                camlPEG_pnt camlPEG_nModuleType] I);
              camlPEG_tokeq caml_lex_EqualT; camlPEG_pnt camlPEG_nModExpr]
             (camlPEG_bindNT camlPEG_nModuleDef));
       (INL camlPEG_nDefinition,
        camlPEG_pegf (camlPEG_choicel [camlPEG_pnt camlPEG_nTopLetRec;
                       camlPEG_pnt camlPEG_nTopLet;
                       camlPEG_pnt camlPEG_nTypeDefinition;
                       camlPEG_pnt camlPEG_nExcDefinition;
                       camlPEG_pnt camlPEG_nOpen;
                       camlPEG_pnt camlPEG_nModuleTypeDef;
                       camlPEG_pnt camlPEG_nModuleDef;
                       // CakeML code pragmas:
                       camlPEG_pnt camlPEG_nCakeMLPragma])
             (
              // include moduleexpr
              // functor versions of the moduletype thing
              camlPEG_bindNT camlPEG_nDefinition));
       (
        // -- Module types (signatures) --------------------------------------
        INL camlPEG_nExcType,
        camlPEG_seql [camlPEG_tokeq caml_lex_ExceptionT; camlPEG_pnt
          camlPEG_nConstrDecl]
             (camlPEG_bindNT camlPEG_nExcType));
       (INL camlPEG_nValType,
        camlPEG_seql [camlPEG_tokeq caml_lex_ValT; camlPEG_pnt
          camlPEG_nValueName; camlPEG_tokeq caml_lex_ColonT; camlPEG_pnt
          camlPEG_nType]
             (camlPEG_bindNT camlPEG_nValType));
       (INL camlPEG_nModAscApp,
        camlPEG_seql [camlPEG_tokeq caml_lex_LparT; camlPEG_pnt
          camlPEG_nModuleName; camlPEG_tokeq caml_lex_ColonT;
              camlPEG_pnt camlPEG_nModuleType; camlPEG_tokeq caml_lex_RparT]
             (camlPEG_bindNT camlPEG_nModAscApp));
       (INL camlPEG_nModAscApps,
        camlPEG_seql [camlPEG_pnt camlPEG_nModAscApp; camlPEG_try
          (camlPEG_pnt camlPEG_nModAscApps)]
             (camlPEG_bindNT camlPEG_nModAscApps));
       (INL camlPEG_nModTypeAsc,
        camlPEG_seql [camlPEG_tokeq caml_lex_ModuleT; camlPEG_tokeq
          caml_lex_TypeT; camlPEG_pnt camlPEG_nModuleName;
              camlPEG_try (camlPEG_pnt camlPEG_nModAscApps);
              camlPEG_tokeq caml_lex_ColonT; camlPEG_pnt
                camlPEG_nModuleType]
             (camlPEG_bindNT camlPEG_nModTypeAsc));
       (INL camlPEG_nModTypeAssign,
        camlPEG_seql [camlPEG_tokeq caml_lex_ModuleT; camlPEG_tokeq
          caml_lex_TypeT; camlPEG_pnt camlPEG_nModTypeName;
              camlPEG_try (camlPEG_seql [camlPEG_tokeq caml_lex_EqualT;
                camlPEG_pnt camlPEG_nModuleType] I)]
             (camlPEG_bindNT camlPEG_nModTypeAssign));
       (INL camlPEG_nOpenMod,
        camlPEG_seql [camlPEG_tokeq caml_lex_OpenT; camlPEG_pnt
          camlPEG_nModulePath]
             (camlPEG_bindNT camlPEG_nOpenMod));
       (INL camlPEG_nIncludeMod,
        camlPEG_seql [camlPEG_tokeq caml_lex_IncludeT; camlPEG_pnt
          camlPEG_nModulePath]
             (camlPEG_bindNT camlPEG_nIncludeMod));
       (INL camlPEG_nSigItem,
        camlPEG_pegf (camlPEG_choicel [camlPEG_pnt camlPEG_nTypeDefinition;
                       camlPEG_pnt camlPEG_nExcType;
                       camlPEG_pnt camlPEG_nValType;
                       camlPEG_pnt camlPEG_nModTypeAsc;
                       camlPEG_pnt camlPEG_nModTypeAssign;
                       camlPEG_pnt camlPEG_nOpenMod;
                       camlPEG_pnt camlPEG_nIncludeMod])
             (camlPEG_bindNT camlPEG_nSigItem));
       (INL camlPEG_nSigItems,
        camlPEG_seql [camlPEG_pnt camlPEG_nSigItem; camlPEG_try (camlPEG_pnt
          camlPEG_nSemis); camlPEG_try (camlPEG_pnt camlPEG_nSigItems)]
             (camlPEG_bindNT camlPEG_nSigItems));
       (INL camlPEG_nSigSpec,
        camlPEG_seql [camlPEG_tokeq caml_lex_SigT; camlPEG_try (camlPEG_pnt
          camlPEG_nSigItems); camlPEG_tokeq caml_lex_EndT]
             (camlPEG_bindNT camlPEG_nSigSpec));
       (INL camlPEG_nModuleType,
        camlPEG_pegf (camlPEG_choicel [camlPEG_pnt camlPEG_nModTypePath;
                       camlPEG_pnt camlPEG_nSigSpec;
                       camlPEG_seql [camlPEG_tokeq caml_lex_LparT;
                         camlPEG_pnt camlPEG_nModuleType; camlPEG_tokeq
                         caml_lex_RparT] I])
             (
              // functor syntax
              camlPEG_bindNT camlPEG_nModuleType));
       (INL camlPEG_nModuleTypeDef,
        camlPEG_seql [camlPEG_tokeq caml_lex_ModuleT; camlPEG_tokeq
          caml_lex_TypeT; camlPEG_pnt camlPEG_nModTypeName; camlPEG_tokeq
          caml_lex_EqualT;
              camlPEG_pnt camlPEG_nModuleType]
             (camlPEG_bindNT camlPEG_nModuleTypeDef));
       (
        // -- Typedef --------------------------------------------------------
        INL camlPEG_nExcDefinition,
        camlPEG_seql [camlPEG_tokeq caml_lex_ExceptionT;
              camlPEG_choicel [camlPEG_seql [camlPEG_pnt
                camlPEG_nConstrName; camlPEG_tokeq caml_lex_EqualT; camlPEG_pnt
                camlPEG_nConstr] I;
                       camlPEG_pnt camlPEG_nConstrDecl]]
             (camlPEG_bindNT camlPEG_nExcDefinition));
       (INL camlPEG_nTypeDefinition,
        camlPEG_seql [camlPEG_tokeq caml_lex_TypeT; camlPEG_try
          (camlPEG_tokeq caml_lex_NonrecT); camlPEG_pnt camlPEG_nTypeDefs]
             (camlPEG_bindNT camlPEG_nTypeDefinition));
       (INL camlPEG_nTypeDef,
        camlPEG_seql [camlPEG_try (camlPEG_pnt camlPEG_nTypeParams);
          camlPEG_pnt camlPEG_nTypeConstrName;
              camlPEG_try (camlPEG_pnt camlPEG_nTypeInfo)]
             (camlPEG_bindNT camlPEG_nTypeDef));
       (INL camlPEG_nTypeDefs,
        camlPEG_seql [camlPEG_pnt camlPEG_nTypeDef; camlPEG_try
          (camlPEG_seql [camlPEG_tokeq caml_lex_AndT; camlPEG_pnt
          camlPEG_nTypeDefs] I)]
             (camlPEG_bindNT camlPEG_nTypeDefs));
       (INL camlPEG_nTypeParams,
        camlPEG_choicel [camlPEG_pegf (camlPEG_pnt camlPEG_nTVar)
          (camlPEG_bindNT camlPEG_nTypeParams);
                 camlPEG_seql [camlPEG_tokeq caml_lex_LparT; camlPEG_pnt
                   camlPEG_nTVar;
                       peg_rpt (camlPEG_seql [camlPEG_tokeq caml_lex_CommaT;
                         camlPEG_pnt camlPEG_nTVar] I) FLAT;
                       camlPEG_tokeq caml_lex_RparT]
                      (camlPEG_bindNT camlPEG_nTypeParams)]);
       (INL camlPEG_nTypeInfo,
        camlPEG_seql [camlPEG_tokeq caml_lex_EqualT;
              camlPEG_choicel [camlPEG_pnt camlPEG_nType; camlPEG_pnt
                camlPEG_nTypeRepr]]
             (camlPEG_bindNT camlPEG_nTypeInfo));
       (INL camlPEG_nTypeRepr,
        camlPEG_seql [camlPEG_try (camlPEG_tokeq caml_lex_BarT); camlPEG_pnt
          camlPEG_nConstrDecl; camlPEG_try (camlPEG_pnt camlPEG_nTypeReprs)]
             (camlPEG_bindNT camlPEG_nTypeRepr));
       (INL camlPEG_nTypeReprs,
        camlPEG_seql [camlPEG_tokeq caml_lex_BarT; camlPEG_pnt
          camlPEG_nConstrDecl; camlPEG_try (camlPEG_pnt camlPEG_nTypeReprs)]
             (camlPEG_bindNT camlPEG_nTypeReprs));
       (INL camlPEG_nConstrDecl,
        camlPEG_seql [camlPEG_pnt camlPEG_nConstrName;
              camlPEG_try (camlPEG_seql [camlPEG_tokeq caml_lex_OfT;
                camlPEG_choicel [camlPEG_pnt camlPEG_nConstrArgs; camlPEG_pnt
                camlPEG_nRecord]] I)]
             (camlPEG_bindNT camlPEG_nConstrDecl));
       (INL camlPEG_nRecord,
        camlPEG_seql [camlPEG_tokeq caml_lex_LbraceT; camlPEG_pnt
          camlPEG_nFieldDecs; camlPEG_try (camlPEG_tokeq caml_lex_SemiT);
          camlPEG_tokeq caml_lex_RbraceT]
             (camlPEG_bindNT camlPEG_nRecord));
       (INL camlPEG_nFieldDecs,
        camlPEG_seql [camlPEG_pnt camlPEG_nFieldDec; camlPEG_try
          (camlPEG_seql [camlPEG_tokeq caml_lex_SemiT; camlPEG_pnt
          camlPEG_nFieldDecs] I)]
             (camlPEG_bindNT camlPEG_nFieldDecs));
       (INL camlPEG_nFieldDec,
        camlPEG_seql [camlPEG_pnt camlPEG_nFieldName; camlPEG_tokeq
          caml_lex_ColonT; camlPEG_pnt camlPEG_nType]
             (camlPEG_bindNT camlPEG_nFieldDec));
       (INL camlPEG_nConstrArgs,
        camlPEG_seql [camlPEG_pnt camlPEG_nTConstr; peg_rpt (camlPEG_seql
          [camlPEG_tokeq caml_lex_StarT; camlPEG_pnt camlPEG_nTConstr] I) FLAT]
             (camlPEG_bindNT camlPEG_nConstrArgs));
       (
        // -- Type5 ----------------------------------------------------------
        INL camlPEG_nTypeList,
        camlPEG_seql [camlPEG_pnt camlPEG_nType; camlPEG_tokeq
          caml_lex_CommaT; camlPEG_pnt camlPEG_nTypeLists]
             (camlPEG_bindNT camlPEG_nTypeList));
       (INL camlPEG_nTypeLists,
        camlPEG_seql [camlPEG_pnt camlPEG_nType; camlPEG_try (camlPEG_seql
          [camlPEG_tokeq caml_lex_CommaT; camlPEG_pnt camlPEG_nTypeLists] I)]
             (camlPEG_bindNT camlPEG_nTypeLists));
       (INL camlPEG_nTVar,
        camlPEG_seql [camlPEG_tokeq caml_lex_TickT; camlPEG_pnt
          camlPEG_nIdent] (camlPEG_bindNT camlPEG_nTVar));
       (INL camlPEG_nTBase,
        camlPEG_pegf (camlPEG_choicel [camlPEG_seql [camlPEG_tokeq
          caml_lex_LparT; camlPEG_pnt camlPEG_nType; camlPEG_tokeq
          caml_lex_RparT] I;
                       camlPEG_seql [camlPEG_tokeq caml_lex_LparT;
                         camlPEG_pnt camlPEG_nTypeList; camlPEG_tokeq
                         caml_lex_RparT;
                             camlPEG_pnt camlPEG_nTypeConstr] I;
                       camlPEG_pnt camlPEG_nTVar])
             (camlPEG_bindNT camlPEG_nTBase));
       (
        // -- Type4 ----------------------------------------------------------
        INL camlPEG_nTConstr,
        camlPEG_choicel [camlPEG_seql [camlPEG_try (camlPEG_pnt
          camlPEG_nTBase); camlPEG_pnt camlPEG_nTypeConstr;
                       peg_rpt (camlPEG_pnt camlPEG_nTypeConstr) FLAT]
                      (camlPEG_bindNT camlPEG_nTConstr);
                 camlPEG_pegf (camlPEG_pnt camlPEG_nTBase) (camlPEG_bindNT
                   camlPEG_nTConstr)]);
       (
        // -- Type3 ----------------------------------------------------------
        INL camlPEG_nTProd,
        camlPEG_seql [camlPEG_pnt camlPEG_nTConstr; peg_rpt (camlPEG_seql
          [camlPEG_tokeq caml_lex_StarT; camlPEG_pnt camlPEG_nTConstr] I) FLAT]
             (camlPEG_bindNT camlPEG_nTProd));
       (
        // -- Type2 ----------------------------------------------------------
        INL camlPEG_nTFun,
        camlPEG_seql [camlPEG_pnt camlPEG_nTProd; camlPEG_try (camlPEG_seql
          [camlPEG_tokeq caml_lex_RarrowT; camlPEG_pnt camlPEG_nTFun] I)]
             (camlPEG_bindNT camlPEG_nTFun));
       (
        // -- Type -----------------------------------------------------------
        INL camlPEG_nType,
        camlPEG_pegf (camlPEG_pnt camlPEG_nTFun) (camlPEG_bindNT
          camlPEG_nType));
       (
        // -- Expr16 ---------------------------------------------------------
        INL camlPEG_nEList,
        camlPEG_seql [camlPEG_tokeq caml_lex_LbrackT;
              camlPEG_try (camlPEG_seql [camlPEG_pnt camlPEG_nEIf;
                         peg_rpt (camlPEG_seql [camlPEG_tokeq
                           caml_lex_SemiT; camlPEG_pnt camlPEG_nEIf] I) FLAT;
                         camlPEG_try (camlPEG_tokeq caml_lex_SemiT)] I);
              camlPEG_tokeq caml_lex_RbrackT]
             (camlPEG_bindNT camlPEG_nEList));
       (INL camlPEG_nLiteral,
        camlPEG_choicel [
          peg_tok caml_lex_isInt (camlPEG_bindNT camlPEG_nLiteral o
            camlPEG_mktokLf);
          peg_tok caml_lex_isString (camlPEG_bindNT camlPEG_nLiteral o
            camlPEG_mktokLf);
          peg_tok isChar (camlPEG_bindNT camlPEG_nLiteral o
            camlPEG_mktokLf);
          peg_tok (\x. MEM x [caml_lex_TrueT; caml_lex_FalseT])
            (camlPEG_bindNT camlPEG_nLiteral o camlPEG_mktokLf)]);
       (INL camlPEG_nIdent,
        peg_tok isIdent (camlPEG_bindNT camlPEG_nIdent o camlPEG_mktokLf));
       (INL camlPEG_nUpdate,
        camlPEG_seql [camlPEG_pnt camlPEG_nFieldName; camlPEG_tokeq
          caml_lex_EqualT; camlPEG_pnt camlPEG_nEIf]
             (camlPEG_bindNT camlPEG_nUpdate));
       (INL camlPEG_nUpdates,
        camlPEG_seql [camlPEG_pnt camlPEG_nUpdate; camlPEG_try (camlPEG_seql
          [camlPEG_tokeq caml_lex_SemiT; camlPEG_pnt camlPEG_nUpdates] I)]
             (camlPEG_bindNT camlPEG_nUpdates));
       (INL camlPEG_nERecUpdate,
        camlPEG_seql [camlPEG_pnt camlPEG_nConstr; camlPEG_tokeq
          caml_lex_LbraceT; camlPEG_pnt camlPEG_nExpr; camlPEG_tokeq
          caml_lex_WithT; camlPEG_pnt camlPEG_nUpdates;
              camlPEG_try (camlPEG_tokeq caml_lex_SemiT); camlPEG_tokeq
                caml_lex_RbraceT]
             (camlPEG_bindNT camlPEG_nERecUpdate));
       (INL camlPEG_nEBase,
        camlPEG_choicel [
          camlPEG_pegf (camlPEG_pnt camlPEG_nLiteral) (camlPEG_bindNT
            camlPEG_nEBase);
          camlPEG_pegf (camlPEG_pnt camlPEG_nValuePath) (camlPEG_bindNT
            camlPEG_nEBase);
          // N.B. nERecUpdate goes before nConstr, because they coincide
          camlPEG_pegf (camlPEG_pnt camlPEG_nERecUpdate) (camlPEG_bindNT
            camlPEG_nEBase);
          camlPEG_pegf (camlPEG_pnt camlPEG_nConstr) (camlPEG_bindNT
            camlPEG_nEBase);
          camlPEG_pegf (camlPEG_pnt camlPEG_nEList) (camlPEG_bindNT
            camlPEG_nEBase);
          camlPEG_seql [camlPEG_tokeq caml_lex_LparT; camlPEG_tokeq
            caml_lex_RparT] (camlPEG_bindNT camlPEG_nEBase);
          // unit
          camlPEG_seql [camlPEG_tokeq caml_lex_BeginT; camlPEG_tokeq
            caml_lex_EndT] (camlPEG_bindNT camlPEG_nEBase);
          // unit
          camlPEG_seql [camlPEG_tokeq caml_lex_LparT; camlPEG_pnt
            camlPEG_nExpr;
                camlPEG_try (camlPEG_seql [camlPEG_tokeq caml_lex_ColonT;
                  camlPEG_pnt camlPEG_nType] I);
                camlPEG_tokeq caml_lex_RparT] (camlPEG_bindNT
                  camlPEG_nEBase);
          camlPEG_seql [camlPEG_tokeq caml_lex_BeginT; camlPEG_pnt
            camlPEG_nExpr; camlPEG_tokeq caml_lex_EndT] (camlPEG_bindNT
            camlPEG_nEBase)]);
       (
        // -- Expr15 ---------------------------------------------------------
        INL camlPEG_nPrefixOp,
        camlPEG_pegf (camlPEG_tokSymP (camlPEG_validPrefixSym o explode))
             (camlPEG_bindNT camlPEG_nPrefixOp));
       (INL camlPEG_nEPrefix,
        camlPEG_seql [camlPEG_try (camlPEG_pnt camlPEG_nPrefixOp);
          camlPEG_pnt camlPEG_nEBase] (camlPEG_bindNT camlPEG_nEPrefix));
       (
        // -- Expr14.6 -------------------------------------------------------
        INL camlPEG_nArrIdx,
        camlPEG_seql [camlPEG_tokeq caml_lex_DotT; camlPEG_tokeq
          caml_lex_LparT; camlPEG_pnt camlPEG_nExpr; camlPEG_tokeq
          caml_lex_RparT]
             (camlPEG_bindNT camlPEG_nArrIdx));
       (INL camlPEG_nStrIdx,
        camlPEG_seql [camlPEG_tokeq caml_lex_DotT; camlPEG_tokeq
          caml_lex_LbrackT; camlPEG_pnt camlPEG_nExpr; camlPEG_tokeq
          caml_lex_RbrackT]
             (camlPEG_bindNT camlPEG_nStrIdx));
       (INL camlPEG_nEIndex,
        camlPEG_seql [camlPEG_pnt camlPEG_nEPrefix; camlPEG_try
          (camlPEG_choicel [camlPEG_pnt camlPEG_nStrIdx; camlPEG_pnt
          camlPEG_nArrIdx])]
             (camlPEG_bindNT camlPEG_nEIndex));
       (
        // -- Expr14.5 -------------------------------------------------------
        INL camlPEG_nERecProj,
        camlPEG_seql [camlPEG_pnt camlPEG_nEIndex;
              camlPEG_try (camlPEG_seql [camlPEG_tokeq caml_lex_DotT;
                camlPEG_pnt camlPEG_nConstr; camlPEG_tokeq caml_lex_DotT;
                camlPEG_pnt camlPEG_nFieldName] I)]
             (camlPEG_bindNT camlPEG_nERecProj));
       (
        // -- Expr14 ---------------------------------------------------------
        INL camlPEG_nEAssert,
        camlPEG_seql [camlPEG_tokeq caml_lex_AssertT; camlPEG_pnt
          camlPEG_nERecProj] (camlPEG_bindNT camlPEG_nEAssert));
       (INL camlPEG_nELazy,
        camlPEG_seql [camlPEG_tokeq caml_lex_LazyT; camlPEG_pnt
          camlPEG_nERecProj] (camlPEG_bindNT camlPEG_nELazy));
       (INL camlPEG_nEConstr,
        camlPEG_seql [camlPEG_pnt camlPEG_nConstr; camlPEG_pnt
          camlPEG_nERecProj] (camlPEG_bindNT camlPEG_nEConstr));
       (INL camlPEG_nERecCons,
        camlPEG_seql [camlPEG_pnt camlPEG_nConstr;
              camlPEG_tokeq caml_lex_LbraceT; camlPEG_pnt camlPEG_nUpdates;
                camlPEG_try (camlPEG_tokeq caml_lex_SemiT); camlPEG_tokeq
                caml_lex_RbraceT]
             (camlPEG_bindNT camlPEG_nERecCons));
       (INL camlPEG_nEFunapp,
        camlPEG_seql [camlPEG_pnt camlPEG_nERecProj; peg_rpt (camlPEG_pnt
          camlPEG_nERecProj) FLAT]
             (\l. match l with
                    [] -> []
                  | CONS h t -> [FOLDL (\a b. camlPEG_mkNd (INL
                    camlPEG_nEFunapp) [a; b])
                              (camlPEG_mkNd (INL camlPEG_nEFunapp) [h])
                                t]));
       (INL camlPEG_nEApp,
        camlPEG_pegf (camlPEG_choicel (MAP camlPEG_pnt [camlPEG_nELazy;
          camlPEG_nEAssert; camlPEG_nERecCons; camlPEG_nEConstr;
          camlPEG_nEFunapp;
                              camlPEG_nERecProj]))
             (camlPEG_bindNT camlPEG_nEApp));
       (
        // -- Expr13 ---------------------------------------------------------
        INL camlPEG_nEUnclosed,
        camlPEG_pegf (camlPEG_choicel [
                camlPEG_pnt camlPEG_nELetRec; camlPEG_pnt camlPEG_nELet;
                  camlPEG_pnt camlPEG_nEMatch; camlPEG_pnt camlPEG_nEFun;
                  camlPEG_pnt camlPEG_nEFunction;
                camlPEG_pnt camlPEG_nETry; camlPEG_pnt camlPEG_nEWhile;
                  camlPEG_pnt camlPEG_nEFor; camlPEG_pnt camlPEG_nEApp])
             (camlPEG_bindNT camlPEG_nEUnclosed));
       (INL camlPEG_nELetRec,
        camlPEG_seql [camlPEG_tokeq caml_lex_LetT; camlPEG_tokeq
          caml_lex_RecT; camlPEG_pnt camlPEG_nLetRecBindings;
              camlPEG_tokeq caml_lex_InT; camlPEG_pnt camlPEG_nExpr]
             (camlPEG_bindNT camlPEG_nELetRec));
       (INL camlPEG_nELet,
        camlPEG_seql [camlPEG_tokeq caml_lex_LetT; camlPEG_pnt
          camlPEG_nLetBindings;
              camlPEG_tokeq caml_lex_InT; camlPEG_pnt camlPEG_nExpr]
             (camlPEG_bindNT camlPEG_nELet));
       (INL camlPEG_nEMatch,
        camlPEG_seql [camlPEG_tokeq caml_lex_MatchT; camlPEG_pnt
          camlPEG_nExpr; camlPEG_tokeq caml_lex_WithT; camlPEG_pnt
          camlPEG_nPatternMatch]
             (camlPEG_bindNT camlPEG_nEMatch));
       (INL camlPEG_nEFun,
        camlPEG_seql [camlPEG_tokeq caml_lex_FunT; camlPEG_pnt
          camlPEG_nPatterns;
              camlPEG_try (camlPEG_seql [camlPEG_tokeq caml_lex_ColonT;
                camlPEG_pnt camlPEG_nType] I);
              camlPEG_tokeq caml_lex_RarrowT; camlPEG_pnt camlPEG_nExpr]
             (camlPEG_bindNT camlPEG_nEFun));
       (INL camlPEG_nEFunction,
        camlPEG_seql [camlPEG_tokeq caml_lex_FunctionT; camlPEG_pnt
          camlPEG_nPatternMatch]
             (camlPEG_bindNT camlPEG_nEFunction));
       (INL camlPEG_nETry,
        camlPEG_seql [camlPEG_tokeq caml_lex_TryT; camlPEG_pnt
          camlPEG_nExpr; camlPEG_tokeq caml_lex_WithT; camlPEG_pnt
          camlPEG_nPatternMatch]
             (camlPEG_bindNT camlPEG_nETry));
       (INL camlPEG_nEWhile,
        camlPEG_seql [camlPEG_tokeq caml_lex_WhileT; camlPEG_pnt
          camlPEG_nExpr; camlPEG_tokeq caml_lex_DoT; camlPEG_pnt camlPEG_nExpr;
          camlPEG_tokeq caml_lex_DoneT]
             (camlPEG_bindNT camlPEG_nEWhile));
       (INL camlPEG_nEFor,
        camlPEG_seql [camlPEG_tokeq caml_lex_ForT; camlPEG_pnt
          camlPEG_nValueName; camlPEG_tokeq caml_lex_EqualT; camlPEG_pnt
          camlPEG_nExpr;
              camlPEG_choicel [camlPEG_tokeq caml_lex_ToT; camlPEG_tokeq
                caml_lex_DowntoT]; camlPEG_pnt camlPEG_nExpr;
              camlPEG_tokeq caml_lex_DoT; camlPEG_pnt camlPEG_nExpr;
                camlPEG_tokeq caml_lex_DoneT]
             (camlPEG_bindNT camlPEG_nEFor));
       (
        // -- Expr12 ---------------------------------------------------------
        INL camlPEG_nENeg,
        camlPEG_seql [camlPEG_try (camlPEG_choicel [camlPEG_tokeq
          caml_lex_MinusT; camlPEG_tokeq caml_lex_MinusFT]);
              // try the non-closed expressions or an application
              camlPEG_pnt camlPEG_nEUnclosed]
             (camlPEG_bindNT camlPEG_nENeg));
       (
        // -- Expr11 ---------------------------------------------------------
        INL camlPEG_nShiftOp,
        camlPEG_pegf (camlPEG_choicel [camlPEG_tokSymP (validShiftOp o
          explode); camlPEG_tokeq caml_lex_LslT; camlPEG_tokeq caml_lex_LsrT;
          camlPEG_tokeq caml_lex_AsrT])
             (camlPEG_bindNT camlPEG_nShiftOp));
       (INL camlPEG_nEShift,
        camlPEG_seql [camlPEG_pnt camlPEG_nENeg; camlPEG_try (camlPEG_seql
          [camlPEG_pnt camlPEG_nShiftOp; camlPEG_pnt camlPEG_nEShift] I)]
             (camlPEG_bindNT camlPEG_nEShift));
       (
        // -- Expr10 ---------------------------------------------------------
        INL camlPEG_nMultOp,
        camlPEG_pegf (camlPEG_choicel [camlPEG_tokeq caml_lex_StarT;
          camlPEG_tokeq caml_lex_ModT; camlPEG_tokeq caml_lex_LandT;
          camlPEG_tokeq caml_lex_LorT;
                       camlPEG_tokeq caml_lex_LxorT; camlPEG_tokSymP
                         (validMultOp o explode)])
             (camlPEG_bindNT camlPEG_nMultOp));
       (INL camlPEG_nEMult,
        camlPEG_peg_linfix (INL camlPEG_nEMult) (camlPEG_pnt
          camlPEG_nEShift) (camlPEG_pnt camlPEG_nMultOp));
       (
        // -- Expr9 ----------------------------------------------------------
        INL camlPEG_nAddOp,
        camlPEG_pegf (camlPEG_choicel [camlPEG_tokeq caml_lex_PlusT;
          camlPEG_tokeq caml_lex_MinusT; camlPEG_tokeq caml_lex_MinusFT;
                       camlPEG_tokSymP (validAddOp o explode)])
             (camlPEG_bindNT camlPEG_nAddOp));
       (INL camlPEG_nEAdd,
        camlPEG_peg_linfix (INL camlPEG_nEAdd) (camlPEG_pnt camlPEG_nEMult)
          (camlPEG_pnt camlPEG_nAddOp));
       (
        // -- Expr8 ----------------------------------------------------------
        INL camlPEG_nECons,
        camlPEG_seql [camlPEG_pnt camlPEG_nEAdd; camlPEG_try (camlPEG_seql
          [camlPEG_tokeq caml_lex_ColonsT; camlPEG_pnt camlPEG_nECons] I)]
             (camlPEG_bindNT camlPEG_nECons));
       (
        // -- Expr7 ----------------------------------------------------------
        INL camlPEG_nCatOp,
        camlPEG_pegf (camlPEG_tokSymP (validCatOp o explode))
             (camlPEG_bindNT camlPEG_nCatOp));
       (INL camlPEG_nECat,
        camlPEG_seql [camlPEG_pnt camlPEG_nECons; camlPEG_try (camlPEG_seql
          [camlPEG_pnt camlPEG_nCatOp; camlPEG_pnt camlPEG_nECat] I)]
             (camlPEG_bindNT camlPEG_nECat));
       (
        // -- Expr6 ----------------------------------------------------------
        INL camlPEG_nRelOp,
        camlPEG_pegf (camlPEG_choicel [camlPEG_tokeq caml_lex_EqualT;
          camlPEG_tokeq caml_lex_LessT; camlPEG_tokeq caml_lex_GreaterT;
          camlPEG_tokeq caml_lex_NeqT;
                       camlPEG_tokSymP (validRelOp o explode)])
             (camlPEG_bindNT camlPEG_nRelOp));
       (INL camlPEG_nERel,
        camlPEG_peg_linfix (INL camlPEG_nERel) (camlPEG_pnt camlPEG_nECat)
          (camlPEG_pnt camlPEG_nRelOp));
       (
        // -- Expr5 ----------------------------------------------------------
        INL camlPEG_nAndOp,
        camlPEG_pegf (camlPEG_choicel [camlPEG_tokeq caml_lex_AmpT;
          camlPEG_tokeq caml_lex_AndalsoT])
             (camlPEG_bindNT camlPEG_nAndOp));
       (INL camlPEG_nEAnd,
        camlPEG_seql [camlPEG_pnt camlPEG_nERel; camlPEG_try (camlPEG_seql
          [camlPEG_pnt camlPEG_nAndOp; camlPEG_pnt camlPEG_nEAnd] I)]
             (camlPEG_bindNT camlPEG_nEAnd));
       (
        // -- Expr4 ----------------------------------------------------------
        INL camlPEG_nOrOp,
        camlPEG_pegf (camlPEG_choicel [camlPEG_tokeq caml_lex_OrelseT;
          camlPEG_tokeq caml_lex_OrT])
             (camlPEG_bindNT camlPEG_nOrOp));
       (INL camlPEG_nEOr,
        camlPEG_seql [camlPEG_pnt camlPEG_nEAnd; camlPEG_try (camlPEG_seql
          [camlPEG_pnt camlPEG_nOrOp; camlPEG_pnt camlPEG_nEOr] I)]
             (camlPEG_bindNT camlPEG_nEOr));
       (
        // -- Expr 3.5 -------------------------------------------------------
        INL camlPEG_nEHolInfix,
        camlPEG_peg_linfix (INL camlPEG_nEHolInfix) (camlPEG_pnt
          camlPEG_nEOr) (camlPEG_pnt camlPEG_nHolInfixOp));
       (
        // -- Expr3 ----------------------------------------------------------
        INL camlPEG_nEProd,
        camlPEG_seql [camlPEG_pnt camlPEG_nEHolInfix;
              peg_rpt (camlPEG_seql [camlPEG_tokeq caml_lex_CommaT;
                camlPEG_pnt camlPEG_nEHolInfix] I) FLAT]
             (camlPEG_bindNT camlPEG_nEProd));
       (
        // -- Expr2: assignments ---------------------------------------------
        INL camlPEG_nAssignOp,
        camlPEG_pegf (camlPEG_choicel [camlPEG_tokeq caml_lex_UpdateT;
          camlPEG_tokeq caml_lex_LarrowT])
             (camlPEG_bindNT camlPEG_nAssignOp));
       (INL camlPEG_nEAssign,
        camlPEG_seql [camlPEG_pnt camlPEG_nEProd; camlPEG_try (camlPEG_seql
          [camlPEG_pnt camlPEG_nAssignOp; camlPEG_pnt camlPEG_nEAssign] I)]
             (camlPEG_bindNT camlPEG_nEAssign));
       (
        // -- Expr1 ----------------------------------------------------------
        INL camlPEG_nEIf,
        camlPEG_pegf (camlPEG_choicel [camlPEG_seql [camlPEG_tokeq
          caml_lex_IfT; camlPEG_pnt camlPEG_nExpr; camlPEG_tokeq
          caml_lex_ThenT; camlPEG_pnt camlPEG_nEIf;
                             camlPEG_try (camlPEG_seql [camlPEG_tokeq
                               caml_lex_ElseT; camlPEG_pnt camlPEG_nEIf] I)] I;
                       camlPEG_pnt camlPEG_nEAssign])
             (camlPEG_bindNT camlPEG_nEIf));
       (
        // -- Expr: ----------------------------------------------------------
        INL camlPEG_nESeq,
        camlPEG_seql [camlPEG_pnt camlPEG_nEIf; camlPEG_try (camlPEG_seql
          [camlPEG_tokeq caml_lex_SemiT; camlPEG_pnt camlPEG_nExpr] I)]
             (camlPEG_bindNT camlPEG_nESeq));
       (INL camlPEG_nExpr,
        camlPEG_pegf (camlPEG_choicel [camlPEG_pnt camlPEG_nESeq])
             (camlPEG_bindNT camlPEG_nExpr));
       (
        // -- Pattern matches ------------------------------------------------
        INL camlPEG_nPatternMatch,
        camlPEG_seql [camlPEG_try (camlPEG_tokeq caml_lex_BarT); camlPEG_pnt
          camlPEG_nPatternMatches]
             (camlPEG_bindNT camlPEG_nPatternMatch));
       (INL camlPEG_nPatternMatches,
        camlPEG_seql [camlPEG_pnt camlPEG_nPattern;
              camlPEG_try (camlPEG_seql [camlPEG_tokeq caml_lex_WhenT;
                camlPEG_pnt camlPEG_nExpr] I);
              camlPEG_tokeq caml_lex_RarrowT; camlPEG_pnt camlPEG_nExpr;
              camlPEG_try (camlPEG_seql [camlPEG_tokeq caml_lex_BarT;
                camlPEG_pnt camlPEG_nPatternMatches] I)]
             (camlPEG_bindNT camlPEG_nPatternMatches));
       (
        // -- Let bindings ---------------------------------------------------
        INL camlPEG_nLetRecBinding,
        camlPEG_seql [camlPEG_pnt camlPEG_nValueName;
              camlPEG_try (camlPEG_pnt camlPEG_nPatterns);
              camlPEG_try (camlPEG_seql [camlPEG_tokeq caml_lex_ColonT;
                camlPEG_pnt camlPEG_nType] I);
              camlPEG_tokeq caml_lex_EqualT; camlPEG_pnt camlPEG_nExpr]
             (camlPEG_bindNT camlPEG_nLetRecBinding));
       (INL camlPEG_nLetRecBindings,
        camlPEG_seql [camlPEG_pnt camlPEG_nLetRecBinding; camlPEG_try
          (camlPEG_seql [camlPEG_tokeq caml_lex_AndT; camlPEG_pnt
          camlPEG_nLetRecBindings] I)]
             (camlPEG_bindNT camlPEG_nLetRecBindings));
       (INL camlPEG_nLetBinding,
        camlPEG_pegf (camlPEG_choicel [camlPEG_seql [camlPEG_pnt
          camlPEG_nPattern; camlPEG_tokeq caml_lex_EqualT; camlPEG_pnt
          camlPEG_nExpr] I;
                       camlPEG_seql [camlPEG_pnt camlPEG_nValueName;
                         camlPEG_try (camlPEG_pnt camlPEG_nPatterns);
                             camlPEG_try (camlPEG_seql [camlPEG_tokeq
                               caml_lex_ColonT; camlPEG_pnt camlPEG_nType] I);
                             camlPEG_tokeq caml_lex_EqualT; camlPEG_pnt
                               camlPEG_nExpr] I])
             (camlPEG_bindNT camlPEG_nLetBinding));
       (INL camlPEG_nLetBindings,
        camlPEG_seql [camlPEG_pnt camlPEG_nLetBinding; camlPEG_try
          (camlPEG_seql [camlPEG_tokeq caml_lex_AndT; camlPEG_pnt
          camlPEG_nLetBindings] I)]
             (camlPEG_bindNT camlPEG_nLetBindings));
       (
        // -- Pat3 -----------------------------------------------------------
        INL camlPEG_nPAny,
        // ::= '_'
        camlPEG_pegf (camlPEG_tokeq caml_lex_AnyT) (camlPEG_bindNT
          camlPEG_nPAny));
       (INL camlPEG_nPList,
        // ::= '[' (p ';')* p? ']'
        camlPEG_seql [camlPEG_tokeq caml_lex_LbrackT;
              peg_rpt (camlPEG_seql [camlPEG_pnt camlPEG_nPattern;
                camlPEG_tokeq caml_lex_SemiT] I) FLAT; camlPEG_try (camlPEG_pnt
                camlPEG_nPattern);
              camlPEG_tokeq caml_lex_RbrackT]
             (camlPEG_bindNT camlPEG_nPList));
       (INL camlPEG_nPPar,
        // ::= '(' (p (':' ty)?)? ')'
        camlPEG_seql [camlPEG_tokeq caml_lex_LparT;
              camlPEG_try (camlPEG_seql [camlPEG_pnt camlPEG_nPattern;
                         camlPEG_try (camlPEG_seql [camlPEG_tokeq
                           caml_lex_ColonT; camlPEG_pnt camlPEG_nType] I)] I);
              camlPEG_tokeq caml_lex_RparT]
             (camlPEG_bindNT camlPEG_nPPar));
       (INL camlPEG_nPatLiteral,
        camlPEG_choicel [camlPEG_pegf (camlPEG_pnt camlPEG_nLiteral)
          (camlPEG_bindNT camlPEG_nPatLiteral);
                 camlPEG_seql [camlPEG_tokeq caml_lex_MinusT; peg_tok
                   caml_lex_isInt camlPEG_mktokLf]
                      (camlPEG_bindNT camlPEG_nPatLiteral)]);
       (INL camlPEG_nPBase,
        // ::= any / var / lit / list / '(' p ')' / constr
        camlPEG_pegf (camlPEG_choicel [camlPEG_pnt camlPEG_nPatLiteral;
          camlPEG_pnt camlPEG_nValueName; camlPEG_pnt camlPEG_nPAny;
          camlPEG_pnt camlPEG_nPList;
                       camlPEG_pnt camlPEG_nPPar; camlPEG_pnt
                         camlPEG_nConstr])
             (camlPEG_bindNT camlPEG_nPBase));
       (
        // -- Pat2 -----------------------------------------------------------
        INL camlPEG_nPRecFields,
        // '{' field (';' field)* ';'? '}'
        camlPEG_seql [camlPEG_tokeq caml_lex_LbraceT;
              camlPEG_pnt camlPEG_nFieldName;
              peg_rpt (camlPEG_seql [camlPEG_tokeq caml_lex_SemiT;
                camlPEG_pnt camlPEG_nFieldName] I) FLAT;
              camlPEG_try (camlPEG_tokeq caml_lex_SemiT);
              camlPEG_tokeq caml_lex_RbraceT]
             (camlPEG_bindNT camlPEG_nPRecFields));
       (INL camlPEG_nPCons,
        // ::= constr ('{' fields '}' | p?)
        camlPEG_pegf (camlPEG_choicel [camlPEG_seql [camlPEG_pnt
          camlPEG_nConstr;
                             camlPEG_choicel [camlPEG_pnt
                               camlPEG_nPRecFields; camlPEG_pnt
                               camlPEG_nPBase]] I;
                       camlPEG_pnt camlPEG_nPBase])
             (camlPEG_bindNT camlPEG_nPCons));
       (INL camlPEG_nPAs,
        // ::= p ('as' id)*
        camlPEG_seql [camlPEG_pnt camlPEG_nPCons; peg_rpt (camlPEG_seql
          [camlPEG_tokeq caml_lex_AsT; camlPEG_pnt camlPEG_nIdent] I) FLAT]
             (camlPEG_bindNT camlPEG_nPAs));
       (
        // -- Pat1 -----------------------------------------------------------
        INL camlPEG_nPOps,
        camlPEG_seql [camlPEG_pnt camlPEG_nPAs; peg_rpt (camlPEG_seql
          [peg_tok (\t. t = caml_lex_ColonsT \/ t = caml_lex_CommaT \/ t =
          caml_lex_BarT)
                              camlPEG_mktokLf; camlPEG_pnt camlPEG_nPAs] I)
                                FLAT]
             (camlPEG_bindNT camlPEG_nPOps));
       (INL camlPEG_nPattern,
        camlPEG_pegf (camlPEG_pnt camlPEG_nPOps) (camlPEG_bindNT
          camlPEG_nPattern));
       (
        // This rule is used for the patterns in let (rec) and fun, and since
        // * these allow curried pattern arguments, we must not let applications
        // * and similar be unparenthesized. This is why we accept nPBase instead
        // * of nPattern. nPBase contains single-token patterns, and patterns
        // * enclosed in [] or ().
        INL camlPEG_nPatterns,
        camlPEG_seql [camlPEG_pnt camlPEG_nPBase; camlPEG_try (camlPEG_pnt
          camlPEG_nPatterns)]
             (camlPEG_bindNT camlPEG_nPatterns));
       (INL camlPEG_nStart,
        camlPEG_seql [camlPEG_try (camlPEG_pnt camlPEG_nModuleItems)]
          (camlPEG_bindNT camlPEG_nStart))])`;;

(* -------------------------------------------------------------------------
 * Some of this is used in proving parser side conditions in translation later.
 * ------------------------------------------------------------------------- *)

(* HOL4 camlPEGScript.sml:815-821: the ML values that the definitions below
   antiquote *)

(* HOL4 camlPEGScript.sml:823-825: ML code, not ported *)

(* HOL4 camlPEGScript.sml:827-842: a theorem that HOL4 states as the value
   of an ML expression: camlpeg_rules_applied *)

(* HOL4 camlPEGScript.sml:844-849: a theorem that HOL4 states as the value
   of an ML expression: FDOM_camlPEG *)

(* HOL4 camlPEGScript.sml:851-854: ML code, not ported *)

(* HOL4 camlPEGScript.sml:856-868: ML code, not ported *)

(* HOL4 camlPEGScript.sml:870-875: a theorem that HOL4 states as the value
   of an ML expression: camlPEG_exec_thm *)

(* HOL4 camlPEGScript.sml:877-886: code that the source has in a comment *)

(* frange_image[local] *)
let camlPEG_frange_image = prove
 (`FRANGE fm = IMAGE (FAPPLY fm) (FDOM fm)`,
  CHEAT_TAC);;

(* HOL4 camlPEGScript.sml:894: ML code, not ported *)

(* HOL4 camlPEGScript.sml:896-899: ML code, not ported *)

(* [local] *)
let peg_start = SIMP_CONV [camlPEG_def] `start camlPEG`;;

(* HOL4 camlPEGScript.sml:903-914: ML code, not ported *)

(* HOL4 camlPEGScript.sml:916-920: ML code, not ported *)

(* HOL4 camlPEGScript.sml:922-931: ML code, not ported *)

(* HOL4 camlPEGScript.sml:933-944: the ML values that the definitions below
   antiquote *)

(* HOL4 camlPEGScript.sml:946-950: ML code, not ported *)

(* peg0_pegf *)
let camlPEG_peg0_pegf = prove
 (`peg0 G (camlPEG_pegf s f) = peg0 G s`,
  CHEAT_TAC);;

(* peg0_seql *)
let camlPEG_peg0_seql = prove
 (`(peg0 G (camlPEG_seql [] f) <=> T) /\
   (peg0 G (camlPEG_seql (CONS h t) f) <=> peg0 G h /\ peg0 G
     (camlPEG_seql t I))`,
  CHEAT_TAC);;

(* peg0_tokeq *)
let camlPEG_peg0_tokeq = prove
 (`peg0 G (camlPEG_tokeq t) = F`,
  CHEAT_TAC);;

(* peg0_tokSymP *)
let camlPEG_peg0_tokSymP = prove
 (`peg0 G (camlPEG_tokSymP P) <=> F`,
  CHEAT_TAC);;
add_simp camlPEG_peg0_tokSymP;;

let peg0_tokIdP = prove
 (`peg0 G (tokIdP P) <=> F`,
  CHEAT_TAC);;
add_simp peg0_tokIdP;;

(* peg0_choicel *)
let camlPEG_peg0_choicel = prove
 (`(peg0 G (camlPEG_choicel []) = F) /\
   (peg0 G (camlPEG_choicel (CONS h t)) <=> peg0 G h \/ pegfail G h
     /\ peg0 G (camlPEG_choicel t))`,
  CHEAT_TAC);;

(* HOL4 camlPEGScript.sml:990-1004: a theorem that HOL4 states as the value
   of an ML expression: th *)

(* HOL4 camlPEGScript.sml:1006-1031: ML code, not ported *)

(* HOL4 camlPEGScript.sml:1033-1045: a theorem that HOL4 states as the value
   of an ML expression: th *)

(* HOL4 camlPEGScript.sml:1047-1071: the ML values that the definitions
   below antiquote *)

(* HOL4 camlPEGScript.sml:1073-1074: a theorem that HOL4 states as the value
   of an ML expression: cml_wfpeg_thm *)

(* subexprs_pnt[local] *)
let camlPEG_subexprs_pnt = prove
 (`subexprs (camlPEG_pnt n) = {camlPEG_pnt n}`,
  CHEAT_TAC);;

(* HOL4 camlPEGScript.sml:1082-1088: a theorem that HOL4 states as the value
   of an ML expression: PEG_exprs *)

(* PEG_wellformed *)
let camlPEG_PEG_wellformed = prove
 (`wfG camlPEG`,
  CHEAT_TAC);;
add_simp camlPEG_PEG_wellformed;;

(* HOL4 camlPEGScript.sml:1100-1103: a theorem that HOL4 states as the value
   of an ML expression: parse_Start_total *)

(* HOL4 camlPEGScript.sml:1105-1108: a theorem that HOL4 states as the value
   of an ML expression: coreloop_Start_total *)

(* HOL4 camlPEGScript.sml:1110-1111: a theorem that HOL4 states as the value
   of an ML expression: owhile_Start_total *)

(* and the interface *)
let _ = unhide_overloads ();;
