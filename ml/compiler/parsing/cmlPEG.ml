(* ======================================================== *)
(*  cmlPEG: ported from HOL4's
    compiler/parsing/cmlPEGScript.sml
    A definition theory, with 25 definitions and 17 theorems.
    Needed by camlPtreeConversion.ml, cmlParse.ml, fromSexp.ml,
    infer.ml, parserProg.ml, pegComplete.ml and pegSound.ml.  *)
(* ======================================================== *)

(*
  Definition of the PEG for CakeML.
  Includes a proof that the PEG is well-formed.
*)

needs "basis/pure/mlstring.ml";;
needs "lib/grammar.ml";;
needs "lib/peg.ml";;
needs "lib/pegexec.ml";;
needs "lib/simpleSexpParse.ml";;
needs "semantics/ast.ml";;
needs "semantics/gram.ml";;
needs "semantics/tokenUtils.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "cmlPEG"
  ["gram"; "tokenUtils"];;

(* HOL4 cmlPEGScript.sml:14: the overload monad_bind, which the port expands *)
(* HOL4 cmlPEGScript.sml:15: the overload assert, which the port expands *)

(* HOL4 cmlPEGScript.sml:17-29: ML code, not ported *)

let cmlPEG_sumID_def = define_cases
  `(cmlPEG_sumID (INL x) = x) /\
   (cmlPEG_sumID (INR y) = y)`;;

let mktokLf_def = new_definition
  `cmlPEG_mktokLf t = [Lf
  ((grammar_TOK:tokens_token->(tokens_token,MMLnonT)grammar_symbol) (FST
  t),SND t)]`;;

let mkNd_def = new_definition
  `cmlPEG_mkNd ntnm l = Nd (ntnm,ptree_list_loc l) l`;;

let bindNT0_def = new_definition
  `cmlPEG_bindNT0 ntnm l = Nd ((INL:MMLnonT->MMLnonT+num)
  ntnm,ptree_list_loc l) l`;;

let bindNT_def = new_definition
  `cmlPEG_bindNT ntnm l = [cmlPEG_bindNT0 ntnm l]`;;

make_size "locs";;
make_size "parsetree";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let mk_linfix_def,mk_linfix_ind = define_wf
  `MEASURE (\(x0,x1,x2). parsetree_size1 locs_size (\x. 0) (\x. 0) x2)`
  `(cmlPEG_mk_linfix tgt acc [] = acc) /\
   (cmlPEG_mk_linfix tgt acc [t] = acc) /\
   (cmlPEG_mk_linfix tgt acc (CONS opt (CONS t rest)) =
     cmlPEG_mk_linfix tgt (cmlPEG_mkNd tgt [acc; opt; t]) rest)`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let mk_rinfix_def,mk_rinfix_ind = define_wf
  `MEASURE (\(x0,x1). parsetree_size1 locs_size (\x. 0) (\x. 0) x1)`
  `(mk_rinfix tgt [] = cmlPEG_mkNd tgt []) /\
   (mk_rinfix tgt [t] = cmlPEG_mkNd tgt [t]) /\
   (mk_rinfix tgt (CONS t (CONS opt rest)) = cmlPEG_mkNd tgt [t; opt;
    mk_rinfix tgt rest])`;;

let peg_linfix_def = new_definition
  `cmlPEG_peg_linfix tgtnt rptsym opsym =
     peg_seq rptsym (peg_rpt (peg_seq opsym rptsym APPEND) FLAT)
         (\a b. match a with
                    [] -> []
                   | CONS h _ -> [cmlPEG_mk_linfix tgtnt (cmlPEG_mkNd
                     tgtnt [h]) b])`;;

(* have to use these versions of choicel and pegf below because the
   "built-in" versions from HOL/examples/ use ARB in their definitions.
   Logically, the ARBs are harmless, but they completely mess with the
   translator
*)
let cmlPEG_choicel_def,cmlPEG_choicel_ind = define_rec
  `(cmlPEG_choicel [] = peg_not (peg_empty []) []) /\
   (cmlPEG_choicel (CONS h t) = peg_choice h (cmlPEG_choicel t)
    cmlPEG_sumID)`;;

let cmlPEG_pegf_def = new_definition
  `cmlPEG_pegf sym f = peg_seq sym (peg_empty []) (\l1 l2. f l1)`;;

let seql_def = new_definition
  `cmlPEG_seql l f = cmlPEG_pegf (ITLIST (\p acc. peg_seq p acc APPEND) l
  (peg_empty [])) f`;;

(* HOL4 cmlPEGScript.sml:94-98: code that the source has in a comment *)

let try_def = new_definition
  `cmlPEG_try sym = cmlPEG_choicel [sym; peg_empty []]`;;

let cmlPEG_tokeq_def = new_definition
  `cmlPEG_tokeq t = peg_tok ((=) t) cmlPEG_mktokLf`;;

let tokSymP_def = new_definition
  `cmlPEG_tokSymP P =
     peg_tok (\t. ((OPTION_BIND) (destSymbolT t) (\s. OPTION_GUARD (P
       s))) = SOME one) cmlPEG_mktokLf`;;

let cmlPEG_pnt_def = new_definition
  `cmlPEG_pnt ntsym = peg_nt ((INL:MMLnonT->MMLnonT+num) ntsym) I`;;

(* ----------------------------------------------------------------------
    PEG for types
   ---------------------------------------------------------------------- *)

let peg_UQConstructorName_def = new_definition
  `peg_UQConstructorName =
     peg_tok (\t. (OPTION_BIND) (destAlphaT t) (\s.
                 OPTION_GUARD (~(s = (implode "")) /\ isUpper (strsub s 0)))
                   = SOME one)
         (cmlPEG_bindNT gram_nUQConstructorName o cmlPEG_mktokLf)`;;

let peg_TypeDec_def = new_definition
  `peg_TypeDec =
     peg_seq (cmlPEG_tokeq tokens_DatatypeT)
         (cmlPEG_peg_linfix ((INL:MMLnonT->MMLnonT+num) gram_nDtypeDecls)
           (cmlPEG_pnt gram_nDtypeDecl)
                     (cmlPEG_tokeq tokens_AndT))
         (\l1 l2. cmlPEG_bindNT gram_nTypeDec (APPEND l1 l2))`;;

(* expressions *)
let peg_V_def = new_definition
  `peg_V =
    cmlPEG_choicel [peg_tok (\t.
                   (OPTION_BIND) (destAlphaT t) (\s.
                      OPTION_GUARD (~(s IN {(implode "before"),(implode
                        "div"),(implode "mod"),(implode "o")}) /\ ~(s =
                        (implode "")) /\ ~(isUpper (strsub s 0)))) = SOME one)
                 (cmlPEG_bindNT gram_nV o cmlPEG_mktokLf);
             cmlPEG_pegf (cmlPEG_tokSymP (gram_validPrefixSym o explode))
               (cmlPEG_bindNT gram_nV)]`;;

let peg_longV_def = new_definition
  `peg_longV = peg_tok (\t. (OPTION_BIND) (destLongidT t) (\(str,s).
                         OPTION_GUARD (~(s = (implode "")) /\ (isAlpha
                           (strsub s 0) ==> ~(isUpper (strsub s 0))))) = SOME
                           one)
                   (cmlPEG_bindNT gram_nFQV o cmlPEG_mktokLf)`;;

let peg_EbaseParenFn_def = new_definition
  `peg_EbaseParenFn l =
     match l with
       [lp; es; rp] -> [cmlPEG_mkNd ((INL:MMLnonT->MMLnonT+num) gram_nEbase)
         [lp; cmlPEG_mkNd ((INL:MMLnonT->MMLnonT+num) gram_nEseq) [es]; rp]]
     | [lp; e; sep; es; rp] ->
       (match tokenUtils_destLf sep with
          NONE -> []
        | SOME t ->
          (match tokenUtils_destTOK t with
             NONE -> []
           | SOME t ->
             if t = tokens_CommaT then
               [
                 cmlPEG_mkNd ((INL:MMLnonT->MMLnonT+num) gram_nEbase) [
                   cmlPEG_mkNd ((INL:MMLnonT->MMLnonT+num) gram_nEtuple)
                     [lp; cmlPEG_mkNd ((INL:MMLnonT->MMLnonT+num) gram_nElist2)
                     [e; sep; es]; rp]]]
             else [
                 cmlPEG_mkNd ((INL:MMLnonT->MMLnonT+num) gram_nEbase) [lp;
                   cmlPEG_mkNd ((INL:MMLnonT->MMLnonT+num) gram_nEseq) [e; sep;
                   es]; rp]]))
     | _ -> []`;;

let peg_EbaseParen_def = new_definition
  `peg_EbaseParen =
     cmlPEG_seql [cmlPEG_tokeq tokens_LparT; cmlPEG_pnt gram_nE;
           cmlPEG_choicel [cmlPEG_tokeq tokens_RparT;
                    cmlPEG_seql [cmlPEG_tokeq tokens_CommaT; cmlPEG_pnt
                      gram_nElist1; cmlPEG_tokeq tokens_RparT] I;
                    cmlPEG_seql [cmlPEG_tokeq tokens_SemicolonT; cmlPEG_pnt
                      gram_nEseq; cmlPEG_tokeq tokens_RparT] I]]
          peg_EbaseParenFn`;;

let peg_StructName_def = new_definition
  `peg_StructName =
     peg_tok (\t. (OPTION_BIND) (destAlphaT t) (\s.
                 OPTION_GUARD (~(s = (implode "")))) = SOME one)
         (cmlPEG_bindNT gram_nStructName o cmlPEG_mktokLf)`;;

make_size "MMLnonT";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let ptPapply0_def,ptPapply0_ind = define_wf
  `MEASURE (\(x0,x1). parsetree_size1 locs_size MMLnonT_size (\x. 0) x1)`
  `ptPapply0 c x2 =
   match x2 with
     [] -> []
   // can't happen
   | [pb_pt] -> cmlPEG_bindNT gram_nPapp [c; pb_pt]
   | CONS pb pbs -> ptPapply0 (cmlPEG_bindNT0 gram_nPConApp [c; pb]) pbs`;;

let ptPapply_def = new_definition
  `ptPapply x1 =
   match x1 with
     [] -> []
   // can't happen
   | [_] -> []
   // can't happen
   | CONS c rest -> ptPapply0 (cmlPEG_bindNT0 gram_nPConApp [c]) rest`;;


let cmlPEG_def = new_definition
  `cmlPEG = mk_peg (cmlPEG_pnt gram_nTopLevelDecs) "Didn't expect an EOF"
  "Failed to see expected token"
  "Failed to see expected token; saw EOF instead" "Not combinator failed"
  (FEMPTY |++
              [((INL:MMLnonT->MMLnonT+num) gram_nV,peg_V);
               ((INL:MMLnonT->MMLnonT+num) gram_nTyvarN,cmlPEG_pegf (peg_tok
                 isTyvarT cmlPEG_mktokLf) (cmlPEG_bindNT gram_nTyvarN));
               ((INL:MMLnonT->MMLnonT+num) gram_nFQV,cmlPEG_choicel
                 [cmlPEG_pegf (cmlPEG_pnt gram_nV) (cmlPEG_bindNT gram_nFQV);
                 peg_longV]);
               ((INL:MMLnonT->MMLnonT+num) gram_nEapp,
                cmlPEG_seql [cmlPEG_pnt gram_nEbase; peg_rpt (cmlPEG_pnt
                  gram_nEbase) FLAT]
                     (\l.
                        match l with
                          [] -> []
                        | CONS h t -> [FOLDL (\a b. cmlPEG_mkNd
                          ((INL:MMLnonT->MMLnonT+num) gram_nEapp) [a; b])
                              (cmlPEG_mkNd ((INL:MMLnonT->MMLnonT+num)
                                gram_nEapp) [h]) t]));
               ((INL:MMLnonT->MMLnonT+num) gram_nElist1,
                cmlPEG_seql [cmlPEG_pnt gram_nE; cmlPEG_try (cmlPEG_seql
                  [cmlPEG_tokeq tokens_CommaT; cmlPEG_pnt gram_nElist1] I)]
                     (cmlPEG_bindNT gram_nElist1));
               ((INL:MMLnonT->MMLnonT+num) gram_nMultOps,
                cmlPEG_pegf (
                  cmlPEG_choicel (CONS (cmlPEG_tokSymP (validMultSym o
                    explode))
                    (MAP cmlPEG_tokeq [tokens_StarT; tokens_AlphaT (implode
                      "mod"); tokens_AlphaT (implode "div")]))) (cmlPEG_bindNT
                      gram_nMultOps));
               ((INL:MMLnonT->MMLnonT+num) gram_nAddOps,cmlPEG_pegf
                 (cmlPEG_tokSymP (validAddSym o explode)) (cmlPEG_bindNT
                 gram_nAddOps));
               ((INL:MMLnonT->MMLnonT+num) gram_nRelOps,
                cmlPEG_pegf (cmlPEG_choicel [cmlPEG_tokeq tokens_EqualsT;
                  cmlPEG_tokSymP (validRelSym o explode)])
                     (cmlPEG_bindNT gram_nRelOps));
               ((INL:MMLnonT->MMLnonT+num) gram_nListOps,cmlPEG_pegf
                 (cmlPEG_tokSymP (validListSym o explode)) (cmlPEG_bindNT
                 gram_nListOps));
               ((INL:MMLnonT->MMLnonT+num) gram_nCompOps,cmlPEG_pegf
                 (cmlPEG_choicel [cmlPEG_tokeq (tokens_SymbolT (implode ":="));
                              cmlPEG_tokeq (tokens_AlphaT (implode "o"))])
                              (cmlPEG_bindNT gram_nCompOps));
               ((INL:MMLnonT->MMLnonT+num) gram_nOpID,
                cmlPEG_choicel [peg_tok (\t. (OPTION_BIND) (destLongidT t)
                  (\(str,s).
                              OPTION_GUARD (~(s = (implode "")))) = SOME
                                one) (cmlPEG_bindNT gram_nOpID o
                                cmlPEG_mktokLf);
                         peg_tok (\t. (OPTION_BIND) (destSymbolT t) (\s.
                              OPTION_GUARD (~(s = (implode "")))) = SOME
                                one) (cmlPEG_bindNT gram_nOpID o
                                cmlPEG_mktokLf);
                         peg_tok (\t. (OPTION_BIND) (destAlphaT t) (\s.
                              OPTION_GUARD (~(s = (implode "")))) = SOME
                                one) (cmlPEG_bindNT gram_nOpID o
                                cmlPEG_mktokLf);
                         cmlPEG_pegf (cmlPEG_tokeq tokens_StarT)
                           (cmlPEG_bindNT gram_nOpID);
                         cmlPEG_pegf (cmlPEG_tokeq tokens_EqualsT)
                           (cmlPEG_bindNT gram_nOpID)]);
               ((INL:MMLnonT->MMLnonT+num) gram_nEliteral,
                cmlPEG_choicel [peg_tok tokenUtils_isInt (cmlPEG_bindNT
                  gram_nEliteral o cmlPEG_mktokLf);
                         peg_tok tokenUtils_isString (cmlPEG_bindNT
                           gram_nEliteral o cmlPEG_mktokLf);
                         peg_tok isCharT (cmlPEG_bindNT gram_nEliteral o
                           cmlPEG_mktokLf);
                         peg_tok isWordT (cmlPEG_bindNT gram_nEliteral o
                           cmlPEG_mktokLf);
                         peg_tok (IS_SOME o destFFIT) (cmlPEG_bindNT
                           gram_nEliteral o cmlPEG_mktokLf)]);
               ((INL:MMLnonT->MMLnonT+num) gram_nEbase,
                cmlPEG_choicel [cmlPEG_pegf (cmlPEG_pnt gram_nEliteral)
                  (cmlPEG_bindNT gram_nEbase);
                         cmlPEG_seql [cmlPEG_tokeq tokens_LparT;
                           cmlPEG_tokeq tokens_RparT] (cmlPEG_bindNT
                           gram_nEbase);
                         peg_EbaseParen;
                         cmlPEG_seql [cmlPEG_tokeq tokens_LbrackT;
                           cmlPEG_try (cmlPEG_pnt gram_nElist1); cmlPEG_tokeq
                           tokens_RbrackT]
                              (cmlPEG_bindNT gram_nEbase);
                         cmlPEG_seql [cmlPEG_tokeq tokens_LetT; cmlPEG_pnt
                           gram_nLetDecs; cmlPEG_tokeq tokens_InT; cmlPEG_pnt
                           gram_nEseq;
                              cmlPEG_tokeq tokens_EndT] (cmlPEG_bindNT
                                gram_nEbase);
                         cmlPEG_pegf (cmlPEG_pnt gram_nFQV) (cmlPEG_bindNT
                           gram_nEbase);
                         cmlPEG_pegf (cmlPEG_pnt gram_nConstructorName)
                           (cmlPEG_bindNT gram_nEbase);
                         cmlPEG_seql [cmlPEG_tokeq tokens_OpT; cmlPEG_pnt
                           gram_nOpID] (cmlPEG_bindNT gram_nEbase)]);
               ((INL:MMLnonT->MMLnonT+num) gram_nEseq,
                cmlPEG_seql [cmlPEG_pnt gram_nE; cmlPEG_try (cmlPEG_seql
                  [cmlPEG_tokeq tokens_SemicolonT; cmlPEG_pnt gram_nEseq] I)]
                     (cmlPEG_bindNT gram_nEseq));
               ((INL:MMLnonT->MMLnonT+num) gram_nEmult,
                cmlPEG_peg_linfix ((INL:MMLnonT->MMLnonT+num) gram_nEmult)
                  (cmlPEG_pnt gram_nEapp) (cmlPEG_pnt gram_nMultOps));
               ((INL:MMLnonT->MMLnonT+num) gram_nEadd,cmlPEG_peg_linfix
                 ((INL:MMLnonT->MMLnonT+num) gram_nEadd) (cmlPEG_pnt
                 gram_nEmult) (cmlPEG_pnt gram_nAddOps));
               ((INL:MMLnonT->MMLnonT+num) gram_nElistop,
                cmlPEG_seql [cmlPEG_pnt gram_nEadd; cmlPEG_try (cmlPEG_seql
                  [cmlPEG_pnt gram_nListOps; cmlPEG_pnt gram_nElistop] I)]
                     (cmlPEG_bindNT gram_nElistop));
               ((INL:MMLnonT->MMLnonT+num) gram_nErel,cmlPEG_peg_linfix
                 ((INL:MMLnonT->MMLnonT+num) gram_nErel) (cmlPEG_pnt
                 gram_nElistop) (cmlPEG_pnt gram_nRelOps));
               ((INL:MMLnonT->MMLnonT+num) gram_nEcomp,cmlPEG_peg_linfix
                 ((INL:MMLnonT->MMLnonT+num) gram_nEcomp) (cmlPEG_pnt
                 gram_nErel)
                              (cmlPEG_pnt gram_nCompOps));
               ((INL:MMLnonT->MMLnonT+num) gram_nEbefore,cmlPEG_peg_linfix
                 ((INL:MMLnonT->MMLnonT+num) gram_nEbefore) (cmlPEG_pnt
                 gram_nEcomp)
                              (cmlPEG_tokeq (tokens_AlphaT (implode
                                "before"))));
               ((INL:MMLnonT->MMLnonT+num) gram_nEtyped,cmlPEG_seql
                 [cmlPEG_pnt gram_nEbefore;
                              cmlPEG_try (cmlPEG_seql [cmlPEG_tokeq
                                tokens_ColonT; cmlPEG_pnt gram_nType] I)]
                              (cmlPEG_bindNT gram_nEtyped));
               ((INL:MMLnonT->MMLnonT+num) gram_nElogicAND,
                cmlPEG_peg_linfix ((INL:MMLnonT->MMLnonT+num)
                  gram_nElogicAND) (cmlPEG_pnt gram_nEtyped)
                           (cmlPEG_tokeq tokens_AndalsoT));
               ((INL:MMLnonT->MMLnonT+num) gram_nElogicOR,
                cmlPEG_peg_linfix ((INL:MMLnonT->MMLnonT+num)
                  gram_nElogicOR) (cmlPEG_pnt gram_nElogicAND)
                           (cmlPEG_tokeq tokens_OrelseT));
               ((INL:MMLnonT->MMLnonT+num) gram_nEhandle,
                cmlPEG_seql [cmlPEG_pnt gram_nElogicOR;
                      cmlPEG_try (cmlPEG_seql [cmlPEG_tokeq tokens_HandleT;
                        cmlPEG_pnt gram_nPEs] I)]
                     (cmlPEG_bindNT gram_nEhandle));
               ((INL:MMLnonT->MMLnonT+num) gram_nE,
                cmlPEG_choicel [cmlPEG_seql [cmlPEG_tokeq tokens_RaiseT;
                  cmlPEG_pnt gram_nE] (cmlPEG_bindNT gram_nE);
                         cmlPEG_pegf (cmlPEG_pnt gram_nEhandle)
                           (cmlPEG_bindNT gram_nE);
                         cmlPEG_seql [cmlPEG_tokeq tokens_IfT; cmlPEG_pnt
                           gram_nE; cmlPEG_tokeq tokens_ThenT; cmlPEG_pnt
                           gram_nE;
                              cmlPEG_tokeq tokens_ElseT; cmlPEG_pnt gram_nE]
                              (cmlPEG_bindNT gram_nE);
                         cmlPEG_seql [cmlPEG_tokeq tokens_FnT; cmlPEG_pnt
                           gram_nPattern; cmlPEG_tokeq tokens_DarrowT;
                           cmlPEG_pnt gram_nE]
                              (cmlPEG_bindNT gram_nE);
                         cmlPEG_seql [cmlPEG_tokeq tokens_CaseT; cmlPEG_pnt
                           gram_nE; cmlPEG_tokeq tokens_OfT; cmlPEG_pnt
                           gram_nPEs]
                              (cmlPEG_bindNT gram_nE)]);
               ((INL:MMLnonT->MMLnonT+num) gram_nPEs,
                cmlPEG_seql [cmlPEG_pnt gram_nPattern; cmlPEG_tokeq
                  tokens_DarrowT; cmlPEG_pnt gram_nPE] (cmlPEG_bindNT
                  gram_nPEs));
               ((INL:MMLnonT->MMLnonT+num) gram_nPE,
                cmlPEG_choicel [cmlPEG_seql [cmlPEG_tokeq tokens_IfT;
                  cmlPEG_pnt gram_nE; cmlPEG_tokeq tokens_ThenT; cmlPEG_pnt
                  gram_nE;
                              cmlPEG_tokeq tokens_ElseT; cmlPEG_pnt
                                gram_nPE]
                              (cmlPEG_bindNT gram_nPE);
                         cmlPEG_seql [cmlPEG_tokeq tokens_CaseT; cmlPEG_pnt
                           gram_nE; cmlPEG_tokeq tokens_OfT; cmlPEG_pnt
                           gram_nPEs]
                              (cmlPEG_bindNT gram_nPE);
                         cmlPEG_seql [cmlPEG_tokeq tokens_FnT; cmlPEG_pnt
                           gram_nPattern; cmlPEG_tokeq tokens_DarrowT;
                           cmlPEG_pnt gram_nE]
                              (cmlPEG_bindNT gram_nPE);
                         cmlPEG_seql [cmlPEG_tokeq tokens_RaiseT; cmlPEG_pnt
                           gram_nPE] (cmlPEG_bindNT gram_nPE);
                         cmlPEG_seql [cmlPEG_pnt gram_nElogicOR; cmlPEG_pnt
                           gram_nPEsfx] (cmlPEG_bindNT gram_nPE)]);
               ((INL:MMLnonT->MMLnonT+num) gram_nPEsfx,
                cmlPEG_choicel [cmlPEG_seql [cmlPEG_tokeq tokens_HandleT;
                  cmlPEG_pnt gram_nPEs] (cmlPEG_bindNT gram_nPEsfx);
                         cmlPEG_seql [cmlPEG_tokeq tokens_BarT; cmlPEG_pnt
                           gram_nPEs] (cmlPEG_bindNT gram_nPEsfx);
                         cmlPEG_pegf (peg_empty []) (cmlPEG_bindNT
                           gram_nPEsfx)]);
               ((INL:MMLnonT->MMLnonT+num) gram_nAndFDecls,
                cmlPEG_peg_linfix ((INL:MMLnonT->MMLnonT+num)
                  gram_nAndFDecls) (cmlPEG_pnt gram_nFDecl) (cmlPEG_tokeq
                  tokens_AndT));
               ((INL:MMLnonT->MMLnonT+num) gram_nFDecl,
                cmlPEG_seql [cmlPEG_pnt gram_nV; cmlPEG_pnt
                  gram_nPbaseList1; cmlPEG_tokeq tokens_EqualsT; cmlPEG_pnt
                  gram_nE]
                     (cmlPEG_bindNT gram_nFDecl));
               ((INL:MMLnonT->MMLnonT+num) gram_nPbaseList1,
                cmlPEG_seql [cmlPEG_pnt gram_nPbase; cmlPEG_try (cmlPEG_pnt
                  gram_nPbaseList1)]
                     (cmlPEG_bindNT gram_nPbaseList1));
               ((INL:MMLnonT->MMLnonT+num) gram_nType,
                cmlPEG_seql [cmlPEG_pnt gram_nPType; cmlPEG_try (cmlPEG_seql
                  [cmlPEG_tokeq tokens_ArrowT; cmlPEG_pnt gram_nType] I)]
                     (cmlPEG_bindNT gram_nType));
               ((INL:MMLnonT->MMLnonT+num) gram_nDType,
                cmlPEG_seql [cmlPEG_pnt gram_nTbase; peg_rpt (cmlPEG_pnt
                  gram_nTyOp) FLAT]
                     (\subs.
                        match subs with
                            [] -> []
                          | CONS h t -> [FOLDL (\a b. cmlPEG_mkNd
                            ((INL:MMLnonT->MMLnonT+num) gram_nDType) [a; b])
                              (cmlPEG_mkNd ((INL:MMLnonT->MMLnonT+num)
                                gram_nDType) [h]) t]));
               ((INL:MMLnonT->MMLnonT+num) gram_nTbase,
                cmlPEG_choicel [
                  cmlPEG_seql [cmlPEG_tokeq tokens_LparT; cmlPEG_pnt
                    gram_nType; cmlPEG_tokeq tokens_RparT] (cmlPEG_bindNT
                    gram_nTbase);
                  cmlPEG_seql [cmlPEG_tokeq tokens_LparT; cmlPEG_pnt
                    gram_nTypeList2; cmlPEG_tokeq tokens_RparT; cmlPEG_pnt
                    gram_nTyOp]
                       (cmlPEG_bindNT gram_nTbase);
                  peg_tok isTyvarT (cmlPEG_bindNT gram_nTbase o
                    cmlPEG_mktokLf);
                  cmlPEG_pegf (cmlPEG_pnt gram_nTyOp) (cmlPEG_bindNT
                    gram_nTbase)]);
               ((INL:MMLnonT->MMLnonT+num) gram_nPTbase,
                cmlPEG_choicel [
                  cmlPEG_seql [cmlPEG_tokeq tokens_LparT; cmlPEG_pnt
                    gram_nType; cmlPEG_tokeq tokens_RparT] (cmlPEG_bindNT
                    gram_nPTbase);
                  peg_tok isTyvarT (cmlPEG_bindNT gram_nPTbase o
                    cmlPEG_mktokLf);
                  cmlPEG_pegf (cmlPEG_pnt gram_nTyOp) (cmlPEG_bindNT
                    gram_nPTbase)]);
               ((INL:MMLnonT->MMLnonT+num) gram_nTypeList2,
                cmlPEG_seql [cmlPEG_pnt gram_nType; cmlPEG_tokeq
                  tokens_CommaT; cmlPEG_pnt gram_nTypeList1]
                     (cmlPEG_bindNT gram_nTypeList2));
               ((INL:MMLnonT->MMLnonT+num) gram_nTypeList1,
                cmlPEG_seql [cmlPEG_pnt gram_nType; cmlPEG_try (cmlPEG_seql
                  [cmlPEG_tokeq tokens_CommaT; cmlPEG_pnt gram_nTypeList1] I)]
                     (cmlPEG_bindNT gram_nTypeList1));
               ((INL:MMLnonT->MMLnonT+num) gram_nTbaseList,
                cmlPEG_pegf (cmlPEG_try (cmlPEG_seql [cmlPEG_pnt
                  gram_nPTbase; cmlPEG_pnt gram_nTbaseList] I))
                     (cmlPEG_bindNT gram_nTbaseList));
               ((INL:MMLnonT->MMLnonT+num) gram_nTyOp,
                cmlPEG_pegf (cmlPEG_choicel [cmlPEG_pnt gram_nUQTyOp;
                  peg_tok isLongidT cmlPEG_mktokLf])
                     (cmlPEG_bindNT gram_nTyOp));
               ((INL:MMLnonT->MMLnonT+num) gram_nUQTyOp,
                cmlPEG_pegf (peg_tok isAlphaSym cmlPEG_mktokLf)
                  (cmlPEG_bindNT gram_nUQTyOp));
               ((INL:MMLnonT->MMLnonT+num) gram_nPType,
                cmlPEG_seql [cmlPEG_pnt gram_nDType; cmlPEG_try (cmlPEG_seql
                  [cmlPEG_tokeq tokens_StarT; cmlPEG_pnt gram_nPType] I)]
                     (cmlPEG_bindNT gram_nPType));
               ((INL:MMLnonT->MMLnonT+num) gram_nTypeName,
                cmlPEG_choicel [cmlPEG_pegf (cmlPEG_pnt gram_nUQTyOp)
                  (cmlPEG_bindNT gram_nTypeName);
                         cmlPEG_seql [cmlPEG_tokeq tokens_LparT; cmlPEG_pnt
                           gram_nTyVarList;
                              cmlPEG_tokeq tokens_RparT; cmlPEG_pnt
                                gram_nUQTyOp] (cmlPEG_bindNT gram_nTypeName);
                         cmlPEG_seql [peg_tok isTyvarT cmlPEG_mktokLf;
                           cmlPEG_pnt gram_nUQTyOp]
                              (cmlPEG_bindNT gram_nTypeName)]);
               ((INL:MMLnonT->MMLnonT+num) gram_nTyVarList,
                cmlPEG_peg_linfix ((INL:MMLnonT->MMLnonT+num)
                  gram_nTyVarList) (cmlPEG_pnt gram_nTyvarN) (cmlPEG_tokeq
                  tokens_CommaT));
               ((INL:MMLnonT->MMLnonT+num) gram_nTypeDec,peg_TypeDec);
               ((INL:MMLnonT->MMLnonT+num) gram_nDtypeDecl,
                cmlPEG_seql [cmlPEG_pnt gram_nTypeName;
                      cmlPEG_tokeq tokens_EqualsT;
                      cmlPEG_peg_linfix ((INL:MMLnonT->MMLnonT+num)
                        gram_nDtypeCons) (cmlPEG_pnt gram_nDconstructor)
                        (cmlPEG_tokeq tokens_BarT)]
                     (cmlPEG_bindNT gram_nDtypeDecl));
               ((INL:MMLnonT->MMLnonT+num) gram_nDconstructor,
                cmlPEG_seql [cmlPEG_pnt gram_nUQConstructorName; cmlPEG_pnt
                  gram_nTbaseList]
                     (cmlPEG_bindNT gram_nDconstructor));
               ((INL:MMLnonT->MMLnonT+num)
                 gram_nUQConstructorName,peg_UQConstructorName);
               ((INL:MMLnonT->MMLnonT+num) gram_nConstructorName,
                cmlPEG_choicel [
                  cmlPEG_pegf (cmlPEG_pnt gram_nUQConstructorName)
                    (cmlPEG_bindNT gram_nConstructorName);
                  peg_tok (\t. (OPTION_BIND) (destLongidT t) (\(str,s).
                             OPTION_GUARD (~(s = (implode "")) /\
                              isAlpha (strsub s 0) /\
                              isUpper (strsub s 0))) = SOME one)
                      (cmlPEG_bindNT gram_nConstructorName o
                        cmlPEG_mktokLf)]);
               ((INL:MMLnonT->MMLnonT+num) gram_nPbase,
                cmlPEG_pegf
                  (cmlPEG_choicel [cmlPEG_pnt gram_nV; cmlPEG_pnt
                    gram_nConstructorName; peg_tok tokenUtils_isInt
                    cmlPEG_mktokLf;
                            peg_tok tokenUtils_isString cmlPEG_mktokLf;
                              peg_tok isCharT cmlPEG_mktokLf;
                            cmlPEG_pnt gram_nPtuple; cmlPEG_tokeq
                              tokens_UnderbarT;
                            cmlPEG_seql [cmlPEG_tokeq tokens_LbrackT;
                              cmlPEG_try (cmlPEG_pnt gram_nPatternList);
                              cmlPEG_tokeq tokens_RbrackT] I;
                            cmlPEG_seql [cmlPEG_tokeq tokens_OpT; cmlPEG_pnt
                              gram_nOpID] I])
                  (cmlPEG_bindNT gram_nPbase));
               ((INL:MMLnonT->MMLnonT+num) gram_nPapp,
                cmlPEG_choicel [cmlPEG_seql [cmlPEG_pnt
                  gram_nConstructorName; peg_rpt (cmlPEG_pnt gram_nPbase) FLAT]
                          (\pts. if LENGTH pts = 1 then
                              cmlPEG_bindNT gram_nPapp (cmlPEG_bindNT
                                gram_nPbase pts)
                              else match pts with
                              [] -> []
                              | [
                              // can't happen
                              c] -> []
                              |
                              // can't happen
                              _ -> ptPapply pts);
                         cmlPEG_pegf (cmlPEG_pnt gram_nPbase) (cmlPEG_bindNT
                           gram_nPapp)]);
               ((INL:MMLnonT->MMLnonT+num) gram_nPcons,
                cmlPEG_seql [cmlPEG_pnt gram_nPapp;
                      cmlPEG_try (cmlPEG_seql [cmlPEG_tokeq (tokens_SymbolT
                        (implode "::")); cmlPEG_pnt gram_nPcons] I)]
                     (cmlPEG_bindNT gram_nPcons));
               ((INL:MMLnonT->MMLnonT+num) gram_nPas,
                cmlPEG_seql [cmlPEG_try (cmlPEG_seql [cmlPEG_pnt gram_nV;
                  cmlPEG_tokeq tokens_AsT] I);
                      cmlPEG_pnt gram_nPcons]
                     (cmlPEG_bindNT gram_nPas));
               ((INL:MMLnonT->MMLnonT+num) gram_nPattern,
                cmlPEG_seql [cmlPEG_pnt gram_nPas; cmlPEG_try (cmlPEG_seql
                  [cmlPEG_tokeq tokens_ColonT; cmlPEG_pnt gram_nType] I)]
                     (cmlPEG_bindNT gram_nPattern));
               ((INL:MMLnonT->MMLnonT+num) gram_nPatternList,
                cmlPEG_seql [cmlPEG_pnt gram_nPattern;
                      cmlPEG_try (cmlPEG_seql [cmlPEG_tokeq tokens_CommaT;
                        cmlPEG_pnt gram_nPatternList] I)]
                     (cmlPEG_bindNT gram_nPatternList));
               ((INL:MMLnonT->MMLnonT+num) gram_nPtuple,
                cmlPEG_choicel [cmlPEG_seql [cmlPEG_tokeq tokens_LparT;
                  cmlPEG_tokeq tokens_RparT] (cmlPEG_bindNT gram_nPtuple);
                         cmlPEG_seql [cmlPEG_tokeq tokens_LparT; cmlPEG_pnt
                           gram_nPatternList; cmlPEG_tokeq tokens_RparT]
                              (cmlPEG_bindNT gram_nPtuple)]);
               ((INL:MMLnonT->MMLnonT+num) gram_nLetDec,
                cmlPEG_choicel [cmlPEG_seql [cmlPEG_tokeq tokens_ValT;
                  cmlPEG_pnt gram_nPattern; cmlPEG_tokeq tokens_EqualsT;
                  cmlPEG_pnt gram_nE]
                              (cmlPEG_bindNT gram_nLetDec);
                         cmlPEG_seql [cmlPEG_tokeq tokens_FunT; cmlPEG_pnt
                           gram_nAndFDecls] (cmlPEG_bindNT gram_nLetDec)]);
               ((INL:MMLnonT->MMLnonT+num) gram_nLetDecs,
                cmlPEG_choicel [cmlPEG_seql [cmlPEG_pnt gram_nLetDec;
                  cmlPEG_pnt gram_nLetDecs] (cmlPEG_bindNT gram_nLetDecs);
                         cmlPEG_seql [cmlPEG_tokeq tokens_SemicolonT;
                           cmlPEG_pnt gram_nLetDecs] (cmlPEG_bindNT
                           gram_nLetDecs);
                         cmlPEG_pegf (peg_empty []) (cmlPEG_bindNT
                           gram_nLetDecs)]);
               ((INL:MMLnonT->MMLnonT+num) gram_nDecl,
                cmlPEG_choicel [
                  cmlPEG_seql [cmlPEG_tokeq tokens_ValT; cmlPEG_pnt
                    gram_nPattern; cmlPEG_tokeq tokens_EqualsT; cmlPEG_pnt
                    gram_nE]
                       (cmlPEG_bindNT gram_nDecl);
                  cmlPEG_seql [cmlPEG_tokeq tokens_FunT; cmlPEG_pnt
                    gram_nAndFDecls] (cmlPEG_bindNT gram_nDecl);
                  cmlPEG_seql [cmlPEG_tokeq tokens_ExceptionT; cmlPEG_pnt
                    gram_nDconstructor] (cmlPEG_bindNT gram_nDecl);
                  cmlPEG_seql [cmlPEG_tokeq tokens_LocalT; cmlPEG_pnt
                    gram_nDecls; cmlPEG_tokeq tokens_InT; cmlPEG_pnt
                    gram_nDecls;
                        cmlPEG_tokeq tokens_EndT] (cmlPEG_bindNT
                          gram_nDecl);
                  cmlPEG_seql [cmlPEG_pnt gram_nTypeDec] (cmlPEG_bindNT
                    gram_nDecl);
                  cmlPEG_seql [cmlPEG_pnt gram_nTypeAbbrevDec]
                    (cmlPEG_bindNT gram_nDecl);
                  cmlPEG_seql [cmlPEG_pnt gram_nStructure] (cmlPEG_bindNT
                    gram_nDecl)]);
               ((INL:MMLnonT->MMLnonT+num) gram_nTypeAbbrevDec,
                cmlPEG_seql [cmlPEG_tokeq tokens_TypeT; cmlPEG_pnt
                  gram_nTypeName; cmlPEG_tokeq tokens_EqualsT; cmlPEG_pnt
                  gram_nType]
                     (cmlPEG_bindNT gram_nTypeAbbrevDec));
               ((INL:MMLnonT->MMLnonT+num) gram_nDecls,
                cmlPEG_choicel [cmlPEG_seql [cmlPEG_pnt gram_nDecl;
                  cmlPEG_pnt gram_nDecls] (cmlPEG_bindNT gram_nDecls);
                         cmlPEG_seql [cmlPEG_tokeq tokens_SemicolonT;
                           cmlPEG_pnt gram_nDecls] (cmlPEG_bindNT gram_nDecls);
                         cmlPEG_pegf (peg_empty []) (cmlPEG_bindNT
                           gram_nDecls)]);
               ((INL:MMLnonT->MMLnonT+num) gram_nOptTypEqn,
                cmlPEG_choicel [cmlPEG_seql [cmlPEG_tokeq tokens_EqualsT;
                  cmlPEG_pnt gram_nType] (cmlPEG_bindNT gram_nOptTypEqn);
                         cmlPEG_pegf (peg_empty []) (cmlPEG_bindNT
                           gram_nOptTypEqn)]);
               ((INL:MMLnonT->MMLnonT+num) gram_nSpecLine,
                cmlPEG_choicel [cmlPEG_seql [cmlPEG_tokeq tokens_ValT;
                  cmlPEG_pnt gram_nV; cmlPEG_tokeq tokens_ColonT; cmlPEG_pnt
                  gram_nType]
                              (cmlPEG_bindNT gram_nSpecLine);
                         cmlPEG_seql [cmlPEG_tokeq tokens_TypeT; cmlPEG_pnt
                           gram_nTypeName; cmlPEG_pnt gram_nOptTypEqn]
                              (cmlPEG_bindNT gram_nSpecLine);
                         cmlPEG_seql [cmlPEG_tokeq tokens_ExceptionT;
                           cmlPEG_pnt gram_nDconstructor] (cmlPEG_bindNT
                           gram_nSpecLine);
                         cmlPEG_pegf (cmlPEG_pnt gram_nTypeDec)
                           (cmlPEG_bindNT gram_nSpecLine)]);
               ((INL:MMLnonT->MMLnonT+num) gram_nSpecLineList,
                cmlPEG_choicel [cmlPEG_seql [cmlPEG_pnt gram_nSpecLine;
                  cmlPEG_pnt gram_nSpecLineList]
                              (cmlPEG_bindNT gram_nSpecLineList);
                         cmlPEG_seql [cmlPEG_tokeq tokens_SemicolonT;
                           cmlPEG_pnt gram_nSpecLineList]
                              (cmlPEG_bindNT gram_nSpecLineList);
                         cmlPEG_pegf (peg_empty []) (cmlPEG_bindNT
                           gram_nSpecLineList)]);
               ((INL:MMLnonT->MMLnonT+num) gram_nSignatureValue,
                cmlPEG_seql [cmlPEG_tokeq tokens_SigT; cmlPEG_pnt
                  gram_nSpecLineList; cmlPEG_tokeq tokens_EndT]
                     (cmlPEG_bindNT gram_nSignatureValue));
               ((INL:MMLnonT->MMLnonT+num)
                 gram_nOptionalSignatureAscription,
                cmlPEG_pegf (cmlPEG_try (cmlPEG_seql [cmlPEG_tokeq
                  tokens_SealT; cmlPEG_pnt gram_nSignatureValue] I))
                     (cmlPEG_bindNT gram_nOptionalSignatureAscription));
               ((INL:MMLnonT->MMLnonT+num) gram_nStructName,peg_StructName);
               ((INL:MMLnonT->MMLnonT+num) gram_nStructure,
                cmlPEG_seql [cmlPEG_tokeq tokens_StructureT; cmlPEG_pnt
                  gram_nStructName; cmlPEG_pnt
                  gram_nOptionalSignatureAscription;
                      cmlPEG_tokeq tokens_EqualsT; cmlPEG_tokeq
                        tokens_StructT; cmlPEG_pnt gram_nDecls; cmlPEG_tokeq
                        tokens_EndT]
                     (cmlPEG_bindNT gram_nStructure));
               ((INL:MMLnonT->MMLnonT+num) gram_nTopLevelDecs,
                cmlPEG_choicel [
                  cmlPEG_seql [cmlPEG_pnt gram_nE; cmlPEG_tokeq
                    tokens_SemicolonT; cmlPEG_pnt gram_nTopLevelDecs]
                       (cmlPEG_bindNT gram_nTopLevelDecs);
                  cmlPEG_seql [cmlPEG_pnt gram_nDecl; cmlPEG_pnt
                    gram_nNonETopLevelDecs]
                       (cmlPEG_bindNT gram_nTopLevelDecs);
                  cmlPEG_seql [cmlPEG_tokeq tokens_SemicolonT; cmlPEG_pnt
                    gram_nTopLevelDecs]
                       (cmlPEG_bindNT gram_nTopLevelDecs);
                  cmlPEG_pegf (peg_empty []) (cmlPEG_bindNT
                    gram_nTopLevelDecs)]);
               ((INL:MMLnonT->MMLnonT+num) gram_nNonETopLevelDecs,
                cmlPEG_choicel [
                  cmlPEG_seql [cmlPEG_pnt gram_nDecl; cmlPEG_pnt
                    gram_nNonETopLevelDecs]
                       (cmlPEG_bindNT gram_nNonETopLevelDecs);
                  cmlPEG_seql [cmlPEG_tokeq tokens_SemicolonT; cmlPEG_pnt
                    gram_nTopLevelDecs]
                       (cmlPEG_bindNT gram_nNonETopLevelDecs);
                  cmlPEG_pegf (peg_empty []) (cmlPEG_bindNT
                    gram_nNonETopLevelDecs)])])`;;

(* HOL4 cmlPEGScript.sml:526-532: the ML values that the definitions below
   antiquote *)
(* can't use srw_ss() as it will attack the bodies of the rules,
   and in particular, will destroy predicates from tok
   constructors of the form
        do ... od = SOME ()
   which matches optionTheory.OPTION_BIND_EQUALS_OPTION, putting
   an existential into our rewrite thereby *)
(* HOL4 cmlPEGScript.sml:539-541: ML code, not ported *)

(* HOL4 cmlPEGScript.sml:543-559: a theorem that HOL4 states as the value of
   an ML expression: cmlpeg_rules_applied *)

(* HOL4 cmlPEGScript.sml:561-566: a theorem that HOL4 states as the value of
   an ML expression: FDOM_cmlPEG *)

(* HOL4 cmlPEGScript.sml:568-571: ML code, not ported *)

(* HOL4 cmlPEGScript.sml:573: the ML values that the definitions below
   antiquote *)

(* HOL4 cmlPEGScript.sml:575-580: a theorem that HOL4 states as the value of
   an ML expression: cmlPEG_exec_thm *)

(* HOL4 cmlPEGScript.sml:582-586: ML code, not ported *)

(* [local] *)
let frange_image = prove
 (`FRANGE fm = IMAGE (FAPPLY fm) (FDOM fm)`,
  CHEAT_TAC);;

(* HOL4 cmlPEGScript.sml:594-597: ML code, not ported *)

(* HOL4 cmlPEGScript.sml:599: the ML values that the definitions below
   antiquote *)

(* HOL4 cmlPEGScript.sml:601-613: ML code, not ported *)

(* HOL4 cmlPEGScript.sml:615-618: ML code, not ported *)

(* HOL4 cmlPEGScript.sml:620-629: ML code, not ported *)

(* HOL4 cmlPEGScript.sml:631-642: the ML values that the definitions below
   antiquote *)

(* HOL4 cmlPEGScript.sml:644-647: ML code, not ported *)

let peg0_pegf = prove
 (`peg0 G (cmlPEG_pegf s f) = peg0 G s`,
  CHEAT_TAC);;
add_simp peg0_pegf;;

let peg0_seql = prove
 (`(peg0 G (cmlPEG_seql [] f) <=> T) /\
   (peg0 G (cmlPEG_seql (CONS h t) f) <=> peg0 G h /\ peg0 G (cmlPEG_seql
     t I))`,
  CHEAT_TAC);;
add_simp peg0_seql;;

let peg0_tokeq = prove
 (`peg0 G (cmlPEG_tokeq t) = F`,
  CHEAT_TAC);;
add_simp peg0_tokeq;;

let peg0_tokSymP = prove
 (`peg0 G (cmlPEG_tokSymP P) <=> F`,
  CHEAT_TAC);;
add_simp peg0_tokSymP;;

let peg0_choicel = prove
 (`(peg0 G (cmlPEG_choicel []) = F) /\
   (peg0 G (cmlPEG_choicel (CONS h t)) <=> peg0 G h \/ pegfail G h /\ peg0
     G (cmlPEG_choicel t))`,
  CHEAT_TAC);;
add_simp peg0_choicel;;

(* HOL4 cmlPEGScript.sml:681-695: a theorem that HOL4 states as the value of
   an ML expression: th *)

(* HOL4 cmlPEGScript.sml:697-717: ML code, not ported *)

(* HOL4 cmlPEGScript.sml:719-732: a theorem that HOL4 states as the value of
   an ML expression: th *)

(* HOL4 cmlPEGScript.sml:734-757: the ML values that the definitions below
   antiquote *)

(* HOL4 cmlPEGScript.sml:759-760: a theorem that HOL4 states as the value of
   an ML expression: cml_wfpeg_thm *)

(*
set_diff (TypeBase.constructors_of ``:MMLnonT``)
         (topo_nts @ [``nTyVarList``, ``nTypeList``, ``nDtypeDecls``,
                      ``nDtypeCons``])
*)

(* [local] *)
let subexprs_pnt = prove
 (`subexprs (cmlPEG_pnt n) = {cmlPEG_pnt n}`,
  CHEAT_TAC);;

(* HOL4 cmlPEGScript.sml:774-783: a theorem that HOL4 states as the value of
   an ML expression: PEG_exprs *)

let PEG_wellformed = prove
 (`wfG cmlPEG`,
  CHEAT_TAC);;
add_simp PEG_wellformed;;

(* HOL4 cmlPEGScript.sml:797-799: a theorem that HOL4 states as the value of
   an ML expression: parse_TopLevelDecs_total *)

(* HOL4 cmlPEGScript.sml:801-803: a theorem that HOL4 states as the value of
   an ML expression: coreloop_TopLevelDecs_total *)

(* HOL4 cmlPEGScript.sml:805-806: a theorem that HOL4 states as the value of
   an ML expression: owhile_TopLevelDecs_total *)

(* HOL4 cmlPEGScript.sml:808-816: ML code, not ported *)

(* HOL4 cmlPEGScript.sml:818-820: a proof *)
(* HOL4 cmlPEGScript.sml:821-822: a theorem that HOL4 states as the value of
   an ML expression: FDOM_cmlPEG_nts *)

(* HOL4 cmlPEGScript.sml:824-840: a proof *)
(* HOL4 cmlPEGScript.sml:841-842: a theorem that HOL4 states as the value of
   an ML expression: NTS_in_PEG_exprs *)

(* HOL4 cmlPEGScript.sml:844: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
