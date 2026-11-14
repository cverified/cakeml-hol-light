(* ======================================================== *)
(*  cmlPEG: ported from HOL4's
    compiler/parsing/cmlPEGScript.sml
    A definition theory, with 25 definitions and 17 theorems.
    Needed by cmlParse.ml, fromSexp.ml, infer.ml, pegComplete.ml and
    pegSound.ml.  *)
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

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "cmlPEG"
  ["gram"; "tokenUtils"];;

(* HOL4 cmlPEGScript.sml:14: the overload monad_bind, which the port
   expands *)
hol4_overload "assert" "OPTION_GUARD";;

(* HOL4 cmlPEGScript.sml:17-29: ML code, not ported *)

let cmlPEG_sumID_def = define_cases
  [`cmlPEG_sumID (INL x) = x`;
   `cmlPEG_sumID (INR y) = y`];;
hol4_overload "sumID" "cmlPEG_sumID";;

let mktokLf_def = new_definition
  `mktokLf t = [Lf
  ((grammar_TOK:tokens_token->(tokens_token,MMLnonT)grammar_symbol)
  (FST t),SND t)]`;;

let mkNd_def = new_definition
  `mkNd ntnm l = Nd (ntnm,ptree_list_loc l) l`;;

let bindNT0_def = new_definition
  `bindNT0 ntnm l = Nd ((INL:MMLnonT->MMLnonT+num)
  ntnm,ptree_list_loc l) l`;;

let bindNT_def = new_definition
  `bindNT ntnm l = [bindNT0 ntnm l]`;;

let _ = size_thms "locs";;
let _ = size_thms "parsetree";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let mk_linfix_def,mk_linfix_ind = define_wf
  `MEASURE (\(x0,x1,x2). parsetree_size1 locs_size (\x. 0) (\x. 0) x2)`
  [`mk_linfix tgt acc [] = acc`;
   `mk_linfix tgt acc [t] = acc`;
   `mk_linfix tgt acc (CONS opt (CONS t rest)) =
     mk_linfix tgt (mkNd tgt [acc; opt; t]) rest`];;

let _ = size_thms "locs";;
let _ = size_thms "parsetree";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let mk_rinfix_def,mk_rinfix_ind = define_wf
  `MEASURE (\(x0,x1). parsetree_size1 locs_size (\x. 0) (\x. 0) x1)`
  [`mk_rinfix tgt [] = mkNd tgt []`;
   `mk_rinfix tgt [t] = mkNd tgt [t]`;
   `mk_rinfix tgt (CONS t (CONS opt rest)) = mkNd tgt [t; opt;
  mk_rinfix tgt rest]`];;

let peg_linfix_def = new_definition
  `peg_linfix tgtnt rptsym opsym =
     peg_seq rptsym (peg_rpt (peg_seq opsym rptsym (++)) FLAT)
         (\a b. match a with
                    [] -> [] | CONS h _1 -> [mk_linfix tgtnt (mkNd
                      tgtnt [h]) b])`;;

(* have to use these versions of choicel and pegf below because the
   "built-in" versions from HOL/examples/ use ARB in their definitions.
   Logically, the ARBs are harmless, but they completely mess with the
   translator
*)
let cmlPEG_choicel_def,cmlPEG_choicel_ind = define_rec
  [`cmlPEG_choicel [] = peg_not (peg_empty []) []`;
   `cmlPEG_choicel (CONS h t) = peg_choice h (cmlPEG_choicel t)
  cmlPEG_sumID`];;
hol4_overload "choicel" "cmlPEG_choicel";;

let cmlPEG_pegf_def = new_definition
  `cmlPEG_pegf sym f = peg_seq sym (peg_empty []) (\l1 l2. f l1)`;;
hol4_overload "pegf" "cmlPEG_pegf";;

let seql_def = new_definition
  `seql l f = pegf (ITLIST (\p acc. peg_seq p acc (++)) l (peg_empty
  [])) f`;;

(* HOL4 cmlPEGScript.sml:94-98: code that the source has in a comment *)

let try_def = new_definition
  `cmlPEG_try sym = choicel [sym; peg_empty []]`;;
hol4_overload "try" "cmlPEG_try";;

let cmlPEG_tokeq_def = new_definition
  `cmlPEG_tokeq t = peg_tok ((=) t) mktokLf`;;
hol4_overload "tokeq" "cmlPEG_tokeq";;

let tokSymP_def = new_definition
  `tokSymP P =
     peg_tok (\t. ((OPTION_BIND) (destSymbolT t) (\s. OPTION_GUARD
       (P s))) = SOME one) mktokLf`;;

let cmlPEG_pnt_def = new_definition
  `cmlPEG_pnt ntsym = peg_nt ((INL:MMLnonT->MMLnonT+num) ntsym) I`;;
hol4_overload "pnt" "cmlPEG_pnt";;

(* ----------------------------------------------------------------------
    PEG for types
   ---------------------------------------------------------------------- *)

let peg_UQConstructorName_def = new_definition
  `peg_UQConstructorName =
     peg_tok (\t. (OPTION_BIND) (destAlphaT t) (\s.
                 OPTION_GUARD (~(s = (implode "")) /\ isUpper (strsub
                   s 0))) = SOME one)
         (bindNT nUQConstructorName o mktokLf)`;;

let peg_TypeDec_def = new_definition
  `peg_TypeDec =
     peg_seq (cmlPEG_tokeq tokens_DatatypeT)
         (peg_linfix ((INL:MMLnonT->MMLnonT+num) nDtypeDecls)
           (cmlPEG_pnt nDtypeDecl)
                     (cmlPEG_tokeq tokens_AndT))
         (\l1 l2. bindNT nTypeDec (APPEND l1 l2))`;;

(* expressions *)
let peg_V_def = new_definition
  `peg_V =
    choicel [peg_tok (\t.
                   (OPTION_BIND) (destAlphaT t) (\s.
                      OPTION_GUARD (~(s IN {(implode
                        "before"),(implode "div"),(implode
                        "mod"),(implode "o")}) /\ ~(s = (implode "")) /\
                        ~(isUpper (strsub s 0)))) = SOME one)
                 (bindNT nV o mktokLf);
             pegf (tokSymP (validPrefixSym o explode)) (bindNT
               nV)]`;;

let peg_longV_def = new_definition
  `peg_longV = peg_tok (\t. (OPTION_BIND) (destLongidT t) (\
                         (str,s).
                         OPTION_GUARD (~(s = (implode "")) /\
                           (isAlpha (strsub s 0) ==> ~(isUpper (strsub s
                           0))))) = SOME one)
                   (bindNT nFQV o mktokLf)`;;

let peg_EbaseParenFn_def = new_definition
  `peg_EbaseParenFn l =
     (match l with
       [lp; es; rp] -> [mkNd ((INL:MMLnonT->MMLnonT+num) nEbase) [lp;
         mkNd ((INL:MMLnonT->MMLnonT+num) nEseq) [es]; rp]] | [lp; e;
         sep; es; rp] ->
       (match destLf sep with
          NONE -> [] | SOME t ->
          (match destTOK t with
             NONE -> [] | SOME t ->
             (if t = tokens_CommaT then
               [
                 mkNd ((INL:MMLnonT->MMLnonT+num) nEbase) [
                   mkNd ((INL:MMLnonT->MMLnonT+num) nEtuple) [lp;
                     mkNd ((INL:MMLnonT->MMLnonT+num) nElist2) [e; sep;
                     es]; rp]]] else
               [
                 mkNd ((INL:MMLnonT->MMLnonT+num) nEbase) [lp;
                   mkNd ((INL:MMLnonT->MMLnonT+num) nEseq) [e; sep;
                   es]; rp]]))) | _2 -> [])`;;

let peg_EbaseParen_def = new_definition
  `peg_EbaseParen =
     seql [cmlPEG_tokeq tokens_LparT; cmlPEG_pnt nE;
           choicel [cmlPEG_tokeq tokens_RparT;
                    seql [cmlPEG_tokeq tokens_CommaT; cmlPEG_pnt
                      nElist1; cmlPEG_tokeq tokens_RparT] I;
                    seql [cmlPEG_tokeq tokens_SemicolonT; cmlPEG_pnt
                      nEseq; cmlPEG_tokeq tokens_RparT] I]]
          peg_EbaseParenFn`;;

let peg_StructName_def = new_definition
  `peg_StructName =
     peg_tok (\t. (OPTION_BIND) (destAlphaT t) (\s.
                 OPTION_GUARD (~(s = (implode "")))) = SOME one)
         (bindNT nStructName o mktokLf)`;;

let _ = size_thms "MMLnonT";;
let _ = size_thms "locs";;
let _ = size_thms "parsetree";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let ptPapply0_def,ptPapply0_ind = define_wf
  `MEASURE (\(x0,x1). parsetree_size1 locs_size MMLnonT_size (\x. 0)
  x1)`
  [`ptPapply0 c x2 =
      match x2 with
        [] -> []
      // can't happen
      | [pb_pt] -> bindNT nPapp [c; pb_pt]
      | (CONS pb pbs) -> ptPapply0 (bindNT0 nPConApp [c; pb])
        pbs`];;

let ptPapply_def = new_definition
  `ptPapply x1 =
      match x1 with
        [] -> []
      // can't happen
      | [_3] -> []
      // can't happen
      | (CONS c rest) -> ptPapply0 (bindNT0 nPConApp [c]) rest`;;


let cmlPEG_def = new_definition
  `cmlPEG = mk_peg (cmlPEG_pnt nTopLevelDecs) "Didn't expect an EOF"
  "Failed to see expected token"
  "Failed to see expected token; saw EOF instead"
  "Not combinator failed" (FEMPTY |++
              [((INL:MMLnonT->MMLnonT+num) nV,peg_V);
               ((INL:MMLnonT->MMLnonT+num) nTyvarN,pegf (peg_tok
                 isTyvarT mktokLf) (bindNT nTyvarN));
               ((INL:MMLnonT->MMLnonT+num) nFQV,choicel [pegf
                 (cmlPEG_pnt nV) (bindNT nFQV); peg_longV]);
               ((INL:MMLnonT->MMLnonT+num) nEapp,
                seql [cmlPEG_pnt nEbase; peg_rpt (cmlPEG_pnt nEbase)
                  FLAT]
                     (\l.
                        match l with
                          [] -> [] | CONS h t -> [FOLDL (\a b. mkNd
                            ((INL:MMLnonT->MMLnonT+num) nEapp) [a; b])
                              (mkNd ((INL:MMLnonT->MMLnonT+num)
                                nEapp) [h]) t]));
               ((INL:MMLnonT->MMLnonT+num) nElist1,
                seql [cmlPEG_pnt nE; cmlPEG_try (seql [cmlPEG_tokeq
                  tokens_CommaT; cmlPEG_pnt nElist1] I)]
                     (bindNT nElist1));
               ((INL:MMLnonT->MMLnonT+num) nMultOps,
                pegf (
                  choicel (CONS (tokSymP (validMultSym o explode))
                    (MAP cmlPEG_tokeq [tokens_StarT; tokens_AlphaT
                      (implode "mod"); tokens_AlphaT (implode "div")])))
                      (bindNT nMultOps));
               ((INL:MMLnonT->MMLnonT+num) nAddOps,pegf (tokSymP
                 (validAddSym o explode)) (bindNT nAddOps));
               ((INL:MMLnonT->MMLnonT+num) nRelOps,
                pegf (choicel [cmlPEG_tokeq tokens_EqualsT; tokSymP
                  (validRelSym o explode)])
                     (bindNT nRelOps));
               ((INL:MMLnonT->MMLnonT+num) nListOps,pegf (tokSymP
                 (validListSym o explode)) (bindNT nListOps));
               ((INL:MMLnonT->MMLnonT+num) nCompOps,pegf (choicel
                 [cmlPEG_tokeq (tokens_SymbolT (implode ":="));
                              cmlPEG_tokeq (tokens_AlphaT (implode
                                "o"))])
                              (bindNT nCompOps));
               ((INL:MMLnonT->MMLnonT+num) nOpID,
                choicel [peg_tok (\t. (OPTION_BIND) (destLongidT t)
                  (\
                              (str,s).
                              OPTION_GUARD (~(s = (implode "")))) =
                                SOME one) (bindNT nOpID o mktokLf);
                         peg_tok (\t. (OPTION_BIND) (destSymbolT t)
                           (\
                              s.
                              OPTION_GUARD (~(s = (implode "")))) =
                                SOME one) (bindNT nOpID o mktokLf);
                         peg_tok (\t. (OPTION_BIND) (destAlphaT t) (\
                              s.
                              OPTION_GUARD (~(s = (implode "")))) =
                                SOME one) (bindNT nOpID o mktokLf);
                         pegf (cmlPEG_tokeq tokens_StarT) (bindNT
                           nOpID);
                         pegf (cmlPEG_tokeq tokens_EqualsT) (bindNT
                           nOpID)]);
               ((INL:MMLnonT->MMLnonT+num) nEliteral,
                choicel [peg_tok isInt (bindNT nEliteral o mktokLf);
                         peg_tok isString (bindNT nEliteral o
                           mktokLf);
                         peg_tok isCharT (bindNT nEliteral o
                           mktokLf);
                         peg_tok isWordT (bindNT nEliteral o
                           mktokLf);
                         peg_tok (IS_SOME o destFFIT) (bindNT
                           nEliteral o mktokLf)]);
               ((INL:MMLnonT->MMLnonT+num) nEbase,
                choicel [pegf (cmlPEG_pnt nEliteral) (bindNT nEbase);
                         seql [cmlPEG_tokeq tokens_LparT;
                           cmlPEG_tokeq tokens_RparT] (bindNT nEbase);
                         peg_EbaseParen;
                         seql [cmlPEG_tokeq tokens_LbrackT;
                           cmlPEG_try (cmlPEG_pnt nElist1); cmlPEG_tokeq
                           tokens_RbrackT]
                              (bindNT nEbase);
                         seql [cmlPEG_tokeq tokens_LetT; cmlPEG_pnt
                           nLetDecs; cmlPEG_tokeq tokens_InT; cmlPEG_pnt
                           nEseq;
                              cmlPEG_tokeq tokens_EndT] (bindNT
                                nEbase);
                         pegf (cmlPEG_pnt nFQV) (bindNT nEbase);
                         pegf (cmlPEG_pnt nConstructorName) (bindNT
                           nEbase);
                         seql [cmlPEG_tokeq tokens_OpT; cmlPEG_pnt
                           nOpID] (bindNT nEbase)]);
               ((INL:MMLnonT->MMLnonT+num) nEseq,
                seql [cmlPEG_pnt nE; cmlPEG_try (seql [cmlPEG_tokeq
                  tokens_SemicolonT; cmlPEG_pnt nEseq] I)]
                     (bindNT nEseq));
               ((INL:MMLnonT->MMLnonT+num) nEmult,
                peg_linfix ((INL:MMLnonT->MMLnonT+num) nEmult)
                  (cmlPEG_pnt nEapp) (cmlPEG_pnt nMultOps));
               ((INL:MMLnonT->MMLnonT+num) nEadd,peg_linfix
                 ((INL:MMLnonT->MMLnonT+num) nEadd) (cmlPEG_pnt nEmult)
                 (cmlPEG_pnt nAddOps));
               ((INL:MMLnonT->MMLnonT+num) nElistop,
                seql [cmlPEG_pnt nEadd; cmlPEG_try (seql [cmlPEG_pnt
                  nListOps; cmlPEG_pnt nElistop] I)]
                     (bindNT nElistop));
               ((INL:MMLnonT->MMLnonT+num) nErel,peg_linfix
                 ((INL:MMLnonT->MMLnonT+num) nErel) (cmlPEG_pnt
                 nElistop) (cmlPEG_pnt nRelOps));
               ((INL:MMLnonT->MMLnonT+num) nEcomp,peg_linfix
                 ((INL:MMLnonT->MMLnonT+num) nEcomp) (cmlPEG_pnt nErel)
                              (cmlPEG_pnt nCompOps));
               ((INL:MMLnonT->MMLnonT+num) nEbefore,peg_linfix
                 ((INL:MMLnonT->MMLnonT+num) nEbefore) (cmlPEG_pnt
                 nEcomp)
                              (cmlPEG_tokeq (tokens_AlphaT (implode
                                "before"))));
               ((INL:MMLnonT->MMLnonT+num) nEtyped,seql [cmlPEG_pnt
                 nEbefore;
                              cmlPEG_try (seql [cmlPEG_tokeq
                                tokens_ColonT; cmlPEG_pnt nType] I)]
                              (bindNT nEtyped));
               ((INL:MMLnonT->MMLnonT+num) nElogicAND,
                peg_linfix ((INL:MMLnonT->MMLnonT+num) nElogicAND)
                  (cmlPEG_pnt nEtyped)
                           (cmlPEG_tokeq tokens_AndalsoT));
               ((INL:MMLnonT->MMLnonT+num) nElogicOR,
                peg_linfix ((INL:MMLnonT->MMLnonT+num) nElogicOR)
                  (cmlPEG_pnt nElogicAND)
                           (cmlPEG_tokeq tokens_OrelseT));
               ((INL:MMLnonT->MMLnonT+num) nEhandle,
                seql [cmlPEG_pnt nElogicOR;
                      cmlPEG_try (seql [cmlPEG_tokeq tokens_HandleT;
                        cmlPEG_pnt nPEs] I)]
                     (bindNT nEhandle));
               ((INL:MMLnonT->MMLnonT+num) nE,
                choicel [seql [cmlPEG_tokeq tokens_RaiseT; cmlPEG_pnt
                  nE] (bindNT nE);
                         pegf (cmlPEG_pnt nEhandle) (bindNT nE);
                         seql [cmlPEG_tokeq tokens_IfT; cmlPEG_pnt
                           nE; cmlPEG_tokeq tokens_ThenT; cmlPEG_pnt nE;
                              cmlPEG_tokeq tokens_ElseT; cmlPEG_pnt
                                nE]
                              (bindNT nE);
                         seql [cmlPEG_tokeq tokens_FnT; cmlPEG_pnt
                           nPattern; cmlPEG_tokeq tokens_DarrowT;
                           cmlPEG_pnt nE]
                              (bindNT nE);
                         seql [cmlPEG_tokeq tokens_CaseT; cmlPEG_pnt
                           nE; cmlPEG_tokeq tokens_OfT; cmlPEG_pnt nPEs]
                              (bindNT nE)]);
               ((INL:MMLnonT->MMLnonT+num) nPEs,
                seql [cmlPEG_pnt nPattern; cmlPEG_tokeq
                  tokens_DarrowT; cmlPEG_pnt nPE] (bindNT nPEs));
               ((INL:MMLnonT->MMLnonT+num) nPE,
                choicel [seql [cmlPEG_tokeq tokens_IfT; cmlPEG_pnt
                  nE; cmlPEG_tokeq tokens_ThenT; cmlPEG_pnt nE;
                              cmlPEG_tokeq tokens_ElseT; cmlPEG_pnt
                                nPE]
                              (bindNT nPE);
                         seql [cmlPEG_tokeq tokens_CaseT; cmlPEG_pnt
                           nE; cmlPEG_tokeq tokens_OfT; cmlPEG_pnt nPEs]
                              (bindNT nPE);
                         seql [cmlPEG_tokeq tokens_FnT; cmlPEG_pnt
                           nPattern; cmlPEG_tokeq tokens_DarrowT;
                           cmlPEG_pnt nE]
                              (bindNT nPE);
                         seql [cmlPEG_tokeq tokens_RaiseT; cmlPEG_pnt
                           nPE] (bindNT nPE);
                         seql [cmlPEG_pnt nElogicOR; cmlPEG_pnt
                           nPEsfx] (bindNT nPE)]);
               ((INL:MMLnonT->MMLnonT+num) nPEsfx,
                choicel [seql [cmlPEG_tokeq tokens_HandleT;
                  cmlPEG_pnt nPEs] (bindNT nPEsfx);
                         seql [cmlPEG_tokeq tokens_BarT; cmlPEG_pnt
                           nPEs] (bindNT nPEsfx);
                         pegf (peg_empty []) (bindNT nPEsfx)]);
               ((INL:MMLnonT->MMLnonT+num) nAndFDecls,
                peg_linfix ((INL:MMLnonT->MMLnonT+num) nAndFDecls)
                  (cmlPEG_pnt nFDecl) (cmlPEG_tokeq tokens_AndT));
               ((INL:MMLnonT->MMLnonT+num) nFDecl,
                seql [cmlPEG_pnt nV; cmlPEG_pnt nPbaseList1;
                  cmlPEG_tokeq tokens_EqualsT; cmlPEG_pnt nE]
                     (bindNT nFDecl));
               ((INL:MMLnonT->MMLnonT+num) nPbaseList1,
                seql [cmlPEG_pnt nPbase; cmlPEG_try (cmlPEG_pnt
                  nPbaseList1)]
                     (bindNT nPbaseList1));
               ((INL:MMLnonT->MMLnonT+num) nType,
                seql [cmlPEG_pnt nPType; cmlPEG_try (seql
                  [cmlPEG_tokeq tokens_ArrowT; cmlPEG_pnt nType] I)]
                     (bindNT nType));
               ((INL:MMLnonT->MMLnonT+num) nDType,
                seql [cmlPEG_pnt nTbase; peg_rpt (cmlPEG_pnt nTyOp)
                  FLAT]
                     (\subs.
                        match subs with
                            [] -> [] | CONS h t -> [FOLDL (\a b. mkNd
                              ((INL:MMLnonT->MMLnonT+num) nDType) [a;
                              b])
                              (mkNd ((INL:MMLnonT->MMLnonT+num)
                                nDType) [h]) t]));
               ((INL:MMLnonT->MMLnonT+num) nTbase,
                choicel [
                  seql [cmlPEG_tokeq tokens_LparT; cmlPEG_pnt nType;
                    cmlPEG_tokeq tokens_RparT] (bindNT nTbase);
                  seql [cmlPEG_tokeq tokens_LparT; cmlPEG_pnt
                    nTypeList2; cmlPEG_tokeq tokens_RparT; cmlPEG_pnt
                    nTyOp]
                       (bindNT nTbase);
                  peg_tok isTyvarT (bindNT nTbase o mktokLf);
                  pegf (cmlPEG_pnt nTyOp) (bindNT nTbase)]);
               ((INL:MMLnonT->MMLnonT+num) nPTbase,
                choicel [
                  seql [cmlPEG_tokeq tokens_LparT; cmlPEG_pnt nType;
                    cmlPEG_tokeq tokens_RparT] (bindNT nPTbase);
                  peg_tok isTyvarT (bindNT nPTbase o mktokLf);
                  pegf (cmlPEG_pnt nTyOp) (bindNT nPTbase)]);
               ((INL:MMLnonT->MMLnonT+num) nTypeList2,
                seql [cmlPEG_pnt nType; cmlPEG_tokeq tokens_CommaT;
                  cmlPEG_pnt nTypeList1]
                     (bindNT nTypeList2));
               ((INL:MMLnonT->MMLnonT+num) nTypeList1,
                seql [cmlPEG_pnt nType; cmlPEG_try (seql
                  [cmlPEG_tokeq tokens_CommaT; cmlPEG_pnt nTypeList1]
                  I)]
                     (bindNT nTypeList1));
               ((INL:MMLnonT->MMLnonT+num) nTbaseList,
                pegf (cmlPEG_try (seql [cmlPEG_pnt nPTbase;
                  cmlPEG_pnt nTbaseList] I))
                     (bindNT nTbaseList));
               ((INL:MMLnonT->MMLnonT+num) nTyOp,
                pegf (choicel [cmlPEG_pnt nUQTyOp; peg_tok isLongidT
                  mktokLf])
                     (bindNT nTyOp));
               ((INL:MMLnonT->MMLnonT+num) nUQTyOp,
                pegf (peg_tok isAlphaSym mktokLf) (bindNT nUQTyOp));
               ((INL:MMLnonT->MMLnonT+num) nPType,
                seql [cmlPEG_pnt nDType; cmlPEG_try (seql
                  [cmlPEG_tokeq tokens_StarT; cmlPEG_pnt nPType] I)]
                     (bindNT nPType));
               ((INL:MMLnonT->MMLnonT+num) nTypeName,
                choicel [pegf (cmlPEG_pnt nUQTyOp) (bindNT
                  nTypeName);
                         seql [cmlPEG_tokeq tokens_LparT; cmlPEG_pnt
                           nTyVarList;
                              cmlPEG_tokeq tokens_RparT; cmlPEG_pnt
                                nUQTyOp] (bindNT nTypeName);
                         seql [peg_tok isTyvarT mktokLf; cmlPEG_pnt
                           nUQTyOp]
                              (bindNT nTypeName)]);
               ((INL:MMLnonT->MMLnonT+num) nTyVarList,
                peg_linfix ((INL:MMLnonT->MMLnonT+num) nTyVarList)
                  (cmlPEG_pnt nTyvarN) (cmlPEG_tokeq tokens_CommaT));
               ((INL:MMLnonT->MMLnonT+num) nTypeDec,peg_TypeDec);
               ((INL:MMLnonT->MMLnonT+num) nDtypeDecl,
                seql [cmlPEG_pnt nTypeName;
                      cmlPEG_tokeq tokens_EqualsT;
                      peg_linfix ((INL:MMLnonT->MMLnonT+num)
                        nDtypeCons) (cmlPEG_pnt nDconstructor)
                        (cmlPEG_tokeq tokens_BarT)]
                     (bindNT nDtypeDecl));
               ((INL:MMLnonT->MMLnonT+num) nDconstructor,
                seql [cmlPEG_pnt nUQConstructorName; cmlPEG_pnt
                  nTbaseList]
                     (bindNT nDconstructor));
               ((INL:MMLnonT->MMLnonT+num)
                 nUQConstructorName,peg_UQConstructorName);
               ((INL:MMLnonT->MMLnonT+num) nConstructorName,
                choicel [
                  pegf (cmlPEG_pnt nUQConstructorName) (bindNT
                    nConstructorName);
                  peg_tok (\t. (OPTION_BIND) (destLongidT t) (\
                             (str,s).
                             OPTION_GUARD (~(s = (implode "")) /\
                              isAlpha (strsub s 0) /\
                              isUpper (strsub s 0))) = SOME one)
                      (bindNT nConstructorName o mktokLf)]);
               ((INL:MMLnonT->MMLnonT+num) nPbase,
                pegf
                  (choicel [cmlPEG_pnt nV; cmlPEG_pnt
                    nConstructorName; peg_tok isInt mktokLf;
                            peg_tok isString mktokLf; peg_tok isCharT
                              mktokLf;
                            cmlPEG_pnt nPtuple; cmlPEG_tokeq
                              tokens_UnderbarT;
                            seql [cmlPEG_tokeq tokens_LbrackT;
                              cmlPEG_try (cmlPEG_pnt nPatternList);
                              cmlPEG_tokeq tokens_RbrackT] I;
                            seql [cmlPEG_tokeq tokens_OpT; cmlPEG_pnt
                              nOpID] I])
                  (bindNT nPbase));
               ((INL:MMLnonT->MMLnonT+num) nPapp,
                choicel [seql [cmlPEG_pnt nConstructorName; peg_rpt
                  (cmlPEG_pnt nPbase) FLAT]
                          (\pts. if LENGTH pts = 1 then
                              bindNT nPapp (bindNT nPbase pts) else
                              match pts with
                              [] -> [] | [
                              // can't happen
                              c] -> [] |
                              // can't happen
                              _4 -> ptPapply pts);
                         pegf (cmlPEG_pnt nPbase) (bindNT nPapp)]);
               ((INL:MMLnonT->MMLnonT+num) nPcons,
                seql [cmlPEG_pnt nPapp;
                      cmlPEG_try (seql [cmlPEG_tokeq (tokens_SymbolT
                        (implode "::")); cmlPEG_pnt nPcons] I)]
                     (bindNT nPcons));
               ((INL:MMLnonT->MMLnonT+num) nPas,
                seql [cmlPEG_try (seql [cmlPEG_pnt nV; cmlPEG_tokeq
                  tokens_AsT] I);
                      cmlPEG_pnt nPcons]
                     (bindNT nPas));
               ((INL:MMLnonT->MMLnonT+num) nPattern,
                seql [cmlPEG_pnt nPas; cmlPEG_try (seql [cmlPEG_tokeq
                  tokens_ColonT; cmlPEG_pnt nType] I)]
                     (bindNT nPattern));
               ((INL:MMLnonT->MMLnonT+num) nPatternList,
                seql [cmlPEG_pnt nPattern;
                      cmlPEG_try (seql [cmlPEG_tokeq tokens_CommaT;
                        cmlPEG_pnt nPatternList] I)]
                     (bindNT nPatternList));
               ((INL:MMLnonT->MMLnonT+num) nPtuple,
                choicel [seql [cmlPEG_tokeq tokens_LparT;
                  cmlPEG_tokeq tokens_RparT] (bindNT nPtuple);
                         seql [cmlPEG_tokeq tokens_LparT; cmlPEG_pnt
                           nPatternList; cmlPEG_tokeq tokens_RparT]
                              (bindNT nPtuple)]);
               ((INL:MMLnonT->MMLnonT+num) nLetDec,
                choicel [seql [cmlPEG_tokeq tokens_ValT; cmlPEG_pnt
                  nPattern; cmlPEG_tokeq tokens_EqualsT; cmlPEG_pnt nE]
                              (bindNT nLetDec);
                         seql [cmlPEG_tokeq tokens_FunT; cmlPEG_pnt
                           nAndFDecls] (bindNT nLetDec)]);
               ((INL:MMLnonT->MMLnonT+num) nLetDecs,
                choicel [seql [cmlPEG_pnt nLetDec; cmlPEG_pnt
                  nLetDecs] (bindNT nLetDecs);
                         seql [cmlPEG_tokeq tokens_SemicolonT;
                           cmlPEG_pnt nLetDecs] (bindNT nLetDecs);
                         pegf (peg_empty []) (bindNT nLetDecs)]);
               ((INL:MMLnonT->MMLnonT+num) nDecl,
                choicel [
                  seql [cmlPEG_tokeq tokens_ValT; cmlPEG_pnt
                    nPattern; cmlPEG_tokeq tokens_EqualsT; cmlPEG_pnt
                    nE]
                       (bindNT nDecl);
                  seql [cmlPEG_tokeq tokens_FunT; cmlPEG_pnt
                    nAndFDecls] (bindNT nDecl);
                  seql [cmlPEG_tokeq tokens_ExceptionT; cmlPEG_pnt
                    nDconstructor] (bindNT nDecl);
                  seql [cmlPEG_tokeq tokens_LocalT; cmlPEG_pnt
                    nDecls; cmlPEG_tokeq tokens_InT; cmlPEG_pnt nDecls;
                        cmlPEG_tokeq tokens_EndT] (bindNT nDecl);
                  seql [cmlPEG_pnt nTypeDec] (bindNT nDecl);
                  seql [cmlPEG_pnt nTypeAbbrevDec] (bindNT nDecl);
                  seql [cmlPEG_pnt nStructure] (bindNT nDecl)]);
               ((INL:MMLnonT->MMLnonT+num) nTypeAbbrevDec,
                seql [cmlPEG_tokeq tokens_TypeT; cmlPEG_pnt
                  nTypeName; cmlPEG_tokeq tokens_EqualsT; cmlPEG_pnt
                  nType]
                     (bindNT nTypeAbbrevDec));
               ((INL:MMLnonT->MMLnonT+num) nDecls,
                choicel [seql [cmlPEG_pnt nDecl; cmlPEG_pnt nDecls]
                  (bindNT nDecls);
                         seql [cmlPEG_tokeq tokens_SemicolonT;
                           cmlPEG_pnt nDecls] (bindNT nDecls);
                         pegf (peg_empty []) (bindNT nDecls)]);
               ((INL:MMLnonT->MMLnonT+num) nOptTypEqn,
                choicel [seql [cmlPEG_tokeq tokens_EqualsT;
                  cmlPEG_pnt nType] (bindNT nOptTypEqn);
                         pegf (peg_empty []) (bindNT nOptTypEqn)]);
               ((INL:MMLnonT->MMLnonT+num) nSpecLine,
                choicel [seql [cmlPEG_tokeq tokens_ValT; cmlPEG_pnt
                  nV; cmlPEG_tokeq tokens_ColonT; cmlPEG_pnt nType]
                              (bindNT nSpecLine);
                         seql [cmlPEG_tokeq tokens_TypeT; cmlPEG_pnt
                           nTypeName; cmlPEG_pnt nOptTypEqn]
                              (bindNT nSpecLine);
                         seql [cmlPEG_tokeq tokens_ExceptionT;
                           cmlPEG_pnt nDconstructor] (bindNT nSpecLine);
                         pegf (cmlPEG_pnt nTypeDec) (bindNT
                           nSpecLine)]);
               ((INL:MMLnonT->MMLnonT+num) nSpecLineList,
                choicel [seql [cmlPEG_pnt nSpecLine; cmlPEG_pnt
                  nSpecLineList]
                              (bindNT nSpecLineList);
                         seql [cmlPEG_tokeq tokens_SemicolonT;
                           cmlPEG_pnt nSpecLineList]
                              (bindNT nSpecLineList);
                         pegf (peg_empty []) (bindNT
                           nSpecLineList)]);
               ((INL:MMLnonT->MMLnonT+num) nSignatureValue,
                seql [cmlPEG_tokeq tokens_SigT; cmlPEG_pnt
                  nSpecLineList; cmlPEG_tokeq tokens_EndT]
                     (bindNT nSignatureValue));
               ((INL:MMLnonT->MMLnonT+num)
                 nOptionalSignatureAscription,
                pegf (cmlPEG_try (seql [cmlPEG_tokeq tokens_SealT;
                  cmlPEG_pnt nSignatureValue] I))
                     (bindNT nOptionalSignatureAscription));
               ((INL:MMLnonT->MMLnonT+num)
                 nStructName,peg_StructName);
               ((INL:MMLnonT->MMLnonT+num) nStructure,
                seql [cmlPEG_tokeq tokens_StructureT; cmlPEG_pnt
                  nStructName; cmlPEG_pnt nOptionalSignatureAscription;
                      cmlPEG_tokeq tokens_EqualsT; cmlPEG_tokeq
                        tokens_StructT; cmlPEG_pnt nDecls; cmlPEG_tokeq
                        tokens_EndT]
                     (bindNT nStructure));
               ((INL:MMLnonT->MMLnonT+num) nTopLevelDecs,
                choicel [
                  seql [cmlPEG_pnt nE; cmlPEG_tokeq
                    tokens_SemicolonT; cmlPEG_pnt nTopLevelDecs]
                       (bindNT nTopLevelDecs);
                  seql [cmlPEG_pnt nDecl; cmlPEG_pnt
                    nNonETopLevelDecs]
                       (bindNT nTopLevelDecs);
                  seql [cmlPEG_tokeq tokens_SemicolonT; cmlPEG_pnt
                    nTopLevelDecs]
                       (bindNT nTopLevelDecs);
                  pegf (peg_empty []) (bindNT nTopLevelDecs)]);
               ((INL:MMLnonT->MMLnonT+num) nNonETopLevelDecs,
                choicel [
                  seql [cmlPEG_pnt nDecl; cmlPEG_pnt
                    nNonETopLevelDecs]
                       (bindNT nNonETopLevelDecs);
                  seql [cmlPEG_tokeq tokens_SemicolonT; cmlPEG_pnt
                    nTopLevelDecs]
                       (bindNT nNonETopLevelDecs);
                  pegf (peg_empty []) (bindNT
                    nNonETopLevelDecs)])])`;;

(* HOL4 cmlPEGScript.sml:526-532: the ML values that the definitions
   below antiquote *)
(* can't use srw_ss() as it will attack the bodies of the rules,
   and in particular, will destroy predicates from tok
   constructors of the form
        do ... od = SOME ()
   which matches optionTheory.OPTION_BIND_EQUALS_OPTION, putting
   an existential into our rewrite thereby *)
(* HOL4 cmlPEGScript.sml:539-541: ML code, not ported *)

(* HOL4 cmlPEGScript.sml:543-559: a theorem that HOL4 states as the
   value of an ML expression: cmlpeg_rules_applied *)

(* HOL4 cmlPEGScript.sml:561-566: a theorem that HOL4 states as the
   value of an ML expression: FDOM_cmlPEG *)

(* HOL4 cmlPEGScript.sml:568-571: ML code, not ported *)

(* HOL4 cmlPEGScript.sml:573: the ML values that the definitions
   below antiquote *)

(* HOL4 cmlPEGScript.sml:575-580: a theorem that HOL4 states as the
   value of an ML expression: cmlPEG_exec_thm *)

(* HOL4 cmlPEGScript.sml:582-586: ML code, not ported *)

(* [local] *)
let frange_image = prove
 (`FRANGE fm = IMAGE (FAPPLY fm) (FDOM fm)`,
  (REWRITE_TAC[FRANGE; EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
    MESON_TAC[]));;

(* HOL4 cmlPEGScript.sml:594-597: ML code, not ported *)

(* HOL4 cmlPEGScript.sml:599: the ML values that the definitions
   below antiquote *)

(* HOL4 cmlPEGScript.sml:601-613: ML code, not ported *)

(* HOL4 cmlPEGScript.sml:615-618: ML code, not ported *)

(* HOL4 cmlPEGScript.sml:620-629: ML code, not ported *)

(* HOL4 cmlPEGScript.sml:631-642: the ML values that the definitions
   below antiquote *)

(* HOL4 cmlPEGScript.sml:644-647: ML code, not ported *)

(* [simp] *)
let peg0_pegf = prove
 (`peg0 G (pegf s f) = peg0 G s`,
  CHEAT_TAC);;

(* [simp] *)
let peg0_seql = prove
 (`(peg0 G (seql [] f) <=> T) /\
   (peg0 G (seql (CONS h t) f) <=> peg0 G h /\ peg0 G (seql t I))`,
  CHEAT_TAC);;

(* [simp] *)
let peg0_tokeq = prove
 (`peg0 G (cmlPEG_tokeq t) = F`,
  CHEAT_TAC);;

(* [simp] *)
let peg0_tokSymP = prove
 (`peg0 G (tokSymP P) <=> F`,
  CHEAT_TAC);;

(* [simp] *)
let peg0_choicel = prove
 (`(peg0 G (choicel []) = F) /\
   (peg0 G (choicel (CONS h t)) <=> peg0 G h \/ pegfail G h /\ peg0
     G (choicel t))`,
  CHEAT_TAC);;

(* HOL4 cmlPEGScript.sml:681-695: a theorem that HOL4 states as the
   value of an ML expression: th *)

(* HOL4 cmlPEGScript.sml:697-717: ML code, not ported *)

(* HOL4 cmlPEGScript.sml:719-732: a theorem that HOL4 states as the
   value of an ML expression: th *)

(* HOL4 cmlPEGScript.sml:734-757: the ML values that the definitions
   below antiquote *)

(* HOL4 cmlPEGScript.sml:759-760: a theorem that HOL4 states as the
   value of an ML expression: cml_wfpeg_thm *)

(*
set_diff (TypeBase.constructors_of ``:MMLnonT``)
         (topo_nts @ [``nTyVarList``, ``nTypeList``, ``nDtypeDecls``,
                      ``nDtypeCons``])
*)

(* [local] *)
let subexprs_pnt = prove
 (`subexprs (cmlPEG_pnt n) = {cmlPEG_pnt n}`,
  (REWRITE_TAC[subexprs_def; cmlPEG_pnt_def]));;

(* HOL4 cmlPEGScript.sml:774-783: a theorem that HOL4 states as the
   value of an ML expression: PEG_exprs *)

(* [simp] *)
let PEG_wellformed = prove
 (`wfG cmlPEG`,
  CHEAT_TAC);;

(* HOL4 cmlPEGScript.sml:797-799: a theorem that HOL4 states as the
   value of an ML expression: parse_TopLevelDecs_total *)

(* HOL4 cmlPEGScript.sml:801-803: a theorem that HOL4 states as the
   value of an ML expression: coreloop_TopLevelDecs_total *)

(* HOL4 cmlPEGScript.sml:805-806: a theorem that HOL4 states as the
   value of an ML expression: owhile_TopLevelDecs_total *)

(* HOL4 cmlPEGScript.sml:808-816: ML code, not ported *)

(* HOL4 cmlPEGScript.sml:818-820: a proof *)
(* HOL4 cmlPEGScript.sml:821-822: a theorem that HOL4 states as the
   value of an ML expression: FDOM_cmlPEG_nts *)

(* HOL4 cmlPEGScript.sml:824-840: a proof *)
(* HOL4 cmlPEGScript.sml:841-842: a theorem that HOL4 states as the
   value of an ML expression: NTS_in_PEG_exprs *)

(* HOL4 cmlPEGScript.sml:844: ML code, not ported *)

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
