(* ======================================================== *)
(*  cmlPEG: ported from HOL4's
    compiler/parsing/cmlPEGScript.sml  *)
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

(* HOL4 overload (expanded in the port):
     monad_bind = OPTION_BIND *)
hol4_overload "assert" "OPTION_GUARD";;

(* HOL4 ML code, not ported:
val distinct_ths = let
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
  recurse ntlist
end
*)

let sumID_def = cake_define_list
  [`cmlPEG_sumID (INL x) = x`;
   `cmlPEG_sumID (INR y) = y`];;
hol4_overload "sumID" "cmlPEG_sumID";;

let mktokLf_def = cake_define
  `mktokLf t = [Lf
  ((grammar_TOK:tokens_token->(tokens_token,MMLnonT)grammar_symbol)
  (FST t),SND t)]`;;

let mkNd_def = cake_define
  `mkNd ntnm l = Nd (ntnm,ptree_list_loc l) l`;;

let bindNT0_def = cake_define
  `bindNT0 ntnm l = Nd ((INL:MMLnonT->MMLnonT+num)
  ntnm,ptree_list_loc l) l`;;

let bindNT_def = cake_define
  `bindNT ntnm l = [bindNT0 ntnm l]`;;

let mk_linfix_def = cake_define_list
  [`mk_linfix tgt acc [] = acc`;
   `mk_linfix tgt acc [t] = acc`;
   `mk_linfix tgt acc (opt :: t :: rest) =
     mk_linfix tgt (mkNd tgt [acc; opt; t]) rest`];;

let mk_rinfix_def = cake_define_list
  [`mk_rinfix tgt [] = mkNd tgt []`;
   `mk_rinfix tgt [t] = mkNd tgt [t]`;
   `mk_rinfix tgt (t :: opt :: rest) = mkNd tgt [t; opt; mk_rinfix
  tgt rest]`];;

let peg_linfix_def = cake_define
  `peg_linfix tgtnt rptsym opsym =
     peg_seq rptsym (peg_rpt (peg_seq opsym rptsym (++)) FLAT)
         (\a b. match a with
                    [] -> [] | h :: _1 -> [mk_linfix tgtnt (mkNd
                      tgtnt [h]) b])`;;

(* have to use these versions of choicel and pegf below because the
   "built-in" versions from HOL/examples/ use ARB in their definitions.
   Logically, the ARBs are harmless, but they completely mess with the
   translator
*)
let choicel_def = cake_define_list
  [`cmlPEG_choicel [] = peg_not (peg_empty []) []`;
   `cmlPEG_choicel (h :: t) = peg_choice h (cmlPEG_choicel t)
  cmlPEG_sumID`];;
hol4_overload "choicel" "cmlPEG_choicel";;

let pegf_def = cake_define
  `cmlPEG_pegf sym f = peg_seq sym (peg_empty []) (\l1 l2. f l1)`;;
hol4_overload "pegf" "cmlPEG_pegf";;

let seql_def = cake_define
  `seql l f = pegf (ITLIST (\p acc. peg_seq p acc (++)) l (peg_empty
  [])) f`;;

(* unused
Definition peg_nonfix_def:
  peg_nonfix tgtnt argsym opsym =
    seql [argsym; choicel [seq opsym argsym (++); empty []]] (bindNT
      tgtnt)
End *)

let try_def = cake_define
  `cmlPEG_try sym = choicel [sym; peg_empty []]`;;
hol4_overload "try" "cmlPEG_try";;

let tokeq_def = cake_define
  `cmlPEG_tokeq t = peg_tok ((=) t) mktokLf`;;
hol4_overload "tokeq" "cmlPEG_tokeq";;

let tokSymP_def = cake_define
  `tokSymP P =
     peg_tok (\t. ((OPTION_BIND) (destSymbolT t) (\s. OPTION_GUARD
       (P s))) = SOME one) mktokLf`;;

let pnt_def = cake_define
  `cmlPEG_pnt ntsym = peg_nt ((INL:MMLnonT->MMLnonT+num) ntsym) I`;;
hol4_overload "pnt" "cmlPEG_pnt";;

(* ---------------------------------------------------------------------
   -
    PEG for types
   ---------------------------------------------------------------------
     - *)

let peg_UQConstructorName_def = cake_define
  `peg_UQConstructorName =
     peg_tok (\t. (OPTION_BIND) (destAlphaT t) (\s.
                 OPTION_GUARD (~(s = (implode "")) /\ isUpper (strsub
                   s 0))) = SOME one)
         (bindNT nUQConstructorName o mktokLf)`;;

let peg_TypeDec_def = cake_define
  `peg_TypeDec =
     peg_seq (cmlPEG_tokeq tokens_DatatypeT)
         (peg_linfix ((INL:MMLnonT->MMLnonT+num) nDtypeDecls)
           (cmlPEG_pnt nDtypeDecl)
                     (cmlPEG_tokeq tokens_AndT))
         (\l1 l2. bindNT nTypeDec (l1 ++ l2))`;;

(* expressions *)
let peg_V_def = cake_define
  `peg_V =
    choicel [peg_tok (\t.
                   (OPTION_BIND) (destAlphaT t) (\s.
                      OPTION_GUARD (~(s IN {(implode
                        "before"),(implode "div"),(implode
                        "mod"),(implode "o")}) /\ ~(
                             s = (implode "")) /\ ~isUpper (strsub s
                               0))) = SOME one)
                 (bindNT nV o mktokLf);
             pegf (tokSymP (validPrefixSym o explode)) (bindNT
               nV)]`;;

let peg_longV_def = cake_define
  `peg_longV = peg_tok (\t. (OPTION_BIND) (destLongidT t) (\
                         (str,s).
                         OPTION_GUARD (~(s = (implode "")) /\
                           (isAlpha (strsub s 0) ==> ~isUpper (strsub s
                           0)))) = SOME one)
                   (bindNT nFQV o mktokLf)`;;

let peg_EbaseParenFn_def = cake_define
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

let peg_EbaseParen_def = cake_define
  `peg_EbaseParen =
     seql [cmlPEG_tokeq tokens_LparT; cmlPEG_pnt nE;
           choicel [cmlPEG_tokeq tokens_RparT;
                    seql [cmlPEG_tokeq tokens_CommaT; cmlPEG_pnt
                      nElist1; cmlPEG_tokeq tokens_RparT] I;
                    seql [cmlPEG_tokeq tokens_SemicolonT; cmlPEG_pnt
                      nEseq; cmlPEG_tokeq tokens_RparT] I]]
          peg_EbaseParenFn`;;

let peg_StructName_def = cake_define
  `peg_StructName =
     peg_tok (\t. (OPTION_BIND) (destAlphaT t) (\s.
                 OPTION_GUARD (~(s = (implode "")))) = SOME one)
         (bindNT nStructName o mktokLf)`;;

let ptPapply0_def = cake_define
  `ptPapply0 c x2 =
      match x2 with
        [] -> []
      | [pb_pt] -> bindNT nPapp [c; pb_pt]
      | (pb :: pbs) -> ptPapply0 (bindNT0 nPConApp [c; pb]) pbs`;;

let ptPapply_def = cake_define
  `ptPapply x1 =
      match x1 with
        [] -> []
      | [_3] -> []
      | (c :: rest) -> ptPapply0 (bindNT0 nPConApp [c]) rest`;;


let cmlPEG_def = cake_define
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
                          [] -> [] | h :: t -> [FOLDL (\a b. mkNd
                            ((INL:MMLnonT->MMLnonT+num) nEapp) [a; b])
                              (mkNd ((INL:MMLnonT->MMLnonT+num)
                                nEapp) [h]) t]));
               ((INL:MMLnonT->MMLnonT+num) nElist1,
                seql [cmlPEG_pnt nE; cmlPEG_try (seql [cmlPEG_tokeq
                  tokens_CommaT; cmlPEG_pnt nElist1] I)]
                     (bindNT nElist1));
               ((INL:MMLnonT->MMLnonT+num) nMultOps,
                pegf (
                  choicel (
                    tokSymP (validMultSym o explode) ::
                    MAP cmlPEG_tokeq [tokens_StarT; tokens_AlphaT
                      (implode "mod"); tokens_AlphaT (implode "div")]))
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
                            [] -> [] | h :: t -> [FOLDL (\a b. mkNd
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
                              [] -> [] | [c] -> [] | _4 -> ptPapply
                                pts);
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

(* HOL4 ML code, not ported:
val rules_t = ``cmlPEG.rules``
fun ty2frag ty = let
  open simpLib
  val {convs,rewrs} = TypeBase.simpls_of ty
in
  merge_ss (rewrites rewrs :: map conv_ss convs)
end
*)
(* can't use srw_ss() as it will attack the bodies of the rules,
   and in particular, will destroy predicates from tok
   constructors of the form
        do ... od = SOME ()
   which matches optionTheory.OPTION_BIND_EQUALS_OPTION, putting
   an existential into our rewrite thereby *)
(* HOL4 ML code, not ported:
val rules = SIMP_CONV (bool_ss ++ ty2frag ``:(α,β,γ,δ)peg``)
                      [cmlPEG_def, combinTheory.K_DEF,
                       finite_mapTheory.FUPDATE_LIST_THM] rules_t
*)

(* HOL4 ML code, not ported:
val _ = print "Calculating application of cmlPEG rules\n"
val cmlpeg_rules_applied = let
  val app0 = finite_mapSyntax.fapply_tm
  val theta =
      Type.match_type (type_of app0 |> dom_rng |> #1) (type_of rules_t)
  val app = inst theta app0
  val app_rules = AP_TERM app rules
  val sset = bool_ss ++ ty2frag ``:'a + 'b`` ++ ty2frag ``:MMLnonT``
  fun mkrule t =
      AP_THM app_rules ``mkNT ^t``
             |> SIMP_RULE sset
                  [finite_mapTheory.FAPPLY_FUPDATE_THM]
  val ths = TypeBase.constructors_of ``:MMLnonT`` |> map mkrule
in
    save_thm("cmlpeg_rules_applied", LIST_CONJ ths);
    ths
end
*)

(* HOL4 ML code, not ported:
val spec0 =
    peg_nt_thm |> Q.GEN `G`  |> Q.ISPEC `cmlPEG`
               |> SIMP_RULE (srw_ss()) [FDOM_cmlPEG]
               |> Q.GEN `n`
*)

(* HOL4 ML code, not ported:
val mkNT = ``mkNT``
*)

(* HOL4 ML code, not ported:
val test1 = time EVAL
             “peg_exec cmlPEG (pnt nErel)
              (map_loc [IntT 3; StarT; IntT 4; SymbolT «/»; IntT (-2);
                        SymbolT «>»; AlphaT «x»] 0)
              [] NONE [] done failed”
*)

(* HOL4 ML code, not ported:
val peg_range =
    SIMP_CONV (srw_ss())
              (FDOM_cmlPEG :: frange_image :: cmlpeg_rules_applied)
              ``FRANGE cmlPEG.rules``
*)

(* HOL4 ML code, not ported:
val peg_start = SIMP_CONV(srw_ss()) [cmlPEG_def]``cmlPEG.start``
*)

(* HOL4 ML code, not ported:
val wfpeg_rwts = wfpeg_cases
                   |> ISPEC ``cmlPEG``
                   |> (fn th => map (fn t => Q.SPEC t th)
                                    [`seq e1 e2 f`, `choice e1 e2 f`,
                                      `tok P f`,
                                     `any f`, `empty v`, `not e v`, `rpt
                                       e f`,
                                     `choicel []`, `choicel (h::t)`,
                                       `tokeq t`,
                                     `pegf e f`, ‘tokSymP P’
                      ])
                   |> map (CONV_RULE
                             (RAND_CONV (SIMP_CONV (srw_ss())
                                                   [choicel_def,
                                                     seql_def,
                                                    tokeq_def,
                                                      tokSymP_def,
                                                    pegf_def])))
*)

(* HOL4 ML code, not ported:
val wfpeg_pnt = wfpeg_cases
                  |> ISPEC ``cmlPEG``
                  |> Q.SPEC `pnt n`
                  |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss())
                    [pnt_def]))
*)

(* HOL4 ML code, not ported:
val peg0_rwts = peg0_cases
                  |> ISPEC ``cmlPEG`` |> CONJUNCTS
                  |> map (fn th => map (fn t => Q.SPEC t th)
                                       [`tok P f`, `choice e1 e2 f`,
                                        ‘seq e1 e2 f’, ‘tokSymP P’,
                                        `tokeq t`, `empty l`, `not e
                                          v`])
                  |> List.concat
                  |> map (CONV_RULE
                            (RAND_CONV (SIMP_CONV (srw_ss())
                                                  [tokeq_def,
                                                    tokSymP_def])))
*)

(* HOL4 ML code, not ported:
val pegfail_t = ``pegfail``
val peg0_rwts = let
  fun filterthis th = let
    val c = concl th
    val (l,r) = dest_eq c
    val (f,_) = strip_comb l
  in
    not (same_const pegfail_t f) orelse is_const r
  end
in
  List.filter filterthis peg0_rwts
end
*)

(* HOL4 ML code, not ported:
val pegnt_case_ths = peg0_cases
                      |> ISPEC ``cmlPEG`` |> CONJUNCTS
                      |> map (Q.SPEC `pnt n`)
                      |> map (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss())
                        [pnt_def])))
*)

(* HOL4 ML code, not ported:
fun pegnt(t,acc) = let
  val th =
      Q.prove(`¬peg0 cmlPEG (pnt ^t)`,
            simp pegnt_case_ths >>
            simp cmlpeg_rules_applied >>
            simp[FDOM_cmlPEG, peg_V_def, peg_UQConstructorName_def,
                 peg_StructName_def, peg_EbaseParen_def,
                 peg_TypeDec_def, peg_longV_def, peg_linfix_def] >>
            simp(peg0_rwts @ acc))
  val nm = "peg0_" ^ term_to_string t
  val th' = save_thm(nm, SIMP_RULE bool_ss [pnt_def] th)
  val _ = export_rewrites [nm]
in
  th::acc
end
*)

(* HOL4 ML code, not ported:
val npeg0_rwts =
    List.foldl pegnt []
               [“nTypeDec”, “nTypeAbbrevDec”, “nOpID”, “nStructure”,
                “nDecl”, “nV”, “nUQTyOp”,
                “nUQConstructorName”, “nStructName”, “nConstructorName”,
                “nTypeName”,
                “nDtypeDecl”, “nDconstructor”, “nFDecl”, “nTyvarN”,
                “nTyOp”, “nTbase”, “nPTbase”, “nDType”, “nPType”,
                  “nType”,
                “nTypeList1”, “nTypeList2”,
                “nRelOps”, “nPtuple”, “nPbase”, “nPapp”,
                “nPcons”, “nPas”, “nPattern”,
                “nPatternList”, “nPbaseList1”,
                “nLetDec”, “nMultOps”, “nListOps”,
                “nFQV”, “nAddOps”, “nCompOps”, “nEliteral”,
                “nEbase”, “nEapp”,
                “nEmult”, “nEadd”, “nElistop”, “nErel”, “nEcomp”,
                “nEbefore”,
                “nEtyped”, “nElogicAND”, “nElogicOR”, “nEhandle”,
                “nE”, “nPE”, “nPEs”, “nElist1”,
                “nSpecLine”
               ]
*)

(* HOL4 ML code, not ported:
fun wfnt(t,acc) = let
  val th =
    Q.prove(`wfpeg cmlPEG (pnt ^t)`,
          SIMP_TAC (srw_ss())
                   (cmlpeg_rules_applied @
                    [wfpeg_pnt, FDOM_cmlPEG, try_def, peg_longV_def,
                     seql_def, peg_TypeDec_def, peg_V_def,
                     peg_EbaseParen_def, peg_StructName_def,
                     peg_UQConstructorName_def,
                     tokeq_def, peg_linfix_def]) THEN
          simp(wfpeg_rwts @ npeg0_rwts @ peg0_rwts @ acc))
in
  th::acc
end;
*)

(* HOL4 ML code, not ported:
val topo_nts = [“nV”, “nTyvarN”, “nTypeDec”, “nTypeAbbrevDec”,
                “nSpecLine”, “nSpecLineList”, “nSignatureValue”,
                “nStructure”,
                “nDecl”,
                “nUQTyOp”, “nUQConstructorName”, “nStructName”,
                “nConstructorName”, “nTyVarList”, “nTypeName”, “nTyOp”,
                “nTbase”, “nPTbase”, “nTbaseList”, “nDType”, “nPType”,
                “nListOps”, “nRelOps”, “nPtuple”, “nPbase”, “nPapp”,
                “nPcons”, “nPas”, “nPattern”,
                “nPatternList”, “nPbaseList1”,
                “nPEs”, “nMultOps”, “nLetDec”, “nLetDecs”,
                “nFQV”,
                “nFDecl”, “nAddOps”, “nCompOps”, “nOpID”,
                “nEliteral”, “nEbase”, “nEapp”,
                “nEmult”, “nEadd”, “nElistop”, “nErel”,
                “nEcomp”, “nEbefore”, “nEtyped”, “nElogicAND”,
                “nElogicOR”, “nPE”, “nPEsfx”, “nEhandle”, “nE”,
                “nType”, “nTypeList1”, “nTypeList2”,
                “nEseq”, “nElist1”, “nDtypeDecl”,
                “nOptTypEqn”,
                “nDecls”, “nDconstructor”, “nAndFDecls”,
                “nOptionalSignatureAscription”,
                “nTopLevelDecs”, “nNonETopLevelDecs”
               ]
*)

(*
set_diff (TypeBase.constructors_of ``:MMLnonT``)
         (topo_nts @ [``nTyVarList``, ``nTypeList``, ``nDtypeDecls``,
                      ``nDtypeCons``])
*)

(* HOL4 ML code, not ported:
local
  val c = concl FDOM_cmlPEG
  val r = rhs c
  fun recurse acc t =
      case Lib.total pred_setSyntax.dest_insert t of
          SOME(e,t') => recurse (e :: acc) t'
        | NONE => acc
  val nts = recurse [] r
in
*)

(* HOL4 ML code, not ported:
  local
    fun p t = Q.prove(`^t ∈ FDOM cmlPEG.rules`, simp[FDOM_cmlPEG])
  in
*)

(* HOL4 ML code, not ported:
  local
    val exprs_th' = REWRITE_RULE [pnt_def] PEG_exprs
                                 |> INST_TYPE [alpha |-> “:string”]
    val exprs_t = rhs (concl exprs_th')
    val nt = mk_thy_const{Thy = "peg", Name = "nt",
                          Ty = ``:MMLnonT inf -> (mlptree list ->
                            mlptree list) ->
                               (token,MMLnonT,mlptree list,string)
                                 pegsym``}
    val I_t = mk_thy_const{Thy = "combin", Name = "I",
                           Ty = ``:mlptree list -> mlptree list``}
    fun p t = let
      val _ = print ("PEGexpr: "^term_to_string t^"\n")
      val th0 = prove(pred_setSyntax.mk_in(list_mk_comb(nt,[t,I_t]),
        exprs_t),
                      simp[pnt_def])
                handle e => (print("Failed on "^term_to_string t^"\n");
                             raise e)
    in CONV_RULE (RAND_CONV (K (SYM exprs_th'))) th0 end
  in
*)

(* HOL4 ML code, not ported:
end (* local *)
*)
