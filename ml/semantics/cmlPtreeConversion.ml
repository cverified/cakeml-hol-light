(* ======================================================== *)
(*  cmlPtreeConversion: ported from HOL4's
    semantics/cmlPtreeConversionScript.sml  *)
(* ======================================================== *)

(*
  Specification of how to convert parse trees to abstract syntax.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/encoders/asm/asmSem.ml";;
needs "compiler/parsing/cmlPEG.ml";;
needs "lib/grammar.ml";;
needs "lib/location.ml";;
needs "lib/peg.ml";;
needs "semantics/ast.ml";;
needs "semantics/gram.ml";;
needs "semantics/namespace.ml";;
needs "semantics/tokenUtils.ml";;
needs "semantics/tokens.ml";;

(* handling constructor arities gets very complicated when "open" is
   implemented *)
let PCstate0_FIELDS = define_record "PCstate0"
  ["fixities","(mlstring,num option)fmap";
   "ctr_arities","((mlstring,mlstring)namespace_id,num)fmap"];;
(* recording a fixity of NONE is what you have to do to represent an
   explicit nonfix declaration *)

(* HOL4 type abbreviation (expanded in the port):
     M = PCstate0 list -> ('a # PCstate0 list) option *)

let empty_PCstate0_def = cake_define
  `empty_PCstate0 = mk_PCstate0 FEMPTY FEMPTY`;;

let mpushPC_scope_def = cake_define
  `(mpushPC_scope:PCstate0 list->(1#PCstate0 list) option) = (\pcs.
  SOME (one,empty_PCstate0 :: pcs))`;;

let fixity_lookup_def = cake_define
  `fixity_lookup nm pcs =
     (match pcs with
         [] -> NONE | pc0 :: rest ->
           (match FLOOKUP (PCstate0_fixities pc0) nm with
               NONE -> fixity_lookup nm rest | SOME NONE -> NONE |
                 SOME r -> r))`;;

(* mfixity_lookup : mlstring -> num M
    'fails' if the mlstring has no fixity, even though it is perfectly
    reasonable for a mlstring to be nonfix.
*)
let mfixity_lookup_def = cake_define
  `(mfixity_lookup nm:PCstate0 list->(num#PCstate0 list) option) =
     (\pcs. OPTION_MAP (\r. (r,pcs)) (fixity_lookup nm pcs))`;;

let mFUPD_HD_def = cake_define
  `mFUPD_HD f pcs =
     (match pcs with
         [] -> NONE | h :: t -> SOME (one,f h :: t))`;;

(* msetfix : mlstring -> num option -> unit M *)
let msetfix_def = cake_define
  `(msetfix nm fix:PCstate0 list->(1#PCstate0 list) option) =
     mFUPD_HD (\s0. PCstate0_fixities_fupd (\fm. fm |+ (nm,fix))
       s0)`;;

(* mpop_anonscope : unit M *)
let mpop_anonscope_def = cake_define
  `(mpopscope:PCstate0 list->(1#PCstate0 list) option) = (\pcs.
     match pcs with
       [] -> NONE | _1 :: t -> SOME (one,t))`;;

let mpop_namedscope_def = cake_define
  `(mpop_namedscope (s:mlstring):PCstate0 list->(1#PCstate0 list)
  option) = (\pcs.
     match pcs with
       [] -> NONE | [_2] -> NONE | curr :: next :: rest -> SOME
         (one,next :: rest))`;;
(* needs to be adjusted so that constructors (only) declared in the
   current
   scope get recorded in the next level up with the given name as a
     prefix.

   Does nothing different at this stage, when I expect just to be
     handling
   fixities (which are handled in a non-exportable way).
 *)


(* ---------------------------------------------------------------------
   -
    We'll be using the option monad quite a bit in what follows
   ---------------------------------------------------------------------
     - *)

(* HOL4 overload (expanded in the port):
     lift = option$OPTION_MAP *)

let ifM_def = cake_define
  `ifM bM tM eM =
     monad_bind bM (\
        b.
        if b then tM else eM)`;;

let mk_binop_def = cake_define
  `mk_binop a_op a1 a2 =
     (if a_op = Short (implode "::") then Con (SOME (Short
       (implode "::"))) [a1; a2] else App Opapp [App Opapp [Var a_op;
       a1]; a2])`;;

(* HOL4 overload (expanded in the port):
     ' = λf a. OPTION_BIND a f *)

let tokcheck_def = cake_define
  `tokcheck pt tok' <=> (FAPPLY destTOK (destLf pt) = SOME tok')`;;

let ptree_UQTyop_def = cake_define_list
  [`ptree_UQTyop (Lf _4) = NONE`;
   `ptree_UQTyop (Nd nt' args) =
      (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nUQTyOp) then NONE
        else
        match args with
            [pt] ->
            monad_bind (destLf pt) (\
              lf. monad_bind (destTOK lf) (\
              tk.
              destSymbolT tk ++ destAlphaT tk)) | _5 -> NONE)`];;

let ptree_TyvarN_def = cake_define_list
  [`ptree_TyvarN (Lf _7) = NONE`;
   `ptree_TyvarN (Nd nt' args) =
      (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nTyvarN) then NONE
        else
        match args with
            [tyv] -> destTyvarPT tyv | _8 -> NONE)`];;

let Long_Short_def = cake_define_list
  [`Long_Short End (s:mlstring) = Short s`;
   `Long_Short (Mod x xs:tokens_path) s = Long x (Long_Short xs s)`];;

let ptree_Tyop_def = cake_define_list
  [`ptree_Tyop (Lf _10) = NONE`;
   `ptree_Tyop (Nd nt' args) =
      (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nTyOp) then NONE
        else
        match args with
            [pt] ->
            monad_bind (FAPPLY destLongidT (FAPPLY destTOK (destLf
              pt))) (\
              (xs,s).
              SOME (Long_Short xs s)) ++
            monad_bind (ptree_UQTyop pt) (\
              nm.
              SOME (Short nm)) | _11 -> NONE)`];;

let tokcheckl_def = cake_define
  `tokcheckl pts toks <=>
     (match (pts,toks) with
       ([],[]) -> T | (pt :: prest,tok' :: tokrest) -> tokcheck pt
         tok' /\ tokcheckl prest tokrest | _12 -> F)`;;

let ptree_linfix_def = cake_define
  `ptree_linfix topnt opn elnt (pt:(tokens_token,MMLnonT,locs)parsetree)
  =
     (match pt with
         Lf _13 -> NONE | Nd nt' args ->
         (if FST nt' = (INL:MMLnonT->MMLnonT+num) topnt then
           match args with
               [pt] -> monad_bind (elnt pt) (\e. SOME [e]) | [x;
                 op_pt; pt] -> monad_ignore_bind
                 (assert (tokcheck op_pt opn)) (monad_bind
                   (ptree_linfix topnt opn elnt x) (\
                 front. monad_bind (elnt pt) (\
                 last.
                 SOME (front ++ [last])))) | _14 -> NONE else
                   NONE))`;;

let tuplify_def = cake_define
  `tuplify tys =
      match tys with
        [] -> NONE
      | [ty] -> SOME ty
      | tys -> SOME (Attup tys)`;;

let ptree_Type_def = cake_define_list
  [`(ptree_Type nt' (Lf _15):ast_t option) = NONE`;
   `ptree_Type nm (Nd nt' args) =
         (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nm) then NONE
           else if nm = nType then
           match args with
              [dt] ->
              monad_bind (ptree_PType dt) (\
                tys.
                tuplify tys) | [dt; arrowt; rt] ->
                  monad_ignore_bind
                    (assert (tokcheck arrowt ArrowT)) (monad_bind
                      (ptree_PType dt) (\
                    dtys. monad_bind (tuplify dtys) (\
                    dty. monad_bind (ptree_Type nType rt) (\
                    rty.
                    SOME (Atfun dty rty))))) | _16 -> NONE else if
                      nm = nDType then
           match args with
               [pt] -> ptree_Type nTbase pt | [dt; opn] ->
                 monad_bind (ptree_Type nDType dt) (\
                              dty. monad_bind (ptree_Tyop opn) (\
                              opname.
                              SOME (Atapp [dty] opname))) | _17 ->
                                NONE else if nm = nTbase then
           match args with
               [pt] ->
                    OPTION_MAP Atvar (destTyvarPT pt) ++
                    OPTION_MAP (Atapp []) (ptree_Tyop pt) | [lpart;
                      t; rpart] ->
                  monad_ignore_bind
                    (assert (tokcheck lpart LparT /\ tokcheck rpart
                      RparT)) (
                    ptree_Type nType t) | [lpart; tl; rpart; opn] ->
               monad_ignore_bind
                  (assert (tokcheck lpart LparT /\ tokcheck rpart
                    RparT)) (monad_bind (ptree_Typelist2 tl) (\
                  tylist. monad_bind (ptree_Tyop opn) (\
                  opname.
                  SOME (Atapp tylist opname)))) | _18 -> NONE
                    else NONE)`;
   `(ptree_Typelist2 ptree:(ast_t list) option) =
         (match ptree with
           Lf _19 -> NONE | Nd nt' args ->
           (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nTypeList2)
             then NONE else
             match args with [dt; commat; tl'] ->
                 monad_ignore_bind
                   (assert (tokcheck commat CommaT)) (monad_bind
                     (ptree_Type nType dt) (\
                   ty. monad_bind (ptree_TypeList1 tl') (\
                   tylist.
                   SOME (ty :: tylist)))) | _20 -> NONE))`;
   `(ptree_TypeList1 ptree:(ast_t list) option) =
        (match ptree with
            Lf _21 -> NONE | Nd nt' args ->
            (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nTypeList1)
              then NONE else
              match args with
                  [dt] ->
                  monad_bind (ptree_Type nType dt) (\
                    ty.
                    SOME ([ty])) | [dt; commat; tl] ->
                  monad_ignore_bind
                    (assert (tokcheck commat CommaT)) (monad_bind
                      (ptree_Type nType dt) (\
                    ty. monad_bind (ptree_TypeList1 tl) (\
                    tl.
                    SOME (ty :: tl)))) | _22 -> NONE))`;
   `(ptree_PType ptree:(ast_t list) option) =
         (match ptree with
             Lf _23 -> NONE | Nd nt' args ->
             (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nPType) then
               NONE else
               match args with
                   [dty_pt] ->
                   monad_bind (ptree_Type nDType dty_pt) (\
                     dty.
                     SOME [dty]) | [dty_pt; st; pty_pt] ->
                   monad_ignore_bind
                     (assert (tokcheck st StarT)) (monad_bind
                       (ptree_Type nDType dty_pt) (\
                     dty. monad_bind (ptree_PType pty_pt) (\
                     ptys.
                     SOME (dty :: ptys)))) | _24 -> NONE))`];;

let ptree_TypeName_def = cake_define
  `(ptree_TypeName ptree:(mlstring list#mlstring) option) =
     (match ptree with
       Lf _25 -> NONE | Nd nt' args ->
       (if FST nt' = (INL:MMLnonT->MMLnonT+num) nTypeName then
         match args with
           [opt] -> monad_bind (ptree_UQTyop opt) (\opn. SOME
             ([],opn)) | [sym; opt] -> monad_bind (destTyvarPT sym)
             (\tyvn. monad_bind (ptree_UQTyop opt) (\
                            opn.
                            return ([tyvn],opn))) | [lp; tyvl; rp;
                              opt] ->
           monad_ignore_bind
             (assert (tokcheck lp LparT /\ tokcheck rp RparT))
               (monad_bind (ptree_linfix nTyVarList CommaT ptree_TyvarN
               tyvl) (\
             tyvnms. monad_bind (ptree_UQTyop opt) (\
             opn.
             return (tyvnms,opn)))) | _26 -> NONE else NONE))`;;

let ptree_UQConstructorName_def = cake_define_list
  [`ptree_UQConstructorName (Lf _28) = NONE`;
   `ptree_UQConstructorName (Nd nm args) =
      (if ~(FST nm = (INL:MMLnonT->MMLnonT+num) nUQConstructorName)
        then NONE else
        match args with
            [pt] -> FAPPLY destAlphaT (FAPPLY destTOK (destLf
              pt)) | _29 -> NONE)`];;

let ptree_ConstructorName_def = cake_define
  `ptree_ConstructorName ast =
     (match ast with
         Lf _30 -> NONE | Nd nt' args ->
         (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nConstructorName)
           then NONE else
           match args with
               [pt] ->
               monad_bind (ptree_UQConstructorName pt) (\
                 s.
                 SOME (Short s)) ++
               monad_bind (FAPPLY destLongidT (FAPPLY destTOK (destLf
                 pt))) (\
                 (xs,s).
                 SOME (Long_Short xs s)) | _31 -> NONE))`;;

let detuplify_def = cake_define
  `detuplify ty =
      match ty with
        Attup args -> args
      | ty -> [ty]`;;

let ptree_PTbase_def = cake_define
  `ptree_PTbase ast =
     (match ast with
         Lf _32 -> fail | Nd nt' args ->
         (if FST nt' = (INL:MMLnonT->MMLnonT+num) nPTbase then
           match args with
               [pt] ->
                 OPTION_MAP Atvar (destTyvarPT pt) ++
                 OPTION_MAP (Atapp []) (ptree_Tyop pt) | [lpart; t;
                   rpart] ->
               monad_ignore_bind
                 (assert (tokcheck lpart LparT /\ tokcheck rpart
                   RparT)) (
                 ptree_Type nType t) | _33 -> fail else fail))`;;

let ptree_TbaseList_def = cake_define
  `ptree_TbaseList ast =
     (match ast with
         Lf _34 -> fail | Nd nt' args ->
         (if FST nt' = (INL:MMLnonT->MMLnonT+num) nTbaseList then
           match args with
               [] -> return [] | [ptb_pt; rest_pt] -> monad_bind
                 (ptree_PTbase ptb_pt) (\
                 b. monad_bind (ptree_TbaseList rest_pt) (\
                 rest.
                 return (b :: rest))) | _35 -> fail else fail))`;;

let ptree_Dconstructor_def = cake_define
  `ptree_Dconstructor ast =
     (match ast with
         Lf x -> NONE | Nd nt' args ->
         (if FST nt' = (INL:MMLnonT->MMLnonT+num) nDconstructor then
           match args with
               [] -> NONE | t :: ts ->
               monad_bind (ptree_UQConstructorName t) (\
                  cname. monad_bind (match ts with
                              [blist] ->
                              monad_bind (ptree_TbaseList blist) (\
                              args.
                              return args) | _36 -> NONE) (\
                  types.
                  SOME (cname,types))) else NONE))`;;

let ptree_DtypeDecl_def = cake_define
  `ptree_DtypeDecl (pt:(tokens_token,MMLnonT,locs)parsetree) =
     (match pt with
         Lf _37 -> NONE | Nd nt' args ->
         (if FST nt' = (INL:MMLnonT->MMLnonT+num) nDtypeDecl then
           match args with
               [tynm_pt; eqt; dtc_pt] -> monad_ignore_bind
                 (assert (tokcheck eqt EqualsT)) (monad_bind
                   (ptree_TypeName tynm_pt) (\
                 tynm. monad_bind (ptree_linfix nDtypeCons BarT
                   ptree_Dconstructor dtc_pt) (\
                 dtc.
                 SOME (FST tynm,SND tynm,dtc)))) | _38 -> NONE
                   else NONE))`;;

let ptree_TypeDec_def = cake_define
  `(ptree_TypeDec ptree:((mlstring list#mlstring#(mlstring#ast_t list)
  list) list) option) =
     (match ptree with
       Lf _39 -> NONE | Nd nt' args ->
       (if FST nt' = (INL:MMLnonT->MMLnonT+num) nTypeDec then
         match args with
             [datatype_pt; pt] -> monad_ignore_bind
               (assert (tokcheck datatype_pt DatatypeT)) (
               ptree_linfix nDtypeDecls AndT ptree_DtypeDecl pt) |
                 _40 -> NONE else NONE))`;;

let ptree_TypeAbbrevDec_def = cake_define
  `(ptree_TypeAbbrevDec ptree:dec option) =
     (match ptree with
       Lf _41 -> NONE | Nd nt' args ->
       (if FST nt' = (INL:MMLnonT->MMLnonT+num) nTypeAbbrevDec then
         match args with
           [typetok; tynm; eqtok; typ_pt] -> monad_ignore_bind
             (assert (tokcheck typetok TypeT /\ tokcheck eqtok
               EqualsT)) (monad_bind (ptree_TypeName tynm) (\
             (vars,nm). monad_bind (ptree_Type nType typ_pt) (\
             typ.
             SOME (Dtabbrev (SND nt') vars nm typ)))) | _42 ->
               NONE else NONE))`;;

let singleSymP_def = cake_define
  `singleSymP P x2 =
      match x2 with
        [pt] -> monad_bind (FAPPLY destSymbolT (FAPPLY destTOK
          (destLf pt))) (\s. monad_ignore_bind
                         (assert (P s)) (
                         return (Short s)))
      | _43 -> NONE`;;

let ptree_Op_def = cake_define_list
  [`ptree_Op (Lf _44) = NONE`;
   `ptree_Op (Nd nt' subs) =
      (if FST nt' = (INL:MMLnonT->MMLnonT+num) nMultOps then
        if tokcheckl subs [StarT] then SOME (Short (implode "*"))
          else if tokcheckl subs [AlphaT (implode "mod")] then SOME
          (Short (implode "mod")) else if tokcheckl subs [AlphaT
          (implode "div")] then SOME (Short (implode "div")) else
          singleSymP (validMultSym o explode) subs else if FST nt' =
          (INL:MMLnonT->MMLnonT+num) nAddOps then singleSymP
          (validAddSym o explode) subs else if FST nt' =
          (INL:MMLnonT->MMLnonT+num) nListOps then singleSymP
          (validListSym o explode) subs else if FST nt' =
          (INL:MMLnonT->MMLnonT+num) nRelOps then
        singleSymP (validRelSym o explode) subs ++
        monad_ignore_bind (assert (tokcheckl subs [EqualsT]))
          (return (Short (implode "="))) else if FST nt' =
          (INL:MMLnonT->MMLnonT+num) nCompOps then
        if tokcheckl subs [SymbolT (implode ":=")] then SOME
          (Short (implode ":=")) else if tokcheckl subs [AlphaT
          (implode "o")] then SOME (Short (implode "o")) else NONE
          else NONE)`];;

let ptree_V_def = cake_define_list
  [`ptree_V (Lf _46) = NONE`;
   `ptree_V (Nd nt' subs) =
         monad_ignore_bind
           (assert (FST nt' = (INL:MMLnonT->MMLnonT+num) nV)) (
           match subs with
              [pt] -> monad_bind (FAPPLY destTOK (destLf pt)) (\t.
                         destAlphaT t ++ destSymbolT t) | _47 ->
                           NONE)`];;

let ptree_FQV_def = cake_define_list
  [`ptree_FQV (Lf _49) = NONE`;
   `ptree_FQV (Nd nt' args) =
      (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nFQV) then NONE
        else
        match args with
            [pt] -> OPTION_MAP Short (ptree_V pt) ++
                    monad_bind (FAPPLY destLongidT (FAPPLY destTOK
                      (destLf pt))) (\
                      (xs,s).
                      SOME (Long_Short xs s)) | _50 -> NONE)`];;

let isSymbolicConstructor_def = cake_define
  `isSymbolicConstructor s =
     return (s = "::")`;;

let isConstructor_def = cake_define
  `isConstructor s =
       ifM (isSymbolicConstructor s)
         (return T)
         (return (match oHD s with NONE -> F | SOME c -> isAlpha c
           /\ isUpper c))`;;

(* third clause below will lead to a failure when the environment is
   consulted to reveal that the long-id given does not correspond to a
   constructor.  We do this rather than fail to make the "totality"
     theorem
   work *)
let EtoPat_def = cake_define
  `EtoPat x1 =
        match x1 with
          Con x args -> (if NULL args then SOME (Pcon x []) else
            NONE)
        | (Var (Short n)) -> SOME (Pvar n)
        | (Var (Long str n)) -> SOME (Pcon (SOME (Long str n)) [])
        | _51 -> NONE`;;

let ptree_OpID_def = cake_define_list
  [`ptree_OpID (Lf _54) = NONE`;
   `ptree_OpID (Nd nt' subs) =
      (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nOpID) then NONE
        else
        match subs with
            [Lf
              ((TOK:tokens_token->(tokens_token,MMLnonT)grammar_symbol)
              tk,_55)] ->
            monad_bind (destAlphaT tk) (\
                s.
                ifM (isConstructor (explode s))
                    (return (Con (SOME (Short s)) []))
                    (return (Var (Short s)))) ++
            monad_bind (destSymbolT tk) (\
                s.
                ifM (isSymbolicConstructor (explode s))
                    (return (Con (SOME (Short s)) []))
                    (return (Var (Short s)))) ++
            monad_bind (destLongidT tk) (\
                (path,s).
                ifM (isConstructor (explode s))
                    (return (Con (SOME (Long_Short path s)) []))
                    (return (Var (Long_Short path s)))) ++
            (if tk = StarT then
               ifM (isSymbolicConstructor "*")
                   (return (Con (SOME (Short (implode "*"))) []))
                   (return (Var (Short (implode "*")))) else if
                     tk = EqualsT then return (Var (Short (implode
                     "="))) else NONE) | _56 -> NONE)`];;

let papply_def = cake_define
  `Papply pat arg =
     (match pat with
       Pcon cn args -> Pcon cn (args ++ [arg]) | _57 -> pat)`;;

(* HOL4 ML code, not ported:
val maybe_handleRef_def = PmatchHeuristics.with_classic_heuristic Define
  ‘
  maybe_handleRef (Pcon (SOME (Short «Ref»)) [pat]) = Pref pat ∧
  maybe_handleRef p = p’
*)

let ptree_Pattern_def = cake_define_list
  [`ptree_Pattern nt' (Lf _58) = NONE`;
   `ptree_Pattern nt' (Nd nm args) =
        (if ~((INL:MMLnonT->MMLnonT+num) nt' = FST nm) then NONE
          else if FST nm = (INL:MMLnonT->MMLnonT+num) nPbase then
          match args with
              [vic] ->
              ptree_Pattern nPtuple vic ++
              monad_bind (ptree_ConstructorName vic) (\
                 cname.
                 SOME (Pcon (SOME cname) [])) ++
              monad_bind (ptree_V vic) (\vname. SOME (Pvar vname))
                ++
              monad_bind (destLf vic) (\
                lf. monad_bind (destTOK lf) (\
                t.
                (monad_bind (destIntT t) (\i. return (Plit (IntLit
                  i))) ++
                 monad_bind (destStringT t) (\s. return (Plit
                   (StrLit s))) ++
                 monad_bind (destCharT t) (\c. return (Plit (Char
                   c)))))) ++
              monad_ignore_bind (assert (tokcheck vic UnderbarT))
                (return Pany) | [lb; rb] ->
              (if tokcheckl args [LbrackT; RbrackT] then
                SOME (Pcon (SOME (Short (implode "[]"))) []) else if
                  tokcheckl [lb] [OpT] then
                monad_bind (ptree_OpID rb) (\e. EtoPat e) else NONE)
                  | [lb; plistpt; rb] ->
              monad_ignore_bind
                (assert (tokcheckl [lb; rb] [LbrackT; RbrackT]))
                  (monad_bind (ptree_Plist plistpt) (\
                plist.
                SOME (ITLIST (\p a. Pcon (SOME (Short (implode
                  "::"))) [p; a])
                            plist
                            (Pcon (SOME (Short (implode "[]")))
                              [])))) | _59 -> NONE else if FST nm =
                              (INL:MMLnonT->MMLnonT+num) nPConApp then
          match args with
            [cn] ->
            monad_bind (ptree_ConstructorName cn) (\
              cname.
              return (Pcon (SOME cname) [])) | [capp_pt; base_pt] ->
            monad_bind (ptree_Pattern nPConApp capp_pt) (\
              capp. monad_bind (ptree_Pattern nPbase base_pt) (\
              base.
              return (Papply capp base))) | _60 -> fail else if FST
                nm = (INL:MMLnonT->MMLnonT+num) nPapp then
          match args with
              [pb] -> ptree_Pattern nPbase pb | [capp_pt; ppt] ->
              monad_bind (ptree_Pattern nPConApp capp_pt) (\
                capp. monad_bind (ptree_Pattern nPbase ppt) (\
                b.
                return (maybe_handleRef (Papply capp b)))) | _61 ->
                  NONE else if FST nm = (INL:MMLnonT->MMLnonT+num)
                  nPcons then
          match args with
              [papt] -> ptree_Pattern nPapp papt | [papt; cons_t;
                pcons_pt] ->
              monad_ignore_bind
                (assert (tokcheck cons_t (SymbolT (implode "::"))))
                  (monad_bind (ptree_Pattern nPapp papt) (\
                pa. monad_bind (ptree_Pattern nPcons pcons_pt) (\
                patt.
                SOME (Pcon (SOME (Short (implode "::"))) [pa;
                  patt])))) | _62 -> NONE else if FST nm =
                  (INL:MMLnonT->MMLnonT+num) nPas then
          match args with
              [papt] -> ptree_Pattern nPcons papt | [vt; as_t; papt]
                ->
              monad_ignore_bind
                (assert (tokcheck as_t AsT)) (monad_bind
                  (ptree_Pattern nPcons papt) (\
                pa. monad_bind (ptree_V vt) (\
                vtt.
                SOME (Pas pa vtt)))) | _63 -> fail else if FST nm =
                  (INL:MMLnonT->MMLnonT+num) nPattern then
          match args with
              [pas] -> ptree_Pattern nPas pas | [pas_pt; colon_t;
                type_pt] ->
              monad_ignore_bind
                (assert (tokcheck colon_t ColonT)) (monad_bind
                  (ptree_Pattern nPas pas_pt) (\
                pc. monad_bind (ptree_Type nType type_pt) (\
                ty.
                return (Ptannot pc ty)))) | _64 -> fail else if FST
                  nm = (INL:MMLnonT->MMLnonT+num) nPtuple then
          match args with
              [lp; rp] -> monad_ignore_bind (assert (tokcheckl [lp;
                rp] [LparT; RparT])) (
                             return (Pcon NONE [])) | [lp; pl_pt;
                               rp] ->
              monad_ignore_bind
                (assert (tokcheckl [lp; rp] [LparT; RparT]))
                  (monad_bind (ptree_Plist pl_pt) (\
                pl.
                match pl with
                    [] -> NONE | [p] -> SOME p | _65 -> SOME
                      (Pcon NONE pl))) | _66 -> NONE else NONE)`;
   `ptree_Plist (Lf _67) = NONE`;
   `ptree_Plist (Nd nm args) =
         (if ~(FST nm = (INL:MMLnonT->MMLnonT+num) nPatternList)
           then NONE else
           match args with
               [p_pt] ->
               monad_bind (ptree_Pattern nPattern p_pt) (\
                 p.
                 SOME [p]) | [p; ct; pl] ->
               monad_ignore_bind
                 (assert (tokcheck ct CommaT)) (monad_bind
                   (ptree_Pattern nPattern p) (\
                 hdpat. monad_bind (ptree_Plist pl) (\
                 tlpats.
                 SOME (hdpat :: tlpats)))) | _68 -> NONE)`];;

new_type_abbrev("ptree",`: (tokens_token,MMLnonT,locs)parsetree`);;

let ptree_PbaseList1_def = cake_define_list
  [`ptree_PbaseList1 (Lf _70) = NONE`;
   `ptree_PbaseList1 (Nd nm args) =
         (if ~(FST nm = (INL:MMLnonT->MMLnonT+num) nPbaseList1) then
           NONE else
           match args with
               [p_pt] -> (OPTION_MAP) SINGL (ptree_Pattern nPbase
                 p_pt) | [p_pt; pl_pt] ->
                   lift2 CONS
                         (ptree_Pattern nPbase p_pt)
                         (ptree_PbaseList1 pl_pt) | _71 -> NONE)`];;

let eseq_encode_def = cake_define
  `Eseq_encode x1 =
        match x1 with
          [] -> NONE
        | [e] -> SOME e
        | (e :: es) ->
      monad_bind (Eseq_encode es) (\
        body.
        SOME (Let NONE e body))`;;

let dest_Conk_def = cake_define
  `dest_Conk x1 k v =
        match x1 with
          Con x y -> k x y
        | _72 -> v`;;

let destFFIop_def = cake_define
  `destFFIop x1 =
        match x1 with
          FFI s -> SOME s
        | _73 -> NONE`;;

let strip_loc_expr_def = cake_define
  `strip_loc_expr e =
        match e with
          Lannot e l ->
       (match (strip_loc_expr e) with
         (e0,_74) -> (e0,SOME l))
        | e -> (e,NONE)`;;

let merge_locsopt_def = cake_define
  `merge_locsopt x1 x2 =
      match (x1,x2) with
        (SOME l1,SOME l2) -> SOME (merge_locs l1 l2)
      | (_75,_76) -> NONE`;;

let optLannot_def = cake_define_list
  [`optLannot NONE e = e`;
   `optLannot (SOME l) e = Lannot e l`];;

let mkAst_App_def = cake_define
  `mkAst_App a1 a2 =
     (let (a10,loc1) = strip_loc_expr a1 in
       dest_Conk a10
         (\nm_opt args.
           if nm_opt = SOME (Short (implode "Ref")) /\ NULL args then
             App Opref [a2] else
             let (a2',loc2) = strip_loc_expr a2 in
               optLannot (merge_locsopt loc1 loc2) (Con nm_opt (args
                 ++ [a2'])))
         (match a10 with
            App opn args ->
              (match (destFFIop opn) with
                 NONE -> App Opapp [a1; a2] | SOME s -> App opn
                   (args ++ [a2])) | _77 -> App Opapp [a1; a2]))`;;

let dePat_def = cake_define
  `dePat p b =
        match p with
          Pvar v -> (v,b)
        | p -> ((implode ""),Mat (Var (Short (implode "")))
          [(p,b)])`;;

let mkFun_def = cake_define
  `mkFun p b = UNCURRY Fun (dePat p b)`;;

let ptree_Eliteral_def = cake_define_list
  [`ptree_Eliteral (Lf _78) = NONE`;
   `ptree_Eliteral (Nd nt' subs) =
      monad_ignore_bind
        (assert (LENGTH subs = 1 /\ FST nt' =
          (INL:MMLnonT->MMLnonT+num) nEliteral)) (monad_bind (destLf (HD
          subs)) (\
        lf. monad_bind (destTOK lf) (\
        t.
        (monad_bind (destIntT t) (\i. return (Lit (IntLit i))) ++
         monad_bind (destCharT t) (\c. return (Lit (Char c))) ++
         monad_bind (destStringT t) (\s. return (Lit (StrLit s))) ++
         monad_bind (destWordT t) (\n. return (Lit (Word64 (n2w
           n)))) ++
         monad_bind (destFFIT t) (\s. return (App (FFI s)
           []))))))`];;

let bind_loc_def = cake_define
  `bind_loc e l' =
      match e with
        Lannot e l -> Lannot e l
      | e -> Lannot e l'`;;

let letFromPat_def = cake_define
  `letFromPat p rhs body =
     (match p with
       Pany -> Let NONE rhs body | Pvar v -> Let (SOME v) rhs body
         | _79 -> Mat rhs [(p,body)])`;;

let ptree_Expr_def = cake_define_list
  [`ptree_Expr ent (Lf _80) = NONE`;
   `ptree_Expr ent (Nd (nt',loc) subs) =
    monad_bind (if (INL:MMLnonT->MMLnonT+num) ent = nt' then
        if nt' = (INL:MMLnonT->MMLnonT+num) nEbase then
          match subs with
              [lpart; pt; rpart] ->
                (if tokcheck lpart LparT then
                  monad_ignore_bind
                    (assert (tokcheck rpart RparT)) (monad_bind
                      (ptree_Eseq pt) (\
                    eseq.
                    Eseq_encode eseq)) else
                  monad_ignore_bind
                    (assert (tokcheckl [lpart; rpart] [LbrackT;
                      RbrackT])) (monad_bind (ptree_Exprlist nElist1 pt)
                      (\
                    elist.
                    SOME (ITLIST (\e acc. Con (SOME (Short (implode
                      "::"))) [e; acc])
                           elist
                              (Con (SOME (Short (implode "[]")))
                                []))))) | [single] ->
                ptree_Eliteral single ++
                monad_bind (ptree_FQV single) (\
                  s.
                  SOME (Var s)) ++
                monad_bind (ptree_ConstructorName single) (\cname.
                   SOME (Con (SOME cname) [])) ++
                ptree_Expr nEtuple single | [lp; rp] -> (if
                  tokcheckl [lp; rp] [LparT; RparT] then
                           SOME (Con NONE []) else if tokcheckl [lp;
                             rp] [LbrackT; RbrackT] then
                           SOME (Con (SOME (Short (implode "[]")))
                             []) else if tokcheck lp OpT then
                           ptree_OpID rp else
                           NONE) | [lett; letdecs_pt; intok; ept;
                             endt] ->
              monad_ignore_bind
                (assert (tokcheckl [lett; intok; endt] [LetT; InT;
                  EndT])) (monad_bind (ptree_LetDecs letdecs_pt) (\
                letdecs. monad_bind (ptree_Eseq ept) (\
                eseq. monad_bind (Eseq_encode eseq) (\
                e.
                SOME (ITLIST (\df acc. match df with
                              INL (p,e0) -> letFromPat p e0 acc |
                                INR fds -> Letrec fds acc)
                           letdecs
                           e))))) | _81 -> NONE else if nt' =
                             (INL:MMLnonT->MMLnonT+num) nEapp then
          match subs with
              [t1; t2] -> monad_bind (ptree_Expr nEapp t1) (\
                            a1. monad_bind (ptree_Expr nEbase t2) (\
                            a2.
                            SOME (mkAst_App a1 a2))) | [t] ->
                              ptree_Expr nEbase t | _82 -> NONE else if
                              nt' = (INL:MMLnonT->MMLnonT+num) nEtuple
                              then
          match subs with
              [lpart; el2; rpart] ->
              monad_ignore_bind
                (assert (tokcheckl [lpart; rpart] [LparT; RparT]))
                  (monad_bind (ptree_Exprlist nElist2 el2) (\
                es.
                SOME (Con NONE es))) | _83 -> NONE else if nt' =
                  (INL:MMLnonT->MMLnonT+num) nEmult then
          match subs with
            [t1; opt; t2] -> monad_bind (ptree_Expr nEmult t1) (\
              a1. monad_bind (ptree_Op opt) (\
              a_op. monad_bind (ptree_Expr nEapp t2) (\
              a2.
              return (mk_binop a_op a1 a2)))) | [t] -> ptree_Expr
                nEapp t | _84 -> NONE else if nt' =
                (INL:MMLnonT->MMLnonT+num) nEadd then
          match subs with
              [t1; opt; t2] -> monad_bind (ptree_Expr nEadd t1) (\
                a1. monad_bind (ptree_Op opt) (\
                a_op. monad_bind (ptree_Expr nEmult t2) (\
                a2.
                return (mk_binop a_op a1 a2)))) | [t] -> ptree_Expr
                  nEmult t | _85 -> NONE else if nt' =
                  (INL:MMLnonT->MMLnonT+num) nElistop then
          match subs with
              [t1; opt; t2] -> monad_bind (ptree_Expr nEadd t1) (\
                a1. monad_bind (ptree_Op opt) (\
                a_op. monad_bind (ptree_Expr nElistop t2) (\
                a2.
                return (mk_binop a_op a1 a2)))) | [t] -> ptree_Expr
                  nEadd t | _86 -> NONE else if nt' =
                  (INL:MMLnonT->MMLnonT+num) nErel then
          match subs with
              [t1; opt; t2] -> monad_bind (ptree_Expr nErel t1) (\
                a1. monad_bind (ptree_Op opt) (\
                a_op. monad_bind (ptree_Expr nElistop t2) (\
                a2.
                return (mk_binop a_op a1 a2)))) | [t] -> ptree_Expr
                  nElistop t | _87 -> NONE else if nt' =
                  (INL:MMLnonT->MMLnonT+num) nEcomp then
          match subs with
              [t1; opt; t2] -> monad_bind (ptree_Expr nEcomp t1) (\
                a1. monad_bind (ptree_Op opt) (\
                a_op. monad_bind (ptree_Expr nErel t2) (\
                a2.
                return (mk_binop a_op a1 a2)))) | [t] -> ptree_Expr
                  nErel t | _88 -> NONE else if nt' =
                  (INL:MMLnonT->MMLnonT+num) nEbefore then
          match subs with
            [t1; opt; t2] -> monad_ignore_bind
              (assert (tokcheck opt (AlphaT (implode "before"))))
                (monad_bind (ptree_Expr nEbefore t1) (\
              a1. monad_bind (ptree_Expr nEcomp t2) (\
              a2.
              return (mk_binop (Short (implode "before")) a1 a2))))
                | [t] -> ptree_Expr nEcomp t | _89 -> NONE else if nt' =
                (INL:MMLnonT->MMLnonT+num) nEtyped then
          match subs with
            [e_pt; colon; ty_pt] -> monad_ignore_bind
              (assert (tokcheck colon ColonT)) (monad_bind
                (ptree_Expr nEbefore e_pt) (\
              e. monad_bind (ptree_Type nType ty_pt) (\
              ty.
              return (Tannot e ty)))) | [t] -> ptree_Expr nEbefore t
                | _90 -> NONE else if nt' = (INL:MMLnonT->MMLnonT+num)
                nElogicAND then
          match subs with
              [t1; andt; t2] -> monad_ignore_bind
                (assert (tokcheck andt AndalsoT)) (monad_bind
                  (ptree_Expr nElogicAND t1) (\
                a1. monad_bind (ptree_Expr nEtyped t2) (\
                a2.
                SOME (Log Andalso a1 a2)))) | [t] -> ptree_Expr
                  nEtyped t | _91 -> NONE else if nt' =
                  (INL:MMLnonT->MMLnonT+num) nElogicOR then
          match subs with
              [t1; ort; t2] -> monad_ignore_bind
                (assert (tokcheck ort OrelseT)) (monad_bind
                  (ptree_Expr nElogicOR t1) (\
                a1. monad_bind (ptree_Expr nElogicAND t2) (\
                a2.
                SOME (Log Orelse a1 a2)))) | [t] -> ptree_Expr
                  nElogicAND t | _92 -> NONE else if nt' =
                  (INL:MMLnonT->MMLnonT+num) nEhandle then
          match subs with
              [pt] -> ptree_Expr nElogicOR pt | [e1pt; handlet; ent]
                ->
              monad_ignore_bind
                (assert (tokcheck handlet HandleT)) (monad_bind
                  (ptree_Expr nElogicOR e1pt) (\
                e. monad_bind (ptree_PEs ent) (\
                pes.
                SOME (Handle e pes)))) | _93 -> NONE else if nt' =
                  (INL:MMLnonT->MMLnonT+num) nE then
          match subs with [t] -> ptree_Expr nEhandle t | [raiset;
            ept] ->
              monad_ignore_bind
                (assert (tokcheck raiset RaiseT)) (monad_bind
                  (ptree_Expr nE ept) (\
                e.
                SOME (Raise e))) | [fnt; pnt'; arrowt; ent] ->
              monad_ignore_bind
                (assert (tokcheckl [fnt; arrowt] [FnT; DarrowT]))
                  (monad_bind (ptree_Pattern nPattern pnt') (\
                p. monad_bind (ptree_Expr nE ent) (\
                e.
                SOME (mkFun p e)))) ++ monad_ignore_bind
                (assert (tokcheckl [fnt; arrowt] [CaseT; OfT]))
                  (monad_bind (ptree_Expr nE pnt') (\
                e. monad_bind (ptree_PEs ent) (\
                pes.
                SOME (Mat e pes)))) | [ift; g; thent; te; elset; ee]
                  -> monad_ignore_bind
                (assert (tokcheckl [ift; thent; elset] [IfT; ThenT;
                  ElseT])) (monad_bind (ptree_Expr nE g) (\
                a1. monad_bind (ptree_Expr nE te) (\
                a2. monad_bind (ptree_Expr nE ee) (\
                a3.
                SOME (If a1 a2 a3))))) | _94 -> NONE else NONE else
                  NONE) (\
    e.
      SOME (bind_loc e loc))`;
   `ptree_Exprlist nm ast =
         (match ast with
             Lf _95 -> NONE | Nd (nt',_96) subs ->
             (if nt' = (INL:MMLnonT->MMLnonT+num) nElist1 then
               match subs with
                   [sing] -> monad_bind (ptree_Expr nE sing) (\e.
                     SOME [e]) | [e; ct; el1] ->
                   monad_ignore_bind
                     (assert (tokcheck ct CommaT)) (monad_bind
                       (ptree_Expr nE e) (\
                     front. monad_bind (ptree_Exprlist nElist1 el1)
                       (\
                     back.
                     SOME (front :: back)))) | _97 -> NONE else if
                       nt' = (INL:MMLnonT->MMLnonT+num) nElist2 then
               match subs with
                   [e; ct; el1] ->
                   monad_ignore_bind
                     (assert (tokcheck ct CommaT)) (monad_bind
                       (ptree_Expr nE e) (\
                     front. monad_bind (ptree_Exprlist nElist1 el1)
                       (\
                     back.
                     SOME (front :: back)))) | _98 -> NONE else
                       NONE))`;
   `ptree_AndFDecls ast =
      (match ast with
          Lf _99 -> NONE | Nd (nt',_100) subs ->
          (if nt' = (INL:MMLnonT->MMLnonT+num) nAndFDecls then
            match subs with
                [single] -> monad_bind (ptree_FDecl single) (\fdec.
                  SOME ([fdec])) | [fdecspt; andt; fdecpt] ->
                monad_ignore_bind
                  (assert (tokcheck andt AndT)) (monad_bind
                    (ptree_AndFDecls fdecspt) (\
                  fdecs. monad_bind (ptree_FDecl fdecpt) (\
                  fdec.
                  SOME (fdecs ++ [fdec])))) | _101 -> NONE else
                    NONE))`;
   `ptree_FDecl ast =
        (match ast with
            Lf _102 -> NONE | Nd (nt',_103) subs ->
            (if nt' = (INL:MMLnonT->MMLnonT+num) nFDecl then
              match subs with
                  [fname_pt; pats_pt; eqt; body_pt] ->
                  monad_ignore_bind
                    (assert (tokcheck eqt EqualsT)) (monad_bind
                      (ptree_V fname_pt) (\
                    fname. monad_bind (ptree_PbaseList1 pats_pt) (\
                    ps. monad_bind (oHD ps) (\
                    p1. monad_bind (ptree_Expr nE body_pt) (\
                    body0.
                    SOME (fname,dePat p1 (ITLIST mkFun (TL ps)
                      body0))))))) | _104 -> NONE else NONE))`;
   `ptree_LetDecs ptree =
        (match ptree with
            Lf _105 -> NONE | Nd (nt',_106) args ->
            (if ~(nt' = (INL:MMLnonT->MMLnonT+num) nLetDecs) then
              NONE else
              match args with
                  [] -> SOME [] | [ld_pt; lds_pt] ->
                  (if tokcheck ld_pt SemicolonT then ptree_LetDecs
                    lds_pt else
                    monad_bind (ptree_LetDec ld_pt) (\
                      ld. monad_bind (ptree_LetDecs lds_pt) (\
                      lds.
                      SOME (ld :: lds)))) | _107 -> NONE))`;
   `ptree_LetDec ptree =
        (match ptree with
            Lf _108 -> NONE | Nd (nt',_109) args ->
            (if ~(nt' = (INL:MMLnonT->MMLnonT+num) nLetDec) then
              NONE else
              match args with
                  [funtok; andfdecls_pt] ->
                  monad_ignore_bind
                    (assert (tokcheck funtok FunT)) (monad_bind
                      (ptree_AndFDecls andfdecls_pt) (\
                    fds.
                    SOME (INR fds))) | [valtok; p_pt; eqtok; e_pt]
                      ->
                  monad_ignore_bind
                    (assert (tokcheckl [valtok; eqtok] [ValT;
                      EqualsT])) (monad_bind (ptree_Pattern nPattern
                      p_pt) (\
                    p. monad_bind (ptree_Expr nE e_pt) (\
                    e.
                    SOME (INL (p,e))))) | _110 -> NONE))`;
   `ptree_PEs (Lf _111) = (NONE:((ast_pat#ast_exp) list) option)`;
   `ptree_PEs (Nd (nt',_112) args) =
        (if ~(nt' = (INL:MMLnonT->MMLnonT+num) nPEs) then NONE else
          match args with
              [pattern_pt; arrow_pt; pe_pt] ->
              monad_ignore_bind
                (assert (tokcheck arrow_pt DarrowT)) (monad_bind
                  (ptree_Pattern nPattern pattern_pt) (\
                pat. monad_bind (ptree_PE pe_pt) (\
                (e,pes).
                SOME ((pat,e) :: pes)))) | _113 -> NONE)`;
   `ptree_PE (Lf _114) = NONE`;
   `ptree_PE (Nd (nt',_115) args) =
         (if ~(nt' = (INL:MMLnonT->MMLnonT+num) nPE) then NONE else
           match args with
               [eorraise_pt; pesfx_pt] ->
               monad_ignore_bind
                 (assert (tokcheck eorraise_pt RaiseT)) (monad_bind
                   (ptree_PE pesfx_pt) (\
                 (e,pes).
                 SOME (Raise e,pes))) ++
               monad_bind (ptree_Expr nElogicOR eorraise_pt) (\
                 e. monad_bind (ptree_PEsfx pesfx_pt) (\
                 (handlep,pes).
                 SOME (if handlep then (Handle e pes,[]) else
                   (e,pes)))) | [fncase_tok; epat_pt; arrowof_tok;
                   last_pt] ->
               monad_ignore_bind
                 (assert (tokcheckl [fncase_tok; arrowof_tok] [FnT;
                   DarrowT])) (monad_bind (ptree_Pattern nPattern
                   epat_pt) (\
                 pat. monad_bind (ptree_Expr nE last_pt) (\
                 e.
                 SOME (mkFun pat e,[])))) ++
               monad_ignore_bind
                 (assert (tokcheckl [fncase_tok; arrowof_tok]
                   [CaseT; OfT])) (monad_bind (ptree_Expr nE epat_pt) (\
                 e. monad_bind (ptree_PEs last_pt) (\
                 pes.
                 SOME (Mat e pes,[])))) | [iftok; ge_pt; thentok;
                   then_pt; elsetok; else_pt] ->
               monad_ignore_bind
                 (assert (tokcheckl [iftok; thentok; elsetok] [IfT;
                   ThenT; ElseT])) (monad_bind (ptree_Expr nE ge_pt) (\
                 ge. monad_bind (ptree_Expr nE then_pt) (\
                 te. monad_bind (ptree_PE else_pt) (\
                 (ee,rest).
                 SOME (If ge te ee,rest))))) | _116 -> NONE)`;
   `(ptree_PEsfx (Lf _117):(bool#(ast_pat#ast_exp) list) option) =
  NONE`;
   `ptree_PEsfx (Nd (nt',_118) args) =
         (if ~(nt' = (INL:MMLnonT->MMLnonT+num) nPEsfx) then NONE
           else
           match args with
               [] -> SOME (F,[]) | [handlebar_tok; pes_pt] ->
               monad_ignore_bind
                 (assert (tokcheck handlebar_tok HandleT))
                   (monad_bind (ptree_PEs pes_pt) (\
                 pes.
                 SOME (T,pes))) ++
               monad_ignore_bind
                 (assert (tokcheck handlebar_tok BarT)) (monad_bind
                   (ptree_PEs pes_pt) (\
                 pes.
                 SOME (F,pes))) | _119 -> NONE)`;
   `ptree_Eseq (Lf _120) = NONE`;
   `ptree_Eseq (Nd (nt',_121) args) =
        (if ~(nt' = (INL:MMLnonT->MMLnonT+num) nEseq) then NONE else
          match args with
              [single] ->
              monad_bind (ptree_Expr nE single) (\
                e.
                SOME [e]) | [e_pt; semi; seq_pt] ->
              monad_ignore_bind
                (assert (tokcheck semi SemicolonT)) (monad_bind
                  (ptree_Expr nE e_pt) (\
                e. monad_bind (ptree_Eseq seq_pt) (\
                seq.
                SOME (e :: seq)))) | _122 -> NONE)`];;

let ptree_StructName_def = cake_define_list
  [`ptree_StructName (Lf _124) = NONE`;
   `ptree_StructName (Nd nm args) =
      (if ~(FST nm = (INL:MMLnonT->MMLnonT+num) nStructName) then
        NONE else
        match args with
            [pt] -> FAPPLY destAlphaT (FAPPLY destTOK (destLf
              pt)) | _125 -> NONE)`];;

let ptree_OptTypEqn_def = cake_define_list
  [`ptree_OptTypEqn (Lf _127) = (NONE:(ast_t option) option)`;
   `ptree_OptTypEqn (Nd nt' args) =
      (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nOptTypEqn) then
        NONE else
        match args with
            [] -> SOME NONE | [eqtok; typ_pt] ->
            monad_ignore_bind
              (assert (tokcheck eqtok EqualsT)) (monad_bind
                (ptree_Type nType typ_pt) (\
              typ.
              SOME (SOME typ))) | _128 -> NONE)`];;

let ptree_SpecLine_def = cake_define_list
  [`ptree_SpecLine (Lf _130) = NONE`;
   `ptree_SpecLine (Nd nt' args) =
      (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nSpecLine) then
        NONE else
        match args with
            [td_pt] ->
            monad_bind (ptree_TypeDec td_pt) (\
              td.
              SOME one) | [exntok; dcon_pt] ->
            monad_ignore_bind
              (assert (tokcheck exntok ExceptionT)) (monad_bind
                (ptree_Dconstructor dcon_pt) (\
              (nm,tys).
              SOME one)) | [typetok; tynm_pt; opteqn_pt] ->
            monad_ignore_bind
              (assert (tokcheck typetok TypeT)) (monad_bind
                (ptree_TypeName tynm_pt) (\
              (vs,nm). monad_bind (ptree_OptTypEqn opteqn_pt) (\
              opteqn.
              SOME one))) | [valtok; vname_pt; coltok; type_pt] ->
            monad_ignore_bind
              (assert (tokcheckl [valtok; coltok] [ValT; ColonT]))
                (monad_bind (ptree_V vname_pt) (\
              vname. monad_bind (ptree_Type nType type_pt) (\
              ty.
              SOME one))) | _131 -> NONE)`];;

let ptree_SpeclineList_def = cake_define_list
  [`ptree_SpeclineList (Lf _133) = NONE`;
   `ptree_SpeclineList (Nd nt' args) =
      (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nSpecLineList) then
        NONE else
        match args with
            [] -> SOME one | [sl_pt; sll_pt] ->
            (if tokcheck sl_pt SemicolonT then ptree_SpeclineList
              sll_pt else
              monad_bind (ptree_SpecLine sl_pt) (\
                sl. monad_bind (ptree_SpeclineList sll_pt) (\
                sll.
                SOME one))) | _134 -> NONE)`];;

let ptree_SignatureValue_def = cake_define_list
  [`ptree_SignatureValue (Lf _136) = NONE`;
   `ptree_SignatureValue (Nd nt' args) =
      (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nSignatureValue)
        then NONE else
        match args with
            [sigtok; sll_pt; endtok] ->
            monad_ignore_bind
              (assert (tokcheckl [sigtok; endtok] [SigT; EndT])) (
              ptree_SpeclineList sll_pt) | _137 -> NONE)`];;

let ptree_Decl_def = cake_define_list
  [`(ptree_Decl pt:dec option) =
        (match pt with
           Lf _138 -> NONE | Nd (nt',locs) args ->
           (if ~(nt' = (INL:MMLnonT->MMLnonT+num) nDecl) then NONE
             else
             match args with
                 [dt] ->
                 monad_bind (ptree_TypeDec dt) (\
                   tydec.
                   SOME (Dtype (locs) tydec)) ++ ptree_TypeAbbrevDec
                     dt ++ ptree_Structure dt | [funtok; fdecls] ->
                 monad_ignore_bind
                   (assert (tokcheck funtok FunT)) (monad_bind
                     (ptree_AndFDecls fdecls) (\
                   fdecs.
                   SOME (Dletrec (locs) fdecs))) ++
                 monad_ignore_bind
                   (assert (tokcheck funtok ExceptionT)) (monad_bind
                     (ptree_Dconstructor fdecls) (\
                   (enm,etys).
                   SOME (Dexn (locs) enm etys))) | [valtok; patpt;
                     eqtok; ept] ->
                 monad_ignore_bind
                   (assert (tokcheckl [valtok; eqtok] [ValT;
                     EqualsT])) (monad_bind (ptree_Pattern nPattern
                     patpt) (\
                   pat. monad_bind (ptree_Expr nE ept) (\
                   e.
                   SOME (Dlet (locs) pat e)))) | [localtok;
                     decls1_pt; intok; decls2_pt; endtok] ->
                 monad_ignore_bind
                   (assert (tokcheckl [localtok; intok; endtok]
                     [LocalT; InT; EndT])) (monad_bind (ptree_Decls
                     decls1_pt) (\
                   decls1. monad_bind (ptree_Decls decls2_pt) (\
                   decls2.
                   return (Dlocal decls1 decls2)))) | _139 ->
                     NONE))`;
   `ptree_Decls (Lf _140) = NONE`;
   `ptree_Decls (Nd (nt',_141) args) =
        (if ~(nt' = (INL:MMLnonT->MMLnonT+num) nDecls) then NONE
          else
          match args with
              [] -> SOME [] | [d_pt; ds_pt] ->
              (if tokcheck d_pt SemicolonT then ptree_Decls ds_pt
                else
                monad_bind (ptree_Decl d_pt) (\
                  d. monad_bind (ptree_Decls ds_pt) (\
                  ds.
                  SOME (d :: ds)))) | _142 -> NONE)`;
   `ptree_Structure (Lf _143) = NONE`;
   `ptree_Structure (Nd nt' args) =
      (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nStructure) then
        NONE else
        match args with
            [structuretok; sname_pt; asc_opt; eqtok; structtok;
              ds_pt; endtok] ->
            monad_ignore_bind
              (assert (tokcheckl [structtok; structuretok; eqtok;
                endtok]
                              [StructT; StructureT; EqualsT; EndT]))
                                (monad_bind (ptree_StructName sname_pt)
                                (\
              sname. monad_bind (match asc_opt with
                         Lf _144 -> NONE | Nd nt' args ->
                           (if ~(FST nt' =
                             (INL:MMLnonT->MMLnonT+num)
                             nOptionalSignatureAscription) then
                             NONE else
                             match args with
                              [] -> SOME NONE | [sealtok; sig_pt] ->
                              monad_ignore_bind
                              (assert (tokcheck sealtok SealT))
                                (monad_bind (ptree_SignatureValue
                                sig_pt) (\
                              sigv.
                              SOME (SOME sigv))) | _145 -> NONE)) (\
              asc. monad_bind (ptree_Decls ds_pt) (\
              ds.
              SOME (Dmod sname ds))))) | _146 -> NONE)`];;

let ptree_TopLevelDecs_def = cake_define_list
  [`ptree_TopLevelDecs (Lf _147) = fail`;
   `ptree_TopLevelDecs (Nd nt' args) =
         (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nTopLevelDecs)
           then fail else
           match args with
               [] -> return [] | [td_pt; tds_pt] ->
               (if tokcheck td_pt SemicolonT then ptree_TopLevelDecs
                 tds_pt else
                 monad_bind (ptree_Decl td_pt) (\
                   td. monad_bind (ptree_NonETopLevelDecs tds_pt) (\
                   tds.
                   return (td :: tds)))) | [e_pt; semitok; tds_pt]
                     ->
               monad_ignore_bind
                 (assert (tokcheck semitok SemicolonT)) (monad_bind
                   (ptree_Expr nE e_pt) (\
                 e. monad_bind (ptree_TopLevelDecs tds_pt) (\
                 tds.
                 return (Dlet (SND nt') (Pvar (implode "it")) e
                   :: tds)))) | _148 -> NONE)`;
   `ptree_NonETopLevelDecs (Lf _149) = fail`;
   `ptree_NonETopLevelDecs (Nd nt' args) =
         (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num)
           nNonETopLevelDecs) then fail else
           match args with
             [] -> return [] | [pt1; pt2] ->
             (if tokcheck pt1 SemicolonT then ptree_TopLevelDecs pt2
               else
               monad_bind (ptree_Decl pt1) (\
                 td. monad_bind (ptree_NonETopLevelDecs pt2) (\
                 tds.
                 return (td :: tds)))) | _150 -> fail)`];;
