(* ======================================================== *)
(*  cmlPtreeConversion: ported from HOL4's
    semantics/cmlPtreeConversionScript.sml
    A definition theory, with 61 definitions, 1 datatype and 8
    theorems.  Needed by cmlParse.ml and semantics.ml.  *)
(* ======================================================== *)

(*
  Specification of how to convert parse trees to abstract syntax.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/closLang.ml";;
needs "lib/grammar.ml";;
needs "lib/location.ml";;
needs "semantics/ast.ml";;
needs "semantics/gram.ml";;
needs "semantics/namespace.ml";;
needs "semantics/tokenUtils.ml";;

(* handling constructor arities gets very complicated when "open" is
   implemented *)
let PCstate0_FIELDS = define_record "PCstate0"
  ["fixities","(mlstring,num option)fmap";
   "ctr_arities","((mlstring,mlstring)namespace_id,num)fmap"];;
(* recording a fixity of NONE is what you have to do to represent an
   explicit nonfix declaration *)

(* HOL4 cmlPtreeConversionScript.sml:22: the type abbreviation M,
   which the port expands *)

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
       [] -> NONE | [_2] -> NONE | curr :: next' :: rest -> SOME
         (one,next' :: rest))`;;
(* needs to be adjusted so that constructors (only) declared in the current
   scope get recorded in the next level up with the given name as a prefix.

   Does nothing different at this stage, when I expect just to be handling
   fixities (which are handled in a non-exportable way).
 *)


(* ----------------------------------------------------------------------
    We'll be using the option monad quite a bit in what follows
   ---------------------------------------------------------------------- *)

hol4_overload "++" "OPTION_CHOICE";;

(* HOL4 cmlPtreeConversionScript.sml:94: the overload lift, which the
   port expands *)

let ifM_def = cake_define
  `ifM bM tM eM =
     OPTION_BIND bM (\
        b.
        if b then tM else eM)`;;

let mk_binop_def = cake_define
  `mk_binop a_op a1 a2 =
     (if a_op = Short (implode "::") then ast_Con (SOME (Short
       (implode "::"))) [a1; a2] else ast_App ast_Opapp [ast_App
       ast_Opapp [ast_Var a_op; a1]; a2])`;;

(* HOL4 cmlPtreeConversionScript.sml:110: the overload ', which the
   port expands *)

let tokcheck_def = cake_define
  `tokcheck pt tok' <=> ((\f a. OPTION_BIND a f) destTOK (destLf pt)
  = SOME tok')`;;

let ptree_UQTyop_def = cake_define_list
  [`ptree_UQTyop (Lf _4) = NONE`;
   `ptree_UQTyop (Nd nt' args) =
      (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nUQTyOp) then NONE
        else
        match args with
            [pt] ->
            OPTION_BIND (destLf pt) (\
              lf. OPTION_BIND (destTOK lf) (\
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
  [`Long_Short tokens_End (s:mlstring) = Short s`;
   `Long_Short (Mod x xs:tokens_path) (s:mlstring) = Long x
  (Long_Short xs s)`];;

let ptree_Tyop_def = cake_define_list
  [`ptree_Tyop (Lf _10) = NONE`;
   `ptree_Tyop (Nd nt' args) =
      (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nTyOp) then NONE
        else
        match args with
            [pt] ->
            OPTION_BIND ((\f a. OPTION_BIND a f) destLongidT ((\f a.
              OPTION_BIND a f) destTOK (destLf pt))) (\
              (xs,s).
              SOME (Long_Short xs s)) ++
            OPTION_BIND (ptree_UQTyop pt) (\
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
               [pt] -> OPTION_BIND (elnt pt) (\e. SOME [e]) | [x;
                 op_pt; pt] -> OPTION_IGNORE_BIND
                 (OPTION_GUARD (tokcheck op_pt opn)) (OPTION_BIND
                   (ptree_linfix topnt opn elnt x) (\
                 front. OPTION_BIND (elnt pt) (\
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
              OPTION_BIND (ptree_PType dt) (\
                tys.
                tuplify tys) | [dt; arrowt; rt] ->
                  OPTION_IGNORE_BIND
                    (OPTION_GUARD (tokcheck arrowt tokens_ArrowT))
                      (OPTION_BIND (ptree_PType dt) (\
                    dtys. OPTION_BIND (tuplify dtys) (\
                    dty. OPTION_BIND (ptree_Type nType rt) (\
                    rty.
                    SOME (Atfun dty rty))))) | _16 -> NONE else if
                      nm = nDType then
           match args with
               [pt] -> ptree_Type nTbase pt | [dt; opn] ->
                 OPTION_BIND (ptree_Type nDType dt) (\
                              dty. OPTION_BIND (ptree_Tyop opn) (\
                              opname.
                              SOME (Atapp [dty] opname))) | _17 ->
                                NONE else if nm = nTbase then
           match args with
               [pt] ->
                    OPTION_MAP Atvar (destTyvarPT pt) ++
                    OPTION_MAP (Atapp []) (ptree_Tyop pt) | [lpart;
                      t; rpart] ->
                  OPTION_IGNORE_BIND
                    (OPTION_GUARD (tokcheck lpart tokens_LparT /\
                      tokcheck rpart tokens_RparT)) (
                    ptree_Type nType t) | [lpart; tl; rpart; opn] ->
               OPTION_IGNORE_BIND
                  (OPTION_GUARD (tokcheck lpart tokens_LparT /\
                    tokcheck rpart tokens_RparT)) (OPTION_BIND
                    (ptree_Typelist2 tl) (\
                  tylist. OPTION_BIND (ptree_Tyop opn) (\
                  opname.
                  SOME (Atapp tylist opname)))) | _18 -> NONE
                    else NONE)`;
   `(ptree_Typelist2 ptree:(ast_t list) option) =
         (match ptree with
           Lf _19 -> NONE | Nd nt' args ->
           (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nTypeList2)
             then NONE else
             match args with [dt; commat; tl'] ->
                 OPTION_IGNORE_BIND
                   (OPTION_GUARD (tokcheck commat tokens_CommaT))
                     (OPTION_BIND (ptree_Type nType dt) (\
                   ty. OPTION_BIND (ptree_TypeList1 tl') (\
                   tylist.
                   SOME (ty :: tylist)))) | _20 -> NONE))`;
   `(ptree_TypeList1 ptree:(ast_t list) option) =
        (match ptree with
            Lf _21 -> NONE | Nd nt' args ->
            (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nTypeList1)
              then NONE else
              match args with
                  [dt] ->
                  OPTION_BIND (ptree_Type nType dt) (\
                    ty.
                    SOME ([ty])) | [dt; commat; tl] ->
                  OPTION_IGNORE_BIND
                    (OPTION_GUARD (tokcheck commat tokens_CommaT))
                      (OPTION_BIND (ptree_Type nType dt) (\
                    ty. OPTION_BIND (ptree_TypeList1 tl) (\
                    tl.
                    SOME (ty :: tl)))) | _22 -> NONE))`;
   `(ptree_PType ptree:(ast_t list) option) =
         (match ptree with
             Lf _23 -> NONE | Nd nt' args ->
             (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nPType) then
               NONE else
               match args with
                   [dty_pt] ->
                   OPTION_BIND (ptree_Type nDType dty_pt) (\
                     dty.
                     SOME [dty]) | [dty_pt; st; pty_pt] ->
                   OPTION_IGNORE_BIND
                     (OPTION_GUARD (tokcheck st tokens_StarT))
                       (OPTION_BIND (ptree_Type nDType dty_pt) (\
                     dty. OPTION_BIND (ptree_PType pty_pt) (\
                     ptys.
                     SOME (dty :: ptys)))) | _24 -> NONE))`];;

let ptree_TypeName_def = cake_define
  `(ptree_TypeName ptree:(mlstring list#mlstring) option) =
     (match ptree with
       Lf _25 -> NONE | Nd nt' args ->
       (if FST nt' = (INL:MMLnonT->MMLnonT+num) nTypeName then
         match args with
           [opt] -> OPTION_BIND (ptree_UQTyop opt) (\opn. SOME
             ([],opn)) | [sym; opt] -> OPTION_BIND (destTyvarPT sym)
             (\tyvn. OPTION_BIND (ptree_UQTyop opt) (\
                            opn.
                            SOME ([tyvn],opn))) | [lp; tyvl; rp; opt]
                              ->
           OPTION_IGNORE_BIND
             (OPTION_GUARD (tokcheck lp tokens_LparT /\ tokcheck rp
               tokens_RparT)) (OPTION_BIND (ptree_linfix nTyVarList
               tokens_CommaT ptree_TyvarN tyvl) (\
             tyvnms. OPTION_BIND (ptree_UQTyop opt) (\
             opn.
             SOME (tyvnms,opn)))) | _26 -> NONE else NONE))`;;

let ptree_UQConstructorName_def = cake_define_list
  [`ptree_UQConstructorName (Lf _28) = NONE`;
   `ptree_UQConstructorName (Nd nm args) =
      (if ~(FST nm = (INL:MMLnonT->MMLnonT+num) nUQConstructorName)
        then NONE else
        match args with
            [pt] -> (\f a. OPTION_BIND a f) destAlphaT ((\f a.
              OPTION_BIND a f) destTOK (destLf pt)) | _29 -> NONE)`];;

let ptree_ConstructorName_def = cake_define
  `ptree_ConstructorName ast =
     (match ast with
         Lf _30 -> NONE | Nd nt' args ->
         (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nConstructorName)
           then NONE else
           match args with
               [pt] ->
               OPTION_BIND (ptree_UQConstructorName pt) (\
                 s.
                 SOME (Short s)) ++
               OPTION_BIND ((\f a. OPTION_BIND a f) destLongidT ((\f
                 a. OPTION_BIND a f) destTOK (destLf pt))) (\
                 (xs,s).
                 SOME (Long_Short xs s)) | _31 -> NONE))`;;

let detuplify_def = cake_define
  `detuplify ty =
      match ty with
        Attup args -> args
      | ty -> [ty]`;;

let detuplify_pmatch = cake_theorem "detuplify_pmatch"
  (fun () ->
    `!ty.
       detuplify ty =
       (match ty with
         Attup args -> args | ty -> [ty])`)
  CHEAT_TAC;;

let ptree_PTbase_def = cake_define
  `ptree_PTbase ast =
     (match ast with
         Lf _32 -> NONE | Nd nt' args ->
         (if FST nt' = (INL:MMLnonT->MMLnonT+num) nPTbase then
           match args with
               [pt] ->
                 OPTION_MAP Atvar (destTyvarPT pt) ++
                 OPTION_MAP (Atapp []) (ptree_Tyop pt) | [lpart; t;
                   rpart] ->
               OPTION_IGNORE_BIND
                 (OPTION_GUARD (tokcheck lpart tokens_LparT /\
                   tokcheck rpart tokens_RparT)) (
                 ptree_Type nType t) | _33 -> NONE else NONE))`;;

let ptree_TbaseList_def = cake_define
  `ptree_TbaseList ast =
     (match ast with
         Lf _34 -> NONE | Nd nt' args ->
         (if FST nt' = (INL:MMLnonT->MMLnonT+num) nTbaseList then
           match args with
               [] -> SOME [] | [ptb_pt; rest_pt] -> OPTION_BIND
                 (ptree_PTbase ptb_pt) (\
                 b. OPTION_BIND (ptree_TbaseList rest_pt) (\
                 rest.
                 SOME (b :: rest))) | _35 -> NONE else NONE))`;;

let ptree_Dconstructor_def = cake_define
  `ptree_Dconstructor ast =
     (match ast with
         Lf x -> NONE | Nd nt' args ->
         (if FST nt' = (INL:MMLnonT->MMLnonT+num) nDconstructor then
           match args with
               [] -> NONE | t :: ts ->
               OPTION_BIND (ptree_UQConstructorName t) (\
                  cname. OPTION_BIND (match ts with
                              [blist] ->
                              OPTION_BIND (ptree_TbaseList blist) (\
                              args.
                              SOME args) | _36 -> NONE) (\
                  types.
                  SOME (cname,types))) else NONE))`;;

let ptree_DtypeDecl_def = cake_define
  `ptree_DtypeDecl (pt:(tokens_token,MMLnonT,locs)parsetree) =
     (match pt with
         Lf _37 -> NONE | Nd nt' args ->
         (if FST nt' = (INL:MMLnonT->MMLnonT+num) nDtypeDecl then
           match args with
               [tynm_pt; eqt; dtc_pt] -> OPTION_IGNORE_BIND
                 (OPTION_GUARD (tokcheck eqt tokens_EqualsT))
                   (OPTION_BIND (ptree_TypeName tynm_pt) (\
                 tynm. OPTION_BIND (ptree_linfix nDtypeCons
                   tokens_BarT ptree_Dconstructor dtc_pt) (\
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
             [datatype_pt; pt] -> OPTION_IGNORE_BIND
               (OPTION_GUARD (tokcheck datatype_pt tokens_DatatypeT))
                 (
               ptree_linfix nDtypeDecls tokens_AndT
                 ptree_DtypeDecl pt) | _40 -> NONE else NONE))`;;

let ptree_TypeAbbrevDec_def = cake_define
  `(ptree_TypeAbbrevDec ptree:dec option) =
     (match ptree with
       Lf _41 -> NONE | Nd nt' args ->
       (if FST nt' = (INL:MMLnonT->MMLnonT+num) nTypeAbbrevDec then
         match args with
           [typetok; tynm; eqtok; typ_pt] -> OPTION_IGNORE_BIND
             (OPTION_GUARD (tokcheck typetok tokens_TypeT /\ tokcheck
               eqtok tokens_EqualsT)) (OPTION_BIND (ptree_TypeName tynm)
               (\
             (vars',nm). OPTION_BIND (ptree_Type nType typ_pt) (\
             typ.
             SOME (Dtabbrev (SND nt') vars' nm typ)))) | _42 ->
               NONE else NONE))`;;

let singleSymP_def = cake_define
  `singleSymP P x2 =
      match x2 with
        [pt] -> OPTION_BIND ((\f a. OPTION_BIND a f) destSymbolT ((\f
          a. OPTION_BIND a f) destTOK (destLf pt))) (\s.
          OPTION_IGNORE_BIND
                         (OPTION_GUARD (P s)) (
                         SOME (Short s)))
      | _43 -> NONE`;;

let ptree_Op_def = cake_define_list
  [`ptree_Op (Lf _44) = NONE`;
   `ptree_Op (Nd nt' subs) =
      (if FST nt' = (INL:MMLnonT->MMLnonT+num) nMultOps then
        if tokcheckl subs [tokens_StarT] then SOME (Short (implode
          "*")) else if tokcheckl subs [tokens_AlphaT (implode "mod")]
          then SOME (Short (implode "mod")) else if tokcheckl subs
          [tokens_AlphaT (implode "div")] then SOME (Short (implode
          "div")) else singleSymP (validMultSym o explode) subs else if
          FST nt' = (INL:MMLnonT->MMLnonT+num) nAddOps then singleSymP
          (validAddSym o explode) subs else if FST nt' =
          (INL:MMLnonT->MMLnonT+num) nListOps then singleSymP
          (validListSym o explode) subs else if FST nt' =
          (INL:MMLnonT->MMLnonT+num) nRelOps then
        singleSymP (validRelSym o explode) subs ++
        OPTION_IGNORE_BIND (OPTION_GUARD (tokcheckl subs
          [tokens_EqualsT])) (SOME (Short (implode "="))) else if FST
          nt' = (INL:MMLnonT->MMLnonT+num) nCompOps then
        if tokcheckl subs [tokens_SymbolT (implode ":=")] then
          SOME (Short (implode ":=")) else if tokcheckl subs
          [tokens_AlphaT (implode "o")] then SOME (Short (implode
          "o")) else NONE else NONE)`];;

let ptree_V_def = cake_define_list
  [`ptree_V (Lf _46) = NONE`;
   `ptree_V (Nd nt' subs) =
         OPTION_IGNORE_BIND
           (OPTION_GUARD (FST nt' = (INL:MMLnonT->MMLnonT+num) nV))
             (
           match subs with
              [pt] -> OPTION_BIND ((\f a. OPTION_BIND a f) destTOK
                (destLf pt)) (\t.
                         destAlphaT t ++ destSymbolT t) | _47
                           -> NONE)`];;

let ptree_FQV_def = cake_define_list
  [`ptree_FQV (Lf _49) = NONE`;
   `ptree_FQV (Nd nt' args) =
      (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nFQV) then NONE
        else
        match args with
            [pt] -> OPTION_MAP Short (ptree_V pt) ++
                    OPTION_BIND ((\f a. OPTION_BIND a f) destLongidT
                      ((\f a. OPTION_BIND a f) destTOK (destLf pt))) (\
                      (xs,s).
                      SOME (Long_Short xs s)) | _50 -> NONE)`];;

let isSymbolicConstructor_def = cake_define
  `isSymbolicConstructor s =
     SOME (s = "::")`;;

let isConstructor_def = cake_define
  `isConstructor s =
       ifM (isSymbolicConstructor s)
         (SOME T)
         (SOME (match oHD s with NONE -> F | SOME c -> isAlpha c
           /\ isUpper c))`;;

(* third clause below will lead to a failure when the environment is
   consulted to reveal that the long-id given does not correspond to a
   constructor.  We do this rather than fail to make the "totality" theorem
   work *)
let EtoPat_def = cake_define
  `EtoPat x1 =
        match x1 with
          (ast_Con x args:ast_exp) -> (if NULL args then SOME
            (ast_Pcon x []) else NONE)
        | (ast_Var (Short n)) -> SOME (ast_Pvar n)
        | (ast_Var (Long str n)) -> SOME (ast_Pcon (SOME (Long str
          n)) [])
        | _51 -> NONE`;;

let ptree_OpID_def = cake_define_list
  [`ptree_OpID (Lf _54) = NONE`;
   `ptree_OpID (Nd nt' subs) =
      (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nOpID) then NONE
        else
        match subs with
            [Lf
              ((grammar_TOK:tokens_token->(tokens_token
              ,MMLnonT)grammar_symbol) tk,_55)] ->
            OPTION_BIND (destAlphaT tk) (\
                s.
                ifM (isConstructor (explode s))
                    (SOME (ast_Con (SOME (Short s)) []))
                    (SOME (ast_Var (Short s)))) ++
            OPTION_BIND (destSymbolT tk) (\
                s.
                ifM (isSymbolicConstructor (explode s))
                    (SOME (ast_Con (SOME (Short s)) []))
                    (SOME (ast_Var (Short s)))) ++
            OPTION_BIND (destLongidT tk) (\
                (path',s).
                ifM (isConstructor (explode s))
                    (SOME (ast_Con (SOME (Long_Short path' s)) []))
                    (SOME (ast_Var (Long_Short path' s)))) ++
            (if tk = tokens_StarT then
               ifM (isSymbolicConstructor "*")
                   (SOME (ast_Con (SOME (Short (implode "*"))) []))
                   (SOME (ast_Var (Short (implode "*")))) else
                     if tk = tokens_EqualsT then SOME (ast_Var
                     (Short (implode "="))) else NONE) | _56 ->
                     NONE)`];;

let papply_def = cake_define
  `Papply pat arg =
     (match pat with
       ast_Pcon cn args -> ast_Pcon cn (args ++ [arg]) | _57 ->
         pat)`;;

let maybe_handleRef_def = cake_define
  `maybe_handleRef p =
      match p with
        (ast_Pcon (SOME (Short (implode "Ref"))) [pat]:ast_pat) ->
          ast_Pref pat
      | p -> p`;;

let ptree_Pattern_def = cake_define_list
  [`ptree_Pattern nt' (Lf _58) = NONE`;
   `ptree_Pattern nt' (Nd nm args) =
        (if ~((INL:MMLnonT->MMLnonT+num) nt' = FST nm) then NONE
          else if FST nm = (INL:MMLnonT->MMLnonT+num) nPbase then
          match args with
              [vic] ->
              ptree_Pattern nPtuple vic ++
              OPTION_BIND (ptree_ConstructorName vic) (\
                 cname.
                 SOME (ast_Pcon (SOME cname) [])) ++
              OPTION_BIND (ptree_V vic) (\vname. SOME (ast_Pvar
                vname)) ++
              OPTION_BIND (destLf vic) (\
                lf. OPTION_BIND (destTOK lf) (\
                t.
                (OPTION_BIND (destIntT t) (\i. SOME (ast_Plit
                  (ast_IntLit i))) ++
                 OPTION_BIND (destStringT t) (\s. SOME (ast_Plit
                   (ast_StrLit s))) ++
                 OPTION_BIND (destCharT t) (\c. SOME (ast_Plit
                   (ast_Char c)))))) ++
              OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck vic
                tokens_UnderbarT)) (SOME ast_Pany) | [lb; rb] ->
              (if tokcheckl args [tokens_LbrackT; tokens_RbrackT]
                then
                SOME (ast_Pcon (SOME (Short (implode "[]"))) [])
                  else if tokcheckl [lb] [tokens_OpT] then
                OPTION_BIND (ptree_OpID rb) (\e. EtoPat e) else
                  NONE) | [lb; plistpt; rb] ->
              OPTION_IGNORE_BIND
                (OPTION_GUARD (tokcheckl [lb; rb] [tokens_LbrackT;
                  tokens_RbrackT])) (OPTION_BIND (ptree_Plist plistpt)
                  (\
                plist.
                SOME (ITLIST (\p a. ast_Pcon (SOME (Short (implode
                  "::"))) [p; a])
                            plist
                            (ast_Pcon (SOME (Short (implode "[]")))
                              [])))) | _59 -> NONE else if FST nm =
                              (INL:MMLnonT->MMLnonT+num) nPConApp then
          match args with
            [cn] ->
            OPTION_BIND (ptree_ConstructorName cn) (\
              cname.
              SOME (ast_Pcon (SOME cname) [])) | [capp_pt; base_pt]
                ->
            OPTION_BIND (ptree_Pattern nPConApp capp_pt) (\
              capp. OPTION_BIND (ptree_Pattern nPbase base_pt) (\
              base.
              SOME (Papply capp base))) | _60 -> NONE else if FST nm
                = (INL:MMLnonT->MMLnonT+num) nPapp then
          match args with
              [pb] -> ptree_Pattern nPbase pb | [capp_pt; ppt] ->
              OPTION_BIND (ptree_Pattern nPConApp capp_pt) (\
                capp. OPTION_BIND (ptree_Pattern nPbase ppt) (\
                b.
                SOME (maybe_handleRef (Papply capp b)))) | _61 ->
                  NONE else if FST nm = (INL:MMLnonT->MMLnonT+num)
                  nPcons then
          match args with
              [papt] -> ptree_Pattern nPapp papt | [papt; cons_t;
                pcons_pt] ->
              OPTION_IGNORE_BIND
                (OPTION_GUARD (tokcheck cons_t (tokens_SymbolT
                  (implode "::")))) (OPTION_BIND (ptree_Pattern nPapp
                  papt) (\
                pa. OPTION_BIND (ptree_Pattern nPcons pcons_pt) (\
                patt.
                SOME (ast_Pcon (SOME (Short (implode "::"))) [pa;
                  patt])))) | _62 -> NONE else if FST nm =
                  (INL:MMLnonT->MMLnonT+num) nPas then
          match args with
              [papt] -> ptree_Pattern nPcons papt | [vt; as_t; papt]
                ->
              OPTION_IGNORE_BIND
                (OPTION_GUARD (tokcheck as_t tokens_AsT))
                  (OPTION_BIND (ptree_Pattern nPcons papt) (\
                pa. OPTION_BIND (ptree_V vt) (\
                vtt.
                SOME (ast_Pas pa vtt)))) | _63 -> NONE else if FST
                  nm = (INL:MMLnonT->MMLnonT+num) nPattern then
          match args with
              [pas] -> ptree_Pattern nPas pas | [pas_pt; colon_t;
                type_pt] ->
              OPTION_IGNORE_BIND
                (OPTION_GUARD (tokcheck colon_t tokens_ColonT))
                  (OPTION_BIND (ptree_Pattern nPas pas_pt) (\
                pc'. OPTION_BIND (ptree_Type nType type_pt) (\
                ty.
                SOME (ast_Ptannot pc' ty)))) | _64 -> NONE else if
                  FST nm = (INL:MMLnonT->MMLnonT+num) nPtuple then
          match args with
              [lp; rp] -> OPTION_IGNORE_BIND (OPTION_GUARD
                (tokcheckl [lp; rp] [tokens_LparT; tokens_RparT])) (
                             SOME (ast_Pcon NONE [])) | [lp; pl_pt;
                               rp] ->
              OPTION_IGNORE_BIND
                (OPTION_GUARD (tokcheckl [lp; rp] [tokens_LparT;
                  tokens_RparT])) (OPTION_BIND (ptree_Plist pl_pt) (\
                pl.
                match pl with
                    [] -> NONE | [p] -> SOME p | _65 -> SOME
                      (ast_Pcon NONE pl))) | _66 -> NONE else NONE)`;
   `ptree_Plist (Lf _67) = NONE`;
   `ptree_Plist (Nd nm args) =
         (if ~(FST nm = (INL:MMLnonT->MMLnonT+num) nPatternList)
           then NONE else
           match args with
               [p_pt] ->
               OPTION_BIND (ptree_Pattern nPattern p_pt) (\
                 p.
                 SOME [p]) | [p; ct; pl] ->
               OPTION_IGNORE_BIND
                 (OPTION_GUARD (tokcheck ct tokens_CommaT))
                   (OPTION_BIND (ptree_Pattern nPattern p) (\
                 hdpat. OPTION_BIND (ptree_Plist pl) (\
                 tlpats.
                 SOME (hdpat :: tlpats)))) | _68 -> NONE)`];;

new_type_abbrev("ptree",`: (tokens_token,MMLnonT,locs)parsetree`);;

(* HOL4 cmlPtreeConversionScript.sml:742-745: a theorem that HOL4
   states as the value of an ML expression: ptree_Pattern_pevaled *)

(* HOL4 cmlPtreeConversionScript.sml:747-748: a theorem that HOL4
   states as the value of an ML expression: ptree_Plist_thm *)

let ptree_PbaseList1_def = cake_define_list
  [`ptree_PbaseList1 (Lf _70) = NONE`;
   `ptree_PbaseList1 (Nd nm args) =
         (if ~(FST nm = (INL:MMLnonT->MMLnonT+num) nPbaseList1) then
           NONE else
           match args with
               [p_pt] -> OPTION_MAP SINGL (ptree_Pattern nPbase
                 p_pt) | [p_pt; pl_pt] ->
                   OPTION_MAP2 CONS
                         (ptree_Pattern nPbase p_pt)
                         (ptree_PbaseList1 pl_pt) | _71 ->
                           NONE)`];;

let eseq_encode_def = cake_define
  `Eseq_encode x1 =
        match x1 with
          [] -> NONE
        | [e] -> SOME e
        | (e :: es) ->
      OPTION_BIND (Eseq_encode es) (\
        body.
        SOME (ast_Let NONE e body))`;;

let dest_Conk_def = cake_define
  `dest_Conk x1 k v =
        match x1 with
          (ast_Con x y:ast_exp) -> k x y
        | _72 -> v`;;

let destFFIop_def = cake_define
  `destFFIop x1 =
        match x1 with
          (ast_FFI s:ast_op) -> SOME s
        | _73 -> NONE`;;

let strip_loc_expr_def = cake_define
  `strip_loc_expr e =
        match e with
          ast_Lannot e l ->
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
   `optLannot (SOME l) e = ast_Lannot e l`];;

let mkAst_App_def = cake_define
  `mkAst_App a1 a2 =
     (let (a10,loc1) = strip_loc_expr a1 in
       dest_Conk a10
         (\nm_opt args.
           if nm_opt = SOME (Short (implode "Ref")) /\ NULL args then
             ast_App ast_Opref [a2] else
             let (a2',loc2) = strip_loc_expr a2 in
               optLannot (merge_locsopt loc1 loc2) (ast_Con nm_opt
                 (args ++ [a2'])))
         (match a10 with
            ast_App opn args ->
              (match (destFFIop opn) with
                 NONE -> ast_App ast_Opapp [a1; a2] | SOME s ->
                   ast_App opn (args ++ [a2])) | _77 -> ast_App
                   ast_Opapp [a1; a2]))`;;

let dePat_def = cake_define
  `dePat p b =
        match p with
          (ast_Pvar v:ast_pat) -> (v,b)
        | p -> ((implode ""),ast_Mat (ast_Var (Short (implode
          ""))) [(p,b)])`;;

let mkFun_def = cake_define
  `mkFun p b = UNCURRY ast_Fun (dePat p b)`;;

let ptree_Eliteral_def = cake_define_list
  [`ptree_Eliteral (Lf _78) = NONE`;
   `ptree_Eliteral (Nd nt' subs) =
      OPTION_IGNORE_BIND
        (OPTION_GUARD (LENGTH subs = 1 /\ FST nt' =
          (INL:MMLnonT->MMLnonT+num) nEliteral)) (OPTION_BIND (destLf
          (HD subs)) (\
        lf. OPTION_BIND (destTOK lf) (\
        t.
        (OPTION_BIND (destIntT t) (\i. SOME (ast_Lit (ast_IntLit
          i))) ++
         OPTION_BIND (destCharT t) (\c. SOME (ast_Lit (ast_Char c)))
           ++
         OPTION_BIND (destStringT t) (\s. SOME (ast_Lit (ast_StrLit
           s))) ++
         OPTION_BIND (destWordT t) (\n. SOME (ast_Lit (ast_Word64
           (n2w n)))) ++
         OPTION_BIND (destFFIT t) (\s. SOME (ast_App (ast_FFI
           s) []))))))`];;

let bind_loc_def = cake_define
  `bind_loc e l' =
      match e with
        ast_Lannot e l -> ast_Lannot e l
      | e -> ast_Lannot e l'`;;

let letFromPat_def = cake_define
  `letFromPat p rhs body =
     (match p with
       ast_Pany -> ast_Let NONE rhs body | ast_Pvar v -> ast_Let
         (SOME v) rhs body | _79 -> ast_Mat rhs [(p,body)])`;;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let ptree_Expr_def = cake_define_list_cheat CHEAT_TAC
  [`ptree_Expr ent (Lf _80) = NONE`;
   `ptree_Expr ent (Nd (nt',loc) subs) =
    OPTION_BIND (if (INL:MMLnonT->MMLnonT+num) ent = nt' then
        if nt' = (INL:MMLnonT->MMLnonT+num) nEbase then
          match subs with
              [lpart; pt; rpart] ->
                (if tokcheck lpart tokens_LparT then
                  OPTION_IGNORE_BIND
                    (OPTION_GUARD (tokcheck rpart tokens_RparT))
                      (OPTION_BIND (ptree_Eseq pt) (\
                    eseq.
                    Eseq_encode eseq)) else
                  OPTION_IGNORE_BIND
                    (OPTION_GUARD (tokcheckl [lpart; rpart]
                      [tokens_LbrackT; tokens_RbrackT])) (OPTION_BIND
                      (ptree_Exprlist nElist1 pt) (\
                    elist.
                    SOME (ITLIST (\e acc. ast_Con (SOME (Short
                      (implode "::"))) [e; acc])
                           elist
                              (ast_Con (SOME (Short (implode "[]")))
                                []))))) | [single] ->
                ptree_Eliteral single ++
                OPTION_BIND (ptree_FQV single) (\
                  s.
                  SOME (ast_Var s)) ++
                OPTION_BIND (ptree_ConstructorName single) (\cname.
                   SOME (ast_Con (SOME cname) [])) ++
                ptree_Expr nEtuple single | [lp; rp] -> (if
                  tokcheckl [lp; rp] [tokens_LparT; tokens_RparT] then
                           SOME (ast_Con NONE []) else if tokcheckl
                             [lp; rp] [tokens_LbrackT; tokens_RbrackT]
                             then
                           SOME (ast_Con (SOME (Short (implode
                             "[]"))) []) else if tokcheck lp tokens_OpT
                             then
                           ptree_OpID rp else
                           NONE) | [lett; letdecs_pt; intok; ept;
                             endt] ->
              OPTION_IGNORE_BIND
                (OPTION_GUARD (tokcheckl [lett; intok; endt]
                  [tokens_LetT; tokens_InT; tokens_EndT])) (OPTION_BIND
                  (ptree_LetDecs letdecs_pt) (\
                letdecs. OPTION_BIND (ptree_Eseq ept) (\
                eseq. OPTION_BIND (Eseq_encode eseq) (\
                e.
                SOME (ITLIST (\df acc. match df with
                              INL (p,e0) -> letFromPat p e0 acc |
                                INR fds -> ast_Letrec fds acc)
                           letdecs
                           e))))) | _81 -> NONE else if nt' =
                             (INL:MMLnonT->MMLnonT+num) nEapp then
          match subs with
              [t1; t2] -> OPTION_BIND (ptree_Expr nEapp t1) (\
                            a1. OPTION_BIND (ptree_Expr nEbase t2)
                              (\
                            a2.
                            SOME (mkAst_App a1 a2))) | [t] ->
                              ptree_Expr nEbase t | _82 -> NONE else if
                              nt' = (INL:MMLnonT->MMLnonT+num) nEtuple
                              then
          match subs with
              [lpart; el2; rpart] ->
              OPTION_IGNORE_BIND
                (OPTION_GUARD (tokcheckl [lpart; rpart]
                  [tokens_LparT; tokens_RparT])) (OPTION_BIND
                  (ptree_Exprlist nElist2 el2) (\
                es.
                SOME (ast_Con NONE es))) | _83 -> NONE else if nt' =
                  (INL:MMLnonT->MMLnonT+num) nEmult then
          match subs with
            [t1; opt; t2] -> OPTION_BIND (ptree_Expr nEmult t1) (\
              a1. OPTION_BIND (ptree_Op opt) (\
              a_op. OPTION_BIND (ptree_Expr nEapp t2) (\
              a2.
              SOME (mk_binop a_op a1 a2)))) | [t] -> ptree_Expr
                nEapp t | _84 -> NONE else if nt' =
                (INL:MMLnonT->MMLnonT+num) nEadd then
          match subs with
              [t1; opt; t2] -> OPTION_BIND (ptree_Expr nEadd t1) (\
                a1. OPTION_BIND (ptree_Op opt) (\
                a_op. OPTION_BIND (ptree_Expr nEmult t2) (\
                a2.
                SOME (mk_binop a_op a1 a2)))) | [t] -> ptree_Expr
                  nEmult t | _85 -> NONE else if nt' =
                  (INL:MMLnonT->MMLnonT+num) nElistop then
          match subs with
              [t1; opt; t2] -> OPTION_BIND (ptree_Expr nEadd t1) (\
                a1. OPTION_BIND (ptree_Op opt) (\
                a_op. OPTION_BIND (ptree_Expr nElistop t2) (\
                a2.
                SOME (mk_binop a_op a1 a2)))) | [t] -> ptree_Expr
                  nEadd t | _86 -> NONE else if nt' =
                  (INL:MMLnonT->MMLnonT+num) nErel then
          match subs with
              [t1; opt; t2] -> OPTION_BIND (ptree_Expr nErel t1) (\
                a1. OPTION_BIND (ptree_Op opt) (\
                a_op. OPTION_BIND (ptree_Expr nElistop t2) (\
                a2.
                SOME (mk_binop a_op a1 a2)))) | [t] -> ptree_Expr
                  nElistop t | _87 -> NONE else if nt' =
                  (INL:MMLnonT->MMLnonT+num) nEcomp then
          match subs with
              [t1; opt; t2] -> OPTION_BIND (ptree_Expr nEcomp t1) (\
                a1. OPTION_BIND (ptree_Op opt) (\
                a_op. OPTION_BIND (ptree_Expr nErel t2) (\
                a2.
                SOME (mk_binop a_op a1 a2)))) | [t] -> ptree_Expr
                  nErel t | _88 -> NONE else if nt' =
                  (INL:MMLnonT->MMLnonT+num) nEbefore then
          match subs with
            [t1; opt; t2] -> OPTION_IGNORE_BIND
              (OPTION_GUARD (tokcheck opt (tokens_AlphaT (implode
                "before")))) (OPTION_BIND (ptree_Expr nEbefore t1) (\
              a1. OPTION_BIND (ptree_Expr nEcomp t2) (\
              a2.
              SOME (mk_binop (Short (implode "before")) a1 a2)))) |
                [t] -> ptree_Expr nEcomp t | _89 -> NONE else if nt' =
                (INL:MMLnonT->MMLnonT+num) nEtyped then
          match subs with
            [e_pt; colon; ty_pt] -> OPTION_IGNORE_BIND
              (OPTION_GUARD (tokcheck colon tokens_ColonT))
                (OPTION_BIND (ptree_Expr nEbefore e_pt) (\
              e. OPTION_BIND (ptree_Type nType ty_pt) (\
              ty.
              SOME (ast_Tannot e ty)))) | [t] -> ptree_Expr nEbefore
                t | _90 -> NONE else if nt' = (INL:MMLnonT->MMLnonT+num)
                nElogicAND then
          match subs with
              [t1; andt; t2] -> OPTION_IGNORE_BIND
                (OPTION_GUARD (tokcheck andt tokens_AndalsoT))
                  (OPTION_BIND (ptree_Expr nElogicAND t1) (\
                a1. OPTION_BIND (ptree_Expr nEtyped t2) (\
                a2.
                SOME (ast_Log Andalso a1 a2)))) | [t] -> ptree_Expr
                  nEtyped t | _91 -> NONE else if nt' =
                  (INL:MMLnonT->MMLnonT+num) nElogicOR then
          match subs with
              [t1; ort; t2] -> OPTION_IGNORE_BIND
                (OPTION_GUARD (tokcheck ort tokens_OrelseT))
                  (OPTION_BIND (ptree_Expr nElogicOR t1) (\
                a1. OPTION_BIND (ptree_Expr nElogicAND t2) (\
                a2.
                SOME (ast_Log Orelse a1 a2)))) | [t] -> ptree_Expr
                  nElogicAND t | _92 -> NONE else if nt' =
                  (INL:MMLnonT->MMLnonT+num) nEhandle then
          match subs with
              [pt] -> ptree_Expr nElogicOR pt | [e1pt; handlet; ent]
                ->
              OPTION_IGNORE_BIND
                (OPTION_GUARD (tokcheck handlet tokens_HandleT))
                  (OPTION_BIND (ptree_Expr nElogicOR e1pt) (\
                e. OPTION_BIND (ptree_PEs ent) (\
                pes.
                SOME (ast_Handle e pes)))) | _93 -> NONE else if nt'
                  = (INL:MMLnonT->MMLnonT+num) nE then
          match subs with [t] -> ptree_Expr nEhandle t | [raiset;
            ept] ->
              OPTION_IGNORE_BIND
                (OPTION_GUARD (tokcheck raiset tokens_RaiseT))
                  (OPTION_BIND (ptree_Expr nE ept) (\
                e.
                SOME (ast_Raise e))) | [fnt; pnt'; arrowt; ent] ->
              OPTION_IGNORE_BIND
                (OPTION_GUARD (tokcheckl [fnt; arrowt] [tokens_FnT;
                  tokens_DarrowT])) (OPTION_BIND (ptree_Pattern nPattern
                  pnt') (\
                p. OPTION_BIND (ptree_Expr nE ent) (\
                e.
                SOME (mkFun p e)))) ++ OPTION_IGNORE_BIND
                (OPTION_GUARD (tokcheckl [fnt; arrowt]
                  [tokens_CaseT; tokens_OfT])) (OPTION_BIND (ptree_Expr
                  nE pnt') (\
                e. OPTION_BIND (ptree_PEs ent) (\
                pes.
                SOME (ast_Mat e pes)))) | [ift; g; thent; te; elset;
                  ee] -> OPTION_IGNORE_BIND
                (OPTION_GUARD (tokcheckl [ift; thent; elset]
                  [tokens_IfT; tokens_ThenT; tokens_ElseT]))
                  (OPTION_BIND (ptree_Expr nE g) (\
                a1. OPTION_BIND (ptree_Expr nE te) (\
                a2. OPTION_BIND (ptree_Expr nE ee) (\
                a3.
                SOME (ast_If a1 a2 a3))))) | _94 -> NONE else NONE
                  else NONE) (\
    e.
      SOME (bind_loc e loc))`;
   `ptree_Exprlist nm ast =
         (match ast with
             Lf _95 -> NONE | Nd (nt',_96) subs ->
             (if nt' = (INL:MMLnonT->MMLnonT+num) nElist1 then
               match subs with
                   [sing] -> OPTION_BIND (ptree_Expr nE sing) (\e.
                     SOME [e]) | [e; ct; el1] ->
                   OPTION_IGNORE_BIND
                     (OPTION_GUARD (tokcheck ct tokens_CommaT))
                       (OPTION_BIND (ptree_Expr nE e) (\
                     front. OPTION_BIND (ptree_Exprlist nElist1 el1)
                       (\
                     back.
                     SOME (front :: back)))) | _97 -> NONE else if
                       nt' = (INL:MMLnonT->MMLnonT+num) nElist2 then
               match subs with
                   [e; ct; el1] ->
                   OPTION_IGNORE_BIND
                     (OPTION_GUARD (tokcheck ct tokens_CommaT))
                       (OPTION_BIND (ptree_Expr nE e) (\
                     front. OPTION_BIND (ptree_Exprlist nElist1 el1)
                       (\
                     back.
                     SOME (front :: back)))) | _98 -> NONE else
                       NONE))`;
   `ptree_AndFDecls ast =
      (match ast with
          Lf _99 -> NONE | Nd (nt',_100) subs ->
          (if nt' = (INL:MMLnonT->MMLnonT+num) nAndFDecls then
            match subs with
                [single] -> OPTION_BIND (ptree_FDecl single) (\fdec.
                  SOME ([fdec])) | [fdecspt; andt; fdecpt] ->
                OPTION_IGNORE_BIND
                  (OPTION_GUARD (tokcheck andt tokens_AndT))
                    (OPTION_BIND (ptree_AndFDecls fdecspt) (\
                  fdecs. OPTION_BIND (ptree_FDecl fdecpt) (\
                  fdec.
                  SOME (fdecs ++ [fdec])))) | _101 -> NONE else
                    NONE))`;
   `ptree_FDecl ast =
        (match ast with
            Lf _102 -> NONE | Nd (nt',_103) subs ->
            (if nt' = (INL:MMLnonT->MMLnonT+num) nFDecl then
              match subs with
                  [fname_pt; pats_pt; eqt; body_pt] ->
                  OPTION_IGNORE_BIND
                    (OPTION_GUARD (tokcheck eqt tokens_EqualsT))
                      (OPTION_BIND (ptree_V fname_pt) (\
                    fname. OPTION_BIND (ptree_PbaseList1 pats_pt) (\
                    ps. OPTION_BIND (oHD ps) (\
                    p1. OPTION_BIND (ptree_Expr nE body_pt) (\
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
                  (if tokcheck ld_pt tokens_SemicolonT then
                    ptree_LetDecs lds_pt else
                    OPTION_BIND (ptree_LetDec ld_pt) (\
                      ld. OPTION_BIND (ptree_LetDecs lds_pt) (\
                      lds.
                      SOME (ld :: lds)))) | _107 -> NONE))`;
   `ptree_LetDec ptree =
        (match ptree with
            Lf _108 -> NONE | Nd (nt',_109) args ->
            (if ~(nt' = (INL:MMLnonT->MMLnonT+num) nLetDec) then
              NONE else
              match args with
                  [funtok; andfdecls_pt] ->
                  OPTION_IGNORE_BIND
                    (OPTION_GUARD (tokcheck funtok tokens_FunT))
                      (OPTION_BIND (ptree_AndFDecls andfdecls_pt) (\
                    fds.
                    SOME (INR fds))) | [valtok; p_pt; eqtok; e_pt]
                      ->
                  OPTION_IGNORE_BIND
                    (OPTION_GUARD (tokcheckl [valtok; eqtok]
                      [tokens_ValT; tokens_EqualsT])) (OPTION_BIND
                      (ptree_Pattern nPattern p_pt) (\
                    p. OPTION_BIND (ptree_Expr nE e_pt) (\
                    e.
                    SOME (INL (p,e))))) | _110 -> NONE))`;
   `ptree_PEs (Lf _111) = (NONE:((ast_pat#ast_exp) list) option)`;
   `ptree_PEs (Nd (nt',_112) args) =
        ((if ~(nt' = (INL:MMLnonT->MMLnonT+num) nPEs) then NONE else
          match args with
              [pattern_pt; arrow_pt; pe_pt] ->
              OPTION_IGNORE_BIND
                (OPTION_GUARD (tokcheck arrow_pt tokens_DarrowT))
                  (OPTION_BIND (ptree_Pattern nPattern pattern_pt) (\
                pat. OPTION_BIND (ptree_PE pe_pt) (\
                (e,pes).
                SOME ((pat,e) :: pes)))) | _113 ->
                  NONE):((ast_pat#ast_exp) list) option)`;
   `ptree_PE (Lf _114) = NONE`;
   `ptree_PE (Nd (nt',_115) args) =
         (if ~(nt' = (INL:MMLnonT->MMLnonT+num) nPE) then NONE else
           match args with
               [eorraise_pt; pesfx_pt] ->
               OPTION_IGNORE_BIND
                 (OPTION_GUARD (tokcheck eorraise_pt tokens_RaiseT))
                   (OPTION_BIND (ptree_PE pesfx_pt) (\
                 (e,pes).
                 SOME (ast_Raise e,pes))) ++
               OPTION_BIND (ptree_Expr nElogicOR eorraise_pt) (\
                 e. OPTION_BIND (ptree_PEsfx pesfx_pt) (\
                 (handlep,pes).
                 SOME (if handlep then (ast_Handle e pes,[]) else
                   (e,pes)))) | [fncase_tok; epat_pt; arrowof_tok;
                   last_pt] ->
               OPTION_IGNORE_BIND
                 (OPTION_GUARD (tokcheckl [fncase_tok; arrowof_tok]
                   [tokens_FnT; tokens_DarrowT])) (OPTION_BIND
                   (ptree_Pattern nPattern epat_pt) (\
                 pat. OPTION_BIND (ptree_Expr nE last_pt) (\
                 e.
                 SOME (mkFun pat e,[])))) ++
               OPTION_IGNORE_BIND
                 (OPTION_GUARD (tokcheckl [fncase_tok; arrowof_tok]
                   [tokens_CaseT; tokens_OfT])) (OPTION_BIND (ptree_Expr
                   nE epat_pt) (\
                 e. OPTION_BIND (ptree_PEs last_pt) (\
                 pes.
                 SOME (ast_Mat e pes,[])))) | [iftok; ge_pt;
                   thentok; then_pt; elsetok; else_pt] ->
               OPTION_IGNORE_BIND
                 (OPTION_GUARD (tokcheckl [iftok; thentok; elsetok]
                   [tokens_IfT; tokens_ThenT; tokens_ElseT]))
                   (OPTION_BIND (ptree_Expr nE ge_pt) (\
                 ge. OPTION_BIND (ptree_Expr nE then_pt) (\
                 te. OPTION_BIND (ptree_PE else_pt) (\
                 (ee,rest).
                 SOME (ast_If ge te ee,rest))))) | _116 -> NONE)`;
   `(ptree_PEsfx (Lf _117):(bool#(ast_pat#ast_exp) list) option) =
  NONE`;
   `ptree_PEsfx (Nd (nt',_118) args) =
         (if ~(nt' = (INL:MMLnonT->MMLnonT+num) nPEsfx) then NONE
           else
           match args with
               [] -> SOME (F,[]) | [handlebar_tok; pes_pt] ->
               OPTION_IGNORE_BIND
                 (OPTION_GUARD (tokcheck handlebar_tok
                   tokens_HandleT)) (OPTION_BIND (ptree_PEs pes_pt) (\
                 pes.
                 SOME (T,pes))) ++
               OPTION_IGNORE_BIND
                 (OPTION_GUARD (tokcheck handlebar_tok tokens_BarT))
                   (OPTION_BIND (ptree_PEs pes_pt) (\
                 pes.
                 SOME (F,pes))) | _119 -> NONE)`;
   `ptree_Eseq (Lf _120) = NONE`;
   `ptree_Eseq (Nd (nt',_121) args) =
        (if ~(nt' = (INL:MMLnonT->MMLnonT+num) nEseq) then NONE else
          match args with
              [single] ->
              OPTION_BIND (ptree_Expr nE single) (\
                e.
                SOME [e]) | [e_pt; semi; seq_pt] ->
              OPTION_IGNORE_BIND
                (OPTION_GUARD (tokcheck semi tokens_SemicolonT))
                  (OPTION_BIND (ptree_Expr nE e_pt) (\
                e. OPTION_BIND (ptree_Eseq seq_pt) (\
                seq'.
                SOME (e :: seq')))) | _122 -> NONE)`];;

let dumb1 = cake_theorem "dumb1[local]"
  (fun () ->
    `COND (p = q) t e = COND (q = p) t e`)
  CHEAT_TAC;;
let dumb2 = cake_theorem "dumb2[local]"
  (fun () ->
    `COND gd t NONE = OPTION_IGNORE_BIND (OPTION_GUARD gd) t`)
  CHEAT_TAC;;
(* HOL4 cmlPtreeConversionScript.sml:1259-1262: a theorem that HOL4
   states as the value of an ML expression: ptree_Expr_def' *)

(* HOL4 cmlPtreeConversionScript.sml:1264-1271: a theorem that HOL4
   states as the value of an ML expression: ptree_Expr_pevaled *)

(* HOL4 cmlPtreeConversionScript.sml:1273-1274: a theorem that HOL4
   states as the value of an ML expression: ptree_Expr_others *)

let ptree_StructName_def = cake_define_list
  [`ptree_StructName (Lf _124) = NONE`;
   `ptree_StructName (Nd nm args) =
      (if ~(FST nm = (INL:MMLnonT->MMLnonT+num) nStructName) then
        NONE else
        match args with
            [pt] -> (\f a. OPTION_BIND a f) destAlphaT ((\f a.
              OPTION_BIND a f) destTOK (destLf pt)) | _125 -> NONE)`];;

let ptree_OptTypEqn_def = cake_define_list
  [`ptree_OptTypEqn (Lf _127) = (NONE:(ast_t option) option)`;
   `ptree_OptTypEqn (Nd nt' args) =
      ((if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nOptTypEqn) then
        NONE else
        match args with
            [] -> SOME NONE | [eqtok; typ_pt] ->
            OPTION_IGNORE_BIND
              (OPTION_GUARD (tokcheck eqtok tokens_EqualsT))
                (OPTION_BIND (ptree_Type nType typ_pt) (\
              typ.
              SOME (SOME typ))) | _128 -> NONE):(ast_t option)
                option)`];;

let ptree_SpecLine_def = cake_define_list
  [`ptree_SpecLine (Lf _130) = NONE`;
   `ptree_SpecLine (Nd nt' args) =
      (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nSpecLine) then
        NONE else
        match args with
            [td_pt] ->
            OPTION_BIND (ptree_TypeDec td_pt) (\
              td.
              SOME one) | [exntok; dcon_pt] ->
            OPTION_IGNORE_BIND
              (OPTION_GUARD (tokcheck exntok tokens_ExceptionT))
                (OPTION_BIND (ptree_Dconstructor dcon_pt) (\
              (nm,tys).
              SOME one)) | [typetok; tynm_pt; opteqn_pt] ->
            OPTION_IGNORE_BIND
              (OPTION_GUARD (tokcheck typetok tokens_TypeT))
                (OPTION_BIND (ptree_TypeName tynm_pt) (\
              (vs,nm). OPTION_BIND (ptree_OptTypEqn opteqn_pt) (\
              opteqn.
              SOME one))) | [valtok; vname_pt; coltok; type_pt] ->
            OPTION_IGNORE_BIND
              (OPTION_GUARD (tokcheckl [valtok; coltok]
                [tokens_ValT; tokens_ColonT])) (OPTION_BIND (ptree_V
                vname_pt) (\
              vname. OPTION_BIND (ptree_Type nType type_pt) (\
              ty.
              SOME one))) | _131 -> NONE)`];;

let ptree_SpeclineList_def = cake_define_list
  [`ptree_SpeclineList (Lf _133) = NONE`;
   `ptree_SpeclineList (Nd nt' args) =
      (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nSpecLineList) then
        NONE else
        match args with
            [] -> SOME one | [sl_pt; sll_pt] ->
            (if tokcheck sl_pt tokens_SemicolonT then
              ptree_SpeclineList sll_pt else
              OPTION_BIND (ptree_SpecLine sl_pt) (\
                sl. OPTION_BIND (ptree_SpeclineList sll_pt) (\
                sll.
                SOME one))) | _134 -> NONE)`];;

let ptree_SignatureValue_def = cake_define_list
  [`ptree_SignatureValue (Lf _136) = NONE`;
   `ptree_SignatureValue (Nd nt' args) =
      (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nSignatureValue)
        then NONE else
        match args with
            [sigtok; sll_pt; endtok] ->
            OPTION_IGNORE_BIND
              (OPTION_GUARD (tokcheckl [sigtok; endtok]
                [tokens_SigT; tokens_EndT])) (
              ptree_SpeclineList sll_pt) | _137 -> NONE)`];;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let ptree_Decl_def = cake_define_list_cheat CHEAT_TAC
  [`(ptree_Decl pt:dec option) =
        (match pt with
           Lf _138 -> NONE | Nd (nt',locs) args ->
           (if ~(nt' = (INL:MMLnonT->MMLnonT+num) nDecl) then NONE
             else
             match args with
                 [dt] ->
                 OPTION_BIND (ptree_TypeDec dt) (\
                   tydec.
                   SOME (Dtype (locs) tydec)) ++ ptree_TypeAbbrevDec
                     dt ++ ptree_Structure dt | [funtok; fdecls] ->
                 OPTION_IGNORE_BIND
                   (OPTION_GUARD (tokcheck funtok tokens_FunT))
                     (OPTION_BIND (ptree_AndFDecls fdecls) (\
                   fdecs.
                   SOME (Dletrec (locs) fdecs))) ++
                 OPTION_IGNORE_BIND
                   (OPTION_GUARD (tokcheck funtok
                     tokens_ExceptionT)) (OPTION_BIND
                     (ptree_Dconstructor fdecls) (\
                   (enm,etys).
                   SOME (Dexn (locs) enm etys))) | [valtok; patpt;
                     eqtok; ept] ->
                 OPTION_IGNORE_BIND
                   (OPTION_GUARD (tokcheckl [valtok; eqtok]
                     [tokens_ValT; tokens_EqualsT])) (OPTION_BIND
                     (ptree_Pattern nPattern patpt) (\
                   pat. OPTION_BIND (ptree_Expr nE ept) (\
                   e.
                   SOME (Dlet (locs) pat e)))) | [localtok;
                     decls1_pt; intok; decls2_pt; endtok] ->
                 OPTION_IGNORE_BIND
                   (OPTION_GUARD (tokcheckl [localtok; intok;
                     endtok] [tokens_LocalT; tokens_InT; tokens_EndT]))
                     (OPTION_BIND (ptree_Decls decls1_pt) (\
                   decls1. OPTION_BIND (ptree_Decls decls2_pt) (\
                   decls2.
                   SOME (Dlocal decls1 decls2)))) | _139 ->
                     NONE))`;
   `ptree_Decls (Lf _140) = NONE`;
   `ptree_Decls (Nd (nt',_141) args) =
        (if ~(nt' = (INL:MMLnonT->MMLnonT+num) nDecls) then NONE
          else
          match args with
              [] -> SOME [] | [d_pt; ds_pt] ->
              (if tokcheck d_pt tokens_SemicolonT then ptree_Decls
                ds_pt else
                OPTION_BIND (ptree_Decl d_pt) (\
                  d. OPTION_BIND (ptree_Decls ds_pt) (\
                  ds.
                  SOME (d :: ds)))) | _142 -> NONE)`;
   `ptree_Structure (Lf _143) = NONE`;
   `ptree_Structure (Nd nt' args) =
      (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nStructure) then
        NONE else
        match args with
            [structuretok; sname_pt; asc_opt; eqtok; structtok;
              ds_pt; endtok] ->
            OPTION_IGNORE_BIND
              (OPTION_GUARD (tokcheckl [structtok; structuretok;
                eqtok; endtok]
                              [tokens_StructT; tokens_StructureT;
                                tokens_EqualsT; tokens_EndT]))
                                (OPTION_BIND (ptree_StructName sname_pt)
                                (\
              sname. OPTION_BIND (match asc_opt with
                         Lf _144 -> NONE | Nd nt' args ->
                           (if ~(FST nt' =
                             (INL:MMLnonT->MMLnonT+num)
                             nOptionalSignatureAscription) then
                             NONE else
                             match args with
                              [] -> SOME NONE | [sealtok; sig_pt] ->
                              OPTION_IGNORE_BIND
                              (OPTION_GUARD (tokcheck sealtok
                                tokens_SealT)) (OPTION_BIND
                                (ptree_SignatureValue sig_pt) (\
                              sigv.
                              SOME (SOME sigv))) | _145 -> NONE)) (\
              asc. OPTION_BIND (ptree_Decls ds_pt) (\
              ds.
              SOME (Dmod sname ds))))) | _146 -> NONE)`];;

let ptree_TopLevelDecs_def = cake_define_list
  [`ptree_TopLevelDecs (Lf _147) = NONE`;
   `ptree_TopLevelDecs (Nd nt' args) =
         (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num) nTopLevelDecs)
           then NONE else
           match args with
               [] -> SOME [] | [td_pt; tds_pt] ->
               (if tokcheck td_pt tokens_SemicolonT then
                 ptree_TopLevelDecs tds_pt else
                 OPTION_BIND (ptree_Decl td_pt) (\
                   td. OPTION_BIND (ptree_NonETopLevelDecs tds_pt)
                     (\
                   tds.
                   SOME (td :: tds)))) | [e_pt; semitok; tds_pt] ->
               OPTION_IGNORE_BIND
                 (OPTION_GUARD (tokcheck semitok tokens_SemicolonT))
                   (OPTION_BIND (ptree_Expr nE e_pt) (\
                 e. OPTION_BIND (ptree_TopLevelDecs tds_pt) (\
                 tds.
                 SOME (Dlet (SND nt') (ast_Pvar (implode "it")) e
                   :: tds)))) | _148 -> NONE)`;
   `ptree_NonETopLevelDecs (Lf _149) = NONE`;
   `ptree_NonETopLevelDecs (Nd nt' args) =
         (if ~(FST nt' = (INL:MMLnonT->MMLnonT+num)
           nNonETopLevelDecs) then NONE else
           match args with
             [] -> SOME [] | [pt1; pt2] ->
             (if tokcheck pt1 tokens_SemicolonT then
               ptree_TopLevelDecs pt2 else
               OPTION_BIND (ptree_Decl pt1) (\
                 td. OPTION_BIND (ptree_NonETopLevelDecs pt2) (\
                 tds.
                 SOME (td :: tds)))) | _150 -> NONE)`];;

hol4_only "++" "APPEND";;
