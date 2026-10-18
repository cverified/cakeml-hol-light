(* ======================================================== *)
(*  pegComplete: ported from HOL4's
    compiler/parsing/proofs/pegCompleteScript.sml
    A proof theory, with 9 definitions and 81 theorems.  Needed by
    compilerProof.ml.  *)
(* ======================================================== *)

(*
  Completeness proof for the parser. If a successful parse exists,
  then the parser will find one.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/parsing/cmlPEG.ml";;
needs "compiler/parsing/proofs/cmlNTProps.ml";;
needs "compiler/parsing/proofs/pegSound.ml";;
needs "lib/NTproperties.ml";;
needs "lib/grammar.ml";;
needs "lib/location.ml";;
needs "lib/peg.ml";;
needs "semantics/gram.ml";;
needs "semantics/proofs/gramProps.ml";;

(* Set up ML bindings *)
(* HOL4 pegCompleteScript.sml:13-14: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:18-19: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:21: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:23-25: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:38: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:40-45: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:47-59: ML code, not ported *)


(* HOL4 pegCompleteScript.sml:62-90: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:163-166: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:168-169: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:171-173: the ML values that the
   definitions below antiquote *)

(* HOL4 pegCompleteScript.sml:201-203: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:263-265: ML code, not ported *)

let sym2peg_def = cake_define_list
  [`sym2peg (grammar_TOK tk) = cmlPEG_tokeq tk`;
   `sym2peg (grammar_NT N) = peg_nt N I`];;

(* only the subs = [x] and subs = [x;y] cases are relevant *)
let left_insert1_def = cake_define_list
  [`left_insert1 pt (Lf (tk,l)) = Lf (tk,merge_locs (ptree_loc pt) l)`;
   `left_insert1 pt (Nd (n,l0) subs) =
         (match subs with
             [] -> Nd (n,merge_locs (ptree_loc pt) l0) [pt] |
               [x] -> mkNd n [mkNd n [pt]; x] | x :: xs -> mkNd n
               (left_insert1 pt x :: xs))`];;

(* HOL4 pegCompleteScript.sml:341: ML code, not ported *)

let leftLoc_def = cake_define
  `leftLoc (Locs l1 _1) = l1`;;
let rightLoc_def = cake_define
  `rightLoc (Locs _2 l2) = l2`;;

(* two valid parse-trees with the same head, and the same fringes, which
   are all tokens, must be identical. *)

(* HOL4 pegCompleteScript.sml:395-414: code that the source has in a
   comment *)

let leftmost_def = cake_define_list
  [`leftmost (Lf s) = Lf s`;
   `leftmost (Nd (n,l) args) =
      (if ~(args = []) /\ n = (INL:MMLnonT->MMLnonT+num) nTbase then
        HD args else
        match args with
            [] -> Nd (n,l) args | h :: _4 -> leftmost h)`];;

(* pt is a Tbase, and n will be DType all the way down *)
let left_insert2_def = cake_define_list
  [`left_insert2 pt (Lf (tk,l)) = Lf (tk,merge_locs (ptree_loc pt) l)`;
   `left_insert2 pt (Nd (n,l0) subs) =
         (match subs with
             [] -> Nd (n,merge_locs (ptree_loc pt) l0) [pt] |
               [Nd _6 [tyop]] -> mkNd n [mkNd n [pt]; tyop] | x ::
               ys -> mkNd n (left_insert2 pt x :: ys))`];;

(* the situation with DType is similar to that with Eapp and Ebase.

   The grammar rules are

      DType ::= DType TyOp | Tbase

   and the PEG handles this by grabbing a TBase, and then a sequence
   of TyOps (think something like "num list option").

   The reassociated theorem to come states that if we have a good
   DType (num list) followed by a TyOp (option), then it's possible to
   recast this as a Tbase (num) followed by a DType (list option).
   This latter is bogus as an SML type, but is fine syntax because
   "list" is both a valid TyOp and thus a Tbase as well. The
   left_insert2 function does the work to turn something like

    DType -+- DType -- TBase -- TyOp -- "list"
           |
           `- TyOp  -- "option"

   into

    DType -+- DType --- DType --- TBase -- TyOp -- "num"
           |         |
           |         `- TyOp  -- "list"
           |
           `- TyOp -- "option"
*)

(*
  The next reassociation scenario is the general story of a left-associative
  binary operator, such that the rule is of the form

    P ::= P SEP C | C

  Imagine you have a valid P-tree to the right, and a single C to the left.
  You can insert that C-tree into the valid P-tree in the leftmost position,
  generating a new, valid P-tree.
*)


let left_insert_def = cake_define_list
  [`left_insert (Lf (tk,l)) p sep c = Lf (tk,merge_locs (ptree_loc c)
  l)`;
   `left_insert (Nd (n,l) subs) p sep c =
         (if ~(n = p) then Nd (n,merge_locs (ptree_loc c) l) subs
           else
           match subs with
               [c0] -> mkNd p [mkNd p [c]; sep; c0] | [p'; s';
                 c'] -> mkNd p [left_insert p' p sep c; s'; c'] |
                 _8 -> Nd (n,merge_locs (ptree_loc c) l) subs)`];;

(* HOL4 pegCompleteScript.sml:697: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:734-737: ML code, not ported *)

let nestoppers_def = cake_define
  `nestoppers =
      UNIV DIFF
        ({tokens_AndalsoT,tokens_ArrowT,tokens_BarT,tokens_ColonT
        ,tokens_HandleT,tokens_OrelseT,
                  tokens_AlphaT (implode "before")} UNION
                 firstSet cmlG [(\nt'. grammar_NT
                   ((INL:MMLnonT->MMLnonT+num) nt')) nMultOps] UNION
                 firstSet cmlG [(\nt'. grammar_NT
                   ((INL:MMLnonT->MMLnonT+num) nt')) nRelOps] UNION
                 firstSet cmlG [(\nt'. grammar_NT
                   ((INL:MMLnonT->MMLnonT+num) nt')) nListOps] UNION
                 firstSet cmlG [(\nt'. grammar_NT
                   ((INL:MMLnonT->MMLnonT+num) nt')) nAddOps] UNION
                 firstSet cmlG [(\nt'. grammar_NT
                   ((INL:MMLnonT->MMLnonT+num) nt')) nCompOps] UNION
                 firstSet cmlG [(\nt'. grammar_NT
                   ((INL:MMLnonT->MMLnonT+num) nt')) nEbase] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                   ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp])`;;

let stoppers_def = cake_define
  `pegComplete_stoppers x1 =
        match x1 with
          nAndFDecls -> nestoppers DELETE tokens_AndT
        | nDconstructor ->
        UNIV DIFF
          ({tokens_StarT,tokens_OfT,tokens_ArrowT,tokens_LparT} UNION
          firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
          nt')) nTyOp] UNION
                   {tokens_TyvarT s | T})
        | nDecl ->
        nestoppers DIFF
          ({tokens_BarT,tokens_StarT,tokens_AndT,tokens_OfT} UNION
          {tokens_TyvarT s | T})
        | nDecls ->
        nestoppers DIFF
        ({tokens_BarT,tokens_StarT,tokens_AndT,tokens_SemicolonT
          ,tokens_FunT,tokens_ValT,tokens_DatatypeT,tokens_OfT
          ,tokens_ExceptionT,
          tokens_TypeT,tokens_LocalT,tokens_StructureT} UNION
            {tokens_TyvarT s | T})
        | nDType -> UNIV DIFF firstSet cmlG [(\nt'. grammar_NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp]
        | nDtypeCons ->
        UNIV DIFF
          ({tokens_ArrowT,tokens_BarT,tokens_StarT,tokens_OfT
          ,tokens_LparT} UNION firstSet cmlG [(\nt'. grammar_NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp] UNION
                   {tokens_TyvarT s | T})
        | nDtypeDecl ->
        UNIV DIFF
          ({tokens_ArrowT,tokens_BarT,tokens_StarT,tokens_OfT
          ,tokens_LparT} UNION firstSet cmlG [(\nt'. grammar_NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp] UNION
                   {tokens_TyvarT s | T})
        | nDtypeDecls ->
        UNIV DIFF
          ({tokens_AndT,tokens_ArrowT,tokens_BarT,tokens_StarT
          ,tokens_OfT,tokens_LparT} UNION {tokens_TyvarT s | T} UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp])
        | nE -> nestoppers
        | nEadd ->
        UNIV DIFF (firstSet cmlG [(\nt'. grammar_NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nMultOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nAddOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nEbase])
        | nEapp -> UNIV DIFF firstSet cmlG [(\nt'. grammar_NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nEbase]
        | nEbefore ->
        UNIV DIFF ({tokens_AlphaT (implode "before")} UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nCompOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nRelOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nListOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nMultOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nAddOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nEbase])
        | nEcomp ->
        UNIV DIFF (firstSet cmlG [(\nt'. grammar_NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nCompOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nRelOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nListOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nMultOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nAddOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nEbase])
        | nEhandle -> nestoppers
        | nElist1 -> nestoppers DELETE tokens_CommaT
        | nElist2 -> nestoppers DELETE tokens_CommaT
        | nElistop -> UNIV DIFF (firstSet cmlG [(\nt'. grammar_NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nMultOps] UNION
                              firstSet cmlG [(\nt'. grammar_NT
                                ((INL:MMLnonT->MMLnonT+num) nt'))
                                nAddOps] UNION
                              firstSet cmlG [(\nt'. grammar_NT
                                ((INL:MMLnonT->MMLnonT+num) nt'))
                                nListOps] UNION
                              firstSet cmlG [(\nt'. grammar_NT
                                ((INL:MMLnonT->MMLnonT+num) nt'))
                                nEbase])
        | nElogicAND ->
        UNIV DIFF
          ({tokens_AndalsoT,tokens_ColonT,tokens_ArrowT,tokens_AlphaT
          (implode "before")} UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nCompOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nRelOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nListOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nMultOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nAddOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nEbase] UNION
                     firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp])
        | nElogicOR ->
        UNIV DIFF
          ({tokens_AndalsoT,tokens_ColonT,tokens_ArrowT,tokens_OrelseT
          ,tokens_AlphaT (implode "before")} UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nCompOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nRelOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nListOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nMultOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nAddOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nEbase] UNION
                     firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp])
        | nEmult ->
        UNIV DIFF (firstSet cmlG [(\nt'. grammar_NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nEbase] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nMultOps])
        | nErel ->
        UNIV DIFF (firstSet cmlG [(\nt'. grammar_NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nRelOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nListOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nMultOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nAddOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nEbase])
        | nEseq -> nestoppers DELETE tokens_SemicolonT
        | nEtyped ->
        UNIV DIFF ({tokens_ColonT,tokens_ArrowT,tokens_AlphaT
          (implode "before")} UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nCompOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nListOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nRelOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nMultOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nAddOps] UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nEbase] UNION
                     firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp])
        | nFDecl -> nestoppers
        | nLetDec -> nestoppers DELETE tokens_AndT
        | nLetDecs -> nestoppers DIFF
          {tokens_AndT,tokens_FunT,tokens_ValT,tokens_SemicolonT}
        | nNonETopLevelDecs -> {}
        | nOptTypEqn ->
        UNIV DIFF ({tokens_ArrowT,tokens_StarT,tokens_EqualsT} UNION
          firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
          nt')) nTyOp])
        | nPcons ->
        UNIV DIFF
          ({tokens_LparT,tokens_UnderbarT,tokens_LbrackT,tokens_SymbolT
          (implode "::"),tokens_OpT} UNION
                   {tokens_IntT i | T} UNION {tokens_StringT s | T}
                     UNION {tokens_CharT c | T} UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nV] UNION
                     firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt'))
                     nConstructorName])
        | nPas ->
        UNIV DIFF
          ({tokens_LparT,tokens_UnderbarT,tokens_LbrackT,tokens_SymbolT
          (implode "::"),tokens_AsT,tokens_OpT} UNION
                   {tokens_IntT i | T} UNION {tokens_StringT s | T}
                     UNION {tokens_CharT c | T} UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nV] UNION
                     firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt'))
                     nConstructorName])
        | nPConApp ->
        UNIV DIFF
          ({tokens_LparT,tokens_UnderbarT,tokens_LbrackT,tokens_OpT}
          UNION {tokens_IntT i | T} UNION
                   {tokens_StringT s | T} UNION {tokens_CharT c | T}
                     UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nV] UNION
                     firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt'))
                     nConstructorName])
        | nPapp ->
        UNIV DIFF
          ({tokens_LparT,tokens_UnderbarT,tokens_LbrackT,tokens_OpT}
          UNION {tokens_IntT i | T} UNION
                   {tokens_StringT s | T} UNION {tokens_CharT c | T}
                     UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nV] UNION
                     firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt'))
                     nConstructorName])
        | nPattern ->
        UNIV DIFF
          ({tokens_LparT,tokens_UnderbarT,tokens_LbrackT,tokens_ColonT
          ,tokens_ArrowT,tokens_StarT,tokens_AsT,tokens_OpT} UNION
                   {tokens_AlphaT s | T} UNION {tokens_SymbolT s | T}
                     UNION {tokens_LongidT s1 s2 | T} UNION
                   {tokens_IntT i | T} UNION {tokens_StringT s | T}
                     UNION {tokens_CharT c | T} UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nV] UNION
                     firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt'))
                     nConstructorName])
        | nPatternList ->
        UNIV DIFF
          ({tokens_CommaT,tokens_LparT,tokens_UnderbarT,tokens_LbrackT
          ,tokens_ColonT,tokens_ArrowT,tokens_StarT,tokens_AsT,
                    tokens_OpT} UNION
                   {tokens_AlphaT s | T} UNION {tokens_SymbolT s | T}
                     UNION {tokens_LongidT s1 s2 | T} UNION
                   {tokens_IntT i | T} UNION {tokens_StringT s | T}
                     UNION {tokens_CharT c | T} UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nV] UNION
                     firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt'))
                     nConstructorName])
        | nPbaseList1 -> UNIV DIFF firstSet cmlG [(\nt'. grammar_NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nPbase]
        | nPE -> nestoppers
        | nPEs -> nestoppers
        | nPEsfx -> nestoppers
        | nPType -> UNIV DIFF ({tokens_StarT} UNION firstSet cmlG
          [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp])
        | nSpecLine ->
        UNIV DIFF
          ({tokens_ArrowT,tokens_AndT,tokens_BarT,tokens_StarT
          ,tokens_OfT,tokens_EqualsT,tokens_LparT} UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp] UNION
                     {tokens_TyvarT s | T})
        | nSpecLineList ->
        UNIV DIFF
          ({tokens_ValT,tokens_DatatypeT,tokens_TypeT,tokens_ExceptionT
          ,tokens_SemicolonT,
                    tokens_ArrowT,tokens_AndT,tokens_BarT
                      ,tokens_StarT,tokens_OfT,tokens_EqualsT
                      ,tokens_LparT} UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp] UNION
                     {tokens_TyvarT s | T})
        | nTbaseList ->
        UNIV DIFF ({tokens_LparT} UNION firstSet cmlG [(\nt'.
          grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp] UNION
          {tokens_TyvarT s | T})
        | nTopLevelDecs -> {}
        | nType -> UNIV DIFF ({tokens_ArrowT,tokens_StarT} UNION
          firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
          nt')) nTyOp])
        | nTypeAbbrevDec ->
        UNIV DIFF ({tokens_ArrowT,tokens_StarT} UNION firstSet cmlG
          [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp])
        | nTypeDec ->
        UNIV DIFF
          ({tokens_AndT,tokens_ArrowT,tokens_StarT,tokens_BarT
          ,tokens_OfT,tokens_LparT} UNION {tokens_TyvarT s | T} UNION
                   firstSet cmlG [(\nt'. grammar_NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp])
        | nTypeList1 ->
        UNIV DIFF ({tokens_CommaT,tokens_ArrowT,tokens_StarT} UNION
          firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
          nt')) nTyOp])
        | nTypeList2 ->
        UNIV DIFF ({tokens_CommaT,tokens_ArrowT,tokens_StarT} UNION
          firstSet cmlG [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
          nt')) nTyOp])
        | nTyVarList -> {tokens_RparT}
        | nOptionalSignatureAscription -> UNIV DELETE tokens_SealT
        | _9 -> UNIV`;;
hol4_overload "stoppers" "pegComplete_stoppers";;

(* HOL4 pegCompleteScript.sml:897: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:1137: the overload RANK, which the port
   expands *)

(* could generalise this slightly: allowing for nullable seps, but this would
   require a more complicated condition on the sfx, something like
     (sfx ≠ [] ∧ ¬nullable cmlG [SEP] ⇒ HD sfx ∉ firstSet cmlG [SEP]) ∧
     (sfx ≠ [] ∧ nullable cmlG [SEP] ⇒ HD sfx ∉ firstSet cmlG [C])
   and I can't be bothered with that right now. *)

(* HOL4 pegCompleteScript.sml:2024-2026: a proof *)

(* HOL4 pegCompleteScript.sml:2028: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:2030: the ML values that the
   definitions below antiquote *)

(* HOL4 pegCompleteScript.sml:2032-2036: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:2038-2041: a proof *)

(* HOL4 pegCompleteScript.sml:2087: the ML values that the
   definitions below antiquote *)
