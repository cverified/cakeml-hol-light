(* ======================================================== *)
(*  pegComplete: ported from HOL4's
    compiler/parsing/proofs/pegCompleteScript.sml  *)
(* ======================================================== *)

(*
  Completeness proof for the parser. If a successful parse exists,
  then the parser will find one.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/parsing/cmlPEG.ml";;
needs "compiler/parsing/proofs/cmlNTProps.ml";;
needs "compiler/parsing/proofs/pegSound.ml";;
needs "lib/grammar.ml";;
needs "lib/location.ml";;
needs "lib/peg.ml";;
needs "semantics/gram.ml";;
needs "semantics/proofs/gramProps.ml";;
needs "semantics/tokens.ml";;
(* HOL4 ancestors outside the port: NTproperties *)

(* Set up ML bindings *)
(* HOL4 ML code, not ported:
open pegTheory grammarTheory pegSoundTheory
     gramTheory gramPropsTheory cmlPEGTheory cmlNTPropsTheory;
*)

(* HOL4 ML code, not ported:
val bindNT0_lemma = REWRITE_RULE [GSYM mkNd_def] bindNT0_def
val _ = augment_srw_ss [rewrites [bindNT0_lemma]]
*)

(* HOL4 ML code, not ported:
fun SRULE ths = SIMP_RULE (srw_ss()) ths
*)

(* HOL4 ML code, not ported:
val skths = [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
val SKRULE = SRULE skths
val SKTAC = gs skths
*)

(* HOL4 ML code, not ported:
val peg_det = CONJUNCT1 peg_deterministic
*)

(* HOL4 ML code, not ported:
fun PULLV v t = let
  val (bv,b) = dest_abs(rand t)
in
  if bv ~~ v then ALL_CONV
  else BINDER_CONV (PULLV v) THENC SWAP_VARS_CONV
end t
*)

(* HOL4 ML code, not ported:
fun REFINE_EXISTS_TAC t (asl, w) = let
  val (qvar, body) = dest_exists w
  val ctxt = free_varsl (w::asl)
  val qvars = op_set_diff aconv (free_vars t) ctxt
  val newgoal = subst [qvar |-> t] body
  fun chl [] ttac = ttac
    | chl (h::t) ttac = X_CHOOSE_THEN h (chl t ttac)
in
  SUBGOAL_THEN
    (list_mk_exists(rev qvars, newgoal))
    (chl (rev qvars) (fn th => Tactic.EXISTS_TAC t THEN ACCEPT_TAC th))
    (asl, w)
end
*)


(* HOL4 ML code, not ported:
fun unify_firstconj k th (g as (asl,w)) = let
  val (exvs, body) = strip_exists w
  val c = hd (strip_conj body)
  val (favs, fabody) = strip_forall (concl th)
  val con = #2 (dest_imp fabody)
  val theta = Unify.simp_unify_terms (op_set_diff aconv (free_vars c)
    exvs) c con
  fun inst_exvs theta =
      case theta of
          [] => ALL_TAC
        | {redex,residue} :: rest =>
          if tmem redex exvs andalso
             HOLset.isEmpty (HOLset.intersection (FVL [residue]
               empty_tmset, HOLset.addList(empty_tmset,exvs)))
          then
            if HOLset.isEmpty (HOLset.intersection (FVL [residue]
              empty_tmset, HOLset.addList(empty_tmset,favs))) then
              CONV_TAC (PULLV redex) THEN EXISTS_TAC residue THEN
              inst_exvs rest
            else CONV_TAC (PULLV redex) THEN REFINE_EXISTS_TAC residue
              THEN
                 inst_exvs rest
          else inst_exvs rest
  fun inst_favs theta th =
      case theta of
          [] => k th
        | {redex,residue} :: rest =>
          if tmem redex favs then
            inst_favs rest (th |> CONV_RULE (PULLV redex) |> SPEC
              residue)
          else inst_favs rest th
in
  inst_exvs theta THEN inst_favs theta th
end g
*)

(* HOL4 ML code, not ported:
val _ = augment_srw_ss [rewrites [
  peg_eval_tok_SOME, tokeq_def, bindNT_def, mktokLf_def,
  pegf_def, peg_eval_seq_SOME, pnt_def, peg_eval_try,
  try_def]]
*)

(* HOL4 ML code, not ported:
val has_length = assert (can (find_term (same_const
  listSyntax.length_tm)) o
                         concl)
*)

(* HOL4 ML code, not ported:
val peg_eval_choice_NONE =
  ``peg_eval G (i, choice s1 s2 f) (Failure fl fe)``
    |> SIMP_CONV (srw_ss()) [Once peg_eval_cases]
*)

(* HOL4 ML code, not ported:
val cmlPEG_total =
    peg_eval_total |> Q.GEN `G` |> Q.ISPEC `cmlPEG`
                             |> C MATCH_MP PEG_wellformed
*)

(* HOL4 ML code, not ported:
val fFail_def = new_specification(
  "fFail_def", ["fFAIL1", "fFAIL2"],
  SKRULE peg_respects_firstSets);
*)

let sym2peg_def = cake_define_list
  [`sym2peg (TOK tk:('a,'b)grammar_symbol) = tokeq tk`;
   `sym2peg (NT N:('a,'b)grammar_symbol) = nt N I`];;

(* only the subs = [x] and subs = [x;y] cases are relevant *)
let left_insert1_def = cake_define_list
  [`left_insert1 pt (Lf (tk,l):('a,'b,'locs)parsetree) = Lf
  (tk,merge_locs (ptree_loc pt) l)`;
   `left_insert1 pt (Nd (n,l0) subs:('a,'b,'locs)parsetree) =
         (match subs with
             [] -> Nd (n,merge_locs (ptree_loc pt) l0) [pt] | [x]
               -> mkNd n [mkNd n [pt]; x] | x :: xs -> mkNd n
               (left_insert1 pt x :: xs))`];;

(* HOL4 ML code, not ported:
val _ = export_rewrites ["grammar.ptree_loc_def"]
*)

let leftLoc_def = cake_define
  `leftLoc (Locs l1 _1) = l1`;;
let rightLoc_def = cake_define
  `rightLoc (Locs _2 l2) = l2`;;

(* two valid parse-trees with the same head, and the same fringes, which
   are all tokens, must be identical. *)

(* Problem with Eapp is that it's left-recursive in the grammar :

     Eapp ::= Eapp Ebase | Ebase

   but the PEG parses it by calling Ebase >> rpt Ebase, and then doing
   a FOLDL on the resulting list to assemble it into a valid parse-tree.

   Then, when it comes time to prove completeness (eapp_completeness
   below), we know that we have a valid Eapp parse-tree, but we expand
   the PEG invocation out into Ebase >> rpt Ebase, and do an induction
     on the
   length of the token-list to be consumed.  The gist of it all is that
     we
   end up wanting to know that if we've generated an Eapp to our right,
     then
   we can insert an Ebase from its left, generating a valid tree.

   This next result says that if we have a parse tree (i.e., with an
   Eapp (pt) to the left, and an Ebase bpt to the right, then we can
   "reassociate", giving us an Ebase (bpt') sitting to the left and an
   Eapp (pt') sitting to the right, such that left-inserting the
   former into the latter gives us back what we started with.
*)

let leftmost_def = cake_define_list
  [`leftmost (Lf s:('a,'b,'locs)parsetree) = Lf s`;
   `leftmost (Nd (n,l) args:('a,'b,'locs)parsetree) =
      (if ~(args = []) /\ n = (INL:MMLnonT->MMLnonT+num) nTbase then
        HD args else
        match args with
            [] -> Nd (n,l) args | h :: _4 -> leftmost h)`];;

(* pt is a Tbase, and n will be DType all the way down *)
let left_insert2_def = cake_define_list
  [`left_insert2 pt (Lf (tk,l):('a,'b,'locs)parsetree) = Lf
  (tk,merge_locs (ptree_loc pt) l)`;
   `left_insert2 pt (Nd (n,l0) subs:('a,'b,'locs)parsetree) =
         (match subs with
             [] -> Nd (n,merge_locs (ptree_loc pt) l0) [pt] | [Nd
               _6 [tyop]] -> mkNd n [mkNd n [pt]; tyop] | x :: ys ->
               mkNd n (left_insert2 pt x :: ys))`];;

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
  The next reassociation scenario is the general story of a
    left-associative
  binary operator, such that the rule is of the form

    P ::= P SEP C | C

  Imagine you have a valid P-tree to the right, and a single C to the
    left.
  You can insert that C-tree into the valid P-tree in the leftmost
    position,
  generating a new, valid P-tree.
*)


let left_insert_def = cake_define_list
  [`left_insert (Lf (tk,l):('a,'b,'locs)parsetree) p sep c = Lf
  (tk,merge_locs (ptree_loc c) l)`;
   `left_insert (Nd (n,l) subs:('a,'b,'locs)parsetree) p sep c =
         (if ~(n = p) then Nd (n,merge_locs (ptree_loc c) l) subs
           else
           match subs with
               [c0] -> mkNd p [mkNd p [c]; sep; c0] | [p'; s';
                 c'] -> mkNd p [left_insert p' p sep c; s'; c'] | _8
                 -> Nd (n,merge_locs (ptree_loc c) l) subs)`];;

(* HOL4 ML code, not ported:
fun has_const c = assert (Lib.can (find_term (same_const c)) o concl)
*)

(* HOL4 ML code, not ported:
fun qpat_drule pat th =
  qpat_assum pat (mp_then (Pos hd) assume_tac th)
fun qpat_dxrule pat th =
  qpat_x_assum pat (mp_then (Pos hd) assume_tac th)
*)

let nestoppers_def = cake_define
  `nestoppers =
      UNIV DIFF ({AndalsoT,ArrowT,BarT,ColonT,HandleT,OrelseT,
                  AlphaT (implode "before")} UNION
                 firstSet cmlG [(\nt'. NT ((INL:MMLnonT->MMLnonT+num)
                   nt')) nMultOps] UNION
                 firstSet cmlG [(\nt'. NT ((INL:MMLnonT->MMLnonT+num)
                   nt')) nRelOps] UNION
                 firstSet cmlG [(\nt'. NT ((INL:MMLnonT->MMLnonT+num)
                   nt')) nListOps] UNION
                 firstSet cmlG [(\nt'. NT ((INL:MMLnonT->MMLnonT+num)
                   nt')) nAddOps] UNION
                 firstSet cmlG [(\nt'. NT ((INL:MMLnonT->MMLnonT+num)
                   nt')) nCompOps] UNION
                 firstSet cmlG [(\nt'. NT
                   ((INL:MMLnonT->MMLnonT+num) nt')) nEbase] UNION
                   firstSet cmlG [(\nt'. NT
                   ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp])`;;

let stoppers_def = cake_define
  `stoppers nAndFDecls =
        match  with
           -> nestoppers DELETE AndT
        |  ->
        UNIV DIFF ({StarT,OfT,ArrowT,LparT} UNION firstSet cmlG
          [(\nt'. NT ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp] UNION
                   {TyvarT s | T})
        |  ->
        nestoppers DIFF ({BarT,StarT,AndT,OfT} UNION {TyvarT s | T})
        |  ->
        nestoppers DIFF
        ({BarT,StarT,AndT,SemicolonT,FunT,ValT,DatatypeT,OfT
          ,ExceptionT,
          TypeT,LocalT,StructureT} UNION {TyvarT s | T})
        |  -> UNIV DIFF firstSet cmlG [(\nt'. NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp]
        |  ->
        UNIV DIFF ({ArrowT,BarT,StarT,OfT,LparT} UNION firstSet cmlG
          [(\nt'. NT ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp] UNION
                   {TyvarT s | T})
        |  ->
        UNIV DIFF ({ArrowT,BarT,StarT,OfT,LparT} UNION firstSet cmlG
          [(\nt'. NT ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp] UNION
                   {TyvarT s | T})
        |  ->
        UNIV DIFF ({AndT,ArrowT,BarT,StarT,OfT,LparT} UNION {TyvarT s
          | T} UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp])
        |  -> nestoppers
        |  ->
        UNIV DIFF (firstSet cmlG [(\nt'. NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nMultOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nAddOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nEbase])
        |  -> UNIV DIFF firstSet cmlG [(\nt'. NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nEbase]
        |  ->
        UNIV DIFF ({AlphaT (implode "before")} UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nCompOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nRelOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nListOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nMultOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nAddOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nEbase])
        |  ->
        UNIV DIFF (firstSet cmlG [(\nt'. NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nCompOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nRelOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nListOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nMultOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nAddOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nEbase])
        |  -> nestoppers
        |  -> nestoppers DELETE CommaT
        |  -> nestoppers DELETE CommaT
        |  -> UNIV DIFF (firstSet cmlG [(\nt'. NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nMultOps] UNION
                              firstSet cmlG [(\nt'. NT
                                ((INL:MMLnonT->MMLnonT+num) nt'))
                                nAddOps] UNION
                              firstSet cmlG [(\nt'. NT
                                ((INL:MMLnonT->MMLnonT+num) nt'))
                                nListOps] UNION
                              firstSet cmlG [(\nt'. NT
                                ((INL:MMLnonT->MMLnonT+num) nt'))
                                nEbase])
        |  ->
        UNIV DIFF ({AndalsoT,ColonT,ArrowT,AlphaT (implode "before")}
          UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nCompOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nRelOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nListOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nMultOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nAddOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nEbase] UNION
                     firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp])
        |  ->
        UNIV DIFF ({AndalsoT,ColonT,ArrowT,OrelseT,AlphaT (implode
          "before")} UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nCompOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nRelOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nListOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nMultOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nAddOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nEbase] UNION
                     firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp])
        |  ->
        UNIV DIFF (firstSet cmlG [(\nt'. NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nEbase] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nMultOps])
        |  ->
        UNIV DIFF (firstSet cmlG [(\nt'. NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nRelOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nListOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nMultOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nAddOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nEbase])
        |  -> nestoppers DELETE SemicolonT
        |  ->
        UNIV DIFF ({ColonT,ArrowT,AlphaT (implode "before")} UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nCompOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nListOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nRelOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nMultOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nAddOps] UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nEbase] UNION
                     firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp])
        |  -> nestoppers
        |  -> nestoppers DELETE AndT
        |  -> nestoppers DIFF {AndT,FunT,ValT,SemicolonT}
        |  -> {}
        |  ->
        UNIV DIFF ({ArrowT,StarT,EqualsT} UNION firstSet cmlG [(\nt'.
          NT ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp])
        |  ->
        UNIV DIFF ({LparT,UnderbarT,LbrackT,SymbolT (implode
          "::"),OpT} UNION
                   {IntT i | T} UNION {StringT s | T} UNION {CharT c
                     | T} UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nV] UNION
                     firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt'))
                     nConstructorName])
        |  ->
        UNIV DIFF ({LparT,UnderbarT,LbrackT,SymbolT (implode
          "::"),AsT,OpT} UNION
                   {IntT i | T} UNION {StringT s | T} UNION {CharT c
                     | T} UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nV] UNION
                     firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt'))
                     nConstructorName])
        |  ->
        UNIV DIFF ({LparT,UnderbarT,LbrackT,OpT} UNION {IntT i | T}
          UNION
                   {StringT s | T} UNION {CharT c | T} UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nV] UNION
                     firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt'))
                     nConstructorName])
        |  ->
        UNIV DIFF ({LparT,UnderbarT,LbrackT,OpT} UNION {IntT i | T}
          UNION
                   {StringT s | T} UNION {CharT c | T} UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nV] UNION
                     firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt'))
                     nConstructorName])
        |  ->
        UNIV DIFF
          ({LparT,UnderbarT,LbrackT,ColonT,ArrowT,StarT,AsT,OpT} UNION
                   {AlphaT s | T} UNION {SymbolT s | T} UNION
                     {LongidT s1 s2 | T} UNION
                   {IntT i | T} UNION {StringT s | T} UNION {CharT c
                     | T} UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nV] UNION
                     firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt'))
                     nConstructorName])
        |  ->
        UNIV DIFF
          ({CommaT,LparT,UnderbarT,LbrackT,ColonT,ArrowT,StarT,AsT,
                    OpT} UNION
                   {AlphaT s | T} UNION {SymbolT s | T} UNION
                     {LongidT s1 s2 | T} UNION
                   {IntT i | T} UNION {StringT s | T} UNION {CharT c
                     | T} UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nV] UNION
                     firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt'))
                     nConstructorName])
        |  -> UNIV DIFF firstSet cmlG [(\nt'. NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nPbase]
        |  -> nestoppers
        |  -> nestoppers
        |  -> nestoppers
        |  -> UNIV DIFF ({StarT} UNION firstSet cmlG [(\nt'. NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp])
        |  ->
        UNIV DIFF ({ArrowT,AndT,BarT,StarT,OfT,EqualsT,LparT} UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp] UNION
                     {TyvarT s | T})
        |  ->
        UNIV DIFF ({ValT,DatatypeT,TypeT,ExceptionT,SemicolonT,
                    ArrowT,AndT,BarT,StarT,OfT,EqualsT,LparT} UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp] UNION
                     {TyvarT s | T})
        |  ->
        UNIV DIFF ({LparT} UNION firstSet cmlG [(\nt'. NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp] UNION {TyvarT s | T})
        |  -> {}
        |  -> UNIV DIFF ({ArrowT,StarT} UNION firstSet cmlG [(\nt'.
          NT ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp])
        |  ->
        UNIV DIFF ({ArrowT,StarT} UNION firstSet cmlG [(\nt'. NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp])
        |  ->
        UNIV DIFF ({AndT,ArrowT,StarT,BarT,OfT,LparT} UNION {TyvarT s
          | T} UNION
                   firstSet cmlG [(\nt'. NT
                     ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp])
        |  ->
        UNIV DIFF ({CommaT,ArrowT,StarT} UNION firstSet cmlG [(\nt'.
          NT ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp])
        |  ->
        UNIV DIFF ({CommaT,ArrowT,StarT} UNION firstSet cmlG [(\nt'.
          NT ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp])
        |  -> {RparT}
        |  -> UNIV DELETE SealT
        |  -> UNIV`;;

(* HOL4 ML code, not ported:
val normlist = REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND]
*)

(* HOL4 overload (expanded in the port):
     RANK = λn. NT_rank (mkNT n) *)

(* could generalise this slightly: allowing for nullable seps, but this
   would
   require a more complicated condition on the sfx, something like
     (sfx ≠ [] ∧ ¬nullable cmlG [SEP] ⇒ HD sfx ∉ firstSet cmlG [SEP]) ∧
     (sfx ≠ [] ∧ nullable cmlG [SEP] ⇒ HD sfx ∉ firstSet cmlG [C])
   and I can't be bothered with that right now. *)

(* HOL4 ML code, not ported:
val stdstart =
    simp[Once peg_eval_NT_SOME, cmlpeg_rules_applied, MAP_EQ_CONS] >>
      rw[] >>
    fs[MAP_EQ_CONS, MAP_EQ_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >> rw[]
*)

(* HOL4 ML code, not ported:
fun note_tac s g = (print (s ^ "\n"); ALL_TAC g)
*)

(* HOL4 ML code, not ported:
val list_case_eq = TypeBase.case_eq_of ``:'a list``
*)

(* HOL4 ML code, not ported:
fun hasc cnm t = #1 (dest_const t) = cnm handle HOL_ERR _ => false
fun const_assum0 f cnm k =
  f (k o assert (can (find_term (hasc cnm)) o concl))
val const_assum = const_assum0 first_assum
val const_x_assum = const_assum0 first_x_assum
*)

(* HOL4 ML code, not ported:
val pmap_cases =
  rpt ((rename [`(_,_) = (_ ## _) pair`] >> Cases_on `pair` >> fs[] >>
    rveq)
         ORELSE
       (rename [`(_ ## _) pair = (_,_)`] >> Cases_on `pair` >> fs[] >>
         rveq))
*)

(* HOL4 ML code, not ported:
val loseRK = loseC “NT_rank”
*)
