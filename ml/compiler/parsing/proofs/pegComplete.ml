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
needs "lib/regexp_compiler.ml";;
needs "semantics/gram.ml";;
needs "semantics/proofs/gramProps.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "pegComplete"
  ["cmlNTProps"; "cmlPEG"; "gram"; "gramProps"; "pegSound"];;

let _ = do_list hide_constant ["C"; "sub"];;

(* Set up ML bindings *)
(* HOL4 pegCompleteScript.sml:13-14: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:18-19: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:21: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:23-25: ML code, not ported *)

(* option_case_eq[local] *)
let pegComplete_option_case_eq = prove
 (`(option_CASE optv n sf = v) <=>
      optv = NONE /\ n = v \/ (?v0. optv = SOME v0 /\ sf v0 = v)`,
  CHEAT_TAC);;
(* [local] *)
let MAP_EQ_CONS = prove
 (`MAP f l = h :: t <=> (?h0 t0. l = h0 :: t0 /\ f h0 = h /\ MAP f t0
  = t)`,
  CHEAT_TAC);;

(* HOL4 pegCompleteScript.sml:38: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:40-45: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:47-59: ML code, not ported *)


(* HOL4 pegCompleteScript.sml:62-90: ML code, not ported *)

let seql_cons = prove
 (`!x. peg_eval G (i0,seql (h :: t) f) x <=>
         (?r. peg_eval G (i0,h) r /\
             ((?fl fe. r = peg_Failure fl fe /\ x = r) \/
              (?i1 rh eo1 r2.
                 r = peg_Success i1 rh eo1 /\
                 peg_eval G (i1,seql t I) r2 /\
                 ((?fl fe. r2 = peg_Failure fl fe /\ x = r2) \/
                  (?i rt eopt2.
                    r2 = peg_Success i rt eopt2 /\
                    x = peg_Success i (f (rh ++ rt)) eopt2)))))`,
  CHEAT_TAC);;

let seql_cons_SOME = prove
 (`peg_eval G (i0,seql (h :: t) f) (peg_Success i r eo) <=>
   (?i1 rh rt eo1.
     peg_eval G (i0,h) (peg_Success i1 rh eo1) /\
     peg_eval G (i1,seql t I) (peg_Success i rt eo) /\
     r = f (rh ++ rt))`,
  CHEAT_TAC);;

let choicel_cons = prove
 (`peg_eval G (i0,cmlPEG_choicel (h :: t)) x <=>
     (?r. peg_eval G (i0,h) r /\
         ((?i ptl eo. r = peg_Success i ptl eo /\ x = r) \/
          (?res2 fl1 fe1 i ptl eopt fl2 fe2.
             r = peg_Failure fl1 fe1 /\
             peg_eval G (i0,cmlPEG_choicel t) res2 /\
             (res2 = peg_Success i ptl eopt /\
              x = peg_Success i ptl (optmax MAXerr (SOME (fl1,fe1))
                eopt) \/
              res2 = peg_Failure fl2 fe2 /\
              x = UNCURRY peg_Failure (MAXerr (fl1,fe1)
                (fl2,fe2))))))`,
  CHEAT_TAC);;

let choicel_cons_NONE = prove
 (`peg_eval G (i0,cmlPEG_choicel (h :: t)) (peg_Failure fl fe:(('a#locs)
  list,'c list,'d)pegresult) <=>
     (?fl1 fe1 fl2 fe2.
       peg_eval G (i0,h) (peg_Failure fl1 fe1) /\
       peg_eval G (i0,cmlPEG_choicel t) (peg_Failure fl2 fe2) /\
       (peg_Failure fl fe:(('a#locs) list,'c list,'d)pegresult) =
       UNCURRY peg_Failure (MAXerr (fl1,fe1) (fl2,fe2)))`,
  CHEAT_TAC);;

(* [simp] *)
let peg_eval_tok_CONS_NONE = prove
 (`peg_eval G (h :: t,peg_tok P f) (peg_Failure fl fe) <=>
     (?tk l. h = (tk,l) /\ fl = l /\ fe = peg_tokFALSE G /\ ~(P
       tk))`,
  CHEAT_TAC);;

(* HOL4 pegCompleteScript.sml:153-155: a theorem that HOL4 states as
   the value of an ML expression: peg_eval_tok *)

(* [simp] *)
let peg_eval_tok_NIL = prove
 (`peg_eval G ([],peg_tok P f) r <=> r = peg_Failure (Locs EOFpt
  EOFpt) (peg_tokEOF G)`,
  CHEAT_TAC);;

(* HOL4 pegCompleteScript.sml:163-166: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:168-169: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:171-173: the ML values that the
   definitions below antiquote *)

(* [simp] *)
let peg_eval_tokSymP_NONE = prove
 (`peg_eval G (i,tokSymP P) (peg_Failure fl fe) <=>
     (!l tk t. i = (tk,l) :: t ==>
               (!s. tk = tokens_SymbolT s ==> ~(P s) /\ fl = l /\ fe
                 = peg_tokFALSE G) /\
               ((!s. ~(tk = tokens_SymbolT s)) ==> fl = l /\ fe =
                 peg_tokFALSE G)) /\
     (i = [] ==> fl = Locs EOFpt EOFpt /\ fe = peg_tokEOF G)`,
  CHEAT_TAC);;

(* disjImpI[local] *)
let pegComplete_disjImpI = prove
 (`~p \/ q <=> p ==> q`,
  CHEAT_TAC);;

(* [local] *)
let ptree_head_eq_tok0 = prove
 (`(ptree_head pt = grammar_TOK tk) <=> (?l. pt = Lf (grammar_TOK
  tk,l))`,
  CHEAT_TAC);;

(* HOL4 pegCompleteScript.sml:197-199: a theorem that HOL4 states as
   the value of an ML expression: ptree_head_eq_tok *)

(* HOL4 pegCompleteScript.sml:201-203: ML code, not ported *)

(* [local] *)
let FLAT_EQ_CONS = prove
 (`!ll h t.
      FLAT ll = h :: t <=>
      (?p t0 s. ll = p ++ [h :: t0] ++ s /\
               EVERY ((=) []) p /\ FLAT (t0 :: s) = t)`,
  CHEAT_TAC);;

let rfirstSet_nonempty_fringe = prove
 (`!pt t l rest.
     real_fringe pt = (grammar_TOK t,l) :: rest /\ valid_lptree G pt
       ==>
     t IN firstSet G [ptree_head pt]`,
  CHEAT_TAC);;

let peg_respects_firstSets = prove
 (`!N i0 t l. ~(t IN firstSet cmlG [grammar_NT N]) /\ ~(peg0 cmlPEG
  (peg_nt N I)) /\
      peg_nt N I IN Gexprs cmlPEG ==>
      (?fl fe.
        peg_eval cmlPEG ((t,l) :: i0,peg_nt N I) (peg_Failure fl
          fe))`,
  CHEAT_TAC);;

(* HOL4 pegCompleteScript.sml:263-265: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:267-269: a theorem that HOL4 states as
   the value of an ML expression: peg_respects_firstSets_rwt *)

let peg_eval_NIL_NT = prove
 (`peg_eval cmlPEG ([],peg_nt N I) (peg_Success i r eo) ==>
   (\G n. nullable G [grammar_NT n]) cmlG N /\ i = []`,
  CHEAT_TAC);;

let not_nullable_input_CONS = prove
 (`~((\G n. nullable G [grammar_NT n]) cmlG N) ==> peg_eval cmlPEG
  (i0,peg_nt N I) (peg_Success i r eo) ==>
   (?ht l t. i0 = (ht,l) :: t /\ LENGTH i <= LENGTH t)`,
  CHEAT_TAC);;

let not_nullable_seql_input_CONS = prove
 (`~((\G n. nullable G [grammar_NT n]) cmlG N) ==>
   peg_eval cmlPEG (i0,seql (peg_nt N I :: rest) f) (peg_Success i r
     eo) ==>
   (?ht l t. i0 = (ht,l) :: t /\ LENGTH i <= LENGTH t)`,
  CHEAT_TAC);;

let sym2peg_def = define_cases
  [`sym2peg (grammar_TOK tk) = cmlPEG_tokeq tk`;
   `sym2peg (grammar_NT N) = peg_nt N I`];;

let not_peg0_peg_eval_NIL_NONE = prove
 (`~(peg0 G sym) /\ sym IN Gexprs G /\ wfG G ==>
   (?fl fe. peg_eval G ([],sym) (peg_Failure fl fe))`,
  CHEAT_TAC);;

(* [local] *)
let list_case_lemma = prove
 (`([x] = (match a with [] -> [] | h :: t -> f h t)) <=>
     (~(a = []) /\ [x] = f (HD a) (TL a))`,
  CHEAT_TAC);;

(* only the subs = [x] and subs = [x;y] cases are relevant *)
let _ = size_thms "locs";;
let _ = size_thms "parsetree";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let left_insert1_def,left_insert1_ind = define_wf
  `MEASURE (\(x0,x1). parsetree_size locs_size (\x. 0) (\x. 0) x1)`
  [`left_insert1 pt (Lf (tk,l)) = Lf (tk,merge_locs (ptree_loc pt) l)`;
   `left_insert1 pt (Nd (n,l0) subs) =
         (match subs with
             [] -> Nd (n,merge_locs (ptree_loc pt) l0) [pt] |
               [x] -> mkNd n [mkNd n [pt]; x] | x :: xs -> mkNd n
               (left_insert1 pt x :: xs))`];;

let left_insert1_FOLDL = prove
 (`left_insert1 pt (FOLDL (\a b. mkNd ((INL:MMLnonT->MMLnonT+num) P) [a;
  b]) acc arg) =
    FOLDL (\a b. mkNd ((INL:MMLnonT->MMLnonT+num) P) [a; b])
      (left_insert1 pt acc) arg`,
  CHEAT_TAC);;

(* HOL4 pegCompleteScript.sml:341: ML code, not ported *)

(* [simp] *)
let ptree_loc_mkNd = prove
 (`ptree_loc (mkNd n subs) = ptree_list_loc subs`,
  CHEAT_TAC);;

let merge_list_locs_HDLAST = prove
 (`!h. merge_list_locs (h :: t) = merge_locs h (LAST (h :: t))`,
  CHEAT_TAC);;

let ptree_loc_left_insert1 = prove
 (`!subpt pt.
      valid_locs pt ==>
        ptree_loc (left_insert1 subpt pt) =
        merge_locs (ptree_loc subpt) (ptree_loc pt)`,
  CHEAT_TAC);;

let leftLoc_def = define_general
  [`leftLoc (Locs l1 _1) = l1`];;
let rightLoc_def = define_general
  [`rightLoc (Locs _2 l2) = l2`];;

let merge_locs_LR = prove
 (`merge_locs l1 l2 = Locs (leftLoc l1) (rightLoc l2)`,
  CHEAT_TAC);;

(* [simp] *)
let leftLoc_merge_locs = prove
 (`leftLoc (merge_locs l1 l2) = leftLoc l1`,
  CHEAT_TAC);;

(* [simp] *)
let rightLoc_merge_locs = prove
 (`rightLoc (merge_locs l1 l2) = rightLoc l2`,
  CHEAT_TAC);;

(* two valid parse-trees with the same head, and the same fringes, which
   are all tokens, must be identical. *)

(* Problem with Eapp is that it's left-recursive in the grammar :

     Eapp ::= Eapp Ebase | Ebase

   but the PEG parses it by calling Ebase >> rpt Ebase, and then doing
   a FOLDL on the resulting list to assemble it into a valid parse-tree.

   Then, when it comes time to prove completeness (eapp_completeness
   below), we know that we have a valid Eapp parse-tree, but we expand
   the PEG invocation out into Ebase >> rpt Ebase, and do an induction on the
   length of the token-list to be consumed.  The gist of it all is that we
   end up wanting to know that if we've generated an Eapp to our right, then
   we can insert an Ebase from its left, generating a valid tree.

   This next result says that if we have a parse tree (i.e., with an
   Eapp (pt) to the left, and an Ebase bpt to the right, then we can
   "reassociate", giving us an Ebase (bpt') sitting to the left and an
   Eapp (pt') sitting to the right, such that left-inserting the
   former into the latter gives us back what we started with.
*)

let eapp_reassociated = prove
 (`!pt bpt pf bf.
      valid_lptree cmlG pt /\ ptree_head pt = (\nt'. grammar_NT
        ((INL:MMLnonT->MMLnonT+num) nt')) nEapp /\
      real_fringe pt = MAP
        ((grammar_TOK:tokens_token->(tokens_token
        ,MMLnonT)grammar_symbol) ## I) pf /\
      valid_lptree cmlG bpt /\ ptree_head bpt = (\nt'. grammar_NT
        ((INL:MMLnonT->MMLnonT+num) nt')) nEbase /\
      real_fringe bpt = MAP
        ((grammar_TOK:tokens_token->(tokens_token
        ,MMLnonT)grammar_symbol) ## I) bf ==>
      (?pt' bpt'.
        valid_lptree cmlG pt' /\ valid_lptree cmlG bpt' /\
        leftLoc (ptree_loc bpt') = leftLoc (ptree_loc pt) /\
        rightLoc (ptree_loc pt') = rightLoc (ptree_loc bpt) /\
        ptree_head pt' = (\nt'. grammar_NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nEapp /\ ptree_head bpt' =
          (\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nEbase /\
        real_fringe bpt' ++ real_fringe pt' = MAP
          ((grammar_TOK:tokens_token->(tokens_token
          ,MMLnonT)grammar_symbol) ## I) (pf ++ bf) /\
        mkNd ((INL:MMLnonT->MMLnonT+num) nEapp) [pt; bpt] =
          left_insert1 bpt' pt')`,
  CHEAT_TAC);;

let _ = size_thms "MMLnonT";;
let _ = size_thms "parsetree";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let leftmost_def,leftmost_ind = define_wf
  `MEASURE (\x0. parsetree_size (\x. 0) MMLnonT_size (\x. 0) x0)`
  [`leftmost (Lf s) = Lf s`;
   `leftmost (Nd (n,l) args) =
      (if ~(args = []) /\ n = (INL:MMLnonT->MMLnonT+num) nTbase then
        HD args else
        match args with
            [] -> Nd (n,l) args | h :: _4 -> leftmost h)`];;

(* pt is a Tbase, and n will be DType all the way down *)
let _ = size_thms "locs";;
let _ = size_thms "parsetree";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let left_insert2_def,left_insert2_ind = define_wf
  `MEASURE (\(x0,x1). parsetree_size locs_size (\x. 0) (\x. 0) x1)`
  [`left_insert2 pt (Lf (tk,l)) = Lf (tk,merge_locs (ptree_loc pt) l)`;
   `left_insert2 pt (Nd (n,l0) subs) =
         (match subs with
             [] -> Nd (n,merge_locs (ptree_loc pt) l0) [pt] | [Nd _6
               [
                  // nTbase
                  tyop]] -> mkNd n [mkNd n [pt]; tyop] | x ::
                    ys -> mkNd n (left_insert2 pt x :: ys))`];;

let ptree_loc_left_insert2 = prove
 (`!bpt dpt.
     valid_locs dpt ==>
       ptree_loc (left_insert2 bpt dpt) =
       merge_locs (ptree_loc bpt) (ptree_loc dpt)`,
  CHEAT_TAC);;

let left_insert2_FOLDL = prove
 (`left_insert2 pt (FOLDL (\a b. mkNd ((INL:MMLnonT->MMLnonT+num) P) [a;
  b]) acc arg) =
    FOLDL (\a b. mkNd ((INL:MMLnonT->MMLnonT+num) P) [a; b])
      (left_insert2 pt acc) arg`,
  CHEAT_TAC);;

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

let dtype_reassociated = prove
 (`!pt bpt pf bf.
      valid_lptree cmlG pt /\ ptree_head pt = (\nt'. grammar_NT
        ((INL:MMLnonT->MMLnonT+num) nt')) nDType /\
      real_fringe pt = MAP
        ((grammar_TOK:tokens_token->(tokens_token
        ,MMLnonT)grammar_symbol) ## I) pf /\
      valid_lptree cmlG bpt /\ ptree_head bpt = (\nt'. grammar_NT
        ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp /\
      real_fringe bpt = MAP
        ((grammar_TOK:tokens_token->(tokens_token
        ,MMLnonT)grammar_symbol) ## I) bf ==>
      (?pt' bpt'.
        valid_lptree cmlG pt' /\ valid_lptree cmlG bpt' /\
        valid_lptree cmlG (leftmost pt') /\
        ptree_head (leftmost pt') = (\nt'. grammar_NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nTyOp /\
        ptree_head pt' = (\nt'. grammar_NT
          ((INL:MMLnonT->MMLnonT+num) nt')) nDType /\ ptree_head bpt' =
          (\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nTbase /\
        real_fringe bpt' ++ real_fringe pt' = MAP
          ((grammar_TOK:tokens_token->(tokens_token
          ,MMLnonT)grammar_symbol) ## I) (pf ++ bf) /\
        leftLoc (ptree_loc bpt') = leftLoc (ptree_loc pt) /\
        rightLoc (ptree_loc pt') = rightLoc (ptree_loc bpt) /\
        mkNd ((INL:MMLnonT->MMLnonT+num) nDType) [pt; bpt] =
          left_insert2 bpt' pt')`,
  CHEAT_TAC);;

(*
  The next reassociation scenario is the general story of a left-associative
  binary operator, such that the rule is of the form

    P ::= P SEP C | C

  Imagine you have a valid P-tree to the right, and a single C to the left.
  You can insert that C-tree into the valid P-tree in the leftmost position,
  generating a new, valid P-tree.
*)


let _ = size_thms "locs";;
let _ = size_thms "parsetree";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let left_insert_def,left_insert_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3). parsetree_size locs_size (\x. 0) (\x. 0)
  x0)`
  [`left_insert (Lf (tk,l)) p sep c = Lf (tk,merge_locs (ptree_loc c)
  l)`;
   `left_insert (Nd (n,l) subs) p sep c =
         (if ~(n = p) then Nd (n,merge_locs (ptree_loc c) l) subs
           else
           match subs with
               [c0] -> mkNd p [mkNd p [c]; sep; c0] | [p'; s';
                 c'] -> mkNd p [left_insert p' p sep c; s'; c'] |
                 _8 -> Nd (n,merge_locs (ptree_loc c) l) subs)`];;


(* [simp] *)
let left_insert_mkNd = prove
 (`(left_insert (mkNd n [c0]) n sep c = mkNd n [mkNd n [c]; sep; c0]) /\
   (left_insert (mkNd n [p'; s'; c']) n sep c =
      mkNd n [left_insert p' n sep c; s'; c'])`,
  CHEAT_TAC);;

let ptree_loc_left_insert = prove
 (`!bpt n sep c.
     valid_locs bpt ==>
       ptree_loc (left_insert bpt n sep c) =
       merge_locs (ptree_loc c) (ptree_loc bpt)`,
  CHEAT_TAC);;

let lassoc_reassociated = prove
 (`!G P SEP C' ppt spt cpt pf sf cf. FAPPLY (rules
      G) P = {[grammar_NT P; SEP; C'],[C']} ==>
      valid_lptree G ppt /\ ptree_head ppt = grammar_NT P /\
        real_fringe ppt = MAP (grammar_TOK ## I) pf /\
      valid_lptree G spt /\ ptree_head spt = SEP /\
        real_fringe spt = MAP (grammar_TOK ## I) sf /\
      valid_lptree G cpt /\ ptree_head cpt = C' /\
        real_fringe cpt = MAP (grammar_TOK ## I) cf ==>
      (?cpt' spt' ppt'.
        valid_lptree G ppt' /\ ptree_head ppt' = grammar_NT P /\
        valid_lptree G spt' /\ ptree_head spt' = SEP /\
        valid_lptree G cpt' /\ ptree_head cpt' = C' /\
        real_fringe cpt' ++ real_fringe spt' ++ real_fringe ppt' =
          MAP (grammar_TOK ## I) (pf ++ sf ++ cf) /\
        leftLoc (ptree_loc cpt') = leftLoc (ptree_loc ppt) /\
        rightLoc (ptree_loc ppt') = rightLoc (ptree_loc cpt) /\
        mkNd P [ppt; spt; cpt] = left_insert ppt' P spt' cpt')`,
  CHEAT_TAC);;

let left_insert_mk_linfix = prove
 (`left_insert (mk_linfix N acc arg) N s c =
    mk_linfix N (left_insert acc N s c) arg`,
  CHEAT_TAC);;

(* [local] *)
let elim_disjineq = prove
 (`p \/ ~(x = y) <=> (x = y ==> p)`,
  CHEAT_TAC);;

(* [local] *)
let elim_det = prove
 (`(!x. P x <=> (x = y)) ==> P y`,
  CHEAT_TAC);;

let peg_seql_NONE_det = prove
 (`peg_eval G (i0,seql syms f) (peg_Failure fl fe) ==>
    (!f' r. peg_eval G (i0,seql syms f') r <=> r = (peg_Failure fl
      fe))`,
  CHEAT_TAC);;

(* HOL4 pegCompleteScript.sml:697: ML code, not ported *)

let firstSet_respect_peg_eval_not_success = prove
 (`~(t IN firstSet cmlG [grammar_NT N]) /\ ~(peg0 cmlPEG (peg_nt N I))
  /\ peg_nt N I IN Gexprs cmlPEG ==>
     ~(peg_eval cmlPEG ((t,l) :: i0,peg_nt N I) (peg_Success i r
       e0))`,
  CHEAT_TAC);;

let eOR_wrongtok = prove
 (`~(peg_eval cmlPEG ((tokens_RaiseT,loc) :: i0,peg_nt
  ((INL:MMLnonT->MMLnonT+num) nElogicOR) I) (peg_Success i r eo)) /\
   ~(peg_eval cmlPEG ((tokens_FnT,loc) :: i0,peg_nt
     ((INL:MMLnonT->MMLnonT+num) nElogicOR) I) (peg_Success i r eo)) /\
   ~(peg_eval cmlPEG ((tokens_CaseT,loc) :: i0,peg_nt
     ((INL:MMLnonT->MMLnonT+num) nElogicOR) I) (peg_Success i r eo)) /\
   ~(peg_eval cmlPEG ((tokens_IfT,loc) :: i0,peg_nt
     ((INL:MMLnonT->MMLnonT+num) nElogicOR) I) (peg_Success i r eo))`,
  CHEAT_TAC);;

let peg_eval_seqempty = prove
 (`peg_eval G (i0,peg_seq e1 (peg_empty []) f) r =
   (?r0. peg_eval G (i0,e1) r0 /\
        ((?fl fe. r0 = peg_Failure fl fe /\ r = r0) \/
         (?i r00 eo. r0 = peg_Success i r00 eo /\ r = peg_Success i
           (f r00 []) NONE)))`,
  CHEAT_TAC);;

let peg_eval_NT = prove
 (`peg_eval G (i0,peg_nt N f) r <=>
     (?r0. r = resultmap f r0 /\ N IN FDOM (rules G) /\ peg_eval G
       (i0,FAPPLY (rules G) N) r0)`,
  CHEAT_TAC);;

(* HOL4 pegCompleteScript.sml:734-737: ML code, not ported *)

let nestoppers_def = new_definition
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

let stoppers_def = new_definition
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


let left_insert1_mkNd = prove
 (`left_insert1 pt1 (mkNd ((INL:MMLnonT->MMLnonT+num) nEapp) [pt2]) =
   mkNd ((INL:MMLnonT->MMLnonT+num) nEapp) [mkNd
     ((INL:MMLnonT->MMLnonT+num) nEapp) [pt1]; pt2]`,
  CHEAT_TAC);;

let eapp_complete = prove
 (`(!pt' pfx' sfx' N.
       LENGTH pfx' < LENGTH master /\ valid_lptree cmlG pt' /\
       (INL:MMLnonT->MMLnonT+num) N IN FDOM (rules cmlPEG) /\
       ptree_head pt' = (\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
         nt')) N /\ real_fringe pt' = MAP
         ((grammar_TOK:tokens_token->(tokens_token
         ,MMLnonT)grammar_symbol) ## I) pfx' /\
       (~(sfx' = []) ==> FST (HD sfx') IN pegComplete_stoppers N) ==>
       (?eo.
         peg_eval cmlPEG (pfx' ++ sfx',peg_nt
           ((INL:MMLnonT->MMLnonT+num) N) I) (peg_Success sfx' [pt']
           eo))) /\
    (!pt' sfx'.
       valid_lptree cmlG pt' /\ ptree_head pt' = (\nt'. grammar_NT
         ((INL:MMLnonT->MMLnonT+num) nt')) nEbase /\
       real_fringe pt' = MAP
         ((grammar_TOK:tokens_token->(tokens_token
         ,MMLnonT)grammar_symbol) ## I) master /\
       (~(sfx' = []) ==> FST (HD sfx') IN pegComplete_stoppers
         nEbase) ==>
       (?eo.
       peg_eval cmlPEG (master ++ sfx',peg_nt
         ((INL:MMLnonT->MMLnonT+num) nEbase) I)
                (peg_Success sfx' [pt'] eo))) ==>
     (!pfx apt sfx.
       IS_SUFFIX master pfx /\ valid_lptree cmlG apt /\
       ptree_head apt = (\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
         nt')) nEapp /\ real_fringe apt = MAP
         ((grammar_TOK:tokens_token->(tokens_token
         ,MMLnonT)grammar_symbol) ## I) pfx /\
       (~(sfx = []) ==> FST (HD sfx) IN pegComplete_stoppers nEapp)
         ==>
       (?eo.
         peg_eval cmlPEG (pfx ++ sfx,peg_nt
           ((INL:MMLnonT->MMLnonT+num) nEapp) I) (peg_Success sfx
           [apt] eo)))`,
  CHEAT_TAC);;

let peg_respects_firstSets' = prove
 (`peg_eval cmlPEG ((t,l) :: rest,peg_nt N I) (peg_Success sfx res eo)
  /\
   peg_nt N I IN Gexprs cmlPEG /\ ~(peg0 cmlPEG (peg_nt N I)) ==>
   t IN firstSet cmlG [grammar_NT N]`,
  CHEAT_TAC);;

let nUQConstructorName_input_monotone = prove
 (`peg_eval cmlPEG (i0,peg_nt ((INL:MMLnonT->MMLnonT+num)
  nUQConstructorName) I) (peg_Success i r eo) ==>
   peg_eval cmlPEG (i0 ++ sfx,peg_nt ((INL:MMLnonT->MMLnonT+num)
     nUQConstructorName) I)
     (peg_Success (i ++ sfx) r eo)`,
  CHEAT_TAC);;

let nConstructorName_input_monotone = prove
 (`peg_eval cmlPEG (i0,peg_nt ((INL:MMLnonT->MMLnonT+num)
  nConstructorName) I) (peg_Success i r eo) ==>
   peg_eval cmlPEG (i0 ++ sfx,peg_nt ((INL:MMLnonT->MMLnonT+num)
     nConstructorName) I)
     (peg_Success (i ++ sfx) r eo)`,
  CHEAT_TAC);;

(* HOL4 pegCompleteScript.sml:1030-1032: a theorem that HOL4 states
   as the value of an ML expression: peg_eval_NT_NONE *)

let nConstructorName_NONE_input_monotone = prove
 (`peg_eval cmlPEG ((tk,l) :: i,peg_nt ((INL:MMLnonT->MMLnonT+num)
  nConstructorName) I) (peg_Failure fl fe) ==>
   peg_eval cmlPEG
            ((tk,l) :: (i ++ sfx),peg_nt ((INL:MMLnonT->MMLnonT+num)
              nConstructorName) I)
            (peg_Failure fl fe)`,
  CHEAT_TAC);;

let nV_input_monotone = prove
 (`peg_eval cmlPEG (i0,peg_nt ((INL:MMLnonT->MMLnonT+num) nV) I)
  (peg_Success i r eo) ==>
   peg_eval cmlPEG (i0 ++ sfx,peg_nt ((INL:MMLnonT->MMLnonT+num)
     nV) I) (peg_Success (i ++ sfx) r eo)`,
  CHEAT_TAC);;

let nV_NONE_input_monotone = prove
 (`peg_eval cmlPEG ((tk,l) :: i0,peg_nt ((INL:MMLnonT->MMLnonT+num) nV)
  I) (peg_Failure fl fe) ==>
   peg_eval cmlPEG ((tk,l) :: (i0 ++ sfx),peg_nt
     ((INL:MMLnonT->MMLnonT+num) nV) I) (peg_Failure fl fe)`,
  CHEAT_TAC);;

let nOpID_input_monotone = prove
 (`peg_eval cmlPEG (i0,peg_nt ((INL:MMLnonT->MMLnonT+num) nOpID) I)
  (peg_Success i r eo) ==>
   peg_eval cmlPEG (i0 ++ sfx,peg_nt ((INL:MMLnonT->MMLnonT+num)
     nOpID) I) (peg_Success (i ++ sfx) r eo)`,
  CHEAT_TAC);;

let nUQTyOp_input_monotone = prove
 (`peg_eval cmlPEG (i0,peg_nt ((INL:MMLnonT->MMLnonT+num) nUQTyOp) I)
  (peg_Success i r eo) ==>
   peg_eval cmlPEG (i0 ++ sfx,peg_nt ((INL:MMLnonT->MMLnonT+num)
     nUQTyOp) I) (peg_Success (i ++ sfx) r eo)`,
  CHEAT_TAC);;

(* HOL4 pegCompleteScript.sml:1085-1086: a theorem that HOL4 states
   as the value of an ML expression: nUQTyOp_input_monotone' *)

let nTyOp_input_monotone = prove
 (`peg_eval cmlPEG (i0,peg_nt ((INL:MMLnonT->MMLnonT+num) nTyOp) I)
  (peg_Success i r eo) ==>
   peg_eval cmlPEG (i0 ++ sfx,peg_nt ((INL:MMLnonT->MMLnonT+num)
     nTyOp) I) (peg_Success (i ++ sfx) r eo)`,
  CHEAT_TAC);;

(* HOL4 pegCompleteScript.sml:1102-1103: a theorem that HOL4 states
   as the value of an ML expression: nTyOp_input_monotone' *)

let nTyOplist_input_monotone = prove
 (`!pts res i0 i sfx.
     peg_eval_list cmlPEG (i0,peg_nt ((INL:MMLnonT->MMLnonT+num)
       nTyOp) I) (i,pts,res) /\
     (i = [] /\ ~(sfx = []) ==> FST (HD sfx) IN pegComplete_stoppers
       nDType) ==>
     (?res'.
       peg_eval_list cmlPEG (i0 ++ sfx,peg_nt
         ((INL:MMLnonT->MMLnonT+num) nTyOp) I) (i ++ sfx,pts,res'))`,
  CHEAT_TAC);;

(* [local,simp] *)
let peg_eval_TyOp_LparT = prove
 (`peg_eval cmlPEG ((tokens_LparT,loc) :: i0,peg_nt
  ((INL:MMLnonT->MMLnonT+num) nTyOp) I) (peg_Success i r eo) <=> F`,
  CHEAT_TAC);;

(* HOL4 pegCompleteScript.sml:1137: the overload RANK, which the port
   expands *)

(* Type_input_monotone *)
let type_input_monotone = prove
 (`!N i0 i r sfx eo.
     N IN {nTypeList2,nTypeList1,nType,nPType,nDType,nTbase} /\
     (~(i = []) ==> FST (HD i) IN pegComplete_stoppers N) /\
     (i = [] /\ ~(sfx = []) ==> FST (HD sfx) IN pegComplete_stoppers
       N) /\
     peg_eval cmlPEG (i0,peg_nt ((INL:MMLnonT->MMLnonT+num) N) I)
       (peg_Success i r eo) ==>
     peg_eval cmlPEG (i0 ++ sfx,peg_nt ((INL:MMLnonT->MMLnonT+num)
       N) I) (peg_Success (i ++ sfx) r eo)`,
  CHEAT_TAC);;

(* [local] *)
let Pattern_nV_nCons = prove
 (`peg_eval cmlPEG (i,peg_nt ((INL:MMLnonT->MMLnonT+num) nV) I)
  (peg_Success j r eo) /\
   (~(j = []) ==> FST (HD j) IN pegComplete_stoppers nPcons) ==>
   (?r1 eo1.
     peg_eval cmlPEG (i,peg_nt ((INL:MMLnonT->MMLnonT+num) nPcons)
       I) (peg_Success j r1 eo1))`,
  CHEAT_TAC);;

(* Pattern_input_monotone0[local] *)
let pattern_input_monotone0 = prove
 (`!N i0 rlist b i r l sfx eo res.
     (N IN
       {nPbase,nPtuple,nPattern,nPapp,nPatternList,nPas,nPcons,nV} /\ ~b
       /\
      (~(i = []) ==> FST (HD i) IN pegComplete_stoppers N) /\
      (i = [] /\ ~(sfx = []) ==> FST (HD sfx) IN pegComplete_stoppers
        N) /\
      peg_eval cmlPEG (i0,peg_nt ((INL:MMLnonT->MMLnonT+num) N) I)
        (peg_Success i r eo) ==>
      peg_eval cmlPEG (i0 ++ sfx,peg_nt ((INL:MMLnonT->MMLnonT+num)
        N) I) (peg_Success (i ++ sfx) r eo)) /\
     (N = nPbase /\ b /\
      (~(i = []) ==> ~(FST (HD i) IN firstSet cmlG [(\nt'. grammar_NT
        ((INL:MMLnonT->MMLnonT+num) nt')) nPbase])) /\
      (i = [] /\ ~(sfx = []) ==> ~(FST (HD sfx) IN firstSet cmlG
        [(\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nPbase]))
        /\
      peg_eval_list cmlPEG (i0,peg_nt ((INL:MMLnonT->MMLnonT+num) N)
        I) (i,rlist,l,res) ==>
      (?res'.
        peg_eval_list cmlPEG (i0 ++ sfx,peg_nt
          ((INL:MMLnonT->MMLnonT+num) N) I) (i ++ sfx,rlist,res')))`,
  CHEAT_TAC);;

(* HOL4 pegCompleteScript.sml:1645-1646: a theorem that HOL4 states
   as the value of an ML expression: Pattern_input_monotone *)

let extend_Pbase_list = prove
 (`!results pfx sfx sfx' result e eo.
     peg_eval_list cmlPEG (pfx,peg_nt ((INL:MMLnonT->MMLnonT+num)
       nPbase) I) ([],results,e) /\
     peg_eval cmlPEG (sfx,peg_nt ((INL:MMLnonT->MMLnonT+num) nPbase)
       I) (peg_Success sfx' result eo) /\
     (~(sfx' = []) ==> ~(FST (HD sfx') IN firstSet cmlG [(\nt'.
       grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) nPbase])) ==>
     (?e'. peg_eval_list cmlPEG (pfx ++ sfx,peg_nt
       ((INL:MMLnonT->MMLnonT+num) nPbase) I)
                        (sfx',results ++ [result],e'))`,
  CHEAT_TAC);;

let papp_complete = prove
 (`(!pt' pfx' N sfx'.
      LENGTH pfx' < LENGTH master /\ valid_lptree cmlG pt' /\
      (INL:MMLnonT->MMLnonT+num) N IN FDOM (rules cmlPEG) /\
        ptree_head pt' = (\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
        nt')) N /\
      real_fringe pt' = MAP
        ((grammar_TOK:tokens_token->(tokens_token
        ,MMLnonT)grammar_symbol) ## I) pfx' /\
      (~(sfx' = []) ==> FST (HD sfx') IN pegComplete_stoppers N) ==>
      (?eo.
        peg_eval cmlPEG (pfx' ++ sfx',peg_nt
          ((INL:MMLnonT->MMLnonT+num) N) I) (peg_Success sfx' [pt']
          eo))) /\
   (!pt' sfx'.
      valid_lptree cmlG pt' /\ ptree_head pt' = (\nt'. grammar_NT
        ((INL:MMLnonT->MMLnonT+num) nt')) nConstructorName /\
      real_fringe pt' = MAP
        ((grammar_TOK:tokens_token->(tokens_token
        ,MMLnonT)grammar_symbol) ## I) master ==>
      (?eo.
        peg_eval cmlPEG (master ++ sfx',peg_nt
          ((INL:MMLnonT->MMLnonT+num) nConstructorName) I)
                 (peg_Success sfx' [pt'] eo))) ==>
   (!pfx accpt sfx.
     pfx <<= master /\
     valid_lptree cmlG accpt /\ ptree_head accpt = (\nt'. grammar_NT
       ((INL:MMLnonT->MMLnonT+num) nt')) nPConApp /\
     real_fringe accpt = MAP
       ((grammar_TOK:tokens_token->(tokens_token,MMLnonT)grammar_symbol)
       ## I) pfx /\
     (~(sfx = []) ==> FST (HD sfx) IN pegComplete_stoppers nPConApp)
       ==>
     (?cpt i bpts eo e.
        peg_eval cmlPEG
                 (pfx ++ sfx,peg_nt ((INL:MMLnonT->MMLnonT+num)
                   nConstructorName) I)
                 (peg_Success i [cpt] eo) /\
        peg_eval_list cmlPEG (i,peg_nt ((INL:MMLnonT->MMLnonT+num)
          nPbase) I) (sfx,bpts,e) /\
        accpt =
        FOLDL (\pcpt bpt. bindNT0 nPConApp [pcpt; bpt])
              (mkNd ((INL:MMLnonT->MMLnonT+num) nPConApp) [cpt])
                (FLAT bpts)))`,
  CHEAT_TAC);;

(* [simp] *)
let leftmost_mkNd_DType = prove
 (`leftmost (mkNd ((INL:MMLnonT->MMLnonT+num) nDType) (c :: cs)) =
  leftmost c`,
  CHEAT_TAC);;

(* [simp] *)
let leftmost_mkNd_Tbase = prove
 (`leftmost (mkNd ((INL:MMLnonT->MMLnonT+num) nTbase) (x :: xs)) = x`,
  CHEAT_TAC);;

let leftmost_FOLDL = prove
 (`leftmost (FOLDL (\a b. mkNd ((INL:MMLnonT->MMLnonT+num) nDType) [a;
  b]) acc args) =
    leftmost acc`,
  CHEAT_TAC);;

(* [simp] *)
let left_insert2_mkNd = prove
 (`left_insert2 bpt (mkNd ((INL:MMLnonT->MMLnonT+num) nDType) [mkNd n
  [sub]]) =
   mkNd ((INL:MMLnonT->MMLnonT+num) nDType) [mkNd
     ((INL:MMLnonT->MMLnonT+num) nDType) [bpt]; sub]`,
  CHEAT_TAC);;

let dtype_complete = prove
 (`(!pt' pfx' sfx' N.
      LENGTH pfx' < LENGTH master /\ valid_lptree cmlG pt' /\
      (INL:MMLnonT->MMLnonT+num) N IN FDOM (rules cmlPEG) /\
      ptree_head pt' = (\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
        nt')) N /\ real_fringe pt' = MAP
        ((grammar_TOK:tokens_token->(tokens_token
        ,MMLnonT)grammar_symbol) ## I) pfx' /\
      (~(sfx' = []) ==> FST (HD sfx') IN pegComplete_stoppers N) ==>
      (?eo.
        peg_eval cmlPEG (pfx' ++ sfx',peg_nt
          ((INL:MMLnonT->MMLnonT+num) N) I) (peg_Success sfx' [pt']
          eo))) /\
   (!pt' sfx'.
      valid_lptree cmlG pt' /\ ptree_head pt' = (\nt'. grammar_NT
        ((INL:MMLnonT->MMLnonT+num) nt')) nTbase /\
      real_fringe pt' = MAP
        ((grammar_TOK:tokens_token->(tokens_token
        ,MMLnonT)grammar_symbol) ## I) master /\
      (~(sfx' = []) ==> FST (HD sfx') IN pegComplete_stoppers nEbase)
        ==>
      (?eo.
        peg_eval cmlPEG (master ++ sfx',peg_nt
          ((INL:MMLnonT->MMLnonT+num) nTbase) I)
                 (peg_Success sfx' [pt'] eo))) ==>
   (!pfx apt sfx.
     IS_SUFFIX master pfx /\ valid_lptree cmlG apt /\
     ptree_head apt = (\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
       nt')) nDType /\ real_fringe apt = MAP
       ((grammar_TOK:tokens_token->(tokens_token,MMLnonT)grammar_symbol)
       ## I) pfx /\
     (~(sfx = []) ==> FST (HD sfx) IN pegComplete_stoppers nDType)
       ==>
     (?eo.
       peg_eval cmlPEG (pfx ++ sfx,peg_nt
         ((INL:MMLnonT->MMLnonT+num) nDType) I) (peg_Success sfx [apt]
         eo)))`,
  CHEAT_TAC);;

(* could generalise this slightly: allowing for nullable seps, but this would
   require a more complicated condition on the sfx, something like
     (sfx ≠ [] ∧ ¬nullable cmlG [SEP] ⇒ HD sfx ∉ firstSet cmlG [SEP]) ∧
     (sfx ≠ [] ∧ nullable cmlG [SEP] ⇒ HD sfx ∉ firstSet cmlG [C])
   and I can't be bothered with that right now. *)

let peg_linfix_complete = prove
 (`(!n. SEP = grammar_NT n ==>
        (?nn. n = (INL:MMLnonT->MMLnonT+num) nn /\ peg_nt
          ((INL:MMLnonT->MMLnonT+num) nn) I IN Gexprs cmlPEG /\
             pegComplete_stoppers nn = UNIV)) /\
   (!n. C = grammar_NT n ==> (?nn. n = (INL:MMLnonT->MMLnonT+num)
     nn)) /\
   (!t. t IN firstSet cmlG [SEP] ==> ~(t IN pegComplete_stoppers P))
     /\
   (!n. C = grammar_NT ((INL:MMLnonT->MMLnonT+num) n) ==>
        (!t. t IN firstSet cmlG [SEP] ==> t IN pegComplete_stoppers
          n) /\
        (!t. t IN pegComplete_stoppers P ==> t IN
          pegComplete_stoppers n)) /\
   ~(peg0 cmlPEG (sym2peg C)) /\ ~(nullable cmlG [C]) /\
   ~(peg0 cmlPEG (sym2peg SEP)) /\ ~(nullable cmlG [SEP]) /\ FAPPLY
     (rules
   cmlG) ((INL:MMLnonT->MMLnonT+num) P) = {[grammar_NT
     ((INL:MMLnonT->MMLnonT+num) P); SEP; C],[C]} /\
   (!pt pfx0 sfx.
      LENGTH pfx0 < LENGTH master /\
      (!n. ptree_head pt = grammar_NT ((INL:MMLnonT->MMLnonT+num) n)
        /\ ~(sfx = []) ==>
           FST (HD sfx) IN pegComplete_stoppers n) /\
      valid_lptree cmlG pt /\ ptree_head pt IN {SEP,C} /\
      real_fringe pt = MAP (grammar_TOK ## I) pfx0 ==>
      (?eo.
        peg_eval cmlPEG (pfx0 ++ sfx,sym2peg (ptree_head pt))
                 (peg_Success sfx [pt] eo))) /\
   (!pt sfx.
      valid_lptree cmlG pt /\ ptree_head pt = C /\
      (!n. C = grammar_NT ((INL:MMLnonT->MMLnonT+num) n) /\ ~(sfx =
        []) ==> FST (HD sfx) IN pegComplete_stoppers n) /\
      real_fringe pt = MAP (grammar_TOK ## I) master ==>
      (?eo.
        peg_eval cmlPEG (master ++ sfx,sym2peg C) (peg_Success sfx
          [pt] eo))) ==>
   (!pfx pt sfx.
    IS_SUFFIX master pfx /\
    valid_lptree cmlG pt /\ ptree_head pt = grammar_NT
      ((INL:MMLnonT->MMLnonT+num) P) /\
    (~(sfx = []) ==> FST (HD sfx) IN pegComplete_stoppers P) /\
    real_fringe pt = MAP (grammar_TOK ## I) pfx ==>
   (?eo.
     peg_eval cmlPEG (pfx ++ sfx,
                      peg_linfix ((INL:MMLnonT->MMLnonT+num) P)
                        (sym2peg C) (sym2peg SEP))
              (peg_Success sfx [pt] eo)))`,
  CHEAT_TAC);;

(* HOL4 pegCompleteScript.sml:2024-2026: a proof *)

(* HOL4 pegCompleteScript.sml:2028: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:2030: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:2032-2036: ML code, not ported *)

(* HOL4 pegCompleteScript.sml:2038-2041: a proof *)

(* [simp] *)
let pmap_EQ = prove
 (`(x,y) = (f ## g) p <=> (?x0 y0. p = (x0,y0) /\ x = f x0 /\ y = g
  y0)`,
  CHEAT_TAC);;

let ptPapply0_FOLDL = prove
 (`!l a pt.
     ptPapply0 a (l ++ [pt]) =
     [bindNT0 nPapp [FOLDL (\pcpt bpt. bindNT0 nPConApp [pcpt; bpt])
       a l;
                     pt]]`,
  CHEAT_TAC);;

(* [simp] *)
let FST_EQ = prove
 (`FST p = x <=> (?y. p = (x,y))`,
  CHEAT_TAC);;

(* [simp] *)
let FST_NEQ = prove
 (`~(FST p = x) <=> (?x0 y. p = (x0,y) /\ ~(x0 = x))`,
  CHEAT_TAC);;

(* [simp] *)
let ALL_FST_NEQ = prove
 (`(!y. ~(p = (x,y))) <=> (?x0 y. p = (x0,y) /\ ~(x0 = x))`,
  CHEAT_TAC);;

let FST_IN = prove
 (`FST p IN s <=> (?tk l. p = (tk,l) /\ tk IN s)`,
  CHEAT_TAC);;

let FST_NOTIN = prove
 (`~(FST p IN s) <=> (?tk l. p = (tk,l) /\ ~(tk IN s))`,
  CHEAT_TAC);;

(* HOL4 pegCompleteScript.sml:2087: the ML values that the
   definitions below antiquote *)

let completeness = prove
 (`!pt N pfx sfx.
     valid_lptree cmlG pt /\ ptree_head pt = grammar_NT
       ((INL:MMLnonT->MMLnonT+num) N) /\
     (INL:MMLnonT->MMLnonT+num) N IN FDOM (rules cmlPEG) /\
     (~(sfx = []) ==> FST (HD sfx) IN pegComplete_stoppers N) /\
     real_fringe pt = MAP (grammar_TOK ## I) pfx ==>
     (?eo.
       peg_eval cmlPEG (pfx ++ sfx,peg_nt
         ((INL:MMLnonT->MMLnonT+num) N) I) (peg_Success sfx [pt] eo))`,
  CHEAT_TAC);;

let cmlG_unambiguous = prove
 (`valid_lptree cmlG pt1 /\ ptree_head pt1 = grammar_NT
  ((INL:MMLnonT->MMLnonT+num) N) /\
   valid_lptree cmlG pt2 /\ ptree_head pt2 = grammar_NT
     ((INL:MMLnonT->MMLnonT+num) N) /\
   (INL:MMLnonT->MMLnonT+num) N IN FDOM (rules cmlPEG) /\
   // e.g., nTopLevelDecs
   real_fringe pt2 = real_fringe pt1 /\
   (!s. s IN set_of_list (ptree_fringe pt1) ==> (?t. s = grammar_TOK
     t)) ==>
     pt1 = pt2`,
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["C";
   "sub"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
