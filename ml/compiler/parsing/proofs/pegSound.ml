(* ======================================================== *)
(*  pegSound: ported from HOL4's
    compiler/parsing/proofs/pegSoundScript.sml
    A proof theory, with 1 definition and 42 theorems.  Needed by
    compilerProof.ml and pegComplete.ml.  *)
(* ======================================================== *)

(*
  Soundness proof for the parser. If the parser returns a parse tree,
  then it is valid w.r.t. the specification grammar.
*)

needs "compiler/parsing/cmlPEG.ml";;
needs "lib/NTproperties.ml";;
needs "lib/grammar.ml";;
needs "lib/peg.ml";;
needs "semantics/gram.ml";;
needs "semantics/proofs/gramProps.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "pegSound"
  ["cmlPEG"; "gram"; "gramProps"];;

(* Set up ML bindings *)
(* HOL4 pegSoundScript.sml:12: ML code, not ported *)

(* HOL4 pegSoundScript.sml:14-15: ML code, not ported *)
(* HOL4 pegSoundScript.sml:18-19: the overload choicel, which the
   port expands *)

let Success_COND_Failure = prove
 (`~(peg_Success i r opt = (if P then peg_Failure fl1 fe1 else
  peg_Failure fl2 fe2))`,
  CHEAT_TAC);;
add_simp Success_COND_Failure;;

let peg_eval_choicel_NIL = prove
 (`peg_eval G (i0,cmlPEG_choicel []) x <=> x = peg_Failure (sloc i0)
  (peg_notFAIL G)`,
  CHEAT_TAC);;
add_simp peg_eval_choicel_NIL;;

let peg_TF = prove
 (`(?i' r eopt. peg_eval G (i,e) (peg_Success i' r eopt)) ==>
   ~(peg_eval G (i,e) (peg_Failure fl fe))`,
  CHEAT_TAC);;

let peg_FT = prove
 (`(?fl fe. peg_eval G (i,e) (peg_Failure fl fe)) ==>
   ~(peg_eval G (i,e) (peg_Success i' r eopt))`,
  CHEAT_TAC);;

let peg_eval_choicel_CONS = prove
 (`!x. peg_eval G (i0,cmlPEG_choicel (CONS h t)) x <=>
         (?i r eopt.
            peg_eval G (i0,h) (peg_Success i r eopt) /\ x =
              peg_Success i r eopt) \/
         (?res2 fl1 fe1 i r eopt fl2 fe2.
            peg_eval G (i0,h) (peg_Failure fl1 fe1) /\
            peg_eval G (i0,cmlPEG_choicel t) res2 /\
            (res2 = peg_Success i r eopt /\
             x = peg_Success i r (optmax MAXerr (SOME (fl1,fe1))
               eopt) \/
             res2 = peg_Failure fl2 fe2 /\
             x = UNCURRY peg_Failure (MAXerr (fl1,fe1) (fl2,fe2))))`,
  CHEAT_TAC);;

let peg_eval_seql_NIL = prove
 (`peg_eval G (i0,seql [] f) x <=> x = peg_Success i0 (f []) NONE`,
  CHEAT_TAC);;
add_simp peg_eval_seql_NIL;;

let peg_eval_try = prove
 (`!x. peg_eval G (i0,cmlPEG_try s) x <=>
         (?fl fe. peg_eval G (i0,s) (peg_Failure fl fe) /\
                  x = peg_Success i0 [] (optmax MAXerr (SOME (fl,fe))
                    NONE)) \/
         (?i r eo. peg_eval G (i0,s) (peg_Success i r eo) /\ x =
           peg_Success i r eo)`,
  CHEAT_TAC);;

let peg_eval_seql_CONS = prove
 (`!x. peg_eval G (i0,seql (CONS h t) f) x <=>
         (?fl fe. peg_eval G (i0,h) (peg_Failure fl fe) /\ x =
           peg_Failure fl fe) \/
         (?rh i1 fl fe eopt.
            peg_eval G (i0,h) (peg_Success i1 rh eopt) /\
            peg_eval G (i1,seql t I) (peg_Failure fl fe) /\ x =
              peg_Failure fl fe) \/
         (?rh i1 i rt eopt1 eopt2.
            peg_eval G (i0,h) (peg_Success i1 rh eopt1) /\
            peg_eval G (i1,seql t I) (peg_Success i rt eopt2) /\
            x = peg_Success i (f (APPEND rh rt)) eopt2)`,
  CHEAT_TAC);;

(* HOL4 pegSoundScript.sml:100-107: a theorem that HOL4 states as the
   value of an ML expression: peg_eval_choicel_SING *)

let not_peg0_LENGTH_decreases = prove
 (`~(peg0 G s) ==> peg_eval G (i0,s) (peg_Success i r eo) ==> LENGTH i
  < LENGTH i0`,
  CHEAT_TAC);;

(* HOL4 pegSoundScript.sml:115-118: ML code, not ported *)

let peg_eval_tokSymP = prove
 (`peg_eval G (i0,tokSymP P) (peg_Success i r eo) <=>
   (?h s. FST h = tokens_SymbolT s /\ P s /\ i0 = CONS h i /\ r =
     mktokLf h /\ eo = NONE)`,
  CHEAT_TAC);;
add_simp peg_eval_tokSymP;;

(* [local] *)
let FADISJ_EQ_IMP' = prove
 (`((!x. P x) \/ Q <=> (!x. ~(P x) ==> Q)) /\
   ((Q \/ (!x. P x)) <=> (!x. ~(P x) ==> Q))`,
  (MESON_TAC[]));;
add_simp FADISJ_EQ_IMP';;

let peg_eval_TypeDec_wrongtok = prove
 (`~(FST tk = tokens_DatatypeT) ==>
      ~(peg_eval cmlPEG (CONS tk i,peg_nt
        ((INL:MMLnonT->MMLnonT+num) nTypeDec) f) (peg_Success i' r
        eo))`,
  CHEAT_TAC);;

let peg_eval_TypeAbbrevDec_wrongtok = prove
 (`~(FST tk = tokens_TypeT) ==>
      ~(peg_eval cmlPEG (CONS tk i,peg_nt
        ((INL:MMLnonT->MMLnonT+num) nTypeAbbrevDec) f) (peg_Success i'
        r eo))`,
  CHEAT_TAC);;

let peg_eval_Structure_wrongtok = prove
 (`~(FST tk = tokens_StructureT) ==>
     ~(peg_eval cmlPEG (CONS tk i,peg_nt
       ((INL:MMLnonT->MMLnonT+num) nStructure) f) (peg_Success i' r
       e0))`,
  CHEAT_TAC);;


let peg_eval_LetDec_wrongtok = prove
 (`FST tk = tokens_SemicolonT ==>
   ~(peg_eval cmlPEG (CONS tk i,peg_nt ((INL:MMLnonT->MMLnonT+num)
     nLetDec) f) (peg_Success i' r eo))`,
  CHEAT_TAC);;

let peg_eval_nUQConstructor_wrongtok = prove
 (`(!s. ~(FST t = tokens_AlphaT s)) ==>
    ~(peg_eval cmlPEG (CONS t i,peg_nt ((INL:MMLnonT->MMLnonT+num)
      nUQConstructorName) f) (peg_Success i' r eo))`,
  CHEAT_TAC);;

let peg_eval_nConstructor_wrongtok = prove
 (`(!s. ~(FST t = tokens_AlphaT s)) /\ (!s1 s2. ~(FST t = tokens_LongidT
  s1 s2)) ==>
   ~(peg_eval cmlPEG (CONS t i,peg_nt ((INL:MMLnonT->MMLnonT+num)
     nConstructorName) f) (peg_Success i' r eo))`,
  CHEAT_TAC);;

let peg_eval_nV_wrongtok = prove
 (`(!s. ~(FST t = tokens_AlphaT s)) /\ (!s. ~(FST t = tokens_SymbolT s))
  ==>
    ~(peg_eval cmlPEG (CONS t i,peg_nt ((INL:MMLnonT->MMLnonT+num)
      nV) f) (peg_Success i' r eo))`,
  CHEAT_TAC);;

let peg_eval_nFQV_wrongtok = prove
 (`(!s. ~(FST t = tokens_AlphaT s)) /\ (!s. ~(FST t = tokens_SymbolT s))
  /\
   (!s1 s2. ~(FST t = tokens_LongidT s1 s2)) ==>
   ~(peg_eval cmlPEG (CONS t i,peg_nt ((INL:MMLnonT->MMLnonT+num)
     nFQV) f) (peg_Success i' r eo))`,
  CHEAT_TAC);;

let peg_eval_rpt_never_NONE = prove
 (`~(peg_eval G (i,peg_rpt sym f) (peg_Failure fl fe))`,
  CHEAT_TAC);;
add_simp peg_eval_rpt_never_NONE;;

let pegsym_to_sym_def = new_definition
  `pegsym_to_sym x1 =
        match x1 with
          peg_tok P f -> (if f = mktokLf then
            {(grammar_TOK:tokens_token->(tokens_token
            ,MMLnonT)grammar_symbol) t | P t} else {})
        | (peg_nt N f) -> {grammar_NT N}
        | _1 -> {}`;;

let valid_ptree_mkNd = prove
 (`valid_ptree G (mkNd N subs) <=>
     N IN FDOM (peg_rules G) /\ MAP ptree_head subs IN FAPPLY
       (peg_rules G) N /\
     (!pt. MEM pt subs ==> valid_ptree G pt)`,
  (REWRITE_TAC[mkNd_def; valid_ptree_def; IN_SET_OF_LIST]));;
add_simp valid_ptree_mkNd;;

let ptree_head_mkNd = prove
 (`ptree_head (mkNd N subs) = grammar_NT N`,
  (REWRITE_TAC[mkNd_def; ptree_head_def]));;
add_simp ptree_head_mkNd;;

(* HOL4 pegSoundScript.sml:233: ML code, not ported *)
let ptree_list_loc_SING = prove
 (`ptree_list_loc [pt] = ptree_loc pt`,
  CHEAT_TAC);;
add_simp ptree_list_loc_SING;;

let ptree_fringemkNd = prove
 (`ptree_fringe (mkNd N subs) = FLAT (MAP ptree_fringe subs)`,
  (REWRITE_TAC[mkNd_def; ptree_fringe_def]));;
add_simp ptree_fringemkNd;;

let valid_locs_mkNd = prove
 (`valid_locs (mkNd N subs) <=> (!pt. MEM pt subs ==> valid_locs pt)`,
  (REWRITE_TAC[mkNd_def; valid_locs_def; ptree_list_loc_def]));;
add_simp valid_locs_mkNd;;

let rfringe_length_not_nullable = prove
 (`!G s. ~(nullable G [s]) ==>
         (!pt. ptree_head pt = s ==> valid_lptree G pt ==>
              0 < LENGTH (real_fringe pt))`,
  CHEAT_TAC);;

let valid_lptree_mkNd = prove
 (`valid_lptree G (mkNd n children) <=>
      n IN FDOM (peg_rules G) /\ MAP ptree_head children IN FAPPLY
        (peg_rules G) n /\
      (!pt. MEM pt children ==> valid_lptree G pt)`,
  CHEAT_TAC);;
add_simp valid_lptree_mkNd;;

let real_fringe_mkNd = prove
 (`real_fringe (mkNd n subs) = FLAT (MAP real_fringe subs)`,
  (REWRITE_TAC[mkNd_def; real_fringe_def]));;
add_simp real_fringe_mkNd;;

let ptree_head_NT_mkNd = prove
 (`ptree_head pt = (\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt')) n
  /\ valid_lptree cmlG pt /\
   real_fringe pt = MAP
     ((grammar_TOK:tokens_token->(tokens_token,MMLnonT)grammar_symbol)
     ## I) pf ==>
   (?subs. pt = mkNd ((INL:MMLnonT->MMLnonT+num) n) subs)`,
  CHEAT_TAC);;

let mkNd_11 = prove
 (`mkNd n1 sub1 = mkNd n2 sub2 <=> n1 = n2 /\ sub1 = sub2`,
  CHEAT_TAC);;
add_simp mkNd_11;;

let peg_linfix_correct_lemma = prove
 (`!UpperN sym sepsym i0 i pts eo.
      peg_eval cmlPEG (i0,peg_linfix UpperN sym sepsym) (peg_Success
        i pts eo) ==>
      (!i0' i pts s eo.
         s IN {sym,sepsym} ==>
         LENGTH i0' < LENGTH i0 ==>
         peg_eval cmlPEG (i0',s) (peg_Success i pts eo) ==>
         (?pt. pts = [pt] /\ ptree_head pt IN pegsym_to_sym s /\
              valid_lptree cmlG pt /\
              MAP
                ((grammar_TOK:tokens_token->(tokens_token
                ,MMLnonT)grammar_symbol) ## I) i0' = APPEND (real_fringe
                pt) (MAP
                ((grammar_TOK:tokens_token->(tokens_token
                ,MMLnonT)grammar_symbol) ## I) i))) /\
      (!i pts s eo.
         s IN {sym,sepsym} ==>
         peg_eval cmlPEG (i0,s) (peg_Success i pts eo) ==>
         (?pt. pts = [pt] /\ ptree_head pt IN pegsym_to_sym s /\
              valid_lptree cmlG pt /\
              MAP
                ((grammar_TOK:tokens_token->(tokens_token
                ,MMLnonT)grammar_symbol) ## I) i0 = APPEND (real_fringe
                pt) (MAP
                ((grammar_TOK:tokens_token->(tokens_token
                ,MMLnonT)grammar_symbol) ## I) i))) /\
      ~(peg0 cmlPEG sym) /\
      UpperN IN FDOM (peg_rules cmlG) /\
      {[gsym] | gsym IN pegsym_to_sym sym} SUBSET FAPPLY (peg_rules
        cmlG) UpperN /\
      {[grammar_NT UpperN; gsep; gsym] |
          gsep IN pegsym_to_sym sepsym /\ gsym IN pegsym_to_sym sym}
            SUBSET FAPPLY (peg_rules
        cmlG) UpperN ==>
      (?pt. pts = [pt] /\ ptree_head pt = grammar_NT UpperN /\
        valid_lptree cmlG pt /\
           MAP
             ((grammar_TOK:tokens_token->(tokens_token
             ,MMLnonT)grammar_symbol) ## I) i0 = APPEND (real_fringe
             pt) (MAP
             ((grammar_TOK:tokens_token->(tokens_token
             ,MMLnonT)grammar_symbol) ## I) i))`,
  CHEAT_TAC);;

let length_no_greater = prove
 (`peg_eval G (i0,sym) (peg_Success i r eo) ==> LENGTH i <= LENGTH i0`,
  CHEAT_TAC);;

let MAP_TK_11 = prove
 (`MAP
  (grammar_TOK:tokens_token->(tokens_token,MMLnonT)grammar_symbol) x =
  MAP (grammar_TOK:tokens_token->(tokens_token,MMLnonT)grammar_symbol)
  y <=> x = y`,
  CHEAT_TAC);;
add_simp MAP_TK_11;;

let peg_eval_nTyOp_wrongtok = prove
 (`FST tk = tokens_LparT ==>
   ~(peg_eval cmlPEG (CONS tk i,peg_nt ((INL:MMLnonT->MMLnonT+num)
     nTyOp) f) (peg_Success i' r eo))`,
  CHEAT_TAC);;

let peg_EbaseParen_sound = prove
 (`!i0 i pts eo.
      peg_eval cmlPEG (i0,peg_EbaseParen) (peg_Success i pts eo) ==>
      (!i0' N i pts eo.
        LENGTH i0' < LENGTH i0 /\
        peg_eval cmlPEG (i0',peg_nt ((INL:MMLnonT->MMLnonT+num) N) I)
          (peg_Success i pts eo) ==>
        (?pt.
           pts = [pt] /\ ptree_head pt = grammar_NT
             ((INL:MMLnonT->MMLnonT+num) N) /\
           valid_lptree cmlG pt /\
           MAP (grammar_TOK ## I) i0' = APPEND (real_fringe pt) (MAP
             (grammar_TOK ## I) i))) ==>
      (?pt.
        pts = [pt] /\ ptree_head pt = grammar_NT
          ((INL:MMLnonT->MMLnonT+num) nEbase) /\
        valid_lptree cmlG pt /\
        MAP (grammar_TOK ## I) i0 = APPEND (real_fringe pt) (MAP
          (grammar_TOK ## I) i))`,
  CHEAT_TAC);;

(* [local] *)
let PAIR_MAP_I = prove
 (`(f ## I) x = (f (FST x),SND x) <=> T`,
  CHEAT_TAC);;
add_simp PAIR_MAP_I;;

(* HOL4 pegSoundScript.sml:443: a theorem that HOL4 states as the
   value of an ML expression: bindNT0_lemma *)

(* left recursive rules in the grammar turn into calls to rpt in the PEG,
   and this in turn requires inductions *)
let ptPapply_lemma = prove
 (`!limit'.
     (!i0 i pts eo.
       LENGTH i0 < limit' ==>
       peg_eval cmlPEG (i0,peg_nt ((INL:MMLnonT->MMLnonT+num) nPbase)
         I) (peg_Success i pts eo) ==>
       (?pt. pts = [pt] /\ ptree_head pt = (\nt'. grammar_NT
         ((INL:MMLnonT->MMLnonT+num) nt')) nPbase /\ valid_lptree cmlG
         pt /\
            MAP
              ((grammar_TOK:tokens_token->(tokens_token
              ,MMLnonT)grammar_symbol) ## I) i0 = APPEND (real_fringe
              pt) (MAP
              ((grammar_TOK:tokens_token->(tokens_token
              ,MMLnonT)grammar_symbol) ## I) i))) ==>
     (!ptlist pt0 acc i0 err.
       peg_eval_list cmlPEG (i0,peg_nt ((INL:MMLnonT->MMLnonT+num)
         nPbase) I) (i,ptlist,err) /\
       ptree_head pt0 = (\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
         nt')) nPbase /\ valid_lptree cmlG pt0 /\
       ptree_head acc = (\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num)
         nt')) nPConApp /\ valid_lptree cmlG acc /\
       LENGTH i0 < limit' ==>
       (?pt. ptPapply0 acc (CONS pt0 (FLAT ptlist)) = [pt] /\
            ptree_head pt = (\nt'. grammar_NT
              ((INL:MMLnonT->MMLnonT+num) nt')) nPapp /\ valid_lptree
              cmlG pt /\ APPEND (APPEND (real_fringe acc) (real_fringe
              pt0)) (MAP
              ((grammar_TOK:tokens_token->(tokens_token
              ,MMLnonT)grammar_symbol) ## I) i0) = APPEND (real_fringe
              pt) (MAP
              ((grammar_TOK:tokens_token->(tokens_token
              ,MMLnonT)grammar_symbol) ## I) i)))`,
  CHEAT_TAC);;

(* HOL4 pegSoundScript.sml:479-482: a proof *)

(* [local] *)
let pmap_EQ_pair = prove
 (`(f ## g) p = (a,b) <=> (?c d. p = (c,d) /\ f c = a /\ g d = b)`,
  (REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM; PAIR_EQ] THEN
    MESON_TAC[]));;
add_simp pmap_EQ_pair;;

(* [local] *)
let pair_EQ_components = prove
 (`(p = (x,SND p) <=> FST p = x) /\
   ((x,SND p) = p <=> FST p = x) /\
   (p = (FST p,y) <=> SND p = y) /\
   ((FST p,y) = p <=> SND p = y)`,
  (MESON_TAC[PAIR; FST; SND]));;
add_simp pair_EQ_components;;

let peg_sound = prove
 (`!N i0 i pts eo.
       peg_eval cmlPEG (i0,peg_nt N I) (peg_Success i pts eo) ==>
       (?pt. pts = [pt] /\ ptree_head pt = grammar_NT N /\
            valid_lptree cmlG pt /\
            MAP (grammar_TOK ## I) i0 = APPEND (real_fringe pt)
              (MAP (grammar_TOK ## I) i))`,
  CHEAT_TAC);;
