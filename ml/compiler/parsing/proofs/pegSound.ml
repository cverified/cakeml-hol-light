(* ======================================================== *)
(*  pegSound: ported from HOL4's
    compiler/parsing/proofs/pegSoundScript.sml  *)
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

(* Set up ML bindings *)
(* HOL4 pegSoundScript.sml:12: ML code, not ported *)

(* HOL4 pegSoundScript.sml:14-15: ML code, not ported *)
(* HOL4 pegSoundScript.sml:18-19: the overload choicel, which the
   port expands *)

let Success_COND_Failure = cake_theorem "Success_COND_Failure[simp]"
  (fun () ->
    `~(peg_Success i r opt = (if P then peg_Failure fl1 fe1 else
  peg_Failure fl2 fe2))`)
  CHEAT_TAC;;

let peg_eval_choicel_NIL = cake_theorem "peg_eval_choicel_NIL[simp]"
  (fun () ->
    `peg_eval G (i0,cmlPEG_choicel []) x <=> x = peg_Failure (sloc i0)
  (peg_notFAIL G)`)
  CHEAT_TAC;;

let peg_TF = cake_theorem "peg_TF"
  (fun () ->
    `(?i' r eopt. peg_eval G (i,e) (peg_Success i' r eopt)) ==>
     ~(peg_eval G (i,e) (peg_Failure fl fe))`)
  CHEAT_TAC;;

let peg_FT = cake_theorem "peg_FT"
  (fun () ->
    `(?fl fe. peg_eval G (i,e) (peg_Failure fl fe)) ==>
     ~(peg_eval G (i,e) (peg_Success i' r eopt))`)
  CHEAT_TAC;;

let peg_eval_choicel_CONS = cake_theorem "peg_eval_choicel_CONS"
  (fun () ->
    `!x. peg_eval G (i0,cmlPEG_choicel (h :: t)) x <=>
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
               x = UNCURRY peg_Failure (MAXerr (fl1,fe1)
                 (fl2,fe2))))`)
  CHEAT_TAC;;

let peg_eval_seql_NIL = cake_theorem "peg_eval_seql_NIL[simp]"
  (fun () ->
    `peg_eval G (i0,seql [] f) x <=> x = peg_Success i0 (f []) NONE`)
  CHEAT_TAC;;

let peg_eval_try = cake_theorem "peg_eval_try"
  (fun () ->
    `!x. peg_eval G (i0,cmlPEG_try s) x <=>
           (?fl fe. peg_eval G (i0,s) (peg_Failure fl fe) /\
                    x = peg_Success i0 [] (optmax MAXerr (SOME
                      (fl,fe)) NONE)) \/
           (?i r eo. peg_eval G (i0,s) (peg_Success i r eo) /\ x
             = peg_Success i r eo)`)
  CHEAT_TAC;;

let peg_eval_seql_CONS = cake_theorem "peg_eval_seql_CONS"
  (fun () ->
    `!x. peg_eval G (i0,seql (h :: t) f) x <=>
           (?fl fe. peg_eval G (i0,h) (peg_Failure fl fe) /\ x =
             peg_Failure fl fe) \/
           (?rh i1 fl fe eopt.
              peg_eval G (i0,h) (peg_Success i1 rh eopt) /\
              peg_eval G (i1,seql t I) (peg_Failure fl fe) /\ x =
                peg_Failure fl fe) \/
           (?rh i1 i rt eopt1 eopt2.
              peg_eval G (i0,h) (peg_Success i1 rh eopt1) /\
              peg_eval G (i1,seql t I) (peg_Success i rt eopt2) /\
              x = peg_Success i (f (rh ++ rt)) eopt2)`)
  CHEAT_TAC;;

(* HOL4 pegSoundScript.sml:100-107: a theorem that HOL4 states as the
   value of an ML expression: peg_eval_choicel_SING *)

let not_peg0_LENGTH_decreases = cake_theorem "not_peg0_LENGTH_decreases"
  (fun () ->
    `~(peg0 G s) ==> peg_eval G (i0,s) (peg_Success i r eo) ==> LENGTH
  i < LENGTH i0`)
  CHEAT_TAC;;

(* HOL4 pegSoundScript.sml:115-118: ML code, not ported *)

let peg_eval_tokSymP = cake_theorem "peg_eval_tokSymP[simp]"
  (fun () ->
    `peg_eval G (i0,tokSymP P) (peg_Success i r eo) <=>
     (?h s. FST h = tokens_SymbolT s /\ P s /\ i0 = h :: i /\ r =
       mktokLf h /\ eo = NONE)`)
  CHEAT_TAC;;

let FADISJ_EQ_IMP' = cake_theorem "FADISJ_EQ_IMP'[simp,local]"
  (fun () ->
    `((!x. P x) \/ Q <=> (!x. ~(P x) ==> Q)) /\
     ((Q \/ (!x. P x)) <=> (!x. ~(P x) ==> Q))`)
  CHEAT_TAC;;

let peg_eval_TypeDec_wrongtok = cake_theorem "peg_eval_TypeDec_wrongtok"
  (fun () ->
    `~(FST tk = tokens_DatatypeT) ==>
        ~(peg_eval cmlPEG (tk :: i,peg_nt
          ((INL:MMLnonT->MMLnonT+num) nTypeDec) f) (peg_Success i' r
          eo))`)
  CHEAT_TAC;;

let peg_eval_TypeAbbrevDec_wrongtok =
  cake_theorem "peg_eval_TypeAbbrevDec_wrongtok"
  (fun () ->
    `~(FST tk = tokens_TypeT) ==>
        ~(peg_eval cmlPEG (tk :: i,peg_nt
          ((INL:MMLnonT->MMLnonT+num) nTypeAbbrevDec) f) (peg_Success
          i' r eo))`)
  CHEAT_TAC;;

let peg_eval_Structure_wrongtok =
  cake_theorem "peg_eval_Structure_wrongtok"
  (fun () ->
    `~(FST tk = tokens_StructureT) ==>
       ~(peg_eval cmlPEG (tk :: i,peg_nt
         ((INL:MMLnonT->MMLnonT+num) nStructure) f) (peg_Success i' r
         e0))`)
  CHEAT_TAC;;


let peg_eval_LetDec_wrongtok = cake_theorem "peg_eval_LetDec_wrongtok"
  (fun () ->
    `FST tk = tokens_SemicolonT ==>
     ~(peg_eval cmlPEG (tk :: i,peg_nt
       ((INL:MMLnonT->MMLnonT+num) nLetDec) f) (peg_Success i' r eo))`)
  CHEAT_TAC;;

let peg_eval_nUQConstructor_wrongtok =
  cake_theorem "peg_eval_nUQConstructor_wrongtok"
  (fun () ->
    `(!s. ~(FST t = tokens_AlphaT s)) ==>
      ~(peg_eval cmlPEG (t :: i,peg_nt
        ((INL:MMLnonT->MMLnonT+num) nUQConstructorName) f)
        (peg_Success i' r eo))`)
  CHEAT_TAC;;

let peg_eval_nConstructor_wrongtok =
  cake_theorem "peg_eval_nConstructor_wrongtok"
  (fun () ->
    `(!s. ~(FST t = tokens_AlphaT s)) /\ (!s1 s2. ~(FST t =
  tokens_LongidT s1 s2)) ==>
     ~(peg_eval cmlPEG (t :: i,peg_nt ((INL:MMLnonT->MMLnonT+num)
       nConstructorName) f) (peg_Success i' r eo))`)
  CHEAT_TAC;;

let peg_eval_nV_wrongtok = cake_theorem "peg_eval_nV_wrongtok"
  (fun () ->
    `(!s. ~(FST t = tokens_AlphaT s)) /\ (!s. ~(FST t = tokens_SymbolT
  s)) ==>
      ~(peg_eval cmlPEG (t :: i,peg_nt
        ((INL:MMLnonT->MMLnonT+num) nV) f) (peg_Success i' r eo))`)
  CHEAT_TAC;;

let peg_eval_nFQV_wrongtok = cake_theorem "peg_eval_nFQV_wrongtok"
  (fun () ->
    `(!s. ~(FST t = tokens_AlphaT s)) /\ (!s. ~(FST t = tokens_SymbolT
  s)) /\
     (!s1 s2. ~(FST t = tokens_LongidT s1 s2)) ==>
     ~(peg_eval cmlPEG (t :: i,peg_nt ((INL:MMLnonT->MMLnonT+num)
       nFQV) f) (peg_Success i' r eo))`)
  CHEAT_TAC;;

let peg_eval_rpt_never_NONE =
  cake_theorem "peg_eval_rpt_never_NONE[simp]"
  (fun () ->
    `~(peg_eval G (i,peg_rpt sym f) (peg_Failure fl fe))`)
  CHEAT_TAC;;

let pegsym_to_sym_def = cake_define
  `pegsym_to_sym x1 =
        match x1 with
          peg_tok P f -> (if f = mktokLf then
            {(grammar_TOK:tokens_token->(tokens_token
            ,MMLnonT)grammar_symbol) t | P t} else {})
        | (peg_nt N f) -> {grammar_NT N}
        | _1 -> {}`;;

let valid_ptree_mkNd = cake_theorem "valid_ptree_mkNd[simp]"
  (fun () ->
    `valid_ptree G (mkNd N subs) <=>
       N IN FDOM (rules G) /\ MAP ptree_head subs IN FAPPLY (rules
         G) N /\
       (!pt. MEM pt subs ==> valid_ptree G pt)`)
  CHEAT_TAC;;

let ptree_head_mkNd = cake_theorem "ptree_head_mkNd[simp]"
  (fun () ->
    `ptree_head (mkNd N subs) = grammar_NT N`)
  CHEAT_TAC;;

(* HOL4 pegSoundScript.sml:233: ML code, not ported *)
let ptree_list_loc_SING = cake_theorem "ptree_list_loc_SING[simp]"
  (fun () ->
    `ptree_list_loc [pt] = ptree_loc pt`)
  CHEAT_TAC;;

let ptree_fringemkNd = cake_theorem "ptree_fringemkNd[simp]"
  (fun () ->
    `ptree_fringe (mkNd N subs) = FLAT (MAP ptree_fringe subs)`)
  CHEAT_TAC;;

let valid_locs_mkNd = cake_theorem "valid_locs_mkNd[simp]"
  (fun () ->
    `valid_locs (mkNd N subs) <=> (!pt. MEM pt subs ==> valid_locs pt)`)
  CHEAT_TAC;;

let rfringe_length_not_nullable =
  cake_theorem "rfringe_length_not_nullable"
  (fun () ->
    `!G s. ~(nullable G [s]) ==>
           (!pt. ptree_head pt = s ==> valid_lptree G pt ==>
                0 < LENGTH (real_fringe pt))`)
  CHEAT_TAC;;

let valid_lptree_mkNd = cake_theorem "valid_lptree_mkNd[simp]"
  (fun () ->
    `valid_lptree G (mkNd n children) <=>
        n IN FDOM (rules G) /\ MAP ptree_head children IN FAPPLY
          (rules G) n /\
        (!pt. MEM pt children ==> valid_lptree G pt)`)
  CHEAT_TAC;;

let real_fringe_mkNd = cake_theorem "real_fringe_mkNd[simp]"
  (fun () ->
    `real_fringe (mkNd n subs) = FLAT (MAP real_fringe subs)`)
  CHEAT_TAC;;

let ptree_head_NT_mkNd = cake_theorem "ptree_head_NT_mkNd"
  (fun () ->
    `ptree_head pt = (\nt'. grammar_NT ((INL:MMLnonT->MMLnonT+num) nt'))
  n /\ valid_lptree cmlG pt /\
     real_fringe pt = MAP
       ((grammar_TOK:tokens_token->(tokens_token,MMLnonT)grammar_symbol)
       ## I) pf ==>
     (?subs. pt = mkNd ((INL:MMLnonT->MMLnonT+num) n) subs)`)
  CHEAT_TAC;;

let mkNd_11 = cake_theorem "mkNd_11[simp]"
  (fun () ->
    `mkNd n1 sub1 = mkNd n2 sub2 <=> n1 = n2 /\ sub1 = sub2`)
  CHEAT_TAC;;

let peg_linfix_correct_lemma = cake_theorem "peg_linfix_correct_lemma"
  (fun () ->
    `!UpperN sym sepsym i0 i pts eo.
        peg_eval cmlPEG (i0,peg_linfix UpperN sym sepsym)
          (peg_Success i pts eo) ==>
        (!i0' i pts s eo.
           s IN {sym,sepsym} ==>
           LENGTH i0' < LENGTH i0 ==>
           peg_eval cmlPEG (i0',s) (peg_Success i pts eo) ==>
           (?pt. pts = [pt] /\ ptree_head pt IN pegsym_to_sym s /\
                valid_lptree cmlG pt /\
                MAP
                  ((grammar_TOK:tokens_token->(tokens_token
                  ,MMLnonT)grammar_symbol) ## I) i0' = real_fringe pt ++
                  MAP
                  ((grammar_TOK:tokens_token->(tokens_token
                  ,MMLnonT)grammar_symbol) ## I) i)) /\
        (!i pts s eo.
           s IN {sym,sepsym} ==>
           peg_eval cmlPEG (i0,s) (peg_Success i pts eo) ==>
           (?pt. pts = [pt] /\ ptree_head pt IN pegsym_to_sym s /\
                valid_lptree cmlG pt /\
                MAP
                  ((grammar_TOK:tokens_token->(tokens_token
                  ,MMLnonT)grammar_symbol) ## I) i0 = real_fringe pt ++
                  MAP
                  ((grammar_TOK:tokens_token->(tokens_token
                  ,MMLnonT)grammar_symbol) ## I) i)) /\
        ~(peg0 cmlPEG sym) /\
        UpperN IN FDOM (rules cmlG) /\
        {[gsym] | gsym IN pegsym_to_sym sym} SUBSET FAPPLY (rules
          cmlG) UpperN /\
        {[grammar_NT UpperN; gsep; gsym] |
            gsep IN pegsym_to_sym sepsym /\ gsym IN pegsym_to_sym
              sym} SUBSET FAPPLY (rules
          cmlG) UpperN ==>
        (?pt. pts = [pt] /\ ptree_head pt = grammar_NT UpperN /\
          valid_lptree cmlG pt /\
             MAP
               ((grammar_TOK:tokens_token->(tokens_token
               ,MMLnonT)grammar_symbol) ## I) i0 = real_fringe pt ++
               MAP
               ((grammar_TOK:tokens_token->(tokens_token
               ,MMLnonT)grammar_symbol) ## I) i)`)
  CHEAT_TAC;;

let length_no_greater = cake_theorem "length_no_greater"
  (fun () ->
    `peg_eval G (i0,sym) (peg_Success i r eo) ==> LENGTH i <= LENGTH
  i0`)
  CHEAT_TAC;;

let MAP_TK_11 = cake_theorem "MAP_TK_11[simp]"
  (fun () ->
    `MAP
  (grammar_TOK:tokens_token->(tokens_token,MMLnonT)grammar_symbol) x =
  MAP (grammar_TOK:tokens_token->(tokens_token,MMLnonT)grammar_symbol)
  y <=> x = y`)
  CHEAT_TAC;;

let peg_eval_nTyOp_wrongtok = cake_theorem "peg_eval_nTyOp_wrongtok"
  (fun () ->
    `FST tk = tokens_LparT ==>
     ~(peg_eval cmlPEG (tk :: i,peg_nt
       ((INL:MMLnonT->MMLnonT+num) nTyOp) f) (peg_Success i' r eo))`)
  CHEAT_TAC;;

let peg_EbaseParen_sound = cake_theorem "peg_EbaseParen_sound"
  (fun () ->
    `!i0 i pts eo.
        peg_eval cmlPEG (i0,peg_EbaseParen) (peg_Success i pts eo)
          ==>
        (!i0' N i pts eo.
          LENGTH i0' < LENGTH i0 /\
          peg_eval cmlPEG (i0',peg_nt ((INL:MMLnonT->MMLnonT+num)
            N) I) (peg_Success i pts eo) ==>
          (?pt.
             pts = [pt] /\ ptree_head pt = grammar_NT
               ((INL:MMLnonT->MMLnonT+num) N) /\
             valid_lptree cmlG pt /\
             MAP (grammar_TOK ## I) i0' = real_fringe pt ++ MAP
               (grammar_TOK ## I) i)) ==>
        (?pt.
          pts = [pt] /\ ptree_head pt = grammar_NT
            ((INL:MMLnonT->MMLnonT+num) nEbase) /\
          valid_lptree cmlG pt /\
          MAP (grammar_TOK ## I) i0 = real_fringe pt ++ MAP
            (grammar_TOK ## I) i)`)
  CHEAT_TAC;;

let PAIR_MAP_I = cake_theorem "PAIR_MAP_I[local,simp]"
  (fun () ->
    `(f ## I) x = (f (FST x),SND x) <=> T`)
  CHEAT_TAC;;

(* HOL4 pegSoundScript.sml:443: a theorem that HOL4 states as the
   value of an ML expression: bindNT0_lemma *)

(* left recursive rules in the grammar turn into calls to rpt in the PEG,
   and this in turn requires inductions *)
let ptPapply_lemma = cake_theorem "ptPapply_lemma"
  (fun () ->
    `!limit'.
       (!i0 i pts eo.
         LENGTH i0 < limit' ==>
         peg_eval cmlPEG (i0,peg_nt ((INL:MMLnonT->MMLnonT+num)
           nPbase) I) (peg_Success i pts eo) ==>
         (?pt. pts = [pt] /\ ptree_head pt = (\nt'. grammar_NT
           ((INL:MMLnonT->MMLnonT+num) nt')) nPbase /\ valid_lptree cmlG
           pt /\
              MAP
                ((grammar_TOK:tokens_token->(tokens_token
                ,MMLnonT)grammar_symbol) ## I) i0 = real_fringe pt ++
                MAP
                ((grammar_TOK:tokens_token->(tokens_token
                ,MMLnonT)grammar_symbol) ## I) i)) ==>
       (!ptlist pt0 acc i0 err.
         peg_eval_list cmlPEG (i0,peg_nt
           ((INL:MMLnonT->MMLnonT+num) nPbase) I) (i,ptlist,err) /\
         ptree_head pt0 = (\nt'. grammar_NT
           ((INL:MMLnonT->MMLnonT+num) nt')) nPbase /\ valid_lptree cmlG
           pt0 /\
         ptree_head acc = (\nt'. grammar_NT
           ((INL:MMLnonT->MMLnonT+num) nt')) nPConApp /\ valid_lptree
           cmlG acc /\
         LENGTH i0 < limit' ==>
         (?pt. ptPapply0 acc (pt0 :: FLAT ptlist) = [pt] /\
              ptree_head pt = (\nt'. grammar_NT
                ((INL:MMLnonT->MMLnonT+num) nt')) nPapp /\ valid_lptree
                cmlG pt /\
              real_fringe acc ++ real_fringe pt0 ++ MAP
                ((grammar_TOK:tokens_token->(tokens_token
                ,MMLnonT)grammar_symbol) ## I) i0 =
              real_fringe pt ++ MAP
                ((grammar_TOK:tokens_token->(tokens_token
                ,MMLnonT)grammar_symbol) ## I) i))`)
  CHEAT_TAC;;

(* HOL4 pegSoundScript.sml:479-482: a proof *)

let pmap_EQ_pair = cake_theorem "pmap_EQ_pair[simp,local]"
  (fun () ->
    `(f ## g) p = (a,b) <=> (?c d. p = (c,d) /\ f c = a /\ g d = b)`)
  CHEAT_TAC;;

let pair_EQ_components = cake_theorem "pair_EQ_components[simp,local]"
  (fun () ->
    `(p = (x,SND p) <=> FST p = x) /\
     ((x,SND p) = p <=> FST p = x) /\
     (p = (FST p,y) <=> SND p = y) /\
     ((FST p,y) = p <=> SND p = y)`)
  CHEAT_TAC;;

let peg_sound = cake_theorem "peg_sound"
  (fun () ->
    `!N i0 i pts eo.
         peg_eval cmlPEG (i0,peg_nt N I) (peg_Success i pts eo) ==>
         (?pt. pts = [pt] /\ ptree_head pt = grammar_NT N /\
              valid_lptree cmlG pt /\
              MAP (grammar_TOK ## I) i0 = real_fringe pt ++ MAP
                (grammar_TOK ## I) i)`)
  CHEAT_TAC;;
