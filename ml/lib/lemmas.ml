(* ================================================================== *)
(*  The lemmas that the proofs of phase three need and that neither   *)
(*  HOL Light nor the ported library theories have.                   *)
(*                                                                    *)
(*  This file defines nothing, so it can be loaded again into a       *)
(*  running session (tools/bin/reload), where a change in             *)
(*  ml/lib/hol4.ml costs the session.  A lemma that a single proof    *)
(*  needs stays in that proof; this is for the ones that the files    *)
(*  share.                                                            *)
(* ================================================================== *)

(* HOL4's EL_DROP, which the proofs of the port need and which HOL
   Light has not (it has no DROP of its own) *)

let EL_DROP = prove
 (`!l n k. n + k < LENGTH l ==> EL n (DROP k l) = EL (n + k) l`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC[LENGTH; LT];
   REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN
   REWRITE_TAC[DROP; LENGTH; EL; TL; ADD_CLAUSES; ARITH_EQ;
               NOT_SUC; SUC_SUB1; LT_SUC] THEN
   DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[]]);;

(* HOL4's LLOOKUP_EQ_EL, and the step over an APPEND that its
   proofs take with EL_APPEND2: oEL is HOL4's LLOOKUP, and
   ml/lib/hol4.ml defines it, so the lemmas about it come here *)

let oEL_EL = prove
 (`!l n. n < LENGTH l ==> oEL n l = SOME (EL n l)`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC[LENGTH; LT];
   REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
   REWRITE_TAC[oEL; LENGTH; EL; TL; HD; ARITH_EQ; NOT_SUC;
               SUC_SUB1; LT_SUC] THEN
   DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[]]);;

let oEL_APPEND = prove
 (`!l m i. oEL (i + LENGTH l) (APPEND l m) = oEL i m`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; APPEND; ADD_CLAUSES; oEL; NOT_SUC;
              SUC_SUB1] THEN
  ASM_REWRITE_TAC[]);;

(* the two size facts that a measure induction over a definition
   which recurses on BUTLAST and LAST needs (HOL4 gets them from
   its own size simp set) *)

let list_size_BUTLAST = prove
 (`!(f:A->num) l. list_size f (BUTLAST l) <= list_size f l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[BUTLAST; list_size; LE_REFL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[list_size; LE_0] THEN
  ASM_ARITH_TAC);;

let list_size_LAST = prove
 (`!(f:A->num) l. ~(l = []) ==> f (LAST l) <= list_size f l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[NOT_CONS_NIL; LAST; list_size] THEN
  COND_CASES_TAC THENL
  [ARITH_TAC;
   FIRST_ASSUM(fun ih -> FIRST_ASSUM(fun c ->
     MP_TAC(MATCH_MP ih c))) THEN ARITH_TAC]);;

(* and the other direction of HOL4's LLOOKUP_EQ_EL *)

let oEL_SOME = prove
 (`!l n x. oEL n l = SOME x ==> n < LENGTH l /\ EL n l = x`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[oEL; distinctness "option"] THEN
  STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[oEL; ARITH_EQ; NOT_SUC; SUC_SUB1; LENGTH; EL; TL;
              HD; LT_0; LT_SUC; injectivity "option"] THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);;

(* HOL4's DROP_0: the clauses of DROP decide on the number, so
   DROP 0 of a list that is a variable does not reduce *)

let DROP_0 = prove
 (`!l:A list. DROP 0 l = l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[DROP]);;

(* HOL4's SNOC and its laws.  ml/lib/hol4.ml defines SNOC, because
   a few sources define a function by recursion on one, and HOL4
   carries some seventy lemmas about it that HOL Light has none of.
   These are the ones a proof needs to read the front and the last
   expression off a list that a pass recurses on
   (PORTING-GUIDE.md entry 15); BUTLAST is HOL Light's name for
   what the sources call FRONT. *)

let SNOC_APPEND = prove
 (`!(l:A list) x. SNOC x l = APPEND l [x]`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC; APPEND]);;

let NOT_SNOC_NIL = prove
 (`!(l:A list) x. ~(SNOC x l = [])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC; NOT_CONS_NIL]);;

let SNOC_CASES = prove
 (`!l:A list. ~(l = []) ==> ?x y. l = SNOC x y`,
  GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `LAST (l:A list)` THEN
  EXISTS_TAC `BUTLAST (l:A list)` THEN
  REWRITE_TAC[SNOC_APPEND] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP APPEND_BUTLAST_LAST th]));;

let FRONT_SNOC = prove
 (`!(l:A list) x. BUTLAST (SNOC x l) = l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[SNOC; BUTLAST; NOT_SNOC_NIL]);;

let LAST_SNOC = prove
 (`!(l:A list) x. LAST (SNOC x l) = x`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[SNOC; LAST; NOT_SNOC_NIL]);;

let LENGTH_SNOC = prove
 (`!(l:A list) x. LENGTH (SNOC x l) = LENGTH l + 1`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC; LENGTH] THEN
  ARITH_TAC);;

(* and the size of one, which the measure of such an induction
   asks for and HOL4 gets from its own size simp set *)

let list_size_SNOC = prove
 (`!(f:A->num) x l.
     list_size f (SNOC x l) = list_size f l + (f x + 1)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[SNOC; list_size] THEN ARITH_TAC);;

(* the value that a Var reads when a pass has moved an expression
   into tail-position: the first one past the front of the list *)

let EL_LEN_APPEND = prove
 (`!(a:A list) v l. EL (LENGTH a) (APPEND a (CONS v l)) = v`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; APPEND; EL; HD; TL]);;

(* ------------------------------------------------------------------ *)
(* NULL as an equation, which HOL4 has as NULL_EQ of listTheory, and  *)
(* the list cases with names that an induction has not taken.         *)
(* ------------------------------------------------------------------ *)

let NULL_EQ = prove
 (`!l:A list. NULL l <=> l = []`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; NOT_CONS_NIL]);;

let list_CASES_v = prove
 (`!l:A list. l = [] \/ (?v vs. l = CONS v vs)`,
  MESON_TAC[list_CASES]);;

(* ------------------------------------------------------------------ *)
(* The finite maps of HOL4's finite_mapTheory: the port has the       *)
(* definitions (ml/lib/finite_map.ml), and a proof needs the facts    *)
(* about the representing function that they are phrased with.        *)
(* ------------------------------------------------------------------ *)

let FMAP_FN_FINITE = prove
 (`!fm:(A,B)fmap. FINITE {x | ~(fmap_fn fm x = NONE)}`,
  GEN_TAC THEN ONCE_REWRITE_TAC[CONJUNCT2 fmap_tybij] THEN
  REWRITE_TAC[ETA_AX; CONJUNCT1 fmap_tybij]);;

let FMAP_FN_FUPDATE = prove
 (`!(fm:(A,B)fmap) kv.
     fmap_fn (fm |+ kv) =
     (\x. if x = FST kv then SOME (SND kv) else fmap_fn fm x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUPDATE] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 fmap_tybij)] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
    `(FST (kv:A#B)) INSERT
     {x | ~(fmap_fn (fm:(A,B)fmap) x = NONE)}` THEN
  REWRITE_TAC[FINITE_INSERT; FMAP_FN_FINITE] THEN
  REWRITE_TAC[SUBSET; IN_INSERT; IN_ELIM_THM] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let FAPPLY_FUPDATE_THM = prove
 (`!(fm:(A,B)fmap) k v x.
     FAPPLY (fm |+ (k,v)) x = (if x = k then v else FAPPLY fm x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fmap_apply; FMAP_FN_FUPDATE; FST; SND] THEN
  COND_CASES_TAC THEN REWRITE_TAC[THE]);;

(* the range of a finite map, which HOL4 has as IN_FRANGE of
   finite_mapTheory; the port cannot have that name, because CakeML
   has a theorem of its own called IN_FRANGE (copying_gc.ml) *)

let FMAP_IN_FRANGE = prove
 (`!(f:(A,B)fmap) v.
     v IN FRANGE f <=> ?k. k IN FDOM f /\ FAPPLY f k = v`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FRANGE; FDOM; fmap_apply; IN_ELIM_THM] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `k:A` THEN
    ASM_REWRITE_TAC[THE; distinctness "option"];
    EXISTS_TAC `k:A` THEN
    REPEAT(FIRST_X_ASSUM MP_TAC) THEN
    STRUCT_CASES_TAC(ISPEC `fmap_fn (f:(A,B)fmap) k`
                           (cases_of `:(B)option`)) THEN
    REWRITE_TAC[THE; injectivity "option"; distinctness "option"] THEN
    MESON_TAC[]]);;
