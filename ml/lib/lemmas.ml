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
