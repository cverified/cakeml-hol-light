(* ================================================================== *)
(*  Lazy lists, which HOL Light does not have.                        *)
(*                                                                    *)
(*  HOL4 defines 'a llist coinductively; HOL Light has no coinductive *)
(*  types, so a lazy list is represented here by the function that    *)
(*  gives                                                             *)
(*  its elements, which is NONE from the end of the list onwards. The *)
(*  operations are the ones of HOL4's llistTheory that the CakeML port*)
(*  needs; LUNFOLD needs the helper LUNFOLD_state, which HOL4 does not*)
(*  have (see ISSUES.md).                                             *)
(* ================================================================== *)

let llist_tybij =
  let th = prove
   (`?f:num->A option. !n. f n = NONE ==> f (SUC n) = NONE`,
    EXISTS_TAC `\n:num. (NONE:A option)` THEN REWRITE_TAC[]) in
  new_type_definition "llist" ("mk_llist","llist_fn") th;;

let LNIL = new_definition
  `LNIL = mk_llist (\n:num. (NONE:A option))`;;

let LCONS = new_definition
  `LCONS (h:A) t =
   mk_llist (\n. if n = 0 then SOME h else llist_fn t (n - 1))`;;

let LHD = new_definition
  `LHD (l:A llist) = llist_fn l 0`;;

let LTL = new_definition
  `LTL (l:A llist) =
   if llist_fn l 0 = NONE then NONE
   else SOME (mk_llist (\n. llist_fn l (n + 1)))`;;

let LNTH = new_definition
  `LNTH n (l:A llist) = llist_fn l n`;;

let LFINITE = new_definition
  `LFINITE (l:A llist) <=> ?n. llist_fn l n = NONE`;;

let LLENGTH = new_definition
  `LLENGTH (l:A llist) =
   if LFINITE l then SOME (minimal n. llist_fn l n = NONE) else NONE`;;

let LTAKE = new_definition
  `LTAKE n (l:A llist) =
   if (!m. m < n ==> ~(llist_fn l m = NONE))
   then SOME (list_of_seq (\m. THE (llist_fn l m)) n) else NONE`;;

let LPREFIX = new_definition
  `LPREFIX (l1:A llist) l2 <=>
   !n x. llist_fn l1 n = SOME x ==> llist_fn l2 n = SOME x`;;

let fromList = new_definition
  `fromList (l:A list) = mk_llist (\n. oEL n l)`;;

let toList = new_definition
  `toList (l:A llist) =
   if LFINITE l then LTAKE (THE (LLENGTH l)) l else NONE`;;

let LAPPEND = new_definition
  `LAPPEND (l1:A llist) l2 =
   mk_llist (\n. match LLENGTH l1 with
                   NONE -> llist_fn l1 n
                 | SOME k -> if n < k then llist_fn l1 n
                             else llist_fn l2 (n - k))`;;

let LMAP = new_definition
  `LMAP (f:A->B) l = mk_llist (\n. OPTION_MAP f (llist_fn l n))`;;

(* the state of LUNFOLD after n steps, and LUNFOLD itself *)

let LUNFOLD_state = new_recursive_definition num_RECURSION
  `(LUNFOLD_state (f:A->(A#B)option) 0 x = SOME x) /\
   (LUNFOLD_state f (SUC n) x =
    match LUNFOLD_state f n x with
      NONE -> NONE
    | SOME y -> (match f y with
                   NONE -> NONE
                 | SOME (z,a) -> SOME z))`;;

let LUNFOLD = new_definition
  `LUNFOLD (f:A->(A#B)option) x =
   mk_llist (\n. match LUNFOLD_state f n x with
                   NONE -> NONE
                 | SOME y -> OPTION_MAP SND (f y))`;;

(* the n-th tail of a lazy list, which is NONE when the list has
   fewer than n elements (HOL4's LDROP) *)

let LDROP = new_definition
  `LDROP n (l:A llist) =
   if (!m. m < n ==> ~(llist_fn l m = NONE))
   then SOME (mk_llist (\m. llist_fn l (m + n))) else NONE`;;

(* HOL4 defines eventually inductively: it says that P holds of the
   list itself or of a tail of it *)

let eventually = new_definition
  `eventually P (l:A llist) <=> ?n t. LDROP n l = SOME t /\ P t`;;

(* the facts about LDROP that a recursion along a lazy list needs *)

let LLIST_FN_EQ = prove
 (`!l1 l2:A llist. llist_fn l1 = llist_fn l2 ==> l1 = l2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `mk_llist:(num->A option)->A llist`) THEN
  REWRITE_TAC[CONJUNCT1 llist_tybij]);;

let LDROP_0 = prove
 (`!l:A llist. LDROP 0 l = SOME l`,
  GEN_TAC THEN REWRITE_TAC[LDROP; ARITH_RULE `~(m < 0)`] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LLIST_FN_EQ THEN
  REWRITE_TAC[ADD_CLAUSES; ETA_AX; CONJUNCT1 llist_tybij]);;

let LTL_LDROP_1 = prove
 (`!(l:A llist) t. LTL l = SOME t ==> LDROP 1 l = SOME t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LTL; LDROP] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  ASM_SIMP_TAC[ARITH_RULE `m < 1 <=> m = 0`; FORALL_UNWIND_THM2]);;

(* the first element of a lazy list is one step before the elements
   of its tail *)

let llist_fn_NONE = prove
 (`!(l:A llist) n. llist_fn l n = NONE ==> llist_fn l (SUC n) = NONE`,
  GEN_TAC THEN
  MP_TAC(SPEC `llist_fn (l:A llist)` (CONJUNCT2 llist_tybij)) THEN
  REWRITE_TAC[CONJUNCT1 llist_tybij]);;

let LTL_LLIST_FN = prove
 (`!(l:A llist) t n.
     LTL l = SOME t ==> llist_fn t n = llist_fn l (n + 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LTL] THEN COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `llist_fn (mk_llist (\n. llist_fn (l:A llist) (n + 1))) =
    (\n. llist_fn l (n + 1))`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM(CONJUNCT2 llist_tybij)] THEN GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `SUC n + 1 = SUC (n + 1)`] THEN
  MATCH_ACCEPT_TAC llist_fn_NONE);;

let LTL_NONE_LDROP = prove
 (`!(l:A llist) n. LTL l = NONE ==> LDROP (SUC n) l = NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LTL; LDROP] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < SUC n`]);;

let LDROP_SUC = prove
 (`!(l:A llist) t n. LTL l = SOME t ==> LDROP (SUC n) l = LDROP n t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!m. llist_fn (t:A llist) m = llist_fn l (m + 1)`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[LTL_LLIST_FN]; ALL_TAC] THEN
  SUBGOAL_THEN `~(llist_fn (l:A llist) 0 = NONE)` ASSUME_TAC THENL
   [UNDISCH_TAC `LTL (l:A llist) = SOME t` THEN REWRITE_TAC[LTL] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "option"];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LDROP] THEN
  SUBGOAL_THEN
   `(!m. m < SUC n ==> ~(llist_fn (l:A llist) m = NONE)) <=>
    (!m. m < n ==> ~(llist_fn l (m + 1) = NONE))`
   SUBST1_TAC THENL
   [EQ_TAC THENL
     [DISCH_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `m < n` THEN
      ARITH_TAC;
      DISCH_TAC THEN X_GEN_TAC `m:num` THEN
      STRUCT_CASES_TAC (SPEC `m:num` num_CASES) THEN
      REWRITE_TAC[LT_SUC] THEN REWRITE_TAC[ADD1] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC LLIST_FN_EQ THEN
  REWRITE_TAC[CONJUNCT1 llist_tybij; FUN_EQ_THM] THEN GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `x + SUC n = (x + n) + 1`]);;

(* a list of which P does not hold itself but eventually does, is a
   list with a tail, of which P eventually holds *)

let eventually_LTL = prove
 (`!P (l:A llist).
     eventually P l /\ ~P l
     ==> ?t. LTL l = SOME t /\ eventually P t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eventually] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `u:A llist`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
   [UNDISCH_TAC `LDROP n (l:A llist) = SOME u` THEN
    ASM_REWRITE_TAC[LDROP_0; injectivity "option"] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?m. n = SUC m` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [ASM_MESON_TAC[num_CASES]; ALL_TAC] THEN
  SUBGOAL_THEN `?t. LTL (l:A llist) = SOME t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LTL_NONE_LDROP; cases "option";
                  distinctness "option"];
    ALL_TAC] THEN
  EXISTS_TAC `t:A llist` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `u:A llist`] THEN
  ASM_MESON_TAC[LDROP_SUC]);;

(* the least number that satisfies a predicate that 0 does not
   satisfy is one more than the least number that satisfies the
   predicate one step on (which a recursion along a lazy list needs,
   for misc's Lnext) *)

let MINIMAL_SUC = prove
 (`!P. (?n. P n) /\ ~P 0
       ==> (minimal n. P n) = SUC (minimal n. P (SUC n))`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `?m. (P:num->bool) (SUC m)` ASSUME_TAC THENL
   [ASM_MESON_TAC[num_CASES]; ALL_TAC] THEN
  MP_TAC(SPEC `\m. (P:num->bool) (SUC m)` MINIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC MINIMAL_UNIQUE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN
  STRUCT_CASES_TAC (SPEC `m:num` num_CASES) THEN
  ASM_REWRITE_TAC[LT_SUC] THEN ASM_MESON_TAC[]);;
