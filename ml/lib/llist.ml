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
