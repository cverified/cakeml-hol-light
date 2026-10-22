(* ======================================================== *)
(*  set_sep: ported from HOL4's
    examples/machine-code/hoare-triple/set_sepScript.sml  *)
(* ======================================================== *)

(* this file needs nothing of the port *)
(* HOL4 ancestors outside the port: pred_set pair words *)

let one_def = cake_define
  `set_sep_one x = (\s. (s = {x}))`;;
let emp_def = cake_define
  `emp = (\s. (s = {}))`;;
let cond_def = cake_define
  `cond c = (\s. (s = {}) /\ c)`;;
let SEP_T_def = cake_define
  `SEP_T s = T`;;
let SPLIT_def = cake_define
  `SPLIT (s:'a->bool) (u,v) <=> (u UNION v = s) /\ DISJOINT u v`;;
let STAR_def = cake_define
  `STAR p q = (\s. ?u v. SPLIT s (u,v) /\ p u /\ q v)`;;

overload_interface("*",
  `STAR:((A->bool)->bool)->((A->bool)->bool)->(A->bool)->bool`);;

let SEP_EXISTS = cake_define
  `(SEP_EXISTS) = (\f (s:'a->bool). (?) (\y. f y s))`;;

let fun2set_def = cake_define
  `fun2set ((f:'b->'a),d) = {(a,f a) | a IN d}`;;

(* ================================================================== *)
(*  The theorems of set_sepTheory that a proof of phase three asks   *)
(*  for.  HOL4 states the unit laws of the separating conjunction    *)
(*  as two of the many clauses of SEP_CLAUSES, whose others are      *)
(*  about the disjunction of two separation predicates and about     *)
(*  SEP_F, which the port does not have; so the unit laws stand on   *)
(*  their own here.                                                  *)
(* ================================================================== *)

let STAR_COMM = prove
 (`!(p:(A->bool)->bool) q. p * q = q * p`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `s:A->bool` THEN REWRITE_TAC[STAR_def; SPLIT_def] THEN
  MESON_TAC[UNION_COMM; DISJOINT_SYM]);;

let emp_STAR = prove
 (`!p:(A->bool)->bool. emp * p = p`,
  GEN_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `s:A->bool` THEN
  REWRITE_TAC[STAR_def; SPLIT_def; emp_def] THEN EQ_TAC THENL
   [STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[UNION_EMPTY]) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`{}:A->bool`; `s:A->bool`] THEN
    ASM_REWRITE_TAC[UNION_EMPTY; DISJOINT_EMPTY]]);;

let STAR_emp = prove
 (`!p:(A->bool)->bool. p * emp = p`,
  GEN_TAC THEN ONCE_REWRITE_TAC[STAR_COMM] THEN
  MATCH_ACCEPT_TAC emp_STAR);;

(* HOL4's STAR_ASSOC_LEMMA, with the associativity from it and the
   commutativity, the way set_sepScript.sml does it *)

let STAR_ASSOC_LEMMA = prove
 (`!(x:A->bool) (p:(A->bool)->bool) q r.
     (p * (q * r)) x ==> ((p * q) * r) x`,
  REWRITE_TAC[STAR_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`u UNION u':A->bool`; `v':A->bool`] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT(FIRST_X_ASSUM MP_TAC) THEN REWRITE_TAC[SPLIT_def] THEN
    SET_TAC[];
    MAP_EVERY EXISTS_TAC [`u:A->bool`; `u':A->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM MP_TAC) THEN REWRITE_TAC[SPLIT_def] THEN
    SET_TAC[];
    ASM_REWRITE_TAC[]]);;

let STAR_ASSOC = prove
 (`!(p:(A->bool)->bool) q r. p * (q * r) = (p * q) * r`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
  MESON_TAC[STAR_ASSOC_LEMMA; STAR_COMM]);;

(* the first clause of HOL4's SEP_CLAUSES: an existential of a
   separation predicate comes out of the separating conjunction *)

let SEP_EXISTS_STAR = prove
 (`!(p:B->(A->bool)->bool) q.
     SEP_EXISTS p * q = SEP_EXISTS (\v. p v * q)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `s:A->bool` THEN
  REWRITE_TAC[STAR_def; SEP_EXISTS] THEN MESON_TAC[]);;

let STAR_SEP_EXISTS = prove
 (`!(p:B->(A->bool)->bool) q.
     q * SEP_EXISTS p = SEP_EXISTS (\v. q * p v)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[STAR_COMM] THEN
  REWRITE_TAC[SEP_EXISTS_STAR] THEN
  ONCE_REWRITE_TAC[STAR_COMM] THEN REWRITE_TAC[]);;
