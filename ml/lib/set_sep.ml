(* ======================================================== *)
(*  set_sep: ported from HOL4's
    examples/machine-code/hoare-triple/set_sepScript.sml  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: pred_set pair words *)

let one_def = new_definition
  `set_sep_one x = (\s. (s = {x}))`;;
let emp_def = new_definition
  `emp = (\s. (s = {}))`;;
let cond_def = new_definition
  `cond c = (\s. (s = {}) /\ c)`;;
let SEP_T_def = new_definition
  `SEP_T s = T`;;
let SPLIT_def = new_definition
  `SPLIT (s:'a->bool) (u,v) <=> (u UNION v = s) /\ DISJOINT u v`;;
let STAR_def = new_definition
  `STAR p q = (\s. ?u v. SPLIT s (u,v) /\ p u /\ q v)`;;

overload_interface("*",
  `STAR:((A->bool)->bool)->((A->bool)->bool)->(A->bool)->bool`);;

let SEP_EXISTS = new_definition
  `(SEP_EXISTS) = (\f (s:'a->bool). (?) (\y. f y s))`;;

let fun2set_def = new_definition
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

(* the two clauses of HOL4's SEP_CLAUSES that take a separation
   predicate apart at a point: what an existential of one says of a
   set, and what a condition beside one says of it *)

let SEP_EXISTS_THM = prove
 (`!(p:B->(A->bool)->bool) s. (SEP_EXISTS p) s <=> ?y. p y s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SEP_EXISTS] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[]);;

let cond_STAR = prove
 (`!c (p:(A->bool)->bool) s. (cond c * p) s <=> c /\ p s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[STAR_def; cond_def; SPLIT_def] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:A->bool`
      (X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC)) THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `s:A->bool = v` SUBST1_TAC THENL
     [REPEAT(FIRST_X_ASSUM MP_TAC) THEN SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`{}:A->bool`; `s:A->bool`] THEN
    ASM_REWRITE_TAC[UNION_EMPTY; DISJOINT_EMPTY]]);;

let STAR_cond = prove
 (`!c (p:(A->bool)->bool) s. (p * cond c) s <=> c /\ p s`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [STAR_COMM] THEN
  MATCH_ACCEPT_TAC cond_STAR);;

(* ================================================================== *)
(*  The theorems of set_sepTheory that take the cell at an address    *)
(*  out of a separation predicate over a memory: HOL4's SEP_R_TAC     *)
(*  and SEP_W_TAC are these two (read_fun2set and write_fun2set)      *)
(*  applied to the assumption, and the port does that by hand.        *)
(* ================================================================== *)

let SPLIT_LEMMA = prove
 (`!(s:A->bool) t v. SPLIT s (t,v) <=> v = s DIFF t /\ t SUBSET s`,
  REWRITE_TAC[SPLIT_def] THEN SET_TAC[]);;

let one_STAR = prove
 (`!(x:A) s p. (set_sep_one x * p) s <=> x IN s /\ p (s DELETE x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[STAR_def; one_def; SPLIT_LEMMA] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  MP_TAC(SET_RULE `({x:A} SUBSET s <=> x IN s) /\
                   (s DIFF {x} = s DELETE x)`) THEN
  MESON_TAC[]);;

(* and the membership of a fun2set, which is what the cell of the
   one says *)

let IN_fun2set = prove
 (`!(f:B->A) d a x. (a,x) IN fun2set (f,d) <=> f a = x /\ a IN d`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fun2set_def; IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;

let read_fun2set = prove
 (`!a x p (f:B->A) d. (set_sep_one (a,x) * p) (fun2set (f,d))
     ==> f a = x /\ a IN d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[one_STAR; IN_fun2set] THEN
  SIMP_TAC[]);;

(* HOL4's APPLY_UPDATE_THM of combinTheory, which the write of a
   cell goes through.  It stands here rather than in
   ml/lib/lemmas.ml because the load order of a run puts this file
   before the preamble's lemmas *)

let APPLY_UPDATE_THM = prove
 (`!(f:A->B) a b c. ((a =+ b) f) c = (if a = c then b else f c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[UPDATE] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[]);;

let write_fun2set = prove
 (`!y a x p (f:B->A) d. (set_sep_one (a,x) * p) (fun2set (f,d))
     ==> (p * set_sep_one (a,y)) (fun2set ((a =+ y) f,d))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV) [STAR_COMM] THEN
  REWRITE_TAC[one_STAR; IN_fun2set; APPLY_UPDATE_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `fun2set ((a =+ y) (f:B->A),d) DELETE (a,y) =
                fun2set (f,d) DELETE (a,x)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_DELETE; IN_fun2set;
                UPDATE; PAIR_EQ] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    X_GEN_TAC `b:B` THEN X_GEN_TAC `z:A` THEN
    ASM_CASES_TAC `b:B = a` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    FIRST_ASSUM ACCEPT_TAC]);;

(* the associativity and the commutativity as one permutative
   rewrite, the way HOL Light's ADD_AC is written *)

let STAR_AC = prove
 (`((p:(A->bool)->bool) * q = q * p) /\
   ((p * q) * r = p * (q * r)) /\
   (p * (q * r) = q * (p * r))`,
  REPEAT CONJ_TAC THENL
   [MATCH_ACCEPT_TAC STAR_COMM;
    REWRITE_TAC[GSYM STAR_ASSOC];
    REWRITE_TAC[STAR_ASSOC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [STAR_COMM] THEN
    REWRITE_TAC[]]);;

(* what a separation predicate beside SEP_T says: that it holds of
   some part of the set.  HOL4 does the same reasoning through its
   SEP_IMP and SEP_T_def by hand in every proof that needs it *)

let STAR_SEP_T = prove
 (`!(p:(A->bool)->bool) s. (p * SEP_T) s <=> ?u. u SUBSET s /\ p u`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[STAR_def; SEP_T_def; SPLIT_LEMMA] THEN
  MESON_TAC[]);;
