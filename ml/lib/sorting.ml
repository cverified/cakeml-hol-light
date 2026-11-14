(* ======================================================== *)
(*  sorting: ported from HOL4's
    src/sort/sortingScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs, and 35 theorems of it from LightCake.  Needed
    by 22 files of the port.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: rich_list combin pair relation
   list arithmetic pred_set *)

let PERM_DEF = new_definition
  `PERM L1 L2 = (!x. FILTER ((=) x) L1 = FILTER ((=) x) L2)`;;

let SORTED_DEF,SORTED_DEF_ind = define_guess
  [`SORTED R [] = T`;
   `SORTED R [x] = T`;
   `SORTED R (CONS x (CONS y rst)) <=> R x y /\ SORTED R (CONS y
  rst)`];;

let SORTS_DEF = new_definition
  `SORTS f R <=> (!l. PERM l (f R l) /\ SORTED R (f R l))`;;

let PART_DEF,PART_DEF_ind = define_rec
  [`PART P [] l1 l2 = (l1,l2)`;
   `PART P (CONS h rst) l1 l2 =
              (if P h then PART P rst (CONS h l1) l2 else PART
                P rst l1 (CONS h l2))`];;

let PARTITION_DEF = new_definition
  `PARTITION P l = PART P l [] []`;;

(* ================================================================ *)
(*  The theorems of sortingTheory that LightCake proves and this  *)
(*  port needs, taken from its hol4/sorting.                      *)
(*                                                                *)
(*  LightCake is the other HOL Light port of CakeML               *)
(*  (hol-light-family/LightCake, BSD 3-Clause); its HOL4 library  *)
(*  layer is proved, and of these theories this port has only     *)
(*  the definitions that CakeML needs.  tools/lightcake.py        *)
(*  writes this file: the statements and the proofs are           *)
(*  LightCake's, with its constants under the names this port     *)
(*  gives them.  What it could not take, and why, is at the end.  *)
(* ================================================================ *)


let PERM_REFL = prove
 (`!L:A list. PERM L L`,
  REWRITE_TAC[PERM_DEF]);;

let PERM_INTRO = prove
 (`!x y:A list. x = y ==> PERM x y`,
  SIMP_TAC[PERM_REFL]);;

let PERM_transitive = prove
 (`transitive (PERM:A list->A list->bool)`,
  REWRITE_TAC[transitive_def; PERM_DEF] THEN MESON_TAC[]);;

let PERM_TRANS = prove
 (`!x y z:A list. PERM x y /\ PERM y z ==> PERM x z`,
  REWRITE_TAC[PERM_DEF] THEN MESON_TAC[]);;

let PERM_SYM = prove
 (`!l1 l2:A list. PERM l1 l2 <=> PERM l2 l1`,
  REWRITE_TAC[PERM_DEF] THEN MESON_TAC[]);;

let PERM_CONG = prove
 (`!L1 L2 L3 L4:A list.
     PERM L1 L3 /\ PERM L2 L4 ==> PERM (APPEND L1 L2) (APPEND L3 L4)`,
  REWRITE_TAC[PERM_DEF; FILTER_APPEND] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let PERM_NIL = prove
 (`!L:A list. (PERM L [] <=> L = []) /\ (PERM [] L <=> L = [])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[PERM_REFL; NOT_CONS_NIL] THEN
  REWRITE_TAC[PERM_DEF; FILTER] THEN CONJ_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `h:A`) THEN REWRITE_TAC[] THEN
  MESON_TAC[NOT_CONS_NIL]);;

let LSORTAUX_MEM_FILTER_EQ = prove
 (`!l (x:A). MEM x l <=> ~(FILTER ((=) x) l = [])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; FILTER] THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL] THEN
    ASM_MESON_TAC[]);;

let FILTER_EQ_REP = prove
 (`!(x:A) l. FILTER ((=) x) l = REPLICATE (LENGTH (FILTER ((=) x) l))
   x`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; LENGTH;
    REPLICATE] THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[LENGTH;
    REPLICATE] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[CONS_11]);;

let FILTER_EQ_LENGTHS_EQ = prove
 (`!(x:A) l1 l2.
     LENGTH (FILTER ((=) x) l1) = LENGTH (FILTER ((=) x) l2)
     ==> FILTER ((=) x) l1 = FILTER ((=) x) l2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[FILTER_EQ_REP]
    THEN
  ASM_REWRITE_TAC[]);;

let PERM_alt = prove
 (`!L1 L2:A list.
     PERM L1 L2 <=> !x. LENGTH (FILTER ((=) x) L1) = LENGTH (FILTER ((=)
       x) L2)`,
  REWRITE_TAC[PERM_DEF] THEN REPEAT GEN_TAC THEN EQ_TAC THENL
   [SIMP_TAC[]; MESON_TAC[FILTER_EQ_LENGTHS_EQ]]);;

let PERM_SWAP_L_AT_FRONT = prove
 (`!x y (l1:A list) l2.
     PERM (APPEND (APPEND x y) l1) (APPEND (APPEND y x) l2) <=> PERM l1
       l2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PERM_alt; FILTER_APPEND;
    LENGTH_APPEND] THEN
  AP_TERM_TAC THEN ABS_TAC THEN ARITH_TAC);;

let PERM_MEM_EQ = prove
 (`!l1 l2:A list. PERM l1 l2 ==> !x. MEM x l1 <=> MEM x l2`,
  REWRITE_TAC[PERM_DEF; LSORTAUX_MEM_FILTER_EQ] THEN SIMP_TAC[]);;

let PERM_LIST_TO_SET = prove
 (`!l1 l2:A list. PERM l1 l2 ==> set_of_list l1 = set_of_list l2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_SET_OF_LIST] THEN
  ASM_MESON_TAC[PERM_MEM_EQ]);;

let PERM_EVERY = prove
 (`!P ls ls':A list. PERM ls ls' ==> (ALL P ls <=> ALL P ls')`,
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[PERM_MEM_EQ]);;

let PART_LENGTH = prove
 (`!P (L:A list) l1 l2 p q.
     (p,q) = PART P L l1 l2
     ==> LENGTH L + LENGTH l1 + LENGTH l2 = LENGTH p + LENGTH q`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[PART_DEF; PAIR_EQ;
    LENGTH] THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC]);;

let PART_LENGTH_LEM = prove
 (`!P (L:A list) l1 l2 p q.
     (p,q) = PART P L l1 l2
     ==> LENGTH p <= LENGTH L + LENGTH l1 + LENGTH l2 /\
         LENGTH q <= LENGTH L + LENGTH l1 + LENGTH l2`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PART_LENGTH) THEN
  ARITH_TAC);;

let PERM_APPEND_IFF = prove
 (`(!l:A list l1 l2. PERM (APPEND l l1) (APPEND l l2) <=> PERM l1 l2) /\
   (!l:A list l1 l2. PERM (APPEND l1 l) (APPEND l2 l) <=> PERM l1 l2)`,
  REWRITE_TAC[PERM_alt; FILTER_APPEND; LENGTH_APPEND; EQ_ADD_LCANCEL;
              EQ_ADD_RCANCEL]);;

let PERM_EQUIVALENCE_ALT_DEF = prove
 (`!x y:A list. PERM x y <=> PERM x = PERM y`,
  REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[PERM_REFL; PERM_SYM;
    PERM_TRANS]);;

let SORTED_NIL = prove
 (`!R. SORTED R ([]:A list)`,
  REWRITE_TAC[SORTED_DEF]);;

let SORTED_SING = prove
 (`!R (x:A). SORTED R [x]`,
  REWRITE_TAC[SORTED_DEF]);;

let MEM_PERM = prove
 (`!l1 l2:A list. PERM l1 l2 ==> !a. MEM a l1 <=> MEM a l2`,
  MATCH_ACCEPT_TAC PERM_MEM_EQ);;

let PERM_FUN_APPEND_C = prove
 (`!l1 l1' l2 l2':A list.
     PERM l1 = PERM l1' ==> PERM l2 = PERM l2'
     ==> PERM (APPEND l1 l2) = PERM (APPEND l1' l2')`,
  REWRITE_TAC[GSYM PERM_EQUIVALENCE_ALT_DEF] THEN
    MESON_TAC[PERM_CONG]);;

let PERM_FUN_APPEND_APPEND_1 = prove
 (`!l1 l2 l3 l4:A list.
     PERM l1 = PERM (APPEND l2 l3)
     ==> PERM (APPEND l1 l4) = PERM (APPEND l2 (APPEND l3 l4))`,
  REWRITE_TAC[GSYM PERM_EQUIVALENCE_ALT_DEF] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[APPEND_ASSOC] THEN ASM_SIMP_TAC[PERM_CONG; PERM_REFL]);;

let PERM_FUN_APPEND_APPEND_2 = prove
 (`!l1 l2 l3 l4:A list.
     PERM l1 = PERM (APPEND l2 l3)
     ==> PERM (APPEND l4 l1) = PERM (APPEND l2 (APPEND l4 l3))`,
  REWRITE_TAC[GSYM PERM_EQUIVALENCE_ALT_DEF; PERM_alt; FILTER_APPEND;
              LENGTH_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let PERM_FUN_APPEND_IFF = prove
 (`!l l1 l2:A list.
     PERM l1 = PERM l2 ==> PERM (APPEND l l1) = PERM (APPEND l l2)`,
  REWRITE_TAC[GSYM PERM_EQUIVALENCE_ALT_DEF; PERM_APPEND_IFF]);;

let PERM_FUN_CONG = prove
 (`!l1 l1' l2 l2':A list.
     PERM l1 = PERM l1' ==> PERM l2 = PERM l2' ==> (PERM l1 l2 <=> PERM
       l1' l2')`,
  MESON_TAC[PERM_EQUIVALENCE_ALT_DEF]);;

let PERM_CONG_2 = prove
 (`!l1 l1' l2 l2':A list.
     PERM l1 l1' ==> PERM l2 l2' ==> (PERM l1 l2 <=> PERM l1' l2')`,
  MESON_TAC[PERM_EQUIVALENCE_ALT_DEF]);;

let PERM_CONG_APPEND_IFF = prove
 (`!l l1 l1' l2 l2':A list.
     PERM l1 (APPEND l l1') ==> PERM l2 (APPEND l l2')
     ==> (PERM l1 l2 <=> PERM l1' l2')`,
  MESON_TAC[PERM_EQUIVALENCE_ALT_DEF; PERM_APPEND_IFF]);;

let PERM_CONG_APPEND_IFF2 = prove
 (`!l1 l1' l1'' l2 l2' l2'':A list.
     PERM l1 (APPEND l1' l1'') ==> PERM l2 (APPEND l2' l2'') ==>
     PERM l1' l2' ==> (PERM l1 l2 <=> PERM l1'' l2'')`,
  REWRITE_TAC[PERM_alt; FILTER_APPEND; LENGTH_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[EQ_ADD_LCANCEL]);;

let PERM_FUN_SPLIT = prove
 (`!l l1 l1' l2:A list.
     PERM l (APPEND l1 l2) ==> PERM l1' l1 ==> PERM l (APPEND l1' l2)`,
  MESON_TAC[PERM_EQUIVALENCE_ALT_DEF; PERM_APPEND_IFF; PERM_CONG;
    PERM_REFL;
            PERM_SYM; PERM_TRANS]);;

let PERM_REWR = prove
 (`!l r l1 l2:A list.
     PERM l r ==> (PERM (APPEND l l1) l2 <=> PERM (APPEND r l1) l2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] PERM_CONG_2)
    THEN
  ASM_SIMP_TAC[PERM_CONG; PERM_REFL]);;

let LSORTAUX_transitive_LT = prove
 (`transitive ((<):num->num->bool)`,
  REWRITE_TAC[transitive_def] THEN ARITH_TAC);;

let LSORTAUX_BIJ_COUNT = prove
 (`!f n. BIJ f (count n) (count n) <=>
         (!i. i < n ==> f i < n) /\ (!i j. i < n /\ j < n /\ f i = f j
           ==> i = j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIJ; INJ; SURJ; count_def;
    IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`{m:num | m < n}`; `f:num->num`]
    SURJECTIVE_IFF_INJECTIVE) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM]
    THEN
  MESON_TAC[]);;

let LSORTAUX_EQ_LIST_OF_SEQ = prove
 (`!l (g:num->A) n. l = list_of_seq g n <=> LENGTH l = n /\ !i. i < n
   ==> EL i l = g i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[EL_LIST_OF_SEQ]);;

(* What this port cannot take from LightCake's sorting
   yet, with the names of its own that each proof
   uses:

     PERM_MONO                        CONS
     PERM_CONS_IFF                    CONS PERM_MONO
     LSORTAUX_FILTER_EQ_CONS_APPEND   CONS
     LSORTAUX_FILTER_CONS_APPEND      CONS
                                      LSORTAUX_FILTER_EQ_CONS_APPEND
     PERM_CONS_EQ_APPEND              CONS LSORTAUX_FILTER_CONS_APPEND
     PERM_SING                        PERM_CONS_EQ_APPEND
     PERM_APPEND                      PERM_CONS_EQ_APPEND
     CONS_PERM                        CONS PERM_CONS_EQ_APPEND
     APPEND_PERM_SYM                  PERM_APPEND
     PERM_SPLIT_IF                    CONS_PERM PERM_CONS_IFF
     PERM_SPLIT                       PERM_SPLIT_IF
     PERM_IND                         CONS PERM_CONS_EQ_APPEND
     LSORTAUX_PERM_SWAP_HEAD          CONS PERM_CONS_EQ_APPEND
     PERM_SWAP_AT_FRONT               CONS LSORTAUX_PERM_SWAP_HEAD
                                      PERM_CONS_IFF
     LSORTAUX_PERM_SWAP               CONS PERM_SWAP_AT_FRONT
     PERM_STRONG_IND                  CONS LSORTAUX_PERM_SWAP PERM_IND
                                      PERM_MONO
     PERM_LENGTH                      PERM_IND
     PERM_NULL_EQ                     PERM_IND
     SORTED_IND                       CONS
     SORTED_EQ                        CONS
     SORTED_APPEND                    SORTED_EQ
     SORTED_APPEND_IMP                SORTED_APPEND
     LSORTAUX_SORTED_CONS             CONS
     SORTED_APPEND_GEN                LSORTAUX_SORTED_CONS
     PARTs_HAVE_PROP                  CONS
     LSORTAUX_PART_PERM               CONS_PERM
     PART_MEM                         LSORTAUX_PART_PERM
     PERM_SINGLE_SWAP_SYM             PERM_SINGLE_SWAP_DEF
     PERM_SINGLE_SWAP_I               PERM_SINGLE_SWAP_DEF
     PERM_SINGLE_SWAP_APPEND          PERM_SINGLE_SWAP_I
     PERM_SINGLE_SWAP_REFL            PERM_SINGLE_SWAP_APPEND
     PERM_SINGLE_SWAP_CONS            CONS PERM_SINGLE_SWAP_DEF
     PERM_SINGLE_SWAP_TC_CONS         CONS PERM_SINGLE_SWAP_CONS TC_INC
                                      TC_INDUCT TC_TRANS
     LSORTAUX_PERM_IS_TC_PSS          CONS M PERM_CONS_EQ_APPEND
                                      PERM_SINGLE_SWAP_APPEND
                                      PERM_SINGLE_SWAP_REFL
                                      PERM_SINGLE_SWAP_TC_CONS TC_INC
                                      TC_TRANS
     LSORTAUX_PSS_IS_PERM             PERM_SINGLE_SWAP_DEF
     PERM_TC                          LSORTAUX_PERM_IS_TC_PSS
                                      LSORTAUX_PSS_IS_PERM TC_INDUCT
     PERM_lifts_transitive_relations  PERM_SINGLE_SWAP_DEF PERM_TC
                                      TC_INDUCT
     PERM_lifts_equalities            PERM_lifts_transitive_relations
     PERM_lifts_invariants            PERM_lifts_transitive_relations
     PERM_lifts_monotonicities        PERM_APPEND
                                      PERM_lifts_transitive_relations
     ALL_DISTINCT_PERM                PERM_STRONG_IND
     LSORTAUX_ALL_DISTINCT_FILTER     -- Error in included file the
                                      block
     PERM_ALL_DISTINCT                -- Error: Unbound value
                                      LSORTAUX_ALL_DISTINCT_FILTER
     PERM_MAP                         PERM_CONS_IFF PERM_IND
                                      PERM_SWAP_AT_FRONT
     PERM_SUM                         PERM_IND
     PERM_FILTER                      PERM_CONS_IFF PERM_IND
                                      PERM_SWAP_AT_FRONT
     PERM_REVERSE                     CONS_PERM
     PERM_REVERSE_EQ                  PERM_REVERSE
     SORTED_TL                        CONS
     SORTED_EL_SUC                    SORTED_IND
     SORTED_EL_LESS                   SORTED_EQ
     SORTED_PERM_EQ                   PERM_CONS_IFF SORTED_EQ can
     SORTS_PERM_EQ                    SORTED_PERM_EQ
     SORTED_FILTER                    SORTED_EQ
     ALL_DISTINCT_SORTED_WEAKEN       SORTED_IND
     PERM_FUN_CONS                    CONS PERM_CONS_IFF
     PERM_FUN_APPEND_CONS             CONS CONS_PERM
     PERM_FUN_SWAP_AT_FRONT           CONS PERM_SWAP_AT_FRONT
     PERM_FUN_CONS_11_SWAP_AT_FRONT   CONS LSORTAUX_PERM_SWAP_HEAD
                                      PERM_CONS_IFF
     PERM_FUN_CONS_11_APPEND          CONS CONS_PERM
     PERM_FUN_CONS_APPEND_1           CONS
     PERM_FUN_CONS_APPEND_2           CONS CONS_PERM
     PERM_FUN_APPEND                  PERM_APPEND
     PERM_FUN_CONS_IFF                CONS PERM_CONS_IFF
     PERM_TO_APPEND_SIMPS             CONS
     PERM_FLAT                        PERM_IND
     LSORTAUX_LIST_IND2               CONS
     SORTED_weaken                    LSORTAUX_LIST_IND2
     sorted_map                       LSORTAUX_LIST_IND2 inv_image
                                      inv_image_THM
     less_sorted_eq                   SORTED_EQ
     greater_sorted_eq                CONS SORTED_EQ
     SORTED_ALL_DISTINCT              SORTED_EQ
     sorted_filter                    SORTED_FILTER
     SORTED_ALL_DISTINCT_LIST_TO_SET_EQ PERM_ALL_DISTINCT SORTED_PERM_EQ
     LSORTAUX_PERM_BIJ_EL             PERM_IND
     PERM_BIJ                         LSORTAUX_PERM_BIJ_EL
     _                                PERM_CONS_IFF PERM_REVERSE_EQ
                                      PERM_SING cake_add_simps

*)
