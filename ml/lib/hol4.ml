(* ========================================================================= *)
(*  The vocabulary of the HOL4 basic libraries that HOL Light does not have. *)
(*                                                                          *)
(*  The definitions are the ones of HOL4's combinTheory, optionTheory,       *)
(*  listTheory, rich_listTheory, indexedListsTheory and stringTheory, so     *)
(*  that the CakeML sources can be ported without changing them.            *)
(*                                                                          *)
(*  HOL Light already provides, with the same meaning as in HOL4:            *)
(*    I o FST SND CURRY UNCURRY ARB SUC PRE DIV MOD EXP MIN MAX EVEN ODD     *)
(*    NIL CONS APPEND LENGTH MAP FILTER MEM EL HD TL LAST NULL REVERSE       *)
(*    ZIP MAP2 REPLICATE SOME NONE INL INR OUTL OUTR                        *)
(*  and the following, which the port uses under the HOL Light name:         *)
(*    EVERY = ALL, EXISTS = EX, FRONT = BUTLAST,                             *)
(*    LIST_TO_SET = set_of_list, GENLIST f n = list_of_seq f n,              *)
(*    FOLDR f e l = ITLIST f l e                                            *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The HOL4 names and notations of the HOL Light constants that have         *)
(* another name, so that the port can use the CakeML ones.                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("::",(15,"right"));;
override_interface("::",`CONS:A->(A)list->(A)list`);;
override_interface("++",`APPEND:(A)list->(A)list->(A)list`);;
override_interface("EVERY",`ALL:(A->bool)->(A)list->bool`);;
override_interface("EXISTS",`EX:(A->bool)->(A)list->bool`);;
override_interface("FRONT",`BUTLAST:(A)list->(A)list`);;
override_interface("GENLIST",`list_of_seq:(num->A)->num->(A)list`);;
override_interface("LIST_TO_SET",`set_of_list:(A)list->A->bool`);;
override_interface("LIST_REL",
  `ALL2:(A->B->bool)->(A)list->(B)list->bool`);;

(* ------------------------------------------------------------------------- *)
(* combinTheory                                                              *)
(* ------------------------------------------------------------------------- *)

let K_DEF = new_definition
  `K (x:A) (y:B) = x`;;

let C_DEF = new_definition
  `C (f:A->B->C) x y = f y x`;;

let W_DEF = new_definition
  `W (f:A->A->B) x = f x x`;;

let FUNPOW = new_recursive_definition num_RECURSION
  `(FUNPOW (f:A->A) 0 x = x) /\
   (FUNPOW f (SUC n) x = FUNPOW f n (f x))`;;

let FLIP_DEF = new_definition
  `FLIP (f:A->B->C) x y = f y x`;;

(* ------------------------------------------------------------------------- *)
(* optionTheory                                                              *)
(* ------------------------------------------------------------------------- *)

let THE = new_recursive_definition option_RECURSION
  `THE (SOME (x:A)) = x`;;

let IS_SOME = new_recursive_definition option_RECURSION
  `(IS_SOME (SOME (x:A)) <=> T) /\ (IS_SOME NONE <=> F)`;;

let IS_NONE = new_recursive_definition option_RECURSION
  `(IS_NONE (SOME (x:A)) <=> F) /\ (IS_NONE NONE <=> T)`;;

let OPTION_MAP = new_recursive_definition option_RECURSION
  `(OPTION_MAP (f:A->B) (SOME x) = SOME (f x)) /\
   (OPTION_MAP f NONE = NONE)`;;

let OPTION_BIND = new_recursive_definition option_RECURSION
  `(OPTION_BIND NONE (f:A->B option) = NONE) /\
   (OPTION_BIND (SOME x) f = f x)`;;

let OPTION_IGNORE_BIND = new_definition
  `OPTION_IGNORE_BIND (m:A option) (n:B option) =
   OPTION_BIND m (\x. n)`;;

let OPTION_JOIN = new_recursive_definition option_RECURSION
  `(OPTION_JOIN NONE = (NONE:A option)) /\
   (OPTION_JOIN (SOME x) = x)`;;

let OPTION_MAP2 = new_definition
  `OPTION_MAP2 (f:A->B->C) x y =
   OPTION_BIND x (\a. OPTION_BIND y (\b. SOME (f a b)))`;;

let OPTION_CHOICE = new_recursive_definition option_RECURSION
  `(OPTION_CHOICE NONE (y:A option) = y) /\
   (OPTION_CHOICE (SOME x) y = SOME x)`;;

let OPTION_ALL = new_recursive_definition option_RECURSION
  `(OPTION_ALL (P:A->bool) NONE <=> T) /\
   (OPTION_ALL P (SOME x) <=> P x)`;;

let OPTION_APPLY = new_recursive_definition option_RECURSION
  `(OPTION_APPLY NONE (x:A) = (NONE:B option)) /\
   (OPTION_APPLY (SOME f) x = SOME (f x))`;;

(* HOL4's some binder: the choice that gives NONE when there is
   nothing to choose *)

let some_DEF = new_definition
  `some (P:A->bool) = if (?x. P x) then SOME (@x. P x) else NONE`;;

let OPT_MMAP = new_recursive_definition list_RECURSION
  `(OPT_MMAP (f:A->B option) [] = SOME []) /\
   (OPT_MMAP f (CONS h t) =
    OPTION_BIND (f h) (\x. OPTION_MAP (CONS x) (OPT_MMAP f t)))`;;

(* ------------------------------------------------------------------------- *)
(* listTheory and rich_listTheory                                            *)
(* ------------------------------------------------------------------------- *)





let FOLDL = new_recursive_definition list_RECURSION
  `(FOLDL (f:B->A->B) e [] = e) /\
   (FOLDL f e (CONS x xs) = FOLDL f (f e x) xs)`;;


let FLAT = new_recursive_definition list_RECURSION
  `(FLAT [] = ([]:A list)) /\
   (FLAT (CONS h t) = APPEND h (FLAT t))`;;

let SUM_DEF = new_definition
  `SUM (l:num list) = ITLIST (+) l 0`;;

let SNOC = new_recursive_definition list_RECURSION
  `(SNOC (x:A) [] = [x]) /\
   (SNOC x (CONS y ys) = CONS y (SNOC x ys))`;;


let TAKE = new_recursive_definition list_RECURSION
  `(TAKE n [] = ([]:A list)) /\
   (TAKE n (CONS x xs) =
    if n = 0 then [] else CONS x (TAKE (n - 1) xs))`;;

let DROP = new_recursive_definition list_RECURSION
  `(DROP n [] = ([]:A list)) /\
   (DROP n (CONS x xs) =
    if n = 0 then CONS x xs else DROP (n - 1) xs)`;;

let ALL_DISTINCT = new_definition
  `ALL_DISTINCT (l:A list) <=> PAIRWISE (\x y. ~(x = y)) l`;;

let ALOOKUP = new_recursive_definition list_RECURSION
  `(ALOOKUP [] (k:A) = (NONE:B option)) /\
   (ALOOKUP (CONS p t) k =
    if FST p = k then SOME (SND p) else ALOOKUP t k)`;;

let LUPDATE = new_recursive_definition list_RECURSION
  `(LUPDATE (e:A) n [] = []) /\
   (LUPDATE e n (CONS x xs) =
    if n = 0 then CONS e xs else CONS x (LUPDATE e (n - 1) xs))`;;

let oEL = new_recursive_definition list_RECURSION
  `(oEL n [] = (NONE:A option)) /\
   (oEL n (CONS x xs) = if n = 0 then SOME x else oEL (n - 1) xs)`;;

let MAPi_DEF = new_recursive_definition list_RECURSION
  `(MAPi (f:num->A->B) [] = []) /\
   (MAPi f (CONS h t) = CONS (f 0 h) (MAPi (\n. f (SUC n)) t))`;;

let LIST_BIND = new_definition
  `LIST_BIND (l:A list) (f:A->B list) = FLAT (MAP f l)`;;

let LIST_IGNORE_BIND = new_definition
  `LIST_IGNORE_BIND (m:A list) (n:B list) = LIST_BIND m (\x. n)`;;

let COUNT_LIST = new_definition
  `COUNT_LIST n = list_of_seq (\i:num. i) n`;;

let UNZIP = new_recursive_definition list_RECURSION
  `(UNZIP [] = (([]:A list),([]:B list))) /\
   (UNZIP (CONS p l) =
    (CONS (FST p) (FST (UNZIP l)),CONS (SND p) (SND (UNZIP l))))`;;

let REV = new_recursive_definition list_RECURSION
  `(REV [] (acc:A list) = acc) /\
   (REV (CONS x xs) acc = REV xs (CONS x acc))`;;

let nub = new_recursive_definition list_RECURSION
  `(nub ([]:A list) = []) /\
   (nub (CONS x l) = if MEM x l then nub l else CONS x (nub l))`;;

let SPLITP = new_recursive_definition list_RECURSION
  `(SPLITP (P:A->bool) [] = ([],[])) /\
   (SPLITP P (CONS x xs) =
    if P x then ([],CONS x xs)
    else (CONS x (FST (SPLITP P xs)),SND (SPLITP P xs)))`;;

let INDEX_FIND = new_recursive_definition list_RECURSION
  `(INDEX_FIND i (P:A->bool) [] = NONE) /\
   (INDEX_FIND i P (CONS h t) =
    if P h then SOME (i,h) else INDEX_FIND (SUC i) P t)`;;

let INDEX_OF = new_definition
  `INDEX_OF (x:A) l = OPTION_MAP FST (INDEX_FIND 0 (\y. y = x) l)`;;

let PAD_LEFT = new_definition
  `PAD_LEFT (c:A) n l = APPEND (REPLICATE (n - LENGTH l) c) l`;;

let PAD_RIGHT = new_definition
  `PAD_RIGHT (c:A) n l = APPEND l (REPLICATE (n - LENGTH l) c)`;;

let isPREFIX = new_recursive_definition list_RECURSION
  `(isPREFIX [] (l:A list) <=> T) /\
   (isPREFIX (CONS x xs) l <=>
    ~(l = []) /\ x = HD l /\ isPREFIX xs (TL l))`;;

let LAST_DEF = new_definition
  `LAST_N n (l:A list) = DROP (LENGTH l - n) l`;;

let list_size = new_recursive_definition list_RECURSION
  `(list_size (f:A->num) [] = 0) /\
   (list_size f (CONS h t) = 1 + (f h + list_size f t))`;;

let pair_size = new_definition
  `pair_size (f:A->num) (g:B->num) p = 1 + (f (FST p) + g (SND p))`;;

let option_size = new_recursive_definition option_RECURSION
  `(option_size (f:A->num) NONE = 0) /\
   (option_size f (SOME x) = 1 + f x)`;;

let bool_size = new_definition
  `bool_size (b:bool) = 0`;;

let num_size = new_definition
  `num_size (n:num) = n`;;

(* ------------------------------------------------------------------------- *)
(* stringTheory                                                              *)
(* ------------------------------------------------------------------------- *)

let ORD = new_recursive_definition char_RECURSION
  `ORD (ASCII b0 b1 b2 b3 b4 b5 b6 b7) =
   (if b0 then 128 else 0) + (if b1 then 64 else 0) +
   (if b2 then 32 else 0) + (if b3 then 16 else 0) +
   (if b4 then 8 else 0) + (if b5 then 4 else 0) +
   (if b6 then 2 else 0) + (if b7 then 1 else 0)`;;

let CHR = new_definition
  `CHR n =
   ASCII (ODD (n DIV 128)) (ODD (n DIV 64)) (ODD (n DIV 32))
         (ODD (n DIV 16)) (ODD (n DIV 8)) (ODD (n DIV 4))
         (ODD (n DIV 2)) (ODD n)`;;

let char_lt = new_definition
  `char_lt c1 c2 <=> ORD c1 < ORD c2`;;

let char_le = new_definition
  `char_le c1 c2 <=> ORD c1 <= ORD c2`;;

let string_lt = new_recursive_definition list_RECURSION
  `(string_lt s [] <=> F) /\
   (string_lt s (CONS c2 t2) <=>
    if s = [] then T
    else char_lt (HD s) c2 \/
         (HD s = c2 /\ string_lt (TL s) t2))`;;

let string_le = new_definition
  `string_le s1 s2 <=> s1 = s2 \/ string_lt s1 s2`;;

let STRCAT = new_definition
  `STRCAT (s1:string) s2 = APPEND s1 s2`;;

let STRLEN = new_definition
  `STRLEN (s:string) = LENGTH s`;;

let EXPLODE = new_definition
  `EXPLODE (s:string) = s`;;

let IMPLODE = new_definition
  `IMPLODE (l:char list) = l`;;

let isLower = new_definition
  `isLower c <=> 97 <= ORD c /\ ORD c <= 122`;;

let isUpper = new_definition
  `isUpper c <=> 65 <= ORD c /\ ORD c <= 90`;;

let isDigit = new_definition
  `isDigit c <=> 48 <= ORD c /\ ORD c <= 57`;;

let isAlpha = new_definition
  `isAlpha c <=> isLower c \/ isUpper c`;;

let isAlphaNum = new_definition
  `isAlphaNum c <=> isAlpha c \/ isDigit c`;;

let isSpace = new_definition
  `isSpace c <=> ORD c = 32 \/ 9 <= ORD c /\ ORD c <= 13`;;

let isPunct = new_definition
  `isPunct c <=>
   33 <= ORD c /\ ORD c <= 47 \/ 58 <= ORD c /\ ORD c <= 64 \/
   91 <= ORD c /\ ORD c <= 96 \/ 123 <= ORD c /\ ORD c <= 126`;;

let isPrint = new_definition
  `isPrint c <=> 32 <= ORD c /\ ORD c < 127`;;

let toLower = new_definition
  `toLower c = if isUpper c then CHR (ORD c + 32) else c`;;

let toUpper = new_definition
  `toUpper c = if isLower c then CHR (ORD c - 32) else c`;;

(* ------------------------------------------------------------------------- *)
(* What the termination proofs of the port need: the wellfounded             *)
(* relations of HOL4's WF_REL_TAC, and the fact that the elements of a       *)
(* list are smaller than the list.                                           *)
(* ------------------------------------------------------------------------- *)

let inv_image = new_definition
  `inv_image (R:B->B->bool) (f:A->B) = \x y. R (f x) (f y)`;;

parse_as_infix("LEX",(14,"right"));;

let LEX = new_definition
  `((R1:A->A->bool) LEX (R2:B->B->bool)) =
   \(x1,y1) (x2,y2). R1 x1 x2 \/ x1 = x2 /\ R2 y1 y2`;;

let WF_inv_image = prove
 (`!R:B->B->bool f:A->B. WF R ==> WF (inv_image R f)`,
  REWRITE_TAC[inv_image] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC WF_MEASURE_GEN THEN ASM_REWRITE_TAC[]);;

let WF_LEX_ALT = prove
 (`!R1:A->A->bool R2:B->B->bool.
     WF R1 /\ WF R2 ==> WF (R1 LEX R2)`,
  REWRITE_TAC[LEX] THEN MATCH_ACCEPT_TAC WF_LEX);;

let MEM_list_size = prove
 (`!f:A->num x l. MEM x l ==> f x < list_size f l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; list_size] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THENL
   [ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let sum_measure = new_recursive_definition sum_RECURSION
  `(sum_measure (f:A->num) (g:B->num) (INL a) = f a) /\
   (sum_measure f g (INR b) = g b)`;;

let DIV2 = new_definition
  `DIV2 n = n DIV 2`;;

let DIV2_LT = prove
 (`!n. ~(n = 0) ==> DIV2 n < n`,
  GEN_TAC THEN REWRITE_TAC[DIV2] THEN
  MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN ARITH_TAC);;

let list_size_DROP = prove
 (`!f:A->num l k. list_size f (DROP k l) <= list_size f l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  REWRITE_TAC[DROP; list_size; LE_REFL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[list_size; LE_REFL] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `list_size (f:A->num) t` THEN
  CONJ_TAC THENL [FIRST_ASSUM MATCH_ACCEPT_TAC; ARITH_TAC]);;

let list_size_TAKE = prove
 (`!f:A->num l k. list_size f (TAKE k l) <= list_size f l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  REWRITE_TAC[TAKE; list_size; LE_REFL; LE_0] THEN
  COND_CASES_TAC THEN REWRITE_TAC[list_size; LE_0] THEN
  ASM_SIMP_TAC[LE_ADD_LCANCEL] THEN ASM_ARITH_TAC);;

(* HOL4's LOG2, from logrootTheory *)

let LOG2 = define
  `LOG2 n = if n < 2 then 0 else SUC (LOG2 (n DIV 2))`;;

(* the facts about division that termination proofs need; HOL Light
   has DIV_LE and MOD_LE already *)

let DIV_LT_SELF = prove
 (`!m k. ~(m = 0) /\ 2 <= k ==> m DIV k < m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `k:num`] DIVISION) THEN
  ASM_SIMP_TAC[ARITH_RULE `2 <= k ==> ~(k = 0)`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `m DIV k * 2 <= m DIV k * k` MP_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_REWRITE_TAC[];
    ASM_ARITH_TAC]);;

let MOD_LT_SELF = prove
 (`!m k. ~(k = 0) ==> m MOD k < k`,
  MESON_TAC[DIVISION]);;

let MEM_list_size_ALT = prove
 (`!(x:A) l. MEM x l ==> !f:A->num. f x < list_size f l`,
  MESON_TAC[MEM_list_size]);;

let list_size_APPEND = prove
 (`!f:A->num l1 l2.
     list_size f (APPEND l1 l2) = list_size f l1 + list_size f l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; list_size] THEN ARITH_TAC);;

let list_size_REVERSE = prove
 (`!f:A->num l. list_size f (REVERSE l) = list_size f l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REVERSE; list_size; list_size_APPEND] THEN ARITH_TAC);;
