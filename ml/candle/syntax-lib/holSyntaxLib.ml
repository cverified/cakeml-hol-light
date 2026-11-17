(* ======================================================== *)
(*  holSyntaxLib: ported from HOL4's
    candle/syntax-lib/holSyntaxLibScript.sml
    A definition theory, with 11 definitions, 1 datatype and 37
    theorems.  Needed by 18 files of the port.  *)
(* ======================================================== *)

(*
  Definitions for manipulating (deeply embedded) HOL syntax.
*)

needs "basis/pure/mlstring.ml";;
needs "lib/sorting.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "holSyntaxLib"
  ["mlstring"];;

let ALPHAVARS_def = define_cases
  `(ALPHAVARS [] tmp <=> (FST tmp = SND tmp)) /\
   (ALPHAVARS (CONS tp oenv) tmp <=>
        (tmp = tp) \/
        (~(FST tp = FST tmp)) /\ (~(SND tp = SND tmp)) /\ ALPHAVARS
            oenv tmp)`;;

let ALPHAVARS_REFL = prove
 (`!env t. ALL (UNCURRY (=)) env ==> ALPHAVARS env (t,t)`,
  CHEAT_TAC);;

let ALPHAVARS_MEM = prove
 (`!env tp. ALPHAVARS env tp ==> MEM tp env \/ (FST tp = SND tp)`,
  CHEAT_TAC);;

let REV_ASSOCD_def,REV_ASSOCD_ind = define_guess
  `(REV_ASSOCD a [] d = d) /\
   (REV_ASSOCD a (CONS p t) d = if SND p = a then FST p else REV_ASSOCD a
    t d)`;;

let REV_ASSOCD = prove
 (`(!a d. REV_ASSOCD a [] d = d) /\
    (!a x y t d. REV_ASSOCD a (CONS (x,y) t) d =
                 (if y = a then x else REV_ASSOCD a t d))`,
  CHEAT_TAC);;

let REV_ASSOCD_ALOOKUP = prove
 (`!ls x d. REV_ASSOCD x ls d = match ALOOKUP (MAP (\(x,y). (y,x)) ls) x with
  NONE -> d | SOME y -> y`,
  CHEAT_TAC);;

let PRIMED_INFINITE = prove
 (`INFINITE (IMAGE (\n. APPEND x (list_of_seq (K (CHR 39)) n)) UNIV)`,
  CHEAT_TAC);;

let REV_ASSOCD_FILTER = prove
 (`!l a b d.
      REV_ASSOCD a (FILTER (\(y,x). P x) l) b =
        if P a then REV_ASSOCD a l b else b`,
  CHEAT_TAC);;

let REV_ASSOCD_MEM = prove
 (`!l x d. MEM (REV_ASSOCD x l d,x) l \/ (REV_ASSOCD x l d = d)`,
  CHEAT_TAC);;

let tyvar_inst_exists = prove
 (`?i. ty = REV_ASSOCD tyvar i b`,
  CHEAT_TAC);;

let holSyntaxLib_result_INDUCT,holSyntaxLib_result_RECURSION = define_datatype
  "holSyntaxLib_result =
     holSyntaxLib_Clash ('a)
   | holSyntaxLib_Result ('a)";;

let IS_RESULT_def = define_cases
  `(IS_RESULT (holSyntaxLib_Clash _) = F) /\
   (IS_RESULT (holSyntaxLib_Result _) = T)`;;
add_simp IS_RESULT_def;;

let IS_CLASH_def = define_cases
  `(IS_CLASH (holSyntaxLib_Clash _) = T) /\
   (IS_CLASH (holSyntaxLib_Result _) = F)`;;
add_simp IS_CLASH_def;;

let RESULT_def = new_definition
  `RESULT (holSyntaxLib_Result t) = t`;;
add_simp RESULT_def;;

let CLASH_def = new_definition
  `CLASH (holSyntaxLib_Clash t) = t`;;
add_simp CLASH_def;;


let NOT_IS_CLASH_IS_RESULT = prove
 (`!x. IS_CLASH x <=> ~(IS_RESULT x)`,
  CHEAT_TAC);;

let RESULT_eq_suff = prove
 (`x = holSyntaxLib_Result y ==> RESULT x = y`,
  CHEAT_TAC);;

let IS_CLASH_IMP = prove
 (`!x. IS_CLASH x ==> (!tm. ~(x = holSyntaxLib_Result tm))`,
  CHEAT_TAC);;

let NOT_IS_CLASH_IMP = prove
 (`!x. ~(IS_CLASH x) ==> (!tm. ~(x = holSyntaxLib_Clash tm))`,
  CHEAT_TAC);;

let IS_RESULT_IMP = prove
 (`!x. IS_RESULT x ==> (!tm. ~(x = holSyntaxLib_Clash tm))`,
  CHEAT_TAC);;

let NOT_IS_RESULT_IMP_Clash = prove
 (`!x. ~(IS_RESULT x) ==> (?var. x = holSyntaxLib_Clash var)`,
  CHEAT_TAC);;

let IS_RESULT_IMP_Result = prove
 (`!x. IS_RESULT x ==> (?res. x = holSyntaxLib_Result res)`,
  CHEAT_TAC);;

let NOT_IS_CLASH_IMP_Result = prove
 (`!x. ~(IS_CLASH x) ==> (?res. x = holSyntaxLib_Result res)`,
  CHEAT_TAC);;

let LIST_INSERT_def = new_definition
  `LIST_INSERT x xs = if MEM x xs then xs else CONS x xs`;;

let MEM_LIST_INSERT = prove
 (`!l x. set_of_list (LIST_INSERT x l) = x INSERT set_of_list l`,
  CHEAT_TAC);;

let LIST_UNION_def = new_definition
  `LIST_UNION xs ys = ITLIST LIST_INSERT xs ys`;;

let MEM_LIST_UNION = prove
 (`!l1 l2. set_of_list (LIST_UNION l1 l2) = set_of_list l1 UNION set_of_list
  l2`,
  CHEAT_TAC);;

let MEM_FOLDR_LIST_UNION = prove
 (`!ls x f b. MEM x (ITLIST (\x y. LIST_UNION (f x) y) ls b) <=> MEM x b \/
  (?y. MEM y ls /\ MEM x (f y))`,
  CHEAT_TAC);;

let LIST_UNION_NIL = prove
 (`!l2. (LIST_UNION [] l2 = l2)`,
  CHEAT_TAC);;
add_simp LIST_UNION_NIL;;

let set_LIST_UNION = prove
 (`!l1 l2. set_of_list (LIST_UNION l1 l2) = set_of_list l1 UNION set_of_list
  l2`,
  CHEAT_TAC);;
add_simp set_LIST_UNION;;

let LIST_UNION_NIL_2 = prove
 (`!ls. ALL_DISTINCT ls ==> LIST_UNION ls [] = ls`,
  CHEAT_TAC);;

let LIST_UNION_same = prove
 (`!l1 l2. set_of_list l1 SUBSET set_of_list l2 ==> LIST_UNION l1 l2 = l2`,
  CHEAT_TAC);;

let INORDER_INSERT_def = new_definition
  `INORDER_INSERT x xs =
     APPEND (FILTER (\y. string_lt y x) xs)
    (APPEND [x] (FILTER (\y. string_lt x y) xs))`;;

(* [local] *)
let LENGTH_INORDER_INSERT = prove
 (`!xs. ALL_DISTINCT (CONS x xs) ==> (LENGTH (INORDER_INSERT x xs) = SUC
  (LENGTH xs))`,
  CHEAT_TAC);;

(* [local] *)
let ALL_DISTINCT_INORDER_INSERT = prove
 (`!xs h. ALL_DISTINCT xs ==> ALL_DISTINCT (INORDER_INSERT h xs)`,
  CHEAT_TAC);;

(* [local] *)
let ALL_DISTINCT_FOLDR_INORDER_INSERT = prove
 (`!xs. ALL_DISTINCT (ITLIST INORDER_INSERT xs [])`,
  CHEAT_TAC);;

let MEM_FOLDR_INORDER_INSERT = prove
 (`!xs x. MEM x (ITLIST INORDER_INSERT xs []) = MEM x xs`,
  CHEAT_TAC);;
add_simp MEM_FOLDR_INORDER_INSERT;;

let STRING_SORT_def = new_definition
  `STRING_SORT xs = ITLIST INORDER_INSERT xs []`;;

let PERM_STRING_SORT = prove
 (`!ls. ALL_DISTINCT ls ==> PERM ls (STRING_SORT ls)`,
  CHEAT_TAC);;

let LENGTH_STRING_SORT = prove
 (`!ls. ALL_DISTINCT ls ==> (LENGTH (STRING_SORT ls) = LENGTH ls)`,
  CHEAT_TAC);;
add_simp LENGTH_STRING_SORT;;

let MEM_STRING_SORT = prove
 (`!ls. set_of_list (STRING_SORT ls) = set_of_list ls`,
  CHEAT_TAC);;
add_simp MEM_STRING_SORT;;

let ALL_DISTINCT_STRING_SORT = prove
 (`!xs. ALL_DISTINCT (STRING_SORT xs)`,
  CHEAT_TAC);;
add_simp ALL_DISTINCT_STRING_SORT;;

let STRING_SORT_SORTED = prove
 (`!ls. SORTED (<) (STRING_SORT ls)`,
  CHEAT_TAC);;

let STRING_SORT_EQ = prove
 (`!l1 l2. ALL_DISTINCT l1 /\ ALL_DISTINCT l2 ==>
      (STRING_SORT l1 = STRING_SORT l2 <=> PERM l1 l2)`,
  CHEAT_TAC);;

let ALL_DISTINCT_LIST_UNION = prove
 (`!l1 l2. ALL_DISTINCT l2 ==> ALL_DISTINCT (LIST_UNION l1 l2)`,
  CHEAT_TAC);;

let set_MAP_implode_STRING_SORT_MAP_explode = prove
 (`set_of_list (MAP implode (STRING_SORT (MAP explode ls))) = set_of_list ls`,
  CHEAT_TAC);;

let mlstring_sort_def = new_definition
  `mlstring_sort ls = MAP implode (STRING_SORT (MAP explode ls))`;;

let mlstring_sort_eq = prove
 (`!l1 l2. ALL_DISTINCT l1 /\ ALL_DISTINCT l2 ==>
    ((mlstring_sort l1 = mlstring_sort l2) <=> PERM l1 l2)`,
  CHEAT_TAC);;

let mlstring_sort_nil = prove
 (`!l. mlstring_sort l = [] ==> l = []`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
