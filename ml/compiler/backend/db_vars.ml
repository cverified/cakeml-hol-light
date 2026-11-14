(* ======================================================== *)
(*  db_vars: ported from HOL4's
    compiler/backend/db_varsScript.sml
    A definition theory, with 8 definitions, 1 datatype and 14
    theorems.  Needed by 8 files of the port.  *)
(* ======================================================== *)

(*
  Defines a datatype that is handy when keeping track of which dB vars
  are live when traversing a language using dB vars.
*)

needs "lib/sptree.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "db_vars" [];;

let db_var_set_INDUCT,db_var_set_RECURSION = define_datatype
  "db_var_set = db_vars_Empty | db_vars_Var (num) | db_vars_Shift \
   (num) (db_var_set) | db_vars_Union (db_var_set) (db_var_set)";;
hol4_overload "Empty" "db_vars_Empty";;
hol4_overload "Var" "db_vars_Var";;
hol4_overload "Shift" "db_vars_Shift";;
hol4_overload "Union" "db_vars_Union";;

let mk_Union_def = new_definition
  `mk_Union t1 t2 =
     (if t1 = db_vars_Empty then t2 else
     if t2 = db_vars_Empty then t1 else
       db_vars_Union t1 t2)`;;

(* [simp] *)
let mk_Union_Empty = prove
 (`mk_Union (db_vars_Empty:db_var_set) A = A /\ mk_Union A
  db_vars_Empty = A`,
  CHEAT_TAC);;

let list_mk_Union_def,list_mk_Union_ind = define_rec
  [`list_mk_Union [] = db_vars_Empty`;
   `list_mk_Union (CONS x xs) = mk_Union x (list_mk_Union xs)`];;

let FOLDR_mk_Union_UNZIP = prove
 (`ITLIST (\(x,l) (ts,frees). (CONS x ts,mk_Union l frees)) l ([],A) =
   (let (ts,fvs) = UNZIP l in
     (ts,list_mk_Union (APPEND fvs [A])))`,
  CHEAT_TAC);;

let db_to_set_acc_def,db_to_set_acc_ind = define_rec
  [`db_to_set_acc (n:num) (db_vars_Empty:db_var_set) s = s`;
   `db_to_set_acc (n:num) (db_vars_Var v:db_var_set) s =
         (if v < n then s else sptree_insert (v - n) one s)`;
   `db_to_set_acc (n:num) (db_vars_Shift k d:db_var_set) s =
  db_to_set_acc (n + k) d s`;
   `db_to_set_acc (n:num) (db_vars_Union v1 v2:db_var_set) s =
         db_to_set_acc n v1 (db_to_set_acc n v2 s)`];;

let wf_db_to_set_acc = prove
 (`!s n a. sptree_wf a ==> sptree_wf (db_to_set_acc n s a)`,
  CHEAT_TAC);;

let db_to_set_def = new_definition
  `db_to_set db = db_to_set_acc 0 db LN`;;

let wf_db_to_set = prove
 (`!db. sptree_wf (db_to_set db)`,
  CHEAT_TAC);;

let vars_to_list_def = new_definition
  `vars_to_list db = MAP FST (toAList (db_to_set db))`;;

let vars_from_list_def = new_definition
  `vars_from_list vs = FOLDL (\s1 v. db_vars_Union (db_vars_Var v)
  s1) db_vars_Empty vs`;;

let vars_flatten_def = new_definition
  `vars_flatten db = vars_from_list (vars_to_list db)`;;

let has_var_def,has_var_ind = define_rec
  [`has_var n (db_vars_Empty:db_var_set) <=> F`;
   `has_var n (db_vars_Var v:db_var_set) <=> (n = v)`;
   `has_var n (db_vars_Shift k d:db_var_set) <=> has_var (n + k) d`;
   `has_var n (db_vars_Union d1 d2:db_var_set) <=> has_var n d1 \/
  has_var n d2`];;

(* [simp] *)
let has_var_mk_Union = prove
 (`has_var n (mk_Union l1 l2) <=> has_var n l1 \/ has_var n l2`,
  CHEAT_TAC);;

(* [simp] *)
let has_var_list_mk_Union = prove
 (`!ls. has_var n (list_mk_Union ls) <=> EX (has_var n) ls`,
  CHEAT_TAC);;

let lookup_db_to_set_acc = prove
 (`!d n k s.
     sptree_lookup n (db_to_set_acc k d s) =
       (if has_var (n + k) d then SOME one else sptree_lookup n s)`,
  (MATCH_MP_TAC db_var_set_INDUCT THEN
   REWRITE_TAC[has_var_def; db_to_set_acc_def] THEN REPEAT STRIP_TAC
     THENL
    [COND_CASES_TAC THEN REWRITE_TAC[lookup_insert] THENL
      [SUBGOAL_THEN `~(n + k = a)` (fun th -> REWRITE_TAC[th]) THEN
        ASM_ARITH_TAC;
       SUBGOAL_THEN `n = a - k <=> n + k = a` (fun th ->
         REWRITE_TAC[th]) THEN
       ASM_ARITH_TAC];
     ASM_REWRITE_TAC[ADD_ASSOC];
     ASM_REWRITE_TAC[] THEN
     MAP_EVERY ASM_CASES_TAC [`has_var (n + k) a0`; `has_var (n + k)
       a1`] THEN
     ASM_REWRITE_TAC[]]));;

let lookup_db_to_set = prove
 (`has_var n d = (sptree_lookup n (db_to_set d) = SOME one)`,
  (REWRITE_TAC[lookup_db_to_set_acc; db_to_set_def; lookup_def;
    ADD_CLAUSES] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]));;

let lookup_db_to_set_Shift = prove
 (`sptree_lookup n (db_to_set (db_vars_Shift k s)) = sptree_lookup (n
  + k) (db_to_set s)`,
  (REWRITE_TAC[db_to_set_def; db_to_set_acc_def;
    lookup_db_to_set_acc;
   lookup_def; ADD_CLAUSES]));;

let MEM_vars_to_list = prove
 (`MEM n (vars_to_list d) = has_var n d`,
  CHEAT_TAC);;

(* [local] *)
let has_var_FOLDL_Union = prove
 (`!vs n s. has_var n (FOLDL (\s1 v. db_vars_Union (db_vars_Var v) s1) s
  vs) <=>
              MEM n vs \/ has_var n s`,
  (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FOLDL; MEM; has_var_def] THEN
   MESON_TAC[]));;

let MEM_vars_from_list = prove
 (`!vs n. has_var n (vars_from_list vs) <=> MEM n vs`,
  (REWRITE_TAC[vars_from_list_def; has_var_FOLDL_Union; has_var_def]));;

(* [simp] *)
let has_var_vars_flatten = prove
 (`has_var n (vars_flatten d) = has_var n d`,
  (REWRITE_TAC[vars_flatten_def; MEM_vars_from_list;
    MEM_vars_to_list]));;

let ALL_DISTINCT_vars_to_list = prove
 (`ALL_DISTINCT (vars_to_list d)`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
