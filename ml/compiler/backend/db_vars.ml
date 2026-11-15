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

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "db_vars" [];;

let db_var_set_INDUCT,db_var_set_RECURSION = define_datatype
  "db_var_set =
     db_vars_Empty
   | db_vars_Var num
   | db_vars_Shift num db_var_set
   | db_vars_Union db_var_set db_var_set";;

let mk_Union_def = new_definition
  `mk_Union t1 t2 =
     if t1 = db_vars_Empty then t2 else if t2 = db_vars_Empty then t1
       else db_vars_Union t1 t2`;;

let mk_Union_Empty = prove
 (`mk_Union db_vars_Empty A = A /\ mk_Union A db_vars_Empty = A`,
  CHEAT_TAC);;
add_simp mk_Union_Empty;;

let list_mk_Union_def,list_mk_Union_ind = define_rec
  `(list_mk_Union [] = db_vars_Empty) /\
   (list_mk_Union (CONS x xs) = mk_Union x (list_mk_Union xs))`;;

let FOLDR_mk_Union_UNZIP = prove
 (`ITLIST (\(x,l) (ts,frees). (CONS x ts,mk_Union l frees)) l ([],A) =
   let (ts,fvs) = UNZIP l in
     (ts,list_mk_Union (APPEND fvs [A]))`,
  CHEAT_TAC);;

let db_to_set_acc_def,db_to_set_acc_ind = define_rec
  `(db_to_set_acc (n:num) (db_vars_Empty:db_var_set) s = s) /\
   (db_to_set_acc (n:num) (db_vars_Var v) s =
         if v < n then s else sptree_insert (v - n) one s) /\
   (db_to_set_acc (n:num) (db_vars_Shift k d) s = db_to_set_acc (n + k) d s) /\
   (db_to_set_acc (n:num) (db_vars_Union v1 v2) s =
         db_to_set_acc n v1 (db_to_set_acc n v2 s))`;;

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
  `vars_from_list vs = FOLDL (\s1 v. db_vars_Union (db_vars_Var v) s1)
  db_vars_Empty vs`;;

let vars_flatten_def = new_definition
  `vars_flatten db = vars_from_list (vars_to_list db)`;;

let has_var_def,has_var_ind = define_rec
  `(has_var n db_vars_Empty <=> F) /\
   (has_var n (db_vars_Var v) <=> (n = v)) /\
   (has_var n (db_vars_Shift k d) <=> has_var (n + k) d) /\
   (has_var n (db_vars_Union d1 d2) <=> has_var n d1 \/ has_var n d2)`;;
add_simp has_var_def;;

let has_var_mk_Union = prove
 (`has_var n (mk_Union l1 l2) <=> has_var n l1 \/ has_var n l2`,
  CHEAT_TAC);;
add_simp has_var_mk_Union;;

let has_var_list_mk_Union = prove
 (`!ls. has_var n (list_mk_Union ls) <=> EX (has_var n) ls`,
  CHEAT_TAC);;
add_simp has_var_list_mk_Union;;

let lookup_db_to_set_acc = prove
 (`!d n k s.
     sptree_lookup n (db_to_set_acc k d s) =
       if has_var (n + k) d then SOME one else sptree_lookup n s`,
  CHEAT_TAC);;

let lookup_db_to_set = prove
 (`has_var n d = (sptree_lookup n (db_to_set d) = SOME one)`,
  CHEAT_TAC);;

let lookup_db_to_set_Shift = prove
 (`sptree_lookup n (db_to_set (db_vars_Shift k s)) = sptree_lookup (n + k)
  (db_to_set s)`,
  CHEAT_TAC);;

let MEM_vars_to_list = prove
 (`MEM n (vars_to_list d) = has_var n d`,
  CHEAT_TAC);;

(* [local] *)
let has_var_FOLDL_Union = prove
 (`!vs n s. has_var n (FOLDL (\s1 v. db_vars_Union (db_vars_Var v) s1) s vs)
  <=>
              MEM n vs \/ has_var n s`,
  CHEAT_TAC);;

let MEM_vars_from_list = prove
 (`!vs n. has_var n (vars_from_list vs) <=> MEM n vs`,
  CHEAT_TAC);;

let has_var_vars_flatten = prove
 (`has_var n (vars_flatten d) = has_var n d`,
  CHEAT_TAC);;
add_simp has_var_vars_flatten;;

let ALL_DISTINCT_vars_to_list = prove
 (`ALL_DISTINCT (vars_to_list d)`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
