(* ======================================================== *)
(*  db_vars: ported from HOL4's
    compiler/backend/db_varsScript.sml  *)
(* ======================================================== *)

(*
  Defines a datatype that is handy when keeping track of which dB vars
  are live when traversing a language using dB vars.
*)

needs "lib/sptree.ml";;

let db_var_set_INDUCT,db_var_set_RECURSION = define_datatype
  "db_var_set = db_vars_Empty | db_vars_Var (num) | db_vars_Shift \
   (num) (db_var_set) | db_vars_Union (db_var_set) (db_var_set)";;
hol4_overload "Empty" "db_vars_Empty";;
hol4_overload "Var" "db_vars_Var";;
hol4_overload "Shift" "db_vars_Shift";;
hol4_overload "Union" "db_vars_Union";;

let mk_Union_def = cake_define
  `mk_Union t1 t2 =
     (if t1 = Empty then t2 else
     if t2 = Empty then t1 else
       Union t1 t2)`;;

let list_mk_Union_def = cake_define
  `(list_mk_Union [] = Empty) /\
   (list_mk_Union (x :: xs) = mk_Union x (list_mk_Union xs))`;;

let db_to_set_acc_def = cake_define
  `(db_to_set_acc (n:num) (Empty:db_var_set) s = s) /\
   (db_to_set_acc n (Var v) s =
      (if v < n then s else insert (v - n) one s)) /\
   (db_to_set_acc n (Shift k d) s = db_to_set_acc (n + k) d s) /\
   (db_to_set_acc n (Union v1 v2) s =
      db_to_set_acc n v1 (db_to_set_acc n v2 s))`;;

let db_to_set_def = cake_define
  `db_to_set db = db_to_set_acc 0 db LN`;;

let vars_to_list_def = cake_define
  `vars_to_list db = MAP FST (toAList (db_to_set db))`;;

let vars_from_list_def = cake_define
  `vars_from_list vs = FOLDL (\s1 v. Union (Var v) s1) Empty vs`;;

let vars_flatten_def = cake_define
  `vars_flatten db = vars_from_list (vars_to_list db)`;;

let has_var_def = cake_define
  `(has_var n Empty <=> F) /\
   (has_var n (Var v) <=> (n = v)) /\
   (has_var n (Shift k d) <=> has_var (n + k) d) /\
   (has_var n (Union d1 d2) <=> has_var n d1 \/ has_var n d2)`;;
