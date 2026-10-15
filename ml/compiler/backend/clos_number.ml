(* ======================================================== *)
(*  clos_number: ported from HOL4's
    compiler/backend/clos_numberScript.sml  *)
(* ======================================================== *)

(*
  This simple compiler phase walks the program and gives each closure
  a unique numeric name.
*)

needs "compiler/backend/closLang.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(* add fresh code locations *)

let renumber_code_locs_def = cake_define_list
  [`renumber_code_locs_list n [] = (n,[])`;
   `renumber_code_locs_list n (x :: xs) =
         (let (n,x) = renumber_code_locs n x in
         let (n,xs) = renumber_code_locs_list n xs in
         (n,x :: xs))`;
   `renumber_code_locs n (Var t v:closLang_exp) = (n,(Var t v))`;
   `renumber_code_locs n (If t x1 x2 x3:closLang_exp) =
         (let (n,x1) = renumber_code_locs n x1 in
         let (n,x2) = renumber_code_locs n x2 in
         let (n,x3) = renumber_code_locs n x3 in
           (n,If t x1 x2 x3))`;
   `renumber_code_locs n (Let t xs x2:closLang_exp) =
         (let (n,xs) = renumber_code_locs_list n xs in
         let (n,x2) = renumber_code_locs n x2 in
           (n,Let t xs x2))`;
   `renumber_code_locs n (Raise t x1:closLang_exp) =
         (let (n,x1) = renumber_code_locs n x1 in
           (n,Raise t x1))`;
   `renumber_code_locs n (Tick t x1:closLang_exp) =
         (let (n,x1) = renumber_code_locs n x1 in
           (n,Tick t x1))`;
   `renumber_code_locs n (Op t op xs:closLang_exp) =
         (let (n,xs) = renumber_code_locs_list n xs in
           (n,Op t op xs))`;
   `renumber_code_locs n (App t loc_opt x1 x2:closLang_exp) =
         (let (n,x1) = renumber_code_locs n x1 in
         let (n,x2) = renumber_code_locs_list n x2 in
           (n,App t NONE x1 x2))`;
   `renumber_code_locs n (Fn t loc vs num_args x1:closLang_exp) =
         (let (n,x1) = renumber_code_locs n x1 in
           (n + 2,Fn t (SOME n) vs num_args x1))`;
   `renumber_code_locs n (Letrec t loc vs fns x1:closLang_exp) =
         (let (m,fns') = renumber_code_locs_list n (MAP SND fns) in
         let (n,x1) = renumber_code_locs (m + 2 * LENGTH fns') x1 in
           (n,Letrec t (SOME m) vs (ZIP (MAP FST fns) fns') x1))`;
   `renumber_code_locs n (Handle t x1 x2:closLang_exp) =
         (let (n,x1) = renumber_code_locs n x1 in
         let (n,x2) = renumber_code_locs n x2 in
           (n,Handle t x1 x2))`;
   `renumber_code_locs n (Call t ticks dest xs:closLang_exp) =
         (let (n,xs) = renumber_code_locs_list n xs in
           (n,Op t (IntOp Add) xs))`];;

(* HOL4 ML code, not ported:
val renumber_code_locs_ind = theorem"renumber_code_locs_ind";
*)

let compile_inc_def = cake_define
  `clos_number_compile_inc n xs =
     (let n1 = make_even (n + MAX (LENGTH xs) 1) in
     let (m,ys) = renumber_code_locs_list n1 xs in
       (m,Op backend_common_None (IntOp (Const (&n))) [] :: ys))`;;
hol4_overload "compile_inc" "clos_number_compile_inc";;

let ignore_table_def = cake_define
  `ignore_table f st (code,aux) = (let (st',code') = f st code in
  (st',(code',aux)))`;;
