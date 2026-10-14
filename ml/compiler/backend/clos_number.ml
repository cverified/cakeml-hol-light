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

(* add fresh code locations *)

(* HOL4 termination: >> rw [] >> TRY decide_tac >> Induct_on `fns` >>
   srw_tac [ARITH_ss] [exp_size_def] >> Cases_on `h` >> rw
   [exp_size_def, basicSizeTheory.pair_size_def] *)
let renumber_code_locs_def = cake_define_wf
  `inv_image (<) (\x. match x with INL p -> list_size exp_size (SND p)
  | INR p -> exp_size (SND p))`
  `(renumber_code_locs_list n [] = (n,[])) /\
   (renumber_code_locs_list n (x :: xs) =
      (let (n,x) = renumber_code_locs n x in
      let (n,xs) = renumber_code_locs_list n xs in
      (n,x :: xs))) /\
   (renumber_code_locs n (closLang_Var t v) = (n,(closLang_Var t v)))
     /\
   (renumber_code_locs n (closLang_If t x1 x2 x3) =
      (let (n,x1) = renumber_code_locs n x1 in
      let (n,x2) = renumber_code_locs n x2 in
      let (n,x3) = renumber_code_locs n x3 in
        (n,closLang_If t x1 x2 x3))) /\
   (renumber_code_locs n (closLang_Let t xs x2) =
      (let (n,xs) = renumber_code_locs_list n xs in
      let (n,x2) = renumber_code_locs n x2 in
        (n,closLang_Let t xs x2))) /\
   (renumber_code_locs n (closLang_Raise t x1) =
      (let (n,x1) = renumber_code_locs n x1 in
        (n,closLang_Raise t x1))) /\
   (renumber_code_locs n (closLang_Tick t x1) =
      (let (n,x1) = renumber_code_locs n x1 in
        (n,closLang_Tick t x1))) /\
   (renumber_code_locs n (closLang_Op t closLang_op xs) =
      (let (n,xs) = renumber_code_locs_list n xs in
        (n,closLang_Op t closLang_op xs))) /\
   (renumber_code_locs n (closLang_App t loc_opt x1 x2) =
      (let (n,x1) = renumber_code_locs n x1 in
      let (n,x2) = renumber_code_locs_list n x2 in
        (n,closLang_App t NONE x1 x2))) /\
   (renumber_code_locs n (closLang_Fn t loc vs num_args x1) =
      (let (n,x1) = renumber_code_locs n x1 in
        (n + 2,closLang_Fn t (SOME n) vs num_args x1))) /\
   (renumber_code_locs n (closLang_Letrec t loc vs fns x1) =
      (let (m,fns') = renumber_code_locs_list n (MAP SND fns) in
      let (n,x1) = renumber_code_locs (m + 2 * LENGTH fns') x1 in
        (n,closLang_Letrec t (SOME m) vs (ZIP (MAP FST fns,fns'))
          x1))) /\
   (renumber_code_locs n (closLang_Handle t x1 x2) =
      (let (n,x1) = renumber_code_locs n x1 in
      let (n,x2) = renumber_code_locs n x2 in
        (n,closLang_Handle t x1 x2))) /\
   (renumber_code_locs n (closLang_Call t ticks dest xs) =
      (let (n,xs) = renumber_code_locs_list n xs in
        (n,closLang_Op t (closLang_IntOp closLang_Add) xs)))`;;

(* HOL4 ML code, not ported:
val renumber_code_locs_ind = theorem"renumber_code_locs_ind";
*)

let compile_inc_def = cake_define
  `clos_number_compile_inc n xs =
     (let n1 = make_even (n + MAX (LENGTH xs) 1) in
     let (m,ys) = renumber_code_locs_list n1 xs in
       (m,closLang_Op backend_common_None (closLang_IntOp
         (closLang_Const (&n))) [] :: ys))`;;

let ignore_table_def = cake_define
  `ignore_table f st (code,aux) = (let (st',code') = f st code in
  (st',(code',aux)))`;;
