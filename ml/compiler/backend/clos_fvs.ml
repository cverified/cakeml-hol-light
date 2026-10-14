(* ======================================================== *)
(*  clos_fvs: ported from HOL4's
    compiler/backend/clos_fvsScript.sml  *)
(* ======================================================== *)

(*
  Replaces free variables with constant type errors.
*)

needs "compiler/backend/closLang.ml";;

let remove_fvs_def = cake_define
  `(remove_fvs fvs [] = []) /\
   (remove_fvs fvs ((x:closLang_exp) :: y :: xs) =
      HD (remove_fvs fvs [x]) :: remove_fvs fvs (y :: xs)) /\
   (remove_fvs fvs [closLang_Var t v] =
     (if v < fvs then [closLang_Var t v] else [closLang_Op t
       (closLang_MemOp closLang_El) []])) /\
   (remove_fvs fvs [closLang_If t x1 x2 x3] =
      [closLang_If t (HD (remove_fvs fvs [x1]))
            (HD (remove_fvs fvs [x2]))
            (HD (remove_fvs fvs [x3]))]) /\
   (remove_fvs fvs [closLang_Let t xs x2] =
      (let xs = remove_fvs fvs xs in
      let n = LENGTH xs in
      let x2 = HD (remove_fvs (fvs + n) [x2]) in
        [closLang_Let t xs x2])) /\
   (remove_fvs fvs [closLang_Raise t x1] =
      [closLang_Raise t (HD (remove_fvs fvs [x1]))]) /\
   (remove_fvs fvs [closLang_Handle t x1 x2] =
      [closLang_Handle t (HD (remove_fvs fvs [x1]))
               (HD (remove_fvs (fvs + 1) [x2]))]) /\
   (remove_fvs fvs [closLang_Op t closLang_op xs] =
      [closLang_Op t closLang_op (remove_fvs fvs xs)]) /\
   (remove_fvs fvs [closLang_Tick t x] = [closLang_Tick t (HD
     (remove_fvs fvs [x]))]) /\
   (remove_fvs fvs [closLang_Call t ticks dest xs] = [closLang_Call t
     ticks dest (remove_fvs fvs xs)]) /\
   (remove_fvs fvs [closLang_App t loc_opt x1 xs] = [closLang_App t
     loc_opt (HD (remove_fvs fvs [x1])) (remove_fvs fvs xs)]) /\
   (remove_fvs fvs [closLang_Letrec t loc_opt vs fns x1] =
      (let m = LENGTH fns in
      let new_fvs = match vs with NONE -> fvs | SOME x -> LENGTH x in
      let new_fns =
        MAP (\(num_args,x).
          (num_args,HD (remove_fvs (num_args + m + new_fvs) [x])))
            fns in
      [closLang_Letrec t loc_opt vs new_fns (HD (remove_fvs (m + fvs)
        [x1]))])) /\
   (remove_fvs fvs [closLang_Fn t loc_opt vs num_args x1] =
     (let fvs = match vs with NONE -> fvs | SOME x -> LENGTH x in
     [closLang_Fn t loc_opt vs num_args (HD (remove_fvs (num_args
       + fvs) [x1]))]))`;;

(* HOL4 termination: *)
let remove_fvs_sing_def = cake_define_wf
  `MEASURE (\x. match x with INL (_1,e) -> exp_size e | INR (INL
  (_2,es)) -> list_size exp_size es | INR (INR (_3,_4,es)) -> list_size
  (pair_size (\x. x) exp_size) es)`
  `(remove_fvs_sing fvs (closLang_Var t v) =
     (if v < fvs then closLang_Var t v else closLang_Op t
       (closLang_MemOp closLang_El) [])) /\
   (remove_fvs_sing fvs (closLang_If t x1 x2 x3) =
      closLang_If t (remove_fvs_sing fvs x1)
           (remove_fvs_sing fvs x2)
           (remove_fvs_sing fvs x3)) /\
   (remove_fvs_sing fvs (closLang_Let t xs x2) =
      (let xs = remove_fvs_list fvs xs in
      let n = LENGTH xs in
      let x2 = remove_fvs_sing (fvs + n) x2 in
        closLang_Let t xs x2)) /\
   (remove_fvs_sing fvs (closLang_Raise t x1) =
      closLang_Raise t (remove_fvs_sing fvs x1)) /\
   (remove_fvs_sing fvs (closLang_Handle t x1 x2) =
      closLang_Handle t (remove_fvs_sing fvs x1)
               (remove_fvs_sing (fvs + 1) x2)) /\
   (remove_fvs_sing fvs (closLang_Op t closLang_op xs) =
      closLang_Op t closLang_op (remove_fvs_list fvs xs)) /\
   (remove_fvs_sing fvs (closLang_Tick t x) = closLang_Tick t
     (remove_fvs_sing fvs x)) /\
   (remove_fvs_sing fvs (closLang_Call t ticks dest xs) =
     closLang_Call t ticks dest (remove_fvs_list fvs xs)) /\
   (remove_fvs_sing fvs (closLang_App t loc_opt x1 xs) =
     closLang_App t loc_opt (remove_fvs_sing fvs x1) (remove_fvs_list
       fvs xs)) /\
   (remove_fvs_sing fvs (closLang_Letrec t loc_opt vs fns x1) =
      (let m = LENGTH fns in
      let new_fvs = match vs with NONE -> fvs | SOME x -> LENGTH x in
      let new_fns = remove_fvs_let m new_fvs fns in
      closLang_Letrec t loc_opt vs new_fns (remove_fvs_sing (m + fvs)
        x1))) /\
   (remove_fvs_sing fvs (closLang_Fn t loc_opt vs num_args x1) =
     (let fvs = match vs with NONE -> fvs | SOME x -> LENGTH x in
     closLang_Fn t loc_opt vs num_args (remove_fvs_sing (num_args +
       fvs) x1))) /\
   (remove_fvs_list fvs [] = []) /\
   (remove_fvs_list fvs ((x:closLang_exp) :: xs) =
      remove_fvs_sing fvs x :: remove_fvs_list fvs xs) /\
   (remove_fvs_let m fvs [] = []) /\
   (remove_fvs_let m new_fvs ((num_args,x) :: xs) =
      (num_args,remove_fvs_sing (num_args + m + new_fvs) x) ::
        remove_fvs_let m new_fvs xs)`;;

let compile_def = cake_define
  `clos_fvs_compile exps = remove_fvs 0 exps`;;

let compile_inc_def = cake_define
  `clos_fvs_compile_inc (e,xs) = (clos_fvs_compile e,[])`;;
