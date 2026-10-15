(* ======================================================== *)
(*  clos_fvs: ported from HOL4's
    compiler/backend/clos_fvsScript.sml  *)
(* ======================================================== *)

(*
  Replaces free variables with constant type errors.
*)

needs "compiler/backend/closLang.ml";;
needs "semantics/ast.ml";;

let remove_fvs_def = cake_define_list
  [`remove_fvs fvs [] = []`;
   `remove_fvs fvs ((x:closLang_exp) :: y :: xs) =
         HD (remove_fvs fvs [x]) :: remove_fvs fvs (y :: xs)`;
   `remove_fvs fvs [(Var t v:closLang_exp)] =
        (if v < fvs then [Var t v] else [Op t (MemOp El) []])`;
   `remove_fvs fvs [(If t x1 x2 x3:closLang_exp)] =
         [If t (HD (remove_fvs fvs [x1]))
               (HD (remove_fvs fvs [x2]))
               (HD (remove_fvs fvs [x3]))]`;
   `remove_fvs fvs [(Let t xs x2:closLang_exp)] =
         (let xs = remove_fvs fvs xs in
         let n = LENGTH xs in
         let x2 = HD (remove_fvs (fvs + n) [x2]) in
           [Let t xs x2])`;
   `remove_fvs fvs [(Raise t x1:closLang_exp)] =
         [Raise t (HD (remove_fvs fvs [x1]))]`;
   `remove_fvs fvs [(Handle t x1 x2:closLang_exp)] =
         [Handle t (HD (remove_fvs fvs [x1]))
                  (HD (remove_fvs (fvs + 1) [x2]))]`;
   `remove_fvs fvs [(Op t op xs:closLang_exp)] =
         [Op t op (remove_fvs fvs xs)]`;
   `remove_fvs fvs [(Tick t x:closLang_exp)] = [Tick t (HD
  (remove_fvs fvs [x]))]`;
   `remove_fvs fvs [(Call t ticks dest xs:closLang_exp)] = [Call t
  ticks dest (remove_fvs fvs xs)]`;
   `remove_fvs fvs [(App t loc_opt x1 xs:closLang_exp)] = [App t
  loc_opt (HD (remove_fvs fvs [x1])) (remove_fvs fvs xs)]`;
   `remove_fvs fvs [(Letrec t loc_opt vs fns x1:closLang_exp)] =
         (let m = LENGTH fns in
         let new_fvs = match vs with NONE -> fvs | SOME x -> LENGTH
           x in
         let new_fns =
           MAP (\(num_args,x).
             (num_args,HD (remove_fvs (num_args + m + new_fvs)
               [x]))) fns in
         [Letrec t loc_opt vs new_fns (HD (remove_fvs (m + fvs)
           [x1]))])`;
   `remove_fvs fvs [(Fn t loc_opt vs num_args x1:closLang_exp)] =
        (let fvs = match vs with NONE -> fvs | SOME x -> LENGTH x in
        [Fn t loc_opt vs num_args (HD (remove_fvs (num_args +
          fvs) [x1]))])`];;

let remove_fvs_sing_def = cake_define_list
  [`remove_fvs_sing fvs (Var t v:closLang_exp) =
        (if v < fvs then Var t v else Op t (MemOp El) [])`;
   `remove_fvs_sing fvs (If t x1 x2 x3:closLang_exp) =
         If t (remove_fvs_sing fvs x1)
              (remove_fvs_sing fvs x2)
              (remove_fvs_sing fvs x3)`;
   `remove_fvs_sing fvs (Let t xs x2:closLang_exp) =
         (let xs = remove_fvs_list fvs xs in
         let n = LENGTH xs in
         let x2 = remove_fvs_sing (fvs + n) x2 in
           Let t xs x2)`;
   `remove_fvs_sing fvs (Raise t x1:closLang_exp) =
         Raise t (remove_fvs_sing fvs x1)`;
   `remove_fvs_sing fvs (Handle t x1 x2:closLang_exp) =
         Handle t (remove_fvs_sing fvs x1)
                  (remove_fvs_sing (fvs + 1) x2)`;
   `remove_fvs_sing fvs (Op t op xs:closLang_exp) =
         Op t op (remove_fvs_list fvs xs)`;
   `remove_fvs_sing fvs (Tick t x:closLang_exp) = Tick t
  (remove_fvs_sing fvs x)`;
   `remove_fvs_sing fvs (Call t ticks dest xs:closLang_exp) =
        Call t ticks dest (remove_fvs_list fvs xs)`;
   `remove_fvs_sing fvs (App t loc_opt x1 xs:closLang_exp) =
        App t loc_opt (remove_fvs_sing fvs x1) (remove_fvs_list
          fvs xs)`;
   `remove_fvs_sing fvs (Letrec t loc_opt vs fns x1:closLang_exp) =
         (let m = LENGTH fns in
         let new_fvs = match vs with NONE -> fvs | SOME x -> LENGTH
           x in
         let new_fns = remove_fvs_let m new_fvs fns in
         Letrec t loc_opt vs new_fns (remove_fvs_sing (m + fvs)
           x1))`;
   `remove_fvs_sing fvs (Fn t loc_opt vs num_args x1:closLang_exp) =
        (let fvs = match vs with NONE -> fvs | SOME x -> LENGTH x in
        Fn t loc_opt vs num_args (remove_fvs_sing (num_args +
          fvs) x1))`;
   `remove_fvs_list fvs [] = []`;
   `remove_fvs_list fvs ((x:closLang_exp) :: xs) =
         remove_fvs_sing fvs x :: remove_fvs_list fvs xs`;
   `remove_fvs_let m fvs [] = []`;
   `remove_fvs_let m new_fvs ((num_args,x) :: xs) =
         (num_args,remove_fvs_sing (num_args + m + new_fvs) x) ::
           remove_fvs_let m new_fvs xs`];;

let compile_def = cake_define
  `clos_fvs_compile exps = remove_fvs 0 exps`;;
hol4_overload "compile" "clos_fvs_compile";;

let compile_inc_def = cake_define
  `clos_fvs_compile_inc (e,xs) = (compile e,[])`;;
hol4_overload "compile_inc" "clos_fvs_compile_inc";;
