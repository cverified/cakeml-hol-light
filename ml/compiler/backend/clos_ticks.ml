(* ======================================================== *)
(*  clos_ticks: ported from HOL4's
    compiler/backend/clos_ticksScript.sml  *)
(* ======================================================== *)

(*
  This simple compiler phase removes all Tick operations. Tick
  operations appear as a side effect of function inlining, and can be
  removed because they have no observable behaviour. It is a good idea
  to remove them because they get in the way of pattern matching done
  by several optimisations.
*)

needs "compiler/backend/closLang.ml";;
needs "semantics/ast.ml";;

let remove_ticks_def = cake_define_list
  [`clos_ticks_remove_ticks [] = []`;
   `clos_ticks_remove_ticks ((x:closLang_exp) :: y :: xs) =
         HD (clos_ticks_remove_ticks [x]) ::
           clos_ticks_remove_ticks (y :: xs)`;
   `clos_ticks_remove_ticks [(Var t v:closLang_exp)] = [(Var t
  v:closLang_exp)]`;
   `clos_ticks_remove_ticks [(If t x1 x2 x3:closLang_exp)] =
         [If t (HD (clos_ticks_remove_ticks [x1]))
               (HD (clos_ticks_remove_ticks [x2]))
               (HD (clos_ticks_remove_ticks [x3]))]`;
   `clos_ticks_remove_ticks [(Let t xs x2:closLang_exp)] =
         [Let t (clos_ticks_remove_ticks xs) (HD
           (clos_ticks_remove_ticks [x2]))]`;
   `clos_ticks_remove_ticks [(Raise t x1:closLang_exp)] =
         [Raise t (HD (clos_ticks_remove_ticks [x1]))]`;
   `clos_ticks_remove_ticks [(Handle t x1 x2:closLang_exp)] =
         [Handle t (HD (clos_ticks_remove_ticks [x1]))
                   (HD (clos_ticks_remove_ticks [x2]))]`;
   `clos_ticks_remove_ticks [(closLang_Op t op xs:closLang_exp)] =
         [closLang_Op t op (clos_ticks_remove_ticks xs)]`;
   `clos_ticks_remove_ticks [(closLang_Tick t x1:closLang_exp)] =
  clos_ticks_remove_ticks [x1]`;
   `clos_ticks_remove_ticks [(closLang_Call t ticks dest
  xs:closLang_exp)] =
         [closLang_Call t 0 dest (clos_ticks_remove_ticks xs)]`;
   `clos_ticks_remove_ticks [(App t loc_opt x1 xs:closLang_exp)] =
         [App t loc_opt (HD (clos_ticks_remove_ticks [x1]))
           (clos_ticks_remove_ticks xs)]`;
   `clos_ticks_remove_ticks [(Letrec t loc_opt vs fns x1:closLang_exp)]
  =
         (let new_fns = MAP (\(num_args,x). (num_args,HD
           (clos_ticks_remove_ticks [x]))) fns in
         [Letrec t loc_opt vs new_fns (HD
           (clos_ticks_remove_ticks [x1]))])`;
   `clos_ticks_remove_ticks [closLang_Fn t loc_opt vs num_args x1] =
         [closLang_Fn t loc_opt vs num_args (HD
           (clos_ticks_remove_ticks [x1]))]`];;
hol4_overload "remove_ticks" "clos_ticks_remove_ticks";;

let remove_ticks_sing_def = cake_define_list
  [`clos_ticks_remove_ticks_sing (Var t v:closLang_exp) = ((Var t
  v:closLang_exp))`;
   `clos_ticks_remove_ticks_sing (If t x1 x2 x3:closLang_exp) =
         (If t ((clos_ticks_remove_ticks_sing (x1)))
               ((clos_ticks_remove_ticks_sing (x2)))
               ((clos_ticks_remove_ticks_sing (x3))))`;
   `clos_ticks_remove_ticks_sing (Let t xs x2:closLang_exp) =
         (Let t (clos_ticks_remove_ticks_list xs)
           ((clos_ticks_remove_ticks_sing (x2))))`;
   `clos_ticks_remove_ticks_sing (Raise t x1:closLang_exp) =
         (Raise t ((clos_ticks_remove_ticks_sing (x1))))`;
   `clos_ticks_remove_ticks_sing (Handle t x1 x2:closLang_exp) =
         (Handle t ((clos_ticks_remove_ticks_sing (x1)))
                   ((clos_ticks_remove_ticks_sing (x2))))`;
   `clos_ticks_remove_ticks_sing (closLang_Op t op xs:closLang_exp) =
         (closLang_Op t op (clos_ticks_remove_ticks_list xs))`;
   `clos_ticks_remove_ticks_sing (closLang_Tick t x1:closLang_exp) =
  clos_ticks_remove_ticks_sing (x1)`;
   `clos_ticks_remove_ticks_sing (closLang_Call t ticks dest
  xs:closLang_exp) =
         (closLang_Call t 0 dest (clos_ticks_remove_ticks_list
           xs))`;
   `clos_ticks_remove_ticks_sing (App t loc_opt x1 xs:closLang_exp) =
         (App t loc_opt ((clos_ticks_remove_ticks_sing (x1)))
           (clos_ticks_remove_ticks_list xs))`;
   `clos_ticks_remove_ticks_sing (Letrec t loc_opt vs fns
  x1:closLang_exp) =
         (let new_fns = remove_ticks_let fns in
         (Letrec t loc_opt vs new_fns
           ((clos_ticks_remove_ticks_sing (x1)))))`;
   `clos_ticks_remove_ticks_sing (closLang_Fn t loc_opt vs num_args x1)
  =
         (closLang_Fn t loc_opt vs num_args
           ((clos_ticks_remove_ticks_sing (x1))))`;
   `clos_ticks_remove_ticks_list [] = []`;
   `clos_ticks_remove_ticks_list ((x:closLang_exp) :: xs) =
         clos_ticks_remove_ticks_sing x ::
           clos_ticks_remove_ticks_list xs`;
   `remove_ticks_let [] = []`;
   `remove_ticks_let ((num_args,x) :: xs) =
       (num_args,clos_ticks_remove_ticks_sing x) ::
         remove_ticks_let xs`];;
hol4_overload "remove_ticks_list" "clos_ticks_remove_ticks_list";;
hol4_overload "remove_ticks_sing" "clos_ticks_remove_ticks_sing";;

(* HOL4 clos_ticksScript.sml:77: ML code, not ported *)

let compile_inc_def = cake_define
  `clos_ticks_compile_inc (e,xs) = (clos_ticks_remove_ticks e,[])`;;
hol4_overload "compile_inc" "clos_ticks_compile_inc";;
