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

let remove_ticks_def = cake_define
  `(clos_ticks_remove_ticks [] = []) /\
   (clos_ticks_remove_ticks ((x:closLang_exp) :: y :: xs) =
      HD (clos_ticks_remove_ticks [x]) :: clos_ticks_remove_ticks (y
        :: xs)) /\
   (clos_ticks_remove_ticks [closLang_Var t v] = [closLang_Var t v])
     /\
   (clos_ticks_remove_ticks [closLang_If t x1 x2 x3] =
      [closLang_If t (HD (clos_ticks_remove_ticks [x1]))
            (HD (clos_ticks_remove_ticks [x2]))
            (HD (clos_ticks_remove_ticks [x3]))]) /\
   (clos_ticks_remove_ticks [closLang_Let t xs x2] =
      [closLang_Let t (clos_ticks_remove_ticks xs) (HD
        (clos_ticks_remove_ticks [x2]))]) /\
   (clos_ticks_remove_ticks [closLang_Raise t x1] =
      [closLang_Raise t (HD (clos_ticks_remove_ticks [x1]))]) /\
   (clos_ticks_remove_ticks [closLang_Handle t x1 x2] =
      [closLang_Handle t (HD (clos_ticks_remove_ticks [x1]))
                (HD (clos_ticks_remove_ticks [x2]))]) /\
   (clos_ticks_remove_ticks [closLang_Op t closLang_op xs] =
      [closLang_Op t closLang_op (clos_ticks_remove_ticks xs)]) /\
   (clos_ticks_remove_ticks [closLang_Tick t x1] =
     clos_ticks_remove_ticks [x1]) /\
   (clos_ticks_remove_ticks [closLang_Call t ticks dest xs] =
      [closLang_Call t 0 dest (clos_ticks_remove_ticks xs)]) /\
   (clos_ticks_remove_ticks [closLang_App t loc_opt x1 xs] =
      [closLang_App t loc_opt (HD (clos_ticks_remove_ticks [x1]))
        (clos_ticks_remove_ticks xs)]) /\
   (clos_ticks_remove_ticks [closLang_Letrec t loc_opt vs fns x1] =
      (let new_fns = MAP (\(num_args,x). (num_args,HD
        (clos_ticks_remove_ticks [x]))) fns in
      [closLang_Letrec t loc_opt vs new_fns (HD
        (clos_ticks_remove_ticks [x1]))])) /\
   (clos_ticks_remove_ticks [closLang_Fn t loc_opt vs num_args x1] =
      [closLang_Fn t loc_opt vs num_args (HD
        (clos_ticks_remove_ticks [x1]))])`;;

let remove_ticks_sing_def = cake_define
  `clos_ticks_remove_ticks_sing x1 =
        match x1 with
          (closLang_Var t v) -> (closLang_Var t v)
        | (closLang_If t x1 x2 x3) ->
        (closLang_If t ((clos_ticks_remove_ticks_sing (x1)))
              ((clos_ticks_remove_ticks_sing (x2)))
              ((clos_ticks_remove_ticks_sing (x3))))
        | (closLang_Let t xs x2) ->
        (closLang_Let t (clos_ticks_remove_ticks_list xs)
          ((clos_ticks_remove_ticks_sing (x2))))
        | (closLang_Raise t x1) ->
        (closLang_Raise t ((clos_ticks_remove_ticks_sing (x1))))
        | (closLang_Handle t x1 x2) ->
        (closLang_Handle t ((clos_ticks_remove_ticks_sing (x1)))
                  ((clos_ticks_remove_ticks_sing (x2))))
        | (closLang_Op t closLang_op xs) ->
        (closLang_Op t closLang_op (clos_ticks_remove_ticks_list xs))
        | (closLang_Tick t x1) -> clos_ticks_remove_ticks_sing (x1)
        | (closLang_Call t ticks dest xs) ->
        (closLang_Call t 0 dest (clos_ticks_remove_ticks_list xs))
        | (closLang_App t loc_opt x1 xs) ->
        (closLang_App t loc_opt ((clos_ticks_remove_ticks_sing (x1)))
          (clos_ticks_remove_ticks_list xs))
        | (closLang_Letrec t loc_opt vs fns x1) ->
        let new_fns = remove_ticks_let fns in
        (closLang_Letrec t loc_opt vs new_fns
          ((clos_ticks_remove_ticks_sing (x1))))
        | (closLang_Fn t loc_opt vs num_args x1) ->
        (closLang_Fn t loc_opt vs num_args
          ((clos_ticks_remove_ticks_sing (x1))))
        | [] -> []
        | ((x:closLang_exp) :: xs) ->
        clos_ticks_remove_ticks_sing x ::
          clos_ticks_remove_ticks_list xs
        | [] -> []
        | ((num_args,x) :: xs) ->
      (num_args,clos_ticks_remove_ticks_sing x) ::
        remove_ticks_let xs`;;

(* HOL4 ML code, not ported:
val remove_ticks_ind = theorem "remove_ticks_ind";
*)

let compile_inc_def = cake_define
  `clos_ticks_compile_inc (e,xs) = (clos_ticks_remove_ticks e,[])`;;
