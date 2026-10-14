(* ======================================================== *)
(*  clos_letop: ported from HOL4's
    compiler/backend/clos_letopScript.sml  *)
(* ======================================================== *)

(*
  This simple compiler phase tidies up after function inlining, in
  particular it turns `Let [x0; x1; ...] (Op op [Var 0; Var 1; ...])`
  into `Op op [x0; x1; ...]`, which enables further optimisation
  later, e.g. in bvi_tailrec.
*)

needs "compiler/backend/closLang.ml";;

(* let_op -- a function that optimises Let [...] (Op op [Var ...]) *)

let var_list_def = cake_define
  `clos_letop_var_list n x2 x3 =
        match (x2,x3) with
          ([],[]) -> T
        | ((closLang_Var t m :: xs),(y :: ys)) -> ((m = n) /\
          clos_letop_var_list (n + 1) xs ys)
        | (_1,_2) -> F`;;

let dest_op_def = cake_define
  `clos_letop_dest_op x1 args =
        match x1 with
          (closLang_Op t closLang_op xs) -> (if clos_letop_var_list 0
            xs args then SOME closLang_op else NONE)
        | _3 -> NONE`;;

let let_op_def = cake_define
  `(clos_letop_let_op [] = []) /\
   (clos_letop_let_op ((x:closLang_exp) :: y :: xs) =
      HD (clos_letop_let_op [x]) :: clos_letop_let_op (y :: xs)) /\
   (clos_letop_let_op [closLang_Var t v] = [closLang_Var t v]) /\
   (clos_letop_let_op [closLang_If t x1 x2 x3] =
      [closLang_If t (HD (clos_letop_let_op [x1]))
            (HD (clos_letop_let_op [x2]))
            (HD (clos_letop_let_op [x3]))]) /\
   (clos_letop_let_op [closLang_Let t xs x2] =
      (let xs = clos_letop_let_op xs in
      let x2 = HD (clos_letop_let_op [x2]) in
        match clos_letop_dest_op x2 xs with SOME closLang_op ->
          [closLang_Op t closLang_op xs] | NONE -> [closLang_Let t xs
          x2])) /\
   (clos_letop_let_op [closLang_Raise t x1] =
      [closLang_Raise t (HD (clos_letop_let_op [x1]))]) /\
   (clos_letop_let_op [closLang_Handle t x1 x2] =
      [closLang_Handle t (HD (clos_letop_let_op [x1]))
               (HD (clos_letop_let_op [x2]))]) /\
   (clos_letop_let_op [closLang_Op t closLang_op xs] =
      [closLang_Op t closLang_op (clos_letop_let_op xs)]) /\
   (clos_letop_let_op [closLang_Tick t x] = [closLang_Tick t (HD
     (clos_letop_let_op [x]))]) /\
   (clos_letop_let_op [closLang_Call t ticks dest xs] =
     [closLang_Call t ticks dest (clos_letop_let_op xs)]) /\
   (clos_letop_let_op [closLang_App t loc_opt x1 xs] = [closLang_App
     t loc_opt (HD (clos_letop_let_op [x1])) (clos_letop_let_op xs)]) /\
   (clos_letop_let_op [closLang_Letrec t loc_opt vs fns x1] =
      (let new_fns = MAP (\(num_args,x). (num_args,HD
        (clos_letop_let_op [x]))) fns in
      [closLang_Letrec t loc_opt vs new_fns (HD (clos_letop_let_op
        [x1]))])) /\
   (clos_letop_let_op [closLang_Fn t loc_opt vs num_args x1] =
     [closLang_Fn t loc_opt vs num_args (HD (clos_letop_let_op
     [x1]))])`;;

(* HOL4 ML code, not ported:
val let_op_ind = theorem "let_op_ind";
*)

(* TERMINATION: wf_rel_tac ‘measure $ λx. case x of
                            | INL x => exp_size x
                            | INR(INL x) => list_size exp_size x
                            | INR(INR x) => list_size (pair_size (λx. x)
                              exp_size) x’ *)
let let_op_sing_def = cake_define
  `clos_letop_let_op_sing x1 =
        match x1 with
          (closLang_Var t v) -> (closLang_Var t v)
        | (closLang_If t x1 x2 x3) ->
        (closLang_If t ((clos_letop_let_op_sing (x1)))
              ((clos_letop_let_op_sing (x2)))
              ((clos_letop_let_op_sing (x3))))
        | (closLang_Let t xs x2) ->
        let xs = clos_letop_let_op_list xs in
        let x2 = (clos_letop_let_op_sing (x2)) in
          match clos_letop_dest_op x2 xs with SOME closLang_op ->
            (closLang_Op t closLang_op xs) | NONE -> (closLang_Let t xs
            x2)
        | (closLang_Raise t x1) ->
        (closLang_Raise t ((clos_letop_let_op_sing (x1))))
        | (closLang_Handle t x1 x2) ->
        (closLang_Handle t ((clos_letop_let_op_sing (x1)))
                 ((clos_letop_let_op_sing (x2))))
        | (closLang_Op t closLang_op xs) ->
        (closLang_Op t closLang_op (clos_letop_let_op_list xs))
        | (closLang_Tick t x) -> (closLang_Tick t
          ((clos_letop_let_op_sing (x))))
        | (closLang_Call t ticks dest xs) -> (closLang_Call t ticks
          dest (clos_letop_let_op_list xs))
        | (closLang_App t loc_opt x1 xs) -> (closLang_App t loc_opt
          ((clos_letop_let_op_sing (x1))) (clos_letop_let_op_list xs))
        | (closLang_Letrec t loc_opt vs fns x1) ->
        let new_fns = let_op_let fns in
        (closLang_Letrec t loc_opt vs new_fns
          ((clos_letop_let_op_sing (x1))))
        | (closLang_Fn t loc_opt vs num_args x1) -> (closLang_Fn t
          loc_opt vs num_args ((clos_letop_let_op_sing (x1))))
        | [] -> []
        | ((x:closLang_exp) :: xs) ->
      clos_letop_let_op_sing x :: clos_letop_let_op_list xs
        | [] -> []
        | ((num_args,(x:closLang_exp)) :: xs) ->
      (num_args,clos_letop_let_op_sing x) :: let_op_let xs`;;

let compile_inc_def = cake_define
  `clos_letop_compile_inc (e,xs) = (clos_letop_let_op e,[])`;;
