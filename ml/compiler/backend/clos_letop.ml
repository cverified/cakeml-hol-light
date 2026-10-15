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

needs "compiler/backend/bvl_inline.ml";;
needs "compiler/backend/closLang.ml";;
needs "semantics/ast.ml";;

(* let_op -- a function that optimises Let [...] (Op op [Var ...]) *)

let var_list_def = cake_define
  `clos_letop_var_list n x2 x3 =
        match (x2,x3) with
          ([],[]) -> T
        | ((Var t m :: xs),(y :: ys)) -> ((m = n) /\
          clos_letop_var_list (n + 1) xs ys)
        | (_1,_2) -> F`;;
hol4_overload "var_list" "clos_letop_var_list";;

let dest_op_def = cake_define
  `clos_letop_dest_op x1 args =
        match x1 with
          (Op t op xs) -> (if var_list 0 xs args then SOME op else
            NONE)
        | _3 -> NONE`;;
hol4_overload "dest_op" "clos_letop_dest_op";;

let let_op_def = cake_define
  `(clos_letop_let_op [] = []) /\
   (clos_letop_let_op ((x:closLang_exp) :: y :: xs) =
      HD (clos_letop_let_op [x]) :: clos_letop_let_op (y :: xs)) /\
   (clos_letop_let_op [Var t v] = [Var t v]) /\
   (clos_letop_let_op [If t x1 x2 x3] =
      [If t (HD (clos_letop_let_op [x1]))
            (HD (clos_letop_let_op [x2]))
            (HD (clos_letop_let_op [x3]))]) /\
   (clos_letop_let_op [Let t xs x2] =
      (let xs = clos_letop_let_op xs in
      let x2 = HD (clos_letop_let_op [x2]) in
        match dest_op x2 xs with SOME op -> [Op t op xs] | NONE ->
          [Let t xs x2])) /\
   (clos_letop_let_op [Raise t x1] =
      [Raise t (HD (clos_letop_let_op [x1]))]) /\
   (clos_letop_let_op [Handle t x1 x2] =
      [Handle t (HD (clos_letop_let_op [x1]))
               (HD (clos_letop_let_op [x2]))]) /\
   (clos_letop_let_op [Op t op xs] =
      [Op t op (clos_letop_let_op xs)]) /\
   (clos_letop_let_op [Tick t x] = [Tick t (HD (clos_letop_let_op
     [x]))]) /\
   (clos_letop_let_op [Call t ticks dest xs] = [Call t ticks dest
     (clos_letop_let_op xs)]) /\
   (clos_letop_let_op [App t loc_opt x1 xs] = [App t loc_opt (HD
     (clos_letop_let_op [x1])) (clos_letop_let_op xs)]) /\
   (clos_letop_let_op [Letrec t loc_opt vs fns x1] =
      (let new_fns = MAP (\(num_args,x). (num_args,HD
        (clos_letop_let_op [x]))) fns in
      [Letrec t loc_opt vs new_fns (HD (clos_letop_let_op [x1]))]))
        /\
   (clos_letop_let_op [closLang_Fn t loc_opt vs num_args x1] =
     [closLang_Fn t loc_opt vs num_args (HD (clos_letop_let_op
     [x1]))])`;;
hol4_overload "let_op" "clos_letop_let_op";;

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
          (Var t v) -> (Var t v)
        | (If t x1 x2 x3) ->
        (If t ((clos_letop_let_op_sing (x1)))
              ((clos_letop_let_op_sing (x2)))
              ((clos_letop_let_op_sing (x3))))
        | (Let t xs x2) ->
        let xs = clos_letop_let_op_list xs in
        let x2 = (clos_letop_let_op_sing (x2)) in
          match dest_op x2 xs with SOME op -> (Op t op xs) | NONE ->
            (Let t xs x2)
        | (Raise t x1) ->
        (Raise t ((clos_letop_let_op_sing (x1))))
        | (Handle t x1 x2) ->
        (Handle t ((clos_letop_let_op_sing (x1)))
                 ((clos_letop_let_op_sing (x2))))
        | (Op t op xs) ->
        (Op t op (clos_letop_let_op_list xs))
        | (Tick t x) -> (Tick t ((clos_letop_let_op_sing (x))))
        | (Call t ticks dest xs) -> (Call t ticks dest
          (clos_letop_let_op_list xs))
        | (App t loc_opt x1 xs) -> (App t loc_opt
          ((clos_letop_let_op_sing (x1))) (clos_letop_let_op_list xs))
        | (Letrec t loc_opt vs fns x1) ->
        let new_fns = let_op_let fns in
        (Letrec t loc_opt vs new_fns ((clos_letop_let_op_sing (x1))))
        | (closLang_Fn t loc_opt vs num_args x1) -> (closLang_Fn t
          loc_opt vs num_args ((clos_letop_let_op_sing (x1))))
        | [] -> []
        | ((x:closLang_exp) :: xs) ->
      clos_letop_let_op_sing x :: clos_letop_let_op_list xs
        | [] -> []
        | ((num_args,(x:closLang_exp)) :: xs) ->
      (num_args,clos_letop_let_op_sing x) :: let_op_let xs`;;
hol4_overload "let_op_list" "clos_letop_let_op_list";;
hol4_overload "let_op_sing" "clos_letop_let_op_sing";;

let compile_inc_def = cake_define
  `clos_letop_compile_inc (e,xs) = (let_op e,[])`;;
hol4_overload "compile_inc" "clos_letop_compile_inc";;
