(* ======================================================== *)
(*  clos_letop: ported from HOL4's
    compiler/backend/clos_letopScript.sml
    A definition theory, with 5 definitions and 2 theorems.  Needed
    by clos_known.ml and clos_letopProof.ml.  *)
(* ======================================================== *)

(*
  This simple compiler phase tidies up after function inlining, in
  particular it turns `Let [x0; x1; ...] (Op op [Var 0; Var 1; ...])`
  into `Op op [x0; x1; ...]`, which enables further optimisation
  later, e.g. in bvi_tailrec.
*)

needs "compiler/backend/closLang.ml";;
needs "semantics/ast.ml";;

(* let_op -- a function that optimises Let [...] (Op op [Var ...]) *)

let var_list_def = cake_define
  `clos_letop_var_list n x2 x3 =
        match (x2,x3) with
          ([],[]) -> T
        | (((Var t m:closLang_exp) :: xs),(y :: ys)) -> ((m = n) /\
          clos_letop_var_list (n + 1) xs ys)
        | (_1,_2) -> F`;;
hol4_overload "var_list" "clos_letop_var_list";;

let dest_op_def = cake_define
  `clos_letop_dest_op x1 args =
        match x1 with
          (closLang_Op t op xs:closLang_exp) -> (if
            clos_letop_var_list 0 xs args then SOME op else NONE)
        | _3 -> NONE`;;
hol4_overload "dest_op" "clos_letop_dest_op";;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let let_op_def = cake_define_list_cheat CHEAT_TAC
  [`clos_letop_let_op [] = []`;
   `clos_letop_let_op ((x:closLang_exp) :: y :: xs) =
         HD (clos_letop_let_op [x]) :: clos_letop_let_op (y ::
           xs)`;
   `clos_letop_let_op [(Var t v:closLang_exp)] = [(Var t
  v:closLang_exp)]`;
   `clos_letop_let_op [(If t x1 x2 x3:closLang_exp)] =
         [If t (HD (clos_letop_let_op [x1]))
               (HD (clos_letop_let_op [x2]))
               (HD (clos_letop_let_op [x3]))]`;
   `clos_letop_let_op [(Let t xs x2:closLang_exp)] =
         (let xs = clos_letop_let_op xs in
         let x2 = HD (clos_letop_let_op [x2]) in
           match clos_letop_dest_op x2 xs with SOME op ->
             [closLang_Op t op xs] | NONE -> [(Let t xs
             x2:closLang_exp)])`;
   `clos_letop_let_op [(Raise t x1:closLang_exp)] =
         [Raise t (HD (clos_letop_let_op [x1]))]`;
   `clos_letop_let_op [(Handle t x1 x2:closLang_exp)] =
         [Handle t (HD (clos_letop_let_op [x1]))
                  (HD (clos_letop_let_op [x2]))]`;
   `clos_letop_let_op [(closLang_Op t op xs:closLang_exp)] =
         [closLang_Op t op (clos_letop_let_op xs)]`;
   `clos_letop_let_op [(closLang_Tick t x:closLang_exp)] =
  [closLang_Tick t (HD (clos_letop_let_op [x]))]`;
   `clos_letop_let_op [(closLang_Call t ticks dest xs:closLang_exp)]
  = [closLang_Call t ticks dest (clos_letop_let_op xs)]`;
   `clos_letop_let_op [(App t loc_opt x1 xs:closLang_exp)] = [App t
  loc_opt (HD (clos_letop_let_op [x1])) (clos_letop_let_op xs)]`;
   `clos_letop_let_op [(Letrec t loc_opt vs fns x1:closLang_exp)] =
         (let new_fns = MAP (\(num_args,x). (num_args,HD
           (clos_letop_let_op [x]))) fns in
         [Letrec t loc_opt vs new_fns (HD (clos_letop_let_op
           [x1]))])`;
   `clos_letop_let_op [closLang_Fn t loc_opt vs num_args x1] =
  [closLang_Fn t loc_opt vs num_args (HD (clos_letop_let_op [x1]))]`];;
hol4_overload "let_op" "clos_letop_let_op";;

(* HOL4 clos_letopScript.sml:57: ML code, not ported *)

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let let_op_sing_def = cake_define_list_try (fun () ->
  `MEASURE (\x. match x with INL x -> closLang_exp_size x | INR (INL x)
     -> list_size closLang_exp_size x | INR (INR x) -> list_size
     (pair_size (\x. x) closLang_exp_size) x)`)
  [`clos_letop_let_op_sing (Var t v:closLang_exp) = ((Var t
  v:closLang_exp))`;
   `clos_letop_let_op_sing (If t x1 x2 x3:closLang_exp) =
         (If t ((clos_letop_let_op_sing (x1)))
               ((clos_letop_let_op_sing (x2)))
               ((clos_letop_let_op_sing (x3))))`;
   `clos_letop_let_op_sing (Let t xs x2:closLang_exp) =
         (let xs = clos_letop_let_op_list xs in
         let x2 = (clos_letop_let_op_sing (x2)) in
           match clos_letop_dest_op x2 xs with SOME op ->
             (closLang_Op t op xs) | NONE -> ((Let t xs
             x2:closLang_exp)))`;
   `clos_letop_let_op_sing (Raise t x1:closLang_exp) =
         (Raise t ((clos_letop_let_op_sing (x1))))`;
   `clos_letop_let_op_sing (Handle t x1 x2:closLang_exp) =
         (Handle t ((clos_letop_let_op_sing (x1)))
                  ((clos_letop_let_op_sing (x2))))`;
   `clos_letop_let_op_sing (closLang_Op t op xs:closLang_exp) =
         (closLang_Op t op (clos_letop_let_op_list xs))`;
   `clos_letop_let_op_sing (closLang_Tick t x:closLang_exp) =
  (closLang_Tick t ((clos_letop_let_op_sing (x))))`;
   `clos_letop_let_op_sing (closLang_Call t ticks dest
  xs:closLang_exp) = (closLang_Call t ticks dest
  (clos_letop_let_op_list xs))`;
   `clos_letop_let_op_sing (App t loc_opt x1 xs:closLang_exp) = (App
  t loc_opt ((clos_letop_let_op_sing (x1))) (clos_letop_let_op_list
  xs))`;
   `clos_letop_let_op_sing (Letrec t loc_opt vs fns x1:closLang_exp) =
         (let new_fns = let_op_let fns in
         (Letrec t loc_opt vs new_fns ((clos_letop_let_op_sing
           (x1)))))`;
   `clos_letop_let_op_sing (closLang_Fn t loc_opt vs num_args x1) =
  (closLang_Fn t loc_opt vs num_args ((clos_letop_let_op_sing (x1))))`;
   `clos_letop_let_op_list [] = []`;
   `clos_letop_let_op_list ((x:closLang_exp) :: xs) =
       clos_letop_let_op_sing x :: clos_letop_let_op_list xs`;
   `let_op_let [] = []`;
   `let_op_let ((num_args,(x:closLang_exp)) :: xs) =
       (num_args,clos_letop_let_op_sing x) :: let_op_let xs`];;
hol4_overload "let_op_list" "clos_letop_let_op_list";;
hol4_overload "let_op_sing" "clos_letop_let_op_sing";;

let compile_inc_def = cake_define
  `clos_letop_compile_inc (e,xs) = (clos_letop_let_op e,[])`;;
hol4_overload "compile_inc" "clos_letop_compile_inc";;
