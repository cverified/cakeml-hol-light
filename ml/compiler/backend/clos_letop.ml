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

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "clos_letop"
  ["closLang"];;

(* let_op -- a function that optimises Let [...] (Op op [Var ...]) *)

make_size "clos_exp";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let clos_letop_var_list_def,clos_letop_var_list_ind = define_wf
  `MEASURE (\(x0,x1,x2). clos_exp_size1 x1)`
  `clos_letop_var_list n x2 x3 =
     match (x2,x3) with
       ([],[]) -> T
     | (CONS (clos_Var t m) xs,CONS y ys) -> ((m = n) /\ clos_letop_var_list
       (n + 1) xs ys)
     | (_,_) -> F`;;

let clos_letop_dest_op_def = new_definition
  `clos_letop_dest_op x1 args =
     match x1 with
       clos_Op t op xs -> (if clos_letop_var_list 0 xs args then SOME op
         else NONE)
     | _ -> NONE`;;

(* the clauses in three quotations: fns is ((num # exp) list) and (_#_)list;
   t is tra, (mlstring list) and mlstring; xs is (_)list and (exp list),
   which one quotation cannot typecheck *)
let clos_letop_let_op_def,clos_letop_let_op_ind = assume_definition_rec_clauses
  "termination (CHEAT_TAC)"
  [`(clos_letop_let_op [] = []) /\
    (clos_letop_let_op (CONS (x:clos_exp) (CONS y xs)) = CONS (HD
    (clos_letop_let_op [x])) (clos_letop_let_op (CONS y xs))) /\
    (clos_letop_let_op [clos_Var t v] = [(clos_Var t v:clos_exp)]) /\
    (clos_letop_let_op [clos_If t x1 x2 x3] =
         [clos_If t (HD (clos_letop_let_op [x1]))
               (HD (clos_letop_let_op [x2]))
               (HD (clos_letop_let_op [x3]))]) /\
    (clos_letop_let_op [clos_Let t xs x2] =
         let xs = clos_letop_let_op xs in
         let x2 = HD (clos_letop_let_op [x2]) in
           match clos_letop_dest_op x2 xs with SOME op -> [clos_Op t op xs]
           | NONE -> [(clos_Let t xs x2:clos_exp)]) /\
    (clos_letop_let_op [clos_Raise t x1] =
         [clos_Raise t (HD (clos_letop_let_op [x1]))]) /\
    (clos_letop_let_op [clos_Handle t x1 x2] =
         [clos_Handle t (HD (clos_letop_let_op [x1]))
                  (HD (clos_letop_let_op [x2]))]) /\
    (clos_letop_let_op [clos_Op t op xs] =
         [clos_Op t op (clos_letop_let_op xs)]) /\
    (clos_letop_let_op [clos_Tick t x] = [clos_Tick t (HD (clos_letop_let_op
    [x]))]) /\
    (clos_letop_let_op [clos_Call t ticks dest xs] = [clos_Call t ticks dest
    (clos_letop_let_op xs)]) /\
    (clos_letop_let_op [clos_App t loc_opt x1 xs] = [clos_App t loc_opt (HD
    (clos_letop_let_op [x1])) (clos_letop_let_op xs)])`;
   `clos_letop_let_op [clos_Letrec t loc_opt vs fns x1] =
         let new_fns = MAP (\(num_args,x). (num_args,HD (clos_letop_let_op
             [x]))) fns in
         [clos_Letrec t loc_opt vs new_fns (HD (clos_letop_let_op
             [x1]))]`;
   `clos_letop_let_op [clos_Fn t loc_opt vs num_args x1] = [clos_Fn t
    loc_opt vs num_args (HD (clos_letop_let_op [x1]))]`];;

(* HOL4 clos_letopScript.sml:57: ML code, not ported *)

let LENGTH_let_op = prove
 (`!xs. LENGTH (clos_letop_let_op xs) = LENGTH xs`,
  CHEAT_TAC);;

(* the clauses in three quotations: fns is ((num # exp) list) and (_)list; t
   is tra, (mlstring list) and mlstring; xs is (exp list), (_)list and
   (_#_)list, which one quotation cannot typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL x -> clos_exp_size x
                                   | INR (INL x) -> list_size clos_exp_size x
                                   | INR (INR x) -> list_size (pair_size (\x.
                                     x)
                                     clos_exp_size) x)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let clos_letop_let_op_sing_def,clos_letop_let_op_sing_ind =
  define_shaped_rec_clauses
  "maplist>maplist>nested"
  [`(clos_letop_let_op_sing (clos_Var t v) = ((clos_Var t v:clos_exp))) /\
    (clos_letop_let_op_sing (clos_If t x1 x2 x3) =
         (clos_If t ((clos_letop_let_op_sing (x1)))
               ((clos_letop_let_op_sing (x2)))
               ((clos_letop_let_op_sing (x3))))) /\
    (clos_letop_let_op_sing (clos_Let t xs x2) =
         let xs = clos_letop_let_op_list xs in
         let x2 = (clos_letop_let_op_sing (x2)) in
           match clos_letop_dest_op x2 xs with SOME op -> (clos_Op t op xs)
           | NONE -> ((clos_Let t xs x2:clos_exp))) /\
    (clos_letop_let_op_sing (clos_Raise t x1) =
         (clos_Raise t ((clos_letop_let_op_sing (x1))))) /\
    (clos_letop_let_op_sing (clos_Handle t x1 x2) =
         (clos_Handle t ((clos_letop_let_op_sing (x1)))
                  ((clos_letop_let_op_sing (x2))))) /\
    (clos_letop_let_op_sing (clos_Op t op xs) =
         (clos_Op t op (clos_letop_let_op_list xs))) /\
    (clos_letop_let_op_sing (clos_Tick t x) = (clos_Tick t
    ((clos_letop_let_op_sing (x))))) /\
    (clos_letop_let_op_sing (clos_Call t ticks dest xs) = (clos_Call t ticks
    dest (clos_letop_let_op_list xs))) /\
    (clos_letop_let_op_sing (clos_App t loc_opt x1 xs) = (clos_App t loc_opt
    ((clos_letop_let_op_sing (x1))) (clos_letop_let_op_list xs))) /\
    (clos_letop_let_op_list [] = []) /\
    (clos_letop_let_op_list (CONS (x:clos_exp) xs) = CONS
    (clos_letop_let_op_sing x) (clos_letop_let_op_list xs)) /\
    (let_op_let [] = [])`;
   `(clos_letop_let_op_sing (clos_Letrec t loc_opt vs fns x1) =
         let new_fns = let_op_let fns in
         (clos_Letrec t loc_opt vs new_fns ((clos_letop_let_op_sing
             (x1))))) /\
    (let_op_let (CONS (num_args,(x:clos_exp)) xs) = CONS
    (num_args,clos_letop_let_op_sing x) (let_op_let xs))`;
   `clos_letop_let_op_sing (clos_Fn t loc_opt vs num_args x1) = (clos_Fn t
    loc_opt vs num_args ((clos_letop_let_op_sing (x1))))`];;

let let_op_sing_eq = prove
 (`(!e. clos_letop_let_op [e] = [clos_letop_let_op_sing e]) /\
   (!es. clos_letop_let_op es = clos_letop_let_op_list es) /\
   (!fns.
     let_op_let fns =
     MAP (\(num_args,x). (num_args,HD (clos_letop_let_op [x]))) fns)`,
  CHEAT_TAC);;

let clos_letop_compile_inc_def = new_definition
  `clos_letop_compile_inc (e,xs) = (clos_letop_let_op e,[])`;;

(* and the interface *)
let _ = unhide_overloads ();;
