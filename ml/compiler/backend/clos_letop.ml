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

let _ = size_thms "closLang_exp";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let clos_letop_var_list_def,clos_letop_var_list_ind = define_wf
  `MEASURE (\(x0,x1,x2). closLang_exp_size1 x1)`
  [`clos_letop_var_list n x2 x3 =
        match (x2,x3) with
          ([],[]) -> T
        | (CONS (closLang_Var t m:closLang_exp) xs,CONS y ys) -> ((m
          = n) /\ clos_letop_var_list (n + 1) xs ys)
        | (_1,_2) -> F`];;

let clos_letop_dest_op_def = new_definition
  `clos_letop_dest_op x1 args =
        match x1 with
          (closLang_Op t op xs:closLang_exp) -> (if
            clos_letop_var_list 0 xs args then SOME op else NONE)
        | _3 -> NONE`;;

let clos_letop_let_op_def,clos_letop_let_op_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`clos_letop_let_op [] = []`;
   `clos_letop_let_op (CONS (x:closLang_exp) (CONS y xs)) = CONS (HD
    (clos_letop_let_op [x])) (clos_letop_let_op (CONS y xs))`;
   `clos_letop_let_op [(closLang_Var t v:closLang_exp)] =
    [(closLang_Var t v:closLang_exp)]`;
   `clos_letop_let_op [(closLang_If t x1 x2 x3:closLang_exp)] =
         [closLang_If t (HD (clos_letop_let_op [x1]))
               (HD (clos_letop_let_op [x2]))
               (HD (clos_letop_let_op [x3]))]`;
   `clos_letop_let_op [(closLang_Let t xs x2:closLang_exp)] =
         (let xs = clos_letop_let_op xs in
         let x2 = HD (clos_letop_let_op [x2]) in
           match clos_letop_dest_op x2 xs with SOME op ->
               [closLang_Op t op xs] | NONE -> [(closLang_Let t xs
               x2:closLang_exp)])`;
   `clos_letop_let_op [(closLang_Raise t x1:closLang_exp)] =
         [closLang_Raise t (HD (clos_letop_let_op [x1]))]`;
   `clos_letop_let_op [(closLang_Handle t x1 x2:closLang_exp)] =
         [closLang_Handle t (HD (clos_letop_let_op [x1]))
                  (HD (clos_letop_let_op [x2]))]`;
   `clos_letop_let_op [(closLang_Op t op xs:closLang_exp)] =
         [closLang_Op t op (clos_letop_let_op xs)]`;
   `clos_letop_let_op [(closLang_Tick t x:closLang_exp)] =
    [closLang_Tick t (HD (clos_letop_let_op [x]))]`;
   `clos_letop_let_op [(closLang_Call t ticks dest xs:closLang_exp)]
    = [closLang_Call t ticks dest (clos_letop_let_op xs)]`;
   `clos_letop_let_op [(closLang_App t loc_opt x1 xs:closLang_exp)] =
    [closLang_App t loc_opt (HD (clos_letop_let_op [x1]))
    (clos_letop_let_op xs)]`;
   `clos_letop_let_op [(closLang_Letrec t loc_opt vs fns
    x1:closLang_exp)] =
         (let new_fns = MAP (\(num_args,x). (num_args,HD
             (clos_letop_let_op [x]))) fns in
         [closLang_Letrec t loc_opt vs new_fns (HD
             (clos_letop_let_op [x1]))])`;
   `clos_letop_let_op [closLang_Fn t loc_opt vs num_args x1] =
    [closLang_Fn t loc_opt vs num_args (HD (clos_letop_let_op
    [x1]))]`];;

(* HOL4 clos_letopScript.sml:57: ML code, not ported *)

let LENGTH_let_op = prove
 (`!xs. LENGTH (clos_letop_let_op xs) = LENGTH xs`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL x -> closLang_exp_size x | INR (INL x)
       -> list_size closLang_exp_size x | INR (INR x) -> list_size
       (pair_size (\x. x) closLang_exp_size) x)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let clos_letop_let_op_sing_def,clos_letop_let_op_sing_ind =
  define_shaped_rec
  "maplist>maplist>nested"
  [`clos_letop_let_op_sing (closLang_Var t v:closLang_exp) =
    ((closLang_Var t v:closLang_exp))`;
   `clos_letop_let_op_sing (closLang_If t x1 x2 x3:closLang_exp) =
         (closLang_If t ((clos_letop_let_op_sing (x1)))
               ((clos_letop_let_op_sing (x2)))
               ((clos_letop_let_op_sing (x3))))`;
   `clos_letop_let_op_sing (closLang_Let t xs x2:closLang_exp) =
         (let xs = clos_letop_let_op_list xs in
         let x2 = (clos_letop_let_op_sing (x2)) in
           match clos_letop_dest_op x2 xs with SOME op ->
               (closLang_Op t op xs) | NONE -> ((closLang_Let t xs
               x2:closLang_exp)))`;
   `clos_letop_let_op_sing (closLang_Raise t x1:closLang_exp) =
         (closLang_Raise t ((clos_letop_let_op_sing (x1))))`;
   `clos_letop_let_op_sing (closLang_Handle t x1 x2:closLang_exp) =
         (closLang_Handle t ((clos_letop_let_op_sing (x1)))
                  ((clos_letop_let_op_sing (x2))))`;
   `clos_letop_let_op_sing (closLang_Op t op xs:closLang_exp) =
         (closLang_Op t op (clos_letop_let_op_list xs))`;
   `clos_letop_let_op_sing (closLang_Tick t x:closLang_exp) =
    (closLang_Tick t ((clos_letop_let_op_sing (x))))`;
   `clos_letop_let_op_sing (closLang_Call t ticks dest
    xs:closLang_exp) = (closLang_Call t ticks dest
    (clos_letop_let_op_list xs))`;
   `clos_letop_let_op_sing (closLang_App t loc_opt x1
    xs:closLang_exp) = (closLang_App t loc_opt
    ((clos_letop_let_op_sing (x1))) (clos_letop_let_op_list xs))`;
   `clos_letop_let_op_sing (closLang_Letrec t loc_opt vs fns
    x1:closLang_exp) =
         (let new_fns = let_op_let fns in
         (closLang_Letrec t loc_opt vs new_fns
             ((clos_letop_let_op_sing (x1)))))`;
   `clos_letop_let_op_sing (closLang_Fn t loc_opt vs num_args x1) =
    (closLang_Fn t loc_opt vs num_args ((clos_letop_let_op_sing
    (x1))))`;
   `clos_letop_let_op_list [] = []`;
   `clos_letop_let_op_list (CONS (x:closLang_exp) xs) = CONS
    (clos_letop_let_op_sing x) (clos_letop_let_op_list xs)`;
   `let_op_let [] = []`;
   `let_op_let (CONS (num_args,(x:closLang_exp)) xs) = CONS
    (num_args,clos_letop_let_op_sing x) (let_op_let xs)`];;

let let_op_sing_eq = prove
 (`(!e. clos_letop_let_op [e] = [clos_letop_let_op_sing e]) /\
   (!es. clos_letop_let_op es = clos_letop_let_op_list es) /\
   (!fns.
     let_op_let fns =
     MAP (\(num_args,x). (num_args,HD (clos_letop_let_op [x])))
       fns)`,
  CHEAT_TAC);;

let clos_letop_compile_inc_def = new_definition
  `clos_letop_compile_inc (e,xs) = (clos_letop_let_op e,[])`;;

(* and the interface *)
let _ = unhide_overloads ();;
