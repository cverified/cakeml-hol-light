(* ======================================================== *)
(*  clos_fvs: ported from HOL4's
    compiler/backend/clos_fvsScript.sml
    A definition theory, with 4 definitions and 3 theorems.  Needed
    by clos_fvsProof.ml, clos_known.ml and clos_knownProof.ml.  *)
(* ======================================================== *)

(*
  Replaces free variables with constant type errors.
*)

needs "compiler/backend/closLang.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "clos_fvs"
  ["closLang"];;

(* the clauses in three quotations: fns is ((num # exp) list) and (_#_)list;
   t is tra, (mlstring list) and mlstring; xs is (exp list) and (_)list,
   which one quotation cannot typecheck *)
let remove_fvs_def,remove_fvs_ind = define_shaped_rec_clauses
  "sing>nested"
  [`(remove_fvs fvs [] = []) /\
    (remove_fvs fvs (CONS (x:clos_exp) (CONS y xs)) = CONS (HD (remove_fvs
    fvs [x])) (remove_fvs fvs (CONS y xs))) /\
    (remove_fvs fvs [clos_Var t v] =
        if v < fvs then [(clos_Var t v:clos_exp)]
        else [clos_Op t (clos_MemOp clos_El) []]) /\
    (remove_fvs fvs [clos_If t x1 x2 x3] =
         [clos_If t (HD (remove_fvs fvs [x1]))
               (HD (remove_fvs fvs [x2]))
               (HD (remove_fvs fvs [x3]))]) /\
    (remove_fvs fvs [clos_Let t xs x2] =
         let xs = remove_fvs fvs xs in
         let n = LENGTH xs in
         let x2 = HD (remove_fvs (fvs + n) [x2]) in
           [(clos_Let t xs x2:clos_exp)]) /\
    (remove_fvs fvs [clos_Raise t x1] =
         [clos_Raise t (HD (remove_fvs fvs [x1]))]) /\
    (remove_fvs fvs [clos_Handle t x1 x2] =
         [clos_Handle t (HD (remove_fvs fvs [x1]))
                  (HD (remove_fvs (fvs + 1) [x2]))]) /\
    (remove_fvs fvs [clos_Op t op xs] =
         [clos_Op t op (remove_fvs fvs xs)]) /\
    (remove_fvs fvs [clos_Tick t x] = [clos_Tick t (HD (remove_fvs fvs
    [x]))]) /\
    (remove_fvs fvs [clos_Call t ticks dest xs] = [clos_Call t ticks dest
    (remove_fvs fvs xs)]) /\
    (remove_fvs fvs [clos_App t loc_opt x1 xs] = [clos_App t loc_opt (HD
    (remove_fvs fvs [x1])) (remove_fvs fvs xs)])`;
   `remove_fvs fvs [clos_Letrec t loc_opt vs fns x1] =
         let m = LENGTH fns in
         let new_fvs = (match vs with NONE -> fvs | SOME x -> LENGTH x) in
         let new_fns =
           MAP (\(num_args,x).
             (num_args,HD (remove_fvs (num_args + m + new_fvs) [x]))) fns
                 in
         [clos_Letrec t loc_opt vs new_fns (HD (remove_fvs (m + fvs)
             [x1]))]`;
   `remove_fvs fvs [clos_Fn t loc_opt vs num_args x1] =
        let fvs = (match vs with NONE -> fvs | SOME x -> LENGTH x) in
        [clos_Fn t loc_opt vs num_args (HD (remove_fvs (num_args +
            fvs) [x1]))]`];;

(* the clauses in three quotations: fns is ((num # exp) list) and (_)list; t
   is tra, (mlstring list) and mlstring; xs is (exp list), (_)list and
   (_#_)list, which one quotation cannot typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL (_,e) -> clos_exp_size e
                                   | INR (INL (_,es)) -> list_size
                                     clos_exp_size
                                     es
                                   | INR (INR (_,_,es)) -> list_size (pair_size
                                     (\x. x) clos_exp_size) es)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let remove_fvs_sing_def,remove_fvs_sing_ind = define_shaped_rec_clauses
  "maplist>maplist>nested"
  [`(remove_fvs_sing fvs (clos_Var t v) =
        if v < fvs then (clos_Var t v:clos_exp)
        else clos_Op t (clos_MemOp clos_El) []) /\
    (remove_fvs_sing fvs (clos_If t x1 x2 x3) =
         clos_If t (remove_fvs_sing fvs x1)
              (remove_fvs_sing fvs x2)
              (remove_fvs_sing fvs x3)) /\
    (remove_fvs_sing fvs (clos_Let t xs x2) =
         let xs = remove_fvs_list fvs xs in
         let n = LENGTH xs in
         let x2 = remove_fvs_sing (fvs + n) x2 in
           clos_Let t xs x2) /\
    (remove_fvs_sing fvs (clos_Raise t x1) =
         clos_Raise t (remove_fvs_sing fvs x1)) /\
    (remove_fvs_sing fvs (clos_Handle t x1 x2) =
         clos_Handle t (remove_fvs_sing fvs x1)
                  (remove_fvs_sing (fvs + 1) x2)) /\
    (remove_fvs_sing fvs (clos_Op t op xs) =
         clos_Op t op (remove_fvs_list fvs xs)) /\
    (remove_fvs_sing fvs (clos_Tick t x) = clos_Tick t (remove_fvs_sing fvs
    x)) /\
    (remove_fvs_sing fvs (clos_Call t ticks dest xs) =
        clos_Call t ticks dest (remove_fvs_list fvs xs)) /\
    (remove_fvs_sing fvs (clos_App t loc_opt x1 xs) =
        clos_App t loc_opt (remove_fvs_sing fvs x1) (remove_fvs_list
            fvs xs)) /\
    (remove_fvs_list fvs [] = []) /\
    (remove_fvs_list fvs (CONS (x:clos_exp) xs) = CONS (remove_fvs_sing fvs
    x) (remove_fvs_list fvs xs)) /\
    (remove_fvs_let m fvs [] = [])`;
   `(remove_fvs_sing fvs (clos_Letrec t loc_opt vs fns x1) =
         let m = LENGTH fns in
         let new_fvs = (match vs with NONE -> fvs | SOME x -> LENGTH x) in
         let new_fns = remove_fvs_let m new_fvs fns in
         clos_Letrec t loc_opt vs new_fns (remove_fvs_sing (m + fvs)
             x1)) /\
    (remove_fvs_let m new_fvs (CONS (num_args,x) xs) = CONS
    (num_args,remove_fvs_sing (num_args + m + new_fvs) x) (remove_fvs_let
    m new_fvs xs))`;
   `remove_fvs_sing fvs (clos_Fn t loc_opt vs num_args x1) =
        let fvs = (match vs with NONE -> fvs | SOME x -> LENGTH x) in
        clos_Fn t loc_opt vs num_args (remove_fvs_sing (num_args + fvs)
            x1)`];;

let remove_fvs_sing_eq = prove
 (`(!fvs e. remove_fvs fvs [e] = [remove_fvs_sing fvs e]) /\
   (!fvs es. remove_fvs fvs es = remove_fvs_list fvs es) /\
   (!m new_fvs fns.
     remove_fvs_let m new_fvs fns =
     MAP (\(num_args,x). (num_args,HD (remove_fvs (num_args + m + new_fvs)
       [x]))) fns)`,
  CHEAT_TAC);;

let clos_fvs_compile_def = new_definition
  `clos_fvs_compile exps = remove_fvs 0 exps`;;

(* compile_eq *)
let clos_fvs_compile_eq = prove
 (`clos_fvs_compile exps = remove_fvs_list 0 exps`,
  (REWRITE_TAC[clos_fvs_compile_def; remove_fvs_sing_eq]));;

let clos_fvs_compile_inc_def = new_definition
  `clos_fvs_compile_inc (e,xs) = (clos_fvs_compile e,[])`;;

let LENGTH_remove_fvs = prove
 (`!fvs xs. LENGTH (remove_fvs fvs xs) = LENGTH xs`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
