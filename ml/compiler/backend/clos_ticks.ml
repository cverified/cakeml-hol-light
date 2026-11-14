(* ======================================================== *)
(*  clos_ticks: ported from HOL4's
    compiler/backend/clos_ticksScript.sml
    A definition theory, with 3 definitions and 2 theorems.  Needed
    by clos_known.ml and clos_ticksProof.ml.  *)
(* ======================================================== *)

(*
  This simple compiler phase removes all Tick operations. Tick
  operations appear as a side effect of function inlining, and can be
  removed because they have no observable behaviour. It is a good idea
  to remove them because they get in the way of pattern matching done
  by several optimisations.
*)

needs "compiler/backend/closLang.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "clos_ticks"
  ["closLang"];;

let clos_ticks_remove_ticks_def,clos_ticks_remove_ticks_ind =
  define_shaped_rec
  "sing>nested"
  [`clos_ticks_remove_ticks [] = []`;
   `clos_ticks_remove_ticks (CONS (x:closLang_exp) (CONS y xs)) =
    CONS (HD (clos_ticks_remove_ticks [x])) (clos_ticks_remove_ticks
    (CONS y xs))`;
   `clos_ticks_remove_ticks [(closLang_Var t v:closLang_exp)] =
    [(closLang_Var t v:closLang_exp)]`;
   `clos_ticks_remove_ticks [(closLang_If t x1 x2 x3:closLang_exp)] =
         [closLang_If t (HD (clos_ticks_remove_ticks [x1]))
               (HD (clos_ticks_remove_ticks [x2]))
               (HD (clos_ticks_remove_ticks [x3]))]`;
   `clos_ticks_remove_ticks [(closLang_Let t xs x2:closLang_exp)] =
         [closLang_Let t (clos_ticks_remove_ticks xs) (HD
             (clos_ticks_remove_ticks [x2]))]`;
   `clos_ticks_remove_ticks [(closLang_Raise t x1:closLang_exp)] =
         [closLang_Raise t (HD (clos_ticks_remove_ticks [x1]))]`;
   `clos_ticks_remove_ticks [(closLang_Handle t x1 x2:closLang_exp)] =
         [closLang_Handle t (HD (clos_ticks_remove_ticks [x1]))
                   (HD (clos_ticks_remove_ticks [x2]))]`;
   `clos_ticks_remove_ticks [(closLang_Op t op xs:closLang_exp)] =
         [closLang_Op t op (clos_ticks_remove_ticks xs)]`;
   `clos_ticks_remove_ticks [(closLang_Tick t x1:closLang_exp)] =
    clos_ticks_remove_ticks [x1]`;
   `clos_ticks_remove_ticks [(closLang_Call t ticks dest
    xs:closLang_exp)] =
         [closLang_Call t 0 dest (clos_ticks_remove_ticks xs)]`;
   `clos_ticks_remove_ticks [(closLang_App t loc_opt x1
    xs:closLang_exp)] =
         [closLang_App t loc_opt (HD (clos_ticks_remove_ticks
             [x1])) (clos_ticks_remove_ticks xs)]`;
   `clos_ticks_remove_ticks [(closLang_Letrec t loc_opt vs fns
    x1:closLang_exp)] =
         (let new_fns = MAP (\(num_args,x). (num_args,HD
             (clos_ticks_remove_ticks [x]))) fns in
         [closLang_Letrec t loc_opt vs new_fns (HD
             (clos_ticks_remove_ticks [x1]))])`;
   `clos_ticks_remove_ticks [closLang_Fn t loc_opt vs num_args x1] =
         [closLang_Fn t loc_opt vs num_args (HD
             (clos_ticks_remove_ticks [x1]))]`];;

let clos_ticks_remove_ticks_sing_def,clos_ticks_remove_ticks_sing_ind =
  define_shaped_rec
  "maplist>maplist>nested"
  [`clos_ticks_remove_ticks_sing (closLang_Var t v:closLang_exp) =
    ((closLang_Var t v:closLang_exp))`;
   `clos_ticks_remove_ticks_sing (closLang_If t x1 x2 x3:closLang_exp) =
         (closLang_If t ((clos_ticks_remove_ticks_sing (x1)))
               ((clos_ticks_remove_ticks_sing (x2)))
               ((clos_ticks_remove_ticks_sing (x3))))`;
   `clos_ticks_remove_ticks_sing (closLang_Let t xs x2:closLang_exp) =
         (closLang_Let t (clos_ticks_remove_ticks_list xs)
             ((clos_ticks_remove_ticks_sing (x2))))`;
   `clos_ticks_remove_ticks_sing (closLang_Raise t x1:closLang_exp) =
         (closLang_Raise t ((clos_ticks_remove_ticks_sing (x1))))`;
   `clos_ticks_remove_ticks_sing (closLang_Handle t x1 x2:closLang_exp)
    =
         (closLang_Handle t ((clos_ticks_remove_ticks_sing (x1)))
                   ((clos_ticks_remove_ticks_sing (x2))))`;
   `clos_ticks_remove_ticks_sing (closLang_Op t op xs:closLang_exp) =
         (closLang_Op t op (clos_ticks_remove_ticks_list xs))`;
   `clos_ticks_remove_ticks_sing (closLang_Tick t x1:closLang_exp) =
    clos_ticks_remove_ticks_sing (x1)`;
   `clos_ticks_remove_ticks_sing (closLang_Call t ticks dest
    xs:closLang_exp) =
         (closLang_Call t 0 dest (clos_ticks_remove_ticks_list
             xs))`;
   `clos_ticks_remove_ticks_sing (closLang_App t loc_opt x1
    xs:closLang_exp) =
         (closLang_App t loc_opt ((clos_ticks_remove_ticks_sing
             (x1))) (clos_ticks_remove_ticks_list xs))`;
   `clos_ticks_remove_ticks_sing (closLang_Letrec t loc_opt vs fns
    x1:closLang_exp) =
         (let new_fns = remove_ticks_let fns in
         (closLang_Letrec t loc_opt vs new_fns
             ((clos_ticks_remove_ticks_sing (x1)))))`;
   `clos_ticks_remove_ticks_sing (closLang_Fn t loc_opt vs num_args x1)
    =
         (closLang_Fn t loc_opt vs num_args
             ((clos_ticks_remove_ticks_sing (x1))))`;
   `clos_ticks_remove_ticks_list [] = []`;
   `clos_ticks_remove_ticks_list (CONS (x:closLang_exp) xs) = CONS
    (clos_ticks_remove_ticks_sing x) (clos_ticks_remove_ticks_list
    xs)`;
   `remove_ticks_let [] = []`;
   `remove_ticks_let (CONS (num_args,x) xs) = CONS
    (num_args,clos_ticks_remove_ticks_sing x) (remove_ticks_let xs)`];;

(* HOL4 clos_ticksScript.sml:77: ML code, not ported *)

(* LENGTH_remove_ticks *)
let clos_ticks_LENGTH_remove_ticks = prove
 (`!(es:closLang_exp list). LENGTH (clos_ticks_remove_ticks es) =
  LENGTH es`,
  CHEAT_TAC);;

let remove_ticks_sing_eq = prove
 (`(!e. clos_ticks_remove_ticks [e] = [clos_ticks_remove_ticks_sing e])
  /\
   (!es. clos_ticks_remove_ticks es = clos_ticks_remove_ticks_list
     es) /\
   (!fns.
     remove_ticks_let fns =
     MAP (\(num_args,x). (num_args,HD (clos_ticks_remove_ticks
       [x]))) fns)`,
  CHEAT_TAC);;

let clos_ticks_compile_inc_def = new_definition
  `clos_ticks_compile_inc (e,xs) = (clos_ticks_remove_ticks e,[])`;;
