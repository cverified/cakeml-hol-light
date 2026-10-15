(* ======================================================== *)
(*  clos_call: ported from HOL4's
    compiler/backend/clos_callScript.sml  *)
(* ======================================================== *)

(*
  This compiler phase moves code from closures into a separate code
  table and tries to change calls to known closures into fast C-style
  function calls.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/db_vars.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

let free_def = cake_define_list
  [`clos_call_free [] = ([],db_vars_Empty)`;
   `clos_call_free ((x:closLang_exp) :: y :: xs) =
         (let (c1,l1) = clos_call_free [x] in
         let (c2,l2) = clos_call_free (y :: xs) in
           (c1 ++ c2,mk_Union l1 l2))`;
   `clos_call_free [(Var t v:closLang_exp)] = ([Var t v],Var v)`;
   `clos_call_free [(If t x1 x2 x3:closLang_exp)] =
         (let (c1,l1) = clos_call_free [x1] in
         let (c2,l2) = clos_call_free [x2] in
         let (c3,l3) = clos_call_free [x3] in
           ([If t (HD c1) (HD c2) (HD c3)],mk_Union l1 (mk_Union
             l2 l3)))`;
   `clos_call_free [(Let t xs x2:closLang_exp)] =
         (let (c1,l1) = clos_call_free xs in
         let (c2,l2) = clos_call_free [x2] in
           ([Let t c1 (HD c2)],mk_Union l1 (Shift (LENGTH xs)
             l2)))`;
   `clos_call_free [(Raise t x1:closLang_exp)] =
         (let (c1,l1) = clos_call_free [x1] in
           ([Raise t (HD c1)],l1))`;
   `clos_call_free [closLang_Tick t x1] =
         (let (c1,l1) = clos_call_free [x1] in
           ([closLang_Tick t (HD c1)],l1))`;
   `clos_call_free [closLang_Op t op xs] =
         (let (c1,l1) = clos_call_free xs in
           ([closLang_Op t op c1],l1))`;
   `clos_call_free [(App t loc_opt x1 xs2:closLang_exp)] =
         (let (c1,l1) = clos_call_free [x1] in
         let (c2,l2) = clos_call_free xs2 in
           ([App t loc_opt (HD c1) c2],mk_Union l1 l2))`;
   `clos_call_free [closLang_Fn t loc _1 num_args x1] =
         (let (c1,l1) = clos_call_free [x1] in
         let l2 = Shift num_args l1 in
           ([closLang_Fn t loc (SOME (vars_to_list l2)) num_args
             (HD c1)],l2))`;
   `clos_call_free [(Letrec t loc _2 fns x1:closLang_exp)] =
         (let m = LENGTH fns in
         let res = MAP (\(n,x). let (c,l) = clos_call_free [x] in
                              ((n,HD c),Shift (n + m) l)) fns in
         let c1 = MAP FST res in
         let l1 = list_mk_Union (MAP SND res) in
         let (c2,l2) = clos_call_free [x1] in
           ([Letrec t loc (SOME (vars_to_list l1)) c1 (HD c2)],
            mk_Union l1 (Shift (LENGTH fns) l2)))`;
   `clos_call_free [(Handle t x1 x2:closLang_exp)] =
         (let (c1,l1) = clos_call_free [x1] in
         let (c2,l2) = clos_call_free [x2] in
           ([Handle t (HD c1) (HD c2)],mk_Union l1 (Shift 1 l2)))`;
   `clos_call_free [closLang_Call t ticks dest xs] =
         (let (c1,l1) = clos_call_free xs in
           ([closLang_Call t ticks dest c1],l1))`];;
hol4_overload "free" "clos_call_free";;

(* HOL4 ML code, not ported:
val free_ind = theorem "free_ind";
*)

let free_sing_def = cake_define_list
  [`free_sing (Var t v:closLang_exp) = (Var t v,Var v)`;
   `free_sing (If t x1 x2 x3:closLang_exp) =
         (let (c1,l1) = free_sing x1 in
         let (c2,l2) = free_sing x2 in
         let (c3,l3) = free_sing x3 in
           (If t c1 c2 c3,mk_Union l1 (mk_Union l2 l3)))`;
   `free_sing (Let t xs x2:closLang_exp) =
         (let (c1,l1) = free_list xs in
         let (c2,l2) = free_sing x2 in
           (Let t c1 c2,mk_Union l1 (Shift (LENGTH xs) l2)))`;
   `free_sing (Raise t x1:closLang_exp) =
         (let (c1,l1) = free_sing x1 in
           (Raise t c1,l1))`;
   `free_sing (closLang_Tick t x1) =
         (let (c1,l1) = free_sing x1 in
           (closLang_Tick t c1,l1))`;
   `free_sing (closLang_Op t op xs) =
         (let (c1,l1) = free_list xs in
           (closLang_Op t op c1,l1))`;
   `free_sing (App t loc_opt x1 xs2:closLang_exp) =
         (let (c1,l1) = free_sing x1 in
         let (c2,l2) = free_list xs2 in
           (App t loc_opt c1 c2,mk_Union l1 l2))`;
   `free_sing (closLang_Fn t loc _3 num_args x1) =
         (let (c1,l1) = free_sing x1 in
         let l2 = Shift num_args l1 in
           (closLang_Fn t loc (SOME (vars_to_list l2)) num_args
             c1,l2))`;
   `free_sing (Letrec t loc _4 fns x1:closLang_exp) =
         (let m = LENGTH fns in
         let res = MAP (\(n,x). let (c,l) = free_sing x in
                              ((n,c),Shift (n + m) l)) fns in
         let c1 = MAP FST res in
         let l1 = list_mk_Union (MAP SND res) in
         let (c2,l2) = free_sing x1 in
           (Letrec t loc (SOME (vars_to_list l1)) c1 c2,
            mk_Union l1 (Shift (LENGTH fns) l2)))`;
   `free_sing (Handle t x1 x2:closLang_exp) =
         (let (c1,l1) = free_sing x1 in
         let (c2,l2) = free_sing x2 in
           (Handle t c1 c2,mk_Union l1 (Shift 1 l2)))`;
   `free_sing (closLang_Call t ticks dest xs) =
         (let (c1,l1) = free_list xs in
           (closLang_Call t ticks dest c1,l1))`;
   `free_list [] = ([],db_vars_Empty)`;
   `free_list ((x:closLang_exp) :: xs) =
         (let (c1,l1) = free_sing x in
         let (c2,l2) = free_list xs in
           (c1 :: c2,mk_Union l1 l2))`];;

(* HOL4 ML code, not ported:
val free_LENGTH_LEMMA = Q.prove(
  `!xs. (case free xs of (ys,s1) => (LENGTH xs = LENGTH ys))`,
  recInduct free_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [free_def]
  \\ SRW_TAC [] [] \\ SRW_TAC [] []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REV_FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] [] \\ DECIDE_TAC)
  |> SIMP_RULE std_ss [] |> SPEC_ALL;
*)
let closed_def = cake_define
  `clos_call_closed x = (\t. t = LN) (db_to_set (SND (clos_call_free
  [x])))`;;
hol4_overload "closed" "clos_call_closed";;

let insert_each_def = cake_define_list
  [`insert_each p 0 g = g`;
   `insert_each p (SUC n) (g1,g2) = insert_each (p + 2) n
  (sptree_insert p one g1,g2)`];;

let code_list_def = cake_define_list
  [`code_list loc [] g = g`;
   `code_list loc ((n,p) :: xs) (g1,g2) =
         code_list (loc + 2) xs (g1,(loc + 1,n,p) :: g2)`];;

let GENLIST_Var_def = cake_define
  `GENLIST_Var t (i:num) n =
     (if n = 0 then [] else
       GENLIST_Var t (i + 1) (n - (1:num)) ++ [Var t (n - 1)])`;;

let calls_list_def = cake_define_list
  [`calls_list t (i:num) loc [] = []`;
   `calls_list t i loc ((n,_5) :: xs) =
         (n,closLang_Call t 0 (loc + 1) (GENLIST_Var t 1 n)) ::
              calls_list t (i + 1) (loc + 2) xs`];;

let calls_def = cake_define_list
  [`calls [] g = ([],g)`;
   `calls ((x:closLang_exp) :: y :: xs) g =
         (let (e1,g) = calls [x] g in
         let (e2,g) = calls (y :: xs) g in
           (e1 ++ e2,g))`;
   `calls [(Var t v:closLang_exp)] g =
         ([Var t v],g)`;
   `calls [(If t x1 x2 x3:closLang_exp)] g =
         (let (e1,g) = calls [x1] g in
         let (e2,g) = calls [x2] g in
         let (e3,g) = calls [x3] g in
         let e1 = HD e1 in
         let e2 = HD e2 in
         let e3 = HD e3 in
           ([If t e1 e2 e3],g))`;
   `calls [(Let t xs x2:closLang_exp)] g =
         (let (e1,g) = calls xs g in
         let (e2,g) = calls [x2] g in
         let e2 = HD e2 in
           ([Let t e1 e2],g))`;
   `calls [(Raise t x1:closLang_exp)] g =
         (let (e1,g) = calls [x1] g in
         let e1 = HD e1 in
           ([Raise t e1],g))`;
   `calls [closLang_Tick t x1] g =
         (let (e1,g) = calls [x1] g in
         let e1 = HD e1 in
           ([closLang_Tick t e1],g))`;
   `calls [(Handle t x1 x2:closLang_exp)] g =
         (let (e1,g) = calls [x1] g in
         let (e2,g) = calls [x2] g in
         let e1 = HD e1 in
         let e2 = HD e2 in
           ([Handle t e1 e2],g))`;
   `calls [closLang_Call t ticks dest xs] g =
         (let (xs,g) = calls xs g in
           ([closLang_Call t ticks dest xs],g))`;
   `calls [closLang_Op t op xs] g =
         (let (e1,g) = calls xs g in
           ([closLang_Op t op e1],g))`;
   `calls [(App t loc_opt x xs:closLang_exp)] g =
         (let (es,g) = calls xs g in
         let (e1,g) = calls [x] g in
         let e1 = HD e1 in
         let loc = (match loc_opt with SOME loc -> loc | NONE -> 0)
           in
           if IS_SOME loc_opt /\ IS_SOME (sptree_lookup loc (FST g))
             then
             if pure x then ([closLang_Call t (LENGTH es) (loc + 1)
               es],g) else
               ([Let (mk_cons t 0) (SNOC e1 es)
                  (closLang_Call (mk_cons t 1) (LENGTH es) (loc +
                    1) (GENLIST_Var backend_common_None 2 (LENGTH
                    es)))],g) else ([App t loc_opt e1 es],g))`;
   `calls [closLang_Fn t loc_opt ws num_args x1] g =
         (let loc = (match loc_opt with SOME loc -> loc | NONE -> 0)
           in
         let new_g = insert_each loc 1 g in
         let (e1,new_g) = calls [x1] new_g in
         let new_g = (FST new_g,(loc + 1,num_args,HD e1) :: SND
           new_g) in
           if clos_call_closed (closLang_Fn t loc_opt ws num_args
             (HD e1)) then
             ([closLang_Fn t loc_opt ws num_args
                 (closLang_Call backend_common_None 0 (loc + 1)
                   (GENLIST_Var backend_common_None 1 num_args))],new_g)
                   else
             let (e1,g) = calls [x1] g in
               ([closLang_Fn t loc_opt ws num_args (HD e1)],g))`;
   `calls [(Letrec t loc_opt ws fns x1:closLang_exp)] g =
         (let loc = (match loc_opt with SOME loc -> loc | NONE -> 0)
           in
         let new_g = insert_each loc (LENGTH fns) g in
         let (fns1,new_g) = calls (MAP SND fns) new_g in
           if EVERY2 (\(n,_6) p. clos_call_closed (closLang_Fn
             (implode "") NONE NONE n p)) fns fns1 then
             let new_g = code_list loc (ZIP (MAP FST fns) fns1)
               new_g in
             let (e1,g) = calls [x1] new_g in
               ([Letrec t loc_opt ws (calls_list backend_common_None
                 1 loc fns) (HD e1)],g) else
             let (fns1,g) = calls (MAP SND fns) g in
             let (e1,g) = calls [x1] g in
               ([Letrec t loc_opt ws (ZIP (MAP FST fns) fns1) (HD
                 e1)],g))`];;

let calls_sing_def = cake_define_list
  [`calls_sing (Var t v:closLang_exp) g =
         (Var t v,g)`;
   `calls_sing (If t x1 x2 x3:closLang_exp) g =
         (let (e1,g) = calls_sing x1 g in
         let (e2,g) = calls_sing x2 g in
         let (e3,g) = calls_sing x3 g in
           (If t e1 e2 e3,g))`;
   `calls_sing (Let t xs x2:closLang_exp) g =
         (let (e1,g) = calls_sing_list xs g in
         let (e2,g) = calls_sing x2 g in
           (Let t e1 e2,g))`;
   `calls_sing (Raise t x1:closLang_exp) g =
         (let (e1,g) = calls_sing x1 g in
           (Raise t e1,g))`;
   `calls_sing (closLang_Tick t x1) g =
         (let (e1,g) = calls_sing x1 g in
           (closLang_Tick t e1,g))`;
   `calls_sing (Handle t x1 x2:closLang_exp) g =
         (let (e1,g) = calls_sing x1 g in
         let (e2,g) = calls_sing x2 g in
           (Handle t e1 e2,g))`;
   `calls_sing (closLang_Call t ticks dest xs) g =
         (let (xs,g) = calls_sing_list xs g in
           (closLang_Call t ticks dest xs,g))`;
   `calls_sing (closLang_Op t op xs) g =
         (let (e1,g) = calls_sing_list xs g in
           (closLang_Op t op e1,g))`;
   `calls_sing (App t loc_opt x xs:closLang_exp) g =
         (let (es,g) = calls_sing_list xs g in
         let (e1,g) = calls_sing x g in
         let loc = (match loc_opt with SOME loc -> loc | NONE -> 0)
           in
           if IS_SOME loc_opt /\ IS_SOME (sptree_lookup loc (FST g))
             then
             if pure x then (closLang_Call t (LENGTH es) (loc + 1)
               es,g) else
               (Let (mk_cons t 0) (SNOC e1 es)
                  (closLang_Call (mk_cons t 1) (LENGTH es) (loc +
                    1) (GENLIST_Var backend_common_None 2 (LENGTH
                    es))),g) else (App t loc_opt e1 es,g))`;
   `calls_sing (closLang_Fn t loc_opt ws num_args x1) g =
         (let loc = (match loc_opt with SOME loc -> loc | NONE -> 0)
           in
         let new_g = insert_each loc 1 g in
         let (e1,new_g) = calls_sing x1 new_g in
         let new_g = (FST new_g,(loc + 1,num_args,e1) :: SND new_g)
           in
           if clos_call_closed (closLang_Fn t loc_opt ws num_args
             e1) then
             (closLang_Fn t loc_opt ws num_args
                 (closLang_Call backend_common_None 0 (loc + 1)
                   (GENLIST_Var backend_common_None 1 num_args)),new_g)
                   else
             let (e1,g) = calls_sing x1 g in
               (closLang_Fn t loc_opt ws num_args e1,g))`;
   `calls_sing (Letrec t loc_opt ws fns x1:closLang_exp) g =
         (let loc = (match loc_opt with SOME loc -> loc | NONE -> 0)
           in
         let new_g = insert_each loc (LENGTH fns) g in
         let (fns1,new_g) = calls_sing_list (MAP SND fns) new_g in
           if EVERY2 (\(n,_7) p. clos_call_closed (closLang_Fn
             (implode "") NONE NONE n p)) fns fns1 then
             let new_g = code_list loc (ZIP (MAP FST fns) fns1)
               new_g in
             let (e1,g) = calls_sing x1 new_g in
               (Letrec t loc_opt ws (calls_list backend_common_None
                 1 loc fns) e1,g) else
             let (fns1,g) = calls_sing_list (MAP SND fns) g in
             let (e1,g) = calls_sing x1 g in
               (Letrec t loc_opt ws (ZIP (MAP FST fns) fns1)
                 e1,g))`;
   `calls_sing_list [] g = ([],g)`;
   `calls_sing_list ((x:closLang_exp) :: xs) g =
         (let (e1,g) = calls_sing x g in
         let (e2,g) = calls_sing_list xs g in
           (e1 :: e2,g))`];;

let compile_def = cake_define_list
  [`clos_call_compile F x = (x,(LN,[]))`;
   `clos_call_compile T x = (let (xs,g) = calls x (LN,[]) in (xs,g))`];;
hol4_overload "compile" "clos_call_compile";;

let compile_inc_def = cake_define
  `clos_call_compile_inc d (e,xs) =
     (let (ea,d1,new_code) = calls e (d,[]) in
       (d1,ea,new_code))`;;
hol4_overload "compile_inc" "clos_call_compile_inc";;

let cond_call_compile_inc_def = cake_define
  `cond_call_compile_inc do_it = (if do_it then clos_call_compile_inc
  else CURRY I)`;;

(* HOL4 ML code, not ported:
val selftest = let
*)
  (* example code *)
(* HOL4 ML code, not ported:
  val f = ``Fn «» (SOME 800) NONE 1 (Op None (IntOp Add) [Var None 0; Op
    None (IntOp (Const 1)) []])``
  val g = ``Fn «» (SOME 900) NONE 1 (App None (SOME 800) (Var None 1)
    [Var None 0])``
  val f_g_5 = ``App None (SOME 800) (Var None 1) [App None (SOME 900)
    (Var None 0) [Op None (IntOp (Const 5)) []]]``
  val let_let = ``[Let None [^f] (Let None [^g] ^f_g_5)]``
*)
  (* compiler evaluation *)
(* HOL4 ML code, not ported:
  val tm = EVAL ``compile T ^let_let`` |> concl
  val n = tm |> find_terms (aconv ``closLang$Call``) |> length
  val _ = (n = 5) orelse failwith "clos_call implementation broken"
  in tm end
*)
