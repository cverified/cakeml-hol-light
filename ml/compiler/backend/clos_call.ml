(* ======================================================== *)
(*  clos_call: ported from HOL4's
    compiler/backend/clos_callScript.sml
    A definition theory, with 12 definitions and 16 theorems.
    Needed by backendProof.ml, clos_callProof.ml, clos_to_bvl.ml and
    clos_to_bvlProof.ml.  *)
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

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "clos_call"
  ["closLang"; "db_vars"];;

let free_def,free_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`clos_call_free [] = ([],db_vars_Empty)`;
   `clos_call_free (CONS (x:closLang_exp) (CONS y xs)) =
         (let (c1,l1) = clos_call_free [x] in
         let (c2,l2) = clos_call_free (CONS y xs) in
           (APPEND c1 c2,mk_Union l1 l2))`;
   `clos_call_free [(closLang_Var t v:closLang_exp)] =
    ([(closLang_Var t v:closLang_exp)],db_vars_Var v)`;
   `clos_call_free [(closLang_If t x1 x2 x3:closLang_exp)] =
         (let (c1,l1) = clos_call_free [x1] in
         let (c2,l2) = clos_call_free [x2] in
         let (c3,l3) = clos_call_free [x3] in
           ([closLang_If t (HD c1) (HD c2) (HD c3)],mk_Union l1
               (mk_Union l2 l3)))`;
   `clos_call_free [(closLang_Let t xs x2:closLang_exp)] =
         (let (c1,l1) = clos_call_free xs in
         let (c2,l2) = clos_call_free [x2] in
           ([closLang_Let t c1 (HD c2)],mk_Union l1
               (db_vars_Shift (LENGTH xs) l2)))`;
   `clos_call_free [(closLang_Raise t x1:closLang_exp)] =
         (let (c1,l1) = clos_call_free [x1] in
           ([closLang_Raise t (HD c1)],l1))`;
   `clos_call_free [(closLang_Tick t x1:closLang_exp)] =
         (let (c1,l1) = clos_call_free [x1] in
           ([closLang_Tick t (HD c1)],l1))`;
   `clos_call_free [(closLang_Op t op xs:closLang_exp)] =
         (let (c1,l1) = clos_call_free xs in
           ([closLang_Op t op c1],l1))`;
   `clos_call_free [(closLang_App t loc_opt x1 xs2:closLang_exp)] =
         (let (c1,l1) = clos_call_free [x1] in
         let (c2,l2) = clos_call_free xs2 in
           ([closLang_App t loc_opt (HD c1) c2],mk_Union l1 l2))`;
   `clos_call_free [closLang_Fn t loc _1 num_args x1] =
         (let (c1,l1) = clos_call_free [x1] in
         let l2 = db_vars_Shift num_args l1 in
           ([closLang_Fn t loc (SOME (vars_to_list l2)) num_args
               (HD c1)],l2))`;
   `clos_call_free [(closLang_Letrec t loc _3 fns x1:closLang_exp)] =
         (let m = LENGTH fns in
         let res = MAP (\(n,x). let (c,l) = clos_call_free [x] in
                              ((n,HD c),db_vars_Shift (n + m) l))
                                  fns in
         let c1 = MAP FST res in
         let l1 = list_mk_Union (MAP SND res) in
         let (c2,l2) = clos_call_free [x1] in
           ([closLang_Letrec t loc (SOME (vars_to_list l1)) c1 (HD
               c2)],
            mk_Union l1 (db_vars_Shift (LENGTH fns) l2)))`;
   `clos_call_free [(closLang_Handle t x1 x2:closLang_exp)] =
         (let (c1,l1) = clos_call_free [x1] in
         let (c2,l2) = clos_call_free [x2] in
           ([closLang_Handle t (HD c1) (HD c2)],mk_Union l1
               (db_vars_Shift 1 l2)))`;
   `clos_call_free [(closLang_Call t ticks dest xs:closLang_exp)] =
         (let (c1,l1) = clos_call_free xs in
           ([closLang_Call t ticks dest c1],l1))`];;

(* HOL4 clos_callScript.sml:63: ML code, not ported *)

let free_sing_def,free_sing_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`free_sing (closLang_Var t v:closLang_exp) = ((closLang_Var t
    v:closLang_exp),db_vars_Var v)`;
   `free_sing (closLang_If t x1 x2 x3:closLang_exp) =
         (let (c1,l1) = free_sing x1 in
         let (c2,l2) = free_sing x2 in
         let (c3,l3) = free_sing x3 in
           (closLang_If t c1 c2 c3,mk_Union l1 (mk_Union l2 l3)))`;
   `free_sing (closLang_Let t xs x2:closLang_exp) =
         (let (c1,l1) = free_list xs in
         let (c2,l2) = free_sing x2 in
           (closLang_Let t c1 c2,mk_Union l1 (db_vars_Shift
               (LENGTH xs) l2)))`;
   `free_sing (closLang_Raise t x1:closLang_exp) =
         (let (c1,l1) = free_sing x1 in
           (closLang_Raise t c1,l1))`;
   `free_sing (closLang_Tick t x1:closLang_exp) =
         (let (c1,l1) = free_sing x1 in
           (closLang_Tick t c1,l1))`;
   `free_sing (closLang_Op t op xs:closLang_exp) =
         (let (c1,l1) = free_list xs in
           (closLang_Op t op c1,l1))`;
   `free_sing (closLang_App t loc_opt x1 xs2:closLang_exp) =
         (let (c1,l1) = free_sing x1 in
         let (c2,l2) = free_list xs2 in
           (closLang_App t loc_opt c1 c2,mk_Union l1 l2))`;
   `free_sing (closLang_Fn t loc _4 num_args x1) =
         (let (c1,l1) = free_sing x1 in
         let l2 = db_vars_Shift num_args l1 in
           (closLang_Fn t loc (SOME (vars_to_list l2)) num_args
               c1,l2))`;
   `free_sing (closLang_Letrec t loc _6 fns x1:closLang_exp) =
         (let m = LENGTH fns in
         let res = MAP (\(n,x). let (c,l) = free_sing x in
                              ((n,c),db_vars_Shift (n + m) l)) fns
                                  in
         let c1 = MAP FST res in
         let l1 = list_mk_Union (MAP SND res) in
         let (c2,l2) = free_sing x1 in
           (closLang_Letrec t loc (SOME (vars_to_list l1)) c1 c2,
            mk_Union l1 (db_vars_Shift (LENGTH fns) l2)))`;
   `free_sing (closLang_Handle t x1 x2:closLang_exp) =
         (let (c1,l1) = free_sing x1 in
         let (c2,l2) = free_sing x2 in
           (closLang_Handle t c1 c2,mk_Union l1 (db_vars_Shift 1
               l2)))`;
   `free_sing (closLang_Call t ticks dest xs:closLang_exp) =
         (let (c1,l1) = free_list xs in
           (closLang_Call t ticks dest c1,l1))`;
   `free_list [] = ([],db_vars_Empty)`;
   `free_list (CONS (x:closLang_exp) xs) =
         (let (c1,l1) = free_sing x in
         let (c2,l2) = free_list xs in
           (CONS c1 c2,mk_Union l1 l2))`];;

let free_sing_eq = prove
 (`(!e. clos_call_free [e] = (\(e,vs). ([e],vs)) (free_sing e)) /\
   (!es. clos_call_free es = free_list es)`,
  CHEAT_TAC);;

(* HOL4 clos_callScript.sml:142-150: a theorem that HOL4 states as
   the value of an ML expression: free_LENGTH_LEMMA *)

let free_LENGTH = prove
 (`!xs ys l. (clos_call_free xs = (ys,l)) ==> (LENGTH ys = LENGTH xs)`,
  CHEAT_TAC);;

let free_SING = prove
 (`(clos_call_free [x] = (ys,l)) ==> (?y. ys = [y])`,
  (REPEAT STRIP_TAC THEN RES_ASSUME free_LENGTH THEN
   POP_ASSUM MP_TAC THEN SPEC_TAC(`ys:closLang_exp
     list`,`ys:closLang_exp list`) THEN
   LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ;
     LENGTH_EQ_NIL] THEN
   MESON_TAC[]));;

let LENGTH_FST_free = prove
 (`LENGTH (FST (clos_call_free fns)) = LENGTH fns`,
  CHEAT_TAC);;

let HD_FST_free = prove
 (`[HD (FST (clos_call_free [x1]))] = FST (clos_call_free [x1])`,
  CHEAT_TAC);;

let free_CONS = prove
 (`FST (clos_call_free (CONS x xs)) = CONS (HD (FST (clos_call_free
  [x]))) (FST (clos_call_free xs))`,
  CHEAT_TAC);;
let closed_def = new_definition
  `clos_call_closed x = (\t. t = LN) (db_to_set (SND (clos_call_free
  [x])))`;;

let closed_eq = prove
 (`clos_call_closed x = (\t. t = LN) (db_to_set (SND (free_sing x)))`,
  CHEAT_TAC);;

(* [local] *)
let EL_MEM_LEMMA = prove
 (`!xs i x. i < LENGTH xs /\ (x = EL i xs) ==> MEM x xs`,
  (MESON_TAC[MEM_EL]));;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let insert_each_def,insert_each_ind = define_wf
  `MEASURE (\(x0,x1,x2). (\n. n) x1)`
  [`insert_each p 0 g = g`;
   `insert_each p (SUC n) (g1,g2) = insert_each (p + 2) n
    (sptree_insert p one g1,g2)`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let code_list_def,code_list_ind = define_wf
  `MEASURE (\(x0,x1,x2). list_size (pair_size (\x. 0) (\x. 0)) x1)`
  [`code_list loc [] g = g`;
   `code_list loc (CONS (n,p) xs) (g1,g2) =
         code_list (loc + 2) xs (g1,CONS (loc + 1,n,p) g2)`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let GENLIST_Var_def,GENLIST_Var_ind = define_wf
  `MEASURE (\(x0,x1,x2). (\n. n) x2)`
  [`GENLIST_Var t (i:num) n =
     (if n = 0 then [] else APPEND (GENLIST_Var t (i + 1) (n -
       (1:num))) [closLang_Var t (n - 1)])`];;

let calls_list_def,calls_list_ind = define_rec
  [`calls_list t (i:num) loc [] = []`;
   `calls_list t (i:num) loc (CONS (n,_7) xs) = CONS (n,closLang_Call t
    0 (loc + 1) (GENLIST_Var t 1 n))
              (calls_list t (i + 1) (loc + 2) xs)`];;

(* HOL4 clos_callScript.sml:226-230: a theorem whose statement the
   port cannot state yet: exp3_size_MAP_SND *)

let _ = size_thms "closLang_exp";;
let calls_def,calls_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`calls [] g = ([],g)`;
   `calls (CONS (x:closLang_exp) (CONS y xs)) g =
         (let (e1,g) = calls [x] g in
         let (e2,g) = calls (CONS y xs) g in
           (APPEND e1 e2,g))`;
   `calls [(closLang_Var t v:closLang_exp)] g =
         ([(closLang_Var t v:closLang_exp)],g)`;
   `calls [(closLang_If t x1 x2 x3:closLang_exp)] g =
         (let (e1,g) = calls [x1] g in
         let (e2,g) = calls [x2] g in
         let (e3,g) = calls [x3] g in
         let e1 = HD e1 in
         let e2 = HD e2 in
         let e3 = HD e3 in
           ([closLang_If t e1 e2 e3],g))`;
   `calls [(closLang_Let t xs x2:closLang_exp)] g =
         (let (e1,g) = calls xs g in
         let (e2,g) = calls [x2] g in
         let e2 = HD e2 in
           ([closLang_Let t e1 e2],g))`;
   `calls [(closLang_Raise t x1:closLang_exp)] g =
         (let (e1,g) = calls [x1] g in
         let e1 = HD e1 in
           ([closLang_Raise t e1],g))`;
   `calls [(closLang_Tick t x1:closLang_exp)] g =
         (let (e1,g) = calls [x1] g in
         let e1 = HD e1 in
           ([closLang_Tick t e1],g))`;
   `calls [(closLang_Handle t x1 x2:closLang_exp)] g =
         (let (e1,g) = calls [x1] g in
         let (e2,g) = calls [x2] g in
         let e1 = HD e1 in
         let e2 = HD e2 in
           ([closLang_Handle t e1 e2],g))`;
   `calls [(closLang_Call t ticks dest xs:closLang_exp)] g =
         (let (xs,g) = calls xs g in
           ([(closLang_Call t ticks dest xs:closLang_exp)],g))`;
   `calls [(closLang_Op t op xs:closLang_exp)] g =
         (let (e1,g) = calls xs g in
           ([closLang_Op t op e1],g))`;
   `calls [(closLang_App t loc_opt x xs:closLang_exp)] g =
         (let (es,g) = calls xs g in
         let (e1,g) = calls [x] g in
         let e1 = HD e1 in
         let loc = (match loc_opt with SOME loc -> loc | NONE -> 0)
             in
           if IS_SOME loc_opt /\ IS_SOME (sptree_lookup loc (FST g))
               then
             if pure x then ([closLang_Call t (LENGTH es) (loc + 1)
                 es],g) else
               ([closLang_Let (mk_cons t 0) (SNOC e1 es)
                  (closLang_Call (mk_cons t 1) (LENGTH es) (loc +
                      1) (GENLIST_Var backend_common_None 2 (LENGTH
                      es)))],g) else ([closLang_App t loc_opt e1
                      es],g))`;
   `calls [closLang_Fn t loc_opt ws num_args x1] g =
         // loc_opt ought to be SOME loc, with loc being EVEN
         (let loc = (match loc_opt with SOME loc -> loc | NONE -> 0)
             in
         let new_g = insert_each loc 1 g in
         let (e1,new_g) = calls [x1] new_g in
         let new_g = (FST new_g,CONS (loc + 1,num_args,HD e1) (SND
             new_g)) in
           // Closedness is checked on the transformed program because
           // the calls function can sometimes remove free variables.
           if clos_call_closed (closLang_Fn t loc_opt ws num_args
               (HD e1)) then
             ([closLang_Fn t loc_opt ws num_args
                 (closLang_Call backend_common_None 0 (loc + 1)
                     (GENLIST_Var backend_common_None 1
                     num_args))],new_g) else
             let (e1,g) = calls [x1] g in
               ([closLang_Fn t loc_opt ws num_args (HD e1)],g))`;
   `calls [(closLang_Letrec t loc_opt ws fns x1:closLang_exp)] g =
         (let loc = (match loc_opt with SOME loc -> loc | NONE -> 0)
             in
         let new_g = insert_each loc (LENGTH fns) g in
         let (fns1,new_g) = calls (MAP SND fns) new_g in
           if ALL2 (\(n,_16) p. clos_call_closed (closLang_Fn
               (implode "") NONE NONE n p)) fns fns1 then
             let new_g = code_list loc (ZIP (MAP FST fns) fns1)
                 new_g in
             let (e1,g) = calls [x1] new_g in
               ([closLang_Letrec t loc_opt ws (calls_list
                   backend_common_None 1 loc fns) (HD e1)],g) else
             let (fns1,g) = calls (MAP SND fns) g in
             let (e1,g) = calls [x1] g in
               ([closLang_Letrec t loc_opt ws (ZIP (MAP FST
                   fns) fns1) (HD e1)],g))`];;

let calls_sing_def,calls_sing_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`calls_sing (closLang_Var t v:closLang_exp) g =
         ((closLang_Var t v:closLang_exp),g)`;
   `calls_sing (closLang_If t x1 x2 x3:closLang_exp) g =
         (let (e1,g) = calls_sing x1 g in
         let (e2,g) = calls_sing x2 g in
         let (e3,g) = calls_sing x3 g in
           (closLang_If t e1 e2 e3,g))`;
   `calls_sing (closLang_Let t xs x2:closLang_exp) g =
         (let (e1,g) = calls_sing_list xs g in
         let (e2,g) = calls_sing x2 g in
           (closLang_Let t e1 e2,g))`;
   `calls_sing (closLang_Raise t x1:closLang_exp) g =
         (let (e1,g) = calls_sing x1 g in
           (closLang_Raise t e1,g))`;
   `calls_sing (closLang_Tick t x1:closLang_exp) g =
         (let (e1,g) = calls_sing x1 g in
           (closLang_Tick t e1,g))`;
   `calls_sing (closLang_Handle t x1 x2:closLang_exp) g =
         (let (e1,g) = calls_sing x1 g in
         let (e2,g) = calls_sing x2 g in
           (closLang_Handle t e1 e2,g))`;
   `calls_sing (closLang_Call t ticks dest xs:closLang_exp) g =
         (let (xs,g) = calls_sing_list xs g in
           ((closLang_Call t ticks dest xs:closLang_exp),g))`;
   `calls_sing (closLang_Op t op xs:closLang_exp) g =
         (let (e1,g) = calls_sing_list xs g in
           (closLang_Op t op e1,g))`;
   `calls_sing (closLang_App t loc_opt x xs:closLang_exp) g =
         (let (es,g) = calls_sing_list xs g in
         let (e1,g) = calls_sing x g in
         let loc = (match loc_opt with SOME loc -> loc | NONE -> 0)
             in
           if IS_SOME loc_opt /\ IS_SOME (sptree_lookup loc (FST g))
               then
             if pure x then (closLang_Call t (LENGTH es) (loc + 1)
                 es,g) else
               (closLang_Let (mk_cons t 0) (SNOC e1 es)
                  (closLang_Call (mk_cons t 1) (LENGTH es) (loc +
                      1) (GENLIST_Var backend_common_None 2 (LENGTH
                      es))),g) else (closLang_App t loc_opt e1 es,g))`;
   `calls_sing (closLang_Fn t loc_opt ws num_args x1) g =
         // loc_opt ought to be SOME loc, with loc being EVEN
         (let loc = (match loc_opt with SOME loc -> loc | NONE -> 0)
             in
         let new_g = insert_each loc 1 g in
         let (e1,new_g) = calls_sing x1 new_g in
         let new_g = (FST new_g,CONS (loc + 1,num_args,e1) (SND
             new_g)) in
           // Closedness is checked on the transformed program because
           // the calls function can sometimes remove free variables.
           if clos_call_closed (closLang_Fn t loc_opt ws num_args
               e1) then
             (closLang_Fn t loc_opt ws num_args
                 (closLang_Call backend_common_None 0 (loc + 1)
                     (GENLIST_Var backend_common_None 1
                     num_args)),new_g) else
             let (e1,g) = calls_sing x1 g in
               (closLang_Fn t loc_opt ws num_args e1,g))`;
   `calls_sing (closLang_Letrec t loc_opt ws fns x1:closLang_exp) g =
         (let loc = (match loc_opt with SOME loc -> loc | NONE -> 0)
             in
         let new_g = insert_each loc (LENGTH fns) g in
         let (fns1,new_g) = calls_sing_list (MAP SND fns) new_g in
           if ALL2 (\(n,_25) p. clos_call_closed (closLang_Fn
               (implode "") NONE NONE n p)) fns fns1 then
             let new_g = code_list loc (ZIP (MAP FST fns) fns1)
                 new_g in
             let (e1,g) = calls_sing x1 new_g in
               (closLang_Letrec t loc_opt ws (calls_list
                   backend_common_None 1 loc fns) e1,g) else
             let (fns1,g) = calls_sing_list (MAP SND fns) g in
             let (e1,g) = calls_sing x1 g in
               (closLang_Letrec t loc_opt ws (ZIP (MAP FST fns)
                   fns1) e1,g))`;
   `calls_sing_list [] g = ([],g)`;
   `calls_sing_list (CONS (x:closLang_exp) xs) g =
         (let (e1,g) = calls_sing x g in
         let (e2,g) = calls_sing_list xs g in
           (CONS e1 e2,g))`];;

let calls_sing_eq = prove
 (`(!e g. calls [e] g = (\(e,rest). ([e],rest)) (calls_sing e g)) /\
   (!es g. calls es g = calls_sing_list es g)`,
  CHEAT_TAC);;

let clos_call_compile_def = define_general
  [`clos_call_compile F x = (x,(LN,[]))`;
   `clos_call_compile T x = (let (xs,g) = calls x (LN,[]) in
    (xs,g))`];;

let clos_call_compile_inc_def = new_definition
  `clos_call_compile_inc d (e,xs) =
     (let (ea,d1,new_code) = calls e (d,[]) in
       (d1,ea,new_code))`;;

(* compile_eq *)
let clos_call_compile_eq = prove
 (`clos_call_compile F x = (x,(LN,[])) /\
   clos_call_compile T x = (let (xs,g) = calls_sing_list x (LN,[])
     in (xs,g))`,
  CHEAT_TAC);;

(* compile_inc_eq *)
let clos_call_compile_inc_eq = prove
 (`clos_call_compile_inc d (e,xs) =
     (let (ea,d1,new_code) = calls_sing_list e (d,[]) in
       (d1,ea,new_code))`,
  CHEAT_TAC);;

let cond_call_compile_inc_def = new_definition
  `cond_call_compile_inc do_it = (if do_it then clos_call_compile_inc
  else CURRY I)`;;

let calls_length = prove
 (`!xs g0 ys g. calls xs g0 = (ys,g) ==> LENGTH ys = LENGTH xs`,
  CHEAT_TAC);;

let calls_sing = prove
 (`!x g0 ys g. calls [x] g0 = (ys,g) ==> (?y. ys = [y])`,
  (REPEAT STRIP_TAC THEN RES_ASSUME calls_length THEN
   POP_ASSUM MP_TAC THEN SPEC_TAC(`ys:closLang_exp
     list`,`ys:closLang_exp list`) THEN
   LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ;
     LENGTH_EQ_NIL] THEN
   MESON_TAC[]));;

(* compile_LENGTH *)
let clos_call_compile_LENGTH = prove
 (`clos_call_compile x y = (a,b) ==> LENGTH y = LENGTH a`,
  CHEAT_TAC);;

let compile_nil = prove
 (`clos_call_compile x [] = (a,g,b) ==> a = [] /\ g = LN /\ b = []`,
  CHEAT_TAC);;

(* HOL4 clos_callScript.sml:464: ML code, not ported *)
  (* example code *)
(* HOL4 clos_callScript.sml:466-469: the ML values that the
   definitions below antiquote *)
  (* compiler evaluation *)
(* HOL4 clos_callScript.sml:471-474: the ML values that the
   definitions below antiquote *)
