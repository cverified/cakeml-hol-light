(* ======================================================== *)
(*  clos_annotate: ported from HOL4's
    compiler/backend/clos_annotateScript.sml  *)
(* ======================================================== *)

(*
  A compiler phase that annotates code that creates closures with
  (minimal) live variable annotations. Such live variable annotations
  are required for closure conversion, which is implemented in
  the clos_to_bvl phase of the compiler.
*)

needs "compiler/backend/closLang.ml";;
needs "compiler/backend/db_vars.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(* alt_free calculates free variable annotations, and replaces unused
   lets with dummies *)

let const_0_def = cake_define
  `const_0 t = closLang_Op t (closLang_IntOp (closLang_Const (&0)))
  []`;;

let no_overlap_def = cake_define_list
  [`no_overlap 0 l <=> T`;
   `no_overlap (SUC n) l <=>
         (if has_var n l then F else no_overlap n l)`];;

let alt_free_def = cake_define_list
  [`alt_free [] = ([],db_vars_Empty)`;
   `alt_free ((x:closLang_exp) :: y :: xs) =
         (let (c1,l1) = alt_free [x] in
         let (c2,l2) = alt_free (y :: xs) in
           (c1 ++ c2,mk_Union l1 l2))`;
   `alt_free [(Var t v:closLang_exp)] = ([(Var t v:closLang_exp)],Var
  v)`;
   `alt_free [(If t x1 x2 x3:closLang_exp)] =
         (let (c1,l1) = alt_free [x1] in
         let (c2,l2) = alt_free [x2] in
         let (c3,l3) = alt_free [x3] in
           ([If t (HD c1) (HD c2) (HD c3)],mk_Union l1 (mk_Union
             l2 l3)))`;
   `alt_free [(Let t xs x2:closLang_exp)] =
         (let m = LENGTH xs in
         let (c2,l2) = alt_free [x2] in
           if no_overlap m l2 /\ EVERY pure xs then
             ([Let t (REPLICATE m (const_0 t)) (HD c2)],Shift m l2)
               else
             let (c1,l1) = alt_free xs in
               ([Let t c1 (HD c2)],mk_Union l1 (Shift (LENGTH xs)
                 l2)))`;
   `alt_free [(Raise t x1:closLang_exp)] =
         (let (c1,l1) = alt_free [x1] in
           ([Raise t (HD c1)],l1))`;
   `alt_free [(closLang_Tick t x1:closLang_exp)] =
         (let (c1,l1) = alt_free [x1] in
           ([closLang_Tick t (HD c1)],l1))`;
   `alt_free [(closLang_Op t op xs:closLang_exp)] =
         (let (c1,l1) = alt_free xs in
           ([closLang_Op t op c1],l1))`;
   `alt_free [(App t loc_opt x1 xs2:closLang_exp)] =
         (let (c1,l1) = alt_free [x1] in
         let (c2,l2) = alt_free xs2 in
           ([App t loc_opt (HD c1) c2],mk_Union l1 l2))`;
   `alt_free [closLang_Fn t loc _1 num_args x1] =
         (let (c1,l1) = alt_free [x1] in
         let l2 = Shift num_args l1 in
           ([closLang_Fn t loc (SOME (vars_to_list l2)) num_args
             (HD c1)],l2))`;
   `alt_free [(Letrec t loc _3 fns x1:closLang_exp)] =
         (let m = LENGTH fns in
         let (c2,l2) = alt_free [x1] in
         let res = MAP (\(n,x). let (c,l) = alt_free [x] in
                              ((n,HD c),Shift (n + m) l)) fns in
         let c1 = MAP FST res in
         let l1 = list_mk_Union (MAP SND res) in
           ([Letrec t loc (SOME (vars_to_list l1)) c1 (HD c2)],
            mk_Union l1 (Shift (LENGTH fns) l2)))`;
   `alt_free [(Handle t x1 x2:closLang_exp)] =
         (let (c1,l1) = alt_free [x1] in
         let (c2,l2) = alt_free [x2] in
           ([Handle t (HD c1) (HD c2)],mk_Union l1 (Shift 1 l2)))`;
   `alt_free [(closLang_Call t ticks dest xs:closLang_exp)] =
         (let (c1,l1) = alt_free xs in
           ([closLang_Call t ticks dest c1],l1))`];;

let alt_free_sing_def = cake_define_list
  [`alt_free_sing (Var t v:closLang_exp) = ((Var t
  v:closLang_exp),Var v)`;
   `alt_free_sing (If t x1 x2 x3:closLang_exp) =
         (let (c1,l1) = alt_free_sing x1 in
         let (c2,l2) = alt_free_sing x2 in
         let (c3,l3) = alt_free_sing x3 in
           (If t c1 c2 c3,mk_Union l1 (mk_Union l2 l3)))`;
   `alt_free_sing (Let t xs x2:closLang_exp) =
         (let m = LENGTH xs in
         let (c2,l2) = alt_free_sing x2 in
           if no_overlap m l2 /\ EVERY pure xs then
             (Let t (REPLICATE m (const_0 t)) c2,Shift m l2) else
             let (c1,l1) = alt_free_list xs in
               (Let t c1 c2,mk_Union l1 (Shift (LENGTH xs) l2)))`;
   `alt_free_sing (Raise t x1:closLang_exp) =
         (let (c1,l1) = alt_free_sing x1 in
           (Raise t c1,l1))`;
   `alt_free_sing (closLang_Tick t x1:closLang_exp) =
         (let (c1,l1) = alt_free_sing x1 in
           (closLang_Tick t c1,l1))`;
   `alt_free_sing (closLang_Op t op xs:closLang_exp) =
         (let (c1,l1) = alt_free_list xs in
           (closLang_Op t op c1,l1))`;
   `alt_free_sing (App t loc_opt x1 xs2:closLang_exp) =
         (let (c1,l1) = alt_free_sing x1 in
         let (c2,l2) = alt_free_list xs2 in
           (App t loc_opt c1 c2,mk_Union l1 l2))`;
   `alt_free_sing (closLang_Fn t loc _4 num_args x1) =
         (let (c1,l1) = alt_free_sing x1 in
         let l2 = Shift num_args l1 in
           (closLang_Fn t loc (SOME (vars_to_list l2)) num_args
             c1,l2))`;
   `alt_free_sing (Letrec t loc _6 fns x1:closLang_exp) =
         (let m = LENGTH fns in
         let (c2,l2) = alt_free_sing x1 in
         let res = alt_free_letrec m fns in
         let c1 = MAP FST res in
         let l1 = list_mk_Union (MAP SND res) in
           (Letrec t loc (SOME (vars_to_list l1)) c1 c2,
            mk_Union l1 (Shift (LENGTH fns) l2)))`;
   `alt_free_sing (Handle t x1 x2:closLang_exp) =
         (let (c1,l1) = alt_free_sing x1 in
         let (c2,l2) = alt_free_sing x2 in
           (Handle t c1 c2,mk_Union l1 (Shift 1 l2)))`;
   `alt_free_sing (closLang_Call t ticks dest xs:closLang_exp) =
         (let (c1,l1) = alt_free_list xs in
           (closLang_Call t ticks dest c1,l1))`;
   `alt_free_list [] = ([],db_vars_Empty)`;
   `alt_free_list ((x:closLang_exp) :: xs) =
         (let (c1,l1) = alt_free_sing x in
         let (c2,l2) = alt_free_list xs in
           (c1 :: c2,mk_Union l1 l2))`;
   `alt_free_letrec m [] = []`;
   `alt_free_letrec m ((n,x) :: rest) =
         (let (c,l) = alt_free_sing x in
           ((n,c),Shift (n + m) l) :: alt_free_letrec m rest)`];;

(* shift renames variables to use only those in the annotations *)

let get_var_def = cake_define
  `clos_annotate_get_var m l i v =
     (if v < l then v else l + zlookup i (v - l))`;;
hol4_overload "get_var" "clos_annotate_get_var";;

let shifted_env_def = cake_define_list
  [`shifted_env n [] = LN`;
   `shifted_env n (x :: xs) = sptree_insert x (n:num) (shifted_env
  (n + 1) xs)`];;

let shift_def = cake_define_list
  [`clos_annotate_shift [] (m:num) (l:num) (i:num spt) = []`;
   `clos_annotate_shift ((x:closLang_exp) :: y :: xs) m l i =
         (let c1 = clos_annotate_shift [x] m l i in
         let c2 = clos_annotate_shift (y :: xs) m l i in
           (c1 ++ (c2:closLang_exp list)))`;
   `clos_annotate_shift [(Var t v:closLang_exp)] m l i =
         [Var t (clos_annotate_get_var m l i v)]`;
   `clos_annotate_shift [(If t x1 x2 x3:closLang_exp)] m l i =
         (let c1 = clos_annotate_shift [x1] m l i in
         let c2 = clos_annotate_shift [x2] m l i in
         let c3 = clos_annotate_shift [x3] m l i in
           ([If t (HD c1) (HD c2) (HD c3)]))`;
   `clos_annotate_shift [(Let t xs x2:closLang_exp)] m l i =
         (let c1 = clos_annotate_shift xs m l i in
         let c2 = clos_annotate_shift [x2] m (l + LENGTH xs) i in
           ([Let t c1 (HD c2)]))`;
   `clos_annotate_shift [(Raise t x1:closLang_exp)] m l i =
         (let (c1) = clos_annotate_shift [x1] m l i in
           ([Raise t (HD c1)]))`;
   `clos_annotate_shift [(closLang_Tick t x1:closLang_exp)] m l i =
         (let c1 = clos_annotate_shift [x1] m l i in
           ([closLang_Tick t (HD c1)]))`;
   `clos_annotate_shift [(closLang_Op t op xs:closLang_exp)] m l i =
         (let c1 = clos_annotate_shift xs m l i in
           ([closLang_Op t op c1]))`;
   `clos_annotate_shift [(App t loc_opt x1 xs2:closLang_exp)] m l i =
         (let c1 = clos_annotate_shift [x1] m l i in
         let c2 = clos_annotate_shift xs2 m l i in
           ([App t loc_opt (HD c1) c2]))`;
   `clos_annotate_shift [closLang_Fn t loc vs_opt num_args x1] m l i =
         (let k = m + l in
         let vs = (match vs_opt with NONE -> [] | SOME vs -> vs) in
         let live = FILTER (\n. n < k) vs in
         let vars' = MAP (clos_annotate_get_var m l i) live in
         let c1 = clos_annotate_shift [x1] k num_args (shifted_env 0
           live) in
           ([closLang_Fn t loc (SOME vars') num_args (HD c1)]))`;
   `clos_annotate_shift [(Letrec t loc vsopt fns x1:closLang_exp)] m l i
  =
         (let vs = (match vsopt with NONE -> [] | SOME x -> x) in
         let k = m + l in
         let live = FILTER (\n. n < k) vs in
         let vars' = MAP (clos_annotate_get_var m l i) live in
         let new_i = shifted_env 0 live in
         let fns_len = LENGTH fns in
         let cs = MAP (\(n,x). let c = clos_annotate_shift [x] k (n
           + fns_len) new_i in
                              (n,HD c)) fns in
         let c1 = clos_annotate_shift [x1] m (l + LENGTH fns) i in
           ([Letrec t loc (SOME vars') cs (HD c1)]))`;
   `clos_annotate_shift [(Handle t x1 x2:closLang_exp)] m l i =
         (let c1 = clos_annotate_shift [x1] m l i in
         let c2 = clos_annotate_shift [x2] m (l + 1) i in
           ([Handle t (HD c1) (HD c2)]))`;
   `clos_annotate_shift [(closLang_Call t ticks dest xs:closLang_exp)] m
  l i =
         (let c1 = clos_annotate_shift xs m l i in
           ([closLang_Call t ticks dest c1]))`];;
hol4_overload "shift" "clos_annotate_shift";;

let shift_sing_def = cake_define_list
  [`shift_sing (Var t v:closLang_exp) m l i =
         Var t (clos_annotate_get_var m l i v)`;
   `shift_sing (If t x1 x2 x3:closLang_exp) m l i =
         (let c1 = shift_sing x1 m l i in
         let c2 = shift_sing x2 m l i in
         let c3 = shift_sing x3 m l i in
           (If t c1 c2 c3))`;
   `shift_sing (Let t xs x2:closLang_exp) m l i =
         (let c1 = shift_list xs m l i in
         let c2 = shift_sing x2 m (l + LENGTH xs) i in
           (Let t c1 c2))`;
   `shift_sing (Raise t x1:closLang_exp) m l i =
         (let (c1) = shift_sing x1 m l i in
           (Raise t c1))`;
   `shift_sing (closLang_Tick t x1:closLang_exp) m l i =
         (let c1 = shift_sing x1 m l i in
           (closLang_Tick t c1))`;
   `shift_sing (closLang_Op t op xs:closLang_exp) m l i =
         (let c1 = shift_list xs m l i in
           (closLang_Op t op c1))`;
   `shift_sing (App t loc_opt x1 xs2:closLang_exp) m l i =
         (let c1 = shift_sing x1 m l i in
         let c2 = shift_list xs2 m l i in
           (App t loc_opt c1 c2))`;
   `shift_sing (closLang_Fn t loc vs_opt num_args x1) m l i =
         (let k = m + l in
         let vs = (match vs_opt with NONE -> [] | SOME vs -> vs) in
         let live = FILTER (\n. n < k) vs in
         let vars' = MAP (clos_annotate_get_var m l i) live in
         let c1 = shift_sing x1 k num_args (shifted_env 0 live) in
           (closLang_Fn t loc (SOME vars') num_args c1))`;
   `shift_sing (Letrec t loc vsopt fns x1:closLang_exp) m l i =
         (let vs = (match vsopt with NONE -> [] | SOME x -> x) in
         let k = m + l in
         let live = FILTER (\n. n < k) vs in
         let vars' = MAP (clos_annotate_get_var m l i) live in
         let new_i = shifted_env 0 live in
         let fns_len = LENGTH fns in
         let cs = shift_letrec fns_len k new_i fns in
         let c1 = shift_sing x1 m (l + LENGTH fns) i in
           (Letrec t loc (SOME vars') cs c1))`;
   `shift_sing (Handle t x1 x2:closLang_exp) m l i =
         (let c1 = shift_sing x1 m l i in
         let c2 = shift_sing x2 m (l + 1) i in
           (Handle t c1 c2))`;
   `shift_sing (closLang_Call t ticks dest xs:closLang_exp) m l i =
         (let c1 = shift_list xs m l i in
           (closLang_Call t ticks dest c1))`;
   `shift_list [] (m:num) (l:num) (i:num spt) = []`;
   `shift_list ((x:closLang_exp) :: xs) m l i =
         (let c1 = shift_sing x m l i in
         let c2 = shift_list xs m l i in
           (c1 :: (c2:closLang_exp list)))`;
   `shift_letrec fns_len k new_i [] = []`;
   `shift_letrec fns_len k new_i ((n,x) :: rest) =
         (let c = shift_sing x k (n + fns_len) new_i in
           (n,c) :: shift_letrec fns_len k new_i rest)`];;

(* main functions *)

let annotate_def = cake_define
  `clos_annotate_annotate arity xs = clos_annotate_shift (FST
  (alt_free xs)) 0 arity LN`;;
hol4_overload "annotate" "clos_annotate_annotate";;

let compile_def = cake_define
  `clos_annotate_compile prog =
     MAP (\(n,args,exp). (n,args,HD (clos_annotate_annotate args
       [exp]))) prog`;;
hol4_overload "compile" "clos_annotate_compile";;

let compile_inc_def = cake_define
  `clos_annotate_compile_inc (e,aux) = (clos_annotate_annotate 0
  e,clos_annotate_compile aux)`;;
hol4_overload "compile_inc" "clos_annotate_compile_inc";;

(* cv versions *)

let annotate_sing_def = cake_define
  `annotate_sing arity x = shift_sing (FST (alt_free_sing x)) 0 arity
  LN`;;

let annotate_list_def = cake_define
  `annotate_list arity xs = shift_list (FST (alt_free_list xs)) 0
  arity LN`;;
