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
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/db_vars.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;

(* alt_free calculates free variable annotations, and replaces unused
   lets with dummies *)

let const_0_def = cake_define
  `const_0 t = closLang_Op t (closLang_IntOp (closLang_Const 0)) []`;;

let no_overlap_def = cake_define
  `(no_overlap 0 l <=> T) /\
   (no_overlap (SUC n) l <=>
      (if has_var n l then F else no_overlap n l))`;;

let alt_free_def = cake_define
  `(alt_free [] = ([],db_vars_Empty)) /\
   (alt_free ((x:closLang_exp) :: y :: xs) =
      (let (c1,l1) = alt_free [x] in
      let (c2,l2) = alt_free (y :: xs) in
        (c1 ++ c2,mk_Union l1 l2))) /\
   (alt_free [db_vars_Var t v] = ([db_vars_Var t v],db_vars_Var v))
     /\
   (alt_free [closLang_If t x1 x2 x3] =
      (let (c1,l1) = alt_free [x1] in
      let (c2,l2) = alt_free [x2] in
      let (c3,l3) = alt_free [x3] in
        ([closLang_If t (HD c1) (HD c2) (HD c3)],mk_Union l1
          (mk_Union l2 l3)))) /\
   (alt_free [closLang_Let t xs x2] =
      (let m = LENGTH xs in
      let (c2,l2) = alt_free [x2] in
        if no_overlap m l2 /\ EVERY pure xs then
          ([closLang_Let t (REPLICATE m (const_0 t)) (HD
            c2)],db_vars_Shift m l2) else
          let (c1,l1) = alt_free xs in
            ([closLang_Let t c1 (HD c2)],mk_Union l1 (db_vars_Shift
              (LENGTH xs) l2)))) /\
   (alt_free [closLang_Raise t x1] =
      (let (c1,l1) = alt_free [x1] in
        ([closLang_Raise t (HD c1)],l1))) /\
   (alt_free [closLang_Tick t x1] =
      (let (c1,l1) = alt_free [x1] in
        ([closLang_Tick t (HD c1)],l1))) /\
   (alt_free [closLang_Op t closLang_op xs] =
      (let (c1,l1) = alt_free xs in
        ([closLang_Op t closLang_op c1],l1))) /\
   (alt_free [closLang_App t loc_opt x1 xs2] =
      (let (c1,l1) = alt_free [x1] in
      let (c2,l2) = alt_free xs2 in
        ([closLang_App t loc_opt (HD c1) c2],mk_Union l1 l2))) /\
   (alt_free [closLang_Fn t loc _1 num_args x1] =
      (let (c1,l1) = alt_free [x1] in
      let l2 = db_vars_Shift num_args l1 in
        ([closLang_Fn t loc (SOME (vars_to_list l2)) num_args (HD
          c1)],l2))) /\
   (alt_free [closLang_Letrec t loc _2 fns x1] =
      (let m = LENGTH fns in
      let (c2,l2) = alt_free [x1] in
      let res = MAP (\(n,x). let (c,l) = alt_free [x] in
                              ((n,HD c),db_vars_Shift (n + m) l)) fns
                                in
      let c1 = MAP FST res in
      let l1 = list_mk_Union (MAP SND res) in
        ([closLang_Letrec t loc (SOME (vars_to_list l1)) c1 (HD c2)],
         mk_Union l1 (db_vars_Shift (LENGTH fns) l2)))) /\
   (alt_free [closLang_Handle t x1 x2] =
      (let (c1,l1) = alt_free [x1] in
      let (c2,l2) = alt_free [x2] in
        ([closLang_Handle t (HD c1) (HD c2)],mk_Union l1
          (db_vars_Shift 1 l2)))) /\
   (alt_free [closLang_Call t ticks dest xs] =
      (let (c1,l1) = alt_free xs in
        ([closLang_Call t ticks dest c1],l1)))`;;

(* HOL4 termination: *)
let alt_free_sing_def = cake_define_wf
  `MEASURE (\x. match x with INL e -> exp_size e | INR (INL es) ->
  list_size exp_size es | INR (INR (_5,fns)) -> list_size (pair_size
  (\x. x) exp_size) fns)`
  `(alt_free_sing (db_vars_Var t v) = (db_vars_Var t v,db_vars_Var v))
  /\
   (alt_free_sing (closLang_If t x1 x2 x3) =
      (let (c1,l1) = alt_free_sing x1 in
      let (c2,l2) = alt_free_sing x2 in
      let (c3,l3) = alt_free_sing x3 in
        (closLang_If t c1 c2 c3,mk_Union l1 (mk_Union l2 l3)))) /\
   (alt_free_sing (closLang_Let t xs x2) =
      (let m = LENGTH xs in
      let (c2,l2) = alt_free_sing x2 in
        if no_overlap m l2 /\ EVERY pure xs then
          (closLang_Let t (REPLICATE m (const_0 t)) c2,db_vars_Shift
            m l2) else
          let (c1,l1) = alt_free_list xs in
            (closLang_Let t c1 c2,mk_Union l1 (db_vars_Shift (LENGTH
              xs) l2)))) /\
   (alt_free_sing (closLang_Raise t x1) =
      (let (c1,l1) = alt_free_sing x1 in
        (closLang_Raise t c1,l1))) /\
   (alt_free_sing (closLang_Tick t x1) =
      (let (c1,l1) = alt_free_sing x1 in
        (closLang_Tick t c1,l1))) /\
   (alt_free_sing (closLang_Op t closLang_op xs) =
      (let (c1,l1) = alt_free_list xs in
        (closLang_Op t closLang_op c1,l1))) /\
   (alt_free_sing (closLang_App t loc_opt x1 xs2) =
      (let (c1,l1) = alt_free_sing x1 in
      let (c2,l2) = alt_free_list xs2 in
        (closLang_App t loc_opt c1 c2,mk_Union l1 l2))) /\
   (alt_free_sing (closLang_Fn t loc _3 num_args x1) =
      (let (c1,l1) = alt_free_sing x1 in
      let l2 = db_vars_Shift num_args l1 in
        (closLang_Fn t loc (SOME (vars_to_list l2)) num_args c1,l2)))
          /\
   (alt_free_sing (closLang_Letrec t loc _4 fns x1) =
      (let m = LENGTH fns in
      let (c2,l2) = alt_free_sing x1 in
      let res = alt_free_letrec m fns in
      let c1 = MAP FST res in
      let l1 = list_mk_Union (MAP SND res) in
        (closLang_Letrec t loc (SOME (vars_to_list l1)) c1 c2,
         mk_Union l1 (db_vars_Shift (LENGTH fns) l2)))) /\
   (alt_free_sing (closLang_Handle t x1 x2) =
      (let (c1,l1) = alt_free_sing x1 in
      let (c2,l2) = alt_free_sing x2 in
        (closLang_Handle t c1 c2,mk_Union l1 (db_vars_Shift 1 l2))))
          /\
   (alt_free_sing (closLang_Call t ticks dest xs) =
      (let (c1,l1) = alt_free_list xs in
        (closLang_Call t ticks dest c1,l1))) /\
   (alt_free_list [] = ([],db_vars_Empty)) /\
   (alt_free_list ((x:closLang_exp) :: xs) =
      (let (c1,l1) = alt_free_sing x in
      let (c2,l2) = alt_free_list xs in
        (c1 :: c2,mk_Union l1 l2))) /\
   (alt_free_letrec m [] = []) /\
   (alt_free_letrec m ((n,x) :: rest) =
      (let (c,l) = alt_free_sing x in
        ((n,c),db_vars_Shift (n + m) l) :: alt_free_letrec m
          rest))`;;

(* shift renames variables to use only those in the annotations *)

let get_var_def = cake_define
  `clos_annotate_get_var m l i v =
     (if v < l then v else l + zlookup i (v - l))`;;

let shifted_env_def = cake_define
  `(shifted_env n [] = LN) /\
   (shifted_env n (x :: xs) = sptree_insert x (n:num) (shifted_env
     (n + 1) xs))`;;

let shift_def = cake_define
  `(clos_annotate_shift [] (m:num) (l:num) (i:num spt) = []) /\
   (clos_annotate_shift ((x:closLang_exp) :: y :: xs) m l i =
      (let c1 = clos_annotate_shift [x] m l i in
      let c2 = clos_annotate_shift (y :: xs) m l i in
        (c1 ++ (c2:closLang_exp list)))) /\
   (clos_annotate_shift [db_vars_Var t v] m l i =
      [db_vars_Var t (clos_annotate_get_var m l i v)]) /\
   (clos_annotate_shift [closLang_If t x1 x2 x3] m l i =
      (let c1 = clos_annotate_shift [x1] m l i in
      let c2 = clos_annotate_shift [x2] m l i in
      let c3 = clos_annotate_shift [x3] m l i in
        ([closLang_If t (HD c1) (HD c2) (HD c3)]))) /\
   (clos_annotate_shift [closLang_Let t xs x2] m l i =
      (let c1 = clos_annotate_shift xs m l i in
      let c2 = clos_annotate_shift [x2] m (l + LENGTH xs) i in
        ([closLang_Let t c1 (HD c2)]))) /\
   (clos_annotate_shift [closLang_Raise t x1] m l i =
      (let (c1) = clos_annotate_shift [x1] m l i in
        ([closLang_Raise t (HD c1)]))) /\
   (clos_annotate_shift [closLang_Tick t x1] m l i =
      (let c1 = clos_annotate_shift [x1] m l i in
        ([closLang_Tick t (HD c1)]))) /\
   (clos_annotate_shift [closLang_Op t closLang_op xs] m l i =
      (let c1 = clos_annotate_shift xs m l i in
        ([closLang_Op t closLang_op c1]))) /\
   (clos_annotate_shift [closLang_App t loc_opt x1 xs2] m l i =
      (let c1 = clos_annotate_shift [x1] m l i in
      let c2 = clos_annotate_shift xs2 m l i in
        ([closLang_App t loc_opt (HD c1) c2]))) /\
   (clos_annotate_shift [closLang_Fn t loc vs_opt num_args x1] m l i
     =
      (let k = m + l in
      let vs = match vs_opt with NONE -> [] | SOME vs -> vs in
      let live = FILTER (\n. n < k) vs in
      let vars = MAP (clos_annotate_get_var m l i) live in
      let c1 = clos_annotate_shift [x1] k num_args (shifted_env 0
        live) in
        ([closLang_Fn t loc (SOME vars) num_args (HD c1)]))) /\
   (clos_annotate_shift [closLang_Letrec t loc vsopt fns x1] m l i =
      (let vs = match vsopt with NONE -> [] | SOME x -> x in
      let k = m + l in
      let live = FILTER (\n. n < k) vs in
      let vars = MAP (clos_annotate_get_var m l i) live in
      let new_i = shifted_env 0 live in
      let fns_len = LENGTH fns in
      let cs = MAP (\(n,x). let c = clos_annotate_shift [x] k (n +
        fns_len) new_i in
                              (n,HD c)) fns in
      let c1 = clos_annotate_shift [x1] m (l + LENGTH fns) i in
        ([closLang_Letrec t loc (SOME vars) cs (HD c1)]))) /\
   (clos_annotate_shift [closLang_Handle t x1 x2] m l i =
      (let c1 = clos_annotate_shift [x1] m l i in
      let c2 = clos_annotate_shift [x2] m (l + 1) i in
        ([closLang_Handle t (HD c1) (HD c2)]))) /\
   (clos_annotate_shift [closLang_Call t ticks dest xs] m l i =
      (let c1 = clos_annotate_shift xs m l i in
        ([closLang_Call t ticks dest c1])))`;;

(* HOL4 termination: *)
let shift_sing_def = cake_define_wf
  `MEASURE (\x. match x with INL (e,_6,_7,_8) -> exp_size e | INR (INL
  (es,_9,_10,_11)) -> list_size exp_size es | INR (INR (_12,_13,_14,l))
  -> list_size (pair_size (\x. x) exp_size) l)`
  `shift_sing fns_len m l i =
        match (fns_len,m,l,i) with
          ((db_vars_Var t v),m,l,i) ->
        db_vars_Var t (clos_annotate_get_var m l i v)
        | ((closLang_If t x1 x2 x3),m,l,i) ->
        let c1 = shift_sing x1 m l i in
        let c2 = shift_sing x2 m l i in
        let c3 = shift_sing x3 m l i in
          (closLang_If t c1 c2 c3)
        | ((closLang_Let t xs x2),m,l,i) ->
        let c1 = shift_list xs m l i in
        let c2 = shift_sing x2 m (l + LENGTH xs) i in
          (closLang_Let t c1 c2)
        | ((closLang_Raise t x1),m,l,i) ->
        let (c1) = shift_sing x1 m l i in
          (closLang_Raise t c1)
        | ((closLang_Tick t x1),m,l,i) ->
        let c1 = shift_sing x1 m l i in
          (closLang_Tick t c1)
        | ((closLang_Op t closLang_op xs),m,l,i) ->
        let c1 = shift_list xs m l i in
          (closLang_Op t closLang_op c1)
        | ((closLang_App t loc_opt x1 xs2),m,l,i) ->
        let c1 = shift_sing x1 m l i in
        let c2 = shift_list xs2 m l i in
          (closLang_App t loc_opt c1 c2)
        | ((closLang_Fn t loc vs_opt num_args x1),m,l,i) ->
        let k = m + l in
        let vs = match vs_opt with NONE -> [] | SOME vs -> vs in
        let live = FILTER (\n. n < k) vs in
        let vars = MAP (clos_annotate_get_var m l i) live in
        let c1 = shift_sing x1 k num_args (shifted_env 0 live) in
          (closLang_Fn t loc (SOME vars) num_args c1)
        | ((closLang_Letrec t loc vsopt fns x1),m,l,i) ->
        let vs = match vsopt with NONE -> [] | SOME x -> x in
        let k = m + l in
        let live = FILTER (\n. n < k) vs in
        let vars = MAP (clos_annotate_get_var m l i) live in
        let new_i = shifted_env 0 live in
        let fns_len = LENGTH fns in
        let cs = shift_letrec fns_len k new_i fns in
        let c1 = shift_sing x1 m (l + LENGTH fns) i in
          (closLang_Letrec t loc (SOME vars) cs c1)
        | ((closLang_Handle t x1 x2),m,l,i) ->
        let c1 = shift_sing x1 m l i in
        let c2 = shift_sing x2 m (l + 1) i in
          (closLang_Handle t c1 c2)
        | ((closLang_Call t ticks dest xs),m,l,i) ->
        let c1 = shift_list xs m l i in
          (closLang_Call t ticks dest c1)
        | ([],(m:num),(l:num),(i:num spt)) -> []
        | (((x:closLang_exp) :: xs),m,l,i) ->
        let c1 = shift_sing x m l i in
        let c2 = shift_list xs m l i in
          (c1 :: (c2:closLang_exp list))
        | (fns_len,k,new_i,[]) -> []
        | (fns_len,k,new_i,((n,x) :: rest)) ->
        let c = shift_sing x k (n + fns_len) new_i in
          (n,c) :: shift_letrec fns_len k new_i rest`;;

(* main functions *)

let annotate_def = cake_define
  `clos_annotate_annotate arity xs = clos_annotate_shift (FST
  (alt_free xs)) 0 arity LN`;;

let compile_def = cake_define
  `clos_annotate_compile prog =
     MAP (\(n,args,closLang_exp). (n,args,HD
       (clos_annotate_annotate args [closLang_exp]))) prog`;;

let compile_inc_def = cake_define
  `clos_annotate_compile_inc (e,aux) = (clos_annotate_annotate 0
  e,clos_annotate_compile aux)`;;

(* cv versions *)

let annotate_sing_def = cake_define
  `annotate_sing arity x = shift_sing (FST (alt_free_sing x)) 0 arity
  LN`;;

let annotate_list_def = cake_define
  `annotate_list arity xs = shift_list (FST (alt_free_list xs)) 0
  arity LN`;;
