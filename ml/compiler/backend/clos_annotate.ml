(* ======================================================== *)
(*  clos_annotate: ported from HOL4's
    compiler/backend/clos_annotateScript.sml
    A definition theory, with 13 definitions and 15 theorems.
    Needed by bvlSem.ml, clos_annotateProof.ml and clos_to_bvl.ml.  *)
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

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "clos_annotate"
  ["closLang"; "db_vars"; "misc"];;

(* alt_free calculates free variable annotations, and replaces unused lets with dummies *)

let const_0_def = new_definition
  `const_0 t = closLang_Op t (closLang_IntOp (closLang_Const (&0)))
  []`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let no_overlap_def,no_overlap_ind = define_wf
  `MEASURE (\(x0,x1). (\n. n) x0)`
  [`no_overlap 0 l <=> T`;
   `no_overlap (SUC n) l <=>
         (if has_var n l then F else no_overlap n l)`];;

let alt_free_def,alt_free_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`alt_free [] = ([],db_vars_Empty)`;
   `alt_free (CONS (x:closLang_exp) (CONS y xs)) =
         (let (c1,l1) = alt_free [x] in
         let (c2,l2) = alt_free (CONS y xs) in
           (APPEND c1 c2,mk_Union l1 l2))`;
   `alt_free [(db_vars_Var t v:closLang_exp)] = ([(db_vars_Var t
  v:closLang_exp)],db_vars_Var v)`;
   `alt_free [(closLang_If t x1 x2 x3:closLang_exp)] =
         (let (c1,l1) = alt_free [x1] in
         let (c2,l2) = alt_free [x2] in
         let (c3,l3) = alt_free [x3] in
           ([closLang_If t (HD c1) (HD c2) (HD c3)],mk_Union l1
             (mk_Union l2 l3)))`;
   `alt_free [(closLang_Let t xs x2:closLang_exp)] =
         (let m = LENGTH xs in
         let (c2,l2) = alt_free [x2] in
           if no_overlap m l2 /\ ALL pure xs then
             ([closLang_Let t (REPLICATE m (const_0 t)) (HD
               c2)],db_vars_Shift m l2) else
             let (c1,l1) = alt_free xs in
               ([closLang_Let t c1 (HD c2)],mk_Union l1
                 (db_vars_Shift (LENGTH xs) l2)))`;
   `alt_free [(closLang_Raise t x1:closLang_exp)] =
         (let (c1,l1) = alt_free [x1] in
           ([closLang_Raise t (HD c1)],l1))`;
   `alt_free [(closLang_Tick t x1:closLang_exp)] =
         (let (c1,l1) = alt_free [x1] in
           ([closLang_Tick t (HD c1)],l1))`;
   `alt_free [(closLang_Op t op xs:closLang_exp)] =
         (let (c1,l1) = alt_free xs in
           ([closLang_Op t op c1],l1))`;
   `alt_free [(closLang_App t loc_opt x1 xs2:closLang_exp)] =
         (let (c1,l1) = alt_free [x1] in
         let (c2,l2) = alt_free xs2 in
           ([closLang_App t loc_opt (HD c1) c2],mk_Union l1 l2))`;
   `alt_free [closLang_Fn t loc _1 num_args x1] =
         (let (c1,l1) = alt_free [x1] in
         let l2 = db_vars_Shift num_args l1 in
           ([closLang_Fn t loc (SOME (vars_to_list l2)) num_args
             (HD c1)],l2))`;
   `alt_free [(closLang_Letrec t loc _3 fns x1:closLang_exp)] =
         (let m = LENGTH fns in
         let (c2,l2) = alt_free [x1] in
         // if no_overlap m l2 then
         // ([Let t (REPLICATE m (const_0 t)) (HD c2)], Shift m l2)
         // else
         let res = MAP (\(n,x). let (c,l) = alt_free [x] in
                              ((n,HD c),db_vars_Shift (n + m) l))
                                fns in
         let c1 = MAP FST res in
         let l1 = list_mk_Union (MAP SND res) in
           ([closLang_Letrec t loc (SOME (vars_to_list l1)) c1 (HD
             c2)],
            mk_Union l1 (db_vars_Shift (LENGTH fns) l2)))`;
   `alt_free [(closLang_Handle t x1 x2:closLang_exp)] =
         (let (c1,l1) = alt_free [x1] in
         let (c2,l2) = alt_free [x2] in
           ([closLang_Handle t (HD c1) (HD c2)],mk_Union l1
             (db_vars_Shift 1 l2)))`;
   `alt_free [(closLang_Call t ticks dest xs:closLang_exp)] =
         (let (c1,l1) = alt_free xs in
           ([closLang_Call t ticks dest c1],l1))`];;

let alt_free_sing_def,alt_free_sing_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`alt_free_sing (db_vars_Var t v:closLang_exp) = ((db_vars_Var t
  v:closLang_exp),db_vars_Var v)`;
   `alt_free_sing (closLang_If t x1 x2 x3:closLang_exp) =
         (let (c1,l1) = alt_free_sing x1 in
         let (c2,l2) = alt_free_sing x2 in
         let (c3,l3) = alt_free_sing x3 in
           (closLang_If t c1 c2 c3,mk_Union l1 (mk_Union l2 l3)))`;
   `alt_free_sing (closLang_Let t xs x2:closLang_exp) =
         (let m = LENGTH xs in
         let (c2,l2) = alt_free_sing x2 in
           if no_overlap m l2 /\ ALL pure xs then
             (closLang_Let t (REPLICATE m (const_0 t))
               c2,db_vars_Shift m l2) else
             let (c1,l1) = alt_free_list xs in
               (closLang_Let t c1 c2,mk_Union l1 (db_vars_Shift
                 (LENGTH xs) l2)))`;
   `alt_free_sing (closLang_Raise t x1:closLang_exp) =
         (let (c1,l1) = alt_free_sing x1 in
           (closLang_Raise t c1,l1))`;
   `alt_free_sing (closLang_Tick t x1:closLang_exp) =
         (let (c1,l1) = alt_free_sing x1 in
           (closLang_Tick t c1,l1))`;
   `alt_free_sing (closLang_Op t op xs:closLang_exp) =
         (let (c1,l1) = alt_free_list xs in
           (closLang_Op t op c1,l1))`;
   `alt_free_sing (closLang_App t loc_opt x1 xs2:closLang_exp) =
         (let (c1,l1) = alt_free_sing x1 in
         let (c2,l2) = alt_free_list xs2 in
           (closLang_App t loc_opt c1 c2,mk_Union l1 l2))`;
   `alt_free_sing (closLang_Fn t loc _4 num_args x1) =
         (let (c1,l1) = alt_free_sing x1 in
         let l2 = db_vars_Shift num_args l1 in
           (closLang_Fn t loc (SOME (vars_to_list l2)) num_args
             c1,l2))`;
   `alt_free_sing (closLang_Letrec t loc _6 fns x1:closLang_exp) =
         (let m = LENGTH fns in
         let (c2,l2) = alt_free_sing x1 in
         // if no_overlap m l2 then
         // ([Let t (REPLICATE m (const_0 t)) (HD c2)], Shift m l2)
         // else
         let res = alt_free_letrec m fns in
         let c1 = MAP FST res in
         let l1 = list_mk_Union (MAP SND res) in
           (closLang_Letrec t loc (SOME (vars_to_list l1)) c1 c2,
            mk_Union l1 (db_vars_Shift (LENGTH fns) l2)))`;
   `alt_free_sing (closLang_Handle t x1 x2:closLang_exp) =
         (let (c1,l1) = alt_free_sing x1 in
         let (c2,l2) = alt_free_sing x2 in
           (closLang_Handle t c1 c2,mk_Union l1 (db_vars_Shift 1
             l2)))`;
   `alt_free_sing (closLang_Call t ticks dest xs:closLang_exp) =
         (let (c1,l1) = alt_free_list xs in
           (closLang_Call t ticks dest c1,l1))`;
   `alt_free_list [] = ([],db_vars_Empty)`;
   `alt_free_list (CONS (x:closLang_exp) xs) =
         (let (c1,l1) = alt_free_sing x in
         let (c2,l2) = alt_free_list xs in
           (CONS c1 c2,mk_Union l1 l2))`;
   `alt_free_letrec m [] = []`;
   `alt_free_letrec m (CONS (n,x) rest) =
         (let (c,l) = alt_free_sing x in CONS
           ((n,c),db_vars_Shift (n + m) l) (alt_free_letrec m
           rest))`];;

let alt_free_sing_eq = prove
 (`(!e. alt_free [e] = (\(e,dbs). [e],dbs) (alt_free_sing e)) /\
   (!es. alt_free es = alt_free_list es) /\
   (!m fns. ALL (\(n,e). alt_free [e] = (\(e,dbs). [e],dbs)
     (alt_free_sing e)) fns /\
            alt_free_letrec m fns =
            MAP (\(n,x). let (c,l) = alt_free_sing x in
                           ((n,c),db_vars_Shift (n + m) l)) fns)`,
  CHEAT_TAC);;

(* [local] *)
let alt_free_LENGTH_LEMMA = prove
 (`!xs. (match alt_free xs with (ys,s1) -> (LENGTH xs = LENGTH ys))`,
  CHEAT_TAC);;

let alt_free_LENGTH = prove
 (`!xs ys l. (alt_free xs = (ys,l)) ==> (LENGTH ys = LENGTH xs)`,
  CHEAT_TAC);;

let alt_free_SING = prove
 (`(alt_free [x] = (ys,l)) ==> (?y. ys = [y])`,
  (REPEAT STRIP_TAC THEN RES_ASSUME alt_free_LENGTH THEN
   POP_ASSUM MP_TAC THEN SPEC_TAC(`ys:closLang_exp
     list`,`ys:closLang_exp list`) THEN
   LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ;
     LENGTH_EQ_NIL] THEN
   MESON_TAC[]));;

let LENGTH_FST_alt_free = prove
 (`LENGTH (FST (alt_free fns)) = LENGTH fns`,
  CHEAT_TAC);;

let HD_FST_alt_free = prove
 (`[HD (FST (alt_free [x1]))] = FST (alt_free [x1])`,
  CHEAT_TAC);;

let alt_free_CONS = prove
 (`FST (alt_free (CONS x xs)) = CONS (HD (FST (alt_free [x]))) (FST
  (alt_free xs))`,
  CHEAT_TAC);;

(* shift renames variables to use only those in the annotations *)

let get_var_def = new_definition
  `clos_annotate_get_var m l i v =
     (if v < l then v else l + zlookup i (v - l))`;;

let shifted_env_def,shifted_env_ind = define_rec
  [`shifted_env (n:num) [] = LN`;
   `shifted_env (n:num) (CONS x xs) = sptree_insert x (n:num)
  (shifted_env (n + 1) xs)`];;

let shift_def,shift_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`clos_annotate_shift [] (m:num) (l:num) (i:num spt) = []`;
   `clos_annotate_shift (CONS (x:closLang_exp) (CONS y xs)) (m:num)
  (l:num) (i:num spt) =
         (let c1 = clos_annotate_shift [x] m l i in
         let c2 = clos_annotate_shift (CONS y xs) m l i in
           (APPEND c1 (c2:closLang_exp list)))`;
   `clos_annotate_shift [(db_vars_Var t v:closLang_exp)] (m:num) (l:num)
  (i:num spt) =
         [db_vars_Var t (clos_annotate_get_var m l i v)]`;
   `clos_annotate_shift [(closLang_If t x1 x2 x3:closLang_exp)] (m:num)
  (l:num) (i:num spt) =
         (let c1 = clos_annotate_shift [x1] m l i in
         let c2 = clos_annotate_shift [x2] m l i in
         let c3 = clos_annotate_shift [x3] m l i in
           ([closLang_If t (HD c1) (HD c2) (HD c3)]))`;
   `clos_annotate_shift [(closLang_Let t xs x2:closLang_exp)] (m:num)
  (l:num) (i:num spt) =
         (let c1 = clos_annotate_shift xs m l i in
         let c2 = clos_annotate_shift [x2] m (l + LENGTH xs) i in
           ([closLang_Let t c1 (HD c2)]))`;
   `clos_annotate_shift [(closLang_Raise t x1:closLang_exp)] (m:num)
  (l:num) (i:num spt) =
         (let (c1) = clos_annotate_shift [x1] m l i in
           ([closLang_Raise t (HD c1)]))`;
   `clos_annotate_shift [(closLang_Tick t x1:closLang_exp)] (m:num)
  (l:num) (i:num spt) =
         (let c1 = clos_annotate_shift [x1] m l i in
           ([closLang_Tick t (HD c1)]))`;
   `clos_annotate_shift [(closLang_Op t op xs:closLang_exp)] (m:num)
  (l:num) (i:num spt) =
         (let c1 = clos_annotate_shift xs m l i in
           ([closLang_Op t op c1]))`;
   `clos_annotate_shift [(closLang_App t loc_opt x1 xs2:closLang_exp)]
  (m:num) (l:num) (i:num spt) =
         (let c1 = clos_annotate_shift [x1] m l i in
         let c2 = clos_annotate_shift xs2 m l i in
           ([closLang_App t loc_opt (HD c1) c2]))`;
   `clos_annotate_shift [closLang_Fn t loc vs_opt num_args x1] (m:num)
  (l:num) (i:num spt) =
         (let k = m + l in
         let vs = (match vs_opt with NONE -> [] | SOME vs -> vs) in
         let live = FILTER (\n. n < k) vs in
         let vars' = MAP (clos_annotate_get_var m l i) live in
         let c1 = clos_annotate_shift [x1] k num_args (shifted_env 0
           live) in
           ([closLang_Fn t loc (SOME vars') num_args (HD c1)]))`;
   `clos_annotate_shift [(closLang_Letrec t loc vsopt fns
  x1:closLang_exp)] (m:num) (l:num) (i:num spt) =
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
           ([closLang_Letrec t loc (SOME vars') cs (HD c1)]))`;
   `clos_annotate_shift [(closLang_Handle t x1 x2:closLang_exp)] (m:num)
  (l:num) (i:num spt) =
         (let c1 = clos_annotate_shift [x1] m l i in
         let c2 = clos_annotate_shift [x2] m (l + 1) i in
           ([closLang_Handle t (HD c1) (HD c2)]))`;
   `clos_annotate_shift [(closLang_Call t ticks dest xs:closLang_exp)]
  (m:num) (l:num) (i:num spt) =
         (let c1 = clos_annotate_shift xs m l i in
           ([closLang_Call t ticks dest c1]))`];;

let shift_sing_def,shift_sing_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`shift_sing (db_vars_Var t v:closLang_exp) (m:num) (l:num) (i:num
  spt) =
         db_vars_Var t (clos_annotate_get_var m l i v)`;
   `shift_sing (closLang_If t x1 x2 x3:closLang_exp) (m:num) (l:num)
  (i:num spt) =
         (let c1 = shift_sing x1 m l i in
         let c2 = shift_sing x2 m l i in
         let c3 = shift_sing x3 m l i in
           (closLang_If t c1 c2 c3))`;
   `shift_sing (closLang_Let t xs x2:closLang_exp) (m:num) (l:num)
  (i:num spt) =
         (let c1 = shift_list xs m l i in
         let c2 = shift_sing x2 m (l + LENGTH xs) i in
           (closLang_Let t c1 c2))`;
   `shift_sing (closLang_Raise t x1:closLang_exp) (m:num) (l:num) (i:num
  spt) =
         (let (c1) = shift_sing x1 m l i in
           (closLang_Raise t c1))`;
   `shift_sing (closLang_Tick t x1:closLang_exp) (m:num) (l:num) (i:num
  spt) =
         (let c1 = shift_sing x1 m l i in
           (closLang_Tick t c1))`;
   `shift_sing (closLang_Op t op xs:closLang_exp) (m:num) (l:num) (i:num
  spt) =
         (let c1 = shift_list xs m l i in
           (closLang_Op t op c1))`;
   `shift_sing (closLang_App t loc_opt x1 xs2:closLang_exp) (m:num)
  (l:num) (i:num spt) =
         (let c1 = shift_sing x1 m l i in
         let c2 = shift_list xs2 m l i in
           (closLang_App t loc_opt c1 c2))`;
   `shift_sing (closLang_Fn t loc vs_opt num_args x1) (m:num) (l:num)
  (i:num spt) =
         (let k = m + l in
         let vs = (match vs_opt with NONE -> [] | SOME vs -> vs) in
         let live = FILTER (\n. n < k) vs in
         let vars' = MAP (clos_annotate_get_var m l i) live in
         let c1 = shift_sing x1 k num_args (shifted_env 0 live) in
           (closLang_Fn t loc (SOME vars') num_args c1))`;
   `shift_sing (closLang_Letrec t loc vsopt fns x1:closLang_exp) (m:num)
  (l:num) (i:num spt) =
         (let vs = (match vsopt with NONE -> [] | SOME x -> x) in
         let k = m + l in
         let live = FILTER (\n. n < k) vs in
         let vars' = MAP (clos_annotate_get_var m l i) live in
         let new_i = shifted_env 0 live in
         let fns_len = LENGTH fns in
         let cs = shift_letrec fns_len k new_i fns in
         let c1 = shift_sing x1 m (l + LENGTH fns) i in
           (closLang_Letrec t loc (SOME vars') cs c1))`;
   `shift_sing (closLang_Handle t x1 x2:closLang_exp) (m:num) (l:num)
  (i:num spt) =
         (let c1 = shift_sing x1 m l i in
         let c2 = shift_sing x2 m (l + 1) i in
           (closLang_Handle t c1 c2))`;
   `shift_sing (closLang_Call t ticks dest xs:closLang_exp) (m:num)
  (l:num) (i:num spt) =
         (let c1 = shift_list xs m l i in
           (closLang_Call t ticks dest c1))`;
   `shift_list [] (m:num) (l:num) (i:num spt) = []`;
   `shift_list (CONS (x:closLang_exp) xs) (m:num) (l:num) (i:num spt) =
         (let c1 = shift_sing x m l i in
         let c2 = shift_list xs m l i in
           (CONS c1 (c2:closLang_exp list)))`;
   `shift_letrec fns_len k new_i [] = []`;
   `shift_letrec fns_len k new_i (CONS (n,x) rest) =
         (let c = shift_sing x k (n + fns_len) new_i in CONS
           (n,c) (shift_letrec fns_len k new_i rest))`];;

let shift_sing_eq = prove
 (`(!e m l i. clos_annotate_shift [e] m l i = [shift_sing e m l i]) /\
   (!es m l i. clos_annotate_shift es m l i = shift_list es m l i) /\
   (!fns_len k new_i fns.
      ALL (\(n,e). clos_annotate_shift [e] k (n + fns_len) new_i =
                     [shift_sing e k (n + fns_len) new_i]) fns /\
      shift_letrec fns_len k new_i fns =
        MAP (\(n,x). let c = shift_sing x k (n + fns_len) new_i in
                       (n,c)) fns)`,
  CHEAT_TAC);;

let shift_LENGTH_LEMMA = prove
 (`!xs m l i. LENGTH (clos_annotate_shift xs m l i) = LENGTH xs`,
  (REWRITE_TAC[shift_sing_eq] THEN LIST_INDUCT_TAC THEN
   REWRITE_TAC[shift_sing_def] THEN CONV_TAC (TOP_DEPTH_CONV
     let_CONV) THEN
   ASM_REWRITE_TAC[LENGTH]));;

(* HOL4 clos_annotateScript.sml:383-387: a theorem that HOL4 states
   as the value of an ML expression: shift_SING *)

let shift_CONS = prove
 (`clos_annotate_shift (CONS (x:closLang_exp) xs) m l i =
      (let c1 = clos_annotate_shift [x] m l i in
      let c2 = clos_annotate_shift xs m l i in
        (CONS (HD c1) (c2:closLang_exp list)))`,
  CHEAT_TAC);;

(* [simp] *)
let HD_shift = prove
 (`LENGTH (clos_annotate_shift [x] m l i) = 1 /\
   [HD (clos_annotate_shift [x] m l i)] = clos_annotate_shift [x] m
     l i`,
  CHEAT_TAC);;

(* main functions *)

let annotate_def = new_definition
  `clos_annotate_annotate arity xs = clos_annotate_shift (FST
  (alt_free xs)) 0 arity LN`;;

let clos_annotate_compile_def = new_definition
  `clos_annotate_compile prog =
     MAP (\(n,args,exp). (n,args,HD (clos_annotate_annotate args
       [exp]))) prog`;;

let clos_annotate_compile_inc_def = new_definition
  `clos_annotate_compile_inc (e,aux) = (clos_annotate_annotate 0
  e,clos_annotate_compile aux)`;;

(* cv versions *)

let annotate_sing_def = new_definition
  `annotate_sing arity x = shift_sing (FST (alt_free_sing x)) 0 arity
  LN`;;

let annotate_list_def = new_definition
  `annotate_list arity xs = shift_list (FST (alt_free_list xs)) 0
  arity LN`;;

let annotate_sing_eq = prove
 (`clos_annotate_annotate arity [e] = [annotate_sing arity e] /\
   clos_annotate_annotate arity es = annotate_list arity es`,
  CHEAT_TAC);;

(* compile_eq *)
let clos_annotate_compile_eq = prove
 (`clos_annotate_compile prog =
     MAP (\(n,args,exp). (n,args,annotate_sing args exp)) prog`,
  CHEAT_TAC);;

let compile_inc_eq = prove
 (`clos_annotate_compile_inc (e,aux) = (annotate_list 0
  e,clos_annotate_compile aux)`,
  (REWRITE_TAC[clos_annotate_compile_inc_def; annotate_sing_eq]));;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
