(* ======================================================== *)
(*  clos_known: ported from HOL4's
    compiler/backend/clos_knownScript.sml
    A definition theory, with 29 definitions, 4 datatypes and 12
    theorems.  Needed by 7 files of the port.  *)
(* ======================================================== *)

(*
  This complicated compiler phase tracks where closure values flow
  in a program. It attempts to annotate function applications with the
  (numeric) names of the called closures (annotations lead to better
  code in clos_to_bvl). If the code for the applied closure is
  statically known and small enough, then this compiler phase can
  inline the body of the called closure. The function inlining is
  recursive and controlled using configurable parameters.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_fvs.ml";;
needs "compiler/backend/clos_letop.ml";;
needs "compiler/backend/clos_op.ml";;
needs "compiler/backend/clos_ticks.ml";;
needs "compiler/backend/db_vars.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "clos_known"
  ["closLang"; "clos_fvs"; "clos_letop"; "clos_op"; "clos_ticks";
   "db_vars"];;

let _ = do_list hide_constant ["all"; "pmatch"];;

(* HOL4 clos_knownScript.sml:16: code that the source has in a
   comment *)

(* This definition is written to short-circuit,
   i.e. exit as soon as possible. *)
let _ = size_thms "closLang_exp";;
(* HOL4 clos_knownScript.sml:63-66: the tactic that proves the
   termination *)
let get_size_sc_aux_def,get_size_sc_aux_ind = define_guess
  [`get_size_sc_aux n [] = n`;
   `get_size_sc_aux n (x :: y :: xs) =
         (if n = 0 then n else
           let n = get_size_sc_aux n [x] in if n = 0 then n else
             get_size_sc_aux n (y :: xs))`;
   `get_size_sc_aux n [(Var t v:closLang_exp)] = n - 1`;
   `get_size_sc_aux n [(If t x1 x2 x3:closLang_exp)] =
         (let n = n - 1 in if n = 0 then 0 else
         let n = get_size_sc_aux n [x1] in if n = 0 then 0 else
         let n = get_size_sc_aux n [x2] in if n = 0 then 0 else
           get_size_sc_aux n [x3])`;
   `get_size_sc_aux n [(Let t xs x2:closLang_exp)] =
         (let n = n - 1 in if n = 0 then 0 else
         let n = get_size_sc_aux n xs in if n = 0 then 0 else
           get_size_sc_aux n [x2])`;
   `get_size_sc_aux n [(Raise t x1:closLang_exp)] =
         (let n = n - 1 in if n = 0 then 0 else
           get_size_sc_aux n [x1])`;
   `get_size_sc_aux n [(Handle t x1 x2:closLang_exp)] =
         (let n = n - 1 in if n = 0 then 0 else
         let n = get_size_sc_aux n [x1] in if n = 0 then 0 else
           get_size_sc_aux n [x2])`;
   `get_size_sc_aux n [(closLang_Op t op xs:closLang_exp)] =
         (let n = n - 1 in if n = 0 then 0 else
           get_size_sc_aux n xs)`;
   `get_size_sc_aux n [(closLang_Tick t x:closLang_exp)] =
  get_size_sc_aux n [x]`;
   `get_size_sc_aux n [(closLang_Call t ticks dest xs:closLang_exp)] =
         (let n = n - 1 in if n = 0 then 0 else
           get_size_sc_aux n xs)`;
   `get_size_sc_aux n [closLang_Fn t loc_opt ws_opt num_args x1] =
         (let n = n - 1 in if n = 0 then 0 else
           get_size_sc_aux n [x1])`;
   `get_size_sc_aux n [(Letrec t loc_opt ws_opt fns x1:closLang_exp)] =
         (let n = n - 1 in if n = 0 then 0 else
         let n = get_size_sc_aux n (MAP SND fns) in if n = 0 then 0
           else
           get_size_sc_aux n [x1])`;
   `get_size_sc_aux n [(App t loc_opt x1 xs:closLang_exp)] =
         (let n = n - 1 in if n = 0 then 0 else
         let n = get_size_sc_aux n [x1] in if n = 0 then 0 else
           get_size_sc_aux n xs)`];;

let get_size_sc_def = new_definition
  `get_size_sc limit' e =
     (let n = get_size_sc_aux (limit' + 1) [e] in
       if n = 0 then NONE else SOME ((limit' + 1) - n))`;;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 clos_knownScript.sml:99-102: the tactic that proves the
   termination *)
let get_size_aux_def,get_size_aux_ind = define_wf
  `MEASURE (list_size closLang_exp_size)`
  [`get_size_aux [] = 0`;
   `get_size_aux (x :: y :: xs) =
         get_size_aux [x] + get_size_aux (y :: xs)`;
   `get_size_aux [(Var t v:closLang_exp)] = 1`;
   `get_size_aux [(If t x1 x2 x3:closLang_exp)] =
         1 + get_size_aux [x1] + get_size_aux [x2] + get_size_aux
           [x3]`;
   `get_size_aux [(Let t xs x2:closLang_exp)] =
         1 + get_size_aux xs + get_size_aux [x2]`;
   `get_size_aux [(Raise t x1:closLang_exp)] =
         1 + get_size_aux [x1]`;
   `get_size_aux [(Handle t x1 x2:closLang_exp)] =
         1 + get_size_aux [x1] + get_size_aux [x2]`;
   `get_size_aux [(closLang_Op t op xs:closLang_exp)] =
         1 + get_size_aux xs`;
   `get_size_aux [(closLang_Tick t x:closLang_exp)] =
         get_size_aux [x]`;
   `get_size_aux [(closLang_Call t ticks dest xs:closLang_exp)] =
         1 + get_size_aux xs`;
   `get_size_aux [closLang_Fn t loc_opt ws_opt num_args x1] =
         1 + get_size_aux [x1]`;
   `get_size_aux [(Letrec t loc_opt ws_opt fns x1:closLang_exp)] =
         1 + get_size_aux (MAP SND fns) + get_size_aux [x1]`;
   `get_size_aux [(App t loc_opt x1 xs:closLang_exp)] =
         1 + get_size_aux [x1] + get_size_aux xs`];;

(* HOL4 clos_knownScript.sml:104: ML code, not ported *)

let get_size_def = new_definition
  `clos_known_get_size e = get_size_aux [e]`;;
hol4_overload "get_size" "clos_known_get_size";;

let get_size_sc_aux_correct = prove
 (`!xs limit' n. get_size_sc_aux limit' xs = limit' - get_size_aux xs`,
  CHEAT_TAC);;

let get_size_sc_SOME = prove
 (`!exp limit' n. get_size_sc limit' exp = SOME n ==>
  clos_known_get_size exp = n`,
  CHEAT_TAC);;

let clos_known_free_def,clos_known_free_ind = define_guess
  [`clos_known_free [] = ([],db_vars_Empty)`;
   `clos_known_free ((x:closLang_exp) :: y :: xs) =
         (let (c1,l1) = clos_known_free [x] in
         let (c2,l2) = clos_known_free (y :: xs) in
           (c1 ++ c2,mk_Union l1 l2))`;
   `clos_known_free [(Var t v:closLang_exp)] = ([(Var t
  v:closLang_exp)],Var v)`;
   `clos_known_free [(If t x1 x2 x3:closLang_exp)] =
         (let (c1,l1) = clos_known_free [x1] in
         let (c2,l2) = clos_known_free [x2] in
         let (c3,l3) = clos_known_free [x3] in
           ([If t (HD c1) (HD c2) (HD c3)],mk_Union l1 (mk_Union
             l2 l3)))`;
   `clos_known_free [(Let t xs x2:closLang_exp)] =
         (let (c1,l1) = clos_known_free xs in
         let (c2,l2) = clos_known_free [x2] in
           ([Let t c1 (HD c2)],mk_Union l1 (Shift (LENGTH xs)
             l2)))`;
   `clos_known_free [(Raise t x1:closLang_exp)] =
         (let (c1,l1) = clos_known_free [x1] in
           ([Raise t (HD c1)],l1))`;
   `clos_known_free [(closLang_Tick t x1:closLang_exp)] =
         (let (c1,l1) = clos_known_free [x1] in
           ([closLang_Tick t (HD c1)],l1))`;
   `clos_known_free [(closLang_Op t op xs:closLang_exp)] =
         (let (c1,l1) = clos_known_free xs in
           ([closLang_Op t op c1],l1))`;
   `clos_known_free [(App t loc_opt x1 xs2:closLang_exp)] =
         (let (c1,l1) = clos_known_free [x1] in
         let (c2,l2) = clos_known_free xs2 in
           ([App t loc_opt (HD c1) c2],mk_Union l1 l2))`;
   `clos_known_free [closLang_Fn t loc _1 num_args x1] =
         (let (c1,l1) = clos_known_free [x1] in
         let l2 = Shift num_args l1 in
           ([closLang_Fn t loc (SOME (vars_to_list l2)) num_args
             (HD c1)],l2))`;
   `clos_known_free [(Letrec t loc _3 fns x1:closLang_exp)] =
         (let m = LENGTH fns in
         let res = MAP (\(n,x). let (c,l) = clos_known_free [x] in
                              ((n,HD c),Shift (n + m) l)) fns in
         let c1 = MAP FST res in
         let l1 = list_mk_Union (MAP SND res) in
         let (c2,l2) = clos_known_free [x1] in
           ([Letrec t loc (SOME (vars_to_list l1)) c1 (HD c2)],
            mk_Union l1 (Shift (LENGTH fns) l2)))`;
   `clos_known_free [(Handle t x1 x2:closLang_exp)] =
         (let (c1,l1) = clos_known_free [x1] in
         let (c2,l2) = clos_known_free [x2] in
           ([Handle t (HD c1) (HD c2)],mk_Union l1 (Shift 1 l2)))`;
   `clos_known_free [(closLang_Call t ticks dest xs:closLang_exp)] =
         (let (c1,l1) = clos_known_free xs in
           ([closLang_Call t ticks dest c1],l1))`];;
hol4_overload "free" "clos_known_free";;

(* HOL4 clos_knownScript.sml:175-220: code that the source has in a
   comment *)

let clos_known_closed_def = new_definition
  `clos_known_closed x = (\t. t = LN) (db_to_set (SND
  (clos_known_free [x])))`;;
hol4_overload "closed" "clos_known_closed";;

let _ = size_thms "closLang_exp";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let contains_closures_def,contains_closures_ind = define_wf
  `MEASURE (\x0. closLang_exp_size1 x0)`
  [`contains_closures [] = F`;
   `contains_closures (x :: y :: xs) =
        (if contains_closures [x] then T else
          contains_closures (y :: xs))`;
   `contains_closures [(Var t v:closLang_exp)] = F`;
   `contains_closures [(If t x1 x2 x3:closLang_exp)] =
         (if contains_closures [x1] then T else
         if contains_closures [x2] then T else
           contains_closures [x3])`;
   `contains_closures [(Let t xs x2:closLang_exp)] =
         (if contains_closures xs then T else
           contains_closures [x2])`;
   `contains_closures [(Raise t x1:closLang_exp)] = contains_closures
  [x1]`;
   `contains_closures [(Handle t x1 x2:closLang_exp)] =
         (if contains_closures [x1] then T else
           contains_closures [x2])`;
   `contains_closures [(closLang_Op t op xs:closLang_exp)] =
  contains_closures xs`;
   `contains_closures [(closLang_Tick t x:closLang_exp)] =
  contains_closures [x]`;
   `contains_closures [(closLang_Call t ticks dest xs:closLang_exp)]
  = contains_closures xs`;
   `contains_closures [closLang_Fn t loc_opt ws_opt num_args x1] = T`;
   `contains_closures [(Letrec t loc_opt ws_opt fns x1:closLang_exp)]
  = T`;
   `contains_closures [(App t loc_opt x1 xs:closLang_exp)] =
         (if contains_closures [x1] then T else
           contains_closures xs)`];;

(* -----------------------------------------------------------------

  This compiler transformation turns App NONEs into APP SOMEs.
  An App can carry a `SOME loc` if:
   1) the closure value that is used there was created with location loc;
   2) the closure value exepcts the number of arguments it gets here.

  This part of the compiler makes two passes. The first pass tracks
  which closure values flow into which globals. The second pass tracks
  closure values (with help of the result of the first pass) and
  switches App NONEs into App SOMEs wherever possible.

   ----------------------------------------------------------------- *)

let val_approx_INDUCT,val_approx_RECURSION = define_datatype
  "val_approx = clos_known_ClosNoInline (num) (num) \
   // location in code table, arity\n\
   | clos_known_Clos (num) (num) (closLang_exp) (num) \
   // loc, arity, body, body size\n\
   | clos_known_Tuple (num) (val_approx list) \
   // conses or tuples\n\
   | clos_known_Int (int) \
   // used to index tuples\n\
   | clos_known_Other \
   // unknown\n\
   | clos_known_Impossible \
   // value 'returned' by Raise";;
hol4_overload "ClosNoInline" "clos_known_ClosNoInline";;
hol4_overload "Clos" "clos_known_Clos";;
hol4_overload "Tuple" "clos_known_Tuple";;
hol4_overload "Int" "clos_known_Int";;
hol4_overload "Other" "clos_known_Other";;
hol4_overload "Impossible" "clos_known_Impossible";;
(* HOL4 clos_knownScript.sml:276: ML code, not ported *)

let _ = size_thms "val_approx";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let clos_known_merge_def,clos_known_merge_ind = define_wf
  `MEASURE (\(x0,x1). val_approx_size x0 + val_approx_size x1)`
  [`clos_known_merge x y =
        match (x,y) with
          (clos_known_Impossible,y) -> y
        | (x,clos_known_Impossible) -> x
        | ((clos_known_Tuple tg1 xs),(clos_known_Tuple tg2 ys)) ->
        (if LENGTH xs = LENGTH ys /\ tg1 = tg2 then clos_known_Tuple
          tg1 (MAP2 clos_known_merge xs ys) else clos_known_Other)
        | ((clos_known_ClosNoInline m1 n1),(clos_known_ClosNoInline
          m2 n2)) ->
        (if m1 = m2 /\ n1 = n2 then clos_known_ClosNoInline m1 n1
          else clos_known_Other)
        | ((clos_known_Clos m1 n1 e1 s1),(clos_known_Clos m2 n2 e2
          s2)) ->
        (if m1 = m2 /\ n1 = n2 /\ e1 = e2 /\ s1 = s2 then
          clos_known_Clos m1 n1 e1 s1 else clos_known_Other)
        | ((Int i),(Int j)) -> (if i = j then Int i else
          clos_known_Other)
        | (_4,_5) -> clos_known_Other`];;
hol4_overload "merge" "clos_known_merge";;

(* HOL4 clos_knownScript.sml:294-295: a theorem that HOL4 states as
   the value of an ML expression: merge_def *)

(* Avoid MAP2 *)
let _ = size_thms "val_approx";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 clos_knownScript.sml:313-321: the tactic that proves the
   termination *)
let merge_tup_def,merge_tup_ind = define_wf
  `MEASURE (val_approx_size o FST)`
  [`merge_tup x1 =
        match x1 with
          (clos_known_Impossible,y) -> y
        | (x,clos_known_Impossible) -> x
        | (clos_known_Tuple tg1 xs,clos_known_Tuple tg2 ys) ->
        (if LENGTH xs = LENGTH ys /\ tg1 = tg2 then
          clos_known_Tuple tg1 (MAP merge_tup (ZIP xs ys)) else
            clos_known_Other)
        | (clos_known_ClosNoInline m1 n1,clos_known_ClosNoInline m2
          n2) ->
        (if m1 = m2 /\ n1 = n2 then clos_known_ClosNoInline m1 n1
          else clos_known_Other)
        | (clos_known_Clos m1 n1 e1 s1,clos_known_Clos m2 n2 e2 s2)
          ->
        (if m1 = m2 /\ n1 = n2 /\ e1 = e2 /\ s1 = s2 then
          clos_known_Clos m1 n1 e1 s1 else clos_known_Other)
        | (Int i,Int j) -> (if i = j then Int i else
          clos_known_Other)
        | (_6,_7) -> clos_known_Other`];;

(* HOL4 clos_knownScript.sml:323-342: code that the source has in a
   comment *)

let merge_alt = prove
 (`!x y. merge x y = merge_tup (x,y)`,
  CHEAT_TAC);;

let known_op_def = new_definition
  `known_op op as g =
        match op with
          closLang_GlobOp (closLang_Global n) ->
      (if NULL as then
        match sptree_lookup n g with NONE -> (clos_known_Other,g) |
          SOME x -> (x,g) else (clos_known_Other,g))
        | (closLang_GlobOp (closLang_SetGlobal n)) ->
        (match as with [] -> (clos_known_Other,g) | (a :: xs) ->
          (match sptree_lookup n g with NONE ->
            (clos_known_Other,sptree_insert n a g) | SOME other ->
            (clos_known_Other,sptree_insert n (merge other a) g)))
        | (closLang_BlockOp (closLang_Cons tg)) -> (clos_known_Tuple
          tg as,g)
        | (closLang_IntOp (closLang_Const i)) -> (Int i,g)
        | (closLang_MemOp closLang_El) ->
        (match as with [clos_known_Tuple _8 xs; Int i] ->
            (if (&0) <= i /\ i < &(LENGTH xs) then (EL (num_of_int i)
              xs,g) else (clos_known_Other,g)) | clos_known_Impossible
              :: xs -> (clos_known_Impossible,g) | _9 ::
              clos_known_Impossible :: xs -> (clos_known_Impossible,g) |
              _10 -> (clos_known_Other,g))
        | op -> (clos_known_Other,g)`;;

let known_op_pmatch = prove
 (`!op as g.
   known_op op as g =
   (match op with
     closLang_GlobOp (closLang_Global n) ->
      (if NULL as then
        match sptree_lookup n g with NONE -> (clos_known_Other,g) |
          SOME x -> (x,g) else (clos_known_Other,g)) | closLang_GlobOp
          (closLang_SetGlobal n) ->
     (match as with [] -> (clos_known_Other,g) | (a :: xs) ->
        (match sptree_lookup n g with NONE ->
          (clos_known_Other,sptree_insert n a g) | SOME other ->
          (clos_known_Other,sptree_insert n (merge other a) g))) |
          closLang_BlockOp (closLang_Cons tg) -> (clos_known_Tuple tg
          as,g) | closLang_IntOp (closLang_Const i) -> (Int i,g) |
          closLang_MemOp closLang_El ->
     (match as with [clos_known_Tuple _11 xs; Int i] ->
          (if (&0) <= i /\ i < &(LENGTH xs) then (EL (num_of_int i)
            xs,g) else (clos_known_Other,g)) | clos_known_Impossible
            :: xs -> (clos_known_Impossible,g) | _12 ::
            clos_known_Impossible :: xs -> (clos_known_Impossible,g) |
            _13 -> (clos_known_Other,g)) | _14 ->
            (clos_known_Other,g))`,
  CHEAT_TAC);;

(* EL_MEM_LEMMA[local] *)
let clos_known_EL_MEM_LEMMA = prove
 (`!xs i x. i < LENGTH xs /\ (x = EL i xs) ==> MEM x xs`,
  CHEAT_TAC);;

let clos_approx_def = new_definition
  `clos_approx max_size loc num_args body =
     (match get_size_sc max_size body with NONE ->
       clos_known_ClosNoInline loc num_args | SOME body_size ->
       clos_known_Clos loc num_args body body_size)`;;

let clos_gen_noinline_def,clos_gen_noinline_ind = define_rec
  [`clos_gen_noinline n i [] = []`;
   `clos_gen_noinline n i ((a,e) :: xs) =
        clos_known_ClosNoInline (n + 2 * i) a ::
          clos_gen_noinline n (i + 1) xs`];;

let globalOpt_INDUCT,globalOpt_RECURSION = define_datatype
  "globalOpt = gO_Int (int) | gO_NullTuple (num) | gO_None";;

let isGlobal_def = new_definition
  `isGlobal x1 =
        match x1 with
          closLang_GlobOp (closLang_Global _15) -> T
        | _16 -> F`;;

let isGlobal_pmatch = prove
 (`!op.
     isGlobal op =
     (match op with
       closLang_GlobOp (closLang_Global _17) -> T | _18 -> F)`,
  CHEAT_TAC);;

let gO_destApx_def = new_definition
  `gO_destApx x1 =
        match x1 with
          (Int i:val_approx) -> gO_Int i
        | (clos_known_Tuple tag args) -> (if NULL args then
          gO_NullTuple tag else gO_None)
        | _19 -> gO_None`;;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let mk_Ticks_def,mk_Ticks_ind = define_wf
  `MEASURE (FST o SND o SND)`
  [`clos_known_mk_Ticks t tc n e =
     (if n = 0 then e else clos_known_mk_Ticks t (tc + 1) (n -
       1) (closLang_Tick (mk_cons t tc) e))`];;
hol4_overload "mk_Ticks" "clos_known_mk_Ticks";;

let inliningDecision_INDUCT,inliningDecision_RECURSION = define_datatype
  "inliningDecision = inlD_Nothing | inlD_Annotate (num) | \
   inlD_LetInline (closLang_exp)";;

let clos_known_config_FIELDS = define_record "clos_known_config"
  ["inline_max_body_size","num";
   "inline_factor","num";
   (* As in 'Inline expansion: when and how?' by Manuel Serrano *)
   "initial_inline_factor","num";
   "val_approx_spt","val_approx spt"
   (* TODO: this could replace the explicit g argument in known_def *)
  ];;

let default_inline_factor_def = new_definition
  `default_inline_factor = 8`;;
let default_max_body_size_def = new_definition
  `default_max_body_size max_app inline_factor = (max_app + 1) *
  inline_factor`;;

let mk_config_def = new_definition
  `mk_config max_body_size inline_factor = mk_clos_known_config
  max_body_size inline_factor inline_factor LN`;;

let clos_known_default_config_def = new_definition
  `clos_known_default_config max_app = mk_config
  (default_max_body_size max_app default_inline_factor)
  default_inline_factor`;;
hol4_overload "default_config" "clos_known_default_config";;

let dec_inline_factor_def = new_definition
  `dec_inline_factor c = clos_known_config_inline_factor_fupd (K
  (clos_known_config_inline_factor c DIV 2)) c`;;

let reset_inline_factor_def = new_definition
  `reset_inline_factor c = clos_known_config_inline_factor_fupd (K
  (clos_known_config_initial_inline_factor c)) c`;;

let decide_inline_def = new_definition
  `decide_inline c fapx app_lopt app_arity =
     (match fapx with clos_known_ClosNoInline loc arity ->
           (if app_lopt = NONE /\ app_arity = arity then
             inlD_Annotate loc else inlD_Nothing) | clos_known_Clos loc
             arity body body_size ->
           (if app_lopt = NONE /\ app_arity = arity then
             (if body_size < clos_known_config_inline_factor c * (1 +
               app_arity) /\
                 ~(contains_closures [body]) /\
                 clos_known_closed (closLang_Fn (implode "") NONE
                   NONE app_arity body) then
                 // Consider moving these checks to the point where Clos approximations
                 // are created, and bake them into the val_approx_val relation.
                 inlD_LetInline body else inlD_Annotate loc) else
                   inlD_Nothing) | _20 -> inlD_Nothing)`;;

let decide_inline_LetInline = prove
 (`!c fapx lopt arity body.
     decide_inline c fapx lopt arity = inlD_LetInline body ==> 0 <
       clos_known_config_inline_factor c`,
  CHEAT_TAC);;

let _ = size_thms "closLang_exp";;
(* HOL4 clos_knownScript.sml:630-639: the tactic that proves the
   termination *)
let known_def,known_ind = define_guess
  [`known c [] vs (g:val_approx spt) = ([],g)`;
   `known c ((x:closLang_exp) :: y :: xs) vs (g:val_approx spt) =
         (let (eas1,g) = known c [x] vs g in
         let (eas2,g) = known c (y :: xs) vs g in
           (eas1 ++ eas2,g))`;
   `known c [(Var t v:closLang_exp)] vs (g:val_approx spt) =
         ([((Var t v:closLang_exp),any_el v vs
           clos_known_Other)],g)`;
   `known c [(If t x1 x2 x3:closLang_exp)] vs (g:val_approx spt) =
         (let (ea1,g) = known c [x1] vs g in
         let (ea2,g) = known c [x2] vs g in
         let (ea3,g) = known c [x3] vs g in
         let (e1,a1) = HD ea1 in
         let (e2,a2) = HD ea2 in
         let (e3,a3) = HD ea3 in
           ([(If t e1 e2 e3),merge a2 a3],g))`;
   `known c [(Let t xs x2:closLang_exp)] vs (g:val_approx spt) =
         (let (ea1,g) = known c xs vs g in
         let (ea2,g) = known c [x2] (MAP SND ea1 ++ vs) g in
         let (e2,a2) = HD ea2 in
           ([(Let t (MAP FST ea1) e2,a2)],g))`;
   `known c [(Raise t x1:closLang_exp)] vs (g:val_approx spt) =
         (let (ea1,g) = known c [x1] vs g in
         let (e1,a1) = HD ea1 in
           ([(Raise t e1,clos_known_Impossible)],g))`;
   `known c [(closLang_Tick t x1:closLang_exp)] vs (g:val_approx spt) =
         (let (ea1,g) = known c [x1] vs g in
         let (e1,a1) = HD ea1 in
           ([(closLang_Tick t e1,a1)],g))`;
   `known c [(Handle t x1 x2:closLang_exp)] vs (g:val_approx spt) =
         (let (ea1,g) = known c [x1] vs g in
         let (ea2,g) = known c [x2] (clos_known_Other :: vs) g in
         let (e1,a1) = HD ea1 in
         let (e2,a2) = HD ea2 in
           ([(Handle t e1 e2,merge a1 a2)],g))`;
   `known c [(closLang_Call t ticks dest xs:closLang_exp)] vs
  (g:val_approx spt) =
         (let (ea1,g) = known c xs vs g in
           ([(closLang_Call t ticks dest (MAP FST
             ea1),clos_known_Other)],g))`;
   `known c [(closLang_Op t op xs:closLang_exp)] vs (g:val_approx spt) =
         (let (ea1,g) = known c xs vs g in
         let (a,g) = known_op op (REVERSE (MAP SND ea1)) g in
         let e =
             (if isGlobal op then
               match gO_destApx a with gO_None -> clos_op_SmartOp t
                 op | gO_Int i -> closLang_Op t (closLang_IntOp
                 (closLang_Const i)) | gO_NullTuple tag -> closLang_Op t
                 (closLang_BlockOp (Cons tag)) else clos_op_SmartOp t
                 op) (MAP FST ea1) in
           ([(e,a)],g))`;
   `known c [(App t loc_opt x xs:closLang_exp)] vs (g:val_approx spt) =
         (let (ea2,g) = known c xs vs g in
         let (ea1,g) = known c [x] vs g in
         let (e1,a1) = HD ea1 in
           match decide_inline c a1 loc_opt (LENGTH xs) with
             inlD_Nothing -> ([(App t loc_opt e1 (MAP FST
             ea2),clos_known_Other)],g) | inlD_Annotate new_loc ->
             ([(App t (SOME new_loc) e1 (MAP FST
             ea2),clos_known_Other)],g) | inlD_LetInline body ->
                 (let (eabody,_23) = known (dec_inline_factor c)
                   [body] (MAP SND ea2) g in
                 let (ebody,abody) = HD eabody in
                   if pure x then
                     ([(
                        // We don't have to evaluate x
                        Let (mk_cons t 0) (MAP FST ea2)
                              (clos_known_mk_Ticks t 1 (LENGTH xs)
                                ebody),abody)],g) else
                     ([(
                        // We need to evaluate x for its side-effects,
                        // but we must do so after evaluating the args.
                        Let (mk_cons t 0) (SNOC e1 (MAP FST ea2))
                              (clos_known_mk_Ticks t 1 (LENGTH
                                xs) ebody),abody)],g)))`;
   `known c [closLang_Fn t loc_opt ws_opt num_args x1] vs (g:val_approx
  spt) =
         (let (ea1,g) = known c [x1] (REPLICATE num_args
           clos_known_Other ++ vs) g in
         let (body,a1) = HD ea1 in
           ([(closLang_Fn t loc_opt NONE num_args body,
              (match loc_opt with SOME loc -> clos_approx
                (clos_known_config_inline_max_body_size c) loc
                num_args x1 | NONE -> clos_known_Other))],g))`;
   `known c [(Letrec t loc_opt _25 fns x1:closLang_exp)] vs
  (g:val_approx spt) =
         (let clos = (match loc_opt with
                       NONE -> REPLICATE (LENGTH fns)
                         clos_known_Other | SOME loc ->
                         clos_gen_noinline loc 0 fns) in
         // The following ignores SetGlobal within fns, but it shouldn't
         // appear there, and missing it just means this opt will do less.
         let new_fns = MAP (\(num_args,x).
                        let new_vs = REPLICATE num_args
                          clos_known_Other ++ clos ++ vs in
                        let res = known c [x] new_vs g in
                          (num_args,FST (HD (FST res)))) fns in
         let (ea1,g) = known c [x1] (clos ++ vs) g in
         let (e1,a1) = HD ea1 in
           ([(Letrec t loc_opt NONE new_fns e1,a1)],g))`];;

let known_LENGTH = prove
 (`!limit' es vs g. LENGTH (FST (known limit' es vs g)) = LENGTH es`,
  CHEAT_TAC);;

let known_LENGTH_EQ_E = prove
 (`known limit es vs g0 = (alist,g) ==> LENGTH alist = LENGTH es`,
  CHEAT_TAC);;

let known_sing = prove
 (`!limit' e vs g. ?e' a g'. known limit' [e] vs g = ([(e',a)],g')`,
  CHEAT_TAC);;

let known_sing_EQ_E = prove
 (`!limit' e vs g0 all' g. known limit' [e] vs g0 = (all',g) ==> (?e'
  apx. all' = [(e',apx)])`,
  CHEAT_TAC);;

let clos_known_compile_def = define_cases
  [`clos_known_compile NONE exps = (NONE,exps)`;
   `clos_known_compile (SOME c) exps =
      (let exps = clos_fvs_compile exps in
      let (es,g) = known c exps [] LN in
      let es1 = clos_ticks_remove_ticks (MAP FST es) in
      let es2 = clos_letop_let_op es1 in
        (SOME (clos_known_config_val_approx_spt_fupd (K g)
          c),es2))`];;
hol4_overload "compile" "clos_known_compile";;

let clos_known_compile_inc_def = new_definition
  `clos_known_compile_inc c g (es,xs) =
     (let (eas,g') = known (reset_inline_factor c) es [] g in
       (g',MAP FST eas,xs))`;;
hol4_overload "compile_inc" "clos_known_compile_inc";;

let known_static_conf_def = new_definition
  `known_static_conf kc = (match kc with NONE -> NONE | SOME kc ->
  SOME (clos_known_config_val_approx_spt_fupd (K LN)
  (reset_inline_factor kc)))`;;

let known_compile_inc_def = define_cases
  [`known_compile_inc NONE spt (p:closLang_exp
  list#(num#num#closLang_exp) list) = (spt,p)`;
   `known_compile_inc (SOME c) spt (p:closLang_exp
  list#(num#num#closLang_exp) list) =
      (let (p:closLang_exp list#(num#num#closLang_exp) list) =
        clos_fvs_compile_inc p in
      let (spt,p) = clos_known_compile_inc c spt p in
      let (p:closLang_exp list#(num#num#closLang_exp) list) =
        clos_ticks_compile_inc p in
      let p = clos_letop_compile_inc p in
      (spt,p))`];;

let option_val_approx_spt_def = new_definition
  `option_val_approx_spt kc = (match kc with NONE -> LN | SOME kcfg
  -> clos_known_config_val_approx_spt kcfg)`;;

let option_upd_val_spt_def = define_cases
  [`option_upd_val_spt spt NONE = NONE`;
   `option_upd_val_spt spt (SOME kc) = SOME
  (clos_known_config_val_approx_spt_fupd (K spt) kc)`];;

(*

(* Trace starting points *)
val t0 = ``SourceLoc 0 0 0 0``;
val t1 = ``SourceLoc 1 1 1 1``;

(* The numerical constant 1 *)
val const1 = ``Op None (IntOp (Const 1)) []``;
val const2 = ``Op None (IntOp (Const 2)) []``;


(* fn f x => f x *)
val apply = ``Fn None (SOME 0) NONE 2 (App ^t0 NONE (Var None 0) [Var None 1])``;

(* fn x => x + 1 *)
val succ = ``Fn None (SOME 2) NONE 1 (Op None (IntOp Add) [Var None 0; ^const1])``;

(* -------------------------------*)

(* (fn f x => f x) (fn x => x + 1) 2 *)
val example_direct = ``App ^t1 NONE ^apply [^succ; ^const2]``;

val inline_direct = ``clos_known$compile T ^example_direct``;
EVAL inline_direct;

val exp = ``Let None [^const1; ^const2] (Op None (IntOp Add) [Var None 0; Var None 1])``

EVAL ``clos_letop$let_op [^exp]``;

(*-------------------------------*)

(*
let apply = fn f x => f x
    succ = fn x => x + 1
in
  apply succ 1
end
*)
val example_local = ``Let None [^apply; ^succ] (App ^t1 NONE (Var None 0) [Var None 1; ^const1])``;
val inlined_local = EVAL ``clos_known$compile T ^example_local``;

val inline_local = ``clos_known$compile T ^example_local``;
EVAL inline_local;

(*-------------------------------*)

(* fun apply <f,x> = f x *)
val sg_apply = ``Op None (GlobOp (SetGlobal 0)) [^apply]``;
val g_apply = ``Op None (GlobOp (Global 0)) []``;

(* fun succ <x> = x + 1 *)
val sg_succ = ``Op None (GlobOp (SetGlobal 1)) [^succ]``;
val g_succ = ``Op None (GlobOp (Global 1)) []``;

(*
let _ = SetGlobal 0 (fn f x => f x)
    _ = SetGlobal 1 (fn x => x + 1)
in
  (Global 0) (Global 1) 1
end
*)
val example_global = ``Let None [^sg_apply; ^sg_succ] (App ^t1 NONE ^g_apply [^g_succ; ^const1])``;

val inline_global = ``clos_known$compile T ^example_global``;

EVAL inline_global;

EVAL ``known (100,0) [^apply] [] LN``;
EVAL ``known (100,0) [^succ] [] LN``;

EVAL ``known (0,0) [^example_global] [] LN``;

EVAL ``
    let exp = ^example_local in
    let (_,g1) = known (0,0) [exp] [] LN in
    let (e1,g1') = known (0,0) [exp] [] g1 in
    let (e2,g2) = known (0,0) [FST (HD e1)] [] LN in
    (e1, e2, g1, g1')
``


    let (e2,_) = known (100,2) [FST (HD e1)] [] g2 in
      FST (HD e2)

*)

(* HOL4 clos_knownScript.sml:797-921: code that the source has in a
   comment *)

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["all";
   "pmatch"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
