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

(* HOL4 clos_knownScript.sml:16: code that the source has in a
   comment *)

(* This definition is written to short-circuit,
   i.e. exit as soon as possible. *)
let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 clos_knownScript.sml:63-66: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let get_size_sc_aux_def = cake_define_list_try_tac (fun () ->
  `MEASURE (list_size closLang_exp_size o SND)`)
  CHEAT_TAC
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

let get_size_sc_def = cake_define
  `get_size_sc limit' e =
     (let n = get_size_sc_aux (limit' + 1) [e] in
       if n = 0 then NONE else SOME ((limit' + 1) - n))`;;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 clos_knownScript.sml:99-102: the tactic that proves the
   termination *)
let get_size_aux_def = cake_define_list_try (fun () ->
  `MEASURE (list_size closLang_exp_size)`)
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

let get_size_def = cake_define
  `clos_known_get_size e = get_size_aux [e]`;;
hol4_overload "get_size" "clos_known_get_size";;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let free_def = cake_define_list_cheat CHEAT_TAC
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

let closed_def = cake_define
  `clos_known_closed x = (\t. t = LN) (db_to_set (SND
  (clos_known_free [x])))`;;
hol4_overload "closed" "clos_known_closed";;

let contains_closures_def = cake_define_list
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
  "val_approx = clos_known_ClosNoInline (num) (num) | clos_known_Clos \
   (num) (num) (closLang_exp) (num) | clos_known_Tuple (num) \
   (val_approx list) | clos_known_Int (int) | clos_known_Other | \
   clos_known_Impossible";;
hol4_overload "ClosNoInline" "clos_known_ClosNoInline";;
hol4_overload "Clos" "clos_known_Clos";;
hol4_overload "Tuple" "clos_known_Tuple";;
hol4_overload "Int" "clos_known_Int";;
hol4_overload "Other" "clos_known_Other";;
hol4_overload "Impossible" "clos_known_Impossible";;
(* HOL4 clos_knownScript.sml:276: ML code, not ported *)

let merge_def = cake_define
  `clos_known_merge x y =
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
        | (_4,_5) -> clos_known_Other`;;
hol4_overload "merge" "clos_known_merge";;

(* Avoid MAP2 *)
let _ = size_thms "val_approx";;
(* HOL4 clos_knownScript.sml:313-321: the tactic that proves the
   termination *)
let merge_tup_def = cake_define_wf
  `MEASURE (val_approx_size o FST)`
  `merge_tup x1 =
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
        | (_6,_7) -> clos_known_Other`;;

(* HOL4 clos_knownScript.sml:323-342: code that the source has in a
   comment *)

let known_op_def = cake_define
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

let clos_approx_def = cake_define
  `clos_approx max_size loc num_args body =
     (match get_size_sc max_size body with NONE ->
       clos_known_ClosNoInline loc num_args | SOME body_size ->
       clos_known_Clos loc num_args body body_size)`;;

let clos_gen_noinline_def = cake_define_list
  [`clos_gen_noinline n i [] = []`;
   `clos_gen_noinline n i ((a,e) :: xs) =
        clos_known_ClosNoInline (n + 2 * i) a ::
          clos_gen_noinline n (i + 1) xs`];;

let globalOpt_INDUCT,globalOpt_RECURSION = define_datatype
  "globalOpt = gO_Int (int) | gO_NullTuple (num) | gO_None";;

let isGlobal_def = cake_define
  `isGlobal x1 =
        match x1 with
          closLang_GlobOp (closLang_Global _11) -> T
        | _12 -> F`;;

let gO_destApx_def = cake_define
  `gO_destApx x1 =
        match x1 with
          (Int i:val_approx) -> gO_Int i
        | (clos_known_Tuple tag args) -> (if NULL args then
          gO_NullTuple tag else gO_None)
        | _13 -> gO_None`;;

let mk_Ticks_def = cake_define_wf
  `MEASURE (FST o SND o SND)`
  `clos_known_mk_Ticks t tc n e =
     (if n = 0 then e else clos_known_mk_Ticks t (tc + 1) (n - 1)
       (closLang_Tick (mk_cons t tc) e))`;;
hol4_overload "mk_Ticks" "clos_known_mk_Ticks";;

let inliningDecision_INDUCT,inliningDecision_RECURSION = define_datatype
  "inliningDecision = inlD_Nothing | inlD_Annotate (num) | \
   inlD_LetInline (closLang_exp)";;

let clos_known_config_FIELDS = define_record "clos_known_config"
  ["inline_max_body_size","num";
   "inline_factor","num";
   "initial_inline_factor","num";
   "val_approx_spt","val_approx spt"];;

let default_inline_factor_def = cake_define
  `default_inline_factor = 8`;;
let default_max_body_size_def = cake_define
  `default_max_body_size max_app inline_factor = (max_app + 1) *
  inline_factor`;;

let mk_config_def = cake_define
  `mk_config max_body_size inline_factor = mk_clos_known_config
  max_body_size inline_factor inline_factor LN`;;

let default_config_def = cake_define
  `clos_known_default_config max_app = mk_config
  (default_max_body_size max_app default_inline_factor)
  default_inline_factor`;;
hol4_overload "default_config" "clos_known_default_config";;

let dec_inline_factor_def = cake_define
  `dec_inline_factor c = clos_known_config_inline_factor_fupd (K
  (clos_known_config_inline_factor c DIV 2)) c`;;

let reset_inline_factor_def = cake_define
  `reset_inline_factor c = clos_known_config_inline_factor_fupd (K
  (clos_known_config_initial_inline_factor c)) c`;;

let decide_inline_def = cake_define
  `decide_inline c fapx app_lopt app_arity =
     (match fapx with clos_known_ClosNoInline loc arity ->
           (if app_lopt = NONE /\ app_arity = arity then
             inlD_Annotate loc else inlD_Nothing) | clos_known_Clos loc
             arity body body_size ->
           (if app_lopt = NONE /\ app_arity = arity then
             (if body_size < clos_known_config_inline_factor c * (1 +
               app_arity) /\
                 ~contains_closures [body] /\
                 clos_known_closed (closLang_Fn (implode "") NONE
                   NONE app_arity body) then inlD_LetInline body else
                   inlD_Annotate loc) else inlD_Nothing) | _14 ->
                   inlD_Nothing)`;;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 clos_knownScript.sml:630-639: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let known_def = cake_define_list_try_tac (fun () ->
  `inv_image (MEASURE I LEX MEASURE I)
                              (\(c,xs,vs,g).
                              (clos_known_config_inline_factor
                              c,list_size closLang_exp_size xs))`)
  CHEAT_TAC
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
                 (let (eabody,_17) = known (dec_inline_factor c)
                   [body] (MAP SND ea2) g in
                 let (ebody,abody) = HD eabody in
                   if pure x then
                     ([(Let (mk_cons t 0) (MAP FST ea2)
                              (clos_known_mk_Ticks t 1 (LENGTH xs)
                                ebody),abody)],g) else
                     ([(Let (mk_cons t 0) (SNOC e1 (MAP FST ea2))
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
   `known c [(Letrec t loc_opt _19 fns x1:closLang_exp)] vs
  (g:val_approx spt) =
         (let clos = (match loc_opt with
                       NONE -> REPLICATE (LENGTH fns)
                         clos_known_Other | SOME loc ->
                         clos_gen_noinline loc 0 fns) in
         let new_fns = MAP (\(num_args,x).
                        let new_vs = REPLICATE num_args
                          clos_known_Other ++ clos ++ vs in
                        let res = known c [x] new_vs g in
                          (num_args,FST (HD (FST res)))) fns in
         let (ea1,g) = known c [x1] (clos ++ vs) g in
         let (e1,a1) = HD ea1 in
           ([(Letrec t loc_opt NONE new_fns e1,a1)],g))`];;

let compile_def = cake_define_list
  [`clos_known_compile NONE exps = (NONE,exps)`;
   `clos_known_compile (SOME c) exps =
      (let exps = clos_fvs_compile exps in
      let (es,g) = known c exps [] LN in
      let es1 = clos_ticks_remove_ticks (MAP FST es) in
      let es2 = clos_letop_let_op es1 in
        (SOME (clos_known_config_val_approx_spt_fupd (K g)
          c),es2))`];;
hol4_overload "compile" "clos_known_compile";;

let compile_inc_def = cake_define
  `clos_known_compile_inc c g (es,xs) =
     (let (eas,g') = known (reset_inline_factor c) es [] g in
       (g',MAP FST eas,xs))`;;
hol4_overload "compile_inc" "clos_known_compile_inc";;

let known_static_conf_def = cake_define
  `known_static_conf kc = (match kc with NONE -> NONE | SOME kc ->
  SOME (clos_known_config_val_approx_spt_fupd (K LN)
  (reset_inline_factor kc)))`;;

let known_compile_inc_def = cake_define_list
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

let option_val_approx_spt_def = cake_define
  `option_val_approx_spt kc = (match kc with NONE -> LN | SOME kcfg
  -> clos_known_config_val_approx_spt kcfg)`;;

let option_upd_val_spt_def = cake_define_list
  [`option_upd_val_spt spt NONE = NONE`;
   `option_upd_val_spt spt (SOME kc) = SOME
  (clos_known_config_val_approx_spt_fupd (K spt) kc)`];;

(* HOL4 clos_knownScript.sml:711-795: code that the source has in a
   comment *)

(* HOL4 clos_knownScript.sml:797-921: code that the source has in a
   comment *)
