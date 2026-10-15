(* ======================================================== *)
(*  clos_known: ported from HOL4's
    compiler/backend/clos_knownScript.sml  *)
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

(* val _ = set_grammar_ancestry ["closLang", "sptree", "misc",
   "backend_common"] *)

(* This definition is written to short-circuit,
   i.e. exit as soon as possible. *)
let _ = size_thms "exp";;
let _ = size_thms "list";;
(* HOL4 termination: \\ fs[list_size_pair_size_MAP_FST_SND] *)
let get_size_sc_aux_def = cake_define_wf
  `MEASURE (list_size exp_size o SND)`
  `(get_size_sc_aux n [] = n) /\
   (get_size_sc_aux n (x :: y :: xs) =
      (if n = 0 then n else
        let n = get_size_sc_aux n [x] in if n = 0 then n else
          get_size_sc_aux n (y :: xs))) /\
   (get_size_sc_aux n [Var t v] = n - 1) /\
   (get_size_sc_aux n [If t x1 x2 x3] =
      (let n = n - 1 in if n = 0 then 0 else
      let n = get_size_sc_aux n [x1] in if n = 0 then 0 else
      let n = get_size_sc_aux n [x2] in if n = 0 then 0 else
        get_size_sc_aux n [x3])) /\
   (get_size_sc_aux n [Let t xs x2] =
      (let n = n - 1 in if n = 0 then 0 else
      let n = get_size_sc_aux n xs in if n = 0 then 0 else
        get_size_sc_aux n [x2])) /\
   (get_size_sc_aux n [Raise t x1] =
      (let n = n - 1 in if n = 0 then 0 else
        get_size_sc_aux n [x1])) /\
   (get_size_sc_aux n [Handle t x1 x2] =
      (let n = n - 1 in if n = 0 then 0 else
      let n = get_size_sc_aux n [x1] in if n = 0 then 0 else
        get_size_sc_aux n [x2])) /\
   (get_size_sc_aux n [Op t op xs] =
      (let n = n - 1 in if n = 0 then 0 else
        get_size_sc_aux n xs)) /\
   (get_size_sc_aux n [Tick t x] = get_size_sc_aux n [x]) /\
   (get_size_sc_aux n [Call t ticks dest xs] =
      (let n = n - 1 in if n = 0 then 0 else
        get_size_sc_aux n xs)) /\
   (get_size_sc_aux n [Fn t loc_opt ws_opt num_args x1] =
      (let n = n - 1 in if n = 0 then 0 else
        get_size_sc_aux n [x1])) /\
   (get_size_sc_aux n [Letrec t loc_opt ws_opt fns x1] =
      (let n = n - 1 in if n = 0 then 0 else
      let n = get_size_sc_aux n (MAP SND fns) in if n = 0 then 0 else
        get_size_sc_aux n [x1])) /\
   (get_size_sc_aux n [App t loc_opt x1 xs] =
      (let n = n - 1 in if n = 0 then 0 else
      let n = get_size_sc_aux n [x1] in if n = 0 then 0 else
        get_size_sc_aux n xs))`;;

let get_size_sc_def = cake_define
  `get_size_sc limit e =
     (let n = get_size_sc_aux (limit + 1) [e] in
       if n = 0 then NONE else SOME ((limit + 1) - n))`;;

let _ = size_thms "exp";;
let _ = size_thms "list";;
(* HOL4 termination: \\ simp [list_size_pair_size_MAP_FST_SND] *)
let get_size_aux_def = cake_define_wf
  `MEASURE (list_size exp_size)`
  `(get_size_aux [] = 0) /\
   (get_size_aux (x :: y :: xs) =
      get_size_aux [x] + get_size_aux (y :: xs)) /\
   (get_size_aux [Var t v] = 1) /\
   (get_size_aux [If t x1 x2 x3] =
      1 + get_size_aux [x1] + get_size_aux [x2] + get_size_aux [x3])
        /\
   (get_size_aux [Let t xs x2] =
      1 + get_size_aux xs + get_size_aux [x2]) /\
   (get_size_aux [Raise t x1] =
      1 + get_size_aux [x1]) /\
   (get_size_aux [Handle t x1 x2] =
      1 + get_size_aux [x1] + get_size_aux [x2]) /\
   (get_size_aux [Op t op xs] =
      1 + get_size_aux xs) /\
   (get_size_aux [Tick t x] =
      get_size_aux [x]) /\
   (get_size_aux [Call t ticks dest xs] =
      1 + get_size_aux xs) /\
   (get_size_aux [Fn t loc_opt ws_opt num_args x1] =
      1 + get_size_aux [x1]) /\
   (get_size_aux [Letrec t loc_opt ws_opt fns x1] =
      1 + get_size_aux (MAP SND fns) + get_size_aux [x1]) /\
   (get_size_aux [App t loc_opt x1 xs] =
      1 + get_size_aux [x1] + get_size_aux xs)`;;

(* HOL4 ML code, not ported:
val get_size_aux_ind = theorem "get_size_aux_ind";
*)

let get_size_def = cake_define
  `clos_known_get_size e = get_size_aux [e]`;;
hol4_overload "get_size" "clos_known_get_size";;

let free_def = cake_define
  `(clos_known_free [] = ([],Empty)) /\
   (clos_known_free ((x:closLang_exp) :: y :: xs) =
      (let (c1,l1) = clos_known_free [x] in
      let (c2,l2) = clos_known_free (y :: xs) in
        (c1 ++ c2,mk_Union l1 l2))) /\
   (clos_known_free [Var t v] = ([Var t v],Var v)) /\
   (clos_known_free [If t x1 x2 x3] =
      (let (c1,l1) = clos_known_free [x1] in
      let (c2,l2) = clos_known_free [x2] in
      let (c3,l3) = clos_known_free [x3] in
        ([If t (HD c1) (HD c2) (HD c3)],mk_Union l1 (mk_Union l2
          l3)))) /\
   (clos_known_free [Let t xs x2] =
      (let (c1,l1) = clos_known_free xs in
      let (c2,l2) = clos_known_free [x2] in
        ([Let t c1 (HD c2)],mk_Union l1 (Shift (LENGTH xs) l2)))) /\
   (clos_known_free [Raise t x1] =
      (let (c1,l1) = clos_known_free [x1] in
        ([Raise t (HD c1)],l1))) /\
   (clos_known_free [Tick t x1] =
      (let (c1,l1) = clos_known_free [x1] in
        ([Tick t (HD c1)],l1))) /\
   (clos_known_free [Op t op xs] =
      (let (c1,l1) = clos_known_free xs in
        ([Op t op c1],l1))) /\
   (clos_known_free [App t loc_opt x1 xs2] =
      (let (c1,l1) = clos_known_free [x1] in
      let (c2,l2) = clos_known_free xs2 in
        ([App t loc_opt (HD c1) c2],mk_Union l1 l2))) /\
   (clos_known_free [Fn t loc _1 num_args x1] =
      (let (c1,l1) = clos_known_free [x1] in
      let l2 = Shift num_args l1 in
        ([Fn t loc (SOME (vars_to_list l2)) num_args (HD c1)],l2)))
          /\
   (clos_known_free [Letrec t loc _2 fns x1] =
      (let m = LENGTH fns in
      let res = MAP (\(n,x). let (c,l) = clos_known_free [x] in
                              ((n,HD c),Shift (n + m) l)) fns in
      let c1 = MAP FST res in
      let l1 = list_mk_Union (MAP SND res) in
      let (c2,l2) = clos_known_free [x1] in
        ([Letrec t loc (SOME (vars_to_list l1)) c1 (HD c2)],
         mk_Union l1 (Shift (LENGTH fns) l2)))) /\
   (clos_known_free [Handle t x1 x2] =
      (let (c1,l1) = clos_known_free [x1] in
      let (c2,l2) = clos_known_free [x2] in
        ([Handle t (HD c1) (HD c2)],mk_Union l1 (Shift 1 l2)))) /\
   (clos_known_free [Call t ticks dest xs] =
      (let (c1,l1) = clos_known_free xs in
        ([Call t ticks dest c1],l1)))`;;
hol4_overload "free" "clos_known_free";;

(*
val free_LENGTH_LEMMA = Q.prove(
  `!xs. (pmatch free xs of (ys,s1) => (LENGTH xs = LENGTH ys))`,
  recInduct free_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [free_def]
  \\ SRW_TAC [] [] \\ SRW_TAC [] []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REV_FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] [] \\ DECIDE_TAC)
  |> SIMP_RULE std_ss [] |> SPEC_ALL;

Theorem free_LENGTH:
   !xs ys l. (free xs = (ys,l)) ==> (LENGTH ys = LENGTH xs)
Proof
  REPEAT STRIP_TAC \\ MP_TAC free_LENGTH_LEMMA \\ fs []
QED

Theorem free_SING:
   (free [x] = (ys,l)) ==> ?y. ys = [y]
Proof
  REPEAT STRIP_TAC \\ IMP_RES_TAC free_LENGTH
  \\ Cases_on `ys` \\ fs [LENGTH_NIL]
QED

Theorem LENGTH_FST_free:
   LENGTH (FST (free fns)) = LENGTH fns
Proof
  Cases_on `free fns` \\ fs [] \\ IMP_RES_TAC free_LENGTH
QED

Theorem HD_FST_free:
   [HD (FST (free [x1]))] = FST (free [x1])
Proof
  Cases_on `free [x1]` \\ fs []
  \\ imp_res_tac free_SING \\ fs[]
QED

Theorem free_CONS:
   FST (free (x::xs)) = HD (FST (free [x])) :: FST (free xs)
Proof
  Cases_on `xs` \\ fs [free_def,SING_HD,LENGTH_FST_free,LET_DEF]
  \\ Cases_on `free [x]` \\ fs []
  \\ Cases_on `free (h::t)` \\ fs [SING_HD]
\\ IMP_RES_TAC free_SING \\ fs []
QED
*)

let closed_def = cake_define
  `clos_known_closed x = (\t. t = LN) (db_to_set (SND (free [x])))`;;
hol4_overload "closed" "clos_known_closed";;

let contains_closures_def = cake_define
  `(contains_closures [] = F) /\
   (contains_closures (x :: y :: xs) =
     (if contains_closures [x] then T else
       contains_closures (y :: xs))) /\
   (contains_closures [Var t v] = F) /\
   (contains_closures [If t x1 x2 x3] =
      (if contains_closures [x1] then T else
      if contains_closures [x2] then T else
        contains_closures [x3])) /\
   (contains_closures [Let t xs x2] =
      (if contains_closures xs then T else
        contains_closures [x2])) /\
   (contains_closures [Raise t x1] = contains_closures [x1]) /\
   (contains_closures [Handle t x1 x2] =
      (if contains_closures [x1] then T else
        contains_closures [x2])) /\
   (contains_closures [Op t op xs] = contains_closures xs) /\
   (contains_closures [Tick t x] = contains_closures [x]) /\
   (contains_closures [Call t ticks dest xs] = contains_closures xs)
     /\
   (contains_closures [Fn t loc_opt ws_opt num_args x1] = T) /\
   (contains_closures [Letrec t loc_opt ws_opt fns x1] = T) /\
   (contains_closures [App t loc_opt x1 xs] =
      (if contains_closures [x1] then T else
        contains_closures xs))`;;

(* -----------------------------------------------------------------

  This compiler transformation turns App NONEs into APP SOMEs.
  An App can carry a `SOME loc` if:
   1) the closure value that is used there was created with location
     loc;
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
(* HOL4 ML code, not ported:
val val_approx_size_def = definition "val_approx_size_def"
*)

let merge_def = cake_define
  `clos_known_merge x y =
        match (x,y) with
          (Impossible,y) -> y
        | (x,Impossible) -> x
        | ((Tuple tg1 xs),(Tuple tg2 ys)) ->
        if LENGTH xs = LENGTH ys /\ tg1 = tg2 then Tuple tg1 (MAP2
          clos_known_merge xs ys) else Other
        | ((ClosNoInline m1 n1),(ClosNoInline m2 n2)) ->
        if m1 = m2 /\ n1 = n2 then ClosNoInline m1 n1 else Other
        | ((Clos m1 n1 e1 s1),(Clos m2 n2 e2 s2)) ->
        if m1 = m2 /\ n1 = n2 /\ e1 = e2 /\ s1 = s2 then Clos m1 n1
          e1 s1 else Other
        | ((Int i),(Int j)) -> if i = j then Int i else Other
        | (_3,_4) -> Other`;;
hol4_overload "merge" "clos_known_merge";;

(* Avoid MAP2 *)
let _ = size_thms "val_approx";;
(* HOL4 termination: >> Induct_on `xs` >> rpt strip_tac>> imp_res_tac
   MEM_ZIP>>fs[]>> rw[val_approx_size_def] >> Cases_on`ys`>>fs[]>>
   first_x_assum (first_assum o mp_then (Pos (el 2)) mp_tac) >>
   simp[] >> rename[`_ < (tag:num) + (_ + _)`] >> disch_then
   (qspec_then `tag` mp_tac) >> simp[] *)
let merge_tup_def = cake_define_wf
  `MEASURE (val_approx_size o FST)`
  `merge_tup x1 =
        match x1 with
          (Impossible,y) -> y
        | (x,Impossible) -> x
        | (Tuple tg1 xs,Tuple tg2 ys) ->
        if LENGTH xs = LENGTH ys /\ tg1 = tg2 then
          Tuple tg1 (MAP merge_tup (ZIP (xs,ys))) else Other
        | (ClosNoInline m1 n1,ClosNoInline m2 n2) ->
        if m1 = m2 /\ n1 = n2 then ClosNoInline m1 n1 else Other
        | (Clos m1 n1 e1 s1,Clos m2 n2 e2 s2) ->
        if m1 = m2 /\ n1 = n2 /\ e1 = e2 /\ s1 = s2 then Clos m1 n1
          e1 s1 else Other
        | (Int i,Int j) -> if i = j then Int i else Other
        | (_5,_6) -> Other`;;

(* TODO: this function seems to throw the translator into an infinite
   loop
Theorem merge_tup_pmatch:
  !tup.
  merge_tup tup =
    pmatch tup of
      (Impossible,y) => y
    | (x,Impossible) => x
    | (Tuple tg1 xs,Tuple tg2 ys) =>
      if LENGTH xs = LENGTH ys ∧ tg1 = tg2 then Tuple tg1 (MAP merge_tup
        (ZIP(xs,ys)))
      else Other
    | (Clos m1 n1,Clos m2 n2) => if m1 = m2 ∧ n1 = n2 then Clos m1 n1
                                 else Other
    | (Int i,Int j) => if i = j then Int i else Other
    | _ => Other
Proof
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >>
    every_case_tac)
  >> fs[merge_tup_def] >> metis_tac []
QED
 *)

let known_op_def = cake_define
  `known_op op as g =
        match op with
          (GlobOp (Global n)) ->
      if NULL as then
        match lookup n g with NONE -> (Other,g) | SOME x -> (x,g)
          else (Other,g)
        | (GlobOp (SetGlobal n)) ->
        match as with [] -> (Other,g) | (a :: xs) ->
          (match lookup n g with NONE -> (Other,insert n a g) | SOME
            other -> (Other,insert n (merge other a) g))
        | (BlockOp (Cons tg)) -> (Tuple tg as,g)
        | (IntOp (Const i)) -> (Int i,g)
        | (MemOp El) ->
        match as with [Tuple _7 xs; Int i] ->
            (if 0 <= i /\ i < &LENGTH xs then (EL (num_of_int i)
              xs,g) else (Other,g)) | Impossible :: xs -> (Impossible,g)
              | _8 :: Impossible :: xs -> (Impossible,g) | _9 ->
              (Other,g)
        | op -> (Other,g)`;;

let clos_approx_def = cake_define
  `clos_approx max_size loc num_args body =
     (match get_size_sc max_size body with NONE -> ClosNoInline
       loc num_args | SOME body_size -> Clos loc num_args body
       body_size)`;;

let clos_gen_noinline_def = cake_define
  `(clos_gen_noinline n i [] = []) /\
   (clos_gen_noinline n i ((a,e) :: xs) =
     ClosNoInline (n + 2 * i) a :: clos_gen_noinline n (i + 1) xs)`;;

let globalOpt_INDUCT,globalOpt_RECURSION = define_datatype
  "globalOpt = gO_Int (int) | gO_NullTuple (num) | gO_None";;

let isGlobal_def = cake_define
  `isGlobal x1 =
        match x1 with
          (GlobOp (Global _10)) -> T
        | _11 -> F`;;

let gO_destApx_def = cake_define
  `gO_destApx x1 =
        match x1 with
          (Int i) -> gO_Int i
        | (Tuple tag args) -> if NULL args then gO_NullTuple tag else
          gO_None
        | _12 -> gO_None`;;

(* TERMINATION: wf_rel_tac `measure (FST o SND o SND)` *)
let mk_Ticks_def = cake_define
  `mk_Ticks t tc n e =
     (if n = 0 then e else mk_Ticks t (tc + 1) (n - 1) (Tick (§ t
       tc) e))`;;

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
     (match fapx with ClosNoInline loc arity ->
           (if app_lopt = NONE /\ app_arity = arity then
             inlD_Annotate loc else inlD_Nothing) | Clos loc arity body
             body_size ->
           (if app_lopt = NONE /\ app_arity = arity then
             (if body_size < clos_known_config_inline_factor c * (1 +
               app_arity) /\
                 ~contains_closures [body] /\
                 closed (Fn (implode "") NONE NONE app_arity body)
                   then inlD_LetInline body else inlD_Annotate loc)
                   else inlD_Nothing) | _13 -> inlD_Nothing)`;;

(* TERMINATION: wf_rel_tac `inv_image (measure I LEX measure I)
                        (\(c, xs, vs, g). (c.inline_factor, list_size
                          exp_size xs))`
  \\ simp [dec_inline_factor_def] \\ rpt strip_tac
  \\ imp_res_tac decide_inline_LetInline
  \\ fs []
  \\ drule MEM_list_size
  \\ disch_then (qspec_then `pair_size (λx. x) exp_size` mp_tac)
  \\ simp[list_size_pair_size_MAP_FST_SND] *)
let known_def = cake_define
  `(known c [] vs (g:val_approx spt) = ([],g)) /\
   (known c ((x:closLang_exp) :: y :: xs) vs g =
      (let (eas1,g) = known c [x] vs g in
      let (eas2,g) = known c (y :: xs) vs g in
        (eas1 ++ eas2,g))) /\
   (known c [Var t v] vs g =
      ([(Var t v,any_el v vs Other)],g)) /\
   (known c [If t x1 x2 x3] vs g =
      (let (ea1,g) = known c [x1] vs g in
      let (ea2,g) = known c [x2] vs g in
      let (ea3,g) = known c [x3] vs g in
      let (e1,a1) = HD ea1 in
      let (e2,a2) = HD ea2 in
      let (e3,a3) = HD ea3 in
        ([(If t e1 e2 e3),merge a2 a3],g))) /\
   (known c [Let t xs x2] vs g =
      (let (ea1,g) = known c xs vs g in
      let (ea2,g) = known c [x2] (MAP SND ea1 ++ vs) g in
      let (e2,a2) = HD ea2 in
        ([(Let t (MAP FST ea1) e2,a2)],g))) /\
   (known c [Raise t x1] vs g =
      (let (ea1,g) = known c [x1] vs g in
      let (e1,a1) = HD ea1 in
        ([(Raise t e1,Impossible)],g))) /\
   (known c [Tick t x1] vs g =
      (let (ea1,g) = known c [x1] vs g in
      let (e1,a1) = HD ea1 in
        ([(Tick t e1,a1)],g))) /\
   (known c [Handle t x1 x2] vs g =
      (let (ea1,g) = known c [x1] vs g in
      let (ea2,g) = known c [x2] (Other :: vs) g in
      let (e1,a1) = HD ea1 in
      let (e2,a2) = HD ea2 in
        ([(Handle t e1 e2,merge a1 a2)],g))) /\
   (known c [Call t ticks dest xs] vs g =
      (let (ea1,g) = known c xs vs g in
        ([(Call t ticks dest (MAP FST ea1),Other)],g))) /\
   (known c [Op t op xs] vs g =
      (let (ea1,g) = known c xs vs g in
      let (a,g) = known_op op (REVERSE (MAP SND ea1)) g in
      let e =
          (if isGlobal op then
            match gO_destApx a with gO_None -> SmartOp t op | gO_Int
              i -> Op t (IntOp (Const i)) | gO_NullTuple tag -> Op t
              (BlockOp (Cons tag)) else SmartOp t op) (MAP FST ea1) in
        ([(e,a)],g))) /\
   (known c [App t loc_opt x xs] vs g =
      (let (ea2,g) = known c xs vs g in
      let (ea1,g) = known c [x] vs g in
      let (e1,a1) = HD ea1 in
        match decide_inline c a1 loc_opt (LENGTH xs) with
          inlD_Nothing -> ([(App t loc_opt e1 (MAP FST ea2),Other)],g) |
          inlD_Annotate new_loc -> ([(App t (SOME new_loc) e1 (MAP FST
          ea2),Other)],g) | inlD_LetInline body ->
              (let (eabody,_14) = known (dec_inline_factor c) [body]
                (MAP SND ea2) g in
              let (ebody,abody) = HD eabody in
                if pure x then
                  ([(Let (§ t 0) (MAP FST ea2)
                              (mk_Ticks t 1 (LENGTH xs)
                                ebody),abody)],g) else
                  ([(Let (§ t 0) (SNOC e1 (MAP FST ea2))
                              (mk_Ticks t 1 (LENGTH xs)
                                ebody),abody)],g)))) /\
   (known c [Fn t loc_opt ws_opt num_args x1] vs g =
      (let (ea1,g) = known c [x1] (REPLICATE num_args Other ++ vs) g
        in
      let (body,a1) = HD ea1 in
        ([(Fn t loc_opt NONE num_args body,
           (match loc_opt with SOME loc -> clos_approx
             (clos_known_config_inline_max_body_size c) loc num_args x1
             | NONE -> Other))],g))) /\
   (known c [Letrec t loc_opt _15 fns x1] vs g =
      (let clos = match loc_opt with
                    NONE -> REPLICATE (LENGTH fns) Other | SOME loc
                      -> clos_gen_noinline loc 0 fns in
      let new_fns = MAP (\(num_args,x).
                     let new_vs = REPLICATE num_args Other ++ clos ++
                       vs in
                     let res = known c [x] new_vs g in
                       (num_args,FST (HD (FST res)))) fns in
      let (ea1,g) = known c [x1] (clos ++ vs) g in
      let (e1,a1) = HD ea1 in
        ([(Letrec t loc_opt NONE new_fns e1,a1)],g)))`;;

let compile_def = cake_define
  `clos_known_compile NONE exps = (NONE,exps) /\
   clos_known_compile (SOME c) exps =
     (let exps = clos_fvs_compile exps in
     let (es,g) = known c exps [] LN in
     let es1 = remove_ticks (MAP FST es) in
     let es2 = let_op es1 in
       (SOME (clos_known_config_val_approx_spt_fupd (K g) c),es2))`;;
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

let known_compile_inc_def = cake_define
  `known_compile_inc NONE spt p = (spt,p) /\
   known_compile_inc (SOME c) spt p =
     (let (p:closLang_exp list#(num#num#closLang_exp) list) =
       clos_fvs_compile_inc p in
     let (spt,p) = clos_known_compile_inc c spt p in
     let (p:closLang_exp list#(num#num#closLang_exp) list) =
       clos_ticks_compile_inc p in
     let p = clos_letop_compile_inc p in
     (spt,p))`;;

let option_val_approx_spt_def = cake_define
  `option_val_approx_spt kc = (match kc with NONE -> LN | SOME kcfg
  -> clos_known_config_val_approx_spt kcfg)`;;

let option_upd_val_spt_def = cake_define
  `option_upd_val_spt spt NONE = NONE /\
   option_upd_val_spt spt (SOME kc) = SOME
     (clos_known_config_val_approx_spt_fupd (K spt) kc)`;;

(*

(* Trace starting points *)
val t0 = ``SourceLoc 0 0 0 0``;
val t1 = ``SourceLoc 1 1 1 1``;

(* The numerical constant 1 *)
val const1 = ``Op None (IntOp (Const 1)) []``;
val const2 = ``Op None (IntOp (Const 2)) []``;


(* fn f x => f x *)
val apply = ``Fn None (SOME 0) NONE 2 (App ^t0 NONE (Var None 0) [Var
  None 1])``;

(* fn x => x + 1 *)
val succ = ``Fn None (SOME 2) NONE 1 (Op None (IntOp Add) [Var None 0;
  ^const1])``;

(* -------------------------------*)

(* (fn f x => f x) (fn x => x + 1) 2 *)
val example_direct = ``App ^t1 NONE ^apply [^succ; ^const2]``;

val inline_direct = ``clos_known$compile T ^example_direct``;
EVAL inline_direct;

val exp = ``Let None [^const1; ^const2] (Op None (IntOp Add) [Var None
  0; Var None 1])``

EVAL ``clos_letop$let_op [^exp]``;

(*-------------------------------*)

(*
let apply = fn f x => f x
    succ = fn x => x + 1
in
  apply succ 1
end
*)
val example_local = ``Let None [^apply; ^succ] (App ^t1 NONE (Var None
  0) [Var None 1; ^const1])``;
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
val example_global = ``Let None [^sg_apply; ^sg_succ] (App ^t1 NONE
  ^g_apply [^g_succ; ^const1])``;

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

(*

  TEST 0.1

  let
    val f = fn k => 1
  in f 6 end

  val t = ``SourceLoc 0 0 0 0``
  val f = ``Fn None (SOME 900) NONE 1 (Op None (IntOp (Const 1)) [])``
  val exp = ``Let None [^f] (App ^t NONE (Var None 0) [Op None (IntOp
    (Const 6)) []])``

  val ev = EVAL ``compile T ^exp``

  TEST 0.2

  let
    val app = fn f x => f x
    val f = fn x = x + 1
  in app f 10 end

  val t1 = ``SourceLoc 1 1 1 1``
  val t2 = ``SourceLoc 2 2 2 2``
  val app = ``Fn None (SOME 100) NONE 2 (App ^t1 NONE (Var None 0) [Var
    None 1])``
  val f = ``Fn None (SOME 200) NONE 1 (Op None (IntOp Add) [Var None 0;
    Op None (IntOp (Const 1)) []])``
  val exp = ``Let None [^app] (Let None [^f] (App ^t2 NONE (Var None 1)
    [Var None 0; Op None (IntOp (Const 10)) []]))``

  val ev = EVAL ``compile T ^exp``


  TEST 1

  let fun f x = f x in f end

  val f = ``Letrec None (SOME 200) NONE [(1,App None NONE (Var None 1)
    [Var None 0])] (Var None 0)``
  val ev = EVAL ``compile T ^f``


  TEST 2

  let
    val f = fn k => (get_global 60) (k + 1)
    val g = set_global 60 f
  in f 4 end

  val t1 = ``SourceLoc 1 1 1 1``
  val t2 = ``SourceLoc 2 2 2 2``
  val f = ``Fn None (SOME 900) NONE 1 (App ^t1 NONE (Op None (GlobOp
    (Global 60)) []) [Op None (IntOp Add) [Var None 0; Op None (IntOp
    (Const 1)) []]])``
  val g = ``closLang$Op None (GlobOp (SetGlobal 60)) [Var None 0]``
  val exp = ``Let None [^f] (Let None [^g] (App ^t2 NONE (Var None 1)
    [Op None (IntOp (Const 4)) []]))``

  val kn = EVAL ``(I ## sptree$toList) (known (100,2) [^exp] [] LN)``
  val ev = EVAL ``compile T ^exp``

  TEST 2A

  let
    val f = fn k => k + 1
    val g = set_global 60 f
  in
    get_global 60 3
  end

  val t1 = ``SourceLoc 1 1 1 1``
  val f = ``Fn None (SOME 900) NONE 1 (Op None (IntOp Add) [Var None 0;
    Op None (IntOp (Const 1)) []])``
  val g = ``closLang$Op None (GlobOp (SetGlobal 60)) [Var None 0]``
  val exp = ``Let None [^f] (Let None [^g]
                (App ^t1 NONE (Op None (GlobOp (Global 60)) []) [Op None
                  (IntOp (Const 3)) []]))``

  val ev = EVAL ``compile T ^exp``


  TEST 2B (* works nicely *)

  let
    val f = fn k => k + 1
    val g = set_global 60 f
    val h = set_global 62 (get_global 60)
  in
    h
  end

  val h = ``closLang$Op None (GlobOp (SetGlobal 62)) [Op None (GlobOp
    (Global 60)) []]``
  val exp = ``Let None [^f] (Let None [^g] (Let None [^h] (Var None
    0)))``

  val ev1 = EVAL ``known (0, 0) [^exp] [] LN``

  TEST 2C
    (* is ghastly; the g-map will never pick up a good value for global
       62 *)

  let
    val f = fn k => k + 1
    val h = fn k => set_global 62 (get_global 60)
    val g = set_global 60 f
  in
    h 1
  end

  val h = ``Fn None (SOME 800) NONE 1
               (closLang$Op None (GlobOp (SetGlobal 62)) [Op None
                 (GlobOp (Global 60)) []])``
  val exp = ``Let None [^f] (Let None [^h]
                (Let None [^g] (App None NONE (Var None 1) [Op None
                  (IntOp (Const 1)) []])))``

  val ev1 = EVAL ``known (0, 0) [^exp] [] LN``
  val ev2 = EVAL ``known (0, 0) [^exp] [] ^(#2 (dest_pair (rhs (concl
    ev1))))``


  TEST 3

  let val xy =
        let val f = fn k => k + 1
            val g = fn k => k - 1
            in (f,g) end
  in #1 xy 4 end


  val t = ``SourceLoc 0 0 0 0``
  val f = ``Fn None (SOME 800) NONE 1 (Op None (IntOp Add) [Var None 0;
    Op None (IntOp (Const 1)) []])``
  val g = ``Fn None (SOME 900) NONE 1 (Op None (IntOp Sub) [Var None 0;
    Op None (IntOp (Const 1)) []])``
  val xy = ``Let None [^f;^g] (Op None (BlockOp (Cons 0)) [Var None 0;
    Var None 1])``
  val app = ``Let None [^xy] (App ^t NONE (Op None (MemOp El) [Op None
    (IntOp (Const 0)) []; Var None 0]) [Op None (IntOp (Const 4)) []])``

  val ev = EVAL ``compile T ^app``

*)
