(* ======================================================== *)
(*  bvi_tailrec: ported from HOL4's
    compiler/backend/bvi_tailrecScript.sml  *)
(* ======================================================== *)

(*
  A compiler phase that turns some non-tail-recursive functions into
  tail-recursive functions.
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi.ml";;
needs "lib/ternaryComparisons.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;

let dummy_def = cake_define
  `dummy = bvi_Var 1234567890`;;

let is_rec_def = cake_define
  `bvi_tailrec_is_rec name x2 =
        match x2 with
          (bvi_Call _1 d _2 NONE) -> d = SOME name
        | _3 -> F`;;

let is_const_def = cake_define
  `bvi_tailrec_is_const x1 =
        match x1 with
          (closLang_IntOp (closLang_Const i)) -> small_enough_int i
        | _4 -> F`;;

let assoc_op_INDUCT,assoc_op_RECURSION = define_datatype
  "assoc_op = bvi_tailrec_Plus | bvi_tailrec_Times | \
   bvi_tailrec_Append | bvi_tailrec_Noop";;

let v_ty_INDUCT,v_ty_RECURSION = define_datatype
  "v_ty = bvi_tailrec_Int | bvi_tailrec_List | bvi_tailrec_Any";;

let op_type_def = cake_define
  `op_type x1 =
      match x1 with
        bvi_tailrec_Append -> bvi_tailrec_List
      | bvi_tailrec_Noop -> bvi_tailrec_Any
      | _5 -> bvi_tailrec_Int`;;

let to_op_def = cake_define
  `to_op bvi_tailrec_Plus = closLang_IntOp closLang_Add /\
   to_op bvi_tailrec_Times = closLang_IntOp closLang_Mult /\
   to_op bvi_tailrec_Append = closLang_BlockOp closLang_ListAppend /\
   to_op bvi_tailrec_Noop = closLang_IntOp closLang_Mod`;;

let from_op_def = cake_define
  `from_op closLang_op =
     (if closLang_op = closLang_IntOp closLang_Add then
       bvi_tailrec_Plus else if closLang_op = closLang_IntOp
       closLang_Mult then bvi_tailrec_Times else if closLang_op =
       closLang_BlockOp closLang_ListAppend then bvi_tailrec_Append
       else bvi_tailrec_Noop)`;;

let op_eq_def = cake_define
  `op_eq x1 x2 =
        match (x1,x2) with
          (bvi_tailrec_Plus,(bvi_Op closLang_op xs)) -> closLang_op =
            closLang_IntOp closLang_Add
        | (bvi_tailrec_Times,(bvi_Op closLang_op xs)) -> closLang_op
          = closLang_IntOp closLang_Mult
        | (bvi_tailrec_Append,(bvi_Op closLang_op xs)) -> closLang_op
          = closLang_BlockOp closLang_ListAppend
        | (_6,_7) -> F`;;

let apply_op_def = cake_define
  `apply_op closLang_op e1 e2 = bvi_Op (to_op closLang_op) [e1; e2]`;;

let id_from_op_def = cake_define
  `id_from_op bvi_tailrec_Plus = bvi_Op (closLang_IntOp (closLang_Const
  0)) [] /\
   id_from_op bvi_tailrec_Times = bvi_Op (closLang_IntOp
     (closLang_Const 1)) [] /\
   id_from_op bvi_tailrec_Append = bvi_Op (closLang_BlockOp
     (closLang_Cons nil_tag)) [] /\
   id_from_op bvi_tailrec_Noop = dummy`;;

let index_of_def = cake_define
  `index_of x1 =
        match x1 with
          (bvi_Var i) -> SOME i
        | _8 -> NONE`;;

let args_from_def = cake_define
  `args_from x1 =
        match x1 with
          (bvi_Call t (SOME d) as hdl) -> SOME (t,d,as,hdl)
        | _9 -> NONE`;;

let get_bin_args_def = cake_define
  `get_bin_args closLang_op =
     (match closLang_op with bvi_Op _10 [e1; e2] -> SOME (e1,e2) |
       _11 -> NONE)`;;

let opbinargs_def = cake_define
  `opbinargs opr bvi_exp = (if ~op_eq opr bvi_exp then NONE else
  get_bin_args bvi_exp)`;;

let try_update_def = cake_define
  `(try_update vty NONE ts = ts) /\
   (try_update vty (SOME n) ts =
     (if n < LENGTH ts then
       if EL n ts = bvi_tailrec_Any then
         TAKE n ts ++ [vty] ++ DROP (n + 1) ts else ts else ts))`;;

(* --- Checking termination guarantees --- *)

let is_arith_def = cake_define
  `is_arith closLang_op =
     (match closLang_op with
       closLang_IntOp closLang_Add -> T | closLang_IntOp
         closLang_Sub -> T | closLang_IntOp closLang_Mult -> T | _12
         -> F)`;;

let is_rel_def = cake_define
  `is_rel closLang_op =
     (match closLang_op with
       closLang_IntOp (LESS) -> T | closLang_IntOp closLang_LessEq
         -> T | closLang_IntOp (GREATER) -> T | closLang_IntOp
         closLang_GreaterEq -> T | _13 -> F)`;;

(* HOL4 termination: \\ rw [] \\ imp_res_tac exp_size_get_bin_args \\
   fs[] *)
let term_ok_int_def = cake_define_wf
  `MEASURE (exp_size o SND)`
  `term_ok_int ts expr =
     (match expr with
       bvi_Var i -> (if i < LENGTH ts then EL i ts = bvi_tailrec_Int
         else F) | bvi_Op closLang_op xs ->
         (match get_bin_args expr with
           NONE -> xs = [] /\ bvi_tailrec_is_const closLang_op |
             SOME (x,y) -> is_arith closLang_op /\ term_ok_int ts x
             /\ term_ok_int ts y) | _14 -> F)`;;

(* HOL4 termination: \\ rw [] \\ imp_res_tac exp_size_get_bin_args \\
   fs [] *)
let term_ok_any_def = cake_define_wf
  `MEASURE (exp_size o SND o SND)`
  `term_ok_any ts list expr =
        match expr with
          (bvi_Var i) ->
       if ~list then i < LENGTH ts else if i < LENGTH ts then EL i ts
         = bvi_tailrec_List else F
        | (bvi_Op closLang_op xs) ->
       match get_bin_args (bvi_Op closLang_op xs) with
         NONE -> xs = [] /\ (if list then closLang_op =
           closLang_BlockOp (closLang_Cons 0) else bvi_tailrec_is_const
           closLang_op) | SOME (x,y) ->
           (if closLang_op = closLang_BlockOp closLang_ListAppend
             then term_ok_any ts T x /\ term_ok_any ts T y else if ~list
             /\ is_arith closLang_op then term_ok_int ts x /\
             term_ok_int ts y else if ~list /\ is_rel closLang_op then
             term_ok_int ts x /\ term_ok_int ts y else if closLang_op =
             closLang_BlockOp (closLang_Cons 0) then term_ok_any ts T x
             /\ term_ok_any ts F y else F)
        | expr -> F`;;

(* TODO the translator does not accept this with the induction theorem
   above (yet):

Theorem term_ok_any_PMATCH:
   term_ok_any ts list expr =
     pmatch expr of
       Var i => if ~list then i < LENGTH ts
                else if i < LENGTH ts then EL i ts = List
                else F
     | Op op xs =>
          (case get_bin_args (Op op xs) of
            NONE       => xs = [] /\ if list then op = Cons 0 else
              is_const op
          | SOME (x,y) =>
              if op = ListAppend then term_ok_any ts T x /\ term_ok_any
                ts T y
              else if ~list /\ is_arith op then term_ok_int ts x /\
                term_ok_int ts y
              else if ~list /\ is_rel op   then term_ok_int ts x /\
                term_ok_int ts y
              else if op = Cons 0 then term_ok_any ts T x /\ term_ok_any
                ts F y
              else F)
     | _ => F
Proof
  Cases_on `expr` \\ once_rewrite_tac [term_ok_any_def] \\ fs []
QED
*)

let term_ok_def = cake_define
  `term_ok ts ty expr =
     (match ty with
       bvi_tailrec_Any -> term_ok_any ts F expr | bvi_tailrec_Int
         -> term_ok_int ts expr | bvi_tailrec_List -> term_ok_any ts
         T expr)`;;

(* --- Simple tail checking before rewriting --- *)

(* Swap arguments when commutative *)
let try_swap_def = cake_define
  `try_swap loc opr exp =
        match opr with
          bvi_tailrec_Append -> bvi_exp
        | opr ->
       match opbinargs opr bvi_exp with
         NONE -> bvi_exp | SOME (l,r) ->
           (if bvi_tailrec_is_rec loc l then apply_op opr r l else
             bvi_exp)`;;

(* Check if ok to lift xs into accumulator *)
let check_op_def = cake_define
  `check_op ts opr loc bvi_exp =
     (match opbinargs opr (try_swap loc opr bvi_exp) with
       NONE -> NONE | SOME (xs,f) ->
         (if bvi_tailrec_is_rec loc f /\ term_ok ts (op_type opr) xs
           then
           SOME (apply_op opr xs f) else
           NONE))`;;

(* --- Type analysis --- *)

let decide_ty_def = cake_define
  `decide_ty x1 x2 =
        match (x1,x2) with
          (bvi_tailrec_Int,bvi_tailrec_Int) -> bvi_tailrec_Int
        | (bvi_tailrec_List,bvi_tailrec_List) -> bvi_tailrec_List
        | (_15,_16) -> bvi_tailrec_Any`;;

let LAST1_def = cake_define
  `LAST1 x1 =
      match x1 with
        [] -> NONE
      | [x] -> SOME x
      | (x :: xs) -> LAST1 xs`;;

let update_context_def = cake_define
  `update_context ty ts x1 x2 =
     try_update ty (index_of x2) (try_update ty (index_of x1) ts)`;;

let arg_ty_def = cake_define
  `arg_ty x1 =
      match x1 with
        (closLang_IntOp (closLang_Const i)) -> (if small_enough_int i
          then bvi_tailrec_Int else bvi_tailrec_Any)
      | (closLang_IntOp closLang_Add) -> bvi_tailrec_Int
      | (closLang_IntOp closLang_Sub) -> bvi_tailrec_Int
      | (closLang_IntOp closLang_Mult) -> bvi_tailrec_Int
      | (closLang_IntOp closLang_Div) -> bvi_tailrec_Int
      | (closLang_IntOp closLang_Mod) -> bvi_tailrec_Int
      | (closLang_IntOp closLang_LessEq) -> bvi_tailrec_Int
      | (closLang_IntOp (LESS)) -> bvi_tailrec_Int
      | (closLang_IntOp (GREATER)) -> bvi_tailrec_Int
      | (closLang_IntOp closLang_GreaterEq) -> bvi_tailrec_Int
      | (closLang_BlockOp closLang_ListAppend) -> bvi_tailrec_List
      | _17 -> bvi_tailrec_Any`;;

let op_ty_def = cake_define
  `op_ty x1 =
        match x1 with
          (closLang_IntOp closLang_Add) -> bvi_tailrec_Int
        | (closLang_IntOp closLang_Sub) -> bvi_tailrec_Int
        | (closLang_IntOp closLang_Mult) -> bvi_tailrec_Int
        | (closLang_IntOp closLang_Div) -> bvi_tailrec_Int
        | (closLang_IntOp closLang_Mod) -> bvi_tailrec_Int
        | (closLang_BlockOp closLang_ListAppend) -> bvi_tailrec_List
        | (closLang_BlockOp (closLang_Cons tag)) -> if tag = nil_tag
          \/ tag = cons_tag then bvi_tailrec_List else bvi_tailrec_Any
        | (closLang_IntOp (closLang_Const i)) -> if small_enough_int
          i then bvi_tailrec_Int else bvi_tailrec_Any
        | _18 -> bvi_tailrec_Any`;;

(* Gather information about expressions:

     - Build context by following order of evaluation during recursion
       and set variable to Int only if interpretation of the expression
         would
       result in Rerr (Rabort Rtype_error) otherwise.
     - Check if tail positions are arithmetic or variables typed as Int
       in
       context.
     - Check if tail positions carry suitable operation (Add/Mult) and
       track
       branch of origin for the operation in conditionals.
*)

let scan_expr_def = cake_define
  `(scan_expr ts loc [] = []) /\
   (scan_expr ts loc (x :: y :: xs) =
     (let (tx,ty,r,closLang_op) = HD (scan_expr ts loc [x]) in
       (tx,ty,r,closLang_op) :: scan_expr tx loc (y :: xs))) /\
   (scan_expr ts loc [bvi_Var n] =
     (let ty = if n < LENGTH ts then EL n ts else bvi_tailrec_Any in
       [(ts,ty,F,NONE)])) /\
   (scan_expr ts loc [bvi_If xi xt xe] =
     (let (ti,tyi,_19,oi) = HD (scan_expr ts loc [xi]) in
     let (tt,ty1,_20,ot) = HD (scan_expr ti loc [xt]) in
     let (te,ty2,_21,oe) = HD (scan_expr ti loc [xe]) in
     let closLang_op = match ot with NONE -> oe | _22 -> ot in
     let ty = match closLang_op with
                NONE -> decide_ty ty1 ty2 | SOME opr -> decide_ty ty1
                  (decide_ty ty2 (op_type opr)) in
       [(MAP2 decide_ty tt te,ty,IS_SOME oe,closLang_op)])) /\
   (scan_expr ts loc [bvi_Let xs x] =
     (let ys = scan_expr ts loc xs in
     let tt = MAP (FST o SND) ys in
     let tr = (match LAST1 ys with SOME c -> FST c | NONE -> ts) in
     let (tu,ty,_23,closLang_op) = HD (scan_expr (tt ++ tr) loc [x])
       in
       [(DROP (LENGTH ys) tu,ty,F,closLang_op)])) /\
   (scan_expr ts loc [bvi_Raise x] = [(ts,bvi_tailrec_Any,F,NONE)])
     /\
   (scan_expr ts loc [bvi_Tick x] = scan_expr ts loc [x]) /\
   (scan_expr ts loc [bvi_Force _24 n] =
     (let ty = if n < LENGTH ts then EL n ts else bvi_tailrec_Any in
       [(ts,ty,F,NONE)])) /\
   (scan_expr ts loc [bvi_Call t d xs h] =
     [(ts,bvi_tailrec_Any,F,NONE)]) /\
   (scan_expr ts loc [bvi_Return xs] = [(ts,bvi_tailrec_Any,F,NONE)])
     /\
   (scan_expr ts loc [bvi_LetCall rets t d xs y] =
     [(ts,bvi_tailrec_Any,F,NONE)]) /\
   (scan_expr ts loc [bvi_Op closLang_op xs] =
     (let opr = from_op closLang_op in
     let opt = op_type opr in
       match opr with
         bvi_tailrec_Noop ->
           (if arg_ty closLang_op = bvi_tailrec_Int then
             match get_bin_args (bvi_Op closLang_op xs) with
               NONE ->
                 (if bvi_tailrec_is_const closLang_op then
                   [(ts,bvi_tailrec_Int,F,NONE)] else
                   [(ts,bvi_tailrec_Any,F,NONE)]) | SOME (x,y) ->
                 (if ~bvi_tailrec_is_const closLang_op then
                   [(update_context bvi_tailrec_Int ts x
                     y,bvi_tailrec_Any,F,NONE)] else
                   [(ts,bvi_tailrec_Any,F,NONE)]) else if closLang_op
                     = closLang_BlockOp (closLang_Cons 0) /\ xs = []
                     then
             [(ts,bvi_tailrec_List,F,NONE)] else
             [(ts,bvi_tailrec_Any,F,NONE)]) | _25 ->
           (if IS_SOME (check_op ts opr loc (bvi_Op closLang_op xs))
             then
             [(ts,opt,F,SOME opr)] else if term_ok ts opt (bvi_Op
               closLang_op xs) then
             match get_bin_args (bvi_Op closLang_op xs) with
               NONE -> [(ts,bvi_tailrec_Any,F,NONE)] | SOME (x,y) ->
                 [(update_context opt ts x y,opt,F,NONE)] else
             [(ts,bvi_tailrec_Any,F,NONE)])))`;;

let scan_expr_sing_def = cake_define
  `(scan_expr_sing ts loc (bvi_Var n) =
     (let ty = if n < LENGTH ts then EL n ts else bvi_tailrec_Any in
       (ts,ty,F,NONE))) /\
   (scan_expr_sing ts loc (bvi_If xi xt xe) =
     (let (ti,tyi,_26,oi) = scan_expr_sing ts loc xi in
     let (tt,ty1,_27,ot) = scan_expr_sing ti loc xt in
     let (te,ty2,_28,oe) = scan_expr_sing ti loc xe in
     let closLang_op = match ot with NONE -> oe | _29 -> ot in
     let ty = match closLang_op with
                NONE -> decide_ty ty1 ty2 | SOME opr -> decide_ty ty1
                  (decide_ty ty2 (op_type opr)) in
       (MAP2 decide_ty tt te,ty,IS_SOME oe,closLang_op))) /\
   (scan_expr_sing ts loc (bvi_Let xs x) =
     (let ys = scan_expr_list ts loc xs in
     let tt = MAP (FST o SND) ys in
     let tr = (match LAST1 ys with SOME c -> FST c | NONE -> ts) in
     let (tu,ty,_30,closLang_op) = scan_expr_sing (tt ++ tr) loc x in
       (DROP (LENGTH ys) tu,ty,F,closLang_op))) /\
   (scan_expr_sing ts loc (bvi_Raise x) =
     (ts,bvi_tailrec_Any,F,NONE)) /\
   (scan_expr_sing ts loc (bvi_Tick x) = scan_expr_sing ts loc x) /\
   (scan_expr_sing ts loc (bvi_Force _31 n) =
     (let ty = if n < LENGTH ts then EL n ts else bvi_tailrec_Any in
       (ts,ty,F,NONE))) /\
   (scan_expr_sing ts loc (bvi_Call t d xs h) =
     (ts,bvi_tailrec_Any,F,NONE)) /\
   (scan_expr_sing ts loc (bvi_Return xs) =
     (ts,bvi_tailrec_Any,F,NONE)) /\
   (scan_expr_sing ts loc (bvi_LetCall rets t d xs y) =
     (ts,bvi_tailrec_Any,F,NONE)) /\
   (scan_expr_sing ts loc (bvi_Op closLang_op xs) =
     (let opr = from_op closLang_op in
     let opt = op_type opr in
       match opr with
         bvi_tailrec_Noop ->
           (if arg_ty closLang_op = bvi_tailrec_Int then
             match get_bin_args (bvi_Op closLang_op xs) with
               NONE ->
                 (if bvi_tailrec_is_const closLang_op then
                   (ts,bvi_tailrec_Int,F,NONE) else
                   (ts,bvi_tailrec_Any,F,NONE)) | SOME (x,y) ->
                 (if ~bvi_tailrec_is_const closLang_op then
                   (update_context bvi_tailrec_Int ts x
                     y,bvi_tailrec_Any,F,NONE) else
                   (ts,bvi_tailrec_Any,F,NONE)) else if closLang_op =
                     closLang_BlockOp (closLang_Cons 0) /\ xs = [] then
             (ts,bvi_tailrec_List,F,NONE) else
             (ts,bvi_tailrec_Any,F,NONE)) | _32 ->
           (if IS_SOME (check_op ts opr loc (bvi_Op closLang_op xs))
             then
             (ts,opt,F,SOME opr) else if term_ok ts opt (bvi_Op
               closLang_op xs) then
             match get_bin_args (bvi_Op closLang_op xs) with
               NONE -> (ts,bvi_tailrec_Any,F,NONE) | SOME (x,y) ->
                 (update_context opt ts x y,opt,F,NONE) else
             (ts,bvi_tailrec_Any,F,NONE)))) /\
   (scan_expr_list ts loc [] = []) /\
   (scan_expr_list ts loc (x :: xs) =
     (let (tx,ty,r,closLang_op) = scan_expr_sing ts loc x in
       (tx,ty,r,closLang_op) :: scan_expr_list tx loc xs))`;;

let push_call_def = cake_define
  `push_call n op acc exp x5 =
        match x5 with
          (SOME (ticks,dest,args,handler)) ->
       bvi_Call ticks (SOME n) (args ++ [apply_op closLang_op
         (bvi_Var acc) bvi_exp]) handler
        | _33 -> dummy`;;

let rewrite_def = cake_define
  `rewrite loc next opr acc ts exp =
        match exp with
          (bvi_Var n) -> (F,bvi_Var n)
        | (bvi_If x1 x2 x3) ->
       let t1 = FST (HD (scan_expr ts loc [x1])) in
       let (r2,y2) = rewrite loc next opr acc t1 x2 in
       let (r3,y3) = rewrite loc next opr acc t1 x3 in
       let z2 = if r2 then y2 else apply_op opr (bvi_Var acc) x2 in
       let z3 = if r3 then y3 else apply_op opr (bvi_Var acc) x3 in
         ((r2 \/ r3),bvi_If x1 z2 z3)
        | (bvi_Let xs x) ->
       let ys = scan_expr ts loc xs in
       let tt = MAP (FST o SND) ys in
       let tr = match LAST1 ys with NONE -> ts | SOME c -> FST c in
       let (r,y) = rewrite loc next opr (acc + LENGTH xs) (tt ++ tr)
         x in
         (r,bvi_Let xs y)
        | (bvi_Tick x) ->
       let (r,y) = rewrite loc next opr acc ts x in
         (r,bvi_Tick y)
        | (bvi_Force l v) -> (F,bvi_Force l v)
        | bvi_exp ->
       match check_op ts opr loc bvi_exp with
         NONE -> (F,apply_op opr (bvi_Var acc) bvi_exp) | SOME
           bvi_exp ->
           (match opbinargs opr bvi_exp with
             NONE -> (F,apply_op opr (bvi_Var acc) bvi_exp) | SOME
               (xs,f) -> (T,push_call next opr acc xs (args_from f)))`;;


(* --- Top-level expression check --- *)

let has_rec_def = cake_define
  `has_rec loc x2 =
        match x2 with
          [] -> F
        | (x :: y :: xs) ->
       if has_rec loc [x] then T else has_rec loc (y :: xs)
        | [bvi_If x1 x2 x3] ->
       if has_rec loc [x2] then T else has_rec loc [x3]
        | [bvi_Let xs x] -> has_rec loc [x]
        | [bvi_Tick x] -> has_rec loc [x]
        | [bvi_Op closLang_op xs] ->
       if EXISTS (bvi_tailrec_is_rec loc) xs then T else has_rec loc
         xs
        | [x] -> F`;;

let has_rec1_def = cake_define
  `has_rec1 loc x = has_rec loc [x]`;;

let has_rec_sing_def = cake_define
  `has_rec_sing loc x =
        match x with
          (bvi_If x1 x2 x3) ->
       if has_rec_sing loc x2 then T else has_rec_sing loc x3
        | (bvi_Let xs x) -> has_rec_sing loc x
        | (bvi_Tick x) -> has_rec_sing loc x
        | (bvi_Op closLang_op xs) ->
       if EXISTS (bvi_tailrec_is_rec loc) xs then T else has_rec_list
         loc xs
        | x -> F
        | [] -> F
        | (x :: xs) ->
       if has_rec_sing loc x then T else has_rec_list loc xs`;;

(* HOL4 ML code, not ported:
val test1_tm = ``Let [] (Call 0 (SOME 0) [] NONE)``
*)

(* HOL4 ML code, not ported:
val test2_tm = ``Op (IntOp Add) [Call 0 (SOME 0) [] NONE; Var 0]``
*)

let check_exp_def = cake_define
  `check_exp loc arity bvi_exp =
     (if ~has_rec1 loc bvi_exp then NONE else
       let context = REPLICATE arity bvi_tailrec_Any in
         match scan_expr context loc [bvi_exp] with
           [] -> NONE | (ts,ty,r,opr) :: _34 ->
             (match opr with
               NONE -> NONE | SOME closLang_op ->
                 (if ~(ty = op_type closLang_op) then NONE else
                   opr)))`;;

let let_wrap_def = cake_define
  `let_wrap arity id bvi_exp =
     bvi_Let ((GENLIST (\i. bvi_Var i) arity) ++ [id]) bvi_exp`;;

let mk_aux_call_def = cake_define
  `mk_aux_call loc arity id =
     bvi_Call 0 (SOME loc) (id :: GENLIST (\i. bvi_Var i) arity)
       NONE`;;

let compile_exp_def = cake_define
  `bvi_tailrec_compile_exp loc next arity bvi_exp =
     (match check_exp loc arity bvi_exp with
       NONE -> NONE | SOME closLang_op ->
       (let context = REPLICATE arity bvi_tailrec_Any in
       let (r,opt) = rewrite loc next closLang_op arity context
         bvi_exp in
       let aux = let_wrap arity (id_from_op closLang_op) opt in
         SOME (aux,opt)))`;;

let compile_each_def = cake_define
  `(bvi_tailrec_compile_each next [] = (next,[])) /\
   (bvi_tailrec_compile_each next ((loc,arity,bvi_exp) :: xs) =
     (match bvi_tailrec_compile_exp loc next arity bvi_exp with NONE
       ->
         (let (n,ys) = bvi_tailrec_compile_each next xs in
           (n,(loc,arity,bvi_exp) :: ys)) | SOME (exp_aux,exp_opt) ->
         (let (n,ys) = bvi_tailrec_compile_each (next +
           bvl_to_bvi_namespaces) xs in
         (n,(loc,arity,exp_aux) :: (next,arity + 1,exp_opt) ::
           ys))))`;;

let compile_prog_def = cake_define
  `bvi_tailrec_compile_prog do_it next xs =
     (if do_it then bvi_tailrec_compile_each next xs else
       (next,xs))`;;

(* --- Test rewriting --- *)

(* HOL4 ML code, not ported:
val fac_tm = ``
  Let [Op (IntOp LessEq) [Var 0; Op (IntOp (Const 1)) []]]
    (If (Var 0)
       (Op (IntOp (Const 1)) [])
       (Let [Op (IntOp Sub) [Op (IntOp (Const 1)) []; Var 1]]
         (Op (IntOp Mult) [Var 2; Call 0 (SOME 0) [Var 0] NONE])))``
*)

(* HOL4 ML code, not ported:
val opt_tm = ``
  Let [Op (IntOp LessEq) [Var 0; Op (IntOp (Const 1)) []]]
     (If (Var 0) (Op (IntOp Mult) [Var 2; Op (IntOp (Const 1)) []])
        (Let [Op (IntOp Sub) [Op (IntOp (Const 1)) []; Var 1]]
           (Call 0 (SOME 1) [Var 0; Op (IntOp Mult) [Var 3; Var 2]]
              NONE)))``
val aux_tm = ``Let [Var 0; Op (IntOp (Const 1)) []] ^opt_tm``
*)

(* HOL4 ML code, not ported:
val rev_tm = ``
  Let [Op (IntOp (Const 0)) []]
    (If (Op (BlockOp (TagLenEq 0 0)) [Var 1])
        (Op (BlockOp (Cons 0)) [])
        (Let [Op (MemOp El) [Op (IntOp (Const 0)) []; Var 1]]
          (Let [Op (MemOp El) [Op (IntOp (Const 1)) []; Var 2]]
            (Op (BlockOp ListAppend)
              [Op (BlockOp (Cons 0)) [Op (BlockOp (Cons 0)) []; Var 1];
               Call 0 (SOME 444) [Var 0] NONE]))))``
*)

(* HOL4 ML code, not ported:
val opt_tm = ``
  Let [Op (IntOp (Const 0)) []]
    (If (Op (BlockOp (TagLenEq 0 0)) [Var 1])
        (Op (BlockOp ListAppend) [Var 2; Op (BlockOp (Cons 0)) []])
        (Let [Op (MemOp El) [Op (IntOp (Const 0)) []; Var 1]]
          (Let [Op (MemOp El) [Op (IntOp (Const 1)) []; Var 2]]
            (Call 0 (SOME 445)
              [Var 0;
               Op (BlockOp ListAppend) [Var 4; Op (BlockOp (Cons 0)) [Op
                 (BlockOp (Cons 0)) []; Var 1]]]
              NONE))))``
*)

(* HOL4 ML code, not ported:
val aux_tm = ``Let [Var 0; Op (BlockOp (Cons 0)) []] ^opt_tm``
*)
