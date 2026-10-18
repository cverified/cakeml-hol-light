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
needs "compiler/backend/closLang.ml";;
needs "lib/comparison.ml";;
needs "semantics/ast.ml";;

let dummy_def = cake_define
  `dummy = bvi_Var 1234567890`;;

let is_rec_def = cake_define
  `bvi_tailrec_is_rec name x2 =
        match x2 with
          bvi_Call _1 d _2 NONE -> d = SOME name
        | _3 -> F`;;
hol4_overload "is_rec" "bvi_tailrec_is_rec";;

let is_const_def = cake_define
  `bvi_tailrec_is_const x1 =
        match x1 with
          closLang_IntOp (closLang_Const i) -> small_enough_int i
        | _4 -> F`;;
hol4_overload "is_const" "bvi_tailrec_is_const";;

let assoc_op_INDUCT,assoc_op_RECURSION = define_datatype
  "assoc_op = bvi_tailrec_Plus | bvi_tailrec_Times | \
   bvi_tailrec_Append | bvi_tailrec_Noop";;
hol4_overload "Plus" "bvi_tailrec_Plus";;
hol4_overload "Times" "bvi_tailrec_Times";;
hol4_overload "Append" "bvi_tailrec_Append";;
hol4_overload "Noop" "bvi_tailrec_Noop";;

let v_ty_INDUCT,v_ty_RECURSION = define_datatype
  "v_ty = bvi_tailrec_Int | bvi_tailrec_List | bvi_tailrec_Any";;
hol4_overload "Int" "bvi_tailrec_Int";;
hol4_overload "List" "bvi_tailrec_List";;
hol4_overload "Any" "bvi_tailrec_Any";;

let op_type_def = cake_define
  `op_type x1 =
      match x1 with
        (Append:assoc_op) -> List
      | bvi_tailrec_Noop -> bvi_tailrec_Any
      | _5 -> Int`;;

let to_op_def = cake_define_list
  [`to_op bvi_tailrec_Plus = closLang_IntOp closLang_Add`;
   `to_op bvi_tailrec_Times = closLang_IntOp closLang_Mult`;
   `to_op (Append:assoc_op) = closLang_BlockOp ListAppend`;
   `to_op bvi_tailrec_Noop = closLang_IntOp closLang_Mod`];;

let from_op_def = cake_define
  `from_op op =
     (if op = closLang_IntOp closLang_Add then bvi_tailrec_Plus
       else if op = closLang_IntOp closLang_Mult then
       bvi_tailrec_Times else if op = closLang_BlockOp ListAppend
       then Append else bvi_tailrec_Noop)`;;

let op_eq_def = cake_define
  `op_eq x1 x2 =
        match (x1,x2) with
          (bvi_tailrec_Plus,(Op op xs:bvi_exp)) -> op =
            closLang_IntOp closLang_Add
        | (bvi_tailrec_Times,(Op op xs)) -> op = closLang_IntOp
          closLang_Mult
        | (Append,(Op op xs)) -> op = closLang_BlockOp ListAppend
        | (_6,_7) -> F`;;

let apply_op_def = cake_define
  `apply_op op e1 e2 = Op (to_op op) [e1; e2]`;;

let id_from_op_def = cake_define_list
  [`id_from_op bvi_tailrec_Plus = bvi_Op (closLang_IntOp
  (closLang_Const (&0))) []`;
   `id_from_op bvi_tailrec_Times = bvi_Op (closLang_IntOp
  (closLang_Const (&1))) []`;
   `id_from_op (Append:assoc_op) = bvi_Op (closLang_BlockOp
  (closLang_Cons nil_tag)) []`;
   `id_from_op bvi_tailrec_Noop = dummy`];;

let index_of_def = cake_define
  `index_of x1 =
        match x1 with
          bvi_Var i -> SOME i
        | _8 -> NONE`;;

let args_from_def = cake_define
  `args_from x1 =
        match x1 with
          bvi_Call t (SOME d) as hdl -> SOME (t,d,as,hdl)
        | _9 -> NONE`;;

let get_bin_args_def = cake_define
  `get_bin_args op =
     (match op with bvi_Op _10 [e1; e2] -> SOME (e1,e2) | _11 ->
       NONE)`;;

let opbinargs_def = cake_define
  `opbinargs opr exp = (if ~op_eq opr exp then NONE else get_bin_args
  exp)`;;

let try_update_def = cake_define_list
  [`try_update vty NONE ts = ts`;
   `try_update vty (SOME n) ts =
        (if n < LENGTH ts then
          if EL n ts = bvi_tailrec_Any then
            TAKE n ts ++ [vty] ++ DROP (n + 1) ts else ts else
              ts)`];;

(* --- Checking termination guarantees --- *)

let is_arith_def = cake_define
  `is_arith op =
     (match op with
       closLang_IntOp closLang_Add -> T | closLang_IntOp
         closLang_Sub -> T | closLang_IntOp closLang_Mult -> T | _12
         -> F)`;;

let is_rel_def = cake_define
  `is_rel op =
     (match op with
       closLang_IntOp closLang_Less -> T | closLang_IntOp
         closLang_LessEq -> T | closLang_IntOp Greater -> T |
         closLang_IntOp closLang_GreaterEq -> T | _13 -> F)`;;

let _ = size_thms "bvi_exp";;

let exp_size_get_bin_args = prove
 (`!x x1 x2. get_bin_args x = SOME (x1,x2)
             ==> bvi_exp_size x1 + bvi_exp_size x2 < bvi_exp_size x`,
  GEN_TAC THEN
  STRUCT_CASES_TAC
    (ISPEC `x:bvi_exp` (CONJUNCT1 (cases "bvi_exp"))) THEN
  REWRITE_TAC[get_bin_args_def; distinctness "option"] THEN
  STRUCT_CASES_TAC (ISPEC `a1:bvi_exp list` list_CASES) THEN
  REWRITE_TAC[distinctness "option"] THEN
  STRUCT_CASES_TAC (ISPEC `t:bvi_exp list` list_CASES) THEN
  REWRITE_TAC[distinctness "option"] THEN
  STRUCT_CASES_TAC (ISPEC `t':bvi_exp list` list_CASES) THEN
  REWRITE_TAC[distinctness "option"; injectivity "option";
              PAIR_EQ] THEN
  REWRITE_TAC(all_size_thms()) THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

cake_term_facts := exp_size_get_bin_args :: (!cake_term_facts);;

let _ = size_thms "bvi_exp";;
(* HOL4 bvi_tailrecScript.sml:280-284: the tactic that proves the
   termination *)
let term_ok_int_def = cake_define_wf
  `MEASURE (bvi_exp_size o SND)`
  `term_ok_int ts expr =
     (match expr with
       Var i -> (if i < LENGTH ts then EL i ts = Int else F) | Op op
         xs ->
         (match get_bin_args expr with
           NONE -> xs = [] /\ bvi_tailrec_is_const op | SOME (x,y)
             -> is_arith op /\ term_ok_int ts x /\ term_ok_int ts y)
             | _14 -> F)`;;

let _ = size_thms "bvi_exp";;
(* HOL4 bvi_tailrecScript.sml:303-307: the tactic that proves the
   termination *)
let term_ok_any_def = cake_define_wf
  `MEASURE (bvi_exp_size o SND o SND)`
  `term_ok_any ts list' expr =
        match expr with
          (Var i:bvi_exp) ->
       (if ~list' then i < LENGTH ts else if i < LENGTH ts then EL i
         ts = List else F)
        | (Op op xs) ->
       (match get_bin_args (Op op xs) with
         NONE -> xs = [] /\ (if list' then op = closLang_BlockOp
           (closLang_Cons 0) else bvi_tailrec_is_const op) | SOME (x,y)
           ->
           (if op = closLang_BlockOp ListAppend then term_ok_any ts T
             x /\ term_ok_any ts T y else if ~list' /\ is_arith op then
             term_ok_int ts x /\ term_ok_int ts y else if ~list' /\
             is_rel op then term_ok_int ts x /\ term_ok_int ts y else if
             op = closLang_BlockOp (closLang_Cons 0) then term_ok_any ts
             T x /\ term_ok_any ts F y else F))
        | expr -> F`;;

(* HOL4 bvi_tailrecScript.sml:324-346: code that the source has in a
   comment *)

let term_ok_def = cake_define
  `term_ok ts ty expr =
     (match ty with
       bvi_tailrec_Any -> term_ok_any ts F expr | Int ->
         term_ok_int ts expr | List -> term_ok_any ts T expr)`;;

(* --- Simple tail checking before rewriting --- *)

(* Swap arguments when commutative *)
let try_swap_def = cake_define
  `try_swap loc opr exp =
        match opr with
          (Append:assoc_op) -> exp
        | opr ->
       (match opbinargs opr exp with
         NONE -> exp | SOME (l,r) ->
           (if bvi_tailrec_is_rec loc l then apply_op opr r l else
             exp))`;;

(* Check if ok to lift xs into accumulator *)
let check_op_def = cake_define
  `check_op ts opr loc exp =
     (match opbinargs opr (try_swap loc opr exp) with
       NONE -> NONE | SOME (xs,f) ->
         (if bvi_tailrec_is_rec loc f /\ term_ok ts (op_type opr) xs
           then
           SOME (apply_op opr xs f) else
           NONE))`;;

(* --- Type analysis --- *)

let decide_ty_def = cake_define
  `decide_ty x1 x2 =
        match (x1,x2) with
          ((Int:v_ty),(Int:v_ty)) -> Int
        | (List,List) -> List
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
        closLang_IntOp (closLang_Const i) -> (if small_enough_int i
          then Int else bvi_tailrec_Any)
      | (closLang_IntOp closLang_Add) -> Int
      | (closLang_IntOp closLang_Sub) -> Int
      | (closLang_IntOp closLang_Mult) -> Int
      | (closLang_IntOp closLang_Div) -> Int
      | (closLang_IntOp closLang_Mod) -> Int
      | (closLang_IntOp closLang_LessEq) -> Int
      | (closLang_IntOp closLang_Less) -> Int
      | (closLang_IntOp Greater) -> Int
      | (closLang_IntOp closLang_GreaterEq) -> Int
      | (closLang_BlockOp ListAppend) -> List
      | _17 -> bvi_tailrec_Any`;;

let op_ty_def = cake_define
  `op_ty x1 =
        match x1 with
          closLang_IntOp closLang_Add -> Int
        | (closLang_IntOp closLang_Sub) -> Int
        | (closLang_IntOp closLang_Mult) -> Int
        | (closLang_IntOp closLang_Div) -> Int
        | (closLang_IntOp closLang_Mod) -> Int
        | (closLang_BlockOp ListAppend) -> List
        | (closLang_BlockOp (closLang_Cons tag)) -> (if tag = nil_tag
          \/ tag = cons_tag then List else bvi_tailrec_Any)
        | (closLang_IntOp (closLang_Const i)) -> (if small_enough_int
          i then Int else bvi_tailrec_Any)
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

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let scan_expr_def = cake_define_list_cheat CHEAT_TAC
  [`scan_expr ts loc [] = []`;
   `scan_expr ts loc (x :: y :: xs) =
        (let (tx,ty,r,op) = HD (scan_expr ts loc [x]) in
          (tx,ty,r,op) :: scan_expr tx loc (y :: xs))`;
   `scan_expr ts loc [(Var n:bvi_exp)] =
        (let ty = (if n < LENGTH ts then EL n ts else
          bvi_tailrec_Any) in
          [(ts,ty,F,NONE)])`;
   `scan_expr ts loc [(If xi xt xe:bvi_exp)] =
        (let (ti,tyi,_27,oi) = HD (scan_expr ts loc [xi]) in
        let (tt,ty1,_28,ot) = HD (scan_expr ti loc [xt]) in
        let (te,ty2,_29,oe) = HD (scan_expr ti loc [xe]) in
        let op = (match ot with NONE -> oe | _30 -> ot) in
        let ty = (match op with
                   NONE -> decide_ty ty1 ty2 | SOME opr -> decide_ty
                     ty1 (decide_ty ty2 (op_type opr))) in
          [(MAP2 decide_ty tt te,ty,IS_SOME oe,op)])`;
   `scan_expr ts loc [(Let xs x:bvi_exp)] =
        (let ys = scan_expr ts loc xs in
        let tt = MAP (FST o SND) ys in
        let tr = (match LAST1 ys with SOME c -> FST c | NONE -> ts)
          in
        let (tu,ty,_33,op) = HD (scan_expr (tt ++ tr) loc [x]) in
          [(DROP (LENGTH ys) tu,ty,F,op)])`;
   `scan_expr ts loc [(Raise x:bvi_exp)] =
  [(ts,bvi_tailrec_Any,F,NONE)]`;
   `scan_expr ts loc [(Tick x:bvi_exp)] = scan_expr ts loc [x]`;
   `scan_expr ts loc [(Force _35 n:bvi_exp)] =
        (let ty = (if n < LENGTH ts then EL n ts else
          bvi_tailrec_Any) in
          [(ts,ty,F,NONE)])`;
   `scan_expr ts loc [(Call t d xs h:bvi_exp)] =
  [(ts,bvi_tailrec_Any,F,NONE)]`;
   `scan_expr ts loc [(bvi_Return xs:bvi_exp)] =
  [(ts,bvi_tailrec_Any,F,NONE)]`;
   `scan_expr ts loc [bvi_LetCall rets t d xs y] =
  [(ts,bvi_tailrec_Any,F,NONE)]`;
   `scan_expr ts loc [(Op op xs:bvi_exp)] =
        (let opr = from_op op in
        let opt = op_type opr in
          match opr with
            bvi_tailrec_Noop ->
              (if arg_ty op = Int then
                match get_bin_args (Op op xs) with
                  NONE ->
                    (if bvi_tailrec_is_const op then
                      [(ts,Int,F,NONE)] else
                      [(ts,bvi_tailrec_Any,F,NONE)]) | SOME (x,y) ->
                    (if ~bvi_tailrec_is_const op then
                      [(update_context Int ts x
                        y,bvi_tailrec_Any,F,NONE)] else
                      [(ts,bvi_tailrec_Any,F,NONE)]) else if op =
                        closLang_BlockOp (closLang_Cons 0) /\ xs = []
                        then
                [(ts,List,F,NONE)] else
                [(ts,bvi_tailrec_Any,F,NONE)]) | _38 ->
              (if IS_SOME (check_op ts opr loc (Op op xs)) then
                [(ts,opt,F,SOME opr)] else if term_ok ts opt (Op op
                  xs) then
                match get_bin_args (Op op xs) with
                  NONE -> [(ts,bvi_tailrec_Any,F,NONE)] | SOME (x,y)
                    ->
                    [(update_context opt ts x y,opt,F,NONE)] else
                [(ts,bvi_tailrec_Any,F,NONE)]))`];;

let scan_expr_sing_def = cake_define_list
  [`scan_expr_sing ts loc (Var n:bvi_exp) =
        (let ty = (if n < LENGTH ts then EL n ts else
          bvi_tailrec_Any) in
          (ts,ty,F,NONE))`;
   `scan_expr_sing ts loc (If xi xt xe:bvi_exp) =
        (let (ti,tyi,_47,oi) = scan_expr_sing ts loc xi in
        let (tt,ty1,_48,ot) = scan_expr_sing ti loc xt in
        let (te,ty2,_49,oe) = scan_expr_sing ti loc xe in
        let op = (match ot with NONE -> oe | _50 -> ot) in
        let ty = (match op with
                   NONE -> decide_ty ty1 ty2 | SOME opr -> decide_ty
                     ty1 (decide_ty ty2 (op_type opr))) in
          (MAP2 decide_ty tt te,ty,IS_SOME oe,op))`;
   `scan_expr_sing ts loc (Let xs x:bvi_exp) =
        (let ys = scan_expr_list ts loc xs in
        let tt = MAP (FST o SND) ys in
        let tr = (match LAST1 ys with SOME c -> FST c | NONE -> ts)
          in
        let (tu,ty,_53,op) = scan_expr_sing (tt ++ tr) loc x in
          (DROP (LENGTH ys) tu,ty,F,op))`;
   `scan_expr_sing ts loc (Raise x:bvi_exp) =
  (ts,bvi_tailrec_Any,F,NONE)`;
   `scan_expr_sing ts loc (Tick x:bvi_exp) = scan_expr_sing ts loc x`;
   `scan_expr_sing ts loc (Force _55 n:bvi_exp) =
        (let ty = (if n < LENGTH ts then EL n ts else
          bvi_tailrec_Any) in
          (ts,ty,F,NONE))`;
   `scan_expr_sing ts loc (Call t d xs h:bvi_exp) =
  (ts,bvi_tailrec_Any,F,NONE)`;
   `scan_expr_sing ts loc (bvi_Return xs:bvi_exp) =
  (ts,bvi_tailrec_Any,F,NONE)`;
   `scan_expr_sing ts loc (bvi_LetCall rets t d xs y) =
  (ts,bvi_tailrec_Any,F,NONE)`;
   `scan_expr_sing ts loc (Op op xs:bvi_exp) =
        (let opr = from_op op in
        let opt = op_type opr in
          match opr with
            bvi_tailrec_Noop ->
              (if arg_ty op = Int then
                match get_bin_args (Op op xs) with
                  NONE ->
                    (if bvi_tailrec_is_const op then
                      (ts,Int,F,NONE) else
                      (ts,bvi_tailrec_Any,F,NONE)) | SOME (x,y) ->
                    (if ~bvi_tailrec_is_const op then
                      (update_context Int ts x
                        y,bvi_tailrec_Any,F,NONE) else
                      (ts,bvi_tailrec_Any,F,NONE)) else if op =
                        closLang_BlockOp (closLang_Cons 0) /\ xs = []
                        then
                (ts,List,F,NONE) else
                (ts,bvi_tailrec_Any,F,NONE)) | _58 ->
              (if IS_SOME (check_op ts opr loc (Op op xs)) then
                (ts,opt,F,SOME opr) else if term_ok ts opt (Op op
                  xs) then
                match get_bin_args (Op op xs) with
                  NONE -> (ts,bvi_tailrec_Any,F,NONE) | SOME (x,y)
                    ->
                    (update_context opt ts x y,opt,F,NONE) else
                (ts,bvi_tailrec_Any,F,NONE)))`;
   `scan_expr_list ts loc [] = []`;
   `scan_expr_list ts loc (x :: xs) =
        (let (tx,ty,r,op) = scan_expr_sing ts loc x in
          (tx,ty,r,op) :: scan_expr_list tx loc xs)`];;

let push_call_def = cake_define
  `push_call n op acc exp x5 =
        match x5 with
          SOME (ticks,dest,args,handler) ->
       Call ticks (SOME n) (args ++ [apply_op op (Var acc) exp])
         handler
        | _59 -> dummy`;;

let rewrite_def = cake_define
  `rewrite loc next' opr acc ts exp =
        match exp with
          (Var n:bvi_exp) -> (F,Var n)
        | (If x1 x2 x3) ->
       (let t1 = FST (HD (scan_expr ts loc [x1])) in
       let (r2,y2) = rewrite loc next' opr acc t1 x2 in
       let (r3,y3) = rewrite loc next' opr acc t1 x3 in
       let z2 = (if r2 then y2 else apply_op opr (Var acc) x2) in
       let z3 = (if r3 then y3 else apply_op opr (Var acc) x3) in
         ((r2 \/ r3),If x1 z2 z3))
        | (Let xs x) ->
       (let ys = scan_expr ts loc xs in
       let tt = MAP (FST o SND) ys in
       let tr = (match LAST1 ys with NONE -> ts | SOME c -> FST c) in
       let (r,y) = rewrite loc next' opr (acc + LENGTH xs) (tt ++ tr)
         x in
         (r,Let xs y))
        | (Tick x) ->
       (let (r,y) = rewrite loc next' opr acc ts x in
         (r,Tick y))
        | (Force l v) -> (F,Force l v)
        | exp ->
       (match check_op ts opr loc exp with
         NONE -> (F,apply_op opr (Var acc) exp) | SOME exp ->
           (match opbinargs opr exp with
             NONE -> (F,apply_op opr (Var acc) exp) | SOME (xs,f)
               -> (T,push_call next' opr acc xs (args_from f))))`;;


(* --- Top-level expression check --- *)

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let has_rec_def = cake_define_cheat CHEAT_TAC
  `has_rec loc x2 =
        match x2 with
          [] -> F
        | (x :: y :: xs) ->
       (if has_rec loc [x] then T else has_rec loc (y :: xs))
        | [(If x1 x2 x3:bvi_exp)] ->
       (if has_rec loc [x2] then T else has_rec loc [x3])
        | [Let xs x] -> has_rec loc [x]
        | [Tick x] -> has_rec loc [x]
        | [Op op xs] ->
       (if EXISTS (bvi_tailrec_is_rec loc) xs then T else has_rec loc
         xs)
        | [x] -> F`;;

let has_rec1_def = cake_define
  `has_rec1 loc x = has_rec loc [x]`;;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let has_rec_sing_def = cake_define_list_cheat CHEAT_TAC
  [`has_rec_sing loc (If x1 x2 x3:bvi_exp) =
        (if has_rec_sing loc x2 then T else has_rec_sing loc x3)`;
   `has_rec_sing loc (Let xs x:bvi_exp) = has_rec_sing loc x`;
   `has_rec_sing loc (Tick x:bvi_exp) = has_rec_sing loc x`;
   `has_rec_sing loc (Op op xs:bvi_exp) =
        (if EXISTS (bvi_tailrec_is_rec loc) xs then T else
          has_rec_list loc xs)`;
   `has_rec_sing loc x = F`;
   `has_rec_list loc [] = F`;
   `has_rec_list loc (x :: xs) =
        (if has_rec_sing loc x then T else has_rec_list loc xs)`];;

(* HOL4 bvi_tailrecScript.sml:744: ML code, not ported *)

(* HOL4 bvi_tailrecScript.sml:751: ML code, not ported *)

let check_exp_def = cake_define
  `check_exp loc arity exp =
     (if ~has_rec1 loc exp then NONE else
       let context = REPLICATE arity bvi_tailrec_Any in
         match scan_expr context loc [exp] with
           [] -> NONE | (ts,ty,r,opr) :: _60 ->
             (match opr with
               NONE -> NONE | SOME op ->
                 (if ~(ty = op_type op) then NONE else opr)))`;;

let let_wrap_def = cake_define
  `let_wrap arity id' exp =
     Let ((GENLIST (\i. Var i) arity) ++ [id']) exp`;;

let mk_aux_call_def = cake_define
  `mk_aux_call loc arity id' =
     Call 0 (SOME loc) (id' :: GENLIST (\i. Var i) arity) NONE`;;

let compile_exp_def = cake_define
  `bvi_tailrec_compile_exp loc next' arity exp =
     (match check_exp loc arity exp with
       NONE -> NONE | SOME op ->
       (let context = REPLICATE arity bvi_tailrec_Any in
       let (r,opt) = rewrite loc next' op arity context exp in
       let aux = let_wrap arity (id_from_op op) opt in
         SOME (aux,opt)))`;;
hol4_overload "compile_exp" "bvi_tailrec_compile_exp";;

let compile_each_def = cake_define_list
  [`bvi_tailrec_compile_each next' [] = (next',[])`;
   `bvi_tailrec_compile_each next' ((loc,arity,exp) :: xs) =
        (match bvi_tailrec_compile_exp loc next' arity exp with NONE
          ->
            (let (n,ys) = bvi_tailrec_compile_each next' xs in
              (n,(loc,arity,exp) :: ys)) | SOME (exp_aux,exp_opt) ->
            (let (n,ys) = bvi_tailrec_compile_each (next' +
              bvl_to_bvi_namespaces) xs in
            (n,(loc,arity,exp_aux) :: (next',arity + 1,exp_opt)
              :: ys)))`];;
hol4_overload "compile_each" "bvi_tailrec_compile_each";;

let compile_prog_def = cake_define
  `bvi_tailrec_compile_prog do_it next' xs =
     (if do_it then bvi_tailrec_compile_each next' xs else
       (next',xs))`;;
hol4_overload "compile_prog" "bvi_tailrec_compile_prog";;

(* --- Test rewriting --- *)

(* HOL4 bvi_tailrecScript.sml:860-865: ML code, not ported *)

(* HOL4 bvi_tailrecScript.sml:867-873: ML code, not ported *)

(* HOL4 bvi_tailrecScript.sml:887-895: ML code, not ported *)

(* HOL4 bvi_tailrecScript.sml:897-906: ML code, not ported *)

(* HOL4 bvi_tailrecScript.sml:908: ML code, not ported *)
