(* ======================================================== *)
(*  bvi_tailrec: ported from HOL4's
    compiler/backend/bvi_tailrecScript.sml
    A definition theory, with 39 definitions, 2 datatypes and 35
    theorems.  Needed by bvi_tailrecProof.ml, bvl_to_bvi.ml,
    bvl_to_bviProof.ml and word_bignum.ml.  *)
(* ======================================================== *)

(*
  A compiler phase that turns some non-tail-recursive functions into
  tail-recursive functions.
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "bvi_tailrec"
  ["backend_common"; "bvi"];;

let _ = do_list hide_constant ["pmatch"];;

let dummy_def = new_definition
  `dummy = bvi_Var 1234567890`;;

make_size "bvi_exp";;
let MEM_exp_size_imp = prove
 (`!xs a. MEM a xs ==> bvi_exp_size a < list_size bvi_exp_size xs`,
  CHEAT_TAC);;

let is_rec_def = new_definition
  `bvi_tailrec_is_rec name x2 =
     match x2 with
       bvi_Call _ d _ NONE -> d = SOME name
     | _ -> F`;;

let is_rec_PMATCH = prove
 (`!expr. bvi_tailrec_is_rec name expr =
    match expr with
      bvi_Call _ d _ NONE -> d = SOME name
    | _ -> F`,
  CHEAT_TAC);;

let is_const_def = new_definition
  `bvi_tailrec_is_const x1 =
     match x1 with
       clos_IntOp (clos_Const i) -> small_enough_int i
     | _ -> F`;;
add_simp is_const_def;;

let is_const_PMATCH = prove
 (`!op. bvi_tailrec_is_const op =
    match op with
      clos_IntOp (clos_Const i) -> small_enough_int i
    | _ -> F`,
  CHEAT_TAC);;

let assoc_op_INDUCT,assoc_op_RECURSION = define_datatype
  "assoc_op =
     bvi_tailrec_Plus
   | bvi_tailrec_Times
   | bvi_tailrec_Append
   | bvi_tailrec_Noop";;

let v_ty_INDUCT,v_ty_RECURSION = define_datatype
  "v_ty =
     bvi_tailrec_Int
   | bvi_tailrec_List
   | bvi_tailrec_Any";;

let op_type_def = new_definition
  `op_type x1' =
   match x1' with
     bvi_tailrec_Append -> bvi_tailrec_List
   | bvi_tailrec_Noop -> bvi_tailrec_Any
   | _ -> bvi_tailrec_Int`;;

let to_op_def = define_cases
  `(to_op bvi_tailrec_Plus = clos_IntOp clos_Add) /\
   (to_op bvi_tailrec_Times = clos_IntOp clos_Mult) /\
   (to_op bvi_tailrec_Append = clos_BlockOp clos_ListAppend) /\
   (to_op bvi_tailrec_Noop = clos_IntOp clos_Mod)`;;

let from_op_def = new_definition
  `from_op op =
     if op = clos_IntOp clos_Add then bvi_tailrec_Plus
     else if op = clos_IntOp clos_Mult then bvi_tailrec_Times
     else if op = clos_BlockOp clos_ListAppend then bvi_tailrec_Append
     else bvi_tailrec_Noop`;;

let from_op_PMATCH = prove
 (`!op.
    from_op op =
      match op with
        clos_IntOp clos_Add -> bvi_tailrec_Plus
      | clos_IntOp clos_Mult -> bvi_tailrec_Times
      | clos_BlockOp clos_ListAppend -> bvi_tailrec_Append
      | _ -> bvi_tailrec_Noop`,
  CHEAT_TAC);;

(* HOL4 bvi_tailrecScript.sml:103-107: a theorem that HOL4 states as the
   value of an ML expression: from_op_thm *)

let op_eq_def = new_definition
  `op_eq x1 x2 =
     match (x1,x2) with
       (bvi_tailrec_Plus,bvi_Op op xs) -> op = clos_IntOp clos_Add
     | (bvi_tailrec_Times,bvi_Op op xs) -> op = clos_IntOp clos_Mult
     | (bvi_tailrec_Append,bvi_Op op xs) -> op = clos_BlockOp
       clos_ListAppend
     | (_,_) -> F`;;

let op_eq_PMATCH = prove
 (`!a expr.
     op_eq a expr =
       match expr with
         bvi_Op op xs ->
           (match a with
             bvi_tailrec_Plus -> op = clos_IntOp clos_Add
           | bvi_tailrec_Times -> op = clos_IntOp clos_Mult
           | bvi_tailrec_Append -> op = clos_BlockOp clos_ListAppend
           | _ -> F)
       | _ -> F`,
  CHEAT_TAC);;

let op_eq_to_op = prove
 (`!iop op xs.
      op_eq iop (bvi_Op op xs) <=>
      op = to_op iop /\ ~(iop = bvi_tailrec_Noop)`,
  CHEAT_TAC);;
add_simp op_eq_to_op;;

let apply_op_def = new_definition
  `apply_op op e1 e2 = bvi_Op (to_op op) [e1; e2]`;;

let id_from_op_def = define_cases
  `(id_from_op bvi_tailrec_Plus = bvi_Op (clos_IntOp (clos_Const (&0))) []) /\
   (id_from_op bvi_tailrec_Times = bvi_Op (clos_IntOp (clos_Const (&1))) []) /\
   (id_from_op bvi_tailrec_Append = bvi_Op (clos_BlockOp (clos_Cons
    nil_tag)) []) /\
   (id_from_op bvi_tailrec_Noop = dummy)`;;

let index_of_def = new_definition
  `index_of x1 =
     match x1 with
       bvi_Var i -> SOME i
     | _ -> NONE`;;

let index_of_PMATCH = prove
 (`!expr.
     index_of expr =
       match expr with
         bvi_Var i -> SOME i
       | _ -> NONE`,
  CHEAT_TAC);;

let args_from_def = new_definition
  `args_from x1' =
     match x1' with
       bvi_Call t (SOME d) as hdl -> SOME (t,d,as,hdl)
     | _ -> NONE`;;

let args_from_PMATCH = prove
 (`!expr.
     args_from expr =
       match expr with
         bvi_Call t (SOME d) as hdl -> SOME (t,d,as,hdl)
       | _ -> NONE`,
  CHEAT_TAC);;

let get_bin_args_def = new_definition
  `get_bin_args op =
     match op with bvi_Op _ [e1; e2] -> SOME (e1,e2)
     | _ -> NONE`;;

let get_bin_args_PMATCH = prove
 (`!op.
     get_bin_args op =
       match op with
         bvi_Op _ [e1; e2] -> SOME (e1,e2)
       | _ -> NONE`,
  CHEAT_TAC);;

let exp_size_get_bin_args = prove
 (`!x x1 x2.
     get_bin_args x = SOME (x1,x2) ==>
       bvi_exp_size x1 + bvi_exp_size x2 < bvi_exp_size x`,
  CHEAT_TAC);;

let opbinargs_def = new_definition
  `opbinargs opr exp = if ~(op_eq opr exp) then NONE else get_bin_args exp`;;

let try_update_def = define_cases
  `(try_update vty NONE ts = ts) /\
   (try_update vty (SOME n) ts =
        if n < LENGTH ts then
          if EL n ts = bvi_tailrec_Any then APPEND (APPEND (TAKE n ts)
              [vty]) (DROP (n + 1) ts)
          else ts
        else ts)`;;

(* --- Checking termination guarantees --- *)

let is_arith_def = new_definition
  `is_arith op =
     match op with
       clos_IntOp clos_Add -> T
     | clos_IntOp clos_Sub -> T
     | clos_IntOp clos_Mult -> T
     | _ -> F`;;

let is_arith_PMATCH = prove
 (`!op.
     is_arith op =
       match op with
         clos_IntOp clos_Add -> T
       | clos_IntOp clos_Sub -> T
       | clos_IntOp clos_Mult -> T
       | _ -> F`,
  CHEAT_TAC);;

let is_rel_def = new_definition
  `is_rel op =
     match op with
       clos_IntOp clos_Less -> T
     | clos_IntOp clos_LessEq -> T
     | clos_IntOp clos_Greater -> T
     | clos_IntOp clos_GreaterEq -> T
     | _ -> F`;;

let is_rel_PMATCH = prove
 (`!op.
     is_rel op =
       match op with
         clos_IntOp clos_Less -> T
       | clos_IntOp clos_LessEq -> T
       | clos_IntOp clos_Greater -> T
       | clos_IntOp clos_GreaterEq -> T
       | _ -> F`,
  CHEAT_TAC);;

let _ = size_thms "bvi_exp";;

let exp_size_get_bin_args_term = prove
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

cake_term_facts := exp_size_get_bin_args_term ::
  (!cake_term_facts);;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 bvi_tailrecScript.sml:280-284: the tactic that proves the
   termination *)
let term_ok_int_def,term_ok_int_ind = define_wf
  `MEASURE (bvi_exp_size o SND)`
  `term_ok_int ts expr =
     match expr with
       bvi_Var i -> if i < LENGTH ts then EL i ts = bvi_tailrec_Int else F
     | bvi_Op op xs ->
         (match get_bin_args expr with
           NONE -> xs = [] /\ bvi_tailrec_is_const op
         | SOME (x,y) -> is_arith op /\ term_ok_int ts x /\ term_ok_int ts
           y)
     | _ -> F`;;

(* HOL4 bvi_tailrecScript.sml:286: a theorem that HOL4 states as the value
   of an ML expression: term_ok_int_ind *)

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 bvi_tailrecScript.sml:303-307: the tactic that proves the
   termination *)
let term_ok_any_def,term_ok_any_ind = define_wf
  `MEASURE (bvi_exp_size o SND o SND)`
  `term_ok_any ts list' expr =
     match expr with
       bvi_Var i ->
       if ~list' then i < LENGTH ts
       else if i < LENGTH ts then EL i ts = bvi_tailrec_List
       else F
     | bvi_Op op xs ->
       (match get_bin_args (bvi_Op op xs) with
         NONE -> xs = [] /\ (if list' then op = clos_BlockOp (clos_Cons 0)
           else bvi_tailrec_is_const op)
       | SOME (x,y) ->
           if op = clos_BlockOp clos_ListAppend then term_ok_any ts T x
             /\ term_ok_any ts T y
           else if ~list' /\ is_arith op then term_ok_int ts x
             /\ term_ok_int ts y
           else if ~list' /\ is_rel op then term_ok_int ts x /\ term_ok_int
             ts y
           else if op = clos_BlockOp (clos_Cons 0) then term_ok_any ts T x
             /\ term_ok_any ts F y
           else F)
     | expr -> F`;;

let is_op_thms = prove
 (`~(is_arith (clos_BlockOp (clos_Cons 0))) /\ ~(is_arith (clos_BlockOp
  clos_ListAppend)) /\
   ~(is_rel (clos_BlockOp (clos_Cons 0))) /\ ~(is_rel (clos_BlockOp
     clos_ListAppend)) /\
   (!op. ~(op = clos_BlockOp clos_ListAppend) /\ is_arith op <=> is_arith
     op) /\
   (!op. ~(op = clos_BlockOp clos_ListAppend) /\ ~(is_arith op) /\ is_rel op
     <=> is_rel op) /\
   (!op. ~(is_arith op) /\ ~(is_rel op) /\ op = clos_BlockOp (clos_Cons 0)
     <=> op = clos_BlockOp (clos_Cons 0)) /\
   (!op. ~(op = clos_BlockOp clos_ListAppend) /\ op = clos_BlockOp
     (clos_Cons 0) <=> op = clos_BlockOp (clos_Cons 0))`,
  CHEAT_TAC);;

(* HOL4 bvi_tailrecScript.sml:322: a theorem that HOL4 states as the value
   of an ML expression: term_ok_any_ind *)

(* HOL4 bvi_tailrecScript.sml:324-346: code that the source has in a comment *)

let term_ok_def = new_definition
  `term_ok ts ty expr =
     match ty with
       bvi_tailrec_Any -> term_ok_any ts F expr
     | bvi_tailrec_Int -> term_ok_int ts expr
     | bvi_tailrec_List -> term_ok_any ts T expr`;;

(* --- Simple tail checking before rewriting --- *)

(* Swap arguments when commutative *)
let try_swap_def = new_definition
  `try_swap loc opr exp =
     match opr with
       bvi_tailrec_Append -> exp
     | opr ->
       (match opbinargs opr exp with
         NONE -> exp
       | SOME (l,r) ->
           if bvi_tailrec_is_rec loc l then apply_op opr r l else exp)`;;

(* Check if ok to lift xs into accumulator *)
let check_op_def = new_definition
  `check_op ts opr loc exp =
     match opbinargs opr (try_swap loc opr exp) with
       NONE -> NONE
     | SOME (xs,f) ->
         if bvi_tailrec_is_rec loc f /\ term_ok ts (op_type opr) xs then
           SOME (apply_op opr xs f)
         else NONE`;;

(* --- Type analysis --- *)

let decide_ty_def = new_definition
  `decide_ty x1 x2 =
     match (x1,x2) with
       (bvi_tailrec_Int,bvi_tailrec_Int) -> bvi_tailrec_Int
     | (bvi_tailrec_List,bvi_tailrec_List) -> bvi_tailrec_List
     | (_,_) -> bvi_tailrec_Any`;;
add_simp decide_ty_def;;

let decide_ty_PMATCH = prove
 (`!ty1 ty2.
     decide_ty ty1 ty2 =
       match (ty1,ty2) with
         (bvi_tailrec_Int,bvi_tailrec_Int) -> bvi_tailrec_Int
       | (bvi_tailrec_List,bvi_tailrec_List) -> bvi_tailrec_List
       | _ -> bvi_tailrec_Any`,
  CHEAT_TAC);;

let LAST1_def,LAST1_ind = define_guess
  `LAST1 x1' =
   match x1' with
     [] -> NONE
   | [x] -> SOME x
   | CONS x xs -> LAST1 xs`;;

let update_context_def = new_definition
  `update_context ty ts x1 x2 =
     try_update ty (index_of x2) (try_update ty (index_of x1) ts)`;;

let arg_ty_def = new_definition
  `arg_ty x1'' =
   match x1'' with
     clos_IntOp (clos_Const i) -> (if small_enough_int i then
       bvi_tailrec_Int else bvi_tailrec_Any)
   | clos_IntOp clos_Add -> bvi_tailrec_Int
   | clos_IntOp clos_Sub -> bvi_tailrec_Int
   | clos_IntOp clos_Mult -> bvi_tailrec_Int
   | clos_IntOp clos_Div -> bvi_tailrec_Int
   | clos_IntOp clos_Mod -> bvi_tailrec_Int
   | clos_IntOp clos_LessEq -> bvi_tailrec_Int
   | clos_IntOp clos_Less -> bvi_tailrec_Int
   | clos_IntOp clos_Greater -> bvi_tailrec_Int
   | clos_IntOp clos_GreaterEq -> bvi_tailrec_Int
   | clos_BlockOp clos_ListAppend -> bvi_tailrec_List
   | _ -> bvi_tailrec_Any`;;

let arg_ty_PMATCH = prove
 (`!op.
     arg_ty op =
       match op with
         clos_IntOp clos_Add -> bvi_tailrec_Int
       | clos_IntOp clos_Sub -> bvi_tailrec_Int
       | clos_IntOp clos_Mult -> bvi_tailrec_Int
       | clos_IntOp clos_Div -> bvi_tailrec_Int
       | clos_IntOp clos_Mod -> bvi_tailrec_Int
       | clos_IntOp clos_LessEq -> bvi_tailrec_Int
       | clos_IntOp clos_Less -> bvi_tailrec_Int
       | clos_IntOp clos_Greater -> bvi_tailrec_Int
       | clos_IntOp clos_GreaterEq -> bvi_tailrec_Int
       | clos_IntOp (clos_Const i) -> if small_enough_int i then
         bvi_tailrec_Int else bvi_tailrec_Any
       | clos_BlockOp clos_ListAppend -> bvi_tailrec_List
       | _ -> bvi_tailrec_Any`,
  CHEAT_TAC);;

let op_ty_def = new_definition
  `op_ty x1''' =
     match x1''' with
       clos_IntOp clos_Add -> bvi_tailrec_Int
     | clos_IntOp clos_Sub -> bvi_tailrec_Int
     | clos_IntOp clos_Mult -> bvi_tailrec_Int
     | clos_IntOp clos_Div -> bvi_tailrec_Int
     | clos_IntOp clos_Mod -> bvi_tailrec_Int
     | clos_BlockOp clos_ListAppend -> bvi_tailrec_List
     | clos_BlockOp (clos_Cons tag) -> if tag = nil_tag \/ tag = cons_tag
       then bvi_tailrec_List else bvi_tailrec_Any
     | clos_IntOp (clos_Const i) -> if small_enough_int i then
       bvi_tailrec_Int else bvi_tailrec_Any
     | _ -> bvi_tailrec_Any`;;

let op_ty_PMATCH = prove
 (`!op.
     op_ty op =
       match op with
         clos_IntOp clos_Add -> bvi_tailrec_Int
       | clos_IntOp clos_Sub -> bvi_tailrec_Int
       | clos_IntOp clos_Mult -> bvi_tailrec_Int
       | clos_IntOp clos_Div -> bvi_tailrec_Int
       | clos_IntOp clos_Mod -> bvi_tailrec_Int
       | clos_BlockOp clos_ListAppend -> bvi_tailrec_List
       | clos_BlockOp (clos_Cons tag) -> if tag = cons_tag \/ tag = nil_tag
         then bvi_tailrec_List else bvi_tailrec_Any
       | clos_IntOp (clos_Const i) -> if small_enough_int i then
         bvi_tailrec_Int else bvi_tailrec_Any
       | _ -> bvi_tailrec_Any`,
  CHEAT_TAC);;

(* Gather information about expressions:

     - Build context by following order of evaluation during recursion
       and set variable to Int only if interpretation of the expression would
       result in Rerr (Rabort Rtype_error) otherwise.
     - Check if tail positions are arithmetic or variables typed as Int in
       context.
     - Check if tail positions carry suitable operation (Add/Mult) and track
       branch of origin for the operation in conditionals.
*)

(* the clauses in two quotations: d is (num option) and num; xs is (_)list
   and (exp list), which one quotation cannot typecheck *)
let scan_expr_def,scan_expr_ind = assume_definition_rec_clauses
  "termination (CHEAT_TAC)"
  [`(scan_expr ts loc [] = []) /\
    (scan_expr ts loc (CONS x (CONS y xs)) =
        let (tx,ty,r,op) = HD (scan_expr ts loc [x]) in CONS
            (tx,ty,r,op) (scan_expr tx loc (CONS y xs))) /\
    (scan_expr ts loc [bvi_Var n] =
        let ty = (if n < LENGTH ts then EL n ts else bvi_tailrec_Any) in
          [(ts,ty,F,NONE)]) /\
    (scan_expr ts loc [bvi_If xi xt xe] =
        let (ti,tyi,_,oi) = HD (scan_expr ts loc [xi]) in
        let (tt,ty1,_,ot) = HD (scan_expr ti loc [xt]) in
        let (te,ty2,_,oe) = HD (scan_expr ti loc [xe]) in
        let op = (match ot with NONE -> oe | _ -> ot) in
        let ty = (match op with
                   NONE -> decide_ty ty1 ty2
                 | SOME opr -> decide_ty ty1 (decide_ty ty2 (op_type opr)))
                     in
          [(MAP2 decide_ty tt te,ty,IS_SOME oe,op)]) /\
    (scan_expr ts loc [bvi_Let xs x] =
        let ys = scan_expr ts loc xs in
        let tt = MAP (FST o SND) ys in
        let tr = (match LAST1 ys with SOME c -> FST c | NONE -> ts) in
        let (tu,ty,_,op) = HD (scan_expr (APPEND tt tr) loc [x]) in
          [(DROP (LENGTH ys) tu,ty,F,op)]) /\
    (scan_expr ts loc [bvi_Raise x] = [(ts,bvi_tailrec_Any,F,NONE)]) /\
    (scan_expr ts loc [bvi_Tick x] = scan_expr ts loc [x]) /\
    (scan_expr ts loc [bvi_Force _ n] =
        let ty = (if n < LENGTH ts then EL n ts else bvi_tailrec_Any) in
          [(ts,ty,F,NONE)]) /\
    (scan_expr ts loc [bvi_Call t d xs h] = [(ts,bvi_tailrec_Any,F,NONE)]) /\
    // multi-value calls/returns decline the tail-rec optimisation. TODO(multiret):
    // to optimise them, is_rec/has_rec/scan_expr/rewrite must recognise LetCall
    // self-calls and Return-based accumulation.
    (scan_expr ts loc [bvi_Return xs] = [(ts,bvi_tailrec_Any,F,NONE)]) /\
    (scan_expr ts loc [bvi_Op op xs] =
        let opr = from_op op in
        let opt = op_type opr in
          match opr with
            bvi_tailrec_Noop ->
              // Constants?
              if arg_ty op = bvi_tailrec_Int then
                match get_bin_args (bvi_Op op xs) with
                  NONE ->
                    if bvi_tailrec_is_const op then
                      [(ts,bvi_tailrec_Int,F,NONE)]
                    else [(ts,bvi_tailrec_Any,F,NONE)]
                | SOME (x,y) ->
                    if ~(bvi_tailrec_is_const op) then
                      [(update_context bvi_tailrec_Int ts x
                          y,bvi_tailrec_Any,F,NONE)]
                    else [(ts,bvi_tailrec_Any,F,NONE)]
              else if op = clos_BlockOp (clos_Cons 0) /\ xs = [] then
                [(
                  // list nil
                  ts,bvi_tailrec_List,F,NONE)]
              else [(ts,bvi_tailrec_Any,F,NONE)]
          | _ ->
              // Things we can optimize
              if IS_SOME (check_op ts opr loc (bvi_Op op xs)) then
                [(ts,opt,F,SOME opr)]
              else if term_ok ts opt (bvi_Op op xs) then
                match get_bin_args (bvi_Op op xs) with
                  NONE -> [(ts,bvi_tailrec_Any,F,NONE)]
                | SOME (x,y) ->
                    [(update_context opt ts x y,opt,F,NONE)]
              else [(ts,bvi_tailrec_Any,F,NONE)])`;
   `scan_expr ts loc [bvi_LetCall rets t d xs y] =
    [(ts,bvi_tailrec_Any,F,NONE)]`];;

(* the clauses in two quotations: d is (num option) and num; xs is (exp list)
   and (_)list, which one quotation cannot typecheck *)
let scan_expr_sing_def,scan_expr_sing_ind = define_rec_clauses
  [`(scan_expr_sing ts loc (bvi_Var n) =
        let ty = (if n < LENGTH ts then EL n ts else bvi_tailrec_Any) in
          (ts,ty,F,NONE)) /\
    (scan_expr_sing ts loc (bvi_If xi xt xe) =
        let (ti,tyi,_,oi) = scan_expr_sing ts loc xi in
        let (tt,ty1,_,ot) = scan_expr_sing ti loc xt in
        let (te,ty2,_,oe) = scan_expr_sing ti loc xe in
        let op = (match ot with NONE -> oe | _ -> ot) in
        let ty = (match op with
                   NONE -> decide_ty ty1 ty2
                 | SOME opr -> decide_ty ty1 (decide_ty ty2 (op_type opr)))
                     in
          (MAP2 decide_ty tt te,ty,IS_SOME oe,op)) /\
    (scan_expr_sing ts loc (bvi_Let xs x) =
        let ys = scan_expr_list ts loc xs in
        let tt = MAP (FST o SND) ys in
        let tr = (match LAST1 ys with SOME c -> FST c | NONE -> ts) in
        let (tu,ty,_,op) = scan_expr_sing (APPEND tt tr) loc x in
          (DROP (LENGTH ys) tu,ty,F,op)) /\
    (scan_expr_sing ts loc (bvi_Raise x) = (ts,bvi_tailrec_Any,F,NONE)) /\
    (scan_expr_sing ts loc (bvi_Tick x) = scan_expr_sing ts loc x) /\
    (scan_expr_sing ts loc (bvi_Force _ n) =
        let ty = (if n < LENGTH ts then EL n ts else bvi_tailrec_Any) in
          (ts,ty,F,NONE)) /\
    (scan_expr_sing ts loc (bvi_Call t d xs h) = (ts,bvi_tailrec_Any,F,NONE))
      /\
    (scan_expr_sing ts loc (bvi_Return xs) = (ts,bvi_tailrec_Any,F,NONE)) /\
    (scan_expr_sing ts loc (bvi_Op op xs) =
        let opr = from_op op in
        let opt = op_type opr in
          match opr with
            bvi_tailrec_Noop ->
              // Constants?
              if arg_ty op = bvi_tailrec_Int then
                match get_bin_args (bvi_Op op xs) with
                  NONE ->
                    if bvi_tailrec_is_const op then
                      (ts,bvi_tailrec_Int,F,NONE)
                    else (ts,bvi_tailrec_Any,F,NONE)
                | SOME (x,y) ->
                    if ~(bvi_tailrec_is_const op) then
                      (update_context bvi_tailrec_Int ts x
                          y,bvi_tailrec_Any,F,NONE)
                    else (ts,bvi_tailrec_Any,F,NONE)
              else if op = clos_BlockOp (clos_Cons 0) /\ xs = [] then
                (
                 // list nil
                 ts,bvi_tailrec_List,F,NONE)
              else (ts,bvi_tailrec_Any,F,NONE)
          | _ ->
              // Things we can optimize
              if IS_SOME (check_op ts opr loc (bvi_Op op xs)) then
                (ts,opt,F,SOME opr)
              else if term_ok ts opt (bvi_Op op xs) then
                match get_bin_args (bvi_Op op xs) with
                  NONE -> (ts,bvi_tailrec_Any,F,NONE)
                | SOME (x,y) ->
                    (update_context opt ts x y,opt,F,NONE)
              else (ts,bvi_tailrec_Any,F,NONE)) /\
    (scan_expr_list ts loc [] = []) /\
    (scan_expr_list ts loc (CONS x xs) =
        let (tx,ty,r,op) = scan_expr_sing ts loc x in CONS
            (tx,ty,r,op) (scan_expr_list tx loc xs))`;
   `scan_expr_sing ts loc (bvi_LetCall rets t d xs y) =
    (ts,bvi_tailrec_Any,F,NONE)`];;

let scan_expr_eq = prove
 (`(!e ts loc. scan_expr ts loc [e] = [scan_expr_sing ts loc e]) /\
   (!es ts loc. scan_expr ts loc es = scan_expr_list ts loc es)`,
  CHEAT_TAC);;

let push_call_def = new_definition
  `push_call n op acc exp x5 =
     match x5 with
       SOME (ticks,dest,args,handler) ->
       bvi_Call ticks (SOME n) (APPEND args [apply_op op (bvi_Var acc) exp])
         handler
     | _ -> dummy`;;

let rewrite_def,rewrite_ind = define_shaped_rec
  "match"
  `rewrite loc next' opr acc ts exp =
     match exp with
       bvi_Var n -> (F,bvi_Var n)
     | bvi_If x1 x2 x3 ->
       let t1 = FST (HD (scan_expr ts loc [x1])) in
       let (r2,y2) = rewrite loc next' opr acc t1 x2 in
       let (r3,y3) = rewrite loc next' opr acc t1 x3 in
       let z2 = (if r2 then y2 else apply_op opr (bvi_Var acc) x2) in
       let z3 = (if r3 then y3 else apply_op opr (bvi_Var acc) x3) in
         ((r2 \/ r3),bvi_If x1 z2 z3)
     | bvi_Let xs x ->
       let ys = scan_expr ts loc xs in
       let tt = MAP (FST o SND) ys in
       let tr = (match LAST1 ys with NONE -> ts | SOME c -> FST c) in
       let (r,y) = rewrite loc next' opr (acc + LENGTH xs) (APPEND tt tr) x
         in
         (r,bvi_Let xs y)
     | bvi_Tick x ->
       let (r,y) = rewrite loc next' opr acc ts x in
         (r,bvi_Tick y)
     | bvi_Force l v -> (F,bvi_Force l v)
     | exp ->
       (match check_op ts opr loc exp with
         NONE -> (F,apply_op opr (bvi_Var acc) exp)
       | SOME exp ->
           (match opbinargs opr exp with
             NONE -> (F,apply_op opr (bvi_Var acc) exp)
           | SOME (xs,f) -> (T,push_call next' opr acc xs (args_from
             f))))`;;

let rewrite_PMATCH = prove
 (`!loc next' opr acc ts expr.
     rewrite loc next' opr acc ts expr =
       match expr with
         bvi_Var n -> (F,bvi_Var n)
       | bvi_If x1 x2 x3 ->
           let t1 = FST (HD (scan_expr ts loc [x1])) in
           let (r2,y2) = rewrite loc next' opr acc t1 x2 in
           let (r3,y3) = rewrite loc next' opr acc t1 x3 in
           let z2 = (if r2 then y2 else apply_op opr (bvi_Var acc) x2) in
           let z3 = (if r3 then y3 else apply_op opr (bvi_Var acc) x3) in
             ((r2 \/ r3),bvi_If x1 z2 z3)
       | bvi_Let xs x ->
           let ys = scan_expr ts loc xs in
           let tt = MAP (FST o SND) ys in
           let tr = (match LAST1 ys with NONE -> ts | SOME c -> FST c) in
           let (r,y) = rewrite loc next' opr (acc + LENGTH xs) (APPEND tt
             tr) x in
             (r,bvi_Let xs y)
       | bvi_Tick x ->
           let (r,y) = rewrite loc next' opr acc ts x in (r,bvi_Tick y)
       | bvi_Force l v -> (F,bvi_Force l v)
       | _ ->
           (match check_op ts opr loc expr with
             NONE -> (F,apply_op opr (bvi_Var acc) expr)
           | SOME expr2 ->
             (match opbinargs opr expr2 with
               NONE -> (F,apply_op opr (bvi_Var acc) expr2)
             | SOME (xs,f) -> (T,push_call next' opr acc xs (args_from
               f))))`,
  CHEAT_TAC);;

(* HOL4 bvi_tailrecScript.sml:694: a theorem that HOL4 states as the value
   of an ML expression: rewrite_eq *)


(* --- Top-level expression check --- *)

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let has_rec_def,has_rec_ind = define_guess_cheat
  `has_rec loc x2 =
     match x2 with
       [] -> F
     | CONS x (CONS y xs) ->
       if has_rec loc [x] then T
       else has_rec loc (CONS y xs)
     | [bvi_If x1 x2 x3] ->
       if has_rec loc [x2] then T
       else has_rec loc [x3]
     | [bvi_Let xs x] -> has_rec loc [x]
     | [bvi_Tick x] -> has_rec loc [x]
     | [bvi_Op op xs] ->
       if EX (bvi_tailrec_is_rec loc) xs then T
       else has_rec loc xs
     | [x] -> F`;;

let has_rec1_def = new_definition
  `has_rec1 loc x = has_rec loc [x]`;;

let has_rec_sing_def,has_rec_sing_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  `(has_rec_sing loc (bvi_If x1 x2 x3) =
        if has_rec_sing loc x2 then T
        else has_rec_sing loc x3) /\
   (has_rec_sing loc (bvi_Let xs x) = has_rec_sing loc x) /\
   (has_rec_sing loc (bvi_Tick x) = has_rec_sing loc x) /\
   (has_rec_sing loc (bvi_Op op xs) =
        if EX (bvi_tailrec_is_rec loc) xs then T
        else has_rec_list loc xs) /\
   (has_rec_sing loc x = F) /\
   (has_rec_list loc [] = F) /\
   (has_rec_list loc (CONS x xs) =
        if has_rec_sing loc x then T
        else has_rec_list loc xs)`;;

let has_rec_eq = prove
 (`(!e loc. has_rec loc [e] = has_rec_sing loc e) /\
   (!es loc. has_rec loc es = has_rec_list loc es)`,
  CHEAT_TAC);;

(* HOL4 bvi_tailrecScript.sml:744: the ML values that the definitions below
   antiquote *)
let has_rec_test1 = prove
 (`has_rec1 0 (bvi_Let [] (bvi_Call 0 (SOME 0) [] NONE)) <=> F`,
  (REWRITE_TAC[has_rec1_def; has_rec_def]));;

(* HOL4 bvi_tailrecScript.sml:751: the ML values that the definitions below
   antiquote *)
let has_rec_test2 = prove
 (`has_rec1 0 (bvi_Op (clos_IntOp clos_Add) [bvi_Call 0 (SOME 0) [] NONE;
  bvi_Var 0]) <=> T`,
  CHEAT_TAC);;

let check_exp_def = new_definition
  `check_exp loc arity exp =
     if ~(has_rec1 loc exp) then NONE else let context = REPLICATE arity
       bvi_tailrec_Any in
         match scan_expr context loc [exp] with
           [] -> NONE
         | CONS (ts,ty,r,opr) _ ->
             (match opr with
               NONE -> NONE
             | SOME op ->
                 if ~(ty = op_type op) then NONE else opr)`;;

(* HOL4 bvi_tailrecScript.sml:771-772: a theorem that HOL4 states as the
   value of an ML expression: check_exp_eq *)

let let_wrap_def = new_definition
  `let_wrap arity id' exp =
     bvi_Let (APPEND (list_of_seq (\i. bvi_Var i) arity) [id']) exp`;;

let mk_aux_call_def = new_definition
  `mk_aux_call loc arity id' =
     bvi_Call 0 (SOME loc) (CONS id' (list_of_seq (\i. bvi_Var i) arity))
       NONE`;;

let bvi_tailrec_compile_exp_def = new_definition
  `bvi_tailrec_compile_exp loc next' arity exp =
     match check_exp loc arity exp with
       NONE -> NONE
     | SOME op ->
       let context = REPLICATE arity bvi_tailrec_Any in
       let (r,opt) = rewrite loc next' op arity context exp in
       let aux = let_wrap arity (id_from_op op) opt in
         SOME (aux,opt)`;;

let compile_each_def,compile_each_ind = define_rec
  `(bvi_tailrec_compile_each next' [] = (next',[])) /\
   (bvi_tailrec_compile_each next' (CONS (loc,arity,exp) xs) =
        match bvi_tailrec_compile_exp loc next' arity exp with NONE ->
            let (n,ys) = bvi_tailrec_compile_each next' xs in
              (n,CONS (loc,arity,exp) ys)
        | SOME (exp_aux,exp_opt) ->
            let (n,ys) = bvi_tailrec_compile_each (next' +
                bvl_to_bvi_namespaces) xs in
            (n,CONS (loc,arity,exp_aux) (CONS (next',arity +
                1,exp_opt) ys)))`;;

let bvi_tailrec_compile_prog_def = new_definition
  `bvi_tailrec_compile_prog do_it next' xs =
     if do_it then bvi_tailrec_compile_each next' xs else (next',xs)`;;

let scan_expr_not_nil = prove
 (`!x. ~(scan_expr ts loc [x] = [])`,
  (REWRITE_TAC[CONJUNCT1 scan_expr_eq; NOT_CONS_NIL]));;
add_simp scan_expr_not_nil;;

let LENGTH_scan_expr = prove
 (`!ts loc xs. LENGTH (scan_expr ts loc xs) = LENGTH xs`,
  CHEAT_TAC);;
add_simp LENGTH_scan_expr;;

let scan_expr_SING = prove
 (`[HD (scan_expr ts loc [x])] = scan_expr ts loc [x]`,
  (REWRITE_TAC[CONJUNCT1 scan_expr_eq; HD]));;
add_simp scan_expr_SING;;

let scan_expr_HD_SING = prove
 (`HD (scan_expr ts loc [x]) = y <=> scan_expr ts loc [x] = [y]`,
  (REWRITE_TAC[CONJUNCT1 scan_expr_eq; HD; CONS_11]));;
add_simp scan_expr_HD_SING;;

let check_exp_SOME_simp = prove
 (`check_exp loc arity expr = SOME op <=>
     (?ts ty r.
       has_rec1 loc expr /\
       scan_expr (REPLICATE arity bvi_tailrec_Any) loc
         [expr] = [(ts,ty,r,SOME op)] /\
       ty = op_type op)`,
  CHEAT_TAC);;
add_simp check_exp_SOME_simp;;

(* --- Test rewriting --- *)

(* HOL4 bvi_tailrecScript.sml:860-865: the ML values that the definitions
   below antiquote *)

(* HOL4 bvi_tailrecScript.sml:867-873: the ML values that the definitions
   below antiquote *)

(* [local] *)
let fac_check_exp = prove
 (`check_exp 0 1 (bvi_Let [bvi_Op (clos_IntOp clos_LessEq) [bvi_Var 0; bvi_Op
  (clos_IntOp (clos_Const (&1))) []]]
    (bvi_If (bvi_Var 0)
       (bvi_Op (clos_IntOp (clos_Const (&1))) [])
       (bvi_Let [bvi_Op (clos_IntOp clos_Sub) [bvi_Op (clos_IntOp
         (clos_Const (&1))) []; bvi_Var 1]]
         (bvi_Op (clos_IntOp clos_Mult) [bvi_Var 2; bvi_Call 0 (SOME 0)
           [bvi_Var 0] NONE])))) = SOME bvi_tailrec_Times`,
  CHEAT_TAC);;

let fac_compile_exp = prove
 (`bvi_tailrec_compile_exp 0 1 1 (bvi_Let [bvi_Op (clos_IntOp clos_LessEq)
  [bvi_Var 0; bvi_Op (clos_IntOp (clos_Const (&1))) []]]
    (bvi_If (bvi_Var 0)
       (bvi_Op (clos_IntOp (clos_Const (&1))) [])
       (bvi_Let [bvi_Op (clos_IntOp clos_Sub) [bvi_Op (clos_IntOp
         (clos_Const (&1))) []; bvi_Var 1]]
         (bvi_Op (clos_IntOp clos_Mult) [bvi_Var 2; bvi_Call 0 (SOME 0)
           [bvi_Var 0] NONE])))) = SOME ((bvi_Let [bvi_Var 0; bvi_Op
           (clos_IntOp (clos_Const (&1))) []] (bvi_Let [bvi_Op (clos_IntOp
           clos_LessEq) [bvi_Var 0; bvi_Op (clos_IntOp (clos_Const (&1))) []]]
           (bvi_If (bvi_Var 0) (bvi_Op (clos_IntOp clos_Mult) [bvi_Var 2;
           bvi_Op (clos_IntOp (clos_Const (&1))) []])
        (bvi_Let [bvi_Op (clos_IntOp clos_Sub) [bvi_Op (clos_IntOp
          (clos_Const (&1))) []; bvi_Var 1]] (bvi_Call 0 (SOME 1) [bvi_Var 0;
          bvi_Op (clos_IntOp clos_Mult) [bvi_Var 3; bvi_Var 2]]
              NONE))))),(bvi_Let [bvi_Op (clos_IntOp clos_LessEq) [bvi_Var
                0; bvi_Op (clos_IntOp (clos_Const (&1))) []]] (bvi_If
                (bvi_Var 0) (bvi_Op (clos_IntOp clos_Mult) [bvi_Var 2; bvi_Op
                (clos_IntOp (clos_Const (&1))) []]) (bvi_Let [bvi_Op
                (clos_IntOp clos_Sub) [bvi_Op (clos_IntOp (clos_Const (&1)))
                []; bvi_Var 1]] (bvi_Call 0 (SOME 1) [bvi_Var 0; bvi_Op
                (clos_IntOp clos_Mult) [bvi_Var 3; bvi_Var 2]] NONE)))))`,
  CHEAT_TAC);;

(* HOL4 bvi_tailrecScript.sml:887-895: the ML values that the definitions
   below antiquote *)

(* HOL4 bvi_tailrecScript.sml:897-906: the ML values that the definitions
   below antiquote *)

(* HOL4 bvi_tailrecScript.sml:908: the ML values that the definitions below
   antiquote *)

(* [local] *)
let rev_check_exp = prove
 (`check_exp 444 1 (bvi_Let [bvi_Op (clos_IntOp (clos_Const (&0))) []]
     (bvi_If (bvi_Op (clos_BlockOp (clos_TagLenEq 0 0)) [bvi_Var 1])
         (bvi_Op (clos_BlockOp (clos_Cons 0)) [])
         (bvi_Let [bvi_Op (clos_MemOp clos_El) [bvi_Op (clos_IntOp
           (clos_Const (&0))) []; bvi_Var 1]]
           (bvi_Let [bvi_Op (clos_MemOp clos_El) [bvi_Op (clos_IntOp
             (clos_Const (&1))) []; bvi_Var 2]]
             (bvi_Op (clos_BlockOp clos_ListAppend)
               [bvi_Op (clos_BlockOp (clos_Cons 0)) [bvi_Op (clos_BlockOp
                 (clos_Cons 0)) []; bvi_Var 1];
                bvi_Call 0 (SOME 444) [bvi_Var 0] NONE]))))) = SOME
                  bvi_tailrec_Append`,
  CHEAT_TAC);;

(* [local] *)
let rev_compile_exp = prove
 (`bvi_tailrec_compile_exp 444 445 1 (bvi_Let [bvi_Op (clos_IntOp (clos_Const
  (&0))) []]
     (bvi_If (bvi_Op (clos_BlockOp (clos_TagLenEq 0 0)) [bvi_Var 1])
         (bvi_Op (clos_BlockOp (clos_Cons 0)) [])
         (bvi_Let [bvi_Op (clos_MemOp clos_El) [bvi_Op (clos_IntOp
           (clos_Const (&0))) []; bvi_Var 1]]
           (bvi_Let [bvi_Op (clos_MemOp clos_El) [bvi_Op (clos_IntOp
             (clos_Const (&1))) []; bvi_Var 2]]
             (bvi_Op (clos_BlockOp clos_ListAppend)
               [bvi_Op (clos_BlockOp (clos_Cons 0)) [bvi_Op (clos_BlockOp
                 (clos_Cons 0)) []; bvi_Var 1];
                bvi_Call 0 (SOME 444) [bvi_Var 0] NONE]))))) = SOME
                  ((bvi_Let [bvi_Var 0; bvi_Op (clos_BlockOp (clos_Cons 0)) []]
                  (bvi_Let [bvi_Op (clos_IntOp (clos_Const (&0))) []] (bvi_If
                  (bvi_Op (clos_BlockOp (clos_TagLenEq 0 0)) [bvi_Var 1])
                  (bvi_Op (clos_BlockOp clos_ListAppend) [bvi_Var 2; bvi_Op
                  (clos_BlockOp (clos_Cons 0)) []])
         (bvi_Let [bvi_Op (clos_MemOp clos_El) [bvi_Op (clos_IntOp
           (clos_Const (&0))) []; bvi_Var 1]]
           (bvi_Let [bvi_Op (clos_MemOp clos_El) [bvi_Op (clos_IntOp
             (clos_Const (&1))) []; bvi_Var 2]]
             (bvi_Call 0 (SOME 445) [bvi_Var 0; bvi_Op (clos_BlockOp
               clos_ListAppend) [bvi_Var 4; bvi_Op (clos_BlockOp (clos_Cons 0))
               [bvi_Op (clos_BlockOp (clos_Cons 0)) []; bvi_Var 1]]]
               NONE)))))),(bvi_Let [bvi_Op (clos_IntOp (clos_Const (&0)))
                 []] (bvi_If (bvi_Op (clos_BlockOp (clos_TagLenEq 0 0))
                 [bvi_Var 1]) (bvi_Op (clos_BlockOp clos_ListAppend) [bvi_Var
                 2; bvi_Op (clos_BlockOp (clos_Cons 0)) []]) (bvi_Let [bvi_Op
                 (clos_MemOp clos_El) [bvi_Op (clos_IntOp (clos_Const (&0)))
                 []; bvi_Var 1]] (bvi_Let [bvi_Op (clos_MemOp clos_El)
                 [bvi_Op (clos_IntOp (clos_Const (&1))) []; bvi_Var 2]]
                 (bvi_Call 0 (SOME 445) [bvi_Var 0; bvi_Op (clos_BlockOp
                 clos_ListAppend) [bvi_Var 4; bvi_Op (clos_BlockOp (clos_Cons
                 0)) [bvi_Op (clos_BlockOp (clos_Cons 0)) []; bvi_Var 1]]]
                 NONE))))))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["pmatch"];;

(* and the interface *)
let _ = unhide_overloads ();;
