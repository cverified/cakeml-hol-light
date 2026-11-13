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
needs "compiler/backend/closLang.ml";;
needs "lib/comparison.ml";;
needs "semantics/ast.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "bvi_tailrec"
  ["backend_common"; "bvi"];;

let _ = do_list hide_constant ["pmatch"];;

let dummy_def = new_definition
  `dummy = bvi_Var 1234567890`;;

(* HOL4 bvi_tailrecScript.sml:21-25: a theorem whose statement the
   port cannot state yet: MEM_exp_size_imp *)

let is_rec_def = new_definition
  `bvi_tailrec_is_rec name x2 =
        match x2 with
          bvi_Call _1 d _2 NONE -> d = SOME name
        | _3 -> F`;;
hol4_overload "is_rec" "bvi_tailrec_is_rec";;

let is_rec_PMATCH = prove
 (`!expr. bvi_tailrec_is_rec name expr =
    (match expr with
      Call _4 d _5 NONE -> d = SOME name | _6 -> F)`,
  CHEAT_TAC);;

let is_const_def = new_definition
  `bvi_tailrec_is_const x1 =
        match x1 with
          closLang_IntOp (closLang_Const i) -> small_enough_int i
        | _7 -> F`;;
hol4_overload "is_const" "bvi_tailrec_is_const";;

let is_const_PMATCH = prove
 (`!op. bvi_tailrec_is_const op =
    (match op with
      closLang_IntOp (closLang_Const i) -> small_enough_int i | _8
        -> F)`,
  CHEAT_TAC);;

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

let op_type_def = new_definition
  `op_type x1 =
      match x1 with
        (Append:assoc_op) -> List
      | bvi_tailrec_Noop -> bvi_tailrec_Any
      | _9 -> Int`;;

let to_op_def = define_cases
  [`to_op bvi_tailrec_Plus = closLang_IntOp closLang_Add`;
   `to_op bvi_tailrec_Times = closLang_IntOp closLang_Mult`;
   `to_op (Append:assoc_op) = closLang_BlockOp ListAppend`;
   `to_op bvi_tailrec_Noop = closLang_IntOp closLang_Mod`];;

let from_op_def = new_definition
  `from_op op =
     (if op = closLang_IntOp closLang_Add then bvi_tailrec_Plus
       else if op = closLang_IntOp closLang_Mult then
       bvi_tailrec_Times else if op = closLang_BlockOp ListAppend
       then Append else bvi_tailrec_Noop)`;;

let from_op_PMATCH = prove
 (`!op.
    from_op op =
      (match op with
        closLang_IntOp closLang_Add -> bvi_tailrec_Plus |
          closLang_IntOp closLang_Mult -> bvi_tailrec_Times |
          closLang_BlockOp ListAppend -> Append | _10 ->
          bvi_tailrec_Noop)`,
  CHEAT_TAC);;

(* HOL4 bvi_tailrecScript.sml:103-107: a theorem that HOL4 states as
   the value of an ML expression: from_op_thm *)

let op_eq_def = new_definition
  `op_eq x1 x2 =
        match (x1,x2) with
          (bvi_tailrec_Plus,(Op op xs:bvi_exp)) -> op =
            closLang_IntOp closLang_Add
        | (bvi_tailrec_Times,(Op op xs)) -> op = closLang_IntOp
          closLang_Mult
        | (Append,(Op op xs)) -> op = closLang_BlockOp ListAppend
        | (_11,_12) -> F`;;

let op_eq_PMATCH = prove
 (`!a expr.
     op_eq a expr =
       (match expr with
         Op op xs ->
           (match a with
             bvi_tailrec_Plus -> op = closLang_IntOp closLang_Add |
               bvi_tailrec_Times -> op = closLang_IntOp closLang_Mult
               | Append -> op = closLang_BlockOp ListAppend | _13 ->
               F) | _14 -> F)`,
  CHEAT_TAC);;

(* [simp] *)
let op_eq_to_op = prove
 (`!iop op xs.
      op_eq iop (Op op xs:bvi_exp) <=>
      op = to_op iop /\ ~(iop = bvi_tailrec_Noop)`,
  CHEAT_TAC);;

let apply_op_def = new_definition
  `apply_op op e1 e2 = Op (to_op op) [e1; e2]`;;

let id_from_op_def = define_cases
  [`id_from_op bvi_tailrec_Plus = bvi_Op (closLang_IntOp
  (closLang_Const (&0))) []`;
   `id_from_op bvi_tailrec_Times = bvi_Op (closLang_IntOp
  (closLang_Const (&1))) []`;
   `id_from_op (Append:assoc_op) = bvi_Op (closLang_BlockOp
  (closLang_Cons nil_tag)) []`;
   `id_from_op bvi_tailrec_Noop = dummy`];;

let index_of_def = new_definition
  `index_of x1 =
        match x1 with
          bvi_Var i -> SOME i
        | _15 -> NONE`;;

let index_of_PMATCH = prove
 (`!expr.
     index_of expr =
       (match expr with
         Var i -> SOME i | _16 -> NONE)`,
  CHEAT_TAC);;

let args_from_def = new_definition
  `args_from x1 =
        match x1 with
          bvi_Call t (SOME d) as hdl -> SOME (t,d,as,hdl)
        | _17 -> NONE`;;

let args_from_PMATCH = prove
 (`!expr.
     args_from expr =
       (match expr with
         Call t (SOME d) as hdl -> SOME (t,d,as,hdl) | _18 -> NONE)`,
  CHEAT_TAC);;

let get_bin_args_def = new_definition
  `get_bin_args op =
     (match op with bvi_Op _19 [e1; e2] -> SOME (e1,e2) | _20 ->
       NONE)`;;

let get_bin_args_PMATCH = prove
 (`!op.
     get_bin_args op =
       (match op with
         Op _21 [e1; e2] -> SOME (e1,e2) | _22 -> NONE)`,
  CHEAT_TAC);;

let exp_size_get_bin_args = prove
 (`!x x1 x2.
     get_bin_args x = SOME (x1,x2) ==>
       bvi_exp_size x1 + bvi_exp_size x2 < bvi_exp_size x`,
  CHEAT_TAC);;

let opbinargs_def = new_definition
  `opbinargs opr exp = (if ~(op_eq opr exp) then NONE else
  get_bin_args exp)`;;

let try_update_def = define_cases
  [`try_update vty NONE ts = ts`;
   `try_update vty (SOME n) ts =
        (if n < LENGTH ts then
          if EL n ts = bvi_tailrec_Any then
            TAKE n ts ++ [vty] ++ DROP (n + 1) ts else ts else
              ts)`];;

(* --- Checking termination guarantees --- *)

let is_arith_def = new_definition
  `is_arith op =
     (match op with
       closLang_IntOp closLang_Add -> T | closLang_IntOp
         closLang_Sub -> T | closLang_IntOp closLang_Mult -> T | _23
         -> F)`;;

let is_arith_PMATCH = prove
 (`!op.
     is_arith op =
       (match op with
         closLang_IntOp closLang_Add -> T | closLang_IntOp
           closLang_Sub -> T | closLang_IntOp closLang_Mult -> T | _24
           -> F)`,
  CHEAT_TAC);;

let is_rel_def = new_definition
  `is_rel op =
     (match op with
       closLang_IntOp closLang_Less -> T | closLang_IntOp
         closLang_LessEq -> T | closLang_IntOp Greater -> T |
         closLang_IntOp closLang_GreaterEq -> T | _25 -> F)`;;

let is_rel_PMATCH = prove
 (`!op.
     is_rel op =
       (match op with
         closLang_IntOp closLang_Less -> T | closLang_IntOp
           closLang_LessEq -> T | closLang_IntOp Greater -> T |
           closLang_IntOp closLang_GreaterEq -> T | _26 -> F)`,
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

let _ = size_thms "bvi_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 bvi_tailrecScript.sml:280-284: the tactic that proves the
   termination *)
let term_ok_int_def,term_ok_int_ind = define_wf
  `MEASURE (bvi_exp_size o SND)`
  [`term_ok_int ts expr =
     (match expr with
       Var i -> (if i < LENGTH ts then EL i ts = Int else F) | Op op
         xs ->
         (match get_bin_args expr with
           NONE -> xs = [] /\ bvi_tailrec_is_const op | SOME
             (x,y) -> is_arith op /\ term_ok_int ts x /\
             term_ok_int ts y) | _27 -> F)`];;

(* HOL4 bvi_tailrecScript.sml:286: a theorem that HOL4 states as the
   value of an ML expression: term_ok_int_ind *)

let _ = size_thms "bvi_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 bvi_tailrecScript.sml:303-307: the tactic that proves the
   termination *)
let term_ok_any_def,term_ok_any_ind = define_wf
  `MEASURE (bvi_exp_size o SND o SND)`
  [`term_ok_any ts list' expr =
        match expr with
          (Var i:bvi_exp) ->
       (if ~list' then i < LENGTH ts else if i < LENGTH ts then EL i
         ts = List else F)
        | (Op op xs) ->
       (match get_bin_args (Op op xs) with
         NONE -> xs = [] /\ (if list' then op = closLang_BlockOp
           (closLang_Cons 0) else bvi_tailrec_is_const op) | SOME (x,y)
           ->
           (if op = closLang_BlockOp ListAppend then term_ok_any ts
             T x /\ term_ok_any ts T y else if ~list' /\ is_arith op
             then term_ok_int ts x /\ term_ok_int ts y else if ~list'
             /\ is_rel op then term_ok_int ts x /\ term_ok_int ts y
             else if op = closLang_BlockOp (closLang_Cons 0) then
             term_ok_any ts T x /\ term_ok_any ts F y else F))
        | expr -> F`];;

let is_op_thms = prove
 (`~(is_arith (closLang_BlockOp (closLang_Cons 0))) /\ ~(is_arith
  (closLang_BlockOp ListAppend)) /\
   ~(is_rel (closLang_BlockOp (closLang_Cons 0))) /\ ~(is_rel
     (closLang_BlockOp ListAppend)) /\
   (!op. ~(op = closLang_BlockOp ListAppend) /\ is_arith op <=>
     is_arith op) /\
   (!op. ~(op = closLang_BlockOp ListAppend) /\ ~(is_arith op) /\
     is_rel op <=> is_rel op) /\
   (!op. ~(is_arith op) /\ ~(is_rel op) /\ op = closLang_BlockOp
     (closLang_Cons 0) <=> op = closLang_BlockOp (closLang_Cons 0)) /\
   (!op. ~(op = closLang_BlockOp ListAppend) /\ op =
     closLang_BlockOp (closLang_Cons 0) <=> op = closLang_BlockOp
     (closLang_Cons 0))`,
  CHEAT_TAC);;

(* HOL4 bvi_tailrecScript.sml:322: a theorem that HOL4 states as the
   value of an ML expression: term_ok_any_ind *)

(* HOL4 bvi_tailrecScript.sml:324-346: code that the source has in a
   comment *)

let term_ok_def = new_definition
  `term_ok ts ty expr =
     (match ty with
       bvi_tailrec_Any -> term_ok_any ts F expr | Int ->
         term_ok_int ts expr | List -> term_ok_any ts T expr)`;;

(* --- Simple tail checking before rewriting --- *)

(* Swap arguments when commutative *)
let try_swap_def = new_definition
  `try_swap loc opr exp =
        match opr with
          (Append:assoc_op) -> exp
        | opr ->
       (match opbinargs opr exp with
         NONE -> exp | SOME (l,r) ->
           (if bvi_tailrec_is_rec loc l then apply_op opr r l else
             exp))`;;

(* Check if ok to lift xs into accumulator *)
let check_op_def = new_definition
  `check_op ts opr loc exp =
     (match opbinargs opr (try_swap loc opr exp) with
       NONE -> NONE | SOME (xs,f) ->
         (if bvi_tailrec_is_rec loc f /\ term_ok ts (op_type opr) xs
           then
           SOME (apply_op opr xs f) else
           NONE))`;;

(* --- Type analysis --- *)

let decide_ty_def = new_definition
  `decide_ty x1 x2 =
        match (x1,x2) with
          ((Int:v_ty),(Int:v_ty)) -> Int
        | (List,List) -> List
        | (_28,_29) -> bvi_tailrec_Any`;;

let decide_ty_PMATCH = prove
 (`!ty1 ty2.
     decide_ty ty1 ty2 =
       (match (ty1,ty2) with
         (Int,Int) -> Int | (List,List) -> List | _30 ->
           bvi_tailrec_Any)`,
  CHEAT_TAC);;

let LAST1_def,LAST1_ind = define_guess
  [`LAST1 x1 =
      match x1 with
        [] -> NONE
      | [x] -> SOME x
      | (x :: xs) -> LAST1 xs`];;

let update_context_def = new_definition
  `update_context ty ts x1 x2 =
     try_update ty (index_of x2) (try_update ty (index_of x1) ts)`;;

let arg_ty_def = new_definition
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
      | _31 -> bvi_tailrec_Any`;;

let arg_ty_PMATCH = prove
 (`!op.
     arg_ty op =
       (match op with
         closLang_IntOp closLang_Add -> Int | closLang_IntOp
           closLang_Sub -> Int | closLang_IntOp closLang_Mult -> Int |
           closLang_IntOp closLang_Div -> Int | closLang_IntOp
           closLang_Mod -> Int | closLang_IntOp closLang_LessEq -> Int
           | closLang_IntOp closLang_Less -> Int | closLang_IntOp
           Greater -> Int | closLang_IntOp closLang_GreaterEq -> Int |
           closLang_IntOp (closLang_Const i) -> (if small_enough_int i
           then Int else bvi_tailrec_Any) | closLang_BlockOp
           ListAppend -> List | _32 -> bvi_tailrec_Any)`,
  CHEAT_TAC);;

let op_ty_def = new_definition
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
        | _33 -> bvi_tailrec_Any`;;

let op_ty_PMATCH = prove
 (`!op.
     op_ty op =
       (match op with
         closLang_IntOp closLang_Add -> Int | closLang_IntOp
           closLang_Sub -> Int | closLang_IntOp closLang_Mult -> Int |
           closLang_IntOp closLang_Div -> Int | closLang_IntOp
           closLang_Mod -> Int | closLang_BlockOp ListAppend -> List |
           closLang_BlockOp (closLang_Cons tag) -> (if tag = cons_tag
           \/ tag = nil_tag then List else bvi_tailrec_Any) |
           closLang_IntOp (closLang_Const i) -> (if small_enough_int i
           then Int else bvi_tailrec_Any) | _34 -> bvi_tailrec_Any)`,
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

let scan_expr_def,scan_expr_ind = define_rec
  [`scan_expr ts loc [] = []`;
   `scan_expr ts loc (x :: y :: xs) =
        (let (tx,ty,r,op) = HD (scan_expr ts loc [x]) in
          (tx,ty,r,op) :: scan_expr tx loc (y :: xs))`;
   `scan_expr ts loc [(Var n:bvi_exp)] =
        (let ty = (if n < LENGTH ts then EL n ts else
          bvi_tailrec_Any) in
          [(ts,ty,F,NONE)])`;
   `scan_expr ts loc [(If xi xt xe:bvi_exp)] =
        (let (ti,tyi,_43,oi) = HD (scan_expr ts loc [xi]) in
        let (tt,ty1,_44,ot) = HD (scan_expr ti loc [xt]) in
        let (te,ty2,_45,oe) = HD (scan_expr ti loc [xe]) in
        let op = (match ot with NONE -> oe | _46 -> ot) in
        let ty = (match op with
                   NONE -> decide_ty ty1 ty2 | SOME opr -> decide_ty
                     ty1 (decide_ty ty2 (op_type opr))) in
          [(MAP2 decide_ty tt te,ty,IS_SOME oe,op)])`;
   `scan_expr ts loc [(Let xs x:bvi_exp)] =
        (let ys = scan_expr ts loc xs in
        let tt = MAP (FST o SND) ys in
        let tr = (match LAST1 ys with SOME c -> FST c | NONE -> ts)
          in
        let (tu,ty,_49,op) = HD (scan_expr (tt ++ tr) loc [x]) in
          [(DROP (LENGTH ys) tu,ty,F,op)])`;
   `scan_expr ts loc [(Raise x:bvi_exp)] =
  [(ts,bvi_tailrec_Any,F,NONE)]`;
   `scan_expr ts loc [(Tick x:bvi_exp)] = scan_expr ts loc [x]`;
   `scan_expr ts loc [(Force _51 n:bvi_exp)] =
        (let ty = (if n < LENGTH ts then EL n ts else
          bvi_tailrec_Any) in
          [(ts,ty,F,NONE)])`;
   `scan_expr ts loc [(Call t d xs h:bvi_exp)] =
  [(ts,bvi_tailrec_Any,F,NONE)]`;
   `// multi-value calls/returns decline the tail-rec optimisation. TODO(multiret):
    // to optimise them, is_rec/has_rec/scan_expr/rewrite must recognise LetCall
    // self-calls and Return-based accumulation.
    scan_expr ts loc [(bvi_Return xs:bvi_exp)] =
      [(ts,bvi_tailrec_Any,F,NONE)]`;
   `scan_expr ts loc [bvi_LetCall rets t d xs y] =
  [(ts,bvi_tailrec_Any,F,NONE)]`;
   `scan_expr ts loc [(Op op xs:bvi_exp)] =
        (let opr = from_op op in
        let opt = op_type opr in
          match opr with
            bvi_tailrec_Noop ->
              // Constants?
              (if arg_ty op = Int then
                match get_bin_args (Op op xs) with
                  NONE ->
                    (if bvi_tailrec_is_const op then
                      [(ts,Int,F,NONE)] else
                      [(ts,bvi_tailrec_Any,F,NONE)]) | SOME (x,y) ->
                    (if ~(bvi_tailrec_is_const op) then
                      [(update_context Int ts x
                        y,bvi_tailrec_Any,F,NONE)] else
                      [(ts,bvi_tailrec_Any,F,NONE)]) else if op =
                        closLang_BlockOp (closLang_Cons 0) /\ xs = []
                        then
                [(
                  // list nil
                  ts,List,F,NONE)] else
                [(ts,bvi_tailrec_Any,F,NONE)]) | _54 ->
              // Things we can optimize
              (if IS_SOME (check_op ts opr loc (Op op xs)) then
                [(ts,opt,F,SOME opr)] else if term_ok ts opt (Op op
                  xs) then
                match get_bin_args (Op op xs) with
                  NONE -> [(ts,bvi_tailrec_Any,F,NONE)] | SOME (x,y)
                    ->
                    [(update_context opt ts x y,opt,F,NONE)] else
                [(ts,bvi_tailrec_Any,F,NONE)]))`];;

let scan_expr_sing_def = define_mutual_rec
  [`scan_expr_sing ts loc (Var n:bvi_exp) =
        (let ty = (if n < LENGTH ts then EL n ts else
          bvi_tailrec_Any) in
          (ts,ty,F,NONE))`;
   `scan_expr_sing ts loc (If xi xt xe:bvi_exp) =
        (let (ti,tyi,_63,oi) = scan_expr_sing ts loc xi in
        let (tt,ty1,_64,ot) = scan_expr_sing ti loc xt in
        let (te,ty2,_65,oe) = scan_expr_sing ti loc xe in
        let op = (match ot with NONE -> oe | _66 -> ot) in
        let ty = (match op with
                   NONE -> decide_ty ty1 ty2 | SOME opr -> decide_ty
                     ty1 (decide_ty ty2 (op_type opr))) in
          (MAP2 decide_ty tt te,ty,IS_SOME oe,op))`;
   `scan_expr_sing ts loc (Let xs x:bvi_exp) =
        (let ys = scan_expr_list ts loc xs in
        let tt = MAP (FST o SND) ys in
        let tr = (match LAST1 ys with SOME c -> FST c | NONE -> ts)
          in
        let (tu,ty,_69,op) = scan_expr_sing (tt ++ tr) loc x in
          (DROP (LENGTH ys) tu,ty,F,op))`;
   `scan_expr_sing ts loc (Raise x:bvi_exp) =
  (ts,bvi_tailrec_Any,F,NONE)`;
   `scan_expr_sing ts loc (Tick x:bvi_exp) = scan_expr_sing ts loc x`;
   `scan_expr_sing ts loc (Force _71 n:bvi_exp) =
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
              // Constants?
              (if arg_ty op = Int then
                match get_bin_args (Op op xs) with
                  NONE ->
                    (if bvi_tailrec_is_const op then
                      (ts,Int,F,NONE) else
                      (ts,bvi_tailrec_Any,F,NONE)) | SOME (x,y) ->
                    (if ~(bvi_tailrec_is_const op) then
                      (update_context Int ts x
                        y,bvi_tailrec_Any,F,NONE) else
                      (ts,bvi_tailrec_Any,F,NONE)) else if op =
                        closLang_BlockOp (closLang_Cons 0) /\ xs = []
                        then
                (
                 // list nil
                 ts,List,F,NONE) else
                (ts,bvi_tailrec_Any,F,NONE)) | _74 ->
              // Things we can optimize
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

let scan_expr_eq = prove
 (`(!e ts loc. scan_expr ts loc [e] = [scan_expr_sing ts loc e]) /\
   (!es ts loc. scan_expr ts loc es = scan_expr_list ts loc es)`,
  CHEAT_TAC);;

let push_call_def = new_definition
  `push_call n op acc exp x5 =
        match x5 with
          SOME (ticks,dest,args,handler) ->
       Call ticks (SOME n) (args ++ [apply_op op (Var acc) exp])
         handler
        | _75 -> dummy`;;

let rewrite_def,rewrite_ind = define_shaped_rec
  "match"
  [`rewrite loc next' opr acc ts exp =
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
       let tr = (match LAST1 ys with NONE -> ts | SOME c -> FST c)
         in
       let (r,y) = rewrite loc next' opr (acc + LENGTH xs) (tt ++
         tr) x in
         (r,Let xs y))
        | (Tick x) ->
       (let (r,y) = rewrite loc next' opr acc ts x in
         (r,Tick y))
        | (Force l v) -> (F,Force l v)
        | exp ->
       (match check_op ts opr loc exp with
         NONE -> (F,apply_op opr (Var acc) exp) | SOME exp ->
           (match opbinargs opr exp with
             NONE -> (F,apply_op opr (Var acc) exp) | SOME
               (xs,f) -> (T,push_call next' opr acc xs (args_from
               f))))`];;

let rewrite_PMATCH = prove
 (`!loc next' opr acc ts expr.
     rewrite loc next' opr acc ts expr =
       (match expr with
         Var n -> (F,Var n) | If x1 x2 x3 ->
           (let t1 = FST (HD (scan_expr ts loc [x1])) in
           let (r2,y2) = rewrite loc next' opr acc t1 x2 in
           let (r3,y3) = rewrite loc next' opr acc t1 x3 in
           let z2 = (if r2 then y2 else apply_op opr (Var acc) x2) in
           let z3 = (if r3 then y3 else apply_op opr (Var acc) x3) in
             ((r2 \/ r3),If x1 z2 z3)) | Let xs x ->
           (let ys = scan_expr ts loc xs in
           let tt = MAP (FST o SND) ys in
           let tr = (match LAST1 ys with NONE -> ts | SOME c -> FST
             c) in
           let (r,y) = rewrite loc next' opr (acc + LENGTH xs) (tt ++
             tr) x in
             (r,Let xs y)) | Tick x ->
           (let (r,y) = rewrite loc next' opr acc ts x in (r,Tick y))
             | Force l v -> (F,Force l v) | _76 ->
           (match check_op ts opr loc expr with
             NONE -> (F,apply_op opr (Var acc) expr) | SOME expr2 ->
             (match opbinargs opr expr2 with
               NONE -> (F,apply_op opr (Var acc) expr2) | SOME
                 (xs,f) -> (T,push_call next' opr acc xs (args_from
                 f)))))`,
  CHEAT_TAC);;

(* HOL4 bvi_tailrecScript.sml:694: a theorem that HOL4 states as the
   value of an ML expression: rewrite_eq *)


(* --- Top-level expression check --- *)

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let has_rec_def,has_rec_ind = define_rec
  [`has_rec loc x2 =
        match x2 with
          [] -> F
        | (x :: y :: xs) ->
       (if has_rec loc [x] then T else has_rec loc (y :: xs))
        | [(If x1 x2 x3:bvi_exp)] ->
       (if has_rec loc [x2] then T else has_rec loc [x3])
        | [Let xs x] -> has_rec loc [x]
        | [Tick x] -> has_rec loc [x]
        | [Op op xs] ->
       (if EXISTS (bvi_tailrec_is_rec loc) xs then T else has_rec
         loc xs)
        | [x] -> F`];;

let has_rec1_def = new_definition
  `has_rec1 loc x = has_rec loc [x]`;;

let has_rec_sing_def = define_mutual_rec
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

let has_rec_eq = prove
 (`(!e loc. has_rec loc [e] = has_rec_sing loc e) /\
   (!es loc. has_rec loc es = has_rec_list loc es)`,
  CHEAT_TAC);;

(* HOL4 bvi_tailrecScript.sml:744: the ML values that the definitions
   below antiquote *)
let has_rec_test1 = prove
 (`has_rec1 0 (Let [] (bvi_Call 0 (SOME 0) [] NONE):bvi_exp) <=> F`,
  CHEAT_TAC);;

(* HOL4 bvi_tailrecScript.sml:751: the ML values that the definitions
   below antiquote *)
let has_rec_test2 = prove
 (`has_rec1 0 (Op (closLang_IntOp closLang_Add) [Call 0 (SOME 0) []
  NONE; Var 0]:bvi_exp) <=> T`,
  CHEAT_TAC);;

let check_exp_def = new_definition
  `check_exp loc arity exp =
     (if ~(has_rec1 loc exp) then NONE else
       let context = REPLICATE arity bvi_tailrec_Any in
         match scan_expr context loc [exp] with
           [] -> NONE | (ts,ty,r,opr) :: _77 ->
             (match opr with
               NONE -> NONE | SOME op ->
                 (if ~(ty = op_type op) then NONE else opr)))`;;

(* HOL4 bvi_tailrecScript.sml:771-772: a theorem that HOL4 states as
   the value of an ML expression: check_exp_eq *)

let let_wrap_def = new_definition
  `let_wrap arity id' exp =
     Let ((GENLIST (\i. Var i) arity) ++ [id']) exp`;;

let mk_aux_call_def = new_definition
  `mk_aux_call loc arity id' =
     Call 0 (SOME loc) (id' :: GENLIST (\i. Var i) arity) NONE`;;

let bvi_tailrec_compile_exp_def = new_definition
  `bvi_tailrec_compile_exp loc next' arity exp =
     (match check_exp loc arity exp with
       NONE -> NONE | SOME op ->
       (let context = REPLICATE arity bvi_tailrec_Any in
       let (r,opt) = rewrite loc next' op arity context exp in
       let aux = let_wrap arity (id_from_op op) opt in
         SOME (aux,opt)))`;;
hol4_overload "compile_exp" "bvi_tailrec_compile_exp";;

let compile_each_def,compile_each_ind = define_rec
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

let bvi_tailrec_compile_prog_def = new_definition
  `bvi_tailrec_compile_prog do_it next' xs =
     (if do_it then bvi_tailrec_compile_each next' xs else
       (next',xs))`;;
hol4_overload "compile_prog" "bvi_tailrec_compile_prog";;

(* [simp] *)
let scan_expr_not_nil = prove
 (`!x. ~(scan_expr ts loc [x] = [])`,
  CHEAT_TAC);;

(* [simp] *)
let LENGTH_scan_expr = prove
 (`!ts loc xs. LENGTH (scan_expr ts loc xs) = LENGTH xs`,
  CHEAT_TAC);;

(* [simp] *)
let scan_expr_SING = prove
 (`[HD (scan_expr ts loc [x])] = scan_expr ts loc [x]`,
  CHEAT_TAC);;

(* [simp] *)
let scan_expr_HD_SING = prove
 (`HD (scan_expr ts loc [x]) = y <=> scan_expr ts loc [x] = [y]`,
  CHEAT_TAC);;

(* [simp] *)
let check_exp_SOME_simp = prove
 (`check_exp loc arity expr = SOME op <=>
     (?ts ty r.
       has_rec1 loc expr /\
       scan_expr (REPLICATE arity bvi_tailrec_Any) loc
         [expr] = [(ts,ty,r,SOME op)] /\
       ty = op_type op)`,
  CHEAT_TAC);;

(* --- Test rewriting --- *)

(* HOL4 bvi_tailrecScript.sml:860-865: the ML values that the
   definitions below antiquote *)

(* HOL4 bvi_tailrecScript.sml:867-873: the ML values that the
   definitions below antiquote *)

(* [local] *)
let fac_check_exp = prove
 (`check_exp 0 1 (Let [Op (closLang_IntOp closLang_LessEq) [Var 0; Op
  (closLang_IntOp (closLang_Const (&1))) []]]
    (bvi_If (bvi_Var 0)
       (bvi_Op (closLang_IntOp (closLang_Const (&1))) [])
       (bvi_Let [Op (closLang_IntOp closLang_Sub) [Op (closLang_IntOp
         (closLang_Const (&1))) []; Var 1]]
         (bvi_Op (closLang_IntOp closLang_Mult) [Var 2; Call 0
           (SOME 0) [Var 0] NONE]))):bvi_exp) = SOME bvi_tailrec_Times`,
  CHEAT_TAC);;

let fac_compile_exp = prove
 (`bvi_tailrec_compile_exp 0 1 1 (Let [Op (closLang_IntOp
  closLang_LessEq) [Var 0; Op (closLang_IntOp (closLang_Const (&1)))
  []]]
    (bvi_If (bvi_Var 0)
       (bvi_Op (closLang_IntOp (closLang_Const (&1))) [])
       (bvi_Let [Op (closLang_IntOp closLang_Sub) [Op (closLang_IntOp
         (closLang_Const (&1))) []; Var 1]]
         (bvi_Op (closLang_IntOp closLang_Mult) [Var 2; Call 0 (SOME
           0) [Var 0] NONE]))):bvi_exp) = SOME ((Let [Var 0; Op
           (closLang_IntOp (closLang_Const (&1))) []] (bvi_Let [Op
           (closLang_IntOp closLang_LessEq) [Var 0; Op (closLang_IntOp
           (closLang_Const (&1))) []]] (bvi_If (bvi_Var 0) (bvi_Op
           (closLang_IntOp closLang_Mult) [Var 2; Op (closLang_IntOp
           (closLang_Const (&1))) []])
        (bvi_Let [Op (closLang_IntOp closLang_Sub) [Op
          (closLang_IntOp (closLang_Const (&1))) []; Var 1]] (bvi_Call 0
          (SOME 1) [Var 0; Op (closLang_IntOp closLang_Mult) [Var 3; Var
          2]]
              NONE))))),(Let [Op (closLang_IntOp closLang_LessEq)
                [Var 0; Op (closLang_IntOp (closLang_Const (&1))) []]]
                (bvi_If (bvi_Var 0) (bvi_Op (closLang_IntOp
                closLang_Mult) [Var 2; Op (closLang_IntOp
                (closLang_Const (&1))) []]) (bvi_Let [Op
                (closLang_IntOp closLang_Sub) [Op (closLang_IntOp
                (closLang_Const (&1))) []; Var 1]] (bvi_Call 0 (SOME
                1) [Var 0; Op (closLang_IntOp closLang_Mult) [Var 3;
                Var 2]] NONE)))))`,
  CHEAT_TAC);;

(* HOL4 bvi_tailrecScript.sml:887-895: the ML values that the
   definitions below antiquote *)

(* HOL4 bvi_tailrecScript.sml:897-906: the ML values that the
   definitions below antiquote *)

(* HOL4 bvi_tailrecScript.sml:908: the ML values that the definitions
   below antiquote *)

(* [local] *)
let rev_check_exp = prove
 (`check_exp 444 1 (Let [Op (closLang_IntOp (closLang_Const (&0))) []]
     (bvi_If (bvi_Op (closLang_BlockOp (closLang_TagLenEq 0 0)) [Var
       1])
         (bvi_Op (closLang_BlockOp (closLang_Cons 0)) [])
         (bvi_Let [Op (closLang_MemOp closLang_El) [Op
           (closLang_IntOp (closLang_Const (&0))) []; Var 1]]
           (bvi_Let [Op (closLang_MemOp closLang_El) [Op
             (closLang_IntOp (closLang_Const (&1))) []; Var 2]]
             (bvi_Op (closLang_BlockOp ListAppend)
               [Op (closLang_BlockOp (closLang_Cons 0)) [Op
                 (closLang_BlockOp (closLang_Cons 0)) []; Var 1];
                Call 0 (SOME 444) [Var 0] NONE])))):bvi_exp) = SOME
                  Append`,
  CHEAT_TAC);;

(* [local] *)
let rev_compile_exp = prove
 (`bvi_tailrec_compile_exp 444 445 1 (Let [Op (closLang_IntOp
  (closLang_Const (&0))) []]
     (bvi_If (bvi_Op (closLang_BlockOp (closLang_TagLenEq 0 0)) [Var
       1])
         (bvi_Op (closLang_BlockOp (closLang_Cons 0)) [])
         (bvi_Let [Op (closLang_MemOp closLang_El) [Op
           (closLang_IntOp (closLang_Const (&0))) []; Var 1]]
           (bvi_Let [Op (closLang_MemOp closLang_El) [Op
             (closLang_IntOp (closLang_Const (&1))) []; Var 2]]
             (bvi_Op (closLang_BlockOp ListAppend)
               [Op (closLang_BlockOp (closLang_Cons 0)) [Op
                 (closLang_BlockOp (closLang_Cons 0)) []; Var 1];
                Call 0 (SOME 444) [Var 0] NONE])))):bvi_exp) = SOME
                  ((Let [Var 0; Op (closLang_BlockOp (closLang_Cons 0))
                  []] (bvi_Let [Op (closLang_IntOp (closLang_Const
                  (&0))) []] (bvi_If (bvi_Op (closLang_BlockOp
                  (closLang_TagLenEq 0 0)) [Var 1]) (bvi_Op
                  (closLang_BlockOp ListAppend) [Var 2; Op
                  (closLang_BlockOp (closLang_Cons 0)) []])
         (bvi_Let [Op (closLang_MemOp closLang_El) [Op
           (closLang_IntOp (closLang_Const (&0))) []; Var 1]]
           (bvi_Let [Op (closLang_MemOp closLang_El) [Op
             (closLang_IntOp (closLang_Const (&1))) []; Var 2]]
             (bvi_Call 0 (SOME 445) [Var 0; Op (closLang_BlockOp
               ListAppend) [Var 4; Op (closLang_BlockOp (closLang_Cons
               0)) [Op (closLang_BlockOp (closLang_Cons 0)) []; Var 1]]]
               NONE)))))),(Let [Op (closLang_IntOp (closLang_Const
                 (&0))) []] (bvi_If (bvi_Op (closLang_BlockOp
                 (closLang_TagLenEq 0 0)) [Var 1]) (bvi_Op
                 (closLang_BlockOp ListAppend) [Var 2; Op
                 (closLang_BlockOp (closLang_Cons 0)) []]) (bvi_Let
                 [Op (closLang_MemOp closLang_El) [Op (closLang_IntOp
                 (closLang_Const (&0))) []; Var 1]] (bvi_Let [Op
                 (closLang_MemOp closLang_El) [Op (closLang_IntOp
                 (closLang_Const (&1))) []; Var 2]] (bvi_Call 0 (SOME
                 445) [Var 0; Op (closLang_BlockOp ListAppend) [Var 4;
                 Op (closLang_BlockOp (closLang_Cons 0)) [Op
                 (closLang_BlockOp (closLang_Cons 0)) []; Var 1]]]
                 NONE))))))`,
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["pmatch"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
