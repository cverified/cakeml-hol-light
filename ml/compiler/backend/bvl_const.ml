(* ======================================================== *)
(*  bvl_const: ported from HOL4's
    compiler/backend/bvl_constScript.sml
    A definition theory, with 13 definitions and 12 theorems.
    Needed by 10 files of the port.  *)
(* ======================================================== *)

(*
   This is a BVL transformation that propagates simple and
   cheap-to-compute context-free expression from Let bindings. It also
   performs some simple constant folding with SmartOp (below).

   The most significant impact of this optimisation is that it removes
   each Var in a Let, i.e. Let [...; Var ...; ...] ..., and replaces
   them with constants Let [...; Op (IntOp (Const _)) []; ...] .... and
   replaces all occurrences of the bound var with a lookup to the
   original variable.

   bvi_let is a simpler version of this optimisation.
*)

needs "compiler/backend/bvl.ml";;
needs "compiler/backend/closLang.ml";;
needs "lib/comparison.ml";;
needs "semantics/ast.ml";;

let dest_simple_def = cake_define
  `dest_simple x1 =
        match x1 with
          bvl_Op (closLang_IntOp (closLang_Const i)) xs -> (if NULL
            xs then SOME i else NONE)
        | _1 -> NONE`;;

let case_op_const_def = cake_define
  `case_op_const exp =
       (match exp with (Op op [x1; Op (closLang_IntOp
         (closLang_Const n2)) l]) -> (if NULL l then SOME (op,x1,n2)
         else NONE) | _2 -> NONE)`;;

let SmartOp_flip_def = cake_define
  `SmartOp_flip op x1 x2 =
     (match (dest_simple x1) with (SOME i) ->
         (if MEM op [closLang_IntOp closLang_Add; closLang_IntOp
           closLang_Mult] then (op,x2,x1) else if op = closLang_IntOp
           closLang_Sub then (closLang_IntOp closLang_Add,x2,Op
           (closLang_IntOp (closLang_Const (--i))) []) else
           (op,x1,x2)) | _3 -> (op,x1,x2))`;;

let SmartOp2_def = cake_define
  `SmartOp2 (op,(x1:bvl_exp),(x2:bvl_exp)) =
     (let mk_add_const = (\x1 c2.
       if c2 = (&0) then x1 else Op (closLang_IntOp closLang_Add)
         [x1; Op (closLang_IntOp (closLang_Const c2)) []]) in
     let mk_add = (\x1 x2.
       let default = Op (closLang_IntOp closLang_Add) [x1; x2] in
         match (dest_simple x2) with (SOME n2) -> (
             match (case_op_const x1) with SOME (op,x11,n12) ->
                 (if op = closLang_IntOp closLang_Add then
                   mk_add_const x11 (n2 + n12) else if op =
                   closLang_IntOp closLang_Sub then Op (closLang_IntOp
                   closLang_Sub) [x11; Op (closLang_IntOp
                   (closLang_Const (n2 + n12))) []] else default) | _4
                   ->
                 (match (dest_simple x1) with SOME n1 -> Op
                   (closLang_IntOp (closLang_Const (n2 + n1))) [] | _5
                   -> mk_add_const x1 n2)) | _6 ->
             (match (case_op_const x1,case_op_const x2) with (SOME
               (op1,x11,n12),SOME (op2,x21,n22)) ->
                 (if op1 = closLang_IntOp closLang_Add /\ op2 =
                   closLang_IntOp closLang_Add then
                   mk_add_const (Op (closLang_IntOp closLang_Add)
                     [x11; x21]) (n22 + n12) else if op1 =
                     closLang_IntOp closLang_Add /\ op2 = closLang_IntOp
                     closLang_Sub then
                   Op (closLang_IntOp closLang_Sub) [Op
                     (closLang_IntOp closLang_Sub) [x11; x21]; Op
                     (closLang_IntOp (closLang_Const (n22 + n12))) []]
                     else if op1 = closLang_IntOp closLang_Sub /\ op2 =
                     closLang_IntOp closLang_Add then
                   mk_add_const (Op (closLang_IntOp closLang_Sub)
                     [x11; x21]) (n22 + n12) else default) | _7 ->
                     default)) in
     let mk_sub = (\x1 x2.
       let default = Op (closLang_IntOp closLang_Sub) [x1; x2] in
         match (dest_simple x2) with (SOME n2) -> (
             match (case_op_const x1) with SOME (op,x11,n12) ->
                 (if op = closLang_IntOp closLang_Add then Op
                   (closLang_IntOp closLang_Sub) [x11; Op
                   (closLang_IntOp (closLang_Const (n2 - n12))) []] else
                   if op = closLang_IntOp closLang_Sub then mk_add_const
                   x11 (n2 - n12) else default) | _8 ->
                 (match (dest_simple x1) with SOME n1 -> Op
                   (closLang_IntOp (closLang_Const (n2 - n1))) [] | _9
                   -> default)) | _10 ->
             (match (case_op_const x1,case_op_const x2) with (SOME
               (op1,x11,n12),SOME (op2,x21,n22)) ->
                 (if op1 = closLang_IntOp closLang_Add /\ op2 =
                   closLang_IntOp closLang_Add then
                   Op (closLang_IntOp closLang_Add) [Op
                     (closLang_IntOp closLang_Sub) [x11; x21]; Op
                     (closLang_IntOp (closLang_Const (n22 - n12))) []]
                     else if op1 = closLang_IntOp closLang_Add /\ op2 =
                     closLang_IntOp closLang_Sub then
                   Op (closLang_IntOp closLang_Sub) [Op
                     (closLang_IntOp closLang_Add) [x11; x21]; Op
                     (closLang_IntOp (closLang_Const (n22 - n12))) []]
                     else if op1 = closLang_IntOp closLang_Sub /\ op2 =
                     closLang_IntOp closLang_Add then
                   mk_add_const (Op (closLang_IntOp closLang_Add)
                     [x11; x21]) (n22 - n12) else default) | _11 ->
                     default)) in
     let mk_mul = (\x1 x2.
       let default = Op (closLang_IntOp closLang_Mult) [x1; x2] in
         match (dest_simple x2) with (SOME n2) -> (
             match (case_op_const x1) with SOME (op,x11,n12) ->
                 (if op = closLang_IntOp closLang_Mult then Op
                   (closLang_IntOp closLang_Mult) [x11; Op
                   (closLang_IntOp (closLang_Const (n2 * n12))) []] else
                   default) | _12 ->
                 (match (dest_simple x1) with SOME n1 -> Op
                   (closLang_IntOp (closLang_Const (n2 * n1))) [] | _13
                   ->
                     (if n2 = (&1) then x1 else if n2 = --(&1) then
                       mk_sub x1 (Op (closLang_IntOp (closLang_Const
                       (&0))) []) else default))) | _14 ->
             (match (case_op_const x1,case_op_const x2) with (SOME
               (op1,x11,n12),SOME (op2,x21,n22)) ->
                 (if op1 = closLang_IntOp closLang_Mult /\ op2 =
                   closLang_IntOp closLang_Mult then
                   Op (closLang_IntOp closLang_Mult) [Op
                     (closLang_IntOp (closLang_Const (n22 * n12))) [];
                     Op (closLang_IntOp closLang_Mult) [x11; x21]] else
                     default) | _15 -> default)) in
     let default = Op op [x1; x2] in
     if op = closLang_IntOp closLang_Add then
       mk_add x1 x2 else if op = closLang_IntOp closLang_Sub then
       mk_sub x1 x2 else if op = closLang_IntOp closLang_Mult then
       mk_mul x1 x2 else if MEM op [closLang_IntOp closLang_Div;
         closLang_IntOp closLang_Mod; closLang_IntOp closLang_Less;
         closLang_IntOp closLang_LessEq; closLang_IntOp Greater;
         closLang_IntOp closLang_GreaterEq] then
       match (dest_simple x1,dest_simple x2) with (SOME x1,SOME
         (x2:int)) ->
           (match op with closLang_IntOp closLang_Div -> (if x1 =
             (&0) then default else Op (closLang_IntOp (closLang_Const
             (x2 / x1))) []) | closLang_IntOp closLang_Mod -> (if x1 =
             (&0) then default else Op (closLang_IntOp (closLang_Const
             (x2 % x1))) []) | closLang_IntOp closLang_Less -> bvl_Bool
             (x2 < x1) | closLang_IntOp closLang_LessEq -> bvl_Bool (x2
             <= x1) | closLang_IntOp Greater -> bvl_Bool (x2 > x1) |
             closLang_IntOp closLang_GreaterEq -> bvl_Bool (x2 >= x1) |
             _16 -> default) | _17 -> default else if op =
             closLang_BlockOp closLang_Equal then
       match (dest_simple x1,dest_simple x2) with (SOME i,SOME j) ->
         bvl_Bool (j = i) | (SOME i,_18) -> Op (closLang_BlockOp
         (closLang_EqualConst (closLang_Int i))) [x2] | (_19,SOME i) ->
         Op (closLang_BlockOp (closLang_EqualConst (closLang_Int i)))
         [x1] | _20 -> default else if op = closLang_MemOp closLang_El
         then
       match dest_simple x1 with SOME i -> (if i < (&0) then
         default else Op (closLang_BlockOp (closLang_ElemAt
         (num_of_int i))) [x2]) | _21 -> default else default)`;;

(* NOTE: the space after case and pmatch is important *)
(* HOL4 bvl_constScript.sml:196-198: ML code, not ported *)
(* HOL4 bvl_constScript.sml:206: ML code, not ported *)


let dest_EqualInt_def = cake_define
  `dest_EqualInt x1 =
      match x1 with
        closLang_BlockOp (closLang_EqualConst (closLang_Int i)) ->
          SOME i
      | _22 -> NONE`;;

let SmartOp1_def = cake_define
  `SmartOp1 op x =
     (match dest_EqualInt op with NONE -> Op op [x] | SOME i ->
       (match dest_simple x with NONE -> Op op [x] | SOME j ->
         bvl_Bool (j = i)))`;;


let SmartOp_def = cake_define
  `bvl_const_SmartOp op xs =
     (match xs with [x1; x2] -> SmartOp2 (SmartOp_flip op x1 x2) |
       [x] -> SmartOp1 op x | _23 -> Op op xs)`;;
hol4_overload "SmartOp" "bvl_const_SmartOp";;

let extract_def = cake_define
  `bvl_const_extract x1 ys =
        match x1 with
          ((Var n):bvl_exp) -> SOME ((Var (n + LENGTH ys +
            1)):bvl_exp)
        | (Op (closLang_IntOp (closLang_Const i)) xs) -> SOME (Op
          (closLang_IntOp (closLang_Const i)) [])
        | (Op (closLang_BlockOp (closLang_Cons t)) xs) ->
       (if NULL xs then SOME (Op (closLang_BlockOp (closLang_Cons t))
         []) else NONE)
        | _24 -> NONE`;;
hol4_overload "extract" "bvl_const_extract";;

let extract_list_def = cake_define_list
  [`bvl_const_extract_list [] = []`;
   `bvl_const_extract_list (x :: xs) = extract x xs ::
  bvl_const_extract_list xs`];;
hol4_overload "extract_list" "bvl_const_extract_list";;

let delete_var_def = cake_define
  `bvl_const_delete_var x =
        match x with
          ((Var n):bvl_exp) -> Op (closLang_IntOp (closLang_Const
            (&0))) []
        | x -> x`;;
hol4_overload "delete_var" "bvl_const_delete_var";;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let compile_def = cake_define_list_cheat CHEAT_TAC
  [`bvl_const_compile env [] = []`;
   `bvl_const_compile env (x :: y :: xs) = bvl_const_compile env [x]
  ++ bvl_const_compile env (y :: xs)`;
   `bvl_const_compile env [(Var v:bvl_exp)] =
         (match (\l n. oEL n l) env v with NONE -> [Var v] | SOME
           NONE -> [Var v] | SOME (SOME (Var i)) -> [Var (v + i)] |
           SOME (SOME x) -> [x])`;
   `bvl_const_compile env [(If x1 x2 x3:bvl_exp)] =
         (let y1 = HD (bvl_const_compile env [x1]) in
         let y2 = HD (bvl_const_compile env [x2]) in
         let y3 = HD (bvl_const_compile env [x3]) in
           if y1 = bvl_Bool T then [y2] else
           if y1 = bvl_Bool F then [y3] else
             [If y1 y2 y3])`;
   `bvl_const_compile env [(Let xs x2:bvl_exp)] =
         (let ys = bvl_const_compile env xs in
           [Let (MAP bvl_const_delete_var ys)
                (HD (bvl_const_compile (bvl_const_extract_list ys
                  ++ env) [x2]))])`;
   `bvl_const_compile env [(Handle x1 x2:bvl_exp)] =
         [Handle (HD (bvl_const_compile env [x1])) (HD
           (bvl_const_compile (NONE :: env) [x2]))]`;
   `bvl_const_compile env [(Raise x1:bvl_exp)] =
         [Raise (HD (bvl_const_compile env [x1]))]`;
   `bvl_const_compile env [(Op op xs:bvl_exp)] = [bvl_const_SmartOp
  op (bvl_const_compile env xs)]`;
   `bvl_const_compile env [(Tick x:bvl_exp)] = [Tick (HD
  (bvl_const_compile env [x]))]`;
   `bvl_const_compile env [(Force loc v:bvl_exp)] =
         (match (\l n. oEL n l) env v with NONE -> [Force loc v]
           | SOME NONE -> [Force loc v] | SOME (SOME (Var i)) ->
           [Force loc (v + i)] | SOME (SOME x) -> [Force loc v])`;
   `bvl_const_compile env [(Call t dest xs:bvl_exp)] = [Call t dest
  (bvl_const_compile env xs)]`];;
hol4_overload "compile" "bvl_const_compile";;

let compile_sing_def = cake_define_list
  [`bvl_const_compile_sing env (Var v:bvl_exp) =
         (match (\l n. oEL n l) env v with NONE -> Var v | SOME
           NONE -> Var v | SOME (SOME (Var i)) -> Var (v + i) | SOME
           (SOME x) -> x)`;
   `bvl_const_compile_sing env (If x1 x2 x3:bvl_exp) =
         (let y1 = bvl_const_compile_sing env x1 in
         let y2 = bvl_const_compile_sing env x2 in
         let y3 = bvl_const_compile_sing env x3 in
           if y1 = bvl_Bool T then y2 else
           if y1 = bvl_Bool F then y3 else
             If y1 y2 y3)`;
   `bvl_const_compile_sing env (Let xs x2:bvl_exp) =
         (let ys = bvl_const_compile_list env xs in
           Let (MAP bvl_const_delete_var ys)
               (bvl_const_compile_sing (bvl_const_extract_list ys
                 ++ env) x2))`;
   `bvl_const_compile_sing env (Handle x1 x2:bvl_exp) =
         Handle (bvl_const_compile_sing env x1)
           (bvl_const_compile_sing (NONE :: env) x2)`;
   `bvl_const_compile_sing env (Raise x1:bvl_exp) =
         Raise (bvl_const_compile_sing env x1)`;
   `bvl_const_compile_sing env (Op op xs:bvl_exp) = bvl_const_SmartOp
  op (bvl_const_compile_list env xs)`;
   `bvl_const_compile_sing env (Tick x:bvl_exp) = Tick
  (bvl_const_compile_sing env x)`;
   `bvl_const_compile_sing env (Force loc v:bvl_exp) =
         (match (\l n. oEL n l) env v with NONE -> Force loc v |
           SOME NONE -> Force loc v | SOME (SOME (Var i)) -> Force
           loc (v + i) | SOME (SOME x) -> Force loc v)`;
   `bvl_const_compile_sing env (Call t dest xs:bvl_exp) = Call t dest
  (bvl_const_compile_list env xs)`;
   `bvl_const_compile_list env [] = []`;
   `bvl_const_compile_list env (x :: xs) = bvl_const_compile_sing
  env x :: bvl_const_compile_list env xs`];;
hol4_overload "compile_list" "bvl_const_compile_list";;
hol4_overload "compile_sing" "bvl_const_compile_sing";;

let compile_exp_def = cake_define
  `bvl_const_compile_exp x =
     (match bvl_const_compile [] [x] with (y :: _25) -> y | _26 ->
       Var 0)`;;
hol4_overload "compile_exp" "bvl_const_compile_exp";;
