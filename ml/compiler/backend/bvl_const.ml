(* ======================================================== *)
(*  bvl_const: ported from HOL4's
    compiler/backend/bvl_constScript.sml
    A definition theory, with 13 definitions and 12 theorems.
    Needed by 11 files of the port.  *)
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
needs "lib/set_sep.ml";;
needs "semantics/ast.ml";;

let _ = do_list hide_constant ["pmatch"];;

let dest_simple_def = cake_define
  `dest_simple x1 =
        match x1 with
          bvl_Op (closLang_IntOp (closLang_Const i)) xs -> (if NULL
            xs then SOME i else NONE)
        | _1 -> NONE`;;

let dest_simple_pmatch = prove
 (`!op. dest_simple op =
   (match op with
     bvl_Op (closLang_IntOp (closLang_Const i)) [] -> SOME i | _2
       -> NONE)`,
  (* HOL4's pmatch is the match of HOL Light as well, so the two
     sides differ in one thing only: the pattern of the source
     matches any list and asks NULL of it, and this one matches the
     empty list.  The case split on the expression decides both *)
  (GEN_TAC THEN REWRITE_TAC[dest_simple_def] THEN
   EVERY_CASE_TAC THEN REWRITE_TAC[NULL]));;

let case_op_const_def = cake_define
  `case_op_const exp =
       (match exp with (Op op [x1; Op (closLang_IntOp
         (closLang_Const n2)) l]) -> (if NULL l then SOME (op,x1,n2)
         else NONE) | _3 -> NONE)`;;

let case_op_const_pmatch = prove
 (`!exp. case_op_const exp =
   (match exp with (Op op [x1; Op (closLang_IntOp (closLang_Const
     n2)) []]) -> SOME (op,x1,n2) | _4 -> NONE)`,
  (GEN_TAC THEN REWRITE_TAC[case_op_const_def] THEN
   EVERY_CASE_TAC THEN REWRITE_TAC[NULL]));;

let SmartOp_flip_def = cake_define
  `SmartOp_flip op x1 x2 =
     (match (dest_simple x1) with (SOME i) ->
         (if MEM op [closLang_IntOp closLang_Add; closLang_IntOp
           closLang_Mult] then (op,x2,x1) else if op = closLang_IntOp
           closLang_Sub then (closLang_IntOp closLang_Add,x2,Op
           (closLang_IntOp (closLang_Const (--i))) []) else
           (op,x1,x2)) | _5 -> (op,x1,x2))`;;

let SmartOp_flip_pmatch = prove
 (`!op x1 x2. SmartOp_flip op x1 x2 =
     (match (dest_simple x1) with (SOME i) ->
         (if MEM op [closLang_IntOp closLang_Add; closLang_IntOp
           closLang_Mult] then (op,x2,x1) else if op = closLang_IntOp
           closLang_Sub then (closLang_IntOp closLang_Add,x2,Op
           (closLang_IntOp (closLang_Const (--i))) []) else
           (op,x1,x2)) | _6 -> (op,x1,x2))`,
  (* this one has no NULL in it, so the two sides are the same
     term and the definition is the whole proof *)
  (REPEAT GEN_TAC THEN REWRITE_TAC[SmartOp_flip_def]));;

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
                   (closLang_Const (n2 + n12))) []] else default) | _7
                   ->
                 (match (dest_simple x1) with SOME n1 -> Op
                   (closLang_IntOp (closLang_Const (n2 + n1))) [] | _8
                   -> mk_add_const x1 n2)) | _9 ->
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
                     [x11; x21]) (n22 + n12) else default) | _10 ->
                     default)) in
     let mk_sub = (\x1 x2.
       let default = Op (closLang_IntOp closLang_Sub) [x1; x2] in
         match (dest_simple x2) with (SOME n2) -> (
             match (case_op_const x1) with SOME (op,x11,n12) ->
                 (if op = closLang_IntOp closLang_Add then Op
                   (closLang_IntOp closLang_Sub) [x11; Op
                   (closLang_IntOp (closLang_Const (n2 - n12))) []] else
                   if op = closLang_IntOp closLang_Sub then mk_add_const
                   x11 (n2 - n12) else default) | _11 ->
                 (match (dest_simple x1) with SOME n1 -> Op
                   (closLang_IntOp (closLang_Const (n2 - n1))) [] | _12
                   -> default)) | _13 ->
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
                     [x11; x21]) (n22 - n12) else default) | _14 ->
                     default)) in
     let mk_mul = (\x1 x2.
       let default = Op (closLang_IntOp closLang_Mult) [x1; x2] in
         match (dest_simple x2) with (SOME n2) -> (
             match (case_op_const x1) with SOME (op,x11,n12) ->
                 (if op = closLang_IntOp closLang_Mult then Op
                   (closLang_IntOp closLang_Mult) [x11; Op
                   (closLang_IntOp (closLang_Const (n2 * n12))) []] else
                   default) | _15 ->
                 (match (dest_simple x1) with SOME n1 -> Op
                   (closLang_IntOp (closLang_Const (n2 * n1))) [] | _16
                   ->
                     (if n2 = (&1) then x1 else if n2 = --(&1) then
                       mk_sub x1 (Op (closLang_IntOp (closLang_Const
                       (&0))) []) else default))) | _17 ->
             (match (case_op_const x1,case_op_const x2) with (SOME
               (op1,x11,n12),SOME (op2,x21,n22)) ->
                 (if op1 = closLang_IntOp closLang_Mult /\ op2 =
                   closLang_IntOp closLang_Mult then
                   Op (closLang_IntOp closLang_Mult) [Op
                     (closLang_IntOp (closLang_Const (n22 * n12))) [];
                     Op (closLang_IntOp closLang_Mult) [x11; x21]] else
                     default) | _18 -> default)) in
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
             _19 -> default) | _20 -> default else if op =
             closLang_BlockOp closLang_Equal then
       match (dest_simple x1,dest_simple x2) with (SOME i,SOME j) ->
         bvl_Bool (j = i) | (SOME i,_21) -> Op (closLang_BlockOp
         (closLang_EqualConst (closLang_Int i))) [x2] | (_22,SOME i) ->
         Op (closLang_BlockOp (closLang_EqualConst (closLang_Int i)))
         [x1] | _23 -> default else if op = closLang_MemOp closLang_El
         then
       match dest_simple x1 with SOME i -> (if i < (&0) then
         default else Op (closLang_BlockOp (closLang_ElemAt
         (num_of_int i))) [x2]) | _24 -> default else default)`;;

(* NOTE: the space after case and pmatch is important *)
(* HOL4 bvl_constScript.sml:196-198: ML code, not ported *)

(* HOL4 bvl_constScript.sml:200-205: a theorem whose statement the
   port cannot state yet: SmartOp2_pmatch *)
(* HOL4 bvl_constScript.sml:206: ML code, not ported *)


let dest_EqualInt_def = cake_define
  `dest_EqualInt x1 =
      match x1 with
        closLang_BlockOp (closLang_EqualConst (closLang_Int i)) ->
          SOME i
      | _25 -> NONE`;;

let dest_EqualInt_pmatch = prove
 (`dest_EqualInt x = (match x with closLang_BlockOp
  (closLang_EqualConst (closLang_Int i)) -> SOME i | _26 -> NONE)`,
  (REWRITE_TAC[dest_EqualInt_def]));;

let SmartOp1_def = cake_define
  `SmartOp1 op x =
     (match dest_EqualInt op with NONE -> Op op [x] | SOME i ->
       (match dest_simple x with NONE -> Op op [x] | SOME j ->
         bvl_Bool (j = i)))`;;


let SmartOp_def = cake_define
  `bvl_const_SmartOp op xs =
     (match xs with [x1; x2] -> SmartOp2 (SmartOp_flip op x1 x2) |
       [x] -> SmartOp1 op x | _27 -> Op op xs)`;;
hol4_overload "SmartOp" "bvl_const_SmartOp";;

let SmartOp_pmatch = prove
 (`!op xs. bvl_const_SmartOp op xs =
   (match xs with [x1; x2] -> SmartOp2 (SmartOp_flip op x1 x2) |
     [x] -> SmartOp1 op x | _28 -> Op op xs)`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[SmartOp_def]));;

let bvl_const_extract_def = cake_define
  `bvl_const_extract x1 ys =
        match x1 with
          ((Var n):bvl_exp) -> SOME ((Var (n + LENGTH ys +
            1)):bvl_exp)
        | (Op (closLang_IntOp (closLang_Const i)) xs) -> SOME (Op
          (closLang_IntOp (closLang_Const i)) [])
        | (Op (closLang_BlockOp (closLang_Cons t)) xs) ->
       (if NULL xs then SOME (Op (closLang_BlockOp (closLang_Cons t))
         []) else NONE)
        | _29 -> NONE`;;
hol4_overload "extract" "bvl_const_extract";;

let extract_pmatch = prove
 (`!op ys. extract op ys =
   (match op with
     ((Var n):bvl_exp) -> SOME ((Var (n + LENGTH ys + 1)):bvl_exp)
       | Op (closLang_IntOp (closLang_Const i)) xs -> SOME (Op
       (closLang_IntOp (closLang_Const i)) []) | Op (closLang_BlockOp
       (closLang_Cons t)) [] -> SOME (Op (closLang_BlockOp
       (closLang_Cons t)) []) | _30 -> NONE)`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[bvl_const_extract_def] THEN
   EVERY_CASE_TAC THEN REWRITE_TAC[NULL]));;

let bvl_const_extract_list_def = cake_define_list
  [`bvl_const_extract_list [] = []`;
   `bvl_const_extract_list (x :: xs) = extract x xs ::
  bvl_const_extract_list xs`];;
hol4_overload "extract_list" "bvl_const_extract_list";;

let bvl_const_delete_var_def = cake_define
  `bvl_const_delete_var x =
        match x with
          ((Var n):bvl_exp) -> Op (closLang_IntOp (closLang_Const
            (&0))) []
        | x -> x`;;
hol4_overload "delete_var" "bvl_const_delete_var";;

let delete_var_pmatch = prove
 (`!op.
   bvl_const_delete_var op =
     (match op with
       Var n -> Op (closLang_IntOp (closLang_Const (&0))) [] | x ->
         x)`,
  (GEN_TAC THEN REWRITE_TAC[bvl_const_delete_var_def]));;

let _ = size_thms "bvl_exp";;
(* the termination relation is not in the HOL4 source *)
(* the port proves the termination with that relation, which
   define_single takes as it stands: the strategies that
   cake_define_gen tries before it declare the constant and
   leave it no chance (a minute, which is what this costs) *)
let bvl_const_compile_def =
  let th = end_itlist CONJ (fst (define_single
    [(`MEASURE (list_size bvl_exp_size o SND)`,
      TERM_TAC)]
    (cake_conj_list
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
  (bvl_const_compile env xs)]`]))) in
  (note_dest_fact th; cake_note_def th; th);;
hol4_overload "compile" "bvl_const_compile";;

let bvl_const_compile_sing_def = cake_define_list
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

let compile_eq = prove
 (`(!e env. bvl_const_compile env [e] = [bvl_const_compile_sing env e])
  /\
   (!es env. bvl_const_compile env es = bvl_const_compile_list env
     es)`,
  (let cp = bvl_const_compile_def in
   let cs = bvl_const_compile_sing_def in
   let sz = size_thms "bvl_exp" in
   (* HOL4 does this induction on the structure of an expression
      (Induct), which is an induction over the two types of the
      family at once; HOL Light's define keeps no such theorem, so
      the induction is on the measure the definition was made with
      -- here a mutual one, over the size of an expression and over
      the size of a list of them -- and every use of the hypothesis
      leaves a side condition *)
   let compile_CONS = prove
    (`!n x xs. bvl_const_compile n (CONS x xs) =
               APPEND (bvl_const_compile n [x])
                      (bvl_const_compile n xs)`,
     REPEAT GEN_TAC THEN
     STRUCT_CASES_TAC(ISPEC `xs:bvl_exp list` list_CASES) THEN
     REWRITE_TAC[cp; APPEND_NIL]) in
   (* no expression has size 0, which is what the base case says *)
   let size_pos = prove
    (`!e:bvl_exp. 1 <= bvl_exp_size e`,
     GEN_TAC THEN
     STRUCT_CASES_TAC(ISPEC `e:bvl_exp` (cases_of `:bvl_exp`)) THEN
     REWRITE_TAC sz THEN ARITH_TAC) in
   let size_tac =
     RULE_ASSUM_TAC(REWRITE_RULE(list_size :: sz)) THEN
     REWRITE_TAC(list_size :: sz) THEN ASM_ARITH_TAC in
   let cond1 t =
     mk_binop `(<=):num->num->bool`
       (list_mk_icomb "bvl_exp_size" [t]) `k:num` in
   let cond2 t =
     mk_binop `(<=):num->num->bool`
       (list_mk_icomb "list_size" [`bvl_exp_size`; t]) `k:num` in
   let use1_by tac t =
     SUBGOAL_THEN (cond1 t)
       (fun c -> FIRST_ASSUM(fun ih ->
          REWRITE_TAC[MATCH_MP (CONJUNCT1 ih) c])) THEN TRY tac in
   let use2_by tac t =
     SUBGOAL_THEN (cond2 t)
       (fun c -> FIRST_ASSUM(fun ih ->
          REWRITE_TAC[MATCH_MP (CONJUNCT2 ih) c])) THEN TRY tac in
   let use1 = use1_by size_tac in
   let use2 = use2_by size_tac in
   let both = REWRITE_TAC[cp; cs] in
   (* Var and Force read the environment, so both sides have the
      same match on it *)
   let match_case =
     REWRITE_TAC[cp; cs] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     EVERY_CASE_TAC THEN REWRITE_TAC[] in
   (* the If folds the condition away when it compiled to a
      constant, and the list of one is inside the branches on one
      side of the equation and outside them on the other, so the
      two tests are decided before the sides are compared *)
   let sing_if_case =
     REWRITE_TAC[cp; cs; LET_DEF; LET_END_DEF] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     use1 `x1:bvl_exp` THEN use1 `x2:bvl_exp` THEN
     use1 `x3:bvl_exp` THEN REWRITE_TAC[HD] THEN
     ASM_CASES_TAC `bvl_const_compile_sing env x1 = bvl_Bool T` THEN
     ASM_REWRITE_TAC[] THEN
     ASM_CASES_TAC `bvl_const_compile_sing env x1 = bvl_Bool F` THEN
     ASM_REWRITE_TAC[] in
   (* the Let compiles its body in an environment that the compiled
      bindings build, which the hypothesis is quantified over *)
   let sing_let_case =
     REWRITE_TAC[cp; cs; LET_DEF; LET_END_DEF] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     use2 `xs:bvl_exp list` THEN use1 `x2:bvl_exp` THEN
     REWRITE_TAC[HD] in
   let part1 =
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     NAMED_CASES_TAC `e:bvl_exp`
       [["v"]; ["x1"; "x2"; "x3"]; ["xs"; "x2"]; ["x1"];
        ["x1"; "x2"]; ["x1"]; ["tt"; "dd"; "gs"]; ["loc"; "fv"];
        ["op"; "os"]] THENL
     [match_case;
      sing_if_case;
      sing_let_case;
      both THEN use1 `x1:bvl_exp` THEN REWRITE_TAC[HD];
      both THEN use1 `x1:bvl_exp` THEN use1 `x2:bvl_exp` THEN
      REWRITE_TAC[HD];
      both THEN use1 `x1:bvl_exp` THEN REWRITE_TAC[HD];
      both THEN use2 `gs:bvl_exp list` THEN REWRITE_TAC[];
      match_case;
      both THEN use2 `os:bvl_exp list` THEN REWRITE_TAC[]] in
   (* and the list, where compile takes the head apart with the
      clause for two or more and compile_list with its own *)
   let part2 =
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     NAMED_CASES_TAC `es:bvl_exp list` [[]; ["y"; "ys"]] THENL
     [REWRITE_TAC[cp; cs];
      REWRITE_TAC[cs] THEN ONCE_REWRITE_TAC[compile_CONS] THEN
      use1 `y:bvl_exp` THEN use2 `ys:bvl_exp list` THEN
      REWRITE_TAC[APPEND]] in
   let sing_base =
     CONJ_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `F` CONTR_TAC THEN
      MP_TAC(ISPEC `e:bvl_exp` size_pos) THEN ASM_ARITH_TAC;
      REPEAT GEN_TAC THEN DISCH_TAC THEN
      NAMED_CASES_TAC `es:bvl_exp list` [[]; ["y"; "ys"]] THENL
      [REWRITE_TAC[cp; cs];
       FIRST_ASSUM MP_TAC THEN
       REWRITE_TAC[list_size; ARITH_RULE `~(1 + a + b <= 0)`]]] in
   SUBGOAL_THEN
     `!k. (!env e. bvl_exp_size e <= k ==>
             bvl_const_compile env [e] =
             [bvl_const_compile_sing env e]) /\
          (!env es. list_size bvl_exp_size es <= k ==>
             bvl_const_compile env es =
             bvl_const_compile_list env es)`
     (fun th -> CONJ_TAC THEN REPEAT GEN_TAC THENL
        [MP_TAC(CONJUNCT1(SPEC `bvl_exp_size (e:bvl_exp)` th));
         MP_TAC(CONJUNCT2
                  (SPEC `list_size bvl_exp_size (es:bvl_exp list)`
                     th))]
        THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL]) THEN
   INDUCT_TAC THENL
   [sing_base; CONJ_TAC THENL [part1; part2]]));;

(* compile_length[simp] *)
let bvl_const_compile_length = prove
 (`!n xs. LENGTH (bvl_const_compile n xs) = LENGTH xs`,
  (let cp = bvl_const_compile_def in
   let sz = size_thms "bvl_exp" in
   (* HOL4 takes the induction theorem that its termination proof
      left behind (HO_MATCH_MP_TAC compile_ind); the port induces on
      the measure the definition was made with *)
   let cond t =
     mk_binop `(<=):num->num->bool`
       (list_mk_icomb "list_size" [`bvl_exp_size`; t]) `k:num` in
   let size_tac =
     RULE_ASSUM_TAC(REWRITE_RULE(list_size :: sz)) THEN
     REWRITE_TAC(list_size :: sz) THEN ASM_ARITH_TAC in
   let use_ih t =
     SUBGOAL_THEN (cond t)
       (fun c -> FIRST_ASSUM(fun ih -> REWRITE_TAC[MATCH_MP ih c]))
     THEN TRY size_tac in
   (* every clause but the empty list and the list of two or more
      makes a list of one, so only that clause uses the hypothesis *)
   let one = REWRITE_TAC[cp; LENGTH] in
   let sing_case =
     REWRITE_TAC[cp] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     EVERY_CASE_TAC THEN REWRITE_TAC[LENGTH] in
   let if_case =
     REWRITE_TAC[cp; LET_DEF; LET_END_DEF] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     REPEAT COND_CASES_TAC THEN REWRITE_TAC[LENGTH] in
   let let_case =
     REWRITE_TAC[cp; LET_DEF; LET_END_DEF] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[LENGTH] in
   let single_case =
     NAMED_CASES_TAC `x1:bvl_exp`
       [["v"]; ["e1"; "e2"; "e3"]; ["es"; "e"]; ["e"]; ["e1"; "e2"];
        ["e"]; ["tt"; "dd"; "es"]; ["loc"; "v"]; ["op"; "es"]] THENL
     [sing_case; if_case; let_case; one; one; one; one; sing_case;
      one] in
   let cons_cons_case =
     REWRITE_TAC[cp; LENGTH_APPEND] THEN
     use_ih `[x1:bvl_exp]` THEN use_ih `(x2:bvl_exp) :: xr2` THEN
     REWRITE_TAC[LENGTH] THEN ARITH_TAC in
   let base_case =
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     NAMED_CASES_TAC `xs:bvl_exp list` [[]; ["x1"; "xr"]] THENL
     [REWRITE_TAC[cp];
      FIRST_ASSUM MP_TAC THEN
      REWRITE_TAC[list_size; ARITH_RULE `~(1 + a + b <= 0)`]] in
   let step_case =
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     NAMED_CASES_TAC `xs:bvl_exp list` [[]; ["x1"; "xr"]] THENL
     [REWRITE_TAC[cp];
      NAMED_CASES_TAC `xr:bvl_exp list` [[]; ["x2"; "xr2"]] THENL
      [single_case; cons_cons_case]] in
   MEASURE_INDUCT_TAC `list_size bvl_exp_size` THENL
   [base_case; step_case]));;

(* compile_HD_SING *)
let bvl_const_compile_HD_SING = prove
 (`[HD (bvl_const_compile n [x])] = bvl_const_compile n [x]`,
  (* the compiled list of one has length one, so it is its own head
     put back into a list *)
  (MP_TAC(SPECL [`n:(bvl_exp option) list`; `[x:bvl_exp]`]
            bvl_const_compile_length) THEN
   STRUCT_CASES_TAC(ISPEC `bvl_const_compile n [x]` list_CASES) THEN
   REWRITE_TAC[LENGTH; SUC_INJ; LENGTH_EQ_NIL; NOT_SUC] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   TRY(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[HD]));;

let bvl_const_compile_exp_def = cake_define
  `bvl_const_compile_exp x =
     (match bvl_const_compile [] [x] with (y :: _31) -> y | _32 ->
       Var 0)
   // impossible`;;
hol4_overload "compile_exp" "bvl_const_compile_exp";;

(* compile_exp_eq *)
let bvl_const_compile_exp_eq = prove
 (`!x. bvl_const_compile_exp x = bvl_const_compile_sing [] x`,
  (* HOL4 applies compile_eq to compile_exp_def: the compiled list
     of one is a singleton, so the match of compile_exp reduces to
     its head *)
  (let ce = bvl_const_compile_exp_def in
   GEN_TAC THEN REWRITE_TAC[ce; CONJUNCT1 compile_eq] THEN
   MATCH_REDUCE_TAC THEN REWRITE_TAC[]));;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["pmatch"];;
