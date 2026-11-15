(* ======================================================== *)
(*  bvl_const: ported from HOL4's
    compiler/backend/bvl_constScript.sml
    A definition theory, with 13 definitions and 12 theorems.
    Needed by bvlProps.ml, bvl_constProof.ml, bvl_handle.ml and
    bvl_to_bvi.ml.  *)
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

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "bvl_const"
  ["bvl"];;

let _ = do_list hide_constant ["pmatch"];;

let dest_simple_def = new_definition
  `dest_simple x1 =
     match x1 with
       bvl_Op (clos_IntOp (clos_Const i)) xs -> if NULL xs then SOME i else
         NONE
     | _ -> NONE`;;
add_simp dest_simple_def;;

let dest_simple_pmatch = prove
 (`!op. dest_simple op =
   match op with
     bvl_Op (clos_IntOp (clos_Const i)) [] -> SOME i
   | _ -> NONE`,
  CHEAT_TAC);;

let case_op_const_def = new_definition
  `case_op_const exp =
       match exp with (bvl_Op op [x1; bvl_Op (clos_IntOp (clos_Const n2))
         l]) -> if NULL l then SOME (op,x1,n2) else NONE
       | _ -> NONE`;;

let case_op_const_pmatch = prove
 (`!exp. case_op_const exp =
   match exp with (bvl_Op op [x1; bvl_Op (clos_IntOp (clos_Const n2)) []])
     -> SOME (op,x1,n2)
     | _ -> NONE`,
  CHEAT_TAC);;

let SmartOp_flip_def = new_definition
  `SmartOp_flip op x1 x2 =
     match (dest_simple x1) with (SOME i) ->
         if MEM op [clos_IntOp clos_Add; clos_IntOp clos_Mult] then
           (op,x2,x1)
         else if op = clos_IntOp clos_Sub then (clos_IntOp
           clos_Add,x2,bvl_Op (clos_IntOp (clos_Const (--i))) [])
         else (op,x1,x2)
     | _ -> (op,x1,x2)`;;

let SmartOp_flip_pmatch = prove
 (`!op x1 x2. SmartOp_flip op x1 x2 =
     match (dest_simple x1) with (SOME i) ->
         if MEM op [clos_IntOp clos_Add; clos_IntOp clos_Mult] then
           (op,x2,x1)
         else if op = clos_IntOp clos_Sub then (clos_IntOp
           clos_Add,x2,bvl_Op (clos_IntOp (clos_Const (--i))) [])
         else (op,x1,x2)
     | _ -> (op,x1,x2)`,
  CHEAT_TAC);;

let SmartOp2_def = new_definition
  `SmartOp2 (op,(x1:bvl_exp),(x2:bvl_exp)) =
     let mk_add_const = (\x1 c2.
       if c2 = (&0) then x1
       else bvl_Op (clos_IntOp clos_Add) [x1; bvl_Op (clos_IntOp (clos_Const
         c2)) []]) in
     let mk_add = (\x1 x2.
       let default = bvl_Op (clos_IntOp clos_Add) [x1; x2] in
         match (dest_simple x2) with (SOME n2) -> (
             match (case_op_const x1) with SOME (op,x11,n12) ->
                 if op = clos_IntOp clos_Add then mk_add_const x11 (n2 +
                   n12)
                 else if op = clos_IntOp clos_Sub then bvl_Op (clos_IntOp
                   clos_Sub) [x11; bvl_Op (clos_IntOp (clos_Const (n2 + n12)))
                   []]
                 else default
             | _ ->
                 (match (dest_simple x1) with SOME n1 -> bvl_Op (clos_IntOp
                   (clos_Const (n2 + n1))) []
                 | _ -> mk_add_const x1 n2))
         | _ ->
             (match (case_op_const x1,case_op_const x2) with (SOME
               (op1,x11,n12),SOME (op2,x21,n22)) ->
                 if op1 = clos_IntOp clos_Add /\ op2 = clos_IntOp clos_Add
                   then
                   mk_add_const (bvl_Op (clos_IntOp clos_Add) [x11; x21])
                     (n22 + n12)
                 else if op1 = clos_IntOp clos_Add /\ op2 = clos_IntOp
                   clos_Sub then
                   bvl_Op (clos_IntOp clos_Sub) [bvl_Op (clos_IntOp
                     clos_Sub) [x11; x21]; bvl_Op (clos_IntOp (clos_Const (n22
                     + n12))) []]
                 else if op1 = clos_IntOp clos_Sub /\ op2 = clos_IntOp
                   clos_Add then
                   mk_add_const (bvl_Op (clos_IntOp clos_Sub) [x11; x21])
                     (n22 + n12)
                 else default
             | _ -> default)) in
     let mk_sub = (\x1 x2.
       let default = bvl_Op (clos_IntOp clos_Sub) [x1; x2] in
         match (dest_simple x2) with (SOME n2) -> (
             match (case_op_const x1) with SOME (op,x11,n12) ->
                 if op = clos_IntOp clos_Add then bvl_Op (clos_IntOp
                   clos_Sub) [x11; bvl_Op (clos_IntOp (clos_Const (n2 - n12)))
                   []]
                 else if op = clos_IntOp clos_Sub then mk_add_const x11 (n2
                   - n12)
                 else default
             | _ ->
                 (match (dest_simple x1) with SOME n1 -> bvl_Op (clos_IntOp
                   (clos_Const (n2 - n1))) []
                 | _ -> default))
         | _ ->
             (match (case_op_const x1,case_op_const x2) with (SOME
               (op1,x11,n12),SOME (op2,x21,n22)) ->
                 if op1 = clos_IntOp clos_Add /\ op2 = clos_IntOp clos_Add
                   then
                   bvl_Op (clos_IntOp clos_Add) [bvl_Op (clos_IntOp
                     clos_Sub) [x11; x21]; bvl_Op (clos_IntOp (clos_Const (n22
                     - n12))) []]
                 else if op1 = clos_IntOp clos_Add /\ op2 = clos_IntOp
                   clos_Sub then
                   bvl_Op (clos_IntOp clos_Sub) [bvl_Op (clos_IntOp
                     clos_Add) [x11; x21]; bvl_Op (clos_IntOp (clos_Const (n22
                     - n12))) []]
                 else if op1 = clos_IntOp clos_Sub /\ op2 = clos_IntOp
                   clos_Add then
                   mk_add_const (bvl_Op (clos_IntOp clos_Add) [x11; x21])
                     (n22 - n12)
                 else default
             | _ -> default)) in
     let mk_mul = (\x1 x2.
       let default = bvl_Op (clos_IntOp clos_Mult) [x1; x2] in
         match (dest_simple x2) with (SOME n2) -> (
             match (case_op_const x1) with SOME (op,x11,n12) ->
                 if op = clos_IntOp clos_Mult then bvl_Op (clos_IntOp
                   clos_Mult) [x11; bvl_Op (clos_IntOp (clos_Const (n2 * n12)))
                   []]
                 else default
             | _ ->
                 (match (dest_simple x1) with SOME n1 -> bvl_Op (clos_IntOp
                   (clos_Const (n2 * n1))) []
                 | _ ->
                     if n2 = (&1) then x1
                     else if n2 = --(&1) then mk_sub x1 (bvl_Op (clos_IntOp
                       (clos_Const (&0))) [])
                     else default))
         | _ ->
             (match (case_op_const x1,case_op_const x2) with (SOME
               (op1,x11,n12),SOME (op2,x21,n22)) ->
                 if op1 = clos_IntOp clos_Mult /\ op2 = clos_IntOp clos_Mult
                   then
                   bvl_Op (clos_IntOp clos_Mult) [bvl_Op (clos_IntOp
                     (clos_Const (n22 * n12))) []; bvl_Op (clos_IntOp
                     clos_Mult) [x11; x21]]
                 else default
             | _ -> default)) in
     let default = bvl_Op op [x1; x2] in
     if op = clos_IntOp clos_Add then
       mk_add x1 x2
     else if op = clos_IntOp clos_Sub then
       mk_sub x1 x2
     else if op = clos_IntOp clos_Mult then
       mk_mul x1 x2
     else if MEM op [clos_IntOp clos_Div; clos_IntOp clos_Mod; clos_IntOp
       clos_Less; clos_IntOp clos_LessEq; clos_IntOp clos_Greater; clos_IntOp
       clos_GreaterEq] then
       match (dest_simple x1,dest_simple x2) with (SOME x1,SOME (x2:int)) ->
           (match op with clos_IntOp clos_Div -> if x1 = (&0) then default
             else bvl_Op (clos_IntOp (clos_Const (x2 / x1))) []
            | clos_IntOp clos_Mod -> if x1 = (&0) then default else bvl_Op
              (clos_IntOp (clos_Const (x2 % x1))) []
            | clos_IntOp clos_Less -> bvl_Bool (x2 < x1)
            | clos_IntOp clos_LessEq -> bvl_Bool (x2 <= x1)
            | clos_IntOp clos_Greater -> bvl_Bool (x2 > x1)
            | clos_IntOp clos_GreaterEq -> bvl_Bool (x2 >= x1)
            | _ -> default)
       | _ -> default
     else if op = clos_BlockOp clos_Equal then
       match (dest_simple x1,dest_simple x2) with (SOME i,SOME j) ->
         bvl_Bool (j = i)
       | (SOME i,_) -> bvl_Op (clos_BlockOp (clos_EqualConst (clos_Int i)))
         [x2]
       | (_,SOME i) -> bvl_Op (clos_BlockOp (clos_EqualConst (clos_Int i)))
         [x1]
       | _ -> default
     else if op = clos_MemOp clos_El then
       match dest_simple x1 with SOME i -> if i < (&0) then default else
         bvl_Op (clos_BlockOp (clos_ElemAt (num_of_int i))) [x2]
       | _ -> default
     else default`;;

(* NOTE: the space after case and pmatch is important *)
(* HOL4 bvl_constScript.sml:196-198: ML code, not ported *)

(* HOL4 bvl_constScript.sml:200-205: a theorem whose statement the port
   cannot state yet: SmartOp2_pmatch *)
(* HOL4 bvl_constScript.sml:206: ML code, not ported *)


let dest_EqualInt_def = new_definition
  `dest_EqualInt x1' =
   match x1' with
     clos_BlockOp (clos_EqualConst (clos_Int i)) -> SOME i
   | _ -> NONE`;;

let dest_EqualInt_pmatch = prove
 (`dest_EqualInt x = match x with clos_BlockOp (clos_EqualConst (clos_Int i))
  -> SOME i | _ -> NONE`,
  CHEAT_TAC);;

let SmartOp1_def = new_definition
  `SmartOp1 op x =
     match dest_EqualInt op with NONE -> bvl_Op op [x]
     | SOME i ->
       (match dest_simple x with NONE -> bvl_Op op [x]
       | SOME j -> bvl_Bool (j = i))`;;


let SmartOp_def = new_definition
  `bvl_const_SmartOp op xs =
     match xs with [x1; x2] -> SmartOp2 (SmartOp_flip op x1 x2)
     | [x] -> SmartOp1 op x
     | _ -> bvl_Op op xs`;;

let SmartOp_pmatch = prove
 (`!op xs. bvl_const_SmartOp op xs =
   match xs with [x1; x2] -> SmartOp2 (SmartOp_flip op x1 x2)
   | [x] -> SmartOp1 op x
   | _ -> bvl_Op op xs`,
  CHEAT_TAC);;

let bvl_const_extract_def = new_definition
  `bvl_const_extract x1'' ys =
     match x1'' with
       ((bvl_Var n):bvl_exp) -> SOME ((bvl_Var (n + LENGTH ys + 1)):bvl_exp)
     | bvl_Op (clos_IntOp (clos_Const i)) xs -> SOME (bvl_Op (clos_IntOp
       (clos_Const i)) [])
     | bvl_Op (clos_BlockOp (clos_Cons t)) xs ->
       if NULL xs then SOME (bvl_Op (clos_BlockOp (clos_Cons t)) []) else
         NONE
     | _ -> NONE`;;

let extract_pmatch = prove
 (`!op ys. bvl_const_extract op ys =
   match op with
     ((bvl_Var n):bvl_exp) -> SOME ((bvl_Var (n + LENGTH ys + 1)):bvl_exp)
   | bvl_Op (clos_IntOp (clos_Const i)) xs -> SOME (bvl_Op (clos_IntOp
     (clos_Const i)) [])
   | bvl_Op (clos_BlockOp (clos_Cons t)) [] -> SOME (bvl_Op (clos_BlockOp
     (clos_Cons t)) [])
   | _ -> NONE`,
  CHEAT_TAC);;

let bvl_const_extract_list_def,bvl_const_extract_list_ind = define_rec
  `(bvl_const_extract_list [] = []) /\
   (bvl_const_extract_list (CONS x xs) = CONS (bvl_const_extract x xs)
    (bvl_const_extract_list xs))`;;

let bvl_const_delete_var_def = new_definition
  `bvl_const_delete_var x =
     match x with
       ((bvl_Var n):bvl_exp) -> bvl_Op (clos_IntOp (clos_Const (&0))) []
     | x -> x`;;

let delete_var_pmatch = prove
 (`!op.
   bvl_const_delete_var op =
     match op with
       bvl_Var n -> bvl_Op (clos_IntOp (clos_Const (&0))) []
     | x -> x`,
  CHEAT_TAC);;

make_size "bvl_exp";;
(* the termination relation is not in the HOL4 source *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let bvl_const_compile_def,bvl_const_compile_ind = define_wf_cheat
  `MEASURE (list_size bvl_exp_size o SND)`
  `(bvl_const_compile env [] = []) /\
   (bvl_const_compile env (CONS x (CONS y xs)) = APPEND (bvl_const_compile
    env [x]) (bvl_const_compile env (CONS y xs))) /\
   (bvl_const_compile env [bvl_Var v] =
         match (\l n. oEL n l) env v with NONE -> [bvl_Var v]
         | SOME NONE -> [bvl_Var v]
         | SOME (SOME (bvl_Var i)) -> [bvl_Var (v + i)]
         | SOME (SOME x) -> [x]) /\
   (bvl_const_compile env [bvl_If x1 x2 x3] =
         let y1 = HD (bvl_const_compile env [x1]) in
         let y2 = HD (bvl_const_compile env [x2]) in
         let y3 = HD (bvl_const_compile env [x3]) in
           if y1 = bvl_Bool T then [y2] else if y1 = bvl_Bool F then
               [y3] else [bvl_If y1 y2 y3]) /\
   (bvl_const_compile env [bvl_Let xs x2] =
         let ys = bvl_const_compile env xs in
           [bvl_Let (MAP bvl_const_delete_var ys)
                (HD (bvl_const_compile (APPEND (bvl_const_extract_list
                    ys) env) [x2]))]) /\
   (bvl_const_compile env [bvl_Handle x1 x2] =
         [bvl_Handle (HD (bvl_const_compile env [x1])) (HD
             (bvl_const_compile (CONS NONE env) [x2]))]) /\
   (bvl_const_compile env [bvl_Raise x1] =
         [bvl_Raise (HD (bvl_const_compile env [x1]))]) /\
   (bvl_const_compile env [bvl_Op op xs] = [bvl_const_SmartOp op
    (bvl_const_compile env xs)]) /\
   (bvl_const_compile env [bvl_Tick x] = [bvl_Tick (HD (bvl_const_compile
    env [x]))]) /\
   (bvl_const_compile env [bvl_Force loc v] =
         match (\l n. oEL n l) env v with NONE -> [bvl_Force loc v]
         | SOME NONE -> [bvl_Force loc v]
         | SOME (SOME (bvl_Var i)) -> [bvl_Force loc (v + i)]
         | SOME (SOME x) -> [bvl_Force loc v]) /\
   (bvl_const_compile env [bvl_Call t dest xs] = [bvl_Call t dest
    (bvl_const_compile env xs)])`;;

let bvl_const_compile_sing_def,bvl_const_compile_sing_ind = define_rec
  `(bvl_const_compile_sing env (bvl_Var v) =
         match (\l n. oEL n l) env v with NONE -> bvl_Var v
         | SOME NONE -> bvl_Var v
         | SOME (SOME (bvl_Var i)) -> bvl_Var (v + i)
         | SOME (SOME x) -> x) /\
   (bvl_const_compile_sing env (bvl_If x1 x2 x3) =
         let y1 = bvl_const_compile_sing env x1 in
         let y2 = bvl_const_compile_sing env x2 in
         let y3 = bvl_const_compile_sing env x3 in
           if y1 = bvl_Bool T then y2 else if y1 = bvl_Bool F then y3
               else bvl_If y1 y2 y3) /\
   (bvl_const_compile_sing env (bvl_Let xs x2) =
         let ys = bvl_const_compile_list env xs in
           bvl_Let (MAP bvl_const_delete_var ys)
               (bvl_const_compile_sing (APPEND (bvl_const_extract_list
                   ys) env) x2)) /\
   (bvl_const_compile_sing env (bvl_Handle x1 x2) =
         bvl_Handle (bvl_const_compile_sing env x1)
             (bvl_const_compile_sing (CONS NONE env) x2)) /\
   (bvl_const_compile_sing env (bvl_Raise x1) =
         bvl_Raise (bvl_const_compile_sing env x1)) /\
   (bvl_const_compile_sing env (bvl_Op op xs) = bvl_const_SmartOp op
    (bvl_const_compile_list env xs)) /\
   (bvl_const_compile_sing env (bvl_Tick x) = bvl_Tick
    (bvl_const_compile_sing env x)) /\
   (bvl_const_compile_sing env (bvl_Force loc v) =
         match (\l n. oEL n l) env v with NONE -> bvl_Force loc v
         | SOME NONE -> bvl_Force loc v
         | SOME (SOME (bvl_Var i)) -> bvl_Force loc (v + i)
         | SOME (SOME x) -> bvl_Force loc v) /\
   (bvl_const_compile_sing env (bvl_Call t dest xs) = bvl_Call t dest
    (bvl_const_compile_list env xs)) /\
   (bvl_const_compile_list env [] = []) /\
   (bvl_const_compile_list env (CONS x xs) = CONS (bvl_const_compile_sing
    env x) (bvl_const_compile_list env xs))`;;

let compile_eq = prove
 (`(!e env. bvl_const_compile env [e] = [bvl_const_compile_sing env e]) /\
   (!es env. bvl_const_compile env es = bvl_const_compile_list env es)`,
  CHEAT_TAC);;

(* compile_length *)
let bvl_const_compile_length = prove
 (`!n xs. LENGTH (bvl_const_compile n xs) = LENGTH xs`,
  CHEAT_TAC);;
add_simp bvl_const_compile_length;;

(* compile_HD_SING *)
let bvl_const_compile_HD_SING = prove
 (`[HD (bvl_const_compile n [x])] = bvl_const_compile n [x]`,
  CHEAT_TAC);;

let bvl_const_compile_exp_def = new_definition
  `bvl_const_compile_exp x =
     match bvl_const_compile [] [x] with (CONS y _) -> y | _ -> bvl_Var 0
   // impossible`;;

let bvl_const_compile_exp_eq =
  SIMP_RULE [compile_eq] bvl_const_compile_exp_def;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["pmatch"];;

(* and the interface *)
let _ = unhide_overloads ();;
