(* ======================================================== *)
(*  clos_op: ported from HOL4's
    compiler/backend/clos_opScript.sml  *)
(* ======================================================== *)

(*
  This file implements a "smart" version of ClosLang's Op
  constructor. When possible, this smart constructor breaks
  the operation into faster separate operators.
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "lib/comparison.ml";;
needs "lib/indexedLists.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(* matchers *)

let dest_Const_def = cake_define
  `dest_Const x1 =
      match x1 with
        closLang_IntOp (closLang_Const i) -> SOME i
      | _1 -> NONE`;;

let dest_Constant_def = cake_define
  `clos_op_dest_Constant x1 =
      match x1 with
        closLang_BlockOp (closLang_Constant (ConstStr c)) -> SOME
          (closLang_Str c)
      | (closLang_BlockOp (closLang_Constant (ConstInt c))) -> SOME
        (closLang_Int c)
      | (closLang_BlockOp (closLang_Constant (ConstWord64 c))) ->
        SOME (W64 c)
      | _2 -> NONE`;;
hol4_overload "dest_Constant" "clos_op_dest_Constant";;

let dest_Cons_def = cake_define
  `clos_op_dest_Cons x1 =
      match x1 with
        closLang_BlockOp (closLang_Cons i) -> SOME i
      | _3 -> NONE`;;
hol4_overload "dest_Cons" "clos_op_dest_Cons";;

let dest_ElemAt_def = cake_define
  `dest_ElemAt x1 =
      match x1 with
        closLang_BlockOp (closLang_ElemAt i) -> SOME i
      | _4 -> NONE`;;

let dest_TagEq_def = cake_define
  `dest_TagEq x1 =
      match x1 with
        closLang_BlockOp (closLang_TagEq i) -> SOME i
      | _5 -> NONE`;;

let dest_LenEq_def = cake_define
  `dest_LenEq x1 =
      match x1 with
        closLang_BlockOp (closLang_LenEq i) -> SOME i
      | _6 -> NONE`;;

let dest_TagLenEq_def = cake_define
  `dest_TagLenEq x1 =
      match x1 with
        closLang_BlockOp (closLang_TagLenEq i j) -> SOME (i,j)
      | _7 -> NONE`;;

let dest_Op_def = cake_define
  `dest_Op f x2 =
      match x2 with
        (closLang_Op t op xs:closLang_exp) ->
     (match f op with NONE -> NONE | SOME i -> SOME (i,xs))
      | _8 -> NONE`;;

let dest_Op_Nil_def = cake_define
  `dest_Op_Nil f x =
     (match dest_Op f x with NONE -> NONE | SOME (i,xs) -> (if
       NULL xs then SOME i else NONE))`;;

(* HOL4 overload (expanded in the port):
     dest_Op_Cons = dest_Op dest_Cons *)
(* HOL4 overload (expanded in the port):
     dest_Op_Cons_Nil = dest_Op_Nil dest_Cons *)
(* HOL4 overload (expanded in the port):
     dest_Op_Const = dest_Op_Nil dest_Const *)
(* HOL4 overload (expanded in the port):
     dest_Op_Constant = dest_Op_Nil dest_Constant *)

let dest_Op_Consts_def = cake_define
  `dest_Op_Consts x y =
     (match (dest_Op_Nil dest_Const) x with NONE -> NONE | SOME i ->
       (match (dest_Op_Nil dest_Const) y with NONE -> NONE | SOME
         j -> SOME (i,j)))`;;

let MakeBool_def = cake_define
  `MakeBool b = closLang_Op backend_common_None (closLang_BlockOp
  (closLang_Cons (if b then 1 else 0))) []`;;

let MakeInt_def = cake_define
  `MakeInt i = closLang_Op backend_common_None (closLang_IntOp
  (closLang_Const i)) []`;;

let int_op_def = cake_define
  `clos_op_int_op op i j =
     (if op = closLang_IntOp closLang_Add then SOME (MakeInt (j + i))
       else
     if op = closLang_IntOp closLang_Sub then SOME (MakeInt (j - i))
       else
     if op = closLang_IntOp closLang_Mult then SOME (MakeInt (j * i))
       else
     if op = closLang_IntOp closLang_Div then SOME (MakeInt (if i =
       (&0) then (&0) else j / i)) else
     if op = closLang_IntOp closLang_Mod then SOME (MakeInt (if i =
       (&0) then (&0) else j % i)) else
     if op = closLang_IntOp closLang_Less then SOME (MakeBool (j <
       i)) else
     if op = closLang_IntOp closLang_LessEq then SOME (MakeBool (j <=
       i)) else
     if op = closLang_IntOp Greater then SOME (MakeBool (i < j)) else
     if op = closLang_IntOp closLang_GreaterEq then SOME (MakeBool (i
       <= j)) else
     if op = closLang_BlockOp closLang_Equal then SOME (MakeBool
       (j = i)) else NONE)`;;
hol4_overload "int_op" "clos_op_int_op";;

let cons_op_def = cake_define
  `cons_op op t xs =
     (match dest_ElemAt op with SOME n -> (if n < LENGTH xs then
                    SOME (Let backend_common_None xs (Var
                      backend_common_None (LENGTH xs - (n + 1)))) else
                      NONE) | NONE ->
     (match dest_TagLenEq op with SOME (n,l) -> SOME (Let
       backend_common_None xs (MakeBool (n = t /\ LENGTH xs = l))) |
       NONE ->
     (match dest_TagEq op with SOME n -> SOME (Let
       backend_common_None xs (MakeBool (n = t))) | NONE ->
     (match dest_LenEq op with SOME l -> SOME (Let
       backend_common_None xs (MakeBool (LENGTH xs = l))) | NONE ->
       NONE))))`;;

let is_Var_def = cake_define
  `is_Var x1 =
      match x1 with
        (Var _11 _12:closLang_exp) -> T
      | _13 -> F`;;

let eq_direct_nil_def = cake_define
  `eq_direct_nil x y =
     (match (dest_Op_Nil clos_op_dest_Cons) x with SOME i ->
         (match (dest_Op_Nil clos_op_dest_Cons) y with SOME j -> SOME
           (MakeBool (i = j)) | NONE -> SOME (closLang_Op
           backend_common_None (closLang_BlockOp (closLang_TagLenEq i
           0)) [y])) | NONE ->
         (match (dest_Op_Nil clos_op_dest_Cons) y with SOME i ->
           SOME (closLang_Op backend_common_None (closLang_BlockOp
           (closLang_TagLenEq i 0)) [x]) | NONE -> NONE))`;;

let eq_direct_const_def = cake_define
  `eq_direct_const x y =
     (match (dest_Op_Nil dest_Const) x with SOME i ->
         (match (dest_Op_Nil dest_Const) y with SOME j -> SOME
           (MakeBool (i = j)) | NONE -> SOME (closLang_Op
           backend_common_None (closLang_BlockOp (closLang_EqualConst
           (closLang_Int i))) [y])) | NONE ->
         (match (dest_Op_Nil dest_Const) y with SOME i -> SOME
           (closLang_Op backend_common_None (closLang_BlockOp
           (closLang_EqualConst (closLang_Int i))) [x]) | NONE ->
           NONE))`;;

let eq_direct_constant_def = cake_define
  `eq_direct_constant x y =
     (match (dest_Op_Nil clos_op_dest_Constant) x with SOME p ->
         (match (dest_Op_Nil clos_op_dest_Constant) y with SOME q ->
           SOME (MakeBool (q = p)) | NONE -> SOME (closLang_Op
           backend_common_None (closLang_BlockOp (closLang_EqualConst
           p)) [y])) | NONE ->
         (match (dest_Op_Nil clos_op_dest_Constant) y with SOME p
           -> SOME (closLang_Op backend_common_None (closLang_BlockOp
           (closLang_EqualConst p)) [x]) | NONE -> NONE))`;;

let eq_direct_def = cake_define
  `eq_direct x y =
     (match eq_direct_const x y with SOME res -> SOME res | NONE
       -> (match eq_direct_constant x y with SOME res -> SOME res |
       NONE -> eq_direct_nil x y))`;;

let _ = size_thms "closLang_exp";;
(* HOL4 termination: \\ Cases \\ fs [dest_Op_def] \\ Cases_on ‘o'’ \\
   fs [dest_Cons_def,exp_size_def] \\ Cases_on ‘b’ \\ fs
   [dest_Cons_def,exp_size_def] \\ Induct_on ‘l’ \\ fs [exp_size_def]
   \\ rw [] \\ res_tac \\ fs [] *)
let cons_measure_def = cake_define_wf
  `MEASURE closLang_exp_size`
  `cons_measure x =
     (match (dest_Op clos_op_dest_Cons) x with NONE -> 0 | SOME
       (_14,xs) -> SUM (MAP cons_measure xs) + LENGTH xs + 1)`;;

(* HOL4 termination: \\ reverse (rpt strip_tac) \\ fs [] THEN1
   (imp_res_tac cons_measure_lemma \\ fs [cons_measure_lemma]) THEN1
   (fs [o_DEF,cons_measure_lemma] \\ imp_res_tac cons_measure_lemma
   \\ fs [] \\ ‘LENGTH p_2 = LENGTH (REVERSE p_2)’ by fs [] \\ ‘SUM
   (MAP cons_measure p_2) = SUM (MAP cons_measure (REVERSE p_2))’ by
   (rpt (pop_assum kall_tac) \\ Induct_on ‘p_2’ \\ fs [SUM_APPEND])
   \\ asm_rewrite_tac[] \\ qspec_tac (‘REVERSE p_2’,‘p_3’) \\ Induct
   using SNOC_INDUCT \\ fs [SNOC_APPEND,MAPi_APPEND,SUM_APPEND]) \\
   imp_res_tac cons_measure_lemma \\ fs
   [cons_measure_lemma,MEM_SPLIT,SUM_APPEND] \\ qpat_x_assum ‘LENGTH
   _ = _’ mp_tac \\ rename [‘LENGTH xs = LENGTH ys’] \\ qid_spec_tac
   ‘ys’ \\ qid_spec_tac ‘xs’ \\ Induct THEN1 (Cases \\ fs []) \\
   Cases_on ‘ys'’ \\ fs [] \\ rpt strip_tac \\ first_x_assum drule \\
   fs [GSYM rich_listTheory.ZIP_APPEND,SUM_APPEND] *)
let eq_pure_list_def = cake_define_wf
  `MEASURE (SUM o MAP (\(x,y). 1 + cons_measure x + cons_measure y +
                              (if cons_measure x < cons_measure y
                                then 1 else 0)))`
  `eq_pure_list x1 =
      match x1 with
        [] -> misc_Nil
      | [x,y] ->
    (match eq_direct x y with SOME z -> misc_List [z] | NONE ->
       (match ((dest_Op clos_op_dest_Cons) x,(dest_Op
         clos_op_dest_Cons) y) with (NONE,NONE) -> misc_List
         [closLang_Op backend_common_None (closLang_BlockOp
         closLang_Equal) [x; y]] | (SOME (t1,xs),SOME (t2,ys)) ->
            (if ~(t1 = t2) \/ ~(LENGTH xs = LENGTH ys) then misc_List
              [MakeBool F] else eq_pure_list (ZIP (REVERSE xs) (REVERSE
              ys))) | (SOME (t1,xs),NONE) ->
            misc_Append (misc_List [closLang_Op backend_common_None
              (closLang_BlockOp (closLang_TagLenEq t1 (LENGTH xs)))
              [y]])
                   (eq_pure_list (MAPi (\i x. (x,closLang_Op
                     backend_common_None (closLang_BlockOp
                     (closLang_ElemAt i)) [y])) (REVERSE xs))) |
                     (NONE,SOME (t1,ys)) -> eq_pure_list [(y,x)]))
      | (xy :: xys) -> misc_Append (eq_pure_list [xy])
        (eq_pure_list xys)`;;

let ConjList_def = cake_define
  `ConjList x1 =
      match x1 with
        [] -> MakeBool T
      | [x] -> x
      | (x :: xs) -> If backend_common_None x (ConjList xs)
        (MakeBool F)`;;

let eq_pure_def = cake_define
  `eq_pure x y = ConjList (append (eq_pure_list [(x,y)]))`;;

let dont_lift_def = cake_define
  `dont_lift x =
     (match (dest_Op_Nil dest_Const) x with SOME i -> T | NONE ->
       (match (dest_Op_Nil clos_op_dest_Cons) x with SOME t -> T |
         NONE ->
         (match (dest_Op_Nil clos_op_dest_Constant) x with SOME t
           -> T | NONE -> F)))`;;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let lift_exps_def = cake_define_list_wf
  `MEASURE (\(xs,n,binds). list_size closLang_exp_size xs)`
  [`lift_exps [] n binds = ([],n,binds)`;
   `lift_exps (x :: xs) n binds =
      (if dont_lift x then
        (let (xs,n,binds) = lift_exps xs n binds in
           (x :: xs,n,binds)) else match (dest_Op clos_op_dest_Cons)
             x with SOME (t,ys) ->
              (let (ys,n,binds) = lift_exps ys n binds in
               let (xs,n,binds) = lift_exps xs n binds in
                 (closLang_Op backend_common_None (closLang_BlockOp
                   (closLang_Cons t)) ys :: xs,n,binds)) | NONE ->
              (let (xs,n1,binds) = lift_exps xs (n + 1) (binds ++
                [x]) in
                (Var backend_common_None n :: xs,n1,binds)))`];;

let eq_any_def = cake_define
  `eq_any x y =
     (match lift_exps [x; y] 0 [] with (x :: y :: _15,_16,binds)
       -> SOME (Let backend_common_None binds (eq_pure x y)) | _17 ->
       NONE)`;;

let eq_op_def = cake_define
  `eq_op x y =
     (if is_Var x /\ is_Var y then NONE else
       match eq_direct x y with NONE -> eq_any x y | SOME res ->
         SOME res)`;;

(* top-level implementations *)

let SmartOp'_def = cake_define
  `SmartOp' tra op xs =
     (match xs with [x] ->
       (match (dest_Op clos_op_dest_Cons) x with SOME (t,xs) ->
         cons_op op t xs | NONE -> NONE) | [x; y] ->
       (match dest_Op_Consts x y with SOME (i,j) -> clos_op_int_op
         op i j | NONE -> (if op = closLang_BlockOp closLang_Equal
         then eq_op x y else NONE)) | _18 -> NONE)`;;

let SmartOp_def = cake_define
  `clos_op_SmartOp tra op xs =
     (match SmartOp' tra op xs with NONE -> closLang_Op tra op xs
       | SOME x -> x)`;;
hol4_overload "SmartOp" "clos_op_SmartOp";;
