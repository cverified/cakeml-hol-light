(* ======================================================== *)
(*  clos_op: ported from HOL4's
    compiler/backend/clos_opScript.sml
    A definition theory, with 29 definitions and 11 theorems.
    Needed by clos_known.ml and clos_opProof.ml.  *)
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

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "clos_op"
  ["backend_common"; "closLang"; "misc"];;

let _ = do_list hide_constant ["pmatch"];;

(* matchers *)

let dest_Const_def = new_definition
  `dest_Const x1 =
      match x1 with
        closLang_IntOp (closLang_Const i) -> SOME i
      | _1 -> NONE`;;

let dest_Const_pmatch = prove
 (`dest_Const x = (match x with closLang_IntOp (closLang_Const i) ->
  SOME i | _2 -> NONE)`,
  CHEAT_TAC);;

let dest_Constant_def = new_definition
  `clos_op_dest_Constant x1 =
      match x1 with
        closLang_BlockOp (closLang_Constant (ConstStr c)) -> SOME
          (closLang_Str c)
      | (closLang_BlockOp (closLang_Constant (ConstInt c))) -> SOME
        (closLang_Int c)
      | (closLang_BlockOp (closLang_Constant (ConstWord64 c))) ->
        SOME (W64 c)
      | _3 -> NONE`;;
hol4_overload "dest_Constant" "clos_op_dest_Constant";;

let dest_Constant_pmatch = prove
 (`clos_op_dest_Constant x = (match x with closLang_BlockOp
  (closLang_Constant (ConstStr c)) -> SOME (closLang_Str c) |
  closLang_BlockOp (closLang_Constant (ConstInt c)) -> SOME
  (closLang_Int c) | closLang_BlockOp (closLang_Constant (ConstWord64
  c)) -> SOME (W64 c) | _4 -> NONE)`,
  CHEAT_TAC);;

let clos_op_dest_Cons_def = new_definition
  `clos_op_dest_Cons x1 =
      match x1 with
        closLang_BlockOp (closLang_Cons i) -> SOME i
      | _5 -> NONE`;;
hol4_overload "dest_Cons" "clos_op_dest_Cons";;

let dest_Cons_pmatch = prove
 (`clos_op_dest_Cons x = (match x with closLang_BlockOp (closLang_Cons
  i) -> SOME i | _6 -> NONE)`,
  CHEAT_TAC);;

let dest_ElemAt_def = new_definition
  `dest_ElemAt x1 =
      match x1 with
        closLang_BlockOp (closLang_ElemAt i) -> SOME i
      | _7 -> NONE`;;

let dest_ElemAt_pmatch = prove
 (`dest_ElemAt x = (match x with closLang_BlockOp (closLang_ElemAt i)
  -> SOME i | _8 -> NONE)`,
  CHEAT_TAC);;

let dest_TagEq_def = new_definition
  `dest_TagEq x1 =
      match x1 with
        closLang_BlockOp (closLang_TagEq i) -> SOME i
      | _9 -> NONE`;;

let dest_TagEq_pmatch = prove
 (`dest_TagEq x = (match x with closLang_BlockOp (closLang_TagEq i) ->
  SOME i | _10 -> NONE)`,
  CHEAT_TAC);;

let dest_LenEq_def = new_definition
  `dest_LenEq x1 =
      match x1 with
        closLang_BlockOp (closLang_LenEq i) -> SOME i
      | _11 -> NONE`;;

let dest_LenEq_pmatch = prove
 (`dest_LenEq x = (match x with closLang_BlockOp (closLang_LenEq i) ->
  SOME i | _12 -> NONE)`,
  CHEAT_TAC);;

let dest_TagLenEq_def = new_definition
  `dest_TagLenEq x1 =
      match x1 with
        closLang_BlockOp (closLang_TagLenEq i j) -> SOME (i,j)
      | _13 -> NONE`;;

let dest_TagLenEq_pmatch = prove
 (`dest_TagLenEq x = (match x with closLang_BlockOp (closLang_TagLenEq
  i j) -> SOME (i,j) | _14 -> NONE)`,
  CHEAT_TAC);;

let dest_Op_def = new_definition
  `dest_Op f x2 =
      match x2 with
        (closLang_Op t op xs:closLang_exp) ->
     (match f op with NONE -> NONE | SOME i -> SOME (i,xs))
      | _15 -> NONE`;;

let dest_Op_pmatch = prove
 (`dest_Op f x =
     (match x with closLang_Op t op xs ->
       (match f op with NONE -> NONE | SOME i -> SOME (i,xs)) | _16
         -> NONE)`,
  CHEAT_TAC);;

let dest_Op_Nil_def = new_definition
  `dest_Op_Nil f x =
     (match dest_Op f x with NONE -> NONE | SOME (i,xs) -> (if
       NULL xs then SOME i else NONE))`;;

(* HOL4 clos_opScript.sml:141: the overload dest_Op_Cons, which the
   port expands *)
(* HOL4 clos_opScript.sml:142: the overload dest_Op_Cons_Nil, which
   the port expands *)
(* HOL4 clos_opScript.sml:143: the overload dest_Op_Const, which the
   port expands *)
(* HOL4 clos_opScript.sml:144: the overload dest_Op_Constant, which
   the port expands *)

let dest_Op_Consts_def = new_definition
  `dest_Op_Consts x y =
     (match (dest_Op_Nil dest_Const) x with NONE -> NONE | SOME i ->
       (match (dest_Op_Nil dest_Const) y with NONE -> NONE | SOME
         j -> SOME (i,j)))`;;

let MakeBool_def = new_definition
  `MakeBool b = closLang_Op backend_common_None (closLang_BlockOp
  (closLang_Cons (if b then 1 else 0))) []`;;

let MakeInt_def = new_definition
  `MakeInt i = closLang_Op backend_common_None (closLang_IntOp
  (closLang_Const i)) []`;;

let clos_op_int_op_def = new_definition
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

let cons_op_def = new_definition
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

let is_Var_def = new_definition
  `is_Var x1 =
      match x1 with
        (Var _19 _20:closLang_exp) -> T
      | _21 -> F`;;

let is_Var_pmatch = prove
 (`is_Var x = (match x with Var _22 _23 -> T | _24 -> F)`,
  CHEAT_TAC);;

let eq_direct_nil_def = new_definition
  `eq_direct_nil x y =
     (match (dest_Op_Nil clos_op_dest_Cons) x with SOME i ->
         (match (dest_Op_Nil clos_op_dest_Cons) y with SOME j -> SOME
           (MakeBool (i = j)) | NONE -> SOME (closLang_Op
           backend_common_None (closLang_BlockOp (closLang_TagLenEq i
           0)) [y])) | NONE ->
         (match (dest_Op_Nil clos_op_dest_Cons) y with SOME i ->
           SOME (closLang_Op backend_common_None (closLang_BlockOp
           (closLang_TagLenEq i 0)) [x]) | NONE -> NONE))`;;

let eq_direct_const_def = new_definition
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

let eq_direct_constant_def = new_definition
  `eq_direct_constant x y =
     (match (dest_Op_Nil clos_op_dest_Constant) x with SOME p ->
         (match (dest_Op_Nil clos_op_dest_Constant) y with SOME q ->
           SOME (MakeBool (q = p)) | NONE -> SOME (closLang_Op
           backend_common_None (closLang_BlockOp (closLang_EqualConst
           p)) [y])) | NONE ->
         (match (dest_Op_Nil clos_op_dest_Constant) y with SOME p
           -> SOME (closLang_Op backend_common_None (closLang_BlockOp
           (closLang_EqualConst p)) [x]) | NONE -> NONE))`;;

let eq_direct_def = new_definition
  `eq_direct x y =
     (match eq_direct_const x y with SOME res -> SOME res | NONE
       -> (match eq_direct_constant x y with SOME res -> SOME res |
       NONE -> eq_direct_nil x y))`;;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 clos_opScript.sml:261-268: the tactic that proves the
   termination *)
let cons_measure_def,cons_measure_ind = define_wf
  `MEASURE closLang_exp_size`
  [`cons_measure x =
     (match (dest_Op clos_op_dest_Cons) x with NONE -> 0 | SOME
       (_25,xs) -> SUM (MAP cons_measure xs) + LENGTH xs + 1)`];;

let cons_measure_lemma = prove
 (`((dest_Op clos_op_dest_Cons) x = SOME (t,xs) ==> cons_measure x = SUM
  (MAP cons_measure xs) + LENGTH xs + 1) /\
   ((dest_Op clos_op_dest_Cons) x = NONE ==> cons_measure x = 0) /\
   (cons_measure (closLang_Op backend_common_None (closLang_BlockOp
     (closLang_ElemAt i)) [y]:closLang_exp) = 0)`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (SUM o MAP (\(x,y). 1 + cons_measure x + cons_measure y +
                                   (if cons_measure x < cons_measure y
                                     then 1 else 0)))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 clos_opScript.sml:294-317: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let eq_pure_list_def,eq_pure_list_ind = define_guess_cheat
  [`eq_pure_list x1 =
      match x1 with
        [] -> misc_Nil
      | [x,y] ->
    (match eq_direct x y with SOME z -> misc_List [z] | NONE ->
       (match ((dest_Op clos_op_dest_Cons) x,(dest_Op
         clos_op_dest_Cons) y) with (NONE,NONE) -> misc_List
         [closLang_Op backend_common_None (closLang_BlockOp
         closLang_Equal) [x; y]] | (SOME (t1,xs),SOME (t2,ys)) ->
            (if ~(t1 = t2) \/ ~(LENGTH xs = LENGTH ys) then
              misc_List [MakeBool F] else eq_pure_list (ZIP (REVERSE
              xs) (REVERSE ys))) | (SOME (t1,xs),NONE) ->
            misc_Append (misc_List [closLang_Op backend_common_None
              (closLang_BlockOp (closLang_TagLenEq t1 (LENGTH xs)))
              [y]])
                   (eq_pure_list (MAPi (\i x. (x,closLang_Op
                     backend_common_None (closLang_BlockOp
                     (closLang_ElemAt i)) [y])) (REVERSE xs))) |
                     (NONE,SOME (t1,ys)) -> eq_pure_list [(y,x)]))
      | (CONS xy xys) -> misc_Append (eq_pure_list [xy])
        (eq_pure_list xys)`];;

let _ = size_thms "closLang_exp";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let ConjList_def,ConjList_ind = define_wf
  `MEASURE (\x0. closLang_exp_size1 x0)`
  [`ConjList x1 =
      match x1 with
        [] -> MakeBool T
      | [x] -> x
      | (CONS x xs) -> If backend_common_None x (ConjList xs)
        (MakeBool F)`];;

let eq_pure_def = new_definition
  `eq_pure x y = ConjList (append (eq_pure_list [(x,y)]))`;;

(* [local] *)
let eq_pure_list_test = prove
 (`append (eq_pure_list
          [(Var backend_common_None 5,
            closLang_Op backend_common_None (closLang_BlockOp
              (closLang_Cons 70)) [closLang_Op backend_common_None
              (closLang_IntOp (closLang_Const (&2))) []; closLang_Op
              backend_common_None (closLang_BlockOp (closLang_Cons 4))
              []])]) =
     [closLang_Op backend_common_None (closLang_BlockOp
       (closLang_TagLenEq 70 2)) [Var backend_common_None 5];
      closLang_Op backend_common_None (closLang_BlockOp
        (closLang_TagLenEq 4 0)) [closLang_Op backend_common_None
        (closLang_BlockOp (closLang_ElemAt 0)) [Var backend_common_None
        5]];
      closLang_Op backend_common_None (closLang_BlockOp
        (closLang_EqualConst (closLang_Int (&2)))) [closLang_Op
        backend_common_None (closLang_BlockOp (closLang_ElemAt 1))
        [Var backend_common_None 5]]]`,
  CHEAT_TAC);;

let dont_lift_def = new_definition
  `dont_lift x =
     (match (dest_Op_Nil dest_Const) x with SOME i -> T | NONE ->
       (match (dest_Op_Nil clos_op_dest_Cons) x with SOME t -> T |
         NONE ->
         (match (dest_Op_Nil clos_op_dest_Constant) x with SOME t
           -> T | NONE -> F)))`;;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 clos_opScript.sml:368-373: the tactic that proves the
   termination *)
let lift_exps_def,lift_exps_ind = define_wf
  `MEASURE (\(xs,n,binds). list_size closLang_exp_size xs)`
  [`lift_exps [] n binds = ([],n,binds)`;
   `lift_exps (CONS x xs) n binds =
      (if dont_lift x then
        (let (xs,n,binds) = lift_exps xs n binds in
           (CONS x xs,n,binds)) else match (dest_Op
             clos_op_dest_Cons) x with SOME (t,ys) ->
              (let (ys,n,binds) = lift_exps ys n binds in
               let (xs,n,binds) = lift_exps xs n binds in
                 (CONS (closLang_Op backend_common_None
                   (closLang_BlockOp (closLang_Cons t)) ys) xs,n,binds))
                   | NONE ->
              (let (xs,n1,binds) = lift_exps xs (n + 1) (APPEND
                binds [x]) in
                (CONS (Var backend_common_None n)
                  xs,n1,binds)))`];;

let eq_any_def = new_definition
  `eq_any x y =
     (match lift_exps [x; y] 0 [] with (CONS x (CONS y
       _26),_27,binds) -> SOME (Let backend_common_None binds
       (eq_pure x y)) | _28 -> NONE)`;;

let eq_op_def = new_definition
  `eq_op x y =
     (if is_Var x /\ is_Var y then NONE else
       match eq_direct x y with NONE -> eq_any x y | SOME res ->
         SOME res)`;;

(* top-level implementations *)

let SmartOp'_def = new_definition
  `SmartOp' tra op xs =
     (match xs with [x] ->
       (match (dest_Op clos_op_dest_Cons) x with SOME (t,xs) ->
         cons_op op t xs | NONE -> NONE) | [x; y] ->
       (match dest_Op_Consts x y with SOME (i,j) -> clos_op_int_op
         op i j | NONE -> (if op = closLang_BlockOp closLang_Equal
         then eq_op x y else NONE)) | _29 -> NONE)`;;

let clos_op_SmartOp_def = new_definition
  `clos_op_SmartOp tra op xs =
     (match SmartOp' tra op xs with NONE -> closLang_Op tra op xs
       | SOME x -> x)`;;
hol4_overload "SmartOp" "clos_op_SmartOp";;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["pmatch"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
