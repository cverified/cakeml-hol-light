(* ======================================================== *)
(*  clos_opProof: ported from HOL4's
    compiler/backend/proofs/clos_opProofScript.sml
    A proof theory about clos_op.ml, with 2 definitions and 62
    theorems.  Needed by clos_knownProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for clos_op
*)

needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_op.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "semantics/ast.ml";;

let simple_exp = cake_inductive
  `(!t i. simple_exp (Var t i)) /\
   (!t x y z. simple_exp x /\ simple_exp y /\ simple_exp z ==>
     simple_exp (If t x y z)) /\
   (!t i. simple_exp (closLang_Op t (closLang_IntOp (closLang_Const
     i)) [])) /\
   (!t i. simple_exp (closLang_Op t (closLang_BlockOp
     (closLang_Constant (ConstInt i))) [])) /\
   (!t i. simple_exp (closLang_Op t (closLang_BlockOp
     (closLang_Constant (ConstStr i))) [])) /\
   (!t i. simple_exp (closLang_Op t (closLang_BlockOp
     (closLang_Constant (ConstWord64 i))) [])) /\
   (!t i xs. EVERY simple_exp xs ==> simple_exp (closLang_Op t
     (closLang_BlockOp (closLang_Cons i)) xs)) /\
   (!t i x. simple_exp x ==> simple_exp (closLang_Op t
     (closLang_BlockOp (closLang_EqualConst (closLang_Int i))) [x])) /\
   (!t i x. simple_exp x ==> simple_exp (closLang_Op t
     (closLang_BlockOp (closLang_EqualConst (closLang_Str i))) [x])) /\
   (!t i x. simple_exp x ==> simple_exp (closLang_Op t
     (closLang_BlockOp (closLang_EqualConst (W64 i))) [x])) /\
   (!t i x. simple_exp x ==> simple_exp (closLang_Op t
     (closLang_BlockOp (closLang_ElemAt i)) [x])) /\
   (!t x y. simple_exp x /\ simple_exp y ==> simple_exp (closLang_Op
     t (closLang_BlockOp closLang_Equal) [x; y])) /\
   (!t l y x. simple_exp x ==> simple_exp (closLang_Op t
     (closLang_BlockOp (closLang_TagLenEq l y)) [x]))`;;

let red_rel = cake_inductive
  `((!xs ys t op iop i tag t1 t2 s w.
       red_rel xs ys /\
       MEM op [
         closLang_IntOp iop;
         closLang_BlockOp closLang_Equal; closLang_BlockOp
           (closLang_Cons tag); closLang_BlockOp (closLang_ElemAt t1);
         closLang_BlockOp (closLang_TagLenEq t1 t2); closLang_BlockOp
           (closLang_LenEq n); closLang_BlockOp (closLang_TagEq tag);
         closLang_BlockOp (closLang_EqualConst (closLang_Str s));
         closLang_BlockOp (closLang_EqualConst (W64 w));
         closLang_BlockOp (closLang_EqualConst (closLang_Int i));
         closLang_BlockOp (closLang_Constant (ConstInt i));
         closLang_BlockOp (closLang_Constant (ConstStr s));
         closLang_BlockOp (closLang_Constant (ConstWord64 w))] ==>
       red_rel [closLang_Op t op xs] ys)) /\
   ((red_rel [] [])) /\
   ((!x. red_rel [x] [x])) /\
   ((!v t. red_rel [Var t v] [])) /\
   ((!x y zs x1 x2.
       red_rel [x] x1 /\ red_rel (y :: zs) x2 ==>
       red_rel (x :: y :: zs) (x1 ++ x2))) /\
   ((!xs x x1 t.
       red_rel xs x1 /\ red_rel [x] [] ==>
       red_rel [Let t xs x] x1)) /\
   ((!x y z x1 x2 x3.
       red_rel [x] x1 /\ red_rel [y] x2 /\ red_rel [z] x3 ==>
       red_rel [If t x y z] (x1 ++ x2 ++ x3)))`;;
