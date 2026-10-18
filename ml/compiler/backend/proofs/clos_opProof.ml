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
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;


let list_split3 = cake_theorem "list_split3[local]"
  (fun () ->
    `!P. P [] /\ (!x y z zs. P (x :: y :: z :: zs)) /\ (!x. P [x]) /\
  (!x y. P [x; y]) ==>
         (!xs. P xs)`)
  CHEAT_TAC;;

let evaluate_MakeBool = cake_theorem "evaluate_MakeBool[local]"
  (fun () ->
    `!b. closSem_evaluate ([MakeBool b],vs,s) = (Rval [Boolv b],s)`)
  CHEAT_TAC;;

let dest_Op_thm = cake_theorem "dest_Op_thm"
  (fun () ->
    `dest_Op f x = SOME (i,ys) <=>
     (?tra y. x = closLang_Op tra y ys /\ f y = SOME i)`)
  CHEAT_TAC;;

let dest_Op_Nil_thm = cake_theorem "dest_Op_Nil_thm"
  (fun () ->
    `dest_Op_Nil f x = SOME i <=>
     (?tra y. x = closLang_Op tra y [] /\ f y = SOME i)`)
  CHEAT_TAC;;

let dest_Const_thm = cake_theorem "dest_Const_thm"
  (fun () ->
    `dest_Const x = SOME i <=> x = closLang_IntOp (closLang_Const i)`)
  CHEAT_TAC;;

let dest_Constant_thm = cake_theorem "dest_Constant_thm"
  (fun () ->
    `clos_op_dest_Constant x = SOME i <=>
     (?s w j.
       x = closLang_BlockOp (closLang_Constant (ConstStr s)) /\ i =
         closLang_Str s \/
       x = closLang_BlockOp (closLang_Constant (ConstInt j)) /\ i =
         closLang_Int j \/
       x = closLang_BlockOp (closLang_Constant (ConstWord64 w))
         /\ i = W64 w)`)
  CHEAT_TAC;;

let dest_Cons_thm = cake_theorem "dest_Cons_thm"
  (fun () ->
    `clos_op_dest_Cons x = SOME i <=> x = closLang_BlockOp
  (closLang_Cons i)`)
  CHEAT_TAC;;

let eq_direct_thm = cake_theorem "eq_direct_thm"
  (fun () ->
    `!x y env s res s1 t z.
       closSem_evaluate ([closLang_Op t (closLang_BlockOp
         closLang_Equal) [x; y]],env,s) = (res,s1) /\ ~(res = Rerr
         (Rabort Rtype_error)) /\
       eq_direct x y = SOME z ==>
       closSem_evaluate ([z],env,s) = (res,s1)`)
  CHEAT_TAC;;

let dont_lift_thm = cake_theorem "dont_lift_thm"
  (fun () ->
    `dont_lift x <=>
     (?t i. x = closLang_Op t (closLang_IntOp (closLang_Const i))
       []) \/
     (?t n. x = closLang_Op t (closLang_BlockOp (closLang_Cons n))
       []) \/
     (?t s. x = closLang_Op t (closLang_BlockOp (closLang_Constant
       (ConstStr s))) []) \/
     (?t i. x = closLang_Op t (closLang_BlockOp (closLang_Constant
       (ConstInt i))) []) \/
     (?t w. x = closLang_Op t (closLang_BlockOp
       (closLang_Constant (ConstWord64 w))) [])`)
  CHEAT_TAC;;

let dont_lift_pure = cake_theorem "dont_lift_pure"
  (fun () ->
    `dont_lift x ==> pure x`)
  CHEAT_TAC;;

let dont_lift_Rval = cake_theorem "dont_lift_Rval"
  (fun () ->
    `dont_lift x /\ closSem_evaluate ([x],env,s1) = (res,s2) ==>
     (?v. res = Rval [v] /\ s2 = s1)`)
  CHEAT_TAC;;

let evaluate_dont_lift = cake_theorem "evaluate_dont_lift"
  (fun () ->
    `closSem_evaluate ([x],env,s1) = (Rval
  [v],(s2:('a,'b)closSem_state)) /\ dont_lift x ==>
     closSem_evaluate ([x],env1,s) = (Rval
       [v],(s:('a,'b)closSem_state))`)
  CHEAT_TAC;;

let lift_exps_acc = cake_theorem "lift_exps_acc"
  (fun () ->
    `!xs n binds ys k binds2.
       lift_exps xs n binds = (ys,k,binds2) ==>
       (?binds1. binds2 = binds ++ binds1)`)
  CHEAT_TAC;;

let lift_exps_n = cake_theorem "lift_exps_n"
  (fun () ->
    `!xs n binds ys k binds2.
       lift_exps xs n binds = (ys,k,binds2) /\ n = LENGTH binds ==>
       k = LENGTH binds2`)
  CHEAT_TAC;;

let lift_exps_length = cake_theorem "lift_exps_length"
  (fun () ->
    `!xs n binds ys k binds2.
       lift_exps xs n binds = (ys,k,binds2) ==>
       LENGTH xs = LENGTH ys`)
  CHEAT_TAC;;

let lift_exps_thm = cake_theorem "lift_exps_thm"
  (fun () ->
    `!xs n binds env s0 ys k vs0 binds2 s1 (s2:('a,'b)closSem_state)
  res0.
       closSem_evaluate (binds,env,s0) = (Rval vs0,s1) /\
       closSem_evaluate (xs,env,s1) = (res0,s2) /\ n = LENGTH binds
         /\
       lift_exps xs n binds = (ys,k,binds2) ==>
       (?res.
         closSem_evaluate (binds2,env,s0) = (res,s2) /\
         (!err. res = Rerr err ==> res0 = res) /\
         (!ws (s3:('a,'b)closSem_state) bind_vals.
           res = Rval bind_vals ==>
           (?vs. res0 = Rval vs /\
                closSem_evaluate (ys,bind_vals ++ ws,s3) = (Rval
                  vs,s3))))`)
  CHEAT_TAC;;

let lift_exps_Let = cake_theorem "lift_exps_Let"
  (fun () ->
    `lift_exps [x] 0 [] = ([y],n,binds) /\
     closSem_evaluate ([x],env,s1) = (res,s2) ==>
     closSem_evaluate ([Let backend_common_None binds y],env,s1)
       = (res,s2)`)
  CHEAT_TAC;;

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

let simple_exp_pure = cake_theorem "simple_exp_pure"
  (fun () ->
    `!x. simple_exp x ==> pure x`)
  CHEAT_TAC;;

let simple_exp_pure_every = cake_theorem "simple_exp_pure_every"
  (fun () ->
    `EVERY simple_exp xs ==> EVERY pure xs`)
  CHEAT_TAC;;

let lift_exps_simple_exp = cake_theorem "lift_exps_simple_exp"
  (fun () ->
    `!xs n binds ys k binds2.
       lift_exps xs n binds = (ys,k,binds2) ==> EVERY simple_exp
         ys`)
  CHEAT_TAC;;

let evaluate_ConjList_append_F =
  cake_theorem "evaluate_ConjList_append_F"
  (fun () ->
    `!xs ys.
       closSem_evaluate ([ConjList xs],env1,r) = (Rval [Boolv F],r)
         /\ EVERY pure xs ==>
       closSem_evaluate ([ConjList (xs ++ ys)],env1,r) = (Rval
         [Boolv F],(r:('c,'ffi)closSem_state))`)
  CHEAT_TAC;;

let evaluate_ConjList_append_T =
  cake_theorem "evaluate_ConjList_append_T"
  (fun () ->
    `!xs ys.
       closSem_evaluate ([ConjList xs],env1,r) = (Rval [Boolv T],r)
         /\ EVERY pure xs ==>
       closSem_evaluate ([ConjList (xs ++ ys)],env1,r) =
       closSem_evaluate ([ConjList
         ys],env1,(r:('c,'ffi)closSem_state))`)
  CHEAT_TAC;;

let evaluate_ConjList_F = cake_theorem "evaluate_ConjList_F"
  (fun () ->
    `closSem_evaluate ([x],env,r) = (Rval [Boolv F],r) ==>
     closSem_evaluate ([ConjList (x :: xs)],env,r) = (Rval [Boolv
       F],r)`)
  CHEAT_TAC;;

let evaluate_ConjList_T = cake_theorem "evaluate_ConjList_T"
  (fun () ->
    `closSem_evaluate ([x],env,r) = (Rval [Boolv T],r) /\
     closSem_evaluate ([ConjList xs],env,r) = res ==>
     closSem_evaluate ([ConjList (x :: xs)],env,r) = res`)
  CHEAT_TAC;;

let eq_direct_simple_exp = cake_theorem "eq_direct_simple_exp"
  (fun () ->
    `eq_direct x y = SOME z /\ simple_exp x /\ simple_exp y ==>
  simple_exp z`)
  CHEAT_TAC;;

let simple_exp_eq_pure_list = cake_theorem "simple_exp_eq_pure_list"
  (fun () ->
    `!xs.
       EVERY (\(x,y). simple_exp x /\ simple_exp y) xs ==>
       EVERY simple_exp (append (eq_pure_list xs))`)
  CHEAT_TAC;;

let evaluate_EL = cake_theorem "evaluate_EL"
  (fun () ->
    `!xs i vs.
       closSem_evaluate (xs,env,s) = (Rval vs,s) /\ i < LENGTH xs
         /\ EVERY pure xs ==>
       closSem_evaluate ([EL i xs],env,s) = (Rval [EL i vs],s)`)
  CHEAT_TAC;;

let simpl_exp_Cons_EL = cake_theorem "simpl_exp_Cons_EL"
  (fun () ->
    `simple_exp (closLang_Op tra (closLang_BlockOp (closLang_Cons n))
  xs) /\ i < LENGTH xs ==>
     simple_exp (EL i xs)`)
  CHEAT_TAC;;

let eq_pure_thm = cake_theorem "eq_pure_thm"
  (fun () ->
    `closSem_evaluate ([x1; y1],env1,r) = (Rval [h1; h2],r) /\
  simple_exp x1 /\ simple_exp y1 /\
     do_eq h1 h2 = Eq_val b ==>
     closSem_evaluate ([eq_pure x1 y1],env1,r) = (Rval [Boolv
       b],r)`)
  CHEAT_TAC;;

let clos_opProof_SmartOp_thm = cake_theorem "SmartOp_thm"
  (fun () ->
    `closSem_evaluate ([closLang_Op t op xs],env,s) = (res,s1) /\ ~(res
  = Rerr (Rabort Rtype_error)) ==>
     closSem_evaluate ([clos_op_SmartOp t op xs],env,s) =
       (res,s1)`)
  CHEAT_TAC;;

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

(* HOL4 clos_opProofScript.sml:733-734: a theorem that HOL4 states as
   the value of an ML expression: red_rel_nil *)

let red_rel_ConjList = cake_theorem "red_rel_ConjList"
  (fun () ->
    `!xs. red_rel xs [] ==> red_rel [ConjList xs] []`)
  CHEAT_TAC;;

let red_rel_EVERY = cake_theorem "red_rel_EVERY"
  (fun () ->
    `!xs. EVERY (\h. red_rel [h] []) xs ==> red_rel xs []`)
  CHEAT_TAC;;

let simple_exp_red_rel = cake_theorem "simple_exp_red_rel"
  (fun () ->
    `!xs. EVERY simple_exp xs ==> red_rel xs []`)
  CHEAT_TAC;;

let red_rel_eq_pure = cake_theorem "red_rel_eq_pure"
  (fun () ->
    `simple_exp x /\ simple_exp y ==> red_rel [eq_pure x y] []`)
  CHEAT_TAC;;

let IMP_red_rel_cons_0 = cake_theorem "IMP_red_rel_cons_0"
  (fun () ->
    `red_rel [x] ys /\ red_rel xs zs ==> red_rel (x :: xs) (ys ++ zs)`)
  CHEAT_TAC;;

let red_rel_exists_append = cake_theorem "red_rel_exists_append"
  (fun () ->
    `red_rel (h :: xs) ys <=>
     (?ys1 ys2. red_rel [h] ys1 /\ red_rel xs ys2 /\ ys = ys1 ++
       ys2)`)
  CHEAT_TAC;;

let IMP_red_rel_append = cake_theorem "IMP_red_rel_append"
  (fun () ->
    `!xs ys xs1 ys1.
       red_rel xs ys /\ red_rel xs1 ys1 ==> red_rel (xs ++ xs1)
         (ys ++ ys1)`)
  CHEAT_TAC;;

let IMP_red_rel_cons = cake_theorem "IMP_red_rel_cons"
  (fun () ->
    `red_rel [x] [] /\ red_rel xs ys ==> red_rel (x :: xs) ys`)
  CHEAT_TAC;;

let IMP_red_rel_cons_1 = cake_theorem "IMP_red_rel_cons_1"
  (fun () ->
    `red_rel xs ys ==> red_rel (x :: xs) (x :: ys)`)
  CHEAT_TAC;;

let lift_exps_red_rel = cake_theorem "lift_exps_red_rel"
  (fun () ->
    `!xs n binds ys k binds2.
       lift_exps xs n binds = (ys,k,binds2) ==>
       (?zs. red_rel xs zs /\ red_rel (DROP (LENGTH binds)
         binds2) zs)`)
  CHEAT_TAC;;

let eq_direct_red_rel = cake_theorem "eq_direct_red_rel"
  (fun () ->
    `eq_direct x y = SOME z ==>
     (?ys. red_rel [x; y] ys /\ red_rel [z] ys)`)
  CHEAT_TAC;;

let red_rel_refl = cake_theorem "red_rel_refl"
  (fun () ->
    `!xs. red_rel xs xs`)
  CHEAT_TAC;;

let red_rel_exists = cake_theorem "red_rel_exists"
  (fun () ->
    `!t op xs. ?ys. red_rel [closLang_Op t op xs] ys /\ red_rel
  [clos_op_SmartOp t op xs] ys`)
  CHEAT_TAC;;

let red_rel_pure = cake_theorem "red_rel_pure"
  (fun () ->
    `!xs ys. red_rel xs ys ==> (EVERY pure xs <=> EVERY pure ys)`)
  CHEAT_TAC;;

let red_rel_elist_globals = cake_theorem "red_rel_elist_globals"
  (fun () ->
    `!xs ys. red_rel xs ys ==> (closProps_elist_globals xs =
  closProps_elist_globals ys)`)
  CHEAT_TAC;;

let red_rel_esgc_free = cake_theorem "red_rel_esgc_free"
  (fun () ->
    `!xs ys. red_rel xs ys ==> (EVERY closProps_esgc_free xs <=> EVERY
  closProps_esgc_free ys)`)
  CHEAT_TAC;;

let SmartOp_simp = cake_theorem "SmartOp_simp"
  (fun () ->
    `pure (clos_op_SmartOp t op xs) = pure (closLang_Op t op xs) /\
     closProps_set_globals (clos_op_SmartOp t op xs) =
       closProps_set_globals (closLang_Op t op xs) /\
     closProps_esgc_free (clos_op_SmartOp t op xs) =
       closProps_esgc_free (closLang_Op t op xs)`)
  CHEAT_TAC;;

let SmartOp_Const = cake_theorem "SmartOp_Const"
  (fun () ->
    `!xs. clos_op_SmartOp t (closLang_IntOp (closLang_Const i)) xs =
  closLang_Op t (closLang_IntOp (closLang_Const i)) xs`)
  CHEAT_TAC;;

let SmartOp_Cons = cake_theorem "SmartOp_Cons"
  (fun () ->
    `!xs. clos_op_SmartOp t (closLang_BlockOp (closLang_Cons n)) xs =
  closLang_Op t (closLang_BlockOp (closLang_Cons n)) xs`)
  CHEAT_TAC;;

let SmartOp_Install = cake_theorem "SmartOp_Install"
  (fun () ->
    `clos_op_SmartOp t (closLang_Install:closLang_op) = closLang_Op t
  closLang_Install`)
  CHEAT_TAC;;

let code_locs_SmartOp = cake_theorem "code_locs_SmartOp"
  (fun () ->
    `LIST_TO_BAG (code_locs [clos_op_SmartOp t op xs]) =
     LIST_TO_BAG (code_locs [closLang_Op t op xs])`)
  CHEAT_TAC;;

let every_Fn_SOME_SmartOp = cake_theorem "every_Fn_SOME_SmartOp"
  (fun () ->
    `every_Fn_SOME [clos_op_SmartOp t op xs] = every_Fn_SOME
  [closLang_Op t op xs]`)
  CHEAT_TAC;;

let every_Fn_vs_NONE_SmartOp = cake_theorem "every_Fn_vs_NONE_SmartOp"
  (fun () ->
    `every_Fn_vs_NONE xs ==> every_Fn_vs_NONE [clos_op_SmartOp t op
  xs]`)
  CHEAT_TAC;;

let no_Labels_SmartOp = cake_theorem "no_Labels_SmartOp"
  (fun () ->
    `no_Labels (clos_op_SmartOp t op xs) <=> no_Labels (closLang_Op t
  op xs)`)
  CHEAT_TAC;;

let obeys_max_app_SmartOp = cake_theorem "obeys_max_app_SmartOp"
  (fun () ->
    `EVERY (obeys_max_app k) xs ==> obeys_max_app k (clos_op_SmartOp t
  op xs)`)
  CHEAT_TAC;;

let lift_exps_fv = cake_theorem "lift_exps_fv"
  (fun () ->
    `!xs n binds ys k binds2.
       lift_exps xs n binds = (ys,k,binds2) /\ n = LENGTH binds ==>
       k = LENGTH binds2 /\
       (!l. fv l binds2 ==> fv l xs \/ fv l binds) /\
       (!l. fv l ys ==> l < k)`)
  CHEAT_TAC;;

let fv1_ConjList = cake_theorem "fv1_ConjList"
  (fun () ->
    `!xs. fv1 n (ConjList xs) = fv n xs`)
  CHEAT_TAC;;

let fv1_EL = cake_theorem "fv1_EL"
  (fun () ->
    `!xs n k. fv1 n (EL k xs) /\ k < LENGTH xs ==> fv n xs`)
  CHEAT_TAC;;

let fv1_eq_pure = cake_theorem "fv1_eq_pure"
  (fun () ->
    `fv1 n (eq_pure x y) ==> fv1 n x \/ fv1 n y`)
  CHEAT_TAC;;

let eq_op_fv = cake_theorem "eq_op_fv"
  (fun () ->
    `eq_op x y = SOME z ==> fv n [z] ==> fv n [x] \/ fv n [y]`)
  CHEAT_TAC;;

let fv1_SmartOp = cake_theorem "fv1_SmartOp"
  (fun () ->
    `fv1 n (clos_op_SmartOp t op xs) ==> fv1 n (closLang_Op t op xs)`)
  CHEAT_TAC;;
