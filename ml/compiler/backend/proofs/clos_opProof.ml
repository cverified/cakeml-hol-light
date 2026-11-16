(* ======================================================== *)
(*  clos_opProof: ported from HOL4's
    compiler/backend/proofs/clos_opProofScript.sml
    A proof theory about clos_op.ml, with 2 definitions and 62
    theorems.  Needed by clos_knownProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for clos_op
*)

needs "characteristic/cfFFIType.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_op.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "misc/misc.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "clos_opProof"
  ["closLang"; "closProps"; "closSem"; "clos_op"];;


(* [local] *)
let list_split3 = prove
 (`!P. P [] /\ (!x y z zs. P (CONS x (CONS y (CONS z zs)))) /\ (!x. P [x])
  /\ (!x y. P [x; y]) ==>
       (!xs. P xs)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_MakeBool = prove
 (`!b. closSem_evaluate ([MakeBool b],vs,s) = (Rval [closSem_Boolv b],s)`,
  CHEAT_TAC);;

let dest_Op_thm = prove
 (`dest_Op f x = SOME (i,ys) <=>
   (?tra y. x = clos_Op tra y ys /\ f y = SOME i)`,
  CHEAT_TAC);;

let dest_Op_Nil_thm = prove
 (`dest_Op_Nil f x = SOME i <=>
   (?tra y. x = clos_Op tra y [] /\ f y = SOME i)`,
  CHEAT_TAC);;

let dest_Const_thm = prove
 (`dest_Const x = SOME i <=> x = clos_IntOp (clos_Const i)`,
  CHEAT_TAC);;

let dest_Constant_thm = prove
 (`clos_op_dest_Constant x = SOME i <=>
   (?s w j.
     x = clos_BlockOp (clos_Constant (ConstStr s)) /\ i = clos_Str s \/
     x = clos_BlockOp (clos_Constant (ConstInt j)) /\ i = clos_Int j \/
     x = clos_BlockOp (clos_Constant (ConstWord64 w)) /\ i = clos_W64 w)`,
  CHEAT_TAC);;

let dest_Cons_thm = prove
 (`clos_op_dest_Cons x = SOME i <=> x = clos_BlockOp (clos_Cons i)`,
  CHEAT_TAC);;

let eq_direct_thm = prove
 (`!x y env s res s1 t z.
     closSem_evaluate ([clos_Op t (clos_BlockOp clos_Equal) [x; y]],env,s) =
       (res,s1) /\ ~(res = Rerr (Rabort Rtype_error)) /\
     eq_direct x y = SOME z ==>
     closSem_evaluate ([z],env,s) = (res,s1)`,
  CHEAT_TAC);;

let dont_lift_thm = prove
 (`dont_lift x <=>
   (?t i. x = clos_Op t (clos_IntOp (clos_Const i)) []) \/
   (?t n. x = clos_Op t (clos_BlockOp (clos_Cons n)) []) \/
   (?t s. x = clos_Op t (clos_BlockOp (clos_Constant (ConstStr s))) []) \/
   (?t i. x = clos_Op t (clos_BlockOp (clos_Constant (ConstInt i))) []) \/
   (?t w. x = clos_Op t (clos_BlockOp (clos_Constant (ConstWord64 w))) [])`,
  CHEAT_TAC);;

let dont_lift_pure = prove
 (`dont_lift x ==> pure x`,
  CHEAT_TAC);;

let dont_lift_Rval = prove
 (`dont_lift x /\ closSem_evaluate ([x],env,s1) = (res,s2) ==>
   (?v. res = Rval [v] /\ s2 = s1)`,
  CHEAT_TAC);;

let evaluate_dont_lift = prove
 (`closSem_evaluate ([x],env,s1) = (Rval [v],(s2:('a,'b)closSem_state))
  /\ dont_lift x ==>
   closSem_evaluate ([x],env1,s) = (Rval [v],(s:('a,'b)closSem_state))`,
  CHEAT_TAC);;

let lift_exps_acc = prove
 (`!xs n binds ys k binds2.
     lift_exps xs n binds = (ys,k,binds2) ==>
     (?binds1. binds2 = APPEND binds binds1)`,
  CHEAT_TAC);;

let lift_exps_n = prove
 (`!xs n binds ys k binds2.
     lift_exps xs n binds = (ys,k,binds2) /\ n = LENGTH binds ==>
     k = LENGTH binds2`,
  CHEAT_TAC);;

let lift_exps_length = prove
 (`!xs n binds ys k binds2.
     lift_exps xs n binds = (ys,k,binds2) ==>
     LENGTH xs = LENGTH ys`,
  CHEAT_TAC);;

let lift_exps_thm = prove
 (`!xs n binds env s0 ys k vs0 binds2 s1 (s2:('a,'b)closSem_state) res0.
     closSem_evaluate (binds,env,s0) = (Rval vs0,s1) /\
     closSem_evaluate (xs,env,s1) = (res0,s2) /\ n = LENGTH binds /\
     lift_exps xs n binds = (ys,k,binds2) ==>
     (?res.
       closSem_evaluate (binds2,env,s0) = (res,s2) /\
       (!err. res = Rerr err ==> res0 = res) /\
       (!ws (s3:('a,'b)closSem_state) bind_vals.
         res = Rval bind_vals ==>
         (?vs. res0 = Rval vs /\
              closSem_evaluate (ys,APPEND bind_vals ws,s3) = (Rval
                vs,s3))))`,
  CHEAT_TAC);;

let lift_exps_Let = prove
 (`lift_exps [x] 0 [] = ([y],n,binds) /\
   closSem_evaluate ([x],env,s1) = (res,s2) ==>
   closSem_evaluate ([clos_Let backend_common_None binds y],env,s1) =
     (res,s2)`,
  CHEAT_TAC);;

let simple_exp = cake_inductive
  `(!t i. clos_opProof_simple_exp (clos_Var t i)) /\
   (!t x y z. clos_opProof_simple_exp x /\ clos_opProof_simple_exp y
     /\ clos_opProof_simple_exp z ==> clos_opProof_simple_exp (clos_If t x y
     z)) /\
   (!t i. clos_opProof_simple_exp (clos_Op t (clos_IntOp (clos_Const i))
     [])) /\
   (!t i. clos_opProof_simple_exp (clos_Op t (clos_BlockOp (clos_Constant
     (ConstInt i))) [])) /\
   (!t i. clos_opProof_simple_exp (clos_Op t (clos_BlockOp (clos_Constant
     (ConstStr i))) [])) /\
   (!t i. clos_opProof_simple_exp (clos_Op t (clos_BlockOp (clos_Constant
     (ConstWord64 i))) [])) /\
   (!t i xs. ALL clos_opProof_simple_exp xs ==> clos_opProof_simple_exp
     (clos_Op t (clos_BlockOp (clos_Cons i)) xs)) /\
   (!t i x. clos_opProof_simple_exp x ==> clos_opProof_simple_exp (clos_Op t
     (clos_BlockOp (clos_EqualConst (clos_Int i))) [x])) /\
   (!t i x. clos_opProof_simple_exp x ==> clos_opProof_simple_exp (clos_Op t
     (clos_BlockOp (clos_EqualConst (clos_Str i))) [x])) /\
   (!t i x. clos_opProof_simple_exp x ==> clos_opProof_simple_exp (clos_Op t
     (clos_BlockOp (clos_EqualConst (clos_W64 i))) [x])) /\
   (!t i x. clos_opProof_simple_exp x ==> clos_opProof_simple_exp (clos_Op t
     (clos_BlockOp (clos_ElemAt i)) [x])) /\
   (!t x y. clos_opProof_simple_exp x /\ clos_opProof_simple_exp y ==>
     clos_opProof_simple_exp (clos_Op t (clos_BlockOp clos_Equal) [x; y])) /\
   (!t l y x. clos_opProof_simple_exp x ==> clos_opProof_simple_exp
     (clos_Op t (clos_BlockOp (clos_TagLenEq l y)) [x]))`;;

let simple_exp_pure = prove
 (`!x. clos_opProof_simple_exp x ==> pure x`,
  CHEAT_TAC);;

let simple_exp_pure_every = prove
 (`ALL clos_opProof_simple_exp xs ==> ALL pure xs`,
  CHEAT_TAC);;

let lift_exps_simple_exp = prove
 (`!xs n binds ys k binds2.
     lift_exps xs n binds = (ys,k,binds2) ==> ALL clos_opProof_simple_exp
       ys`,
  CHEAT_TAC);;

let evaluate_ConjList_append_F = prove
 (`!xs ys.
     closSem_evaluate ([ConjList xs],env1,r) = (Rval [closSem_Boolv F],r)
       /\ ALL pure xs ==>
     closSem_evaluate ([ConjList (APPEND xs ys)],env1,r) = (Rval
       [closSem_Boolv F],(r:('c,'ffi)closSem_state))`,
  CHEAT_TAC);;

let evaluate_ConjList_append_T = prove
 (`!xs ys.
     closSem_evaluate ([ConjList xs],env1,r) = (Rval [closSem_Boolv T],r)
       /\ ALL pure xs ==>
     closSem_evaluate ([ConjList (APPEND xs ys)],env1,r) =
     closSem_evaluate ([ConjList ys],env1,(r:('c,'ffi)closSem_state))`,
  CHEAT_TAC);;

let evaluate_ConjList_F = prove
 (`closSem_evaluate ([x],env,r) = (Rval [closSem_Boolv F],r) ==>
   closSem_evaluate ([ConjList (CONS x xs)],env,r) = (Rval [closSem_Boolv
     F],r)`,
  CHEAT_TAC);;

let evaluate_ConjList_T = prove
 (`closSem_evaluate ([x],env,r) = (Rval [closSem_Boolv T],r) /\
   closSem_evaluate ([ConjList xs],env,r) = res ==>
   closSem_evaluate ([ConjList (CONS x xs)],env,r) = res`,
  CHEAT_TAC);;

let eq_direct_simple_exp = prove
 (`eq_direct x y = SOME z /\ clos_opProof_simple_exp x
  /\ clos_opProof_simple_exp y ==> clos_opProof_simple_exp z`,
  CHEAT_TAC);;

let simple_exp_eq_pure_list = prove
 (`!xs.
     ALL (\(x,y). clos_opProof_simple_exp x /\ clos_opProof_simple_exp y) xs
       ==>
     ALL clos_opProof_simple_exp (append (eq_pure_list xs))`,
  CHEAT_TAC);;

let evaluate_EL = prove
 (`!xs i vs.
     closSem_evaluate (xs,env,s) = (Rval vs,s) /\ i < LENGTH xs /\ ALL pure
       xs ==>
     closSem_evaluate ([EL i xs],env,s) = (Rval [EL i vs],s)`,
  CHEAT_TAC);;

let simpl_exp_Cons_EL = prove
 (`clos_opProof_simple_exp (clos_Op tra (clos_BlockOp (clos_Cons n)) xs) /\ i <
  LENGTH xs ==>
   clos_opProof_simple_exp (EL i xs)`,
  CHEAT_TAC);;

let eq_pure_thm = prove
 (`closSem_evaluate ([x1; y1],env1,r) = (Rval [h1; h2],r)
  /\ clos_opProof_simple_exp x1 /\ clos_opProof_simple_exp y1 /\
   closSem_do_eq h1 h2 = Eq_val b ==>
   closSem_evaluate ([eq_pure x1 y1],env1,r) = (Rval [closSem_Boolv b],r)`,
  CHEAT_TAC);;

(* SmartOp_thm *)
let clos_opProof_SmartOp_thm = prove
 (`closSem_evaluate ([clos_Op t op xs],env,s) = (res,s1) /\ ~(res = Rerr
  (Rabort Rtype_error)) ==>
   closSem_evaluate ([clos_op_SmartOp t op xs],env,s) = (res,s1)`,
  CHEAT_TAC);;

let red_rel = cake_inductive
  `((!xs ys t op iop i tag t1 t2 s w.
       red_rel xs ys /\
       MEM op [
         clos_IntOp iop;
         clos_BlockOp clos_Equal; clos_BlockOp (clos_Cons tag); clos_BlockOp
           (clos_ElemAt t1);
         clos_BlockOp (clos_TagLenEq t1 t2); clos_BlockOp (clos_LenEq n);
           clos_BlockOp (clos_TagEq tag);
         clos_BlockOp (clos_EqualConst (clos_Str s));
         clos_BlockOp (clos_EqualConst (clos_W64 w));
         clos_BlockOp (clos_EqualConst (clos_Int i));
         clos_BlockOp (clos_Constant (ConstInt i));
         clos_BlockOp (clos_Constant (ConstStr s));
         clos_BlockOp (clos_Constant (ConstWord64 w))] ==>
       red_rel [clos_Op t op xs] ys)) /\
   ((red_rel [] [])) /\
   ((!x. red_rel [x] [x])) /\
   ((!v t. red_rel [clos_Var t v] [])) /\
   ((!x y zs x1 x2.
       red_rel [x] x1 /\ red_rel (CONS y zs) x2 ==>
       red_rel (CONS x (CONS y zs)) (APPEND x1 x2))) /\
   ((!xs x x1 t.
       red_rel xs x1 /\ red_rel [x] [] ==>
       red_rel [clos_Let t xs x] x1)) /\
   ((!x y z x1 x2 x3.
       red_rel [x] x1 /\ red_rel [y] x2 /\ red_rel [z] x3 ==>
       red_rel [clos_If t x y z] (APPEND (APPEND x1 x2) x3)))`;;

(* HOL4 clos_opProofScript.sml:733-734: a theorem that HOL4 states as the
   value of an ML expression: red_rel_nil *)

let red_rel_ConjList = prove
 (`!xs. red_rel xs [] ==> red_rel [ConjList xs] []`,
  CHEAT_TAC);;

let red_rel_EVERY = prove
 (`!xs. ALL (\h. red_rel [h] []) xs ==> red_rel xs []`,
  CHEAT_TAC);;

let simple_exp_red_rel = prove
 (`!xs. ALL clos_opProof_simple_exp xs ==> red_rel xs []`,
  CHEAT_TAC);;

let red_rel_eq_pure = prove
 (`clos_opProof_simple_exp x /\ clos_opProof_simple_exp y ==> red_rel
  [eq_pure x y] []`,
  CHEAT_TAC);;

let IMP_red_rel_cons_0 = prove
 (`red_rel [x] ys /\ red_rel xs zs ==> red_rel (CONS x xs) (APPEND ys zs)`,
  CHEAT_TAC);;

let red_rel_exists_append = prove
 (`red_rel (CONS h xs) ys <=>
   (?ys1 ys2. red_rel [h] ys1 /\ red_rel xs ys2 /\ ys = APPEND ys1 ys2)`,
  CHEAT_TAC);;

let IMP_red_rel_append = prove
 (`!xs ys xs1 ys1.
     red_rel xs ys /\ red_rel xs1 ys1 ==> red_rel (APPEND xs xs1) (APPEND
       ys ys1)`,
  CHEAT_TAC);;

let IMP_red_rel_cons = prove
 (`red_rel [x] [] /\ red_rel xs ys ==> red_rel (CONS x xs) ys`,
  CHEAT_TAC);;

let IMP_red_rel_cons_1 = prove
 (`red_rel xs ys ==> red_rel (CONS x xs) (CONS x ys)`,
  CHEAT_TAC);;

let lift_exps_red_rel = prove
 (`!xs n binds ys k binds2.
     lift_exps xs n binds = (ys,k,binds2) ==>
     (?zs. red_rel xs zs /\ red_rel (DROP (LENGTH binds) binds2) zs)`,
  CHEAT_TAC);;

let eq_direct_red_rel = prove
 (`eq_direct x y = SOME z ==>
   (?ys. red_rel [x; y] ys /\ red_rel [z] ys)`,
  CHEAT_TAC);;

let red_rel_refl = prove
 (`!xs. red_rel xs xs`,
  CHEAT_TAC);;

let red_rel_exists = prove
 (`!t op xs. ?ys. red_rel [clos_Op t op xs] ys /\ red_rel [clos_op_SmartOp t
  op xs] ys`,
  CHEAT_TAC);;

let red_rel_pure = prove
 (`!xs ys. red_rel xs ys ==> (ALL pure xs <=> ALL pure ys)`,
  CHEAT_TAC);;

let red_rel_elist_globals = prove
 (`!xs ys. red_rel xs ys ==> (closProps_elist_globals xs =
  closProps_elist_globals ys)`,
  CHEAT_TAC);;

let red_rel_esgc_free = prove
 (`!xs ys. red_rel xs ys ==> (ALL closProps_esgc_free xs <=> ALL
  closProps_esgc_free ys)`,
  CHEAT_TAC);;

let SmartOp_simp = prove
 (`pure (clos_op_SmartOp t op xs) = pure (clos_Op t op xs) /\
   closProps_set_globals (clos_op_SmartOp t op xs) = closProps_set_globals
     (clos_Op t op xs) /\
   closProps_esgc_free (clos_op_SmartOp t op xs) = closProps_esgc_free
     (clos_Op t op xs)`,
  CHEAT_TAC);;

let SmartOp_Const = prove
 (`!xs. clos_op_SmartOp t (clos_IntOp (clos_Const i)) xs = clos_Op t
  (clos_IntOp (clos_Const i)) xs`,
  CHEAT_TAC);;

let SmartOp_Cons = prove
 (`!xs. clos_op_SmartOp t (clos_BlockOp (clos_Cons n)) xs = clos_Op t
  (clos_BlockOp (clos_Cons n)) xs`,
  CHEAT_TAC);;

let SmartOp_Install = prove
 (`clos_op_SmartOp t clos_Install = clos_Op t clos_Install`,
  CHEAT_TAC);;

let code_locs_SmartOp = prove
 (`LIST_TO_BAG (code_locs [clos_op_SmartOp t op xs]) =
   LIST_TO_BAG (code_locs [clos_Op t op xs])`,
  CHEAT_TAC);;

let every_Fn_SOME_SmartOp = prove
 (`every_Fn_SOME [clos_op_SmartOp t op xs] = every_Fn_SOME [clos_Op t op xs]`,
  CHEAT_TAC);;

let every_Fn_vs_NONE_SmartOp = prove
 (`every_Fn_vs_NONE xs ==> every_Fn_vs_NONE [clos_op_SmartOp t op xs]`,
  CHEAT_TAC);;

let no_Labels_SmartOp = prove
 (`no_Labels (clos_op_SmartOp t op xs) <=> no_Labels (clos_Op t op xs)`,
  CHEAT_TAC);;

let obeys_max_app_SmartOp = prove
 (`ALL (obeys_max_app k) xs ==> obeys_max_app k (clos_op_SmartOp t op xs)`,
  CHEAT_TAC);;

let lift_exps_fv = prove
 (`!xs n binds ys k binds2.
     lift_exps xs n binds = (ys,k,binds2) /\ n = LENGTH binds ==>
     k = LENGTH binds2 /\
     (!l. fv l binds2 ==> fv l xs \/ fv l binds) /\
     (!l. fv l ys ==> l < k)`,
  CHEAT_TAC);;

let fv1_ConjList = prove
 (`!xs. fv1 n (ConjList xs) = fv n xs`,
  CHEAT_TAC);;

let fv1_EL = prove
 (`!xs n k. fv1 n (EL k xs) /\ k < LENGTH xs ==> fv n xs`,
  CHEAT_TAC);;

let fv1_eq_pure = prove
 (`fv1 n (eq_pure x y) ==> fv1 n x \/ fv1 n y`,
  CHEAT_TAC);;

let eq_op_fv = prove
 (`eq_op x y = SOME z ==> fv n [z] ==> fv n [x] \/ fv n [y]`,
  CHEAT_TAC);;

let fv1_SmartOp = prove
 (`fv1 n (clos_op_SmartOp t op xs) ==> fv1 n (clos_Op t op xs)`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
