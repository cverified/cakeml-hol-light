(* ======================================================== *)
(*  bvl_constProof: ported from HOL4's
    compiler/backend/proofs/bvl_constProofScript.sml
    A proof theory about bvl_const.ml, with 2 definitions and 24
    theorems.  Needed by bvl_handleProof.ml and bvl_to_bviProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for bvl_const
*)

needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "bvl_constProof"
  ["bvlProps"; "bvlSem"; "bvl_const"];;

let bvl_constProof_v_rel_def = new_definition
  `bvl_constProof_v_rel (:'c) (:'ffi) a x y xs ys =
     match a with bvl_Var n -> (\l n. oEL n l) ys n = SOME x
     | bvl_Op _ _ ->
       (x = y) /\
       (!(s:('c,'ffi)bvlSem_state) env. bvlSem_evaluate ([a],env,s) = (Rval
         [x],s))
     | _ -> F`;;

make_size "bvlSem_v";;
make_size "bvl_exp";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let bvl_constProof_env_rel_def,bvl_constProof_env_rel_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3,x4).      (\x. 0) x0 +      (\x. 0) x1 +
  list_size (option_size bvl_exp_size) x2 +      bvlSem_v_size1 x3 +
  bvlSem_v_size1 x4)`
  `bvl_constProof_env_rel x1 x2 x3 e1 e2 =
     match (x1,x2,x3,e1,e2) with
       ((:'c),(:'ffi),[],e1,e2) -> (e1 = e2)
     | ((:'c),(:'ffi),CONS NONE rest,CONS x e1,CONS y e2) ->
        (x = y) /\ bvl_constProof_env_rel (:'c) (:'ffi) rest e1 e2
     | ((:'c),(:'ffi),CONS (SOME a) rest,CONS x e1,CONS y e2) ->
        bvl_constProof_v_rel (:'c) (:'ffi) a x y (CONS x e1) (CONS y e2)
          /\ bvl_constProof_env_rel (:'c) (:'ffi) rest e1 e2
     | (_,_,_,_,_) -> F`;;

(* env_rel_length *)
let bvl_constProof_env_rel_length = prove
 (`!ax env env2. bvl_constProof_env_rel (:'c) (:'ffi) ax env env2 ==> LENGTH
  env2 = LENGTH env`,
  CHEAT_TAC);;

(* env_rel_LLOOKUP_NONE[local] *)
let bvl_constProof_env_rel_LLOOKUP_NONE = prove
 (`!ax env env2 n.
       bvl_constProof_env_rel (:'c) (:'ffi) ax env env2 /\
       ((\l n. oEL n l) ax n = NONE \/ (\l n. oEL n l) ax n = SOME NONE) ==>
       EL n env2 = EL n env`,
  CHEAT_TAC);;

(* env_rel_LOOKUP_SOME[local] *)
let bvl_constProof_env_rel_LOOKUP_SOME = prove
 (`!env env2 ax x n.
       bvl_constProof_env_rel (:'c) (:'ffi) ax env env2 /\
       (\l n. oEL n l) ax n = SOME (SOME x) ==>
       bvl_constProof_v_rel (:'c) (:'ffi) x (EL n env) (EL n env2) (DROP n
         env) (DROP n env2)`,
  CHEAT_TAC);;

(* evaluate_delete_var_Rerr_SING *)
let bvl_constProof_evaluate_delete_var_Rerr_SING = prove
 (`!x s r e env2.
      bvlSem_evaluate ([x],env2,s) = (Rerr e,r) /\ ~(e = Rabort Rtype_error)
        ==>
      bvlSem_evaluate ([bvl_const_delete_var x],env2,s) = (Rerr e,r)`,
  CHEAT_TAC);;

(* evaluate_delete_var_Rerr[local] *)
let bvl_constProof_evaluate_delete_var_Rerr = prove
 (`!xs s r e env2.
       bvlSem_evaluate (xs,env2,s) = (Rerr e,r) /\ ~(e = Rabort Rtype_error)
         ==>
       bvlSem_evaluate (MAP bvl_const_delete_var xs,env2,s) = (Rerr e,r)`,
  CHEAT_TAC);;

(* evaluate_delete_var_Rval[local] *)
let bvl_constProof_evaluate_delete_var_Rval = prove
 (`!xs env2 s a r ax env.
       bvlSem_evaluate (xs,env2,(s:('c,'ffi)bvlSem_state)) = (Rval a,r) /\
       bvl_constProof_env_rel (:'c) (:'ffi) ax env env2 ==>
       (?b. bvlSem_evaluate (MAP bvl_const_delete_var xs,env2,s) = (Rval
         b,r) /\
           bvl_constProof_env_rel (:'c) (:'ffi) (APPEND
             (bvl_const_extract_list xs) ax) (APPEND a env) (APPEND b env2))`,
  CHEAT_TAC);;

let evaluate_EQ_NIL = prove
 (`bvlSem_evaluate (xs,env,s) = (Rval [],t) <=> xs = [] /\ s = t`,
  CHEAT_TAC);;

(* [local] *)
let dest_simple_eq = prove
 (`dest_simple h = SOME y <=> (h = bvl_Op (clos_IntOp (clos_Const y)) [])`,
  CHEAT_TAC);;

(* [local] *)
let case_op_const_eq = prove
 (`case_op_const exp = SOME x <=>
   (?op x1 n2. x = (op,x1,n2) /\ (exp = bvl_Op op [x1; bvl_Op (clos_IntOp
     (clos_Const n2)) []]))`,
  CHEAT_TAC);;

(* [local] *)
let SmartOp_flip_thm = prove
 (`(op',x1',x2') = SmartOp_flip op x1 x2 /\
   bvlSem_evaluate ([bvl_Op op [x1; x2]],env,s) = (res,s2) /\ ~(res = Rerr
     (Rabort Rtype_error)) ==>
   bvlSem_evaluate ([bvl_Op op' [x1'; x2']],env,s) = (res,s2)`,
  CHEAT_TAC);;

(* [local] *)
let SmartOp2_thm = prove
 (`bvlSem_evaluate ([bvl_Op op [x1; x2]],env,s) = (res,s2) /\ ~(res = Rerr
  (Rabort Rtype_error)) ==>
   bvlSem_evaluate ([SmartOp2 (op,x1,x2)],env,s) = (res,s2)`,
  CHEAT_TAC);;

let SmartOp1_thm = prove
 (`bvlSem_evaluate ([bvl_Op op [x]],env,s) = (res,s2) /\ ~(res = Rerr (Rabort
  Rtype_error)) ==>
   bvlSem_evaluate ([SmartOp1 op x],env,s) = (res,s2)`,
  CHEAT_TAC);;

let SmartOp_thm = prove
 (`bvlSem_evaluate ([bvl_Op op xs],env,s) = (res,s2) /\ ~(res = Rerr (Rabort
  Rtype_error)) ==>
    bvlSem_evaluate ([bvl_const_SmartOp op xs],env,s) = (res,s2)`,
  CHEAT_TAC);;

(* evaluate_env_rel *)
let bvl_constProof_evaluate_env_rel = prove
 (`!xs env1 (s1:('c,'ffi)bvlSem_state) ax env2 res s2 ys.
      (bvlSem_evaluate (xs,env1,s1) = (res,s2)) /\
      bvl_constProof_env_rel (:'c) (:'ffi) ax env1 env2 /\ ~(res = Rerr
        (Rabort Rtype_error)) ==>
      (bvlSem_evaluate (bvl_const_compile ax xs,env2,s1) = (res,s2))`,
  CHEAT_TAC);;

let bvl_constProof_compile_thm =
  SIMP_RULE [bvl_constProof_env_rel_def] (GEN_ALL (CAKE_SPECL [`xs`; `env`;
  `s1`; `[]`; `env`] bvl_constProof_evaluate_env_rel));;

(* evaluate_compile_exp *)
let bvl_constProof_evaluate_compile_exp = prove
 (`bvlSem_evaluate ([d],env,s) = (r,t) /\ ~(r = Rerr (Rabort Rtype_error)) ==>
    bvlSem_evaluate ([bvl_const_compile_exp d],env,s) = (r,t)`,
  CHEAT_TAC);;

let delete_var_code_labels = prove
 (`!x. bvlProps_get_code_labels (bvl_const_delete_var x) =
  bvlProps_get_code_labels x`,
  CHEAT_TAC);;
add_simp delete_var_code_labels;;

let dest_simple_SOME_code_labels = prove
 (`!x y. dest_simple x = SOME y ==> bvlProps_get_code_labels x = {}`,
  CHEAT_TAC);;

let SmartOp2_code_labels = prove
 (`bvlProps_get_code_labels (SmartOp2 (op,x1,x2)) =
    assign_get_code_label op UNION bvlProps_get_code_labels x1 UNION
      bvlProps_get_code_labels x2`,
  CHEAT_TAC);;
add_simp SmartOp2_code_labels;;

let SmartOp1_code_labels = prove
 (`bvlProps_get_code_labels (SmartOp1 op x) = bvlProps_get_code_labels
  (bvl_Op op [x])`,
  CHEAT_TAC);;

let SmartOp_code_labels = prove
 (`bvlProps_get_code_labels (bvl_const_SmartOp op xs) =
   assign_get_code_label op UNION UNIONS (set_of_list (MAP
     bvlProps_get_code_labels xs))`,
  CHEAT_TAC);;
add_simp SmartOp_code_labels;;

let MEM_extract_list_code_labels = prove
 (`!xs x. MEM (SOME x) (bvl_const_extract_list xs) ==>
  bvlProps_get_code_labels x = {}`,
  CHEAT_TAC);;

(* compile_code_labels *)
let bvl_constProof_compile_code_labels = prove
 (`!x y. UNIONS (set_of_list (MAP bvlProps_get_code_labels (bvl_const_compile x
  y))) SUBSET
         UNIONS (set_of_list (MAP bvlProps_get_code_labels y)) UNION
         UNIONS (set_of_list (MAP (bvlProps_get_code_labels o THE) (FILTER
           IS_SOME x)))`,
  CHEAT_TAC);;

(* compile_exp_code_labels *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let bvl_constProof_compile_exp_code_labels = prove
 (cake_as_vars (fun () ->
    `!e. bvlProps_get_code_labels (bvl_const_compile_exp e) SUBSET
  bvlProps_get_code_labels e`),
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
