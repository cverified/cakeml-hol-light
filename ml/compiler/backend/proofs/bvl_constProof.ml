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
needs "compiler/backend/semantics/closSem.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

let v_rel_def = cake_define
  `bvl_constProof_v_rel (:'c) (:'ffi) a x y xs ys =
     (match a with Var n -> (\l n. oEL n l) ys n = SOME x | Op _1 _2
       ->
       (x = y) /\
       (!(s:('c,'ffi)bvlSem_state) env. evaluate ([a],env,s) =
         (Rval [x],s)) | _3 -> F)`;;
hol4_overload "v_rel" "bvl_constProof_v_rel";;

let env_rel_def = cake_define
  `bvl_constProof_env_rel x1 x2 x3 e1 e2 =
        match (x1,x2,x3,e1,e2) with
          ((:'c),(:'ffi),[],e1,e2) -> (e1 = e2)
        | ((:'c),(:'ffi),(NONE :: rest),(x :: e1),(y :: e2)) ->
        (x = y) /\ bvl_constProof_env_rel (:'c) (:'ffi) rest e1 e2
        | ((:'c),(:'ffi),(SOME a :: rest),(x :: e1),(y :: e2)) ->
        bvl_constProof_v_rel (:'c) (:'ffi) a x y (x :: e1) (y :: e2)
          /\ bvl_constProof_env_rel (:'c) (:'ffi) rest e1 e2
        | (_4,_5,_6,_7,_8) -> F`;;
hol4_overload "env_rel" "bvl_constProof_env_rel";;

let bvl_constProof_env_rel_length = cake_theorem "env_rel_length"
  (fun () ->
    `!ax env env2. bvl_constProof_env_rel (:'c) (:'ffi) ax env env2
  ==> LENGTH env2 = LENGTH env`)
  CHEAT_TAC;;

let bvl_constProof_env_rel_LLOOKUP_NONE =
  cake_theorem "env_rel_LLOOKUP_NONE[local]"
  (fun () ->
    `!ax env env2 n.
         bvl_constProof_env_rel (:'c) (:'ffi) ax env env2 /\
         ((\l n. oEL n l) ax n = NONE \/ (\l n. oEL n l) ax n =
           SOME NONE) ==>
         EL n env2 = EL n env`)
  CHEAT_TAC;;

let bvl_constProof_env_rel_LOOKUP_SOME =
  cake_theorem "env_rel_LOOKUP_SOME[local]"
  (fun () ->
    `!env env2 ax x n.
         bvl_constProof_env_rel (:'c) (:'ffi) ax env env2 /\
         (\l n. oEL n l) ax n = SOME (SOME x) ==>
         bvl_constProof_v_rel (:'c) (:'ffi) x (EL n env) (EL n
           env2) (DROP n env) (DROP n env2)`)
  CHEAT_TAC;;

let bvl_constProof_evaluate_delete_var_Rerr_SING =
  cake_theorem "evaluate_delete_var_Rerr_SING"
  (fun () ->
    `!x s r e env2.
        evaluate ([x],env2,s) = (Rerr e,r) /\ ~(
        e = Rabort Rtype_error) ==>
        evaluate ([bvl_const_delete_var x],env2,s) = (Rerr e,r)`)
  CHEAT_TAC;;

let bvl_constProof_evaluate_delete_var_Rerr =
  cake_theorem "evaluate_delete_var_Rerr[local]"
  (fun () ->
    `!xs s r e env2.
         evaluate (xs,env2,s) = (Rerr e,r) /\ ~(
         e = Rabort Rtype_error) ==>
         evaluate (MAP bvl_const_delete_var xs,env2,s) = (Rerr
           e,r)`)
  CHEAT_TAC;;

let bvl_constProof_evaluate_delete_var_Rval =
  cake_theorem "evaluate_delete_var_Rval[local]"
  (fun () ->
    `!xs env2 s a r ax env.
         evaluate (xs,env2,(s:('c,'ffi)bvlSem_state)) = (Rval a,r)
           /\
         bvl_constProof_env_rel (:'c) (:'ffi) ax env env2 ==>
         (?b. evaluate (MAP bvl_const_delete_var xs,env2,s) = (Rval
           b,r) /\
             bvl_constProof_env_rel (:'c) (:'ffi)
               (bvl_const_extract_list xs ++ ax) (a ++ env) (b ++
               env2))`)
  CHEAT_TAC;;

let evaluate_EQ_NIL = cake_theorem "evaluate_EQ_NIL"
  (fun () ->
    `bvlSem_evaluate (xs,env,s) = (Rval [],t) <=> xs = [] /\ s = t`)
  CHEAT_TAC;;

let dest_simple_eq = cake_theorem "dest_simple_eq[local]"
  (fun () ->
    `dest_simple h = SOME y <=> (h = Op (closLang_IntOp
  (closLang_Const y)) [])`)
  CHEAT_TAC;;

let case_op_const_eq = cake_theorem "case_op_const_eq[local]"
  (fun () ->
    `case_op_const exp = SOME x <=>
     (?op x1 n2. x = (op,x1,n2) /\ (exp = Op op [x1; Op
       (closLang_IntOp (closLang_Const n2)) []]))`)
  CHEAT_TAC;;

let SmartOp_flip_thm = cake_theorem "SmartOp_flip_thm[local]"
  (fun () ->
    `(op',x1',x2') = SmartOp_flip op x1 x2 /\
     evaluate ([Op op [x1; x2]],env,s) = (res,s2) /\ ~(
     res = Rerr (Rabort Rtype_error)) ==>
     evaluate ([Op op' [x1'; x2']],env,s) = (res,s2)`)
  CHEAT_TAC;;

let SmartOp2_thm = cake_theorem "SmartOp2_thm[local]"
  (fun () ->
    `evaluate ([Op op [x1; x2]],env,s) = (res,s2) /\ ~(
     res = Rerr (Rabort Rtype_error)) ==>
     evaluate ([SmartOp2 (op,x1,x2)],env,s) = (res,s2)`)
  CHEAT_TAC;;

let SmartOp1_thm = cake_theorem "SmartOp1_thm"
  (fun () ->
    `evaluate ([Op op [x]],env,s) = (res,s2) /\ ~(
     res = Rerr (Rabort Rtype_error)) ==>
     evaluate ([SmartOp1 op x],env,s) = (res,s2)`)
  CHEAT_TAC;;

let SmartOp_thm = cake_theorem "SmartOp_thm"
  (fun () ->
    `evaluate ([Op op xs],env,s) = (res,s2) /\ ~(
      res = Rerr (Rabort Rtype_error)) ==>
      evaluate ([SmartOp op xs],env,s) = (res,s2)`)
  CHEAT_TAC;;

let bvl_constProof_evaluate_env_rel = cake_theorem "evaluate_env_rel"
  (fun () ->
    `!xs env1 (s1:('c,'ffi)bvlSem_state) ax env2 res s2 ys.
        (evaluate (xs,env1,s1) = (res,s2)) /\
        bvl_constProof_env_rel (:'c) (:'ffi) ax env1 env2 /\ ~(
        res = Rerr (Rabort Rtype_error)) ==>
        (evaluate (compile ax xs,env2,s1) = (res,s2))`)
  CHEAT_TAC;;

(* HOL4 bvl_constProofScript.sml:311-314: a theorem that HOL4 states
   as the value of an ML expression *)

let bvl_constProof_evaluate_compile_exp =
  cake_theorem "evaluate_compile_exp"
  (fun () ->
    `evaluate ([d],env,s) = (r,t) /\ ~(
      r = Rerr (Rabort Rtype_error)) ==>
      evaluate ([bvl_const_compile_exp d],env,s) = (r,t)`)
  CHEAT_TAC;;

let delete_var_code_labels = cake_theorem "delete_var_code_labels[simp]"
  (fun () ->
    `!x. bvlProps_get_code_labels (bvl_const_delete_var x) =
  bvlProps_get_code_labels x`)
  CHEAT_TAC;;

let dest_simple_SOME_code_labels =
  cake_theorem "dest_simple_SOME_code_labels"
  (fun () ->
    `!x y. dest_simple x = SOME y ==> bvlProps_get_code_labels x = {}`)
  CHEAT_TAC;;

let SmartOp2_code_labels = cake_theorem "SmartOp2_code_labels[simp]"
  (fun () ->
    `bvlProps_get_code_labels (SmartOp2 (op,x1,x2)) =
      assign_get_code_label op UNION bvlProps_get_code_labels x1
        UNION bvlProps_get_code_labels x2`)
  CHEAT_TAC;;

let SmartOp1_code_labels = cake_theorem "SmartOp1_code_labels"
  (fun () ->
    `bvlProps_get_code_labels (SmartOp1 op x) =
  bvlProps_get_code_labels (Op op [x])`)
  CHEAT_TAC;;

let SmartOp_code_labels = cake_theorem "SmartOp_code_labels[simp]"
  (fun () ->
    `bvlProps_get_code_labels (SmartOp op xs) =
     assign_get_code_label op UNION BIGUNION (set_of_list (MAP
       bvlProps_get_code_labels xs))`)
  CHEAT_TAC;;

let MEM_extract_list_code_labels =
  cake_theorem "MEM_extract_list_code_labels"
  (fun () ->
    `!xs x. MEM (SOME x) (bvl_const_extract_list xs) ==>
  bvlProps_get_code_labels x = {}`)
  CHEAT_TAC;;

let bvl_constProof_compile_code_labels =
  cake_theorem "compile_code_labels"
  (fun () ->
    `!x y. BIGUNION (set_of_list (MAP bvlProps_get_code_labels
  (bvl_const_compile x y))) SUBSET
           BIGUNION (set_of_list (MAP bvlProps_get_code_labels y))
             UNION
           BIGUNION (set_of_list (MAP (bvlProps_get_code_labels o
             THE) (FILTER IS_SOME x)))`)
  CHEAT_TAC;;

let bvl_constProof_compile_exp_code_labels =
  cake_theorem "compile_exp_code_labels"
  (fun () ->
    `!e. bvlProps_get_code_labels (bvl_const_compile_exp e) SUBSET
  bvlProps_get_code_labels e`)
  CHEAT_TAC;;
