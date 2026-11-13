(* ======================================================== *)
(*  bvl_handleProof: ported from HOL4's
    compiler/backend/proofs/bvl_handleProofScript.sml
    A proof theory about bvl_handle.ml, with 3 definitions and 57
    theorems.  Needed by bvl_inlineProof.ml and bvl_to_bviProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for bvl_handle
*)

needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/bvl_handle.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/db_vars.ml";;
needs "compiler/backend/proofs/bvl_constProof.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/indexedLists.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "bvl_handleProof"
  ["bvlProps"; "bvlSem"; "bvl_constProof"; "bvl_handle"];;

let can_raise_thm = prove
 (`(!e env s (s:('a,'b)bvlSem_state).
     evaluate ([e],env,s) = (Rerr (Rraise a),r) ==> can_raise e) /\
   (!es env s (s:('a,'b)bvlSem_state).
     evaluate (es,env,s) = (Rerr (Rraise a),r) ==> can_raise1 es)`,
  CHEAT_TAC);;

(* [simp] *)
let handle_adj_vars_0 = prove
 (`(!x l. handle_adj_vars l 0 x = x) /\
   (!x l. handle_adj_vars1 l 0 x = x)`,
  CHEAT_TAC);;

let evaluate_handle_adj_vars_lemma = prove
 (`(!x xs a env (r:('a,'b)bvlSem_state).
      evaluate ([handle_adj_vars (LENGTH xs) (LENGTH a) x],xs ++ (a
        ++ env),r) =
      evaluate ([x],xs ++ env,r)) /\
   (!x xs a env (r:('a,'b)bvlSem_state).
      evaluate (handle_adj_vars1 (LENGTH xs) (LENGTH a) x,xs ++ (a ++
        env),r) =
      evaluate (x,xs ++ env,r))`,
  CHEAT_TAC);;

let evaluate_handle_adj_vars = prove
 (`!xs l a env r.
     l <= LENGTH env ==>
     evaluate ([handle_adj_vars (LENGTH xs) (l + LENGTH a) x2],xs ++
       (a ++ env),r) =
     evaluate ([handle_adj_vars (LENGTH xs) l x2],xs ++ env,r)`,
  CHEAT_TAC);;

let handle_adj_vars_evaluate = prove
 (`(!env. evaluate ([x1],env,r) = evaluate ([x2],env,r)) /\ d + l <=
  LENGTH env ==>
   evaluate ([handle_adj_vars d l x1],env,r) = evaluate
     ([handle_adj_vars d l x2],env,r)`,
  CHEAT_TAC);;

let evaluate_handle_simp = prove
 (`(!x env (s:('a,'b)bvlSem_state).
      evaluate ([handle_simp x],env,s) =
      evaluate ([x],env,s)) /\
   (!xs env (s:('a,'b)bvlSem_state).
      evaluate (handle_simp_list xs,env,s) =
      evaluate (xs,env,s)) /\
   (!x1 x2 l env (s:('a,'b)bvlSem_state).
      l <= LENGTH env ==>
      evaluate ([make_handle x1 x2 l],env,s) =
      evaluate ([Handle x1 (handle_adj_vars 1 l x2)],env,s))`,
  CHEAT_TAC);;

(* [simp] *)
let evaluate_SmartLet = prove
 (`bvlSem_evaluate ([SmartLet xs x],env,s) = evaluate ([Let xs
  x],env,s)`,
  CHEAT_TAC);;

let let_ok_def = cake_define
  `let_ok x1 =
        match x1 with
          (Let xs b:bvl_exp) -> EVERY isVar xs /\ bVarBound (LENGTH
            xs) [b]
        | _1 -> F`;;

let _ = size_thms "bvl_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let handle_ok_def = cake_define_list_try_tac (fun () ->
  `MEASURE (list_size bvl_exp_size)`)
  CHEAT_TAC
  [`handle_ok [] <=> T`;
   `handle_ok ((x:bvl_exp) :: y :: xs) <=>
         handle_ok [x] /\ handle_ok (y :: xs)`;
   `handle_ok [(Var v:bvl_exp)] <=> T`;
   `handle_ok [(If x1 x2 x3:bvl_exp)] <=>
         handle_ok [x1] /\ handle_ok [x2] /\ handle_ok [x3]`;
   `handle_ok [(Let xs x2:bvl_exp)] <=>
         (if LENGTH xs = 0 then
           let_ok x2 /\ (!ys y. x2 = Let ys y ==> handle_ok [y])
             else
           handle_ok xs /\ handle_ok [x2])`;
   `handle_ok [(Raise x1:bvl_exp)] <=> handle_ok [x1]`;
   `handle_ok [(Tick x1:bvl_exp)] <=> handle_ok [x1]`;
   `handle_ok [(Op op xs:bvl_exp)] <=> handle_ok xs`;
   `handle_ok [(Handle x1 x2:bvl_exp)] <=>
         (match x1 with Let xs b ->
             EVERY isVar xs /\ bVarBound (LENGTH xs) [b] /\
             handle_ok [b] /\ handle_ok [x2] | _4 -> F)`;
   `handle_ok [(Force loc n:bvl_exp)] <=> T`;
   `handle_ok [(Call ticks dest xs:bvl_exp)] <=> handle_ok xs`];;

(* HOL4 bvl_handleProofScript.sml:192-195: a theorem that HOL4 states
   as the value of an ML expression: evaluate_GENLIST *)

let bvl_handleProof_env_rel_def = cake_define
  `bvl_handleProof_env_rel l env env1 =
     LIST_RELi (\i v1 v2. has_var i l ==> v1 = v2) env env1`;;
hol4_overload "env_rel" "bvl_handleProof_env_rel";;

let env_rel_mk_Union = prove
 (`!env env1. env_rel (mk_Union lx ly) env env1 <=>
               env_rel lx env env1 /\ env_rel ly env env1`,
  CHEAT_TAC);;

(* env_rel_length *)
let bvl_handleProof_env_rel_length = prove
 (`env_rel l env env1 ==> LENGTH env1 = LENGTH env`,
  CHEAT_TAC);;

let env_rel_MAPi = prove
 (`env_rel l1 env (MAPi (\i v. if has_var i l1 then v else Number
  (&0)) env)`,
  CHEAT_TAC);;

let IMP_EL_SING = prove
 (`k = LENGTH xs ==> EL k (xs ++ [x] ++ ys) = x`,
  CHEAT_TAC);;

(* HOL4 bvl_handleProofScript.sml:228-233: a theorem that HOL4 states
   as the value of an ML expression: ALOOKUP_MAPi_SWAP *)

(* HOL4 bvl_handleProofScript.sml:235-239: a theorem that HOL4 states
   as the value of an ML expression: ALOOKUP_MAPi_APPEND2 *)

let IS_SOME_lookup_db_to_set = prove
 (`!n. IS_SOME (sptree_lookup n (db_to_set l)) = has_var n l`,
  CHEAT_TAC);;

let evaluate_LetLet = prove
 (`(!env2 extra.
       env_rel l1 env env2 ==> evaluate ([y],env2 ++ extra,s1) = res)
         /\
    env_rel l1 env env1 ==>
    evaluate ([LetLet (LENGTH env) (db_to_set l1) y],env1 ++
      extra,s1) = res`,
  CHEAT_TAC);;

let env_rel_refl = prove
 (`env_rel l env env`,
  CHEAT_TAC);;

(* [local] *)
let opt_lemma = prove
 (`x = y <=> (x = SOME one <=> y = SOME one)`,
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let OptionalLetLet_IMP = prove
 (cake_as_vars (fun () ->
    `(ys,l,s',nr') = OptionalLetLet y (LENGTH env) lx s1 limit nr /\
       (!env2 extra.
         env_rel l env env2 ==> evaluate ([y],env2 ++ extra,s) =
           res) /\
       env_rel l env env1 /\ b ==>
       evaluate (ys,env1 ++ extra,s) = res /\ b`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let OptionalLetLet_limit = prove
 (cake_as_vars (fun () ->
    `(ys,l,s',nr') = OptionalLetLet e (LENGTH env) lx s1 limit nr /\
      env_rel l env env1 ==> env_rel lx env env1`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let OptionalLetLet_nr = prove
 (cake_as_vars (fun () ->
    `(ys,l,s',nr') = OptionalLetLet e (LENGTH env) lx s1 limit nr ==>
      nr' = nr`),
  CHEAT_TAC);;

(* HOL4 bvl_handleProofScript.sml:352-473: a theorem that HOL4 states
   as the value of an ML expression: compile_correct *)

(* [allow_rebind] *)
let bvl_handleProof_compile_correct = bvi_to_dataProof_compile_correct;;

(* compile_correct[allow_rebind] *)
let bvl_handleProof_compile_correct = prove
 (`(evaluate ([x],env,s1) = (res,s2)) /\ ~(res = Rerr (Rabort
  Rtype_error)) /\
    k = LENGTH env ==>
    (evaluate ([compile_exp l k x],env,s1) = (res,s2))`,
  CHEAT_TAC);;

let dest_Seq_thm = prove
 (`!x. bvl_handle_dest_Seq x = SOME (y0,y1) <=>
        x = Let [y0; y1] (bvl_Var 1)`,
  CHEAT_TAC);;

let compile_seqs_correct = prove
 (`!l x acc s1 s2 s3 res res3.
      evaluate ([x],[],s1) = (res,s2) /\
      (!y r. acc = SOME y /\ res = Rval r ==> ~(res3 = Rerr (Rabort
        Rtype_error)) /\
             evaluate ([y],[],s2) = (res3,s3)) /\ ~(res = Rerr
               (Rabort Rtype_error)) ==>
      evaluate ([compile_seqs l x acc],[],s1) =
        (if acc = NONE then (res,s2) else
          match res with Rval _5 -> (res3,s3) | _6 -> (res,s2))`,
  CHEAT_TAC);;

let compile_any_correct = prove
 (`(evaluate ([x],env,s1) = (res,s2)) /\ ~(res = Rerr (Rabort
  Rtype_error)) /\
    k = LENGTH env ==>
    (evaluate ([compile_any split_seq l k x],env,s1) = (res,s2))`,
  CHEAT_TAC);;

let compile_IMP_LENGTH = prove
 (`compile l n xs = (ys,l1,s1) ==> LENGTH ys = LENGTH xs`,
  CHEAT_TAC);;

let bVarBound_CONS = prove
 (`bVarBound m [x] /\ bVarBound m xs ==> bVarBound m (x :: xs)`,
  CHEAT_TAC);;

let bVarBound_MEM = prove
 (`bVarBound n xs <=> (!x. MEM x xs ==> bVarBound n [x])`,
  CHEAT_TAC);;

let bEvery_MEM = prove
 (`bEvery p xs = (!x. MEM x xs ==> bEvery p [x])`,
  CHEAT_TAC);;

let bVarBound_LESS_EQ = prove
 (`!m xs n. bVarBound m xs /\ m <= n ==> bVarBound n xs`,
  CHEAT_TAC);;

let ALOOKUP_MAPi = prove
 (`!xs i x.
      ALOOKUP (MAPi (\i x. (x,i)) xs) n = SOME x ==> x < LENGTH xs`,
  CHEAT_TAC);;

(* [simp] *)
let bVarBound_SmartLet = prove
 (`bVarBound m [SmartLet x xs] = bVarBound m [Let x xs]`,
  CHEAT_TAC);;

let bVarBound_LetLet = prove
 (`bVarBound m [y] /\ n <= m ==> bVarBound m [LetLet n (l1:1 spt) y]`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let bVarBound_OptionalLetLet = prove
 (cake_as_vars (fun () ->
    `bVarBound m [e] /\ n <= m ==>
      bVarBound m (FST (OptionalLetLet e n l s limit nr))`),
  CHEAT_TAC);;

let bVarBound_compile = prove
 (`!l n xs m. n <= m ==> bVarBound m (FST (compile l n xs))`,
  CHEAT_TAC);;

let compile_IMP_bVarBound = prove
 (`compile l n xs = (ys,l2,s2) ==> bVarBound n ys`,
  CHEAT_TAC);;

let compile_exp_bVarBound = prove
 (`bVarBound n [compile_exp l n x]`,
  CHEAT_TAC);;

let compile_seqs_bVarBound = prove
 (`!l x acc.
      (!y. acc = SOME y ==> bVarBound 0 [y]) ==>
      bVarBound 0 [compile_seqs l x acc]`,
  CHEAT_TAC);;

let bEvery_CONS = prove
 (`bEvery p [x] /\ bEvery p xs ==> bEvery p (x :: xs)`,
  CHEAT_TAC);;

let handle_ok_Var_Const_list = prove
 (`EVERY (\x. ?v i. x = Var v \/ x = Op (closLang_IntOp
  (closLang_Const i)) []) xs ==> handle_ok xs`,
  CHEAT_TAC);;

let handle_ok_SmartLet = prove
 (`handle_ok [SmartLet xs x] <=> handle_ok xs /\ handle_ok [x]`,
  CHEAT_TAC);;

let handle_ok_OptionalLetLet = prove
 (`handle_ok [e] /\ bVarBound n [e] ==>
    handle_ok (FST (OptionalLetLet e n lx s l nr))`,
  CHEAT_TAC);;

let compile_handle_ok = prove
 (`!l n xs. handle_ok (FST (compile l n xs))`,
  CHEAT_TAC);;

let compile_exp_handle_ok = prove
 (`handle_ok [compile_exp l n x]`,
  CHEAT_TAC);;

let compile_seqs_handle_ok = prove
 (`!l x acc.
      (!y. acc = SOME y ==> handle_ok [y] /\ bVarBound 0 [y]) ==>
      handle_ok [compile_seqs l x acc]`,
  CHEAT_TAC);;

let compile_any_handle_ok = prove
 (`handle_ok [compile_any split_seq l n x]`,
  CHEAT_TAC);;

let handle_ok_CONS = prove
 (`!x xs. handle_ok (x :: xs) <=> handle_ok [x] /\ handle_ok xs`,
  CHEAT_TAC);;

let handle_ok_EVERY = prove
 (`!xs. handle_ok xs <=> EVERY (\x. handle_ok [x]) xs`,
  CHEAT_TAC);;

(* [simp] *)
let LetLet_code_labels = prove
 (`bvlProps_get_code_labels (LetLet x y z) = bvlProps_get_code_labels
  z`,
  CHEAT_TAC);;

(* compile_code_labels *)
let bvl_handleProof_compile_code_labels = prove
 (`!a b c. BIGUNION (set_of_list (MAP bvlProps_get_code_labels (FST
  (bvl_handle_compile a b c)))) SUBSET
           BIGUNION (set_of_list (MAP bvlProps_get_code_labels c))`,
  CHEAT_TAC);;

(* [local] *)
let get_code_labels_dest_handle_Raise = prove
 (`!c x. dest_handle_Raise c = SOME x ==>
         bvlProps_get_code_labels c = bvlProps_get_code_labels x`,
  CHEAT_TAC);;

(* [local] *)
let get_code_labels_handle_adj_vars = prove
 (`(!x d l. bvlProps_get_code_labels (handle_adj_vars d l x) =
  bvlProps_get_code_labels x) /\
   (!x d l. MAP bvlProps_get_code_labels (handle_adj_vars1 d l x) =
     MAP bvlProps_get_code_labels x)`,
  CHEAT_TAC);;

let get_code_labels_handle_simp = prove
 (`(!c. bvlProps_get_code_labels (handle_simp c) SUBSET
  bvlProps_get_code_labels c) /\
   (!c. BIGUNION (set_of_list (MAP bvlProps_get_code_labels
     (handle_simp_list c))) SUBSET
        BIGUNION (set_of_list (MAP bvlProps_get_code_labels c))) /\
   (!c d l. bvlProps_get_code_labels (make_handle c d l) SUBSET
            bvlProps_get_code_labels c UNION
              bvlProps_get_code_labels d)`,
  CHEAT_TAC);;

(* compile_exp_code_labels *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let bvl_handleProof_compile_exp_code_labels = prove
 (cake_as_vars (fun () ->
    `!a b c. bvlProps_get_code_labels (compile_exp a b c) SUBSET
  bvlProps_get_code_labels c`),
  CHEAT_TAC);;

let compile_seqs_code_labels = prove
 (`!cut e acc.
     bvlProps_get_code_labels (compile_seqs cut e acc) SUBSET
     bvlProps_get_code_labels e UNION
     (match acc with NONE -> {} | SOME r ->
       bvlProps_get_code_labels r)`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
