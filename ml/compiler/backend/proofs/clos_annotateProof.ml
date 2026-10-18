(* ======================================================== *)
(*  clos_annotateProof: ported from HOL4's
    compiler/backend/proofs/clos_annotateProofScript.sml
    A proof theory about clos_annotate.ml, with 4 definitions and 67
    theorems.  Needed by clos_to_bvlProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for clos_annotate
*)

needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/db_vars.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* HOL4 clos_annotateProofScript.sml:14-15: ML code, not ported *)

(* alternative definition of free_vars (fv) function *)

let alt_fv_def = cake_define
  `alt_fv n xs = has_var n (SND (alt_free xs))`;;

let alt_free_thm = cake_theorem "alt_free_thm"
  (fun () ->
    `!xs.
       let (ys,l) = alt_free xs in
         !n. (alt_fv n xs = has_var n l)`)
  CHEAT_TAC;;

let alt_fv = cake_theorem "alt_fv"
  (fun () ->
    `(!n. alt_fv n [] <=> F) /\
      (!y xs x n. alt_fv n (x :: y :: xs) <=> alt_fv n [x] \/
        alt_fv n (y :: xs)) /\
      (!v0 v n. alt_fv n [Var v0 v] <=> n = v) /\
      (!x3 x2 x1 v1 n.
        alt_fv n [If v1 x1 x2 x3] <=> alt_fv n [x1] \/ alt_fv n
          [x2] \/ alt_fv n [x3]) /\
      (!xs x2 v2 n.
        alt_fv n [Let v2 xs x2] <=>
          (if no_overlap (LENGTH xs) (SND (alt_free [x2])) /\ EVERY
            pure xs then
            alt_fv (n + LENGTH xs) [x2] else
            alt_fv n xs \/ alt_fv (n + LENGTH xs) [x2])) /\
      (!x1 v3 n. alt_fv n [Raise v3 x1] <=> alt_fv n [x1]) /\
      (!x1 v4 n. alt_fv n [closLang_Tick v4 x1] <=> alt_fv n [x1])
        /\
      (!xs v5 op n. alt_fv n [closLang_Op v5 op xs] <=> alt_fv n
        xs) /\
      (!x2 x1 v6 n loc_opt.
         alt_fv n [App v6 loc_opt x1 x2] <=> alt_fv n [x1] \/
           alt_fv n x2) /\
      (!x1 vs v7 num_args n loc.
         alt_fv n [closLang_Fn v7 loc vs num_args x1] <=> alt_fv (n
           + num_args) [x1]) /\
      (!x1 vs v8 n loc fns.
         alt_fv n [Letrec v8 loc vs fns x1] <=>
           EXISTS (\(num_args,x). alt_fv (n + num_args + LENGTH
             fns) [x]) fns \/
           alt_fv (n + LENGTH fns) [x1]) /\
      (!x2 x1 v9 n. alt_fv n [Handle v9 x1 x2] <=> alt_fv n [x1] \/
        alt_fv (n + 1) [x2]) /\
      (!xs v10 ticks n dest. alt_fv n [closLang_Call v10 ticks
        dest xs] <=> alt_fv n xs)`)
  CHEAT_TAC;;

let alt_fv_nil = cake_theorem "alt_fv_nil[simp]"
  (fun () ->
    `alt_fv v [] <=> F`)
  CHEAT_TAC;;

let alt_fv1_def = cake_define
  `alt_fv1 v e = alt_fv v [e]`;;

(* HOL4 clos_annotateProofScript.sml:81-82: a theorem that HOL4
   states as the value of an ML expression: alt_fv1_intro *)
(* HOL4 clos_annotateProofScript.sml:83-84: a theorem that HOL4
   states as the value of an ML expression: alt_fv1_thm *)

let alt_fv_cons = cake_theorem "alt_fv_cons[simp]"
  (fun () ->
    `alt_fv v (x :: xs) <=> alt_fv1 v x \/ alt_fv v xs`)
  CHEAT_TAC;;

let alt_fv_REPLICATE = cake_theorem "alt_fv_REPLICATE[simp]"
  (fun () ->
    `alt_fv n (REPLICATE m e) <=> 0 < m /\ alt_fv1 n e`)
  CHEAT_TAC;;

(* value relation *)

(* HOL4 clos_annotateProofScript.sml:101: the overload alt_fv_set,
   which the port expands *)

let v_rel = cake_inductive
  `(clos_annotateProof_v_rel (closSem_Number j) (closSem_Number j)) /\
   (clos_annotateProof_v_rel (Word64 w) (Word64 w)) /\
   (EVERY2 clos_annotateProof_v_rel (xs:closSem_v list) (ys:closSem_v
     list) ==>
    clos_annotateProof_v_rel (closSem_Block t xs) (closSem_Block t
      ys)) /\
   (clos_annotateProof_v_rel (closSem_ByteVector ws)
     (closSem_ByteVector ws)) /\
   (clos_annotateProof_v_rel (closSem_RefPtr b r1) (closSem_RefPtr b
     r1)) /\
   ((clos_annotate_shift (FST (alt_free [c])) m num_args i = [c']) /\
    (!n. (\x y. alt_fv y x) [c] n /\ num_args <= n ==>
         env_ok m 0 i env env' (n - num_args)) /\
    every_Fn_vs_NONE [c] /\
    (LENGTH env = m) /\ EVERY2 clos_annotateProof_v_rel vals vals'
      ==>
    clos_annotateProof_v_rel (Closure p vals env num_args c) (Closure
      p vals' env' num_args c')) /\
   (EVERY2 (\(num_args,c1) (num_args',c1').
      ?m i.
        (num_args' = num_args) /\
        (clos_annotate_shift (FST (alt_free [c1])) m (LENGTH cs +
          num_args) i = [c1']) /\
        (!n. (\x y. alt_fv y x) [c1] n /\ num_args + LENGTH cs <= n
          ==>
           env_ok m 0 i env env' (n - (num_args + LENGTH cs))) /\
        every_Fn_vs_NONE [c1] /\
        (LENGTH env = m)) cs cs' /\
    EVERY2 clos_annotateProof_v_rel vals vals' /\ index < LENGTH cs
      ==>
    clos_annotateProof_v_rel (Recclosure p vals env cs index)
      (Recclosure p vals' env' cs' index)) /\
   (l + m <= n ==>
    env_ok m l i (env2:closSem_v list) (env2':closSem_v list) n) /\
   (n < l /\ clos_annotateProof_v_rel (EL n env2) (EL n env2') /\
    n < LENGTH env2 /\ n < LENGTH env2' ==>
    env_ok m l i env2 env2' n) /\
   (l <= n /\ n < l + m /\
    n < l + m /\ (sptree_lookup (n - l) i = SOME v) /\
    n < LENGTH env2 /\
    l + v < LENGTH env2' /\
    clos_annotateProof_v_rel (EL n env2) (EL (l + v) env2') ==>
    env_ok m l i env2 env2' n)`;;
hol4_overload "v_rel" "clos_annotateProof_v_rel";;

(* HOL4 clos_annotateProofScript.sml:148-164: a theorem that HOL4
   states as the value of an ML expression: v_rel_simp *)

let v_rel_Boolv = cake_theorem "v_rel_Boolv[simp]"
  (fun () ->
    `(clos_annotateProof_v_rel x (Boolv b) <=> (x = Boolv b)) /\
      (clos_annotateProof_v_rel (Boolv b) x <=> (x = Boolv b))`)
  CHEAT_TAC;;

let v_rel_Unit = cake_theorem "v_rel_Unit[simp]"
  (fun () ->
    `(clos_annotateProof_v_rel x closSem_Unit <=> (x = closSem_Unit)) /\
      (clos_annotateProof_v_rel closSem_Unit x <=> (x =
        closSem_Unit))`)
  CHEAT_TAC;;

(* HOL4 clos_annotateProofScript.sml:180: ML code, not ported *)

let env_ok_EXTEND = cake_theorem "env_ok_EXTEND[local]"
  (fun () ->
    `EVERY2 clos_annotateProof_v_rel env1 env2 /\ (l1 = LENGTH env1) /\
       (l1 <= n ==> env_ok m l i env1' env2' (n - l1)) ==>
       env_ok m (l + l1) i (env1 ++ env1') (env2 ++ env2') n`)
  CHEAT_TAC;;

(* HOL4 clos_annotateProofScript.sml:211-213: ML code, not ported *)

(* HOL4 clos_annotateProofScript.sml:215-217: ML code, not ported *)

(* HOL4 clos_annotateProofScript.sml:219-222: ML code, not ported *)

(* HOL4 clos_annotateProofScript.sml:224-226: ML code, not ported *)

let env_ok_EXTEND_IGNORE = cake_theorem "env_ok_EXTEND_IGNORE[local]"
  (fun () ->
    `(LENGTH env2 = LENGTH env1) /\ LENGTH env1 <= n /\ l1 = LENGTH env1
  /\
      env_ok m l i env1' env2' (n - l1) ==>
      env_ok m (l + l1) i (env1 ++ env1') (env2 ++ env2') n`)
  CHEAT_TAC;;

let state_rel_def = cake_define
  `clos_annotateProof_state_rel (s:('c,'ffi)closSem_state)
  (t:('c,'ffi)closSem_state) <=>
     (state_clock s = state_clock t) /\
     (state_ffi s = state_ffi t) /\
     (closSem_state_max_app s = closSem_state_max_app t) /\
     (closSem_state_compile_oracle t = (I ## (clos_annotate_annotate
       0) ## clos_annotate_compile) o closSem_state_compile_oracle s) /\
     (closSem_state_compile s = (\cfg (es,aux). closSem_state_compile
       t cfg (clos_annotate_annotate 0 es,clos_annotate_compile aux)))
       /\
     EVERY2 (OPTREL clos_annotateProof_v_rel) (closSem_state_globals
       s) (closSem_state_globals t) /\
     (FDOM (state_refs s) = FDOM (state_refs t)) /\
     (!n r1.
       (FLOOKUP (state_refs s) n = SOME r1) ==>
       (?r2. (FLOOKUP (state_refs t) n = SOME r2) /\
         closProps_ref_rel clos_annotateProof_v_rel r1 r2)) /\
     (FDOM (closSem_state_code s) = FDOM (closSem_state_code t)) /\
     (!name arity c.
       (FLOOKUP (closSem_state_code s) name = SOME (arity,c)) ==>
       (?c2.
         (clos_annotate_shift (FST (alt_free [c])) 0 arity LN = [c2])
           /\
         (FLOOKUP (closSem_state_code t) name = SOME (arity,c2))))`;;
hol4_overload "state_rel" "clos_annotateProof_state_rel";;

let state_rel_max_app = cake_theorem "state_rel_max_app"
  (fun () ->
    `clos_annotateProof_state_rel s t ==> closSem_state_max_app s =
  closSem_state_max_app t`)
  CHEAT_TAC;;

(* some syntactic properties of the compiler *)

let MAP_FST_compile = cake_theorem "MAP_FST_compile[simp]"
  (fun () ->
    `MAP FST (clos_annotate_compile p) = MAP FST p`)
  CHEAT_TAC;;

let REVERSE_compile = cake_theorem "REVERSE_compile"
  (fun () ->
    `REVERSE (clos_annotate_compile ls) = clos_annotate_compile
  (REVERSE ls)`)
  CHEAT_TAC;;

let ALOOKUP_compile = cake_theorem "ALOOKUP_compile"
  (fun () ->
    `ALOOKUP (clos_annotate_compile ls) =
      OPTION_MAP (\(args,e). (args,HD (clos_annotate_annotate
        args [e]))) o (ALOOKUP ls)`)
  CHEAT_TAC;;

let compile_append = cake_theorem "compile_append"
  (fun () ->
    `clos_annotate_compile (p1 ++ p2) = clos_annotate_compile p1 ++
  clos_annotate_compile p2`)
  CHEAT_TAC;;

(* semantic functions respect relation *)

let clos_annotateProof_list_to_v_v_rel = cake_theorem "list_to_v_v_rel"
  (fun () ->
    `!xs ys. LIST_REL clos_annotateProof_v_rel xs ys ==>
  clos_annotateProof_v_rel (list_to_v xs) (list_to_v ys)`)
  CHEAT_TAC;;

let v_to_list = cake_theorem "v_to_list[local]"
  (fun () ->
    `!h h'.
         clos_annotateProof_v_rel h h' ==>
         (v_to_list h = NONE /\
          v_to_list h' = NONE) \/
         (?x x'. (v_to_list h = SOME x) /\
                (v_to_list h' = SOME x') /\
                EVERY2 clos_annotateProof_v_rel x x')`)
  CHEAT_TAC;;

let clos_annotateProof_do_app_lemma = cake_theorem "do_app_lemma[local]"
  (fun () ->
    `clos_annotateProof_state_rel s t /\ LIST_REL
  clos_annotateProof_v_rel xs ys ==>
     (match do_app opp xs s with
       Rval (x,s1) ->
         (?y t1. clos_annotateProof_v_rel x y /\
           clos_annotateProof_state_rel s1 t1 /\ do_app opp ys t = Rval
           (y,t1)) | Rerr err1 ->
         (?err2. do_app opp ys t = Rerr err2 /\ exc_rel
           clos_annotateProof_v_rel err1 err2))`)
  CHEAT_TAC;;

let do_app_thm = cake_theorem "do_app_thm[local]"
  (fun () ->
    `clos_annotateProof_state_rel s1 t1 /\ EVERY2
  clos_annotateProof_v_rel xs ys /\
      (do_app op xs s1 = Rval (v,s2)) ==>
      (?w t2. (do_app op ys t1 = Rval (w,t2)) /\
             clos_annotateProof_v_rel v w /\
               clos_annotateProof_state_rel s2 t2)`)
  CHEAT_TAC;;

let v_rel_Number = cake_theorem "v_rel_Number[local]"
  (fun () ->
    `(clos_annotateProof_v_rel x (closSem_Number i:closSem_v) <=> (x =
  (closSem_Number i:closSem_v))) /\
     (clos_annotateProof_v_rel (closSem_Number i) x <=> (x =
       closSem_Number i)) /\
     (clos_annotateProof_v_rel (closSem_ByteVector ws) x <=> (x =
       closSem_ByteVector ws)) /\
     (clos_annotateProof_v_rel x (Word64 w) <=> (x = Word64 w)) /\
     (clos_annotateProof_v_rel (Word64 w) x <=> (x = Word64 w))`)
  CHEAT_TAC;;

let do_app_err_thm = cake_theorem "do_app_err_thm[local]"
  (fun () ->
    `clos_annotateProof_state_rel s1 t1 /\ EVERY2
  clos_annotateProof_v_rel xs ys /\
      do_app op xs s1 = Rerr err /\ (~(err = Rabort Rtype_error))
        ==>
        (?w. do_app op ys t1 = Rerr w /\
             exc_rel clos_annotateProof_v_rel err w)`)
  CHEAT_TAC;;

let v_to_bytes = cake_theorem "v_to_bytes"
  (fun () ->
    `clos_annotateProof_v_rel x y ==> (closSem_v_to_bytes x) =
  (closSem_v_to_bytes y)`)
  CHEAT_TAC;;

let v_to_words = cake_theorem "v_to_words"
  (fun () ->
    `clos_annotateProof_v_rel x y ==> (closSem_v_to_words x) =
  (closSem_v_to_words y)`)
  CHEAT_TAC;;

let do_install_thm = cake_theorem "do_install_thm"
  (fun () ->
    `clos_annotateProof_state_rel s1 t1 /\ LIST_REL
  clos_annotateProof_v_rel xs ys /\
     closSem_do_install xs s1 = (res1,s2) /\
     closSem_do_install ys t1 = (res2,t2) ==>
     semanticPrimitivesProps_result_rel (\e1 e2. e2 =
       (clos_annotate_annotate 0 e1)) (=) res1 res2 /\
     clos_annotateProof_state_rel s2 t2`)
  CHEAT_TAC;;

(* compiler correctness *)

let lookup_EL_shifted_env = cake_theorem "lookup_EL_shifted_env[local]"
  (fun () ->
    `!y n k. n < LENGTH y /\ ALL_DISTINCT y ==>
               (sptree_lookup (EL n y) (shifted_env k y) = SOME
                 (k + n))`)
  CHEAT_TAC;;

let env_ok_shifted_env = cake_theorem "env_ok_shifted_env[local]"
  (fun () ->
    `env_ok m l i env env2 k /\ MEM k live /\ ALL_DISTINCT live /\
       (lookup_vars (MAP (clos_annotate_get_var m l i) (FILTER (\n.
         n < m + l) live)) env2 =
         SOME x) ==>
       env_ok (m + l) 0 (shifted_env 0 (FILTER (\n. n < m + l)
         live)) env x k`)
  CHEAT_TAC;;

let EL_shift_alt_free = cake_theorem "EL_shift_alt_free[local]"
  (fun () ->
    `!fns index.
        index < LENGTH fns ==>
        ([EL index (clos_annotate_shift (FST (alt_free fns)) l m
          i)] =
         (clos_annotate_shift (FST (alt_free [EL index fns])) l m
           i))`)
  CHEAT_TAC;;

let FOLDR_mk_Union = cake_theorem "FOLDR_mk_Union[local]"
  (fun () ->
    `!ys aux l.
       ITLIST (\(x,l) (ts,alt_frees). (x :: ts,mk_Union l
         alt_frees)) ys (aux,l) =
       (MAP FST ys ++ aux,ITLIST mk_Union (MAP SND ys) l)`)
  CHEAT_TAC;;

(* HOL4 clos_annotateProofScript.sml:533-539: code that the source
   has in a comment *)

let evaluate_shift_REPLICATE_const_0 =
  cake_theorem "evaluate_shift_REPLICATE_const_0[simp]"
  (fun () ->
    `closSem_evaluate (clos_annotate_shift (REPLICATE n (const_0 v8)) m
  l i,env,t1) =
        (Rval (REPLICATE n (closSem_Number (&0))),t1)`)
  CHEAT_TAC;;

let no_overlap_has_var_IMP =
  cake_theorem "no_overlap_has_var_IMP[local]"
  (fun () ->
    `!n l2 x. no_overlap n l2 /\ has_var x l2 ==> n <= x`)
  CHEAT_TAC;;

let evaluate_pure_IMP = cake_theorem "evaluate_pure_IMP[local]"
  (fun () ->
    `closSem_evaluate (xs,env,(s:('c,'ffi)closSem_state)) = (q,r) /\
  EVERY pure xs /\ ~(q = Rerr (Rabort Rtype_error)) ==>
     (?vs. q = Rval vs /\ r = s /\ LENGTH vs = LENGTH xs)`)
  CHEAT_TAC;;

(* HOL4 clos_annotateProofScript.sml:573-577: ML code, not ported *)

(* HOL4 clos_annotateProofScript.sml:579-584: a proof *)

let state_rel_opt_rel_refs =
  cake_theorem "state_rel_opt_rel_refs[local]"
  (fun () ->
    `(clos_annotateProof_state_rel s1 s2 /\ FLOOKUP (state_refs s1) n =
  r1 ==>
        (?r2. FLOOKUP (state_refs s2) n = r2 /\ OPTREL
          (closProps_ref_rel clos_annotateProof_v_rel) r1 r2)) /\
     (clos_annotateProof_state_rel s1 s2 /\ FLOOKUP (state_refs s2)
       n = r2 ==>
        (?r1. FLOOKUP (state_refs s1) n = r1 /\ OPTREL
          (closProps_ref_rel clos_annotateProof_v_rel) r1 r2))`)
  CHEAT_TAC;;

let state_rel_clocks_eqs = cake_theorem "state_rel_clocks_eqs[local]"
  (fun () ->
    `clos_annotateProof_state_rel s t ==> state_clock s = state_clock
  t`)
  CHEAT_TAC;;

let rel_update_thunk = cake_theorem "rel_update_thunk[local]"
  (fun () ->
    `clos_annotateProof_state_rel s1 s2 /\
     LIST_REL clos_annotateProof_v_rel vs ys ==>
       (update_thunk [closSem_RefPtr v ptr] (state_refs s1) vs =
         SOME refs1 ==>
          (?refs2. update_thunk [closSem_RefPtr v ptr] (state_refs
            s2) ys = SOME refs2 /\
                  clos_annotateProof_state_rel (state_refs_fupd
                    (K refs1) s1) (state_refs_fupd (K refs2) s2)))`)
  CHEAT_TAC;;

let shift_correct = cake_theorem "shift_correct[local]"
  (fun () ->
    `(!xs env (s1:('c,'ffi)closSem_state) env' t1 res s2 m l i.
        (closSem_evaluate (xs,env,s1) = (res,s2)) /\ ~(res = Rerr
          (Rabort Rtype_error)) /\
        (LENGTH env = m + l) /\
        (\x y. alt_fv y x) xs SUBSET env_ok m l i env env' /\
        every_Fn_vs_NONE xs /\ FEVERY (\p. every_Fn_vs_NONE [SND
          (SND p)]) (closSem_state_code s1) /\
        (!n. every_Fn_vs_NONE (FST (SND
          (closSem_state_compile_oracle s1 n))) /\
             every_Fn_vs_NONE (MAP (SND o SND) (SND (SND
               (closSem_state_compile_oracle s1 n))))) /\
        clos_annotateProof_state_rel s1 t1 ==>
        (?res' t2.
           (closSem_evaluate (clos_annotate_shift (FST (alt_free
             xs)) m l i,env',t1) = (res',t2)) /\
           semanticPrimitivesProps_result_rel (LIST_REL
             clos_annotateProof_v_rel) clos_annotateProof_v_rel res res'
             /\
           clos_annotateProof_state_rel s2 t2)) /\
      (!loc_opt f args (s1:('c,'ffi)closSem_state) res s2 f' args'
        s1'.
        (evaluate_app loc_opt f args s1 = (res,s2)) /\
        clos_annotateProof_v_rel f f' /\ EVERY2
          clos_annotateProof_v_rel args args' /\
        FEVERY (\p. every_Fn_vs_NONE [SND (SND p)])
          (closSem_state_code s1) /\
        (!n. every_Fn_vs_NONE (FST (SND
          (closSem_state_compile_oracle s1 n))) /\
             every_Fn_vs_NONE (MAP (SND o SND) (SND (SND
               (closSem_state_compile_oracle s1 n))))) /\
        clos_annotateProof_state_rel s1 s1' /\ ~(res = Rerr (Rabort
          Rtype_error)) ==>
        (?res' s2'.
          (evaluate_app loc_opt f' args' s1' = (res',s2')) /\
          semanticPrimitivesProps_result_rel (LIST_REL
            clos_annotateProof_v_rel) clos_annotateProof_v_rel res res'
            /\
          clos_annotateProof_state_rel s2 s2'))`)
  CHEAT_TAC;;

let env_set_default = cake_theorem "env_set_default[local]"
  (fun () ->
    `x SUBSET env_ok 0 0 LN [] env'`)
  CHEAT_TAC;;

(* HOL4 clos_annotateProofScript.sml:1306-1309: a theorem that HOL4
   states as the value of an ML expression: annotate_correct *)

(* more correctness properties *)

let every_Fn_vs_SOME_shift = cake_theorem "every_Fn_vs_SOME_shift[simp]"
  (fun () ->
    `!a b c d. every_Fn_vs_SOME (clos_annotate_shift a b c d)`)
  CHEAT_TAC;;

let every_Fn_vs_SOME_annotate =
  cake_theorem "every_Fn_vs_SOME_annotate[simp]"
  (fun () ->
    `every_Fn_vs_SOME (clos_annotate_annotate n es)`)
  CHEAT_TAC;;

let every_Fn_SOME_shift = cake_theorem "every_Fn_SOME_shift[simp]"
  (fun () ->
    `!a b c d. every_Fn_SOME (clos_annotate_shift a b c d) <=>
  every_Fn_SOME a`)
  CHEAT_TAC;;

let every_Fn_SOME_const_0 = cake_theorem "every_Fn_SOME_const_0[simp]"
  (fun () ->
    `every_Fn_SOME [const_0 t]`)
  CHEAT_TAC;;

let every_Fn_SOME_alt_free = cake_theorem "every_Fn_SOME_alt_free"
  (fun () ->
    `!es. every_Fn_SOME es ==> every_Fn_SOME (FST (alt_free es))`)
  CHEAT_TAC;;

let every_Fn_SOME_annotate = cake_theorem "every_Fn_SOME_annotate"
  (fun () ->
    `every_Fn_SOME es ==> every_Fn_SOME (clos_annotate_annotate n es)`)
  CHEAT_TAC;;

(* HOL4 clos_annotateProofScript.sml:1375: ML code, not ported *)

let shift_code_locs = cake_theorem "shift_code_locs[local]"
  (fun () ->
    `!xs env s1 env'. code_locs (clos_annotate_shift xs env s1 env') =
  code_locs xs`)
  CHEAT_TAC;;

let code_locs_const_0 = cake_theorem "code_locs_const_0[simp]"
  (fun () ->
    `code_locs [const_0 t] = []`)
  CHEAT_TAC;;

let alt_free_code_locs = cake_theorem "alt_free_code_locs[local]"
  (fun () ->
    `!xs. set_of_list (code_locs (FST (alt_free xs))) SUBSET
  set_of_list (code_locs xs)`)
  CHEAT_TAC;;

let alt_free_code_locs_distinct =
  cake_theorem "alt_free_code_locs_distinct[local]"
  (fun () ->
    `!xs. ALL_DISTINCT (code_locs xs) ==> ALL_DISTINCT (code_locs (FST
  (alt_free xs)))`)
  CHEAT_TAC;;

let annotate_code_locs = cake_theorem "annotate_code_locs"
  (fun () ->
    `!n ls. set_of_list (code_locs (clos_annotate_annotate n ls)) SUBSET
  set_of_list (code_locs ls) /\
            (ALL_DISTINCT (code_locs ls) ==> ALL_DISTINCT
              (code_locs (clos_annotate_annotate n ls)))`)
  CHEAT_TAC;;

let EVERY_shift_sing = cake_theorem "EVERY_shift_sing"
  (fun () ->
    `EVERY f (clos_annotate_shift [y] x1 x2 x3) <=> f (HD
  (clos_annotate_shift [y] x1 x2 x3))`)
  CHEAT_TAC;;

let shift_obeys_max_app = cake_theorem "shift_obeys_max_app"
  (fun () ->
    `!xs m l i.
        EVERY (obeys_max_app n) xs ==>
        EVERY (obeys_max_app n) (clos_annotate_shift xs m l i)`)
  CHEAT_TAC;;

let alt_free_obeys_max_app = cake_theorem "alt_free_obeys_max_app"
  (fun () ->
    `!xs m l i.
        EVERY (obeys_max_app n) xs ==>
        EVERY (obeys_max_app n) (FST (alt_free xs))`)
  CHEAT_TAC;;

let annotate_obeys_max_app = cake_theorem "annotate_obeys_max_app"
  (fun () ->
    `!n xs. EVERY (obeys_max_app m) xs ==>
             EVERY (obeys_max_app m) (clos_annotate_annotate n
               xs)`)
  CHEAT_TAC;;

let shift_no_Labels = cake_theorem "shift_no_Labels"
  (fun () ->
    `!xs m l i.
        EVERY no_Labels xs ==>
        EVERY no_Labels (clos_annotate_shift xs m l i)`)
  CHEAT_TAC;;

let alt_free_no_Labels = cake_theorem "alt_free_no_Labels"
  (fun () ->
    `!xs m l i.
        EVERY no_Labels xs ==>
        EVERY no_Labels (FST (alt_free xs))`)
  CHEAT_TAC;;

let annotate_no_Labels = cake_theorem "annotate_no_Labels"
  (fun () ->
    `!n xs. EVERY no_Labels xs ==>
             EVERY no_Labels (clos_annotate_annotate n xs)`)
  CHEAT_TAC;;

let code_locs_REP_const_0 = cake_theorem "code_locs_REP_const_0"
  (fun () ->
    `code_locs (REPLICATE n (const_0 t)) = []`)
  CHEAT_TAC;;

let code_locs_alt_free = cake_theorem "code_locs_alt_free"
  (fun () ->
    `!xs r1 r2. alt_free xs = (r1,r2) ==> set_of_list (code_locs r1)
  SUBSET set_of_list (code_locs xs)`)
  CHEAT_TAC;;

let code_locs_shift = cake_theorem "code_locs_shift"
  (fun () ->
    `!xs k1 k2 k3. code_locs (clos_annotate_shift xs k1 k2 k3) =
  code_locs xs`)
  CHEAT_TAC;;

let code_locs_annotate = cake_theorem "code_locs_annotate"
  (fun () ->
    `!n xs. set_of_list (code_locs (clos_annotate_annotate n xs))
  SUBSET set_of_list (code_locs xs)`)
  CHEAT_TAC;;

(* semantics preservation *)

let semantics_annotate = cake_theorem "semantics_annotate"
  (fun () ->
    `~(closSem_semantics (ffi:'ffi ffi_state) max_app (alist_to_fmap
  prog) co
          (pure_cc clos_annotate_compile_inc cc) xs = ffi_Fail) ==>
        every_Fn_vs_NONE xs /\
        every_Fn_vs_NONE (MAP (SND o SND) prog) /\
        (!n. every_Fn_vs_NONE (FST (SND (co n))) /\
             every_Fn_vs_NONE (MAP (SND o SND) (SND (SND (co n)))))
               ==>
        closSem_semantics (ffi:'ffi ffi_state) max_app
          (alist_to_fmap (clos_annotate_compile prog))
          (pure_co clos_annotate_compile_inc o co) cc
            (clos_annotate_annotate 0 xs) =
        closSem_semantics (ffi:'ffi ffi_state) max_app
          (alist_to_fmap prog)
          co (pure_cc clos_annotate_compile_inc cc) xs`)
  CHEAT_TAC;;

(* more syntactic properties *)

let call_dests_shift = cake_theorem "call_dests_shift[simp]"
  (fun () ->
    `!a b c d. app_call_dests opt (clos_annotate_shift a b c d) =
  app_call_dests opt a`)
  CHEAT_TAC;;

let no_Labels_ann = cake_theorem "no_Labels_ann"
  (fun () ->
    `!xs.
        EVERY no_Labels (MAP (SND o SND) xs) ==>
        EVERY no_Labels (MAP (SND o SND) (clos_annotate_compile
          xs))`)
  CHEAT_TAC;;

let obeys_max_app_ann = cake_theorem "obeys_max_app_ann"
  (fun () ->
    `!xs.
        EVERY (obeys_max_app m) (MAP (SND o SND) xs) ==>
        EVERY (obeys_max_app m) (MAP (SND o SND)
          (clos_annotate_compile xs))`)
  CHEAT_TAC;;

let HD_annotate_SING = cake_theorem "HD_annotate_SING"
  (fun () ->
    `[HD (clos_annotate_annotate x [y])] = clos_annotate_annotate x
  [y]`)
  CHEAT_TAC;;

let every_Fn_SOME_ann = cake_theorem "every_Fn_SOME_ann"
  (fun () ->
    `!xs.
        every_Fn_SOME (MAP (SND o SND) xs) ==>
        every_Fn_SOME (MAP (SND o SND) (clos_annotate_compile
          xs))`)
  CHEAT_TAC;;
