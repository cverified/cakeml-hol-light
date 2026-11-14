(* ======================================================== *)
(*  clos_mtiProof: ported from HOL4's
    compiler/backend/proofs/clos_mtiProofScript.sml
    A proof theory about clos_mti.ml, with 10 definitions and 68
    theorems.  Needed by clos_to_bvlProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for the clos_mti compiler pass. The theorem is
  proved using a backwards simulation, i.e. against the direction of
  compilation.
*)

needs "compiler/backend/clos_mti.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "clos_mtiProof"
  ["backendProps"; "closProps"; "closSem"; "clos_mti"];;

(* HOL4 clos_mtiProofScript.sml:18: ML code, not ported *)

(* code relation *)

(* HOL4 clos_mtiProofScript.sml:22-23: a theorem that HOL4 states as
   the value of an ML expression: no_mti_def *)

let clos_mtiProof_code_rel_def = new_definition
  `clos_mtiProof_code_rel max_app e1 e2 <=>
     ALL no_mti e1 /\ (e2 = intro_multi max_app e1)`;;

(* code_rel_IMP_LENGTH *)
let clos_mtiProof_code_rel_IMP_LENGTH = prove
 (`clos_mtiProof_code_rel max_app xs ys ==> LENGTH ys = LENGTH xs`,
  CHEAT_TAC);;

let HD_intro_multi = prove
 (`[HD (intro_multi max_app [e2])] = intro_multi max_app [e2]`,
  CHEAT_TAC);;
add_simp HD_intro_multi;;

let intro_multi_cons = prove
 (`!xs x. intro_multi m (CONS x xs) = CONS (HD (intro_multi m [x]))
  (intro_multi m xs)`,
  CHEAT_TAC);;

(* code_rel_CONS_CONS *)
let clos_mtiProof_code_rel_CONS_CONS = prove
 (`clos_mtiProof_code_rel m (CONS x1 (CONS x2 xs)) (CONS y1 (CONS y2
  ys)) <=>
    clos_mtiProof_code_rel m [x1] [y1] /\ clos_mtiProof_code_rel m
      (CONS x2 xs) (CONS y2 ys)`,
  CHEAT_TAC);;

(* value relation *)

let mk_Fns_def,mk_Fns_ind = define_rec
  [`mk_Fns [] e = e`;
   `mk_Fns (CONS t ts) e = closLang_Fn t NONE NONE 1 (mk_Fns ts e)`];;

let clos_mtiProof_f_rel_def = new_definition
  `clos_mtiProof_f_rel max_app (a1,e1) (a2,e2) <=>
     (?b1 ts.
       clos_mtiProof_code_rel max_app [b1] [e2] /\ a2 <= max_app /\
         no_mti b1 /\
       a1 = 1 /\ e1 = mk_Fns ts b1 /\ a2 = LENGTH ts + 1)`;;

let clos_mtiProof_v_rel = cake_inductive
  `(!i. clos_mtiProof_v_rel (max_app:num) (closSem_Number i)
  (closSem_Number i)) /\
   (!w. clos_mtiProof_v_rel max_app (closSem_Word64 w)
     (closSem_Word64 w)) /\
   (!w. clos_mtiProof_v_rel max_app (closSem_ByteVector w)
     (closSem_ByteVector w)) /\
   (!n b. clos_mtiProof_v_rel max_app (closSem_RefPtr b n)
     (closSem_RefPtr b n)) /\
   (!tag xs ys.
      ALL2 (clos_mtiProof_v_rel max_app) xs ys ==>
      clos_mtiProof_v_rel max_app (closSem_Block tag xs)
        (closSem_Block tag ys)) /\
   (!args1 args2 env1 env2 arg_count e1 ts e2.
      1 + LENGTH ts + LENGTH args1 = arg_count /\
      clos_mtiProof_code_rel max_app [e1] [e2] /\
      ALL2 (clos_mtiProof_v_rel max_app) env1 env2 /\
      ALL2 (clos_mtiProof_v_rel max_app) args1 args2 ==>
      clos_mtiProof_v_rel max_app
        (closSem_Closure NONE [] (APPEND args1 env1) 1 (mk_Fns ts
          e1))
        (closSem_Closure NONE args2 env2 arg_count e2)) /\
   (!env1 funs1 env2 funs2 n.
      ALL2 (clos_mtiProof_f_rel max_app) funs1 funs2 /\
      ALL2 (clos_mtiProof_v_rel max_app) env1 env2 /\
      n < LENGTH funs2 ==>
      clos_mtiProof_v_rel max_app
        (closSem_Recclosure NONE [] env1 funs1 n)
        (closSem_Recclosure NONE [] env2 funs2 n)) /\
   (!args1 env1 funs1 args2 env2 funs2 n recc ts e1 e2 arg_count.
      ALL2 (clos_mtiProof_f_rel max_app) funs1 funs2 /\
      ALL2 (clos_mtiProof_v_rel max_app) env1 env2 /\
      ALL2 (clos_mtiProof_v_rel max_app) args1 args2 /\ ~(args2 = [])
        /\
      n < LENGTH funs2 /\ EL n funs2 = (arg_count,e2) /\
      1 + LENGTH ts + LENGTH args1 = arg_count /\
      clos_mtiProof_code_rel max_app [e1] [e2] /\
      ALL2 (clos_mtiProof_v_rel max_app) recc
           (list_of_seq (closSem_Recclosure NONE [] env2 funs2)
             (LENGTH funs2)) ==>
      clos_mtiProof_v_rel max_app
        (closSem_Closure NONE [] (APPEND (APPEND args1 recc) env1) 1
          (mk_Fns ts e1))
        (closSem_Recclosure NONE args2 env2 funs2 n))`;;

let v_rel_opt_def = new_definition
  `v_rel_opt max_app x2 x3 =
        match (x2,x3) with
          (NONE,NONE) -> T
        | ((SOME x),(SOME y)) -> clos_mtiProof_v_rel max_app x y
        | (_1,_2) -> F`;;

let clos_mtiProof_ref_rel = cake_inductive
  `(!bs. clos_mtiProof_ref_rel max_app (closSem_ByteArray bs)
  (closSem_ByteArray bs)) /\
   (!xs ys.
     ALL2 (clos_mtiProof_v_rel max_app) xs ys ==>
     clos_mtiProof_ref_rel max_app (closSem_ValueArray xs)
       (closSem_ValueArray ys)) /\
   (!m v w.
     clos_mtiProof_v_rel max_app v w ==>
     clos_mtiProof_ref_rel max_app (closSem_Thunk m v)
       (closSem_Thunk m w))`;;

(* HOL4 clos_mtiProofScript.sml:128-132: a theorem that HOL4 states
   as the value of an ML expression: ref_rel_simps *)

let clos_mtiProof_FMAP_REL_def = new_definition
  `clos_mtiProof_FMAP_REL r f1 f2 <=>
     FDOM f1 = FDOM f2 /\
     (!k v. FLOOKUP f1 k = SOME v ==>
           (?v2. FLOOKUP f2 k = SOME v2 /\ r v v2))`;;

(* state relation *)

let SND_compile_inc = prove
 (`SND (clos_mti_compile_inc max_app p) = []`,
  CHEAT_TAC);;
add_simp SND_compile_inc;;

let clos_mtiProof_state_rel_def = new_definition
  `clos_mtiProof_state_rel (s:('c,'ffi)closSem_state)
  (t:('c,'ffi)closSem_state) <=>
     (!n. SND (SND (closSem_state_compile_oracle s n)) = [] /\
          ALL no_mti (FST (SND (closSem_state_compile_oracle s n))))
            /\ closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY /\
       closSem_state_max_app
     t = closSem_state_max_app s /\ 1 <= closSem_state_max_app s /\
       closSem_state_clock
     t = closSem_state_clock s /\ closSem_state_ffi
     t = closSem_state_ffi s /\
     ALL2 (v_rel_opt (closSem_state_max_app s))
       (closSem_state_globals s) (closSem_state_globals t) /\
     clos_mtiProof_FMAP_REL (clos_mtiProof_ref_rel
       (closSem_state_max_app s)) (closSem_state_refs s)
       (closSem_state_refs t) /\ closSem_state_compile
     s = pure_cc (clos_mti_compile_inc (closSem_state_max_app s))
       (closSem_state_compile t) /\ closSem_state_compile_oracle
     t = pure_co (clos_mti_compile_inc (closSem_state_max_app s))
       o closSem_state_compile_oracle s`;;

(* state_rel_max_app[local] *)
let clos_mtiProof_state_rel_max_app = prove
 (`clos_mtiProof_state_rel s t ==> closSem_state_max_app s =
  closSem_state_max_app t /\ 1 <= closSem_state_max_app t`,
  CHEAT_TAC);;

(* [local] *)
let state_rel_clocks = prove
 (`clos_mtiProof_state_rel s t ==> state_clock s = state_clock t`,
  CHEAT_TAC);;

(* evaluation theorem *)

let collect_args_IMP = prove
 (`!max_app k e1 num_args e2.
      collect_args max_app k e1 = (num_args,e2) /\ k <= max_app ==>
      k <= num_args /\ num_args <= max_app`,
  CHEAT_TAC);;

let collect_args_ok_IMP = prove
 (`!max_app k e num_args e2.
      collect_args max_app k e = (num_args,e2) /\ no_mti e ==>
      (?ts. e = mk_Fns ts e2 /\ num_args = k + LENGTH ts /\ no_mti
        e2)`,
  CHEAT_TAC);;

(* dest_closure_SOME_IMP *)
let clos_mtiProof_dest_closure_SOME_IMP = prove
 (`dest_closure max_app loc_opt f2 xs = SOME x ==>
    (?loc arg_env clo_env num_args e. f2 = closSem_Closure loc
      arg_env clo_env num_args e) \/
    (?loc arg_env clo_env fns i. f2 = closSem_Recclosure loc
      arg_env clo_env fns i)`,
  CHEAT_TAC);;

(* [local] *)
let collect_apps_acc = prove
 (`!max_app acc e res s.
     collect_apps max_app acc e = (res,s) ==>
     (?other. res = APPEND acc other)`,
  CHEAT_TAC);;

(* [local] *)
let collect_apps_cons_lemma = prove
 (`!e1 m ys other e2.
     collect_apps (m + LENGTH ys) ys e1 = (APPEND ys other,e2) <=>
     collect_apps m [] e1 = (other,e2)`,
  CHEAT_TAC);;

(* [local] *)
let collect_apps_cons = prove
 (`!e1 m x other e2.
     collect_apps m [x] e1 = (CONS x other,e2) /\ ~(m = 0) ==>
     collect_apps (m - 1) [] e1 = (other,e2)`,
  CHEAT_TAC);;

let mk_Apps_def,mk_Apps_ind = define_rec
  [`mk_Apps e [] = e`;
   `mk_Apps e (CONS (t,other) ts) = closLang_App t NONE (mk_Apps e
    ts) [other]`];;

let collect_apps_IMP_mk_Apps = prove
 (`!e max_app (acc:closLang_exp list) other e3.
       collect_apps max_app [] e = (other,e3) /\ no_mti e ==>
       (?ts. e = mk_Apps e3 (ZIP ts other) /\ LENGTH other = LENGTH
         ts /\
            LENGTH other <= max_app)`,
  CHEAT_TAC);;

(* [local] *)
let mk_Apps_err_1 = prove
 (`!ts other env1 s1 e3.
     closSem_evaluate (other,env1,s1) = (Rerr e2,s2) /\
     LENGTH other = LENGTH ts ==>
     closSem_evaluate ([mk_Apps e3 (ZIP ts other)],env1,s1) = (Rerr
       e2,s2)`,
  CHEAT_TAC);;

(* [local] *)
let mk_Apps_err_2 = prove
 (`!ts other env1 s1 e3 vs.
     closSem_evaluate ([e3],env1,s2) = (Rerr e2,s2') /\
     closSem_evaluate (other,env1,s1) = (Rval vs,s2) /\
     LENGTH other = LENGTH ts ==>
     closSem_evaluate ([mk_Apps e3 (ZIP ts other)],env1,s1) = (Rerr
       e2,s2')`,
  CHEAT_TAC);;

let collect_apps_no_mti = prove
 (`!k aux e res e1.
      collect_apps k aux e = (res,e1) /\
      no_mti e /\ ALL no_mti aux ==>
      ALL no_mti res /\ no_mti e1`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_mk_Apps_err = prove
 (`!other ts env1 s1 vs.
     closSem_evaluate (other,env1,s1) = (Rval vs,s3) /\
     closSem_evaluate ([e],env1,s3) = (Rerr e3,s2') /\
     LENGTH other = LENGTH ts ==>
     closSem_evaluate ([mk_Apps e (ZIP ts other)],env1,s1) = (Rerr
       e3,s2')`,
  CHEAT_TAC);;

let evaluate_apps_def,evaluate_apps_ind = define_rec
  [`evaluate_apps f [] s = (Rval [f],s)`;
   `evaluate_apps f (CONS x xs) s =
      (match evaluate_apps f xs s with (Rval [v],s1) ->
          evaluate_app NONE v [x] s1 | res -> res)`];;

(* [local] *)
let evaluate_mk_Apps_ok = prove
 (`!other ts env1 s1 vs.
       closSem_evaluate ([e],env1,s3) = (Rval [f],s2') /\
       closSem_evaluate (other,env1,s1) = (Rval vs,s3) /\
       LENGTH other = LENGTH ts ==>
       closSem_evaluate ([mk_Apps e (ZIP ts other)],env1,s1) =
       evaluate_apps f vs s2'`,
  CHEAT_TAC);;

(* [local] *)
let dest_closure_NONE_IMP_apps = prove
 (`!xs f1 s1.
       dest_closure (closSem_state_max_app s1) NONE f1 [LAST xs] =
         NONE /\ ~(xs = []) ==>
       evaluate_apps f1 xs s1 = (Rerr (Rabort Rtype_error),s1)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_apps_SNOC = prove
 (`!xs x f s.
       evaluate_apps f (SNOC x xs) s =
       (match evaluate_app NONE f [x] s with (Rval [v],s) ->
         evaluate_apps v xs s | res -> res)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_apps_Clos_timeout = prove
 (`!ys ts s1 e1 env. state_clock
       s1 < LENGTH ys /\ LENGTH ys <= LENGTH ts /\
       1 <= closSem_state_max_app s1 ==>
       evaluate_apps (closSem_Closure NONE [] env 1 (mk_Fns ts e1))
         ys s1 = (Rerr (Rabort Rtimeout_error),state_clock_fupd (K
           0) s1)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_apps_Clos_timeout_alt = prove
 (`!ys ts s1 e1 env. state_clock
       s1 <= LENGTH ts /\ LENGTH ts < LENGTH ys /\
       1 <= closSem_state_max_app s1 ==>
       evaluate_apps (closSem_Closure NONE [] env 1 (mk_Fns ts e1))
         ys s1 = (Rerr (Rabort Rtimeout_error),state_clock_fupd (K
           0) s1)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_apps_Clos_short = prove
 (`!ys ts s1 e1 env.
       LENGTH ys <= state_clock s1 /\ LENGTH ys <= LENGTH ts /\
       1 <= closSem_state_max_app s1 ==>
       evaluate_apps (closSem_Closure NONE [] env 1 (mk_Fns ts e1))
         ys s1 =
          (Rval [closSem_Closure NONE [] (APPEND ys env) 1
                    (mk_Fns (DROP (LENGTH ys) ts) e1)],
           closSem_dec_clock (LENGTH ys) s1)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_apps_Clos_long = prove
 (`!ys ts s1 e1 env.
       LENGTH ts < state_clock s1 /\ LENGTH ts < LENGTH ys /\
       1 <= closSem_state_max_app s1 ==>
       evaluate_apps (closSem_Closure NONE [] env 1 (mk_Fns ts e1))
         ys s1 =
         (match closSem_evaluate ([e1],APPEND (REVERSE (TAKE (1 +
           LENGTH ts) (REVERSE ys))) env,
                 closSem_dec_clock (1 + LENGTH ts) s1) with (Rval
                   [v],s) ->
              evaluate_apps v (REVERSE (DROP (1 + LENGTH ts)
                (REVERSE ys))) s | res -> res)`,
  CHEAT_TAC);;

(* [local] *)
let LIST_REL_f_rel_IMP = prove
 (`!fns funs1. ALL2 (clos_mtiProof_f_rel max_app) funs1 fns ==> (!x.
  ~(MEM (0,x) fns))`,
  CHEAT_TAC);;

(* HOL4 clos_mtiProofScript.sml:494-507: a theorem that HOL4 states
   as the value of an ML expression: v_rel_simps *)

(* [local] *)
let v_rel_opt_thm = prove
 (`v_rel_opt m = OPTREL (clos_mtiProof_v_rel m)`,
  CHEAT_TAC);;

(* simple_val_rel *)
let clos_mtiProof_simple_val_rel = prove
 (`closProps_simple_val_rel (clos_mtiProof_v_rel max_app_n)`,
  CHEAT_TAC);;

(* simple_state_rel *)
let clos_mtiProof_simple_state_rel = prove
 (`closProps_simple_state_rel (clos_mtiProof_v_rel max_app_n)
     (\s t. closSem_state_max_app s = max_app_n /\
       clos_mtiProof_state_rel s t)`,
  CHEAT_TAC);;

(* state_rel_opt_rel_refs[local] *)
let clos_mtiProof_state_rel_opt_rel_refs = prove
 (`(clos_mtiProof_state_rel s1 s2 /\ FLOOKUP (state_refs s1) n = r1 ==>
      (?r2. FLOOKUP (state_refs s2) n = r2 /\ OPTREL
        (clos_mtiProof_ref_rel (closSem_state_max_app s1)) r1 r2)) /\
   (clos_mtiProof_state_rel s1 s2 /\ FLOOKUP (state_refs s2) n = r2
     ==>
      (?r1. FLOOKUP (state_refs s1) n = r1 /\ OPTREL
        (clos_mtiProof_ref_rel (closSem_state_max_app s1)) r1 r2))`,
  CHEAT_TAC);;

(* rel_update_thunk[local] *)
let clos_mtiProof_rel_update_thunk = prove
 (`clos_mtiProof_state_rel s1 s2 /\
   ALL2 (clos_mtiProof_v_rel (closSem_state_max_app s1)) vs ys ==>
     (closSem_update_thunk [closSem_RefPtr v ptr] (state_refs s2) ys
       = NONE ==>
        closSem_update_thunk [closSem_RefPtr v ptr] (state_refs s1)
          vs = NONE) /\
     (closSem_update_thunk [closSem_RefPtr v ptr] (state_refs s2) ys
       = SOME refs2 ==>
        (?refs1. closSem_update_thunk [closSem_RefPtr v ptr]
          (state_refs s1) vs = SOME refs1 /\
                clos_mtiProof_state_rel (state_refs_fupd (K refs1)
                  s1) (state_refs_fupd (K refs2) s2)))`,
  CHEAT_TAC);;

(* HOL4 clos_mtiProofScript.sml:581-586: ML code, not ported *)

(* do_app_lemma *)
let clos_mtiProof_do_app_lemma = prove
 (`clos_mtiProof_state_rel s (t:('c,'ffi)closSem_state) /\ ALL2
  (clos_mtiProof_v_rel (closSem_state_max_app s)) xs ys ==>
     (match closSem_do_app opp ys t with Rerr err2 -> (?err1.
       closSem_do_app opp xs s = Rerr err1 /\
                            exc_rel (clos_mtiProof_v_rel
                              (closSem_state_max_app s)) err1 err2) |
                              Rval (y,t1) -> (?x s1. clos_mtiProof_v_rel
                              (closSem_state_max_app s) x y /\
                              clos_mtiProof_state_rel s1 t1 /\
                             closSem_do_app opp xs s = Rval
                               (x,s1)))`,
  CHEAT_TAC);;

(* v_rel_IMP_v_to_bytes[local] *)
let clos_mtiProof_v_rel_IMP_v_to_bytes = prove
 (`clos_mtiProof_v_rel max_app x y ==> closSem_v_to_bytes y =
  closSem_v_to_bytes x`,
  CHEAT_TAC);;

(* v_rel_IMP_v_to_words[local] *)
let clos_mtiProof_v_rel_IMP_v_to_words = prove
 (`clos_mtiProof_v_rel max_app x y ==> closSem_v_to_words y =
  closSem_v_to_words x`,
  CHEAT_TAC);;

(* HOL4 clos_mtiProofScript.sml:611-617: ML code, not ported *)

(* do_install_lemma[local] *)
let clos_mtiProof_do_install_lemma = prove
 (`clos_mtiProof_state_rel s t /\ ALL2 (clos_mtiProof_v_rel
  (closSem_state_max_app s)) xs ys ==>
   (match closSem_do_install xs s with (Rerr err1,s1) -> (?err2 t1.
     closSem_do_install ys t = (Rerr err2,t1) /\
                           exc_rel (clos_mtiProof_v_rel
                             (closSem_state_max_app s)) err1 err2 /\
                             closSem_state_max_app
                           s1 = closSem_state_max_app s /\
                             clos_mtiProof_state_rel s1 t1) | (Rval
                             exps1,s1) -> (?exps2 t1.
                             (closSem_state_max_app s1 =
                             closSem_state_max_app s /\
                              clos_mtiProof_state_rel s1 t1) /\
                                (~(exps1 = [])) /\
                              clos_mtiProof_code_rel
                                (closSem_state_max_app s) exps1 exps2 /\
                              closSem_do_install ys t = (Rval
                                exps2,t1)))`,
  CHEAT_TAC);;

let intro_multi_EQ_NIL = prove
 (`!max_app es. intro_multi max_app es = [] <=> es = []`,
  CHEAT_TAC);;
add_simp intro_multi_EQ_NIL;;

let intro_multi_nil = prove
 (`intro_multi x [] = []`,
  CHEAT_TAC);;

(* result_rel_Rval2 *)
let clos_mtiProof_result_rel_Rval2 = prove
 (`semanticPrimitivesProps_result_rel P P' x (Rval v') = (?v. x = Rval
  v /\ P v v')`,
  CHEAT_TAC);;

let evaluate_intro_multi = prove
 (`(!ys env2 (t1:('c,'ffi)closSem_state) env1 t2 s1 res2 xs.
     (closSem_evaluate (ys,env2,t1) = (res2,t2)) /\
     ALL2 (clos_mtiProof_v_rel (closSem_state_max_app s1)) env1 env2
       /\
     clos_mtiProof_state_rel s1 t1 /\ clos_mtiProof_code_rel
       (closSem_state_max_app s1) xs ys ==>
     (?res1 s2.
        (closSem_evaluate (xs,env1,s1) = (res1,s2)) /\
        semanticPrimitivesProps_result_rel (ALL2 (clos_mtiProof_v_rel
          (closSem_state_max_app s1))) (clos_mtiProof_v_rel
          (closSem_state_max_app s1)) res1 res2 /\
        clos_mtiProof_state_rel s2 t2)) /\
   (!loc_opt f2 args2 (t1:('c,'ffi)closSem_state) res2 t2 f1 args1
     s1.
     (evaluate_app loc_opt f2 args2 t1 = (res2,t2)) /\ loc_opt = NONE
       /\
     clos_mtiProof_v_rel (closSem_state_max_app s1) f1 f2 /\ ALL2
       (clos_mtiProof_v_rel (closSem_state_max_app s1)) args1 args2 /\
     clos_mtiProof_state_rel s1 t1 /\ LENGTH args1 <=
       closSem_state_max_app s1 ==>
     (?res1 s2.
       (evaluate_apps f1 args1 s1 = (res1,s2)) /\
       semanticPrimitivesProps_result_rel (ALL2 (clos_mtiProof_v_rel
         (closSem_state_max_app s1))) (clos_mtiProof_v_rel
         (closSem_state_max_app s1)) res1 res2 /\
       clos_mtiProof_state_rel s2 t2))`,
  CHEAT_TAC);;

let intro_multi_correct = prove
 (`!xs env1 (s1:('c,'ffi)closSem_state) res1 s2 env2 t2 t1.
      closSem_evaluate (xs,env1,s1) = (res1,s2) /\ ALL no_mti xs /\
      ALL2 (clos_mtiProof_v_rel (closSem_state_max_app s1)) env1 env2
        /\ clos_mtiProof_state_rel s1 t1 ==>
      (?res2 t2.
        closSem_evaluate (intro_multi (closSem_state_max_app s1)
          xs,env2,t1) = (res2,t2) /\
        semanticPrimitivesProps_result_rel (ALL2 (clos_mtiProof_v_rel
          (closSem_state_max_app s1))) (clos_mtiProof_v_rel
          (closSem_state_max_app s1)) res1
          res2 /\ clos_mtiProof_state_rel s2 t2)`,
  CHEAT_TAC);;

(* syntax well-formedness *)

let contains_App_SOME_collect_args = prove
 (`!m x y a b. collect_args m x y = (a,b) ==>
    (contains_App_SOME m [y] <=> contains_App_SOME m [b])`,
  CHEAT_TAC);;

let contains_App_SOME_collect_apps = prove
 (`!max_app x y a b. collect_apps max_app x y = (a,b) ==>
    (max_app < LENGTH x \/ contains_App_SOME max_app x \/
      contains_App_SOME max_app [y] <=>
     max_app < LENGTH a \/ contains_App_SOME max_app a \/
       contains_App_SOME max_app [b])`,
  CHEAT_TAC);;

let contains_App_SOME_intro_multi = prove
 (`!max_app es. contains_App_SOME max_app (intro_multi max_app es) <=>
  contains_App_SOME max_app es`,
  CHEAT_TAC);;
add_simp contains_App_SOME_intro_multi;;

let contains_App_SOME_compile = prove
 (`!do_mti es. contains_App_SOME max_app (clos_mti_compile do_mti
  max_app es) <=> contains_App_SOME max_app es`,
  CHEAT_TAC);;
add_simp contains_App_SOME_compile;;

let collect_args_preserves_esgc_free = prove
 (`!max_app n e n' e'. collect_args max_app n e = (n',e') /\
                       closProps_esgc_free e ==>
                         closProps_esgc_free e'`,
  CHEAT_TAC);;

(* [local] *)
let every_Fn_vs_NONE_collect_apps = prove
 (`!max_app es e x y. collect_apps max_app es e = (x,y) ==>
   (every_Fn_vs_NONE x /\ every_Fn_vs_NONE [y] <=>
    every_Fn_vs_NONE es /\ every_Fn_vs_NONE [e])`,
  CHEAT_TAC);;

(* [local] *)
let every_Fn_vs_NONE_collect_args = prove
 (`!max_app es e x y. collect_args max_app es e = (x,y) ==>
     (every_Fn_vs_NONE [y] <=> every_Fn_vs_NONE [e])`,
  CHEAT_TAC);;

let every_Fn_vs_NONE_intro_multi = prove
 (`!max_app es. every_Fn_vs_NONE (intro_multi max_app es) =
  every_Fn_vs_NONE es`,
  CHEAT_TAC);;
add_simp every_Fn_vs_NONE_intro_multi;;

let compile_EQ_NIL = prove
 (`!do_mti es. clos_mti_compile do_mti max_app es = [] <=> es = []`,
  CHEAT_TAC);;
add_simp compile_EQ_NIL;;

(* compile_length *)
let clos_mtiProof_compile_length = prove
 (`LENGTH (clos_mti_compile do_mti max_app es) = LENGTH es`,
  CHEAT_TAC);;
add_simp clos_mtiProof_compile_length;;

(* [local] *)
let EVERY_HD = prove
 (`ALL P l /\ ~(l = []) ==> P (HD l)`,
  CHEAT_TAC);;

let collect_apps_preserves_set_globals = prove
 (`!max_app es e es' e'.
     collect_apps max_app es e = (es',e') ==> (BAG_UNION)
       (closProps_elist_globals es) (closProps_set_globals e) =
       (BAG_UNION) (closProps_elist_globals es')
       (closProps_set_globals e')`,
  CHEAT_TAC);;

let collect_apps_preserves_esgc_free = prove
 (`!max_app es e es' e'.
     collect_apps max_app es e = (es',e') /\ ALL closProps_esgc_free
       es /\ closProps_esgc_free e ==>
     ALL closProps_esgc_free es' /\ closProps_esgc_free e'`,
  CHEAT_TAC);;

let collect_args_preserves_set_globals = prove
 (`!max_app n e n' e'. collect_args max_app n e = (n',e') ==>
  closProps_set_globals e' = closProps_set_globals e`,
  CHEAT_TAC);;

(* HOL4 clos_mtiProofScript.sml:1469-1481: the ML values that the
   definitions below antiquote *)

let intro_multi_preserves_elist_globals = prove
 (`!max_app es. closProps_elist_globals (intro_multi max_app es) =
  closProps_elist_globals es`,
  CHEAT_TAC);;

let intro_multi_preserves_esgc_free = prove
 (`!max_app es. ALL closProps_esgc_free es ==> ALL closProps_esgc_free
  (intro_multi max_app es)`,
  CHEAT_TAC);;

let compile_preserves_elist_globals = prove
 (`!do_mti es. closProps_elist_globals (clos_mti_compile do_mti
  max_app es) = closProps_elist_globals es`,
  CHEAT_TAC);;

let compile_preserves_esgc_free = prove
 (`!do_mti es. ALL closProps_esgc_free es ==>
               ALL closProps_esgc_free (clos_mti_compile do_mti
                 max_app es)`,
  CHEAT_TAC);;

let EVERY_intro_multi = prove
 (`!m xs. ALL P (intro_multi m xs) = ALL (\x. P (HD (intro_multi m
  [x]))) xs`,
  CHEAT_TAC);;

let intro_multi_obeys_max_app = prove
 (`!m xs. ~(m = 0) /\ ALL no_mti xs ==>
   ALL (obeys_max_app m) (intro_multi m xs)`,
  CHEAT_TAC);;

let collect_apps_no_Labels = prove
 (`!m es e es' e'.
      collect_apps m es e = (es',e') /\ ALL no_Labels es /\ no_Labels
        e ==>
      ALL no_Labels es' /\ no_Labels e'`,
  CHEAT_TAC);;

let collect_args_no_Labels = prove
 (`!m na e es' e'.
      collect_args m na e = (es',e') /\ no_Labels e ==> no_Labels
        e'`,
  CHEAT_TAC);;

let intro_multi_no_Labels = prove
 (`!m xs. ALL no_Labels xs ==> ALL no_Labels (intro_multi m xs)`,
  CHEAT_TAC);;

(* preservation of observable semantics *)

let semantics_intro_multi = prove
 (`~(closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
        co (pure_cc (clos_mti_compile_inc max_app) cc) xs = ffi_Fail)
          ==>
      (!n. SND (SND (co n)) = [] /\ ALL no_mti (FST (SND (co n)))) /\
      1 <= max_app /\ ALL no_mti xs ==>
      closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
        (pure_co (clos_mti_compile_inc max_app) o co) cc
        (intro_multi max_app xs) =
      closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
        co (pure_cc (clos_mti_compile_inc max_app) cc) xs`,
  CHEAT_TAC);;

(* semantics_compile *)
let clos_mtiProof_semantics_compile = prove
 (`~(closSem_semantics ffi max_app FEMPTY co cc1 xs = ffi_Fail) /\
      cc1 = (if do_mti then pure_cc (clos_mti_compile_inc max_app)
        else I) cc /\
      co1 = (if do_mti then pure_co (clos_mti_compile_inc max_app)
        else I) o co /\
      (do_mti ==> (!n. SND (SND (co n)) = [] /\ ALL no_mti (FST (SND
        (co n)))) /\
           1 <= max_app /\ ALL no_mti xs) ==>
      closSem_semantics ffi max_app FEMPTY co1 cc (clos_mti_compile
        do_mti max_app xs) =
      closSem_semantics ffi max_app FEMPTY co cc1 xs`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
