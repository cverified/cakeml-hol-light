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
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* HOL4 clos_mtiProofScript.sml:18: ML code, not ported *)

(* code relation *)

(* HOL4 clos_mtiProofScript.sml:22-23: a theorem that HOL4 states as
   the value of an ML expression: no_mti_def *)

let code_rel_def = cake_define
  `clos_mtiProof_code_rel max_app e1 e2 <=>
     EVERY no_mti e1 /\ (e2 = intro_multi max_app e1)`;;
hol4_overload "code_rel" "clos_mtiProof_code_rel";;

let clos_mtiProof_code_rel_IMP_LENGTH =
  cake_theorem "code_rel_IMP_LENGTH"
  (fun () ->
    `clos_mtiProof_code_rel max_app xs ys ==> LENGTH ys = LENGTH xs`)
  CHEAT_TAC;;

let HD_intro_multi = cake_theorem "HD_intro_multi[simp]"
  (fun () ->
    `[HD (intro_multi max_app [e2])] = intro_multi max_app [e2]`)
  CHEAT_TAC;;

let intro_multi_cons = cake_theorem "intro_multi_cons"
  (fun () ->
    `!xs x. intro_multi m (x :: xs) = HD (intro_multi m [x]) ::
  intro_multi m xs`)
  CHEAT_TAC;;

let clos_mtiProof_code_rel_CONS_CONS = cake_theorem "code_rel_CONS_CONS"
  (fun () ->
    `clos_mtiProof_code_rel m (x1 :: x2 :: xs) (y1 :: y2 :: ys) <=>
      clos_mtiProof_code_rel m [x1] [y1] /\
        clos_mtiProof_code_rel m (x2 :: xs) (y2 :: ys)`)
  CHEAT_TAC;;

(* value relation *)

let mk_Fns_def = cake_define_list
  [`mk_Fns [] e = e`;
   `mk_Fns (t :: ts) e = closLang_Fn t NONE NONE 1 (mk_Fns ts e)`];;

let f_rel_def = cake_define
  `clos_mtiProof_f_rel max_app (a1,e1) (a2,e2) <=>
     (?b1 ts.
       clos_mtiProof_code_rel max_app [b1] [e2] /\ a2 <= max_app /\
         no_mti b1 /\
       a1 = 1 /\ e1 = mk_Fns ts b1 /\ a2 = LENGTH ts + 1)`;;
hol4_overload "f_rel" "clos_mtiProof_f_rel";;

let v_rel = cake_inductive
  `(!i. clos_mtiProof_v_rel (max_app:num) (closSem_Number i)
  (closSem_Number i)) /\
   (!w. clos_mtiProof_v_rel max_app (Word64 w) (Word64 w)) /\
   (!w. clos_mtiProof_v_rel max_app (closSem_ByteVector w)
     (closSem_ByteVector w)) /\
   (!n b. clos_mtiProof_v_rel max_app (closSem_RefPtr b n)
     (closSem_RefPtr b n)) /\
   (!tag xs ys.
      LIST_REL (clos_mtiProof_v_rel max_app) xs ys ==>
      clos_mtiProof_v_rel max_app (closSem_Block tag xs)
        (closSem_Block tag ys)) /\
   (!args1 args2 env1 env2 arg_count e1 ts e2.
      1 + LENGTH ts + LENGTH args1 = arg_count /\
      clos_mtiProof_code_rel max_app [e1] [e2] /\
      LIST_REL (clos_mtiProof_v_rel max_app) env1 env2 /\
      LIST_REL (clos_mtiProof_v_rel max_app) args1 args2 ==>
      clos_mtiProof_v_rel max_app
        (Closure NONE [] (args1 ++ env1) 1 (mk_Fns ts e1))
        (Closure NONE args2 env2 arg_count e2)) /\
   (!env1 funs1 env2 funs2 n.
      LIST_REL (clos_mtiProof_f_rel max_app) funs1 funs2 /\
      LIST_REL (clos_mtiProof_v_rel max_app) env1 env2 /\
      n < LENGTH funs2 ==>
      clos_mtiProof_v_rel max_app
        (Recclosure NONE [] env1 funs1 n)
        (Recclosure NONE [] env2 funs2 n)) /\
   (!args1 env1 funs1 args2 env2 funs2 n recc ts e1 e2 arg_count.
      LIST_REL (clos_mtiProof_f_rel max_app) funs1 funs2 /\
      LIST_REL (clos_mtiProof_v_rel max_app) env1 env2 /\
      LIST_REL (clos_mtiProof_v_rel max_app) args1 args2 /\ ~(args2 =
        []) /\
      n < LENGTH funs2 /\ EL n funs2 = (arg_count,e2) /\
      1 + LENGTH ts + LENGTH args1 = arg_count /\
      clos_mtiProof_code_rel max_app [e1] [e2] /\
      LIST_REL (clos_mtiProof_v_rel max_app) recc
           (GENLIST (Recclosure NONE [] env2 funs2) (LENGTH funs2))
             ==>
      clos_mtiProof_v_rel max_app
        (Closure NONE [] (args1 ++ recc ++ env1) 1 (mk_Fns ts e1))
        (Recclosure NONE args2 env2 funs2 n))`;;
hol4_overload "v_rel" "clos_mtiProof_v_rel";;

let v_rel_opt_def = cake_define
  `v_rel_opt max_app x2 x3 =
        match (x2,x3) with
          (NONE,NONE) -> T
        | ((SOME x),(SOME y)) -> clos_mtiProof_v_rel max_app x y
        | (_1,_2) -> F`;;

let ref_rel = cake_inductive
  `(!bs. clos_mtiProof_ref_rel max_app (closSem_ByteArray bs)
  (closSem_ByteArray bs)) /\
   (!xs ys.
     LIST_REL (clos_mtiProof_v_rel max_app) xs ys ==>
     clos_mtiProof_ref_rel max_app (closSem_ValueArray xs)
       (closSem_ValueArray ys)) /\
   (!m v w.
     clos_mtiProof_v_rel max_app v w ==>
     clos_mtiProof_ref_rel max_app (Thunk m v) (Thunk m w))`;;
hol4_overload "ref_rel" "clos_mtiProof_ref_rel";;

(* HOL4 clos_mtiProofScript.sml:128-132: a theorem that HOL4 states
   as the value of an ML expression: ref_rel_simps *)

let FMAP_REL_def = cake_define
  `clos_mtiProof_FMAP_REL r f1 f2 <=>
     FDOM f1 = FDOM f2 /\
     (!k v. FLOOKUP f1 k = SOME v ==>
           (?v2. FLOOKUP f2 k = SOME v2 /\ r v v2))`;;
hol4_overload "FMAP_REL" "clos_mtiProof_FMAP_REL";;

(* state relation *)

let SND_compile_inc = cake_theorem "SND_compile_inc[simp]"
  (fun () ->
    `SND (clos_mti_compile_inc max_app p) = []`)
  CHEAT_TAC;;

let state_rel_def = cake_define
  `clos_mtiProof_state_rel (s:('c,'ffi)closSem_state)
  (t:('c,'ffi)closSem_state) <=>
     (!n. SND (SND (closSem_state_compile_oracle s n)) = [] /\
          EVERY no_mti (FST (SND (closSem_state_compile_oracle s
            n)))) /\ closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY /\
       closSem_state_max_app
     t = closSem_state_max_app s /\ 1 <= closSem_state_max_app s /\
       state_clock
     t = state_clock s /\ state_ffi
     t = state_ffi s /\
     LIST_REL (v_rel_opt (closSem_state_max_app s))
       (closSem_state_globals s) (closSem_state_globals t) /\
     clos_mtiProof_FMAP_REL (ref_rel (closSem_state_max_app s))
       (state_refs s) (state_refs t) /\ closSem_state_compile
     s = pure_cc (clos_mti_compile_inc (closSem_state_max_app s))
       (closSem_state_compile t) /\ closSem_state_compile_oracle
     t = pure_co (clos_mti_compile_inc (closSem_state_max_app s))
       o closSem_state_compile_oracle s`;;
hol4_overload "state_rel" "clos_mtiProof_state_rel";;

let clos_mtiProof_state_rel_max_app =
  cake_theorem "state_rel_max_app[local]"
  (fun () ->
    `clos_mtiProof_state_rel s t ==> closSem_state_max_app s =
  closSem_state_max_app t /\ 1 <= closSem_state_max_app t`)
  CHEAT_TAC;;

let state_rel_clocks = cake_theorem "state_rel_clocks[local]"
  (fun () ->
    `clos_mtiProof_state_rel s t ==> state_clock s = state_clock t`)
  CHEAT_TAC;;

(* evaluation theorem *)

let collect_args_IMP = cake_theorem "collect_args_IMP"
  (fun () ->
    `!max_app k e1 num_args e2.
        collect_args max_app k e1 = (num_args,e2) /\ k <= max_app
          ==>
        k <= num_args /\ num_args <= max_app`)
  CHEAT_TAC;;

let collect_args_ok_IMP = cake_theorem "collect_args_ok_IMP"
  (fun () ->
    `!max_app k e num_args e2.
        collect_args max_app k e = (num_args,e2) /\ no_mti e ==>
        (?ts. e = mk_Fns ts e2 /\ num_args = k + LENGTH ts /\
          no_mti e2)`)
  CHEAT_TAC;;

let clos_mtiProof_dest_closure_SOME_IMP =
  cake_theorem "dest_closure_SOME_IMP"
  (fun () ->
    `dest_closure max_app loc_opt f2 xs = SOME x ==>
      (?loc arg_env clo_env num_args e. f2 = Closure loc arg_env
        clo_env num_args e) \/
      (?loc arg_env clo_env fns i. f2 = Recclosure loc arg_env
        clo_env fns i)`)
  CHEAT_TAC;;

let collect_apps_acc = cake_theorem "collect_apps_acc[local]"
  (fun () ->
    `!max_app acc e res s.
       collect_apps max_app acc e = (res,s) ==>
       (?other. res = acc ++ other)`)
  CHEAT_TAC;;

let collect_apps_cons_lemma =
  cake_theorem "collect_apps_cons_lemma[local]"
  (fun () ->
    `!e1 m ys other e2.
       collect_apps (m + LENGTH ys) ys e1 = (ys ++ other,e2) <=>
       collect_apps m [] e1 = (other,e2)`)
  CHEAT_TAC;;

let collect_apps_cons = cake_theorem "collect_apps_cons[local]"
  (fun () ->
    `!e1 m x other e2.
       collect_apps m [x] e1 = (x :: other,e2) /\ ~(m = 0) ==>
       collect_apps (m - 1) [] e1 = (other,e2)`)
  CHEAT_TAC;;

let mk_Apps_def = cake_define_list
  [`mk_Apps e [] = e`;
   `mk_Apps e ((t,other) :: ts) = App t NONE (mk_Apps e ts) [other]`];;

let collect_apps_IMP_mk_Apps = cake_theorem "collect_apps_IMP_mk_Apps"
  (fun () ->
    `!e max_app (acc:closLang_exp list) other e3.
         collect_apps max_app [] e = (other,e3) /\ no_mti e ==>
         (?ts. e = mk_Apps e3 (ZIP ts other) /\ LENGTH other =
           LENGTH ts /\
              LENGTH other <= max_app)`)
  CHEAT_TAC;;

let mk_Apps_err_1 = cake_theorem "mk_Apps_err_1[local]"
  (fun () ->
    `!ts other env1 s1 e3.
       closSem_evaluate (other,env1,s1) = (Rerr e2,s2) /\
       LENGTH other = LENGTH ts ==>
       closSem_evaluate ([mk_Apps e3 (ZIP ts other)],env1,s1) =
         (Rerr e2,s2)`)
  CHEAT_TAC;;

let mk_Apps_err_2 = cake_theorem "mk_Apps_err_2[local]"
  (fun () ->
    `!ts other env1 s1 e3 vs.
       closSem_evaluate ([e3],env1,s2) = (Rerr e2,s2') /\
       closSem_evaluate (other,env1,s1) = (Rval vs,s2) /\
       LENGTH other = LENGTH ts ==>
       closSem_evaluate ([mk_Apps e3 (ZIP ts other)],env1,s1) =
         (Rerr e2,s2')`)
  CHEAT_TAC;;

let collect_apps_no_mti = cake_theorem "collect_apps_no_mti"
  (fun () ->
    `!k aux e res e1.
        collect_apps k aux e = (res,e1) /\
        no_mti e /\ EVERY no_mti aux ==>
        EVERY no_mti res /\ no_mti e1`)
  CHEAT_TAC;;

let evaluate_mk_Apps_err = cake_theorem "evaluate_mk_Apps_err[local]"
  (fun () ->
    `!other ts env1 s1 vs.
       closSem_evaluate (other,env1,s1) = (Rval vs,s3) /\
       closSem_evaluate ([e],env1,s3) = (Rerr e3,s2') /\
       LENGTH other = LENGTH ts ==>
       closSem_evaluate ([mk_Apps e (ZIP ts other)],env1,s1) =
         (Rerr e3,s2')`)
  CHEAT_TAC;;

let evaluate_apps_def = cake_define_list
  [`evaluate_apps f [] s = (Rval [f],s)`;
   `evaluate_apps f (x :: xs) s =
      (match evaluate_apps f xs s with (Rval [v],s1) ->
        evaluate_app NONE v [x] s1 | res -> res)`];;

let evaluate_mk_Apps_ok = cake_theorem "evaluate_mk_Apps_ok[local]"
  (fun () ->
    `!other ts env1 s1 vs.
         closSem_evaluate ([e],env1,s3) = (Rval [f],s2') /\
         closSem_evaluate (other,env1,s1) = (Rval vs,s3) /\
         LENGTH other = LENGTH ts ==>
         closSem_evaluate ([mk_Apps e (ZIP ts other)],env1,s1) =
         evaluate_apps f vs s2'`)
  CHEAT_TAC;;

let dest_closure_NONE_IMP_apps =
  cake_theorem "dest_closure_NONE_IMP_apps[local]"
  (fun () ->
    `!xs f1 s1.
         dest_closure (closSem_state_max_app s1) NONE f1 [LAST xs]
           = NONE /\ ~(xs = []) ==>
         evaluate_apps f1 xs s1 = (Rerr (Rabort Rtype_error),s1)`)
  CHEAT_TAC;;

let evaluate_apps_SNOC = cake_theorem "evaluate_apps_SNOC[local]"
  (fun () ->
    `!xs x f s.
         evaluate_apps f (SNOC x xs) s =
         (match evaluate_app NONE f [x] s with (Rval [v],s) ->
           evaluate_apps v xs s | res -> res)`)
  CHEAT_TAC;;

let evaluate_apps_Clos_timeout =
  cake_theorem "evaluate_apps_Clos_timeout[local]"
  (fun () ->
    `!ys ts s1 e1 env. state_clock
         s1 < LENGTH ys /\ LENGTH ys <= LENGTH ts /\
         1 <= closSem_state_max_app s1 ==>
         evaluate_apps (Closure NONE [] env 1 (mk_Fns ts e1))
           ys s1 = (Rerr (Rabort Rtimeout_error),state_clock_fupd
             (K 0) s1)`)
  CHEAT_TAC;;

let evaluate_apps_Clos_timeout_alt =
  cake_theorem "evaluate_apps_Clos_timeout_alt[local]"
  (fun () ->
    `!ys ts s1 e1 env. state_clock
         s1 <= LENGTH ts /\ LENGTH ts < LENGTH ys /\
         1 <= closSem_state_max_app s1 ==>
         evaluate_apps (Closure NONE [] env 1 (mk_Fns ts e1))
           ys s1 = (Rerr (Rabort Rtimeout_error),state_clock_fupd
             (K 0) s1)`)
  CHEAT_TAC;;

let evaluate_apps_Clos_short =
  cake_theorem "evaluate_apps_Clos_short[local]"
  (fun () ->
    `!ys ts s1 e1 env.
         LENGTH ys <= state_clock s1 /\ LENGTH ys <= LENGTH ts /\
         1 <= closSem_state_max_app s1 ==>
         evaluate_apps (Closure NONE [] env 1 (mk_Fns ts e1)) ys s1
           =
            (Rval [Closure NONE [] (ys ++ env) 1
                      (mk_Fns (DROP (LENGTH ys) ts) e1)],
             closSem_dec_clock (LENGTH ys) s1)`)
  CHEAT_TAC;;

let evaluate_apps_Clos_long =
  cake_theorem "evaluate_apps_Clos_long[local]"
  (fun () ->
    `!ys ts s1 e1 env.
         LENGTH ts < state_clock s1 /\ LENGTH ts < LENGTH ys /\
         1 <= closSem_state_max_app s1 ==>
         evaluate_apps (Closure NONE [] env 1 (mk_Fns ts e1)) ys s1
           =
           (match closSem_evaluate ([e1],REVERSE (TAKE (1 + LENGTH
             ts) (REVERSE ys)) ++ env,
                   closSem_dec_clock (1 + LENGTH ts) s1) with (Rval
                     [v],s) ->
                evaluate_apps v (REVERSE (DROP (1 + LENGTH ts)
                  (REVERSE ys))) s | res -> res)`)
  CHEAT_TAC;;

let LIST_REL_f_rel_IMP = cake_theorem "LIST_REL_f_rel_IMP[local]"
  (fun () ->
    `!fns funs1. LIST_REL (clos_mtiProof_f_rel max_app) funs1 fns ==>
  (!x. ~(MEM (0,x) fns))`)
  CHEAT_TAC;;

(* HOL4 clos_mtiProofScript.sml:494-507: a theorem that HOL4 states
   as the value of an ML expression: v_rel_simps *)

let v_rel_opt_thm = cake_theorem "v_rel_opt_thm[local]"
  (fun () ->
    `v_rel_opt m = OPTREL (clos_mtiProof_v_rel m)`)
  CHEAT_TAC;;

let clos_mtiProof_simple_val_rel = cake_theorem "simple_val_rel"
  (fun () ->
    `closProps_simple_val_rel (clos_mtiProof_v_rel max_app_n)`)
  CHEAT_TAC;;

let clos_mtiProof_simple_state_rel = cake_theorem "simple_state_rel"
  (fun () ->
    `closProps_simple_state_rel (clos_mtiProof_v_rel max_app_n)
       (\s t. closSem_state_max_app s = max_app_n /\
         clos_mtiProof_state_rel s t)`)
  CHEAT_TAC;;

let clos_mtiProof_state_rel_opt_rel_refs =
  cake_theorem "state_rel_opt_rel_refs[local]"
  (fun () ->
    `(clos_mtiProof_state_rel s1 s2 /\ FLOOKUP (state_refs s1) n = r1
  ==>
        (?r2. FLOOKUP (state_refs s2) n = r2 /\ OPTREL (ref_rel
          (closSem_state_max_app s1)) r1 r2)) /\
     (clos_mtiProof_state_rel s1 s2 /\ FLOOKUP (state_refs s2) n =
       r2 ==>
        (?r1. FLOOKUP (state_refs s1) n = r1 /\ OPTREL (ref_rel
          (closSem_state_max_app s1)) r1 r2))`)
  CHEAT_TAC;;

let clos_mtiProof_rel_update_thunk =
  cake_theorem "rel_update_thunk[local]"
  (fun () ->
    `clos_mtiProof_state_rel s1 s2 /\
     LIST_REL (clos_mtiProof_v_rel (closSem_state_max_app s1)) vs
       ys ==>
       (update_thunk [closSem_RefPtr v ptr] (state_refs s2) ys =
         NONE ==>
          update_thunk [closSem_RefPtr v ptr] (state_refs s1) vs =
            NONE) /\
       (update_thunk [closSem_RefPtr v ptr] (state_refs s2) ys =
         SOME refs2 ==>
          (?refs1. update_thunk [closSem_RefPtr v ptr] (state_refs
            s1) vs = SOME refs1 /\
                  clos_mtiProof_state_rel (state_refs_fupd (K
                    refs1) s1) (state_refs_fupd (K refs2) s2)))`)
  CHEAT_TAC;;

(* HOL4 clos_mtiProofScript.sml:581-586: ML code, not ported *)

let clos_mtiProof_do_app_lemma = cake_theorem "do_app_lemma"
  (fun () ->
    `clos_mtiProof_state_rel s (t:('c,'ffi)closSem_state) /\ LIST_REL
  (clos_mtiProof_v_rel (closSem_state_max_app s)) xs ys ==>
       (match do_app opp ys t with Rerr err2 -> (?err1. do_app opp
         xs s = Rerr err1 /\
                              exc_rel (clos_mtiProof_v_rel
                                (closSem_state_max_app s)) err1 err2) |
                                Rval (y,t1) -> (?x s1.
                                clos_mtiProof_v_rel
                                (closSem_state_max_app s) x y /\
                                clos_mtiProof_state_rel s1 t1 /\
                              do_app opp xs s = Rval (x,s1)))`)
  CHEAT_TAC;;

let clos_mtiProof_v_rel_IMP_v_to_bytes =
  cake_theorem "v_rel_IMP_v_to_bytes[local]"
  (fun () ->
    `clos_mtiProof_v_rel max_app x y ==> closSem_v_to_bytes y =
  closSem_v_to_bytes x`)
  CHEAT_TAC;;

let clos_mtiProof_v_rel_IMP_v_to_words =
  cake_theorem "v_rel_IMP_v_to_words[local]"
  (fun () ->
    `clos_mtiProof_v_rel max_app x y ==> closSem_v_to_words y =
  closSem_v_to_words x`)
  CHEAT_TAC;;

(* HOL4 clos_mtiProofScript.sml:611-617: ML code, not ported *)

let clos_mtiProof_do_install_lemma =
  cake_theorem "do_install_lemma[local]"
  (fun () ->
    `clos_mtiProof_state_rel s t /\ LIST_REL (clos_mtiProof_v_rel
  (closSem_state_max_app s)) xs ys ==>
     (match closSem_do_install xs s with (Rerr err1,s1) -> (?err2
       t1. closSem_do_install ys t = (Rerr err2,t1) /\
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
                                exps2,t1)))`)
  CHEAT_TAC;;

let intro_multi_EQ_NIL = cake_theorem "intro_multi_EQ_NIL[simp]"
  (fun () ->
    `!max_app es. intro_multi max_app es = [] <=> es = []`)
  CHEAT_TAC;;

let intro_multi_nil = cake_theorem "intro_multi_nil"
  (fun () ->
    `intro_multi x [] = []`)
  CHEAT_TAC;;

let clos_mtiProof_result_rel_Rval2 = cake_theorem "result_rel_Rval2"
  (fun () ->
    `semanticPrimitivesProps_result_rel P P' x (Rval v') = (?v. x =
  Rval v /\ P v v')`)
  CHEAT_TAC;;

let evaluate_intro_multi = cake_theorem "evaluate_intro_multi"
  (fun () ->
    `(!ys env2 (t1:('c,'ffi)closSem_state) env1 t2 s1 res2 xs.
       (closSem_evaluate (ys,env2,t1) = (res2,t2)) /\
       EVERY2 (clos_mtiProof_v_rel (closSem_state_max_app s1)) env1
         env2 /\
       clos_mtiProof_state_rel s1 t1 /\ clos_mtiProof_code_rel
         (closSem_state_max_app s1) xs ys ==>
       (?res1 s2.
          (closSem_evaluate (xs,env1,s1) = (res1,s2)) /\
          semanticPrimitivesProps_result_rel (LIST_REL
            (clos_mtiProof_v_rel (closSem_state_max_app s1)))
            (clos_mtiProof_v_rel (closSem_state_max_app s1)) res1 res2
            /\
          clos_mtiProof_state_rel s2 t2)) /\
     (!loc_opt f2 args2 (t1:('c,'ffi)closSem_state) res2 t2 f1
       args1 s1.
       (evaluate_app loc_opt f2 args2 t1 = (res2,t2)) /\ loc_opt =
         NONE /\
       clos_mtiProof_v_rel (closSem_state_max_app s1) f1 f2 /\
         EVERY2 (clos_mtiProof_v_rel (closSem_state_max_app s1)) args1
         args2 /\
       clos_mtiProof_state_rel s1 t1 /\ LENGTH args1 <=
         closSem_state_max_app s1 ==>
       (?res1 s2.
         (evaluate_apps f1 args1 s1 = (res1,s2)) /\
         semanticPrimitivesProps_result_rel (LIST_REL
           (clos_mtiProof_v_rel (closSem_state_max_app s1)))
           (clos_mtiProof_v_rel (closSem_state_max_app s1)) res1 res2 /\
         clos_mtiProof_state_rel s2 t2))`)
  CHEAT_TAC;;

let intro_multi_correct = cake_theorem "intro_multi_correct"
  (fun () ->
    `!xs env1 (s1:('c,'ffi)closSem_state) res1 s2 env2 t2 t1.
        closSem_evaluate (xs,env1,s1) = (res1,s2) /\ EVERY no_mti
          xs /\
        LIST_REL (clos_mtiProof_v_rel (closSem_state_max_app s1))
          env1 env2 /\ clos_mtiProof_state_rel s1 t1 ==>
        (?res2 t2.
          closSem_evaluate (intro_multi (closSem_state_max_app s1)
            xs,env2,t1) = (res2,t2) /\
          semanticPrimitivesProps_result_rel (LIST_REL
            (clos_mtiProof_v_rel (closSem_state_max_app s1)))
            (clos_mtiProof_v_rel (closSem_state_max_app s1)) res1
            res2 /\ clos_mtiProof_state_rel s2 t2)`)
  CHEAT_TAC;;

(* syntax well-formedness *)

let contains_App_SOME_collect_args =
  cake_theorem "contains_App_SOME_collect_args"
  (fun () ->
    `!m x y a b. collect_args m x y = (a,b) ==>
      (contains_App_SOME m [y] <=> contains_App_SOME m [b])`)
  CHEAT_TAC;;

let contains_App_SOME_collect_apps =
  cake_theorem "contains_App_SOME_collect_apps"
  (fun () ->
    `!max_app x y a b. collect_apps max_app x y = (a,b) ==>
      (max_app < LENGTH x \/ contains_App_SOME max_app x \/
        contains_App_SOME max_app [y] <=>
       max_app < LENGTH a \/ contains_App_SOME max_app a \/
         contains_App_SOME max_app [b])`)
  CHEAT_TAC;;

let contains_App_SOME_intro_multi =
  cake_theorem "contains_App_SOME_intro_multi[simp]"
  (fun () ->
    `!max_app es. contains_App_SOME max_app (intro_multi max_app es)
  <=> contains_App_SOME max_app es`)
  CHEAT_TAC;;

let contains_App_SOME_compile =
  cake_theorem "contains_App_SOME_compile[simp]"
  (fun () ->
    `!do_mti es. contains_App_SOME max_app (clos_mti_compile do_mti
  max_app es) <=> contains_App_SOME max_app es`)
  CHEAT_TAC;;

let collect_args_preserves_esgc_free =
  cake_theorem "collect_args_preserves_esgc_free"
  (fun () ->
    `!max_app n e n' e'. collect_args max_app n e = (n',e') /\
                         closProps_esgc_free e ==>
                           closProps_esgc_free e'`)
  CHEAT_TAC;;

let every_Fn_vs_NONE_collect_apps =
  cake_theorem "every_Fn_vs_NONE_collect_apps[local]"
  (fun () ->
    `!max_app es e x y. collect_apps max_app es e = (x,y) ==>
     (every_Fn_vs_NONE x /\ every_Fn_vs_NONE [y] <=>
      every_Fn_vs_NONE es /\ every_Fn_vs_NONE [e])`)
  CHEAT_TAC;;

let every_Fn_vs_NONE_collect_args =
  cake_theorem "every_Fn_vs_NONE_collect_args[local]"
  (fun () ->
    `!max_app es e x y. collect_args max_app es e = (x,y) ==>
       (every_Fn_vs_NONE [y] <=> every_Fn_vs_NONE [e])`)
  CHEAT_TAC;;

let every_Fn_vs_NONE_intro_multi =
  cake_theorem "every_Fn_vs_NONE_intro_multi[simp]"
  (fun () ->
    `!max_app es. every_Fn_vs_NONE (intro_multi max_app es) =
  every_Fn_vs_NONE es`)
  CHEAT_TAC;;

let compile_EQ_NIL = cake_theorem "compile_EQ_NIL[simp]"
  (fun () ->
    `!do_mti es. clos_mti_compile do_mti max_app es = [] <=> es = []`)
  CHEAT_TAC;;

let clos_mtiProof_compile_length = cake_theorem "compile_length[simp]"
  (fun () ->
    `LENGTH (clos_mti_compile do_mti max_app es) = LENGTH es`)
  CHEAT_TAC;;

let EVERY_HD = cake_theorem "EVERY_HD[local]"
  (fun () ->
    `EVERY P l /\ ~(l = []) ==> P (HD l)`)
  CHEAT_TAC;;

let collect_apps_preserves_set_globals =
  cake_theorem "collect_apps_preserves_set_globals"
  (fun () ->
    `!max_app es e es' e'.
       collect_apps max_app es e = (es',e') ==> (BAG_UNION)
         (closProps_elist_globals es) (closProps_set_globals e) =
         (BAG_UNION) (closProps_elist_globals es')
         (closProps_set_globals e')`)
  CHEAT_TAC;;

let collect_apps_preserves_esgc_free =
  cake_theorem "collect_apps_preserves_esgc_free"
  (fun () ->
    `!max_app es e es' e'.
       collect_apps max_app es e = (es',e') /\ EVERY
         closProps_esgc_free es /\ closProps_esgc_free e ==>
       EVERY closProps_esgc_free es' /\ closProps_esgc_free e'`)
  CHEAT_TAC;;

let collect_args_preserves_set_globals =
  cake_theorem "collect_args_preserves_set_globals"
  (fun () ->
    `!max_app n e n' e'. collect_args max_app n e = (n',e') ==>
  closProps_set_globals e' = closProps_set_globals e`)
  CHEAT_TAC;;

(* HOL4 clos_mtiProofScript.sml:1469-1481: the ML values that the
   definitions below antiquote *)

let intro_multi_preserves_elist_globals =
  cake_theorem "intro_multi_preserves_elist_globals"
  (fun () ->
    `!max_app es. closProps_elist_globals (intro_multi max_app es) =
  closProps_elist_globals es`)
  CHEAT_TAC;;

let intro_multi_preserves_esgc_free =
  cake_theorem "intro_multi_preserves_esgc_free"
  (fun () ->
    `!max_app es. EVERY closProps_esgc_free es ==> EVERY
  closProps_esgc_free (intro_multi max_app es)`)
  CHEAT_TAC;;

let compile_preserves_elist_globals =
  cake_theorem "compile_preserves_elist_globals"
  (fun () ->
    `!do_mti es. closProps_elist_globals (clos_mti_compile do_mti
  max_app es) = closProps_elist_globals es`)
  CHEAT_TAC;;

let compile_preserves_esgc_free =
  cake_theorem "compile_preserves_esgc_free"
  (fun () ->
    `!do_mti es. EVERY closProps_esgc_free es ==>
                 EVERY closProps_esgc_free (clos_mti_compile
                   do_mti max_app es)`)
  CHEAT_TAC;;

let EVERY_intro_multi = cake_theorem "EVERY_intro_multi"
  (fun () ->
    `!m xs. EVERY P (intro_multi m xs) = EVERY (\x. P (HD (intro_multi
  m [x]))) xs`)
  CHEAT_TAC;;

let intro_multi_obeys_max_app = cake_theorem "intro_multi_obeys_max_app"
  (fun () ->
    `!m xs. ~(m = 0) /\ EVERY no_mti xs ==>
     EVERY (obeys_max_app m) (intro_multi m xs)`)
  CHEAT_TAC;;

let collect_apps_no_Labels = cake_theorem "collect_apps_no_Labels"
  (fun () ->
    `!m es e es' e'.
        collect_apps m es e = (es',e') /\ EVERY no_Labels es /\
          no_Labels e ==>
        EVERY no_Labels es' /\ no_Labels e'`)
  CHEAT_TAC;;

let collect_args_no_Labels = cake_theorem "collect_args_no_Labels"
  (fun () ->
    `!m na e es' e'.
        collect_args m na e = (es',e') /\ no_Labels e ==>
          no_Labels e'`)
  CHEAT_TAC;;

let intro_multi_no_Labels = cake_theorem "intro_multi_no_Labels"
  (fun () ->
    `!m xs. EVERY no_Labels xs ==> EVERY no_Labels (intro_multi m xs)`)
  CHEAT_TAC;;

(* preservation of observable semantics *)

let semantics_intro_multi = cake_theorem "semantics_intro_multi"
  (fun () ->
    `~(closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
          co (pure_cc (clos_mti_compile_inc max_app) cc) xs =
            ffi_Fail) ==>
        (!n. SND (SND (co n)) = [] /\ EVERY no_mti (FST (SND (co
          n)))) /\
        1 <= max_app /\ EVERY no_mti xs ==>
        closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
          (pure_co (clos_mti_compile_inc max_app) o co) cc
          (intro_multi max_app xs) =
        closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
          co (pure_cc (clos_mti_compile_inc max_app) cc) xs`)
  CHEAT_TAC;;

let clos_mtiProof_semantics_compile = cake_theorem "semantics_compile"
  (fun () ->
    `~(closSem_semantics ffi max_app FEMPTY co cc1 xs = ffi_Fail) /\
        cc1 = (if do_mti then pure_cc (clos_mti_compile_inc
          max_app) else I) cc /\
        co1 = (if do_mti then pure_co (clos_mti_compile_inc
          max_app) else I) o co /\
        (do_mti ==> (!n. SND (SND (co n)) = [] /\ EVERY no_mti (FST
          (SND (co n)))) /\
             1 <= max_app /\ EVERY no_mti xs) ==>
        closSem_semantics ffi max_app FEMPTY co1 cc
          (clos_mti_compile do_mti max_app xs) =
        closSem_semantics ffi max_app FEMPTY co cc1 xs`)
  CHEAT_TAC;;
